module

public import CFSG.ClassicalInvolution.Asc77.AscT7AApp
public import CFSG.ClassicalInvolution.Asc77.AscT7AEnd
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Cases

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_17_cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → rLayer Ω (t * z) ≤ sigmaGen Ω K →
        dComp Ω K = dstarComp Ω K →
          Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K ∧
            Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K

@[expose] def C21_E_cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        (∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)) → MuIsoWylD4 Ω W →
          (∀ M : Subgroup G,
            M ∈ dstarComp Ω K ↔ M ∈ Ω ∧ M ≤ Subgroup.centralizer ({t * z} : Set G)) ∧
            Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K

variable {p f}

section Frames

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

namespace T7A

theorem mem_dstarComp_of_mem_dComp [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {K J : Subgroup G} (hJ : J ∈ dComp Ω K) : J ∈ dstarComp Ω K := by
  induction hJ with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.tail ⟨hbc.1, ?_⟩
    rcases hbc.2 with h | h
    · exact Or.inl (T3.omegaNbr_subset_omegaStarNbr hp hΩ _ h)
    · exact Or.inr (T3.omegaNbr_subset_omegaStarNbr hp hΩ _ h)

theorem conjSub_le_of_mem {C : Subgroup G} {c : G} (hc : c ∈ C) {M : Subgroup G} (hM : M ≤ C) :
    conjSub c M ≤ C := by
  intro x hx
  have h1 : c⁻¹ * x * c ∈ M := mem_conjSub_iff.mp hx
  have h2 : c * (c⁻¹ * x * c) * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc (hM h1)) (C.inv_mem hc)
  have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
  rwa [e] at h2

theorem centralizer_le_sigmaStarNorm_of_eq (hΩ : ConjInvariant Ω) {K : Subgroup G} {a : G}
    (hstar : ∀ M : Subgroup G,
      M ∈ dstarComp Ω K ↔ M ∈ Ω ∧ M ≤ Subgroup.centralizer ({a} : Set G)) :
    Subgroup.centralizer ({a} : Set G) ≤ sigmaStarNorm Ω K := by
  intro c hc M
  rw [hstar M, hstar (conjSub c M)]
  constructor
  · rintro ⟨hM, hMC⟩
    exact ⟨hΩ c M hM, conjSub_le_of_mem hc hMC⟩
  · rintro ⟨hM, hMC⟩
    refine ⟨?_, ?_⟩
    · have := hΩ c⁻¹ _ hM
      rwa [conjSub_inv_conjSub] at this
    · have := conjSub_le_of_mem (Subgroup.inv_mem _ hc) hMC
      rwa [conjSub_inv_conjSub] at this

end T7A

variable [Finite G] [IsSimpleGroup G]

theorem dComp_eq_dstarComp_of_le (h12 : C21_12 p f) (hWyl : C21_WylTrans p f)
    {K K' J W : Subgroup G} {z u t : G} (h : Hyp21 p f Ω K K' z u J t W)
    (hD : rLayer Ω (t * z) ≤ sigmaGen Ω K) : dComp Ω K = dstarComp Ω K := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  rcases h12 G Ω K K' z u J t W h with heq | hmu
  · exact heq
  · have htr := hWyl G Ω K K' z u J t W h hmu (sigmaNorm Ω K)
      (hD.trans (T7A.sigmaGen_le_sigmaNorm hΩ.conjInvariant hK))
    ext M
    constructor
    · exact fun hM => T7A.mem_dstarComp_of_mem_dComp hp hΩ hM
    · intro hM
      obtain ⟨y, hy, rfl⟩ := htr M hM
      exact (hy K).mp Relation.ReflTransGen.refl

theorem frame_cent_sigmaStarNorm (h12 : C21_12 p f) (h13 : C21_13 p f) (h15 : C21_15 p f)
    (h16 : C21_16 p f) (hWyl : C21_WylTrans p f) (ha : C21_17_cent p f) (hb : C21_E_cent p f)
    {K K' J W : Subgroup G} {z u t : G} (h : Hyp21 p f Ω K K' z u J t W) :
    Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K ∧
      Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K := by
  have hα := h16 G Ω K K' z u J t W h
  by_cases hD : rLayer Ω (t * z) ≤ sigmaGen Ω K
  · exact ha G Ω K K' z u J t W h hα hD (dComp_eq_dstarComp_of_le h12 hWyl h hD)
  · have hSigC := h15 G Ω K K' z u J t W h hα hD
    have hmu : MuIsoWylD4 Ω W := by
      obtain ⟨-, h13'⟩ := h13 G Ω K K' z u J t W h
      rw [hα, bot_sup_eq] at h13'
      rcases h13' with hle | ⟨hmu, -⟩
      · exact absurd hle hD
      · exact hmu
    obtain ⟨hstar, hu⟩ := hb G Ω K K' z u J t W h hα hD hSigC hmu
    exact ⟨T7A.centralizer_le_sigmaStarNorm_of_eq h.std.stand.hyp.conjInvariant hstar, hu⟩

theorem sigmaStarNorm_eq_top (hE : ThmEWithSylow p f) (h12 : C21_12 p f) (h13 : C21_13 p f)
    (h15 : C21_15 p f) (h16 : C21_16 p f) (hWyl : C21_WylTrans p f) (ha : C21_17_cent p f)
    (hb : C21_E_cent p f) {K K' J W : Subgroup G} {z u t : G} (h : Hyp21 p f Ω K K' z u J t W) :
    sigmaStarNorm Ω K = ⊤ := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have htail : StdCentTail Ω K (sigmaStarNorm Ω K) z :=
    stdCentTail_of_frames hp hq hΩ h fun {_ _ _ _ _ _} _ h₁ =>
      frame_cent_sigmaStarNorm h12 h13 h15 h16 hWyl ha hb h₁
  have hstd := stdCent_sigmaStarNorm hp hq hΩ hK h.std.hz h.std.stand.trans htail
  have htrans : ∀ M ∈ dstarComp Ω K, ∃ x ∈ sigmaStarNorm Ω K, conjSub x K = M := by
    intro M hM
    obtain ⟨x, hx⟩ := h.std.stand.trans M (T3.mem_dstarComp_symm hK hM).1
    exact ⟨x, T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hx ▸ hM), hx⟩
  exact thmE_apply hE h.std.stand h.std.hz h.std.hK' h.std.hne hstd htrans

theorem c21_17_of (hE : ThmEWithSylow p f) (h12 : C21_12 p f) (h13 : C21_13 p f)
    (h15 : C21_15 p f) (h16 : C21_16 p f) (hWyl : C21_WylTrans p f) (ha : C21_17_cent p f)
    (hb : C21_E_cent p f) : C21_17 p f := by
  intro G _ _ _ Ω K K' z u J t W h hD
  have htop := sigmaStarNorm_eq_top hE h12 h13 h15 h16 hWyl ha hb h
  have hSig := dComp_eq_dstarComp_of_le h12 hWyl h hD
  have hsn : sigmaNorm Ω K = ⊤ := by
    rw [← htop]
    ext g
    exact forall_congr' fun M => by rw [hSig]
  exact h.std.disconnected (dConnected_of_sigmaNorm_eq_top h.std.stand.mem h.std.stand.trans hsn)

namespace T7A

omit [Finite G] in
theorem eq_one_of_central {c : G} (hnc : ∃ x y : G, x * y ≠ y * x) (hc : ∀ g : G, g * c = c * g) :
    c = 1 := by
  by_contra hc1
  have : (Subgroup.zpowers c).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := hn
    have h1 : g * c ^ k = c ^ k * g := (Commute.zpow_right (show Commute g c from hc g) k).eq
    show g * c ^ k * g⁻¹ ∈ Subgroup.zpowers c
    rw [h1, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers c) with h | h
  · exact hc1 (Subgroup.zpowers_eq_bot.mp h)
  · obtain ⟨x, y, hxy⟩ := hnc
    have hx : x ∈ Subgroup.zpowers c := h ▸ Subgroup.mem_top x
    have hy : y ∈ Subgroup.zpowers c := h ▸ Subgroup.mem_top y
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact hxy (Commute.zpow_zpow_self c m n).eq

end T7A

theorem c21_E_of (hE : ThmEWithSylow p f) (h12 : C21_12 p f) (h13 : C21_13 p f)
    (h15 : C21_15 p f) (h16 : C21_16 p f) (hWyl : C21_WylTrans p f) (ha : C21_17_cent p f)
    (hb : C21_E_cent p f) : C21_E p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSigC hmu
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have htop := sigmaStarNorm_eq_top hE h12 h13 h15 h16 hWyl ha hb h
  obtain ⟨hstar, -⟩ := hb G Ω K K' z u J t W h hα hD hSigC hmu
  have hall : ∀ M ∈ Ω, M ≤ Subgroup.centralizer ({t * z} : Set G) := by
    intro M hM
    obtain ⟨x, hx⟩ := h.std.stand.trans M hM
    have hxH : x ∈ sigmaStarNorm Ω K := by rw [htop]; exact Subgroup.mem_top x
    have hMS : M ∈ dstarComp Ω K := by
      have := (mem_sigmaStarNorm_iff.mp hxH K).mp Relation.ReflTransGen.refl
      rwa [hx] at this
    exact ((hstar M).mp hMS).2
  have hcent : Subgroup.centralizer ({t * z} : Set G) = ⊤ := by
    rw [eq_top_iff, ← h.std.stand.gen]
    exact iSup₂_le fun M hM => hall M hM
  have hcomm : ∀ g : G, g * (t * z) = (t * z) * g := fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (hcent ▸ Subgroup.mem_top g)
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
  obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hp hVR).exists_not_commute
  have h1 : t * z = 1 := T7A.eq_one_of_central ⟨x, y, hxy⟩ hcomm
  have h2 : t = z⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.std.hz.sq
  exact h.twinFrameData.t_ne_z (h2.trans h3)

variable (p f) in
theorem c21_2_of_hyp51 (hE : ThmEWithSylow p f) (hH51 : TwinFrameHyp51 p f)
    (h4 : TwinNormAlpha p f) (h12 : C21_12 p f) (h13 : C21_13 p f) (h14 : C21_14 p f)
    (h15 : C21_15 p f) (hWyl : C21_WylTrans p f) (h17c : C21_17_cent p f)
    (hEc : C21_E_cent p f) : C21_2 p f := by
  have h3 : C21_3 p f := c21_3_of p f hH51
  have h16 : C21_16 p f := c21_16_of p f hE h3 h4 h12 h13 h14 hWyl
  have h17 : C21_17 p f := c21_17_of hE h12 h13 h15 h16 hWyl h17c hEc
  have hEnd : C21_E p f := c21_E_of hE h12 h13 h15 h16 hWyl h17c hEc
  exact c21_2_of_steps (c21_setup p f) (c21_false_of_steps h13 h15 h16 h17 hEnd)

variable (p f) in
theorem c21_2_of_inputs (hE : ThmEWithSylow p f) (hHz : TwinFrameHyp51z p f)
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (h4 : TwinNormAlpha p f)
    (h12 : C21_12 p f) (h13 : C21_13 p f) (h14 : C21_14 p f) (h15 : C21_15 p f)
    (hWyl : C21_WylTrans p f) (h17c : C21_17_cent p f) (hEc : C21_E_cent p f) :
    C21_2 p f :=
  c21_2_of_hyp51 p f hE (twinFrameHyp51_of_cases hHz hHt hHu) h4 h12 h13 h14 h15 hWyl h17c hEc

end Frames

end CFSG.ClassicalInvolution.Asc77
