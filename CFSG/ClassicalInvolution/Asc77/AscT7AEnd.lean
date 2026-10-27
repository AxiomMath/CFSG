module

public import CFSG.ClassicalInvolution.Asc77.AscT7AAlpha
public import CFSG.ClassicalInvolution.Asc77.WP2Thm8

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

@[expose] def sigmaStarNorm (Ω : Set (Subgroup G)) (K : Subgroup G) : Subgroup G where
  carrier := {g | ∀ M : Subgroup G, M ∈ dstarComp Ω K ↔ conjSub g M ∈ dstarComp Ω K}
  one_mem' := fun M => by rw [conjSub_one]
  mul_mem' := by
    intro g h hg hh M
    show M ∈ dstarComp Ω K ↔ conjSub (g * h) M ∈ dstarComp Ω K
    rw [conjSub_mul]
    exact (hh M).trans (hg _)
  inv_mem' := by
    intro g hg M
    have h := hg (conjSub g⁻¹ M)
    rw [conjSub_conjSub_inv] at h
    exact h.symm

theorem mem_sigmaStarNorm_iff {K : Subgroup G} {g : G} :
    g ∈ sigmaStarNorm Ω K ↔ ∀ M : Subgroup G, M ∈ dstarComp Ω K ↔ conjSub g M ∈ dstarComp Ω K :=
  Iff.rfl

theorem sigmaStarNorm_congr {K L : Subgroup G} (h : dstarComp Ω L = dstarComp Ω K) :
    sigmaStarNorm Ω L = sigmaStarNorm Ω K := by
  ext g
  rw [mem_sigmaStarNorm_iff, mem_sigmaStarNorm_iff, h]

namespace T7A

theorem mem_sigmaStarNorm_of_conj (hΩ : ConjInvariant Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {g : G} (hg : conjSub g K ∈ dstarComp Ω K) : g ∈ sigmaStarNorm Ω K := by
  intro M
  have hsym : K ∈ dstarComp Ω (conjSub g K) := (T3.mem_dstarComp_symm hK hg).2
  constructor
  · intro hM
    exact hg.trans (dstarComp_conj hΩ hM g)
  · intro hM
    have h1 : conjSub g M ∈ dstarComp Ω (conjSub g K) := hsym.trans hM
    have h2 := dstarComp_conj hΩ h1 g⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2

theorem centralizer_conj_le {H : Subgroup G} {z z'' y : G} (hy : y ∈ H)
    (hz'' : z'' = y * z * y⁻¹) (hz : Subgroup.centralizer ({z} : Set G) ≤ H) :
    Subgroup.centralizer ({z''} : Set G) ≤ H := by
  intro c hc
  have hc' : y⁻¹ * c * y ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [hz''] at hc
    calc (y⁻¹ * c * y) * z = y⁻¹ * (c * (y * z * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * z * y⁻¹) * c) * y := by rw [hc]
      _ = z * (y⁻¹ * c * y) := by group
  have h2 : y * (y⁻¹ * c * y) * y⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem hy (hz hc')) (H.inv_mem hy)
  have e : y * (y⁻¹ * c * y) * y⁻¹ = c := by group
  rwa [e] at h2

theorem mem_centralizer_conj {g c a : G} (hc : c ∈ Subgroup.centralizer ({a} : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  calc (g * c * g⁻¹) * (g * a * g⁻¹) = g * (c * a) * g⁻¹ := by group
    _ = g * (a * c) * g⁻¹ := by rw [hc]
    _ = (g * a * g⁻¹) * (g * c * g⁻¹) := by group

theorem mem_of_conj_mem {H : Subgroup G} {g c : G} (hg : g ∈ H) (hc : g * c * g⁻¹ ∈ H) :
    c ∈ H := by
  have h2 : g⁻¹ * (g * c * g⁻¹) * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) hc) hg
  have e : g⁻¹ * (g * c * g⁻¹) * g = c := by group
  rwa [e] at h2

theorem sup_le_normalizer_of_twin [Finite G] (hΩ : HypOmegaMod p f Ω) {K K' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) :=
  sup_le Subgroup.le_normalizer (hΩ.le_normalizer_of_twin hK' hK hne hz' hz)

theorem mem_sigmaStarNorm_of_mem_sup [Finite G] (hΩ : HypOmegaMod p f Ω) {K K' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) {g : G} (hg : g ∈ K ⊔ K') : g ∈ sigmaStarNorm Ω K := by
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp (sup_le_normalizer_of_twin hΩ hK hK' hne hz hz' hg)
  exact mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
    (by rw [hgK]; exact Relation.ReflTransGen.refl)

theorem dstarComp_eq_of_mem {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ dstarComp Ω K) :
    dstarComp Ω L = dstarComp Ω K := by
  ext M
  constructor
  · intro hM
    exact hL.trans hM
  · intro hM
    exact (T3.mem_dstarComp_symm hK hL).2.trans hM

theorem dComp_conj (hΩ : ConjInvariant Ω) {K J : Subgroup G} (h : J ∈ dComp Ω K) (g : G) :
    conjSub g J ∈ dComp Ω (conjSub g K) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hΩ g _ hbc.1, dAdj_conjSub hΩ hbc.2 g⟩

theorem dComp_eq_of_mem {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ dComp Ω K) :
    dComp Ω L = dComp Ω K := by
  ext M
  constructor
  · intro hM
    exact hL.trans hM
  · intro hM
    exact (reflTransGen_dAdj_symm hK hL).trans hM

theorem le_sigmaNorm_of_mem_dComp (hΩ : ConjInvariant Ω) {K M : Subgroup G} (hK : K ∈ Ω)
    (hM : M ∈ dComp Ω K) : M ≤ sigmaNorm Ω K := by
  intro a ha N
  have hMa : conjSub a M = M := mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer ha)
  have hKM : dComp Ω M = dComp Ω K := dComp_eq_of_mem hK hM
  constructor
  · intro hN
    have h1 : N ∈ dComp Ω M := by rw [hKM]; exact hN
    have h2 := dComp_conj hΩ h1 a
    rw [hMa, hKM] at h2
    exact h2
  · intro hN
    have h1 : conjSub a N ∈ dComp Ω (conjSub a M) := by rw [hMa, hKM]; exact hN
    have h2 := dComp_conj hΩ h1 a⁻¹
    rw [conjSub_inv_conjSub, conjSub_inv_conjSub, hKM] at h2
    exact h2

theorem sigmaGen_le_sigmaNorm (hΩ : ConjInvariant Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    sigmaGen Ω K ≤ sigmaNorm Ω K :=
  iSup₂_le fun _ hM => le_sigmaNorm_of_mem_dComp hΩ hK hM

end T7A

structure StdCentTail (Ω : Set (Subgroup G)) (K H : Subgroup G) (z : G) : Prop where
  nonTwin : ∀ L ∈ twinSet Ω K, ∀ J ∈ omegaNbr Ω L, ∀ z' : G, IsUniqueInvolution J z' →
    z' ≠ z → Subgroup.centralizer ({z * z'} : Set G) ≤ H
  twin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
    IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂, orderOf x = 4 →
      orderOf y = 4 → Subgroup.centralizer ({x * y} : Set G) ≤ H

section Finite

variable [Finite G]

theorem stdCent_sigmaStarNorm (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M)
    (htail : StdCentTail Ω K (sigmaStarNorm Ω K) z) : StdCent Ω K (sigmaStarNorm Ω K) z := by
  have hz_le : Subgroup.centralizer ({z} : Set G) ≤ sigmaStarNorm Ω K := by
    intro c hc
    have hcz : c * z * c⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
        _ = z := by group
    have hL : conjSub c K ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant c K hK, z, hz, hcz ▸ hz.conj c⟩
    exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
      (AscE186.mem_dstarComp_of_twin hp hΩ hK hL)
  refine ⟨hz_le, ?_, htail.twin⟩
  intro L hL J hJ z' hz' hzz
  have hKL := (l6_3 p f hp hq G Ω hΩ K hK L hL).1
  have hJperp : J ∈ KPerp Ω K := hKL ▸ Set.mem_insert_of_mem _ hJ
  have hnot : J ∉ twinSet Ω K := by
    rintro ⟨-, z₀, hz₀K, hz₀J⟩
    exact hzz ((hz₀J.eq hz').symm.trans (hz.eq hz₀K).symm)
  have hJΩ : J ∈ Ω := hJ.1
  have hJd : J ∈ dstarComp Ω K := by
    rcases Set.mem_insert_iff.mp hJperp with h | h
    · exact absurd (by rw [h]; exact mem_twinSet_self hK hz) hnot
    · exact Relation.ReflTransGen.single ⟨hJΩ, Or.inl (T3.omegaNbr_subset_omegaStarNbr hp hΩ K h)⟩
  obtain ⟨y, hy⟩ := htrans J hJΩ
  have hyH : y ∈ sigmaStarNorm Ω K :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hy ▸ hJd)
  have hzy : IsUniqueInvolution J (y * z * y⁻¹) := hy ▸ hz.conj y
  exact ⟨T7A.centralizer_conj_le hyH (hz'.eq hzy) hz_le, htail.nonTwin L hL J hJ z' hz' hzz⟩

theorem stdCentTail_of_frames (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K K' J W : Subgroup G} {z u t : G} (h : Hyp21 p f Ω K K' z u J t W)
    (hfr : ∀ {L L' J₁ W₁ : Subgroup G} {u₁ t₁ : G}, L ∈ twinSet Ω K →
      Hyp21 p f Ω L L' z u₁ J₁ t₁ W₁ →
        Subgroup.centralizer ({t₁ * z} : Set G) ≤ sigmaStarNorm Ω L ∧
          Subgroup.centralizer ({u₁} : Set G) ≤ sigmaStarNorm Ω L) :
    StdCentTail Ω K (sigmaStarNorm Ω K) z := by
  have hK : K ∈ Ω := h.std.stand.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hzK' := isUniqueInvolution_of_mem_twinSet h.std.hz h.std.hK'
  have hKK : K ∈ twinSet Ω K := mem_twinSet_self hK h.std.hz
  have hstar : ∀ {L : Subgroup G}, L ∈ twinSet Ω K → sigmaStarNorm Ω L = sigmaStarNorm Ω K :=
    fun {L} hL => sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK
      (AscE186.mem_dstarComp_of_twin hp hΩ hK hL))
  refine ⟨?_, ?_⟩
  · intro L hL J'' hJ'' z'' hz'' hzz
    have hKL := (l6_3 p f hp hq G Ω hΩ K hK L hL).1
    have hJperp : J'' ∈ KPerp Ω K := hKL ▸ Set.mem_insert_of_mem _ hJ''
    have hnot : J'' ∉ twinSet Ω K := by
      rintro ⟨-, z₀, hz₀K, hz₀J⟩
      exact hzz ((hz₀J.eq hz'').symm.trans (h.std.hz.eq hz₀K).symm)
    have hJmem : J'' ∈ omegaOfSet Ω (twinSet Ω K) :=
      T7A.mem_omegaOfSet_of_mem_kPerp hp hq hΩ hK hJperp hnot
    obtain ⟨g, hgQ, W₁, hfr', hW₁, hzW₁, htW₁⟩ :=
      exists_twinFrameData_at hp hq hΩ hK h.std.hz h.std.hK' h.std.hne h.hu h.hu2 h.hu1 h.huz
        hJmem hz''
    have h' : Hyp21 p f Ω K K' z u (conjSub g J'') (g * z'' * g⁻¹) W₁ :=
      Hyp21.of_twinFrameData h.std hfr' hW₁ hzW₁ htW₁
    have hcl := (hfr hKK h').1
    have hgH : g ∈ sigmaStarNorm Ω K :=
      T7A.mem_sigmaStarNorm_of_mem_sup hΩ hK hK'Ω h.std.hne h.std.hz hzK' hgQ
    have hgz : g * z * g⁻¹ = z := by
      have := T7A.z_comm_of_mem_sup h.std.hz hzK' hgQ
      calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
        _ = (z * g) * g⁻¹ := by rw [← this]
        _ = z := by group
    have hcomm : z * (g * z'' * g⁻¹) = (g * z'' * g⁻¹) * z := hfr'.comm_zt hp hΩ
    have e1 : (g * z'' * g⁻¹) * z = g * (z * z'') * g⁻¹ := by
      calc (g * z'' * g⁻¹) * z = z * (g * z'' * g⁻¹) := hcomm.symm
        _ = (g * z * g⁻¹) * (g * z'' * g⁻¹) := by rw [hgz]
        _ = g * (z * z'') * g⁻¹ := by group
    intro c hc
    refine T7A.mem_of_conj_mem hgH ?_
    have hc' := T7A.mem_centralizer_conj (g := g) hc
    rw [← e1] at hc'
    exact hcl hc'
  · intro L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy hx4 hy4
    have hLΩ : L ∈ Ω := hL.1
    have hzL := isUniqueInvolution_of_mem_twinSet h.std.hz hL
    have htwL : twinSet Ω L = twinSet Ω K := twinSet_eq_of_mem_twinSet h.std.hz hL
    have hL'L : L' ∈ twinSet Ω L := by rw [htwL]; exact hL'
    have hJL : J ∈ omegaOfSet Ω (twinSet Ω L) := by rw [htwL]; exact h.hJ
    obtain ⟨g, hgQ, W₂, hJg, htg, hW₂, hzW₂, htW₂, hfr'⟩ :=
      exists_twinFrameData_of_sylows hp hq hΩ hLΩ hzL hL'L hne hJL h.ht hR₁ hR₂ hc
    have hfr'' := hfr' x hx y hy hx4 hy4
    have h' : Hyp21 p f Ω L L' z (x * y) (conjSub g J) (g * t * g⁻¹) W₂ :=
      Hyp21.of_twinFrameData (Std7.of_twin h.std hL hL' hne) hfr'' hW₂ hzW₂ htW₂
    have := (hfr hL h').2
    rwa [hstar hL] at this

end Finite

section Alpha4

variable [Finite G] [IsSimpleGroup G]

omit [Finite G] [IsSimpleGroup G] in
theorem T7A.conjSub_sigmaGen_eq (hΩ : ConjInvariant Ω) {K : Subgroup G} (hK : K ∈ Ω) {g : G}
    (hg : conjSub g K ∈ dComp Ω K) (hg' : conjSub g⁻¹ K ∈ dComp Ω K) :
    conjSub g (sigmaGen Ω K) = sigmaGen Ω K := by
  have hmap : ∀ {g : G}, conjSub g K ∈ dComp Ω K → ∀ M ∈ dComp Ω K, conjSub g M ∈ dComp Ω K :=
    fun {g} hg M hM => by
      have := T7A.dComp_conj hΩ hM g
      rwa [T7A.dComp_eq_of_mem hK hg] at this
  unfold sigmaGen
  simp only [T7A.conjSub_iSup]
  apply le_antisymm
  · refine iSup_le fun M => iSup_le fun hM => ?_
    exact le_iSup₂_of_le (conjSub g M) (hmap hg M hM) le_rfl
  · refine iSup_le fun M => iSup_le fun hM => ?_
    have h1 : conjSub g⁻¹ M ∈ dComp Ω K := hmap hg' M hM
    exact le_iSup₂_of_le (conjSub g⁻¹ M) h1 (by rw [conjSub_conjSub_inv])

theorem c21_4_of (h3 : C21_3 p f) (h4 : TwinNormAlpha p f) : C21_4 p f := by
  intro G _ _ _ Ω K K' z u J t W h
  have hs : AlphaSteps p f := ⟨h3, h4⟩
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hKn : K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    h4 G Ω K K' z u J t W h K (mem_twinSet_self hK h.std.hz)
  refine ⟨fun M hM => ?_, fun c hc => ?_⟩
  · obtain ⟨x, hx⟩ := h.std.stand.trans M (T7A.mem_of_mem_dComp hK hM)
    have hxα := hs.conj_alpha_of_mem_dComp h M hM x hx
    have hxiα : conjSub x⁻¹ (alphaOf (Subgroup.closure ({u, z} : Set G))) =
        alphaOf (Subgroup.closure ({u, z} : Set G)) := by
      conv_lhs => rw [← hxα]
      rw [conjSub_inv_conjSub]
    intro m hm
    have hk : x⁻¹ * m * x ∈ K := by
      rw [← hx] at hm
      exact mem_conjSub_iff.mp hm
    have hkα := mem_normalizer_iff_conjSub_eq.mp (hKn hk)
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    have e : m = x * (x⁻¹ * m * x) * x⁻¹ := by group
    rw [e, conjSub_mul, conjSub_mul, hxiα, hkα, hxα]
  · have hcα := hs.conj_alpha_of_mem_centralizer h hc
    have hcz : c * z * c⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
        _ = z := by group
    have hcm : ∀ {d : G}, d * z * d⁻¹ = z → conjSub d K ∈ dComp Ω K := fun {d} hd =>
      T7A.mem_dComp_of_mem_kPerp
        (mem_kPerp_of_twin hΩ (hΩ.conjInvariant d K hK) hK
          (hd ▸ h.std.hz.conj d) h.std.hz)
    have hcz' : c⁻¹ * z * c⁻¹⁻¹ = z := by
      have h1 := congrArg (fun x => c⁻¹ * x * c) hcz
      simpa [mul_assoc] using h1.symm
    have hSig := T7A.conjSub_sigmaGen_eq hΩ.conjInvariant hK (hcm hcz) (hcm hcz')
    rw [T7A.conjSub_sup_eq, hcα, hSig]

end Alpha4

end CFSG.ClassicalInvolution.Asc77
