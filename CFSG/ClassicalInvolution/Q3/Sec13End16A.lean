module

public import CFSG.ClassicalInvolution.Q3.Sec13End15C
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23PfSetup
public import CFSG.ClassicalInvolution.Q3.Sec13EndDict
public import CFSG.ClassicalInvolution.Q3.Sec13EndS3E8

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem exists_omegaStarNbr_not_mem_sup (h : EndHyp Ω) (s : TwinSit Ω K K' z)
    (hE : ¬ eGroup Ω K ≤ K ⊔ K') :
    ∃ J ∈ omegaStarNbr Ω K, ∃ t : G, IsUniqueInvolution J t ∧ t ∉ K ⊔ K' := by
  by_contra hcon
  push Not at hcon
  apply hE
  unfold eGroup
  rw [Subgroup.closure_le]
  rintro u ⟨J, hJ, hu⟩
  rcases hJ with hJK | hJ
  · rw [hJK] at hu
    rw [hu.eq s.isInv]
    exact Subgroup.mem_sup_left s.isInv.mem
  · exact hcon J hJ u hu

theorem hyp23Setting (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z) :
    CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting Ω K K' z := by
  refine ⟨⟨h.thmD.hyp, h.cls, h.thmD.aEmpty, s.mem, h.thmD.trans K s.mem, h.thmD.gen, ?_, ?_⟩,
    h.disc, s.isInv, ?_, s.ne.symm, ?_⟩
  · intro J hJ P hP
    have hJP : J = P := hP.eq_of_le (h.thmD.two J hJ) le_rfl hP.1
    rw [← hJP]
    exact h.card_eq_eight hJ
  · intro J hJ N hN x hx
    exact hN x hx ((h.thmD.two J hJ).to_le (Subgroup.zpowers_le.mpr hx))
  · rw [s.twin]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · exact (h.kPerp_eq_twinSet_of_perp9 h9 s.mem).trans s.twin

section FrameCert


private theorem e16a3_isSylow2In_self {J : Subgroup G} (hJ : IsPGroup 2 J) : IsSylow2In J J :=
  ⟨le_rfl, hJ, fun _ hV' _ hJV' => le_antisymm hV' hJV'⟩

private theorem e16a3_cases {W : Subgroup G} (c : CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx Ω W)
    (F : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.Frame4 Ω W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) (σ : Thompson.Rep Ω W) :
    σ.K = F.ρ.K ∨ σ.K = F.ρ'.K ∨ σ.K = F.ρ₃.K ∨ σ.K = conjSub F.ρ.r F.ρ₃.K ∨
      σ.K = conjSub F.ρ'.r F.ρ₃.K ∨ σ.K = conjSub (F.ρ.r * F.ρ'.r) F.ρ₃.K := by
  have hsq : ∀ ρ : Thompson.Rep Ω W, ρ.img * ρ.img = 1 := fun ρ =>
    congrArg Subtype.val
      (CFSG.ClassicalInvolution.Q3.Q3T6.Mu.muDelta_mul_self c.hΩ c.hW (T7D.imgQ_mem ρ))
  have hinv : ∀ ρ : Thompson.Rep Ω W, ρ.img⁻¹ = ρ.img := fun ρ =>
    inv_eq_of_mul_eq_one_right (hsq ρ)
  rcases T7E.swap_word_cases he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem F.ρ') (T7D.imgQ_mem F.ρ₃)
    hab hcomm hac (T7D.imgQ_mem σ) with h | h | h | h | h | h
  · exact Or.inl (c.K_eq_of_img_eq σ F.ρ (congrArg Subtype.val h))
  · exact Or.inr (Or.inl (c.K_eq_of_img_eq σ F.ρ' (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inl (c.K_eq_of_img_eq σ F.ρ₃ (congrArg Subtype.val h))))
  · have e1 : σ.img = F.ρ.img * F.ρ₃.img * F.ρ.img := congrArg Subtype.val h
    have hm : F.ρ.r ∈ Subgroup.normalizer (W : Set G) := F.ρ.r_mem_normalizer
    have hval : σ.img = Thompson.piG W F.ρ.r * F.ρ₃.img * (Thompson.piG W F.ρ.r)⁻¹ := by
      show σ.img = F.ρ.img * F.ρ₃.img * F.ρ.img⁻¹
      rw [hinv]
      exact e1
    exact Or.inr (Or.inr (Or.inr (Or.inl (c.K_eq_of_img_eq σ
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.conjRep c.hΩ hm F.ρ₃)
      (by rw [CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.conjRep_img]; exact hval)))))
  · have e1 : σ.img = F.ρ'.img * F.ρ₃.img * F.ρ'.img := congrArg Subtype.val h
    have hm : F.ρ'.r ∈ Subgroup.normalizer (W : Set G) := F.ρ'.r_mem_normalizer
    have hval : σ.img = Thompson.piG W F.ρ'.r * F.ρ₃.img * (Thompson.piG W F.ρ'.r)⁻¹ := by
      show σ.img = F.ρ'.img * F.ρ₃.img * F.ρ'.img⁻¹
      rw [hinv]
      exact e1
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (c.K_eq_of_img_eq σ
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.conjRep c.hΩ hm F.ρ₃)
      (by rw [CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.conjRep_img]; exact hval))))))
  · have e1 : σ.img = F.ρ.img * F.ρ'.img * F.ρ₃.img * F.ρ'.img * F.ρ.img :=
      congrArg Subtype.val h
    have hm : F.ρ.r * F.ρ'.r ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.mul_mem _ F.ρ.r_mem_normalizer F.ρ'.r_mem_normalizer
    have hpm : Thompson.piG W (F.ρ.r * F.ρ'.r) = F.ρ.img * F.ρ'.img :=
      Thompson.piG_mul F.ρ.r_mem_normalizer F.ρ'.r_mem_normalizer
    have hval : σ.img = Thompson.piG W (F.ρ.r * F.ρ'.r) * F.ρ₃.img *
        (Thompson.piG W (F.ρ.r * F.ρ'.r))⁻¹ := by
      rw [hpm, mul_inv_rev, hinv, hinv, e1]
      simp only [mul_assoc]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (c.K_eq_of_img_eq σ
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.conjRep c.hΩ hm F.ρ₃)
      (by rw [CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.conjRep_img]; exact hval))))))

theorem exists_wSet_centerIn_ne_bot (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {J : Subgroup G} {t : G} (hJ : J ∈ omegaStarNbr Ω K)
    (ht : IsUniqueInvolution J t) (htK : t ∉ K ⊔ K') :
    ∃ W ∈ WSet Ω, z ∈ W ∧ K ∈ DSet Ω W ∧ J ∈ DSet Ω W ∧
      W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) ≠ ⊥ := by
  obtain ⟨W, hW, hzW, hKW, hJW⟩ := h.exists_wSet_of_mem_omegaStarNbr s.mem hJ s.isInv
  refine ⟨W, hW, hzW, hKW, hJW, ?_⟩
  have hS4 : MuIsoS4 Ω W :=
    h.muIsoS4_of_twinSet_pair (fun L hL => h.kPerp_eq_twinSet_of_perp9 h9 hL) hW hKW s.twin s.ne
  have hs := hyp23Setting h h9 s
  obtain ⟨e, F, he, hρK, hρ'K, hFz, hab, hcomm, hac, -⟩ :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.exists_frame4 hs hW hzW hS4
  have hst := hs.stand
  have hΩ : HypOmegaGen Ω := hst.hyp
  have c : CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx Ω W :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.ctx_of_stand hst hW
  have hcl : Fact (CFSG.ClassicalInvolution.Q3.Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.Frame4.exists_gens c F
  obtain ⟨m, hm, o₁, o₂, o₃, z₁, z₂, z₃⟩ :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.Frame4.orders c F h₁ h₂ h₃
  have hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.Frame4.W_le_closure c F he hab hcomm hac
      h₁ h₂ h₃ r₂ r₃ t₃
  have m₁ : x₁ ∈ W := (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2
  have m₂ : x₂ ∈ W := (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2
  have m₃ : x₃ ∈ W := (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2
  have k₁ : x₁ ∈ K := by
    have := F.ρ.hRK.1 (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).1
    rwa [hρK] at this
  have k₂ : x₂ ∈ K' := by
    have := F.ρ'.hRK.1 (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).1
    rwa [hρ'K] at this
  have c12 : Commute x₁ x₂ := c.comm_W _ m₁ _ m₂
  have c13 : Commute x₁ x₃ := c.comm_W _ m₁ _ m₃
  have c23 : Commute x₂ x₃ := c.comm_W _ m₂ _ m₃
  have hz12 : x₁ ^ (2 * m) = x₂ ^ (2 * m) := z₁.trans z₂.symm
  have o₃' : x₃ ^ (4 * m) = 1 := by rw [← o₃]; exact pow_orderOf_eq_one x₃
  have enf : (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m = x₁ ^ (m : ℤ) * x₂ ^ (-(m : ℤ)) * x₃ ^ (2 * (m : ℤ)) := by
    have h := A3Mod.pow_triple c12 c13 c23 (m : ℤ)
    rwa [zpow_natCast (x₁ * x₂⁻¹ * x₃ ^ 2) m] at h
  have hx2 : x₂ ^ (4 * (m : ℤ)) = 1 := by
    rw [show (4 * (m : ℤ)) = ((4 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← o₂,
      pow_orderOf_eq_one]
  have hx3 : x₃ ^ (4 * (m : ℤ)) = 1 := by
    rw [show (4 * (m : ℤ)) = ((4 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← o₃,
      pow_orderOf_eq_one]
  have he₄W : (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m ∈ W :=
    W.pow_mem (W.mul_mem (W.mul_mem m₁ (W.inv_mem m₂)) (W.pow_mem m₃ 2)) m
  have fr : F.ρ.r * (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m * F.ρ.r⁻¹ = (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m := by
    rw [enf, A3Mod.conj_nf_r c12 c13 r₁ r₂ r₃ (m : ℤ) (-(m : ℤ)) (2 * (m : ℤ)),
      show (2 * (m : ℤ) - (m : ℤ)) = (m : ℤ) by ring]
  have ft : F.ρ'.r * (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m * F.ρ'.r⁻¹ = (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m := by
    rw [enf, A3Mod.conj_nf_t c23 t₁ t₂ t₃ (m : ℤ) (-(m : ℤ)) (2 * (m : ℤ)),
      show (2 * (m : ℤ) - -(m : ℤ)) = -(m : ℤ) + 4 * (m : ℤ) by ring,
      zpow_add x₂ (-(m : ℤ)) (4 * (m : ℤ)), hx2, mul_one]
  have fs : F.ρ₃.r * (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m * F.ρ₃.r⁻¹ = (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m := by
    rw [enf, A3Mod.conj_nf_s c13 c23 s₁ s₂ s₃ (m : ℤ) (-(m : ℤ)) (2 * (m : ℤ)),
      show ((m : ℤ) + -(m : ℤ) - 2 * (m : ℤ)) = 2 * (m : ℤ) + -(4 * (m : ℤ)) by ring,
      zpow_add x₃ (2 * (m : ℤ)) (-(4 * (m : ℤ))), zpow_neg x₃ (4 * (m : ℤ)), hx3, inv_one,
      mul_one]
  have hzK : F.z ∈ K ⊔ K' := by
    rw [hFz]
    exact Subgroup.mem_sup_left s.isInv.mem
  have hrz : F.ρ.r * F.z * F.ρ.r⁻¹ = F.z := by
    rw [← z₁, ← conj_pow, r₁, inv_pow, z₁, inv_eq_of_mul_eq_one_right F.hz.sq]
  have hrj : F.ρ.r * F.j * F.ρ.r⁻¹ = F.j * F.z := by
    rw [← z₃, ← z₁, ← conj_pow, r₃, (c13.symm.mul_pow _)]
  have hr'j : F.ρ'.r * F.j * F.ρ'.r⁻¹ = F.j * F.z := by
    rw [← z₃, ← z₂, ← conj_pow, t₃, (c23.symm.mul_pow _)]
  have hrrj : (F.ρ.r * F.ρ'.r) * F.j * (F.ρ.r * F.ρ'.r)⁻¹ = F.j := by
    calc (F.ρ.r * F.ρ'.r) * F.j * (F.ρ.r * F.ρ'.r)⁻¹
        = F.ρ.r * (F.ρ'.r * F.j * F.ρ'.r⁻¹) * F.ρ.r⁻¹ := by group
      _ = F.ρ.r * (F.j * F.z) * F.ρ.r⁻¹ := by rw [hr'j]
      _ = (F.ρ.r * F.j * F.ρ.r⁻¹) * (F.ρ.r * F.z * F.ρ.r⁻¹) := by group
      _ = (F.j * F.z) * F.z := by rw [hrj, hrz]
      _ = F.j := by rw [mul_assoc, F.hz.sq, mul_one]
  have hjK : F.j ∉ K ⊔ K' := by
    intro hjs
    obtain ⟨σ, hσK, -⟩ := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_rep hΩ hW hJ.1
      (e16a3_isSylow2In_self (h.thmD.two J hJ.1)) hJW
    rcases e16a3_cases c F he hab hcomm hac σ with hc | hc | hc | hc | hc | hc
    · have hJz : IsUniqueInvolution J z := by
        rw [← hσK, hc, hρK]
        exact s.isInv
      exact htK (by rw [ht.eq hJz]; exact Subgroup.mem_sup_left s.isInv.mem)
    · have hJz : IsUniqueInvolution J z := by
        rw [← hσK, hc, hρ'K]
        exact s.mem_twin.2
      exact htK (by rw [ht.eq hJz]; exact Subgroup.mem_sup_left s.isInv.mem)
    · have hJj : IsUniqueInvolution J F.j := by
        rw [← hσK, hc]
        exact F.hj
      exact htK (by rw [ht.eq hJj]; exact hjs)
    · have hJj : IsUniqueInvolution J (F.ρ.r * F.j * F.ρ.r⁻¹) := by
        rw [← hσK, hc]
        exact F.hj.conj F.ρ.r
      exact htK (by rw [ht.eq hJj, hrj]; exact Subgroup.mul_mem _ hjs hzK)
    · have hJj : IsUniqueInvolution J (F.ρ'.r * F.j * F.ρ'.r⁻¹) := by
        rw [← hσK, hc]
        exact F.hj.conj F.ρ'.r
      exact htK (by rw [ht.eq hJj, hr'j]; exact Subgroup.mul_mem _ hjs hzK)
    · have hJj : IsUniqueInvolution J ((F.ρ.r * F.ρ'.r) * F.j * (F.ρ.r * F.ρ'.r)⁻¹) := by
        rw [← hσK, hc]
        exact F.hj.conj (F.ρ.r * F.ρ'.r)
      exact htK (by rw [ht.eq hJj, hrrj]; exact hjs)
  have he₄1 : (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m ≠ 1 := by
    intro h1
    have hu : x₁ ^ m * (x₂ ^ m)⁻¹ ∈ K ⊔ K' :=
      Subgroup.mul_mem_sup (K.pow_mem k₁ m) (K'.inv_mem (K'.pow_mem k₂ m))
    have hue := (A3Mod.triple_facts c12 c13 c23 o₃' hz12).2.2
    rw [h1, mul_one, z₃] at hue
    exact hjK (by rw [← hue]; exact hu)
  have hfixD : ∀ R₀ : Subgroup G, R₀ ∈ DSet Ω W → ∀ r : G, r ∈ R₀ →
      r * (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m * r⁻¹ = (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m := fun R₀ hR₀ r hr =>
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7C2.fixed_of_frame c he F hab hcomm hac he₄W
      fr ft fs hR₀ hr
  have hcent : ∀ n ∈ Subgroup.normalizer (W : Set G),
      n * (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m * n⁻¹ = (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m := by
    intro n hn
    have hn' : n⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hn
    have hnW : n * (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m * n⁻¹ ∈ W :=
      (Thompson.mem_normalizer_iff_of_mem hn _).mpr he₄W
    have hfixc : ∀ σ' : Thompson.Rep Ω W,
        σ'.r * (n * (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m * n⁻¹) * σ'.r⁻¹ =
          n * (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m * n⁻¹ := by
      intro σ'
      have hmemD : n⁻¹ * σ'.r * n ∈ conjSub n⁻¹ σ'.R := by
        rw [mem_conjSub_iff]
        have h1 : (n⁻¹)⁻¹ * (n⁻¹ * σ'.r * n) * n⁻¹ = σ'.r := by group
        rw [h1]
        exact σ'.hr
      have hD := hfixD _ (CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.conjSub_mem_D c.hΩ σ'.hR hn')
        _ hmemD
      calc σ'.r * (n * (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m * n⁻¹) * σ'.r⁻¹
          = n * ((n⁻¹ * σ'.r * n) * (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m * (n⁻¹ * σ'.r * n)⁻¹) * n⁻¹ := by
            group
        _ = n * (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m * n⁻¹ := by rw [hD]
    rcases A3Mod.fixed_eq_one_or c12 c13 c23 o₁ o₂ o₃ hz12 r₁ r₂ r₃ t₁ t₂ t₃ s₁ s₂ s₃
        (hgen hnW) (hfixc F.ρ) (hfixc F.ρ') (hfixc F.ρ₃) with h1 | h1
    · exact absurd (conj_eq_one_iff.mp h1) he₄1
    · exact h1
  have hmemC : (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m ∈ Asc77.centerIn (Subgroup.normalizer (W : Set G)) :=
    CFSG.ClassicalInvolution.Asc77.T7C2.mem_centerIn_of_forall (Subgroup.le_normalizer he₄W) hcent
  intro hbot
  have hmem : (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) :=
    ⟨he₄W, hmemC⟩
  rw [hbot] at hmem
  exact he₄1 (Subgroup.mem_bot.mp hmem)

end FrameCert

end EndHyp

structure Sit16 (Ω : Set (Subgroup G)) (K K' W : Subgroup G) (z u e g : G) : Prop where
  twin : TwinSit Ω K K' z
  data : Hyp23bData Ω K K' W z u e g
  e_not_mem : e ∉ K ⊔ K'

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

section FrameCert


private theorem e16a3_mem_sup_decomp {K K' : Subgroup G} (hc : Commutes K K') {x : G}
    (hx : x ∈ K ⊔ K') : ∃ k ∈ K, ∃ k' ∈ K', x = k * k' := by
  let P : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ k' ∈ K', x = k * k'}
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, k₁', hk₁', rfl⟩ ⟨k₂, hk₂, k₂', hk₂', rfl⟩
        refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, k₁' * k₂', K'.mul_mem hk₁' hk₂', ?_⟩
        have e := hc k₂ hk₂ k₁' hk₁'
        calc k₁ * k₁' * (k₂ * k₂') = k₁ * (k₁' * k₂) * k₂' := by group
          _ = k₁ * (k₂ * k₁') * k₂' := by rw [← e]
          _ = k₁ * k₂ * (k₁' * k₂') := by group
      one_mem' := ⟨1, K.one_mem, 1, K'.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, hk, k', hk', rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, k'⁻¹, K'.inv_mem hk', ?_⟩
        have e := hc k hk k' hk'
        calc (k * k')⁻¹ = k'⁻¹ * k⁻¹ := by group
          _ = k⁻¹ * k'⁻¹ := by
            have e' : (k' * k)⁻¹ = (k * k')⁻¹ := by rw [e]
            rw [mul_inv_rev, mul_inv_rev] at e'
            exact e'.symm }
  have hle : K ⊔ K' ≤ P := by
    refine sup_le (fun k hk => ⟨k, hk, 1, K'.one_mem, by simp⟩)
      (fun k' hk' => ⟨1, K.one_mem, k', hk', by simp⟩)
  exact hle hx

private theorem e16a3_eq_z_of_mem_sup (h : EndHyp Ω) (s : TwinSit Ω K K' z) {e : G}
    (he1 : e ≠ 1) (heKK : e ∈ K ⊔ K') (hcK : ∀ x ∈ K, e * x = x * e)
    (hcK' : ∀ x ∈ K', e * x = x * e) : e = z := by
  have hzK : IsUniqueInvolution K z := s.isInv
  have hzK' : IsUniqueInvolution K' z := s.mem_twin.2
  have hcomm : Commutes K K' := s.commutes h
  have hcen : ∀ (L : Subgroup G), L ∈ Ω → IsUniqueInvolution L z →
      ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1 ∨ x = z := fun L hL hzL x hx hc =>
    hzL.unique x hx ((h.isQuatSub_of_mem hL).sq_eq_one_of_central hx hc)
  obtain ⟨k, hk, k', hk', hke⟩ := e16a3_mem_sup_decomp hcomm heKK
  have hk'K : ∀ x ∈ K, k' * x = x * k' := fun x hx => (hcomm x hx k' hk').symm
  have hkK : ∀ x ∈ K, k * x = x * k := by
    intro x hx
    have ce : Commute e x := hcK x hx
    have ck' : Commute k' x := hk'K x hx
    have hk_eq : k = e * k'⁻¹ := by rw [hke]; group
    rw [hk_eq]
    exact (ce.mul_left ck'.inv_left)
  have hkK' : ∀ y ∈ K', k * y = y * k := fun y hy => hcomm k hk y hy
  have hk'K' : ∀ y ∈ K', k' * y = y * k' := by
    intro y hy
    have ce : Commute e y := hcK' y hy
    have ck : Commute k y := hkK' y hy
    have hk'_eq : k' = k⁻¹ * e := by rw [hke]; group
    rw [hk'_eq]
    exact (ck.inv_left.mul_left ce)
  rcases hcen K s.mem hzK k hk hkK with h1 | h1 <;>
    rcases hcen K' s.mem_twin.1 hzK' k' hk' hk'K' with h2 | h2
  · exfalso
    apply he1
    rw [hke, h1, h2, one_mul]
  · rw [hke, h1, h2, one_mul]
  · rw [hke, h1, h2, mul_one]
  · exfalso
    apply he1
    rw [hke, h1, h2, hzK.sq]

theorem exists_sit16 (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : ¬ eGroup Ω K ≤ K ⊔ K') :
    ∃ (W : Subgroup G) (u e g : G), Sit16 Ω K K' W z u e g := by
  obtain ⟨J, hJ, t, ht, htK⟩ := h.exists_omegaStarNbr_not_mem_sup s hE
  obtain ⟨W, hW, hzW, hKW, -, hWc⟩ := exists_wSet_centerIn_ne_bot h h9 s h13 hJ ht htK
  have hS4 : MuIsoS4 Ω W :=
    h.muIsoS4_of_twinSet_pair (fun L hL => h.kPerp_eq_twinSet_of_perp9 h9 hL) hW hKW s.twin
      s.ne
  obtain ⟨u, e, g, hdata⟩ :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.exists_data (hyp23Setting h h9 s) hW
      hS4 hWc hzW
  refine ⟨W, u, e, g, ⟨s, hdata, ?_⟩⟩
  intro heKK
  have heC : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := by
    rw [← hdata.he]
    exact Subgroup.subset_closure (Set.mem_singleton e)
  have hcenN : ∀ n ∈ Subgroup.normalizer (W : Set G), n * e = e * n := fun n hn =>
    CFSG.ClassicalInvolution.Asc77.T7E.Frame4.commutes_of_mem_centerIn heC.2 hn
  have hK'W : K' ∈ DSet Ω W := h.mem_dSet_of_mem hW s.mem_twin.1 s.mem_twin.2 hzW
  have hcenK : ∀ x ∈ K, e * x = x * e := fun x hx =>
    (hcenN x (hKW.2 hx)).symm
  have hcenK' : ∀ x ∈ K', e * x = x * e := fun x hx =>
    (hcenN x (hK'W.2 hx)).symm
  have he_z : e = z := e16a3_eq_z_of_mem_sup h s hdata.he1 heKK hcenK hcenK'
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := by
    have hle : (⨆ R ∈ DSet Ω W, R : Subgroup G) ≤ Subgroup.normalizer (W : Set G) :=
      iSup₂_le (fun R hR x hx => hR.2 hx)
    exact hle hdata.hg
  have hgc : g * z = z * g := by
    have := hcenN g hgN
    rw [he_z] at this
    exact this
  have hgz : g * z * g⁻¹ = z := by
    rw [hgc]
    group
  have huz : u * z = z := by
    have hgt := hdata.hgt
    rw [he_z, hgz] at hgt
    exact hgt.symm
  exact hdata.hu1 (mul_right_cancel (a := u) (b := z) (c := 1) (by rw [one_mul]; exact huz))

end FrameCert

end EndHyp

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

private theorem e16a2_isSylow2In_self (h : EndHyp Ω) {L : Subgroup G} (hL : L ∈ Ω) :
    IsSylow2In L L :=
  ⟨le_rfl, h.thmD.two L hL, fun _ hVL _ hLV => le_antisymm hVL hLV⟩

private theorem e16a2_eq_of_between {A B C : Subgroup G} (hAC : A ≤ C) (hCB : C ≤ B)
    (hA : Nat.card A = 4) (hB : Nat.card B = 8) (hne : C ≠ B) : C = A := by
  have hdvd : Nat.card A ∣ Nat.card C := Subgroup.card_dvd_of_le hAC
  have hle : Nat.card C ≤ Nat.card B := Subgroup.card_le_of_le hCB
  have hne8 : Nat.card C ≠ 8 := fun h8 => hne (Subgroup.eq_of_le_of_card_ge hCB (by omega))
  have hpos : 0 < Nat.card C := Nat.card_pos
  rw [hA] at hdvd
  have hC4 : Nat.card C = 4 := by omega
  exact (Subgroup.eq_of_le_of_card_ge hAC (by omega)).symm

private theorem e16a2_mem_zpowers_of_comm {L : Subgroup G} (hq : IsQuatSub L)
    (hL8 : Nat.card L = 8) {x : G} (hxL : x ∈ L) (hxo : orderOf x = 4) {k : G} (hkL : k ∈ L)
    (hk : k * x = x * k) : k ∈ Subgroup.zpowers x := by
  have hzC : Subgroup.zpowers x ≤ L ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨hxL, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hne : L ⊓ Subgroup.centralizer ({x} : Set G) ≠ L := by
    intro hCeq
    have hcomm : ∀ y ∈ L, x * y = y * x := by
      intro y hy
      have hyC : y ∈ L ⊓ Subgroup.centralizer ({x} : Set G) := by
        rw [hCeq]
        exact hy
      exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hyC).2).symm
    have hsq : x * x = 1 := hq.sq_eq_one_of_central hxL hcomm
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    rw [hxo] at hdvd
    omega
  have hC : L ⊓ Subgroup.centralizer ({x} : Set G) = Subgroup.zpowers x :=
    e16a2_eq_of_between hzC inf_le_left (by rw [Nat.card_zpowers, hxo]) hL8 hne
  have hkC : k ∈ L ⊓ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hkL, Subgroup.mem_centralizer_singleton_iff.mpr hk⟩
  rw [hC] at hkC
  exact hkC

private theorem e16a2_sq_eq_of_orderOf_four {L : Subgroup G} {t : G}
    (ht : IsUniqueInvolution L t) {x : G} (hx : x ∈ L) (hxo : orderOf x = 4) : x * x = t := by
  have hsq : (x * x) * (x * x) = 1 := by
    calc (x * x) * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hne : x * x ≠ 1 := by
    intro h1
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    rw [hxo] at hdvd
    omega
  rcases ht.unique (x * x) (L.mul_mem hx hx) hsq with h1 | h1
  · exact absurd h1 hne
  · exact h1

private theorem e16a2_orderOf_four {x z : G} (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hxx : x * x = z) : orderOf x = 4 := by
  have h1 : ¬ x ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, hxx]
    exact hz1
  have h2 : x ^ 2 ^ (1 + 1) = 1 := by
    have h4 : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
    rw [h4]
    calc x ^ 4 = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hxx, hzz]
  exact (orderOf_eq_prime_pow h1 h2).trans (by norm_num)

private theorem e16a2_zpow_mul_self {x z : G} (hxx : x * x = z) (m : ℤ) :
    x ^ m * x ^ m = z ^ m := by
  calc x ^ m * x ^ m = x ^ (m + m) := (zpow_add x m m).symm
    _ = x ^ (2 * m) := by congr 1; ring
    _ = (x ^ (2 : ℤ)) ^ m := zpow_mul x 2 m
    _ = (x * x) ^ m := by rw [zpow_two]
    _ = z ^ m := by rw [hxx]

private theorem e16a2_zpow_two_mul {x z : G} (hxx : x * x = z) (a : ℤ) :
    x ^ (2 * a) = z ^ a := by
  rw [zpow_mul, zpow_two, hxx]

private theorem e16a2_mem_sup_decomp {K K' : Subgroup G} (hc : Commutes K K') {x : G}
    (hx : x ∈ K ⊔ K') : ∃ k ∈ K, ∃ k' ∈ K', x = k * k' := by
  let P : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ k' ∈ K', x = k * k'}
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, k₁', hk₁', rfl⟩ ⟨k₂, hk₂, k₂', hk₂', rfl⟩
        refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, k₁' * k₂', K'.mul_mem hk₁' hk₂', ?_⟩
        have e := hc k₂ hk₂ k₁' hk₁'
        calc k₁ * k₁' * (k₂ * k₂') = k₁ * (k₁' * k₂) * k₂' := by group
          _ = k₁ * (k₂ * k₁') * k₂' := by rw [← e]
          _ = k₁ * k₂ * (k₁' * k₂') := by group
      one_mem' := ⟨1, K.one_mem, 1, K'.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, hk, k', hk', rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, k'⁻¹, K'.inv_mem hk', ?_⟩
        have e := hc k hk k' hk'
        calc (k * k')⁻¹ = k'⁻¹ * k⁻¹ := by group
          _ = k⁻¹ * k'⁻¹ := by
            have e' : (k' * k)⁻¹ = (k * k')⁻¹ := by rw [e]
            rw [mul_inv_rev, mul_inv_rev] at e'
            exact e'.symm }
  have hle : K ⊔ K' ≤ P := by
    refine sup_le (fun k hk => ⟨k, hk, 1, K'.one_mem, by simp⟩)
      (fun k' hk' => ⟨1, K.one_mem, k', hk', by simp⟩)
  exact hle hx

private theorem e16a2_isQuatSub (h : EndHyp Ω) {L : Subgroup G} (hL : L ∈ Ω) : IsQuatSub L :=
  Sec6Gen.isQuatSub_of_mem_RSet h.thmD.hyp (TC.mem_RSet_of_isPGroup hL (h.thmD.two L hL))

private theorem e16a2_exists_orderOf_four {A : Subgroup G} [IsCyclic A] (hA : Nat.card A = 4) :
    ∃ x ∈ A, orderOf x = 4 := by
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥A)
  refine ⟨(g₀ : G), g₀.2, ?_⟩
  rw [Subgroup.orderOf_coe, hg₀, hA]

private theorem e16a2_he (c : Sit16 Ω K K' W z u e g) :
    e ∈ W ⊓ CFSG.ClassicalInvolution.Asc77.centerIn (Subgroup.normalizer (W : Set G)) := by
  rw [← c.data.he]
  exact Subgroup.subset_closure (Set.mem_singleton e)

theorem mem_zGroup_of_mem_inf (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) {v : G} (hv : v ∈ W ⊓ (K ⊔ K')) (hv2 : v * v = 1) :
    v ∈ zGroup Ω := by
  have hs : TwinSit Ω K K' z := c.twin
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x :=
    Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have hDN : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hDab : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := h.zGroup_comm h9
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hs.mem, hs.isInv⟩
  have hz1 : z ≠ 1 := hs.isInv.ne_one
  have hzz : z * z = 1 := hs.isInv.sq
  have hK8 : Nat.card K = 8 := h.card_eq_eight hs.mem
  have hK'8 : Nat.card K' = 8 := h.card_eq_eight hs.mem_twin.1
  have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem hd.hW hs.mem hs.isInv hd.hzW
  have hK'D : K' ∈ DSet Ω W := h.mem_dSet_of_mem hd.hW hs.mem_twin.1 hs.mem_twin.2 hd.hzW
  have hKW := Q3CL.Thompson.inf_W_of_mem_D hΩ hd.hW hKD hs.mem (e16a2_isSylow2In_self h hs.mem)
  have hK'W := Q3CL.Thompson.inf_W_of_mem_D hΩ hd.hW hK'D hs.mem_twin.1
    (e16a2_isSylow2In_self h hs.mem_twin.1)
  have hKW4 : Nat.card ↥(K ⊓ W) = 4 := by have := hKW.2.2.2.2; omega
  have hK'W4 : Nat.card ↥(K' ⊓ W) = 4 := by have := hK'W.2.2.2.2; omega
  haveI : IsCyclic ↥(K ⊓ W) := hKW.2.2.1
  obtain ⟨x₁, hx₁A, hx₁o⟩ := e16a2_exists_orderOf_four hKW4
  have hx₁K : x₁ ∈ K := (Subgroup.mem_inf.mp hx₁A).1
  have hx₁W : x₁ ∈ W := (Subgroup.mem_inf.mp hx₁A).2
  have hx₁sq : x₁ * x₁ = z := e16a2_sq_eq_of_orderOf_four hs.isInv hx₁K hx₁o
  obtain ⟨d₀, hd₀D, hsw⟩ := h.exists_mem_zGroup_swap h9 hs h13
  have hd₀z : d₀ * z = z * d₀ := hDab d₀ hd₀D z hzD
  obtain ⟨y, hydef⟩ : ∃ y : G, y = d₀ * x₁ * d₀⁻¹ := ⟨_, rfl⟩
  have hyK' : y ∈ K' := by
    rw [hydef, ← hsw]
    exact conj_mem_conjSub hx₁K
  have hyy : y * y = z := by
    rw [hydef]
    calc d₀ * x₁ * d₀⁻¹ * (d₀ * x₁ * d₀⁻¹) = d₀ * (x₁ * x₁) * d₀⁻¹ := by group
      _ = d₀ * z * d₀⁻¹ := by rw [hx₁sq]
      _ = z := by rw [hd₀z]; group
  have hyo : orderOf y = 4 := e16a2_orderOf_four hz1 hzz hyy
  have heW : e ∈ W := (Subgroup.mem_inf.mp (e16a2_he c)).1
  have htW : u * e ∈ W := W.mul_mem hd.huW heW
  have htD : u * e ∈ zGroup Ω := by
    have hc := hDN.conj_mem z hzD g
    rw [hd.hgt] at hc
    exact hc
  have htz : u * e ≠ z := by
    intro hEq
    apply c.e_not_mem
    have he' : e = u⁻¹ * (u * e) := by group
    rw [he', hEq]
    exact (K ⊔ K').mul_mem ((K ⊔ K').inv_mem hd.hu) (Subgroup.mem_sup_left hs.isInv.mem)
  have htC : u * e ∉ Subgroup.centralizer (K : Set G) := by
    intro hC
    exact htz (h.eq_of_conj_mem_centralizer h9 hs ⟨g, hd.hgt.symm⟩ hC)
  have htK' : u * e ∉ Subgroup.centralizer (K' : Set G) := by
    intro hC
    apply htC
    have hmem : u * e ∈ zGroup Ω ⊓ Subgroup.centralizer (K' : Set G) :=
      Subgroup.mem_inf.mpr ⟨htD, hC⟩
    rw [h.inf_centralizer_twin_eq h9 hs h13] at hmem
    exact (Subgroup.mem_inf.mp hmem).2
  have hKC : K ⊓ Subgroup.centralizer ({u * e} : Set G) = K ⊓ W := by
    have hle : K ⊓ W ≤ K ⊓ Subgroup.centralizer ({u * e} : Set G) := by
      intro k hk
      obtain ⟨hkK, hkW⟩ := Subgroup.mem_inf.mp hk
      exact Subgroup.mem_inf.mpr ⟨hkK, Subgroup.mem_centralizer_singleton_iff.mpr
        (hWab k hkW _ htW)⟩
    refine e16a2_eq_of_between hle inf_le_left hKW4 hK8 ?_
    intro hEq
    apply htC
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : k ∈ K ⊓ Subgroup.centralizer ({u * e} : Set G) := by
      rw [hEq]
      exact hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hk').2
  have hK'C : K' ⊓ Subgroup.centralizer ({u * e} : Set G) = K' ⊓ W := by
    have hle : K' ⊓ W ≤ K' ⊓ Subgroup.centralizer ({u * e} : Set G) := by
      intro k hk
      obtain ⟨hkK, hkW⟩ := Subgroup.mem_inf.mp hk
      exact Subgroup.mem_inf.mpr ⟨hkK, Subgroup.mem_centralizer_singleton_iff.mpr
        (hWab k hkW _ htW)⟩
    refine e16a2_eq_of_between hle inf_le_left hK'W4 hK'8 ?_
    intro hEq
    apply htK'
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : k ∈ K' ⊓ Subgroup.centralizer ({u * e} : Set G) := by
      rw [hEq]
      exact hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hk').2
  have hyW : y ∈ W := by
    have hc1 : Commute d₀ (u * e) := hDab d₀ hd₀D (u * e) htD
    have hc2 : Commute x₁ (u * e) := hWab x₁ hx₁W (u * e) htW
    have hc3 : Commute y (u * e) := by
      rw [hydef]
      exact (hc1.mul_left hc2).mul_left hc1.inv_left
    have hmem : y ∈ K' ⊓ Subgroup.centralizer ({u * e} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hyK', Subgroup.mem_centralizer_singleton_iff.mpr hc3.eq⟩
    rw [hK'C] at hmem
    exact (Subgroup.mem_inf.mp hmem).2
  have hxyD : x₁ * y ∈ zGroup Ω := by
    have hb0 := (h.swap_commutator h9 hs hd₀D hsw (K.inv_mem hx₁K)).1
    have hb : d₀ * x₁⁻¹ * d₀⁻¹ * x₁ ∈ zGroup Ω := by
      have hb1 := (Subgroup.mem_inf.mp hb0).1
      rwa [inv_inv] at hb1
    have hconj : x₁ * (d₀ * x₁⁻¹ * d₀⁻¹ * x₁) * x₁⁻¹ ∈ zGroup Ω := hDN.conj_mem _ hb x₁
    have hid : x₁ * y = (x₁ * (d₀ * x₁⁻¹ * d₀⁻¹ * x₁) * x₁⁻¹) * (d₀ * (x₁ * x₁) * d₀⁻¹) := by
      rw [hydef]
      group
    have hdz : d₀ * (x₁ * x₁) * d₀⁻¹ = z := by
      rw [hx₁sq, hd₀z]
      group
    rw [hid, hdz]
    exact (zGroup Ω).mul_mem hconj hzD
  have hvW : v ∈ W := (Subgroup.mem_inf.mp hv).1
  obtain ⟨k, hkK, k', hk'K', rfl⟩ :=
    e16a2_mem_sup_decomp (hs.commutes h) (Subgroup.mem_inf.mp hv).2
  have hkx₁ : k * x₁ = x₁ * k := by
    have hvx : (k * k') * x₁ = x₁ * (k * k') := hWab _ hvW x₁ hx₁W
    have hk'x : x₁ * k' = k' * x₁ := hs.commutes h x₁ hx₁K k' hk'K'
    refine mul_right_cancel (b := k') ?_
    calc k * x₁ * k' = k * (x₁ * k') := by group
      _ = k * (k' * x₁) := by rw [hk'x]
      _ = (k * k') * x₁ := by group
      _ = x₁ * (k * k') := hvx
      _ = x₁ * k * k' := by group
  have hk'y : k' * y = y * k' := by
    have hvy : (k * k') * y = y * (k * k') := hWab _ hvW y hyW
    have hky : k * y = y * k := hs.commutes h k hkK y hyK'
    refine mul_left_cancel (a := k) ?_
    calc k * (k' * y) = (k * k') * y := by group
      _ = y * (k * k') := hvy
      _ = (y * k) * k' := by group
      _ = (k * y) * k' := by rw [hky]
      _ = k * (y * k') := by group
  have hkmem : k ∈ Subgroup.zpowers x₁ :=
    e16a2_mem_zpowers_of_comm (e16a2_isQuatSub h hs.mem) hK8 hx₁K hx₁o hkK hkx₁
  have hk'mem : k' ∈ Subgroup.zpowers y :=
    e16a2_mem_zpowers_of_comm (e16a2_isQuatSub h hs.mem_twin.1) hK'8 hyK' hyo hk'K' hk'y
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hkmem
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk'mem
  have hcommxy : Commute x₁ y := hWab x₁ hx₁W y hyW
  have hkey : (x₁ ^ m * y ^ n) * (x₁ ^ m * y ^ n) = (x₁ ^ m * x₁ ^ m) * (y ^ n * y ^ n) := by
    calc (x₁ ^ m * y ^ n) * (x₁ ^ m * y ^ n) = x₁ ^ m * (y ^ n * x₁ ^ m) * y ^ n := by group
      _ = x₁ ^ m * (x₁ ^ m * y ^ n) * y ^ n := by rw [← (hcommxy.zpow_zpow m n).eq]
      _ = (x₁ ^ m * x₁ ^ m) * (y ^ n * y ^ n) := by group
  have hzmn : z ^ (m + n) = 1 := by
    rw [zpow_add, ← e16a2_zpow_mul_self hx₁sq m, ← e16a2_zpow_mul_self hyy n, ← hkey]
    exact hv2
  have hz2 : orderOf z = 2 := orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hzz) hz1
  have hdvd : (2 : ℤ) ∣ m + n := by
    have h1 := orderOf_dvd_iff_zpow_eq_one.mpr hzmn
    rw [hz2] at h1
    exact_mod_cast h1
  obtain ⟨a, ha⟩ := Int.even_or_odd' m
  obtain ⟨b, hb⟩ := Int.even_or_odd' n
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb, e16a2_zpow_two_mul hx₁sq, e16a2_zpow_two_mul hyy, ← zpow_add]
    exact (zGroup Ω).zpow_mem hzD _
  · exfalso
    omega
  · exfalso
    omega
  · rw [ha, hb]
    have hcalc : x₁ ^ (2 * a + 1) * y ^ (2 * b + 1) = z ^ (a + b) * (x₁ * y) := by
      have hzbW : z ^ b ∈ W := W.zpow_mem hd.hzW b
      calc x₁ ^ (2 * a + 1) * y ^ (2 * b + 1) = (z ^ a * x₁) * (z ^ b * y) := by
            rw [zpow_add_one, zpow_add_one, e16a2_zpow_two_mul hx₁sq, e16a2_zpow_two_mul hyy]
        _ = z ^ a * (x₁ * z ^ b) * y := by group
        _ = z ^ a * (z ^ b * x₁) * y := by rw [hWab x₁ hx₁W _ hzbW]
        _ = z ^ (a + b) * (x₁ * y) := by rw [zpow_add]; group
    rw [hcalc]
    exact (zGroup Ω).mul_mem ((zGroup Ω).zpow_mem hzD _) hxyD

theorem u_mem_zGroup (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) : u ∈ zGroup Ω ∧ e ∈ zGroup Ω := by
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have huW : u ∈ W ⊓ (K ⊔ K') := Subgroup.mem_inf.mpr ⟨hd.huW, hd.hu⟩
  have hu : u ∈ zGroup Ω := mem_zGroup_of_mem_inf c h h9 h13 huW hd.hu2
  have hDN : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, c.twin.mem, c.twin.isInv⟩
  have hte : u * e ∈ zGroup Ω := by
    have hc := hDN.conj_mem z hzD g
    rw [hd.hgt] at hc
    exact hc
  have he : e = u * (u * e) := by rw [← mul_assoc, hd.hu2, one_mul]
  refine ⟨hu, ?_⟩
  have hprod := (zGroup Ω).mul_mem hu hte
  rw [← he] at hprod
  exact hprod

private theorem e16a2_centerIn (c : Sit16 Ω K K' W z u e g) :
    e ∈ CFSG.ClassicalInvolution.Asc77.centerIn (Subgroup.normalizer (W : Set G)) :=
  (Subgroup.mem_inf.mp (e16a2_he c)).2

private theorem e16a2_comm_of_centerIn {N : Subgroup G} {e : G}
    (he : e ∈ CFSG.ClassicalInvolution.Asc77.centerIn N) {n : G} (hn : n ∈ N) :
    n * e = e * n := by
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp he
  have hc : n * (x : G) = (x : G) * n :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨n, hn⟩)
  have hxe' : (x : G) = e := hxe
  rw [← hxe']
  exact hc

theorem e_mem_centralizer (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) :
    e ∈ Subgroup.centralizer (K : Set G) ∧ e ∈ Subgroup.centralizer (K' : Set G) := by
  have heN := e16a2_centerIn c
  have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW
  have hK'D : K' ∈ DSet Ω W :=
    h.mem_dSet_of_mem c.data.hW c.twin.mem_twin.1 c.twin.mem_twin.2 c.data.hzW
  refine ⟨Subgroup.mem_centralizer_iff.mpr fun k hk => ?_,
    Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  · exact e16a2_comm_of_centerIn heN ((h.mem_dSet_iff.mp hKD).2 hk)
  · exact e16a2_comm_of_centerIn heN ((h.mem_dSet_iff.mp hK'D).2 hk)

private theorem e16a2_mul_not_mem_sup (c : Sit16 Ω K K' W z u e g) : u * e ∉ K ⊔ K' := by
  intro hm
  apply c.e_not_mem
  have he : e = u⁻¹ * (u * e) := by group
  rw [he]
  exact (K ⊔ K').mul_mem ((K ⊔ K').inv_mem c.data.hu) hm

private theorem e16a2_conj_mem_dSet (h : EndHyp Ω) {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) (hR : R ∈ DSet Ω W) :
    conjSub g R ∈ DSet Ω W := by
  rw [h.mem_dSet_iff] at hR
  rw [h.mem_dSet_iff]
  refine ⟨h.thmD.hyp.conjInvariant g R hR.1, ?_⟩
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 : g⁻¹ * x * g ∈ Subgroup.normalizer (W : Set G) := hR.2 hx
  have key := (Subgroup.normalizer (W : Set G)).mul_mem
    ((Subgroup.normalizer (W : Set G)).mul_mem hg h1)
    ((Subgroup.normalizer (W : Set G)).inv_mem hg)
  have e1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [e1] at key
  exact key

private theorem e16a2_g_mem (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) :
    g ∈ Subgroup.normalizer (W : Set G) := by
  have hMle : (⨆ R ∈ DSet Ω W, R) ≤ Subgroup.normalizer (W : Set G) :=
    iSup₂_le fun R hR => (h.mem_dSet_iff.mp hR).2
  exact hMle c.data.hg

theorem conjSub_mem (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) :
    conjSub g K ∈ DSet Ω W ∧ conjSub g K ∈ omegaStarNbr Ω K ∧ conjSub g K ∉ twinSet Ω K ∧
      IsUniqueInvolution (conjSub g K) (u * e) := by
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := e16a2_g_mem c h
  have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem hd.hW hs.mem hs.isInv hd.hzW
  have hJD : conjSub g K ∈ DSet Ω W := e16a2_conj_mem_dSet h hgN hKD
  have hJu : IsUniqueInvolution (conjSub g K) (u * e) := by
    rw [← hd.hgt]
    exact hs.isInv.conj g
  have hne : conjSub g K ≠ K := by
    intro heq
    have hmem : u * e ∈ conjSub g K := hJu.mem
    rw [heq] at hmem
    exact e16a2_mul_not_mem_sup c (Subgroup.mem_sup_left hmem)
  have hOm : conjSub g K ∈ omegaStarNbr Ω K :=
    (Q3CL.Thompson.mem_omegaStarNbr_of_inf_W h.thmD.hyp hd.hW hs.mem
      (h.thmD.hyp.conjInvariant g K hs.mem) hne.symm hKD hJD (e16a2_isSylow2In_self h hs.mem)
      (e16a2_isSylow2In_self h (h.thmD.hyp.conjInvariant g K hs.mem))).1
  have hnt : conjSub g K ∉ twinSet Ω K := by
    rw [hs.twin]
    intro hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with heq | heq
    · exact hne heq
    · have hmem' : u * e ∈ conjSub g K := hJu.mem
      rw [heq] at hmem'
      exact e16a2_mul_not_mem_sup c (Subgroup.mem_sup_right hmem')
  exact ⟨hJD, hOm, hnt, hJu⟩

theorem dSet_le_centralizer (c : Sit16 Ω K K' W z u e g) :
    ∀ R ∈ DSet Ω W, R ≤ Subgroup.centralizer ({e} : Set G) := by
  intro R hR r hr
  have hN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (e16a2_comm_of_centerIn (e16a2_centerIn c) hN)

private theorem e16a2_comm_of_unique {L : Subgroup G} {t : G} (ht : IsUniqueInvolution L t)
    {x : G} (hx : x ∈ L) : x * t = t * x := by
  have hc : x * t * x⁻¹ ∈ L := L.mul_mem (L.mul_mem hx ht.mem) (L.inv_mem hx)
  have hsq : x * t * x⁻¹ * (x * t * x⁻¹) = 1 := by
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [ht.sq]; group
  rcases ht.unique _ hc hsq with h1 | h1
  · exfalso
    apply ht.ne_one
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  · calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [h1]

private theorem e16a2_le_centralizer_u (c : Sit16 Ω K K' W z u e g) {L : Subgroup G}
    (hL : L ∈ DSet Ω W) (hLu : IsUniqueInvolution L (u * e)) :
    L ≤ Subgroup.centralizer ({u} : Set G) := by
  intro x hx
  have hxe : x * e = e * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (dSet_le_centralizer c L hL hx)
  have hxt : x * (u * e) = (u * e) * x := e16a2_comm_of_unique hLu hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * u = x * (u * (e * e)) := by rw [c.data.he2, mul_one]
    _ = x * (u * e) * e := by group
    _ = (u * e * x) * e := by rw [hxt]
    _ = u * e * (x * e) := by group
    _ = u * e * (e * x) := by rw [hxe]
    _ = u * x := by rw [← mul_assoc, mul_assoc u e e, c.data.he2, mul_one]

theorem conjSub_le_centralizer_u (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) :
    conjSub g K ≤ Subgroup.centralizer ({u} : Set G) ∧
      conjSub g K' ≤ Subgroup.centralizer ({u} : Set G) := by
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  obtain ⟨hJD, -, -, hJu⟩ := conjSub_mem c h h9
  have hK'D : K' ∈ DSet Ω W := h.mem_dSet_of_mem hd.hW hs.mem_twin.1 hs.mem_twin.2 hd.hzW
  have hJ'D : conjSub g K' ∈ DSet Ω W := e16a2_conj_mem_dSet h (e16a2_g_mem c h) hK'D
  have hJ'u : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]
    exact hs.mem_twin.2.conj g
  exact ⟨e16a2_le_centralizer_u c hJD hJu, e16a2_le_centralizer_u c hJ'D hJ'u⟩

theorem mul_mem_eGroup (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) :
    u * e ∈ eGroup Ω K ∧ u * e ∉ K ⊔ K' := by
  obtain ⟨-, hOm, -, hJu⟩ := conjSub_mem c h h9
  exact ⟨h.mem_eGroup_of_mem_omegaStarNbr hOm hJu, e16a2_mul_not_mem_sup c⟩

end Sit16

end CFSG.ClassicalInvolution.Q3.Sec13
