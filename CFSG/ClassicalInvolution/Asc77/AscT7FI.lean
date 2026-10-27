module

public import CFSG.ClassicalInvolution.Asc77.AscT7FG
public import CFSG.ClassicalInvolution.Asc77.AscT7FE

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

section Chain

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_isPGroup_sup_sylow {P L : Subgroup G} (hP : IsPGroup 2 P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) :
    ∃ R : Subgroup G, IsSylow2In R L ∧ IsPGroup 2 ↥(P ⊔ R) := by
  obtain ⟨R, hR, hfix⟩ := T3.exists_sylow_normalized hP hPL
  exact ⟨R, hR, hP.to_sup_of_normal_right' hR.2.1 fun u hu =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix u hu)⟩

theorem exists_W_of_isPGroup (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {P : Subgroup G} (hP : IsPGroup 2 P) :
    ∃ W ∈ WSet Ω, ∀ R ∈ RSet Ω, R ≤ P → R ∈ DSet Ω W := by
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := (l6_9_proved p f hp hq G Ω hΩ S).1
  have hηG : η ∈ etaG Ω := ⟨S, hη, hηinv⟩
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hη.1 hV).2
  refine ⟨⨆ V ∈ η, V, ⟨η, hηG, rfl⟩, fun R hR hRP => ⟨hR, ?_⟩⟩
  exact le_normalizer_biSup_of_acts
    ((l6_10_proved p f hp hq G Ω hΩ S η hηG hηS).1 R hR (hRP.trans hS))

end Chain

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

namespace Ctx

variable (c : Ctx p f Ω W)
include c

theorem mul_four_eq_one (hnc : ¬ DbarConnected Ω W) (ρ₁ ρ₂ ρ₃ ρ₄ : Rep Ω W)
    (h₁₂ : ρ₂.K ∈ omegaNbr Ω ρ₁.K) (h₁₃ : ρ₃.K ∈ omegaNbr Ω ρ₁.K)
    (h₂₃ : ρ₃.K ∈ omegaNbr Ω ρ₂.K) (h₁₄ : ρ₄.K ∈ omegaNbr Ω ρ₁.K) (h₂₄ : ρ₄.K ≠ ρ₂.K)
    (h₃₄ : ρ₄.K ≠ ρ₃.K) {z₁ z₂ z₃ z₄ : G} (hz₁ : IsUniqueInvolution ρ₁.K z₁)
    (hz₂ : IsUniqueInvolution ρ₂.K z₂) (hz₃ : IsUniqueInvolution ρ₃.K z₃)
    (hz₄ : IsUniqueInvolution ρ₄.K z₄) : z₁ * z₂ * z₃ * z₄ = 1 := by
  classical
  have hP : PartIHyp p f Ω := ⟨c.hp, c.hq, c.hΩ, c.hA⟩
  obtain ⟨ρ₅, hK51, hK52, hK53, hn51, -, -, hprod⟩ :=
    c.exists_fourth hnc ρ₁ ρ₂ ρ₃ h₁₂ h₁₃ h₂₃ hz₁ hz₂ hz₃
  obtain ⟨z₅, hz₅⟩ := c.hΩ.exists_uniqueInvolution c.hp c.hq ρ₅.hK
  have hK45 : ρ₄.K = ρ₅.K := by
    by_contra hK45
    have hne_of : ∀ σ σ' : Rep Ω W, σ.K ≠ σ'.K → T7D.imgQ σ ≠ T7D.imgQ σ' := fun σ σ' hK e =>
      hK (c.K_eq_of_img_eq σ σ' (congrArg Subtype.val e))
    have hmemC : ∀ σ : Rep Ω W, σ.K ∈ omegaNbr Ω ρ₁.K →
        T7D.imgQ σ ∈ Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁) := fun σ hσ =>
      ⟨T7D.imgQ_mem σ, (Subtype.ext (c.comm_of_omega ρ₁ σ hσ)).symm⟩
    have hx₁C : T7D.imgQ ρ₁ ∈ Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁) :=
      Star3T.self_mem_cent (T7D.imgQ_mem ρ₁)
    have h12 : T7D.imgQ ρ₁ ≠ T7D.imgQ ρ₂ := hne_of _ _ h₁₂.2.1.symm
    have h13 : T7D.imgQ ρ₁ ≠ T7D.imgQ ρ₃ := hne_of _ _ h₁₃.2.1.symm
    have h14 : T7D.imgQ ρ₁ ≠ T7D.imgQ ρ₄ := hne_of _ _ h₁₄.2.1.symm
    have h15 : T7D.imgQ ρ₁ ≠ T7D.imgQ ρ₅ := hne_of _ _ (fun e => hK51 e.symm)
    have h23 : T7D.imgQ ρ₂ ≠ T7D.imgQ ρ₃ := hne_of _ _ h₂₃.2.1.symm
    have h24 : T7D.imgQ ρ₂ ≠ T7D.imgQ ρ₄ := hne_of _ _ h₂₄.symm
    have h25 : T7D.imgQ ρ₂ ≠ T7D.imgQ ρ₅ := hne_of _ _ (fun e => hK52 e.symm)
    have h34 : T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₄ := hne_of _ _ h₃₄.symm
    have h35 : T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₅ := hne_of _ _ (fun e => hK53 e.symm)
    have h45 : T7D.imgQ ρ₄ ≠ T7D.imgQ ρ₅ := hne_of _ _ hK45
    have hC3 : 3 ≤ (Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁)).ncard := by
      have hsub : (↑({T7D.imgQ ρ₁, T7D.imgQ ρ₂, T7D.imgQ ρ₃} : Finset ↥(muGroup Ω W)) :
          Set ↥(muGroup Ω W)) ⊆ Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁) := by
        intro y hy
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact hx₁C
        · exact hmemC ρ₂ h₁₂
        · exact hmemC ρ₃ h₁₃
      have h3 : ({T7D.imgQ ρ₁, T7D.imgQ ρ₂, T7D.imgQ ρ₃} : Finset ↥(muGroup Ω W)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
          Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_coe_finset, h3] at this
    have hC4 : (Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁)).ncard = 4 := by
      rcases thompsonClique G Ω hP W c.hW hnc (T7D.imgQ ρ₁) (T7D.imgQ_mem ρ₁) with h | h | ⟨h, -⟩
      · omega
      · omega
      · exact h
    have hsub5 : (↑({T7D.imgQ ρ₁, T7D.imgQ ρ₂, T7D.imgQ ρ₃, T7D.imgQ ρ₄, T7D.imgQ ρ₅} :
        Finset ↥(muGroup Ω W)) : Set ↥(muGroup Ω W)) ⊆
          Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁) := by
      intro y hy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact hx₁C
      · exact hmemC ρ₂ h₁₂
      · exact hmemC ρ₃ h₁₃
      · exact hmemC ρ₄ h₁₄
      · exact hmemC ρ₅ hn51
    have h5 : ({T7D.imgQ ρ₁, T7D.imgQ ρ₂, T7D.imgQ ρ₃, T7D.imgQ ρ₄, T7D.imgQ ρ₅} :
        Finset ↥(muGroup Ω W)).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14, h15]),
        Finset.card_insert_of_notMem (by simp [h23, h24, h25]),
        Finset.card_insert_of_notMem (by simp [h34, h35]),
        Finset.card_insert_of_notMem (by simp [h45]), Finset.card_singleton]
    have := Set.ncard_le_ncard hsub5 (Set.toFinite _)
    rw [Set.ncard_coe_finset, h5, hC4] at this
    omega
  have hz45 : z₄ = z₅ := hz₄.eq (by rw [hK45]; exact hz₅)
  rw [hz45]
  exact hprod z₅ hz₅

end Ctx

end Thompson

section Frame

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}

omit [Finite G] in
theorem comm_of_comm_mul_of_comm {x t z : G} (hxz : x * z = z * x)
    (hxtz : x * (t * z) = (t * z) * x) : x * t = t * x := by
  have h : x * t * z = t * x * z := by
    calc x * t * z = x * (t * z) := by rw [mul_assoc]
      _ = (t * z) * x := hxtz
      _ = t * (z * x) := by rw [mul_assoc]
      _ = t * (x * z) := by rw [hxz]
      _ = t * x * z := by rw [mul_assoc]
  exact mul_right_cancel h

omit [Finite G] in
theorem le_centralizer_of_le_centralizer_mul {A : Subgroup G}
    (hA : A ≤ Subgroup.centralizer ({t * z} : Set G)) (hz : ∀ x ∈ A, x * z = z * x) :
    A ≤ Subgroup.centralizer ({t} : Set G) := fun x hx => by
  have hx' := Subgroup.mem_centralizer_singleton_iff.mp (hA hx)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact comm_of_comm_mul_of_comm (hz x hx) hx'

omit [Finite G] in
theorem commute_involution_of_conjSub_eq {z : G} (hz : IsUniqueInvolution K z) {x : G}
    (hx : conjSub x K = K) : x * z = z * x :=
  mul_inv_eq_iff_eq_mul.mp (hz.conj_eq hx)

theorem Hyp21.involution_eq_of_mem_omegaNbr (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hSigC : ∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G))
    {J₁ : Subgroup G} {t₁ : G} (hJ₁ : J₁ ∈ omegaNbr Ω K) (ht₁ : IsUniqueInvolution J₁ t₁)
    (hJ₁K' : J₁ ≠ K') (hJ₁J : J₁ ≠ J) : t₁ = t := by
  classical
  have hst := h.std.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have hJΩ : J ∈ Ω := h.hJ.1
  have hJK : J ∈ omegaNbr Ω K := h.hJ.2 K (mem_twinSet_self hK hz)
  have hJK' : J ∈ omegaNbr Ω K' := h.hJ.2 K' h.std.hK'
  have hK'K : K' ∈ omegaNbr Ω K := T3.twin_mem_omegaNbr hΩ hK hK'Ω h.std.hne hz hzK'
  have hJ₁Ω : J₁ ∈ Ω := hJ₁.1
  have hdc : ∀ L ∈ omegaNbr Ω K, L ≤ Subgroup.centralizer ({t * z} : Set G) := fun L hL =>
    hSigC L (Relation.ReflTransGen.single ⟨hL.1, Or.inl hL⟩)
  have hKc : K ≤ Subgroup.centralizer ({t * z} : Set G) := hSigC K Relation.ReflTransGen.refl
  have hKt : K ≤ Subgroup.centralizer ({t} : Set G) :=
    le_centralizer_of_le_centralizer_mul hKc fun x hx =>
      commute_involution_of_conjSub_eq hz (conjSub_eq_self_of_mem hx)
  have hK't : K' ≤ Subgroup.centralizer ({t} : Set G) :=
    le_centralizer_of_le_centralizer_mul (hdc K' hK'K) fun x hx =>
      commute_involution_of_conjSub_eq hzK' (conjSub_eq_self_of_mem hx)
  have hdJ₁ := hdc J₁ hJ₁
  have hJ₁K : J₁ ∈ omegaNbr Ω K := hJ₁
  obtain ⟨-, -, R₁, hR₁, hR₁J₁, hR₁N⟩ := hJ₁
  have hR₁S : IsSylow2In R₁ J₁ := hΩ.isSylow2In_of_mem_RSet_of_le hp hJ₁Ω hR₁ hR₁J₁
  have hR₁2 : IsPGroup 2 R₁ := hR₁S.2.1
  have h8₁ : 8 ≤ Nat.card R₁ := hΩ.eight_le_of_mem_RSet hp hR₁
  have hR₁z : R₁ ≤ Subgroup.centralizer ({z} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_involution_of_conjSub_eq hz (mem_normalizer_iff_conjSub_eq.mp (hR₁N hx))
  have hR₁t : R₁ ≤ Subgroup.centralizer ({t} : Set G) :=
    le_centralizer_of_le_centralizer_mul (hR₁J₁.trans hdJ₁) fun x hx =>
      commute_involution_of_conjSub_eq hz (mem_normalizer_iff_conjSub_eq.mp (hR₁N hx))
  have hR₁K' : R₁ ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK'Ω hJ₁Ω (fun e => hJ₁K' e.symm) hzK' hR₁J₁ hR₁2
      (by omega) hR₁z
  have hR₁J : R₁ ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hJΩ hJ₁Ω (fun e => hJ₁J e.symm) h.ht hR₁J₁ hR₁2
      (by omega) hR₁t
  obtain ⟨R_K, hRKS, hP₁⟩ := exists_isPGroup_sup_sylow hR₁2 hR₁N
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK'Ω h.std.hne.symm hz hzK'
  have hP₁N : R₁ ⊔ R_K ≤ Subgroup.normalizer (K' : Set G) := sup_le hR₁K' (hRKS.1.trans hKN)
  obtain ⟨R_K', hRK'S, hP₂⟩ := exists_isPGroup_sup_sylow hP₁ hP₁N
  have hRKset : R_K ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRKS
  have hRK'set : R_K' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hRK'S
  have h8K : 8 ≤ Nat.card R_K := hΩ.eight_le_of_mem_RSet hp hRKset
  have h8K' : 8 ≤ Nat.card R_K' := hΩ.eight_le_of_mem_RSet hp hRK'set
  have hRKJ : R_K ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hJΩ hK hJK.2.1 h.ht hRKS.1 hRKS.2.1 (by omega)
      (hRKS.1.trans hKt)
  have hRK'J : R_K' ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hJΩ hK'Ω hJK'.2.1 h.ht hRK'S.1 hRK'S.2.1
      (by omega) (hRK'S.1.trans hK't)
  have hP₂N : R₁ ⊔ R_K ⊔ R_K' ≤ Subgroup.normalizer (J : Set G) :=
    sup_le (sup_le hR₁J hRKJ) hRK'J
  obtain ⟨R_J, hRJS, hP₃⟩ := exists_isPGroup_sup_sylow hP₂ hP₂N
  have hRJset : R_J ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hRJS
  obtain ⟨W₁, hW₁, hD⟩ := exists_W_of_isPGroup hp hq hΩ hP₃
  have hR₁D : R₁ ∈ DSet Ω W₁ :=
    hD R₁ hR₁ (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hRKD : R_K ∈ DSet Ω W₁ :=
    hD R_K hRKset (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hRK'D : R_K' ∈ DSet Ω W₁ := hD R_K' hRK'set (le_sup_right.trans le_sup_left)
  have hRJD : R_J ∈ DSet Ω W₁ := hD R_J hRJset le_sup_right
  obtain ⟨ρK, hρK, -⟩ := T7D.exists_rep hp hq hΩ hW₁ hK hRKS hRKD
  obtain ⟨ρK', hρK', -⟩ := T7D.exists_rep hp hq hΩ hW₁ hK'Ω hRK'S hRK'D
  obtain ⟨ρJ, hρJ, -⟩ := T7D.exists_rep hp hq hΩ hW₁ hJΩ hRJS hRJD
  obtain ⟨ρJ₁, hρJ₁, -⟩ := T7D.exists_rep hp hq hΩ hW₁ hJ₁Ω hR₁S hR₁D
  have c₁ : Thompson.Ctx p f Ω W₁ := T7D.ctx_of_stand hst hW₁
  have hnc₁ : ¬ DbarConnected Ω W₁ :=
    thompsonGraphAll G Ω ⟨hst.odd, hst.five, hst.hyp, hst.aEmpty⟩ hst.mem hne hW₁
  have h4 := c₁.mul_four_eq_one hnc₁ ρK ρK' ρJ ρJ₁ (by rw [hρK, hρK']; exact hK'K)
    (by rw [hρK, hρJ]; exact hJK) (by rw [hρK', hρJ]; exact hJK') (by rw [hρK, hρJ₁]; exact hJ₁K)
    (by rw [hρK', hρJ₁]; exact hJ₁K') (by rw [hρJ, hρJ₁]; exact hJ₁J)
    (by rw [hρK]; exact hz) (by rw [hρK']; exact hzK') (by rw [hρJ]; exact h.ht)
    (by rw [hρJ₁]; exact ht₁)
  rw [hz.sq, one_mul] at h4
  have h5 : t₁ = t⁻¹ := eq_inv_of_mul_eq_one_right h4
  rw [h5]
  exact inv_eq_of_mul_eq_one_left h.ht.sq

theorem Hyp21.normalizer_le_centralizer_tz (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hSigC : ∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({t * z} : Set G) := by
  have hst := h.std.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have htz : t ≠ z := by
    intro htz
    have hJV : J ∈ twinSet Ω K := ⟨h.hJ.1, z, hz, htz ▸ h.ht⟩
    exact (h.hJ.2 J hJV).2.1 rfl
  intro n hn
  have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp hn
  have hnz : n * z = z * n := commute_involution_of_conjSub_eq hz hnK
  have hJ₁ : conjSub n J ∈ omegaNbr Ω K := by
    have := omegaNbr_conj hΩ.conjInvariant (h.hJ.2 K (mem_twinSet_self hK hz)) n
    rwa [hnK] at this
  have ht₁ : IsUniqueInvolution (conjSub n J) (n * t * n⁻¹) := h.ht.conj n
  have htt : n * t * n⁻¹ = t := by
    by_cases hJK' : conjSub n J = K'
    · exfalso
      have e1 : n * t * n⁻¹ = z := ht₁.eq (by rw [hJK']; exact hzK')
      apply htz
      have e2 : n * t = z * n := (mul_inv_eq_iff_eq_mul.mp e1).trans rfl
      calc t = n⁻¹ * (n * t) := by group
        _ = n⁻¹ * (z * n) := by rw [e2]
        _ = n⁻¹ * (n * z) := by rw [hnz]
        _ = z := by group
    · by_cases hJJ : conjSub n J = J
      · exact (h.ht.eq (by rw [← hJJ]; exact ht₁)).symm
      · exact h.involution_eq_of_mem_omegaNbr hne hSigC hJ₁ ht₁ hJK' hJJ
  have hnt : n * t = t * n := mul_inv_eq_iff_eq_mul.mp htt
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * (t * z) = (n * t) * z := by rw [mul_assoc]
    _ = (t * n) * z := by rw [hnt]
    _ = t * (n * z) := by rw [mul_assoc]
    _ = t * (z * n) := by rw [hnz]
    _ = (t * z) * n := by rw [mul_assoc]

end Frame

section Final

variable (p f : ℕ) [Fact p.Prime]

theorem c21_starCent_proved : C21_StarCent p f := by
  intro G _ _ _ Ω K K' z u J t W h _ _ hSigC _ M hM
  have hKc : K ≤ Subgroup.centralizer ({t * z} : Set G) := hSigC K Relation.ReflTransGen.refl
  by_cases heq : dComp Ω K = dstarComp Ω K
  · exact hSigC M (by rw [heq]; exact hM)
  · have hN := h.normalizer_le_centralizer_tz heq hSigC
    have hM' : MGrp Ω W ≤ Subgroup.centralizer ({t * z} : Set G) :=
      (h.mGrp_le_rLayer_tz heq).trans (rLayer_le_centralizer Ω (t * z))
    obtain ⟨x, hx, rfl⟩ := h.exists_mem_conj_of_dstarComp heq hM' hN M hM
    intro y hy
    rw [mem_conjSub_iff] at hy
    have hy' := hKc hy
    have hyx : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [hyx]
    exact (Subgroup.centralizer ({t * z} : Set G)).mul_mem
      ((Subgroup.centralizer ({t * z} : Set G)).mul_mem hx hy')
      ((Subgroup.centralizer ({t * z} : Set G)).inv_mem hx)

end Final

end CFSG.ClassicalInvolution.Asc77
