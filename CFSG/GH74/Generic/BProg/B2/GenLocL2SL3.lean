module

public import CFSG.GH74.Generic.BProg.B2.GenLocL2Small
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted
open scoped MatrixGroups
open GenLocL2Small CFSG.Glauberman.Dickson.MaxUp

namespace GenLocL2SL3

theorem exists_equivariant_action {J H D : Type} [Group J] [Group H] [Group D] (φ : H →* J)
    (hφ : Function.Injective φ) (α : D →* MulAut J)
    (hinv : ∀ (d : D) (x : H), ∃ y : H, φ y = α d (φ x)) :
    ∃ β : D →* MulAut H, ∀ (d : D) (x : H), α d (φ x) = φ (β d x) := by
  classical
  choose T hT using hinv
  have hmul : ∀ d x y, T d (x * y) = T d x * T d y := by
    intro d x y
    apply hφ
    rw [map_mul, hT, hT, hT, map_mul, map_mul]
  have hone : ∀ x, T 1 x = x := by
    intro x
    apply hφ
    rw [hT, map_one]
    rfl
  have hcomp : ∀ d d' x, T (d * d') x = T d (T d' x) := by
    intro d d' x
    apply hφ
    rw [hT, hT, hT, map_mul]
    rfl
  let β : D → MulAut H := fun d =>
    { toFun := T d
      invFun := T d⁻¹
      left_inv := fun x => by rw [← hcomp, inv_mul_cancel, hone]
      right_inv := fun x => by rw [← hcomp, mul_inv_cancel, hone]
      map_mul' := hmul d }
  refine ⟨{ toFun := β, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext x
    exact hone x
  · intro d d'
    ext x
    exact hcomp d d' x
  · intro d x
    exact (hT d x).symm

theorem exists_subfield_data {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (u : MulAut SL(2, K)) (hu2 : u * u = 1) (σ : K ≃+* K)
    (hσdef : (gammaOf hodd h3 u).right = σ) (hσ : σ ≠ 1) :
    ∃ φ : SL(2, ↥(fixedField σ)) →* SL(2, K),
      Function.Injective φ ∧ (∀ x, u (φ x) = φ x) ∧ (∀ y : SL(2, K), u y = y → y ∈ φ.range) := by
  have hσ' : (gammaOf hodd h3 u).right ≠ 1 := by rw [hσdef]; exact hσ
  obtain ⟨β, hβ⟩ := exists_conj_slFieldAut hodd h3 u hu2 hσ'
  rw [hσdef] at hβ
  have hconj : ∀ y, u (β y) = β (slFieldAut σ y) := by
    intro y
    rw [← hβ]
    simp [MulAut.mul_apply]
  refine ⟨(β : MulAut SL(2, K)).toMonoidHom.comp (Matrix.SpecialLinearGroup.map (fixedField σ).subtype),
    ?_, ?_, ?_⟩
  · exact β.injective.comp (map_subtype_injective σ)
  · intro x
    have hmem : Matrix.SpecialLinearGroup.map (fixedField σ).subtype x ∈
        fixedSubgroup SL(2, K) (slFieldAut σ) := by
      rw [← range_map_subtype]
      exact ⟨x, rfl⟩
    have hfix : slFieldAut σ (Matrix.SpecialLinearGroup.map (fixedField σ).subtype x) =
        Matrix.SpecialLinearGroup.map (fixedField σ).subtype x := hmem
    change u (β (Matrix.SpecialLinearGroup.map (fixedField σ).subtype x)) =
      β (Matrix.SpecialLinearGroup.map (fixedField σ).subtype x)
    rw [hconj, hfix]
  · intro y hy
    have h1 : slFieldAut σ (β⁻¹ y) = β⁻¹ y := by
      have h2 := hconj (β⁻¹ y)
      rw [MulAut.apply_inv_self, hy] at h2
      have h3' := congrArg (fun z => β⁻¹ z) h2
      simpa using h3'.symm
    have hmem : β⁻¹ y ∈ fixedSubgroup SL(2, K) (slFieldAut σ) := h1
    rw [← range_map_subtype] at hmem
    obtain ⟨x, hx⟩ := hmem
    refine ⟨x, ?_⟩
    change β (Matrix.SpecialLinearGroup.map (fixedField σ).subtype x) = y
    rw [hx]
    simp

theorem card_fixedField_sq {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hσσ : σ * σ = 1)
    (hσ : σ ≠ 1) : Nat.card ↥(fixedField σ) ^ 2 = Nat.card K := by
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσσ) hσ
  simpa [hord] using fixedField_card_pow σ

theorem exists_noncommute_sl2 {F₀ : Type} [Field F₀] [Finite F₀] (h4 : 4 ≤ Nat.card F₀) :
    ∃ x y : SL(2, F₀), x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hperf : commutator SL(2, F₀) = ⊤ :=
    (ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F₀ h4).commutator_eq_top
  have hbot : commutator SL(2, F₀) ≤ ⊥ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [Subgroup.mem_bot, commutatorElement_def]
    have := hcon g₁ g₂
    group
    rw [this]
    group
  rw [hperf] at hbot
  have hcard : Nat.card SL(2, F₀) = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) :=
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F₀
  have h1 : Nat.card SL(2, F₀) = 1 := by
    rw [← Subgroup.card_top (G := SL(2, F₀)), eq_bot_iff.2 hbot, Subgroup.card_bot]
  rw [hcard] at h1
  have : 4 ≤ Nat.card F₀ ^ 2 - 1 := by
    have : 16 ≤ Nat.card F₀ ^ 2 := by nlinarith
    omega
  nlinarith

theorem mem_center_of_commute_range {K F₀ : Type} [Field K] [Field F₀] [Finite F₀]
    (h4 : 4 ≤ Nat.card F₀) (φ : SL(2, F₀) →* SL(2, K)) (hφ : Function.Injective φ)
    (c : SL(2, K)) (hc : ∀ x : SL(2, F₀), c * φ x = φ x * c) :
    c ∈ Subgroup.center SL(2, K) := by
  by_contra hcz
  obtain ⟨x, y, hxy⟩ := exists_noncommute_sl2 h4
  apply hxy
  apply hφ
  rw [map_mul, map_mul]
  have hfix : ∀ z : SL(2, F₀), φ z ∈ fixedSubgroup SL(2, K) (MulAut.conj c) := by
    intro z
    change c * φ z * c⁻¹ = φ z
    rw [hc z]
    group
  exact comm_fixed_conj c hcz _ (hfix x) _ (hfix y)

section Subfield

theorem gammaAct_eq_top_of_trivial_two {F₀ : Type} [Field F₀]
    [Finite F₀] {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF₀ : Nat.card F₀ = p ^ k) (h5 : 5 ≤ p ^ k)
    {D : Type} [Group D] [Finite D] (hD : CFSG.IsElementaryAbelian 2 D) (h8 : Nat.card D = 8)
    (β : D →* MulAut SL(2, F₀)) (u : D) (hu1 : u ≠ 1) (hβu : β u = 1)
    (hnoninn : ∃ d : D, β d ∉ (MulAut.conj : SL(2, F₀) →* MulAut SL(2, F₀)).range) :
    gammaAct β = ⊤ := by
  set N : Subgroup D := Subgroup.zpowers u with hN
  have hu2 : u * u = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD u
  have hNcard : Nat.card N = 2 := by
    rw [hN, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have hNnormal : N.Normal := inferInstance
  have hker : N ≤ β.ker := by
    rw [hN, Subgroup.zpowers_le]
    exact hβu
  let β' : D ⧸ N →* MulAut SL(2, F₀) := QuotientGroup.lift N β (fun n hn => hker hn)
  have hβ : β = β'.comp (QuotientGroup.mk' N) := by
    ext d x
    rfl
  have hQEA : CFSG.IsElementaryAbelian 2 (D ⧸ N) :=
    GenLocBasic.isEA_of_surjective hD (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hQcard : Nat.card (D ⧸ N) = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h8, hNcard] at h1
    omega
  have hQrank : pRank 2 (D ⧸ N) = 2 := by
    have h1 := GenLocBasic.card_eq_two_pow_pRank_type hQEA
    rw [hQcard] at h1
    have h2 : (2 : ℕ) ^ pRank 2 (D ⧸ N) = 2 ^ 2 := by
      rw [← h1]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  have hgen : gammaAct β = gammaAct β' := by
    rw [hβ]
    exact GenLocBasic.gammaAct_comp_surj hD β' (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  rw [hgen]
  refine gammaAct_sl2_rank2 hp hp2 hF₀ h5 β' ⟨hQEA, Or.inl hQrank⟩ hQrank ?_
  rintro ⟨-, hle⟩
  obtain ⟨d, hd⟩ := hnoninn
  exact hd (hle ⟨QuotientGroup.mk' N d, rfl⟩)

end Subfield

section Lifts

variable {K : Type} [Field K] [Finite K]

theorem mem_center_of_mul_self_eq_one (hodd : Odd (Nat.card K)) {x : SL(2, K)} (hx : x * x = 1) :
    x ∈ Subgroup.center SL(2, K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two hodd)
  have hsq : (x : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hx, Matrix.SpecialLinearGroup.coe_one]
  rw [CFSG.LieType.SteinbergBR.mem_center_SL2_iff]
  exact CFSG.SectionRank.Ccomm.eq_one_or_neg_one_of_sq_eq_one h2 x.2 hsq

theorem not_commute_of_lifts (hodd : Odd (Nat.card K)) {D : Subgroup (MulAut SL(2, K))}
    (hD : CFSG.IsElementaryAbelian 2 ↥D) {c b : ↥D} {s t : SL(2, K)}
    (hc : (c : MulAut SL(2, K)) = MulAut.conj s) (hb : (b : MulAut SL(2, K)) = MulAut.conj t)
    (hc1 : c ≠ 1) (hb1 : b ≠ 1) (hcb : c ≠ b) : s * t ≠ t * s := by
  have hZc := card_center_sl2 hodd
  have hnc : ∀ (d : ↥D) (x : SL(2, K)), d ≠ 1 → (d : MulAut SL(2, K)) = MulAut.conj x →
      x ∉ Subgroup.center SL(2, K) := by
    intro d x hd1 hx hxc
    apply hd1
    apply Subtype.ext
    rw [hx, (GenLocL2Small.conj_eq_one_iff x).2 hxc]
    rfl
  have hsq : ∀ (d : ↥D) (x : SL(2, K)), (d : MulAut SL(2, K)) = MulAut.conj x →
      x * x ∈ Subgroup.center SL(2, K) := by
    intro d x hx
    rw [← GenLocL2Small.conj_eq_one_iff, map_mul, ← hx]
    exact congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD d)
  have hsne : s * s ≠ 1 := fun h => hnc c s hc1 hc (mem_center_of_mul_self_eq_one hodd h)
  have htne : t * t ≠ 1 := fun h => hnc b t hb1 hb (mem_center_of_mul_self_eq_one hodd h)
  have hst : s * s = t * t := by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center SL(2, K)))).1 hZc
    have h1 : (⟨s * s, hsq c s hc⟩ : ↥(Subgroup.center SL(2, K))) = y :=
      hy _ (fun h => hsne (congrArg Subtype.val h))
    have h2 : (⟨t * t, hsq b t hb⟩ : ↥(Subgroup.center SL(2, K))) = y :=
      hy _ (fun h => htne (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)
  intro hcomm
  have hz := mul_self_eq_one_of_mem_center hZc (hsq c s hc)
  have h1 : (s * t) * (s * t) = 1 := by
    calc (s * t) * (s * t) = s * (t * s) * t := by group
      _ = s * (s * t) * t := by rw [hcomm]
      _ = (s * s) * (t * t) := by group
      _ = (s * s) * (s * s) := by rw [← hst]
      _ = 1 := hz
  have h2 : s * t ∈ Subgroup.center SL(2, K) := mem_center_of_mul_self_eq_one hodd h1
  have h3 : MulAut.conj (s * t) = 1 := (GenLocL2Small.conj_eq_one_iff _).2 h2
  rw [map_mul, ← hc, ← hb] at h3
  have h4 : (c : MulAut SL(2, K)) * (b : MulAut SL(2, K)) = 1 := h3
  have hbb : (b : MulAut SL(2, K)) * (b : MulAut SL(2, K)) = 1 :=
    congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD b)
  apply hcb
  apply Subtype.ext
  calc (c : MulAut SL(2, K)) = (c : MulAut SL(2, K)) * ((b : MulAut SL(2, K)) * (b : MulAut SL(2, K))) := by
        rw [hbb, mul_one]
    _ = ((c : MulAut SL(2, K)) * (b : MulAut SL(2, K))) * (b : MulAut SL(2, K)) := by rw [mul_assoc]
    _ = b := by rw [h4, one_mul]

end Lifts

section NonInner

variable {K F₀ : Type} [Field K] [Finite K] [Field F₀] [Finite F₀]

theorem noninner_of_not_fixed (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card F₀)
    (φ : SL(2, F₀) →* SL(2, K)) (hφ : Function.Injective φ) {D : Type} [Group D]
    (α : D →* MulAut SL(2, K)) (β : D →* MulAut SL(2, F₀))
    (hβ : ∀ (d : D) (x : SL(2, F₀)), α d (φ x) = φ (β d x)) (u b : D)
    (hufix : ∀ x, α u (φ x) = φ x) (ŝ : SL(2, K)) (hb : α b = MulAut.conj ŝ) (hŝ : α u ŝ ≠ ŝ) :
    β b ∉ (MulAut.conj : SL(2, F₀) →* MulAut SL(2, F₀)).range := by
  rintro ⟨h, hh⟩
  have hc : ∀ x : SL(2, F₀), ((φ h)⁻¹ * ŝ) * φ x = φ x * ((φ h)⁻¹ * ŝ) := by
    intro x
    have h1 : α b (φ x) = φ (β b x) := hβ b x
    rw [hb, ← hh] at h1
    simp only [MulAut.conj_apply, map_mul, map_inv] at h1
    calc ((φ h)⁻¹ * ŝ) * φ x = (φ h)⁻¹ * (ŝ * φ x * ŝ⁻¹) * ŝ := by group
      _ = (φ h)⁻¹ * (φ h * φ x * (φ h)⁻¹) * ŝ := by rw [h1]
      _ = φ x * ((φ h)⁻¹ * ŝ) := by group
  have hcen := mem_center_of_commute_range h4 φ hφ _ hc
  have hu : α u ((φ h)⁻¹ * ŝ) = (φ h)⁻¹ * ŝ := apply_eq_of_mem_center (card_center_sl2 hodd) _ hcen
  apply hŝ
  have hŝeq : ŝ = φ h * ((φ h)⁻¹ * ŝ) := by group
  calc α u ŝ = α u (φ h * ((φ h)⁻¹ * ŝ)) := by rw [← hŝeq]
    _ = α u (φ h) * α u ((φ h)⁻¹ * ŝ) := map_mul _ _ _
    _ = φ h * ((φ h)⁻¹ * ŝ) := by rw [hufix, hu]
    _ = ŝ := hŝeq.symm

end NonInner

section PerfectLemmas

variable {G : Type} [Group G]

theorem false_of_perfect_le_commutative {T M : Subgroup G} (hMT : M ≤ T)
    (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hperf : ⁅M, M⁆ = M) (hM : M ≠ ⊥) : False := by
  apply hM
  rw [eq_bot_iff, ← hperf, Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [Subgroup.mem_bot, commutatorElement_def]
  have := hT g₁ (hMT h₁) g₂ (hMT h₂)
  rw [mul_assoc, this]
  group

theorem false_of_perfect_le_ext {E C M : Subgroup G} [E.Normal]
    (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hEC : E ⊔ C = ⊤) (hperf : ⁅M, M⁆ = M) (hM : M ≠ ⊥) : False := by
  set q := QuotientGroup.mk' E with hq
  have hqE : E.map q = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨e, he, rfl⟩
    exact (QuotientGroup.eq_one_iff e).2 he
  have htop : C.map q = ⊤ := by
    have h1 : (⊤ : Subgroup G).map q = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective E)
    rw [← hEC, Subgroup.map_sup, hqE, bot_sup_eq] at h1
    exact h1
  have hcomm : ∀ x y : G ⧸ E, x * y = y * x := by
    intro x y
    have hx : x ∈ C.map q := by rw [htop]; exact Subgroup.mem_top x
    have hy : y ∈ C.map q := by rw [htop]; exact Subgroup.mem_top y
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨c', hc', rfl⟩ := hy
    rw [← map_mul, ← map_mul, hC c hc c' hc']
  have hME : M ≤ E := by
    rw [← hperf, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    change q (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have := hcomm (q g₁) (q g₂)
    rw [mul_assoc, this]
    group
  exact false_of_perfect_le_commutative hME hE hperf hM

theorem perfect_le_of_card_le_two_mul [Finite G] {T M₁ M₂ : Subgroup G} (h1 : M₁ ≤ T)
    (h2 : M₂ ≤ T) (hperf : ⁅M₂, M₂⁆ = M₂)
    (hcard : Nat.card T = Nat.card M₁ ∨ Nat.card T = 2 * Nat.card M₁) : M₂ ≤ M₁ := by
  rcases hcard with hc | hc
  · have : T = M₁ := (Subgroup.eq_of_le_of_card_ge h1 hc.le).symm
    rw [← this]
    exact h2
  · set N : Subgroup ↥T := M₁.subgroupOf T with hN
    have hNcard : Nat.card N = Nat.card M₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1).toEquiv
    have hNidx : N.index = 2 := by
      have h := Subgroup.card_mul_index N
      rw [hNcard] at h
      have hpos : 0 < Nat.card M₁ := Nat.card_pos
      have : Nat.card M₁ * N.index = Nat.card M₁ * 2 := by rw [h, hc]; ring
      exact Nat.eq_of_mul_eq_mul_left hpos this
    have hNn : N.Normal := Subgroup.normal_of_index_eq_two hNidx
    have hqcard : Nat.card (↥T ⧸ N) = 2 := by
      rw [← Subgroup.index, hNidx]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc : IsCyclic (↥T ⧸ N) := isCyclic_of_prime_card hqcard
    have hcomm : ∀ x y : ↥T ⧸ N, x * y = y * x := fun x y => hcyc.commGroup.mul_comm x y
    rw [← hperf, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have key : ((⟨g₁, h2 hg₁⟩ : ↥T) * ⟨g₂, h2 hg₂⟩ * (⟨g₁, h2 hg₁⟩ : ↥T)⁻¹ * (⟨g₂, h2 hg₂⟩ : ↥T)⁻¹) ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      change (QuotientGroup.mk' N) _ = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have := hcomm ((QuotientGroup.mk' N) ⟨g₁, h2 hg₁⟩) ((QuotientGroup.mk' N) ⟨g₂, h2 hg₂⟩)
      rw [mul_assoc, this]
      group
    rw [commutatorElement_def]
    exact key

end PerfectLemmas

section RangeFacts

variable {K F₀ : Type} [Field K] [Finite K] [Field F₀] [Finite F₀]

theorem center_le_range (hodd : Odd (Nat.card K)) (hF₀odd : Odd (Nat.card F₀))
    (φ : SL(2, F₀) →* SL(2, K)) (hφ : Function.Injective φ) :
    Subgroup.center SL(2, K) ≤ φ.range := by
  have hZc := card_center_sl2 hodd
  have hZ₀c := card_center_sl2 hF₀odd
  obtain ⟨y, hy1, -⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center SL(2, F₀)))).1 hZ₀c
  have hy2 : (y : SL(2, F₀)) * y = 1 := mul_self_eq_one_of_mem_center hZ₀c y.2
  have hφy : φ y ∈ Subgroup.center SL(2, K) :=
    mem_center_of_mul_self_eq_one hodd (by rw [← map_mul, hy2, map_one])
  have hφy1 : φ y ≠ 1 := fun h => hy1 (Subtype.ext (hφ (h.trans (map_one φ).symm)))
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1]
    exact one_mem _
  · obtain ⟨w, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center SL(2, K)))).1 hZc
    have h1 : (⟨z, hz⟩ : ↥(Subgroup.center SL(2, K))) = w :=
      huniq _ (fun h => hz1 (congrArg Subtype.val h))
    have h2 : (⟨φ y, hφy⟩ : ↥(Subgroup.center SL(2, K))) = w :=
      huniq _ (fun h => hφy1 (congrArg Subtype.val h))
    have : z = φ y := congrArg Subtype.val (h1.trans h2.symm)
    rw [this]
    exact ⟨y, rfl⟩

theorem two_mul_card_range_mk (hodd : Odd (Nat.card K)) (hF₀odd : Odd (Nat.card F₀))
    (φ : SL(2, F₀) →* SL(2, K)) (hφ : Function.Injective φ) :
    2 * Nat.card ((QuotientGroup.mk' (Subgroup.center SL(2, K))).comp φ).range =
      Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := by
  set ψ := (QuotientGroup.mk' (Subgroup.center SL(2, K))).comp φ with hψ
  have hker : ψ.ker.map φ = Subgroup.center SL(2, K) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx)
    · intro hz
      obtain ⟨x, rfl⟩ := center_le_range hodd hF₀odd φ hφ hz
      exact ⟨x, MonoidHom.mem_ker.2 ((QuotientGroup.eq_one_iff _).2 hz), rfl⟩
  have hkcard : Nat.card ψ.ker = 2 := by
    rw [← Subgroup.card_map_of_injective hφ, hker, card_center_sl2 hodd]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hkcard,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F₀] at h1
  omega

omit [Finite K] in
theorem commutator_range_mk (h4 : 4 ≤ Nat.card F₀) (φ : SL(2, F₀) →* SL(2, K)) :
    ⁅((QuotientGroup.mk' (Subgroup.center SL(2, K))).comp φ).range,
      ((QuotientGroup.mk' (Subgroup.center SL(2, K))).comp φ).range⁆ =
      ((QuotientGroup.mk' (Subgroup.center SL(2, K))).comp φ).range := by
  have hperf : ⁅(⊤ : Subgroup SL(2, F₀)), (⊤ : Subgroup SL(2, F₀))⁆ = (⊤ : Subgroup SL(2, F₀)) := by
    have := (ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F₀ h4).commutator_eq_top
    rwa [commutator_def] at this
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]

end RangeFacts

section Dickson

theorem sup_eq_top_of_two_perfect {K : Type} [Field K] [Finite K]
    {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hfk : f = 2 * k)
    (h5 : 5 ≤ p ^ k) {M₁ M₂ : Subgroup (PSL2 K)}
    (hc1 : 2 * Nat.card M₁ = p ^ k * ((p ^ k) ^ 2 - 1))
    (hc2 : 2 * Nat.card M₂ = p ^ k * ((p ^ k) ^ 2 - 1)) (hperf1 : ⁅M₁, M₁⁆ = M₁)
    (hperf2 : ⁅M₂, M₂⁆ = M₂) (hne : M₁ ≠ M₂) : M₁ ⊔ M₂ = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hT
  set T := M₁ ⊔ M₂ with hTdef
  have hM1T : M₁ ≤ T := le_sup_left
  have hM2T : M₂ ≤ T := le_sup_right
  set r := p ^ k with hr
  set n := Nat.card M₁ with hn
  have hn2 : Nat.card M₂ = n := by omega
  have hr25 : 25 ≤ r ^ 2 := by nlinarith
  have hn60 : 60 ≤ n := by
    have : 5 * (r ^ 2 - 1) ≤ r * (r ^ 2 - 1) := Nat.mul_le_mul_right _ h5
    omega
  have hk0 : k ≠ 0 := by
    rintro h0
    rw [hr, h0, pow_zero] at h5
    omega
  have hf0 : f ≠ 0 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hnp : p ∣ n := by
    have h1 : p ∣ r * (r ^ 2 - 1) := Dvd.dvd.mul_right (dvd_pow_self p hk0) _
    rw [← hc1] at h1
    exact (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) h1)
  have hdvd : n ∣ Nat.card T := Subgroup.card_dvd_of_le hM1T
  have hM1ne : M₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hn
    omega
  have hkey : (Nat.card T = n ∨ Nat.card T = 2 * n) → False := by
    intro h
    apply hne
    have h21 : M₂ ≤ M₁ := perfect_le_of_card_le_two_mul hM1T hM2T hperf2 h
    exact (Subgroup.eq_of_le_of_card_ge h21 (by omega)).symm
  have hgcd : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨j, hj⟩ := hpodd.pow (n := f)
    rw [hj, show 2 * j + 1 - 1 = 2 * j by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 j)
  have hcomm_of : ∀ (hc : ∀ a b : T, a * b = b * a), ∀ x ∈ T, ∀ y ∈ T, x * y = y * x :=
    fun hc x hx y hy => congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hK T with
    ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, hz2, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, -, -, E, C, hE, hEel, -, hCcyc, -, -, hsup, -, -⟩ | ⟨m, hmf, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩
  · exact false_of_perfect_le_commutative hM1T
      (hcomm_of (fun a b => hel.toIsMulCommutative.is_comm.comm a b)) hperf1 hM1ne
  · exact false_of_perfect_le_commutative hM1T
      (hcomm_of (fun a b => hcyc.commGroup.mul_comm a b)) hperf1 hM1ne
  · rw [hgcd] at hz
    have hcard : Nat.card T = 2 * z := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have h1 : p ∣ 2 * z := by rw [← hcard]; exact hnp.trans hdvd
    exact not_dvd_of_dvd_half hp2 hf0 hz h1
  · have hcard : Nat.card T = 12 := by rw [Nat.card_congr e.toEquiv, card_alternatingFour']
    have := Nat.le_of_dvd (by omega) (hcard ▸ hdvd)
    omega
  · have hcard : Nat.card T = 24 := by rw [Nat.card_congr e.toEquiv, card_permFour]
    have := Nat.le_of_dvd (by omega) (hcard ▸ hdvd)
    omega
  · have hcard : Nat.card T = 60 := by rw [Nat.card_congr e.toEquiv, card_alternatingFive']
    have := Nat.le_of_dvd (by omega) (hcard ▸ hdvd)
    exact hkey (Or.inl (by omega))
  ·
    have hperfT : ⁅M₁.subgroupOf T, M₁.subgroupOf T⁆ = M₁.subgroupOf T := by
      apply Subgroup.map_injective T.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hM1T, hperf1]
    have hMne : M₁.subgroupOf T ≠ ⊥ := by
      intro h
      apply hM1ne
      rw [← Subgroup.map_subgroupOf_eq_of_le hM1T, h, Subgroup.map_bot]
    have : E.Normal := hE
    exact false_of_perfect_le_ext (E := E) (C := C) (M := M₁.subgroupOf T)
      (fun x hx y hy => congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      (fun x hx y hy => congrArg Subtype.val (hCcyc.commGroup.mul_comm ⟨x, hx⟩ ⟨y, hy⟩))
      hsup hperfT hMne
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hf0 (zero_dvd_iff.mp hmf)
    have hcard : Nat.card T = p ^ m * (p ^ (2 * m) - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv, card_psl2_galoisField hp2 hm0]
    have h2m := two_mul_le_of_psl2_shape hK hp2 hT hmf hcard
    have hmk : m ≤ k := by omega
    have h1 : p ^ m ≤ r := Nat.pow_le_pow_right hp.pos hmk
    have h2 : p ^ (2 * m) - 1 ≤ r ^ 2 - 1 := by
      have : p ^ (2 * m) ≤ r ^ 2 := by
        rw [hr, ← pow_mul, mul_comm k 2]
        exact Nat.pow_le_pow_right hp.pos (by omega)
      omega
    have h3 : p ^ m * (p ^ (2 * m) - 1) ≤ r * (r ^ 2 - 1) := Nat.mul_le_mul h1 h2
    have hle : Nat.card T ≤ n := by
      rw [hcard]
      omega
    have hge := Nat.le_of_dvd Nat.card_pos hdvd
    exact hkey (Or.inl (le_antisymm hle hge))
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hf0 (by simpa using hmf)
    have hcard : Nat.card T = p ^ m * (p ^ (2 * m) - 1) := by
      rw [Nat.card_congr e.toEquiv, card_pgl2_galoisField hm0]
    have h2m : 2 * m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hmf
    have hmk : m ≤ k := by omega
    have h1 : p ^ m ≤ r := Nat.pow_le_pow_right hp.pos hmk
    have h2 : p ^ (2 * m) - 1 ≤ r ^ 2 - 1 := by
      have : p ^ (2 * m) ≤ r ^ 2 := by
        rw [hr, ← pow_mul, mul_comm k 2]
        exact Nat.pow_le_pow_right hp.pos (by omega)
      omega
    have h3 : p ^ m * (p ^ (2 * m) - 1) ≤ r * (r ^ 2 - 1) := Nat.mul_le_mul h1 h2
    have hle : Nat.card T ≤ 2 * n := by
      rw [hcard]
      omega
    have hge : n ≤ Nat.card T := Nat.le_of_dvd Nat.card_pos hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hc1' : 1 ≤ c := by
      by_contra h0
      have : c = 0 := by omega
      rw [this, mul_zero] at hc
      exact Nat.card_pos.ne' hc
    have hc2' : c ≤ 2 := by nlinarith
    interval_cases c
    · exact hkey (Or.inl (by omega))
    · exact hkey (Or.inr (by omega))

end Dickson

section SupTop

variable {K F₀ : Type} [Field K] [Finite K] [Field F₀] [Finite F₀]

open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
theorem sup_range_eq_top {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hF₀ : Nat.card F₀ = p ^ k) (hfk : f = 2 * k) (h5 : 5 ≤ p ^ k)
    (φ₁ φ₂ : SL(2, F₀) →* SL(2, K)) (h1 : Function.Injective φ₁) (h2 : Function.Injective φ₂)
    (hne : φ₁.range ≠ φ₂.range) : φ₁.range ⊔ φ₂.range = ⊤ := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have hF₀odd : Odd (Nat.card F₀) := by
    rw [hF₀]
    exact (hp.odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card F₀ := by
    rw [hF₀]
    omega
  set Z := Subgroup.center SL(2, K) with hZ
  set π : SL(2, K) →* PSL2 K := QuotientGroup.mk' Z with hπ
  have hZ1 : Z ≤ φ₁.range := center_le_range hodd hF₀odd φ₁ h1
  have hZ2 : Z ≤ φ₂.range := center_le_range hodd hF₀odd φ₂ h2
  have hc1 := two_mul_card_range_mk hodd hF₀odd φ₁ h1
  have hc2 := two_mul_card_range_mk hodd hF₀odd φ₂ h2
  rw [hF₀] at hc1 hc2
  have hperf1 := commutator_range_mk (K := K) h4 φ₁
  have hperf2 := commutator_range_mk (K := K) h4 φ₂
  have hle : ∀ (φ φ' : SL(2, F₀) →* SL(2, K)), Z ≤ φ'.range →
      (π.comp φ).range ≤ (π.comp φ').range → φ.range ≤ φ'.range := by
    intro φ φ' hZφ' hM x hx
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨y', hy'⟩ := hM ⟨y, rfl⟩
    have hmem : (φ' y')⁻¹ * φ y ∈ Z := QuotientGroup.eq.1 hy'
    have : φ y = φ' y' * ((φ' y')⁻¹ * φ y) := by group
    rw [this]
    exact mul_mem ⟨y', rfl⟩ (hZφ' hmem)
  have hMne : (π.comp φ₁).range ≠ (π.comp φ₂).range := by
    intro hM
    apply hne
    exact le_antisymm (hle φ₁ φ₂ hZ2 hM.le) (hle φ₂ φ₁ hZ1 hM.ge)
  have htop : (π.comp φ₁).range ⊔ (π.comp φ₂).range = ⊤ :=
    sup_eq_top_of_two_perfect hp hp2 hK hfk h5 hc1 hc2 hperf1 hperf2 hMne
  have hperf : commutator SL(2, K) = ⊤ :=
    (ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K (by
      rw [hK, hfk]
      have : 5 ≤ p ^ k := h5
      have : 25 ≤ p ^ (2 * k) := by
        calc 25 = 5 ^ 2 := by norm_num
          _ ≤ (p ^ k) ^ 2 := Nat.pow_le_pow_left h5 2
          _ = p ^ (2 * k) := by rw [← pow_mul, mul_comm]
      omega)).commutator_eq_top
  have hcov : (φ₁.range ⊔ φ₂.range) ⊔ Z = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : π x ∈ (π.comp φ₁).range ⊔ (π.comp φ₂).range := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [MonoidHom.range_comp, MonoidHom.range_comp, ← Subgroup.map_sup] at hx
    obtain ⟨g, hg, hgx⟩ := hx
    have hmem : g⁻¹ * x ∈ Z := QuotientGroup.eq.1 hgx
    have : x = g * (g⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hg hmem
  exact eq_top_of_sup_center_eq_top hperf hcov

end SupTop

section Good

variable {K : Type} [Field K] [Finite K]

theorem eq_of_bad (hodd : Odd (Nat.card K)) {D : Subgroup (MulAut SL(2, K))}
    (hD : CFSG.IsElementaryAbelian 2 ↥D) {B : Subgroup ↥D} (hB4 : Nat.card ↥B = 4)
    (hBinn : ∀ b ∈ B, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s) (u : ↥D)
    {c₁ c₂ : ↥D} (hc₁ : c₁ ∈ B) (hc₂ : c₂ ∈ B)
    (hbad₁ : ∀ b ∈ B, ∀ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s →
      ((u * c₁ : ↥D) : MulAut SL(2, K)) s = s)
    (hbad₂ : ∀ b ∈ B, ∀ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s →
      ((u * c₂ : ↥D) : MulAut SL(2, K)) s = s) : c₁ = c₂ := by
  by_contra hne
  have hd : c₁⁻¹ * c₂ ∈ B := B.mul_mem (B.inv_mem hc₁) hc₂
  have hd1 : c₁⁻¹ * c₂ ≠ 1 := fun h => hne (inv_mul_eq_one.1 h)
  obtain ⟨a, b, ha1, hb1, hab, -⟩ :=
    GenLocL2.exists_klein_gens (GenLocBasic.isEA_subgroup hD B) hB4
  obtain ⟨b', hb'B, hb'1, hb'd⟩ : ∃ b' : ↥D, b' ∈ B ∧ b' ≠ 1 ∧ b' ≠ c₁⁻¹ * c₂ := by
    by_cases h : (a : ↥D) = c₁⁻¹ * c₂
    · refine ⟨b, b.2, fun h' => hb1 (Subtype.ext h'), fun h' => hab (Subtype.ext ?_)⟩
      rw [h, h']
    · exact ⟨a, a.2, fun h' => ha1 (Subtype.ext h'), h⟩
  obtain ⟨sd, hsd⟩ := hBinn _ hd
  obtain ⟨s', hs'⟩ := hBinn _ hb'B
  have h1 := hbad₂ b' hb'B s' hs'
  have h2 : ((u * c₂ : ↥D) : MulAut SL(2, K)) s' =
      sd * s' * sd⁻¹ := by
    have hmul : u * c₂ = (u * c₁) * (c₁⁻¹ * c₂) := by group
    rw [hmul]
    change ((u * c₁ : ↥D) : MulAut SL(2, K)) (((c₁⁻¹ * c₂ : ↥D) : MulAut SL(2, K)) s') = _
    rw [hsd, MulAut.conj_apply, map_mul, map_mul, map_inv,
      hbad₁ _ hd sd hsd, hbad₁ _ hb'B s' hs']
  have hcomm : sd * s' = s' * sd := by
    rw [h1] at h2
    calc sd * s' = (sd * s' * sd⁻¹) * sd := by group
      _ = s' * sd := by rw [← h2]
  exact not_commute_of_lifts hodd hD hsd hs' hd1 hb'1 (fun h => hb'd h.symm) hcomm

theorem exists_two_good (hodd : Odd (Nat.card K)) {D : Subgroup (MulAut SL(2, K))}
    (hD : CFSG.IsElementaryAbelian 2 ↥D) {B : Subgroup ↥D} (hB4 : Nat.card ↥B = 4)
    (hBinn : ∀ b ∈ B, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s) (u : ↥D) :
    ∃ c₁ ∈ B, ∃ c₂ ∈ B, c₁ ≠ c₂ ∧
      (∃ b ∈ B, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s ∧
        ((u * c₁ : ↥D) : MulAut SL(2, K)) s ≠ s) ∧
      (∃ b ∈ B, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s ∧
        ((u * c₂ : ↥D) : MulAut SL(2, K)) s ≠ s) := by
  obtain ⟨a, b, ha1, hb1, hab, -⟩ :=
    GenLocL2.exists_klein_gens (GenLocBasic.isEA_subgroup hD B) hB4
  have hbad : ∀ c ∈ B, (¬ ∃ b ∈ B, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s ∧
      ((u * c : ↥D) : MulAut SL(2, K)) s ≠ s) → ∀ b ∈ B, ∀ s : SL(2, K),
      (b : MulAut SL(2, K)) = MulAut.conj s → ((u * c : ↥D) : MulAut SL(2, K)) s = s := by
    intro c _ h b hb s hs
    by_contra hne
    exact h ⟨b, hb, s, hs, hne⟩
  have hone : (1 : ↥D) ∈ B := B.one_mem
  have h1a : (1 : ↥D) ≠ a := fun h => ha1 (Subtype.ext h.symm)
  have h1b : (1 : ↥D) ≠ b := fun h => hb1 (Subtype.ext h.symm)
  have hab' : (a : ↥D) ≠ b := fun h => hab (Subtype.ext h)
  have hunique : ∀ c₁ c₂ : ↥D, c₁ ∈ B → c₂ ∈ B → c₁ ≠ c₂ →
      (∃ b ∈ B, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s ∧
        ((u * c₁ : ↥D) : MulAut SL(2, K)) s ≠ s) ∨
      (∃ b ∈ B, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s ∧
        ((u * c₂ : ↥D) : MulAut SL(2, K)) s ≠ s) := by
    intro c₁ c₂ hc₁ hc₂ hne
    by_contra h
    push Not at h
    apply hne
    exact eq_of_bad hodd hD hB4 hBinn u hc₁ hc₂ h.1 h.2
  by_cases g1 : ∃ b ∈ B, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s ∧
      ((u * 1 : ↥D) : MulAut SL(2, K)) s ≠ s
  · by_cases ga : ∃ b' ∈ B, ∃ s : SL(2, K), (b' : MulAut SL(2, K)) = MulAut.conj s ∧
        ((u * (a : ↥D) : ↥D) : MulAut SL(2, K)) s ≠ s
    · exact ⟨1, hone, a, a.2, h1a, g1, ga⟩
    · have gb : ∃ b' ∈ B, ∃ s : SL(2, K), (b' : MulAut SL(2, K)) = MulAut.conj s ∧
          ((u * (b : ↥D) : ↥D) : MulAut SL(2, K)) s ≠ s := by
        rcases hunique a b a.2 b.2 hab' with h | h
        · exact absurd h ga
        · exact h
      exact ⟨1, hone, b, b.2, h1b, g1, gb⟩
  · have ga : ∃ b' ∈ B, ∃ s : SL(2, K), (b' : MulAut SL(2, K)) = MulAut.conj s ∧
        ((u * (a : ↥D) : ↥D) : MulAut SL(2, K)) s ≠ s := by
      rcases hunique 1 a hone a.2 h1a with h | h
      · exact absurd h g1
      · exact h
    have gb : ∃ b' ∈ B, ∃ s : SL(2, K), (b' : MulAut SL(2, K)) = MulAut.conj s ∧
        ((u * (b : ↥D) : ↥D) : MulAut SL(2, K)) s ≠ s := by
      rcases hunique 1 b hone b.2 h1b with h | h
      · exact absurd h g1
      · exact h
    exact ⟨a, a.2, b, b.2, hab', ga, gb⟩

end Good

section CardFixed

theorem card_fixedField_eq {K : Type} [Field K] [Finite K] {p f k : ℕ} (hK : Nat.card K = p ^ f)
    (hfk : f = 2 * k) (σ : K ≃+* K) (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Nat.card ↥(fixedField σ) = p ^ k := by
  have h1 := card_fixedField_sq σ hσσ hσ1
  rw [hK, hfk, pow_mul'] at h1
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h1

end CardFixed

section Block

variable {K : Type} [Field K] [Finite K]

theorem subfield_block {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hfk : f = 2 * k) (h5 : 5 ≤ p ^ k) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) {D : Subgroup (MulAut SL(2, K))} [Finite ↥D]
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (h8 : Nat.card ↥D = 8) (σ : K ≃+* K) (hσσ : σ * σ = 1)
    (hσ1 : σ ≠ 1) (u : ↥D) (hu1 : u ≠ 1)
    (hσu : (gammaOf hodd h3 (u : MulAut SL(2, K))).right = σ)
    (hgood : ∃ b : ↥D, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s ∧
      (u : MulAut SL(2, K)) s ≠ s) :
    ∃ (φ : SL(2, ↥(fixedField σ)) →* SL(2, K)) (β : ↥D →* MulAut SL(2, ↥(fixedField σ))),
      Function.Injective φ ∧ (∀ x, (u : MulAut SL(2, K)) (φ x) = φ x) ∧
      (∀ (d : ↥D) (x : SL(2, ↥(fixedField σ))), (d : MulAut SL(2, K)) (φ x) = φ (β d x)) ∧
      gammaAct β = ⊤ := by
  have hu2 : (u : MulAut SL(2, K)) * (u : MulAut SL(2, K)) = 1 :=
    congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD u)
  obtain ⟨φ, hφinj, hφfix, hφrange⟩ :=
    exists_subfield_data hodd h3 (u : MulAut SL(2, K)) hu2 σ hσu hσ1
  have hcard : Nat.card ↥(fixedField σ) = p ^ k := card_fixedField_eq hK hfk σ hσσ hσ1
  have hinv : ∀ (d : ↥D) (x : SL(2, ↥(fixedField σ))),
      ∃ y : SL(2, ↥(fixedField σ)), φ y = D.subtype d (φ x) := by
    intro d x
    have hcomm : (u : MulAut SL(2, K)) * (d : MulAut SL(2, K)) =
        (d : MulAut SL(2, K)) * (u : MulAut SL(2, K)) := congrArg Subtype.val (mul_comm' u d)
    have hfix : (u : MulAut SL(2, K)) ((d : MulAut SL(2, K)) (φ x)) = (d : MulAut SL(2, K)) (φ x) := by
      have := congrArg (fun ψ : MulAut SL(2, K) => ψ (φ x)) hcomm
      simp only [MulAut.mul_apply] at this
      rw [this, hφfix x]
    exact hφrange _ hfix
  obtain ⟨β, hβ⟩ := exists_equivariant_action φ hφinj D.subtype hinv
  have hβu : β u = 1 := by
    refine MulEquiv.ext fun x => ?_
    apply hφinj
    have := hβ u x
    change (u : MulAut SL(2, K)) (φ x) = φ (β u x) at this
    rw [← this, hφfix x]
    rfl
  have h4 : 4 ≤ Nat.card ↥(fixedField σ) := by
    rw [hcard]
    omega
  have hnoninn : ∃ d : ↥D, β d ∉ (MulAut.conj : SL(2, ↥(fixedField σ)) →*
      MulAut SL(2, ↥(fixedField σ))).range := by
    obtain ⟨b, s, hb, hs⟩ := hgood
    refine ⟨b, noninner_of_not_fixed hodd h4 φ hφinj D.subtype β hβ u b hφfix s hb hs⟩
  refine ⟨φ, β, hφinj, hφfix, hβ, ?_⟩
  exact gammaAct_eq_top_of_trivial_two hp hp2 hcard h5 hD h8 β u hu1 hβu hnoninn

end Block

section Core

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem range_ne_of_ne {F₀ : Type} [Field F₀] [Finite F₀] (h4 : 4 ≤ Nat.card F₀)
    {D : Subgroup (MulAut SL(2, K))} {B : Subgroup ↥D}
    (hBinn : ∀ b ∈ B, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s) (u : ↥D)
    {c₁ c₂ : ↥D} (hc₁ : c₁ ∈ B) (hc₂ : c₂ ∈ B) (hc12 : c₁ ≠ c₂)
    (φ₁ φ₂ : SL(2, F₀) →* SL(2, K)) (h1 : Function.Injective φ₁)
    (hfix₁ : ∀ x, ((u * c₁ : ↥D) : MulAut SL(2, K)) (φ₁ x) = φ₁ x)
    (hfix₂ : ∀ x, ((u * c₂ : ↥D) : MulAut SL(2, K)) (φ₂ x) = φ₂ x) :
    φ₁.range ≠ φ₂.range := by
  intro heq
  have hd : c₁⁻¹ * c₂ ∈ B := B.mul_mem (B.inv_mem hc₁) hc₂
  have hd1 : c₁⁻¹ * c₂ ≠ 1 := fun h => hc12 (inv_mul_eq_one.1 h)
  obtain ⟨s₀, hs₀⟩ := hBinn _ hd
  have hmul : (c₁⁻¹ * c₂ : ↥D) = (u * c₁)⁻¹ * (u * c₂) := by group
  have hfixd : ∀ y, ((c₁⁻¹ * c₂ : ↥D) : MulAut SL(2, K)) (φ₁ y) = φ₁ y := by
    intro y
    have hy2 : φ₁ y ∈ φ₂.range := by rw [← heq]; exact ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := hy2
    have hu2 : ((u * c₂ : ↥D) : MulAut SL(2, K)) (φ₁ y) = φ₁ y := by
      rw [← hy']
      exact hfix₂ y'
    rw [hmul]
    change (((u * c₁ : ↥D) : MulAut SL(2, K))⁻¹ * ((u * c₂ : ↥D) : MulAut SL(2, K))) (φ₁ y) = φ₁ y
    rw [MulAut.mul_apply, hu2]
    have h3 := hfix₁ y
    calc (((u * c₁ : ↥D) : MulAut SL(2, K))⁻¹) (φ₁ y)
        = ((u * c₁ : ↥D) : MulAut SL(2, K))⁻¹ (((u * c₁ : ↥D) : MulAut SL(2, K)) (φ₁ y)) := by rw [h3]
      _ = φ₁ y := by simp
  have hc : ∀ y, s₀ * φ₁ y = φ₁ y * s₀ := by
    intro y
    have h := hfixd y
    rw [hs₀, MulAut.conj_apply] at h
    calc s₀ * φ₁ y = (s₀ * φ₁ y * s₀⁻¹) * s₀ := by group
      _ = φ₁ y * s₀ := by rw [h]
  have hcen := mem_center_of_commute_range h4 φ₁ h1 s₀ hc
  apply hd1
  apply Subtype.ext
  rw [hs₀, (GenLocL2Small.conj_eq_one_iff s₀).2 hcen]
  rfl

end Core

section Eight

theorem gammaAct_sl2_subtype_eq_top_of_card_eight
    {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h25 : 25 ≤ p ^ f)
    (D : Subgroup (MulAut SL(2, K))) (hD : CFSG.IsElementaryAbelian 2 ↥D) (h8 : Nat.card ↥D = 8) :
    gammaAct D.subtype = ⊤ := by
  have : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at h25
      omega
    · exact h0
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h3 : 3 < Nat.card K := by
    rw [hK]
    omega
  have hOPP : IsOddPrimePower (Nat.card K) := isOddPrimePower_of hp hp2 hf1 hK
  set ι : ↥D →* PGammaL2 K := (gammaOf hodd h3).comp D.subtype with hι
  have hιinj : Function.Injective ι :=
    (gammaOf_injective hodd h3).comp Subtype.val_injective
  obtain ⟨B, hB4, hBψ, hBfield⟩ := exists_klein_of_card_eight hOPP hD h8 ι hιinj
  have hBinn : ∀ b ∈ B, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s :=
    fun b hb => inner_of_mem_pslRange_sl2 hodd h3 _ (hBψ b hb)
  obtain ⟨u, hu⟩ : ∃ u : ↥D, u ∉ B := by
    by_contra h
    push Not at h
    have : B = ⊤ := eq_top_iff.2 fun x _ => h x
    rw [this, Subgroup.card_top, h8] at hB4
    omega
  have hu1 : u ≠ 1 := fun h => hu (h ▸ B.one_mem)
  set σ := (ι u).right with hσdef
  have hσ1 : σ ≠ 1 := hBfield u hu
  have hsq : ∀ x : ↥D, x * x = 1 := fun x =>
    WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD x
  have hσσ : σ * σ = 1 := by
    have h1 : ι u * ι u = 1 := by rw [← map_mul, hsq u, map_one]
    have h2 := congrArg SemidirectProduct.right h1
    simpa using h2
  have hfeven : ∃ k, f = 2 * k := by
    have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσσ) hσ1
    have hdvd : orderOf σ ∣ f := by
      have := orderOf_dvd_natCard σ
      rwa [card_ringAut K hp hK] at this
    rw [hord] at hdvd
    exact hdvd
  obtain ⟨k, hfk⟩ := hfeven
  have h5 : 5 ≤ p ^ k := by
    have h1 : p ^ f = (p ^ k) ^ 2 := by rw [hfk, pow_mul']
    by_contra hlt
    push Not at hlt
    have h2 : (p ^ k) ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    norm_num at h2
    omega
  obtain ⟨c₁, hc₁, c₂, hc₂, hc12, ⟨b₁, hb₁, s₁, hbs₁, hs₁⟩, ⟨b₂, hb₂, s₂, hbs₂, hs₂⟩⟩ :=
    exists_two_good hodd hD hB4 hBinn u
  have hblock : ∀ c ∈ B, (∃ b ∈ B, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s ∧
      ((u * c : ↥D) : MulAut SL(2, K)) s ≠ s) →
      ∃ (φ : SL(2, ↥(fixedField σ)) →* SL(2, K))
        (β : ↥D →* MulAut SL(2, ↥(fixedField σ))), Function.Injective φ ∧
        (∀ x, ((u * c : ↥D) : MulAut SL(2, K)) (φ x) = φ x) ∧
        (∀ (d : ↥D) (x : SL(2, ↥(fixedField σ))), (d : MulAut SL(2, K)) (φ x) = φ (β d x)) ∧
        gammaAct β = ⊤ := by
    intro c hc hgood
    refine subfield_block hp hp2 hK hfk h5 hodd h3 hD h8 σ hσσ hσ1 (u * c) ?_ ?_ ?_
    · intro h
      apply hu
      have : u = c⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact B.inv_mem hc
    · change (ι (u * c)).right = σ
      rw [map_mul, SemidirectProduct.mul_right]
      have hc1 : (ι c).right = 1 := ((mem_pslRange_iff _).1 (hBψ c hc)).1
      rw [hc1, mul_one]
    · obtain ⟨b, hb, s, hs, hne⟩ := hgood
      exact ⟨b, s, hs, hne⟩
  obtain ⟨φ₁, β₁, hφ₁, hfix₁, hβ₁, hgen₁⟩ := hblock c₁ hc₁ ⟨b₁, hb₁, s₁, hbs₁, hs₁⟩
  obtain ⟨φ₂, β₂, hφ₂, hfix₂, hβ₂, hgen₂⟩ := hblock c₂ hc₂ ⟨b₂, hb₂, s₂, hbs₂, hs₂⟩
  have hF₀ : Nat.card ↥(fixedField σ) = p ^ k := card_fixedField_eq hK hfk σ hσσ hσ1
  have h4 : 4 ≤ Nat.card ↥(fixedField σ) := by
    rw [hF₀]
    omega
  have hne : φ₁.range ≠ φ₂.range :=
    range_ne_of_ne h4 hBinn u hc₁ hc₂ hc12 φ₁ φ₂ hφ₁ hfix₁ hfix₂
  have htop : φ₁.range ⊔ φ₂.range = ⊤ :=
    sup_range_eq_top hp hp2 hK hF₀ hfk h5 φ₁ φ₂ hφ₁ hφ₂ hne
  refine gammaAct_eq_top_of_equivariant D.subtype (ι := Bool)
    (fun _ => SL(2, ↥(fixedField σ))) (fun b => cond b φ₁ φ₂) (fun b => cond b β₁ β₂) ?_ ?_ ?_
  · intro b a x
    cases b
    · exact hβ₂ a x
    · exact hβ₁ a x
  · rw [iSup_bool_eq]
    exact htop
  · intro b
    cases b
    · exact hgen₂
    · exact hgen₁

end Eight

end GenLocL2SL3
section L2SL3

variable {A : Type} [Group A] [Finite A]

theorem gammaAct_sl2_rank3
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h25 : 25 ≤ p ^ f)
    (α : A →* MulAut (SL(2, K))) (hA : IsRank23 A) (hk : pRank 2 A = 3) : gammaAct α = ⊤ := by
  have _ := hk
  by_cases hker : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ α.ker
  · obtain ⟨E, hE, hle⟩ := hker
    exact gammaAct_eq_top_of_le_ker α hE hle
  push Not at hker
  obtain ⟨hD, hγ, -⟩ := range_reduction α hA (fun E hE hle => hker E hE hle)
  rw [hγ]
  have : Finite ↥α.range := Finite.of_surjective _ α.rangeRestrict_surjective
  rcases hD.2 with hr2 | hr3
  · have h4 : Nat.card α.range = 4 := by
      rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr2]
      norm_num
    rcases GenLocL2SL.gammaAct_sl2_core hp hp2 hK (by omega) hD.1 h4 α.range.subtype with h | ⟨hq, -⟩
    · exact h
    · exfalso
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      omega
  · have h8 : Nat.card α.range = 8 := by
      rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr3]
      norm_num
    exact GenLocL2SL3.gammaAct_sl2_subtype_eq_top_of_card_eight hp hp2 hK h25 α.range hD.1 h8

end L2SL3

end CFSG.GH74.Generic.BProg.B2
