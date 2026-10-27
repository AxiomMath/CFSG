module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidity

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)

section TwoElements

variable {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem eq_of_pow_two_pow_eq_of_charTwo {x y : K} {m : ℕ} (h : x ^ 2 ^ m = y ^ 2 ^ m) : x = y := by
  have h1 : (x - y) ^ 2 ^ m = 0 := by rw [sub_pow_char_pow, h, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (by positivity)).1 h1)

theorem exists_conjAut_eq_mulAut_conj_of_pow (hn : 3 ≤ n) (A : GL (Fin n) K) {m : ℕ}
    (hA : conjAut n K A ^ 2 ^ m = 1) :
    ∃ y : projectiveSL n K, conjAut n K A = MulAut.conj y := by
  have hA2 : conjAut n K (A ^ 2 ^ m) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_pow, hA]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 hA2
  have hinj : Function.Injective (fun x : Kˣ => x ^ 2 ^ m) := fun x y hxy => by
    apply Units.ext
    apply eq_of_pow_two_pow_eq_of_charTwo (m := m)
    have h := congrArg Units.val hxy
    simpa only [Units.val_pow_eq_pow_val] using h
  obtain ⟨κ, hκ⟩ := (Finite.injective_iff_surjective.1 hinj) c
  have hκ' : κ ^ 2 ^ m = c := hκ
  set s : GL (Fin n) K := Matrix.GeneralLinearGroup.scalar (Fin n) κ⁻¹ with hs
  set B : GL (Fin n) K := A * s with hB
  have hcomm : Commute A s := (Matrix.GeneralLinearGroup.scalar_commute κ⁻¹ A).symm
  have hB1 : B ^ 2 ^ m = 1 := by
    rw [hB, hcomm.mul_pow, ← hc, hs, ← map_pow, ← map_mul, inv_pow, hκ', mul_inv_cancel, map_one]
  have hdet : (B : Matrix (Fin n) (Fin n) K).det = 1 := by
    apply eq_of_pow_two_pow_eq_of_charTwo (m := m)
    rw [one_pow, ← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hB1, Units.val_one, Matrix.det_one]
  set B' : Matrix.SpecialLinearGroup (Fin n) K := ⟨B, hdet⟩ with hB'
  have hBB' : Matrix.SpecialLinearGroup.toGL B' = B := Units.ext rfl
  refine ⟨proj n K B', ?_⟩
  rw [← conjAut_toGL, hBB', hB, map_mul, hs, conjAut_scalar, mul_one]

end TwoElements

section Commutators

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  [Finite K] [CharP K 2]

theorem exists_eq_or_eq_mul_of_normalizerAut_eq_conjAut (hn : 3 ≤ n) (e : L ≃* projectiveSL n K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {s : G}
    (hs : s ∈ centralizer ({t} : Set G)) {m : ℕ} (hsm : s ^ 2 ^ m = 1) {A : GL (Fin n) K}
    (hA : normalizerAut e ⟨s, hCN hs⟩ = conjAut n K A) :
    ∃ l ∈ L, s = l ∨ s = l * t := by
  have hLt : L ≤ centralizer ({t} : Set G) :=
    le_centralizer_of_mem_centralizer (mem_centralizer_of_inf_eq_zpowers hKt)
  have hA' : conjAut n K A ^ 2 ^ m = 1 := by
    rw [← hA, ← map_pow]
    have h1 : (⟨s, hCN hs⟩ : normalizer (L : Set G)) ^ 2 ^ m = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hsm)
    rw [h1, map_one]
  obtain ⟨p, hp⟩ := exists_conjAut_eq_mulAut_conj_of_pow hn A hA'
  refine ⟨e.symm p, (e.symm p).2, eq_or_eq_mul_of_conj_eq' hLt ht hKt hs (e.symm p).2
    fun y hy => ?_⟩
  have h1 := coe_symm_normalizerAut_apply e ⟨s, hCN hs⟩ ⟨y, hy⟩
  rw [hA, hp, MulAut.conj_apply] at h1
  have h2 : e.symm (p * e ⟨y, hy⟩ * p⁻¹) = e.symm p * ⟨y, hy⟩ * (e.symm p)⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rw [h2] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  exact h1.symm

omit [Finite G] [Finite K] [CharP K 2] in
theorem commutator_mem_of_eq_or_eq_mul {t y z l : G} (hl : l ∈ L) (hy : y = l ∨ y = l * t)
    (hzN : z ∈ normalizer (L : Set G)) (hzt : z ∈ centralizer ({t} : Set G)) :
    y * z * y⁻¹ * z⁻¹ ∈ L := by
  have hzl : z * l⁻¹ * z⁻¹ ∈ L := (mem_normalizer_iff.1 hzN l⁻¹).1 (L.inv_mem hl)
  have hzt' : z * t = t * z := mem_centralizer_singleton_iff.1 hzt
  have hlz : l * z * l⁻¹ * z⁻¹ ∈ L := by
    have e : l * z * l⁻¹ * z⁻¹ = l * (z * l⁻¹ * z⁻¹) := by group
    rw [e]
    exact L.mul_mem hl hzl
  rcases hy with rfl | rfl
  · exact hlz
  · have e : l * t * z * (l * t)⁻¹ * z⁻¹ = l * z * l⁻¹ * z⁻¹ := by
      calc l * t * z * (l * t)⁻¹ * z⁻¹ = l * (t * z) * t⁻¹ * l⁻¹ * z⁻¹ := by group
        _ = l * (z * t) * t⁻¹ * l⁻¹ * z⁻¹ := by rw [hzt']
        _ = l * z * l⁻¹ * z⁻¹ := by group
    rw [e]
    exact hlz

theorem commutator_mem_of_fieldComponent_eq_one (hn : 3 ≤ n) (e : L ≃* projectiveSL n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSt : S ≤ centralizer ({t} : Set G))
    (hfc : ∀ (s : G) (hs : s ∈ S), fieldComponent hn e ⟨s, hCN (hSt hs)⟩ = 1) :
    ∀ y ∈ S, ∀ z ∈ S, y * z * y⁻¹ * z⁻¹ ∈ L := by
  have hpow : ∀ s ∈ S, ∃ m : ℕ, s ^ 2 ^ m = 1 := fun s hs => by
    obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hinner : ∀ s (hs : s ∈ S) (A : GL (Fin n) K),
      normalizerAut e ⟨s, hCN (hSt hs)⟩ = conjAut n K A → ∃ l ∈ L, s = l ∨ s = l * t := by
    intro s hs A hA
    obtain ⟨m, hm⟩ := hpow s hs
    exact exists_eq_or_eq_mul_of_normalizerAut_eq_conjAut hn e ht hKt hCN (hSt hs) hm hA
  have hform : ∀ s (hs : s ∈ S), ∃ (A : GL (Fin n) K) (ε : ℕ), ε ≤ 1 ∧
      normalizerAut e ⟨s, hCN (hSt hs)⟩ = conjAut n K A * dualAut n K ^ ε := fun s hs =>
    (linearFieldPart_eq_one_iff hn _).1 (hfc s hs)
  intro y hy z hz
  obtain ⟨A, ε, hε, hA⟩ := hform y hy
  obtain ⟨B, η, hη, hB⟩ := hform z hz
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hA
    obtain ⟨l, hl, hyl⟩ := hinner y hy A hA
    exact commutator_mem_of_eq_or_eq_mul hl hyl (hCN (hSt hz)) (hSt hz)
  rcases (by omega : η = 0 ∨ η = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hB
    obtain ⟨l, hl, hzl⟩ := hinner z hz B hB
    have h := commutator_mem_of_eq_or_eq_mul hl hzl (hCN (hSt hy)) (hSt hy)
    have e' : y * z * y⁻¹ * z⁻¹ = (z * y * z⁻¹ * y⁻¹)⁻¹ := by group
    rw [e']
    exact L.inv_mem h
  have hd : y * z⁻¹ ∈ S := S.mul_mem hy (S.inv_mem hz)
  have hdA : normalizerAut e ⟨y * z⁻¹, hCN (hSt hd)⟩ = conjAut n K (A * B⁻¹) := by
    have h1 : (⟨y * z⁻¹, hCN (hSt hd)⟩ : normalizer (L : Set G)) =
        ⟨y, hCN (hSt hy)⟩ * (⟨z, hCN (hSt hz)⟩ : normalizer (L : Set G))⁻¹ := rfl
    rw [h1, map_mul, map_inv, hA, hB, pow_one, map_mul, map_inv]
    group
  obtain ⟨l, hl, hdl⟩ := hinner _ hd _ hdA
  have h := commutator_mem_of_eq_or_eq_mul hl hdl (hCN (hSt hz)) (hSt hz)
  have e' : y * z * y⁻¹ * z⁻¹ = y * z⁻¹ * z * (y * z⁻¹)⁻¹ * z⁻¹ := by group
  rw [e']
  exact h

theorem exists_fieldComponent_ne_one_of_commutator_not_mem (hn : 3 ≤ n)
    (e : L ≃* projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSt : S ≤ centralizer ({t} : Set G))
    (hcomm : ∃ y ∈ S, ∃ z ∈ S, y * z * y⁻¹ * z⁻¹ ∉ L) :
    ∃ (s : G) (hs : s ∈ normalizer (L : Set G)), s ∈ S ∧ fieldComponent hn e ⟨s, hs⟩ ≠ 1 := by
  by_contra hno
  push Not at hno
  obtain ⟨y, hy, z, hz, hyz⟩ := hcomm
  exact hyz (commutator_mem_of_fieldComponent_eq_one hn e ht hKt hCN hS2 hSt
    (fun s hs => hno s (hCN (hSt hs)) hs) y hy z hz)

end Commutators

section Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_transvection_of_innerGraphFieldRigid (hset : SeitzSetting G L)
    {n f : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* projectiveSL n K)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range)
    (hU : ∀ (U : Sylow 2 L) {z : L}, z ≠ 1 → (∀ u ∈ (U : Subgroup L), u * z = z * u) →
      IsInvolutionClass 1 (e z))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hFR : InnerGraphFieldRigid K (Nat.le_of_succ_le hn))
    (hB2f : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) →
      ∀ hg : g⁻¹ * t * g ∈ normalizer (L : Set G),
        fieldComponent (Nat.le_of_succ_le hn) e ⟨g⁻¹ * t * g, hg⟩ ≠ 1 →
          ∃ (h : G) (z : L), IsInvolutionClass 1 (e z) ∧ h⁻¹ * t * h = t * (z : G)) :
    ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G) := by
  have := charP_two_of_card_eq_two_pow hK
  have hn3 : 3 ≤ n := Nat.le_of_succ_le hn
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  have hCN := centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
  by_contra hno
  rcases exists_conj_eq_mul_transvection_or_residual hset hn hK e hAutU hU ht hKt with h | h
  · exact hno h
  obtain ⟨S, hSt, hcomm⟩ := h
  have hS := exists_fieldComponent_ne_one_of_commutator_not_mem hn3 e ht hKt hCN S.isPGroup' hSt
    hcomm
  refine false_of_innerGraphFieldRigid hset hn3 e ht hKt hFR (fun g hg hgN => ?_) S hSt hS
  by_contra hne
  exact hno (hB2f g hg hgN hne)

end Assembly

end CFSG.SeitzReduction.LinearPilot
