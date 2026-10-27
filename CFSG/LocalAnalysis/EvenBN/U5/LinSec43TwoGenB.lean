module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBDiagonal
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43TwoGenA

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinT43

open Subgroup Matrix
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule
open scoped MatrixGroups

variable {G : Type*} [Group G]

private theorem conj_sub_one {k : Type*} [Field k] {Gm Gi U : Matrix (Fin 2) (Fin 2) k}
    (h1 : Gm * Gi = 1) : Gm * U * Gi - 1 = Gm * (U - 1) * Gi := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, h1]

private theorem conj_mul_sub_one_eq_zero {k : Type*} [Field k]
    {Gm Gi U U' : Matrix (Fin 2) (Fin 2) k} (h1 : Gm * Gi = 1) (h2 : Gi * Gm = 1)
    (hUU : (U' - 1) * (U - 1) = 0) :
    (Gm * U' * Gi - 1) * (Gm * U * Gi - 1) = 0 := by
  rw [conj_sub_one h1, conj_sub_one h1]
  calc Gm * (U' - 1) * Gi * (Gm * (U - 1) * Gi)
      = Gm * (U' - 1) * (Gi * Gm) * (U - 1) * Gi := by simp only [Matrix.mul_assoc]
    _ = Gm * ((U' - 1) * (U - 1)) * Gi := by
        rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = 0 := by rw [hUU]; simp

private theorem upperElt_sub_one_mul_eq_zero {k : Type*} [Field k] (s t : k) :
    (((upperElt k s : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) - 1) *
      (((upperElt k t : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) - 1) = 0 := by
  rw [coe_upperElt, coe_upperElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem commute_comm_of_mulVec {k : Type*} [Field k]
    {θ0 : (Fin 2 → k) → G} (hadd : ∀ v w, θ0 (v + w) = θ0 v * θ0 w)
    {p p' : G} {M M' : Matrix (Fin 2) (Fin 2) k}
    (hM : ∀ v, p * θ0 v * p⁻¹ = θ0 (M *ᵥ v)) (hM' : ∀ v, p' * θ0 v * p'⁻¹ = θ0 (M' *ᵥ v))
    (hMM : (M' - 1) * (M - 1) = 0) (v : Fin 2 → k) :
    Commute p' (p * θ0 v * p⁻¹ * (θ0 v)⁻¹) := by
  have h2 : M *ᵥ v = (M - 1) *ᵥ v + v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  have h3 : p * θ0 v * p⁻¹ * (θ0 v)⁻¹ = θ0 ((M - 1) *ᵥ v) := by
    rw [hM v, h2, hadd, mul_inv_cancel_right]
  have h4 : M' *ᵥ ((M - 1) *ᵥ v) = (M - 1) *ᵥ v := by
    have h5 : (M' - 1) *ᵥ ((M - 1) *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, hMM, Matrix.zero_mulVec]
    rw [Matrix.sub_mulVec M' 1 _, Matrix.one_mulVec, sub_eq_zero] at h5
    exact h5
  have h6 : p' * θ0 ((M - 1) *ᵥ v) * p'⁻¹ = θ0 ((M - 1) *ᵥ v) := by
    rw [hM', h4]
  rw [h3]
  exact mul_inv_eq_iff_eq_mul.mp h6

private theorem comm_prod_eq {p a a' : G} (hac : Commute a a')
    (hY : Commute a (p * a' * p⁻¹)) :
    p * (a * a') * p⁻¹ * (a * a')⁻¹ = (p * a * p⁻¹ * a⁻¹) * (p * a' * p⁻¹ * a'⁻¹) := by
  have e1 : (a * a')⁻¹ = a⁻¹ * a'⁻¹ := by
    rw [_root_.mul_inv_rev, hac.inv_inv.eq]
  have hY' : a⁻¹ * (p * a' * p⁻¹) = (p * a' * p⁻¹) * a⁻¹ := hY.inv_left.eq
  calc p * (a * a') * p⁻¹ * (a * a')⁻¹
      = (p * a * p⁻¹) * ((p * a' * p⁻¹) * a⁻¹) * a'⁻¹ := by rw [e1]; group
    _ = (p * a * p⁻¹) * (a⁻¹ * (p * a' * p⁻¹)) * a'⁻¹ := by rw [hY']
    _ = (p * a * p⁻¹ * a⁻¹) * (p * a' * p⁻¹ * a'⁻¹) := by group

private theorem fixed_of_mem {k : Type*} [Field k] {B : Subgroup G} {θ : (Fin 2 → k) → G}
    {p a : G} {M : Matrix (Fin 2) (Fin 2) k}
    (hadd : ∀ v w, (θ v * θ w)⁻¹ * θ (v + w) ∈ B) (hinj : ∀ v, θ v ∈ B → v = 0)
    (hM : ∀ v, (θ (M *ᵥ v))⁻¹ * (p * θ v * p⁻¹) ∈ B)
    (hpB : ∀ b ∈ B, p * b * p⁻¹ ∈ B) (ha : (p * a * p⁻¹)⁻¹ * a ∈ B)
    {v : Fin 2 → k} (hv : (θ v)⁻¹ * a ∈ B) : M *ᵥ v = v := by
  have h2 : (p * θ v * p⁻¹)⁻¹ * (p * a * p⁻¹) ∈ B := by
    have e : (p * θ v * p⁻¹)⁻¹ * (p * a * p⁻¹) = p * ((θ v)⁻¹ * a) * p⁻¹ := by group
    rw [e]
    exact hpB _ hv
  have h1 : (θ (M *ᵥ v))⁻¹ * a ∈ B := by
    have e : (θ (M *ᵥ v))⁻¹ * a =
        ((θ (M *ᵥ v))⁻¹ * (p * θ v * p⁻¹)) * ((p * θ v * p⁻¹)⁻¹ * (p * a * p⁻¹)) *
          ((p * a * p⁻¹)⁻¹ * a) := by group
    rw [e]
    exact mul_mem (mul_mem (hM v) h2) ha
  have h3 : (θ (M *ᵥ v))⁻¹ * θ v ∈ B := by
    have e : (θ (M *ᵥ v))⁻¹ * θ v = ((θ (M *ᵥ v))⁻¹ * a) * ((θ v)⁻¹ * a)⁻¹ := by group
    rw [e]
    exact mul_mem h1 (inv_mem hv)
  exact (eq_of_inv_mul_mem_of_add hadd hinj h3).symm

theorem sylow_mul_sub_one_eq_zero [Finite G] {k : Type*} [Field k] [Finite k] {m : ℕ}
    (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m) {R : Subgroup G} (φ : R ≃* SL(2, k))
    {P₀ : Subgroup G} (hP₀ : IsSylowOf 2 P₀ R) {p p' : G} (hp : p ∈ P₀) (hp' : p' ∈ P₀)
    (hpR : p ∈ R) (hp'R : p' ∈ R) :
    ((φ ⟨p', hp'R⟩ : SL(2, k)) - 1 : Matrix (Fin 2) (Fin 2) k) *
      ((φ ⟨p, hpR⟩ : SL(2, k)) - 1 : Matrix (Fin 2) (Fin 2) k) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxR, hPx⟩ := Prelim.exists_conj_of_isSylowOf
    (Prelim.isSylowOf_ofSL_upperUnipotent hk hm φ) hP₀
  have hroot : ∀ q ∈ P₀, ∀ hqR : q ∈ R, ∃ t : k,
      φ ⟨q, hqR⟩ = φ ⟨x, hxR⟩ * upperElt k t * (φ ⟨x, hxR⟩)⁻¹ := by
    intro q hq hqR
    rw [hPx] at hq
    obtain ⟨r, hr, hrq⟩ := Subgroup.mem_map.mp hq
    have hrR : r ∈ R := Prelim.ofSL_le φ _ hr
    obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff k).1
      ((Prelim.coe_mem_ofSL_iff (S := CFSG.Timmesfeld.upperUnipotent k) φ ⟨r, hrR⟩).mp hr)
    refine ⟨t, ?_⟩
    have hq_eq : (⟨q, hqR⟩ : R) = ⟨x, hxR⟩ * ⟨r, hrR⟩ * (⟨x, hxR⟩)⁻¹ :=
      Subtype.ext hrq.symm
    rw [hq_eq, map_mul, map_mul, map_inv, ht]
  obtain ⟨t, ht⟩ := hroot p hp hpR
  obtain ⟨t', ht'⟩ := hroot p' hp' hp'R
  have h1 : ((φ ⟨x, hxR⟩ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) *
      (((φ ⟨x, hxR⟩)⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (((φ ⟨x, hxR⟩)⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) *
      ((φ ⟨x, hxR⟩ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [ht, ht']
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  exact conj_mul_sub_one_eq_zero h1 h2 (upperElt_sub_one_mul_eq_zero t' t)

theorem comm_mem_centralizer_of_isSylowOf [Finite G] {k : Type*} [Field k] [Finite k] {m : ℕ}
    (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m) {R : Subgroup G} (φ : R ≃* SL(2, k))
    {P₀ : Subgroup G} (hP₀ : IsSylowOf 2 P₀ R) {A A' : Subgroup G} {θ θ' : (Fin 2 → k) → G}
    (hθ : CFSG.Timmesfeld.ARS.IsNaturalModule φ θ) (hθ' : CFSG.Timmesfeld.ARS.IsNaturalModule φ θ')
    (hA : Set.range θ = (A : Set G)) (hA' : Set.range θ' = (A' : Set G))
    (hcomm : ∀ a ∈ A ⊔ A', ∀ b ∈ A ⊔ A', a * b = b * a) :
    ∀ p ∈ P₀, ∀ p' ∈ P₀, ∀ f ∈ A ⊔ A', p' * (p * f * p⁻¹ * f⁻¹) * p'⁻¹ = p * f * p⁻¹ * f⁻¹ := by
  intro p hp p' hp' f hf
  have hpR : p ∈ R := hP₀.le hp
  have hp'R : p' ∈ R := hP₀.le hp'
  have hkey := sylow_mul_sub_one_eq_zero hk hm φ hP₀ hp hp' hpR hp'R
  have hM : ∀ θ0 : (Fin 2 → k) → G, CFSG.Timmesfeld.ARS.IsNaturalModule φ θ0 → ∀ v : Fin 2 → k,
      p * θ0 v * p⁻¹ = θ0 (((φ ⟨p, hpR⟩ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) *ᵥ v) :=
    fun θ0 hθ0 v => (hθ0.map_mulVec ⟨p, hpR⟩ v).symm
  have hM' : ∀ θ0 : (Fin 2 → k) → G, CFSG.Timmesfeld.ARS.IsNaturalModule φ θ0 → ∀ v : Fin 2 → k,
      p' * θ0 v * p'⁻¹ = θ0 (((φ ⟨p', hp'R⟩ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) *ᵥ v) :=
    fun θ0 hθ0 v => (hθ0.map_mulVec ⟨p', hp'R⟩ v).symm
  have hcomm_mod : ∀ θ0 : (Fin 2 → k) → G, CFSG.Timmesfeld.ARS.IsNaturalModule φ θ0 →
      ∀ v : Fin 2 → k, Commute p' (p * θ0 v * p⁻¹ * (θ0 v)⁻¹) :=
    fun θ0 hθ0 v => commute_comm_of_mulVec hθ0.map_add (hM θ0 hθ0) (hM' θ0 hθ0) hkey v
  have hYA' : ∀ v' : Fin 2 → k, p * θ' v' * p⁻¹ ∈ A' := by
    intro v'
    rw [hM θ' hθ' v', ← SetLike.mem_coe, ← hA']
    exact Set.mem_range_self _
  have hf' : f ∈ ((A ⊔ A' : Subgroup G) : Set G) := hf
  rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A A'
    (fun a ha b hb => hcomm a (mem_sup_left ha) b (mem_sup_right hb))).2] at hf'
  obtain ⟨a, ha, a', ha', rfl⟩ := hf'
  obtain ⟨v, rfl⟩ : a ∈ Set.range θ := by rw [hA]; exact ha
  obtain ⟨v', rfl⟩ : a' ∈ Set.range θ' := by rw [hA']; exact ha'
  have haA : θ v ∈ A := ha
  have ha'A : θ' v' ∈ A' := ha'
  have hac : Commute (θ v) (θ' v') :=
    hcomm _ (mem_sup_left haA) _ (mem_sup_right ha'A)
  have hY : Commute (θ v) (p * θ' v' * p⁻¹) :=
    hcomm _ (mem_sup_left haA) _ (mem_sup_right (hYA' v'))
  have hC : Commute p' ((p * θ v * p⁻¹ * (θ v)⁻¹) * (p * θ' v' * p⁻¹ * (θ' v')⁻¹)) :=
    (hcomm_mod θ hθ v).mul_right (hcomm_mod θ' hθ' v')
  rw [comm_prod_eq hac hY]
  exact mul_inv_eq_iff_eq_mul.mpr hC.eq

theorem card_inf_centralizer_le_of_isNaturalSection [Finite G] {k : Type*} [Field k] [Finite k]
    {X A B : Subgroup G} (hN : IsNaturalSection X A B k) (hBA : B ≤ A) {p x : G} (hp : p ∈ X)
    (hp1 : p ≠ 1) (hpB : ∀ b ∈ B, p * b * p⁻¹ ∈ B)
    (hx : ∀ a ∈ A, (p * a * p⁻¹)⁻¹ * (x * a * x⁻¹) ∈ B) :
    Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) ≤
      Nat.card k * Nat.card (B ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  obtain ⟨φ, θ, -, hadd, hinj, hsurj, hact⟩ := hN
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin 2) (Fin 2) k,
      M = ((φ ⟨p, hp⟩ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) := ⟨_, rfl⟩
  have hM : ∀ v : Fin 2 → k, (θ (M *ᵥ v))⁻¹ * (p * θ v * p⁻¹) ∈ B := by
    intro v
    rw [hMdef]
    exact hact ⟨p, hp⟩ v
  have hchoice : ∀ a : (A ⊓ centralizer ({x} : Set G) : Subgroup G), ∃ v : Fin 2 → k,
      (θ v)⁻¹ * (a : G) ∈ B := fun a => hsurj (a : G) (mem_inf.mp a.2).1
  choose ρ hρ using hchoice
  have hcent : ∀ a : (A ⊓ centralizer ({x} : Set G) : Subgroup G),
      (a : G) ∈ centralizer ({x} : Set G) := fun a => (mem_inf.mp a.2).2
  have hfib : ∀ a b : (A ⊓ centralizer ({x} : Set G) : Subgroup G), ρ a = ρ b →
      (a : G)⁻¹ * (b : G) ∈ B ⊓ centralizer ({x} : Set G) := by
    intro a b hab
    refine mem_inf.mpr ⟨?_, mul_mem (inv_mem (hcent a)) (hcent b)⟩
    have h1 := hρ a
    have h2 := hρ b
    rw [← hab] at h2
    have e : (a : G)⁻¹ * (b : G) = ((θ (ρ a))⁻¹ * (a : G))⁻¹ * ((θ (ρ a))⁻¹ * (b : G)) := by
      group
    rw [e]
    exact mul_mem (inv_mem h1) h2
  have hfix : ∀ a : (A ⊓ centralizer ({x} : Set G) : Subgroup G), M *ᵥ ρ a = ρ a := by
    intro a
    have haA : (a : G) ∈ A := (mem_inf.mp a.2).1
    have hxa : x * (a : G) * x⁻¹ = (a : G) := by
      have hc := mem_centralizer_singleton_iff.mp (hcent a)
      rw [← hc, mul_inv_cancel_right]
    have h1 : (p * (a : G) * p⁻¹)⁻¹ * (a : G) ∈ B := by
      have := hx _ haA
      rwa [hxa] at this
    exact fixed_of_mem hadd hinj hM hpB h1 (hρ a)
  have hM1 : M - 1 ≠ 0 := by
    intro h
    apply hp1
    have hMeq : ((φ ⟨p, hp⟩ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = 1 := by
      rw [← hMdef]
      exact sub_eq_zero.mp h
    have h1 : φ ⟨p, hp⟩ = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      exact congrFun (congrFun hMeq i) j
    have h2 : (⟨p, hp⟩ : X) = 1 := φ.injective (h1.trans (map_one φ).symm)
    exact congrArg Subtype.val h2
  have hsub : Set.range ρ ⊆ {v : Fin 2 → k | (M - 1) *ᵥ v = 0} := by
    rintro _ ⟨a, rfl⟩
    show (M - 1) *ᵥ ρ a = 0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    exact hfix a
  have hcardρ : Nat.card (Set.range ρ) ≤ Nat.card k := by
    have hle : Nat.card (Set.range ρ) ≤ Nat.card {v : Fin 2 → k // (M - 1) *ᵥ v = 0} :=
      Nat.card_le_card_of_injective
        (fun w => (⟨w.1, hsub w.2⟩ : {v : Fin 2 → k // (M - 1) *ᵥ v = 0}))
        (fun a b hab => by
          have h := congrArg Subtype.val hab
          exact Subtype.ext h)
    exact hle.trans (card_ker_mulVec_le (M - 1) hM1)
  have hH := card_le_range_mul ρ hfib
  exact hH.trans (Nat.mul_le_mul_right _ hcardρ)

end LinT43

end CFSG.LocalAnalysis.EvenBN.U5
