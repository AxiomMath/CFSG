module

public import CFSG.Quasithin.Recognition.G23TypeDefs
public import CFSG.StronglyEmbedded
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBender
public import CFSG.Assembly.RankThreeEvenDefs
public import Certificates.Data.G23RecogWordsInputs

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23
open scoped MatrixGroups

variable {G : Type} [Group G]

structure G23Ctx (G : Type) [Group G] (T H H₁ H₂ M : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  sylow : quasithinIsSylowTwo T
  tH : T ≤ H
  tM : T ≤ M
  one : G23One H H₁ H₂
  two : G23Two M
  inv : ∀ w ∈ H, w ∉ H₁ ⊔ H₂ → ∀ x ∈ H₁ ⊔ H₂, w * x * w⁻¹ * x ∈ pCoreOf 2 H

section StronglyEmbedded

theorem isStronglyEmbeddedOrder_of_one_class {G : Type*} [Group G] [Finite G] {X : Subgroup G}
    {z : G} (hz : orderOf z = 2) (hzX : z ∈ X) (hne : X ≠ ⊤)
    (hC : Subgroup.centralizer ({z} : Set G) ≤ X)
    (hconj : ∀ t ∈ X, orderOf t = 2 → ∃ x ∈ X, x * z * x⁻¹ = t) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hne, ?_, ?_⟩
  · have hdvd : 2 ∣ Nat.card X := by
      have := orderOf_dvd_natCard (⟨z, hzX⟩ : X)
      rwa [Subgroup.orderOf_mk, hz] at this
    exact even_iff_two_dvd.mpr hdvd
  · intro g hg
    by_contra hodd
    have hev := Nat.not_odd_iff_even.mp hodd
    obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ X.map (MulAut.conj g).toMonoidHom))
      2 (even_iff_two_dvd.mp hev)
    have ht2 : orderOf (t' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht'
    obtain ⟨htX, y, hyX, hy⟩ := t'.2
    have hyg : g * y * g⁻¹ = (t' : G) := by simpa [MulAut.conj_apply] using hy
    have hy2 : orderOf y = 2 := by
      have : orderOf (g * y * g⁻¹) = orderOf y := by
        have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
        simpa [MulAut.conj_apply] using this
      rw [← this, hyg, ht2]
    obtain ⟨x, hx, hxz⟩ := hconj _ htX ht2
    obtain ⟨x', hx', hx'z⟩ := hconj _ hyX hy2
    have hc : x⁻¹ * g * x' ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : g * (x' * z * x'⁻¹) * g⁻¹ = x * z * x⁻¹ := by rw [hx'z, hyg, hxz]
      calc x⁻¹ * g * x' * z = x⁻¹ * (g * (x' * z * x'⁻¹) * g⁻¹) * g * x' := by group
        _ = x⁻¹ * (x * z * x⁻¹) * g * x' := by rw [h1]
        _ = z * (x⁻¹ * g * x') := by group
    have : g = x * (x⁻¹ * g * x') * x'⁻¹ := by group
    exact hg (this ▸ mul_mem (mul_mem hx (hC hc)) (inv_mem hx'))

theorem eq_top_of_one_class {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {X : Subgroup G}
    {z : G} (hz : orderOf z = 2) (hzX : z ∈ X)
    (hC : Subgroup.centralizer ({z} : Set G) ≤ X)
    (hconj : ∀ t ∈ X, orderOf t = 2 → ∃ x ∈ X, x * z * x⁻¹ = t)
    {U Y : Subgroup G} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hY : Y ≤ Subgroup.normalizer (U : Set G)) (hYns : ¬ Group.IsSolvable ↥Y) : X = ⊤ := by
  by_contra hne
  have hSE := isStronglyEmbeddedOrder_of_one_class hz hzX hne hC hconj
  have hB := CFSG.Open.fusionIsBenderGroup_of_isBenderGroup (CFSG.BenderSuzuki.bender_suzuki X hSE)
  obtain ⟨q, k, hq⟩ := CFSG.QuasithinUnique.Lin2.exists_fusionBenderBorel_of_fusionIsBenderGroup hB
  exact CFSG.QuasithinUnique.Lin2.false_of_benderBorel hq hU hU2 hY hYns

end StronglyEmbedded

theorem lift_mk_invWord {X : Type*} [Group X] (ρ : Fin 6 → X) (w : List (Fin 6 × Bool)) :
    FreeGroup.lift ρ (FreeGroup.mk (invWord w)) = (FreeGroup.lift ρ (FreeGroup.mk w))⁻¹ := by
  rw [← map_inv, FreeGroup.inv_mk]
  rfl

theorem lift_mk_single {X : Type*} [Group X] {n : ℕ} (τ : Fin n → X) (i : Fin n) (b : Bool) :
    FreeGroup.lift τ (FreeGroup.mk [(i, b)]) = if b then τ i else (τ i)⁻¹ := by
  cases b
  · have : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := rfl
    rw [this, map_inv]; simp
  · have : FreeGroup.mk [(i, true)] = FreeGroup.of i := rfl
    rw [this]; simp

theorem lift_substWord_single {X : Type*} [Group X] (ρ : Fin 6 → X) (i : Fin 3) (b : Bool) :
    FreeGroup.lift ρ (FreeGroup.mk (substWord [(i, b)])) =
      FreeGroup.lift (![evalW ρ dWord₁, evalW ρ dWord₂, ρ 5] : Fin 3 → X)
        (FreeGroup.mk [(i, b)]) := by
  have s0t : substWord [(0, true)] = dWord₁ := by decide
  have s0f : substWord [(0, false)] = invWord dWord₁ := by decide
  have s1t : substWord [(1, true)] = dWord₂ := by decide
  have s1f : substWord [(1, false)] = invWord dWord₂ := by decide
  have s2t : substWord [(2, true)] = [(5, true)] := by decide
  have s2f : substWord [(2, false)] = [(5, false)] := by decide
  by_cases h0 : i = 0
  · subst h0
    cases b
    · rw [s0f, lift_mk_invWord, lift_mk_single]; simp [evalW]
    · rw [s0t, lift_mk_single]; simp [evalW]
  by_cases h1 : i = 1
  · subst h1
    cases b
    · rw [s1f, lift_mk_invWord, lift_mk_single]; simp [evalW]
    · rw [s1t, lift_mk_single]; simp [evalW]
  · have h2 : i = 2 := by omega
    subst h2
    cases b
    · rw [s2f, lift_mk_single, lift_mk_single]; simp
    · rw [s2t, lift_mk_single, lift_mk_single]; simp

theorem lift_substWord {X : Type*} [Group X] (ρ : Fin 6 → X) (r : List (Fin 3 × Bool)) :
    FreeGroup.lift ρ (FreeGroup.mk (substWord r)) =
      FreeGroup.lift (![evalW ρ dWord₁, evalW ρ dWord₂, ρ 5] : Fin 3 → X) (FreeGroup.mk r) := by
  induction r with
  | nil => simp [substWord]
  | cons l r ih =>
    have h1 : substWord (l :: r) = substWord [l] ++ substWord r := by simp [substWord]
    have h2 : (l :: r) = [l] ++ r := rfl
    rw [h1, ← FreeGroup.mul_mk, map_mul, ih, h2, ← FreeGroup.mul_mk, map_mul]
    congr 1
    obtain ⟨i, b⟩ := l
    exact lift_substWord_single ρ i b

theorem g23WordsH_letters : ∀ r ∈ g23WordsH, ∀ l ∈ r, l.1 ≠ 5 := by decide

theorem dWord_letters : (∀ l ∈ dWord₁, l.1 ≠ 5) ∧ (∀ l ∈ dWord₂, l.1 ≠ 5) := by decide

theorem lift_update_of_letters {X : Type*} [Group X] (ρ : Fin 6 → X) (x : X)
    (r : List (Fin 6 × Bool)) (hr : ∀ l ∈ r, l.1 ≠ 5) :
    FreeGroup.lift (Function.update ρ 5 x) (FreeGroup.mk r) = FreeGroup.lift ρ (FreeGroup.mk r) := by
  induction r with
  | nil => simp
  | cons l r ih =>
    have h2 : (l :: r) = [l] ++ r := rfl
    rw [h2, ← FreeGroup.mul_mk, map_mul, map_mul,
      ih (fun l' hl' => hr l' (List.mem_cons_of_mem _ hl'))]
    congr 1
    obtain ⟨i, b⟩ := l
    have hi : i ≠ 5 := hr (i, b) List.mem_cons_self
    cases b
    · show FreeGroup.lift _ (FreeGroup.of i)⁻¹ = FreeGroup.lift _ (FreeGroup.of i)⁻¹
      simp [Function.update_of_ne hi]
    · show FreeGroup.lift _ (FreeGroup.of i) = FreeGroup.lift _ (FreeGroup.of i)
      simp [Function.update_of_ne hi]

end CFSG.GH74.QTGen4.Recog.G23
