module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ProdAut
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

variable {X A B : Type*} [Group X] [Group A] [Group B]

@[expose] noncomputable def prodFirstFactor (e : X ≃* A × B) : Subgroup X :=
  ((⊤ : Subgroup A).prod (⊥ : Subgroup B)).map e.symm.toMonoidHom

@[expose] noncomputable def prodSecondFactor (e : X ≃* A × B) : Subgroup X :=
  ((⊥ : Subgroup A).prod (⊤ : Subgroup B)).map e.symm.toMonoidHom

theorem mem_prodFirstFactor_iff {e : X ≃* A × B} {x : X} :
    x ∈ prodFirstFactor e ↔ e x ∈ (⊤ : Subgroup A).prod (⊥ : Subgroup B) := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hxy : e x = y := by rw [← hyx]; simp
    rwa [hxy]
  · intro hx
    exact Subgroup.mem_map.mpr ⟨e x, hx, by simp [MulEquiv.symm_apply_apply]⟩

theorem mem_prodSecondFactor_iff {e : X ≃* A × B} {x : X} :
    x ∈ prodSecondFactor e ↔ e x ∈ (⊥ : Subgroup A).prod (⊤ : Subgroup B) := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hxy : e x = y := by rw [← hyx]; simp
    rwa [hxy]
  · intro hx
    exact Subgroup.mem_map.mpr ⟨e x, hx, by simp [MulEquiv.symm_apply_apply]⟩

theorem prodFirstFactor_normal (e : X ≃* A × B) : (prodFirstFactor e).Normal :=
  (Subgroup.prod_normal (⊤ : Subgroup A) (⊥ : Subgroup B)).map e.symm.toMonoidHom
    e.symm.surjective

theorem prodSecondFactor_normal (e : X ≃* A × B) : (prodSecondFactor e).Normal :=
  (Subgroup.prod_normal (⊥ : Subgroup A) (⊤ : Subgroup B)).map e.symm.toMonoidHom
    e.symm.surjective

theorem prodFirstFactor_sup_prodSecondFactor (e : X ≃* A × B) :
    prodFirstFactor e ⊔ prodSecondFactor e = ⊤ := by
  rw [prodFirstFactor, prodSecondFactor, ← Subgroup.map_sup]
  have h : ((⊤ : Subgroup A).prod (⊥ : Subgroup B)) ⊔
      ((⊥ : Subgroup A).prod (⊤ : Subgroup B)) = ⊤ := by
    ext x
    constructor
    · intro _; exact Subgroup.mem_top x
    · intro _
      have hx : x = (x.1, (1 : B)) * ((1 : A), x.2) := by ext <;> simp
      rw [hx]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by simp⟩))
        (Subgroup.mem_sup_right (Subgroup.mem_prod.mpr ⟨by simp, Subgroup.mem_top _⟩))
  rw [h]
  exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem prodFirstFactor_inf_prodSecondFactor (e : X ≃* A × B) :
    prodFirstFactor e ⊓ prodSecondFactor e = ⊥ := by
  rw [prodFirstFactor, prodSecondFactor, ← Subgroup.map_inf _ _ _ e.symm.injective]
  have h : ((⊤ : Subgroup A).prod (⊥ : Subgroup B)) ⊓
      ((⊥ : Subgroup A).prod (⊤ : Subgroup B)) = ⊥ := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨-, hb⟩ := Subgroup.mem_prod.mp hx1
      obtain ⟨ha, -⟩ := Subgroup.mem_prod.mp hx2
      rw [Subgroup.mem_bot, Prod.ext_iff]
      exact ⟨Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb⟩
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by simp⟩,
          Subgroup.mem_prod.mpr ⟨by simp, Subgroup.mem_top _⟩⟩
  rw [h, Subgroup.map_bot]

theorem commute_prodFirstFactor_prodSecondFactor (e : X ≃* A × B) {x y : X}
    (hx : x ∈ prodFirstFactor e) (hy : y ∈ prodSecondFactor e) : Commute x y := by
  have hx' := (mem_prodFirstFactor_iff (e := e)).mp hx
  have hy' := (mem_prodSecondFactor_iff (e := e)).mp hy
  obtain ⟨-, hx2⟩ := Subgroup.mem_prod.mp hx'
  obtain ⟨hy1, -⟩ := Subgroup.mem_prod.mp hy'
  have hx2' : (e x).2 = 1 := Subgroup.mem_bot.mp hx2
  have hy1' : (e y).1 = 1 := Subgroup.mem_bot.mp hy1
  apply e.injective
  have hxeq : e x = ((e x).1, (1 : B)) := Prod.ext rfl hx2'
  have hyeq : e y = ((1 : A), (e y).2) := Prod.ext hy1' rfl
  rw [map_mul, map_mul, hxeq, hyeq]
  simp [mul_comm]

noncomputable def prodFirstFactorMulEquiv (e : X ≃* A × B) :
    ↥(prodFirstFactor e) ≃* A :=
  ((MulEquiv.subgroupMap e.symm ((⊤ : Subgroup A).prod (⊥ : Subgroup B))).symm.trans
    ((Subgroup.prodEquiv (⊤ : Subgroup A) (⊥ : Subgroup B)).trans
      MulEquiv.prodUnique)).trans Subgroup.topEquiv

noncomputable def prodSecondFactorMulEquiv (e : X ≃* A × B) :
    ↥(prodSecondFactor e) ≃* B :=
  ((MulEquiv.subgroupMap e.symm ((⊥ : Subgroup A).prod (⊤ : Subgroup B))).symm.trans
    ((Subgroup.prodEquiv (⊥ : Subgroup A) (⊤ : Subgroup B)).trans
      MulEquiv.uniqueProd)).trans Subgroup.topEquiv

private theorem map_eq_of_le_of_card_eq {X : Type*} [Group X] [Finite X] {H K : Subgroup X}
    {f : X →* X} (hf : Function.Injective f) (h : H.map f ≤ K)
    (hcard : Nat.card H = Nat.card K) : H.map f = K := by
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [Subgroup.card_map_of_injective hf, hcard]

private theorem prodFactor_map_le_of_preserve {A X : Type*} [Group A] [Group X]
    (e : X ≃* A × A) (α : MulAut X) (β : MulAut (A × A))
    (hβ : ∀ x : X, β (e x) = e (α x))
    (h1 : ∀ a : A, (β (a, 1)).2 = 1) (h2 : ∀ a : A, (β (1, a)).1 = 1) :
    (prodFirstFactor e).map α.toMonoidHom ≤ prodFirstFactor e ∧
      (prodSecondFactor e).map α.toMonoidHom ≤ prodSecondFactor e := by
  constructor
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_prodFirstFactor_iff]
    change e (α y) ∈ (⊤ : Subgroup A).prod (⊥ : Subgroup A)
    rw [← hβ y]
    have hy' := (mem_prodFirstFactor_iff (e := e)).mp hy
    obtain ⟨-, hy2⟩ := Subgroup.mem_prod.mp hy'
    have hyeq : e y = ((e y).1, 1) := Prod.ext rfl (Subgroup.mem_bot.mp hy2)
    rw [hyeq]
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by simp [h1]⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_prodSecondFactor_iff]
    change e (α y) ∈ (⊥ : Subgroup A).prod (⊤ : Subgroup A)
    rw [← hβ y]
    have hy' := (mem_prodSecondFactor_iff (e := e)).mp hy
    obtain ⟨hy1, -⟩ := Subgroup.mem_prod.mp hy'
    have hyeq : e y = ((1 : A), (e y).2) := Prod.ext (Subgroup.mem_bot.mp hy1) rfl
    rw [hyeq]
    exact Subgroup.mem_prod.mpr ⟨by simp [h2], Subgroup.mem_top _⟩

private theorem prodFactor_map_le_of_swap {A X : Type*} [Group A] [Group X]
    (e : X ≃* A × A) (α : MulAut X) (β : MulAut (A × A))
    (hβ : ∀ x : X, β (e x) = e (α x))
    (h1 : ∀ a : A, (β (a, 1)).1 = 1) (h2 : ∀ a : A, (β (1, a)).2 = 1) :
    (prodFirstFactor e).map α.toMonoidHom ≤ prodSecondFactor e ∧
      (prodSecondFactor e).map α.toMonoidHom ≤ prodFirstFactor e := by
  constructor
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_prodSecondFactor_iff]
    change e (α y) ∈ (⊥ : Subgroup A).prod (⊤ : Subgroup A)
    rw [← hβ y]
    have hy' := (mem_prodFirstFactor_iff (e := e)).mp hy
    obtain ⟨-, hy2⟩ := Subgroup.mem_prod.mp hy'
    have hyeq : e y = ((e y).1, 1) := Prod.ext rfl (Subgroup.mem_bot.mp hy2)
    rw [hyeq]
    exact Subgroup.mem_prod.mpr ⟨by simp [h1], Subgroup.mem_top _⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_prodFirstFactor_iff]
    change e (α y) ∈ (⊤ : Subgroup A).prod (⊥ : Subgroup A)
    rw [← hβ y]
    have hy' := (mem_prodSecondFactor_iff (e := e)).mp hy
    obtain ⟨hy1, -⟩ := Subgroup.mem_prod.mp hy'
    have hyeq : e y = ((1 : A), (e y).2) := Prod.ext (Subgroup.mem_bot.mp hy1) rfl
    rw [hyeq]
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by simp [h2]⟩

theorem prodFirstFactor_map_mulAut_eq_or {A X : Type*} [Group A] [Finite A] [Group X]
    [Finite X]
    (hsimple : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤)
    (hcentral : ∀ a : A, (∀ c, a * c = c * a) → a = 1)
    (hnt : ∃ a : A, a ≠ 1) (e : X ≃* A × A) (α : MulAut X) :
    ((prodFirstFactor e).map α.toMonoidHom = prodFirstFactor e ∧
      (prodSecondFactor e).map α.toMonoidHom = prodSecondFactor e) ∨
    ((prodFirstFactor e).map α.toMonoidHom = prodSecondFactor e ∧
      (prodSecondFactor e).map α.toMonoidHom = prodFirstFactor e) := by
  let β : MulAut (A × A) := e.symm.trans (α.trans e)
  have hβ : ∀ x : X, β (e x) = e (α x) := by intro x; simp [β]
  have hcardF : Nat.card (prodFirstFactor e) = Nat.card A :=
    Nat.card_congr (prodFirstFactorMulEquiv e).toEquiv
  have hcardG : Nat.card (prodSecondFactor e) = Nat.card A :=
    Nat.card_congr (prodSecondFactorMulEquiv e).toEquiv
  rcases CFSG.EvenSporadicStandard.M24Std.ProdAut.mulAut_prod_cases hsimple hcentral hnt β with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    obtain ⟨hF, hG⟩ := prodFactor_map_le_of_preserve e α β hβ h1 h2
    exact ⟨map_eq_of_le_of_card_eq α.injective hF rfl,
      map_eq_of_le_of_card_eq α.injective hG rfl⟩
  · right
    obtain ⟨hF, hG⟩ := prodFactor_map_le_of_swap e α β hβ h1 h2
    exact ⟨map_eq_of_le_of_card_eq α.injective hF (by rw [hcardF, hcardG]),
      map_eq_of_le_of_card_eq α.injective hG (by rw [hcardG, hcardF])⟩

end CFSG.GroupTheory

end
