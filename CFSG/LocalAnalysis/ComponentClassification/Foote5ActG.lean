module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Act
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] {𝕊 : Type} [Group 𝕊]

@[expose] noncomputable def actG (A : Subgroup G) (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊) (x : G) :
    MulAut 𝕊 :=
  open Classical in if hx : x ∈ normalizer (A : Set G) then act A ε ⟨x, hx⟩ else 1

@[expose] noncomputable def actImage (A : Subgroup G) (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊)
    (P : Subgroup G) : Subgroup (MulAut 𝕊) :=
  (P.subgroupOf (normalizer (A : Set G))).map (act A ε)

variable {A : Subgroup G} (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊)

theorem actG_of_mem {x : G} (hx : x ∈ normalizer (A : Set G)) :
    actG A ε x = act A ε ⟨x, hx⟩ := by
  unfold actG
  simp only [hx, ↓reduceDIte]

theorem actG_mul {x y : G} (hx : x ∈ normalizer (A : Set G)) (hy : y ∈ normalizer (A : Set G)) :
    actG A ε (x * y) = actG A ε x * actG A ε y := by
  rw [actG_of_mem ε (mul_mem hx hy), actG_of_mem ε hx, actG_of_mem ε hy, ← map_mul]
  rfl

theorem actG_inv {x : G} (hx : x ∈ normalizer (A : Set G)) :
    actG A ε x⁻¹ = (actG A ε x)⁻¹ := by
  rw [actG_of_mem ε (inv_mem hx), actG_of_mem ε hx, ← map_inv]
  rfl

theorem actG_one : actG A ε 1 = 1 := by
  rw [actG_of_mem ε (one_mem _)]
  exact map_one (act A ε)

theorem actG_pow {x : G} (hx : x ∈ normalizer (A : Set G)) (n : ℕ) :
    actG A ε (x ^ n) = actG A ε x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, actG_one]
  | succ n ih => rw [pow_succ, pow_succ, actG_mul ε (pow_mem hx n) hx, ih]

theorem actG_zpow {x : G} (hx : x ∈ normalizer (A : Set G)) (n : ℤ) :
    actG A ε (x ^ n) = actG A ε x ^ n := by
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, actG_pow ε hx]
  · rw [zpow_negSucc, zpow_negSucc, actG_inv ε (pow_mem hx _), actG_pow ε hx]

theorem actG_eq_one_iff {x : G} (hx : x ∈ normalizer (A : Set G)) :
    actG A ε x = 1 ↔ x ∈ coreActionKernel A := by
  rw [actG_of_mem ε hx]
  exact act_eq_one_iff ε _

theorem actG_psi {x : G} (hx : x ∈ normalizer (A : Set G)) (a : ↥A) :
    actG A ε x (psi A ε a) =
      psi A ε ⟨x * a * x⁻¹, (mem_normalizer_iff.mp hx a).mp a.2⟩ := by
  rw [actG_of_mem ε hx]
  exact act_psi ε _ a

theorem actG_of_mem_self {a : G} (ha : a ∈ A) :
    actG A ε a = MulAut.conj (psi A ε ⟨a, ha⟩) := by
  rw [actG_of_mem ε (le_normalizer ha)]
  exact act_of_mem ε ⟨a, ha⟩ _

theorem psi_eq_iff (a b : ↥A) : psi A ε a = psi A ε b ↔ ((a⁻¹ * b : ↥A) : G) ∈ oddCoreIn A := by
  rw [← psi_eq_one_iff ε, map_mul, map_inv, inv_mul_eq_one, eq_comm]

theorem mem_actImage {P : Subgroup G} (hP : P ≤ normalizer (A : Set G)) {α : MulAut 𝕊} :
    α ∈ actImage A ε P ↔ ∃ p ∈ P, actG A ε p = α := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, mem_subgroupOf.mp hp, actG_of_mem ε p.2⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hP hp⟩, mem_subgroupOf.mpr hp, (actG_of_mem ε (hP hp)).symm⟩

theorem actG_mem_actImage {P : Subgroup G} (hP : P ≤ normalizer (A : Set G)) {p : G}
    (hp : p ∈ P) : actG A ε p ∈ actImage A ε P :=
  (mem_actImage ε hP).mpr ⟨p, hp, rfl⟩

theorem isPGroup_actImage {P : Subgroup G} (hP : IsPGroup 2 P) : IsPGroup 2 (actImage A ε P) :=
  (hP.comap_subtype (K := normalizer (A : Set G))).map _

theorem card_eq_card_inf_mul_card_actImage {P : Subgroup G} (hP : P ≤ normalizer (A : Set G)) :
    Nat.card P = Nat.card ↥(P ⊓ coreActionKernel A) * Nat.card (actImage A ε P) := by
  set N := normalizer (A : Set G)
  set φ : ↥(P.subgroupOf N) →* MulAut 𝕊 := (act A ε).comp (P.subgroupOf N).subtype with hφ
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hrange : φ.range = actImage A ε P := by
    rw [hφ, MonoidHom.range_comp, range_subtype]
    rfl
  have hP' : Nat.card ↥(P.subgroupOf N) = Nat.card P :=
    Nat.card_congr (subgroupOfEquivOfLe hP).toEquiv
  have hker : Nat.card φ.ker = Nat.card ↥(P ⊓ coreActionKernel A) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : P.subgroupOf N) : N), mem_inf.mpr ⟨mem_subgroupOf.mp
          (x : P.subgroupOf N).2, (act_eq_one_iff ε _).mp (MonoidHom.mem_ker.mp x.2)⟩⟩
        invFun := fun y => ⟨⟨⟨y, hP (mem_inf.mp y.2).1⟩, mem_subgroupOf.mpr (mem_inf.mp y.2).1⟩,
          MonoidHom.mem_ker.mpr ((act_eq_one_iff ε _).mpr (mem_inf.mp y.2).2)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hrange, hker, hP'] at h1
  exact h1.symm

end CFSG.ComponentClassification.Foote5
