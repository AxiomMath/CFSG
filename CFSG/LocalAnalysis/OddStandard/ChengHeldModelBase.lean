module

public import Certificates.Data.ChengHeldPresProps

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel

structure Rep (M : RegModel) (H : Type) [Group H] where
  pt : H → ℕ
  pt_lt : ∀ h, pt h < M.N
  pt_inj : Function.Injective pt
  pt_surj : ∀ a, a < M.N → ∃ h, pt h = a
  pt_mul : ∀ a b : H, pt (a * b) = M.m (pt a) (pt b)
  pt_one : pt 1 = 0
  pt_inv : ∀ a : H, pt a⁻¹ = M.inv[pt a]!

namespace Rep

variable {M : RegModel} {H : Type} [Group H] (R : Rep M H)

@[expose] def set (B : Array Bool) : Set H := {h | B[R.pt h]! = true}

@[expose] noncomputable def equiv : H ≃ Fin M.N :=
  Equiv.ofBijective (fun h => ⟨R.pt h, R.pt_lt h⟩)
    ⟨fun a b hab => R.pt_inj (by simpa using congrArg Fin.val hab),
      fun a => by
        obtain ⟨h, hh⟩ := R.pt_surj a.1 a.2
        exact ⟨h, Fin.ext hh⟩⟩

include R in
theorem finite : Finite H := Finite.of_injective _ R.equiv.injective

include R in
theorem natCard : Nat.card H = M.N := by
  rw [Nat.card_congr R.equiv, Nat.card_fin]

theorem pt_pow (h : H) (n : ℕ) : R.pt (h ^ n) = M.pw (R.pt h) n := by
  induction n with
  | zero => simpa [RegModel.pw] using R.pt_one
  | succ n ih => rw [pow_succ, R.pt_mul, ih]; rfl

theorem pt_cm (a b : H) : R.pt (a⁻¹ * b⁻¹ * a * b) = M.cm (R.pt a) (R.pt b) := by
  rw [show a⁻¹ * b⁻¹ * a * b = (a⁻¹ * b⁻¹) * (a * b) by group]
  simp only [RegModel.cm, R.pt_mul, R.pt_inv]

theorem pt_cj (a b : H) : R.pt (b⁻¹ * a * b) = M.cj (R.pt a) (R.pt b) := by
  simp only [RegModel.cj, R.pt_mul, R.pt_inv]

theorem mem_set {B : Array Bool} {h : H} : h ∈ R.set B ↔ B[R.pt h]! = true := Iff.rfl

theorem length_eq_ncard {l : List ℕ} (hnd : l.Nodup) (hlt : ∀ a ∈ l, a < M.N) {P : H → Prop}
    (hl : ∀ h, R.pt h ∈ l ↔ P h) : l.length = {h | P h}.ncard := by
  have himg : R.pt '' {h | P h} = (l.toFinset : Set ℕ) := by
    ext a
    simp only [Set.mem_image, Finset.mem_coe, List.mem_toFinset]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact (hl h).2 hh
    · intro ha
      obtain ⟨h, rfl⟩ := R.pt_surj a (hlt a ha)
      exact ⟨h, (hl h).1 ha, rfl⟩
  rw [← Set.ncard_image_of_injective _ R.pt_inj, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

end Rep

end CFSG.OddStandard.ChengHeld.Model
