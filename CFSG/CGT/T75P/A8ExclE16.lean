module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.CGT.Timmesfeld75.Sec3TwelveIrr
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.T75P

open Subgroup
open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix IsMulCommutative

private noncomputable def a8xPow2 {C : Type*} [CommGroup C] {r : ℕ} (v : Fin r → C)
    (hv : ∀ i, v i ^ 2 = 1) : (Fin r → Multiplicative (ZMod 2)) →* C where
  toFun a := ∏ i, v i ^ (Multiplicative.toAdd (a i)).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

private theorem a8x_card_pi : Nat.card (Fin 4 → Multiplicative (ZMod 2)) = 16 := by
  rw [Nat.card_pi]
  simp

theorem a8x_exists_E16 {G : Type*} [Group G] (e : Fin 4 → G) (hsq : ∀ i, e i * e i = 1)
    (hcomm : ∀ i j, e i * e j = e j * e i)
    (hker : ∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun i => e i ^ (a i : ℕ)).prod ≠ 1) :
    ∃ E : Subgroup G, Nat.card E = 16 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  have hsq' : ∀ i, e i ^ 2 = 1 := fun i => by rw [sq]; exact hsq i
  set C := Subgroup.closure (Set.range e) with hC
  have : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let v : Fin 4 → C := fun i => ⟨e i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hv : ∀ i, v i ^ 2 = 1 := fun i => Subtype.ext (by simpa [v] using hsq' i)
  let φ : (Fin 4 → Multiplicative (ZMod 2)) →* G := C.subtype.comp (a8xPow2 v hv)
  have hφ : ∀ a, φ a = (List.ofFn fun i => e i ^ (Multiplicative.toAdd (a i)).val).prod := by
    intro a
    simp only [φ, MonoidHom.comp_apply, a8xPow2, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hφ] at ha
    rw [Subgroup.mem_bot]
    by_contra hne
    refine hker (fun i => ⟨(Multiplicative.toAdd (a i)).val, ZMod.val_lt _⟩) (fun h0 => hne ?_) ha
    funext i
    have h1 := congrFun h0 i
    have h2 : (Multiplicative.toAdd (a i)).val = 0 := by simpa using congrArg Fin.val h1
    exact Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).1 h2)
  have hsqa : ∀ a : Fin 4 → Multiplicative (ZMod 2), a * a = 1 := by
    intro a
    funext i
    rw [Pi.mul_apply, Pi.one_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    exact CharTwo.add_self_eq_zero _
  refine ⟨φ.range, ?_, ?_⟩
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, a8x_card_pi]
  · rintro _ ⟨a, rfl⟩
    rw [sq, ← map_mul, hsqa, map_one]

theorem a8x_prod_four {G : Type*} [Group G] (e : Fin 4 → G) (a : Fin 4 → Fin 2) :
    (List.ofFn fun i => e i ^ (a i : ℕ)).prod =
      e 0 ^ (a 0 : ℕ) * (e 1 ^ (a 1 : ℕ) * (e 2 ^ (a 2 : ℕ) * e 3 ^ (a 3 : ℕ))) := by
  simp [List.ofFn_succ]

variable {G : Type} [Group G]

end CFSG.CGT.T75P
