module

public import CFSG.Certificates.Kernel.Co1Sub.TreeSound
public import CFSG.Certificates.Kernel.Co1FixCount

public section

namespace CFSG.KC.Co1Sub

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.TabMatGrp
  CFSG.KC.Co1Fix

open scoped Matrix

private theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by
  cases a <;> rfl

theorem card_mul_le {G α : Type*} [Group G] (H S : Subgroup G) [Finite H] (hSH : S ≤ H)
    (f : G → α) (hf : ∀ s ∈ S, ∀ h, f (s * h) = f h) {N : ℕ} (p : Fin N → α)
    (hp : Function.Injective p) (hpH : ∀ k, ∃ h ∈ H, f h = p k) :
    N * Nat.card S ≤ Nat.card H := by
  choose h hH hfh using hpH
  let F : Fin N × S → H := fun x => ⟨x.2.1 * h x.1, H.mul_mem (hSH x.2.2) (hH x.1)⟩
  have hF : Function.Injective F := by
    rintro ⟨k, s⟩ ⟨l, t⟩ e
    have e' : s.1 * h k = t.1 * h l := congrArg Subtype.val e
    have hkl : k = l := by
      apply hp
      rw [← hfh k, ← hfh l, ← hf s.1 s.2 (h k), ← hf t.1 t.2 (h l), e']
    subst hkl
    have hst : s = t := Subtype.ext (mul_right_cancel e')
    rw [hst]
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin] at this

theorem fixK_spec : ∀ {gens : List Nat} {x : Nat}, fixK gens x = true → ∀ g ∈ gens, vmS g x = x
  | [], _, _ => fun _ h => absurd h List.not_mem_nil
  | g :: gens, x, h => by
    change CFSG.KLie.CT.andB (Nat.beq (vmS g x) x) (fixK gens x) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact Nat.eq_of_beq_eq_true h.1
    · exact fixK_spec h.2 g' hg'

theorem vecOf_vmS (M v : Nat) : vecOf (vmS M v) = vecOf v ᵥ* MatP 24 M :=
  (vecMul_eq M v).symm

theorem vmS_lt (M v : Nat) : vmS M v < 2 ^ 24 := vmF_lt 24 M v

theorem ptT_lt (r : Nat) : ptT r < 2 ^ 24 := by
  change r &&& 16777215 < 2 ^ 24
  have : r &&& 16777215 ≤ 16777215 := Nat.and_le_right
  omega

theorem tree_card {G : Type*} [Group G] {φ : G →* GL (Fin 24) (ZMod 2)} (H S : Subgroup G)
    [Finite H] (hSH : S ≤ H) {x : Nat} (hx : x < 2 ^ 24)
    (hS : ∀ s ∈ S, vecOf x ᵥ* matOf φ s = vecOf x) {gens : List Nat} {N : Nat} {C : List Nat}
    (h : treeK gens x N C = true)
    (hg : ∀ i < gens.length, ∃ g ∈ H, MatP 24 (gens.getD i 0) = matOf φ g) :
    N * Nat.card S ≤ Nat.card H := by
  let Sx : Set Nat := {y | y < 2 ^ 24 ∧ ∃ g ∈ H, vecOf x ᵥ* matOf φ g = vecOf y}
  have h0 : x ∈ Sx := ⟨hx, 1, H.one_mem, by rw [matOf_one, Matrix.vecMul_one]⟩
  have hcl : ∀ y ∈ Sx, ∀ i < gens.length, vmS (gens.getD i 0) y ∈ Sx := by
    rintro y ⟨-, g, hgH, e⟩ i hi
    obtain ⟨g', hg'H, hm⟩ := hg i hi
    exact ⟨vmS_lt _ _, g * g', H.mul_mem hgH hg'H, by
      rw [vecOf_vmS, hm, ← e, matOf_mul, Matrix.vecMul_vecMul]⟩
  obtain ⟨hin, hmono⟩ := treeK_sound h Sx h0 hcl
  refine card_mul_le H S hSH (fun g => vecOf x ᵥ* matOf φ g) (fun s hs g => ?_)
    (fun k : Fin N => vecOf (ptT (recT C k))) (fun k l e => ?_) (fun k => ?_)
  · rw [matOf_mul, ← Matrix.vecMul_vecMul, hS s hs]
  · have e' := CFSG.Sporadic.SmallF2.toVecD_injective (ptT_lt _) (ptT_lt _) e
    rcases lt_trichotomy k.val l.val with hkl | hkl | hkl
    · exact absurd e' (hmono _ _ hkl l.isLt).ne
    · exact Fin.ext hkl
    · exact absurd e' (hmono _ _ hkl k.isLt).ne'
  · obtain ⟨-, g, hgH, e⟩ := hin k k.isLt
    exact ⟨g, hgH, e⟩

end CFSG.KC.Co1Sub

end
