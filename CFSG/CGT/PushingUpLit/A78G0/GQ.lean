module

public import CFSG.CGT.PushingUpLit.A78.Sp4Local
public import CFSG.CGT.PushingUpLit.A78G0.Basic
import CFSG.CGT.PushingUpLit.A78G0.Fibers

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78

section Commuting

variable {G : Type} [Group G]

theorem commuting_symm {A B : Subgroup G} (h : Commuting A B) : Commuting B A :=
  fun b hb a ha => (h a ha b hb).symm

theorem commuting_cs_iff {A B : Subgroup G} (g : G) :
    Commuting (cs A g) (cs B g) ↔ Commuting A B := by
  constructor
  · intro h a ha b hb
    have h1 := (h _ (conj_mem_cs g ha) _ (conj_mem_cs g hb)).map (MulAut.conj g⁻¹).toMonoidHom
    have e : ∀ x : G, (MulAut.conj g⁻¹).toMonoidHom (g * x * g⁻¹) = x := fun x => by
      simp
      group
    rwa [e, e] at h1
  · intro h x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
    exact (h a ha b hb).map (MulAut.conj g).toMonoidHom

theorem zClass_cs_iff {Z B : Subgroup G} (g : G) : cs B g ∈ zClass Z ↔ B ∈ zClass Z := by
  constructor
  · rintro ⟨g', hg'⟩
    refine ⟨g⁻¹ * g', ?_⟩
    have : cs B g = cs Z g' := hg'.symm
    have h2 : cs (cs B g) g⁻¹ = B := cs_cs_inv B g
    rw [this, ← cs_mul] at h2
    exact h2
  · rintro ⟨g', hg'⟩
    refine ⟨g * g', ?_⟩
    have : B = cs Z g' := hg'.symm
    rw [this, ← cs_mul]

end Commuting

section Transport

variable {G : Type} [Group G] {Z : Subgroup G} {e : ℕ}

def csEquiv (g : G) : Subgroup G ≃ Subgroup G where
  toFun X := cs X g⁻¹
  invFun X := cs X g
  left_inv X := cs_inv_cs X g
  right_inv X := cs_cs_inv X g

theorem mem_sigmaSet_cs_iff (g : G) {C : Subgroup G} :
    C ∈ sigmaSet (zClass Z) (cs Z g) ↔ cs C g⁻¹ ∈ sigmaSet (zClass Z) Z := by
  have hC : C = cs (cs C g⁻¹) g := (cs_inv_cs C g).symm
  have h1 : cs C g⁻¹ ∈ zClass Z ↔ C ∈ zClass Z := zClass_cs_iff g⁻¹
  have h2 : cs C g⁻¹ ≠ Z ↔ C ≠ cs Z g := by
    constructor
    · intro h h'
      apply h
      rw [h', cs_cs_inv]
    · intro h h'
      apply h
      rw [hC, h']
  have h3 : Commuting (cs Z g) C ↔ Commuting Z (cs C g⁻¹) := by
    conv_lhs => rw [hC]
    exact commuting_cs_iff g
  exact ⟨fun ⟨a, b, c⟩ => ⟨h1.2 a, h2.2 b, h3.1 c⟩, fun ⟨a, b, c⟩ => ⟨h1.1 a, h2.1 b, h3.2 c⟩⟩

structure SigmaCliques (Z : Subgroup G) (e : ℕ) (A : Subgroup G) : Prop where
  trans : ∀ B ∈ sigmaSet (zClass Z) A, ∀ C ∈ sigmaSet (zClass Z) A, ∀ D ∈ sigmaSet (zClass Z) A,
    Commuting B C → Commuting C D → Commuting B D
  clique : ∀ B ∈ sigmaSet (zClass Z) A,
    Nat.card {C : Subgroup G // C ∈ sigmaSet (zClass Z) A ∧ Commuting B C} = 2 ^ e
  card : Nat.card (sigmaSet (zClass Z) A) = 2 ^ e * (2 ^ e + 1)

theorem SigmaCliques.conj (h : SigmaCliques Z e Z) (g : G) : SigmaCliques Z e (cs Z g) where
  trans B hB C hC D hD hBC hCD := by
    have hB' := (mem_sigmaSet_cs_iff g).1 hB
    have hC' := (mem_sigmaSet_cs_iff g).1 hC
    have hD' := (mem_sigmaSet_cs_iff g).1 hD
    exact (commuting_cs_iff g⁻¹).1 (h.trans _ hB' _ hC' _ hD'
      ((commuting_cs_iff g⁻¹).2 hBC) ((commuting_cs_iff g⁻¹).2 hCD))
  clique B hB := by
    have hB' := (mem_sigmaSet_cs_iff g).1 hB
    rw [← h.clique _ hB']
    exact Nat.card_congr (Equiv.subtypeEquiv (csEquiv g) fun C => by
      show C ∈ sigmaSet (zClass Z) (cs Z g) ∧ Commuting B C ↔
        cs C g⁻¹ ∈ sigmaSet (zClass Z) Z ∧ Commuting (cs B g⁻¹) (cs C g⁻¹)
      rw [mem_sigmaSet_cs_iff g, commuting_cs_iff g⁻¹])
  card := by
    rw [← h.card]
    exact Nat.card_congr (Equiv.subtypeEquiv (csEquiv g) fun C => by
      show C ∈ sigmaSet (zClass Z) (cs Z g) ↔ cs C g⁻¹ ∈ sigmaSet (zClass Z) Z
      rw [mem_sigmaSet_cs_iff g])

end Transport

section Quadrangle

variable {G : Type} [Group G] [Finite G] {Z : Subgroup G} {e : ℕ}

theorem SigmaCliques.card_common_le (hZ : SigmaCliques Z e Z) {B C : Subgroup G}
    (hB : B ∈ zClass Z) (hC : C ∈ zClass Z) (hBC : ¬ Commuting B C) :
    Nat.card {X : Subgroup G // X ∈ zClass Z ∧ Commuting X B ∧ Commuting X C} ≤ 2 ^ e + 1 := by
  have hloc : ∀ A ∈ zClass Z, SigmaCliques Z e A := by
    rintro A ⟨g, rfl⟩
    exact hZ.conj g
  set I : Set (Subgroup G) := {X | X ∈ zClass Z ∧ Commuting X B ∧ Commuting X C}
  have hcardI : Nat.card {X : Subgroup G // X ∈ zClass Z ∧ Commuting X B ∧ Commuting X C} =
      I.ncard := Nat.card_coe_set_eq I
  rw [hcardI]
  have hBc := hloc B hB
  have hIS : ∀ X ∈ I, X ∈ sigmaSet (zClass Z) B := by
    rintro X ⟨hX, hXB, hXC⟩
    refine ⟨hX, ?_, commuting_symm hXB⟩
    rintro rfl
    exact hBC hXC
  have hIne : ∀ X ∈ I, ∀ X' ∈ I, Commuting X X' → X = X' := by
    rintro X hXI X' hX'I hXX'
    by_contra hne
    obtain ⟨hXz, hXB, hXC⟩ := hXI
    obtain ⟨hX'z, hX'B, hX'C⟩ := hX'I
    have hXc := hloc X hXz
    have hBX : B ≠ X := by
      rintro rfl
      exact hBC hXC
    have hCX : C ≠ X := by
      rintro rfl
      exact hBC (commuting_symm hXB)
    exact hBC (hXc.trans B ⟨hB, hBX, hXB⟩ X' ⟨hX'z, fun h => hne h.symm, hXX'⟩ C
      ⟨hC, hCX, hXC⟩ (commuting_symm hX'B) hX'C)
  let cl : Subgroup G → Set (Subgroup G) :=
    fun X => {Y | Y ∈ sigmaSet (zClass Z) B ∧ Commuting X Y}
  have hcl : ∀ X ∈ I, (cl X).ncard = 2 ^ e := by
    intro X hX
    exact (Nat.card_coe_set_eq (cl X)).symm.trans (hBc.clique X (hIS X hX))
  have hP := ncard_pairs I cl (2 ^ e) hcl
  have hle : {p : Subgroup G × Subgroup G | p.1 ∈ I ∧ p.2 ∈ cl p.1}.ncard ≤
      (sigmaSet (zClass Z) B).ncard := by
    refine Set.ncard_le_ncard_of_injOn Prod.snd (fun p hp => hp.2.1) ?_
    rintro ⟨X, Y⟩ ⟨hXI, hXY⟩ ⟨X', Y'⟩ ⟨hX'I, hX'Y⟩ hYY
    have hYY' : Y = Y' := hYY
    subst hYY'
    have hXX' : X = X' := by
      refine hIne X hXI X' hX'I ?_
      exact hBc.trans X (hIS X hXI) Y hXY.1 X' (hIS X' hX'I) hXY.2 (commuting_symm hX'Y.2)
    rw [hXX']
  have hS : (sigmaSet (zClass Z) B).ncard = 2 ^ e * (2 ^ e + 1) :=
    (Nat.card_coe_set_eq (sigmaSet (zClass Z) B)).symm.trans hBc.card
  rw [hP, hS] at hle
  have hpos : 0 < 2 ^ e := Nat.two_pow_pos e
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc I.ncard * 2 ^ e ≤ 2 ^ e * (2 ^ e + 1) := hle
    _ = (2 ^ e + 1) * 2 ^ e := Nat.mul_comm _ _

end Quadrangle

end CFSG.CGT.PushingUpLit.A78G0
