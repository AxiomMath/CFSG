module

public import CFSG.CGT.PushingUpLit.A78.Sp4Local
public import CFSG.CGT.PushingUpLit.A78.Sp4Fusion
public import CFSG.Timmesfeld.ARS.BasicBridge

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Timmesfeld.ARS

variable {G : Type} [Group G]

section Conj

theorem conjSub_sup (A B : Subgroup G) (g : G) :
    conjSub (A ⊔ B) g = conjSub A g ⊔ conjSub B g :=
  Subgroup.map_sup A B _

theorem conjSub_le_conjSub_iff {A B : Subgroup G} (g : G) :
    conjSub A g ≤ conjSub B g ↔ A ≤ B :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

theorem conjSub_inj_iff {A B : Subgroup G} (g : G) : conjSub A g = conjSub B g ↔ A = B :=
  (Subgroup.map_injective (MulAut.conj g).injective).eq_iff

theorem conjSub_inv_conjSub_eq (H : Subgroup G) (g : G) : conjSub (conjSub H g⁻¹) g = H := by
  have := conjSub_conjSub_inv_eq H g⁻¹
  rwa [inv_inv] at this

theorem commuting_conjSub_iff {A B : Subgroup G} (g : G) :
    Commuting (conjSub A g) (conjSub B g) ↔ Commuting A B :=
  ⟨fun h => by
    have := Commuting.conjSub h g⁻¹
    rwa [conjSub_conjSub_inv_eq, conjSub_conjSub_inv_eq] at this, fun h => Commuting.conjSub h g⟩

@[expose] def conjEquiv (g : G) : Subgroup G ≃ Subgroup G where
  toFun B := conjSub B g
  invFun B := conjSub B g⁻¹
  left_inv B := conjSub_conjSub_inv_eq B g
  right_inv B := conjSub_inv_conjSub_eq B g

theorem nonempty_mulEquiv_conjSub {K : Subgroup G} {M : Type*} [Group M] (g : G)
    (h : Nonempty (↥K ≃* M)) : Nonempty (↥(conjSub K g) ≃* M) :=
  h.map fun φ => (MulEquiv.subgroupMap (MulAut.conj g) K).symm.trans φ

end Conj

section Class

variable {Z A : Subgroup G}

theorem conjSub_mem_zClass (hA : A ∈ zClass Z) (g : G) : conjSub A g ∈ zClass Z := by
  obtain ⟨a, rfl⟩ := hA
  exact ⟨g * a, conjSub_mul Z g a⟩

theorem conjSub_mem_zClass_iff (g : G) : conjSub A g ∈ zClass Z ↔ A ∈ zClass Z :=
  ⟨fun h => by simpa [conjSub_conjSub_inv_eq] using conjSub_mem_zClass h g⁻¹,
    fun h => conjSub_mem_zClass h g⟩

variable (Z) in
theorem self_mem_zClass : Z ∈ zClass Z := ⟨1, conjSub_one Z⟩

variable (Z) in
theorem zClass_conjSub (a : G) : zClass (conjSub Z a) = zClass Z := by
  ext B
  constructor
  · rintro ⟨g, rfl⟩
    exact conjSub_mem_zClass ⟨a, rfl⟩ g
  · rintro ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    rw [← conjSub_mul, inv_mul_cancel_right]

theorem zClass_eq_of_mem (hA : A ∈ zClass Z) : zClass A = zClass Z := by
  obtain ⟨a, rfl⟩ := hA
  exact zClass_conjSub Z a

theorem mem_sigmaSet_conjSub_iff {B : Subgroup G} (g : G) :
    conjSub B g ∈ sigmaSet (zClass Z) (conjSub A g) ↔ B ∈ sigmaSet (zClass Z) A := by
  show (conjSub B g ∈ zClass Z ∧ conjSub B g ≠ conjSub A g ∧
      Commuting (conjSub A g) (conjSub B g)) ↔ (B ∈ zClass Z ∧ B ≠ A ∧ Commuting A B)
  rw [conjSub_mem_zClass_iff, ne_eq, ne_eq, conjSub_inj_iff, commuting_conjSub_iff]

theorem mem_sigmaSet_conjSub_iff' {B : Subgroup G} (g : G) :
    B ∈ sigmaSet (zClass Z) (conjSub A g) ↔ conjSub B g⁻¹ ∈ sigmaSet (zClass Z) A := by
  have := mem_sigmaSet_conjSub_iff (Z := Z) (A := A) (B := conjSub B g⁻¹) g
  rw [conjSub_inv_conjSub_eq] at this
  exact this

end Class

section Rebase

variable {Z : Subgroup G} {e : ℕ}

theorem Sp4Local.rebase (h : Sp4Local G Z e) (a : G) : Sp4Local G (conjSub Z a) e where
  simple := h.simple
  nonabelian := h.nonabelian
  two_le := h.two_le
  card := (card_conjSub_eq Z a).trans h.card
  sq := sq_of_mem_conjSub h.sq a
  abelian_le := h.abelian_le
  sigma_trans := by
    simp only [zClass_conjSub]
    intro B hB C hC D hD hBC hCD
    have hB' := (mem_sigmaSet_conjSub_iff' a).1 hB
    have hC' := (mem_sigmaSet_conjSub_iff' a).1 hC
    have hD' := (mem_sigmaSet_conjSub_iff' a).1 hD
    exact (commuting_conjSub_iff a⁻¹).1
      (h.sigma_trans _ hB' _ hC' _ hD' (Commuting.conjSub hBC a⁻¹) (Commuting.conjSub hCD a⁻¹))
  sigma_clique := by
    simp only [zClass_conjSub]
    intro B hB
    have hB' := (mem_sigmaSet_conjSub_iff' a).1 hB
    rw [← h.sigma_clique _ hB']
    exact Nat.card_congr (Equiv.subtypeEquiv (conjEquiv a⁻¹) fun C => by
      show (C ∈ sigmaSet (zClass Z) (conjSub Z a) ∧ Commuting B C) ↔
        (conjSub C a⁻¹ ∈ sigmaSet (zClass Z) Z ∧
          Commuting (conjSub B a⁻¹) (conjSub C a⁻¹))
      rw [mem_sigmaSet_conjSub_iff' a, commuting_conjSub_iff a⁻¹])
  sigma_card := by
    simp only [zClass_conjSub]
    rw [← h.sigma_card]
    exact Nat.card_congr (Equiv.subtypeEquiv (conjEquiv a⁻¹) fun C => mem_sigmaSet_conjSub_iff' a)
  dual := by
    simp only [zClass_conjSub]
    intro C hC hnc
    have hC' : conjSub C a⁻¹ ∈ zClass Z := (conjSub_mem_zClass_iff a⁻¹).2 hC
    have hnc' : ¬ Commuting Z (conjSub C a⁻¹) := by
      intro hc
      apply hnc
      have := Commuting.conjSub hc a
      rwa [conjSub_inv_conjSub_eq] at this
    obtain ⟨I', h1, h2, h3, h4, h5, h6⟩ := h.dual _ hC' hnc'
    have hK : conjSub (Z ⊔ conjSub C a⁻¹) a = conjSub Z a ⊔ C := by
      rw [conjSub_sup, conjSub_inv_conjSub_eq]
    refine ⟨conjSub I' a, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hK]
      exact nonempty_mulEquiv_conjSub a h1
    · exact nonempty_mulEquiv_conjSub a h2
    · rw [← hK]
      exact Commuting.conjSub h3 a
    · intro P hP hPc
      have hP' : conjSub P a⁻¹ ≤ I' := by
        rw [← conjSub_le_conjSub_iff a, conjSub_inv_conjSub_eq]
        exact hP
      exact (conjSub_mem_zClass_iff a⁻¹).1 (h4 _ hP' ((card_conjSub_eq P a⁻¹).trans hPc))
    · intro X hX hXZ hXC
      have hX' : conjSub X a⁻¹ ∈ zClass Z := (conjSub_mem_zClass_iff a⁻¹).2 hX
      have hXZ' : Commuting (conjSub X a⁻¹) Z := by
        have := Commuting.conjSub hXZ a⁻¹
        rwa [conjSub_conjSub_inv_eq] at this
      have := h5 _ hX' hXZ' (Commuting.conjSub hXC a⁻¹)
      rw [← conjSub_le_conjSub_iff a, conjSub_inv_conjSub_eq] at this
      exact this
    · intro X hX hXI
      have hX' : conjSub X a⁻¹ ∈ zClass Z := (conjSub_mem_zClass_iff a⁻¹).2 hX
      have hXI' : Commuting (conjSub X a⁻¹) I' := by
        have := Commuting.conjSub hXI a⁻¹
        rwa [conjSub_conjSub_inv_eq] at this
      have := h6 _ hX' hXI'
      rw [← conjSub_le_conjSub_iff a, conjSub_inv_conjSub_eq, hK] at this
      exact this

theorem Sp4Local.at_member (h : Sp4Local G Z e) {A : Subgroup G} (hA : A ∈ zClass Z) :
    Sp4Local G A e := by
  obtain ⟨a, rfl⟩ := hA
  exact h.rebase a

theorem Sp4Local.sigma_trans_at (h : Sp4Local G Z e) {A : Subgroup G} (hA : A ∈ zClass Z) :
    ∀ B ∈ sigmaSet (zClass Z) A, ∀ C ∈ sigmaSet (zClass Z) A, ∀ D ∈ sigmaSet (zClass Z) A,
      Commuting B C → Commuting C D → Commuting B D := by
  have := (h.at_member hA).sigma_trans
  rwa [zClass_eq_of_mem hA] at this

theorem Sp4Local.sigma_clique_at (h : Sp4Local G Z e) {A : Subgroup G} (hA : A ∈ zClass Z) :
    ∀ B ∈ sigmaSet (zClass Z) A,
      Nat.card {C : Subgroup G // C ∈ sigmaSet (zClass Z) A ∧ Commuting B C} = 2 ^ e := by
  have := (h.at_member hA).sigma_clique
  rwa [zClass_eq_of_mem hA] at this

theorem Sp4Local.sigma_card_at (h : Sp4Local G Z e) {A : Subgroup G} (hA : A ∈ zClass Z) :
    Nat.card (sigmaSet (zClass Z) A) = 2 ^ e * (2 ^ e + 1) := by
  have := (h.at_member hA).sigma_card
  rwa [zClass_eq_of_mem hA] at this

theorem Sp4Local.dual_at (h : Sp4Local G Z e) {A : Subgroup G} (hA : A ∈ zClass Z) :
    ∀ C ∈ zClass Z, ¬ Commuting A C → ∃ I : Subgroup G,
      Nonempty (↥(A ⊔ C) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) ∧
      Nonempty (↥I ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) ∧
      Commuting (A ⊔ C) I ∧
      (∀ P : Subgroup G, P ≤ I → Nat.card P = 2 ^ e → P ∈ zClass Z) ∧
      (∀ X ∈ zClass Z, Commuting X A → Commuting X C → X ≤ I) ∧
      (∀ X ∈ zClass Z, Commuting X I → X ≤ A ⊔ C) := by
  have := (h.at_member hA).dual
  rwa [zClass_eq_of_mem hA] at this

end Rebase

end CFSG.CGT.PushingUpLit.A78
