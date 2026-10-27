module

public import CFSG.CGT.PushingUpLit.A78G0.Diam

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
  CFSG.ABGLocalTools

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  (h : G0Core G L₁ L₂ V W Z Z₂ e)

include h

theorem exists_noncommuting : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative G := ⟨⟨fun a b => hcon a b⟩⟩
  have hp : (Nat.card G).Prime := Group.is_simple_iff_prime_card.1 h.simple
  have hdvd : 2 ^ e ∣ Nat.card G := h.card_Z ▸ Subgroup.card_subgroup_dvd_card Z
  have h2 : 2 ∣ Nat.card G := (dvd_pow_self 2 (by have := h.two_le; omega)).trans hdvd
  have h3 : 2 = Nat.card G := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
  have h4 : 2 ^ e ≤ 2 := by
    have := Nat.le_of_dvd hp.pos hdvd
    omega
  have h5 : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h.two_le
  omega

theorem card_elemAbelian_le (E : Subgroup G) (_hab : ∀ x ∈ E, ∀ y ∈ E, Commute x y)
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 ^ (3 * e) := by
  have hE2 : IsPGroup 2 ↥E := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    have := hsq x x.2
    simpa [pow_two] using this
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf h.sylow (le_top : E ≤ ⊤) hE2
  have hsq' : ∀ x ∈ cj k E, x * x = 1 := sq_of_mem_conjSub hsq k
  have h1 := h.jst.card_le_of_elemAbelian hk hsq'
  rw [card_cj, h.pair.side₁.card_V, h.card_Z] at h1
  calc Nat.card E ≤ 2 ^ (2 * e) * 2 ^ e := h1
    _ = 2 ^ (3 * e) := by ring

theorem dual_clause (hd : DualBase h) : ∀ C ∈ zClass Z, ¬ Commuting Z C → ∃ I : Subgroup G,
    Nonempty (↥(Z ⊔ C) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) ∧
    Nonempty (↥I ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) ∧
    Commuting (Z ⊔ C) I ∧
    (∀ P : Subgroup G, P ≤ I → Nat.card P = 2 ^ e → P ∈ zClass Z) ∧
    (∀ X ∈ zClass Z, Commuting X Z → Commuting X C → X ≤ I) ∧
    (∀ X ∈ zClass Z, Commuting X I → X ≤ Z ⊔ C) := by
  intro C hC hZC
  obtain ⟨K, A, I, hK, D⟩ := hd.exists_sl2Dual
  obtain ⟨U, hU, hZU, hUC⟩ := h.diam2 hd Z (self_mem_zClass Z) C hC
  have hZne : Z ≠ U := by
    rintro rfl
    exact hZC hUC
  have hCne : C ≠ U := by
    rintro rfl
    exact hZC hZU
  obtain ⟨m, rfl⟩ := hU
  obtain ⟨l, hl, hZCK⟩ := kcount_cs hK m ⟨self_mem_zClass Z, hZne, commuting_symm hZU⟩
    ⟨hC, hCne, hUC⟩ hZC
  have D' := D.conj (m * l)
  rw [← hZCK] at D'
  have hcl := h.sigmaCliques
  have hZCne : Z ≠ C := by
    rintro rfl
    exact hZC (h.commuting_self (self_mem_zClass Z))
  refine ⟨cs I (m * l), D'.iso₁, D'.iso₂, D'.comm, D'.syl₂, ?_, ?_⟩
  · intro X hX hXZ hXC
    have heq := D'.commonNbrs_eq hcl h.two_le (le_sup_left : Z ≤ Z ⊔ C)
      (le_sup_right : C ≤ Z ⊔ C) h.card_Z (h.card_of_mem_zClass hC) hZCne
    have hmem : X ∈ {X : Subgroup G | X ∈ zClass Z ∧ Commuting X Z ∧ Commuting X C} :=
      ⟨hX, hXZ, hXC⟩
    rw [heq] at hmem
    exact hmem.1
  · intro X hX hXI
    obtain ⟨φ₂⟩ := D'.iso₂
    have hcard : 1 < {P : Subgroup G | P ≤ cs I (m * l) ∧ Nat.card P = 2 ^ e}.ncard := by
      rw [ncard_sylow_sl2 h.two_le φ₂]
      have := Nat.two_pow_pos e
      omega
    obtain ⟨P, hP, P', hP', hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).1 hcard
    have heq := D'.symm.commonNbrs_eq hcl h.two_le hP.1 hP'.1 hP.2 hP'.2 hne
    have hmem : X ∈ {X : Subgroup G | X ∈ zClass Z ∧ Commuting X P ∧ Commuting X P'} :=
      ⟨hX, fun x hx p hp => hXI x hx p (hP.1 hp), fun x hx p hp => hXI x hx p (hP'.1 hp)⟩
    rw [heq] at hmem
    exact hmem.1

theorem sp4Local (hd : DualBase h) : Sp4Local G Z e where
  simple := h.simple
  nonabelian := h.exists_noncommuting
  two_le := h.two_le
  card := h.card_Z
  sq := h.sq_Z
  abelian_le := h.card_elemAbelian_le
  sigma_trans := h.sigma_trans
  sigma_clique := h.sigma_clique
  sigma_card := h.sigma_card
  dual := h.dual_clause hd

end G0Core

end CFSG.CGT.PushingUpLit.A78G0
