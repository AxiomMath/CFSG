module

public import CFSG.CGT.PushingUpLit.T2KSW.StrongEmb

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG.Open CFSG.ABGLocalTools CFSG.CGT.PushingUpLit.T2KSW
open scoped Pointwise

variable {X : Type*} [Group X]

@[expose] def SylowAdj (A B : Sylow 2 X) : Prop :=
  A ≠ B ∧ ∃ x : X, x ≠ 1 ∧ x ∈ A ∧ x ∈ B

abbrev SylowConn (A B : Sylow 2 X) : Prop :=
  Relation.ReflTransGen SylowAdj A B

theorem SylowAdj.symm {A B : Sylow 2 X} (h : SylowAdj A B) : SylowAdj B A :=
  ⟨h.1.symm, by
    obtain ⟨x, hx1, hxA, hxB⟩ := h.2
    exact ⟨x, hx1, hxB, hxA⟩⟩

theorem SylowAdj.smul {A B : Sylow 2 X} (g : X) (h : SylowAdj A B) :
    SylowAdj (g • A) (g • B) := by
  refine ⟨fun hg => h.1 (MulAction.injective g hg), ?_⟩
  obtain ⟨x, hx1, hxA, hxB⟩ := h.2
  refine ⟨MulAut.conj g x, fun h1 => hx1 ?_, ?_, ?_⟩
  · exact (MulAut.conj g).injective (by rw [h1, map_one])
  · exact Subgroup.smul_mem_pointwise_smul (G := X) x (MulAut.conj g) _ hxA
  · exact Subgroup.smul_mem_pointwise_smul (G := X) x (MulAut.conj g) _ hxB

namespace SylowConn

theorem refl {A : Sylow 2 X} : SylowConn A A := Relation.ReflTransGen.refl

theorem trans {A B C : Sylow 2 X} (h : SylowConn A B) (h' : SylowConn B C) : SylowConn A C :=
  Relation.ReflTransGen.trans h h'

theorem of_adj {A B : Sylow 2 X} (h : SylowAdj A B) : SylowConn A B :=
  Relation.ReflTransGen.single h

theorem symm {A B : Sylow 2 X} (h : SylowConn A B) : SylowConn B A := by
  induction h with
  | refl => exact refl
  | tail _ hbc ih => exact trans (of_adj hbc.symm) ih

theorem smul {A B : Sylow 2 X} (g : X) (h : SylowConn A B) : SylowConn (g • A) (g • B) := by
  induction h with
  | refl => exact refl
  | tail _ hbc ih => exact trans ih (of_adj (hbc.smul g))

theorem of_mem {A B : Sylow 2 X} {x : X} (hx1 : x ≠ 1) (hxA : x ∈ A) (hxB : x ∈ B) :
    SylowConn A B := by
  by_cases h : A = B
  · rw [h]
  · exact of_adj ⟨h, x, hx1, hxA, hxB⟩

end SylowConn

private theorem mem_map_conj_inv_iff' {H : Subgroup X} {g y : X} :
    y ∈ H.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩

private theorem exists_smul_mem_of_orderOf_two [Finite X] {A : Sylow 2 X} {M : Subgroup X}
    (hAM : (A : Subgroup X) ≤ M) {t : X} (htM : t ∈ M) (ht : orderOf t = 2) :
    ∃ m ∈ M, t ∈ (m • A : Sylow 2 X) := by
  have hA : IsSylowOf 2 (A : Subgroup X) ⊤ := by
    rw [isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, A.isPGroup', A.not_dvd_index⟩
  have hAM' : IsSylowOf 2 (A : Subgroup X) M := hA.of_le hAM le_top
  have hP2 : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht, pow_one]
  obtain ⟨m, hm, hmA⟩ := exists_mem_conj_mem_of_isSylowOf hAM'
    ((Subgroup.zpowers_le (G := X)).2 htM) hP2
  refine ⟨m, hm, ?_⟩
  have h1 : m⁻¹ * t * m ∈ (A : Subgroup X) := hmA t (Subgroup.mem_zpowers t)
  show t ∈ MulAut.conj m • (A : Subgroup X)
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have h2 : (MulAut.conj m)⁻¹ • t = m⁻¹ * t * m := by
    simp [MulAut.smul_def]
  rw [h2]
  exact h1

theorem sylowConn_of_no_stronglyEmbedded [Finite X]
    (hX : ¬ ∃ K : Subgroup X, fusionStronglyEmbedded K) (A B : Sylow 2 X) : SylowConn A B := by
  by_contra hAB
  let M : Subgroup X :=
    { carrier := {g | SylowConn A (g • A)}
      mul_mem' := fun {g h} hg hh => by
        have h1 : SylowConn (g • A) (g • h • A) := SylowConn.smul g hh
        rw [← mul_smul] at h1
        exact SylowConn.trans hg h1
      one_mem' := by
        show SylowConn A ((1 : X) • A)
        rw [one_smul]
      inv_mem' := fun {g} hg => by
        have h1 : SylowConn (g⁻¹ • A) (g⁻¹ • g • A) := SylowConn.smul g⁻¹ hg
        rw [inv_smul_smul] at h1
        exact h1.symm }
  have hmemM : ∀ g : X, g ∈ M ↔ SylowConn A (g • A) := fun g => Iff.rfl
  have hAM : (A : Subgroup X) ≤ M := fun a ha => by
    rw [hmemM, Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer ha)]
  have hMne : M ≠ ⊤ := by
    intro hM
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X A B
    have hgM : g ∈ M := hM ▸ Subgroup.mem_top g
    apply hAB
    have h' : SylowConn A (g • A) := hgM
    rwa [hg] at h'
  have hAbot : (A : Subgroup X) ≠ ⊥ := by
    intro hA
    apply hAB
    have hB : (B : Subgroup X) = ⊥ := by
      have h1 : Nat.card (B : Subgroup X) = Nat.card (A : Subgroup X) := by
        rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
      rw [hA, Subgroup.card_bot] at h1
      exact (Subgroup.eq_bot_iff_card _).2 h1
    have : A = B := Sylow.ext (hA.trans hB.symm)
    rw [this]
  have hMeven : Even (Nat.card M) := by
    have h1 : Nat.card (A : Subgroup X) ∣ Nat.card M := Subgroup.card_dvd_of_le hAM
    have h2 : 2 ∣ Nat.card (A : Subgroup X) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 A.isPGroup'
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hAbot ((Subgroup.eq_bot_iff_card _).2 (by simpa using hk))
      rw [hk]
      exact dvd_pow_self 2 hk0
    exact even_iff_two_dvd.2 (h2.trans h1)
  refine hX ⟨M, hMne, hMeven, fun g hg => ?_⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
  have htM : (t : X) ∈ M := t.2.1
  have htMg : (t : X) ∈ M.map (MulAut.conj g⁻¹).toMonoidHom := t.2.2
  have hord : orderOf (t : X) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact ht
  have ht1 : (t : X) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have htM' : g * t * g⁻¹ ∈ M := mem_map_conj_inv_iff'.1 htMg
  have hord' : orderOf (g * (t : X) * g⁻¹) = 2 := by
    rw [← hord]
    simpa [mul_assoc] using orderOf_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective (t : X)
  obtain ⟨m, hm, hmt⟩ := exists_smul_mem_of_orderOf_two hAM htM hord
  obtain ⟨m', hm', hm't⟩ := exists_smul_mem_of_orderOf_two hAM htM' hord'
  have hm'A : SylowConn A (m' • A) := hm'
  have h3 : (t : X) ∈ ((g⁻¹ * m') • A : Sylow 2 X) := by
    show (t : X) ∈ MulAut.conj (g⁻¹ * m') • (A : Subgroup X)
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h4 : (MulAut.conj (g⁻¹ * m'))⁻¹ • (t : X) = ((MulAut.conj m')⁻¹ • (g * t * g⁻¹)) := by
      simp [MulAut.smul_def, mul_assoc]
    rw [h4]
    have h5 : g * (t : X) * g⁻¹ ∈ (m' • A : Sylow 2 X) := hm't
    show _ ∈ (A : Subgroup X)
    have h6 := h5
    change g * (t : X) * g⁻¹ ∈ MulAut.conj m' • (A : Subgroup X) at h6
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h6
    exact h6
  have h7 : SylowConn (m • A) ((g⁻¹ * m') • A) := SylowConn.of_mem ht1 hmt h3
  have h8 : SylowConn (g⁻¹ • A) ((g⁻¹ * m') • A) := by
    have := SylowConn.smul g⁻¹ hm'A
    rwa [← mul_smul] at this
  have hmA : SylowConn A (m • A) := hm
  have h9 : SylowConn A (g⁻¹ • A) := hmA.trans (h7.trans h8.symm)
  apply hg
  have hginv : g⁻¹ ∈ M := h9
  simpa using M.inv_mem hginv

end CFSG.CGT.PushingUpLit.C2L
