module

public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma551

public section

namespace CFSG.ComponentClassification.HSFLit.L34Uniq

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open scoped Pointwise

variable {G : Type} [Group G]

theorem eq_of_card_two [Finite G] {A : Subgroup G} (hA : Nat.card A = 2) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA
  have hzp : zpowers a = A := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ha)
    rw [hA, Nat.card_zpowers]
    have h1 : orderOf a ∣ 2 := hA ▸ Subgroup.orderOf_dvd_natCard A ha
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · rw [h]
  have hb' : b ∈ zpowers a := hzp ▸ hb
  have ha2 : a * a = 1 := by
    have h1 : orderOf a ∣ 2 := hA ▸ Subgroup.orderOf_dvd_natCard A ha
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  rcases eq_one_or_eq_of_mem_zpowers' ha2 hb' with h | h
  · exact absurd h hb1
  · exact h.symm

theorem isElemTwo_closure {X : Set G} (h2 : ∀ x ∈ X, x * x = 1)
    (hc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : IsElemTwo (closure X) := by
  have hcomm : ∀ a ∈ closure X, ∀ b ∈ closure X, a * b = b * a := by
    have h1 : closure X ≤ centralizer X :=
      (closure_le _).mpr fun x hx => mem_centralizer_iff.mpr fun y hy => hc y hy x hx
    intro a ha b hb
    have h2' : closure X ≤ centralizer ({a} : Set G) := by
      refine (closure_le _).mpr fun x hx => mem_centralizer_singleton_iff.mpr ?_
      exact (mem_centralizer_iff.mp (h1 ha)) x hx
    exact (mem_centralizer_singleton_iff.mp (h2' hb)).symm
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h2 x hx
  | one => exact one_mul 1
  | mul a b ha hb iha ihb =>
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm b hb a ha]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha =>
    rw [← mul_inv_rev, iha, inv_one]

theorem comm_sq_mem_of_le_sup {A Q C : Subgroup G} (hA : IsElemTwo A) (hQC : Q ≤ C)
    (hAC : A ≤ normalizer (C : Set G)) (hQN : A ≤ normalizer (Q : Set G)) :
    ∀ e ∈ A ⊔ Q, ∀ f ∈ A ⊔ Q, e⁻¹ * f⁻¹ * e * f ∈ C ∧ e * e ∈ C := by
  have hset : ((A ⊔ Q : Subgroup G) : Set G) = (A : Set G) * (Q : Set G) :=
    coe_mul_of_left_le_normalizer_right A Q hQN
  have hconj : ∀ a ∈ A, ∀ c ∈ C, a⁻¹ * c * a ∈ C := fun a ha c hc => by
    have := (mem_normalizer_iff.mp (inv_mem (hAC ha)) c).mp hc
    rwa [inv_inv] at this
  intro e he f hf
  have he' : e ∈ (A : Set G) * (Q : Set G) := hset ▸ he
  have hf' : f ∈ (A : Set G) * (Q : Set G) := hset ▸ hf
  obtain ⟨a, ha, c, hc, rfl⟩ := he'
  obtain ⟨b, hb, d, hd, rfl⟩ := hf'
  have hc' : c ∈ C := hQC hc
  have hd' : d ∈ C := hQC hd
  have hab : a⁻¹ * b⁻¹ * a = b⁻¹ := by
    rw [mul_assoc, hA.1 _ (inv_mem hb) _ ha]; group
  constructor
  · have e1 : (a * c)⁻¹ * (b * d)⁻¹ * (a * c) * (b * d) =
        c⁻¹ * (a⁻¹ * d⁻¹ * a) * (a⁻¹ * b⁻¹ * a) * c * b * d := by group
    rw [e1, hab]
    have e2 : c⁻¹ * (a⁻¹ * d⁻¹ * a) * b⁻¹ * c * b * d =
        c⁻¹ * (a⁻¹ * d⁻¹ * a) * (b⁻¹ * c * b) * d := by group
    rw [e2]
    exact mul_mem (mul_mem (mul_mem (inv_mem hc') (hconj a ha _ (inv_mem hd')))
      (hconj b hb c hc')) hd'
  · have e1 : a * c * (a * c) = (a * a) * (a⁻¹ * c * a) * c := by group
    rw [e1, hA.2 a ha, one_mul]
    exact mul_mem (hconj a ha c hc') hc'

theorem card_le_of_inf_le_two [Finite G] {F Q : Subgroup G} (hF : Nat.card F = 16)
    (hFQ : Nat.card ↥(F ⊓ Q) ≤ 2) (hN : F ≤ normalizer (Q : Set G)) :
    8 * Nat.card Q ≤ Nat.card ↥(F ⊔ Q) := by
  have h := RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hN
  rw [hF] at h
  rw [sup_comm]
  rw [inf_comm] at hFQ
  have h2 : Nat.card ↥(Q ⊔ F) * Nat.card ↥(Q ⊓ F) ≤ Nat.card ↥(Q ⊔ F) * 2 :=
    Nat.mul_le_mul_left _ hFQ
  omega

@[expose] def conjSet (S : Subgroup G) (e : G) : Set G := {x | ∃ g ∈ S, x = g⁻¹ * e * g}

theorem le_normalizer_closure_conjSet (S : Subgroup G) (e : G) :
    S ≤ normalizer ((closure (conjSet S e) : Subgroup G) : Set G) := by
  have key : ∀ s ∈ S, ∀ x ∈ closure (conjSet S e), s * x * s⁻¹ ∈ closure (conjSet S e) := by
    intro s hs x hx
    have h1 : closure (conjSet S e) ≤
        (closure (conjSet S e)).comap (MulAut.conj s).toMonoidHom := by
      refine (closure_le _).mpr fun y hy => ?_
      obtain ⟨g, hg, rfl⟩ := hy
      show s * (g⁻¹ * e * g) * s⁻¹ ∈ closure (conjSet S e)
      refine subset_closure ⟨g * s⁻¹, mul_mem hg (inv_mem hs), ?_⟩
      group
    exact h1 hx
  intro s hs
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => key s hs x hx, fun hx => ?_⟩
  have := key s⁻¹ (inv_mem hs) _ hx
  rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at this

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have h : conjugate (A ⊔ B) g = A ⊔ B := by
    rw [show conjugate (A ⊔ B) g = conjugate A g ⊔ conjugate B g from Subgroup.map_sup _ _ _,
      conjugate_eq_self hA, conjugate_eq_self hB]
  exact mem_normalizer_of_conjugate_eq h

theorem card_le_two_of_two_conj [Finite G] {S K : Subgroup G} {s : G} (hs : s ∈ S)
    (horb : ∀ g ∈ S, conjugate K g = K ∨ conjugate K g = conjugate K s) :
    Nat.card S ≤ 2 * Nat.card ↥(S ⊓ normalizer (K : Set G)) := by
  classical
  have hN : ∀ g ∈ S, conjugate K g = conjugate K s →
      g * s⁻¹ ∈ S ⊓ normalizer (K : Set G) := by
    intro g hg h
    refine mem_inf.mpr ⟨mul_mem hg (inv_mem hs), mem_normalizer_of_conjugate_eq ?_⟩
    rw [← conjugate_conjugate'', h, conjugate_conjugate'', mul_inv_cancel, conjugate_one]
  let f : ↥S → Bool × ↥(S ⊓ normalizer (K : Set G)) := fun g =>
    if h : conjugate K (g : G) = K then
      (true, ⟨g, mem_inf.mpr ⟨g.2, mem_normalizer_of_conjugate_eq h⟩⟩)
    else (false, ⟨g * s⁻¹, hN g g.2 ((horb g g.2).resolve_left h)⟩)
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    by_cases ha : conjugate K (a : G) = K <;> by_cases hb : conjugate K (b : G) = K <;>
      simp only [ha, hb, dite_true, dite_false, Prod.mk.injEq, Bool.true_eq_false,
        Bool.false_eq_true, false_and] at hab
    · exact Subtype.ext (congrArg (fun x : ↥(S ⊓ normalizer (K : Set G)) => (x : G)) hab.2)
    · apply Subtype.ext
      have := congrArg (fun x : ↥(S ⊓ normalizer (K : Set G)) => (x : G)) hab.2
      simpa using this
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this

end CFSG.ComponentClassification.HSFLit.L34Uniq
