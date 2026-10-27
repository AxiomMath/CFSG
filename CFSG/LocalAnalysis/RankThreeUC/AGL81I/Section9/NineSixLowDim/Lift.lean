module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open scoped commutatorElement

private lemma normalizerQuotCenterHom_mk {X : Type*} [Group X] (C : Subgroup X)
    (g : ↥(normalizer (C : Set X))) (c : ↥C) :
    normalizerQuotCenterHom C g (c : ↥C ⧸ center ↥C) =
      (C.normalizerMonoidHom g c : ↥C ⧸ center ↥C) :=
  FiveTransitive.CharacteristicAutomorphism.quotient_apply_mk _ _ c

private def centerPowEqOne (G : Type*) [Group G] (m : ℕ) : Subgroup G where
  carrier := {z | z ∈ center G ∧ z ^ m = 1}
  mul_mem' {a b} ha hb :=
    ⟨mul_mem ha.1 hb.1, by rw [Commute.mul_pow (mem_center_iff.mp hb.1 a), ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow _⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

private lemma not_dvd_card_centerPowEqOne {G : Type*} [Group G] [Finite G] {p m : ℕ}
    (hp : p.Prime) (hm : ¬ p ∣ m) : ¬ p ∣ Nat.card (centerPowEqOne G m) := by
  intro h
  have := Fact.mk hp
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p h
  apply hm
  rw [← hz, ← Subgroup.orderOf_coe]
  exact orderOf_dvd_of_pow_eq_one z.2.2

private lemma card_preimage_pow_eq_one {G : Type*} [Group G] {m : ℕ} {c₀ : G}
    (hc₀ : c₀ ^ m = 1) :
    Nat.card {c : G // (c : G ⧸ center G) = (c₀ : G ⧸ center G) ∧ c ^ m = 1} =
      Nat.card (centerPowEqOne G m) := by
  have hz : ∀ c : G, (c : G ⧸ center G) = (c₀ : G ⧸ center G) → c₀⁻¹ * c ∈ center G :=
    fun c hc => QuotientGroup.eq.mp hc.symm
  refine Nat.card_congr
    { toFun := fun s => ⟨c₀⁻¹ * s.1, hz s.1 s.2.1, ?_⟩
      invFun := fun t => ⟨c₀ * t.1, ?_, ?_⟩
      left_inv := fun s => Subtype.ext (mul_inv_cancel_left c₀ s.1)
      right_inv := fun t => Subtype.ext (inv_mul_cancel_left c₀ t.1) }
  · have h := Commute.mul_pow (mem_center_iff.mp (hz s.1 s.2.1) c₀) m
    rw [mul_inv_cancel_left, s.2.2, hc₀, one_mul] at h
    exact h.symm
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr t.2.1, mul_one]
  · rw [Commute.mul_pow (mem_center_iff.mp t.2.1 c₀), hc₀, t.2.2, one_mul]

private lemma exists_preimage_pow_eq_one {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] {p : ℕ} (hp : p.Prime) {x : G ⧸ N} (hx : ¬ p ∣ orderOf x) :
    ∃ m, ¬ p ∣ m ∧ ∃ c : G, (c : G ⧸ N) = x ∧ c ^ m = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨e, m, hpm, hN⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' p hp.one_lt.ne'
  have hxm : orderOf (y : G ⧸ N) ∣ m := by
    have h := orderOf_map_dvd (QuotientGroup.mk' N) y
    rw [hN] at h
    exact (Nat.Coprime.pow_right e (Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hx))).dvd_of_dvd_mul_left h
  obtain ⟨k, hk⟩ : ∃ k, p ^ e * k ≡ 1 [MOD m] := by
    rcases Nat.lt_or_ge 1 m with h | h
    · obtain ⟨k, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
        (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)) h
      exact ⟨k, by rw [Nat.ModEq, hk.2, Nat.mod_eq_of_lt h]⟩
    · interval_cases m
      · exact absurd hN (by simpa using (orderOf_pos y).ne')
      · exact ⟨0, Nat.modEq_one⟩
  refine ⟨m, hpm, y ^ (p ^ e * k), ?_, ?_⟩
  · rw [QuotientGroup.mk_pow]
    exact (pow_eq_pow_iff_modEq.mpr (hk.of_dvd hxm)).trans (pow_one _)
  · rw [← pow_mul, mul_right_comm, ← hN, pow_mul, pow_orderOf_eq_one, one_pow]

private lemma exists_fixed_of_pow_eq_one {α : Type*} [Finite α] {p n : ℕ} (hp : p.Prime)
    {f : Function.End α} (hf : f ^ p ^ n = 1) (hα : ¬ p ∣ Nat.card α) : ∃ a, f a = a := by
  classical
  have := Fintype.ofFinite α
  have := Fact.mk hp
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) hf
  by_contra hne
  push Not at hne
  have : IsEmpty (Function.fixedPoints f) := ⟨fun a => hne a.1 a.2⟩
  simp only [Fintype.card_eq_nat_card, Nat.card_of_isEmpty] at h
  exact hα (Nat.modEq_zero_iff_dvd.mp h)

theorem exists_lift_of_fixed {X : Type*} [Group X] [Finite X] {C : Subgroup X} {p : ℕ}
    (hp : p.Prime) {g : ↥(Subgroup.normalizer (C : Set X))} (hg : ∃ n : ℕ, (g : X) ^ p ^ n = 1)
    {x : ↥C ⧸ Subgroup.center ↥C} (hx : ¬ p ∣ orderOf x)
    (hfix : normalizerQuotCenterHom C g x = x) :
    ∃ c : ↥C, (c : ↥C ⧸ Subgroup.center ↥C) = x ∧ (g : X) * c * (g : X)⁻¹ = c := by
  obtain ⟨n, hn⟩ := hg
  obtain ⟨m, hpm, c₀, rfl, hc₀⟩ := exists_preimage_pow_eq_one (N := center ↥C) hp hx
  let S := {c : ↥C // (c : ↥C ⧸ center ↥C) = (c₀ : ↥C ⧸ center ↥C) ∧ c ^ m = 1}
  let f : Function.End S := fun s => ⟨C.normalizerMonoidHom g s.1,
    by rw [← normalizerQuotCenterHom_mk, s.2.1, hfix], by rw [← map_pow, s.2.2, map_one]⟩
  have hpow : ∀ (k : ℕ) (s : S), ((f ^ k) s).1 = C.normalizerMonoidHom (g ^ k) s.1 := by
    intro k
    induction k with
    | zero => intro s; simp; rfl
    | succ k ih =>
      intro s
      rw [pow_succ, pow_succ, map_mul, MulAut.mul_apply]
      show ((f ^ k) (f s)).1 = _
      rw [ih]
  have hf : f ^ p ^ n = 1 := by
    funext s
    apply Subtype.ext
    rw [hpow, show g ^ p ^ n = 1 from Subtype.ext (by simpa using hn), map_one]
    rfl
  have hS : ¬ p ∣ Nat.card S := by
    rw [card_preimage_pow_eq_one hc₀]
    exact not_dvd_card_centerPowEqOne hp hpm
  obtain ⟨s, hs⟩ := exists_fixed_of_pow_eq_one hp hf hS
  exact ⟨s.1, s.2.1, congrArg (fun t : S => ((t.1 : ↥C) : X)) hs⟩

private lemma commutatorElement_mul_mem_center {G : Type*} [Group G] {a b z w : G}
    (hz : z ∈ center G) (hw : w ∈ center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := mem_center_iff.mp hz
  have hw' := mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * (b * w)) * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by rw [← hz' (b * w)]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [← hw' a⁻¹]; group

theorem le_iSup_centralizer_of_closure_eq_top {X : Type*} [Group X] [Finite X]
    {C : Subgroup X} (hC : Group.IsPerfect ↥C) {p : ℕ} (hp : p.Prime) {E : Subgroup X}
    (_hEN : E ≤ Subgroup.normalizer (C : Set X)) (hE : IsPGroup p E)
    (hgen : Subgroup.closure {x : ↥C ⧸ Subgroup.center ↥C | ¬ p ∣ orderOf x ∧
      ∃ g : ↥(Subgroup.normalizer (C : Set X)), (g : X) ∈ E ∧
        normalizerQuotCenterHom C g ≠ 1 ∧ normalizerQuotCenterHom C g x = x} = ⊤) :
    C ≤ ⨆ (e : X) (_ : e ∈ E) (_ : e ≠ 1), Subgroup.centralizer ({e} : Set X) := by
  set R := ⨆ (e : X) (_ : e ∈ E) (_ : e ≠ 1), Subgroup.centralizer ({e} : Set X)
  have hmap : (R.subgroupOf C).map (QuotientGroup.mk' (center ↥C)) = ⊤ := by
    rw [eq_top_iff, ← hgen, closure_le]
    rintro x ⟨hx, g, hgE, hg1, hfix⟩
    obtain ⟨n, hn⟩ := hE ⟨g, hgE⟩
    obtain ⟨c, hc, hcg⟩ :=
      exists_lift_of_fixed hp ⟨n, by simpa using congrArg Subtype.val hn⟩ hx hfix
    have hne : (g : X) ≠ 1 := fun h => hg1 (by rw [show g = 1 from Subtype.ext h, map_one])
    refine ⟨c, ?_, hc⟩
    exact mem_subgroupOf.mpr (mem_iSup_of_mem (g : X) (mem_iSup_of_mem hgE (mem_iSup_of_mem hne
      (mem_centralizer_singleton_iff.mpr (eq_mul_inv_iff_mul_eq.mp hcg.symm)))))
  have hsurj : ∀ c : ↥C, ∃ r ∈ R.subgroupOf C, r⁻¹ * c ∈ center ↥C := by
    intro c
    obtain ⟨r, hr, hrc⟩ := (mem_map.mp (hmap ▸ mem_top (c : ↥C ⧸ center ↥C)))
    exact ⟨r, hr, QuotientGroup.eq.mp hrc⟩
  have hle : commutator ↥C ≤ R.subgroupOf C := by
    rw [commutator_def, commutator_le]
    intro a _ b _
    obtain ⟨r, hr, hra⟩ := hsurj a
    obtain ⟨s, hs, hsb⟩ := hsurj b
    rw [← mul_inv_cancel_left r a, ← mul_inv_cancel_left s b,
      commutatorElement_mul_mem_center hra hsb, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hr hs) (inv_mem hr)) (inv_mem hs)
  intro c hc
  exact mem_subgroupOf.mp (hle (hC.commutator_eq_top ▸ mem_top (⟨c, hc⟩ : ↥C)))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
