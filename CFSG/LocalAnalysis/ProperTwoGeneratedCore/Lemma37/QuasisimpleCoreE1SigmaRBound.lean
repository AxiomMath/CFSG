module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1SigmaRTypeD

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x m : G}

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G]
  (htype : ∀ s ∈ S.map (QuotientGroup.mk' Z), s ∉ T.map (QuotientGroup.mk' Z) →
    s * s = 1 → CaseC3.Genuine Z s)
include hb htype

theorem exists_conj_thirtytwo_typeD {n : G ⧸ Z} (hn : n ∈ e1NBar Z u m y x) :
    ∃ w, e1EStar w ∧ n * caseC3Word Z u m y x 32 * n⁻¹ = caseC3Word Z u m y x w := by
  obtain ⟨h1, h2, h3⟩ := hb.conj_mem_e1EBar_of_typeD htype (conj_mem_of_mem_e1NBar hn)
    (hb.caseC3Word_mem_e1EBar_iff.mpr e1E_gens.1) (fun h => by
      rw [hb.caseC3Word_eq_one_iff] at h; exact absurd h (by decide))
    (fun h => absurd (hb.caseC3Word_inj.mp h) (by decide))
  obtain ⟨w, hw, hwe⟩ := hb.mem_e1EBar_iff.mp h1
  exact ⟨w, ⟨hw, fun h => h2 (by rw [← hwe, h, caseC3Word_zero]), fun h => h3 (by rw [← hwe, h])⟩,
    hwe.symm⟩

omit htype in
theorem inv_mul_mem_e1KBar_iff (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) {a b : G ⧸ Z}
    (ha : a ∈ e1NBar Z u m y x) (hb' : b ∈ e1NBar Z u m y x) {w w' : Fin 64}
    (hwa : a * caseC3Word Z u m y x 32 * a⁻¹ = caseC3Word Z u m y x w)
    (hwb : b * caseC3Word Z u m y x 32 * b⁻¹ = caseC3Word Z u m y x w') :
    a⁻¹ * b ∈ e1KBar Z u m y x ↔ w' = w ∨ w' = c3Mul w 40 := by
  have h32 : e1Sing 32 := by decide
  obtain ⟨hR, hrr, hr1, hrz⟩ := hb.sing_iff.mpr h32
  have hza : a⁻¹ * caseC3Word Z u m y x 40 * a = caseC3Word Z u m y x 40 :=
    calc a⁻¹ * caseC3Word Z u m y x 40 * a =
          a⁻¹ * (a * caseC3Word Z u m y x 40 * a⁻¹) * a := by
          rw [hb.conj_forty_of_mem_e1NBar ha]
      _ = caseC3Word Z u m y x 40 := by group
  have hconj : a⁻¹ * b * caseC3Word Z u m y x 32 * (a⁻¹ * b)⁻¹ =
      a⁻¹ * caseC3Word Z u m y x w' * a := by
    rw [show a⁻¹ * b * caseC3Word Z u m y x 32 * (a⁻¹ * b)⁻¹ =
      a⁻¹ * (b * caseC3Word Z u m y x 32 * b⁻¹) * a by group, hwb]
  have hw : caseC3Word Z u m y x w = a * caseC3Word Z u m y x 32 * a⁻¹ := hwa.symm
  constructor
  · intro hK
    obtain ⟨-, hK'⟩ := (hb.mem_e1KBar_iff S' hS').mp hK
    rcases hK' _ hR with h | h <;> rw [hconj] at h
    · left
      rw [← hb.caseC3Word_inj, hw, ← h]
      group
    · right
      rw [← hb.caseC3Word_inj, ← hb.caseC3Word_mul, hw]
      calc caseC3Word Z u m y x w' = a * (a⁻¹ * caseC3Word Z u m y x w' * a) * a⁻¹ := by group
        _ = a * caseC3Word Z u m y x 32 * a⁻¹ * (a * caseC3Word Z u m y x 40 * a⁻¹) := by
            rw [h]; group
        _ = a * caseC3Word Z u m y x 32 * a⁻¹ * caseC3Word Z u m y x 40 := by
            rw [hb.conj_forty_of_mem_e1NBar ha]
  · have hab : a⁻¹ * b ∈ e1NBar Z u m y x :=
      (e1NBar Z u m y x).mul_mem ((e1NBar Z u m y x).inv_mem ha) hb'
    rintro (rfl | rfl)
    · refine hb.mem_e1KBar_of_conj S' hS' hab hR hrr hr1 hrz (Or.inl ?_)
      rw [hconj, hw]
      group
    · refine hb.mem_e1KBar_of_conj S' hS' hab hR hrr hr1 hrz (Or.inr ?_)
      rw [hconj, ← hb.caseC3Word_mul, hw, show a⁻¹ * (a * caseC3Word Z u m y x 32 * a⁻¹ *
        caseC3Word Z u m y x 40) * a = caseC3Word Z u m y x 32 *
          (a⁻¹ * caseC3Word Z u m y x 40 * a) by group, hza]

theorem relIndex_e1KBar_dvd_three (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) :
    (e1KBar Z u m y x).relIndex (e1NBar Z u m y x) ∣ 3 := by
  classical
  let pt : G ⧸ Z → Fin 3 := fun t => e1PtW (Function.invFun (caseC3Word Z u m y x) t)
  have hpt : ∀ w, pt (caseC3Word Z u m y x w) = e1PtW w := fun w => by
    simp only [pt, Function.leftInverse_invFun hb.caseC3Word_bijective.1 w]
  have hkey : ∀ a b : e1NBar Z u m y x, (a : G ⧸ Z)⁻¹ * b ∈ e1KBar Z u m y x ↔
      pt (a * caseC3Word Z u m y x 32 * (a : G ⧸ Z)⁻¹) =
        pt (b * caseC3Word Z u m y x 32 * (b : G ⧸ Z)⁻¹) := by
    intro a b
    obtain ⟨w, hw, hwa⟩ := hb.exists_conj_thirtytwo_typeD htype a.2
    obtain ⟨w', hw', hwb⟩ := hb.exists_conj_thirtytwo_typeD htype b.2
    rw [hb.inv_mul_mem_e1KBar_iff S' hS' a.2 b.2 hwa hwb, hwa, hwb, hpt, hpt,
      e1PtW_eq_iff w w' hw hw']
  let F : e1NBar Z u m y x ⧸ (e1KBar Z u m y x).subgroupOf (e1NBar Z u m y x) → Fin 3 :=
    Quotient.lift (fun n => pt (n * caseC3Word Z u m y x 32 * (n : G ⧸ Z)⁻¹)) fun a b hab =>
      (hkey a b).mp (by simpa [Subgroup.mem_subgroupOf] using QuotientGroup.leftRel_apply.mp hab)
  have hF : Function.Injective F := by
    intro p q hpq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    refine QuotientGroup.eq.mpr ?_
    simpa [Subgroup.mem_subgroupOf] using (hkey a b).mpr hpq
  have hcard : (e1KBar Z u m y x).relIndex (e1NBar Z u m y x) ≤ 3 :=
    calc (e1KBar Z u m y x).relIndex (e1NBar Z u m y x) =
          Nat.card (e1NBar Z u m y x ⧸ (e1KBar Z u m y x).subgroupOf (e1NBar Z u m y x)) := rfl
      _ ≤ Nat.card (Fin 3) := Nat.card_le_card_of_injective F hF
      _ = 3 := by simp
  have hodd : ¬ 2 ∣ (e1KBar Z u m y x).relIndex (e1NBar Z u m y x) := by
    intro h2
    have h1 := Subgroup.relIndex_mul_relIndex _ _ _ hb.e1RBar_le_e1NBar e1NBar_le_e1M0
    have h3 := Subgroup.relIndex_dvd_of_le_left (e1NBar Z u m y x)
      (le_sup_left : e1RBar Z u m y x ≤ e1KBar Z u m y x)
    exact hb.not_two_dvd_relIndex S' hS' (dvd_trans (dvd_trans h2 h3) (Dvd.intro _ h1))
  rcases (by omega : (e1KBar Z u m y x).relIndex (e1NBar Z u m y x) = 1 ∨
      (e1KBar Z u m y x).relIndex (e1NBar Z u m y x) = 3) with h | h <;> rw [h]
  · exact one_dvd 3

theorem commute_pow_three_of_odd_typeD (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S)
    {g : G ⧸ Z} {k : ℕ} (hk : Odd k) (hgk : g ^ k = 1)
    (hgR : ∀ s ∈ e1RBar Z u m y x, g * s * g⁻¹ ∈ e1RBar Z u m y x) :
    ∀ s ∈ e1RBar Z u m y x, g ^ 3 * s = s * g ^ 3 := by
  have hgN := hb.mem_e1NBar_of_odd hk hgk hgR
  have := hb.normal_e1KBar S' hS'
  obtain ⟨j, hj⟩ := hb.relIndex_e1KBar_dvd_three htype S' hS'
  have hpow := ((e1KBar Z u m y x).subgroupOf (e1NBar Z u m y x)).pow_mem
    (Subgroup.pow_index_mem ((e1KBar Z u m y x).subgroupOf (e1NBar Z u m y x)) ⟨g, hgN⟩) j
  rw [← pow_mul, show ((e1KBar Z u m y x).subgroupOf (e1NBar Z u m y x)).index * j = 3 from
    hj.symm, Subgroup.mem_subgroupOf] at hpow
  have hg3 : g ^ 3 ∈ e1KBar Z u m y x := by simpa using hpow
  obtain ⟨-, hK⟩ := (hb.mem_e1KBar_iff S' hS').mp hg3
  have h32 : e1Sing 32 := by decide
  obtain ⟨hR, hrr, hr1, hrz⟩ := hb.sing_iff.mpr h32
  exact hb.commute_of_odd (k := k) hk (by rw [← pow_mul, mul_comm, pow_mul, hgk, one_pow])
    (pow_conj_mem_of_conj_mem hgR 3) hR hrr hr1 hrz (hK _ hR)

theorem conj_sing_of_odd_typeD (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S)
    {g : G ⧸ Z} {k : ℕ} (hk : Odd k) (hgk : g ^ k = 1)
    (hgR : ∀ s ∈ e1RBar Z u m y x, g * s * g⁻¹ ∈ e1RBar Z u m y x)
    (hgc : ¬ ∀ s ∈ e1RBar Z u m y x, g * s = s * g) {r : G ⧸ Z} (hr : r ∈ e1RBar Z u m y x)
    (hr1 : r ≠ 1) (hrz : r ≠ caseC3Word Z u m y x 40) :
    (g * r * g⁻¹ ≠ r ∧ g * r * g⁻¹ ≠ r * caseC3Word Z u m y x 40) ∧
      g ^ 3 * r * (g ^ 3)⁻¹ = r :=
  ⟨hb.conj_ne_of_odd_typeD htype hk hgk hgR hgc hr hr1 hrz, by
    rw [hb.commute_pow_three_of_odd_typeD htype S' hS' hk hgk hgR r hr, mul_inv_cancel_right]⟩

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
