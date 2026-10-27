module

public import Certificates.Certificate24590
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsOuter

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open CFSG.ComponentClassification.J2Cover.Models

theorem bOut_mul_mem_S
    {s : Perm315} (hs : s ∈ S) : bOut * s * bOut ∈ S := by
  have h := bOut_conj_mem_S hs
  rwa [bOut_inv] at h

theorem mul_mem_TX_aux
    {x y : Perm315} (hx : x ∈ S ∨ x * bOut ∈ S) (hy : y ∈ S ∨ y * bOut ∈ S) :
    x * y ∈ S ∨ x * y * bOut ∈ S := by
  have hbb := bOut_mul_self
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (S.mul_mem hx hy)
  · refine Or.inr ?_
    rw [mul_assoc]
    exact S.mul_mem hx hy
  · refine Or.inr ?_
    have h := S.mul_mem hx (bOut_mul_mem_S hy)
    have e : x * bOut * (bOut * y * bOut) = x * (bOut * bOut) * y * bOut := by group
    rwa [e, hbb, mul_one] at h
  · refine Or.inl ?_
    have h := S.mul_mem hx (bOut_mul_mem_S hy)
    have e : x * bOut * (bOut * (y * bOut) * bOut) = x * (bOut * bOut) * y * (bOut * bOut) := by
      group
    simpa only [e, hbb, mul_one] using h

theorem inv_mem_TX_aux
    {x : Perm315} (hx : x ∈ S ∨ x * bOut ∈ S) : x⁻¹ ∈ S ∨ x⁻¹ * bOut ∈ S := by
  rcases hx with hx | hx
  · exact Or.inl (S.inv_mem hx)
  · refine Or.inr ?_
    have h := bOut_mul_mem_S (S.inv_mem hx)
    have e : bOut * (x * bOut)⁻¹ * bOut = x⁻¹ * bOut := by group
    rwa [e] at h

@[expose] noncomputable def TX :
    Subgroup Perm315 where
  carrier := {x | x ∈ S ∨ x * bOut ∈ S}
  mul_mem' := fun hx hy => mul_mem_TX_aux hx hy
  one_mem' := Or.inl S.one_mem
  inv_mem' := fun hx => inv_mem_TX_aux hx

theorem mem_TX_iff
    {x : Perm315} : x ∈ TX ↔ x ∈ S ∨ x * bOut ∈ S := Iff.rfl

theorem S_le_TX : S ≤ TX :=
  fun _ hx => Or.inl hx

theorem bOut_mem_TX :
    bOut ∈ TX :=
  Or.inr (by rw [bOut_mul_self]; exact S.one_mem)

theorem bOut_not_mem_S :
    bOut ∉ S := fun h => bOut_not_mem (S_le_P h)

theorem card_TX :
    Nat.card TX = 256 := by
  have hidx : (S.subgroupOf TX).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨bOut, bOut_mem_TX⟩, fun g => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    have hcancel : ∀ y : Perm315, y ∈ S → y * bOut ∈ S → False := fun y hy hyb =>
      bOut_not_mem_S (by simpa using S.mul_mem (S.inv_mem hy) hyb)
    rcases mem_TX_iff.1 g.2 with h | h
    · exact Or.inr ⟨h, fun h' => hcancel _ h h'⟩
    · exact Or.inl ⟨h, fun h' => hcancel _ h' h⟩
  have h1 := (S.subgroupOf TX).card_mul_index
  rw [hidx] at h1
  have h2 : Nat.card (S.subgroupOf TX) = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S_le_TX).toEquiv, card_S]
  omega

theorem exists_elt_TX
    {x : Perm315} (hx : x ∈ TX) :
    (∃ a, a < 128 ∧ x = (elt a : Perm315)) ∨ ∃ a, a < 128 ∧ x = (elt a : Perm315) * bOut := by
  rcases mem_TX_iff.1 hx with hx | hx
  · obtain ⟨a, ha, h⟩ := exists_elt hx
    exact Or.inl ⟨a, ha, h.symm⟩
  · obtain ⟨a, ha, h⟩ := exists_elt hx
    refine Or.inr ⟨a, ha, ?_⟩
    calc x = x * bOut * bOut⁻¹ := by group
      _ = (elt a : Perm315) * bOut := by rw [← h, bOut_inv]

theorem j2SylowCheck_parts :
    (∀ a, a < 128 → mulIdx a 4 = mulIdx 4 a) ∧
      ∀ a, a < 128 → (∀ d, d < 128 → mulIdx a d = mulIdx d a) → a = 0 ∨ a = 4 := by
  have hchk := Certificates.certificate24590
  simp only [j2SylowCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at hchk
  obtain ⟨⟨hcomm, hcen⟩, -⟩ := hchk
  refine ⟨hcomm, fun a ha hd => ?_⟩
  have htrue : ((List.range 128).all fun d => mulIdx a d == mulIdx d a) = true :=
    List.all_eq_true.2 fun d hd' => beq_iff_eq.2 (hd d (List.mem_range.1 hd'))
  rcases hcen a ha with (h1 | h1) | h1
  · rw [htrue] at h1
    exact absurd h1 (by decide)
  · exact Or.inl h1
  · exact Or.inr h1

theorem exists_noncomm : ∀ a < 128, ∃ d < 4, mulIdx d a ≠ mulIdx a (betaIdx d) := by
  decide

theorem betaIdx_four : betaIdx 4 = 4 := by decide

theorem mulIdx_five_five : mulIdx 5 5 = 32 := by decide

theorem mulIdx_thirtytwo_thirtytwo : mulIdx 32 32 = 4 := by decide

theorem coe_elt_mul (a : ℕ)
    {d : ℕ} (hd : d < 128) :
    (elt a : Perm315) * (elt d : Perm315) = (elt (mulIdx a d) : Perm315) := by
  rw [(mulIdx_spec (a := a) hd).2, Subgroup.coe_mul]

theorem bOut_mul_elt {a : ℕ}
    (ha : a < 128) : bOut * (elt a : Perm315) = (elt (betaIdx a) : Perm315) * bOut := by
  have h := bOut_conj_elt ha
  rw [← h]
  group

theorem elt_four_comm
    {y : Perm315} (hy : y ∈ TX) :
    y * (elt 4 : Perm315) = (elt 4 : Perm315) * y := by
  obtain ⟨hcomm, -⟩ := j2SylowCheck_parts
  have hS : ∀ d, d < 128 → (elt d : Perm315) * (elt 4 : Perm315) =
      (elt 4 : Perm315) * (elt d : Perm315) := fun d hd => by
    rw [coe_elt_mul d (d := 4) (by norm_num), coe_elt_mul 4 hd, hcomm d hd]
  rcases exists_elt_TX hy with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
  · exact hS d hd
  · have hb : bOut * (elt 4 : Perm315) = (elt 4 : Perm315) * bOut := by
      rw [bOut_mul_elt (a := 4) (by norm_num), betaIdx_four]
    calc (elt d : Perm315) * bOut * (elt 4 : Perm315)
        = (elt d : Perm315) * (bOut * (elt 4 : Perm315)) := by rw [mul_assoc]
      _ = (elt d : Perm315) * (elt 4 : Perm315) * bOut := by rw [hb, mul_assoc]
      _ = (elt 4 : Perm315) * (elt d : Perm315) * bOut := by rw [hS d hd]
      _ = (elt 4 : Perm315) * ((elt d : Perm315) * bOut) := by rw [mul_assoc]

theorem central_TX_iff
    {x : Perm315} (hx : x ∈ TX) :
    (∀ y ∈ TX, y * x = x * y) ↔ x = 1 ∨ x = (elt 4 : Perm315) := by
  obtain ⟨-, hcen⟩ := j2SylowCheck_parts
  constructor
  · intro hc
    rcases exists_elt_TX hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · have h4 : a = 0 ∨ a = 4 := by
        refine hcen a ha fun d hd => ?_
        have h1 := hc (elt d : Perm315) (S_le_TX (elt d).2)
        rw [coe_elt_mul d ha, coe_elt_mul a hd] at h1
        have h2 : elt (mulIdx d a) = elt (mulIdx a d) := Subtype.ext h1
        exact (elt_injective (mulIdx_spec (a := a) hd).1 (mulIdx_spec (a := d) ha).1 h2.symm)
      rcases h4 with rfl | rfl
      · exact Or.inl (by rw [elt_zero]; rfl)
      · exact Or.inr rfl
    · exfalso
      obtain ⟨d, hd, hne⟩ := exists_noncomm a ha
      have hd' : d < 128 := by omega
      have h1 := hc (elt d : Perm315) (S_le_TX (elt d).2)
      have e1 : (elt d : Perm315) * ((elt a : Perm315) * bOut) =
          (elt (mulIdx d a) : Perm315) * bOut := by
        rw [← coe_elt_mul d ha, mul_assoc]
      have e2 : (elt a : Perm315) * bOut * (elt d : Perm315) =
          (elt (mulIdx a (betaIdx d)) : Perm315) * bOut := by
        rw [mul_assoc, bOut_mul_elt hd', ← coe_elt_mul a (betaIdx_lt hd'), mul_assoc]
      rw [e1, e2] at h1
      have h2 : elt (mulIdx d a) = elt (mulIdx a (betaIdx d)) :=
        Subtype.ext (mul_right_cancel h1)
      exact hne (elt_injective (mulIdx_spec (a := d) ha).1
        (mulIdx_spec (a := a) (betaIdx_lt hd')).1 h2)
  · rintro (rfl | rfl) y hy
    · rw [mul_one, one_mul]
    · exact elt_four_comm hy

end CFSG.EvenSporadicStandard.Fin76b.J2
