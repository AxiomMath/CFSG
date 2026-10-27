module

public import CFSG.Goldschmidt.StatementsX
import CFSG.Goldschmidt.Steps.PropHSetup
public import CFSG.Goldschmidt.StatementsH

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.Assembly.Dichotomy

theorem corX_of (h37 : S_N37) (hX : S_lemmaX) : S_corX := by
  intro G _ _ _ hnab hIH S A U hAS hAab hAcl hUA hUmin hU8 hK1
  obtain ⟨hUel, -, -, -, -, -⟩ := N31 G hnab S A U hAS hAab hAcl hUA hUmin
  obtain ⟨hWodd, -, hNY, hCY, -, -, -, -, hTI⟩ :=
    h37 G hnab hIH S A U hAS hAab hAcl hUA hUmin hU8 hK1
  obtain ⟨hUS, hU1, hUcl, -⟩ := hUmin
  have hLX := hX G hnab hIH S A U hAS hAab hAcl hUA hUel hU1 hUcl (Or.inl hU8)
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU1
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have h2 : 2 ∣ Nat.card G :=
    orderOf_eq_prime (hUel.2 u u.2) hu1' ▸ orderOf_dvd_natCard (u : G)
  by_cases hW : oddCoreSpan U = ⊥
  ·
    have hUTI : fusionIsTI U := hTI.2 (by rw [hW]; exact Subgroup.commutator_bot_left U)
    refine ⟨_, hLX _ ?_ le_rfl
      ((isTI_iff_centralizer_le_normalizer S hUS hUcl hUel.1).1 hUTI)⟩
    intro htop
    have hUn : U.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U with h | h
    · exact hU1 h
    · obtain ⟨a, b, hab⟩ := hnab
      have hab' := hUel.1.is_comm.comm ⟨a, h ▸ Subgroup.mem_top a⟩ ⟨b, h ▸ Subgroup.mem_top b⟩
      exact hab (congrArg Subtype.val hab')
  ·
    refine ⟨_, hLX _ ?_ hNY hCY⟩
    intro htop
    have hWn : (oddCoreSpan U).Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oddCoreSpan U) with h | h
    · exact hW h
    · rw [h, Subgroup.card_top] at hWodd
      exact Nat.not_even_iff_odd.2 hWodd (even_iff_two_dvd.2 h2)

end CFSG.Goldschmidt
