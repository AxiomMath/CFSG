module

public import CFSG.GH74.Uniqueness.Section17Final
public import CFSG.GH74.Uniqueness.Section12Theorem6

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.zHull_dGrp_eq_bot (S : ZDSetup X Z M) {t : X} (htM : t ∉ M) :
    zHull Z (M ⊓ conjugate M t) = ⊥ := by
  have hempty : Z ∩ ((M ⊓ conjugate M t : Subgroup X) : Set X) = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_inf, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hyZ hyM hyt
    obtain ⟨β, -, huniq⟩ := S.prodDisc.existsUnique_fixed_point S.invariant hyZ
    have h1 := huniq M ⟨self_mem_omega M, (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr hyM⟩
    have hβ : conjugate M t ∈ omega M := ⟨t, rfl⟩
    have h2 := huniq (conjugate M t) ⟨hβ, (S.prodDisc.conjugate_eq_iff_mem hβ).mpr hyt⟩
    have h3 : conjugate M t = M := h2.trans h1.symm
    apply htM
    have := conjugate_eq_iff_mem_normalizer.mp h3
    rwa [S.prodDisc.normalizer_eq_self] at this
  rw [zHull, hempty, Subgroup.closure_empty]

theorem ZDSetup.false_of_stmts
    (S : ZDSetup X Z M)
    (hconf : ∀ _ : Ctx16 Z M, Nonempty (Conf16 Z M))
    (h163 : Lemma163Stmt Z M) (h166 : Cor166Stmt Z M) (h173 : Lemma173Stmt Z M)
    (h174 : Lemma174Stmt Z M) (h176 : Prop176Stmt Z M) : False := by
  obtain ⟨t, ht, htM⟩ := S.exists_mem_not_mem
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  by_cases hodd : Odd (Nat.card ↥(M ⊓ conjugate M t))
  · exact S.false_of_odd_card ht htM hodd
  have heven : Even (Nat.card ↥(M ⊓ conjugate M t)) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨c⟩ := hconf ⟨t, z, ht, htM, hz, hzM, heven⟩
  obtain ⟨n, i, e, hB⟩ := (h163 c).1
  have hcases := hB.bender.cases'
  rcases hcases with ⟨hi, -, -⟩ | ⟨hi, -, -⟩ | ⟨hi, -, -⟩
  ·
    subst hi
    obtain ⟨hsup, hinf⟩ := h176 c n e hB
    obtain ⟨-, -, -, -, hY⟩ := h166 c
    obtain ⟨⟨N, hND, hNn, hNodd, hk⟩, -⟩ := hY c.D (S.zHull_dGrp_eq_bot c.htM)
    exact S.false_of_oTwo_complement (D := c.D) (N := N) (u := c.u)
      inf_le_left hsup hinf hND hNn hNodd hk c.hu c.hu2
  · subst hi
    exact h173 c n e hB
  · subst hi
    exact h174 c n e hB

end CFSG.GH74.Uniqueness
