module

public import Certificates.Certificate38704
public import CFSG.GF2Type.SmithTypeE.DMod.Act

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6 CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul)

theorem splitCheck_holds {p w : ℕ} (hp : p < 4096) (hp0 : p ≠ 0)
    (hpq : qf p = false) (hw : w < 4096) (hpw : bf p w = false) (hwq : qf w = true) :
    ∃ s < 4096, s ≠ 0 ∧ qf s = false ∧ bf p s = false ∧ bf w s = true :=
  Certificates.certificate38704 p w hp hp0 hpq hw hpw hwq

theorem split12 {p w : V12} (hp0 : p ≠ 0) (hqp : q12 p = 0)
    (hpw : B12 p w = 0) (hqw : q12 w = 1) :
    ∃ s : V12, q12 s = 0 ∧ B12 p s = 0 ∧ B12 w s = 1 := by
  have ha4 : enc12 p < 4096 := enc12_lt p
  have hap : dec12 (enc12 p) = p := dec12_enc12 p
  have hbw : dec12 (enc12 w) = w := dec12_enc12 w
  have ha0 : enc12 p ≠ 0 := fun h0 => hp0 (by rw [← hap, h0, dec12_zero])
  have hqa : qf (enc12 p) = false := qf_of_q12 (by rw [hap]; exact hqp)
  have hbf : bf (enc12 p) (enc12 w) = false := bf_of_B12 (by rw [hap, hbw]; exact hpw)
  have hqb : qf (enc12 w) = true := by
    have := q12_dec12 (enc12 w)
    rw [hbw, hqw] at this
    cases hq : qf (enc12 w)
    · rw [hq] at this; simp [bit] at this
    · rfl
  obtain ⟨s, -, -, hqs, hs1, hs2⟩ := splitCheck_holds ha4 ha0 hqa (enc12_lt w) hbf hqb
  refine ⟨dec12 s, ?_, ?_, ?_⟩
  · have := q12_dec12 s
    rw [hqs] at this
    simpa [bit] using this
  · rw [← hap, B12_dec12, hs1]
    simp [bit]
  · rw [← hbw, B12_dec12, hs2]
    simp [bit]

theorem siegelEquiv_eq_one_of_dependent {u w : V12} (h : TsPair u w) (hw : w = 0 ∨ w = u) :
    siegelEquiv u w = 1 := by
  refine LinearEquiv.ext fun x => ?_
  rw [siegelEquiv_apply h]
  show _ = x
  rcases hw with rfl | rfl
  · simp [B12_zero_right]
  · have key : ∀ c : ZMod 2, ∀ v : V12, c • v + c • v = 0 := fun c v => by
      rw [← two_smul (ZMod 2) (c • v)]
      simp [show (2 : ZMod 2) = 0 from rfl]
    rw [add_assoc, key, add_zero]

theorem siegelEquiv_eq_one_or_siegelK {u w : V12} (h : TsPair u w) :
    siegelEquiv u w = 1 ∨ ∃ k < 365211, siegelEquiv u w = siegelK k := by
  by_cases hu : u = 0
  · left
    subst hu
    rw [siegelEquiv_swap (tsPair_swap h)]
    exact siegelEquiv_eq_one_of_dependent (tsPair_swap h) (Or.inl rfl)
  by_cases hw : w = 0 ∨ w = u
  · exact Or.inl (siegelEquiv_eq_one_of_dependent h hw)
  · right
    push Not at hw
    have hline : IsTsLine (lineOfPair u w) := ⟨u, w, hu, hw.1, fun e => hw.2 e.symm, h, rfl⟩
    obtain ⟨k, hk, hks⟩ := exists_lineSet_eq hline
    obtain ⟨hu', hw', huw'⟩ := linePair_ne hk
    exact ⟨k, hk, siegelEquiv_eq_of_lineOfPair_eq h (tsPair_linePair hk) hu hw.1
      (fun e => hw.2 e.symm) hu' hw' huw' hks.symm⟩

theorem add_self_V12 (v : V12) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  simp [show (2 : ZMod 2) = 0 from rfl]

theorem eichler_mem_closure_siegelK {p w : V12}
    (hqp : q12 p = 0) (hqw : q12 w = 0) (hpw : B12 p w = 0) :
    eichler Q12 p w ∈ Subgroup.closure (Set.range fun k : Fin 365211 => siegelK k.val) := by
  have h : TsPair p w := ⟨hqp, hqw, hpw⟩
  rw [eichler_eq_siegelEquiv h]
  rcases siegelEquiv_eq_one_or_siegelK h with h1 | ⟨k, hk, h2⟩
  · rw [h1]
    exact Subgroup.one_mem _
  · rw [h2]
    exact Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩

theorem omega_le_closure_siegelK :
    omegaGroup Q12 Q12_polarBilin_nondegenerate ≤
      Subgroup.closure (Set.range fun k : Fin 365211 => siegelK k.val) := by
  refine (S4.omegaGroup_le_closure_pointRadical Q12_polarBilin_nondegenerate
    (by norm_num : 2 ≤ 6) (by rw [finrank_V12])).trans ?_
  rw [Subgroup.closure_le]
  rintro t ⟨p, hp0, hp, ht⟩
  obtain ⟨w, hpw, rfl⟩ := (mem_pointRadical_iff Q12_polarBilin_nondegenerate hp0 hp).mp ht
  have hp' : q12 p = 0 := (Q12_apply p).symm.trans hp
  have hpw' : B12 p w = 0 := (polar_Q12 p w).symm.trans hpw
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (q12 w) with hqw | hqw
  · exact eichler_mem_closure_siegelK hp' hqw hpw'
  · obtain ⟨s, hqs, hps, hws⟩ := split12 hp0 hp' hpw' hqw
    have hws' : q12 (w + s) = 0 := by
      rw [q12_add, hqw, hqs, hws]
      decide
    have hps' : B12 p (w + s) = 0 := by rw [B12_add_right, hpw', hps, add_zero]
    have e : eichler Q12 p w = eichler Q12 p s * eichler Q12 p (w + s) := by
      rw [eichler_mul ((polar_Q12 p s).trans hps) ((polar_Q12 p (w + s)).trans hps')]
      congr 1
      rw [← add_assoc, add_comm s w, add_assoc, add_self_V12, add_zero]
    rw [e]
    exact Subgroup.mul_mem _ (eichler_mem_closure_siegelK hp' hqs hps)
      (eichler_mem_closure_siegelK hp' hws' hps')

end CFSG.GF2Type.SmithTypeE.DMod
