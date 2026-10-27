module

public import CFSG.CGT.Timmesfeld75.Sec66Cover
public import CFSG.CGT.Timmesfeld75.JLemmaGen
public import CFSG.CGT.Timmesfeld75.PlaneCover
public import CFSG.CGT.Timmesfeld75.Sec66J

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {U Tb P : Subgroup G} {y y' : G} {q : ℕ}

theorem Sec66Cfg.jlemma [IsSimpleGroup G] (h215 : Lemma215Stmt) (h26 : Lemma26Input)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (c : Sec66Cfg U Tb P y y' q) :
    IsSimpleGroup (jQuot ↥(U ⊔ Tb ⊔ P)) ∧
      Lemma26Hyp (jQuot ↥(U ⊔ Tb ⊔ P))
        ((U.subgroupOf (U ⊔ Tb ⊔ P)).map (jMap ↥(U ⊔ Tb ⊔ P))) ∧
      Lemma26Concl (jQuot ↥(U ⊔ Tb ⊔ P))
        ((U.subgroupOf (U ⊔ Tb ⊔ P)).map (jMap ↥(U ⊔ Tb ⊔ P))) ∧
      ∀ w : ↥(U ⊔ Tb ⊔ P), w ∈ (jMap ↥(U ⊔ Tb ⊔ P)).ker → ∀ i,
        conjSubgroup (w : G) (sec66Fam U Tb P i) = sec66Fam U Tb P i := by
  obtain ⟨hQab, hQn⟩ := c.Q_spec hnab
  obtain ⟨s, hs, hsB⟩ := c.sec3_B.conj
  obtain ⟨s', hs', hsP⟩ := c.sec3_P.conj
  have hsJ : s ∈ U ⊔ Tb ⊔ P := (le_sup_left : U ⊔ Tb ≤ U ⊔ Tb ⊔ P) hs
  have hs'J : s' ∈ U ⊔ Tb ⊔ P :=
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right : U ⊔ P ≤ U ⊔ Tb ⊔ P) hs'
  have hRconj : ∀ i, ∃ g ∈ U ⊔ Tb ⊔ P, sec66Fam U Tb P i = conjSubgroup g U := by
    intro i
    fin_cases i
    · exact ⟨1, (U ⊔ Tb ⊔ P).one_mem, (conjSubgroup_one U).symm⟩
    · exact ⟨s, hsJ, hsB⟩
    · exact ⟨s', hs'J, hsP⟩
  have hQR : sec66Q U Tb P ≤ U ⊔ Tb ⊔ P := by
    refine iSup_le fun j => (iInf_le _ 0).trans ((normIn_le _ _).trans ?_)
    exact (le_iSup (sec66Fam U Tb P) j).trans (iSup_sec66Fam U Tb P).le
  have hq : 2 * Nat.card ↥(⨅ i, normIn U (sec66Fam U Tb P i)) < Nat.card ↥U := by
    rw [famF_zero, c.cardU]
    have h1 := c.cardA
    have hq2 := c.hq
    have h3 : q * 4 ≤ q * q ^ 2 := Nat.mul_le_mul_left q c.four_le
    have h4 : q ^ 3 = q * q ^ 2 := by ring
    omega
  obtain ⟨hsimple, -, hhyp, hconcl, -, hker⟩ := jLemma35_inf h215 h26 hind c.wc c.glob (r := 3)
    (Ts := sec66Fam U Tb P) ⟨0, rfl⟩ (iSup_sec66Fam U Tb P) hRconj hQR
    (isPGroup_two_of_isElemAbelian hQab) hQn c.commutator_ne_bot hq
  exact ⟨hsimple, hhyp, hconcl, hker⟩

theorem Sec66Cfg.trace_facts [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (c : Sec66Cfg U Tb P y y' q) : ∃ a : ℕ, 2 ≤ a ∧ a ≤ q ∧
      Nat.card ↥(sec66Q U Tb P) ≤ a ^ 3 ∧
      ∀ R ∈ sec66T U Tb P, Nat.card ↥(R ⊓ sec66Q U Tb P) = a := by
  obtain ⟨hQab, hQn⟩ := c.Q_spec hnab
  have htr := sec66T_trace_card hQn
  have hcard := sec66Q_card_le hQab (sec66T_B c.sec3_B.conj) (sec66T_P c.sec3_P.conj) htr
  have hAQ : normIn U Tb ⊓ normIn U P ≤ U ⊓ sec66Q U Tb P := by
    rw [← famF_zero]
    refine le_inf ((iInf_le (fun i => normIn U (sec66Fam U Tb P i)) 0).trans
      (normIn_le U (sec66Fam U Tb P 0))) ?_
    rw [sec66Q_eq]
    exact le_sup_left.trans le_sup_left
  have ha2 : 2 ≤ Nat.card ↥(U ⊓ sec66Q U Tb P) := by
    have h1 : 1 < Nat.card ↥(normIn U Tb ⊓ normIn U P) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 c.A_ne_bot
    have := Subgroup.card_le_of_le hAQ
    omega
  exact ⟨_, ha2, (Subgroup.card_le_of_le (c.inf_Q_le hQab)).trans c.cardA, hcard, htr⟩

theorem Sec66Cfg.ncard_T [IsSimpleGroup G] (h215 : Lemma215Stmt) (h26 : Lemma26Input)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (c : Sec66Cfg U Tb P y y' q)
    (hA6 : ¬ Nonempty (jQuot ↥(U ⊔ Tb ⊔ P) ⧸ Subgroup.center (jQuot ↥(U ⊔ Tb ⊔ P)) ≃*
      alternatingGroup (Fin 6))) : q ^ 2 + q + 1 ≤ (sec66T U Tb P).ncard := by
  obtain ⟨-, -, hconcl, -⟩ := c.jlemma h215 h26 hnab hind
  obtain ⟨s, hs, hsB⟩ := c.sec3_B.conj
  obtain ⟨s', hs', hsP⟩ := c.sec3_P.conj
  have hUJ : U ≤ U ⊔ Tb ⊔ P := le_sup_left.trans le_sup_left
  have hsJ : s ∈ U ⊔ Tb ⊔ P := (le_sup_left : U ⊔ Tb ≤ U ⊔ Tb ⊔ P) hs
  have D := PlaneData.of_two_trans (J := U ⊔ Tb ⊔ P) (U := U) (V := Tb) (q := q) hUJ
    (fun {a₁ a₂ b₁ b₂} ha₁ ha₂ hb₁ hb₂ hne₁ hne₂ =>
      exists_mem_conj_of_jMap_sub c.wc hUJ hconcl hA6 ha₁ ha₂ hb₁ hb₂ hne₁ hne₂)
    hsJ hsB c.neUB (by rw [c.cardU, c.cardNB]; ring)
  exact D.card_ge (by have := c.hq; omega) (sec66T_U U Tb P) (sec66T_B ⟨s, hs, hsB⟩)
    (sec66T_P ⟨s', hs', hsP⟩) c.neUB c.not_le_sup

theorem Sec66Cfg.exists_conj_mem [IsSimpleGroup G] (h215 : Lemma215Stmt) (h26 : Lemma26Input)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (c : Sec66Cfg U Tb P y y' q)
    (hA6 : ¬ Nonempty (jQuot ↥(U ⊔ Tb ⊔ P) ⧸ Subgroup.center (jQuot ↥(U ⊔ Tb ⊔ P)) ≃*
      alternatingGroup (Fin 6))) : ∃ j ∈ U ⊔ Tb ⊔ P, y * y' ∈ conjSubgroup j U := by
  obtain ⟨hQab, hQn⟩ := c.Q_spec hnab
  have hpts := c.ncard_T h215 h26 hnab hind hA6
  obtain ⟨a, ha2, haq, hcard, htr⟩ := c.trace_facts hnab
  have hTI : ∀ R ∈ sec66T U Tb P, ∀ S ∈ sec66T U Tb P, R ≠ S → R ⊓ S = ⊥ := by
    rintro R ⟨j₁, -, hR⟩ S ⟨j₂, -, hS⟩ hne
    exact inf_eq_bot_of_conj_conj c.wc hR hS hne
  have hpts' : a ^ 2 + a + 1 ≤ (sec66T U Tb P).ncard := by
    have := Nat.pow_le_pow_left haq 2
    omega
  obtain ⟨R, ⟨j, hj, rfl⟩, hzR⟩ := exists_mem_of_traces ha2 hTI hcard htr hpts'
    (y * y') ((sec66Q U Tb P).mul_mem c.y_mem_Q c.y'_mem_Q) c.mul_ne_one
  exact ⟨j, hj, hzR⟩

end CFSG.CGT.Timmesfeld75
