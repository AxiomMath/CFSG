module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldFrame

public section

namespace CFSG.OddStandard.ChengHeld.M1b

open CFSG.OddStandard.ChengHeldData Subgroup
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

structure ChCoverParts : Prop where
  frame4 : frame4OK = true
  act4 : act4OK = true
  frame2 : frame2OK = true
  act2 : act2OK = true
  gen : genT0OK = true
  twist : twistOK = true
  kappaFG : kappaFGOK = true
  twist2 : twist2OK = true
  kappa2FG : kappa2FGOK = true
  comm : commOK = true
  gAct : gActOK = true

theorem chCoverParts (h : chCoverOK = true) : ChCoverParts := by
  simp only [chCoverOK, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem frM_lt (α i : ℕ) : (frM α i).1 < 64 := by
  unfold frM
  split <;> (try split_ifs) <;> norm_num

theorem closure_frTg
    (h : genT0OK = true) : closure (wordSet frTg) = T0 := by
  simp only [genT0OK, Bool.and_eq_true, beq_iff_eq] at h
  have hen := enumerates_wordClosure h.1
  have hcard : Nat.card (closure (wordSet frTg)) = 64 := by
    rw [hen.card, Array.length_toList, h.2]
  have hle : closure (wordSet frTg) ≤ T0 := by
    rw [closure_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [frTg, List.mem_map] at hw
    obtain ⟨k, hk, rfl⟩ := hw
    simp only [frIdx, List.mem_cons, List.mem_nil_iff, or_false] at hk
    exact tg_mem_T0 k (by omega)
  exact eq_of_le_of_card_ge hle (by rw [hcard, card_T0])

theorem relsOK_of_frame4 (hC : frame4OK = true) {α : ℕ} (hα : α ≤ 1) :
    relsOK (eqKM (kapOf α)) (frM α) (frame4Rels α) = true := by
  rw [frame4OK, List.all_eq_true] at hC
  exact hC α (by interval_cases α <;> simp)

section Frames

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem frame4_nfM (hC : frame4OK = true) (h : IsQSetting q l) {α : ℕ} (hα : α ≤ 1)
    (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ inK (kapOf α) i j) :
    Frame4 α (nfM l (frM α 0)) (nfM l (frM α 1)) (nfM l (frM α 2)) (nfM l (frM α 3))
      (nfM l (frM α 4)) (nfM l (frM α 5)) (nfM l (frM α 6)) :=
  frame4_of_rels α (fun i => nfM l (frM α i))
    (eval_eq_of_relsOK h (eqf := eqKM (kapOf α)) (fun _ _ hx hy => eqKM_iff h hκ hx hy)
      (frM_lt α) (relsOK_of_frame4 hC hα))

theorem act_nfM (hC : act4OK = true) (h : IsQSetting q l)
    {α : ℕ} (hα : α ≤ 1) (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ inK (kapOf α) i j)
    {β : E ≃* E} {k : ℕ} (hk : k < 3)
    (hβ : ∀ w, β (l (cv w)) = l (cv (substWord (aut (k + 1)) w))) :
    ∀ e ∈ actRels α k, β (nfM l (frM α e.1)) = evalE (fun i => nfM l (frM α i)) e.2 := by
  have hr : actOK (eqKM (kapOf α)) (frM α) (k + 1) (actRels α k) = true := by
    rw [act4OK, List.all_eq_true] at hC
    have := hC α (by interval_cases α <;> simp)
    rw [List.all_eq_true] at this
    exact this k (by interval_cases k <;> simp)
  exact act_of_actOK h (fun _ _ hx hy => eqKM_iff h hκ hx hy) (frM_lt α) (by omega) hβ hr

theorem frame2_nfM (hC : frame2OK = true) (h : IsQSetting q l)
    (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ j.val % 2 = 0) :
    Frame2 (nfM l (frM 2 0)) (nfM l (frM 2 1)) (nfM l (frM 2 2)) (nfM l (frM 2 3))
      (nfM l (frM 2 4)) (nfM l (frM 2 5)) (nfM l (frM 2 6)) :=
  frame2_of_rels (fun i => nfM l (frM 2 i))
    (eval_eq_of_relsOK h (eqf := eqN2) (fun _ _ hx hy => eqN2_iff h hκ hx hy) (frM_lt 2) hC)

theorem act2_nfM (hC : act2OK = true) (h : IsQSetting q l)
    (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ j.val % 2 = 0) {β : E ≃* E} {k : ℕ} (hk : k < 3)
    (hβ : ∀ w, β (l (cv w)) = l (cv (substWord (aut (k + 1)) w))) :
    ∀ e ∈ act2Rels k, β (nfM l (frM 2 e.1)) = evalE (fun i => nfM l (frM 2 i)) e.2 := by
  have hr : actOK eqN2 (frM 2) (k + 1) (act2Rels k) = true := by
    rw [act2OK, List.all_eq_true] at hC
    exact hC k (by interval_cases k <;> simp)
  exact act_of_actOK h (fun _ _ hx hy => eqN2_iff h hκ hx hy) (frM_lt 2) (by omega) hβ hr

end Frames

theorem pow_of_card_two {K : Type*} [Group K] (h2 : Nat.card K = 2) (x : K) (n : ℕ) :
    x ^ n = if n % 2 = 0 then 1 else x := by
  have hx : x ^ 2 = 1 := by
    have := pow_card_eq_one' (G := K) (x := x)
    rwa [h2] at this
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp [pow_mul, hx]
  · simp [pow_succ, pow_mul, hx]

section Ker2

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem exists_kappa2 (h : IsQSetting q l) (h2 : Nat.card ↥q.ker = 2) :
    ∃ ab ∈ kap2Gens, ∀ i j : ZMod 4, zz l i j = 1 ↔ inN2 ab (i, j) = true := by
  classical
  have : Finite ↥q.ker := Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
  have hmem : ∀ i j : ZMod 4, zz l i j ∈ q.ker := zz_mem_ker h
  have hzz : ∀ x : ↥q.ker, ∃ i j : ZMod 4, (x : E) = zz l i j := by
    intro x
    obtain ⟨i, j, hij⟩ := (mem_ker_iff h.ql h.lsurj h.three).1 x.2
    exact ⟨i, j, by rw [hij, zz_ofNat]⟩
  set u : ↥q.ker := ⟨zz l 1 0, hmem 1 0⟩ with hu_def
  set v : ↥q.ker := ⟨zz l 0 1, hmem 0 1⟩ with hv_def
  have hval : ∀ i j : ZMod 4, (⟨zz l i j, hmem i j⟩ : ↥q.ker) = u ^ i.val * v ^ j.val := by
    intro i j
    have e1 : zz l i j = zz l 1 0 ^ i.val * zz l 0 1 ^ j.val := by
      rw [zz_pow, zz_pow, zz_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      simp only [mul_one, mul_zero, add_zero, zero_add]
    exact Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_pow]; exact e1)
  obtain ⟨g, hg1, hg⟩ : ∃ g : ↥q.ker, g ≠ 1 ∧ ∀ x : ↥q.ker, x = 1 ∨ x = g := by
    obtain ⟨g, hg, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥q.ker)).1 h2
    exact ⟨g, hg, fun x => by by_cases hx : x = 1; exact Or.inl hx; exact Or.inr (huniq x hx)⟩
  have hiff : ∀ i j : ZMod 4, zz l i j = 1 ↔ u ^ i.val * v ^ j.val = 1 := by
    intro i j
    rw [← hval i j, Subtype.ext_iff]
    rfl
  have hu := hg u
  have hv := hg v
  have hp := pow_of_card_two h2 g
  have hne : ¬ (u = 1 ∧ v = 1) := by
    rintro ⟨hu1, hv1⟩
    obtain ⟨x, hx1⟩ : ∃ x : ↥q.ker, x ≠ 1 := ⟨g, hg1⟩
    obtain ⟨i, j, hij⟩ := hzz x
    apply hx1
    have := (hiff i j).2 (by rw [hu1, hv1]; simp)
    exact Subtype.ext (by rw [hij]; exact this)
  rcases hu with hu1 | hug <;> rcases hv with hv1 | hvg
  · exact absurd ⟨hu1, hv1⟩ hne
  · refine ⟨(0, 1), by simp [kap2Gens], fun i j => ?_⟩
    rw [hiff, hu1, hvg, hp, one_pow, one_mul]
    simp only [inN2, zero_mul, one_mul, zero_add, beq_iff_eq]
    split_ifs with hj
    · exact ⟨fun _ => hj, fun _ => rfl⟩
    · exact ⟨fun h1 => absurd h1 hg1, fun h1 => absurd h1 hj⟩
  · refine ⟨(1, 0), by simp [kap2Gens], fun i j => ?_⟩
    rw [hiff, hug, hv1, hp, one_pow, mul_one]
    simp only [inN2, zero_mul, one_mul, add_zero, beq_iff_eq]
    split_ifs with hi
    · exact ⟨fun _ => hi, fun _ => rfl⟩
    · exact ⟨fun h1 => absurd h1 hg1, fun h1 => absurd h1 hi⟩
  · refine ⟨(1, 1), by simp [kap2Gens], fun i j => ?_⟩
    rw [hiff, hug, hvg, ← pow_add, hp]
    simp only [inN2, one_mul, beq_iff_eq, ZMod.val_add]
    have h4 : ((i.val + j.val) % 4) % 2 = (i.val + j.val) % 2 := by omega
    rw [h4]
    split_ifs with hij
    · exact ⟨fun _ => hij, fun _ => rfl⟩
    · exact ⟨fun h1 => absurd h1 hg1, fun h1 => absurd h1 hij⟩

theorem exists_twist
    (hE : commutator E = ⊤) (h : IsQSetting q l) {i : ℕ} (hi : i < 36) :
    ∃ l' : Cover →* E, IsQSetting ((MulAut.conj (repPerm i)⁻¹).toMonoidHom.comp q) l' ∧
      ∀ a b : ZMod 4, zz l' a b = zz l (mact i (a, b)).1 (mact i (a, b)).2 := by
  obtain ⟨α, hα, hσα⟩ := exists_alpha hi
  have hρ : (repPerm i)⁻¹ ∈ R := R.inv_mem (repPerm_mem i)
  obtain ⟨hqS', hsurj', hker'⟩ := conj_jq h.qS h.qsurj hρ
  set q' : E →* Equiv.Perm (Fin 42) := (MulAut.conj (repPerm i)⁻¹).toMonoidHom.comp q with hq'
  have hkerc : q'.ker ≤ center E := by rw [hker']; exact h.ker_le
  obtain ⟨l'', hl'', hls''⟩ := exists_lam hE q' hqS' hsurj' hkerc
  have hql : q'.comp (l.comp α) = sigma := by
    refine MonoidHom.ext fun c => ?_
    simp only [hq', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      h.q_l, hσα]
    group
  have heq : l'' = l.comp α :=
    hom_ext_of_central commutator_cover q' hkerc (by rw [hl'', hql])
  subst heq
  refine ⟨l.comp α, ⟨hqS', hsurj', hker'.trans h.ker, fun e he => h.three e (by rwa [← hker']),
    hl'', hls''⟩, fun a b => ?_⟩
  have h1 : (l.comp α) z₁ = zz l (alphaEntry i 64).2.1 (alphaEntry i 64).2.2.1 := by
    have := alphaZ_spec (j := 0) hi (by norm_num)
    show l (α (cv (zGen 0))) = _
    rw [hα, this, l_zOf h]
  have h2 : (l.comp α) z₂ = zz l (alphaEntry i 65).2.1 (alphaEntry i 65).2.2.1 := by
    have := alphaZ_spec (j := 1) hi (by norm_num)
    show l (α (cv (zGen 1))) = _
    rw [hα, this, l_zOf h]
  have hab : zz (l.comp α) a b = (l.comp α) z₁ ^ a.val * (l.comp α) z₂ ^ b.val := by
    rw [← zz_ofNat, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [hab, h1, h2, zz_pow, zz_pow, zz_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rfl

theorem kapOf_of_mem_kapStd {κ : ZMod 4 × ZMod 4} (h : κ ∈ kapStd) :
    ∃ α ≤ 1, kapOf α = κ := by
  simp only [kapStd, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, by simp [kapOf]⟩

theorem mem_allPairs : ∀ x : ZMod 4 × ZMod 4, x ∈ allPairs := by decide

theorem std_of_FG
    (hC : ChCoverParts) (h : IsQSetting q l)
    (hc : IsCyclic ↥q.ker) (h4 : Nat.card ↥q.ker = 4) {β : E ≃* E} {j : ℕ} (hj : j = 1 ∨ j = 2)
    (hβ : ∀ w, β (l (cv w)) = l (cv (substWord (aut j) w))) :
    ∃ α ≤ 1, ∀ a b : ZMod 4, zz l a b = 1 ↔ inK (kapOf α) a b := by
  obtain ⟨κ, hκ, hκz⟩ := exists_kappa h hc h4
  have hj36 : j < 36 := by omega
  have hl := liftsK_of h hκz hj36 hβ
  have hFG := hC.kappaFG
  rw [kappaFGOK, List.all_eq_true] at hFG
  have h1 := hFG κ (by rw [kGensC_eq]; exact hκ)
  have hmem : κ ∈ kapStd := by
    have h2 : (liftsK κ 1 || liftsK κ 2) = true := by rcases hj with rfl | rfl <;> simp [hl]
    simpa [h2] using h1
  obtain ⟨α, hα, rfl⟩ := kapOf_of_mem_kapStd hmem
  exact ⟨α, hα, hκz⟩

theorem std_after_twist
    (hC : ChCoverParts) (hE : commutator E = ⊤) (h : IsQSetting q l) (hc : IsCyclic ↥q.ker)
    (h4 : Nat.card ↥q.ker = 4) :
    ∃ i ∈ ([0, 4, 5] : List ℕ), ∃ l' : Cover →* E,
      IsQSetting ((MulAut.conj (repPerm i)⁻¹).toMonoidHom.comp q) l' ∧
        ∃ α ≤ 1, ∀ a b : ZMod 4, zz l' a b = 1 ↔ inK (kapOf α) a b := by
  obtain ⟨κ, hκ, hκz⟩ := exists_kappa h hc h4
  have ht := hC.twist
  rw [twistOK, List.all_eq_true] at ht
  obtain ⟨i, hi, hany⟩ := List.any_eq_true.1 (ht κ (by rw [kGensC_eq]; exact hκ))
  obtain ⟨κs, hκs, hall⟩ := List.any_eq_true.1 hany
  have hi36 : i < 36 := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
  obtain ⟨l', hl', hzz⟩ := exists_twist hE h hi36
  obtain ⟨α, hα, hακ⟩ := kapOf_of_mem_kapStd hκs
  refine ⟨i, hi, l', hl', α, hα, fun a b => ?_⟩
  rw [hzz, hκz, hακ]
  have := of_decide_eq_true (List.all_eq_true.1 hall (a, b) (mem_allPairs _))
  exact this

theorem inN2_zero_one (x : ZMod 4 × ZMod 4) : inN2 (0, 1) x = true ↔ x.2.val % 2 = 0 := by
  simp [inN2]

theorem mem_kap2Gens_zero_one : ((0 : ZMod 4), (1 : ZMod 4)) ∈ kap2Gens := by simp [kap2Gens]

theorem std2_of_FG
    (hC : ChCoverParts) (h : IsQSetting q l) (h2 : Nat.card ↥q.ker = 2) {β : E ≃* E} {j : ℕ}
    (hj : j = 1 ∨ j = 2) (hβ : ∀ w, β (l (cv w)) = l (cv (substWord (aut j) w))) :
    ∀ a b : ZMod 4, zz l a b = 1 ↔ b.val % 2 = 0 := by
  obtain ⟨ab, hab, hz⟩ := exists_kappa2 h h2
  have hj36 : j < 36 := by omega
  have hl : lifts2 ab j = true := by
    unfold lifts2
    rw [List.all_eq_true]
    intro x _
    by_cases hx : inN2 ab x = true
    · have h1 : zz l x.1 x.2 = 1 := (hz x.1 x.2).2 hx
      have h3 := beta_zz h hj36 hβ x.1 x.2
      rw [h1, map_one] at h3
      have h4 := (hz (mact j x).1 (mact j x).2).1 h3.symm
      simp [h4]
    · simp [hx]
  have hFG := hC.kappa2FG
  rw [kappa2FGOK, List.all_eq_true] at hFG
  have h1 := hFG ab hab
  have hab0 : ab = (0, 1) := by
    have h2' : (lifts2 ab 1 || lifts2 ab 2) = true := by rcases hj with rfl | rfl <;> simp [hl]
    simpa [h2'] using h1
  subst hab0
  intro a b
  rw [hz, inN2_zero_one]

theorem std2_after_twist
    (hC : ChCoverParts) (hE : commutator E = ⊤) (h : IsQSetting q l)
    (h2 : Nat.card ↥q.ker = 2) :
    ∃ i ∈ ([0, 4, 5] : List ℕ), ∃ l' : Cover →* E,
      IsQSetting ((MulAut.conj (repPerm i)⁻¹).toMonoidHom.comp q) l' ∧
        ∀ a b : ZMod 4, zz l' a b = 1 ↔ b.val % 2 = 0 := by
  obtain ⟨ab, hab, hz⟩ := exists_kappa2 h h2
  have ht := hC.twist2
  rw [twist2OK, List.all_eq_true] at ht
  obtain ⟨i, hi, hall⟩ := List.any_eq_true.1 (ht ab hab)
  have hi36 : i < 36 := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi; omega
  obtain ⟨l', hl', hzz⟩ := exists_twist hE h hi36
  refine ⟨i, hi, l', hl', fun a b => ?_⟩
  have h6 := List.all_eq_true.1 hall (a, b) (mem_allPairs _)
  simp only [beq_iff_eq] at h6
  rw [hzz, hz, Prod.mk.eta, h6]
  exact inN2_zero_one (a, b)

theorem betaRep_of_decomp
    (h : IsQSetting q l) {β : E ≃* E} {t i : ℕ} (ht : t < 64) (hi : i < 36)
    (hβ : ∀ e, q (β e) = (wordPerm (tg t) * repPerm i) * q e * (wordPerm (tg t) * repPerm i)⁻¹) :
    ∀ w, (nf l t 0 0)⁻¹ * β (l (cv w)) * nf l t 0 0 = l (cv (substWord (aut i) w)) := by
  intro w
  set β' : E ≃* E := β.trans (MulAut.conj (nf l t 0 0)⁻¹) with hβ'
  have hβ'q : ∀ e, q (β' e) = repPerm i * q e * (repPerm i)⁻¹ := by
    intro e
    have e1 : β' e = (nf l t 0 0)⁻¹ * β e * nf l t 0 0 := by
      rw [hβ', MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
    rw [e1, map_mul, map_mul, map_inv, hβ, q_nf h ht]
    group
  have := beta_cv_of h.ker_le h.ql hβ'q (abPerm_uA hi) (abPerm_uB hi) w
  simp only [hβ', MulEquiv.trans_apply, MulAut.conj_apply, inv_inv] at this
  exact this

end Ker2

end CFSG.OddStandard.ChengHeld.M1b
