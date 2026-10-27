module

public import CFSG.Certificates.Kernel.M3BSyl.Checks
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBSylFact

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.M3BS

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
open CFSG.KC.M3BF (vz GoodRow Ins slpNodes slpWT)
open Timmesfeld.M3B (WT sigW tMats)

section PC

variable {G : Type*} [Group G]

@[expose] def clo (Us : List G) : Subgroup G := Subgroup.closure {x | x ∈ Us}

theorem nfL_mem_clo : ∀ (Us : List G) (es : List ℕ), nfL Us es ∈ clo Us
  | [], _ => by
    simp only [nfL, List.zipWith_nil_left, List.prod_nil]
    exact one_mem _
  | _ :: _, [] => by
    simp only [nfL, List.zipWith_nil_right, List.prod_nil]
    exact one_mem _
  | u :: Us, e :: es => by
    simp only [nfL, List.zipWith_cons_cons, List.prod_cons]
    have hu : u ∈ clo (u :: Us) := Subgroup.subset_closure (by exact List.mem_cons_self)
    refine mul_mem (pow_mem hu e) ?_
    exact Subgroup.closure_mono (fun x hx => List.mem_cons_of_mem _ hx) (nfL_mem_clo Us es)

theorem nfL_drop : ∀ (k : ℕ) (Us : List G) (es : List ℕ), (∀ e ∈ es.take k, e = 0) →
    nfL Us es = nfL (Us.drop k) (es.drop k)
  | 0, _, _, _ => rfl
  | _ + 1, [], _, _ => by simp [nfL]
  | _ + 1, _ :: _, [], _ => by simp [nfL]
  | k + 1, u :: Us, e :: es, h => by
    simp only [List.take_succ_cons, List.mem_cons, forall_eq_or_imp] at h
    have ih := nfL_drop k Us es h.2
    simp only [nfL] at ih ⊢
    rw [List.zipWith_cons_cons, List.prod_cons, h.1, pow_zero, one_mul, List.drop_succ_cons,
      List.drop_succ_cons, ih]

variable [Finite G]

theorem pc_nf : ∀ Us : List G,
    (∀ i (hi : i < Us.length), Us[i] ^ 3 ∈ clo (Us.drop (i + 1)) ∧
      ∀ w ∈ Us.drop (i + 1), Us[i]⁻¹ * w * Us[i] ∈ clo (Us.drop (i + 1))) →
    ∀ x ∈ clo Us, ∃ es : List ℕ, es.length = Us.length ∧ (∀ e ∈ es, e < 3) ∧ x = nfL Us es
  | [], _, x, hx => by
    have h0 : clo ([] : List G) = ⊥ := by simp [clo]
    rw [h0, Subgroup.mem_bot] at hx
    exact ⟨[], rfl, by simp, by simp [hx, nfL]⟩
  | u :: Us, h, x, hx => by
    have ih := pc_nf Us fun i hi => h (i + 1) (by simpa using hi)
    have h3 : u ^ 3 ∈ clo Us := (h 0 (by simp)).1
    have hc : ∀ w ∈ Us, u⁻¹ * w * u ∈ clo Us := (h 0 (by simp)).2
    have hn : ∀ y ∈ clo Us, u⁻¹ * y * u ∈ clo Us := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy => exact hc y hy
      | one => simp
      | mul a b _ _ ha hb =>
        have e : u⁻¹ * (a * b) * u = (u⁻¹ * a * u) * (u⁻¹ * b * u) := by group
        rw [e]
        exact mul_mem ha hb
      | inv a _ ha =>
        have e : u⁻¹ * a⁻¹ * u = (u⁻¹ * a * u)⁻¹ := by group
        rw [e]
        exact inv_mem ha
    let T : Set G := {z | ∃ a < 3, ∃ y ∈ clo Us, z = u ^ a * y}
    have hT : ∀ z ∈ T, ∀ g ∈ u :: Us, z * g ∈ T := by
      rintro z ⟨a, ha, y, hy, rfl⟩ g hg
      rcases List.mem_cons.1 hg with heq | hg
      · rw [heq]
        have e : u ^ a * y * u = u ^ (a + 1) * (u⁻¹ * y * u) := by rw [pow_succ]; group
        rcases (by omega : a + 1 < 3 ∨ a = 2) with h' | rfl
        · exact ⟨a + 1, h', _, hn y hy, e⟩
        · refine ⟨0, by norm_num, u ^ 3 * (u⁻¹ * y * u), mul_mem h3 (hn y hy), ?_⟩
          rw [e, pow_zero, one_mul]
      · exact ⟨a, ha, y * g, mul_mem hy (Subgroup.subset_closure hg), by rw [mul_assoc]⟩
    have hR : ∀ g ∈ clo (u :: Us), ∀ z ∈ T, z * g ∈ T := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg => exact fun z hz => hT z hz g hg
      | one => exact fun z hz => by rwa [mul_one]
      | mul a b _ _ ha hb =>
        intro z hz
        rw [← mul_assoc]
        exact hb _ (ha z hz)
      | inv a _ ha =>
        intro z hz
        have hp : ∀ k : ℕ, ∀ z ∈ T, z * a ^ k ∈ T := by
          intro k
          induction k with
          | zero => exact fun z hz => by rwa [pow_zero, mul_one]
          | succ k ihk =>
            intro z hz
            rw [pow_succ, ← mul_assoc]
            exact ha _ (ihk z hz)
        have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos a),
            pow_orderOf_eq_one]
        rw [hinv]
        exact hp _ z hz
    have hx' := hR x hx 1 ⟨0, by norm_num, 1, one_mem _, by simp⟩
    rw [one_mul] at hx'
    obtain ⟨a, ha, y, hy, rfl⟩ := hx'
    obtain ⟨es, hl, hes, rfl⟩ := ih y hy
    refine ⟨a :: es, by simp [hl], ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact ha
      · exact hes e he
    · simp only [nfL, List.zipWith_cons_cons, List.prod_cons]

end PC

theorem digs_eq (n : ℕ) : digs n =
    [n / 729 % 3, n / 243 % 3, n / 81 % 3, n / 27 % 3, n / 9 % 3, n / 3 % 3, n / 1 % 3] := rfl

theorem digs_surj (es : List ℕ) (hl : es.length = 7) (h : ∀ e ∈ es, e < 3) :
    ∃ n < 2187, digs n = es := by
  rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨x, l⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨ha, hb, hc, hd, he, hf, hg⟩ := h
  refine ⟨a * 729 + b * 243 + c * 81 + d * 27 + e * 9 + f * 3 + g, by omega, ?_⟩
  rw [digs_eq]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

section Syl


theorem coe_rhoL_word (w : WT) :
    ((rhoL ⟨evalG letterG w, tbL_mem_evalG w⟩ : GL (Fin 12) (ZMod 3)) :
      Matrix (Fin 12) (Fin 12) (ZMod 3)) = toMatrix (Timmesfeld.M3B.matOf (Timmesfeld.M3B.LM ()) w) := by
  rw [coe_rhoL]
  exact actMat_evalG w

theorem exists_units {gs : List MatK} (h : ∀ A ∈ gs, ∃ w : WT, Rep A w) :
    ∃ Us : List (GL (Fin 12) (ZMod 3)), List.Forall₂ RepU gs Us ∧ ∀ u ∈ Us, u ∈ rhoL.range := by
  induction gs with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons A gs ih =>
    obtain ⟨Us, h1, h2⟩ := ih fun B hB => h B (List.mem_cons_of_mem _ hB)
    obtain ⟨w, hw⟩ := h A List.mem_cons_self
    refine ⟨rhoL ⟨evalG letterG w, tbL_mem_evalG w⟩ :: Us, .cons ⟨hw.1, ?_⟩ h1, ?_⟩
    · rw [coe_rhoL_word, hw.2]
    · intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · exact ⟨_, rfl⟩
      · exact h2 u hu

theorem sylFact_of_checks {gp : List Ins} {gi : List ℕ} {gs : List MatK} {tp : List (List Ins)}
    {tk : List MatK} {pc : List (ℕ × ℕ × List ℕ)} {v : ℕ} {us : List ℕ} {wv : List (List ℕ)}
    {wu : List (List (List ℕ))} {ko : List ℕ} {cp : List Ins} {r3 : List (ℕ × ℕ × ℕ)}
    {r9 : List ℕ} {fr : List (ℕ × ℕ × ℕ)}
    (hlet : letChk = true) (hgen : genChk gp gi gs = true) (ht : tChk tp tk = true)
    (htw : tp.map slpWT = sigW.toList) (hpc : pcChk gs pc = true) (hu : uChk v us gs = true)
    (hwv : walkChk gs v wv = true) (hwu : walksChk gs us wu = true) (hko : ordChk wv ko = true)
    (hfor : forestW gs wv wu (r3.map Prod.fst ++ r9) fr = true)
    (hr3 : r3Chk gs tk cp r3 = true) (hr9 : r9Chk gs v r9 = true) : SylFact := by
  classical
  unfold SylFact
  obtain ⟨hgl, hgw⟩ := genChk_spec hlet hgen
  obtain ⟨Us, hU, hUr⟩ := exists_units hgw
  have hUl : Us.length = 7 := by rw [← hU.length_eq, hgl]
  have hUk : ∀ k < 7, RepU (gs.getD k idK) (Us.getD k 1) := fun k hk =>
    forall2_getD hU idK 1 k (by omega)
  have hSr : clo Us ≤ rhoL.range := by
    rw [clo, Subgroup.closure_le]
    exact fun u hu => hUr u hu
  have hUS : ∀ k < 7, Us.getD k 1 ∈ clo Us := fun k hk => Subgroup.subset_closure (by
    change Us.getD k 1 ∈ Us
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _)
  have hNS : ∀ n, nfL Us (digs n) ∈ clo Us := fun n => nfL_mem_clo Us (digs n)
  have hrel : ∀ i (hi : i < Us.length), Us[i] ^ 3 ∈ clo (Us.drop (i + 1)) ∧
      ∀ w ∈ Us.drop (i + 1), Us[i]⁻¹ * w * Us[i] ∈ clo (Us.drop (i + 1)) := by
    intro i hi
    have hi7 : i < 7 := by omega
    have hUi := hUk i hi7
    have eUi : Us[i] = Us.getD i 1 := (List.getD_eq_getElem _ _ hi).symm
    rw [eUi]
    constructor
    · obtain ⟨es, -, hz, h3, -⟩ := pcChk_spec hpc (le_refl i) hi7
      have hm := congrArg toMatK (h3 rfl)
      rw [toMatK_mmK (goodMat_mmK _ hUi.1.1).1 hUi.1, toMatK_mmK hUi.1.1 hUi.1, (nfK_rep hU es).2,
        hUi.2] at hm
      have e : Us.getD i 1 ^ 3 = nfL Us es :=
        Units.ext (by rw [Units.val_pow_eq_pow_val, ← hm, pow_three, Matrix.mul_assoc])
      rw [e, nfL_drop (i + 1) Us es hz]
      exact nfL_mem_clo _ _
    · intro w hw
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hw
      rw [List.getElem_drop]
      have hj : i + 1 + k < Us.length := by simp at hk; omega
      rw [← List.getD_eq_getElem _ 1 hj]
      obtain ⟨es, -, hz, -, hr⟩ := pcChk_spec hpc (by omega : i ≤ i + 1 + k) (by omega)
      have hm := congrArg toMatK (hr (by omega))
      have hUj := hUk (i + 1 + k) (by omega)
      rw [toMatK_mmK hUj.1.1 hUi.1, toMatK_mmK hUi.1.1 (nfK_rep hU es).1, (nfK_rep hU es).2,
        hUi.2, hUj.2] at hm
      have e : Us.getD (i + 1 + k) 1 * Us.getD i 1 = Us.getD i 1 * nfL Us es :=
        Units.ext (by rw [Units.val_mul, Units.val_mul, hm])
      have e2 : (Us.getD i 1)⁻¹ * Us.getD (i + 1 + k) 1 * Us.getD i 1 = nfL Us es := by
        rw [mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e2, nfL_drop (i + 1) Us es hz]
      exact nfL_mem_clo _ _
  have hsurj : ∀ x ∈ clo Us, ∃ n < 2187, x = nfL Us (digs n) := by
    intro x hx
    obtain ⟨es, hl, hlt, rfl⟩ := pc_nf Us hrel x hx
    obtain ⟨n, hn, hd⟩ := digs_surj es (by omega) hlt
    exact ⟨n, hn, by rw [hd]⟩
  obtain ⟨hvg, hus⟩ := uChk_spec hu
  have hwv' := walk_spec hU hUl hvg hwv
  obtain ⟨-, -, hwk⟩ := walksChk_spec hwu
  have huk : ∀ k < 3, GoodRow (us.getD k 0) ∧ vz (us.getD k 0) =
      Matrix.vecMul (vz v) ((Us.getD k 1 : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3)) := by
    intro k hk
    have e : us.getD k 0 = vmK v (gs.getD k idK) := by
      rw [hus, M3BF.getD_map_lt (d := idK) (by simp [hgl]; omega),
        List.getD_eq_getElem _ _ (by simp [hgl]; omega), List.getElem_take,
        List.getD_eq_getElem _ _ (by omega)]
    rw [e, vz_vmK (hUk k (by omega)).1, (hUk k (by omega)).2]
    exact ⟨goodRow_vmK _ _, rfl⟩
  have hwu' : ∀ k < 3, ∀ p < 2187, vz (getW (wu.getD k []) p) =
      Matrix.vecMul (vz v) ((Us.getD k 1 * nfL Us (digs p) : GL (Fin 12) (ZMod 3)) :
        Matrix (Fin 12) (Fin 12) (ZMod 3)) := by
    intro k hk p hp
    rw [(walk_spec hU hUl (huk k hk).1 (hwk k hk) p hp).2, (huk k hk).2, Matrix.vecMul_vecMul,
      ← Units.val_mul]
  have hinjN : ∀ n < 2187, ∀ m < 2187,
      Matrix.vecMul (vz v) ((nfL Us (digs n) : GL (Fin 12) (ZMod 3)) :
        Matrix (Fin 12) (Fin 12) (ZMod 3)) =
      Matrix.vecMul (vz v) ((nfL Us (digs m) : GL (Fin 12) (ZMod 3)) :
        Matrix (Fin 12) (Fin 12) (ZMod 3)) → n = m := by
    intro n hn m hm h
    rw [← (hwv' n hn).2, ← (hwv' m hm).2] at h
    exact ordChk_spec hko hn hm (goodRow_inj (hwv' n hn).1 (hwv' m hm).1 h)
  have hinj : ∀ x ∈ clo Us, ∀ y ∈ clo Us,
      Matrix.vecMul (vz v) ((x : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3)) =
      Matrix.vecMul (vz v) ((y : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3)) →
      x = y := by
    intro x hx y hy h
    obtain ⟨n, hn, rfl⟩ := hsurj x hx
    obtain ⟨m, hm, rfl⟩ := hsurj y hy
    rw [hinjN n hn m hm h]
  have hcard : Nat.card (clo Us) = 3 ^ 7 := by
    have hbij : Function.Bijective (fun n : Fin 2187 => (⟨nfL Us (digs n), hNS n⟩ : clo Us)) := by
      refine ⟨fun a b hab => Fin.ext (hinjN a a.isLt b b.isLt ?_), fun x => ?_⟩
      · have := congrArg (fun z : clo Us => Matrix.vecMul (vz v)
          (((z : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3)))) hab
        simpa using this
      · obtain ⟨n, hn, hx⟩ := hsurj x x.2
        exact ⟨⟨n, hn⟩, Subtype.ext hx.symm⟩
    rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hreach : ∀ n, 0 < n → n < 2187 → n < 2187 ∧ ∃ s ∈ clo Us, ∃ r ∈ r3.map Prod.fst ++ r9,
      s⁻¹ * nfL Us (digs n) * s = nfL Us (digs r) := by
    refine forestW_spec hfor _ ?_ ?_
    · intro r hr
      refine ⟨?_, 1, one_mem _, r, hr, by simp⟩
      rcases List.mem_append.1 hr with hr | hr
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
        exact (r3Chk_spec hr3 q hq).1
      · exact (r9Chk_spec hr9 r hr).1
    · rintro n p k hn hk he ⟨hp, s, hs, r, hr, hsr⟩
      have hUk' := hUk k (by omega)
      refine ⟨hn, Us.getD k 1 * s, mul_mem (hUS k (by omega)) hs, r, hr, ?_⟩
      have hv := congrArg vz he
      rw [vz_vmK hUk'.1, (hwv' n hn).2, hUk'.2, Matrix.vecMul_vecMul, ← Units.val_mul,
        hwu' k hk p hp] at hv
      have e := hinj _ (mul_mem (hNS n) (hUS k (by omega))) _ (mul_mem (hUS k (by omega)) (hNS p)) hv
      rw [← hsr]
      calc (Us.getD k 1 * s)⁻¹ * nfL Us (digs n) * (Us.getD k 1 * s)
          = s⁻¹ * ((Us.getD k 1)⁻¹ * (nfL Us (digs n) * Us.getD k 1)) * s := by group
        _ = s⁻¹ * nfL Us (digs p) * s := by
          rw [e]
          group
  refine ⟨clo Us, hSr, hcard, fun y hy hy3 hy1 => ?_⟩
  obtain ⟨n, hn, rfl⟩ := hsurj y hy
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (by rw [digs_zero, nfL_replicate]) hy1
    · exact h
  obtain ⟨-, s, hs, r, hr, hsr⟩ := hreach n hn0 hn
  have hr3' : nfL Us (digs r) ^ 3 = 1 := by
    have := conj_pow (a := s⁻¹) (b := nfL Us (digs n)) (i := 3)
    rw [inv_inv, hsr, hy3, mul_one, inv_mul_cancel] at this
    exact this
  rcases List.mem_append.1 hr with hr | hr
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
    obtain ⟨-, hj3, hi, hmm⟩ := r3Chk_spec hr3 q hq
    have hX := node_rep (rep_letter hlet) cp hi
    have hX' := coe_rhoL_word ((slpNodes cp).getD q.2.2 (.gen 0))
    rw [← hX.2] at hX'
    obtain ⟨a, ha⟩ := hSr hs
    refine ⟨a * ⟨_, tbL_mem_evalG ((slpNodes cp).getD q.2.2 (.gen 0))⟩, q.2.1, hj3, ?_⟩
    have ht' := tChk_spec hlet ht htw q.2.1 hj3
    have hm := congrArg toMatK hmm
    rw [toMatK_mmK (nfK_rep hU _).1.1 hX.1, toMatK_mmK hX.1.1 ht'.1, (nfK_rep hU _).2, ht'.2,
      ← hX'] at hm
    rw [map_mul, ha]
    set X := rhoL ⟨_, tbL_mem_evalG ((slpNodes cp).getD q.2.2 (.gen 0))⟩
    have e : (s * X)⁻¹ * nfL Us (digs n) * (s * X) = X⁻¹ * nfL Us (digs q.1) * X := by
      rw [← hsr]
      group
    rw [e, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hm, ← Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul]
  · exfalso
    obtain ⟨-, hne⟩ := r9Chk_spec hr9 r hr
    have f1 := nfV_rep hU (digs r) v hvg
    have f2 := nfV_rep hU (digs r) _ f1.1
    have f3 := nfV_rep hU (digs r) _ f2.1
    apply hne
    refine goodRow_inj f3.1 hvg ?_
    rw [f3.2, f2.2, f1.2, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Units.val_mul,
      ← Units.val_mul, ← pow_three, hr3', Units.val_one, Matrix.vecMul_one]

end Syl

end CFSG.KC.M3BS

end
