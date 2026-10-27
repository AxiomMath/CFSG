module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEStep2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4L0Gen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.L0Prim
public import Certificates.Certificate12620

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open scoped commutatorElement
open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4.QT CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc
  CFSG.AGLEmbeddingD2.Wilson.Coordinator CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient
  CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77 CFSG.Sporadic.J4.Native
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.GLQ Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

noncomputable abbrev LL : Subgroup J := Coordinator.L0

theorem eq_one_of_mem_center_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {s : S} (hs : s ∈ center S) : s = 1 := by
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S)) with h | h
  · rw [h] at hs; exact hs
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have : a ∈ center S := by rw [h]; trivial
    exact hab ((mem_center_iff.1 this b).symm)

theorem zpowers_le_centralizer_of_comm {G : Type*} [Group G] {w y : G} (h : y * w = w * y) :
    zpowers w ≤ centralizer ({y} : Set G) := by
  rw [zpowers_le]
  exact mem_centralizer_singleton_iff.2 h.symm

theorem isPerfect_of_simple_nonabelian {S : Type*} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) : Group.IsPerfect S := by
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S)) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    have : ⁅a, b⁆ ∈ commutator S := Subgroup.commutator_mem_commutator trivial trivial
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact Group.isPerfect_def.mpr h

theorem isPerfect_of_central_cover {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal] (hZc : Z ≤ center G)
    (hZ6 : ∀ x ∈ Z, x ^ 6 = 1) (hperf : Group.IsPerfect (G ⧸ Z))
    (hZ7 : Z ≤ closure {g : G | g ^ 7 = 1}) : Group.IsPerfect G := by
  have hmap : (commutator G).map (QuotientGroup.mk' Z) = commutator (G ⧸ Z) := by
    rw [_root_.commutator_def, Subgroup.map_commutator, _root_.commutator_def,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)]
  have hdec : ∀ g : G, ∃ c ∈ commutator G, ∃ z ∈ Z, g = c * z := by
    intro g
    have : (QuotientGroup.mk' Z g) ∈ (commutator G).map (QuotientGroup.mk' Z) := by
      rw [hmap, Group.isPerfect_def.1 hperf]; trivial
    obtain ⟨c, hc, hcg⟩ := this
    refine ⟨c, hc, c⁻¹ * g, ?_, by group⟩
    rw [← QuotientGroup.eq]
    exact hcg
  have h7 : ∀ g : G, g ^ 7 = 1 → g ∈ commutator G := by
    intro g hg
    obtain ⟨c, hc, z, hz, rfl⟩ := hdec g
    have hzg : Commute c z := mem_center_iff.1 (hZc hz) c
    have hz36 : z ^ 36 = 1 := by
      calc z ^ 36 = (z ^ 6) ^ 6 := by rw [← pow_mul]
        _ = 1 := by rw [hZ6 z hz, one_pow]
    have e : (c * z) ^ 36 = c ^ 36 := by
      rw [hzg.mul_pow, hz36, mul_one]
    have e2 : c * z = (c * z) ^ 36 := by
      calc c * z = (c * z) * ((c * z) ^ 7) ^ 5 := by rw [hg]; simp
        _ = (c * z) ^ 36 := by rw [← pow_mul, ← pow_succ']
    rw [e2, e]
    exact Subgroup.pow_mem _ hc _
  have hZC : Z ≤ commutator G := fun x hx => by
    have := hZ7 hx
    exact (Subgroup.closure_le (commutator G)).2 (fun g hg => h7 g hg) this
  rw [Group.isPerfect_def, eq_top_iff]
  intro g _
  obtain ⟨c, hc, z, hz, rfl⟩ := hdec g
  exact Subgroup.mul_mem _ hc (hZC hz)

theorem mem_closure_of_coe {G : Type*} [Group G] {H : Subgroup G} (S : Set H) (x : H)
    (h : (x : G) ∈ closure (H.subtype '' S)) : x ∈ closure S := by
  rw [← MonoidHom.map_closure] at h
  obtain ⟨y, hy, hyx⟩ := h
  have : y = x := Subtype.ext hyx
  rw [← this]; exact hy

theorem pow_eq_one_of_card_subgroup {G : Type*} [Group G] (Z : Subgroup G) {n : ℕ}
    (hn : Nat.card Z = n) {x : G} (hx : x ∈ Z) : x ^ n = 1 := by
  have h := pow_card_eq_one' (G := Z) (x := ⟨x, hx⟩)
  rw [hn] at h
  exact congrArg Subtype.val h

section Struct


theorem L0_eq_centralizer (hF : J4Facts) : LL = Subgroup.centralizer ({cE} : Set J) :=
  (centralizer_cE_eq hF).1.symm

theorem card_L0 (hF : J4Facts) : Nat.card ↥LL = 2661120 := by
  rw [L0_eq_centralizer hF]; exact (centralizer_cE_eq hF).2

noncomputable def piL0 (hF : J4Facts) : ↥LL →* Equiv.Perm (Fin 77) :=
  (rho hF).comp (Subgroup.inclusion Coordinator.L0_le_M2)

theorem piL0_eq_one_iff (hF : J4Facts) (x : ↥LL) :
    piL0 hF x = 1 ↔ (x : J) ∈ Kgrp :=
  (mem_Kgrp_iff_rho hF (x : J) (Coordinator.L0_le_M2 x.2)).symm

theorem Kgrp_inf_cE_eq : Kgrp ⊓ Subgroup.centralizer ({cE} : Set J) = zpowers (z0 * cE) :=
  centralizer_K_eq Qgrp cE z0 (cE_normalizes_Qgrp matFacts) (cE_pow_three matFacts)
    (z0_mul_self matFacts) (z0_mem_Qgrp matFacts) z0_comm_cE
    (fun q hq hqc => centralizer_Qgrp_cE hq hqc)

theorem card_zpowers_z0_cE : Nat.card ↥(zpowers (z0 * cE)) = 6 := by
  rw [← Kgrp_inf_cE_eq]
  exact card_centralizer_K Qgrp cE z0 (cE_normalizes_Qgrp matFacts) (cE_pow_three matFacts)
    (cE_ne_one matFacts) (z0_mul_self matFacts) (z0_ne_one matFacts) (z0_mem_Qgrp matFacts)
    z0_comm_cE (fun q hq hqc => centralizer_Qgrp_cE hq hqc)

theorem z0_cE_mem_LL : z0 * cE ∈ LL := by
  rw [Coordinator.mem_L0_iff]
  have h : z0 * cE * z0 = z0 * (z0 * cE) := by
    calc z0 * cE * z0 = z0 * (cE * z0) := mul_assoc _ _ _
      _ = z0 * (z0 * cE) := by rw [← z0_comm_cE.eq]
  have h2 : z0 * cE * cE = cE * (z0 * cE) := by
    calc z0 * cE * cE = cE * z0 * cE := by rw [← z0_comm_cE.eq]
      _ = cE * (z0 * cE) := mul_assoc _ _ _
  exact ⟨h, h2⟩

theorem ker_piL0_eq (hF : J4Facts) :
    (piL0 hF).ker = (zpowers (z0 * cE)).subgroupOf LL := by
  ext x
  rw [MonoidHom.mem_ker, piL0_eq_one_iff, Subgroup.mem_subgroupOf, ← Kgrp_inf_cE_eq]
  constructor
  · intro h
    exact ⟨h, by
      have := Coordinator.L0_le_centralizer_cE x.2
      exact this⟩
  · intro h; exact h.1

theorem card_ker_piL0 (hF : J4Facts) : Nat.card ↥(piL0 hF).ker = 6 := by
  rw [ker_piL0_eq hF, ← card_zpowers_z0_cE]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    ((Subgroup.zpowers_le).2 z0_cE_mem_LL)).toEquiv

theorem card_range_piL0 (hF : J4Facts) : Nat.card ↥(piL0 hF).range = 443520 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (piL0 hF).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (piL0 hF)).toEquiv] at h1
  rw [card_L0 hF, card_ker_piL0 hF] at h1
  omega

theorem ls_parts :
    (List.range 6).all lsHitAt = true ∧ lsHitWords.length = 6 ∧
    eqRows (powRows gmats[13]! 3) idRows = true ∧
    eqRows (powRows (lsARows ()) 7) idRows = true ∧
    eqRows (powRows (lsBRows ()) 7) idRows = true ∧
    eqRows (powRows (mulRows (lsARows ()) (lsBRows ())) 7) cMat = true := by
  have h := Certificates.certificate12620
  simp only [lsOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem gE13_pow_three : gE 13 ^ 3 = 1 := by
  apply Mx_injective
  have h := congrArg rowsMatrix (eqRows_iff.1 ls_parts.2.2.1)
  rw [rowsMatrix_powRows, rowsMatrix_idRows, ← Mx_gE matFacts (by norm_num)] at h
  rw [map_pow, map_one]
  exact h

theorem sPerm_one_odd (hF : J4Facts) : Odd (orderOf (sPerm 1)) := by
  have h13 : sPerm 1 = rho hF ⟨gE 13, gE_mem_M2 matFacts (by norm_num)⟩ :=
    (rho_gE_perm hF (n := 13) (by norm_num)).symm
  have hpow : sPerm 1 ^ 3 = 1 := by
    rw [h13, ← map_pow]
    have : (⟨gE 13, gE_mem_M2 matFacts (by norm_num)⟩ : ↥M2) ^ 3 = 1 :=
      Subtype.ext (by simpa using gE13_pow_three)
    rw [this, map_one]
  exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hpow)

theorem range_piL0_eq_map (hF : J4Facts) :
    (piL0 hF).range = (Coordinator.L0.subgroupOf M2).map (rho hF) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion Coordinator.L0_le_M2 x, x.2, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩

theorem MbarP_le_range (hF : J4Facts) : MbarP ≤ (piL0 hF).range := by
  rw [range_piL0_eq_map hF, MbarP, Subgroup.closure_le]
  intro x hx
  obtain ⟨o3, o5, o7, o11⟩ := L0Prim.orders_sPerm
  simp only [oddPerms, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hx
  rcases hx with h | h | h | h | h
  · have := L0Prim.sPerm_mem_G hF 0 (by rw [o3]; decide)
    rwa [show sPerm 0 = x from h.symm] at this
  · have := L0Prim.sPerm_mem_G hF 1 (sPerm_one_odd hF)
    rwa [show sPerm 1 = x from h.symm] at this
  · have := L0Prim.sPerm_mem_G hF 2 (by rw [o5]; decide)
    rwa [show sPerm 2 = x from h.symm] at this
  · have := L0Prim.sPerm_mem_G hF 3 (by rw [o7]; decide)
    rwa [show sPerm 3 = x from h.symm] at this
  · have := L0Prim.sPerm_mem_G hF 4 (by rw [o11]; decide)
    rwa [show sPerm 4 = x from h.symm] at this

theorem range_piL0_eq (hF : J4Facts) : (piL0 hF).range = MbarP :=
  (Subgroup.eq_of_le_of_card_ge (MbarP_le_range hF)
    (by rw [card_range_piL0 hF, card_MbarP])).symm

theorem simple_range (hF : J4Facts) : IsSimpleGroup ↥(piL0 hF).range := by
  have := isSimpleGroup_MbarP
  exact MulEquiv.isSimpleGroup (MulEquiv.subgroupCongr (range_piL0_eq hF))

theorem nonabelian_range (hF : J4Facts) : ∃ a b : ↥(piL0 hF).range, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := MbarP_nonabelian
  let e := MulEquiv.subgroupCongr (range_piL0_eq hF)
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem center_LL_eq_ker (hF : J4Facts) : center ↥LL = (piL0 hF).ker := by
  ext x
  constructor
  · intro hx
    have : IsSimpleGroup ↥(piL0 hF).range := simple_range hF
    have hc : (⟨piL0 hF x, ⟨x, rfl⟩⟩ : ↥(piL0 hF).range) ∈ center ↥(piL0 hF).range := by
      rw [mem_center_iff]
      rintro ⟨r, y, rfl⟩
      apply Subtype.ext
      show piL0 hF y * piL0 hF x = piL0 hF x * piL0 hF y
      rw [← map_mul, ← map_mul, mem_center_iff.1 hx y]
    have := eq_one_of_mem_center_of_simple (nonabelian_range hF) hc
    exact congrArg Subtype.val this
  · intro hx
    rw [ker_piL0_eq hF, Subgroup.mem_subgroupOf] at hx
    rw [mem_center_iff]
    intro g
    have hg := Coordinator.mem_L0_iff.1 g.2
    have h1 : zpowers (z0 * cE) ≤ centralizer ({(g : J)} : Set J) :=
      zpowers_le_centralizer_of_comm (by
        calc (g : J) * (z0 * cE) = (g * z0) * cE := (mul_assoc _ _ _).symm
          _ = (z0 * g) * cE := by rw [hg.1]
          _ = z0 * (g * cE) := mul_assoc _ _ _
          _ = z0 * (cE * g) := by rw [hg.2]
          _ = (z0 * cE) * g := (mul_assoc _ _ _).symm)
    have h2 := mem_centralizer_singleton_iff.1 (h1 hx)
    exact Subtype.ext h2.symm

theorem card_center_LL (hF : J4Facts) : Nat.card ↥(center ↥LL) = 6 := by
  rw [center_LL_eq_ker hF]; exact card_ker_piL0 hF

noncomputable def quotEquivM22 (hF : J4Facts) :
    (↥LL ⧸ center ↥LL) ≃* ↥CFSG.Blueprint.NativeSporadic.M22 :=
  ((QuotientGroup.quotientMulEquivOfEq (center_LL_eq_ker hF)).trans
    (QuotientGroup.quotientKerEquivRange (piL0 hF))).trans
    ((MulEquiv.subgroupCongr (range_piL0_eq hF)).trans phiEquiv.symm)

@[expose] noncomputable def gHit (i : ℕ) : J := gWord (lsHitWords.getD i [])

theorem lsHit_lt : ∀ i < 6, ∀ n ∈ lsHitWords.getD i [], n < 32 := by decide +kernel

theorem Mx_gHit {i : ℕ} (hi : i < 6) : Mx (gHit i) = rowsMatrix (lsHitRows i) :=
  Mx_gWord _ (lsHit_lt i hi)

theorem gHit_mem {i : ℕ} (hi : i < 6) : gHit i ∈ LL := by
  rw [Coordinator.mem_L0_iff]
  have hM2 : gHit i ∈ M2 := gWord_mem_M2 _ (lsHit_lt i hi)
  refine ⟨(cent_iff.1 hM2).symm, ?_⟩
  have hat : lsHitAt i = true := List.all_eq_true.1 ls_parts.1 i (List.mem_range.2 hi)
  unfold lsHitAt at hat
  simp only [Bool.and_eq_true] at hat
  apply Mx_injective
  have h1 := congrArg rowsMatrix (eqRows_iff.1 hat.2)
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← Mx_cE matFacts, ← Mx_gHit hi] at h1
  rw [map_mul, map_mul]
  exact h1

@[expose] noncomputable def hitProd (idx : List ℕ) : J := idx.foldl (fun acc i => acc * gHit i) 1

theorem hitProd_spec (idx : List ℕ) (hidx : ∀ i ∈ idx, i < 6) :
    hitProd idx ∈ LL ∧ Mx (hitProd idx) = rowsMatrix (lsProdRows idx) := by
  have : ∀ (l : List ℕ), (∀ i ∈ l, i < 6) → ∀ (acc : J) (R : Array V2), acc ∈ LL →
      Mx acc = rowsMatrix R →
      l.foldl (fun acc i => acc * gHit i) acc ∈ LL ∧
        Mx (l.foldl (fun acc i => acc * gHit i) acc) =
          rowsMatrix (l.foldl (fun acc i => mulRows acc (lsHitRows i)) R) := by
    intro l
    induction l with
    | nil => intro _ acc R h1 h2; exact ⟨h1, h2⟩
    | cons i l ih =>
      intro hl acc R h1 h2
      rw [List.foldl_cons, List.foldl_cons]
      have hi := hl i List.mem_cons_self
      refine ih (fun m hm => hl m (List.mem_cons_of_mem _ hm)) _ _
        (Subgroup.mul_mem _ h1 (gHit_mem hi)) ?_
      rw [map_mul, h2, Mx_gHit hi, rowsMatrix_mulRows]
  exact this idx hidx 1 idRows (Subgroup.one_mem _) (by rw [map_one, rowsMatrix_idRows])

@[expose] noncomputable def aJ : J := hitProd lsAIdx ^ lsAExp
@[expose] noncomputable def bJ : J := hitProd lsBIdx ^ lsBExp

theorem lsIdx_lt : (∀ i ∈ lsAIdx, i < 6) ∧ (∀ i ∈ lsBIdx, i < 6) := by decide +kernel

theorem aJ_spec : aJ ∈ LL ∧ Mx aJ = rowsMatrix (lsARows ()) := by
  obtain ⟨h1, h2⟩ := hitProd_spec lsAIdx lsIdx_lt.1
  exact ⟨Subgroup.pow_mem _ h1 _, by rw [aJ, map_pow, h2, lsARows, rowsMatrix_powRows]⟩

theorem bJ_spec : bJ ∈ LL ∧ Mx bJ = rowsMatrix (lsBRows ()) := by
  obtain ⟨h1, h2⟩ := hitProd_spec lsBIdx lsIdx_lt.2
  exact ⟨Subgroup.pow_mem _ h1 _, by rw [bJ, map_pow, h2, lsBRows, rowsMatrix_powRows]⟩

theorem aJ_pow : aJ ^ 7 = 1 := by
  apply Mx_injective
  have h := congrArg rowsMatrix (eqRows_iff.1 ls_parts.2.2.2.1)
  rw [rowsMatrix_powRows, rowsMatrix_idRows, ← aJ_spec.2] at h
  rw [map_pow, map_one]; exact h

theorem bJ_pow : bJ ^ 7 = 1 := by
  apply Mx_injective
  have h := congrArg rowsMatrix (eqRows_iff.1 ls_parts.2.2.2.2.1)
  rw [rowsMatrix_powRows, rowsMatrix_idRows, ← bJ_spec.2] at h
  rw [map_pow, map_one]; exact h

theorem ab_pow : (aJ * bJ) ^ 7 = cE := by
  apply Mx_injective
  have h := congrArg rowsMatrix (eqRows_iff.1 ls_parts.2.2.2.2.2)
  rw [rowsMatrix_powRows, rowsMatrix_mulRows, ← aJ_spec.2, ← bJ_spec.2, ← Mx_cE matFacts] at h
  rw [map_pow, map_mul]; exact h

theorem cE_mem_LL : cE ∈ LL := by
  rw [Coordinator.mem_L0_iff]; exact ⟨z0_comm_cE.symm.eq, rfl⟩

theorem z0_mem_LL : z0 ∈ LL := by
  rw [Coordinator.mem_L0_iff]; exact ⟨rfl, z0_comm_cE.eq⟩

theorem cE_mem_closure_seven :
    (⟨cE, cE_mem_LL⟩ : ↥LL) ∈ Subgroup.closure {g : ↥LL | g ^ 7 = 1} := by
  have ha : (⟨aJ, aJ_spec.1⟩ : ↥LL) ∈ {g : ↥LL | g ^ 7 = 1} := Subtype.ext (by simpa using aJ_pow)
  have hb : (⟨bJ, bJ_spec.1⟩ : ↥LL) ∈ {g : ↥LL | g ^ 7 = 1} := Subtype.ext (by simpa using bJ_pow)
  have := Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure ha)
    (Subgroup.subset_closure hb)) 7
  have e : ((⟨aJ, aJ_spec.1⟩ : ↥LL) * ⟨bJ, bJ_spec.1⟩) ^ 7 = ⟨cE, cE_mem_LL⟩ :=
    Subtype.ext (by simpa using ab_pow)
  rwa [e] at this

theorem z0_mem_closure_seven :
    (⟨z0, z0_mem_LL⟩ : ↥LL) ∈ Subgroup.closure {g : ↥LL | g ^ 7 = 1} := by
  refine mem_closure_of_coe _ _ ?_
  refine (Subgroup.closure_mono ?_) z0_mem_closure_orderSeven
  rintro g ⟨hg, ho⟩
  have h7 : g ^ 7 = 1 := by rw [← ho]; exact pow_orderOf_eq_one g
  exact ⟨⟨g, hg⟩, Subtype.ext (by simpa using h7), rfl⟩

noncomputable def quotEquivRange (hF : J4Facts) : (↥LL ⧸ center ↥LL) ≃* ↥(piL0 hF).range :=
  (QuotientGroup.quotientMulEquivOfEq (center_LL_eq_ker hF)).trans
    (QuotientGroup.quotientKerEquivRange (piL0 hF))

theorem nonabelian_quot (hF : J4Facts) : ∃ a b : ↥LL ⧸ center ↥LL, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := nonabelian_range hF
  refine ⟨(quotEquivRange hF).symm a, (quotEquivRange hF).symm b, fun h => hab ?_⟩
  have := congrArg (quotEquivRange hF) h
  simpa using this

theorem simple_quot (hF : J4Facts) : IsSimpleGroup (↥LL ⧸ center ↥LL) := by
  have := simple_range hF
  exact MulEquiv.isSimpleGroup (quotEquivRange hF)

theorem isPerfect_LL (hF : J4Facts) : Group.IsPerfect ↥LL := by
  have hker : (piL0 hF).ker = center ↥LL := (center_LL_eq_ker hF).symm
  refine isPerfect_of_central_cover (piL0 hF).ker (hker ▸ le_rfl) ?_ ?_ ?_
  · intro x hx
    exact pow_eq_one_of_card_subgroup _ (card_ker_piL0 hF) hx
  · have e : (↥LL ⧸ (piL0 hF).ker) ≃* ↥(piL0 hF).range :=
      QuotientGroup.quotientKerEquivRange (piL0 hF)
    have hs : IsSimpleGroup (↥LL ⧸ (piL0 hF).ker) := by
      have := simple_range hF
      exact MulEquiv.isSimpleGroup e
    refine @isPerfect_of_simple_nonabelian _ _ hs ?_
    obtain ⟨a, b, hab⟩ := nonabelian_range hF
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  · intro x hx
    have hx' := hx
    rw [ker_piL0_eq hF, Subgroup.mem_subgroupOf] at hx'
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx'
    have hw : (⟨z0, z0_mem_LL⟩ * ⟨cE, cE_mem_LL⟩ : ↥LL) ∈
        Subgroup.closure {g : ↥LL | g ^ 7 = 1} :=
      Subgroup.mul_mem _ z0_mem_closure_seven cE_mem_closure_seven
    have e : x = (⟨z0, z0_mem_LL⟩ * ⟨cE, cE_mem_LL⟩ : ↥LL) ^ k := by
      apply Subtype.ext
      rw [← hk]
      simp
    rw [e]
    exact Subgroup.zpow_mem _ hw k

theorem isQuasisimple_LL (hF : J4Facts) : CFSG.IsQuasisimple ↥LL :=
  ⟨isPerfect_LL hF, simple_quot hF, nonabelian_quot hF⟩

end Struct

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
