module

public import Certificates.Certificate589304
public import CFSG.Sporadic.SmallOddCore.J3
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Sporadic.Recognition.LyonsAmalgamInv
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem27
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Sylow
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DuadConcl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RefConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclTransport

public section

namespace CFSG.SectionRank.QTK.Insp443

namespace J3Cls

open Subgroup CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Native
open CFSG.Sporadic.SmallOddCore (genOf tp rep_tp enumOK_spec normOK_spec centCount_spec memT_spec
  forall₂_tablePerm mem_map_tablePerm nodup_of_hkeysDistinct commTT_iff j3_groupData
  ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial tp_mem_genOf permOK enumOK normOK
  centCount j3Sift j3CentTbl j3Rows j3C)
open CFSG.Sporadic.SmallOddCore.Native (mulClosureH memT)

theorem card_genOf_subtype {n cap m : ℕ} (hn : n < 2 ^ 32) {cs : List Table}
    (hc : ∀ c ∈ cs, permOK n c = true) (hC : enumOK n cap m cs = true) {f : Table → Bool}
    {Q : Equiv.Perm (Fin n) → Prop} [DecidablePred Q]
    (hfQ : ∀ T g, Rep n T g → (f T = true ↔ Q g)) :
    Nat.card {x : genOf n cs // Q x} = (mulClosureH n cs.toArray cap).1.toList.countP f := by
  obtain ⟨-, hrep, hcov, hdist⟩ := enumOK_spec hn hc hC
  have hrepL := forall₂_tablePerm (fun k hk => (hrep k hk).1)
  have hnodup := nodup_of_hkeysDistinct hrepL hdist
  have hmemL : ∀ g, g ∈ (mulClosureH n cs.toArray cap).1.toList.map (tablePerm n) ↔
      g ∈ genOf n cs := by
    intro g
    constructor
    · intro hg'
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm (fun k hk => (hrep k hk).1) hg'
      exact (hrep k hk).2
    · intro hg'
      obtain ⟨k, hk, hkrep⟩ := hcov g hg'
      refine List.mem_map.mpr ⟨(mulClosureH n cs.toArray cap).1[k]!, ?_, tablePerm_eq hkrep⟩
      rw [getElem!_pos (mulClosureH n cs.toArray cap).1 k hk]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hk)
  rw [card_subtype_eq_countP (genOf n cs) _ hnodup hmemL Q, List.countP_map]
  apply List.countP_congr
  intro T hT
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
  have hk' := (hrep k hk).1
  rw [getElem!_pos (mulClosureH n cs.toArray cap).1 k hk] at hk'
  simp only [Function.comp_apply, decide_eq_true_eq]
  exact (hfQ _ _ hk').symm

theorem le_or_le_of_forall_mem_or {G : Type*} [Group G] {W A B : Subgroup G}
    (h : ∀ x ∈ W, x ∈ A ∨ x ∈ B) : W ≤ A ∨ W ≤ B := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨a, haW, haA⟩ := SetLike.not_le_iff_exists.mp hne.1
  obtain ⟨b, hbW, hbB⟩ := SetLike.not_le_iff_exists.mp hne.2
  have haB : a ∈ B := (h a haW).resolve_left haA
  have hbA : b ∈ A := (h b hbW).resolve_right hbB
  rcases h (a * b) (W.mul_mem haW hbW) with hab | hab
  · exact haA (by simpa using A.mul_mem hab (A.inv_mem hbA))
  · exact hbB (by simpa using B.mul_mem (B.inv_mem haB) hab)

theorem map_conj_map_conj {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  ext x
  simp

theorem card_quot_le_of_conj_mem' {G : Type*} [Group G] (H : Subgroup G) (x : G) {T : Set G}
    (hT : T.Finite) (h : ∀ g ∈ H, g * x * g⁻¹ ∈ T) :
    Nat.card (↥H ⧸ (H ⊓ Subgroup.centralizer {x}).subgroupOf H) ≤ T.ncard := by
  set C := (H ⊓ Subgroup.centralizer {x}).subgroupOf H
  let f : ↥H ⧸ C → T := Quotient.lift (fun g : ↥H => (⟨(g : G) * x * (g : G)⁻¹, h g g.2⟩ : T))
    (fun a b hab => by
      have hab' := QuotientGroup.leftRel_apply.mp hab
      rw [Subgroup.mem_subgroupOf] at hab'
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hab'.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc ⊢
      calc (a : G) * x * (a : G)⁻¹ = a * ((a : G)⁻¹ * b * x) * (b : G)⁻¹ := by rw [hc]; group
        _ = b * x * (b : G)⁻¹ := by group)
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
      induction q₂ using QuotientGroup.induction_on with
      | H b =>
        have h1 := congrArg Subtype.val hq
        change (a : G) * x * (a : G)⁻¹ = b * x * (b : G)⁻¹ at h1
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        refine ⟨H.mul_mem (H.inv_mem a.2) b.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc (a : G)⁻¹ * b * x = (a : G)⁻¹ * (b * x * (b : G)⁻¹) * b := by group
          _ = (a : G)⁻¹ * (a * x * (a : G)⁻¹) * b := by rw [h1]
          _ = x * ((a : G)⁻¹ * b) := by group
  have : Finite T := hT.to_subtype
  calc Nat.card (↥H ⧸ C) ≤ Nat.card T := Nat.card_le_card_of_injective f hf
    _ = T.ncard := Nat.card_coe_set_eq T

theorem card_le_of_conj_mem' {G : Type*} [Group G] (H : Subgroup G) (x : G) {T : Set G}
    (hT : T.Finite) (h : ∀ g ∈ H, g * x * g⁻¹ ∈ T) :
    Nat.card H ≤ T.ncard * Nat.card ↥(H ⊓ Subgroup.centralizer {x}) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((H ⊓ Subgroup.centralizer {x}).subgroupOf H)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  rw [h1]
  exact Nat.mul_le_mul_right _ (card_quot_le_of_conj_mem' H x hT h)

theorem sixteen_le_card {G : Type} [Group G] [Finite G] (h7 : ¬ 7 ∣ Nat.card G)
    {L V MK : Subgroup G} (h : KConfig G L V MK) : 16 ≤ Nat.card V := by
  have hne : ⁅V, L⁆ ≠ ⊥ := fun hb => h.ne_bot (h.eq_commutator.trans hb)
  obtain ⟨p, hp, hp5, y, hyL, ⟨k, hyk⟩, t, htV, hyt⟩ :=
    exists_pElement_not_comm h.perfect h.le_normalizer hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyt (by simp)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hyk)
  have hyP : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hmod := CFSG.Quasithin.H13.card_modEq_card_centralizer_of_pElement hyP (h.le_normalizer hyL)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp h.elemAbelian.isPGroup
  have hCdvd : Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) ∣ 2 ^ a :=
    ha ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨b, hb, hbC⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hCdvd
  have hba : b < a := by
    rcases lt_or_eq_of_le hb with hlt | rfl
    · exact hlt
    · exfalso
      have hEq : V ⊓ Subgroup.centralizer ({y} : Set G) = V :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [ha, hbC])
      have htV' : t ∈ V ⊓ Subgroup.centralizer ({y} : Set G) := by rw [hEq]; exact htV
      have htC := Subgroup.mem_centralizer_singleton_iff.mp htV'.2
      apply hyt
      rw [← htC, mul_inv_cancel_right]
  have hpG : p ∣ Nat.card G := by
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hy1 hj
    exact (dvd_pow_self p hj0).trans (hj ▸ orderOf_dvd_natCard y)
  by_contra hlt
  push Not at hlt
  have ha3 : a ≤ 3 := by
    by_contra h4
    push Not at h4
    have h16 : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h4
    rw [ha] at hlt
    omega
  rw [ha, hbC] at hmod
  have hdiv : p ∣ 2 ^ a - 2 ^ b :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) hb)).mp hmod.symm
  have hpos : 0 < 2 ^ a - 2 ^ b := Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) hba)
  have hp7 : p ≤ 7 := by
    have h1 := Nat.le_of_dvd hpos hdiv
    have h2 : 2 ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) ha3
    have h3 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    have h4 : (2 : ℕ) ^ 3 = 8 := by norm_num
    omega
  interval_cases p
  · interval_cases a <;> interval_cases b <;> norm_num at hdiv
  · norm_num at hp
  · exact h7 hpG

theorem hn6156 : 6156 < 2 ^ 32 := by norm_num

@[expose] def mMat (masks : List ℕ) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun r i => maskVec 4 (masks.getD i 0) r

theorem mMat_comm₁ : mMat [3, 1, 10, 15] * Duad.Om = Duad.Om * mMat [3, 1, 10, 15] := by decide

theorem mMat_comm₂ : mMat [10, 15, 3, 1] * Duad.Om = Duad.Om * mMat [10, 15, 3, 1] := by decide

theorem mMat_det₁ : (Duad.f4Mat (mMat [3, 1, 10, 15])).det = 1 := by decide

theorem mMat_det₂ : (Duad.f4Mat (mMat [10, 15, 3, 1])).det = 1 := by decide

theorem mem_allTbls_of_eB {T : Table} (h : T ∈ eB) : T ∈ allTbls := by
  show T ∈ eB ++ [omT, scT] ++ mGens ++ sGens ++ cGens
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ h)))

theorem omT_mem : omT ∈ allTbls := by
  show omT ∈ eB ++ [omT, scT] ++ mGens ++ sGens ++ cGens
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ List.mem_cons_self)))

theorem scT_mem : scT ∈ allTbls := by
  show scT ∈ eB ++ [omT, scT] ++ mGens ++ sGens ++ cGens
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))))

theorem mem_allTbls_of_mGens {T : Table} (h : T ∈ mGens) : T ∈ allTbls := by
  show T ∈ eB ++ [omT, scT] ++ mGens ++ sGens ++ cGens
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))

theorem mem_allTbls_of_sGens {T : Table} (h : T ∈ sGens) : T ∈ allTbls := by
  show T ∈ eB ++ [omT, scT] ++ mGens ++ sGens ++ cGens
  exact List.mem_append_left _ (List.mem_append_right _ h)

theorem mem_allTbls_of_cGens {T : Table} (h : T ∈ cGens) : T ∈ allTbls := by
  show T ∈ eB ++ [omT, scT] ++ mGens ++ sGens ++ cGens
  exact List.mem_append_right _ h

theorem nGens_eq : nGens = mGens ++ [omT] := rfl

theorem mem_allTbls_of_nGens {T : Table} (h : T ∈ nGens) : T ∈ allTbls := by
  rw [nGens_eq, List.mem_append, List.mem_singleton] at h
  rcases h with h | h
  · exact mem_allTbls_of_mGens h
  · rw [h]
    exact omT_mem

theorem clsTbl5_mem : clsTbl 5 ∈ mGens := List.mem_cons_self

theorem clsTbl6_mem : clsTbl 6 ∈ mGens := List.mem_cons_of_mem _ List.mem_cons_self

theorem eq_of_mem_mGens {g : Table} (hg : g ∈ mGens) : g = clsTbl 5 ∨ g = clsTbl 6 := by
  simpa only [mGens, List.mem_cons, List.not_mem_nil, or_false] using hg

theorem eB_getD_mem (i : Fin 4) : eB.getD i (idT 6156) ∈ eB := by
  rw [List.getD_eq_getElem _ _ (by show (i : ℕ) < 4; exact i.2)]
  exact List.getElem_mem _

@[expose] noncomputable def el (T : Table) : ↥j3P := by
  classical
  exact if h : tp 6156 T ∈ j3P then ⟨tp 6156 T, h⟩ else 1

theorem coe_el {T : Table} (h : tp 6156 T ∈ j3P) : (el T : Equiv.Perm (Fin 6156)) = tp 6156 T := by
  unfold el
  rw [dif_pos h]

@[expose] noncomputable def vK (i : Fin 4) : ↥j3P := el (eB.getD i (idT 6156))

section Data

theorem k_tbls : tblsOK = true := by
  obtain ⟨h, -⟩ := Certificates.certificate589304
  exact h

theorem k_eb : ebasisOK 6156 eB = true := by
  obtain ⟨-, h, -⟩ := Certificates.certificate589304
  exact h

theorem k_om : masksOK 6156 eB omT [2, 3, 8, 12] = true := by
  obtain ⟨-, -, h, -⟩ := Certificates.certificate589304
  exact h

theorem k_m₁ : masksOK 6156 eB (clsTbl 5) [3, 1, 10, 15] = true := by
  obtain ⟨-, -, -, h, -⟩ := Certificates.certificate589304
  exact h

theorem k_m₂ : masksOK 6156 eB (clsTbl 6) [10, 15, 3, 1] = true := by
  obtain ⟨-, -, -, -, h, -⟩ := Certificates.certificate589304
  exact h

theorem k_enumC : enumOK 6156 3000 1920 cGens = true := by
  obtain ⟨-, -, -, -, -, h, -⟩ := Certificates.certificate589304
  exact h

theorem k_cent : centCount 6156 3000 cGens eB = 16 := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := Certificates.certificate589304
  exact h

theorem k_norm : normCount = 192 := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := Certificates.certificate589304
  exact h

theorem k_enumM : enumOK 6156 3000 960 mGens = true := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate589304
  exact h

theorem k_enumN : enumOK 6156 3000 2880 nGens = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate589304
  exact h

theorem k_normOK : normOK 6156 3000 mGens [omT] = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate589304
  exact h

theorem k_le : eB.all (memT 6156 (mulClosureH 6156 mGens.toArray 3000).1) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate589304
  exact h

theorem k_enumS : enumOK 6156 3000 128 sGens = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate589304
  exact h

theorem k_cls : clsOK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := Certificates.certificate589304
  exact h

theorem tbls_facts {T : Table} (hT : T ∈ allTbls) : permOK 6156 T = true ∧ j3Sift T = true := by
  have h := k_tbls
  simp only [tblsOK, List.all_eq_true, Bool.and_eq_true] at h
  exact h T hT

theorem rep_tbl {T : Table} (hT : T ∈ allTbls) : Rep 6156 T (tp 6156 T) :=
  rep_tp (tbls_facts hT).1

theorem tp_mem_j3P {T : Table} (hT : T ∈ allTbls) : tp 6156 T ∈ j3P :=
  (j3_groupData.sift T _ (rep_tbl hT)).mp (tbls_facts hT).2

theorem rep_el {T : Table} (hT : T ∈ allTbls) : Rep 6156 T (el T : Equiv.Perm (Fin 6156)) := by
  rw [coe_el (tp_mem_j3P hT)]
  exact rep_tbl hT

theorem coe_vK (i : Fin 4) :
    (vK i : Equiv.Perm (Fin 6156)) = tp 6156 (eB.getD i (idT 6156)) :=
  coe_el (tp_mem_j3P (mem_allTbls_of_eB (eB_getD_mem i)))

theorem rep_vK (i : Fin 4) : Rep 6156 (eB.getD i (idT 6156)) (vK i : Equiv.Perm (Fin 6156)) :=
  rep_el (mem_allTbls_of_eB (eB_getD_mem i))

theorem forall₂_vK :
    List.Forall₂ (Rep 6156) eB (List.ofFn fun i => (vK i : Equiv.Perm (Fin 6156))) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [eB], fun i h₁ h₂ => ?_⟩
  have h4 : i < 4 := by simpa using h₂
  have h := rep_vK ⟨i, h4⟩
  rw [List.getD_eq_getElem _ _ h₁] at h
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  exact h

theorem basisP : EBasis fun i => (vK i : Equiv.Perm (Fin 6156)) :=
  ebasis_of_ebasisOK hn6156 forall₂_vK k_eb

theorem basisK : EBasis vK :=
  EBasis.of_map (f := j3P.subtype) Subtype.val_injective basisP

theorem coe_eElt (c : Fin 4 → ZMod 2) :
    ((eElt vK c : ↥j3P) : Equiv.Perm (Fin 6156)) =
      eElt (fun i => (vK i : Equiv.Perm (Fin 6156))) c :=
  map_eElt j3P.subtype c

theorem eB_eq : eB = [j3CentTbl 9, clsTbl 0, clsTbl 1, clsTbl 2] := rfl

theorem vK_zero : (vK 0 : Equiv.Perm (Fin 6156)) = tp 6156 (j3CentTbl 9) := by
  rw [coe_vK, eB_eq]
  simp only [Fin.val_zero, List.getD_cons_zero]

theorem vK_zero_ne_one : vK 0 ≠ 1 := by
  intro h
  have h1 : eElt vK (Pi.single 0 1) = 1 := by rw [eElt_single]; exact h
  have h2 := basisK.ne_one _ h1
  have h3 := congrFun h2 0
  simp at h3

theorem conj_vK {T : Table} (hT : T ∈ allTbls) {masks : List ℕ}
    (hm : masksOK 6156 eB T masks = true) (i : Fin 4) :
    el T * vK i * (el T)⁻¹ = eElt vK (maskVec 4 (masks.getD i 0)) := by
  apply Subtype.ext
  have h := conj_of_masksOK hn6156 forall₂_vK (rep_el hT) hm i
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h, coe_eElt]

theorem el_mem_eNorm {T : Table} (hT : T ∈ allTbls) {masks : List ℕ}
    (hm : masksOK 6156 eB T masks = true) : el T ∈ eNorm basisK :=
  mem_eNorm basisK (mMat masks) fun i => conj_vK hT hm i

theorem eMat_el {T : Table} (hT : T ∈ allTbls) {masks : List ℕ}
    (hm : masksOK 6156 eB T masks = true) :
    eMat basisK ⟨el T, el_mem_eNorm hT hm⟩ = mMat masks :=
  eMat_eq basisK _ _ fun i => conj_vK hT hm i

theorem el_mem_f4Stab {T : Table} (hT : T ∈ allTbls) {masks : List ℕ}
    (hm : masksOK 6156 eB T masks = true) (hc : mMat masks * Duad.Om = Duad.Om * mMat masks) :
    el T ∈ Duad.f4Stab basisK :=
  ⟨el_mem_eNorm hT hm, by rw [eMat_el hT hm]; exact hc⟩

theorem genOf_le_j3P {gs : List Table} (hgs : ∀ g ∈ gs, g ∈ allTbls) : genOf 6156 gs ≤ j3P := by
  rw [genOf, closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact tp_mem_j3P (hgs g (by simpa using hg))

theorem el_mem_subgroupOf {gs : List Table} (hgs : ∀ g ∈ gs, g ∈ allTbls) {g : Table}
    (hg : g ∈ gs) : el g ∈ (genOf 6156 gs).subgroupOf j3P := by
  rw [mem_subgroupOf, coe_el (tp_mem_j3P (hgs g hg))]
  exact tp_mem_genOf hg

theorem subgroupOf_le_of_gens {gs : List Table} (hgs : ∀ g ∈ gs, g ∈ allTbls)
    {H : Subgroup ↥j3P} (h : ∀ g ∈ gs, el g ∈ H) : (genOf 6156 gs).subgroupOf j3P ≤ H := by
  intro x hx
  rw [mem_subgroupOf] at hx
  have hle : genOf 6156 gs ≤ H.map j3P.subtype := by
    rw [genOf, closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ gs := by simpa using hg
    exact ⟨el g, h g hg', coe_el (tp_mem_j3P (hgs g hg'))⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  rwa [show y = x from Subtype.ext hyx] at hy

theorem card_subgroupOf_gens {gs : List Table} (hgs : ∀ g ∈ gs, g ∈ allTbls) {m : ℕ}
    (hm : enumOK 6156 3000 m gs = true) : Nat.card ((genOf 6156 gs).subgroupOf j3P) = m := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (genOf_le_j3P hgs)).toEquiv]
  exact (enumOK_spec hn6156 (fun g hg => (tbls_facts (hgs g hg)).1) hm).1

@[expose] noncomputable def Mk : Subgroup ↥j3P := (genOf 6156 mGens).subgroupOf j3P

@[expose] noncomputable def Nk : Subgroup ↥j3P := (genOf 6156 nGens).subgroupOf j3P

@[expose] noncomputable def Sk : Subgroup ↥j3P := (genOf 6156 sGens).subgroupOf j3P

theorem card_Mk : Nat.card Mk = 960 :=
  card_subgroupOf_gens (fun _ h => mem_allTbls_of_mGens h) k_enumM

theorem card_Nk : Nat.card Nk = 2880 :=
  card_subgroupOf_gens (fun _ h => mem_allTbls_of_nGens h) k_enumN

theorem card_Sk : Nat.card Sk = 128 :=
  card_subgroupOf_gens (fun _ h => mem_allTbls_of_sGens h) k_enumS

theorem eSub_le_Mk : eSub basisK ≤ Mk := by
  obtain ⟨-, hrep, -, -⟩ :=
    enumOK_spec hn6156 (fun g hg => (tbls_facts (mem_allTbls_of_mGens hg)).1) k_enumM
  have hv : ∀ i, vK i ∈ Mk := by
    intro i
    rw [Mk, mem_subgroupOf]
    have h1 := List.all_eq_true.mp k_le _ (eB_getD_mem i)
    obtain ⟨k, hk, hke⟩ := memT_spec (fun k hk => (hrep k hk).1) (rep_vK i) h1
    rw [hke]
    exact (hrep k hk).2
  rw [eSub_eq_closure, closure_le]
  rintro _ ⟨i, rfl⟩
  exact hv i

theorem Mk_le_f4Stab : Mk ≤ Duad.f4Stab basisK := by
  refine subgroupOf_le_of_gens (fun _ h => mem_allTbls_of_mGens h) fun g hg => ?_
  rcases eq_of_mem_mGens hg with h | h
  · rw [h]
    exact el_mem_f4Stab (mem_allTbls_of_mGens clsTbl5_mem) k_m₁ mMat_comm₁
  · rw [h]
    exact el_mem_f4Stab (mem_allTbls_of_mGens clsTbl6_mem) k_m₂ mMat_comm₂

theorem Mk_det (x : ↥Mk) :
    (Duad.f4Mat (eMat basisK ⟨x, (Mk_le_f4Stab x.2).1⟩)).det = 1 := by
  let D : ↥(Duad.f4Stab basisK) →* (Duad.F4)ˣ :=
    Matrix.GeneralLinearGroup.det.comp (Duad.f4Rep basisK)
  let K : Subgroup ↥j3P := D.ker.map (Duad.f4Stab basisK).subtype
  have hmemK : ∀ (y : ↥j3P) (hy : y ∈ Duad.f4Stab basisK),
      (Duad.f4Mat (eMat basisK ⟨y, hy.1⟩)).det = 1 → y ∈ K := by
    intro y hy hd
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    show D ⟨y, hy⟩ = 1
    apply Units.ext
    simpa [D, Duad.f4Rep_coe] using hd
  have hle : Mk ≤ K := by
    refine subgroupOf_le_of_gens (fun _ h => mem_allTbls_of_mGens h) fun g hg => ?_
    rcases eq_of_mem_mGens hg with h | h
    · rw [h]
      have hT := mem_allTbls_of_mGens clsTbl5_mem
      exact hmemK _ (el_mem_f4Stab hT k_m₁ mMat_comm₁) (by rw [eMat_el hT k_m₁]; exact mMat_det₁)
    · rw [h]
      have hT := mem_allTbls_of_mGens clsTbl6_mem
      exact hmemK _ (el_mem_f4Stab hT k_m₂ mMat_comm₂) (by rw [eMat_el hT k_m₂]; exact mMat_det₂)
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have h2 : (Duad.f4Mat (eMat basisK ⟨y, y.2.1⟩)).det = 1 := by
    have h3 := congrArg Units.val (show D y = 1 from hy)
    simpa [D, Duad.f4Rep_coe] using h3
  have hyx' : (⟨(y : ↥j3P), y.2.1⟩ : ↥(eNorm basisK)) = ⟨x, (Mk_le_f4Stab x.2).1⟩ :=
    Subtype.ext hyx
  rwa [hyx'] at h2

theorem exists_vK_of_mem {g : Table} (hg : g ∈ eB) :
    ∃ i : Fin 4, (vK i : Equiv.Perm (Fin 6156)) = tp 6156 g := by
  obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg
  have h4 : i < 4 := by simpa [eB] using hi
  refine ⟨⟨i, h4⟩, ?_⟩
  rw [coe_vK, ← hgi]
  congr 1
  exact List.getD_eq_getElem _ _ hi

theorem genOf_cGens_eq :
    genOf 6156 cGens = j3P ⊓ centralizer ({tp 6156 (j3CentTbl 9)} : Set (Equiv.Perm (Fin 6156))) := by
  obtain ⟨-, -, -, hrows, -⟩ := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  have h := (hrows _ List.mem_cons_self).2.2.2.1
  dsimp only [j3C] at h
  exact h

theorem cent_K : centralizer (eSub basisK : Set ↥j3P) ≤ eSub basisK := by
  have hcount : Nat.card ↥(genOf 6156 cGens ⊓
      centralizer (genOf 6156 eB : Set (Equiv.Perm (Fin 6156)))) = 16 := by
    rw [centCount_spec hn6156 (fun c hc => (tbls_facts (mem_allTbls_of_cGens hc)).1) k_enumC
      (fun g hg => (tbls_facts (mem_allTbls_of_eB hg)).1), k_cent]
  have hle : (centralizer (eSub basisK : Set ↥j3P)).map j3P.subtype ≤
      genOf 6156 cGens ⊓ centralizer (genOf 6156 eB : Set (Equiv.Perm (Fin 6156))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxv : ∀ i, (vK i : Equiv.Perm (Fin 6156)) * x = x * vK i := fun i =>
      congrArg Subtype.val (mem_centralizer_iff.mp hx (vK i) (mem_eSub basisK i))
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [genOf_cGens_eq]
      refine ⟨x.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have h0 := hxv 0
      rw [vK_zero] at h0
      exact h0.symm
    · rw [genOf, centralizer_closure, mem_centralizer_iff]
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨i, hi⟩ := exists_vK_of_mem (by simpa using hg)
      rw [← hi]
      exact hxv i
  have hcard : Nat.card (centralizer (eSub basisK : Set ↥j3P)) ≤ 16 := by
    rw [← Subgroup.card_map_of_injective (f := j3P.subtype) Subtype.val_injective, ← hcount]
    exact Subgroup.card_le_of_le hle
  have hEC : eSub basisK ≤ centralizer (eSub basisK : Set ↥j3P) := fun x hx =>
    mem_centralizer_iff.mpr fun y hy => eSub_comm basisK _ _ hy hx
  have heq := Subgroup.eq_of_le_of_card_ge hEC (by rw [card_eSub]; norm_num; exact hcard)
  exact heq.symm.le

theorem normPred_iff {T : Table} {g : Equiv.Perm (Fin 6156)} (hT : Rep 6156 T g) :
    normPred eB T = true ↔ g ∈ eNorm basisP := by
  have key : ∀ (b : Table) (x : Equiv.Perm (Fin 6156)), Rep 6156 b x →
      ((spanTabs 6156 eB).any (tblEq 6156 (conjT 6156 T (invT 6156 T) b)) = true ↔
        ∃ c, g * x * g⁻¹ = eElt (fun i => (vK i : Equiv.Perm (Fin 6156))) c) := fun b x hb =>
    mem_spanTabs_iff hn6156 forall₂_vK (f := tblEq 6156 (conjT 6156 T (invT 6156 T) b))
      (P := fun u => g * x * g⁻¹ = u)
      fun U u hU => CFSG.Sporadic.SmallOddCore.tblEq_iff_eq
        (rep_conjT hT (rep_invT_of_rep hn6156 hT) hb) hU
  show (eB.all fun b => (spanTabs 6156 eB).any
    (tblEq 6156 (conjT 6156 T (invT 6156 T) b))) = true ↔ _
  rw [List.all_eq_true, mem_eNorm_iff basisP]
  constructor
  · intro hall i
    obtain ⟨b, hb, hbi⟩ := exists_tab_of_mem forall₂_vK (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (key b _ hbi).mp (hall b hb)
  · intro hall b hb
    obtain ⟨x, hx, hbx⟩ := exists_rep_of_mem forall₂_vK hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (key b _ hbx).mpr (hall i)

theorem card_normC :
    Nat.card {x : genOf 6156 cGens // (x : Equiv.Perm (Fin 6156)) ∈ eNorm basisP} = 192 := by
  classical
  rw [card_genOf_subtype hn6156 (fun c hc => (tbls_facts (mem_allTbls_of_cGens hc)).1) k_enumC
    (cap := 3000) (f := normPred eB) (fun T g hT => normPred_iff hT)]
  exact k_norm

theorem mem_of_normCent {y : ↥j3P}
    (hy : y ∈ eNorm basisK ⊓ centralizer ({vK 0} : Set ↥j3P)) :
    (y : Equiv.Perm (Fin 6156)) ∈ genOf 6156 cGens ∧
      (y : Equiv.Perm (Fin 6156)) ∈ eNorm basisP := by
  refine ⟨?_, ?_⟩
  · rw [genOf_cGens_eq]
    refine ⟨y.2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h0 := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy.2)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, vK_zero] at h0
    exact h0
  · rw [mem_eNorm_iff basisP]
    intro i
    obtain ⟨c, hc⟩ := (mem_eNorm_iff basisK y).mp hy.1 i
    refine ⟨c, ?_⟩
    have h1 := congrArg Subtype.val hc
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_eElt] at h1
    exact h1

theorem card_normCent_le :
    Nat.card ↥(eNorm basisK ⊓ centralizer ({vK 0} : Set ↥j3P)) ≤ 192 := by
  rw [← card_normC]
  exact Nat.card_le_card_of_injective
    (fun y => ⟨⟨((y : ↥j3P) : Equiv.Perm (Fin 6156)), (mem_of_normCent y.2).1⟩,
      (mem_of_normCent y.2).2⟩)
    fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun z => (z.1 : Equiv.Perm (Fin 6156)))
      hab))

theorem card_eNorm_le : Nat.card (eNorm basisK) ≤ 2880 := by
  have hconj : ∀ g ∈ eNorm basisK,
      g * vK 0 * g⁻¹ ∈ (eSub basisK : Set ↥j3P) \ {1} := by
    intro g hg
    refine ⟨(mem_normalizer_iff.mp hg (vK 0)).mp (mem_eSub basisK 0), ?_⟩
    intro h1
    apply vK_zero_ne_one
    have h2 : g * vK 0 * g⁻¹ = 1 := h1
    calc vK 0 = g⁻¹ * (g * vK 0 * g⁻¹) * g := by group
      _ = 1 := by rw [h2]; group
  have h1 := card_le_of_conj_mem' (eNorm basisK) (vK 0) (Set.toFinite _) hconj
  have hE16 : (eSub basisK : Set ↥j3P).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact (card_eSub basisK).trans (by norm_num)
  have h15 : ((eSub basisK : Set ↥j3P) \ {1}).ncard = 15 := by
    rw [Set.ncard_diff_singleton_of_mem (one_mem (eSub basisK)), hE16]
  rw [h15] at h1
  have h2 := card_normCent_le
  calc Nat.card (eNorm basisK) ≤ 15 * Nat.card ↥(eNorm basisK ⊓
        centralizer ({vK 0} : Set ↥j3P)) := h1
    _ ≤ 15 * 192 := Nat.mul_le_mul_left _ h2
    _ = 2880 := by norm_num

theorem Nk_le_eNorm : Nk ≤ eNorm basisK := by
  refine subgroupOf_le_of_gens (fun _ h => mem_allTbls_of_nGens h) fun g hg => ?_
  rw [nGens_eq, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | hg
  · rcases eq_of_mem_mGens hg with h | h
    · rw [h]
      exact el_mem_eNorm (mem_allTbls_of_mGens clsTbl5_mem) k_m₁
    · rw [h]
      exact el_mem_eNorm (mem_allTbls_of_mGens clsTbl6_mem) k_m₂
  · rw [hg]
    exact el_mem_eNorm omT_mem k_om

theorem Nk_eq : Nk = eNorm basisK :=
  Subgroup.eq_of_le_of_card_ge Nk_le_eNorm (by rw [card_Nk]; exact card_eNorm_le)

theorem mem_nGens_of_mGens {g : Table} (hg : g ∈ mGens) : g ∈ nGens := by
  rw [nGens_eq]
  exact List.mem_append_left _ hg

theorem omT_mem_nGens : omT ∈ nGens := by
  rw [nGens_eq]
  exact List.mem_append_right _ List.mem_cons_self

theorem Mk_le_Nk : Mk ≤ Nk :=
  subgroupOf_le_of_gens (fun _ h => mem_allTbls_of_mGens h) fun _ hg =>
    el_mem_subgroupOf (fun _ h => mem_allTbls_of_nGens h) (mem_nGens_of_mGens hg)

theorem omT_mem_Nk : el omT ∈ Nk :=
  el_mem_subgroupOf (fun _ h => mem_allTbls_of_nGens h) omT_mem_nGens

theorem omT_mem_normalizer : el omT ∈ normalizer (Mk : Set ↥j3P) := by
  have hle := normOK_spec hn6156 (fun g hg => (tbls_facts (mem_allTbls_of_mGens hg)).1) k_enumM
    (cs := [omT]) (fun c hc => by
      rw [List.mem_singleton] at hc
      rw [hc]
      exact ⟨(tbls_facts omT_mem).1, invOK_invT_of_rep hn6156 (rep_tbl omT_mem)⟩) k_normOK
  have hom : tp 6156 omT ∈ normalizer (genOf 6156 mGens : Set (Equiv.Perm (Fin 6156))) :=
    hle (tp_mem_genOf List.mem_cons_self)
  rw [mem_normalizer_iff]
  intro x
  rw [Mk, mem_subgroupOf, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_el (tp_mem_j3P omT_mem)]
  exact mem_normalizer_iff.mp hom x

theorem Nk_le_normalizer : Nk ≤ normalizer (Mk : Set ↥j3P) := by
  refine subgroupOf_le_of_gens (fun _ h => mem_allTbls_of_nGens h) fun g hg => ?_
  rw [nGens_eq, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | hg
  · exact le_normalizer (el_mem_subgroupOf (fun _ h => mem_allTbls_of_mGens h) hg)
  · rw [hg]
    exact omT_mem_normalizer

theorem commutator_Nk_le : ⁅Nk, Nk⁆ ≤ Mk := by
  haveI hN : (Mk.subgroupOf Nk).Normal :=
    (normal_subgroupOf_iff_le_normalizer Mk_le_Nk).mpr Nk_le_normalizer
  set H : Subgroup ↥Nk := zpowers ⟨el omT, omT_mem_Nk⟩
  have htop : Mk.subgroupOf Nk ⊔ H = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hle : Nk ≤ (Mk.subgroupOf Nk ⊔ H).map Nk.subtype := by
      refine subgroupOf_le_of_gens (fun _ h => mem_allTbls_of_nGens h) fun g hg => ?_
      have hgN : el g ∈ Nk := el_mem_subgroupOf (fun _ h => mem_allTbls_of_nGens h) hg
      refine ⟨⟨el g, hgN⟩, ?_, rfl⟩
      rw [nGens_eq, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | hg
      · exact le_sup_left (a := Mk.subgroupOf Nk) (mem_subgroupOf.mpr
          (el_mem_subgroupOf (fun _ h => mem_allTbls_of_mGens h) hg))
      · have hH : (⟨el g, hgN⟩ : ↥Nk) ∈ H := by
          have he : (⟨el g, hgN⟩ : ↥Nk) = ⟨el omT, omT_mem_Nk⟩ := Subtype.ext (congrArg el hg)
          rw [he]
          exact mem_zpowers _
        exact le_sup_right (a := Mk.subgroupOf Nk) hH
    obtain ⟨w, hw, hwz⟩ := hle z.2
    rwa [show w = z from Subtype.ext hwz] at hw
  have hc := hN.commutator_le_of_self_sup_commutative_eq_top htop inferInstance
  rw [← Subgroup.map_subtype_commutator]
  calc (_root_.commutator ↥Nk).map Nk.subtype ≤ (Mk.subgroupOf Nk).map Nk.subtype :=
        Subgroup.map_mono hc
    _ = Mk ⊓ Nk := Subgroup.subgroupOf_map_subtype Mk Nk
    _ ≤ Mk := inf_le_left

theorem perf_K (K : Subgroup ↥j3P) (hKN : K ≤ normalizer (eSub basisK : Set ↥j3P))
    (hK : ⁅K, K⁆ = K) : K ≤ Mk := by
  have hKN' : K ≤ Nk := by rw [Nk_eq]; exact hKN
  rw [← hK]
  exact (Subgroup.commutator_mono hKN' hKN').trans commutator_Nk_le

theorem refData_K : RefData (eSub basisK) Mk where
  cent := cent_K
  comm := fun a ha b hb => eSub_comm basisK a b ha hb
  le := eSub_le_Mk
  norm := fun _ hx => (Mk_le_f4Stab hx).1
  perf := perf_K
  simple := duad_simple basisK eSub_le_Mk Mk_le_f4Stab Mk_det (inf_le_right.trans cent_K) card_Mk

theorem conclK_K (MK : Subgroup ↥j3P) : ConclK ↥j3P Mk (eSub basisK) MK :=
  conclK_of_duad basisK refData_K Mk_le_f4Stab Mk_det card_Mk MK

theorem invComm_iff {X : Table} {x : Equiv.Perm (Fin 6156)} (hX : Rep 6156 X x) {T : Table}
    {g : Equiv.Perm (Fin 6156)} (hT : Rep 6156 T g) :
    invComm X T = true ↔ g * g = 1 ∧ g * x = x * g := by
  rw [invComm, Bool.and_eq_true, CFSG.Sporadic.SmallOddCore.tblEq_iff_eq (Rep.compT hT hT)
    (Rep.idT hn6156), commTT_iff hT hX]

theorem cls_K (x : ↥j3P) (hxS : x ∈ Sk) (hx2 : x * x = 1)
    (h16 : 16 ≤ Nat.card {y : genOf 6156 sGens // (y : Equiv.Perm (Fin 6156)) * y = 1 ∧
      (y : Equiv.Perm (Fin 6156)) * x = x * y}) :
    x ∈ eSub basisK ∨ x ∈ (eSub basisK).map (MulAut.conj (el scT)).toMonoidHom := by
  classical
  have hsP := fun g hg => (tbls_facts (mem_allTbls_of_sGens (T := g) hg)).1
  obtain ⟨-, -, hcov, -⟩ := enumOK_spec hn6156 hsP k_enumS
  rw [Sk, mem_subgroupOf] at hxS
  obtain ⟨k, hk, hkx⟩ := hcov _ hxS
  have hcls := k_cls
  simp only [clsOK, Array.all_eq_true] at hcls
  have h := hcls k hk
  rw [getElem!_pos _ k hk] at hkx
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with ((h | h) | h) | h
  ·
    have h1 := (CFSG.Sporadic.SmallOddCore.tblEq_iff_eq (Rep.compT hkx hkx)
      (Rep.idT hn6156)).mpr (by rw [← Subgroup.coe_mul, hx2]; rfl)
    rw [h1] at h
    exact absurd h (by decide)
  ·
    left
    obtain ⟨c, hc⟩ := (mem_spanTabs_iff hn6156 forall₂_vK
      (f := tblEq 6156 (mulClosureH 6156 sGens.toArray 3000).1[k])
      (P := fun u => (x : Equiv.Perm (Fin 6156)) = u)
      fun U u hU => CFSG.Sporadic.SmallOddCore.tblEq_iff_eq hkx hU).mp h
    have hxc : x = eElt vK c := Subtype.ext (by rw [coe_eElt]; exact hc)
    rw [hxc]
    exact eElt_mem basisK c
  ·
    right
    have hs := rep_el scT_mem
    obtain ⟨c, hc⟩ := (mem_spanTabs_iff hn6156 forall₂_vK
      (f := fun u => tblEq 6156 (compT 6156 scT u)
        (compT 6156 (mulClosureH 6156 sGens.toArray 3000).1[k] scT))
      (P := fun u => (el scT : Equiv.Perm (Fin 6156)) * u = x * el scT)
      fun U u hU => CFSG.Sporadic.SmallOddCore.tblEq_iff_eq (Rep.compT hs hU)
        (Rep.compT hkx hs)).mp h
    refine ⟨eElt vK c, eElt_mem basisK c, ?_⟩
    show el scT * eElt vK c * (el scT)⁻¹ = x
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_eElt, hc, mul_inv_cancel_right]
  ·
    have hcount := card_genOf_subtype hn6156 hsP k_enumS (cap := 3000)
      (f := invComm (mulClosureH 6156 sGens.toArray 3000).1[k])
      (Q := fun y => y * y = 1 ∧ y * (x : Equiv.Perm (Fin 6156)) = x * y)
      fun T g hT => invComm_iff hkx hT
    rw [hcount] at h16
    exact absurd (decide_eq_true_eq.mp h) (not_lt.mpr h16)

theorem sixteen_le_count {W : Subgroup ↥j3P} (hW : IsElemAbelian 2 W) (hWS : W ≤ Sk)
    (h16 : 16 ≤ Nat.card W) {x : ↥j3P} (hx : x ∈ W) :
    16 ≤ Nat.card {y : genOf 6156 sGens // (y : Equiv.Perm (Fin 6156)) * y = 1 ∧
      (y : Equiv.Perm (Fin 6156)) * x = x * y} := by
  refine h16.trans (Nat.card_le_card_of_injective
    (fun w => ⟨⟨((w : ↥j3P) : Equiv.Perm (Fin 6156)), mem_subgroupOf.mp (hWS w.2)⟩,
      by
        show ((w : ↥j3P) : Equiv.Perm (Fin 6156)) * w = 1
        rw [← Subgroup.coe_mul, hW.mul_self_eq_one w.2]
        rfl,
      by
        show ((w : ↥j3P) : Equiv.Perm (Fin 6156)) * x = x * w
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hW.comm w.2 hx]⟩) ?_)
  intro a b hab
  exact Subtype.ext (Subtype.ext (congrArg (fun z => (z.1 : Equiv.Perm (Fin 6156))) hab))

theorem exists_conj_eq {L V MK : Subgroup ↥j3P} (h : KConfig ↥j3P L V MK) :
    ∃ g : ↥j3P, V = (eSub basisK).map (MulAut.conj g).toMonoidHom := by
  have h16 : 16 ≤ Nat.card V := sixteen_le_card (by rw [card_j3P]; norm_num) h
  have hS2 : IsPGroup 2 Sk := IsPGroup.of_card (n := 7) (by rw [card_Sk] <;> norm_num)
  obtain ⟨c, -, hc⟩ := CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5.exists_conj_le_of_odd_index
    (H := ⊤) (R := Sk) (E := V) le_top le_top hS2 h.elemAbelian.isPGroup (m := 392445)
    ⟨196222, by norm_num⟩ (by rw [Subgroup.card_top, card_j3P, card_Sk] <;> norm_num)
  set W := V.map (MulAut.conj c).toMonoidHom with hWdef
  have hWS : W ≤ Sk := by
    rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  have hWab : IsElemAbelian 2 W := h.elemAbelian.map _
  have hW16 : 16 ≤ Nat.card W := by
    rw [hWdef, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact h16
  have hcov : ∀ x ∈ W, x ∈ eSub basisK ∨ x ∈ (eSub basisK).map (MulAut.conj (el scT)).toMonoidHom :=
    fun x hx => cls_K x (hWS hx) (hWab.mul_self_eq_one hx) (sixteen_le_count hWab hWS hW16 hx)
  have hVW : V = W.map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [hWdef, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have hE16 : Nat.card (eSub basisK) = 16 := (card_eSub basisK).trans (by norm_num)
  rcases le_or_le_of_forall_mem_or hcov with hle | hle
  · have heq : W = eSub basisK :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hE16]; exact hW16)
    exact ⟨c⁻¹, by rw [hVW, heq]⟩
  · have heq : W = (eSub basisK).map (MulAut.conj (el scT)).toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective (MulAut.conj (el scT)).injective, hE16]
        exact hW16)
    exact ⟨c⁻¹ * el scT, by rw [hVW, heq, map_conj_map_conj]⟩

theorem conclK_K0 {L V MK : Subgroup ↥j3P} (h : KConfig ↥j3P L V MK) : ConclK ↥j3P L V MK := by
  obtain ⟨g, hV⟩ := exists_conj_eq h
  obtain ⟨-, hL⟩ := h.eq_of_refData_of_le (refData_K.map_mulEquiv (MulAut.conj g)) hV.ge
  exact h.conclK_of_eq_map (MulAut.conj g) hV hL fun MK' => conclK_K MK'

end Data

end J3Cls

end CFSG.SectionRank.QTK.Insp443

end
