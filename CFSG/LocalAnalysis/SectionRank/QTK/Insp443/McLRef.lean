module

public import Certificates.Certificate589305
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.CheckEnum
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.J3Ref
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Alt7Concl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.E8Concl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RankThreeConcl

public section

namespace CFSG.SectionRank.QTK.Insp443

namespace McLCls

open Subgroup CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Native CFSG.EvenSporadicStandard.M12Std.PropA.Native
open CFSG.Sporadic.SmallOddCore (genOf tp rep_tp commTT commTT_iff mcl_groupData tp_mem_genOf
  permOK mclSift mclCentTbl mclT0 mclCt mclT0_facts mcl_normalizing_model mclU mclOuterTbl selOK
  selOK_iff tblEq_idT_iff)
open CFSG.EvenSporadicStandard.M12Std.PropA (Enum enumP_spec)
open J3Cls (le_or_le_of_forall_mem_or map_conj_one card_le_of_conj_mem')

theorem map_map_mulEquiv {G : Type*} [Group G] (H : Subgroup G) (σ τ : G ≃* G) :
    (H.map σ.toMonoidHom).map τ.toMonoidHom = H.map (σ.trans τ).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem mem_357 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hd : q ∣ 40320) : q ∈ [3, 5, 7] := by
  have h : (40320 : ℕ) = 2 ^ 7 * (3 ^ 2 * (5 * 7)) := by norm_num
  rw [h] at hd
  rcases (Nat.Prime.dvd_mul hq).mp hd with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h1)) hq2
  rcases (Nat.Prime.dvd_mul hq).mp h1 with h2 | h2
  · rw [(Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h2)]
    simp
  rcases (Nat.Prime.dvd_mul hq).mp h2 with h3 | h3
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5)).mp h3]
    simp
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)).mp h3]
    simp

theorem mem_allTbls_of_eB {T : Table} (h : T ∈ eB) : T ∈ allTbls := by
  show T ∈ eB ++ [gT] ++ mGens ++ sGens ++ cGens
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ h)))

theorem gT_mem : gT ∈ allTbls := by
  show gT ∈ eB ++ [gT] ++ mGens ++ sGens ++ cGens
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ List.mem_cons_self)))

theorem mem_allTbls_of_mGens {T : Table} (h : T ∈ mGens) : T ∈ allTbls := by
  show T ∈ eB ++ [gT] ++ mGens ++ sGens ++ cGens
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))

theorem mem_allTbls_of_sGens {T : Table} (h : T ∈ sGens) : T ∈ allTbls := by
  show T ∈ eB ++ [gT] ++ mGens ++ sGens ++ cGens
  exact List.mem_append_left _ (List.mem_append_right _ h)

theorem eB_getD_mem (i : Fin 4) : eB.getD i (idT 275) ∈ eB := by
  rw [List.getD_eq_getElem _ _ (by show (i : ℕ) < 4; exact i.2)]
  exact List.getElem_mem _

@[expose] noncomputable def el (T : Table) : ↥mclP := by
  classical
  exact if h : tp 275 T ∈ mclP then ⟨tp 275 T, h⟩ else 1

theorem coe_el {T : Table} (h : tp 275 T ∈ mclP) : (el T : Equiv.Perm (Fin 275)) = tp 275 T := by
  unfold el
  rw [dif_pos h]

@[expose] noncomputable def vK (i : Fin 4) : ↥mclP := el (eB.getD i (idT 275))

@[expose] noncomputable def Mk : Subgroup ↥mclP := (genOf 275 mGens).subgroupOf mclP

@[expose] noncomputable def Sk : Subgroup ↥mclP := (genOf 275 sGens).subgroupOf mclP

@[expose] def invCommSet (x : Equiv.Perm (Fin 275)) : Set (Equiv.Perm (Fin 275)) :=
  {g | g ∈ (genOf 275 sGens : Set (Equiv.Perm (Fin 275))) ∧ (g * g = 1 ∧ g * x = x * g)}

@[expose] def oSet : Finset (Fin 275) := Finset.univ.filter fun i => i.val ∈ oPts

theorem mem_oSet (i : Fin 275) : i ∈ oSet ↔ i.val ∈ oPts := by
  simp [oSet]

theorem card_oSet : oSet.card = 7 := by decide +kernel

section Data

theorem k_facts : Facts := Certificates.certificate589305

theorem tp_mem_mclP {T : Table} (hT : T ∈ allTbls) : tp 275 T ∈ mclP :=
  (k_facts.tbls.1 T hT).2

theorem coe_vK (i : Fin 4) :
    (vK i : Equiv.Perm (Fin 275)) = tp 275 (eB.getD i (idT 275)) :=
  coe_el (tp_mem_mclP (mem_allTbls_of_eB (eB_getD_mem i)))

theorem vK_eq : (fun i => (vK i : Equiv.Perm (Fin 275))) = F.v := funext coe_vK

theorem basisP : EBasis fun i => (vK i : Equiv.Perm (Fin 275)) := by
  rw [vK_eq]
  exact k_facts.basis

theorem eSubP_eq : eSub basisP = F.W := by
  rw [eSub_eq_closure, vK_eq]

theorem basisK : EBasis vK :=
  EBasis.of_map (f := mclP.subtype) Subtype.val_injective basisP

theorem coe_eElt (c : Fin 4 → ZMod 2) :
    ((eElt vK c : ↥mclP) : Equiv.Perm (Fin 275)) =
      eElt (fun i => (vK i : Equiv.Perm (Fin 275))) c :=
  map_eElt mclP.subtype c

theorem eB_eq : eB = [mclCentTbl 4, clsTbl 0, clsTbl 1, clsTbl 2] := rfl

theorem vK_zero : (vK 0 : Equiv.Perm (Fin 275)) = tp 275 (mclCentTbl 4) := by
  rw [coe_vK, eB_eq]
  simp only [Fin.val_zero, List.getD_cons_zero]

theorem vK_zero_ne_one : vK 0 ≠ 1 := by
  intro h
  have h1 : eElt vK (Pi.single 0 1) = 1 := by rw [eElt_single]; exact h
  have h2 := basisK.ne_one _ h1
  have h3 := congrFun h2 0
  simp at h3

theorem coe_mem_eSub {y : ↥mclP} (hy : y ∈ eSub basisK) :
    (y : Equiv.Perm (Fin 275)) ∈ eSub basisP := by
  obtain ⟨c, rfl⟩ := (mem_eSub_iff basisK y).mp hy
  rw [coe_eElt]
  exact eElt_mem basisP c

theorem mem_eNorm_of_coe {y : ↥mclP} (hy : (y : Equiv.Perm (Fin 275)) ∈ eNorm basisP) :
    y ∈ eNorm basisK := by
  rw [mem_eNorm_iff basisK]
  intro i
  obtain ⟨c, hc⟩ := (mem_eNorm_iff basisP _).mp hy i
  refine ⟨c, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_eElt]
  exact hc

theorem genOf_le_mclP {gs : List Table} (hgs : ∀ g ∈ gs, g ∈ allTbls) : genOf 275 gs ≤ mclP := by
  rw [genOf, closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact tp_mem_mclP (hgs g (by simpa using hg))

theorem card_Mk : Nat.card Mk = 40320 := by
  rw [Mk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (genOf_le_mclP fun _ h => mem_allTbls_of_mGens h)).toEquiv]
  exact k_facts.mOne.2.2.1

theorem card_Sk : Nat.card Sk = 128 := by
  rw [Sk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (genOf_le_mclP fun _ h => mem_allTbls_of_sGens h)).toEquiv]
  exact k_facts.sTwo.2

theorem mem_eSub_of_coe {y : ↥mclP} (hy : (y : Equiv.Perm (Fin 275)) ∈ F.W) :
    y ∈ eSub basisK := by
  rw [← eSubP_eq] at hy
  obtain ⟨c, hc⟩ := (mem_eSub_iff basisP _).mp hy
  have hyc : y = eElt vK c := Subtype.ext (by rw [coe_eElt]; exact hc.symm)
  rw [hyc]
  exact eElt_mem basisK c

theorem eSub_le_Mk : eSub basisK ≤ Mk := by
  intro x hx
  rw [Mk, mem_subgroupOf]
  have h := coe_mem_eSub hx
  rw [eSubP_eq] at h
  exact k_facts.mOne.1 h

theorem Mk_le_eNorm : Mk ≤ eNorm basisK := by
  intro x hx
  apply mem_eNorm_of_coe
  have h := k_facts.mOne.2.1 (mem_subgroupOf.mp hx)
  change (x : Equiv.Perm (Fin 275)) ∈ normalizer ((eSub basisP : Subgroup _) : Set _)
  rw [eSubP_eq]
  exact h

theorem genOf_cGens_eq : genOf 275 cGens = mclCt := by
  have h := mclT0_facts.2.2.1
  exact h

theorem cent_K : centralizer (eSub basisK : Set ↥mclP) ≤ eSub basisK := by
  intro x hx
  apply mem_eSub_of_coe
  refine k_facts.cent.1 _ x.2 fun w hw => ?_
  rw [← eSubP_eq] at hw
  obtain ⟨c, rfl⟩ := (mem_eSub_iff basisP w).mp hw
  have h := congrArg Subtype.val (mem_centralizer_iff.mp hx (eElt vK c) (eElt_mem basisK c))
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_eElt] at h
  exact h.symm

theorem mem_of_normCent {y : ↥mclP}
    (hy : y ∈ eNorm basisK ⊓ centralizer ({vK 0} : Set ↥mclP)) :
    (y : Equiv.Perm (Fin 275)) ∈ genOf 275 cGens ∧
      (y : Equiv.Perm (Fin 275)) ∈ eNorm basisP := by
  rw [Subgroup.mem_inf] at hy
  refine ⟨?_, ?_⟩
  · rw [genOf_cGens_eq, Subgroup.mem_inf]
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
    Nat.card ↥(eNorm basisK ⊓ centralizer ({vK 0} : Set ↥mclP)) ≤ 2688 := by
  have hmem : ∀ y : ↥(eNorm basisK ⊓ centralizer ({vK 0} : Set ↥mclP)),
      ((y : ↥mclP) : Equiv.Perm (Fin 275)) ∈
        F.H ⊓ normalizer (F.W : Set (Equiv.Perm (Fin 275))) := by
    intro y
    obtain ⟨h1, h2⟩ := mem_of_normCent y.2
    rw [genOf_cGens_eq] at h1
    have h2' : ((y : ↥mclP) : Equiv.Perm (Fin 275)) ∈
        normalizer ((eSub basisP : Subgroup _) : Set (Equiv.Perm (Fin 275))) := h2
    rw [eSubP_eq] at h2'
    exact Subgroup.mem_inf.mpr ⟨h1, h2'⟩
  refine le_trans (Nat.card_le_card_of_injective
    (fun y => (⟨((y : ↥mclP) : Equiv.Perm (Fin 275)), hmem y⟩ :
      ↥(F.H ⊓ normalizer (F.W : Set (Equiv.Perm (Fin 275)))))) ?_) k_facts.cent.2
  intro a b hab
  exact Subtype.ext (Subtype.ext (congrArg (fun z => (z.1 : Equiv.Perm (Fin 275))) hab))

theorem card_eNorm_le : Nat.card (eNorm basisK) ≤ 40320 := by
  have hconj : ∀ g ∈ eNorm basisK,
      g * vK 0 * g⁻¹ ∈ (eSub basisK : Set ↥mclP) \ {1} := by
    intro g hg
    refine ⟨(mem_normalizer_iff.mp hg (vK 0)).mp (mem_eSub basisK 0), ?_⟩
    intro h1
    apply vK_zero_ne_one
    have h2 : g * vK 0 * g⁻¹ = 1 := h1
    calc vK 0 = g⁻¹ * (g * vK 0 * g⁻¹) * g := by group
      _ = 1 := by rw [h2]; group
  have h1 := card_le_of_conj_mem' (eNorm basisK) (vK 0) (Set.toFinite _) hconj
  have hE16 : (eSub basisK : Set ↥mclP).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact (card_eSub basisK).trans (by norm_num)
  have h15 : ((eSub basisK : Set ↥mclP) \ {1}).ncard = 15 := by
    rw [Set.ncard_diff_singleton_of_mem (one_mem (eSub basisK)), hE16]
  rw [h15] at h1
  have h2 := card_normCent_le
  calc Nat.card (eNorm basisK) ≤ 15 * Nat.card ↥(eNorm basisK ⊓
        centralizer ({vK 0} : Set ↥mclP)) := h1
    _ ≤ 15 * 2688 := Nat.mul_le_mul_left _ h2
    _ = 40320 := by norm_num

theorem Mk_eq : Mk = eNorm basisK :=
  Subgroup.eq_of_le_of_card_ge Mk_le_eNorm (by rw [card_Mk]; exact card_eNorm_le)

theorem oSet_eq : oSet = F.O := rfl

theorem genOf_mGens_le_setStab : genOf 275 mGens ≤ setStab oSet := by
  rw [oSet_eq]
  exact k_facts.mOne.2.2.2.1

theorem Mk_le_setStab (x : ↥Mk) :
    (mclP.subtype.comp Mk.subtype) x ∈ setStab oSet :=
  genOf_mGens_le_setStab (mem_subgroupOf.mp x.2)

@[expose] noncomputable def mAct : ↥Mk →* Equiv.Perm (Fin 7) :=
  (setAct oSet card_oSet).comp ((mclP.subtype.comp Mk.subtype).codRestrict _ Mk_le_setStab)

theorem mAct_eq_one_iff (x : ↥Mk) :
    mAct x = 1 ↔ ∀ i : Fin 275, i.val ∈ oPts → ((x : ↥mclP) : Equiv.Perm (Fin 275)) i = i := by
  rw [mAct, MonoidHom.comp_apply, setAct_eq_one_iff]
  simp only [mem_oSet]
  rfl

theorem fix_W {y : ↥mclP} (hy : y ∈ eSub basisK) (i : Fin 275) (hi : i.val ∈ oPts) :
    (y : Equiv.Perm (Fin 275)) i = i := by
  have h := coe_mem_eSub hy
  rw [eSubP_eq] at h
  exact k_facts.mOne.2.2.2.2.1 _ h i (by rw [← oSet_eq, mem_oSet]; exact hi)

theorem ker_mAct : mAct.ker = (eSub basisK).subgroupOf Mk := by
  classical
  have hle : (eSub basisK).subgroupOf Mk ≤ mAct.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, mAct_eq_one_iff]
    intro i hi
    rw [mem_subgroupOf] at hx
    exact fix_W hx i hi
  refine le_antisymm (fun x hx => ?_) hle
  rw [mem_subgroupOf]
  apply mem_eSub_of_coe
  refine k_facts.mOne.2.2.2.2.2 _ (mem_subgroupOf.mp (x : ↥Mk).2) fun i hi => ?_
  rw [← oSet_eq, mem_oSet] at hi
  exact (mAct_eq_one_iff x).mp (MonoidHom.mem_ker.mp hx) i hi

theorem range_mAct : mAct.range = alternatingGroup (Fin 7) := by
  apply A7.eq_alt7_of_card
  have h := card_range_eq eSub_le_Mk mAct ker_mAct
  rw [card_eSub, card_Mk] at h
  omega

@[expose] noncomputable def mAlt : ↥Mk →* ↥(alternatingGroup (Fin 7)) :=
  mAct.codRestrict _ fun x => by rw [← range_mAct]; exact ⟨x, rfl⟩

theorem mAlt_surjective : Function.Surjective mAlt := by
  intro σ
  have hσ : (σ : Equiv.Perm (Fin 7)) ∈ mAct.range := by rw [range_mAct]; exact σ.2
  obtain ⟨x, hx⟩ := hσ
  exact ⟨x, Subtype.ext hx⟩

theorem ker_mAlt : mAlt.ker = (eSub basisK).subgroupOf Mk := by
  rw [mAlt, MonoidHom.ker_codRestrict, ker_mAct]

theorem refData_K : RefData (eSub basisK) Mk where
  cent := cent_K
  comm := fun a ha b hb => eSub_comm basisK a b ha hb
  le := eSub_le_Mk
  norm := Mk_le_eNorm
  perf := fun _ hK _ => Mk_eq ▸ hK
  simple := by
    have := A7.alt7_simple
    exact simple_of_surj mAlt mAlt_surjective ker_mAlt

theorem conclK_K (MK : Subgroup ↥mclP) : ConclK ↥mclP Mk (eSub basisK) MK :=
  conclK_of_alt7 refData_K mAlt mAlt_surjective ker_mAlt MK

@[expose] noncomputable def sigU : ↥mclP ≃* ↥mclP :=
  ((MulAut.conj mclU).subgroupMap mclP).trans
    (MulEquiv.subgroupCongr mcl_normalizing_model.2.2.2.1)

theorem coe_sigU (y : ↥mclP) :
    ((sigU y : ↥mclP) : Equiv.Perm (Fin 275)) = mclU * y * mclU⁻¹ :=
  rfl

@[expose] noncomputable def sig : ↥mclP ≃* ↥mclP := sigU.trans (MulAut.conj (el gT))

theorem coe_sig (y : ↥mclP) :
    ((sig y : ↥mclP) : Equiv.Perm (Fin 275)) =
      (tp 275 gT * mclU) * y * (tp 275 gT * mclU)⁻¹ := by
  have h1 : sig y = el gT * sigU y * (el gT)⁻¹ := rfl
  rw [h1, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_sigU,
    coe_el (tp_mem_mclP gT_mem)]
  group

theorem cls_K (x : ↥mclP) (hxS : x ∈ Sk) (hx2 : x * x = 1)
    (h16 : 16 ≤ Nat.card ↥(invCommSet (x : Equiv.Perm (Fin 275)))) :
    x ∈ eSub basisK ∨ x ∈ (eSub basisK).map sig.toMonoidHom := by
  rw [Sk, mem_subgroupOf] at hxS
  have hx2' : (x : Equiv.Perm (Fin 275)) * x = 1 := by
    rw [← Subgroup.coe_mul, hx2]
    rfl
  rcases k_facts.cls _ hxS hx2' with h | ⟨w, hw, hwx⟩ | h
  ·
    exact Or.inl (mem_eSub_of_coe h)
  ·
    right
    rw [← eSubP_eq] at hw
    obtain ⟨c, rfl⟩ := (mem_eSub_iff basisP w).mp hw
    refine ⟨eElt vK c, eElt_mem basisK c, ?_⟩
    change sig (eElt vK c) = x
    apply Subtype.ext
    rw [coe_sig, coe_eElt]
    exact hwx
  ·
    have e : invCommSet (x : Equiv.Perm (Fin 275)) =
        {g : Equiv.Perm (Fin 275) | g ∈ F.S ∧ g * g = 1 ∧ g * x = x * g} := rfl
    rw [e] at h16
    exact absurd h (not_lt.mpr h16)

theorem sixteen_le_count {W : Subgroup ↥mclP} (hW : IsElemAbelian 2 W) (hWS : W ≤ Sk)
    (h16 : 16 ≤ Nat.card W) {x : ↥mclP} (hx : x ∈ W) :
    16 ≤ Nat.card ↥(invCommSet (x : Equiv.Perm (Fin 275))) := by
  refine h16.trans (Nat.card_le_card_of_injective
    (fun w => ⟨((w : ↥mclP) : Equiv.Perm (Fin 275)), mem_subgroupOf.mp (hWS w.2),
      by
        show ((w : ↥mclP) : Equiv.Perm (Fin 275)) * w = 1
        rw [← Subgroup.coe_mul, hW.mul_self_eq_one w.2]
        rfl,
      by
        show ((w : ↥mclP) : Equiv.Perm (Fin 275)) * x = x * w
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hW.comm w.2 hx]⟩) ?_)
  intro a b hab
  exact Subtype.ext (Subtype.ext (congrArg (fun z => (z.1 : Equiv.Perm (Fin 275))) hab))

theorem exists_aut_eq {V : Subgroup ↥mclP} (hV : IsElemAbelian 2 V) (h16 : 16 ≤ Nat.card V) :
    ∃ τ : ↥mclP ≃* ↥mclP, V = (eSub basisK).map τ.toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 Sk := IsPGroup.of_card (n := 7) (by rw [card_Sk] <;> norm_num)
  obtain ⟨c, -, hc⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5.exists_conj_le_of_odd_index
      (H := ⊤) (R := Sk) (E := V) le_top le_top hS2 hV.isPGroup (m := 7016625)
      ⟨3508312, by norm_num⟩ (by rw [Subgroup.card_top, card_mclP, card_Sk] <;> norm_num)
  set W := V.map (MulAut.conj c).toMonoidHom with hWdef
  have hWS : W ≤ Sk := by
    rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  have hWab : IsElemAbelian 2 W := hV.map _
  have hW16 : 16 ≤ Nat.card W := by
    rw [hWdef, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact h16
  have hcov : ∀ x ∈ W, x ∈ eSub basisK ∨ x ∈ (eSub basisK).map sig.toMonoidHom :=
    fun x hx => cls_K x (hWS hx) (hWab.mul_self_eq_one hx) (sixteen_le_count hWab hWS hW16 hx)
  have hVW : V = W.map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [hWdef, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have hE16 : Nat.card (eSub basisK) = 16 := (card_eSub basisK).trans (by norm_num)
  rcases le_or_le_of_forall_mem_or hcov with hle | hle
  · have heq : W = eSub basisK :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hE16]; exact hW16)
    exact ⟨MulAut.conj c⁻¹, by rw [hVW, heq]⟩
  · have heq : W = (eSub basisK).map sig.toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective sig.injective, hE16]
        exact hW16)
    exact ⟨sig.trans (MulAut.conj c⁻¹), by rw [hVW, heq, map_map_mulEquiv]⟩

theorem e8_perm {x a b : Equiv.Perm (Fin 275)} (hx : x ∈ mclCt) (ha : a ∈ mclCt) (hb : b ∈ mclCt)
    (hx1 : x ≠ 1) (hxp : ∃ p ∈ [3, 5, 7], x ^ p = 1) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hat : a ≠ mclT0) (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbt : b ≠ mclT0) (hxa : x * a = a * x)
    (hxb : x * b = b * x) (hab : a * b = b * a) : b = a ∨ b = a * mclT0 :=
  k_facts.e8 x hx a ha b hb hx1 hxp ha2 ha1 hat hb2 hb1 hbt hxa hxb hab

theorem false_of_mem_cent {W : Subgroup ↥mclP} (hW : IsElemAbelian 2 W) (h8 : Nat.card W = 8)
    {x : ↥mclP} (hx : x ∈ centralizer (W : Set ↥mclP)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hxq : orderOf x = q) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hWne : W ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at h8
    norm_num at h8
  obtain ⟨⟨τ, hτW⟩, hτ1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
  have hτ1 : τ ≠ 1 := fun h => hτ1' (Subtype.ext h)
  have hτ2 : (τ : Equiv.Perm (Fin 275)) ^ 2 = 1 := by
    rw [pow_two, ← Subgroup.coe_mul, hW.mul_self_eq_one hτW]
    rfl
  have hτo : orderOf (τ : Equiv.Perm (Fin 275)) = 2 :=
    orderOf_eq_prime hτ2 fun h => hτ1 (Subtype.ext h)
  obtain ⟨g, hg, hτg⟩ := mclT0_facts.2.2.2.2 _ τ.2 hτo
  let ι : ↥mclP →* Equiv.Perm (Fin 275) := (MulAut.conj g⁻¹).toMonoidHom.comp mclP.subtype
  have hι : Function.Injective ι := (MulAut.conj g⁻¹).injective.comp Subtype.val_injective
  have hιapp : ∀ y : ↥mclP, ι y = g⁻¹ * y * g := fun y => by
    show (MulAut.conj g⁻¹) (y : Equiv.Perm (Fin 275)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hιτ : ι τ = mclT0 := by
    rw [hιapp, hτg]
    group
  have hιC : ∀ y : ↥mclP, y * τ = τ * y → ι y ∈ mclCt := fun y hy => by
    rw [Subgroup.mem_inf]
    refine ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
    · rw [hιapp]
      exact mclP.mul_mem (mclP.mul_mem (mclP.inv_mem hg) y.2) hg
    · rw [← hιτ, ← map_mul, ← map_mul, hy]
  have hWn : (W : Set ↥mclP).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact h8
  have h2 : ({1, τ} : Set ↥mclP).ncard < (W : Set ↥mclP).ncard := by
    have e1 := Set.ncard_insert_le (1 : ↥mclP) ({τ} : Set ↥mclP)
    rw [Set.ncard_singleton] at e1
    omega
  obtain ⟨a, haW, ha⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ha
  have h4 : ({1, τ, a, a * τ} : Set ↥mclP).ncard < (W : Set ↥mclP).ncard := by
    have e1 := Set.ncard_insert_le (1 : ↥mclP) ({τ, a, a * τ} : Set ↥mclP)
    have e2 := Set.ncard_insert_le τ ({a, a * τ} : Set ↥mclP)
    have e3 := Set.ncard_insert_le a ({a * τ} : Set ↥mclP)
    have e4 := Set.ncard_singleton (a * τ)
    omega
  obtain ⟨b, hbW, hb⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h4
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
  have hxW : ∀ y ∈ W, x * y = y * x := fun y hy => (mem_centralizer_iff.mp hx y hy).symm
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxq
    exact hq.ne_one hxq.symm
  have hxq' : x ^ q = 1 := hxq ▸ pow_orderOf_eq_one x
  have hιx : ι x ∈ mclCt := hιC x (hxW τ hτW)
  have hιx1 : ι x ≠ 1 := (map_ne_one_iff ι hι).mpr hx1
  have hιxq : ι x ^ q = 1 := by rw [← map_pow, hxq', map_one]
  have hq357 : q ∈ [3, 5, 7] := by
    have hord : orderOf (⟨ι x, hιx⟩ : ↥mclCt) = q := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hιxq hιx1
    have hdvd : q ∣ 40320 := by
      rw [← mclT0_facts.2.2.2.1, ← hord]
      exact orderOf_dvd_natCard _
    exact mem_357 hq hq2 hdvd
  have hιsq : ∀ y ∈ W, ι y * ι y = 1 := fun y hy => by
    rw [← map_mul, hW.mul_self_eq_one hy, map_one]
  have hιne1 : ∀ {y : ↥mclP}, y ≠ 1 → ι y ≠ 1 := fun hy => (map_ne_one_iff ι hι).mpr hy
  have hιneT : ∀ {y : ↥mclP}, y ≠ τ → ι y ≠ mclT0 := fun hy h => hy (hι (h.trans hιτ.symm))
  have hcomm : ∀ {y z : ↥mclP}, y * z = z * y → ι y * ι z = ι z * ι y := fun h => by
    rw [← map_mul, ← map_mul, h]
  rcases e8_perm hιx (hιC a (hW.comm haW hτW)) (hιC b (hW.comm hbW hτW)) hιx1 ⟨q, hq357, hιxq⟩
      (hιsq a haW) (hιne1 ha.1) (hιneT ha.2) (hιsq b hbW) (hιne1 hb.1) (hιneT hb.2.1)
      (hcomm (hxW a haW)) (hcomm (hxW b hbW)) (hcomm (hW.comm haW hbW)) with h | h
  · exact hb.2.2.1 (hι h)
  · rw [← hιτ, ← map_mul] at h
    exact hb.2.2.2 (hι h)

theorem isPGroup_centralizer_of_card_eight {W : Subgroup ↥mclP} (hW : IsElemAbelian 2 W)
    (h8 : Nat.card W = 8) : IsPGroup 2 ↥(centralizer (W : Set ↥mclP)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card
    (n := (Nat.card ↥(centralizer (W : Set ↥mclP))).primeFactorsList.length) ?_
  refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqd => ?_
  by_contra hq2
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqd
  exact false_of_mem_cent hW h8 x.2 hq hq2 (by rw [Subgroup.orderOf_coe]; exact hx)

theorem conclK_K0 {L V MK : Subgroup ↥mclP} (h : KConfig ↥mclP L V MK) : ConclK ↥mclP L V MK := by
  by_cases h16 : 16 ≤ Nat.card V
  · obtain ⟨τ, hV⟩ := exists_aut_eq h.elemAbelian h16
    obtain ⟨-, hL⟩ := h.eq_of_refData_of_le (refData_K.map_mulEquiv τ) hV.ge
    exact h.conclK_of_eq_map τ hV hL fun MK' => conclK_K MK'
  · push Not at h16
    have h8 := h.eight_le_card
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.elemAbelian.isPGroup
    have hk4 : k < 4 := by
      by_contra hk4
      push Not at hk4
      have h1 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
      rw [hk] at h16
      norm_num at h1
      omega
    have hV8 : Nat.card V = 8 := by
      rw [hk] at h8 ⊢
      interval_cases k
      · exact absurd h8 (by norm_num)
      · exact absurd h8 (by norm_num)
      · exact absurd h8 (by norm_num)
      · norm_num
    letI : IsMulCommutative ↥V := h.elemAbelian.1
    have hE2 : CFSG.Quasithin.IsE2 3 ↥V :=
      CFSG.Quasithin.KGC31.Ru.isE2_of_card' (n := 3)
        (fun x y => mul_comm' x y)
        (fun x => by
          apply Subtype.ext
          have hx : (x : ↥mclP) * (x : ↥mclP) = 1 := by
            simpa [pow_two] using h.elemAbelian.2 x x.2
          simpa using hx)
        (by rw [hV8]; norm_num)
    obtain ⟨v, hv, hveq⟩ := CFSG.Quasithin.H13.Ch4.exists_eBasis_of_isE2 hE2
    have hC2 := isPGroup_centralizer_of_card_eight h.elemAbelian hV8
    rw [← hveq] at h hC2
    exact hveq ▸ KConfig.conclK_of_e8 hv h hC2

end Data

end McLCls

end CFSG.SectionRank.QTK.Insp443

end
