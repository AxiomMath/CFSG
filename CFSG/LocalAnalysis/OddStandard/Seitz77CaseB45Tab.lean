module

public import CFSG.GH74.KGroups.Generic6
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Perm
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Fin
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Model

public section

namespace CFSG.OddStandard.Seitz77.CaseB45

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Sporadic.Schreier Certificates.Seitz77CaseB45
  CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

structure TablesFacts : Prop where
  enumT : enumOK 42 tlGens etl = true
  sizeT : etl.tabs.size = 256
  enumU : enumOK 42 uGens eu = true
  sizeU : eu.tabs.size = 64
  U_le_T : ∀ k, k < 64 → etl.tabs.contains eu.tabs[k]! = true
  mul_lt : ∀ i j, i < 256 → j < 256 → mtF i j < 256
  mul_tab : ∀ i j, i < 256 → j < 256 → etl.tabs[mtF i j]! = comp 42 etl.tabs[i]! etl.tabs[j]!
  inv_lt : ∀ i, i < 256 → invArr[i]! < 256
  inv_mul : ∀ i, i < 256 → mtF i invArr[i]! = 0
  lab_lt : ∀ i, i < 256 → labF i < 4
  lab_zero : labF 0 = 0
  lab_eq : ∀ i j, i < 256 → j < 256 → (labF i = labF j ↔ isUF (mtF invArr[i]! j) = true)
  lab_hom : ∀ i j, i < 256 → j < 256 → labF (mtF i j) = laddF (labF i) (labF j)
  tab0 : etl.tabs[0]! = idTab 42

theorem tablesFacts_of_ok (h : tablesOK = true) : TablesFacts := by
  unfold tablesOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_, h13, ?_, ?_, ?_⟩
  · intro i j hi hj
    simpa using (h7 i hi j hj).1
  · intro i j hi hj
    simpa using (h7 i hi j hj).2
  · intro i hi
    simpa using (h8 i hi).1
  · intro i hi
    simpa using (h8 i hi).2
  · intro i hi
    simpa using h11 i hi
  · intro i j hi hj
    have := h14 i hi j hj
    simp only [Bool.beq_eq_decide_eq] at this
    rw [← this]
    simp
  · intro i j hi hj
    simpa using h15 i hi j hj
  · unfold enumOK at h1
    exact (treeOK_spec h1).2.1

theorem tlGens_size : tlGens.size = 3 := by decide

theorem uGens_size : uGens.size = 4 := by decide

theorem TablesFacts.enumerates_T (F : TablesFacts) : Enumerates TLsub etl.tabs.toList := by
  refine enumerates_closure (gens := tlGens) (A := {tl0, tl1, tl2}) ?_ ?_ F.enumT
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨0, by rw [tlGens_size]; norm_num, tabRep_tl0⟩
    · exact ⟨1, by rw [tlGens_size]; norm_num, tabRep_tl1⟩
    · exact ⟨2, by rw [tlGens_size]; norm_num, tabRep_tl2⟩
  · intro j hj
    rw [tlGens_size] at hj
    interval_cases j
    · exact ⟨tl0, by simp, tabRep_tl0⟩
    · exact ⟨tl1, by simp, tabRep_tl1⟩
    · exact ⟨tl2, by simp, tabRep_tl2⟩

theorem TablesFacts.enumerates_U (F : TablesFacts) : Enumerates Usub0 eu.tabs.toList := by
  refine enumerates_closure (gens := uGens) (A := {u0, u1, u2, u3}) ?_ ?_ F.enumU
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨0, by rw [uGens_size]; norm_num, tabRep_u0⟩
    · exact ⟨1, by rw [uGens_size]; norm_num, tabRep_u1⟩
    · exact ⟨2, by rw [uGens_size]; norm_num, tabRep_u2⟩
    · exact ⟨3, by rw [uGens_size]; norm_num, tabRep_u3⟩
  · intro j hj
    rw [uGens_size] at hj
    interval_cases j
    · exact ⟨u0, by simp, tabRep_u0⟩
    · exact ⟨u1, by simp, tabRep_u1⟩
    · exact ⟨u2, by simp, tabRep_u2⟩
    · exact ⟨u3, by simp, tabRep_u3⟩

theorem TablesFacts.card_T (F : TablesFacts) : Nat.card TLsub = 256 := by
  rw [F.enumerates_T.card]
  simpa using F.sizeT

theorem TablesFacts.card_U (F : TablesFacts) : Nat.card Usub0 = 64 := by
  rw [F.enumerates_U.card]
  simpa using F.sizeU

theorem TablesFacts.U_le (F : TablesFacts) : Usub0 ≤ TLsub := by
  intro g hg
  obtain ⟨t, ht, hr⟩ := F.enumerates_U.complete g hg
  obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem ht
  have hc := F.U_le_T k (F.sizeU ▸ hk)
  have hmem : eu.tabs[k]! ∈ etl.tabs.toList := by simpa using hc
  obtain ⟨g', hg', hr'⟩ := F.enumerates_T.sound _ hmem
  have : g' = g := hr'.perm_eq hr
  rw [← this]
  exact hg'

@[expose] noncomputable def permOf (F : TablesFacts) (i : ℕ) : Equiv.Perm (Fin 42) :=
  if h : i < etl.tabs.size then (F.enumerates_T.exists_elt h).choose else 1

theorem permOf_spec (F : TablesFacts) {i : ℕ} (hi : i < 256) :
    permOf F i ∈ TLsub ∧ TabRep etl.tabs[i]! (permOf F i) := by
  have h : i < etl.tabs.size := F.sizeT ▸ hi
  unfold permOf
  simp only [h, ↓reduceDIte]
  exact (F.enumerates_T.exists_elt h).choose_spec

section Index

variable (F : TablesFacts) {A : Subgroup (Equiv.Perm (Fin 42))} (hTA : TLsub ≤ A)

@[expose] noncomputable def TablesFacts.indexing : Indexing (TLsub.subgroupOf A) mtF where
  elt i := ⟨permOf F i, if h : i < 256 then hTA (permOf_spec F h).1 else by
    have : permOf F i = 1 := by
      unfold permOf
      have : ¬ i < etl.tabs.size := F.sizeT ▸ h
      simp only [this, ↓reduceDIte]
    rw [this]
    exact A.one_mem⟩
  inj := by
    intro i j hi hj h
    have h' : permOf F i = permOf F j := congrArg Subtype.val h
    obtain ⟨-, ri⟩ := permOf_spec F hi
    obtain ⟨-, rj⟩ := permOf_spec F hj
    rw [← h'] at rj
    exact F.enumerates_T.pos_unique (F.sizeT ▸ hi) (F.sizeT ▸ hj) ri rj
  mem := by
    intro x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      obtain ⟨k, hk, hr⟩ := F.enumerates_T.exists_pos hx
      have hk' : k < 256 := F.sizeT ▸ hk
      refine ⟨k, hk', Subtype.ext ?_⟩
      exact (permOf_spec F hk').2.perm_eq hr
    · rintro ⟨i, hi, rfl⟩
      exact (permOf_spec F hi).1
  mul_lt := F.mul_lt
  mul := by
    intro i j hi hj
    apply Subtype.ext
    have hk := F.mul_lt i j hi hj
    obtain ⟨-, rk⟩ := permOf_spec F hk
    obtain ⟨-, ri⟩ := permOf_spec F hi
    obtain ⟨-, rj⟩ := permOf_spec F hj
    rw [F.mul_tab i j hi hj] at rk
    exact rk.perm_eq (ri.comp rj)
  one := by
    apply Subtype.ext
    obtain ⟨-, r0⟩ := permOf_spec F (show 0 < 256 by norm_num)
    rw [F.tab0] at r0
    exact r0.perm_eq TabRep.idTab

theorem TablesFacts.elt_inv {i : ℕ} (hi : i < 256) :
    (F.indexing hTA).elt invArr[i]! = ((F.indexing hTA).elt i)⁻¹ := by
  have h1 := (F.indexing hTA).mul i invArr[i]! hi (F.inv_lt i hi)
  rw [F.inv_mul i hi, (F.indexing hTA).one] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem TablesFacts.isUF_iff {i : ℕ} (hi : i < 256) :
    isUF i = true ↔ permOf F i ∈ Usub0 := by
  have hsz : i < etl.tabs.size := F.sizeT ▸ hi
  have h1 : isUF i = eu.tabs.contains etl.tabs[i]! := by
    unfold isUF isUArr
    rw [getElem!_pos (etl.tabs.map fun t => eu.tabs.contains t) i (by simpa using hsz)]
    simp [getElem!_pos etl.tabs i hsz]
  rw [h1]
  obtain ⟨-, ri⟩ := permOf_spec F hi
  constructor
  · intro h
    have hm : etl.tabs[i]! ∈ eu.tabs.toList := by simpa using h
    obtain ⟨g, hg, hr⟩ := F.enumerates_U.sound _ hm
    rw [ri.perm_eq hr]
    exact hg
  · intro h
    obtain ⟨t, ht, hr⟩ := F.enumerates_U.complete _ h
    have : t = etl.tabs[i]! := hr.tab_eq ri
    rw [← this]
    simpa using ht

theorem TablesFacts.labels :
    Labels (F.indexing hTA) (Usub0.subgroupOf A) labF laddF where
  lt := F.lab_lt
  zero := F.lab_zero
  eq_iff := by
    intro i j hi hj
    rw [F.lab_eq i j hi hj]
    have hk := F.mul_lt _ _ (F.inv_lt i hi) hj
    rw [F.isUF_iff hk, Subgroup.mem_subgroupOf, ← F.elt_inv hTA hi,
      ← (F.indexing hTA).mul _ _ (F.inv_lt i hi) hj]
    rfl
  hom := F.lab_hom

end Index

section Model

variable {K : Type} [Group K] (M : AutModel K (Equiv.Perm (Fin 42)))

@[expose] noncomputable def innL : Subgroup ↥M.A :=
  (MulAut.conj : K →* MulAut K).range.map M.Φ.toMonoidHom

theorem normal_inn : ((MulAut.conj : K →* MulAut K).range).Normal := by
  refine ⟨fun a ha φ => ?_⟩
  obtain ⟨k, rfl⟩ := ha
  refine ⟨φ k, ?_⟩
  ext x
  simp [MulAut.conj_apply]

instance innL_normal : (innL M).Normal :=
  (normal_inn (K := K)).map M.Φ.toMonoidHom M.Φ.surjective

theorem natCard_innL_dvd : Nat.card (innL M) ∣ Nat.card K := by
  unfold innL
  rw [Subgroup.card_map_of_injective (f := M.Φ.toMonoidHom) M.Φ.injective]
  exact Subgroup.card_range_dvd _

theorem mem_innL_of_mem {x : ↥M.A} (hx : (x : Equiv.Perm (Fin 42)) ∈ M.P) : x ∈ innL M := by
  obtain ⟨k, hk⟩ := M.e.surjective ⟨x, hx⟩
  refine ⟨MulAut.conj k, ⟨k, rfl⟩, ?_⟩
  have hk' : ((M.e k : M.P) : Equiv.Perm (Fin 42)) = x := congrArg Subtype.val hk
  set σ : Equiv.Perm (Fin 42) := (M.Φ (MulAut.conj k) : Equiv.Perm (Fin 42)) with hσ
  have hσA : σ ∈ M.A := (M.Φ (MulAut.conj k)).2
  have h1 : (x : Equiv.Perm (Fin 42))⁻¹ * σ = 1 := by
    apply AutModel.centralizer_trivial M (M.A.mul_mem (M.A.inv_mem x.2) hσA)
    intro p hp
    obtain ⟨m, hm⟩ := M.e.surjective ⟨p, hp⟩
    have hm' : ((M.e m : M.P) : Equiv.Perm (Fin 42)) = p := congrArg Subtype.val hm
    have hs := M.spec (MulAut.conj k) m
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv] at hs
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hk', hm'] at hs
    calc (x : Equiv.Perm (Fin 42))⁻¹ * σ * p
        = (x : Equiv.Perm (Fin 42))⁻¹ * (σ * p * σ⁻¹) * σ := by group
      _ = p * ((x : Equiv.Perm (Fin 42))⁻¹ * σ) := by rw [← hs]; group
  apply Subtype.ext
  show σ = x
  have h2 : σ = x := by
    have := congrArg (fun z => (x : Equiv.Perm (Fin 42)) * z) h1
    simpa using this
  exact h2

theorem TL_le (hA : M.A = QA.originalSubgroup) :
    TLsub ≤ M.A := by
  rw [hA]
  unfold TLsub
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  exacts [tl0_mem, tl1_mem, tl2_mem]

theorem U_le_P (hP : M.P = QP.originalSubgroup) :
    Usub0 ≤ M.P := by
  rw [hP]
  unfold Usub0
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  exacts [u0_mem, u1_mem, u2_mem, u3_mem]

theorem exists_modelData
    (F : TablesFacts) (hA : M.A = QA.originalSubgroup) (hP : M.P = QP.originalSubgroup)
    (hK : Nat.card K = 20160) (h7 : fb7Check mtF isUF = true)
    (h6 : fb6Check mtF labF laddF = true) :
    ∃ MD : ModelData ↥M.A, MD.Lm = innL M := by
  have hTA : TLsub ≤ M.A := TL_le M hA
  have hUP : Usub0 ≤ M.P := U_le_P M hP
  have hUT : Usub0 ≤ TLsub := F.U_le
  have hUA : Usub0 ≤ M.A := hUT.trans hTA
  set T : Subgroup ↥M.A := TLsub.subgroupOf M.A with hT
  set U : Subgroup ↥M.A := Usub0.subgroupOf M.A with hU
  have hcT : Nat.card T = 256 := by
    rw [hT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv, F.card_T]
  have hcU : Nat.card U = 64 := by
    rw [hU, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUA).toEquiv, F.card_U]
  have hQ : Nat.card ↥M.A = 241920 := by
    rw [hA, card_group QA QA_ok, QA_valid.2]
  have hUle : U ≤ T ⊓ innL M := by
    intro x hx
    have hxU : (x : Equiv.Perm (Fin 42)) ∈ Usub0 := Subgroup.mem_subgroupOf.1 hx
    exact ⟨Subgroup.mem_subgroupOf.2 (hUT hxU), mem_innL_of_mem M (hUP hxU)⟩
  have hcTL : Nat.card ↥(T ⊓ innL M) = 64 := by
    have h1 : Nat.card ↥(T ⊓ innL M) ∣ 256 := hcT ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(T ⊓ innL M) ∣ 20160 :=
      hK ▸ (Subgroup.card_dvd_of_le inf_le_right).trans (natCard_innL_dvd M)
    have h3 : Nat.card ↥(T ⊓ innL M) ∣ 64 := by
      have := Nat.dvd_gcd h1 h2
      simpa using this
    have h4 : 64 ∣ Nat.card ↥(T ⊓ innL M) := hcU ▸ Subgroup.card_dvd_of_le hUle
    exact Nat.dvd_antisymm h3 h4
  have hTL : T ⊓ innL M = U :=
    (Subgroup.eq_of_le_of_card_ge hUle (by rw [hcTL, hcU])).symm
  have hUU : ∀ i, i < 256 → (isUF i = true ↔ (F.indexing hTA).elt i ∈ U) := by
    intro i hi
    rw [F.isUF_iff hi, hU, Subgroup.mem_subgroupOf]
    rfl
  refine ⟨⟨T, innL M, inferInstance, by rw [hcT]; norm_num, ?_, by rw [hTL, hcU]; norm_num, ?_, ?_⟩,
    rfl⟩
  · have := Subgroup.index_mul_card T
    rw [hcT, hQ] at this
    intro h
    omega
  · intro E hET hE
    have := fb7_sound (F.indexing hTA) hUU h7 E hET hE
    rwa [hTL]
  · intro R hRT hSS hsw x hxR hxe hx2 hx1
    rw [hTL] at hSS
    exact fb6_sound (F.labels hTA) h6 hRT hSS hsw hxR hxe hx2 hx1

end Model

end CFSG.OddStandard.Seitz77.CaseB45
