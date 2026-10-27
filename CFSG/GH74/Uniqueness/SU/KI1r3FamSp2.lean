module

public import CFSG.GH74.Uniqueness.SU.KI1r3FamDefs
public import CFSG.GH74.KGroups.M22
public import CFSG.GH74.KGroups.CoverJ3
public import CFSG.GH74.E2.CompCertsJ2
import all CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
import all CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open CFSG CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem isElemAbelian_two_of_sq {G : Type*} [Group G] (E : Subgroup G)
    (h : ∀ x ∈ E, x ^ 2 = 1) : Open.IsElemAbelian 2 E := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, h⟩
  apply Subtype.ext
  have ha := h a a.2
  have hb := h b b.2
  have hab := h (a * b) (E.mul_mem a.2 b.2)
  change (a : G) * b = b * a
  have e1 : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ha)
  have e2 : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb)
  have e3 : ((a : G) * b)⁻¹ = (a : G) * b :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hab)
  rw [← e3, mul_inv_rev, e1, e2]

theorem fourFix_of_E16 {K G : Type} [Group K] [Finite K] [Group G] (e : K ≃* G) (E : Subgroup G)
    (hE : Open.IsElemAbelian 2 E) (hc : Nat.card E = 16) : FourFix K := by
  have : Finite G := Finite.of_equiv K e.toEquiv
  exact FourFix.of_mulEquiv e.symm
    (FourFix.of_four_le_twoRank (four_le_twoRank_of_card_sixteen E hE hc))

theorem exists_isElemAbelian_of_commuting_involutions {G : Type*} [Group G] {r : ℕ}
    (u : Fin r → G) (hsq : ∀ i, u i * u i = 1) (hcomm : ∀ i j, u i * u j = u j * u i)
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1) :
    ∃ E : Subgroup G, Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ r := by
  obtain ⟨f, hf⟩ := GH74.Filter.exists_injective_of_commuting_involutions u
    (fun i => by rw [sq]; exact hsq i) (fun i j => hcomm i j) hker
  refine exists_isElemAbelian_of_injective (p := 2) (A := Fin r → Multiplicative (ZMod 2))
    (fun a b => mul_comm a b) (fun a => ?_) (GH74.Filter.card_pi_zmod_two r) f hf
  funext i
  rw [Pi.pow_apply, Pi.one_apply]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  generalize Multiplicative.toAdd (a i) = z
  revert z
  decide

theorem exists_isElemAbelian_units_two {R' : Type*} [Monoid R'] (S : Submonoid R') {r : ℕ}
    (x : Fin r → R') (hxS : ∀ i, x i ∈ S) (hsq : ∀ i, x i * x i = 1)
    (hcomm : ∀ i j, x i * x j = x j * x i)
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1) :
    ∃ E : Subgroup Sˣ, Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ r := by
  have h2 : ∀ i, (⟨x i, hxS i⟩ : S) ^ 2 = 1 := fun i => Subtype.ext (by simpa [sq] using hsq i)
  let u : Fin r → Sˣ := fun i => Units.ofPowEqOne _ 2 (h2 i) (by norm_num)
  let f : Sˣ →* R' := S.subtype.comp (Units.coeHom S)
  have hf : ∀ i (n : ℕ), f (u i ^ n) = x i ^ n := fun i n => by
    rw [map_pow]
    rfl
  refine exists_isElemAbelian_of_commuting_involutions u (fun i => ?_)
    (fun i j => Units.ext (Subtype.ext (hcomm i j))) (fun a ha h => hker a ha ?_)
  · have := Units.pow_ofPowEqOne (h2 i) (by norm_num : 2 ≠ 0)
    rwa [sq] at this
  · have := congrArg f h
    rwa [map_list_prod, List.map_ofFn, map_one, Function.comp_def, funext fun i => hf i _] at this

@[expose] def opDst : Op → ℕ
  | .mul _ _ k => k
  | .pow _ _ k => k

section Regs

variable {M V : Type} {O : Ops M V} {p d : ℕ} [Inhabited M]

theorem step_getElem!_of_ne (O : Ops M V) (R : Array M) (op : Op) {k : ℕ} (hk : k < R.size)
    (hne : opDst op ≠ k) : (O.step R op)[k]! = R[k]! := by
  cases op with
  | mul i j l =>
    have hne' : l ≠ k := hne
    simp only [Ops.step, Array.set!]
    rw [OpsSpec.getElem!_setIfInBounds_of_lt hk]
    simp [hne']
  | pow e i l =>
    have hne' : l ≠ k := hne
    simp only [Ops.step, Array.set!]
    rw [OpsSpec.getElem!_setIfInBounds_of_lt hk]
    simp [hne']

theorem step_size (O : Ops M V) (R : Array M) (op : Op) : (O.step R op).size = R.size := by
  cases op <;> simp [Ops.step, Array.set!]

theorem run_getElem!_of_ne (O : Ops M V) (prog : List Op) : ∀ (R : Array M) {k : ℕ},
    k < R.size → (∀ op ∈ prog, opDst op ≠ k) → (O.run prog R)[k]! = R[k]! := by
  induction prog with
  | nil => intro R k _ _; rfl
  | cons op prog ih =>
    intro R k hk hne
    have h1 := ih (O.step R op) (by rw [step_size]; exact hk)
      (fun op' hop' => hne op' (List.mem_cons_of_mem _ hop'))
    simp only [Ops.run, List.foldl_cons] at h1 ⊢
    rw [h1, step_getElem!_of_ne O R op hk (hne op List.mem_cons_self)]

theorem initRegs_getElem!_of_ge (O : Ops M V) (A B : M) {n k : ℕ} (hk : k < n) (h2 : 2 ≤ k) :
    (O.initRegs A B n)[k]! = O.one := by
  unfold Ops.initRegs
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  simp [h0, h1]

theorem exists_isElemAbelian_of_secCheck_one (Sp : OpsSpec O p d)
    (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))) (D : SecData)
    (hA : Sp.WF (O.decode D.seedA) ∧ Sp.toMat (O.decode D.seedA) ∈ S)
    (hB : Sp.WF (O.decode D.seedB) ∧ Sp.toMat (O.decode D.seedB) ∈ S)
    (h : O.secCheck D = true) (h2 : 2 ≤ D.tReg) (hw : ∀ op ∈ D.prog, opDst op ≠ D.tReg) :
    ∃ E : Subgroup Sˣ, Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ D.outs.length := by
  unfold Ops.secCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hn, hprog⟩, houts⟩, htreg⟩, hsec⟩ := h
  obtain ⟨hs0, hok0⟩ := Sp.initRegs_ok S hA hB D.nregs
  obtain ⟨hs, hok⟩ := Sp.run_ok S D.prog hok0 (by rw [hs0]; exact hprog)
  set R := O.run D.prog (O.initRegs (O.decode D.seedA) (O.decode D.seedB) D.nregs)
  rw [hs0] at hs
  set xs := D.outs.map fun r => R[r]! with hxsdef
  set T := R[D.tReg]! with hTdef
  have hTok : Sp.WF T ∧ Sp.toMat T ∈ S := hok D.tReg (by rw [hs]; exact htreg)
  have hT1 : Sp.toMat T = 1 := by
    have h1 := run_getElem!_of_ne O D.prog
      (O.initRegs (O.decode D.seedA) (O.decode D.seedB) D.nregs) (k := D.tReg)
      (by rw [hs0]; exact htreg) hw
    rw [initRegs_getElem!_of_ge O _ _ htreg h2] at h1
    rw [hTdef, h1, Sp.toMat_one]
  have hxs : ∀ X ∈ xs, Sp.WF X ∧ Sp.toMat X ∈ S := by
    intro X hX
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact hok r (by rw [hs]; exact of_decide_eq_true (List.all_eq_true.1 houts r hr))
  have hw' : ∀ X ∈ xs, Sp.WF X := fun X hX => (hxs X hX).1
  unfold Ops.secOK at hsec
  simp only [Bool.and_eq_true] at hsec
  obtain ⟨⟨⟨htt, hxT⟩, hcomm⟩, hker⟩ := hsec
  have hpair := Sp.pairwise_of_commsModOK hTok.1 hw' hcomm
  have hsq : ∀ X ∈ xs, Sp.toMat X * Sp.toMat X = 1 := by
    intro X hX
    have h1 := List.all_eq_true.1 hxT X hX
    rw [Bool.and_eq_true] at h1
    have wX := hw' X hX
    have h2 := h1.2
    unfold Ops.inN at h2
    rw [Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · have := Sp.toMat_eq (Sp.mul_wf wX wX) Sp.one_wf h2
      rwa [Sp.toMat_mul wX wX, Sp.toMat_one] at this
    · have := Sp.toMat_eq (Sp.mul_wf wX wX) hTok.1 h2
      rwa [Sp.toMat_mul wX wX, hT1] at this
  rw [← List.length_map (f := fun r => R[r]!)]
  refine exists_isElemAbelian_units_two S (fun i : Fin xs.length => Sp.toMat xs[i])
    (fun i => (hxs _ (List.getElem_mem i.isLt)).2)
    (fun i => hsq _ (List.getElem_mem i.isLt)) (fun i j => ?_)
    (fun a ha => (Sp.ne_of_kerModOK hTok.1 hw' hker a ha).1)
  rcases lt_trichotomy i j with hij | rfl | hij
  · rcases List.pairwise_iff_getElem.1 hpair i j i.isLt j.isLt hij with h | h
    · exact h
    · rwa [hT1, one_mul] at h
  · rfl
  · rcases List.pairwise_iff_getElem.1 hpair j i j.isLt i.isLt hij with h | h
    · exact h.symm
    · rw [hT1, one_mul] at h
      exact h.symm

theorem exists_isElemAbelian_of_secCheck_seed [NeZero p] (Sp : OpsSpec O p d) (D : SecData)
    (h : O.secCheck D = true) (h2 : 2 ≤ D.tReg) (hw : ∀ op ∈ D.prog, opDst op ≠ D.tReg) :
    ∃ E : Subgroup (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
      Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ D.outs.length := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  have hA : Sp.WF (O.decode D.seedA) ∧ Sp.toMat (O.decode D.seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.seedB) ∧ Sp.toMat (O.decode D.seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  exact exists_isElemAbelian_of_secCheck_one Sp S D hA hB h h2 hw

end Regs

theorem exists_E16_M22 :
    ∃ E : Subgroup NativeSporadic.M22, Open.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  have hle : CFSG.GH74.KGroups.M22.QE.originalSubgroup ≤ NativeSporadic.M22 := by
    rw [← CFSG.GH74.KGroups.M22.QP_subgroup]
    exact CFSG.GH74.KGroups.M22.QE_le
  have hsq := CFSG.GH74.KGroups.sqOneCheck_sound CFSG.GH74.KGroups.M22.QE
    CFSG.GH74.KGroups.M22.QE_ok CFSG.GH74.KGroups.M22.QE_sq
  refine ⟨CFSG.GH74.KGroups.M22.QE.originalSubgroup.subgroupOf NativeSporadic.M22, ?_, ?_⟩
  · refine isElemAbelian_two_of_sq _ fun x hx => ?_
    have := hsq x hx
    exact Subtype.ext (by simpa using this)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      CFSG.GH74.KGroups.card_group CFSG.GH74.KGroups.M22.QE CFSG.GH74.KGroups.M22.QE_ok,
      CFSG.GH74.KGroups.M22.QE_valid.2]

theorem famSp_M22 : FamSp .M22 := by
  intro K _ _ ⟨e⟩
  obtain ⟨E, hE, hc⟩ := exists_E16_M22
  exact fourFix_of_E16 (G := NativeSporadic.M22) e E hE hc

theorem exists_E16_J3 :
    ∃ E : Subgroup NativeSporadic.J3, Open.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨e, hsq, hcomm, hker, hconj⟩ := CFSG.GH74.KGroups.J3.exists_e_J3
  have hE := CFSG.GH74.KGroups.exists_E16 (G := NativeSporadic.J3) e hsq hcomm hker hconj
  obtain ⟨E, hEcard, hE2, -, -⟩ := hE
  exact ⟨E, isElemAbelian_two_of_sq E hE2, hEcard⟩

theorem famSp_J3 : FamSp .J3 := by
  intro K _ _ ⟨e⟩
  obtain ⟨E, hE, hc⟩ := exists_E16_J3
  exact fourFix_of_E16 (G := NativeSporadic.J3) e E hE hc

theorem exists_E16_J2 :
    ∃ E : Subgroup NativeSporadic.J2, Open.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨E, hE, hc⟩ := exists_isElemAbelian_of_secCheck_seed (specP 5 14) CFSG.GH74.E2.j2Sec
    CFSG.GH74.E2.j2Sec_check (by decide) (by decide)
  exact ⟨E, hE, hc.trans (by decide)⟩

theorem famSp_J2 : FamSp .J2 := by
  intro K _ _ ⟨e⟩
  obtain ⟨E, hE, hc⟩ := exists_E16_J2
  exact fourFix_of_E16 (G := NativeSporadic.J2) e E hE hc

theorem exists_E16_McL :
    ∃ E : Subgroup NativeSporadic.McL, Open.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨E, hE, hc⟩ := exists_isElemAbelian_of_secCheck_seed (spec3 21) CFSG.GH74.Generic.mclSec
    CFSG.GH74.Generic.mclSec_check (by decide) (by decide)
  exact ⟨E, hE, hc.trans (by decide)⟩

theorem famSp_McL : FamSp .McL := by
  intro K _ _ ⟨e⟩
  obtain ⟨E, hE, hc⟩ := exists_E16_McL
  exact fourFix_of_E16 (G := NativeSporadic.McL) e E hE hc

theorem exists_E16_Ly :
    ∃ E : Subgroup NativeSporadic.Ly, Open.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨E, hE, hc⟩ := exists_isElemAbelian_of_secCheck_seed (specP 5 111) CFSG.GH74.Generic.lySec
    CFSG.GH74.Generic.lySec_check (by decide) (by decide)
  exact ⟨E, hE, hc.trans (by decide)⟩

theorem famSp_Ly : FamSp .Ly := by
  intro K _ _ ⟨e⟩
  obtain ⟨E, hE, hc⟩ := exists_E16_Ly
  exact fourFix_of_E16 (G := NativeSporadic.Ly) e E hE hc

end CFSG.GH74.Uniqueness.SU.K.R3
