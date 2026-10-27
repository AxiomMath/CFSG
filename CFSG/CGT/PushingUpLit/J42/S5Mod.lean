module

public import CFSG.CGT.PushingUpLit.J42.S5Rank
public import CFSG.GH74.Defs
public import CFSG.CGT.PushingUpLit.BHS.SymNatBasic
public import Certificates.Certificate271070

public section

namespace CFSG.CGT.PushingUpLit.SolK

namespace S5Mod

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS Equiv

theorem maskOf_lt (p : Nat → Bool) : ∀ n, maskOf p n < 2 ^ n
  | 0 => by simp [maskOf]
  | n + 1 => by
    have := maskOf_lt p n
    rw [maskOf, pow_succ]
    split_ifs <;> omega

theorem testBit_maskOf (p : Nat → Bool) : ∀ {n i : Nat}, i < n → (maskOf p n).testBit i = p i
  | 0, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, hi => by
    have hlt := maskOf_lt p n
    rw [maskOf]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · split_ifs with hp
      · rw [add_comm, Nat.testBit_two_pow_add_gt h]
        exact testBit_maskOf p h
      · rw [add_zero]
        exact testBit_maskOf p h
    · split_ifs with hp
      · rw [add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        simp [hp]
      · rw [add_zero, Nat.testBit_lt_two_pow hlt]
        simpa using hp

def dElem : Nat → Perm (Fin 5)
  | 0 => 1
  | 1 => swap 0 1
  | 2 => swap 2 3
  | 3 => swap 0 1 * swap 2 3
  | 4 => swap 0 2 * swap 1 3
  | 5 => swap 0 1 * (swap 0 2 * swap 1 3)
  | 6 => swap 2 3 * (swap 0 2 * swap 1 3)
  | _ => swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3)

theorem dElem_mul_aux : ∀ i < 8, ∀ j < 8, mulD i j < 8 ∧
    ∀ x : Fin 5, dElem i (dElem j x) = dElem (mulD i j) x := by
  decide

theorem dElem_inv_aux : ∀ i < 8, ∃ k < 8, ∀ x : Fin 5, dElem k (dElem i x) = x := by
  decide

theorem dElem_inj_aux : ∀ i < 8, ∀ j < 8, (∀ x : Fin 5, dElem i x = dElem j x) → i = j := by
  decide

theorem dElem_mul {i j : Nat} (hi : i < 8) (hj : j < 8) :
    mulD i j < 8 ∧ dElem i * dElem j = dElem (mulD i j) := by
  obtain ⟨h1, h2⟩ := dElem_mul_aux i hi j hj
  exact ⟨h1, Equiv.ext h2⟩

def Dsub : Subgroup (Perm (Fin 5)) where
  carrier := {σ | ∃ i < 8, dElem i = σ}
  one_mem' := ⟨0, by norm_num, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    obtain ⟨hk, he⟩ := dElem_mul hi hj
    exact ⟨mulD i j, hk, he.symm⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨k, hk, h⟩ := dElem_inv_aux i hi
    refine ⟨k, hk, ?_⟩
    rw [eq_inv_iff_mul_eq_one]
    exact Equiv.ext fun x => by simpa using h x

theorem card_Dsub : Nat.card Dsub = 8 := by
  have h : (Dsub : Set (Perm (Fin 5))) = ↑((Finset.range 8).image dElem) := by
    ext σ
    simp [Dsub]
  rw [show Nat.card Dsub = Nat.card (Dsub : Set (Perm (Fin 5))) from rfl, h,
    Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn]
  · simp
  · intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact dElem_inj_aux i hi j hj (fun x => by rw [h])

theorem card_perm_five : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

theorem exists_conj_le_Dsub (A : Subgroup (Perm (Fin 5))) (hA : IsPGroup 2 A) :
    ∃ g : Perm (Fin 5), ∀ x ∈ A, g⁻¹ * x * g ∈ Dsub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hA.exists_le_sylow
  let D0 : Sylow 2 (Perm (Fin 5)) := Sylow.ofCard Dsub (by
    rw [card_Dsub, card_perm_five]
    norm_num [Nat.factorization])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) D0 P
  refine ⟨g, fun x hx => ?_⟩
  have hxP : x ∈ (P : Subgroup (Perm (Fin 5))) := hP hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxP
  have h : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
  rw [h] at hxP
  exact hxP

@[expose] def coordBit (a : Nat) (x : Fin 5) : ZMod 2 := (((vec5 a >>> x.val) &&& 1 : Nat) : ZMod 2)

theorem coordBit_mod (a : Nat) : coordBit a = coordBit (a % 16) := by
  funext x
  simp only [coordBit, vec5, Nat.mod_mod]

theorem coordBit_sum (a : Nat) : ∑ x : Fin 5, coordBit a x = 0 := by
  have h : ∀ b < 16, ∑ x : Fin 5, coordBit b x = 0 := by decide
  rw [coordBit_mod]
  exact h _ (Nat.mod_lt _ (by norm_num))

@[expose] def vecOf (a : Nat) : ↥(coreMod 5) := mkEven (coordBit a) (coordBit_sum a)

theorem vcoord_vecOf (a : Nat) (x : Fin 5) : vcoord (vecOf a) x = coordBit a x := rfl

theorem coordBit_xor_aux : ∀ a < 16, ∀ b < 16, ∀ x : Fin 5,
    coordBit (a ^^^ b) x = coordBit a x + coordBit b x := by
  decide

theorem coordBit_act_aux : ∀ i < 8, ∀ a < 16, ∀ x : Fin 5,
    coordBit (actD i a) (dElem i x) = coordBit a x := by
  decide

theorem xor_lt_aux : ∀ a < 16, ∀ b < 16, a ^^^ b < 16 := by decide

theorem actD_lt_aux : ∀ i < 8, ∀ a < 16, actD i a < 16 := by decide

theorem coordBit_zero : ∀ x : Fin 5, coordBit 0 x = 0 := by decide

theorem vecOf_zero : vecOf 0 = 1 :=
  vcoord_ext fun x => by rw [vcoord_vecOf, vcoord_one, coordBit_zero]

theorem vecOf_xor {a b : Nat} (ha : a < 16) (hb : b < 16) :
    vecOf (a ^^^ b) = vecOf a * vecOf b :=
  vcoord_ext fun x => by
    rw [vcoord_vecOf, vcoord_mul, vcoord_vecOf, vcoord_vecOf]
    exact coordBit_xor_aux a ha b hb x

theorem vecOf_act {i a : Nat} (hi : i < 8) (ha : a < 16) :
    vecOf (actD i a) = coreAct 5 (dElem i) (vecOf a) := by
  refine vcoord_ext fun y => ?_
  rw [vcoord_vecOf, vcoord_coreAct, vcoord_vecOf]
  have h := coordBit_act_aux i hi a ha ((dElem i)⁻¹ y)
  rwa [perm_apply_inv_self] at h

theorem vecOf_surj (v : ↥(coreMod 5)) : ∃ a < 16, vecOf a = v := by
  have key : ∀ c0 c1 c2 c3 : ZMod 2, ∃ a < 16, coordBit a 0 = c0 ∧ coordBit a 1 = c1 ∧
      coordBit a 2 = c2 ∧ coordBit a 3 = c3 ∧ coordBit a 4 = c0 + c1 + c2 + c3 := by
    decide
  have key4 : ∀ c0 c1 c2 c3 c4 : ZMod 2, c0 + c1 + c2 + c3 + c4 = 0 → c4 = c0 + c1 + c2 + c3 := by
    decide
  have hs := sum_vcoord v
  rw [Fin.sum_univ_five] at hs
  obtain ⟨a, ha, h0, h1, h2, h3, h4⟩ := key (vcoord v 0) (vcoord v 1) (vcoord v 2) (vcoord v 3)
  refine ⟨a, ha, vcoord_ext fun x => ?_⟩
  rw [vcoord_vecOf]
  fin_cases x
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4.trans (key4 _ _ _ _ _ hs).symm

theorem bool_imp {a b c : Bool} (h : a = true → b = true → c = true) :
    (!(a && b) || c) = true := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem stepD_sound {S : Subgroup (Perm (Fin 5))} {m : Nat}
    (hm : ∀ k < 8, m.testBit k = true → dElem k ∈ S) :
    ∀ k < 8, (stepD m).testBit k = true → dElem k ∈ S := by
  intro k hk h
  rw [stepD, testBit_maskOf _ hk] at h
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq] at h
  rcases h with h | ⟨i, hi, j, hj, ⟨hmi, hmj⟩, rfl⟩
  · exact hm k hk h
  · obtain ⟨-, he⟩ := dElem_mul hi hj
    rw [← he]
    exact S.mul_mem (hm i hi hmi) (hm j hj hmj)

theorem closeD_sound {S : Subgroup (Perm (Fin 5))} {gs : List Nat}
    (hgs : ∀ i ∈ gs, dElem i ∈ S) : ∀ k < 8, (closeD gs).testBit k = true → dElem k ∈ S := by
  have h0 : ∀ k < 8, (maskOf (fun k => k == 0 || gs.contains k) 8).testBit k = true →
      dElem k ∈ S := by
    intro k hk h
    rw [testBit_maskOf _ hk] at h
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
    rcases h with rfl | h
    · exact S.one_mem
    · exact hgs k h
  exact stepD_sound (stepD_sound (stepD_sound h0))

theorem addVec_sound {N : Subgroup ↥(coreMod 5)} {m v : Nat}
    (hm : ∀ a < 16, m.testBit a = true → vecOf a ∈ N) (hv : v < 16) (hvN : vecOf v ∈ N) :
    ∀ a < 16, (addVec m v).testBit a = true → vecOf a ∈ N := by
  intro a ha h
  rw [addVec, testBit_maskOf _ ha] at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact hm a ha h
  · have h1 : a ^^^ v < 16 := xor_lt_aux a ha v hv
    have h2 : vecOf a = vecOf (a ^^^ v) * vecOf v := by
      rw [← vecOf_xor h1 hv, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [h2]
    exact N.mul_mem (hm _ h1 h) hvN

theorem foldl_addVec_sound {N : Subgroup ↥(coreMod 5)} {l : List Nat}
    (hl : ∀ w ∈ l, w < 16 ∧ vecOf w ∈ N) :
    ∀ m : Nat, (∀ a < 16, m.testBit a = true → vecOf a ∈ N) →
      ∀ a < 16, (l.foldl addVec m).testBit a = true → vecOf a ∈ N := by
  induction l with
  | nil => exact fun m hm => hm
  | cons v l ih =>
    intro m hm
    exact ih (fun w hw => hl w (List.mem_cons_of_mem _ hw)) _
      (addVec_sound hm (hl v List.mem_cons_self).1 (hl v List.mem_cons_self).2)

theorem vspan_sound {N : Subgroup ↥(coreMod 5)} {l : List Nat}
    (hl : ∀ w ∈ l, w < 16 ∧ vecOf w ∈ N) : ∀ a < 16, (vspan l).testBit a = true → vecOf a ∈ N := by
  refine foldl_addVec_sound hl 1 fun a _ h => ?_
  rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at h
  subst h
  rw [vecOf_zero]
  exact N.one_mem

theorem genOK_iff {hm : Nat} {gs : List Nat} (h : genOK hm gs = true) :
    (∀ i ∈ gs, i < 8 ∧ hm.testBit i = true) ∧
      ∀ k < 8, hm.testBit k = true → (closeD gs).testBit k = true := by
  simp only [genOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.1, fun k hk hmk => ?_⟩
  rcases h.2 k hk with h2 | h2
  · rw [hmk] at h2
    exact absurd h2 (by simp)
  · exact h2

theorem tsOK_iff {hm lm : Nat} {ts : List Nat} (h : tsOK hm lm ts = true) :
    (∀ a ∈ ts, a < 16 ∧ lm.testBit a = true) ∧
      ∀ w < 16, lm.testBit w = true → (vspan (orbitList hm ts)).testBit w = true := by
  simp only [tsOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.1, fun w hw hlw => ?_⟩
  rcases h.2 w hw with h2 | h2
  · rw [hlw] at h2
    exact absurd h2 (by simp)
  · exact h2

theorem verify_of_check (h : S5ModCheck) {hm lm : Nat} (hhm : hm < 256) (hc : closedD hm = true)
    (hlm : lm < 65536) (hl : closedV lm = true) (hinv : invV hm lm = true) :
    verify hm lm (pickGs hm) (pickTs hm lm) = true := by
  have h' : check = true := h
  unfold check at h'
  rw [List.all_eq_true] at h'
  have h1 := h' hm (by simp only [hmList, List.mem_filter, List.mem_range]; exact ⟨hhm, hc⟩)
  rw [List.all_eq_true] at h1
  have h2 := h1 lm (by simp only [lmList, List.mem_filter, List.mem_range]; exact ⟨hlm, hl⟩)
  simpa [hinv] using h2

def AltFS : Prop :=
  ∀ A : Subgroup (Perm (Fin 5)), A ≤ Dsub → ∀ W : Subgroup ↥(coreMod 5),
    (∀ h ∈ A, ∀ v ∈ W, coreAct 5 h v ∈ W) →
    ∃ (gs : Finset (Perm (Fin 5))) (ts : Finset ↥(coreMod 5)), gs.card + ts.card ≤ 4 ∧
      (∀ g ∈ gs, g ∈ A) ∧ A ≤ Subgroup.closure (gs : Set (Perm (Fin 5))) ∧ (∀ t ∈ ts, t ∈ W) ∧
      ∀ N : Subgroup ↥(coreMod 5), (∀ h ∈ A, ∀ v ∈ N, coreAct 5 h v ∈ N) →
        (∀ t ∈ ts, t ∈ N) → W ≤ N

theorem altFS : AltFS := by
  classical
  have hc : S5ModCheck := Certificates.certificate271070
  intro A hAD W hW
  set hm : Nat := maskOf (fun i => decide (dElem i ∈ A)) 8 with hhm
  set lm : Nat := maskOf (fun a => decide (vecOf a ∈ W)) 16 with hlm
  have hmbit : ∀ i < 8, hm.testBit i = true ↔ dElem i ∈ A := by
    intro i hi
    rw [hhm, testBit_maskOf _ hi, decide_eq_true_iff]
  have lmbit : ∀ a < 16, lm.testBit a = true ↔ vecOf a ∈ W := by
    intro a ha
    rw [hlm, testBit_maskOf _ ha, decide_eq_true_iff]
  have hmlt : hm < 256 := lt_of_lt_of_le (maskOf_lt _ 8) (by norm_num)
  have lmlt : lm < 65536 := lt_of_lt_of_le (maskOf_lt _ 16) (by norm_num)
  have hcl : closedD hm = true := by
    simp only [closedD, Bool.and_eq_true, List.all_eq_true, List.mem_range]
    refine ⟨(hmbit 0 (by norm_num)).2 A.one_mem, fun i hi j hj => bool_imp fun hi' hj' => ?_⟩
    obtain ⟨hlt, he⟩ := dElem_mul hi hj
    exact (hmbit _ hlt).2 (he ▸ A.mul_mem ((hmbit i hi).1 hi') ((hmbit j hj).1 hj'))
  have lcl : closedV lm = true := by
    simp only [closedV, Bool.and_eq_true, List.all_eq_true, List.mem_range]
    refine ⟨(lmbit 0 (by norm_num)).2 (by rw [vecOf_zero]; exact W.one_mem),
      fun a ha b hb => bool_imp fun ha' hb' => ?_⟩
    exact (lmbit _ (xor_lt_aux a ha b hb)).2 (by
      rw [vecOf_xor ha hb]
      exact W.mul_mem ((lmbit a ha).1 ha') ((lmbit b hb).1 hb'))
  have hinv : invV hm lm = true := by
    simp only [invV, List.all_eq_true, List.mem_range]
    intro i hi a ha
    refine bool_imp fun hi' ha' => ?_
    refine (lmbit _ (actD_lt_aux i hi a ha)).2 ?_
    rw [vecOf_act hi ha]
    exact hW _ ((hmbit i hi).1 hi') _ ((lmbit a ha).1 ha')
  have hv := verify_of_check hc hmlt hcl lmlt lcl hinv
  set gsL := pickGs hm with hgsL
  set tsL := pickTs hm lm with htsL
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨hlen, hgen⟩, hts⟩ := hv
  obtain ⟨hgs1, hgs2⟩ := genOK_iff hgen
  obtain ⟨hts1, hts2⟩ := tsOK_iff hts
  refine ⟨(gsL.map dElem).toFinset, (tsL.map vecOf).toFinset, ?_, ?_, ?_, ?_, ?_⟩
  · calc _ ≤ (gsL.map dElem).length + (tsL.map vecOf).length :=
          Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
      _ = gsL.length + tsL.length := by simp
      _ ≤ 4 := hlen
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hg)
    exact (hmbit i (hgs1 i hi).1).1 (hgs1 i hi).2
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := hAD hx
    have hkm : hm.testBit k = true := (hmbit k hk).2 hx
    refine closeD_sound (S := Subgroup.closure ↑(gsL.map dElem).toFinset) (gs := gsL) ?_ k hk
      (hgs2 k hk hkm)
    intro i hi
    exact Subgroup.subset_closure (Finset.mem_coe.2 (List.mem_toFinset.2
      (List.mem_map_of_mem hi)))
  · intro t ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ht)
    exact (lmbit a (hts1 a ha).1).1 (hts1 a ha).2
  · intro N hNinv hNts v hv
    obtain ⟨a, ha, rfl⟩ := vecOf_surj v
    have hla : lm.testBit a = true := (lmbit a ha).2 hv
    refine vspan_sound (N := N) (l := orbitList hm tsL) ?_ a ha (hts2 a ha hla)
    intro w hw
    simp only [orbitList, List.mem_flatMap, List.mem_filter, List.mem_range,
      List.mem_map] at hw
    obtain ⟨i, ⟨hi, hmi⟩, t, ht, rfl⟩ := hw
    have hiA : dElem i ∈ A := (hmbit i hi).1 hmi
    refine ⟨actD_lt_aux i hi t (hts1 t ht).1, ?_⟩
    rw [vecOf_act hi (hts1 t ht).1]
    exact hNinv _ hiA _ (hNts _ (List.mem_toFinset.2 (List.mem_map_of_mem ht)))

structure AltModData {M : Type*} [Group M] (Q : Subgroup M) (θ : M →* Perm (Fin 5))
    (β : ↥Q ≃* ↥(coreMod 5)) : Prop where
  conj_mem : ∀ m : M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q
  act : ∀ (m : M) (q : ↥Q), β ⟨m * q * m⁻¹, conj_mem m q q.2⟩ = coreAct 5 (θ m) (β q)
  ker : ∀ m : M, θ m = 1 → m ∈ Q

theorem AltModData.conj {M : Type*} [Group M] {Q : Subgroup M} {θ : M →* Perm (Fin 5)}
    {β : ↥Q ≃* ↥(coreMod 5)} (h : AltModData Q θ β) (g : Perm (Fin 5)) :
    AltModData Q ((MulAut.conj g⁻¹).toMonoidHom.comp θ) (β.trans (coreAct 5 g⁻¹)) where
  conj_mem := h.conj_mem
  act m q := by
    have e : (MulAut.conj g⁻¹ : Perm (Fin 5) ≃* Perm (Fin 5)) (θ m) = g⁻¹ * θ m * g := by
      rw [MulAut.conj_apply, inv_inv]
    have e2 : coreAct 5 g (coreAct 5 g⁻¹ (β q)) = β q := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    simp only [MulEquiv.trans_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, h.act,
      map_mul, MulAut.mul_apply]
    rw [e2]
  ker m hm := h.ker m ((map_eq_one_iff (MulAut.conj g⁻¹) (MulAut.conj g⁻¹).injective).1 hm)

theorem gen4_aux (hFS : AltFS) {M : Type*} [Group M] [Finite M] {Q : Subgroup M}
    {θ : M →* Perm (Fin 5)} {β : ↥Q ≃* ↥(coreMod 5)} (hd : AltModData Q θ β) (H : Subgroup M)
    (hH2 : IsPGroup 2 H) (hHD : ∀ m ∈ H, θ m ∈ Dsub) :
    ∃ r : Finset M, r.card ≤ 4 ∧ Subgroup.closure (r : Set M) = H := by
  classical
  have hAD : H.map θ ≤ Dsub := by
    rintro _ ⟨m, hm, rfl⟩
    exact hHD m hm
  have hWinv : ∀ h ∈ H.map θ, ∀ v ∈ (H.subgroupOf Q).map β.toMonoidHom,
      coreAct 5 h v ∈ (H.subgroupOf Q).map β.toMonoidHom := by
    rintro _ ⟨m, hm, rfl⟩ v ⟨q, hq, rfl⟩
    exact ⟨⟨m * q * m⁻¹, hd.conj_mem m q q.2⟩,
      H.mul_mem (H.mul_mem hm hq) (H.inv_mem hm), hd.act m q⟩
  obtain ⟨gs, ts, hcard, hgsA, hAcl, htsW, hN⟩ := hFS _ hAD _ hWinv
  have hlift : ∀ σ : Perm (Fin 5), ∃ h : M, σ ∈ H.map θ → (h ∈ H ∧ θ h = σ) := by
    intro σ
    by_cases hσ : σ ∈ H.map θ
    · obtain ⟨h, hh, hθ⟩ := hσ
      exact ⟨h, fun _ => ⟨hh, hθ⟩⟩
    · exact ⟨1, fun h => absurd h hσ⟩
  choose lift hlift using hlift
  have hs : ((gs.image lift : Finset M) : Set M) ⊆ H := by
    intro x hx
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact (hlift σ (hgsA σ hσ)).1
  have ht : ((ts.image fun v => ((β.symm v : ↥Q) : M) : Finset M) : Set M) ⊆ ↑(H ⊓ Q) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨q, hq, hqv⟩ := htsW v hv
    have : β.symm v = q := by rw [← hqv]; exact β.symm_apply_apply q
    rw [this]
    exact ⟨hq, q.2⟩
  have hsL : Subgroup.closure ((gs.image lift : Finset M) : Set M) ⊔ (H ⊓ Q) = H := by
    apply le_antisymm
    · exact sup_le ((Subgroup.closure_le H).2 hs) inf_le_left
    · intro h hh
      have hθh : θ h ∈ Subgroup.closure (gs : Set (Perm (Fin 5))) := hAcl ⟨h, hh, rfl⟩
      have himg : (Subgroup.closure ((gs.image lift : Finset M) : Set M)).map θ =
          Subgroup.closure (gs : Set (Perm (Fin 5))) := by
        rw [MonoidHom.map_closure]
        congr 1
        ext σ
        constructor
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
          rw [(hlift τ (hgsA τ hτ)).2]
          exact hτ
        · intro hσ
          exact ⟨lift σ, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hσ),
            (hlift σ (hgsA σ hσ)).2⟩
      rw [← himg] at hθh
      obtain ⟨x, hx, hxθ⟩ := hθh
      have hxH : x ∈ H := (Subgroup.closure_le H).2 hs hx
      have hmem : x⁻¹ * h ∈ H ⊓ Q :=
        ⟨H.mul_mem (H.inv_mem hxH) hh,
          hd.ker _ (by rw [map_mul, map_inv, hxθ, inv_mul_cancel])⟩
      have e : h = x * (x⁻¹ * h) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hx hmem
  have htL : ∀ N : Subgroup M, N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) →
      ((ts.image fun v => ((β.symm v : ↥Q) : M) : Finset M) : Set M) ⊆ N → H ⊓ Q ≤ N := by
    intro N _ hNinv htN x hx
    have hN' : ∀ h ∈ H.map θ, ∀ v ∈ (N.subgroupOf Q).map β.toMonoidHom,
        coreAct 5 h v ∈ (N.subgroupOf Q).map β.toMonoidHom := by
      rintro _ ⟨m, hm, rfl⟩ v ⟨q, hq, rfl⟩
      exact ⟨⟨m * q * m⁻¹, hd.conj_mem m q q.2⟩, hNinv m hm q hq, hd.act m q⟩
    have htN' : ∀ v ∈ ts, v ∈ (N.subgroupOf Q).map β.toMonoidHom := by
      intro v hv
      refine ⟨β.symm v, ?_, by simp⟩
      exact htN (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hv))
    have hWN' := hN _ hN' htN'
    have hxW : β ⟨x, hx.2⟩ ∈ (H.subgroupOf Q).map β.toMonoidHom := ⟨⟨x, hx.2⟩, hx.1, rfl⟩
    obtain ⟨q, hq, hqx⟩ := hWN' hxW
    have e : q = ⟨x, hx.2⟩ := β.injective hqx
    rw [e] at hq
    exact hq
  obtain ⟨r, hr, hcl⟩ := exists_card_le_of_normalClosure hH2 inf_le_left hs ht hsL htL
  refine ⟨r, ?_, hcl⟩
  calc r.card ≤ (gs.image lift).card + (ts.image fun v => ((β.symm v : ↥Q) : M)).card := hr
    _ ≤ gs.card + ts.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ 4 := hcard

end S5Mod

open CFSG.Quasithin.G6 in
theorem gen4_of_alt_module {M : Type*} [Group M] [Finite M]
    (Q : Subgroup M) (θ : M →* Equiv.Perm (Fin 5)) (β : ↥Q ≃* ↥(coreMod 5))
    (hQn : ∀ m : M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q)
    (hβ : ∀ (m : M) (q : ↥Q), β ⟨m * q * m⁻¹, hQn m q q.2⟩ = coreAct 5 (θ m) (β q))
    (hker : ∀ m : M, θ m = 1 → m ∈ Q) :
    CFSG.GH74.SectionalTwoRankLE M 4 := by
  intro H hH2
  obtain ⟨g, hg⟩ := S5Mod.exists_conj_le_Dsub (H.map θ) (hH2.map θ)
  have hd : S5Mod.AltModData Q θ β := ⟨hQn, hβ, hker⟩
  exact S5Mod.gen4_aux S5Mod.altFS (hd.conj g) H hH2 fun m hm => by
    have := hg (θ m) (Subgroup.mem_map_of_mem θ hm)
    simpa [MulAut.conj_apply] using this

end CFSG.CGT.PushingUpLit.SolK
