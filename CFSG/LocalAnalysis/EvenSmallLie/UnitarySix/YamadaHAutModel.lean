module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Link
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XFacts
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndCentralizer

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaHAut

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3

theorem basic_spec : validA 693 dTab = true ∧ validA 693 sTab = true ∧
    eqA 693 (compA 693 dTab d2Tab) (idA 693) = true ∧ eqA 693 (compA 693 sTab sTab) (idA 693) = true ∧
    eqA 693 (compA 693 (compA 693 sTab dTab) (compA 693 sTab dTab)) (idA 693) = true := by
  have h := basic_check
  simp only [basicCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem rep_dTab : Rep 693 dTab dP := rep_of_validA basic_spec.1

theorem rep_sTab : Rep 693 sTab sP := rep_of_validA basic_spec.2.1

theorem rep_d2Tab : Rep 693 d2Tab (dP * dP) := rep_compA rep_dTab rep_dTab

theorem rep_dsTab : Rep 693 dsTab (dP * sP) := rep_compA rep_dTab rep_sTab

theorem rep_d2sTab : Rep 693 d2sTab (dP * dP * sP) := rep_compA rep_d2Tab rep_sTab

theorem dP_pow_three : dP ^ 3 = 1 := by
  have h := eq_of_eqA (rep_compA rep_dTab rep_d2Tab) rep_idA basic_spec.2.2.1
  rw [pow_succ, pow_two, mul_assoc]
  rw [← mul_assoc] at h
  rwa [mul_assoc] at h

theorem sP_mul_self : sP * sP = 1 :=
  eq_of_eqA (rep_compA rep_sTab rep_sTab) rep_idA basic_spec.2.2.2.1

theorem sP_inv : sP⁻¹ = sP := inv_eq_of_mul_eq_one_right sP_mul_self

theorem sP_dP_mul_self : sP * dP * (sP * dP) = 1 :=
  eq_of_eqA (rep_compA (rep_compA rep_sTab rep_dTab) (rep_compA rep_sTab rep_dTab)) rep_idA
    basic_spec.2.2.2.2

theorem sP_conj_dP : sP * dP * sP⁻¹ = dP⁻¹ := by
  rw [sP_inv]
  have h := sP_dP_mul_self
  calc sP * dP * sP = sP * dP * sP * (dP * dP⁻¹) := by group
    _ = (sP * dP * (sP * dP)) * dP⁻¹ := by group
    _ = dP⁻¹ := by rw [h, one_mul]

theorem mem_T46_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ T46 ↔ siftA 693 lvL chL.B 0 g = true := by
  rw [← chL_eq_T46]
  exact ChainData.mem_grp_iff tabs_check gensOK_chL chL_ok nodup_chL hG

theorem normL_spec : ∀ w ∈ chL.gens, dP * wP w * dP⁻¹ ∈ T46 ∧ sP * wP w * sP⁻¹ ∈ T46 := by
  intro w hw
  have h := all_O_spec normL_check w hw
  simp only [Bool.and_eq_true] at h
  exact ⟨(mem_T46_iff (rep_conjA basic_spec.1 (rep_wA_gens gensOK_chL hw))).2 h.1,
    (mem_T46_iff (rep_conjA basic_spec.2.1 (rep_wA_gens gensOK_chL hw))).2 h.2⟩

theorem dP_mem_autT : dP ∈ autT := by
  have h := mem_normalizer_grp (c := chL) (g := dP) fun w hw => by
    rw [chL_eq_T46]
    exact (normL_spec w hw).1
  rwa [chL_eq_T46] at h

theorem sP_mem_autT : sP ∈ autT := by
  have h := mem_normalizer_grp (c := chL) (g := sP) fun w hw => by
    rw [chL_eq_T46]
    exact (normL_spec w hw).2
  rwa [chL_eq_T46] at h

theorem T46_le_autT : T46 ≤ autT := le_normalizer

theorem conj_mem_T46_iff {x : Equiv.Perm (Fin 693)} (hx : x ∈ autT) {g : Equiv.Perm (Fin 693)} :
    x * g * x⁻¹ ∈ T46 ↔ g ∈ T46 :=
  ((mem_normalizer_iff.1 hx) g).symm

theorem outer_spec : dP ∉ T46 ∧ dP * dP ∉ T46 ∧ sP ∉ T46 ∧ dP * sP ∉ T46 ∧ dP * dP * sP ∉ T46 := by
  have h := outer_check
  simp only [outerCheck, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · rw [(mem_T46_iff rep_dTab).1 hm] at h1; exact Bool.false_ne_true h1.symm
  · rw [(mem_T46_iff rep_d2Tab).1 hm] at h2; exact Bool.false_ne_true h2.symm
  · rw [(mem_T46_iff rep_sTab).1 hm] at h3; exact Bool.false_ne_true h3.symm
  · rw [(mem_T46_iff rep_dsTab).1 hm] at h4; exact Bool.false_ne_true h4.symm
  · rw [(mem_T46_iff rep_d2sTab).1 hm] at h5; exact Bool.false_ne_true h5.symm

theorem eq_zero_of_mem_T46 : ∀ i < 3, ∀ j < 2, dP ^ i * sP ^ j ∈ T46 → i = 0 ∧ j = 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := outer_spec
  intro i hi j hj hm
  interval_cases i <;> interval_cases j
  · exact ⟨rfl, rfl⟩
  · exact absurd (by simpa using hm) h3
  · exact absurd (by simpa using hm) h1
  · exact absurd (by simpa using hm) h4
  · exact absurd (by simpa [pow_two] using hm) h2
  · exact absurd (by simpa [pow_two] using hm) h5

theorem zpow_mem_T46 {a b : ℤ} (h : dP ^ a * sP ^ b ∈ T46) : (3 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b := by
  have h3 : dP ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, dP_pow_three]
  have h2 : sP ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, sP_mul_self]
  have ha : dP ^ a = dP ^ (a % 3).toNat := by
    rw [zpow_eq_zpow_emod a h3, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg a (by norm_num))]
  have hb : sP ^ b = sP ^ (b % 2).toNat := by
    rw [zpow_eq_zpow_emod b h2, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg b (by norm_num))]
  rw [ha, hb] at h
  have hlt3 : (a % 3).toNat < 3 := by omega
  have hlt2 : (b % 2).toNat < 2 := by omega
  obtain ⟨e1, e2⟩ := eq_zero_of_mem_T46 _ hlt3 _ hlt2 h
  omega

theorem mul_pow_inj {l l' : Equiv.Perm (Fin 693)} (hl : l ∈ T46) (hl' : l' ∈ T46)
    {i i' j j' : ℕ} (hi : i < 3) (hi' : i' < 3) (hj : j < 2) (hj' : j' < 2)
    (h : l * dP ^ i * sP ^ j = l' * dP ^ i' * sP ^ j') : l = l' ∧ i = i' ∧ j = j' := by
  have h1 : dP ^ i * sP ^ j * (dP ^ i' * sP ^ j')⁻¹ ∈ T46 := by
    have e : dP ^ i * sP ^ j * (dP ^ i' * sP ^ j')⁻¹ = l⁻¹ * l' := by
      calc dP ^ i * sP ^ j * (dP ^ i' * sP ^ j')⁻¹
          = l⁻¹ * (l * dP ^ i * sP ^ j) * (dP ^ i' * sP ^ j')⁻¹ := by group
        _ = l⁻¹ * (l' * dP ^ i' * sP ^ j') * (dP ^ i' * sP ^ j')⁻¹ := by rw [h]
        _ = l⁻¹ * l' := by group
    rw [e]
    exact mul_mem (inv_mem hl) hl'
  have hu : dP ^ (-(i' : ℤ)) ∈ autT := zpow_mem dP_mem_autT _
  have h2 := (conj_mem_T46_iff hu).2 h1
  have e2 : dP ^ (-(i' : ℤ)) * (dP ^ i * sP ^ j * (dP ^ i' * sP ^ j')⁻¹) * (dP ^ (-(i' : ℤ)))⁻¹ =
      dP ^ ((i : ℤ) - i') * sP ^ ((j : ℤ) - j') := by
    simp only [← zpow_natCast]
    group
  rw [e2] at h2
  obtain ⟨h3, h4⟩ := zpow_mem_T46 h2
  have hii : i = i' := by omega
  have hjj : j = j' := by omega
  subst hii hjj
  exact ⟨mul_right_cancel (mul_right_cancel h), rfl, rfl⟩

theorem centralizer_T46 : centralizer (T46 : Set (Equiv.Perm (Fin 693))) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [mem_centralizer_iff] at hc
  rw [mem_bot]
  have h0 : c 0 = 0 := fix_unique fun s hs => by
    have hsT : s ∈ T46 := grp_le_T46 gensOK_chS hs
    have := congrArg (fun f : Equiv.Perm (Fin 693) => f 0) (hc s hsT)
    simp only [Equiv.Perm.mul_apply, S_fix s hs] at this
    exact this
  refine Equiv.ext fun p => ?_
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T46 (0 : Fin 693) p
  have hg' : (g : Equiv.Perm (Fin 693)) 0 = p := hg
  have := congrArg (fun f : Equiv.Perm (Fin 693) => f 0) (hc g g.2)
  simp only [Equiv.Perm.mul_apply, h0, hg'] at this
  rw [Equiv.Perm.one_apply]
  exact this.symm

theorem lieModel_T46 : CFSG.Blueprint.LieModel T46 .PSU 6 2 1 :=
  CFSG.Fischer.Classification.Recognition.lieModel_of_mulEquiv_PSU
    CFSG.Fischer.isNondegenerateHermitian_one (suQuotEquiv.symm.trans psuEquiv)

theorem mem_autT_of {l : Equiv.Perm (Fin 693)} (hl : l ∈ T46) (i j : ℕ) :
    l * dP ^ i * sP ^ j ∈ autT :=
  mul_mem (mul_mem (T46_le_autT hl) (pow_mem dP_mem_autT i)) (pow_mem sP_mem_autT j)

@[expose] def prodMap : T46 × Fin 3 × Fin 2 → autT := fun p =>
  ⟨p.1 * dP ^ (p.2.1 : ℕ) * sP ^ (p.2.2 : ℕ), mem_autT_of p.1.2 _ _⟩

theorem prodMap_injective : Function.Injective prodMap := by
  rintro ⟨l, i, j⟩ ⟨l', i', j'⟩ h
  have h' := congrArg Subtype.val h
  obtain ⟨e1, e2, e3⟩ := mul_pow_inj l.2 l'.2 i.2 i'.2 j.2 j'.2 h'
  exact Prod.ext (Subtype.ext e1) (Prod.ext (Fin.ext e2) (Fin.ext e3))

@[expose] def autConj : autT →* MulAut T46 := Subgroup.normalizerMonoidHom T46

theorem autConj_apply (x : autT) (g : T46) :
    ((autConj x g : T46) : Equiv.Perm (Fin 693)) = x * g * (x : Equiv.Perm (Fin 693))⁻¹ :=
  rfl

theorem autConj_injective : Function.Injective autConj := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hc : (x : Equiv.Perm (Fin 693)) ∈ centralizer (T46 : Set (Equiv.Perm (Fin 693))) := by
    rw [mem_centralizer_iff]
    intro h hh
    have h1 := congrArg (fun α : MulAut T46 => ((α ⟨h, hh⟩ : T46) : Equiv.Perm (Fin 693)))
      (MonoidHom.mem_ker.1 hx)
    simp only [autConj_apply, MulAut.one_apply] at h1
    calc h * x = x * h * (x : Equiv.Perm (Fin 693))⁻¹ * x := by rw [h1]
      _ = x * h := by group
  rw [centralizer_T46, mem_bot] at hc
  exact mem_bot.2 (Subtype.ext hc)

theorem finite_mulAut_T46 : Finite (MulAut T46) :=
  Finite.of_injective (fun α : MulAut T46 => (α : T46 → T46)) DFunLike.coe_injective

theorem card_mulAut_T46_le : Nat.card (MulAut T46) ≤ 6 * Nat.card T46 := by
  have h := YamadaEnd.card_mulAut_dvd (X := T46)
  rw [YamadaEnd.card_outer_of_lieModel_PSU lieModel_T46] at h
  exact Nat.le_of_dvd (by rw [card_T46]; norm_num) h

theorem card_autT_eq : Nat.card autT = 6 * Nat.card T46 := by
  have : Finite (MulAut T46) := finite_mulAut_T46
  have h1 : 6 * Nat.card T46 ≤ Nat.card autT := by
    have := Nat.card_le_card_of_injective prodMap prodMap_injective
    rwa [Nat.card_prod, Nat.card_prod, Nat.card_fin, Nat.card_fin, mul_comm] at this
  have h2 : Nat.card autT ≤ Nat.card (MulAut T46) :=
    Nat.card_le_card_of_injective autConj autConj_injective
  exact le_antisymm (h2.trans card_mulAut_T46_le) h1

theorem card_autT : Nat.card autT = 6 * 9196830720 := by rw [card_autT_eq, card_T46]

theorem autConj_bijective : Function.Bijective autConj := by
  have : Finite (MulAut T46) := finite_mulAut_T46
  refine autConj_injective.bijective_of_nat_card_le ?_
  rw [card_autT_eq]
  exact card_mulAut_T46_le

@[expose] def autEquiv : autT ≃* MulAut T46 := MulEquiv.ofBijective autConj autConj_bijective

theorem autEquiv_apply (x : autT) (g : T46) :
    ((autEquiv x g : T46) : Equiv.Perm (Fin 693)) = x * g * (x : Equiv.Perm (Fin 693))⁻¹ :=
  rfl

theorem mem_autT_iff {x : Equiv.Perm (Fin 693)} :
    x ∈ autT ↔ ∃ l ∈ T46, ∃ i < 3, ∃ j < 2, x = l * dP ^ i * sP ^ j := by
  constructor
  · intro hx
    have hbij : Function.Bijective prodMap := by
      refine prodMap_injective.bijective_of_nat_card_le ?_
      rw [card_autT_eq, Nat.card_prod, Nat.card_prod, Nat.card_fin, Nat.card_fin, mul_comm]
    obtain ⟨⟨l, i, j⟩, h⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨l, l.2, i, i.2, j, j.2, (congrArg Subtype.val h).symm⟩
  · rintro ⟨l, hl, i, -, j, -, rfl⟩
    exact mem_autT_of hl i j

theorem normBy_spec {c : ChainData} {lv : Array Level} (hg : c.GensOK)
    (hmem : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin 693)}, Rep 693 g G →
      (G ∈ c.grp ↔ siftA 693 lv c.B 0 g = true)) (h : normBy c lv = true) :
    dP ∈ normalizer (c.grp : Set (Equiv.Perm (Fin 693))) ∧
      sP ∈ normalizer (c.grp : Set (Equiv.Perm (Fin 693))) := by
  unfold normBy at h
  refine ⟨mem_normalizer_grp fun w hw => ?_, mem_normalizer_grp fun w hw => ?_⟩
  · have h1 := all_O_spec h w hw
    simp only [Bool.and_eq_true] at h1
    exact (hmem (rep_conjA basic_spec.1 (rep_wA_gens hg hw))).2 h1.1
  · have h1 := all_O_spec h w hw
    simp only [Bool.and_eq_true] at h1
    exact (hmem (rep_conjA basic_spec.2.1 (rep_wA_gens hg hw))).2 h1.2

theorem normObj_spec : normBy chS lvS = true ∧
    normBy chX1 lvX1 = true ∧
    normBy chX2 lvX2 = true ∧
    normBy chX3 lvX3 = true ∧
    normBy chK1 lvK1 = true ∧
    normBy chK2 lvK2 = true ∧
    normBy chA1 lvA1 = true ∧
    normBy chA2 lvA2 = true ∧
    normBy chK1A1 lvK1A1 = true ∧
    normBy chK2A2 lvK2A2 = true ∧
    normBy chSJ lvSJ = true ∧
    normBy chA3 lvA3 = true ∧
    normBy chA4 lvA4 = true ∧
    normBy chX8 lvX8 = true ∧
    normBy chSig lvSig = true ∧
    normBy chLam lvLam = true ∧
    normBy chZ2S lvZ2S = true ∧
    normBy chZ lvZ = true ∧
    normBy chX1Z lvX1Z = true ∧
    normBy chP2 lvP2 = true ∧
    normBy chX6Z lvX6Z = true := by
  have h := normObj_check
  simp only [normObjCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩,
    h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩

theorem norm_chA1 : dP ∈ normalizer (chA1.grp : Set (Equiv.Perm (Fin 693))) ∧
    sP ∈ normalizer (chA1.grp : Set (Equiv.Perm (Fin 693))) :=
  normBy_spec gensOK_chA1 mem_chA1_iff normObj_spec.2.2.2.2.2.2.1

theorem norm_chA3 : dP ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) ∧
    sP ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) :=
  normBy_spec gensOK_chA3 mem_chA3_iff normObj_spec.2.2.2.2.2.2.2.2.2.2.2.1

theorem norm_chA4 : dP ∈ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693))) ∧
    sP ∈ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693))) :=
  normBy_spec gensOK_chA4 mem_chA4_iff normObj_spec.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem norm_chZ2S : dP ∈ normalizer (chZ2S.grp : Set (Equiv.Perm (Fin 693))) ∧
    sP ∈ normalizer (chZ2S.grp : Set (Equiv.Perm (Fin 693))) :=
  normBy_spec gensOK_chZ2S mem_chZ2S_iff normObj_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem letter_spec : (∀ k ∈ dLetters, dP * gP k = gP k * dP) ∧
    (∀ k ∈ sLetters, sP * gP k = gP k * sP) ∧
    ∀ k ∈ sPairs, sP * gP (k + 1) * sP⁻¹ = gP k * gP (k + 1) := by
  have h := letter_check
  simp only [letterCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hd : ∀ k ∈ dLetters, k < 18 := by decide
  have hs : ∀ k ∈ sLetters, k < 18 := by decide
  have hp : ∀ k ∈ sPairs, k + 1 < 18 := by decide
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · exact eq_of_eqA (rep_compA rep_dTab (rep_gA tabs_check (hd k hk)))
      (rep_compA (rep_gA tabs_check (hd k hk)) rep_dTab) (h1 k hk)
  · exact eq_of_eqA (rep_compA rep_sTab (rep_gA tabs_check (hs k hk)))
      (rep_compA (rep_gA tabs_check (hs k hk)) rep_sTab) (h2 k hk)
  · have hk' : k < 18 := by have := hp k hk; omega
    exact eq_of_eqA (rep_conjA basic_spec.2.1 (rep_gA tabs_check (hp k hk)))
      (rep_compA (rep_gA tabs_check hk') (rep_gA tabs_check (hp k hk))) (h3 k hk)

theorem dP_comm_wP : ∀ w : List ℕ, (∀ k ∈ w, k ∈ dLetters) → dP * wP w = wP w * dP
  | [], _ => by simp [wP]
  | k :: w, hw => by
    have h1 := letter_spec.1 k (hw k List.mem_cons_self)
    have h2 := dP_comm_wP w fun j hj => hw j (List.mem_cons_of_mem k hj)
    rw [wP, List.map_cons, List.prod_cons, ← wP]
    calc dP * (gP k * wP w) = (dP * gP k) * wP w := by group
      _ = gP k * (dP * wP w) := by rw [h1]; group
      _ = gP k * wP w * dP := by rw [h2]; group

theorem sP_comm_wP : ∀ w : List ℕ, (∀ k ∈ w, k ∈ sLetters) → sP * wP w = wP w * sP
  | [], _ => by simp [wP]
  | k :: w, hw => by
    have h1 := letter_spec.2.1 k (hw k List.mem_cons_self)
    have h2 := sP_comm_wP w fun j hj => hw j (List.mem_cons_of_mem k hj)
    rw [wP, List.map_cons, List.prod_cons, ← wP]
    calc sP * (gP k * wP w) = (sP * gP k) * wP w := by group
      _ = gP k * (sP * wP w) := by rw [h1]; group
      _ = gP k * wP w * sP := by rw [h2]; group

theorem dP_mem_centralizer {c : ChainData} (h : ∀ w ∈ c.gens, ∀ k ∈ w, k ∈ dLetters) :
    dP ∈ centralizer (c.grp : Set (Equiv.Perm (Fin 693))) := by
  have hle : c.grp ≤ centralizer ({dP} : Set (Equiv.Perm (Fin 693))) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨w, hw, rfl⟩
    exact mem_centralizer_singleton_iff.2 (dP_comm_wP w (h w hw)).symm
  rw [mem_centralizer_iff]
  intro x hx
  exact mem_centralizer_singleton_iff.1 (hle hx)

theorem dP_centralizer_spec :
    dP ∈ centralizer (chX1.grp : Set (Equiv.Perm (Fin 693))) ∧
    dP ∈ centralizer (chX3.grp : Set (Equiv.Perm (Fin 693))) ∧
    dP ∈ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693))) ∧
    dP ∈ centralizer (chX8.grp : Set (Equiv.Perm (Fin 693))) ∧
    dP ∈ centralizer (chSig.grp : Set (Equiv.Perm (Fin 693))) ∧
    dP ∈ centralizer (chLam.grp : Set (Equiv.Perm (Fin 693))) ∧
    dP ∈ centralizer (chZ2S.grp : Set (Equiv.Perm (Fin 693))) ∧
    dP ∈ centralizer (chZ.grp : Set (Equiv.Perm (Fin 693))) ∧
    dP ∈ centralizer (chX1Z.grp : Set (Equiv.Perm (Fin 693))) :=
  ⟨dP_mem_centralizer (by decide), dP_mem_centralizer (by decide),
    dP_mem_centralizer (by decide), dP_mem_centralizer (by decide),
    dP_mem_centralizer (by decide), dP_mem_centralizer (by decide),
    dP_mem_centralizer (by decide), dP_mem_centralizer (by decide),
    dP_mem_centralizer (by decide)⟩

