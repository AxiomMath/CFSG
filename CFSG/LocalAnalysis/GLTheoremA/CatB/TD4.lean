module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.LargeExtraspecial.S63CD4Iso
public import CFSG.LargeExtraspecial.S63CD4A
public import CFSG.LargeExtraspecial.S9FiveB
public import CFSG.Adapters.TauCetiExceptional.EvenD4

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB TauCeti

theorem lift_extraspecial_noncentral {G : Type} [Group G] [Finite G] {J : Subgroup G} {M : Type*}
    [Group M] (π : ↥J →* M) (hk : ¬ 2 ∣ Nat.card π.ker) {Tb : Subgroup M} {n : ℕ}
    (hTr : Tb ≤ π.range) (hT : CFSG.IsExtraspecialPGroup 2 ↥Tb)
    (hTc : Nat.card Tb = 2 ^ (2 * n + 1)) {t : M} (ht : t ∈ Tb) (ht2 : t ^ 2 = 1)
    (htz : t ∉ Tb ⊓ Subgroup.centralizer (Tb : Set M)) :
    ∃ T : Subgroup G, T ≤ J ∧ IsExtraspecialTwo T n ∧
      ∃ t' ∈ T, t' ^ 2 = 1 ∧ t' ∉ T ⊓ Subgroup.centralizer (T : Set G) := by
  obtain ⟨W, hWp, hWmap, hWinj⟩ := exists_pSubgroup_lift Nat.prime_two π hk hT.1 hTr
  let eWT : W ≃* Tb := (mulEquivMap π hWinj).trans (MulEquiv.subgroupCongr hWmap)
  let eTW : (W.map J.subtype) ≃* W := (W.equivMapOfInjective J.subtype J.subtype_injective).symm
  have hext : CFSG.IsExtraspecialPGroup 2 ↥(W.map J.subtype) :=
    CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv (eWT.symm.trans eTW.symm) hT
  have htW : t ∈ W.map π := hWmap ▸ ht
  obtain ⟨w, hwW, hwt⟩ := htW
  refine ⟨W.map J.subtype, Subgroup.map_subtype_le _, ⟨hext, ?_⟩, J.subtype w,
    Subgroup.mem_map_of_mem _ hwW, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective J.subtype_injective, card_eq_of_injective_comp_subtype π hWinj,
      hWmap, hTc]
  · have h2 : (⟨w ^ 2, W.pow_mem hwW 2⟩ : W) = 1 := by
      apply hWinj
      show π (w ^ 2) = π 1
      rw [map_pow, hwt, ht2, map_one]
    have := congrArg Subtype.val h2
    have h3 : w ^ 2 = 1 := this
    rw [← map_pow, h3, map_one]
  · rintro ⟨-, hc⟩
    apply htz
    refine Subgroup.mem_inf.2 ⟨ht, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : s ∈ W.map π := hWmap ▸ hs
    obtain ⟨v, hvW, rfl⟩ := hs'
    have := Subgroup.mem_centralizer_iff.1 hc (J.subtype v) (Subgroup.mem_map_of_mem _ hvW)
    have hvw : v * w = w * v := Subtype.ext (by simpa using this)
    rw [← hwt]
    change π v * π w = π w * π v
    rw [← map_mul, ← map_mul, hvw]

namespace TD4Model

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin Subgroup

theorem qGens_pos {k : ℕ} (hk : k < 8) : k < qGens.size := by
  rw [qGens_size]; exact hk

theorem qGH_zero_one_ne : qGH 0 * qGH 1 ≠ qGH 1 * qGH 0 := by
  intro h
  have h0 : (0 : ℕ) < qGens.size := qGens_pos (by norm_num)
  have h1 : (1 : ℕ) < qGens.size := qGens_pos (by norm_num)
  have hr1 := repE_mul (repE_qGens h0) (repE_qGens h1)
  have hr2 := repE_mul (repE_qGens h1) (repE_qGens h0)
  have hv1 : validR (mulR qGens[0]! qGens[1]!) = true :=
    validR_mulR (size_of_validR (validR_qGens h0)) (validR_qGens h1)
  have hv2 : validR (mulR qGens[1]! qGens[0]!) = true :=
    validR_mulR (size_of_validR (validR_qGens h1)) (validR_qGens h0)
  have := (eq_iff_of_repE hv1 hv2 hr1 hr2).2 h
  exact absurd this (by decide +kernel)

theorem d4z_mul_self : d4z * d4z = 1 := by
  have h := repE_mul repE_z0R repE_z0R
  have h2 : mulR z0R z0R = oneR := by decide +kernel
  rw [h2] at h
  exact eq_of_repE d4E_injective h repE_one

theorem d4z_ne_one : d4z ≠ 1 := by
  intro h
  have : z0R = oneR := (eq_iff_of_repE validR_z0R validR_oneR repE_z0R repE_one).2 h
  exact absurd this (by decide +kernel)

theorem d4z_sq : d4z ^ 2 = 1 := by rw [pow_two]; exact d4z_mul_self

theorem orderOf_d4z : orderOf d4z = 2 := orderOf_eq_prime d4z_sq d4z_ne_one

theorem mem_zpowers_d4z {x : trialityGroup8} : x ∈ zpowers d4z ↔ x = 1 ∨ x = d4z := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul]
      simp [d4z_sq]
    · right
      rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul]
      simp [d4z_sq]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem qGH_mul_self {k : ℕ} (hk : k < qGens.size) : qGH k * qGH k = 1 := (qGens_hyp k hk).2

theorem qGH_mem {k : ℕ} (hk : k < qGens.size) : qGH k ∈ d4Q :=
  subset_closure ⟨k, hk, rfl⟩

theorem d4z_comm {q : trialityGroup8} (hq : q ∈ d4Q) : q * d4z = d4z * q :=
  mem_centralizer_singleton_iff.1 (d4Q_le_centralizer hq)

theorem conj_gen {k : ℕ} (hk : k < qGens.size) {q : trialityGroup8} (hq : q ∈ d4Q) :
    q * qGH k * q⁻¹ = qGH k ∨ q * qGH k * q⁻¹ = qGH k * d4z := by
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  obtain ⟨-, -, h3, h4, -, -, -, -, -, -, -, -, -, -, -, h15, -⟩ := parts_of_d4ACheckOn h
  simp only [EnumData.ok, Bool.and_eq_true, beq_iff_eq] at h3
  have hQEl : ∀ i < 512, ∃ a ∈ d4Q, RepE d4E Q.El[i]! a := fun i hi =>
    exists_of_enumOK (fun k hk => (qGens_hyp k hk).1) h3.1 i (h3.2 ▸ hi)
  obtain ⟨i, hi, hri⟩ := exists_mem_of_enumOK qGens_hyp h3.1 hq
  rw [h3.2] at hi
  obtain ⟨-, hrq'⟩ := repE_inv_of_invOK hQEl h4 hi hri
  have hc : RepE d4E (conjI Q.El[i]! Q.El[Q.inv[i]!]! qGens[k]!) (q * qGH k * q⁻¹) :=
    repE_mul (repE_mul hri (repE_qGens hk)) hrq'
  rcases h15 i hi k hk with h' | h'
  · left
    rw [h'] at hc
    exact eq_of_repE d4E_injective hc (repE_qGens hk)
  · right
    rw [h'] at hc
    exact eq_of_repE d4E_injective hc (repE_mul (repE_qGens hk) repE_z0R)

theorem d4z_inv : d4z⁻¹ = d4z := (eq_inv_of_mul_eq_one_left d4z_mul_self).symm

theorem conj_all {q y : trialityGroup8} (hq : q ∈ d4Q) (hy : y ∈ d4Q) :
    q * y * q⁻¹ = y ∨ q * y * q⁻¹ = y * d4z := by
  have hz : ∀ {w : trialityGroup8}, w ∈ d4Q → w * d4z = d4z * w := fun hw => d4z_comm hw
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    exact conj_gen hk hq
  | one => left; simp
  | mul a b ha hb iha ihb =>
    have ha' : a ∈ d4Q := ha
    have hb' : b ∈ d4Q := hb
    have e : q * (a * b) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹) := by group
    rw [e]
    have hzb : d4z * b = b * d4z := (hz hb').symm
    rcases iha with h1 | h1 <;> rcases ihb with h2 | h2 <;> rw [h1, h2]
    · left; rfl
    · right; group
    · right
      rw [mul_assoc, hzb, ← mul_assoc]
    · left
      calc a * d4z * (b * d4z) = a * (d4z * b) * d4z := by group
        _ = a * (b * d4z) * d4z := by rw [hzb]
        _ = a * b * (d4z * d4z) := by group
        _ = a * b := by rw [d4z_mul_self, mul_one]
  | inv a ha iha =>
    have ha' : a ∈ d4Q := ha
    have e : q * a⁻¹ * q⁻¹ = (q * a * q⁻¹)⁻¹ := by group
    rw [e]
    rcases iha with h1 | h1
    · left; rw [h1]
    · right
      rw [h1, mul_inv_rev, d4z_inv]
      exact (hz (d4Q.inv_mem ha')).symm

theorem sq_mem {x : trialityGroup8} (hx : x ∈ d4Q) : x ^ 2 ∈ zpowers d4z := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    rw [pow_two, qGH_mul_self hk]
    exact one_mem _
  | one => simp
  | mul a b ha hb iha ihb =>
    have ha' : a ∈ d4Q := ha
    have hb' : b ∈ d4Q := hb
    have e : (a * b) ^ 2 = a * (b * a * b⁻¹) * (b * b) := by simp only [pow_two]; group
    rw [e]
    rcases conj_all hb' ha' with h | h <;> rw [h]
    · have : a * a * (b * b) = a ^ 2 * b ^ 2 := by simp only [pow_two]
      rw [this]
      exact mul_mem iha ihb
    · have : a * (a * d4z) * (b * b) = a ^ 2 * d4z * b ^ 2 := by simp only [pow_two]; group
      rw [this]
      exact mul_mem (mul_mem iha (mem_zpowers _)) ihb
  | inv a ha iha =>
    have : a⁻¹ ^ 2 = (a ^ 2)⁻¹ := by simp only [pow_two]; group
    rw [this]
    exact inv_mem iha

theorem comm_mem {x y : trialityGroup8} (hx : x ∈ d4Q) (hy : y ∈ d4Q) :
    x * y * x⁻¹ * y⁻¹ ∈ zpowers d4z := by
  rcases conj_all hx hy with h | h <;> rw [h]
  · rw [mul_inv_cancel]; exact one_mem _
  · have : y * d4z * y⁻¹ = d4z := by rw [d4z_comm hy, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact mem_zpowers _

theorem center_le {x : trialityGroup8} (hx : x ∈ d4Q) (hc : ∀ y ∈ d4Q, x * y = y * x) :
    x = 1 ∨ x = d4z := by
  by_contra hne
  push Not at hne
  let M : Subgroup trialityGroup8 := d4Q ⊓ centralizer (d4Q : Set trialityGroup8)
  have hM : d4Q ≤ M := by
    refine d4Q_irred M inf_le_left ?_ ?_ ?_
    · intro l hl m hm
      obtain ⟨hmQ, hmc⟩ := mem_inf.1 hm
      refine mem_inf.2 ⟨d4L_normalizes l hl m hmQ, ?_⟩
      rw [mem_centralizer_iff]
      intro q hq
      have hq' : l⁻¹ * q * l⁻¹⁻¹ ∈ d4Q := d4L_normalizes l⁻¹ (d4L.inv_mem hl) q hq
      have h1 := mem_centralizer_iff.1 hmc _ hq'
      calc q * (l * m * l⁻¹) = l * ((l⁻¹ * q * l⁻¹⁻¹) * m) * l⁻¹ := by group
        _ = l * (m * (l⁻¹ * q * l⁻¹⁻¹)) * l⁻¹ := by rw [h1]
        _ = l * m * l⁻¹ * q := by group
    · exact mem_inf.2 ⟨d4z_mem_d4Q, mem_centralizer_iff.2 fun q hq => d4z_comm hq⟩
    · exact ⟨x, mem_inf.2 ⟨hx, mem_centralizer_iff.2 fun q hq => (hc q hq).symm⟩, hne.1, hne.2⟩
  have h0 := (mem_inf.1 (hM (qGH_mem (qGens_pos (by norm_num : 0 < 8))))).2
  have h1 := mem_centralizer_iff.1 h0 (qGH 1) (qGH_mem (qGens_pos (by norm_num : 1 < 8)))
  exact qGH_zero_one_ne h1.symm

theorem isExtraspecial_d4Q : CFSG.IsExtraspecialPGroup 2 ↥d4Q := by
  have hfin : Finite ↥d4Q := Nat.finite_of_card_ne_zero (by rw [card_d4Q]; norm_num)
  have hP : IsPGroup 2 ↥d4Q := IsPGroup.of_card (n := 9) (by rw [card_d4Q]; norm_num)
  let Z : Subgroup ↥d4Q := (zpowers d4z).subgroupOf d4Q
  have hzle : zpowers d4z ≤ d4Q := (zpowers_le).2 d4z_mem_d4Q
  have hZc : Nat.card Z = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv, Nat.card_zpowers, orderOf_d4z]
  refine CFSG.LargeExtraspecial.S9.isExtraspecialPGroup_of_center hP hZc ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    have hz' : (z : trialityGroup8) ∈ zpowers d4z := hz
    rcases mem_zpowers_d4z.1 hz' with h | h
    · change (g : trialityGroup8) * z = z * g
      rw [h]; simp
    · change (g : trialityGroup8) * z = z * g
      rw [h]; exact d4z_comm g.2
  · intro x y
    rw [Subgroup.mem_subgroupOf, commutatorElement_def]
    simpa using comm_mem x.2 y.2
  · intro x
    rw [Subgroup.mem_subgroupOf]
    simpa using sq_mem x.2
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    have := center_le x.2 (fun y hy => by
      have := congrArg Subtype.val (hx ⟨y, hy⟩)
      simpa using this)
    exact mem_zpowers_d4z.2 this
  · refine ⟨⟨qGH 0, qGH_mem (qGens_pos (by norm_num))⟩, fun h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at h
    apply qGH_zero_one_ne
    have h1 : qGH 1 ∈ d4Q := qGH_mem (qGens_pos (by norm_num))
    have h' : qGH 0 ∈ zpowers d4z := h
    rcases mem_zpowers_d4z.1 h' with h0 | h0 <;> rw [h0]
    · simp
    · exact (d4z_comm h1).symm

theorem exists_extraspecial_noncentral : ∃ Tb : Subgroup trialityGroup8,
    CFSG.IsExtraspecialPGroup 2 ↥Tb ∧ Nat.card Tb = 2 ^ (2 * 4 + 1) ∧ ∃ t ∈ Tb, t ^ 2 = 1 ∧
      t ∉ Tb ⊓ centralizer (Tb : Set trialityGroup8) := by
  refine ⟨d4Q, isExtraspecial_d4Q, by rw [card_d4Q]; norm_num, qGH 0,
    qGH_mem (qGens_pos (by norm_num)), ?_, fun h => ?_⟩
  · rw [pow_two]
    exact qGH_mul_self (qGens_pos (by norm_num))
  · have h1 : qGH 1 ∈ d4Q := qGH_mem (qGens_pos (by norm_num))
    exact qGH_zero_one_ne (mem_centralizer_iff.1 (mem_inf.1 h).2 _ h1).symm

end TD4Model

theorem lieIndex_isTD4two {S : Type} [Group S] (h : catalogIs S S9.isTD4two) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.card = 2 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | trialityD4 q => exact ⟨q, hv, hP, ⟨e⟩⟩
  | _ => exact hP.elim

theorem blueprintLieModel_td4two
    {S : Type} [Group S] (h : catalogIs S S9.isTD4two) :
    CFSG.Blueprint.LieModel S .trialityD4 0 2 1 := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isTD4two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 3) = q.card ^ (CFSG.Blueprint.Chevalley.TwistTag.D4).order := by
    rw [GaloisField.card 2 3 (by norm_num), hq]
    rfl
  let σ : GaloisField 2 3 →+* GaloisField 2 3 := frobenius (GaloisField 2 3) 2
  have hσ : ∀ x, σ x = x ^ q.card := fun x => by
    rw [hq]
    rfl
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv h1 (GaloisField 2 3) hK σ hσ
  refine Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, by norm_num, rfl⟩,
    GaloisField 2 3, inferInstance, inferInstance, ?_, σ, ?_, ⟨e.trans b.symm⟩⟩)
  · rw [GaloisField.card 2 3 (by norm_num)]
    rfl
  · intro x
    rw [hσ x, hq]
    rfl

section Holds

theorem extraspecialTD4At_holds (G : Type) [Group G] [Finite G] :
    ∀ (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
      Odd (Nat.card (GLAPPrimeCoreOf 3 L)) →
      (catalogIs (PSimple 3 L) S9.isTD4two → ∃ T : Subgroup G, T ≤ L ∧ IsExtraspecialTwo T 4 ∧
        ∃ t ∈ T, t ^ 2 = 1 ∧ t ∉ T ⊓ Subgroup.centralizer (T : Set G)) := by
  intro X L hX hL hodd hcat
  obtain ⟨e⟩ := CFSG.LargeExtraspecial.S63.nonempty_equiv_trialityGroup8 (PSimple 3 L)
    (blueprintLieModel_td4two hcat)
  obtain ⟨π, hπs, hkc⟩ := exists_hom_of_simple_equiv e
  have hk2 : ¬ 2 ∣ Nat.card π.ker := odd_card_ker L hkc hodd
  obtain ⟨Tb, hT, hTc, t, ht, ht2, htz⟩ := TD4Model.exists_extraspecial_noncentral
  exact lift_extraspecial_noncentral π hk2
    (by rw [MonoidHom.range_eq_top_of_surjective π hπs]; exact le_top) hT hTc ht ht2 htz

end Holds

end CFSG.LocalAnalysis.GLTheoremA.CatB
