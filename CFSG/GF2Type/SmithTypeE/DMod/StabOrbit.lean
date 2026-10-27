module

public import Certificates.Certificate38705
public import CFSG.GF2Type.SmithTypeE.DMod.TD6
public import CFSG.GF2Type.SmithTypeE.DMod.LineTree

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

attribute [local irreducible] tvCols tvLin

theorem stabTreeCheck_holds :
    (∀ c < 6, stabRep c < 365211 ∧ stabCls (stabRep c) = c) ∧
    (∀ g < stabGens.size, stabGens[g]! < 365211 ∧ tvImg stabGens[g]! 0 = 0) ∧
    (∀ v < 365211, Relation.ReflTransGen (fun u v => ∃ g < stabGens.size, tvImg stabGens[g]! u = v)
      (stabRep (stabCls v)) v) :=
  ⟨Certificates.certificate38705.1, Certificates.certificate38705.2.1,
    Certificates.certificate38705.2.2.1⟩

theorem stabCardCheck_holds : chkStabCard = true :=
  Certificates.certificate38705.2.2.2.1

theorem stabNcCheck_holds : chkStabNc = true :=
  Certificates.certificate38705.2.2.2.2.1

theorem stabOrdCheck_holds : chkStabOrd = true :=
  Certificates.certificate38705.2.2.2.2.2

section Orbits

theorem exists_mem_TD6_apply_zero_eq (a : Fin 365211) : ∃ g ∈ TD6, g 0 = a := by
  have key : ∀ v < 365211, ∃ g ∈ TD6, ((g 0 : Fin 365211) : ℕ) = v := by
    intro v hv
    refine lineTree_induct (fun v => ∃ g ∈ TD6, ((g 0 : Fin 365211) : ℕ) = v) ?_ ?_ v hv
    · exact ⟨1, TD6.one_mem, rfl⟩
    · rintro g hg p hp v hv hgv ⟨c, hc, hc0⟩
      refine ⟨tvP ⟨gensArr[g]!, gensArr_lt hg⟩ * c, TD6.mul_mem (tvP_mem _) hc, ?_⟩
      rw [Equiv.Perm.mul_apply, tvP_apply]
      show tvImg gensArr[g]! (c 0).val = v
      rw [hc0]
      exact hgv
  obtain ⟨g, hg, hga⟩ := key a.val a.2
  exact ⟨g, hg, Fin.ext hga⟩

theorem exists_mem_TD6_apply_eq (a b : Fin 365211) : ∃ g ∈ TD6, g a = b := by
  obtain ⟨g, hg, hga⟩ := exists_mem_TD6_apply_zero_eq a
  obtain ⟨h, hh, hhb⟩ := exists_mem_TD6_apply_zero_eq b
  refine ⟨h * g⁻¹, TD6.mul_mem hh (TD6.inv_mem hg), ?_⟩
  rw [Equiv.Perm.mul_apply, ← hga]
  simp [hhb]

theorem tvP_self (k : Fin 365211) : tvP k k = k := by
  apply Fin.ext
  apply lineSet_injective (tvP k k).2 k.2
  have h1 := lineSet_actPerm ⟨siegelK k.val, siegelK_mem_iso k.2⟩ k
  have hT := tsPair_linePair k.2
  have hu : siegelK k.val (dec12 (linePair k.val).1) = dec12 (linePair k.val).1 := by
    unfold siegelK
    rw [siegelEquiv_apply hT, hT.2.2, B12_self]
    simp
  have hw : siegelK k.val (dec12 (linePair k.val).2) = dec12 (linePair k.val).2 := by
    unfold siegelK
    rw [siegelEquiv_apply hT, B12_self, B12_comm, hT.2.2]
    simp
  show lineSet (actPerm ⟨siegelK k.val, siegelK_mem_iso k.2⟩ k).val = lineSet k.val
  rw [h1]
  show (lineOfPair (dec12 (linePair k.val).1) (dec12 (linePair k.val).2)).map
    (siegelK k.val).toEquiv.toEmbedding = lineSet k.val
  rw [lineOfPair_map]
  show lineOfPair (siegelK k.val (dec12 (linePair k.val).1))
    (siegelK k.val (dec12 (linePair k.val).2)) = _
  rw [hu, hw]
  rfl

theorem tvP_ne_one (k : Fin 365211) : tvP k ≠ 1 := by
  intro h
  have h1 : ∀ a : Fin 365211, tvP a = 1 := fun a => by
    obtain ⟨g, hg, hga⟩ := exists_mem_TD6_apply_eq k a
    have := mul_tvP_mul_inv hg k
    rw [h, mul_one, mul_inv_cancel, hga] at this
    exact this.symm
  have h2 := tvP_injective ((h1 0).trans (h1 1).symm)
  exact absurd (congrArg Fin.val h2) (by decide)

theorem card_stabilizer_mul_ncard_orbit (H : Subgroup (Equiv.Perm (Fin 365211))) :
    Nat.card (MulAction.stabilizer H (0 : Fin 365211)) *
        (MulAction.orbit H (0 : Fin 365211)).ncard = Nat.card H := by
  rw [← MulAction.index_stabilizer]
  exact (MulAction.stabilizer H (0 : Fin 365211)).card_mul_index

end Orbits

section Classes

theorem stabCls_le (a : ℕ) : stabCls a ≤ 5 := by
  unfold stabCls
  split_ifs <;> omega

theorem stabCls_zero : stabCls 0 = 0 := by
  unfold stabCls
  exact if_pos rfl

theorem stabCls_eq_zero_iff {a : ℕ} : stabCls a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    unfold stabCls at h
    split_ifs at h <;> first | omega | (simp_all)
  · rintro rfl
    exact stabCls_zero

theorem stabTree_unpack :
    (∀ c < 6, stabRep c < 365211 ∧ stabCls (stabRep c) = c) ∧
    (∀ g < stabGens.size, stabGens[g]! < 365211 ∧ tvImg stabGens[g]! 0 = 0) ∧
    (∀ v < 365211, Relation.ReflTransGen (fun u v => ∃ g < stabGens.size, tvImg stabGens[g]! u = v)
      (stabRep (stabCls v)) v) :=
  stabTreeCheck_holds

theorem exists_stab_rep_aux : ∀ v < 365211, ∃ h ∈ TD6, h 0 = 0 ∧
    ∃ r : Fin 365211, r.val = stabRep (stabCls v) ∧ (h r).val = v := by
  obtain ⟨hreps, hgens, hreach⟩ := stabTree_unpack
  intro v hv
  have hc6 : stabCls v < 6 := Nat.lt_succ_of_le (stabCls_le v)
  have ha := (hreps _ hc6).1
  have hrv := hreach v hv
  generalize stabRep (stabCls v) = a at ha hrv ⊢
  clear hc6 hv
  induction hrv with
  | refl => exact ⟨1, TD6.one_mem, rfl, ⟨_, ha⟩, rfl, rfl⟩
  | tail _ hst ih =>
    obtain ⟨h, hh, hh0, r, hr, hru⟩ := ih
    obtain ⟨g, hg, hgv⟩ := hst
    obtain ⟨hgl, hg0⟩ := hgens g hg
    refine ⟨tvP ⟨stabGens[g]!, hgl⟩ * h, TD6.mul_mem (tvP_mem _) hh, ?_, r, hr, ?_⟩
    · rw [Equiv.Perm.mul_apply, hh0]
      exact Fin.ext (by rw [tvP_apply]; exact hg0)
    · rw [Equiv.Perm.mul_apply, tvP_apply]
      change tvImg stabGens[g]! (h r).val = _
      rw [hru]
      exact hgv

theorem exists_stab_image {a b : Fin 365211} (hab : stabCls a.val = stabCls b.val) :
    ∃ g ∈ TD6, g 0 = 0 ∧ g a = b := by
  obtain ⟨ha, hha, hha0, r, hr, hra⟩ := exists_stab_rep_aux a.val a.2
  obtain ⟨hb, hhb, hhb0, r', hr', hrb⟩ := exists_stab_rep_aux b.val b.2
  have hrr : r = r' := Fin.ext (by rw [hr, hr', hab])
  refine ⟨hb * ha⁻¹, TD6.mul_mem hhb (TD6.inv_mem hha), ?_, ?_⟩
  · have h1 : ha⁻¹ 0 = 0 := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hha0.symm
    rw [Equiv.Perm.mul_apply, h1, hhb0]
  · have h1 : ha⁻¹ a = r := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (Fin.ext hra).symm
    rw [Equiv.Perm.mul_apply, h1, hrr]
    exact Fin.ext hrb

theorem card_stabCls {c : ℕ} (hc : c < 6) :
    (Finset.univ.filter fun a : Fin 365211 => stabCls a.val = c).card = stabSizes[c]! := by
  have h := stabCardCheck_holds
  simp only [chkStabCard, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [← h c hc]
  have e : (Finset.univ.filter fun a : Fin 365211 => stabCls a.val = c).map Fin.valEmbedding =
      (Finset.range 365211).filter fun a => stabCls a = c := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    exact ⟨fun ⟨b, hb, hba⟩ => hba ▸ ⟨b.2, hb⟩, fun ⟨ha, hc⟩ => ⟨⟨a, ha⟩, hc, rfl⟩⟩
  rw [← Finset.card_map Fin.valEmbedding, e]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  apply congrArg List.length
  apply List.filter_congr
  intro x _
  by_cases hx : stabCls x = c <;> simp [hx]

theorem stabSizes_dvd (x1 x2 x3 x4 x5 : Bool)
    (h : (1 + (if x1 then 810 else 0) + (if x2 then 768 else 0) + (if x3 then 25200 else 0) +
      (if x4 then 207360 else 0) + (if x5 then 131072 else 0)) ∣ 365211) :
    (x1 = false ∧ x2 = false ∧ x3 = false ∧ x4 = false ∧ x5 = false) ∨
      (x1 = true ∧ x2 = true ∧ x3 = true ∧ x4 = true ∧ x5 = true) := by
  revert h
  cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> cases x5 <;> decide

theorem orbit_cases {O : Finset (Fin 365211)}
    (hO : ∀ g ∈ TD6, g 0 = 0 → ∀ a ∈ O, g a ∈ O)
    (h0 : (0 : Fin 365211) ∈ O) (hdvd : O.card ∣ 365211) :
    O = {0} ∨ O = Finset.univ := by
  classical
  let B : ℕ → Prop := fun c => ∃ a ∈ O, stabCls a.val = c
  have hB : ∀ a : Fin 365211, a ∈ O ↔ B (stabCls a.val) := fun a =>
    ⟨fun ha => ⟨a, ha, rfl⟩, fun ⟨a', ha', h⟩ => by
      obtain ⟨g, hg, hg0, hga⟩ := exists_stab_image (a := a') (b := a) h
      exact hga ▸ hO g hg hg0 a' ha'⟩
  have hfib : ∀ c, c < 6 → (O.filter fun a : Fin 365211 => stabCls a.val = c).card =
      if B c then stabSizes[c]! else 0 := by
    intro c hc6
    split_ifs with hc
    · rw [← card_stabCls hc6]
      apply congrArg Finset.card
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨(hB a).mpr (h ▸ hc), h⟩⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a ha hac
      exact hc ⟨a, ha, hac⟩
  have hcard : O.card = ∑ c ∈ Finset.range 6, if B c then stabSizes[c]! else 0 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun a : Fin 365211 => stabCls a.val)
      (t := Finset.range 6)
      (fun a _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (stabCls_le a.val)))]
    refine Finset.sum_congr rfl fun c hc => ?_
    exact hfib c (Finset.mem_range.mp hc)
  have hB0 : B 0 := ⟨0, h0, by rw [Fin.val_zero]; exact stabCls_zero⟩
  have hsum : O.card = 1 + (if decide (B 1) then 810 else 0) + (if decide (B 2) then 768 else 0) +
      (if decide (B 3) then 25200 else 0) + (if decide (B 4) then 207360 else 0) +
      (if decide (B 5) then 131072 else 0) := by
    rw [hcard]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_pos hB0,
      decide_eq_true_eq]
    rfl
  rcases stabSizes_dvd (decide (B 1)) (decide (B 2)) (decide (B 3)) (decide (B 4))
    (decide (B 5)) (hsum ▸ hdvd) with ⟨h1, h2, h3, h4, h5⟩ | hall
  · left
    simp only [decide_eq_false_iff_not] at h1 h2 h3 h4 h5
    ext a
    rw [Finset.mem_singleton]
    constructor
    · intro ha
      have hba := (hB a).mp ha
      have hk : stabCls a.val = 0 := by
        have hle := stabCls_le a.val
        generalize stabCls a.val = k at hba hle ⊢
        interval_cases k
        · rfl
        · exact absurd hba h1
        · exact absurd hba h2
        · exact absurd hba h3
        · exact absurd hba h4
        · exact absurd hba h5
      exact Fin.ext (stabCls_eq_zero_iff.mp hk)
    · rintro rfl
      exact h0
  · right
    simp only [decide_eq_true_eq] at hall
    obtain ⟨h1, h2, h3, h4, h5⟩ := hall
    refine Finset.eq_univ_of_forall fun a => (hB a).mpr ?_
    have hle := stabCls_le a.val
    generalize stabCls a.val = k at hle ⊢
    interval_cases k <;> assumption

end Classes

section Group

theorem stabGens_nc :
    ∃ s1 s2 : Fin 365211, tvImg s1 0 = 0 ∧ tvImg s2 0 = 0 ∧ tvImg s1 s2 ≠ s2 := by
  have h := stabNcCheck_holds
  simp only [chkStabNc, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨hsz, hne⟩ := h
  obtain ⟨-, hgens, -⟩ := stabTree_unpack
  have h0 := hgens 0 (by omega)
  have h1 := hgens 1 (by omega)
  exact ⟨⟨stabGens[0]!, h0.1⟩, ⟨stabGens[1]!, h1.1⟩, h0.2, h1.2, hne⟩

theorem tvImg_eq_of_commute {a b : Fin 365211} (h : tvP a * tvP b = tvP b * tvP a) :
    tvImg a b = b := by
  have h1 := mul_tvP_mul_inv (tvP_mem a) b
  rw [h, mul_inv_cancel_right] at h1
  have h2 := congrArg Fin.val (tvP_injective h1)
  rw [tvP_apply] at h2
  exact h2.symm

theorem eq_TD6_of_stabilizer_zero_le {K : Subgroup (Equiv.Perm (Fin 365211))} (hK : K ≤ TD6)
    [IsSimpleGroup K] (hstab : ∀ g ∈ TD6, g 0 = 0 → g ∈ K) : K = TD6 := by
  classical
  have hfix : ∀ g : Fin 365211, tvImg g 0 = 0 → tvP g ∈ K := fun g hg =>
    hstab _ (tvP_mem g) (Fin.ext (by rw [tvP_apply]; exact hg))
  let O : Finset (Fin 365211) := Finset.univ.filter fun a => ∃ g ∈ K, g 0 = a
  have hOmem : ∀ a, a ∈ O ↔ ∃ g ∈ K, g 0 = a := fun a => by
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
  have h0 : (0 : Fin 365211) ∈ O := (hOmem 0).mpr ⟨1, K.one_mem, rfl⟩
  have hO : ∀ g ∈ TD6, g 0 = 0 → ∀ a ∈ O, g a ∈ O := by
    intro g hg hg0 a ha
    obtain ⟨h, hh, rfl⟩ := (hOmem a).mp ha
    exact (hOmem _).mpr ⟨g * h, K.mul_mem (hstab g hg hg0) hh, rfl⟩
  have hsK : Nat.card (MulAction.stabilizer K (0 : Fin 365211)) =
      Nat.card (MulAction.stabilizer TD6 (0 : Fin 365211)) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨⟨k.1.1, hK k.1.2⟩, k.2⟩
        invFun := fun g => ⟨⟨g.1.1, hstab _ g.1.2 g.2⟩, g.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have horbT : (MulAction.orbit TD6 (0 : Fin 365211)).ncard = 365211 := by
    have : MulAction.orbit TD6 (0 : Fin 365211) = Set.univ := by
      refine Set.eq_univ_of_forall fun a => ?_
      obtain ⟨g, hg, hga⟩ := exists_mem_TD6_apply_zero_eq a
      exact ⟨⟨g, hg⟩, hga⟩
    rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have horbK : (MulAction.orbit K (0 : Fin 365211)).ncard = O.card := by
    have : MulAction.orbit K (0 : Fin 365211) = (O : Set (Fin 365211)) := by
      ext a
      rw [Finset.mem_coe, hOmem]
      exact ⟨fun ⟨k, hk⟩ => ⟨k.1, k.2, hk⟩, fun ⟨g, hg, hga⟩ => ⟨⟨g, hg⟩, hga⟩⟩
    rw [this, Set.ncard_coe_finset]
  have hcK := card_stabilizer_mul_ncard_orbit K
  have hcT := card_stabilizer_mul_ncard_orbit TD6
  rw [hsK, horbK] at hcK
  rw [horbT] at hcT
  have hspos : 0 < Nat.card (MulAction.stabilizer TD6 (0 : Fin 365211)) := Nat.card_pos
  have hdvd : O.card ∣ 365211 := by
    have h := Subgroup.card_dvd_of_le hK
    rw [← hcK, ← hcT] at h
    exact Nat.dvd_of_mul_dvd_mul_left hspos h
  rcases orbit_cases hO h0 hdvd with hsing | huniv
  ·
    exfalso
    have hKfix : ∀ k ∈ K, k 0 = 0 := by
      intro k hk
      have : k 0 ∈ O := (hOmem _).mpr ⟨k, hk, rfl⟩
      rw [hsing, Finset.mem_singleton] at this
      exact this
    let x : K := ⟨tvP 0, hstab _ (tvP_mem 0) (tvP_self 0)⟩
    have hx : x ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      have h1 := mul_tvP_mul_inv (hK c.2) 0
      rw [hKfix c.1 c.2] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
    have hcenter : Subgroup.center K = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with hbot | htop
      · exfalso
        rw [hbot, Subgroup.mem_bot] at hx
        exact tvP_ne_one 0 (congrArg Subtype.val hx)
      · exact htop
    obtain ⟨s1, s2, h1, h2, hn⟩ := stabGens_nc
    let y1 : K := ⟨tvP s1, hfix s1 h1⟩
    let y2 : K := ⟨tvP s2, hfix s2 h2⟩
    have hy1 : y1 ∈ Subgroup.center K := hcenter ▸ Subgroup.mem_top y1
    have hc := Subgroup.mem_center_iff.mp hy1 y2
    exact hn (tvImg_eq_of_commute (congrArg Subtype.val hc).symm)
  ·
    refine Subgroup.eq_of_le_of_card_ge hK ?_
    rw [← hcK, ← hcT, huniv, Finset.card_univ, Fintype.card_fin]

theorem eq_TD6_of_stabilizer_le {K : Subgroup (Equiv.Perm (Fin 365211))} (hK : K ≤ TD6)
    [IsSimpleGroup K] (k : Fin 365211) (hstab : ∀ g ∈ TD6, g k = k → g ∈ K) : K = TD6 := by
  obtain ⟨c, hc, hck⟩ := exists_mem_TD6_apply_zero_eq k
  let f := (MulAut.conj c⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj c⁻¹).injective
  let K' := K.map f
  haveI : IsSimpleGroup K' := (Subgroup.equivMapOfInjective K f hf).symm.isSimpleGroup
  have hmemT : ∀ {g : Equiv.Perm (Fin 365211)} (d : Equiv.Perm (Fin 365211)), d ∈ TD6 →
      g ∈ TD6 → d * g * d⁻¹ ∈ TD6 := fun d hd hg =>
    TD6.mul_mem (TD6.mul_mem hd hg) (TD6.inv_mem hd)
  have hK' : K' ≤ TD6 := by
    rintro _ ⟨g, hg, rfl⟩
    simpa [f, MulAut.conj_apply] using hmemT c⁻¹ (TD6.inv_mem hc) (hK hg)
  have hstab' : ∀ g ∈ TD6, g 0 = 0 → g ∈ K' := by
    intro g hg hg0
    refine ⟨c * g * c⁻¹, hstab _ (hmemT c hc hg) ?_, ?_⟩
    · rw [← hck]
      simp [hg0]
    · simp [f, MulAut.conj_apply, mul_assoc]
  have hT := eq_TD6_of_stabilizer_zero_le hK' hstab'
  refine le_antisymm hK fun g hg => ?_
  have : c⁻¹ * g * c⁻¹⁻¹ ∈ K' := by
    rw [hT]
    exact hmemT c⁻¹ (TD6.inv_mem hc) hg
  obtain ⟨g', hg', he⟩ := this
  simp only [f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at he
  have : g' = g := by
    have := congrArg (fun x => c * x * c⁻¹) he
    simpa [mul_assoc] using this
  exact this ▸ hg'

end Group

section Order

theorem stabOrd_unpack :
    (∀ c < 6, (∀ x < 4096, prodPow 0 (stabRep c) stabOrd[c]! x = x) ∧
      (stabOrd[c]! = 1 ∨ (stabOrd[c]! = 4 ∧ ∃ x < 4096, prodPow 0 (stabRep c) 2 x ≠ x) ∨
        (stabOrd[c]! ≠ 1 ∧ stabOrd[c]! ≠ 4 ∧ ∃ x < 4096, prodStep 0 (stabRep c) x ≠ x))) ∧
    linePair 31899 = (fV 0, fV 1) ∧ stabCls 31899 = 5 := by
  have h := stabOrdCheck_holds
  simp only [chkStabOrd, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun c hc => ?_, h3, h4⟩
  have := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at this
  obtain ⟨hA, hB⟩ := this
  refine ⟨hA, ?_⟩
  by_cases h1 : stabOrd[c]! = 1
  · exact Or.inl h1
  · by_cases h4 : stabOrd[c]! = 4
    · simp [h1, h4, List.any_eq_true] at hB
      exact Or.inr (Or.inl ⟨h4, hB⟩)
    · simp [h1, h4, List.any_eq_true] at hB
      exact Or.inr (Or.inr ⟨h1, h4, hB⟩)

theorem prodStep_lt {a b x : ℕ} (ha : a < 365211) (hb : b < 365211) (hx : x < 4096) :
    prodStep a b x < 4096 := by
  obtain ⟨-, ha1, ha2, ha3, -⟩ := lineFacts.entry a ha
  obtain ⟨-, hb1, hb2, hb3, -⟩ := lineFacts.entry b hb
  unfold prodStep
  exact sgl_lt (by omega) (by omega) (sgl_lt (by omega) (by omega) hx)

theorem prodPow_lt {a b : ℕ} (ha : a < 365211) (hb : b < 365211) :
    ∀ n x, x < 4096 → prodPow a b n x < 4096 := by
  intro n
  induction n with
  | zero => intro x hx; exact hx
  | succ n ih => intro x hx; exact ih _ (prodStep_lt ha hb hx)

theorem dec12_prodStep {a b : ℕ} (ha : a < 365211) (hb : b < 365211) (x : ℕ) :
    dec12 (prodStep a b x) = (siegelK a * siegelK b) (dec12 x) := by
  obtain ⟨-, -, -, -, hqa1, hqa2, hba, -⟩ := lineFacts.entry a ha
  obtain ⟨-, -, -, -, hqb1, hqb2, hbb, -⟩ := lineFacts.entry b hb
  show _ = siegelK a (siegelK b (dec12 x))
  have e1 : siegelK b (dec12 x) = dec12 (sgl (linePair b).1 (linePair b).2 x) :=
    siegelEquiv_dec12 hqb1 hqb2 hbb x
  rw [e1]
  exact (siegelEquiv_dec12 hqa1 hqa2 hba _).symm

theorem dec12_prodPow {a b : ℕ} (ha : a < 365211) (hb : b < 365211) (n x : ℕ) :
    dec12 (prodPow a b n x) = ((siegelK a * siegelK b) ^ n) (dec12 x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    show dec12 (prodPow a b n (prodStep a b x)) = _
    rw [ih, dec12_prodStep ha hb, pow_succ]
    rfl

theorem pow_eq_one_of_prodPow {a b n : ℕ} (ha : a < 365211) (hb : b < 365211)
    (h : ∀ x < 4096, prodPow a b n x = x) : (siegelK a * siegelK b) ^ n = 1 := by
  refine LinearEquiv.ext fun y => ?_
  obtain ⟨x, hx, rfl⟩ := dec12_surj y
  rw [← dec12_prodPow ha hb, h x hx]
  rfl

theorem pow_ne_one_of_prodPow {a b n x : ℕ} (ha : a < 365211) (hb : b < 365211) (hx : x < 4096)
    (h : prodPow a b n x ≠ x) : (siegelK a * siegelK b) ^ n ≠ 1 := by
  intro h1
  apply h
  have h2 := dec12_prodPow ha hb n x
  rw [h1] at h2
  exact eq_of_dec12_eq (prodPow_lt ha hb n x hx) hx h2

theorem tvP_mul_pow_eq_one_iff {a b : Fin 365211} (n : ℕ) :
    (tvP a * tvP b) ^ n = 1 ↔ (siegelK a.val * siegelK b.val) ^ n = 1 := by
  have e : tvP a * tvP b = omegaToPerm (⟨siegelK a.val, siegelK_mem_omega a.2⟩ *
      ⟨siegelK b.val, siegelK_mem_omega b.2⟩) := by
    rw [map_mul]
    rfl
  rw [e, ← map_pow, ← map_one omegaToPerm, omegaToPerm_injective.eq_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem orderOf_of_pow {G : Type*} [Group G] {x : G} {o : ℕ} (ho : o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4)
    (h1 : x ^ o = 1)
    (h2 : o = 1 ∨ (o = 4 ∧ x ^ 2 ≠ 1) ∨ (o ≠ 1 ∧ o ≠ 4 ∧ x ≠ 1)) : orderOf x = o := by
  rcases ho with rfl | rfl | rfl | rfl
  · exact orderOf_eq_one_iff.mpr (by simpa using h1)
  · have hne : x ≠ 1 := by
      rcases h2 with h | ⟨h, _⟩ | ⟨_, _, h⟩
      · omega
      · omega
      · exact h
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime h1 hne
  · have hne : x ≠ 1 := by
      rcases h2 with h | ⟨h, _⟩ | ⟨_, _, h⟩
      · omega
      · omega
      · exact h
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime h1 hne
  · have hne : x ^ 2 ≠ 1 := by
      rcases h2 with h | ⟨_, h⟩ | ⟨_, h, _⟩
      · omega
      · exact h
      · omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hne) (by simpa using h1)

theorem orderOf_tvP_mul_tvP_rep {c : ℕ} (hc : c < 6) (hr : stabRep c < 365211) :
    orderOf (tvP 0 * tvP ⟨stabRep c, hr⟩) = stabOrd[c]! := by
  obtain ⟨hall, -⟩ := stabOrd_unpack
  obtain ⟨hA, hB⟩ := hall c hc
  have h0 : (0 : ℕ) < 365211 := by norm_num
  have hmem : stabOrd[c]! = 1 ∨ stabOrd[c]! = 2 ∨ stabOrd[c]! = 3 ∨ stabOrd[c]! = 4 := by
    interval_cases c <;> decide
  have key : ∀ n : ℕ, (tvP 0 * tvP ⟨stabRep c, hr⟩) ^ n = 1 ↔
      (siegelK 0 * siegelK (stabRep c)) ^ n = 1 := fun n =>
    tvP_mul_pow_eq_one_iff (a := 0) (b := ⟨stabRep c, hr⟩) n
  refine orderOf_of_pow hmem ?_ ?_
  · exact (key _).mpr (pow_eq_one_of_prodPow h0 hr hA)
  · rcases hB with h | ⟨h, x, hx, hne⟩ | ⟨h1, h4, x, hx, hne⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h, fun h' => pow_ne_one_of_prodPow h0 hr hx hne ((key 2).mp h')⟩)
    · refine Or.inr (Or.inr ⟨h1, h4, fun h' => ?_⟩)
      exact pow_ne_one_of_prodPow (n := 1) h0 hr hx hne ((key 1).mp (by rw [pow_one]; exact h'))

theorem orderOf_tvP_mul_tvP (a : Fin 365211) :
    orderOf (tvP 0 * tvP a) = stabOrd[stabCls a.val]! := by
  obtain ⟨hreps, -, -⟩ := stabTree_unpack
  have hc6 : stabCls a.val < 6 := Nat.lt_succ_of_le (stabCls_le a.val)
  obtain ⟨hr, hrc⟩ := hreps _ hc6
  obtain ⟨g, hg, hg0, hga⟩ :=
    exists_stab_image (a := ⟨stabRep (stabCls a.val), hr⟩) (b := a) hrc
  have e : g * (tvP 0 * tvP ⟨stabRep (stabCls a.val), hr⟩) * g⁻¹ = tvP 0 * tvP a := by
    have h0 := mul_tvP_mul_inv hg 0
    have h1 := mul_tvP_mul_inv hg ⟨stabRep (stabCls a.val), hr⟩
    rw [hg0] at h0
    rw [hga] at h1
    calc g * (tvP 0 * tvP ⟨stabRep (stabCls a.val), hr⟩) * g⁻¹
        = (g * tvP 0 * g⁻¹) * (g * tvP ⟨stabRep (stabCls a.val), hr⟩ * g⁻¹) := by group
      _ = tvP 0 * tvP a := by rw [h0, h1]
  have e' : orderOf (MulAut.conj g (tvP 0 * tvP ⟨stabRep (stabCls a.val), hr⟩)) =
      orderOf (tvP 0 * tvP a) := by
    rw [MulAut.conj_apply, e]
  rw [MulEquiv.orderOf_eq] at e'
  rw [← e']
  exact orderOf_tvP_mul_tvP_rep hc6 hr

theorem orderOf_tvP_mul_tvP_eq_three_iff (a : Fin 365211) :
    orderOf (tvP 0 * tvP a) = 3 ↔ stabCls a.val = 5 := by
  rw [orderOf_tvP_mul_tvP]
  have hle := stabCls_le a.val
  generalize stabCls a.val = k at hle ⊢
  interval_cases k <;> decide

end Order

def stdOpp : Fin 365211 := 31899

section Pairs

theorem linePair_stdOpp : linePair stdOpp.val = (fV 0, fV 1) := stabOrd_unpack.2.1

theorem stabCls_stdOpp : stabCls stdOpp.val = 5 := stabOrd_unpack.2.2

theorem exists_mem_TD6_pair {kt ku : Fin 365211} (h : orderOf (tvP kt * tvP ku) = 3) :
    ∃ g ∈ TD6, g 0 = kt ∧ g stdOpp = ku := by
  obtain ⟨g₁, hg₁, hg₁0⟩ := exists_mem_TD6_apply_zero_eq kt
  have hg₁a : g₁ (g₁⁻¹ ku) = ku := by simp
  have hord : orderOf (tvP 0 * tvP (g₁⁻¹ ku)) = 3 := by
    have e : g₁ * (tvP 0 * tvP (g₁⁻¹ ku)) * g₁⁻¹ = tvP kt * tvP ku := by
      have h0 := mul_tvP_mul_inv hg₁ 0
      have h1 := mul_tvP_mul_inv hg₁ (g₁⁻¹ ku)
      rw [hg₁0] at h0
      rw [hg₁a] at h1
      calc g₁ * (tvP 0 * tvP (g₁⁻¹ ku)) * g₁⁻¹
          = (g₁ * tvP 0 * g₁⁻¹) * (g₁ * tvP (g₁⁻¹ ku) * g₁⁻¹) := by group
        _ = tvP kt * tvP ku := by rw [h0, h1]
    have e' : orderOf (MulAut.conj g₁ (tvP 0 * tvP (g₁⁻¹ ku))) = orderOf (tvP kt * tvP ku) := by
      rw [MulAut.conj_apply, e]
    rw [MulEquiv.orderOf_eq] at e'
    rw [e', h]
  have hcls : stabCls (g₁⁻¹ ku).val = 5 := (orderOf_tvP_mul_tvP_eq_three_iff _).mp hord
  obtain ⟨g₂, hg₂, hg₂0, hg₂s⟩ :=
    exists_stab_image (a := stdOpp) (b := g₁⁻¹ ku) (stabCls_stdOpp.trans hcls.symm)
  refine ⟨g₁ * g₂, TD6.mul_mem hg₁ hg₂, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hg₂0, hg₁0]
  · rw [Equiv.Perm.mul_apply, hg₂s, hg₁a]

end Pairs

end CFSG.GF2Type.SmithTypeE.DMod
