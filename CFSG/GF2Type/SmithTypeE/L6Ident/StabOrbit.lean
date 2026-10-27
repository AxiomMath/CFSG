module

public import CFSG.GF2Type.SmithTypeE.LMod.T6
public import Certificates.Certificate38650

public section

namespace CFSG.GF2Type.SmithTypeE.L6Ident

open CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod

section Checks


theorem stab_reach : CFSG.SmithL6.K.Reach 1953 1953 (fun a => a == stabRep (stabCls a))
    (fun g u v => tvImg g 0 == 0 && tvImg g u == v && stabCls u == stabCls v) :=
  Certificates.certificate38650.1

theorem full_reach : CFSG.SmithL6.K.Reach 1953 1953 (· == 0) (fun g u v => tvImg g u == v) :=
  Certificates.certificate38650.2.1

theorem stabCardCheck_holds : chkStabCard = true := Certificates.certificate38650.2.2.1

theorem stabCommCheck_holds : chkStabComm = true := Certificates.certificate38650.2.2.2

end Checks

section Classes


theorem stabCls_le (a : ℕ) : stabCls a ≤ 6 := by
  unfold stabCls
  split_ifs <;> omega

theorem exists_mem_T6_apply_zero_eq (a : Fin 1953) : ∃ g ∈ T6, g 0 = a := by
  refine full_reach (fun j => ∀ hj : j < 1953, ∃ g ∈ T6, g 0 = ⟨j, hj⟩) ?_ ?_ a.val a.2 a.2
  · intro v _ hv _
    have : v = 0 := by simpa using hv
    subst this
    exact ⟨1, T6.one_mem, rfl⟩
  · intro g hg u hu v _ he hQ _
    obtain ⟨c, hc, hc0⟩ := hQ hu
    refine ⟨tvP ⟨g, hg⟩ * c, T6.mul_mem (tvP_mem _) hc, Fin.ext ?_⟩
    rw [Equiv.Perm.mul_apply, hc0, tvP_apply]
    exact beq_iff_eq.mp he

variable {O : Set (Fin 1953)}

theorem rep_mem_of_mem (hO : ∀ g : Fin 1953, tvImg g 0 = 0 → ∀ a ∈ O, tvP g a ∈ O)
    (a : Fin 1953) (ha : a ∈ O) : ∃ r ∈ O, r.val = stabRep (stabCls a) := by
  refine stab_reach (fun j => ∀ hj : j < 1953, (⟨j, hj⟩ : Fin 1953) ∈ O →
    ∃ r ∈ O, r.val = stabRep (stabCls j)) ?_ ?_ a.val a.2 a.2 ha
  · intro v _ hr hv hvO
    exact ⟨⟨v, hv⟩, hvO, beq_iff_eq.mp hr⟩
  · intro g hg u hu v _ he hQ hv hvO
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨⟨hg0, hgu⟩, hcls⟩ := he
    have hga : tvP ⟨g, hg⟩ ⟨v, hv⟩ = ⟨u, hu⟩ := by
      apply Fin.ext
      rw [tvP_apply]
      calc tvImg g v = tvImg g (tvImg g u) := by rw [hgu]
        _ = u := tvImg_tvImg hg hu
    obtain ⟨r, hrO, hr⟩ := hQ hu (hga ▸ hO ⟨g, hg⟩ hg0 _ hvO)
    exact ⟨r, hrO, hr.trans (by rw [hcls])⟩

theorem mem_of_rep_mem (hO : ∀ g : Fin 1953, tvImg g 0 = 0 → ∀ a ∈ O, tvP g a ∈ O)
    (a : Fin 1953) (ha : ∃ r ∈ O, r.val = stabRep (stabCls a)) : a ∈ O := by
  refine stab_reach (fun j => ∀ hj : j < 1953, (∃ r ∈ O, r.val = stabRep (stabCls j)) →
    (⟨j, hj⟩ : Fin 1953) ∈ O) ?_ ?_ a.val a.2 a.2 ha
  · intro v _ hroot hv ⟨r, hrO, hr⟩
    have : (⟨v, hv⟩ : Fin 1953) = r := Fin.ext ((beq_iff_eq.mp hroot).trans hr.symm)
    exact this ▸ hrO
  · intro g hg u hu v _ he hQ hv ⟨r, hrO, hr⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨⟨hg0, hgu⟩, hcls⟩ := he
    have huO := hQ hu ⟨r, hrO, hr.trans (by rw [hcls])⟩
    have : tvP ⟨g, hg⟩ ⟨u, hu⟩ = ⟨v, hv⟩ := Fin.ext (by rw [tvP_apply]; exact hgu)
    exact this ▸ hO ⟨g, hg⟩ hg0 _ huO

theorem mem_of_stabCls_eq (hO : ∀ g : Fin 1953, tvImg g 0 = 0 → ∀ a ∈ O, tvP g a ∈ O)
    {a b : Fin 1953} (ha : a ∈ O) (hab : stabCls b = stabCls a) : b ∈ O := by
  obtain ⟨r, hrO, hr⟩ := rep_mem_of_mem hO a ha
  exact mem_of_rep_mem hO b ⟨r, hrO, by rw [hr, hab]⟩

theorem stabCls_zero : stabCls 0 = 0 := by
  unfold stabCls
  exact if_pos rfl

theorem card_stabCls {c : ℕ} (hc : c < 7) :
    (Finset.univ.filter fun a : Fin 1953 => stabCls a = c).card = stabSizes[c]! := by
  have h := stabCardCheck_holds
  simp only [chkStabCard, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [← h c hc]
  have e : (Finset.univ.filter fun a : Fin 1953 => stabCls a = c).map Fin.valEmbedding =
      (Finset.range 1953).filter fun a => stabCls a = c := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    exact ⟨fun ⟨b, hb, hba⟩ => hba ▸ ⟨b.2, hb⟩, fun ⟨ha, hc⟩ => ⟨⟨a, ha⟩, hc, rfl⟩⟩
  rw [← Finset.card_map Fin.valEmbedding, e]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  apply congrArg List.length
  apply List.filter_congr
  intro x _
  by_cases hx : stabCls x = c <;> simp [hx]

theorem stabSizes_dvd (x1 x2 x3 x4 x5 x6 : Bool)
    (h : (1 + (if x1 then 30 else 0) + (if x2 then 30 else 0) + (if x3 then 420 else 0) +
      (if x4 then 480 else 0) + (if x5 then 480 else 0) + (if x6 then 512 else 0)) ∣ 1953) :
    (x3 = false ∧ x4 = false ∧ x5 = false ∧ x6 = false ∧ (x1 = false ∨ x2 = false)) ∨
      (x1 = true ∧ x2 = true ∧ x3 = true ∧ x4 = true ∧ x5 = true ∧ x6 = true) := by
  revert h
  cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> cases x5 <;> cases x6 <;> decide

theorem orbit_cases {O : Finset (Fin 1953)}
    (hO : ∀ g : Fin 1953, tvImg g 0 = 0 → ∀ a ∈ O, tvP g a ∈ O)
    (h0 : (0 : Fin 1953) ∈ O) (hdvd : O.card ∣ 1953) :
    (∀ a ∈ O, stabCls a ≤ 1) ∨ (∀ a ∈ O, stabCls a = 0 ∨ stabCls a = 2) ∨ O = Finset.univ := by
  classical
  have hO' : ∀ g : Fin 1953, tvImg g 0 = 0 → ∀ a ∈ (O : Set (Fin 1953)), tvP g a ∈ (O : Set _) :=
    fun g hg a ha => Finset.mem_coe.mpr (hO g hg a (Finset.mem_coe.mp ha))
  let B : ℕ → Prop := fun c => ∃ a ∈ O, stabCls a = c
  have hB : ∀ a : Fin 1953, a ∈ O ↔ B (stabCls a) := fun a =>
    ⟨fun ha => ⟨a, ha, rfl⟩, fun ⟨a', ha', h⟩ =>
      Finset.mem_coe.mp (mem_of_stabCls_eq hO' (Finset.mem_coe.mpr ha') h.symm)⟩
  have hfib : ∀ c, c < 7 → (O.filter fun a : Fin 1953 => stabCls a = c).card =
      if B c then stabSizes[c]! else 0 := by
    intro c hc7
    split_ifs with hc
    · rw [← card_stabCls hc7]
      apply congrArg Finset.card
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨(hB a).mpr (h ▸ hc), h⟩⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a ha hac
      exact hc ⟨a, ha, hac⟩
  have hcard : O.card = ∑ c ∈ Finset.range 7, if B c then stabSizes[c]! else 0 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun a : Fin 1953 => stabCls a)
      (t := Finset.range 7) (fun a _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (stabCls_le a)))]
    refine Finset.sum_congr rfl fun c hc => ?_
    exact hfib c (Finset.mem_range.mp hc)
  have hB0 : B 0 := ⟨0, h0, by rw [Fin.val_zero]; exact stabCls_zero⟩
  have hsum : O.card = 1 + (if decide (B 1) then 30 else 0) + (if decide (B 2) then 30 else 0) +
      (if decide (B 3) then 420 else 0) + (if decide (B 4) then 480 else 0) +
      (if decide (B 5) then 480 else 0) + (if decide (B 6) then 512 else 0) := by
    rw [hcard]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_pos hB0,
      decide_eq_true_eq]
    rfl
  rcases stabSizes_dvd (decide (B 1)) (decide (B 2)) (decide (B 3)) (decide (B 4))
    (decide (B 5)) (decide (B 6)) (hsum ▸ hdvd) with ⟨h3, h4, h5, h6, h12⟩ | hall
  · simp only [decide_eq_false_iff_not] at h3 h4 h5 h6 h12
    have hle : ∀ a ∈ O, stabCls a = 0 ∨ stabCls a = 1 ∨ stabCls a = 2 := by
      intro a ha
      have hba := (hB a).mp ha
      have hle := stabCls_le a
      obtain ⟨k, hk⟩ : ∃ k, stabCls a = k := ⟨_, rfl⟩
      rw [hk] at hba hle ⊢
      interval_cases k <;> simp_all
    rcases h12 with h1 | h2
    · refine Or.inr (Or.inl fun a ha => ?_)
      rcases hle a ha with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ (hB a).mp ha) h1
      · exact Or.inr h
    · refine Or.inl fun a ha => ?_
      rcases hle a ha with h | h | h
      · omega
      · omega
      · exact absurd (h ▸ (hB a).mp ha) h2
  · simp only [decide_eq_true_eq] at hall
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hall
    refine Or.inr (Or.inr (Finset.eq_univ_of_forall fun a => (hB a).mpr ?_))
    have hle := stabCls_le a
    obtain ⟨k, hk⟩ : ∃ k, stabCls a = k := ⟨_, rfl⟩
    rw [hk] at hle ⊢
    interval_cases k <;> assumption

end Classes

section Group


theorem tvImg_comm01 {a b : ℕ} (ha : a < 1953) (hb : b < 1953) (ha1 : stabCls a ≤ 1)
    (hb1 : stabCls b ≤ 1) : tvImg a b = b := by
  have h := stabCommCheck_holds
  simp only [chkStabComm, Bool.and_eq_true, List.all_eq_true, List.mem_filter, List.mem_range,
    decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1.1.1 a ⟨ha, ha1⟩ b ⟨hb, hb1⟩

theorem tvImg_comm02 {a b : ℕ} (ha : a < 1953) (hb : b < 1953)
    (ha1 : stabCls a = 0 ∨ stabCls a = 2) (hb1 : stabCls b = 0 ∨ stabCls b = 2) :
    tvImg a b = b := by
  have h := stabCommCheck_holds
  simp only [chkStabComm, Bool.and_eq_true, List.all_eq_true, List.mem_filter, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at h
  exact h.1.1.1.2 a ⟨ha, ha1⟩ b ⟨hb, hb1⟩

theorem tvImg_nc : tvImg 1 0 = 0 ∧ tvImg 94 0 = 0 ∧ tvImg 1 94 ≠ 94 := by
  have h := stabCommCheck_holds
  simp only [chkStabComm, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

theorem commute_tvP {a b : Fin 1953} (h : tvImg a b = b) : Commute (tvP a) (tvP b) := by
  have h1 := mul_tvP_mul_inv (tvP_mem a) b
  rw [show tvP a b = b from Fin.ext (by rw [tvP_apply]; exact h)] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem card_stabilizer_mul_ncard_orbit (H : Subgroup (Equiv.Perm (Fin 1953))) :
    Nat.card (MulAction.stabilizer H (0 : Fin 1953)) * (MulAction.orbit H (0 : Fin 1953)).ncard =
      Nat.card H := by
  rw [← MulAction.index_stabilizer]
  exact (MulAction.stabilizer H (0 : Fin 1953)).card_mul_index

theorem eq_T6_of_stabilizer_zero_le {K : Subgroup (Equiv.Perm (Fin 1953))} (hK : K ≤ T6)
    [IsSimpleGroup K] (hstab : ∀ g ∈ T6, g 0 = 0 → g ∈ K) : K = T6 := by
  classical
  have hfix : ∀ g : Fin 1953, tvImg g 0 = 0 → tvP g ∈ K := fun g hg =>
    hstab _ (tvP_mem g) (Fin.ext (by rw [tvP_apply]; exact hg))
  let O : Finset (Fin 1953) := Finset.univ.filter fun a => ∃ g ∈ K, g 0 = a
  have hOmem : ∀ a, a ∈ O ↔ ∃ g ∈ K, g 0 = a := fun a => by
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
  have h0 : (0 : Fin 1953) ∈ O := (hOmem 0).mpr ⟨1, K.one_mem, rfl⟩
  have hO : ∀ g : Fin 1953, tvImg g 0 = 0 → ∀ a ∈ O, tvP g a ∈ O := by
    intro g hg a ha
    obtain ⟨h, hh, rfl⟩ := (hOmem a).mp ha
    exact (hOmem _).mpr ⟨tvP g * h, K.mul_mem (hfix g hg) hh, rfl⟩
  have hsK : Nat.card (MulAction.stabilizer K (0 : Fin 1953)) =
      Nat.card (MulAction.stabilizer T6 (0 : Fin 1953)) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨⟨k.1.1, hK k.1.2⟩, k.2⟩
        invFun := fun g => ⟨⟨g.1.1, hstab _ g.1.2 g.2⟩, g.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have horbT : (MulAction.orbit T6 (0 : Fin 1953)).ncard = 1953 := by
    have : MulAction.orbit T6 (0 : Fin 1953) = Set.univ := by
      refine Set.eq_univ_of_forall fun a => ?_
      obtain ⟨g, hg, hga⟩ := exists_mem_T6_apply_zero_eq a
      exact ⟨⟨g, hg⟩, hga⟩
    rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have horbK : (MulAction.orbit K (0 : Fin 1953)).ncard = O.card := by
    have : MulAction.orbit K (0 : Fin 1953) = (O : Set (Fin 1953)) := by
      ext a
      rw [Finset.mem_coe, hOmem]
      exact ⟨fun ⟨k, hk⟩ => ⟨k.1, k.2, hk⟩, fun ⟨g, hg, hga⟩ => ⟨⟨g, hg⟩, hga⟩⟩
    rw [this, Set.ncard_coe_finset]
  have hcK := card_stabilizer_mul_ncard_orbit K
  have hcT := card_stabilizer_mul_ncard_orbit T6
  rw [hsK, horbK] at hcK
  rw [horbT] at hcT
  have hspos : 0 < Nat.card (MulAction.stabilizer T6 (0 : Fin 1953)) := Nat.card_pos
  have hdvd : O.card ∣ 1953 := by
    have h := Subgroup.card_dvd_of_le hK
    rw [← hcK, ← hcT] at h
    exact Nat.dvd_of_mul_dvd_mul_left hspos h
  rcases orbit_cases hO h0 hdvd with h01 | h02 | huniv
  rotate_left 2
  ·
    refine Subgroup.eq_of_le_of_card_ge hK ?_
    rw [← hcK, ← hcT, huniv, Finset.card_univ, Fintype.card_fin]
  all_goals
    exfalso
    have hcomm : ∀ a ∈ O, ∀ b ∈ O, tvImg a b = b := by
      intro a ha b hb
      first
        | exact tvImg_comm01 a.2 b.2 (h01 a ha) (h01 b hb)
        | exact tvImg_comm02 a.2 b.2 (h02 a ha) (h02 b hb)
    let x : K := ⟨tvP 0, hfix 0 (tvImg_comm01 (by norm_num) (by norm_num)
      (by simp [stabCls_zero]) (by simp [stabCls_zero]))⟩
    have hconj : ∀ u ∈ Group.conjugatesOfSet ({x} : Set K), ∃ a ∈ O, (u : Equiv.Perm _) = tvP a := by
      intro u hu
      obtain ⟨y, hy, hyu⟩ := Group.mem_conjugatesOfSet_iff.mp hu
      rw [Set.mem_singleton_iff] at hy
      subst hy
      obtain ⟨c, rfl⟩ := isConj_iff.mp hyu
      refine ⟨c.1 0, (hOmem _).mpr ⟨c.1, c.2, rfl⟩, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, x]
      exact mul_tvP_mul_inv (hK c.2) 0
    have hpw : (Group.conjugatesOfSet ({x} : Set K)).Pairwise Commute := by
      intro u hu v hv _
      obtain ⟨a, ha, hua⟩ := hconj u hu
      obtain ⟨b, hb, hvb⟩ := hconj v hv
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hua, hvb]
      exact commute_tvP (hcomm a ha b hb)
    have hcl := Subgroup.isMulCommutative_closure hpw
    have htop : Subgroup.normalClosure ({x} : Set K) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({x} : Set K))
        with hbot | htop
      · exfalso
        have hx : x ∈ Subgroup.normalClosure ({x} : Set K) := Subgroup.subset_normalClosure rfl
        rw [hbot, Subgroup.mem_bot] at hx
        have h1 : tvP 0 = 1 := congrArg Subtype.val hx
        obtain ⟨g, hg, hg1⟩ := exists_mem_T6_apply_zero_eq 1
        have h2 := mul_tvP_mul_inv hg 0
        rw [h1, mul_one, mul_inv_cancel, hg1, ← h1] at h2
        exact absurd (congrArg Fin.val (tvP_injective h2)) (by norm_num)
      · exact htop
    obtain ⟨hn1, hn94, hn⟩ := tvImg_nc
    have hm : ∀ y : K, y ∈ Subgroup.closure (Group.conjugatesOfSet ({x} : Set K)) := fun y => by
      have : y ∈ Subgroup.normalClosure ({x} : Set K) := htop ▸ Subgroup.mem_top y
      exact this
    let y1 : K := ⟨tvP 1, hfix 1 hn1⟩
    let y2 : K := ⟨tvP 94, hfix 94 hn94⟩
    have hc12 : y1 * y2 = y2 * y1 := by
      have := hcl.is_comm.comm (⟨y1, hm y1⟩ : Subgroup.closure _) ⟨y2, hm y2⟩
      exact congrArg Subtype.val this
    have h12 : tvP 1 * tvP 94 * (tvP 1)⁻¹ = tvP 94 := by
      have := congrArg Subtype.val hc12
      simp only [Subgroup.coe_mul, y1, y2] at this
      rw [this, mul_inv_cancel_right]
    rw [mul_tvP_mul_inv (tvP_mem 1)] at h12
    have := congrArg Fin.val (tvP_injective h12)
    rw [tvP_apply] at this
    exact hn this

theorem eq_T6_of_stabilizer_le {K : Subgroup (Equiv.Perm (Fin 1953))} (hK : K ≤ T6)
    [IsSimpleGroup K] (k : Fin 1953) (hstab : ∀ g ∈ T6, g k = k → g ∈ K) : K = T6 := by
  obtain ⟨c, hc, hck⟩ := exists_mem_T6_apply_zero_eq k
  let f := (MulAut.conj c⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj c⁻¹).injective
  let K' := K.map f
  haveI : IsSimpleGroup K' := (Subgroup.equivMapOfInjective K f hf).symm.isSimpleGroup
  have hmemT : ∀ {g : Equiv.Perm (Fin 1953)} (d : Equiv.Perm (Fin 1953)), d ∈ T6 → g ∈ T6 →
      d * g * d⁻¹ ∈ T6 := fun d hd hg => T6.mul_mem (T6.mul_mem hd hg) (T6.inv_mem hd)
  have hK' : K' ≤ T6 := by
    rintro _ ⟨g, hg, rfl⟩
    simpa [f, MulAut.conj_apply] using hmemT c⁻¹ (T6.inv_mem hc) (hK hg)
  have hstab' : ∀ g ∈ T6, g 0 = 0 → g ∈ K' := by
    intro g hg hg0
    refine ⟨c * g * c⁻¹, hstab _ (hmemT c hc hg) ?_, ?_⟩
    · rw [← hck]
      simp [hg0]
    · simp [f, MulAut.conj_apply, mul_assoc]
  have hT := eq_T6_of_stabilizer_zero_le hK' hstab'
  refine le_antisymm hK fun g hg => ?_
  have : c⁻¹ * g * c⁻¹⁻¹ ∈ K' := by
    rw [hT]
    exact hmemT c⁻¹ (T6.inv_mem hc) hg
  obtain ⟨g', hg', he⟩ := this
  simp only [f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at he
  have : g' = g := by
    have := congrArg (fun x => c * x * c⁻¹) he
    simpa [mul_assoc] using this
  exact this ▸ hg'

end Group

end CFSG.GF2Type.SmithTypeE.L6Ident
