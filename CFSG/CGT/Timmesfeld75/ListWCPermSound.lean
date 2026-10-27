module

public import CFSG.CGT.Timmesfeld75.ListWCPermMask

public section

namespace CFSG.CGT.Timmesfeld75.WCCheck

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

variable {D : Data} {M : Subgroup (Equiv.Perm (Fin D.n))} {genG : ℤ → M}

section

variable (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l))
  (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (hF : Facts D)
include hn hgen hinv hF

theorem core_of_facts {T : Subgroup M} (hT : IsWC T) (h4 : 4 ≤ Nat.card T)
    (hTS : T ≤ S0 D genG) :
    Nat.card T = 16 ∧ ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → IsConj x y := by
  classical
  have hT1 := ne_bot_of_four_le_card h4
  have hz := z_mem_of_le hn hgen hinv hF hT hT1 hTS
  set f : List (ℕ × List ℤ) → Bool := fun c => decide (∃ q ∈ c, eltG (pcG D genG) q.1 ∈ T)
    with hf
  set J := D.cls.map f with hJdef
  have hJ : J ∈ allMasks D.cls.length := by
    have h := mem_allMasks J
    rwa [hJdef, List.length_map] at h
  have hsel : selCls D J = D.cls.filter f := selCls_map D f
  have hidx : ∀ i, i ∈ idxU D J ↔ i = D.zIdx ∨ ∃ c ∈ D.cls, f c = true ∧ ∃ q ∈ c, q.1 = i := by
    intro i
    simp only [idxU, hsel, List.mem_cons, List.mem_flatMap, List.mem_filter, List.mem_map]
    constructor
    · rintro (h | ⟨c, ⟨hc, hfc⟩, q, hq, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨c, hc, hfc, q, hq, rfl⟩
    · rintro (h | ⟨c, hc, hfc, q, hq, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨c, ⟨hc, hfc⟩, q, hq, rfl⟩
  have hmemT : ∀ x : M, x ∈ T ↔ x = 1 ∨ ∃ i ∈ idxU D J, eltG (pcG D genG) i = x := by
    intro x
    constructor
    · intro hx
      rcases mem_allowed hn hgen hinv hF hT hz hTS hx with h | h | ⟨c, hc, q, hq, hqx⟩
      · exact Or.inl h
      · exact Or.inr ⟨D.zIdx, (hidx _).2 (Or.inl rfl), h.symm⟩
      · refine Or.inr ⟨q.1, (hidx _).2 (Or.inr ⟨c, hc, ?_, q, hq, rfl⟩), hqx⟩
        rw [hf, decide_eq_true_eq]
        exact ⟨q, hq, hqx ▸ hx⟩
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact T.one_mem
      · rcases (hidx i).1 hi with rfl | ⟨c, hc, hfc, q, hq, rfl⟩
        · exact hz
        · rw [hf, decide_eq_true_eq] at hfc
          obtain ⟨p, hp, hpT⟩ := hfc
          exact mem_of_mem_cls hn hgen hinv hF hT hz hc hp hpT hq
  have hsub : List.Sublist (idxU D J) (D.zIdx :: (D.cls.flatMap fun c => c.map Prod.fst)) := by
    rw [idxU, hsel]
    exact (List.Sublist.flatMap (List.filter_sublist) _).cons_cons _
  have hnd0 := hF.idxNodup
  have hnd : (idxU D J).Nodup := (List.nodup_cons.1 hnd0).2.sublist hsub
  have h0 : 0 ∉ idxU D J := fun h => (List.nodup_cons.1 hnd0).1 (hsub.subset h)
  have hbd : ∀ i ∈ idxU D J, i < 2 ^ D.pc.length := by
    intro i hi
    rcases List.mem_cons.1 (hsub.subset hi) with rfl | h
    · exact hF.zlt
    · exact hF.idxLt i h
  have hinj : ∀ i ∈ idxU D J, ∀ j ∈ idxU D J,
      eltG (pcG D genG) i = eltG (pcG D genG) j → i = j := fun i hi j hj hij =>
    eltG_inj hn hgen hF (hbd i hi) (hbd j hj) hij
  have hcard : Nat.card T = (idxU D J).length + 1 := by
    have hl : (1 :: (idxU D J).map (eltG (pcG D genG))).Nodup := by
      refine List.nodup_cons.2 ⟨fun h => ?_, hnd.map_on hinj⟩
      obtain ⟨i, hi, hi1⟩ := List.mem_map.1 h
      apply h0
      have := eltG_inj hn hgen hF (hbd i hi) (Nat.two_pow_pos _)
        (hi1.trans (eltG_zero _).symm)
      rwa [this] at hi
    rw [card_eq_length_of_mem_iff hl fun x => by rw [hmemT, List.mem_cons, List.mem_map]]
    simp
  have hmemU : ∀ {t : Table} {x : M}, Rep D.n t x → t.size = D.n →
      (memU D J t = true ↔ x ∈ T) := by
    intro t x ht hts
    rw [memU, Bool.or_eq_true, List.any_eq_true, hmemT]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact Or.inl (eq_of_beq ht (Rep.idT (G := M) hn) h)
      · exact Or.inr ⟨i, hi, eq_of_beq (rep_el hn hgen i) ht h⟩
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact Or.inl (beq_of_eq ht (Rep.idT (G := M) hn) hts size_idT')
      · exact Or.inr ⟨i, hi, beq_of_eq (rep_el hn hgen i) ht (size_el _) hts⟩
  obtain ⟨⟨J', v⟩, -, hJ', hok⟩ := hF.verdicts J hJ
  simp only at hJ'
  subst hJ'
  have hcontains : ∀ {i : ℕ}, (idxU D J).contains i = true → eltG (pcG D genG) i ∈ T :=
    fun hi => (hmemT _).2 (Or.inr ⟨_, List.elem_iff.1 hi, rfl⟩)
  cases v with
  | small =>
    simp only [verdictOK, decide_eq_true_eq] at hok
    omega
  | notClosed i j =>
    simp only [verdictOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
    obtain ⟨⟨hi, hj⟩, hU⟩ := hok
    have hprod := T.mul_mem (hcontains hi) (hcontains hj)
    have := (hmemU (Rep.compT (rep_el hn hgen i) (rep_el hn hgen j)) (size_compT' _ _)).2 hprod
    rw [hU] at this
    exact absurd this (by decide)
  | bad t y g =>
    simp only [verdictOK, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at hok
    obtain ⟨⟨⟨⟨ht, hy⟩, ht1⟩, hg⟩, hU⟩ := hok
    have htT := hcontains ht
    have ht1' : eltG (pcG D genG) t ≠ 1 := fun h =>
      ht1 (beq_iff_eq.1 (beq_of_eq (rep_el hn hgen t)
        (by rw [show eltG (pcG D genG) t = 1 from h]; exact Rep.idT (G := M) hn)
        (size_el _) size_idT'))
    have hrg := rep_wT hn hgen g
    have hrgi := rep_wT hn hgen (invWord g)
    rw [wG_invWord hinv] at hrgi
    have hgt : wG D genG g * eltG (pcG D genG) t = eltG (pcG D genG) t * wG D genG g :=
      eq_of_rep ((compT_eq_of_commT hg) ▸ Rep.compT hrg (rep_el hn hgen t))
        (Rep.compT (rep_el hn hgen t) hrg)
    have hgN := hT.centralizer_le_normalizer htT ht1'
      (Subgroup.mem_centralizer_singleton_iff.2 hgt)
    have hcT := conj_mem hgN (hcontains hy)
    have := (hmemU (Rep.compT (Rep.compT hrg (rep_el hn hgen y)) hrgi) (size_compT' _ _)).2 hcT
    unfold conjT at hU
    rw [hU] at this
    exact absurd this (by decide)
  | good d =>
    simp only [verdictOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
    obtain ⟨⟨h16, hlen⟩, hd⟩ := hok
    refine ⟨by rw [hcard, h16], ?_⟩
    have hconjz : ∀ x ∈ T, x ≠ 1 → IsConj (zG D genG) x := by
      intro x hx hx1
      rcases (hmemT x).1 hx with rfl | ⟨i, hi, rfl⟩
      · exact absurd rfl hx1
      rcases (hidx i).1 hi with rfl | ⟨c, hc, hfc, q, hq, rfl⟩
      · exact IsConj.refl _
      obtain ⟨⟨i₀, w₀⟩, rest, rfl⟩ := List.exists_cons_of_ne_nil (ne_nil_of_mem_cls hF hc)
      have hcs : (i₀, w₀) :: rest ∈ selCls D J := by
        rw [hsel, List.mem_filter]
        exact ⟨hc, hfc⟩
      obtain ⟨k, hk, hkc⟩ := List.getElem_of_mem hcs
      have hkd : k < d.length := by rw [hlen]; exact hk
      have hzip := hd _ (List.getElem_mem (l := d.zip (selCls D J))
        (by rw [List.length_zip, hlen, min_self]; exact hk))
      rw [List.getElem_zip] at hzip
      simp only [hkc] at hzip
      have hrd := rep_wT hn hgen d[k]
      have hrdi := rep_wT hn hgen (invWord d[k])
      rw [wG_invWord hinv] at hrdi
      have hd0 : wG D genG d[k] * zG D genG * (wG D genG d[k])⁻¹ = eltG (pcG D genG) i₀ :=
        eq_of_beq (Rep.compT (Rep.compT hrd (rep_el hn hgen D.zIdx)) hrdi)
          (rep_el hn hgen i₀) hzip
      obtain ⟨g, -, hgq⟩ := conj_of_mem_cls_head hn hgen hinv hF hc q hq
      exact (isConj_iff.2 ⟨_, hd0⟩).trans (isConj_iff.2 ⟨g, hgq⟩)
    intro x hx hx1 y hy hy1
    exact (hconjz x hx hx1).symm.trans (hconjz y hy hy1)

theorem wcOrderConj_of_facts (hM : ∃ m : ℕ, Odd m ∧ Nat.card M = 2 ^ D.pc.length * m) :
    WCOrderConj M 16 := by
  intro T hT h4
  obtain ⟨m, hm, hcardM⟩ := hM
  have hp := isPGroup_S0 hn hgen hinv hF
  have hidx : ¬ 2 ∣ (S0 D genG).index := by
    have h := (S0 D genG).card_mul_index
    rw [card_S0 hn hgen hF hinv, hcardM] at h
    have : (S0 D genG).index = m := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) h
    rw [this]
    exact hm.not_two_dvd_nat
  let P : Sylow 2 M := hp.toSylow hidx
  obtain ⟨Q, hTQ⟩ := (isPGroup_two_of_isElemAbelian hT.1).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M Q P
  have hT'S : conjSubgroup c T ≤ S0 D genG := by
    intro x hx
    have h1 : x ∈ conjSubgroup c (Q : Subgroup M) := Subgroup.map_mono hTQ hx
    have h2 : x ∈ ((c • Q : Sylow 2 M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul]
      exact h1
    rw [hc] at h2
    exact h2
  have hcard : Nat.card (conjSubgroup c T) = Nat.card T := card_conjSubgroup c T
  obtain ⟨h16, hconj⟩ := core_of_facts hn hgen hinv hF (hT.conj c) (hcard ▸ h4) hT'S
  refine ⟨hcard ▸ h16, fun x hx hx1 y hy hy1 => ?_⟩
  have hmem : ∀ w ∈ T, c * w * c⁻¹ ∈ conjSubgroup c T := fun w hw => by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hw
  have hne : ∀ w : M, w ≠ 1 → c * w * c⁻¹ ≠ 1 := fun w hw h => hw (by
    rw [show w = c⁻¹ * (c * w * c⁻¹) * c by group, h]
    group)
  exact (isConj_iff.2 ⟨c, rfl⟩).trans ((hconj _ (hmem x hx) (hne x hx1) _ (hmem y hy)
    (hne y hy1)).trans (isConj_iff.2 ⟨c, rfl⟩).symm)

end

theorem wcOrderConj_of_wcCheck (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l))
    (hinv : ∀ l, genG (-l) = (genG l)⁻¹)
    (hM : ∃ m : ℕ, Odd m ∧ Nat.card M = 2 ^ D.pc.length * m) (h : wcCheck D = true) :
    WCOrderConj M 16 :=
  wcOrderConj_of_facts hn hgen hinv (facts_of_wcCheck h) hM

end CFSG.CGT.Timmesfeld75.WCCheck
