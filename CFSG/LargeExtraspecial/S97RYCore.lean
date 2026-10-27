module

public import CFSG.LargeExtraspecial.S97RYBase

public section

namespace CFSG.LargeExtraspecial.S11.PairCheck

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75
  CFSG.CGT.Timmesfeld75.WCCheck

variable {D : Data} {M : Subgroup (Equiv.Perm (Fin D.n))} {genG : ℤ → M}

section

variable (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l))
  (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (hF : BaseFacts D)
include hn hgen hinv hF

theorem exists_mask {T : Subgroup M} (hT : IsWC T) (hT1 : T ≠ ⊥) (hTS : T ≤ S0 D genG) :
    ∃ J ∈ allMasks D.cls.length, (idxU D J).Nodup ∧ 0 ∉ idxU D J ∧
      (∀ i ∈ idxU D J, i < 2 ^ D.pc.length) ∧
      ∀ x : M, x ∈ T ↔ x = 1 ∨ ∃ i ∈ idxU D J, eltG (pcG D genG) i = x := by
  classical
  have hz := zG_mem_of_le hn hgen hinv hF hT hT1 hTS
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
      rcases mem_allowed_base hn hgen hinv hF hT hz hTS hx with h | h | ⟨c, hc, q, hq, hqx⟩
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
          exact mem_of_mem_cls_base hn hgen hinv hF hT hz hc hp hpT hq
  have hsub : List.Sublist (idxU D J) (D.zIdx :: (D.cls.flatMap fun c => c.map Prod.fst)) := by
    rw [idxU, hsel]
    exact (List.Sublist.flatMap (List.filter_sublist) _).cons_cons _
  have hnd0 := hF.idxNodup
  refine ⟨J, hJ, (List.nodup_cons.1 hnd0).2.sublist hsub,
    fun h => (List.nodup_cons.1 hnd0).1 (hsub.subset h), fun i hi => ?_, hmemT⟩
  rcases List.mem_cons.1 (hsub.subset hi) with rfl | h
  · exact hF.zlt
  · exact hF.idxLt i h

omit hinv in
theorem card_of_idx {K : Subgroup M} {L : List ℕ} (hnd : L.Nodup) (h0 : 0 ∉ L)
    (hbd : ∀ i ∈ L, i < 2 ^ D.pc.length)
    (hmem : ∀ x : M, x ∈ K ↔ x = 1 ∨ ∃ i ∈ L, eltG (pcG D genG) i = x) :
    Nat.card K = L.length + 1 := by
  have hinj : ∀ i ∈ L, ∀ j ∈ L, eltG (pcG D genG) i = eltG (pcG D genG) j → i = j :=
    fun i hi j hj hij => eltG_inj_base hn hgen hF (hbd i hi) (hbd j hj) hij
  have hl : (1 :: L.map (eltG (pcG D genG))).Nodup := by
    refine List.nodup_cons.2 ⟨fun h => ?_, hnd.map_on hinj⟩
    obtain ⟨i, hi, hi1⟩ := List.mem_map.1 h
    apply h0
    have := eltG_inj_base hn hgen hF (hbd i hi) (Nat.two_pow_pos _)
      (hi1.trans (eltG_zero _).symm)
    rwa [this] at hi
  rw [card_eq_length_of_mem_iff hl fun x => by rw [hmem, List.mem_cons, List.mem_map]]
  simp

end

theorem memU_iff_of_mask (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l))
    {T : Subgroup M} {J : List Bool}
    (hmemT : ∀ x : M, x ∈ T ↔ x = 1 ∨ ∃ i ∈ idxU D J, eltG (pcG D genG) i = x)
    {t : Table} {x : M} (ht : Rep D.n t x) (hts : t.size = D.n) :
    memU D J t = true ↔ x ∈ T := by
  rw [memU, Bool.or_eq_true, List.any_eq_true, hmemT]
  constructor
  · rintro (h | ⟨i, hi, h⟩)
    · exact Or.inl (eq_of_beq ht (Rep.idT (G := M) hn) h)
    · exact Or.inr ⟨i, hi, eq_of_beq (rep_el hn hgen i) ht h⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact Or.inl (beq_of_eq ht (Rep.idT (G := M) hn) hts size_idT')
    · exact Or.inr ⟨i, hi, beq_of_eq (rep_el hn hgen i) ht (size_el _) hts⟩

end CFSG.LargeExtraspecial.S11.PairCheck
