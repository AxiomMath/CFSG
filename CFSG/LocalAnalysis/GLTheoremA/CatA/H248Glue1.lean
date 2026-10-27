module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem catalogIs_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) {Q : TauCeti.CFSGIndex → Prop}
    (h : catalogIs T Q) : catalogIs S Q := by
  unfold catalogIs at h ⊢
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.trans f⟩⟩

theorem isChevSimple_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (q : ℕ)
    (h : IsChevSimple q T) : IsChevSimple q S := by
  unfold IsChevSimple at h ⊢
  rcases h with h | h
  · exact Or.inl (catalogIs_of_mulEquiv e h)
  · exact Or.inr (catalogIs_of_mulEquiv e h)

theorem catRankOneGroup_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (q : ℕ)
    (h : CatRankOneGroup q T) : CatRankOneGroup q S :=
  catalogIs_of_mulEquiv e h

theorem isU3Shape_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (p q : ℕ)
    (h : IsU3Shape p q T) : IsU3Shape p q S := by
  obtain ⟨Q, hQp, hdvd, hT⟩ := h
  exact ⟨Q, hQp, hdvd, catalogIs_of_mulEquiv e hT⟩

theorem le_pRank_of_elemAbelian {H : Type} [Group H] [Finite H] {p k : ℕ} (hp : 2 ≤ p)
    {H0 E : Subgroup H} (hE0 : E ≤ H0) (hE : CFSG.Open.IsElemAbelian p E)
    (hcard : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H0 := by
  unfold CFSG.Open.pRank
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup H, E ≤ H0 ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ k} := by
    refine ⟨Nat.card H, ?_⟩
    rintro m ⟨E', -, -, hE'⟩
    have h1 : Nat.card E' ≤ Nat.card H := Subgroup.card_le_card_group E'
    have h2 : m < p ^ m := Nat.lt_pow_self (by omega)
    have h3 : p ^ m ≤ Nat.card H := by
      rw [← hE']; exact h1
    omega
  exact le_csSup hbdd ⟨E, hE0, hE, hcard⟩

theorem isElemAbelian_map {H K : Type} [Group H] [Group K] (f : H →* K) (hf : Function.Injective f)
    {p : ℕ} {E : Subgroup H} (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  obtain ⟨hcomm, hexp⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    have hxy : x * y = y * x := by
      simpa using congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]

theorem pRank_le_of_mulEquiv {A B : Type} [Group A] [Finite A] [Group B] [Finite B] (e : A ≃* B)
    (p : ℕ) (hp : 2 ≤ p) : CFSG.Open.pRank p (⊤ : Subgroup A) ≤ CFSG.Open.pRank p (⊤ : Subgroup B) := by
  refine csSup_le' ?_
  rintro k ⟨E, -, hE, hcard⟩
  have hinj : Function.Injective (e.toMonoidHom) := e.injective
  have hEm : CFSG.Open.IsElemAbelian p (E.map e.toMonoidHom) := isElemAbelian_map _ hinj hE
  have hcardm : Nat.card (E.map e.toMonoidHom) = p ^ k := by
    rw [← hcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective E _ hinj).toEquiv).symm
  exact le_pRank_of_elemAbelian hp le_top hEm hcardm

theorem pRank_eq_of_mulEquiv {A B : Type} [Group A] [Finite A] [Group B] [Finite B] (e : A ≃* B)
    (p : ℕ) (hp : 2 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup A) = CFSG.Open.pRank p (⊤ : Subgroup B) :=
  le_antisymm (pRank_le_of_mulEquiv e p hp) (pRank_le_of_mulEquiv e.symm p hp)

theorem isoInvariant_isCatalogGroup : CFSG.KCore.IsoInvariant (@CFSG.Open.IsCatalogGroup) := by
  intro X Y _ _ e h
  obtain ⟨i, ⟨f⟩⟩ := h
  exact ⟨i, ⟨e.trans f⟩⟩

theorem isKGroup_subgroup {G : Type} [Group G] (X K : Subgroup G) (hKX : K ≤ X)
    (hX : CFSG.Open.IsKGroup ↥X) : CFSG.Open.IsKGroup ↥K := by
  unfold CFSG.Open.IsKGroup at hX ⊢
  exact CFSG.KCore.KGroupNonab.of_mulEquiv isoInvariant_isCatalogGroup
    (CFSG.KCore.KGroupNonab.subgroup isoInvariant_isCatalogGroup hX (K.subgroupOf X))
    (Subgroup.subgroupOfEquivOfLe hKX).symm

theorem commutator_eq_top_of_commutator_eq {G : Type} [Group G] (K : Subgroup G)
    (h : ⁅K, K⁆ = K) : commutator ↥K = ⊤ := by
  have hmap : Subgroup.map K.subtype (commutator ↥K) = K := by
    rw [commutator_def, Subgroup.map_commutator]
    have htop : Subgroup.map K.subtype (⊤ : Subgroup ↥K) = K := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [htop]
    exact h
  apply (Subgroup.map_injective K.subtype_injective)
  have htop : Subgroup.map K.subtype (⊤ : Subgroup ↥K) = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hmap, htop]

end CFSG.LocalAnalysis.GLTheoremA.H248
