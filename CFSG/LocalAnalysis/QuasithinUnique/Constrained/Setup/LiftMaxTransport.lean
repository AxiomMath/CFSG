module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSylowMax

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.ABGLocalTools

section Transport

variable {G : Type*} [Group G]

theorem subgroupOf_iSup_of_le {ι : Sort*} (H : Subgroup G) (X : ι → Subgroup G)
    (hX : ∀ i, X i ≤ H) : (⨆ i, X i).subgroupOf H = ⨆ i, (X i).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (iSup_le hX), Subgroup.map_iSup]
  exact iSup_congr fun i => (Subgroup.map_subgroupOf_eq_of_le (hX i)).symm

theorem mem_normalizer_subgroupOf_iff {D H : Subgroup G} (hD : D ≤ H) (x : ↥H) :
    x ∈ Subgroup.normalizer ((D.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (x : G) ∈ Subgroup.normalizer (D : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    constructor
    · intro hg
      exact (h ⟨g, hD hg⟩).1 hg
    · intro hg
      have hgH : g ∈ H := by
        have := H.mul_mem (H.mul_mem (H.inv_mem x.2) (hD hg)) x.2
        simpa [mul_assoc] using this
      exact (h ⟨g, hgH⟩).2 hg
  · intro h g
    exact h g

theorem normalizer_subgroupOf_eq {D H : Subgroup G} (hD : D ≤ H) :
    Subgroup.normalizer ((D.subgroupOf H : Subgroup ↥H) : Set ↥H) =
      (Subgroup.normalizer (D : Set G)).subgroupOf H := by
  ext x
  exact mem_normalizer_subgroupOf_iff hD x

theorem map_conj_subgroupOf' {X H : Subgroup G} {t : G} (ht : t ∈ H) :
    (X.subgroupOf H).map (MulAut.conj (⟨t, ht⟩ : ↥H)).toMonoidHom =
      (X.map (MulAut.conj t).toMonoidHom).subgroupOf H := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨t⁻¹ * (x : G) * t, ?_⟩, ?_, ?_⟩
    · exact H.mul_mem (H.mul_mem (H.inv_mem ht) x.2) ht
    · show t⁻¹ * (x : G) * t ∈ X
      have : t⁻¹ * (x : G) * t = y := by
        have h2 : t * y * t⁻¹ = x := hyx
        rw [← h2]
        group
      rw [this]
      exact hy
    · apply Subtype.ext
      show t * (t⁻¹ * (x : G) * t) * t⁻¹ = x
      group

theorem inf_subgroupOf' (A B H : Subgroup G) :
    (A ⊓ B).subgroupOf H = A.subgroupOf H ⊓ B.subgroupOf H := by
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem localNormalizer_subgroupOf {T L H : Subgroup G} (hT : T ≤ H) :
    localNormalizer (T.subgroupOf H) (L.subgroupOf H) = (localNormalizer T L).subgroupOf H := by
  unfold localNormalizer
  rw [← inf_subgroupOf', normalizer_subgroupOf_eq (inf_le_left.trans hT), inf_subgroupOf']

theorem map_top_subtype (H : Subgroup G) : (⊤ : Subgroup ↥H).map H.subtype = H := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem transitive_direct_product_rel [Finite G] {p : ℕ} [Fact p.Prime] {H T M K : Subgroup G}
    (hT : IsSylowOf p T H) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup G, T ≤ Y → Y < H → Y ≤ M)
    {r : ℕ} (hr : 1 ≤ r) {L : Fin r → Subgroup G} (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal)
    (hK : K = ⨆ i, L i)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hind : ∀ i, L i ⊓ (⨆ j, ⨆ (_ : j ≠ i), L j) = ⊥) (hKT : K ⊔ T = H)
    (htrans : ∀ i j, ∃ t ∈ T, (L i).map (MulAut.conj t).toMonoidHom = L j)
    (hBmax : ∀ i, localNormalizer T (L i) < L i ∧ ∀ Y : Subgroup G,
      localNormalizer T (L i) ≤ Y → Y ≤ L i → Y = localNormalizer T (L i) ∨ Y = L i) :
    (∀ i, IsSylowOf p (T ⊓ L i) (L i)) ∧ T ⊓ K = ⨆ i, T ⊓ L i ∧
      M = Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ⊓ H ∧
      M = (⨆ i, localNormalizer T (L i)) ⊔ T ∧ M ⊓ K = ⨆ i, localNormalizer T (L i) ∧
      (∀ i, M ⊓ L i = localNormalizer T (L i)) ∧ Subgroup.normalizer (T : Set G) ⊓ H ≤ M ∧
      M.relIndex H = ∏ i, (localNormalizer T (L i)).relIndex (L i) := by
  classical
  have hTH : T ≤ H := hT.le
  have hMH' : M ≤ H := hMH.le
  have hLK : ∀ i, L i ≤ K := fun i => hK ▸ le_iSup L i
  have hLH : ∀ i, L i ≤ H := fun i => (hLK i).trans hKH
  have hNL : ∀ i, localNormalizer T (L i) ≤ L i := fun i => inf_le_right
  have hNH : ∀ i, localNormalizer T (L i) ≤ H := fun i => (hNL i).trans (hLH i)
  have hτ : ∀ X : Subgroup G, X ≤ H → (X.subgroupOf H).map H.subtype = X := fun X hX =>
    Subgroup.map_subgroupOf_eq_of_le hX
  have hNi : ∀ i, localNormalizer (T.subgroupOf H) ((L i).subgroupOf H) =
      (localNormalizer T (L i)).subgroupOf H := fun i => localNormalizer_subgroupOf hTH
  have hT' : IsSylowOf p (T.subgroupOf H) ⊤ := by
    refine (isSylowOf_map_subtype_iff (p := p) H (A := T.subgroupOf H) (B := ⊤)).1 ?_
    rw [hτ T hTH, map_top_subtype]
    exact hT
  have hTM' : T.subgroupOf H ≤ M.subgroupOf H := fun x hx => hTM hx
  have hMH'' : M.subgroupOf H < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    have := Subgroup.subgroupOf_eq_top.1 h
    exact absurd hMH (not_lt_of_ge this)
  have hmax' : ∀ Y : Subgroup ↥H, T.subgroupOf H ≤ Y → Y < ⊤ → Y ≤ M.subgroupOf H := by
    intro Y hTY hY
    have h1 : T ≤ Y.map H.subtype := by
      have := Subgroup.map_mono (f := H.subtype) hTY
      rwa [hτ T hTH] at this
    have h2 : Y.map H.subtype < H := by
      have := (Subgroup.map_lt_map_iff_of_injective H.subtype_injective).2 hY
      rwa [map_top_subtype] at this
    intro y hy
    exact hmax _ h1 h2 ⟨y, hy, rfl⟩
  have hK' : K.subgroupOf H = ⨆ i, (L i).subgroupOf H := by
    rw [hK]
    exact subgroupOf_iSup_of_le H L hLH
  have hcomm' : ∀ i j, i ≠ j → ∀ x ∈ (L i).subgroupOf H, ∀ y ∈ (L j).subgroupOf H,
      x * y = y * x := fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x hx y hy)
  have hind' : ∀ i, (L i).subgroupOf H ⊓ (⨆ j, ⨆ (_ : j ≠ i), (L j).subgroupOf H) = ⊥ := by
    intro i
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.map_bot]
    have h2 : (⨆ j, ⨆ (_ : j ≠ i), (L j).subgroupOf H).map H.subtype =
        ⨆ j, ⨆ (_ : j ≠ i), L j := by
      rw [Subgroup.map_iSup]
      refine iSup_congr fun j => ?_
      rw [Subgroup.map_iSup]
      exact iSup_congr fun _ => hτ _ (hLH j)
    rw [h2, hτ _ (hLH i)]
    exact hind i
  have hKT' : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKH hTH, hKT, Subgroup.subgroupOf_self]
  have htrans' : ∀ i j, ∃ t ∈ T.subgroupOf H,
      ((L i).subgroupOf H).map (MulAut.conj t).toMonoidHom = (L j).subgroupOf H := by
    intro i j
    obtain ⟨t, ht, hconj⟩ := htrans i j
    refine ⟨⟨t, hTH ht⟩, ht, ?_⟩
    rw [map_conj_subgroupOf' (hTH ht), hconj]
  have hBmax' : ∀ i, localNormalizer (T.subgroupOf H) ((L i).subgroupOf H) < (L i).subgroupOf H ∧
      ∀ Y : Subgroup ↥H, localNormalizer (T.subgroupOf H) ((L i).subgroupOf H) ≤ Y →
        Y ≤ (L i).subgroupOf H →
        Y = localNormalizer (T.subgroupOf H) ((L i).subgroupOf H) ∨ Y = (L i).subgroupOf H := by
    intro i
    rw [hNi i]
    obtain ⟨hlt, hint⟩ := hBmax i
    refine ⟨?_, ?_⟩
    · refine lt_of_le_of_ne (Subgroup.comap_mono (hNL i)) fun h => hlt.ne ?_
      have := congrArg (Subgroup.map H.subtype) h
      rwa [hτ _ (hNH i), hτ _ (hLH i)] at this
    · intro Y hNY hYL
      have h1 : localNormalizer T (L i) ≤ Y.map H.subtype := by
        have := Subgroup.map_mono (f := H.subtype) hNY
        rwa [hτ _ (hNH i)] at this
      have h2 : Y.map H.subtype ≤ L i := by
        have := Subgroup.map_mono (f := H.subtype) hYL
        rwa [hτ _ (hLH i)] at this
      rcases hint _ h1 h2 with h | h
      · left
        rw [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective Y, h]
        rfl
      · right
        rw [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective Y, h]
        rfl
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := transitive_direct_product_local_sylow_normalizers
    hT' hTM' hMH'' hmax' hr hKn hK' hcomm' hind' hKT' htrans' hBmax'
  simp only [hNi] at c4 c5 c6 c8
  have hTL : ∀ i, T.subgroupOf H ⊓ (L i).subgroupOf H = (T ⊓ L i).subgroupOf H := fun i =>
    (inf_subgroupOf' T (L i) H).symm
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_, fun i => ?_, ?_, ?_⟩
  · have := (isSylowOf_map_subtype_iff (p := p) H).2 (c1 i)
    rwa [hTL i, hτ _ (inf_le_left.trans hTH), hτ _ (hLH i)] at this
  · have := congrArg (Subgroup.map H.subtype) c2
    rw [Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.map_iSup, hτ _ hTH,
      hτ _ hKH] at this
    rw [this]
    refine iSup_congr fun i => ?_
    rw [← hτ (T ⊓ L i) (inf_le_left.trans hTH), ← hTL i]
  · have := congrArg (Subgroup.map H.subtype) c3
    rw [hτ _ hMH', ← inf_subgroupOf', normalizer_subgroupOf_eq (inf_le_left.trans hTH),
      Subgroup.subgroupOf_map_subtype] at this
    exact this
  · have := congrArg (Subgroup.map H.subtype) c4
    rw [Subgroup.map_sup, Subgroup.map_iSup, hτ _ hMH', hτ _ hTH] at this
    refine this.trans ?_
    congr 1
    exact iSup_congr fun i => hτ _ (hNH i)
  · have := congrArg (Subgroup.map H.subtype) c5
    rw [Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.map_iSup, hτ _ hMH',
      hτ _ hKH] at this
    exact this.trans (iSup_congr fun i => hτ _ (hNH i))
  · have := congrArg (Subgroup.map H.subtype) (c6 i)
    rw [Subgroup.map_inf _ _ _ H.subtype_injective, hτ _ hMH', hτ _ (hLH i),
      hτ _ (hNH i)] at this
    exact this
  · rintro g ⟨hgN, hgH⟩
    have h1 : (⟨g, hgH⟩ : ↥H) ∈ Subgroup.normalizer ((T.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
      (mem_normalizer_subgroupOf_iff hTH ⟨g, hgH⟩).2 hgN
    exact c7 h1
  · show (M.subgroupOf H).index = _
    rw [c8]
    exact Finset.prod_congr rfl fun i _ => Subgroup.relIndex_subgroupOf (hLH i)

end Transport

end CFSG.QuasithinUnique.Setup.Lift
