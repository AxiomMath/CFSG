module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Sub
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Normalize

variable {G : Type} [Group G] [Finite G]

theorem nbr_le_normalizer {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {x : G} (hS : IsSStarMax p B x L)
    (hP : ∃ P : Subgroup G, P ≤ L ∧ IsPGroup p P ∧ ¬ IsCyclic P) :
    Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  rintro a ⟨-, haC⟩
  by_contra hna
  have hLc : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := IsSStarMax.component hS
  have hKc : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) (GLBConj a L) := by
    have h := glaPComponent_gLBConj hLc a
    rwa [I155X.glbConj_eq_self_of_mem haC] at h
  have hne : GLBConj a L ≠ L := fun h => hna (mem_normalizer_iff_gLBConj_eq.2 h)
  have hsub : GLBConj a L ≤ centModSubgroup p L := le_centModSubgroup_of_ne hp hKc hLc hne
  obtain ⟨P, hPL, hPp, hPnc⟩ := hP
  have hPaL : GLBConj a P ≤ GLBConj a L := by
    unfold GLBConj
    exact Subgroup.map_mono hPL
  have hPa : IsPGroup p (GLBConj a P) := by
    unfold GLBConj
    exact hPp.map _
  have hcyc : IsCyclic (GLBConj a P) :=
    IsSStarMax.cycMod hS _ (fun g hg => centMod_iff.2 (hsub (hPaL hg))) hPa
  apply hPnc
  have hmap : GLBConj a P = P.map (MulAut.conj a⁻¹).toMonoidHom := rfl
  rw [hmap] at hcyc
  let e := P.equivMapOfInjective (MulAut.conj a⁻¹).toMonoidHom (MulAut.conj a⁻¹).injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end Normalize

section Sub

variable {G : Type} [Group G]

theorem mem_map_subtype_iff {H : Subgroup G} (U : Subgroup ↥H) (z : ↥H) :
    (z : G) ∈ U.map H.subtype ↔ z ∈ U :=
  Subgroup.mem_map_iff_mem H.subtype_injective

theorem mem_normalizer_map_iff {H : Subgroup G} (U : Subgroup ↥H) (h : ↥H) :
    (h : G) ∈ Subgroup.normalizer ((U.map H.subtype : Subgroup G) : Set G) ↔
      h ∈ Subgroup.normalizer (U : Set ↥H) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hh y
    have h1 := hh (y : G)
    have e : (h : G) * (y : G) * (h : G)⁻¹ = ((h * y * h⁻¹ : ↥H) : G) := by simp
    rw [e, mem_map_subtype_iff, mem_map_subtype_iff] at h1
    exact h1
  · intro hh y
    by_cases hy : y ∈ H
    · have h1 := hh ⟨y, hy⟩
      have h2 := mem_map_subtype_iff U ⟨y, hy⟩
      have h3 := mem_map_subtype_iff U (h * ⟨y, hy⟩ * h⁻¹)
      have e : ((h * ⟨y, hy⟩ * h⁻¹ : ↥H) : G) = (h : G) * y * (h : G)⁻¹ := by simp
      rw [e] at h3
      exact h2.trans (h1.trans h3.symm)
    · have hyU : y ∉ U.map H.subtype := fun hm => hy (Subgroup.map_subtype_le U hm)
      have hhy : (h : G) * y * (h : G)⁻¹ ∉ U.map H.subtype := by
        intro hm
        apply hy
        have hH' := Subgroup.map_subtype_le U hm
        have e : y = (h : G)⁻¹ * ((h : G) * y * (h : G)⁻¹) * (h : G) := by group
        rw [e]
        exact H.mul_mem (H.mul_mem (H.inv_mem h.2) hH') h.2
      exact ⟨fun h1 => absurd h1 hyU, fun h1 => absurd h1 hhy⟩

theorem mem_normalizer_subgroupOf_iff {H A : Subgroup G} (hAH : A ≤ H) (h : ↥H) :
    h ∈ Subgroup.normalizer ((A.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (h : G) ∈ Subgroup.normalizer (A : Set G) := by
  have h1 := mem_normalizer_map_iff (A.subgroupOf H) h
  rw [Subgroup.map_subgroupOf_eq_of_le hAH] at h1
  exact h1.symm

theorem mem_centralizer_singleton_subtype_iff {H : Subgroup G} {x : G} (hx : x ∈ H) (h : ↥H) :
    (h : G) ∈ Subgroup.centralizer ({x} : Set G) ↔
      h ∈ Subgroup.centralizer ({(⟨x, hx⟩ : ↥H)} : Set ↥H) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hh y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subtype.ext (by simpa using hh x (Set.mem_singleton _))
  · intro hh y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have := congrArg Subtype.val (hh ⟨x, hx⟩ (Set.mem_singleton _))
    simpa using this

theorem map_normalizer_centralizer_eq {H B : Subgroup G} {x : G} (hx : x ∈ H) (hBH : B ≤ H)
    (hNH : Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤ H) :
    ((Subgroup.normalizer ((B.subgroupOf H : Subgroup ↥H) : Set ↥H)) ⊓
        Subgroup.centralizer ({(⟨x, hx⟩ : ↥H)} : Set ↥H)).map H.subtype =
      Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.1 (SetLike.mem_coe.1 hh)
    exact Subgroup.mem_inf.2 ⟨(mem_normalizer_subgroupOf_iff hBH h).1 hh1,
      (mem_centralizer_singleton_subtype_iff hx h).2 hh2⟩
  · intro hg
    obtain ⟨hgN, hgC⟩ := Subgroup.mem_inf.1 hg
    refine ⟨⟨g, hNH hg⟩, ?_, rfl⟩
    exact SetLike.mem_coe.2 (Subgroup.mem_inf.2 ⟨(mem_normalizer_subgroupOf_iff hBH _).2 hgN,
      (mem_centralizer_singleton_subtype_iff hx ⟨g, hNH hg⟩).1 hgC⟩)

theorem map_conj_subtype {H : Subgroup G} (K : Subgroup ↥H) (a : ↥H) :
    (K.map (MulAut.conj a).toMonoidHom).map H.subtype =
      (K.map H.subtype).map (MulAut.conj (a : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem closureIn_map_subtype {H : Subgroup G} (K N : Subgroup ↥H) :
    (closureIn K N).map H.subtype = closureIn (K.map H.subtype) (N.map H.subtype) := by
  apply le_antisymm
  · unfold closureIn
    rw [Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    rw [map_conj_subtype]
    exact le_iSup₂_of_le (a : G) (Subgroup.mem_map_of_mem H.subtype ha) le_rfl
  · unfold closureIn
    refine iSup₂_le fun g hg => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hg
    have e : (K.map H.subtype).map (MulAut.conj (H.subtype a : G)).toMonoidHom =
        (K.map (MulAut.conj a).toMonoidHom).map H.subtype := (map_conj_subtype K a).symm
    rw [e]
    exact Subgroup.map_mono (le_iSup₂_of_le a ha le_rfl)

theorem map_inf_normalizer_subtype {H : Subgroup G} (B U : Subgroup ↥H) :
    (B ⊓ Subgroup.normalizer (U : Set ↥H)).map H.subtype =
      B.map H.subtype ⊓ Subgroup.normalizer ((U.map H.subtype : Subgroup G) : Set G) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.1 (SetLike.mem_coe.1 hh)
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _ hh1, (mem_normalizer_map_iff U h).2 hh2⟩
  · intro hg
    obtain ⟨hgB, hgN⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨h, hhB, rfl⟩ := Subgroup.mem_map.1 hgB
    exact ⟨h, Subgroup.mem_inf.2 ⟨hhB, (mem_normalizer_map_iff U h).1 hgN⟩, rfl⟩

end Sub

section Max

variable {G : Type} [Group G] [Finite G]

private theorem bddAbove_twoLocal_pRank {q : ℕ} (hq : 1 < q) (K : Type) [Group K] [Finite K] :
    BddAbove {k | ∃ N : Subgroup K, IsTwoLocal N ∧ CFSG.Open.pRank q N = k} := by
  refine ⟨Nat.card K, ?_⟩
  rintro k ⟨N, -, rfl⟩
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hq N
  have h1 : CFSG.Open.pRank q N < q ^ CFSG.Open.pRank q N := Nat.lt_pow_self hq
  have h2 : q ^ CFSG.Open.pRank q N ≤ Nat.card K := hE ▸ Subgroup.card_le_card_group E
  omega

theorem gLAIsBmax_subgroupOf {p : ℕ} (hp : p.Prime) {B H T : Subgroup G} (hB : GLAIsBmax p B) (hBH : B ≤ H)
    (hTH : T ≤ H) (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hBT : B ≤ Subgroup.normalizer (T : Set G)) :
    GLAIsBmax p (B.subgroupOf H) := by
  have hBel : IsElemAbelian p B := hB.1
  have hBcard : Nat.card B = p ^ GLATwoLocalRank p G := hB.2.1
  have hBel' : IsElemAbelian p (B.subgroupOf H) := (Y10F.isElemAbelian_subgroupOf_iff hBH).2 hBel
  have hcard' : Nat.card (B.subgroupOf H) = p ^ GLATwoLocalRank p G := by
    rw [Y10F.card_subgroupOf hBH, hBcard]
  have hT'2 : IsPGroup 2 (T.subgroupOf H) := S265.isPGroup_subgroupOf' hT hTH
  have hT'1 : T.subgroupOf H ≠ ⊥ := by
    intro h
    apply hT1
    have := congrArg (fun U : Subgroup ↥H => U.map H.subtype) h
    rw [Subgroup.map_subgroupOf_eq_of_le hTH, Subgroup.map_bot] at this
    exact this
  have hB'N : B.subgroupOf H ≤ Subgroup.normalizer ((T.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro b hb
    exact (mem_normalizer_subgroupOf_iff hTH b).2 (hBT (Subgroup.mem_subgroupOf.1 hb))
  have hle1 : GLATwoLocalRank p G ≤ GLATwoLocalRank p ↥H := by
    have h1 : GLATwoLocalRank p G ≤ CFSG.Open.pRank p (Subgroup.normalizer ((T.subgroupOf H : Subgroup ↥H) : Set ↥H)) :=
      le_csSup (CFSG.SectionRank.pRank_bddAbove hp.one_lt _) ⟨B.subgroupOf H, hB'N, hBel', hcard'⟩
    exact h1.trans (le_csSup (bddAbove_twoLocal_pRank hp.one_lt H) ⟨_, ⟨T.subgroupOf H, hT'1, hT'2, rfl⟩, rfl⟩)
  have hrank : GLATwoLocalRank p ↥H = GLATwoLocalRank p G :=
    le_antisymm (S265.twoLocalRank_subgroup hp H) hle1
  unfold GLAIsBmax
  refine ⟨hBel', ?_, T.subgroupOf H, hT'1, hT'2, hB'N⟩
  rw [hcard', hrank]

end Max

section Split

variable {G : Type} [Group G] [Finite G]

theorem splitInnerDiagMarking16_subgroupOf {p : ℕ} {B L H : Subgroup G} (hBH : B ≤ H) (hLH : L ≤ H)
    (h : SplitInnerDiagMarking16 p B L) : SplitInnerDiagMarking16 p (B.subgroupOf H) (L.subgroupOf H) := by
  let e : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  refine Y10F.glaMarking_congr e (P' := fun lab _ _ I _ θ =>
      GLASplit16 p lab ∧ B ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ) ?_ h
  intro lab R _ I F θ hθ
  obtain ⟨hs, hN, hb⟩ := hθ
  refine ⟨hs, ?_, ?_⟩
  · refine Y10F.le_normalizer_of_map_le ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hBH, Subgroup.map_subgroupOf_eq_of_le hLH]
    exact hN
  · intro b' hb'
    have hbB : (b' : G) ∈ B := Subgroup.mem_subgroupOf.1 hb'
    obtain ⟨φ, hφ, hind⟩ := hb (b' : G) hbB
    refine ⟨φ, hφ, ?_⟩
    intro l l' hll
    have hel : ∀ z : ↥(L.subgroupOf H), ((e z : ↥L) : G) = ((z : ↥H) : G) := fun z => rfl
    have hrel : ((e l' : ↥L) : G) = (b' : G)⁻¹ * ((e l : ↥L) : G) * (b' : G) := by
      rw [hel, hel]
      have := congrArg (fun z : ↥H => (z : G)) hll
      simpa using this
    have := hind (e l) (e l') hrel
    simpa [CFSG.StandardType.centerQuotCongr_mk] using this

end Split

section Type126

variable {G : Type} [Group G] [Finite G]

theorem type126_map_iff {H : Subgroup G} {p : ℕ} (L' K' J' : Subgroup ↥H) :
    Type126 p (L'.map H.subtype) (K'.map H.subtype) (J'.map H.subtype) ↔ Type126 p L' K' J' := by
  unfold Type126
  simp only [S172.catalogIs_pSimple_map_iff]

end Type126

end CFSG.LocalAnalysis.GLTheoremA.T173

end
