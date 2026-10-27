module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4Local
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourModel
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps

section Graph

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] def cnbhd (Ω : Set (Subgroup G)) (N : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ Ω ∧ (L = N ∨ Commutes L N)}

@[expose] def outerSet (Ω : Set (Subgroup G)) (N : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ cnbhd Ω N ∧ cnbhd Ω L ≠ cnbhd Ω N}

@[expose] def outerGen (Ω : Set (Subgroup G)) (N : Subgroup G) : Subgroup G :=
  ⨆ L ∈ outerSet Ω N, L

theorem cnbhd_subset (Ω : Set (Subgroup G)) (N : Subgroup G) : cnbhd Ω N ⊆ Ω := fun _ h => h.1

theorem self_mem_cnbhd {N : Subgroup G} (hN : N ∈ Ω) : N ∈ cnbhd Ω N := ⟨hN, Or.inl rfl⟩

theorem mem_cnbhd_symm {N L : Subgroup G} (hN : N ∈ Ω) (h : L ∈ cnbhd Ω N) :
    N ∈ cnbhd Ω L := by
  rcases h with ⟨-, rfl | h⟩
  · exact ⟨hN, Or.inl rfl⟩
  · exact ⟨hN, Or.inr h.symm⟩

theorem mem_outerSet_symm {N L : Subgroup G} (hN : N ∈ Ω) (h : L ∈ outerSet Ω N) :
    N ∈ outerSet Ω L :=
  ⟨mem_cnbhd_symm hN h.1, fun e => h.2 e.symm⟩

theorem outerSet_eq_of_cnbhd_eq {N L : Subgroup G} (h : cnbhd Ω L = cnbhd Ω N) :
    outerSet Ω L = outerSet Ω N := by
  simp only [outerSet, h]

theorem le_outerGen {N L : Subgroup G} (h : L ∈ outerSet Ω N) : L ≤ outerGen Ω N :=
  le_iSup₂_of_le L h le_rfl

theorem outerGen_eq_of_cnbhd_eq {N L : Subgroup G} (h : cnbhd Ω L = cnbhd Ω N) :
    outerGen Ω L = outerGen Ω N := by
  simp only [outerGen, outerSet_eq_of_cnbhd_eq h]

section Conj

variable (hΩ : ConjInvariant Ω)
include hΩ

theorem conjSub_mem_iff (g : G) {L : Subgroup G} : conjSub g L ∈ Ω ↔ L ∈ Ω := by
  refine ⟨fun h => ?_, hΩ g L⟩
  have := hΩ g⁻¹ _ h
  rwa [conjSub_inv_conjSub] at this

theorem mem_cnbhd_conj (g : G) {N L : Subgroup G} :
    conjSub g L ∈ cnbhd Ω (conjSub g N) ↔ L ∈ cnbhd Ω N := by
  constructor
  · rintro ⟨hL, h | h⟩
    · exact ⟨(conjSub_mem_iff hΩ g).mp hL, Or.inl (conjSub_injective g h)⟩
    · exact ⟨(conjSub_mem_iff hΩ g).mp hL, Or.inr ((commutes_conjSub_iff g).mp h)⟩
  · rintro ⟨hL, h | h⟩
    · exact ⟨hΩ g L hL, Or.inl (by rw [h])⟩
    · exact ⟨hΩ g L hL, Or.inr ((commutes_conjSub_iff g).mpr h)⟩

theorem cnbhd_conj_eq_iff (g : G) {N L : Subgroup G} :
    cnbhd Ω (conjSub g L) = cnbhd Ω (conjSub g N) ↔ cnbhd Ω L = cnbhd Ω N := by
  constructor
  · intro h
    ext X
    rw [← mem_cnbhd_conj hΩ g, ← mem_cnbhd_conj hΩ g (N := N), h]
  · intro h
    ext X
    have hX : X = conjSub g (conjSub g⁻¹ X) := (conjSub_conjSub_inv g X).symm
    rw [hX, mem_cnbhd_conj hΩ g, mem_cnbhd_conj hΩ g, h]

theorem mem_outerSet_conj (g : G) {N L : Subgroup G} :
    conjSub g L ∈ outerSet Ω (conjSub g N) ↔ L ∈ outerSet Ω N := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_cnbhd_conj hΩ g).mp h1, fun e => h2 ((cnbhd_conj_eq_iff hΩ g).mpr e)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_cnbhd_conj hΩ g).mpr h1, fun e => h2 ((cnbhd_conj_eq_iff hΩ g).mp e)⟩

theorem outerGen_conj (g : G) (N : Subgroup G) :
    outerGen Ω (conjSub g N) = conjSub g (outerGen Ω N) := by
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    have hL' : conjSub g⁻¹ L ∈ outerSet Ω N := by
      rw [← mem_outerSet_conj hΩ g, conjSub_conjSub_inv]
      exact hL
    have := conjSub_mono (n := g) (le_outerGen hL')
    rwa [conjSub_conjSub_inv] at this
  · have h : outerGen Ω N ≤ conjSub g⁻¹ (outerGen Ω (conjSub g N)) := by
      refine iSup₂_le fun L hL => ?_
      have hL' : conjSub g L ∈ outerSet Ω (conjSub g N) := (mem_outerSet_conj hΩ g).mpr hL
      have := conjSub_mono (n := g⁻¹) (le_outerGen hL')
      rwa [conjSub_inv_conjSub] at this
    have := conjSub_mono (n := g) h
    rwa [conjSub_conjSub_inv] at this

end Conj



theorem mem_closedNbhd_iff {v u : ↥Ω} :
    u ∈ closedNbhd (commAdj Ω) v ↔ u.1 = v.1 ∨ Commutes u.1 v.1 := by
  show (u = v ∨ commAdj Ω u v) ↔ _
  rw [Subtype.ext_iff]
  rfl

theorem cnbhd_eq_of_closedNbhd_eq {v : ↥Ω} {S : Set (Subgroup G)} (hS : S ⊆ Ω)
    (h : closedNbhd (commAdj Ω) v = {u : ↥Ω | u.1 ∈ S}) : cnbhd Ω v.1 = S := by
  ext L
  constructor
  · rintro ⟨hL, hc⟩
    have : (⟨L, hL⟩ : ↥Ω) ∈ closedNbhd (commAdj Ω) v := mem_closedNbhd_iff.mpr hc
    rw [h] at this
    exact this
  · intro hL
    have : (⟨L, hS hL⟩ : ↥Ω) ∈ closedNbhd (commAdj Ω) v := by
      rw [h]
      exact hL
    exact ⟨hS hL, mem_closedNbhd_iff.mp this⟩

theorem cnbhd_eq_iff_closedNbhd_eq {u v : ↥Ω} :
    cnbhd Ω u.1 = cnbhd Ω v.1 ↔ closedNbhd (commAdj Ω) u = closedNbhd (commAdj Ω) v := by
  constructor
  · intro h
    ext x
    rw [mem_closedNbhd_iff, mem_closedNbhd_iff]
    have := Set.ext_iff.mp h x.1
    constructor
    · intro hx
      exact (this.mp ⟨x.2, hx⟩).2
    · intro hx
      exact (this.mpr ⟨x.2, hx⟩).2
  · intro h
    ext X
    constructor
    · rintro ⟨hX, hc⟩
      have : (⟨X, hX⟩ : ↥Ω) ∈ closedNbhd (commAdj Ω) u := mem_closedNbhd_iff.mpr hc
      rw [h] at this
      exact ⟨hX, mem_closedNbhd_iff.mp this⟩
    · rintro ⟨hX, hc⟩
      have : (⟨X, hX⟩ : ↥Ω) ∈ closedNbhd (commAdj Ω) v := mem_closedNbhd_iff.mpr hc
      rw [← h] at this
      exact ⟨hX, mem_closedNbhd_iff.mp this⟩


end Graph

section Data

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem exists_D4At {a : ℕ} {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hloc : LocalShapeT p f a .POmegaPlus 4 (conjClass K) z) {N : Subgroup G}
    (hN : N ∈ conjClass K) :
    ∃ w : G, IsClassicalMember p f N w ∧ LocalOddCentral (conjClass K) {w} ∧
      ∃ (D : LieSystemData p f (locQuot (conjClass K) w) (locFamily (conjClass K) w))
        (i₁ : Fin D.card), D.card = a + 1 ∧ D.tag i₁ = .POmegaPlus ∧ D.rank i₁ = 4 ∧
          ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2 := by
  obtain ⟨g, hg⟩ := single_class K N hN
  have hw : IsClassicalMember p f N (g * z * g⁻¹) := by
    rw [hg]
    exact S.cls.conj g
  have hP1 : LocalOddCentral (conjClass K) {g * z * g⁻¹} :=
    localOddCentral_conj S.inClass.conjInvariant g z S.p1
  obtain ⟨D, hcard, i₁, ht, hr, hrest⟩ :=
    LocalShapeT.conj (p := p) (f := f) S.inClass.conjInvariant g hloc
  exact ⟨_, hw, hP1, D, i₁, hcard, ht, hr, hrest⟩

theorem single_class_of_mem {K N : Subgroup G} (hN : N ∈ conjClass K) :
    ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g N := by
  intro L hL
  obtain ⟨g₁, hg₁⟩ := single_class K L hL
  obtain ⟨g, hg⟩ := single_class K N hN
  exact ⟨g₁ * g⁻¹, by rw [conjSub_mul, hg, conjSub_inv_conjSub, hg₁]⟩

variable {Ω : Set (Subgroup G)}

theorem cnbhd_eq_centralizingMembers [Finite G] (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {N : Subgroup G} {w : G} (hw : IsClassicalMember p f N w) (hN : N ∈ Ω)
    (hP1 : LocalOddCentral Ω {w}) (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) :
    cnbhd Ω N = centralizingMembers Ω {w} := by
  ext L
  constructor
  · rintro ⟨hLΩ, h⟩
    exact (mem_centralizingMembers_iff hΩ hex hw hN hP1 D hLΩ).mpr h
  · intro hL
    exact ⟨hL.1, (mem_centralizingMembers_iff hΩ hex hw hN hP1 D hL.1).mp hL⟩

theorem outerSet_eq_compMembers [Finite G] (hp2 : p ≠ 2) (hf : 0 < f) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {N : Subgroup G} {w : G}
    (hw : IsClassicalMember p f N w) (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g N)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) {i₁ : Fin D.card}
    (ht : D.tag i₁ = .POmegaPlus) (hr : D.rank i₁ = 4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) :
    outerSet Ω N = compMembers Ω w D i₁ := by
  have hq4 : 4 ≤ p ^ f := by omega
  have hcn := cnbhd_eq_centralizingMembers hΩ hex hw hN hP1 D
  ext L
  constructor
  · rintro ⟨hLc, hne⟩
    have hLw : L ∈ centralizingMembers Ω {w} := hcn ▸ hLc
    obtain ⟨j, hj, -⟩ := exists_unique_comp hΩ hex D hLw
    by_cases hji : j = i₁
    · subst hji
      exact hj
    · exfalso
      obtain ⟨T, hTw, hTimg⟩ := exists_member_of_a1 (Ω := Ω) D (hrest j hji)
      have hTmem : T ∈ compMembers Ω w D j := ⟨hTw, hTimg.le⟩
      have hLT : L = T := eq_of_mem_compMembers_a1 hΩ hex hP1 (hrest j hji) hj hTmem
      subst hLT
      have hcl := closedNbhd_whole hΩ hex hp2 hf hw hP1 D hsingle hLw.1 hTw hTimg
      have h1 := cnbhd_eq_of_closedNbhd_eq (v := (⟨L, hLw.1⟩ : ↥Ω))
        (fun _ h => h.1) hcl
      exact hne (h1.trans hcn.symm)
  · intro hL
    have hLw := hL.1
    refine ⟨hcn ▸ hLw, fun heq => ?_⟩
    exact closedNbhd_ne_of_comp hΩ hex hp2 hq4 hw hN hP1 D ht hr hrest hL hLw.1
      ((cnbhd_eq_iff_closedNbhd_eq (u := ⟨L, hLw.1⟩) (v := ⟨N, hN⟩)).mp heq)


theorem exists_lift_outerGen [Finite G] (hp2 : p ≠ 2) (hf : 0 < f) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {N : Subgroup G} {w : G}
    (hw : IsClassicalMember p f N w) (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g N)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) {i₁ : Fin D.card}
    (ht : D.tag i₁ = .POmegaPlus) (hr : D.rank i₁ = 4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2)
    (k : (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K) :
    ∃ y : ↥(locLayer Ω w), (y : G) ∈ outerGen Ω N ∧ locMk Ω w y = D.hom i₁ k := by
  have hout := outerSet_eq_compMembers hp2 hf hq hΩ hex hw hN hP1 hsingle D ht hr hrest
  have hsc := fundamentalSingleClass_of_ne D i₁ (by rw [ht]; decide) (by rw [ht]; decide)
  let S : Subgroup (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K :=
    Subgroup.comap (D.hom i₁) (Subgroup.map (locMk Ω w)
      ((outerGen Ω N).subgroupOf (locLayer Ω w)))
  have hgen := top_le_iSup_fund_of_eq (p := p) (e := D.exp i₁) ht hr (D.admissible i₁)
  have hS : ∀ R ∈ compFund D i₁, R ≤ S := by
    intro R hR k hk
    obtain ⟨N', hN'⟩ := exists_corr_right hΩ D hsc hR
    have hN'out : N' ∈ outerSet Ω N := by
      rw [hout]
      exact ⟨hN'.1, hN'.2.2 ▸ Subgroup.map_le_range _ _⟩
    have hmem : D.hom i₁ k ∈ locImg Ω w N' := by
      rw [hN'.2.2]
      exact ⟨k, hk, rfl⟩
    obtain ⟨y, hy, hyk⟩ := hmem
    exact ⟨y, Subgroup.mem_subgroupOf.mpr (le_outerGen hN'out (Subgroup.mem_subgroupOf.mp hy)),
      hyk⟩
  have hk : k ∈ S := (hgen.trans (iSup₂_le hS)) trivial
  obtain ⟨y, hy, hyk⟩ := hk
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hyk⟩

theorem exists_conj_of_mem_outerSet [Finite G] (hp2 : p ≠ 2) (hf : 0 < f) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {N : Subgroup G} {w : G}
    (hw : IsClassicalMember p f N w) (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g N)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) {i₁ : Fin D.card}
    (ht : D.tag i₁ = .POmegaPlus) (hr : D.rank i₁ = 4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) {E E' : Subgroup G}
    (hE : E ∈ outerSet Ω N) (hE' : E' ∈ outerSet Ω N) :
    ∃ y ∈ outerGen Ω N, conjSub y E = E' := by
  have hq4 : 4 ≤ p ^ f := by omega
  have hout := outerSet_eq_compMembers hp2 hf hq hΩ hex hw hN hP1 hsingle D ht hr hrest
  rw [hout] at hE hE'
  have hsc := fundamentalSingleClass_of_ne D i₁ (by rw [ht]; decide) (by rw [ht]; decide)
  obtain ⟨R, hR⟩ := exists_corr_left hΩ hex D hE
  obtain ⟨R', hR'⟩ := exists_corr_left hΩ hex D hE'
  obtain ⟨g, hg⟩ := hsc R hR.2.1 R' hR'.2.1
  obtain ⟨y, hyY, hy⟩ := exists_lift_outerGen hp2 hf hq hΩ hex hw hN hP1 hsingle D ht hr hrest g
  refine ⟨y, hyY, ?_⟩
  have hyx : (y : G) ∈ Subgroup.centralizer ({w} : Set G) :=
    centralizingLayer_le_centralizer Ω {w} y.2
  have hconj : conjSub (y : G) E ∈ centralizingMembers Ω {w} := by
    refine ⟨hΩ.conjInvariant _ E hE.1.1, fun a ha => ?_⟩
    rw [mem_conjSub_iff] at ha
    have hx' := hE.1.2 ha
    have : a = (y : G) * ((y : G)⁻¹ * a * (y : G)) * (y : G)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)
  have himg : locImg Ω w (conjSub (y : G) E) = locImg Ω w E' := by
    rw [locImg_conjSub_layer, hR.2.2, hy, hR'.2.2, hg]
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp
  exact locImg_injOn hΩ hP1 hconj hE'.1 himg

theorem outerSet_nonempty [Finite G] (hp2 : p ≠ 2) (hf : 0 < f) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {N : Subgroup G} {w : G}
    (hw : IsClassicalMember p f N w) (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g N)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) {i₁ : Fin D.card}
    (ht : D.tag i₁ = .POmegaPlus) (hr : D.rank i₁ = 4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) :
    (outerSet Ω N).Nonempty := by
  rw [outerSet_eq_compMembers hp2 hf hq hΩ hex hw hN hP1 hsingle D ht hr hrest]
  obtain ⟨R, -, hmem⟩ := D.meets i₁
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp hmem
  exact ⟨L, hL, hLR ▸ Subgroup.map_le_range _ _⟩


theorem routeD_f_pos {K : Subgroup G} {z : G} (S : RouteDSetup p f K z) : 0 < f := by
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · have := S.five
    rw [h0] at this
    simp at this
  · exact h0

end Data

section Shape

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {a : ℕ} {K : Subgroup G}
  {z : G}

theorem outerSet_nonempty_of_shape (S : RouteDSetup p f K z)
    (hloc : LocalShapeT p f a .POmegaPlus 4 (conjClass K) z) {N : Subgroup G}
    (hN : N ∈ conjClass K) : (outerSet (conjClass K) N).Nonempty := by
  obtain ⟨w, hw, hP1, D, i₁, -, ht, hr, hrest⟩ := exists_D4At S hloc hN
  exact outerSet_nonempty S.odd (routeD_f_pos S) S.five S.inClass S.exact hw hN hP1
    (single_class_of_mem hN) D ht hr hrest

theorem exists_conj_of_shape (S : RouteDSetup p f K z)
    (hloc : LocalShapeT p f a .POmegaPlus 4 (conjClass K) z) {N E E' : Subgroup G}
    (hN : N ∈ conjClass K) (hE : E ∈ outerSet (conjClass K) N)
    (hE' : E' ∈ outerSet (conjClass K) N) :
    ∃ y ∈ outerGen (conjClass K) N, conjSub y E = E' := by
  obtain ⟨w, hw, hP1, D, i₁, -, ht, hr, hrest⟩ := exists_D4At S hloc hN
  exact exists_conj_of_mem_outerSet S.odd (routeD_f_pos S) S.five S.inClass S.exact hw hN hP1
    (single_class_of_mem hN) D ht hr hrest hE hE'

theorem ncard_twins_of_shape (S : RouteDSetup p f K z)
    (hloc : LocalShapeT p f a .POmegaPlus 4 (conjClass K) z) {N : Subgroup G}
    (hN : N ∈ conjClass K) :
    {T : Subgroup G | T ∈ conjClass K ∧ cnbhd (conjClass K) T = cnbhd (conjClass K) N}.ncard =
      a := by
  obtain ⟨w, hw, hP1, D, i₁, hcard, ht, hr, hrest⟩ := exists_D4At S hloc hN
  obtain ⟨⟨s, hs, hsm⟩, -⟩ := exists_localData S.odd S.five (routeD_f_pos S) S.inClass S.exact hw
    hN hP1 (single_class_of_mem hN) D hcard ht hr hrest
  have hset : {T : Subgroup G | T ∈ conjClass K ∧
      cnbhd (conjClass K) T = cnbhd (conjClass K) N} = Subtype.val '' (s : Set ↥(conjClass K)) := by
    ext T
    constructor
    · rintro ⟨hT, h⟩
      refine ⟨⟨T, hT⟩, ?_, rfl⟩
      rw [Finset.mem_coe, hsm]
      exact (cnbhd_eq_iff_closedNbhd_eq (u := ⟨T, hT⟩) (v := ⟨N, hN⟩)).mp h
    · rintro ⟨u, hu, rfl⟩
      rw [Finset.mem_coe, hsm] at hu
      exact ⟨u.2, (cnbhd_eq_iff_closedNbhd_eq (u := u) (v := ⟨N, hN⟩)).mpr hu⟩
  rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset, hs]


end Shape

end CFSG.ClassicalInvolution.RouteD.Exotic
