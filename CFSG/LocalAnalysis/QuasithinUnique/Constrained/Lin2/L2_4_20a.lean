module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Derived
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Easy

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Parts

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem lin2_Z_eq_centerOf (hc : centerOf L ≠ ⊥) {Z : Subgroup G}
    (hZ : Z = lin2Z L (thompsonJ S)) : Z = centerOf L :=
  ((lin2Z_cases hZ).resolve_left fun h => hc h.1).2

theorem lin2_20_reg (h8 : Lemma2_4_8) (h16 : Lemma2_4_16) (hcfg : Lin2Cfg G T M H S L n D)
    {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) (hc : centerOf L ≠ ⊥) {B : Subgroup G}
    (hB : Lin2BProps T S (thompsonJ S) D B) {x : G}
    (hxN : x ∈ T ⊓ Subgroup.normalizer (B : Set G)) (hxS : x ∉ S) :
    ActsRegularlyOn B (lin2Delta (thompsonJ S) Z x) := by
  obtain ⟨⟨-, -, hTnR⟩, -, -, h4, -, h6, -⟩ := h8 G T M H S L D n hcfg
  have hxT : x ∈ T := hxN.1
  have hZe : Z = centerOf L := lin2_Z_eq_centerOf hc hZ
  obtain ⟨-, hZ2, -⟩ := h16 G T M H S L D n hcfg Z hZ
  obtain ⟨hZR, hZZ'⟩ := ((hZ2 x hxT hxS).resolve_left fun h => hc h.1).2
  have hDZ : ∀ d ∈ D, ∀ z ∈ Z, d⁻¹ * z * d = z := by
    intro d hd z hz
    have := Subgroup.mem_centralizer_iff.1 (hZe ▸ hz : z ∈ centerOf L).2 d (hcfg.D_le_L hd)
    rw [mul_assoc, ← this, inv_mul_cancel_left]
  have hBeq : B = D ⊔ conjR D x := ((h6 B hB).1 hc x hxN hxS).1
  have hBab := hB.2.2.1
  have hDB : D ≤ B := hB.1
  have hD'B : conjR D x ≤ B := by rw [hBeq]; exact le_sup_right
  have hcommD : ∀ d ∈ D, ∀ d' ∈ conjR D x, d * d' = d' * d := fun d hd d' hd' =>
    hBab d (hDB hd) d' (hD'B hd')
  have hZR_le : Z ≤ centerOf (thompsonJ S) := lin2Z_le_centerOf h16 hcfg hZ
  have hZ'R : conjR Z x ≤ centerOf (thompsonJ S) :=
    calc conjR Z x ≤ conjR (centerOf (thompsonJ S)) x := conjR_mono hZR_le x
      _ = centerOf (thompsonJ S) := centerOf_normalized (hTnR hxT)
  have hcommZ : ∀ z ∈ Z, ∀ z' ∈ conjR Z x, z * z' = z' * z := fun z hz z' hz' =>
    Subgroup.mem_centralizer_iff.1 (hZ'R hz').2 z (hZR_le hz).1
  have hx'T : x⁻¹ ∈ T := T.inv_mem hxT
  have hx'S : x⁻¹ ∉ S := fun h => hxS (by simpa using S.inv_mem h)
  have hreg' : ActsRegularlyOn (conjR D x) (nonIdentity Z) := by
    have := ((h4 x hxT hxS).2.resolve_left hc).2.2
    rwa [← hZe] at this
  have hreg : ActsRegularlyOn D (nonIdentity (conjR Z x)) := by
    have h1 := ((h4 x⁻¹ hx'T hx'S).2.resolve_left hc).2.2
    rw [← hZe] at h1
    have := actsRegularlyOn_conjR h1 x
    rwa [conjR_conjR, inv_mul_cancel, conjR_one] at this
  have hmain := actsRegularlyOn_sup_of_prod hcommD hZZ' hcommZ hDZ (conjR_centralizes hDZ x) hreg
    hreg'
  have hset : lin2Delta (thompsonJ S) Z x =
      {u | u ∈ Z ⊔ conjR Z x ∧ u ∉ Z ∧ u ∉ conjR Z x} := by
    unfold lin2Delta
    rw [hZR]
  rw [hset, hBeq]
  exact hmain

theorem lin2_conjR_Z_eq (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D) {Z : Subgroup G}
    (hZS : S ≤ Subgroup.normalizer (Z : Set G)) {x x' : G} (hx : x ∈ T) (hx' : x' ∈ T)
    (hxS : x ∉ S) (hx'S : x' ∉ S) : conjR Z x' = conjR Z x := by
  obtain ⟨⟨hTS, hTnS, -⟩, -⟩ := h8 G T M H S L D n hcfg
  have hs : x⁻¹ * x' ∈ S := inv_mul_mem_of_relIndex_two hTS hx hx' hxS hx'S
  have h1 : x * (x⁻¹ * x') * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hTnS hx) _).1 hs
  have hn : x⁻¹ * x' ∈ Subgroup.normalizer ((conjR Z x : Subgroup G) : Set G) := by
    rw [conjR_normalizer]; exact mem_conjR.2 (hZS h1)
  calc conjR Z x' = conjR Z (x * (x⁻¹ * x')) := by rw [mul_inv_cancel_left]
    _ = conjR (conjR Z x) (x⁻¹ * x') := (conjR_conjR _ _ _).symm
    _ = conjR Z x := conjR_eq_of_mem_normalizer hn

theorem lin2_isSylowTwoOf_normalizer_Z (h16 : Lemma2_4_16) (hcfg : Lin2Cfg G T M H S L n D)
    {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) (hc : centerOf L ≠ ⊥) :
    IsSylowTwoOf S (Subgroup.normalizer (Z : Set G)) := by
  have hZe : Z = centerOf L := lin2_Z_eq_centerOf hc hZ
  refine hcfg.cs.isSylowTwoOf_normalizer (lin2Z_ne_bot h16 hcfg hZ)
    ((lin2Z_le_centerOf h16 hcfg hZ).trans (inf_le_left.trans (thompsonJ_le_self S))) ?_
  rw [hZe]
  exact hcfg.H_le_normalizer_centerOf

theorem lin2_20_not_two_central (h8 : Lemma2_4_8) (h16 : Lemma2_4_16) (h18 : Lemma2_4_18)
    (hcfg : Lin2Cfg G T M H S L n D) {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S))
    (hc : centerOf L ≠ ⊥) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) (g : G) :
    ¬ conjR T g ≤ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨⟨hTS, -, -⟩, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨hTI, -, -⟩ := h18 G T M H S L D n hcfg Z hZ
  have hSyl := lin2_isSylowTwoOf_normalizer_Z h16 hcfg hZ hc
  intro h
  have hN := h.trans (centralizer_le_normalizer_of_TI hTI hz hz1)
  have h2 : IsPGroup 2 (conjR T g) := (isPGroup_conjR_iff 2).2 hcfg.sylowT.isPGroup
  have h3 := card_le_twoPart hN h2
  rw [← hSyl.card_eq, card_conjR, card_eq_mul_of_relIndex hcfg.S_le_T, hTS] at h3
  have := Nat.card_pos (α := S)
  omega

theorem lin2_20_five (h16 : Lemma2_4_16) (h18 : Lemma2_4_18) (hcfg : Lin2Cfg G T M H S L n D)
    {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) (hc : centerOf L ≠ ⊥) :
    ∀ z ∈ Z, z ≠ 1 → ∀ P : Subgroup G, IsSylowTwoOf P (Subgroup.centralizer ({z} : Set G)) →
      ∃ g : G, P ≤ conjR S g := by
  obtain ⟨hTI, -, -⟩ := h18 G T M H S L D n hcfg Z hZ
  intro z hz hz1 P hP
  obtain ⟨g, -, hg⟩ := exists_le_conjR_of_isSylowTwoOf
    (lin2_isSylowTwoOf_normalizer_Z h16 hcfg hZ hc)
    (hP.le.trans (centralizer_le_normalizer_of_TI hTI hz hz1)) hP.isPGroup
  exact ⟨g, hg⟩

theorem lin2_20_two (h8 : Lemma2_4_8) (h16 : Lemma2_4_16) (h18 : Lemma2_4_18)
    (hcfg : Lin2Cfg G T M H S L n D) {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S))
    (hc : centerOf L ≠ ⊥) {x : G} (hxT : x ∈ T) (hxS : x ∉ S) :
    ∀ u ∈ lin2Delta (thompsonJ S) Z x,
      (∃ m ∈ M, m⁻¹ * u * m ∈ centerOf T) ∧ Subgroup.centralizer ({u} : Set G) ≤ M ∧
        ∀ g : G, g⁻¹ * u * g ∉ Z := by
  obtain ⟨⟨-, -, hTnR⟩, -, ⟨-, -, h3⟩, -, ⟨B, hB⟩, -, h7, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨hZ1, -, -⟩ := h16 G T M H S L D n hcfg Z hZ
  have hset := hcfg.cs.setting
  have hST : S ≤ T := hcfg.S_le_T
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hRT : thompsonJ S ≤ T := hRS.trans hST
  have hZR : Z ≤ centerOf (thompsonJ S) := lin2Z_le_centerOf h16 hcfg hZ
  have hZne : Z ≠ ⊥ := lin2Z_ne_bot h16 hcfg hZ
  have hnc : ∀ z ∈ Z, z ≠ 1 → ¬ T ≤ Subgroup.centralizer ({z} : Set G) := by
    intro z hz hz1 h
    refine lin2_20_not_two_central h8 h16 h18 hcfg hZ hc hz hz1 1 ?_
    rwa [conjR_one]
  obtain ⟨u₀, hu₀Δ, hu₀T⟩ := exists_mem_lin2Delta_center hcfg.sylowT.isPGroup hRT hZR hZne
    (fun g hg => hTnR hg) hxT hnc
  obtain ⟨hDB, hHall, hBab, hTprod, hSRD, hBR, hTRB, hRB, hRNT, hRNT', hDD⟩ := hB
  have hB' : Lin2BProps T S (thompsonJ S) D B :=
    ⟨hDB, hHall, hBab, hTprod, hSRD, hBR, hTRB, hRB, hRNT, hRNT', hDD⟩
  obtain ⟨x', hx'N, hx'S⟩ : ∃ x' ∈ T ⊓ Subgroup.normalizer (B : Set G), x' ∉ S := by
    by_contra hcon
    push Not at hcon
    apply hcfg.S_ne_T
    refine le_antisymm hST ?_
    rw [← hRNT]
    exact sup_le hRS fun y hy => hcon y hy
  have hreg := lin2_20_reg h8 h16 hcfg hZ hc hB' hx'N hx'S
  have hΔ : lin2Delta (thompsonJ S) Z x' = lin2Delta (thompsonJ S) Z x := by
    unfold lin2Delta
    rw [lin2_conjR_Z_eq h8 hcfg hZ1.2.2 hx'N.1 hxT hx'S hxS]
  rw [hΔ] at hreg
  have hBM : B ≤ M := hcfg.B_le_M hB'
  have hu₀2 : u₀ ∈ T ⊓ Subgroup.centralizer (T : Set G) := hu₀T
  have hu₀C : Subgroup.centralizer ({u₀} : Set G) ≤ M := by
    have hu₀1 : u₀ ≠ 1 := by
      rintro rfl
      exact hu₀Δ.2.1 (one_mem Z)
    have h2 : u₀ ^ 2 = 1 := by
      have hu₀U : u₀ ∈ blockU L := by
        have : u₀ ∈ blockU L ⊓ conjR (blockU L) x := by
          rw [(h3 x hxT hxS).2.1]; exact hu₀Δ.1
        exact this.1
      exact (h7 x hxT hxS).1.2 u₀ hu₀U
    exact hset.le_of_isTwoLocal_of_isSylowTwoOf_M hset.isSylowTwoOf_M
      (isTwoLocal_centralizer_of_sq_eq_one h2 hu₀1) (fun t ht => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 hu₀2.2 t ht)
  intro u hu
  obtain ⟨b, hb, hbu⟩ := hreg.2.1 u hu u₀ hu₀Δ
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hu.2.1 (one_mem Z)
  refine ⟨⟨b, hBM hb, by rw [hbu]; exact hu₀2⟩, ?_, ?_⟩
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hg' : b⁻¹ * g * b ∈ Subgroup.centralizer ({u₀} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hbu]
      calc b⁻¹ * g * b * (b⁻¹ * u * b) = b⁻¹ * (g * u) * b := by group
        _ = b⁻¹ * (u * g) * b := by rw [hg]
        _ = b⁻¹ * u * b * (b⁻¹ * g * b) := by group
    have h1 := hu₀C hg'
    have e : g = b * (b⁻¹ * g * b) * b⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem (hBM hb) h1) (M.inv_mem (hBM hb))
  · intro g hg
    refine lin2_20_not_two_central h8 h16 h18 hcfg hZ hc hg (fun h1 => hu1 ?_) (b⁻¹ * g) ?_
    · have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      rw [this, h1]; group
    · intro t ht
      rw [mem_conjR] at ht
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcent := Subgroup.mem_centralizer_iff.1 hu₀2.2 _ ht
      have hu_eq : u = b * u₀ * b⁻¹ := by rw [← hbu]; group
      have hz : g⁻¹ * u * g = (b⁻¹ * g)⁻¹ * u₀ * (b⁻¹ * g) := by rw [hu_eq]; group
      rw [hz]
      calc t * ((b⁻¹ * g)⁻¹ * u₀ * (b⁻¹ * g))
          = (b⁻¹ * g)⁻¹ * (((b⁻¹ * g) * t * (b⁻¹ * g)⁻¹) * u₀) * (b⁻¹ * g) := by group
        _ = (b⁻¹ * g)⁻¹ * (u₀ * ((b⁻¹ * g) * t * (b⁻¹ * g)⁻¹)) * (b⁻¹ * g) := by rw [hcent]
        _ = ((b⁻¹ * g)⁻¹ * u₀ * (b⁻¹ * g)) * t := by group

end Parts

end CFSG.QuasithinUnique.Lin2
