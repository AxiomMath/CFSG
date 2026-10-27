module

public import CFSG.HardMathSupport.Solomon.Coordinator.Defs
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Struct
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FamilyRank
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Glue

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

section Simple

variable {G : Type*} [Group G]

theorem i112f_eq_bot_or_top_aux [IsSimpleGroup G] {H K : Subgroup G}
    (h : CFSG.Open.IsSubnormal H K) : K = ⊤ → H = ⊥ ∨ H = ⊤ :=
  fun hK => by subst hK; exact h.eq_bot_or_top

theorem i112f_eq_bot_or_top_of_isSubnormal [IsSimpleGroup G] {H : Subgroup G}
    (h : CFSG.Open.IsSubnormal H ⊤) : H = ⊥ ∨ H = ⊤ :=
  i112f_eq_bot_or_top_aux h rfl

end Simple

section Center

variable {Q : Type*} [Group Q]

theorem i112f_isElemAbelian_center {p : ℕ} {J : Subgroup Q}
    (h : IsElemAbelian p (J ⊓ Subgroup.centralizer (J : Set Q))) :
    IsElemAbelian p (Subgroup.center ↥J) := by
  refine isElemAbelian_of_forall (fun a _ b hb => Subgroup.mem_center_iff.1 hb a) fun z hz => ?_
  apply Subtype.ext
  have hz' : (z : Q) ∈ J ⊓ Subgroup.centralizer (J : Set Q) := by
    have : (z : Q) ∈ centreIn J := by
      rw [← map_subtype_center J]
      exact ⟨z, hz, rfl⟩
    exact this
  simpa using h.2 _ hz'

theorem i112f_card_center (J : Subgroup Q) :
    Nat.card ↥(Subgroup.center ↥J) = Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set Q)) :=
  (card_centreIn J).symm

end Center

section Bar

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {X B L : Subgroup G}

theorem i112f_comap_normalizer_barX (hL : GLAPComponent p X L) :
    (Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X))).comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) =
      (Subgroup.normalizer (L : Set G)).subgroupOf X := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  have hbar := i113g_barX_gLBConj_eq p x.2 L
  constructor
  · intro h
    have hXg : GLBConj (x : G) X = X :=
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer x.2)
    have hL' : GLAPComponent p X (GLBConj (x : G) L) := by
      have := glaPComponent_gLBConj hL (x : G)
      rwa [hXg] at this
    have h2 : barX p X (GLBConj (x : G) L) = barX p X L := by
      rw [hbar]
      exact mem_normalizer_iff_gLBConj_eq.1 h
    exact mem_normalizer_iff_gLBConj_eq.2 (glaPComponent_unique hL' hL h2)
  · intro h
    have h1 : GLBConj (x : G) L = L := mem_normalizer_iff_gLBConj_eq.1 h
    rw [h1] at hbar
    exact mem_normalizer_iff_gLBConj_eq.2 hbar.symm

theorem i112f_relIndex_barX (hL : GLAPComponent p X L) (hBX : B ≤ X) :
    (Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X))).relIndex (barX p X B) =
      (Subgroup.normalizer (L : Set G)).relIndex B := by
  rw [show barX p X B = (B.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) from rfl,
    ← Subgroup.relIndex_comap, i112f_comap_normalizer_barX hL, Subgroup.relIndex_subgroupOf hBX]

omit [Finite G] in
theorem i112f_barX_mono {K₁ K₂ : Subgroup G} (h : K₁ ≤ K₂) : barX p X K₁ ≤ barX p X K₂ :=
  Subgroup.map_mono fun _ hx => h hx

omit [Finite G] in
theorem i112f_barX_bClosure (hBX : B ≤ X) (hLX : L ≤ X) :
    barX p X (bClosure B L) = i112J (barX p X B) (barX p X L) := by
  set f := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hf
  have hsub : ∀ b ∈ B, GLBConj b L ≤ X := fun b hb => by
    rw [← mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hBX hb))]
    exact gLBConj_mono b hLX
  have hmemB : ∀ b (hb : b ∈ B), f ⟨b, hBX hb⟩ ∈ barX p X B := fun b hb =>
    ⟨⟨b, hBX hb⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩
  refine le_antisymm ?_ ?_
  ·
    set J : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := i112J (barX p X B) (barX p X L)
    have hle : bClosure B L ≤ (J.comap f).map X.subtype := by
      refine iSup₂_le fun b hb => ?_
      have h1 : barX p X (GLBConj b L) ≤ J := by
        rw [i113g_barX_gLBConj_eq p (hBX hb) L]
        exact i112_le_J (hmemB b hb)
      have h2 : (GLBConj b L).subgroupOf X ≤ J.comap f := Subgroup.map_le_iff_le_comap.1 h1
      calc GLBConj b L = ((GLBConj b L).subgroupOf X).map X.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le (hsub b hb)).symm
        _ ≤ (J.comap f).map X.subtype := Subgroup.map_mono h2
    have h3 : (bClosure B L).subgroupOf X ≤ J.comap f := by
      intro x hx
      have hx' : (x : G) ∈ (J.comap f).map X.subtype := hle ((Subgroup.mem_subgroupOf).1 hx)
      obtain ⟨y, hy, hyx⟩ := hx'
      have : y = x := Subtype.ext hyx
      rwa [← this]
    exact Subgroup.map_le_iff_le_comap.2 h3
  · refine iSup₂_le fun g hg => ?_
    obtain ⟨x, hx, rfl⟩ := hg
    have hxB : (x : G) ∈ B := (Subgroup.mem_subgroupOf).1 hx
    have h1 := i113g_barX_gLBConj_eq p x.2 L
    have h2 : GLBConj (x : G) L ≤ bClosure B L :=
      le_iSup₂_of_le (f := fun (b : G) (_ : b ∈ B) => GLBConj b L) (x : G) hxB le_rfl
    calc GLBConj (f x) (barX p X L) = barX p X (GLBConj (x : G) L) := h1.symm
      _ ≤ barX p X (bClosure B L) := i112f_barX_mono h2

end Bar

end CFSG.HardMathSupport.Solomon.Coordinator
