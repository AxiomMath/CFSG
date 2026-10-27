module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VBarLayer
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VSylow
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem i112v_ext_sylow (TM : Tables112More) {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hq' : CFSG.Open.IsQuasisimple ↥(barX 3 X L)) (hK' : CFSG.Open.IsKGroup ↥(barX 3 X L))
    (hZ3' : Nat.card (Subgroup.center ↥(barX 3 X L)) = 3)
    (ht5 : IsHatSix ↥(barX 3 X L) ∨ IsHatSeven ↥(barX 3 X L) ∨ IsHatMTwentyTwo ↥(barX 3 X L) ∨
      IsSLThreeExc ↥(barX 3 X L) ∨ IsSUThreeExc ↥(barX 3 X L))
    {R : Subgroup G} (hRL : R ≤ L) (hR3 : IsPGroup 3 ↥R)
    (hRmax : ∀ S : Subgroup G, S ≤ L → IsPGroup 3 ↥S → R ≤ S → S = R) :
    IsThreeOnePlusTwo R ∧ barCenterX 3 X R = barCenterX 3 X L := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hR₀p : IsPGroup 3 ↥(R.subgroupOf L) := hR3.of_equiv (Subgroup.subgroupOfEquivOfLe hRL).symm
  let R₀ : Sylow 3 ↥L :=
    { toSubgroup := R.subgroupOf L
      isPGroup' := hR₀p
      is_maximal' := fun {Q} hQ hRQ => by
        have hS : Q.map L.subtype = R := by
          refine hRmax _ (Subgroup.map_subtype_le Q) (hQ.map _) fun r hr => ?_
          exact ⟨⟨r, hRL hr⟩, hRQ ((Subgroup.mem_subgroupOf).2 hr), rfl⟩
        rw [← hS, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective L.subtype_injective] }
  set f : ↥L →* ↥(barX 3 X L) := barMap 3 hL.1 with hfdef
  have hf : Function.Surjective f := barMap_surjective hL.1
  have hker : Nat.Coprime 3 (Nat.card f.ker) := by
    rw [hfdef, ker_barMap_eq hp hL.1 hL.2.1]
    exact CFSG.pPrimeCore_coprime_card
  set R' : Sylow 3 ↥(barX 3 X L) := R₀.mapSurjective hf with hR'
  have hR'c : (R' : Subgroup ↥(barX 3 X L)) = (R.subgroupOf L).map f := rfl
  obtain ⟨hc, hna, hexp⟩ := TM.T10_10S _ hq' hK' ht5 R'
  have hZp : IsPGroup 3 (Subgroup.center ↥(barX 3 X L)) :=
    IsPGroup.of_card (n := 1) (by rw [hZ3', pow_one])
  have hZR : Subgroup.center ↥(barX 3 X L) ≤ R' := hZp.le_sylow_of_normal R'
  rw [hR'c] at hc hna hexp hZR
  have hRbar : barX 3 X R = ((R.subgroupOf L).map f).map (barX 3 X L).subtype := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxR : (x : G) ∈ R := (Subgroup.mem_subgroupOf).1 hx
      refine ⟨f ⟨x, hRL hxR⟩, ⟨⟨x, hRL hxR⟩, (Subgroup.mem_subgroupOf).2 hxR, rfl⟩, ?_⟩
      rfl
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      refine ⟨Subgroup.inclusion hL.1 r, (Subgroup.mem_subgroupOf).2 ?_, rfl⟩
      exact (Subgroup.mem_subgroupOf).1 hr
  have hRcard : Nat.card ↥(barX 3 X R) = 27 := by
    rw [hRbar, Subgroup.card_map_of_injective (barX 3 X L).subtype_injective]
    exact hc
  have hRna : ∃ r s : ↥(barX 3 X R), r * s ≠ s * r := by
    obtain ⟨r, hr, s, hs, hrs⟩ := hna
    have hr' : ((r : ↥(barX 3 X L)) : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ barX 3 X R := by
      rw [hRbar]; exact ⟨r, hr, rfl⟩
    have hs' : ((s : ↥(barX 3 X L)) : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ barX 3 X R := by
      rw [hRbar]; exact ⟨s, hs, rfl⟩
    refine ⟨⟨_, hr'⟩, ⟨_, hs'⟩, fun h => hrs ?_⟩
    have h1 := congrArg Subtype.val h
    exact Subtype.ext h1
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  ·
    obtain ⟨r, hr, s, hs, hrs⟩ := hna
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    refine ⟨(r₀ : G), (Subgroup.mem_subgroupOf).1 hr₀, (s₀ : G), (Subgroup.mem_subgroupOf).1 hs₀,
      fun h => hrs ?_⟩
    have h1 : r₀ * s₀ = s₀ * r₀ := Subtype.ext h
    rw [← map_mul, ← map_mul, h1]
  · rw [← hc, i112v_card_map_eq f hker hR₀p]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv).symm
  · intro g hg
    have hg' : (⟨g, hRL hg⟩ : ↥L) ∈ R.subgroupOf L := (Subgroup.mem_subgroupOf).2 hg
    have h3 := hexp (f ⟨g, hRL hg⟩) ⟨_, hg', rfl⟩
    rw [← map_pow] at h3
    have h4 := i112v_eq_one_of_mem_ker f hker hR₀p (Subgroup.pow_mem _ hg' 3) h3
    have h5 := congrArg Subtype.val h4
    simpa using h5
  ·
    rw [barCenterX, barCenterX, map_subtype_center, map_subtype_center]
    have hle : barX 3 X L ⊓ Subgroup.centralizer (barX 3 X L : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ≤
        barX 3 X R ⊓ Subgroup.centralizer (barX 3 X R : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      intro z hz
      have hzZ : z ∈ (Subgroup.center ↥(barX 3 X L)).map (barX 3 X L).subtype := by
        rw [map_subtype_center]; exact hz
      obtain ⟨w, hw, rfl⟩ := hzZ
      have hRL' : barX 3 X R ≤ barX 3 X L := Subgroup.map_mono fun x hx =>
        (Subgroup.mem_subgroupOf).2 (hRL ((Subgroup.mem_subgroupOf).1 hx))
      refine Subgroup.mem_inf.2 ⟨?_, Subgroup.centralizer_le hRL' hz.2⟩
      rw [hRbar]
      exact ⟨w, hZR hw, rfl⟩
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [card_center_eq, card_center_eq, hZ3', i112v_card_center_eq_three hRcard hRna]

theorem input11_2Ext_of_tables (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) : UniquenessMaximal.Input11_2Ext := by
  intro G _ _ m p hS X B L _ hB hBX hr hL hnL
  obtain ⟨hp, hp2, -, hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ := i112v_bar hS hB hBX hr hL hnL
  obtain ⟨h3, hrel, -, hZE, -, hcase⟩ :=
    i112v_core T TL TT TM hQK hp hp2 hQcore hBel hrankQ hLbar hnLQ
  subst h3
  have e : barOf 3 L ≃* ↥(barX 3 X L) := quotEquivBarX hp hL.1 hL.2.1
  have hJ : barX 3 X (bClosure B L) = i112J (barX 3 X B) (barX 3 X L) :=
    i112f_barX_bClosure hBX hL.1
  have hcen : barCenterX 3 X (bClosure B L) =
      i112J (barX 3 X B) (barX 3 X L) ⊓
        Subgroup.centralizer (i112J (barX 3 X B) (barX 3 X L) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    rw [barCenterX, hJ, map_subtype_center]
    rfl
  refine ⟨rfl, (i112f_relIndex_barX hL hBX).symm.trans hrel,
    fun y hyB hyn => i112v_layer_G T TL TT TM hS hB hBX hr hL hnL hyB hyn, ?_⟩
  rcases hcase with ⟨-, -, -, hL2⟩ | ⟨hZ3', ht5, hcZ⟩
  · exact Or.inl (i112f_isLTwoOddPow_of_mulEquiv e.symm hL2)
  · right
    refine ⟨by rw [hcen]; exact hZE, ?_, fun R hRL hR3 hRmax => ?_⟩
    · rw [hcen]
      rcases hcZ with h3' | ⟨h9, -, hC, -⟩
      · exact Or.inl h3'
      · exact Or.inr ⟨h9, hC⟩
    · exact i112v_ext_sylow TM hL (i116e_isQuasisimple hQcore hLbar) (isKGroup_of_le hQK _) hZ3'
        ht5 hRL hR3 hRmax

end CFSG.HardMathSupport.Solomon.Coordinator
