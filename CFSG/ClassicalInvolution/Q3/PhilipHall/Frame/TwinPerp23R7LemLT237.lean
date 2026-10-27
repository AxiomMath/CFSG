module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLCov
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LL3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section T237

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z V : Subgroup Y}

theorem modS3O_rLayer_orb (hZ : P23ZData t u e Z) {f : Y} (hf : f ∈ p23Orb Z t e)
    (h : ModS3O ↥(rLayer (Om R) e)) : ModS3O ↥(rLayer (Om R) f) := by
  obtain ⟨m, -, rfl⟩ := hf
  rw [rLayer_conj]
  exact ModS3O.of_mulEquiv
    (Subgroup.equivMapOfInjective (rLayer (Om R) e) (MulAut.conj m).toMonoidHom
      (MulAut.conj m).injective) h

theorem p23_cover_V (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) (hVZ : V ≤ Z)
    {f : Y} (hf : f ∈ p23Orb Z t e) (hVf : V ≤ aSub R Z f) :
    f ∈ rLayerSub (Om R) V ∧
      rLayerSub (Om R) (V ⊔ Subgroup.zpowers f) ≤ rLayer (Om R) f ∧
      rLayerSub (Om R) (V ⊔ Subgroup.zpowers f) ≤ rLayerSub (Om R) V ∧
      rLayer (Om R) f ≤ oddCoreOf (rLayer (Om R) f) ⊔ rLayerSub (Om R) (V ⊔ Subgroup.zpowers f) := by
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hfZ : f ∈ Z := hZ.orb_le hf
  have hZf := hZ.le_cent hfZ
  have hf2 : f * f = 1 := hZ.sq f hfZ
  have hE₀E : rLayerSub (Om R) (V ⊔ Subgroup.zpowers f) ≤ rLayer (Om R) f := by
    unfold rLayerSub
    refine iSup₂_le fun R'' hR'' => iSup_le fun hC => F7C.le_rLayer hR'' fun x hx => ?_
    have hxC := hC hx
    rw [Subgroup.mem_centralizer_iff] at hxC
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hxC f (Subgroup.mem_sup_right (Subgroup.mem_zpowers f))).symm
  have hE₀X : rLayerSub (Om R) (V ⊔ Subgroup.zpowers f) ≤ rLayerSub (Om R) V :=
    F7L.rLayerSub_mono le_sup_left
  have hcov₀ : rLayer (Om R) f ≤ oddCoreOf (rLayer (Om R) f) ⊔
      rLayerSub (Om R) (V ⊔ Subgroup.zpowers f) := by
    have := p23_cover_f hc hZ hVZ hf hVf
    rwa [inf_eq_right.mpr hE₀E] at this
  have hcovV : rLayer (Om R) f ≤ oddCoreOf (rLayer (Om R) f) ⊔
      (rLayer (Om R) f ⊓ rLayerSub (Om R) V) := by
    refine hcov₀.trans (sup_le_sup_left ?_ _)
    exact le_inf hE₀E hE₀X
  have hfE : f ∈ rLayer (Om R) f := p23_mem_rLayer_self hc hf
  have hf2' : IsPGroup 2 (Subgroup.zpowers f) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf2
  exact ⟨F7C.mem_rLayerSub_of_cover hcovV hfE hf2', hE₀E, hE₀X, hcov₀⟩

theorem Ea_eq_secImage (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) {f : Y}
    (hf : f ∈ p23Orb Z t e) (hfX : f ∈ rLayerSub (Om R) V) :
    Ea (p23SecFamV R V)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨f, hfX⟩) =
      secImage (rLayerSub (Om R) V) (rLayerSub (Om R) (V ⊔ Subgroup.zpowers f)) := by
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hfZ : f ∈ Z := hZ.orb_le hf
  have hf2 : f * f = 1 := hZ.sq f hfZ
  set X := rLayerSub (Om R) V with hXdef
  set E₀ := rLayerSub (Om R) (V ⊔ Subgroup.zpowers f) with hE₀def
  set fb : SecQuot X := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨f, hfX⟩ with hfb
  have hE₀X : E₀ ≤ X := F7L.rLayerSub_mono le_sup_left
  apply le_antisymm
  · refine Ea_le (fun L hL hLc => ?_)
    obtain ⟨R', hR', hR'C, rfl⟩ := hL
    have hR'X : R' ≤ X := le_rLayerSub_of_mem hR' hR'C
    obtain ⟨n, hn, hnc⟩ := exists_conj_cent_sec (Ω := Om R) (A := V)
      (F7C.isPGroup_of_mem_RSet hR') hR'X hfX hf2 hLc
    have hnC : (n : Y) ∈ Subgroup.centralizer (V : Set Y) :=
      F7C.rLayerSub_le_centralizer V n.2
    have hR'' : conjSub (n : Y) R' ∈ RSet (Om R) := Q3CL.Thompson.conjSub_mem_RSet hΩ hR' (n : Y)
    have hR''V : conjSub (n : Y) R' ≤ Subgroup.centralizer (V : Set Y) := by
      have := conjSub_mono (n := (n : Y)) hR'C
      rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hnC)] at this
    have hR''C : conjSub (n : Y) R' ≤ Subgroup.centralizer ((V ⊔ Subgroup.zpowers f : Subgroup Y) :
        Set Y) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      have hxV : x ∈ Subgroup.centralizer (V : Set Y) := hR''V hx
      have hxf : x ∈ Subgroup.centralizer ({f} : Set Y) := hnc hx
      have hle : V ⊔ Subgroup.zpowers f ≤ Subgroup.centralizer ({x} : Set Y) := by
        refine sup_le (fun v hv => ?_) (Subgroup.zpowers_le.mpr ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp hxV v hv)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.mp hxf).symm
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
    have hR''E₀ : conjSub (n : Y) R' ≤ E₀ := F7C.le_rLayerSub hR'' hR''C
    rw [← secImage_conj_eq (Ω := Om R) (A := V) (B := R') hn]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono X hR''E₀)
  · rintro _ ⟨x, hx, rfl⟩
    have hxE₀ : (x : Y) ∈ E₀ := Subgroup.mem_subgroupOf.mp hx
    have hE₀H : E₀ ≤ ((Ea (p23SecFamV R V) fb).comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥X))).map
        X.subtype := by
      unfold rLayerSub
      refine iSup₂_le fun R'' hR'' => iSup_le fun hC => ?_
      have hRV : R'' ≤ Subgroup.centralizer (V : Set Y) := hC.trans (Subgroup.centralizer_le (le_sup_left : V ≤ V ⊔ Subgroup.zpowers f))
      have hRX : R'' ≤ X := le_rLayerSub_of_mem hR'' hRV
      intro r hr
      refine ⟨⟨r, hRX hr⟩, ?_, rfl⟩
      have hmem : secImage X R'' ∈ p23SecFamV R V := ⟨R'', hR'', hRV, rfl⟩
      have hcent : secImage X R'' ≤ Subgroup.centralizer ({fb} : Set (SecQuot X)) := by
        rintro _ ⟨y, hy, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hyR : (y : Y) ∈ R'' := Subgroup.mem_subgroupOf.mp hy
        have hcy : (y : Y) * f = f * (y : Y) := by
          have := hC hyR
          exact (Subgroup.mem_centralizer_iff.mp this f
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers f))).symm
        have hmul : y * (⟨f, hfX⟩ : ↥X) = (⟨f, hfX⟩ : ↥X) * y := Subtype.ext hcy
        show QuotientGroup.mk' (classicalInvolutionOddCore ↥X) y * fb =
          fb * QuotientGroup.mk' (classicalInvolutionOddCore ↥X) y
        rw [hfb, ← map_mul, ← map_mul, hmul]
      exact le_Ea hmem hcent (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr))
    obtain ⟨x', hx', hxx'⟩ := hE₀H hxE₀
    have hxx : x' = x := Subtype.ext hxx'
    subst hxx
    exact hx'

theorem p23_type237 (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) (hVZ : V ≤ Z)
    (hY1 : ModS3O ↥(rLayer (Om R) e)) {f : Y} (hf : f ∈ p23Orb Z t e) (hVf : V ≤ aSub R Z f) :
    ∃ hfX : f ∈ rLayerSub (Om R) V,
      HasS3Quot ↥(Ea (p23SecFamV R V)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨f, hfX⟩)) := by
  obtain ⟨hfX, hE₀E, hE₀X, hcov⟩ := p23_cover_V hc hZ hVZ hf hVf
  refine ⟨hfX, ?_⟩
  rw [Ea_eq_secImage hc hZ hf hfX]
  exact hasS3Quot_secImage_of_cover hE₀X hE₀E hcov (modS3O_rLayer_orb hZ hf hY1)

end T237

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
