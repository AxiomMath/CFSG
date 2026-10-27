module

public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.BrauerFiberSectionInduction
public import CFSG.CharacterTheory.Semidihedral.Local.FourSubgroupCentralizers
public import CFSG.CharacterTheory.BlockBasics.Defects

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

namespace FreeSix

variable {G : Type*} [Group G] [Fintype G] {V E : Subgroup G} (hV : IsKleinFour V)
  (hED : E ≤ dV V) (hVE : V ⊓ E = ⊥) (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e)
  (hEodd : Odd (Nat.card E))

include hV hED hDVE hEodd in
theorem eInM_normal : (eInM V E).Normal := by
  constructor
  intro x hx g
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact conj_mem_of_mem hV hED hDVE hEodd g.2 hx

include hV hED hDVE hEodd in
theorem eInK_normal {t : G} (htV : t ∈ V) : (eInK V E t).Normal := by
  constructor
  intro x hx g
  change (((g * x * g⁻¹ : kInC V t) : cT t) : G) ∈ E
  exact conj_mem_of_mem hV hED hDVE hEodd ((mem_kInC_iff (le_cT hV htV) g).mp g.2) hx

end FreeSix

open FreeSix

theorem free_six_character_normalizer_orbit_defect_four_block {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (V : Subgroup G) (hV : IsKleinFour V) (t : G) (htV : t ∈ V) (ht1 : t ≠ 1)
    (E : Subgroup G) (hED : E ≤ dV V) (hVE : V ⊓ E = ⊥)
    (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e) (hEodd : Odd (Nat.card E))
    (hAut : Function.Surjective V.normalizerMonoidHom)
    (hfour : ∀ U : Subgroup G, IsKleinFour U → t ∈ U → U ≤ cT t →
      ∃ c ∈ cT t, U.map (MulAut.conj c).toMonoidHom = V)
    (ω : dV V →* ℂˣ) (hωV : ∀ x : dV V, (x : G) ∈ V → ω x = 1)
    (hωstab : ∀ m ∈ mV V, (∀ x y : dV V, (y : G) = m⁻¹ * x * m → ω y = ω x) → m ∈ dV V)
    (basisM : FiniteIrreducibleCharacterBasis (mV V))
    (basisMD : FiniteIrreducibleCharacterBasis (dInM V))
    (basisEM : FiniteIrreducibleCharacterBasis (eInM V E))
    (basisC : FiniteIrreducibleCharacterBasis (cT t))
    (basisK : FiniteIrreducibleCharacterBasis (kInC V t))
    (basisKD : FiniteIrreducibleCharacterBasis (dInK V t))
    (basisCD : FiniteIrreducibleCharacterBasis (dInC V t)) :
    let μ : E →* ℂˣ := ω.comp (Subgroup.inclusion hED)
    let Ω := linearOrbit E μ (mV V : Set G)
    let R := localizedComplexIntegerRing ideal
    let BrMD := brauerNormalizerCharacterResidueHom ideal 2 (vInM V) (isPGroup_vInM hV) (dInM V)
      le_rfl (Subgroup.centralizer_le_normalizer _) basisMD
    let BrKD := brauerNormalizerCharacterResidueHom ideal 2 (vInK V t) (isPGroup_vInK hV)
      (dInK V t) le_rfl (Subgroup.centralizer_le_normalizer _) basisKD
    let BrCD := brauerNormalizerCharacterResidueHom ideal 2 (vInC V t) (isPGroup_vInC hV)
      (dInC V t) le_rfl (Subgroup.centralizer_le_normalizer _) basisCD
    let BrGM := brauerNormalizerCharacterResidueHom ideal 2 V (isPGroup_two hV) (mV V)
      (Subgroup.centralizer_le_normalizer _) le_rfl basisM
    let BrCK := brauerNormalizerCharacterResidueHom ideal 2 (vInC V t) (isPGroup_vInC hV)
      (kInC V t) (Subgroup.centralizer_le_normalizer _) le_rfl basisK
    (∀ m ∈ mV V, ∀ e ∈ E, m * e * m⁻¹ ∈ E) ∧ Ω.ncard = 6 ∧
    (∀ ν : basisEM.index, ∃ β : basisMD.index,
      characterSubsetIdempotent basisMD (coefficientBlock basisMD R β) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion (eInM_le_dInM hED))
            (complexCharacterIdempotent (basisEM.representation ν).character) ∧
        ∀ β' : basisMD.index, characterSubsetIdempotent basisMD (coefficientBlock basisMD R β') =
            MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion (eInM_le_dInM hED))
              (complexCharacterIdempotent (basisEM.representation ν).character) →
          sameCoefficientBlock basisMD R β β') ∧
    (∀ (ν : E →* ℂˣ) (n : basisMD.index),
      AffordsInflation basisMD (fun x => ((x : mV V) : G)) V ν n →
        characterSubsetIdempotent basisMD (coefficientBlock basisMD R n) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion (eInM_le_dInM hED))
            (complexCharacterIdempotent fun e : eInM V E => (ν ⟨((e : mV V) : G), e.2⟩ : ℂ))) ∧
    (∀ (ν : E →* ℂˣ) (n : basisKD.index),
      AffordsInflation basisKD (fun x => (((x : kInC V t) : cT t) : G)) V ν n →
        characterSubsetIdempotent basisKD (coefficientBlock basisKD R n) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion (eInK_le_dInK hV hED htV))
            (complexCharacterIdempotent fun e : eInK V E t =>
              (ν ⟨(((e : kInC V t) : cT t) : G), e.2⟩ : ℂ))) ∧
    (∀ (ν : E →* ℂˣ) (n : basisCD.index),
      AffordsInflation basisCD (fun x => ((x : cT t) : G)) V ν n →
        characterSubsetIdempotent basisCD (coefficientBlock basisCD R n) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion (eInC_le_dInC hV hED htV))
            (complexCharacterIdempotent fun e : E.subgroupOf (cT t) =>
              (ν ⟨((e : cT t) : G), e.2⟩ : ℂ))) ∧
    ∃ μs : Fin 3 → (E →* ℂˣ),
      (∀ j, μs j ∈ Ω) ∧
      (∀ j, (linearOrbit E (μs j) ((cT t ⊓ mV V : Subgroup G) : Set G)).ncard = 2) ∧
      (∀ j k, j ≠ k → Disjoint (linearOrbit E (μs j) ((cT t ⊓ mV V : Subgroup G) : Set G))
        (linearOrbit E (μs k) ((cT t ⊓ mV V : Subgroup G) : Set G))) ∧
      Ω = ⋃ j, linearOrbit E (μs j) ((cT t ⊓ mV V : Subgroup G) : Set G) ∧
      ∃ (A : basisM.index) (Aj : Fin 3 → basisK.index) (B : basis.index)
        (b : Fin 3 → basisC.index),
        (∀ ν ∈ Ω, ∀ n : basisMD.index,
          AffordsInflation basisMD (fun x => ((x : mV V) : G)) V ν n →
            BrMD n = centralCharacterResidueHom basisM ideal A) ∧
        (∀ j, ∀ ν ∈ linearOrbit E (μs j) ((cT t ⊓ mV V : Subgroup G) : Set G),
          ∀ n : basisKD.index,
          AffordsInflation basisKD (fun x => (((x : kInC V t) : cT t) : G)) V ν n →
            BrKD n = centralCharacterResidueHom basisK ideal (Aj j)) ∧
        BrGM A = centralCharacterResidueHom basis ideal B ∧
        (∀ j, BrCK (Aj j) = centralCharacterResidueHom basisC ideal (b j)) ∧
        coefficientBlockDefect basisM ideal 2 A (vInM V) ∧
        (∀ j, coefficientBlockDefect basisK ideal 2 (Aj j) (vInK V t)) ∧
        coefficientBlockDefect basis ideal 2 B V ∧
        (∀ j, coefficientBlockDefect basisC ideal 2 (b j) (vInC V t)) ∧
        (∀ j k, j ≠ k → coefficientBlock basisC R (b j) ≠ coefficientBlock basisC R (b k)) ∧
        brauerFiberBlocks basis ideal 2 t (isPGroup_zpowers hV htV) basisC B =
          Finset.univ.image (fun j => coefficientBlock basisC R (b j)) ∧
        (∀ j, (Finset.univ.filter fun β =>
              BrCD β = centralCharacterResidueHom basisC ideal (b j)).image
            (coefficientBlock basisCD R) =
          (Finset.univ.filter fun n => ∃ ν ∈ linearOrbit E (μs j)
              ((cT t ⊓ mV V : Subgroup G) : Set G),
            AffordsInflation basisCD (fun x => ((x : cT t) : G)) V ν n).image
            (coefficientBlock basisCD R)) ∧
        (∀ s : cT t, (s : G) ∈ V → (s : G) ∉ Subgroup.zpowers t →
          Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t)) = dInC V t ∧
          ∀ (hs : IsPGroup 2 (Subgroup.zpowers s))
            (basisCs : FiniteIrreducibleCharacterBasis
              (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t)))),
            (∀ (n : basisCs.index) (n' : basisCD.index),
              (∀ (x : Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t)))
                  (y : dInC V t), (x : cT t) = (y : cT t) →
                (basisCs.representation n).character x =
                  (basisCD.representation n').character y) →
              brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers s) hs
                  (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t)))
                  le_rfl (Subgroup.centralizer_le_normalizer _) basisCs n = BrCD n') ∧
            ∀ j, brauerFiberBlocks basisC ideal 2 s hs basisCs (b j) =
              (Finset.univ.filter fun n => ∃ ν ∈ linearOrbit E (μs j)
                  ((cT t ⊓ mV V : Subgroup G) : Set G),
                AffordsInflation basisCs (fun x => ((x : cT t) : G)) V ν n).image
                (coefficientBlock basisCs R)) ∧
        (8 ∣ Nat.card G → ∀ χ ∈ coefficientBlock basis R B,
          (basis.representation χ).character ≠ 1) := by
  intro μ Ω R BrMD BrKD BrCD BrGM BrCK
  have hV2 : IsPGroup 2 V := isPGroup_two hV
  have hVC : V ≤ cT t := le_cT hV htV
  have hDC : dV V ≤ cT t := dV_le_cT htV
  have hEM : E ≤ mV V := le_mV_of_le_dV hED
  obtain ⟨hΩcard, μs, hμsΩ, hΩj2, hΩjdisj, hΩunion⟩ :=
    orbit_structure hV hED hDVE hEodd ω hωV hωstab hAut htV ht1
  have hself : ∀ (ν : E →* ℂˣ) (X : Subgroup G), ν ∈ linearOrbit E ν (X : Set G) :=
    fun ν X => ⟨1, X.one_mem, fun e e' he' => by
      rw [show e' = e from Subtype.ext (by rw [he']; group)]⟩
  have hμΩ : μ ∈ Ω := hself μ (mV V)
  have hEMnormal : (eInM V E).Normal := eInM_normal hV hED hDVE hEodd
  have hEModd : Odd (Nat.card (eInM V E)) := by rw [card_eInM hED]; exact hEodd
  have hEMp : ¬ 2 ∣ Nat.card (eInM V E) := fun h =>
    (Nat.not_even_iff_odd.mpr hEModd) (even_iff_two_dvd.mpr h)
  obtain ⟨QM, hQM⟩ := exists_sylow_mV hV hED hVE hDVE hEodd hAut
  set φM := KleinFourFiber.centralizerSubgroupOfEquiv (le_mV (V := V)) (dV_le_mV (V := V))
    with hφMdef
  obtain ⟨A, hAdef, hAiff⟩ := level_block hV hED hDVE hEodd ω hωV hωstab (mV V).subtype
    Subtype.val_injective (fun h => h.2) (vInM V) (eInM V E) (Subgroup.subgroupOfEquivOfLe hEM)
    (fun y => rfl) (eInM_le_dInM hED) basisMD φM (fun w => rfl) (comm_vInM hV)
    (vInM_inf_eInM hVE) (decomp_dInM hED hDVE) ideal (isPGroup_vInM hV) basisM
    (isKleinFour_vInM hV) QM hQM hEModd (mV V : Set G)
    (fun g => ⟨fun hg => ⟨⟨g, hg⟩, rfl⟩, fun ⟨h, hh⟩ => hh ▸ h.2⟩) hμΩ
    (by rw [show (dV V).comap (mV V).subtype = (dV V).subgroupOf (mV V) from rfl,
      index_dV hV hAut]; decide)
  have hEKnormal : (eInK V E t).Normal := eInK_normal hV hED hDVE hEodd htV
  have hEKodd : Odd (Nat.card (eInK V E t)) := by rw [card_eInK hV hED htV]; exact hEodd
  have hEKp : ¬ 2 ∣ Nat.card (eInK V E t) := fun h =>
    (Nat.not_even_iff_odd.mpr hEKodd) (even_iff_two_dvd.mpr h)
  obtain ⟨QK, hQK⟩ := exists_sylow_kInC hV hED hVE hDVE htV hEodd hAut ht1
  set φC := KleinFourFiber.centralizerSubgroupOfEquiv hVC hDC with hφCdef
  set φK := KleinFourFiber.centralizerSubgroupOfEquiv (vInC_le_kInC (V := V) (t := t))
    (Subgroup.centralizer_le_normalizer _) with hφKdef
  set eEK : eInK V E t ≃* E := (Subgroup.subgroupOfEquivOfLe (eInC_le_kInC hV hED htV)).trans
    (Subgroup.subgroupOfEquivOfLe (le_cT_of_le_dV hED htV)) with heEKdef
  have hρK : Function.Injective (rhoK V t) := fun x y h => Subtype.ext (Subtype.ext h)
  have hKX : ∀ g, g ∈ ((cT t ⊓ mV V : Subgroup G) : Set G) ↔ ∃ h : kInC V t, rhoK V t h = g :=
    fun g => ⟨fun hg => ⟨⟨⟨g, hg.1⟩, (mem_kInC_iff hVC _).mpr hg.2⟩, rfl⟩,
      fun ⟨h, hh⟩ => hh ▸ ⟨h.1.2, (mem_kInC_iff hVC h.1).mp h.2⟩⟩
  have hcommK : ∀ a ∈ vInK V t, ∀ b ∈ vInK V t, a * b = b * a := fun a ha b hb =>
    Subtype.ext (Subtype.ext (comm hV _ ha _ hb))
  have hKidx : Even ((dV V).comap (rhoK V t)).index := by
    rw [index_comap_rhoK hV htV hAut ht1]; decide
  choose Aj hAjdef hAjiff using fun j => level_block hV hED hDVE hEodd ω hωV hωstab
    (rhoK V t) hρK (fun h => (mem_kInC_iff hVC h).mp h.2) (vInK V t) (eInK V E t) eEK
    (fun y => rfl) (eInK_le_dInK hV hED htV) basisKD (φK.trans φC) (fun w => rfl) hcommK
    (vInK_inf_eInK hVE) (decomp_dInK hV hED hDVE htV) ideal (isPGroup_vInK hV) basisK
    (isKleinFour_vInK hV htV) QK hQK hEKodd _ hKX (hμsΩ j) hKidx
  obtain ⟨himG, hmapG, -, hinjG⟩ :=
    CFSG.Wreathed.defect_normalizer_brauer_correspondence basis ideal 2 V hV2 basisM
  obtain ⟨B, hB⟩ := himG A
  have hBdef : coefficientBlockDefect basis ideal 2 B V := hmapG A B hAdef hB
  obtain ⟨himC, hmapC, hsurjC, hinjC⟩ := CFSG.Wreathed.defect_normalizer_brauer_correspondence
    basisC ideal 2 (vInC V t) (isPGroup_vInC hV) basisK
  choose b hb using fun j => himC (Aj j)
  have hbdef : ∀ j, coefficientBlockDefect basisC ideal 2 (b j) (vInC V t) := fun j =>
    hmapC (Aj j) (b j) (hAjdef j) (hb j)
  obtain ⟨basisD⟩ := finiteIrreducibleCharacterBasis_exists (G := dV V)
  set BrGD := brauerNormalizerCharacterResidueHom ideal 2 V hV2 (dV V) le_rfl
    (Subgroup.centralizer_le_normalizer _) basisD with hBrGD
  set BrGC := brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t)
    (isPGroup_zpowers hV htV) (cT t) le_rfl (Subgroup.centralizer_le_normalizer _) basisC
    with hBrGC
  have hT1 : ∀ (γ : basisMD.index) (γD : basisD.index) (A' : basisM.index),
      CFSG.Wreathed.BlockOrbits.LabelTransport basisMD basisD φM γ γD →
      BrMD γ = centralCharacterResidueHom basisM ideal A' → BrGM A' = BrGD γD :=
    fun γ γD A' hγ hc => KleinFourFiber.brauer_composite ideal 2 V V (mV V) hV2 hV2 le_rfl
      (Subgroup.centralizer_le_normalizer _) le_rfl le_mV dV_le_mV basisM basisMD basisD hγ hc
  have hT2 : ∀ (γ : basisCD.index) (γD : basisD.index) (c : basisC.index),
      CFSG.Wreathed.BlockOrbits.LabelTransport basisCD basisD φC γ γD →
      BrCD γ = centralCharacterResidueHom basisC ideal c → BrGC c = BrGD γD :=
    fun γ γD c hγ hc => KleinFourFiber.brauer_composite ideal 2 (Subgroup.zpowers t) V (cT t)
      (isPGroup_zpowers hV htV) hV2 (Subgroup.zpowers_le.mpr htV) le_rfl
      (Subgroup.centralizer_le_normalizer _) hVC hDC basisC basisCD basisD hγ hc
  have hT3 : ∀ (γ : basisKD.index) (γC : basisCD.index) (a : basisK.index),
      CFSG.Wreathed.BlockOrbits.LabelTransport basisKD basisCD φK γ γC →
      BrKD γ = centralCharacterResidueHom basisK ideal a → BrCK a = BrCD γC :=
    fun γ γC a hγ hc => KleinFourFiber.brauer_composite ideal 2 (vInC V t) (vInC V t) (kInC V t)
      (isPGroup_vInC hV) (isPGroup_vInC hV) le_rfl (Subgroup.centralizer_le_normalizer _) le_rfl
      vInC_le_kInC (Subgroup.centralizer_le_normalizer _) basisK basisKD basisCD hγ hc
  have hAffM : ∀ {ν : E →* ℂˣ} {γ : basisMD.index} {γD : basisD.index},
      CFSG.Wreathed.BlockOrbits.LabelTransport basisMD basisD φM γ γD →
      (AffordsInflation basisMD (fun x => ((x : mV V) : G)) V ν γ ↔
        AffordsInflation basisD (fun x => (x : G)) V ν γD) := fun h =>
    affordsInflation_iff_of_labelTransport basisMD basisD φM (fun x => ((x : mV V) : G))
      (fun x => (x : G)) (fun _ => rfl) V _ h
  have hAffC : ∀ {ν : E →* ℂˣ} {γ : basisCD.index} {γD : basisD.index},
      CFSG.Wreathed.BlockOrbits.LabelTransport basisCD basisD φC γ γD →
      (AffordsInflation basisCD (fun x => ((x : cT t) : G)) V ν γ ↔
        AffordsInflation basisD (fun x => (x : G)) V ν γD) := fun h =>
    affordsInflation_iff_of_labelTransport basisCD basisD φC (fun x => ((x : cT t) : G))
      (fun x => (x : G)) (fun _ => rfl) V _ h
  have hAffK : ∀ {ν : E →* ℂˣ} {γ : basisKD.index} {γC : basisCD.index},
      CFSG.Wreathed.BlockOrbits.LabelTransport basisKD basisCD φK γ γC →
      (AffordsInflation basisKD (fun x => (((x : kInC V t) : cT t) : G)) V ν γ ↔
        AffordsInflation basisCD (fun x => ((x : cT t) : G)) V ν γC) := fun h =>
    affordsInflation_iff_of_labelTransport basisKD basisCD φK
      (fun x => (((x : kInC V t) : cT t) : G)) (fun x => ((x : cT t) : G)) (fun _ => rfl) V _ h
  have hbackK : ∀ γC : basisCD.index, ∃ γK : basisKD.index,
      CFSG.Wreathed.BlockOrbits.LabelTransport basisKD basisCD φK γK γC := fun γC => by
    obtain ⟨γK, h⟩ := CFSG.Wreathed.BlockOrbits.labelTransport_exists basisCD basisKD φK.symm γC
    exact ⟨γK, labelTransport_symm h⟩
  have hbackC : ∀ γD : basisD.index, ∃ γC : basisCD.index,
      CFSG.Wreathed.BlockOrbits.LabelTransport basisCD basisD φC γC γD := fun γD => by
    obtain ⟨γC, h⟩ := CFSG.Wreathed.BlockOrbits.labelTransport_exists basisD basisCD φC.symm γD
    exact ⟨γC, labelTransport_symm h⟩
  have hbackM : ∀ γD : basisD.index, ∃ γM : basisMD.index,
      CFSG.Wreathed.BlockOrbits.LabelTransport basisMD basisD φM γM γD := fun γD => by
    obtain ⟨γM, h⟩ := CFSG.Wreathed.BlockOrbits.labelTransport_exists basisD basisMD φM.symm γD
    exact ⟨γM, labelTransport_symm h⟩
  have hH1 : ∀ j, ∀ ν ∈ linearOrbit E (μs j) ((cT t ⊓ mV V : Subgroup G) : Set G),
      ∀ γC : basisCD.index, AffordsInflation basisCD (fun x => ((x : cT t) : G)) V ν γC →
        BrCD γC = centralCharacterResidueHom basisC ideal (b j) := by
    intro j ν hν γC hγC
    obtain ⟨γK, hγK⟩ := hbackK γC
    have hBrK : BrKD γK = centralCharacterResidueHom basisK ideal (Aj j) :=
      (hAjiff j γK).mpr ⟨ν, hν, γK, (hAffK hγK).mpr hγC, sameCoefficientBlock_refl _ _ _⟩
    rw [← hT3 γK γC (Aj j) hγK hBrK]
    exact hb j
  have hH2 : ∀ j, BrGC (b j) = centralCharacterResidueHom basis ideal B := by
    intro j
    obtain ⟨γC, hγC⟩ := exists_affording_label hV hED hDVE hEodd ω hωV (cT t).subtype
      (vInC V t) basisCD φC (fun w => rfl) (hμsΩ j)
    obtain ⟨γD, hγD⟩ := CFSG.Wreathed.BlockOrbits.labelTransport_exists basisCD basisD φC γC
    obtain ⟨γM, hγM⟩ := hbackM γD
    have hγMaff : AffordsInflation basisMD (fun x => ((x : mV V) : G)) V (μs j) γM :=
      (hAffM hγM).mpr ((hAffC hγD).mp hγC)
    have hBrM : BrMD γM = centralCharacterResidueHom basisM ideal A :=
      (hAiff γM).mpr ⟨μs j, hμsΩ j, γM, hγMaff, sameCoefficientBlock_refl _ _ _⟩
    rw [hT2 γC γD (b j) hγD (hH1 j (μs j) (hself _ _) γC hγC), ← hT1 γM γD A hγM hBrM]
    exact hB
  have hsameRes : ∀ {X : Type} [Group X] [Fintype X] (bX : FiniteIrreducibleCharacterBasis X)
      (x y : bX.index), sameCoefficientBlock bX R x y →
        centralCharacterResidueHom bX ideal x = centralCharacterResidueHom bX ideal y :=
    fun bX x y h => (sameCoefficientBlock_iff_centralCharacterResidueHom_eq bX ideal x y).mp h
  have hH4 : ∀ j (β : basisCD.index),
      BrCD β = centralCharacterResidueHom basisC ideal (b j) ↔
        ∃ n, (∃ ν ∈ linearOrbit E (μs j) ((cT t ⊓ mV V : Subgroup G) : Set G),
          AffordsInflation basisCD (fun x => ((x : cT t) : G)) V ν n) ∧
          sameCoefficientBlock basisCD R n β := by
    intro j β
    constructor
    · intro hβ
      obtain ⟨βK, hβK⟩ := hbackK β
      obtain ⟨A', hA'⟩ := brauerNormalizer_block_image_exists basisK ideal 2 (vInK V t)
        (isPGroup_vInK hV) (dInK V t) le_rfl (Subgroup.centralizer_le_normalizer _) basisKD βK
      have hCA' : BrCK A' = centralCharacterResidueHom basisC ideal (b j) :=
        (hT3 βK β A' hβK hA').trans hβ
      have hA'def := defect_normalizer_brauer_preimage_exact_defect basisC ideal 2 (vInC V t)
        (isPGroup_vInC hV) (b j) (hbdef j) basisK A' hCA'
      have hsameA := hinjC A' (Aj j) hA'def (hAjdef j) (hCA'.trans (hb j).symm)
      have hβK' : BrKD βK = centralCharacterResidueHom basisK ideal (Aj j) := by
        have hA'' : BrKD βK = centralCharacterResidueHom basisK ideal A' := hA'
        rw [hA'', hsameRes basisK A' (Aj j) hsameA]
      obtain ⟨ν, hν, n', hn', hsame'⟩ := (hAjiff j βK).mp hβK'
      obtain ⟨n'C, hn'C⟩ := CFSG.Wreathed.BlockOrbits.labelTransport_exists basisKD basisCD φK n'
      exact ⟨n'C, ⟨ν, hν, (hAffK hn'C).mp hn'⟩,
        (CFSG.Wreathed.BlockOrbits.sameCoefficientBlock_labelTransport_iff basisKD basisCD ideal
          φK hn'C hβK).mp hsame'⟩
    · rintro ⟨n, ⟨ν, hν, hn⟩, hsame⟩
      have heq : BrCD n = BrCD β := KleinFourFiber.brauer_eq_of_same ideal 2 (vInC V t)
        (isPGroup_vInC hV) (dInC V t) le_rfl (Subgroup.centralizer_le_normalizer _) basisCD hsame
      rw [← heq]
      exact hH1 j ν hν n hn
  have hcardV : Nat.card V = 4 := hV.card_four
  have hordt : orderOf t = 2 := orderOf_eq_prime (by rw [sq, mul_self hV htV]) ht1
  have hcardZ : Nat.card (Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, hordt]
  have hH3 : ∀ c : basisC.index, BrGC c = centralCharacterResidueHom basis ideal B →
      ∃ j, sameCoefficientBlock basisC R (b j) c := by
    intro c hc
    obtain ⟨F, hF⟩ := coefficientBlockDefect_exists basisC ideal 2 c
    have : ((Subgroup.zpowers t).subgroupOf (cT t)).Normal := zpowers_subgroupOf_normal
    have hZF : (Subgroup.zpowers t).subgroupOf (cT t) ≤ F :=
      normal_p_le_coefficientBlockDefect basisC ideal 2 ((Subgroup.zpowers t).subgroupOf (cT t))
        (isPGroup_zpowers hV htV).comap_subtype hF
    set F' := F.map (cT t).subtype with hF'def
    have hFF' : F'.subgroupOf (cT t) = F :=
      Subgroup.comap_map_eq_self_of_injective (cT t).subtype_injective F
    have hF'p : IsPGroup 2 F' := (coefficientBlockDefect_isPGroup basisC ideal hF).map _
    have hPF' : Subgroup.zpowers t ≤ F' := fun x hx =>
      ⟨⟨x, zpowers_le_cT hV htV hx⟩, hZF (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hF'C : F' ≤ cT t := Subgroup.map_subtype_le F
    have hlocal : coefficientBlockDefect basisC ideal 2 c (F'.subgroupOf (cT t)) := by
      rw [hFF']
      exact hF
    have hsub := (centralizer_brauer_image_defect_contains_local_defect basis ideal 2
      (Subgroup.zpowers t) (isPGroup_zpowers hV htV) F' hF'p hPF' hF'C basisC c hlocal B hc).1
      V hBdef
    have hle4 : Nat.card F' ≤ 4 := hcardV ▸ subgroupSubconjugate_card_le hsub
    have hge2 : 2 ≤ Nat.card F' := hcardZ ▸ Subgroup.card_le_of_le hPF'
    obtain ⟨k, hk⟩ := hF'p.exists_card_eq
    have hk12 : k = 1 ∨ k = 2 := by
      rw [hk] at hle4 hge2
      rcases k with _ | _ | _ | k
      · norm_num at hge2
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exfalso
        have h8 : 2 ^ 3 ≤ 2 ^ (k + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    rcases hk12 with rfl | rfl
    ·
      exfalso
      have hF'eq : F' = Subgroup.zpowers t :=
        (Subgroup.eq_of_le_of_card_ge hPF' (by rw [hk, hcardZ]; norm_num)).symm
      have hcZ :
          coefficientBlockDefect basisC ideal 2 c ((Subgroup.zpowers t).subgroupOf (cT t)) := by
        rw [← hF'eq]
        exact hlocal
      obtain ⟨-, hmapT, -, -⟩ := centralizer_normalizer_controlled_defect_correspondence basis ideal
        2 (Subgroup.zpowers t) (isPGroup_zpowers hV htV) (Subgroup.zpowers t)
        (isPGroup_zpowers hV htV) le_rfl (zpowers_le_cT hV htV)
        (KleinFourFiber.normalizer_zpowers_le ht1 (mul_self hV htV)) basisC
      have hBt := hmapT c B hcZ hc
      obtain ⟨g, hg⟩ := coefficientBlockDefect_conjugate basis ideal hBdef hBt
      have hcg := conjugation_subgroup_card V g
      rw [hg, hcardZ, hcardV] at hcg
      norm_num at hcg
    ·
      have hF'4 : Nat.card F' = 4 := by rw [hk]; norm_num
      obtain ⟨g, hg⟩ := subgroupsConjugate_of_subconjugate_card_ge hsub (by rw [hF'4, hcardV])
      have hF'K : IsKleinFour F' :=
        { card_four := hF'4
          exponent_two := by
            rw [Monoid.exponent_eq_of_mulEquiv ((F'.equivMapOfInjective
              (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
                (MulEquiv.subgroupCongr hg))]
            exact hV.exponent_two }
      obtain ⟨c', hc'C, hc'⟩ := hfour F' hF'K (hPF' (Subgroup.mem_zpowers t)) hF'C
      have hconjC : subgroupsConjugate F (vInC V t) := by
        refine ⟨⟨c', hc'C⟩, ?_⟩
        apply Subgroup.map_injective (cT t).subtype_injective
        rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hVC, ← hc', hF'def,
          Subgroup.map_map]
        rfl
      have hcdef := FourGroupParity.coefficientBlockDefect_of_subgroupsConjugate basisC ideal hF
        hconjC
      obtain ⟨a, -, hac⟩ := hsurjC c hcdef
      obtain ⟨ebK⟩ := finiteIrreducibleCharacterBasis_exists (G := eInK V E t)
      obtain ⟨-, -, -, -, -, -, -, -, -, hsurjK, -⟩ :=
        normal_abelian_p_centralizer_orbit_idempotents basisK ideal 2 (vInK V t)
          (isPGroup_vInK hV) hcommK (eInK V E t) (eInK_le_dInK hV hED htV) hEKp
          (vInK_inf_eInK hVE) (decomp_dInK hV hED hDVE htV) basisKD ebK
      obtain ⟨-, βK, -, hβK⟩ := hsurjK a
      obtain ⟨βC, hβC⟩ := CFSG.Wreathed.BlockOrbits.labelTransport_exists basisKD basisCD φK βK
      have hβCc : BrCD βC = centralCharacterResidueHom basisC ideal c :=
        (hT3 βK βC a hβC hβK).symm.trans hac
      obtain ⟨βD, hβD⟩ := CFSG.Wreathed.BlockOrbits.labelTransport_exists basisCD basisD φC βC
      have hβDB : BrGD βD = centralCharacterResidueHom basis ideal B :=
        (hT2 βC βD c hβD hβCc).symm.trans hc
      obtain ⟨βM, hβM⟩ := hbackM βD
      obtain ⟨A', hA'⟩ := brauerNormalizer_block_image_exists basisM ideal 2 (vInM V)
        (isPGroup_vInM hV) (dInM V) le_rfl (Subgroup.centralizer_le_normalizer _) basisMD βM
      have hGA' : BrGM A' = centralCharacterResidueHom basis ideal B :=
        (hT1 βM βD A' hβM hA').trans hβDB
      have hA'def := defect_normalizer_brauer_preimage_exact_defect basis ideal 2 V hV2 B hBdef
        basisM A' hGA'
      have hsameA := hinjG A A' hAdef hA'def (hB.trans hGA'.symm)
      have hβMA : BrMD βM = centralCharacterResidueHom basisM ideal A :=
        hA'.trans (hsameRes basisM A A' hsameA).symm
      obtain ⟨ν, hνΩ, n', hn', hsame'⟩ := (hAiff βM).mp hβMA
      have hνU : ν ∈ ⋃ j, linearOrbit E (μs j) ((cT t ⊓ mV V : Subgroup G) : Set G) := by
        rw [← hΩunion]
        exact hνΩ
      obtain ⟨j, hνj⟩ := Set.mem_iUnion.mp hνU
      obtain ⟨n'D, hn'D⟩ := CFSG.Wreathed.BlockOrbits.labelTransport_exists basisMD basisD φM n'
      obtain ⟨n'C, hn'C⟩ := hbackC n'D
      obtain ⟨n'K, hn'K⟩ := hbackK n'C
      have hsameD := (CFSG.Wreathed.BlockOrbits.sameCoefficientBlock_labelTransport_iff basisMD
        basisD ideal φM hn'D hβM).mp hsame'
      have hsameC := (CFSG.Wreathed.BlockOrbits.sameCoefficientBlock_labelTransport_iff basisCD
        basisD ideal φC hn'C hβD).mpr hsameD
      have hsameK := (CFSG.Wreathed.BlockOrbits.sameCoefficientBlock_labelTransport_iff basisKD
        basisCD ideal φK hn'K hβC).mpr hsameC
      have hn'Kaff := (hAffK hn'K).mpr ((hAffC hn'C).mpr ((hAffM hn'D).mp hn'))
      have hβKj : BrKD βK = centralCharacterResidueHom basisK ideal (Aj j) :=
        (hAjiff j βK).mpr ⟨ν, hνj, n'K, hn'Kaff, hsameK⟩
      have hsameAa : sameCoefficientBlock basisK R a (Aj j) :=
        (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basisK ideal a (Aj j)).mpr
          (hβK.symm.trans hβKj)
      have hBrCKeq : BrCK a = BrCK (Aj j) := KleinFourFiber.brauer_eq_of_same ideal 2 (vInC V t)
        (isPGroup_vInC hV) (kInC V t) (Subgroup.centralizer_le_normalizer _) le_rfl basisK hsameAa
      exact ⟨j, (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basisC ideal (b j) c).mpr
        ((hb j).symm.trans (hBrCKeq.symm.trans hac))⟩
  have hfib : brauerFiberBlocks basis ideal 2 t (isPGroup_zpowers hV htV) basisC B =
      Finset.univ.image fun j => coefficientBlock basisC R (b j) := by
    unfold brauerFiberBlocks
    ext Y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      obtain ⟨j, hj⟩ := hH3 θ hθ
      exact ⟨j, (KleinFourFiber.coefficientBlock_eq_iff basisC R (b j) θ).mpr hj⟩
    · rintro ⟨j, rfl⟩
      exact ⟨b j, hH2 j, rfl⟩
  have hdist : ∀ j k, j ≠ k →
      coefficientBlock basisC R (b j) ≠ coefficientBlock basisC R (b k) := by
    intro j k hjk heq
    have hsame := (KleinFourFiber.coefficientBlock_eq_iff basisC R (b j) (b k)).mp heq
    have hsameA := hinjC (Aj j) (Aj k) (hAjdef j) (hAjdef k)
      ((hb j).trans ((hsameRes basisC (b j) (b k) hsame).trans (hb k).symm))
    obtain ⟨γK, hγK⟩ := exists_affording_label hV hED hDVE hEodd ω hωV (rhoK V t) (vInK V t)
      basisKD (φK.trans φC) (fun w => rfl) (hμsΩ k)
    have hk : BrKD γK = centralCharacterResidueHom basisK ideal (Aj k) :=
      (hAjiff k γK).mpr ⟨μs k, hself _ _, γK, hγK, sameCoefficientBlock_refl _ _ _⟩
    have hj : BrKD γK = centralCharacterResidueHom basisK ideal (Aj j) :=
      hk.trans (hsameRes basisK (Aj j) (Aj k) hsameA).symm
    obtain ⟨ν, hν, n', hn', hsame'⟩ := (hAjiff j γK).mp hj
    have hνk : ν = μs k := eq_of_sameCoefficientBlock_of_affordsInflation (rhoK V t) (vInK V t)
      (eInK V E t) eEK (fun y => rfl) (eInK_le_dInK hV hED htV) basisKD hcommK
      (vInK_inf_eInK hVE) (decomp_dInK hV hED hDVE htV) ideal (isPGroup_vInK hV) hEKp hn' hγK
      hsame'
    exact Set.disjoint_left.mp (hΩjdisj j k hjk) (hνk ▸ hν) (hself _ _)
  have hslevel : ∀ s : cT t, (s : G) ∈ V → (s : G) ∉ Subgroup.zpowers t →
      Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t)) = dInC V t ∧
      ∀ (hs : IsPGroup 2 (Subgroup.zpowers s))
        (basisCs : FiniteIrreducibleCharacterBasis
          (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t)))),
        (∀ (n : basisCs.index) (n' : basisCD.index),
          (∀ (x : Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t)))
              (y : dInC V t), (x : cT t) = (y : cT t) →
            (basisCs.representation n).character x = (basisCD.representation n').character y) →
          brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers s) hs
              (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t)))
              le_rfl (Subgroup.centralizer_le_normalizer _) basisCs n = BrCD n') ∧
        ∀ j, brauerFiberBlocks basisC ideal 2 s hs basisCs (b j) =
          (Finset.univ.filter fun n => ∃ ν ∈ linearOrbit E (μs j)
              ((cT t ⊓ mV V : Subgroup G) : Set G),
            AffordsInflation basisCs (fun x => ((x : cT t) : G)) V ν n).image
            (coefficientBlock basisCs R) := by
    intro s hsV hst
    have heq := centralizer_zpowers_eq_dInC hV htV ht1 s hsV hst
    refine ⟨heq, fun hs basisCs => ?_⟩
    set e := MulEquiv.subgroupCongr heq with hedef
    have hproj : ∀ z, centralCoefficientTransport R e
        (centralNormalizerCoefficientProjection R (Subgroup.zpowers s)
          (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t))) le_rfl
          (Subgroup.centralizer_le_normalizer _) z) =
        centralNormalizerCoefficientProjection R (vInC V t) (dInC V t) le_rfl
          (Subgroup.centralizer_le_normalizer _) z := by
      intro z
      apply Subtype.ext
      ext y
      rw [centralCoefficientTransport_coeff, centralNormalizerCoefficientProjection_coeff,
        centralNormalizerCoefficientProjection_coeff, ite_eq_left (e.symm y).2, ite_eq_left y.2]
      rfl
    have hBr : ∀ (n : basisCs.index) (n' : basisCD.index),
        CFSG.Wreathed.BlockOrbits.LabelTransport basisCs basisCD e n n' →
        brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers s) hs
            (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t)))
            le_rfl (Subgroup.centralizer_le_normalizer _) basisCs n = BrCD n' := by
      intro n n' hnn'
      apply RingHom.ext
      intro z
      change centralCharacterResidueHom basisCs ideal n
          (centralNormalizerCoefficientProjection R (Subgroup.zpowers s) _ le_rfl _ z) =
        centralCharacterResidueHom basisCD ideal n'
          (centralNormalizerCoefficientProjection R (vInC V t) (dInC V t) le_rfl _ z)
      rw [← hproj z,
        CFSG.Wreathed.BlockOrbits.centralCharacterResidueHom_labelTransport basisCs basisCD ideal e
          hnn']
    refine ⟨fun n n' hcompat => hBr n n' fun x => (hcompat x (e x) rfl).symm, fun j => ?_⟩
    have hLW : ∀ θ : basisCs.index,
        brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers s) hs
            (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t)))
            le_rfl (Subgroup.centralizer_le_normalizer _) basisCs θ =
          centralCharacterResidueHom basisC ideal (b j) ↔
        ∃ n, (∃ ν ∈ linearOrbit E (μs j) ((cT t ⊓ mV V : Subgroup G) : Set G),
          AffordsInflation basisCs (fun x => ((x : cT t) : G)) V ν n) ∧
          sameCoefficientBlock basisCs R n θ := by
      intro θ
      obtain ⟨θ', hθ'⟩ := CFSG.Wreathed.BlockOrbits.labelTransport_exists basisCs basisCD e θ
      rw [hBr θ θ' hθ', hH4 j θ']
      constructor
      · rintro ⟨n', ⟨ν, hν, hn'⟩, hsame⟩
        obtain ⟨n, hn⟩ := CFSG.Wreathed.BlockOrbits.labelTransport_exists basisCD basisCs e.symm n'
        have hn2 := labelTransport_symm hn
        exact ⟨n, ⟨ν, hν, (affordsInflation_iff_of_labelTransport basisCs basisCD e
            (fun x => ((x : cT t) : G)) (fun x => ((x : cT t) : G)) (fun _ => rfl) V ν hn2).mpr
            hn'⟩,
          (CFSG.Wreathed.BlockOrbits.sameCoefficientBlock_labelTransport_iff basisCs basisCD ideal
            e hn2 hθ').mpr hsame⟩
      · rintro ⟨n, ⟨ν, hν, hn⟩, hsame⟩
        obtain ⟨n', hn'⟩ := CFSG.Wreathed.BlockOrbits.labelTransport_exists basisCs basisCD e n
        exact ⟨n', ⟨ν, hν, (affordsInflation_iff_of_labelTransport basisCs basisCD e
            (fun x => ((x : cT t) : G)) (fun x => ((x : cT t) : G)) (fun _ => rfl) V ν hn').mp
            hn⟩,
          (CFSG.Wreathed.BlockOrbits.sameCoefficientBlock_labelTransport_iff basisCs basisCD ideal
            e hn' hθ').mp hsame⟩
    exact image_coefficientBlock_eq_of_iff basisCs R _ _ hLW
  have hnp : 8 ∣ Nat.card G → ∀ χ ∈ coefficientBlock basis R B,
      (basis.representation χ).character ≠ 1 := by
    intro h8 χ hχ hχ1
    have hsame := (coefficientBlock_mem_iff basis R B χ).mp hχ
    have hχdef := (coefficientBlockDefect_iff_of_same_block basis ideal 2 hsame V).mp hBdef
    obtain ⟨P, hP⟩ := (CFSG.BlockBasics.principal_coefficientBlockDefect_iff_sylow_of_shared 2
      ideal basis χ hχ1 V).mp hχdef
    have h8P := P.pow_dvd_card_of_pow_dvd_card (n := 3)
      (by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact h8)
    rw [hP, hcardV] at h8P
    norm_num at h8P
  obtain ⟨-, -, -, -, hexists5, -⟩ := normal_abelian_p_centralizer_orbit_idempotents basisM ideal 2
    (vInM V) (isPGroup_vInM hV) (comm_vInM hV) (eInM V E) (eInM_le_dInM hED) hEMp
    (vInM_inf_eInM hVE) (decomp_dInM hED hDVE) basisMD basisEM
  have hECp : ¬ 2 ∣ Nat.card (E.subgroupOf (cT t)) := by
    rw [card_eInC hED htV]
    exact fun h => (Nat.not_even_iff_odd.mpr hEodd) (even_iff_two_dvd.mpr h)
  refine ⟨fun m hm e he => conj_mem_of_mem hV hED hDVE hEodd hm he, hΩcard, hexists5,
    fun ν n hn => blockIdempotent_of_affordsInflation (mV V).subtype (vInM V) (eInM V E)
      (Subgroup.subgroupOfEquivOfLe hEM) (fun y => rfl) (eInM_le_dInM hED) basisMD (comm_vInM hV)
      (vInM_inf_eInM hVE) (decomp_dInM hED hDVE) ideal (isPGroup_vInM hV) hEMp hn,
    fun ν n hn => blockIdempotent_of_affordsInflation (rhoK V t) (vInK V t) (eInK V E t) eEK
      (fun y => rfl) (eInK_le_dInK hV hED htV) basisKD hcommK (vInK_inf_eInK hVE)
      (decomp_dInK hV hED hDVE htV) ideal (isPGroup_vInK hV) hEKp hn,
    fun ν n hn => blockIdempotent_of_affordsInflation (cT t).subtype (vInC V t)
      (E.subgroupOf (cT t)) (Subgroup.subgroupOfEquivOfLe (le_cT_of_le_dV hED htV))
      (fun y => rfl) (eInC_le_dInC hV hED htV) basisCD (comm_vInC hV) (vInC_inf_eInC hVE)
      (decomp_dInC hV hED hDVE htV) ideal (isPGroup_vInC hV) hECp hn,
    μs, hμsΩ, hΩj2, hΩjdisj, hΩunion, A, Aj, B, b,
    fun ν hν n hn => (hAiff n).mpr ⟨ν, hν, n, hn, sameCoefficientBlock_refl _ _ _⟩,
    fun j ν hν n hn => (hAjiff j n).mpr ⟨ν, hν, n, hn, sameCoefficientBlock_refl _ _ _⟩,
    hB, hb, hAdef, hAjdef, hBdef, hbdef, hdist, hfib,
    fun j => image_coefficientBlock_eq_of_iff basisCD R _ _ (hH4 j), hslevel, hnp⟩

theorem free_six_semidihedral_hypotheses {G : Type*} [Group G] [Fintype G] (V : Subgroup G)
    (hV : IsKleinFour V) (t : G) (htV : t ∈ V) (S : Sylow 2 G) (hVS : V ≤ S) {n : ℕ}
    (hn : 4 ≤ n) (f : CFSG.Open.SemidihedralGroup n ≃* (S : Subgroup G))
    (hZ : ∀ x : (S : Subgroup G),
      x ∈ Subgroup.center (S : Subgroup G) ↔ (x : G) ∈ Subgroup.zpowers t) :
    (∀ U : Subgroup G, IsKleinFour U → t ∈ U → U ≤ cT t →
      ∃ c ∈ cT t, U.map (MulAut.conj c).toMonoidHom = V) ∧ 8 ∣ Nat.card G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htS : t ∈ (S : Subgroup G) := hVS htV
  have htcen : (⟨t, htS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) :=
    (hZ _).mpr (Subgroup.mem_zpowers t)
  have hSC : (S : Subgroup G) ≤ cT t := by
    intro s hs
    apply DihedralAssociates.mem_centralizer_zpowers_of_commute
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp htcen ⟨s, hs⟩)
  refine ⟨fun U hU htU hUC => ?_, ?_⟩
  ·
    obtain ⟨Q, hQ⟩ := ((isPGroup_two hU).comap_subtype (K := cT t)).exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (cT t) Q (S.subtype hSC)
    set U' := U.map (MulAut.conj (g : G)).toMonoidHom with hU'def
    have hU'S : U' ≤ (S : Subgroup G) := by
      rintro _ ⟨u, hu, rfl⟩
      have huQ : (⟨u, hUC hu⟩ : cT t) ∈ (Q : Subgroup (cT t)) := hQ (Subgroup.mem_subgroupOf.mpr hu)
      have hmem : g * ⟨u, hUC hu⟩ * g⁻¹ ∈ ((g • Q : Sylow 2 (cT t)) : Subgroup (cT t)) := by
        rw [Sylow.coe_subgroup_smul]
        exact ⟨_, huQ, rfl⟩
      rw [hg, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    have hU'K : IsKleinFour U' :=
      { card_four := by
          rw [← hU.card_four]
          exact Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective
        exponent_two := by
          rw [← Monoid.exponent_eq_of_mulEquiv
            (U.equivMapOfInjective (MulAut.conj (g : G)).toMonoidHom
              (MulAut.conj (g : G)).injective)]
          exact hU.exponent_two }
    obtain ⟨-, -, hconj⟩ := CFSG.Semidihedral.Local.semidihedral_four_subgroup_centralizers n hn f
    obtain ⟨h, -, hh⟩ := hconj (U'.subgroupOf S) (V.subgroupOf S)
      (KleinFourFiber.isKleinFour_subgroupOf hU'K hU'S)
      (KleinFourFiber.isKleinFour_subgroupOf hV hVS)
    refine ⟨(h : G) * g, (cT t).mul_mem (hSC h.2) g.2, ?_⟩
    have hmap := congrArg (Subgroup.map (S : Subgroup G).subtype) hh
    rw [Subgroup.map_subgroupOf_eq_of_le hVS, Subgroup.map_map] at hmap
    rw [hmap, show (MulAut.conj ((h : G) * g)).toMonoidHom =
      (MulAut.conj (h : G)).toMonoidHom.comp (MulAut.conj (g : G)).toMonoidHom by ext; simp,
      ← Subgroup.map_map, ← hU'def]
    have hcomp : (S : Subgroup G).subtype.comp (MulAut.conj h).toMonoidHom =
        (MulAut.conj (h : G)).toMonoidHom.comp (S : Subgroup G).subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hU'S]
  · have hS : Nat.card (S : Subgroup G) = 2 ^ n := by
      rw [← Nat.card_congr f.toEquiv, CFSG.Semidihedral.card n (by omega)]
    have h8 : 8 ∣ Nat.card (S : Subgroup G) := by
      rw [hS, show n = 3 + (n - 3) by omega, pow_add]
      exact Dvd.intro _ rfl
    exact h8.trans (Subgroup.card_subgroup_dvd_card _)

end CFSG.Semidihedral.Principal
