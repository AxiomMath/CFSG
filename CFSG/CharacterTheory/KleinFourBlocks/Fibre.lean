module

public import CFSG.CharacterTheory.KleinFourBlocks.FibreLabels
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.Principal.BrauerFiberSectionInduction

public section

open CFSG CFSG.TwoRankLowerBound.Helpers CFSG.BrauerThirdMainTheorem.Helpers
  CFSG.Wreathed CFSG.Wreathed.BlockOrbits CFSG.BlockBasics
  CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.KleinFourFiber
  CFSG.Semidihedral.Principal.ControlledDefect CFSG.Semidihedral.Principal.FreeSix

open scoped Classical

namespace CFSG.KleinFourBlocks

variable {G : Type*} [Group G]

theorem free_orbit_defect_four_block {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (V : Subgroup G) (hV : IsKleinFour V) (t : G) (htV : t ∈ V) (ht1 : t ≠ 1)
    (hAut : Function.Surjective V.normalizerMonoidHom)
    (hfour : ∀ U : Subgroup G, IsKleinFour U → t ∈ U → U ≤ cT t → subgroupsConjugate U V →
      ∃ c ∈ cT t, U.map (MulAut.conj c).toMonoidHom = V)
    (f₀ : G → ℂ) (hf₀supp : ∀ g, g ∉ dV V → f₀ g = 0)
    (hf₀cls : ∀ d ∈ dV V, ∀ g, f₀ (d⁻¹ * g * d) = f₀ g)
    (hf₀V : ∀ v ∈ V, ∀ g, f₀ (v * g) = f₀ g)
    (hf₀stab : ∀ m ∈ mV V, (∀ g, f₀ (m⁻¹ * g * m) = f₀ g) → m ∈ dV V)
    (basisM : FiniteIrreducibleCharacterBasis (mV V))
    (basisMD : FiniteIrreducibleCharacterBasis (dInM V))
    (basisK : FiniteIrreducibleCharacterBasis (kInC V t))
    (basisKD : FiniteIrreducibleCharacterBasis (dInK V t))
    (basisC : FiniteIrreducibleCharacterBasis (cT t))
    (basisCD : FiniteIrreducibleCharacterBasis (dInC V t))
    (basisD : FiniteIrreducibleCharacterBasis (dV V))
    (n₀ : basisD.index) (hn₀ : AffordsFun basisD (fun x => (x : G)) f₀ n₀)
    (hdef₀ : coefficientBlockDefect basisD ideal 2 n₀ (V.subgroupOf (dV V)))
    (hblock₀ : ∀ ℓ : basisD.index,
      sameCoefficientBlock basisD (localizedComplexIntegerRing ideal) n₀ ℓ →
      (∀ (x x' : dV V) (v : G), v ∈ V → (x : G) = v * x' →
        (basisD.representation ℓ).character x = (basisD.representation ℓ).character x') →
      ∀ x, (basisD.representation ℓ).character x = (basisD.representation n₀).character x) :
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
    (fOrbit V f₀).ncard = 6 ∧
    ∃ fs : Fin 3 → (G → ℂ),
      (∀ j, fs j ∈ fOrbit V f₀) ∧
      (∀ j, (kOrbit V t (fs j)).ncard = 2) ∧
      (∀ j k, j ≠ k → Disjoint (kOrbit V t (fs j)) (kOrbit V t (fs k))) ∧
      fOrbit V f₀ = ⋃ j, kOrbit V t (fs j) ∧
      ∃ (A : basisM.index) (Aj : Fin 3 → basisK.index) (B : basis.index)
        (b : Fin 3 → basisC.index),
        (∀ f ∈ fOrbit V f₀, ∀ n : basisMD.index,
          AffordsFun basisMD (fun x => ((x : mV V) : G)) f n →
            BrMD n = centralCharacterResidueHom basisM ideal A) ∧
        (∀ j, ∀ f ∈ kOrbit V t (fs j), ∀ n : basisKD.index,
          AffordsFun basisKD (fun x => (((x : kInC V t) : cT t) : G)) f n →
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
          (Finset.univ.filter fun n => ∃ f ∈ kOrbit V t (fs j),
            AffordsFun basisCD (fun x => ((x : cT t) : G)) f n).image
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
              (Finset.univ.filter fun n => ∃ f ∈ kOrbit V t (fs j),
                AffordsFun basisCs (fun x => ((x : cT t) : G)) f n).image
                (coefficientBlock basisCs R)) := by
  intro R BrMD BrKD BrCD BrGM BrCK
  have hV2 : IsPGroup 2 V := isPGroup_two hV
  have hVC : V ≤ cT t := le_cT hV htV
  have hDC : dV V ≤ cT t := dV_le_cT htV
  have hdata : FreeBlockData V f₀ := ⟨hf₀supp, hf₀cls, hf₀V, hf₀stab⟩
  obtain ⟨hΩcard, fs, hfsΩ, hΩj2, hΩjdisj, hΩunion⟩ :=
    orbit_structure_fun hV hAut htV ht1 hdata
  refine ⟨hΩcard, fs, hfsΩ, hΩj2, hΩjdisj, hΩunion, ?_⟩
  have hself : ∀ f : G → ℂ, f ∈ kOrbit V t f := fun f =>
    ⟨1, (cT t ⊓ mV V).one_mem, fun g => by simp⟩
  set φM := KleinFourFiber.centralizerSubgroupOfEquiv (le_mV (V := V)) (dV_le_mV (V := V))
    with hφMdef
  set φC := KleinFourFiber.centralizerSubgroupOfEquiv hVC hDC with hφCdef
  set φK := KleinFourFiber.centralizerSubgroupOfEquiv (vInC_le_kInC (V := V) (t := t))
    (Subgroup.centralizer_le_normalizer _) with hφKdef
  have hρK : Function.Injective (rhoK V t) := fun x y h => Subtype.ext (Subtype.ext h)
  have hKX : ∀ g, g ∈ ((cT t ⊓ mV V : Subgroup G) : Set G) ↔ ∃ h : kInC V t, rhoK V t h = g :=
    fun g => ⟨fun hg => ⟨⟨⟨g, hg.1⟩, (mem_kInC_iff hVC _).mpr hg.2⟩, rfl⟩,
      fun ⟨h, hh⟩ => hh ▸ ⟨h.1.2, (mem_kInC_iff hVC h.1).mp h.2⟩⟩
  have hcommK : ∀ a ∈ vInK V t, ∀ b ∈ vInK V t, a * b = b * a := fun a ha b hb =>
    Subtype.ext (Subtype.ext (comm hV _ ha _ hb))
  obtain ⟨βM, hβM⟩ := exists_affords basisD hn₀ basisMD (fun x => ((x : mV V) : G)) φM
    (fun w => rfl) (fOrbit_self_mem V f₀)
  obtain ⟨A, hAdef, hAeq, hAiff⟩ := level_block_fun hdata basisD ideal hn₀ hdef₀ hblock₀
    (mV V).subtype Subtype.val_injective (fun h => h.2) (vInM V) (isPGroup_vInM hV)
    (comm_vInM hV) (fun a => Iff.rfl) basisMD (fun x => ((x : mV V) : G)) (fun w => rfl) φM
    (fun w => rfl) basisM (mV V : Set G)
    (fun g => ⟨fun hg => ⟨⟨g, hg⟩, rfl⟩, fun ⟨h, hh⟩ => hh ▸ h.2⟩) (fOrbit_self_mem V f₀) hβM
  have hKex : ∀ j, ∃ β : basisKD.index,
      AffordsFun basisKD (fun x => (((x : kInC V t) : cT t) : G)) (fs j) β := fun j =>
    exists_affords basisD hn₀ basisKD _ (φK.trans φC) (fun w => rfl) (hfsΩ j)
  choose βK hβK using hKex
  choose Aj hAjdef hAjeq hAjiff using fun j => level_block_fun hdata basisD ideal hn₀ hdef₀
    hblock₀ (rhoK V t) hρK (fun h => (mem_kInC_iff hVC h.1).mp h.2) (vInK V t)
    (isPGroup_vInK hV) hcommK (fun a => Iff.rfl) basisKD
    (fun x => (((x : kInC V t) : cT t) : G)) (fun w => rfl) (φK.trans φC) (fun w => rfl) basisK
    ((cT t ⊓ mV V : Subgroup G) : Set G) hKX (hfsΩ j) (hβK j)
  obtain ⟨himG, hmapG, -, hinjG⟩ :=
    CFSG.Wreathed.defect_normalizer_brauer_correspondence basis ideal 2 V hV2 basisM
  obtain ⟨B, hB⟩ := himG A
  have hBdef : coefficientBlockDefect basis ideal 2 B V := hmapG A B hAdef hB
  obtain ⟨himC, hmapC, hsurjC, hinjC⟩ := CFSG.Wreathed.defect_normalizer_brauer_correspondence
    basisC ideal 2 (vInC V t) (isPGroup_vInC hV) basisK
  choose b hb using fun j => himC (Aj j)
  have hbdef : ∀ j, coefficientBlockDefect basisC ideal 2 (b j) (vInC V t) := fun j =>
    hmapC (Aj j) (b j) (hAjdef j) (hb j)
  set BrGD := brauerNormalizerCharacterResidueHom ideal 2 V hV2 (dV V) le_rfl
    (Subgroup.centralizer_le_normalizer _) basisD with hBrGD
  set BrGC := brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t)
    (isPGroup_zpowers hV htV) (cT t) le_rfl (Subgroup.centralizer_le_normalizer _) basisC
    with hBrGC
  have hT1 : ∀ (γ : basisMD.index) (γD : basisD.index) (A' : basisM.index),
      LabelTransport basisMD basisD φM γ γD →
      BrMD γ = centralCharacterResidueHom basisM ideal A' → BrGM A' = BrGD γD :=
    fun γ γD A' hγ hc => KleinFourFiber.brauer_composite ideal 2 V V (mV V) hV2 hV2 le_rfl
      (Subgroup.centralizer_le_normalizer _) le_rfl le_mV dV_le_mV basisM basisMD basisD hγ hc
  have hT2 : ∀ (γ : basisCD.index) (γD : basisD.index) (c : basisC.index),
      LabelTransport basisCD basisD φC γ γD →
      BrCD γ = centralCharacterResidueHom basisC ideal c → BrGC c = BrGD γD :=
    fun γ γD c hγ hc => KleinFourFiber.brauer_composite ideal 2 (Subgroup.zpowers t) V (cT t)
      (isPGroup_zpowers hV htV) hV2 (Subgroup.zpowers_le.mpr htV) le_rfl
      (Subgroup.centralizer_le_normalizer _) hVC hDC basisC basisCD basisD hγ hc
  have hT3 : ∀ (γ : basisKD.index) (γC : basisCD.index) (a : basisK.index),
      LabelTransport basisKD basisCD φK γ γC →
      BrKD γ = centralCharacterResidueHom basisK ideal a → BrCK a = BrCD γC :=
    fun γ γC a hγ hc => KleinFourFiber.brauer_composite ideal 2 (vInC V t) (vInC V t) (kInC V t)
      (isPGroup_vInC hV) (isPGroup_vInC hV) le_rfl (Subgroup.centralizer_le_normalizer _) le_rfl
      vInC_le_kInC (Subgroup.centralizer_le_normalizer _) basisK basisKD basisCD hγ hc
  have hAffM : ∀ {f : G → ℂ} {γ : basisMD.index} {γD : basisD.index},
      LabelTransport basisMD basisD φM γ γD →
      (AffordsFun basisMD (fun x => ((x : mV V) : G)) f γ ↔
        AffordsFun basisD (fun x => (x : G)) f γD) := fun h =>
    affordsFun_iff_of_labelTransport basisMD basisD φM (fun x => ((x : mV V) : G))
      (fun x => (x : G)) (fun _ => rfl) _ h
  have hAffC : ∀ {f : G → ℂ} {γ : basisCD.index} {γD : basisD.index},
      LabelTransport basisCD basisD φC γ γD →
      (AffordsFun basisCD (fun x => ((x : cT t) : G)) f γ ↔
        AffordsFun basisD (fun x => (x : G)) f γD) := fun h =>
    affordsFun_iff_of_labelTransport basisCD basisD φC (fun x => ((x : cT t) : G))
      (fun x => (x : G)) (fun _ => rfl) _ h
  have hAffK : ∀ {f : G → ℂ} {γ : basisKD.index} {γC : basisCD.index},
      LabelTransport basisKD basisCD φK γ γC →
      (AffordsFun basisKD (fun x => (((x : kInC V t) : cT t) : G)) f γ ↔
        AffordsFun basisCD (fun x => ((x : cT t) : G)) f γC) := fun h =>
    affordsFun_iff_of_labelTransport basisKD basisCD φK
      (fun x => (((x : kInC V t) : cT t) : G)) (fun x => ((x : cT t) : G)) (fun _ => rfl) _ h
  have hbackK : ∀ γC : basisCD.index, ∃ γK : basisKD.index,
      LabelTransport basisKD basisCD φK γK γC := fun γC => by
    obtain ⟨γK, h⟩ := labelTransport_exists basisCD basisKD φK.symm γC
    exact ⟨γK, labelTransport_symm h⟩
  have hbackC : ∀ γD : basisD.index, ∃ γC : basisCD.index,
      LabelTransport basisCD basisD φC γC γD := fun γD => by
    obtain ⟨γC, h⟩ := labelTransport_exists basisD basisCD φC.symm γD
    exact ⟨γC, labelTransport_symm h⟩
  have hbackM : ∀ γD : basisD.index, ∃ γM : basisMD.index,
      LabelTransport basisMD basisD φM γM γD := fun γD => by
    obtain ⟨γM, h⟩ := labelTransport_exists basisD basisMD φM.symm γD
    exact ⟨γM, labelTransport_symm h⟩
  have hH1 : ∀ j, ∀ f ∈ kOrbit V t (fs j), ∀ γC : basisCD.index,
      AffordsFun basisCD (fun x => ((x : cT t) : G)) f γC →
        BrCD γC = centralCharacterResidueHom basisC ideal (b j) := by
    intro j f hf γC hγC
    obtain ⟨γK, hγK⟩ := hbackK γC
    have hBrK : BrKD γK = centralCharacterResidueHom basisK ideal (Aj j) :=
      (hAjiff j γK).mpr ⟨f, hf, γK, (hAffK hγK).mpr hγC, sameCoefficientBlock_refl _ _ _⟩
    rw [← hT3 γK γC (Aj j) hγK hBrK]
    exact hb j
  have hH2 : ∀ j, BrGC (b j) = centralCharacterResidueHom basis ideal B := by
    intro j
    obtain ⟨γC, hγC⟩ := exists_affords basisD hn₀ basisCD (fun x => ((x : cT t) : G)) φC
      (fun w => rfl) (hfsΩ j)
    obtain ⟨γD, hγD⟩ := labelTransport_exists basisCD basisD φC γC
    obtain ⟨γM, hγM⟩ := hbackM γD
    have hγMaff : AffordsFun basisMD (fun x => ((x : mV V) : G)) (fs j) γM :=
      (hAffM hγM).mpr ((hAffC hγD).mp hγC)
    have hBrM : BrMD γM = centralCharacterResidueHom basisM ideal A :=
      (hAiff γM).mpr ⟨fs j, hfsΩ j, γM, hγMaff, sameCoefficientBlock_refl _ _ _⟩
    rw [hT2 γC γD (b j) hγD (hH1 j (fs j) (hself _) γC hγC), ← hT1 γM γD A hγM hBrM]
    exact hB
  have hsameRes : ∀ {X : Type} [Group X] [Fintype X] (bX : FiniteIrreducibleCharacterBasis X)
      (x y : bX.index), sameCoefficientBlock bX R x y →
        centralCharacterResidueHom bX ideal x = centralCharacterResidueHom bX ideal y :=
    fun bX x y h => (sameCoefficientBlock_iff_centralCharacterResidueHom_eq bX ideal x y).mp h
  have hH4 : ∀ j (β : basisCD.index),
      BrCD β = centralCharacterResidueHom basisC ideal (b j) ↔
        ∃ n, (∃ f ∈ kOrbit V t (fs j),
          AffordsFun basisCD (fun x => ((x : cT t) : G)) f n) ∧
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
      obtain ⟨f, hf, n', hn', hsame'⟩ := (hAjiff j βK).mp hβK'
      obtain ⟨n'C, hn'C⟩ := labelTransport_exists basisKD basisCD φK n'
      exact ⟨n'C, ⟨f, hf, (hAffK hn'C).mp hn'⟩,
        (sameCoefficientBlock_labelTransport_iff basisKD basisCD ideal φK hn'C hβK).mp hsame'⟩
    · rintro ⟨n, ⟨f, hf, hn⟩, hsame⟩
      have heq : BrCD n = BrCD β := KleinFourFiber.brauer_eq_of_same ideal 2 (vInC V t)
        (isPGroup_vInC hV) (dInC V t) le_rfl (Subgroup.centralizer_le_normalizer _) basisCD hsame
      rw [← heq]
      exact hH1 j f hf n hn
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
    have hle4 : Nat.card F' ≤ 4 :=
      hcardV ▸ CFSG.TwoRankLowerBound.Helpers.subgroupSubconjugate_card_le hsub
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
      obtain ⟨-, hmapT, -, -⟩ := centralizer_normalizer_controlled_defect_correspondence basis
        ideal 2 (Subgroup.zpowers t) (isPGroup_zpowers hV htV) (Subgroup.zpowers t)
        (isPGroup_zpowers hV htV) le_rfl (zpowers_le_cT hV htV)
        (KleinFourFiber.normalizer_zpowers_le ht1 (mul_self hV htV)) basisC
      have hBt := hmapT c B hcZ hc
      obtain ⟨g, hg⟩ := coefficientBlockDefect_conjugate basis ideal hBdef hBt
      have hcg := conjugation_subgroup_card V g
      rw [hg, hcardZ, hcardV] at hcg
      norm_num at hcg
    ·
      have hF'4 : Nat.card F' = 4 := by rw [hk]; norm_num
      have hconjFV := subgroupsConjugate_of_subconjugate_card_ge hsub
        (by rw [hF'4, hcardV])
      obtain ⟨g, hg⟩ := hconjFV
      have hF'K : IsKleinFour F' :=
        { card_four := hF'4
          exponent_two := by
            rw [Monoid.exponent_eq_of_mulEquiv ((F'.equivMapOfInjective
              (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
                (MulEquiv.subgroupCongr hg))]
            exact hV.exponent_two }
      obtain ⟨c', hc'C, hc'⟩ := hfour F' hF'K (hPF' (Subgroup.mem_zpowers t)) hF'C ⟨g, hg⟩
      have hconjC : subgroupsConjugate F (vInC V t) := by
        refine ⟨⟨c', hc'C⟩, ?_⟩
        apply Subgroup.map_injective (cT t).subtype_injective
        rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hVC, ← hc', hF'def,
          Subgroup.map_map]
        rfl
      have hcdef := FourGroupParity.coefficientBlockDefect_of_subgroupsConjugate basisC ideal hF
        hconjC
      obtain ⟨a, -, hac⟩ := hsurjC c hcdef
      obtain ⟨-, hsurjK, -⟩ := normal_p_centralizer_brauer_fibers_are_block_orbits basisK ideal 2
        (vInK V t) (isPGroup_vInK hV) basisKD
      obtain ⟨βK, hβK⟩ := hsurjK a
      obtain ⟨βC, hβC⟩ := labelTransport_exists basisKD basisCD φK βK
      have hβCc : BrCD βC = centralCharacterResidueHom basisC ideal c :=
        (hT3 βK βC a hβC hβK).symm.trans hac
      obtain ⟨βD, hβD⟩ := labelTransport_exists basisCD basisD φC βC
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
      obtain ⟨f, hfΩ, n', hn', hsame'⟩ := (hAiff βM).mp hβMA
      have hfU : f ∈ ⋃ j, kOrbit V t (fs j) := by
        rw [← hΩunion]
        exact hfΩ
      obtain ⟨j, hfj⟩ := Set.mem_iUnion.mp hfU
      obtain ⟨n'D, hn'D⟩ := labelTransport_exists basisMD basisD φM n'
      obtain ⟨n'C, hn'C⟩ := hbackC n'D
      obtain ⟨n'K, hn'K⟩ := hbackK n'C
      have hsameD := (sameCoefficientBlock_labelTransport_iff basisMD basisD ideal φM hn'D
        hβM).mp hsame'
      have hsameC := (sameCoefficientBlock_labelTransport_iff basisCD basisD ideal φC hn'C
        hβD).mpr hsameD
      have hsameK := (sameCoefficientBlock_labelTransport_iff basisKD basisCD ideal φK hn'K
        hβC).mpr hsameC
      have hn'Kaff := (hAffK hn'K).mpr ((hAffC hn'C).mpr ((hAffM hn'D).mp hn'))
      have hβKj : BrKD βK = centralCharacterResidueHom basisK ideal (Aj j) :=
        (hAjiff j βK).mpr ⟨f, hfj, n'K, hn'Kaff, hsameK⟩
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
    have hk : BrKD (βK k) = centralCharacterResidueHom basisK ideal (Aj k) :=
      (hAjiff k (βK k)).mpr ⟨fs k, hself _, βK k, hβK k, sameCoefficientBlock_refl _ _ _⟩
    have hj : BrKD (βK k) = centralCharacterResidueHom basisK ideal (Aj j) :=
      hk.trans (hsameRes basisK (Aj j) (Aj k) hsameA).symm
    obtain ⟨f, hf, n', hn', hsame'⟩ := (hAjiff j (βK k)).mp hj
    have hfk : f = fs k := block_unique hdata basisD ideal hn₀ hblock₀ basisKD
      (fun x => (((x : kInC V t) : cT t) : G)) (φK.trans φC) (fun w => rfl)
      (kOrbit_subset_fOrbit (hfsΩ j) t hf) (hfsΩ k) hn' (hβK k) hsame'
    exact Set.disjoint_left.mp (hΩjdisj j k hjk) hf (hfk ▸ hself _)
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
          (Finset.univ.filter fun n => ∃ f ∈ kOrbit V t (fs j),
            AffordsFun basisCs (fun x => ((x : cT t) : G)) f n).image
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
        LabelTransport basisCs basisCD e n n' →
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
      rw [← hproj z, centralCharacterResidueHom_labelTransport basisCs basisCD ideal e hnn']
    refine ⟨fun n n' hcompat => hBr n n' fun x => (hcompat x (e x) rfl).symm, fun j => ?_⟩
    have hLW : ∀ θ : basisCs.index,
        brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers s) hs
            (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t)))
            le_rfl (Subgroup.centralizer_le_normalizer _) basisCs θ =
          centralCharacterResidueHom basisC ideal (b j) ↔
        ∃ n, (∃ f ∈ kOrbit V t (fs j),
          AffordsFun basisCs (fun x => ((x : cT t) : G)) f n) ∧
          sameCoefficientBlock basisCs R n θ := by
      intro θ
      obtain ⟨θ', hθ'⟩ := labelTransport_exists basisCs basisCD e θ
      rw [hBr θ θ' hθ', hH4 j θ']
      constructor
      · rintro ⟨n', ⟨f, hf, hn'⟩, hsame⟩
        obtain ⟨n, hn⟩ := labelTransport_exists basisCD basisCs e.symm n'
        have hn2 := labelTransport_symm hn
        exact ⟨n, ⟨f, hf, (affordsFun_iff_of_labelTransport basisCs basisCD e
            (fun x => ((x : cT t) : G)) (fun x => ((x : cT t) : G)) (fun _ => rfl) f hn2).mpr
            hn'⟩,
          (sameCoefficientBlock_labelTransport_iff basisCs basisCD ideal e hn2 hθ').mpr hsame⟩
      · rintro ⟨n, ⟨f, hf, hn⟩, hsame⟩
        obtain ⟨n', hn'⟩ := labelTransport_exists basisCs basisCD e n
        exact ⟨n', ⟨f, hf, (affordsFun_iff_of_labelTransport basisCs basisCD e
            (fun x => ((x : cT t) : G)) (fun x => ((x : cT t) : G)) (fun _ => rfl) f hn').mp
            hn⟩,
          (sameCoefficientBlock_labelTransport_iff basisCs basisCD ideal e hn' hθ').mp hsame⟩
    exact image_coefficientBlock_eq_of_iff basisCs R _ _ hLW
  exact ⟨A, Aj, B, b, fun f hf n hn => (hAiff n).mpr ⟨f, hf, n, hn, sameCoefficientBlock_refl _ _ _⟩,
    fun j f hf n hn => (hAjiff j n).mpr ⟨f, hf, n, hn, sameCoefficientBlock_refl _ _ _⟩,
    hB, hb, hAdef, hAjdef, hBdef, hbdef, hdist, hfib,
    fun j => image_coefficientBlock_eq_of_iff basisCD R _ _ (hH4 j), hslevel⟩

end CFSG.KleinFourBlocks
