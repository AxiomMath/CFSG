module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE6ThreeToral
public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagGlue
public import CFSG.RankThree.PartTwo.Sec13.Ronan138WOutAbPSL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic)

section InnDiag


theorem innAutDerived_adjointE6_le_e6Inndiag (K : Type) [Field K] [Finite K] :
    innAutDerived (adjointGroup Tag.E6 K) ≤ e6Inndiag K := by
  obtain ⟨Φ, -, hker, -⟩ := exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
  let Θ : MulAut (adjointGroup Tag.E6 K) →* RingAut K × Multiplicative (ZMod (exactE Tag.E6)) :=
    Φ.comp (QuotientGroup.mk' (inner (adjointGroup Tag.E6 K)))
  have hcomm : ∀ x y : RingAut K × Multiplicative (ZMod (exactE Tag.E6)), x * y = y * x :=
    fun x y => Prod.ext (CFSG.RankThree.PartTwo.Sec13.Ronan138W.ringAut_comm_of_finite _ _)
      (mul_comm _ _)
  have h1 : inner (adjointGroup Tag.E6 K) ≤ Θ.ker := by
    rintro _ ⟨g, rfl⟩
    rw [MonoidHom.mem_ker]
    change Φ (QuotientGroup.mk (MulAut.conj g)) = 1
    rw [(QuotientGroup.eq_one_iff (N := inner (adjointGroup Tag.E6 K)) (MulAut.conj g)).2
      ⟨g, rfl⟩, map_one]
  have h2 : commutator (MulAut (adjointGroup Tag.E6 K)) ≤ Θ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  refine (sup_le h1 h2).trans fun α hα => ?_
  have hα' : QuotientGroup.mk' (inner (adjointGroup Tag.E6 K)) α ∈ Φ.ker := hα
  rw [hker] at hα'
  obtain ⟨a, ha⟩ := hα'
  have hmem : (rootDiagAutHom Tag.E6 K a)⁻¹ * α ∈ inner (adjointGroup Tag.E6 K) := by
    rw [← QuotientGroup.eq]
    exact ha
  have hα2 : α = rootDiagAutHom Tag.E6 K a * ((rootDiagAutHom Tag.E6 K a)⁻¹ * α) := by group
  rw [hα2, e6Inndiag, sup_comm]
  exact Subgroup.mul_mem_sup ⟨a, rfl⟩ hmem

end InnDiag

section Plane


theorem e6Three_exists_good_of_plane {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hEab : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) (hd : E ≤ e6Inndiag K) :
    ∃ β ∈ E, β ≠ 1 ∧ ∃ P : Subgroup (adjointGroup Tag.E6 K), (∀ y ∈ P, β y = y) ∧
      ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  classical
  obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
  have hinj := e6InndiagConj_injective K hK4
  have hfix : ∀ (g : ↥(e6InndiagGL K)) (P : Subgroup (adjointGroup Tag.E6 K)),
      (∀ y ∈ P, (g : ModGL Tag.E6 K) * (y : ModGL Tag.E6 K) * (g : ModGL Tag.E6 K)⁻¹ = y) →
      ∀ y ∈ P, e6InndiagConj K g y = y := fun g P h y hy =>
    Subtype.ext (by rw [e6InndiagConj_apply]; exact h y hy)
  by_cases hiso : E6DiagIsotropic K K₁ E
  ·
    have h3 : ¬ 3 ∣ Nat.card K := by
      intro h3
      have : Fintype K := Fintype.ofFinite K
      haveI := ringChar.charP K
      obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
      rw [Nat.card_eq_fintype_card, hcard] at h3
      exact hK3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    have hEr : E ≤ (e6InndiagConj K).range := by
      rw [range_e6InndiagConj]
      exact hd
    set E₀ : Subgroup ↥(e6InndiagGL K) := E.comap (e6InndiagConj K) with hE₀
    have hmap : E₀.map (e6InndiagConj K) = E := Subgroup.map_comap_eq_self hEr
    have hexp : ∀ x ∈ E₀, x ^ 3 = 1 := fun x hx =>
      hinj (by rw [map_pow, map_one]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hx)
    have hcard₀ : Nat.card E₀ = 3 ^ 2 := by
      rw [← Subgroup.card_map_of_injective hinj, hmap]
      exact hcard
    have hC₁ : ∀ x ∈ E₀, baseChangeGL (algebraMap K K₁) (x : ModGL Tag.E6 K) ∈
        adjointGroup Tag.E6 K₁ := fun x _ =>
      map_e6InndiagGL_le _ hroot (Subgroup.mem_map_of_mem _ x.2)
    obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hin⟩ := e6IsotropicToralInndiag_of_planeToralLang
      e6PlaneToralLang_proved K h3 K₁ E₀ hexp hcard₀ hC₁ (fun x y hx hy => hiso x y hx hy)
    set L := AlgebraicClosure K with hL
    let θ : ↥(e6InndiagGL K) →* ModGL Tag.E6 L :=
      (MulAut.conj g0⁻¹).toMonoidHom.comp
        ((baseChangeGL (algebraMap K L)).comp (e6InndiagGL K).subtype)
    have hθ : ∀ x, θ x = g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL Tag.E6 K) * g0 :=
      fun x => by simp [θ, MulAut.conj_apply]
    have hθinj : Function.Injective θ :=
      (MulAut.conj g0⁻¹).injective.comp
        ((baseChangeGL_injective _).comp Subtype.val_injective)
    have hθT : ∀ x ∈ E₀, θ x ∈ twistedTorusOf
        (canonicalRep (coxeterSystem Tag.E6) L w) (Units.map (entrywiseHom Fr)) := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hin x hx
      rw [hθ, ← hyx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g0⁻¹ * (g0 * y * g0⁻¹) * g0 = y by group]
      exact hy
    have hBcard : Nat.card (E₀.map θ) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective hθinj, hcard₀]
    have : Finite (E₀.map θ) := Nat.finite_of_card_ne_zero (by rw [hBcard]; norm_num)
    have hBT : E₀.map θ ≤ torusGroup Tag.E6 L := by
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_twistedTorusOf.1 (hθT x hx)).1
    have hBpow : ∀ z ∈ E₀.map θ, z ^ 3 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one]
    obtain ⟨a, haB, ha1, hχ⟩ := exists_rootChar_eq_one_of_finite Nat.prime_three hBT hBpow
      (by rw [hBcard]; norm_num) (Pi.single 0 1)
    obtain ⟨x, hx, hxa⟩ := haB
    have hga : g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL Tag.E6 K) * g0 =
        rootDiagUnit Tag.E6 a := (hθ x).symm.trans hxa
    have ha3 : ∀ i, a i ^ 3 = 1 := by
      have h1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 (1 : Fin Tag.E6.rank → Lˣ) := by
        rw [← rootDiagUnit_pow, ← hxa, ← map_pow, hexp x hx, map_one, rootDiagUnit_one]
      have h2 : a ^ 3 = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
      exact fun i => by simpa using congrFun h2 i
    obtain ⟨P, hP, hPperf, hPdvd⟩ := e6Three_exists_perfect_fixed_of_toral hK3 hK4 hFr hg0C hg0
      hga (hxa ▸ hθT x hx) ha3 ha1 (isRoot_single _ 0) hχ
    refine ⟨e6InndiagConj K x, Subgroup.mem_comap.1 hx, fun h => ha1 ?_, P, hfix x P hP,
      hPperf, hPdvd⟩
    have hx1 : x = 1 := hinj (h.trans (map_one _).symm)
    rw [← hxa, hx1, map_one]
  ·
    obtain ⟨F⟩ := exists_e6HeisenbergFrame hK3 hK4 K₁ hroot E hEab hcard hd hiso
    have ha1 : rootDiagUnit Tag.E6 F.a ≠ 1 := by
      intro h1
      apply F.hsh
      have : F.a = 1 :=
        CFSG.LieType.Chevalley.rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
      rw [this]
      simp [rootChar]
    obtain ⟨γ, hγ, hχ⟩ := e6Three_exists_root_rootChar_eq_one F.a F.ha3
    obtain ⟨P, hP, hPperf, hPdvd⟩ := e6Three_exists_perfect_fixed_of_toral hK3 hK4 F.hFr F.hg0C
      F.hg0 F.hg₁ F.hT F.ha3 ha1 hγ hχ
    refine ⟨e6InndiagConj K F.g₁, F.hE₁, fun h => ha1 ?_, P, hfix F.g₁ P hP, hPperf, hPdvd⟩
    have hx1 : F.g₁ = 1 := hinj (h.trans (map_one _).symm)
    rw [← F.hg₁, hx1]
    simp

end Plane

section InnGood


theorem innGoodAt_adjointE6_three {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) (d : TauCeti.LieTypeIndex) :
    InnGoodAt 3 d (adjointGroup Tag.E6 K) := by
  intro D hD hcard hle
  left
  obtain ⟨β, hβD, hβ1, P, hP, hPperf, hPdvd⟩ := e6Three_exists_good_of_plane hK3 hK4
    (CFSG.Open.IsElemAbelian.isElementaryAbelian hD) hcard
    (hle.trans (innAutDerived_adjointE6_le_e6Inndiag K))
  exact ⟨β, hβD, hβ1, P, fun y hy => hP y hy, hPperf, hPdvd⟩

end InnGood

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
