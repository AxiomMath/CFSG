module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A7

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag
  CFSG.RankThree.Classical2 CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.ClassicalInvolution.Upgrade CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private theorem trivialMultiplierT_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : TrivialMultiplierT Y) : TrivialMultiplierT X := by
  intro E _ _ hperf π hsurj hker
  have hcomp : Function.Surjective (e.toMonoidHom.comp π) := e.surjective.comp hsurj
  have hker' : (e.toMonoidHom.comp π).ker ≤ Subgroup.center E := by
    rwa [MonoidHom.ker_comp_of_injective π e.toMonoidHom e.injective]
  have h1 := h E hperf (e.toMonoidHom.comp π) hcomp hker'
  rwa [MonoidHom.ker_comp_of_injective π e.toMonoidHom e.injective] at h1

section Comp


variable {f : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [IsAlgClosed Ω] [CharP Ω 2]
  {Fr : Ω →+* Ω}

theorem twE6_isComponentOf_and_glaLayer_eq_centralizer (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hFr : ∀ c, Fr c = c ^ (2 ^ f)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdvd : q ∣ 2 ^ f + 1) {ζ : Ωˣ}
    (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1)
    (i : KernelComponent (rootCharHom (twE6omega1Tuple ζ)))
    (x : ↥⁅thetaFixed Fr, thetaFixed Fr⁆)
    (hxval : (x : ModGL Tag.E6 Ω) = rootDiagUnit Tag.E6 (twE6omega1Tuple ζ))
    (hx1 : x ≠ 1) :
    CFSG.Open.IsComponentOf
        ((twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i).subgroupOf
          ⁅thetaFixed Fr, thetaFixed Fr⁆)
        (Subgroup.centralizer ({x})) ∧
      CFSG.Open.GLALayer (Subgroup.centralizer ({x})) =
        (twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i).subgroupOf
          ⁅thetaFixed Fr, thetaFixed Fr⁆ := by
  classical
  let C : Subgroup (ModGL Tag.E6 Ω) := ⁅thetaFixed Fr, thetaFixed Fr⁆
  let S : LangSetup Tag.E6 Ω q := twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd
  let J : Subgroup ↥C := (twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i).subgroupOf C
  let d : ModGL Tag.E6 Ω := rootDiagUnit Tag.E6 (twE6omega1Tuple ζ)
  let H : Subgroup (ModGL Tag.E6 Ω) := S.Γ ⊓ Subgroup.centralizer {d}
  have hT : d ∈ S.D.torus := by
    change rootDiagUnit Tag.E6 (twE6omega1Tuple ζ) ∈
      (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd).D.torus
    rw [twE6EnnolaSetup_D]
    rw [twE6EnnolaDatum_torus (ℓ := 2) Nat.prime_two (by omega) hK hFr]
    intro j
    obtain ⟨m, hm⟩ := hqdvd
    simp only [twE6omega1Tuple]
    split_ifs with hj
    · rw [hm, pow_mul, hζq, one_pow]
    · simp
  have hap : ∀ j, twE6omega1Tuple ζ j ^ q = 1 := by
    intro j
    simp only [twE6omega1Tuple]
    split_ifs with hj
    · exact hζq
    · exact one_pow q
  have hd1 : d ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext (hxval.trans h))
  have hTame : ∀ j : KernelComponent (rootCharHom (twE6omega1Tuple ζ)),
      CFSG.IsQuasisimple
          (rationalComponent S.ρ S.Γ (rootCharHom (twE6omega1Tuple ζ)) j) ∨
        Group.IsSolvable
          (rationalComponent S.ρ S.Γ (rootCharHom (twE6omega1Tuple ζ)) j) := by
    intro j
    left
    exact twE6_isQuasisimple_omega1 hf hK hσ hFr hq hq2 hqdvd hζq hζ1 j
  have hker : kernelRoots (rootCharHom (twE6omega1Tuple ζ)) = twE6D5 :=
    kernelRoots_omega1 hq hζq hζ1
  haveI hsub : Subsingleton (KernelComponent (rootCharHom (twE6omega1Tuple ζ))) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨α, rfl⟩ := Quotient.exists_rep a
    obtain ⟨β, rfl⟩ := Quotient.exists_rep b
    exact twE6D5_mk_eq hker
  haveI : Finite ↥C := S.finite_Γ
  have hrange : C.subtype.range = S.Γ := by
    rw [Subgroup.range_subtype]
    exact (twE6EnnolaSetup_Gamma (Fr := Fr) hf hK hσ hFr hq hqdvd).symm
  have hβ : ∀ c : ↥C, C.subtype ((MulAut.conj x) c) = d * C.subtype c * d⁻¹ := by
    intro c
    show (x : ModGL Tag.E6 Ω) * (c : ModGL Tag.E6 Ω) * (x : ModGL Tag.E6 Ω)⁻¹ =
      d * (c : ModGL Tag.E6 Ω) * d⁻¹
    rw [hxval]
  have hcd : H ≤ C.subtype.range := by
    rw [hrange]
    exact inf_le_left
  have hcompR : CFSG.Open.IsComponentOf (twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i) H := by
    obtain ⟨hle, hsubn⟩ := langSubnormal_of_mem_torus S hT i
    refine ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsubn, ?_⟩
    exact ⟨(twE6_isQuasisimple_omega1 hf hK hσ hFr hq hq2 hqdvd hζq hζ1 i).1.commutator_eq_top,
      (twE6_isQuasisimple_omega1 hf hK hσ hFr hq hq2 hqdvd hζq hζ1 i).2.1⟩
  have hfixmap : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)).map C.subtype = H := by
    rw [map_fixSubgroup_eq_of_conj C.subtype C.subtype_injective (MulAut.conj x) d hβ, hrange]
  have hcomapfix : H.comap C.subtype = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) := by
    rw [← hfixmap]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hcompJ : CFSG.Open.IsComponentOf
      ((twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i).comap C.subtype)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) := by
    have h := isComponentOf_comap_of_injective C.subtype C.subtype_injective
      (hcompR.1.trans hcd) hcd hcompR
    rwa [hcomapfix] at h
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x}) := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : x * y * x⁻¹ = y := h
      calc y * x = (x * y * x⁻¹) * x := by rw [h']
        _ = x * y := by group
    · intro h
      show x * y * x⁻¹ = y
      calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [h]
        _ = y := by group
  have hcomp : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({x})) := by
    have h := hcompJ
    rw [hfix] at h
    exact h
  refine ⟨hcomp, ?_⟩
  rw [← hfix]
  refine le_antisymm ?_ (CFSG.LocalAnalysis.GLTheoremA.I142N.le_GLALayer hcompJ)
  refine CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le_of fun P hP => ?_
  obtain ⟨j, -, hPj⟩ := components_of_langSetup S hq C.subtype C.subtype_injective hrange
    (MulAut.conj x) hβ hT hap hd1 hTame hP
  have hji : j = i := Subsingleton.elim j i
  rw [hji] at hPj
  intro p hp
  have hpm : (p : ModGL Tag.E6 Ω) ∈ twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i := by
    have h1' := Subgroup.mem_map_of_mem C.subtype hp
    rw [hPj] at h1'
    exact h1'
  exact hpm

end Comp

section Package


variable {f : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [IsAlgClosed Ω] [CharP Ω 2]
  {Fr : Ω →+* Ω}

theorem twE6_exists_x_J (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hFr : ∀ c, Fr c = c ^ (2 ^ f)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdvd : q ∣ 2 ^ f + 1) (hq3 : q ≠ 3 ∨ 9 ∣ 2 ^ f + 1) {ζ : Ωˣ}
    (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1)
    (i : KernelComponent (rootCharHom (twE6omega1Tuple ζ))) :
    ∃ (x : ↥⁅thetaFixed Fr, thetaFixed Fr⁆)
      (J : Subgroup ↥⁅thetaFixed Fr, thetaFixed Fr⁆),
      x ^ q = 1 ∧ x ≠ 1 ∧ J ≤ Subgroup.centralizer ({x}) ∧
        CFSG.IsQuasisimple ↥J ∧
        (CFSG.Open.IsComponentOf J (Subgroup.centralizer ({x})) ∧
          CFSG.Open.GLALayer (Subgroup.centralizer ({x})) = J) ∧
        HasLabel ↥J (· = ⟨.twD, 5, f⟩) ∧
        Subgroup.center ↥J = ⊥ ∧ TrivialMultiplierT ↥J := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup (ModGL Tag.E6 Ω) := ⁅thetaFixed Fr, thetaFixed Fr⁆
  let x : ↥C :=
    twE6xStar (ℓ := 2) (σ := σ.toRingHom) Nat.prime_two (by omega) hK (fun c => hσ c) hFr
      hq hq2 hqdvd hq3 hζq hζ1
  let J : Subgroup ↥C := (twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i).subgroupOf C
  have hxval : (x : ModGL Tag.E6 Ω) = rootDiagUnit Tag.E6 (twE6omega1Tuple ζ) := rfl
  have hxq : x ^ q = 1 :=
    twE6xStar_pow_eq_one (ℓ := 2) Nat.prime_two (by omega) hK (fun c => hσ c) hFr hq hq2
      hqdvd hq3 hζq hζ1
  have hx1 : x ≠ 1 := by
    intro h
    exact twE6xStar_ne_one (ℓ := 2) Nat.prime_two (by omega) hK (fun c => hσ c) hFr hq
      hq2 hqdvd hq3 hζq hζ1 (Subtype.ext (congrArg Subtype.val h))
  have hcomp := twE6_isComponentOf_and_glaLayer_eq_centralizer hf hK hσ hFr hq hq2 hqdvd
    hζq hζ1 i x hxval hx1
  have hJle : twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i ≤ C :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.rationalComponent_le_Γ
      (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd) i
  have hJq : CFSG.IsQuasisimple ↥J :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJle)
      (twE6_isQuasisimple_omega1 hf hK hσ hFr hq hq2 hqdvd hζq hζ1 i)
  have hlab : HasLabel ↥J (· = ⟨.twD, 5, f⟩) :=
    (hasLabel_subgroupOf_iff hJle (· = ⟨.twD, 5, f⟩)).1
      (twE6_hasLabel_omega1 hf hK hσ hFr hq hq2 hqdvd hζq hζ1 i)
  have hZJ : Subgroup.center ↥J = ⊥ := by
    let e := Subgroup.subgroupOfEquivOfLe hJle
    have hZj : Subgroup.center ↥(twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i) = ⊥ :=
      (twE6_center_eq_bot_and_trivialMultiplierT hf hK hσ hFr hq hq2 hqdvd hζq hζ1 i).1
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center ↥(twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro w
      obtain ⟨y, rfl⟩ := e.surjective w
      calc e y * e z = e (y * z) := (map_mul e y z).symm
        _ = e (z * y) := by rw [hz y]
        _ = e z * e y := map_mul e z y
    rw [hZj, Subgroup.mem_bot] at hz'
    exact e.injective (by simpa using hz')
  have hmult : TrivialMultiplierT ↥J :=
    trivialMultiplierT_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJle)
      (twE6_center_eq_bot_and_trivialMultiplierT hf hK hσ hFr hq hq2 hqdvd hζq hζ1 i).2
  exact ⟨x, J, hxq, hx1, hcomp.1.1, hJq, hcomp, hlab, hZJ, hmult⟩

end Package

end CFSG.LocalAnalysis.GLTheoremA.Y10F
