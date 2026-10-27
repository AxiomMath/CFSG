module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjBar
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCoreDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false

section Witness

variable {K : Type} [Field K]

theorem e6Line_finrank_fixed {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    Module.finrank K (LinearMap.ker
      (((rootDiagUnit .E6 (e6LineChar ω) : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1))
        = 24 :=
  e6Line_finrank_fixed_aux h3 h1

theorem e6ThreeA2Witness_holds : E6ThreeA2WitnessStmt :=
  fun _ _ _ _ h3 h1 => e6Line_finrank_fixed h3 h1

end Witness

section Conj


variable {K : Type} [Field K] [Finite K]

theorem exists_conj_e6Line_of_finrank {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {x : ModGL .E6 K} (hx : x ∈ adjointGroup .E6 K) (hx3 : x ^ 3 = 1)
    (hdim : Module.finrank K (LinearMap.ker ((x : Module.End K (RootModule .E6 K)) - 1)) = 24) :
    ∃ g ∈ adjointGroup .E6 K, g * x * g⁻¹ = rootDiagUnit .E6 (e6LineChar ω) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3q : 3 ∣ Nat.card K - 1 := three_dvd_natCard_sub_one hω3 hω1
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpn, hcard⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hpn⟩
  obtain ⟨p, hp⟩ : ∃ p, p = ringChar K := ⟨_, rfl⟩
  rw [← hp] at hpn hcard
  haveI : Fact p.Prime := ⟨hpn⟩
  haveI : CharP K p := hp ▸ ringChar.charP K
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = (n : ℕ) := ⟨_, rfl⟩
  have hK : Nat.card K = p ^ e := by rw [Nat.card_eq_fintype_card, hcard, he]
  have he1 : 1 ≤ e := by
    rw [he]
    exact n.pos
  have hp3 : p ≠ 3 := ne_three_of_cube_root hω3 hω1
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  obtain ⟨sL, hsL⟩ : ∃ g, g = baseChangeGL (algebraMap K (AlgebraicClosure K)) x := ⟨_, rfl⟩
  have hsLG : sL ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hsL]
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hx
  have hsL3 : sL ^ 3 = 1 := by rw [hsL, ← map_pow, hx3, map_one]
  have hdimL : Module.finrank (AlgebraicClosure K)
      (LinearMap.ker ((sL : Module.End (AlgebraicClosure K) (RootModule Tag.E6
        (AlgebraicClosure K))) - 1)) = 24 := by
    have h := finrank_ker_baseChangeEnd (L := AlgebraicClosure K)
      ((x : Module.End K (RootModule Tag.E6 K)) - 1)
    rw [baseChangeEnd_sub_aux, baseChangeEnd_one_aux] at h
    rw [hsL, coe_baseChangeGL, h, hdim]
  obtain ⟨y, hyG, hsyL⟩ := exists_conj_e6Line_bar hω3 hω1 hsLG hsL3 hdimL
  have hsy : baseChangeGL (algebraMap K (AlgebraicClosure K)) x =
      y * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (rootDiagUnit Tag.E6 (e6LineChar ω)) * y⁻¹ := by
    rw [← hsL]
    exact hsyL
  have hcM := lang_cocycle_mem_toralRootGroup_threeA2 hp3 hK hω3 hω1 hx hyG hsy
  obtain ⟨F, hF⟩ : ∃ F : ModGL Tag.E6 (AlgebraicClosure K) →* ModGL Tag.E6 (AlgebraicClosure K),
      F = entrywiseFrobGL Tag.E6 (AlgebraicClosure K) p e := ⟨_, rfl⟩
  have hFr : ∀ c : AlgebraicClosure K, iterateFrobenius (AlgebraicClosure K) p e c =
      c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hK]
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      a₀ = fun i => Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom
        (e6LineChar ω i) := ⟨_, rfl⟩
  rw [← ha₀] at hcM
  have ha₀3 : ∀ i, a₀ i ^ 3 = 1 := fun i => by
    rw [ha₀, ← map_pow, e6LineChar_pow_three hω3, map_one]
  have hd : baseChangeGL (algebraMap K (AlgebraicClosure K))
      (rootDiagUnit Tag.E6 (e6LineChar ω)) = rootDiagUnit Tag.E6 a₀ := by
    rw [baseChangeGL_rootDiagUnit, ha₀]
  have hstab : ∀ g ∈ toralRootGroup Tag.E6 (AlgebraicClosure K) a₀,
      entrywiseFrobGL Tag.E6 (AlgebraicClosure K) p e g ∈
        toralRootGroup Tag.E6 (AlgebraicClosure K) a₀ := by
    intro g hg
    have h1 := baseChangeGL_mem_toralRootGroup (iterateFrobenius (AlgebraicClosure K) p e) hg
    have h2 : (fun i => Units.map (iterateFrobenius (AlgebraicClosure K) p e).toMonoidHom
        (a₀ i)) = a₀ := by
      funext i
      apply Units.ext
      change iterateFrobenius (AlgebraicClosure K) p e ((a₀ i : (AlgebraicClosure K)ˣ) :
        AlgebraicClosure K) = _
      rw [hFr]
      have h := congrArg Units.val (ha₀3 i)
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h
      exact e6Conj_pow_eq_self_of_pow_three h h3q Nat.card_pos
    rw [h2] at h1
    rw [show entrywiseFrobGL Tag.E6 (AlgebraicClosure K) p e g =
      baseChangeGL (iterateFrobenius (AlgebraicClosure K) p e) g from
        units_map_entrywiseHom_eq_baseChangeGL _ g]
    exact h1
  obtain ⟨z, hz, hzc⟩ := toralRootGroup_lang p a₀ e he1 hstab _ hcM
  rw [← hF] at hzc
  obtain ⟨u, hu⟩ : ∃ u, u = y * z⁻¹ := ⟨_, rfl⟩
  have hFu : F u = u := by
    have hFz : F z = z * (y⁻¹ * F y) := by rw [← hzc]; group
    rw [hu, map_mul, map_inv, hFz]
    group
  have hzt : z * rootDiagUnit Tag.E6 a₀ = rootDiagUnit Tag.E6 a₀ * z := by
    have h3 := (mem_toralCentralizer.1 (toralRootGroup_le a₀ hz)).2
    calc z * rootDiagUnit Tag.E6 a₀
        = (rootDiagUnit Tag.E6 a₀ * z * (rootDiagUnit Tag.E6 a₀)⁻¹) * rootDiagUnit Tag.E6 a₀ := by
          rw [h3]
      _ = rootDiagUnit Tag.E6 a₀ * z := by group
  have hut : u * rootDiagUnit Tag.E6 a₀ * u⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) x := by
    rw [hsy, hd, hu]
    calc y * z⁻¹ * rootDiagUnit Tag.E6 a₀ * (y * z⁻¹)⁻¹
        = y * (z⁻¹ * (rootDiagUnit Tag.E6 a₀ * z)) * y⁻¹ := by group
      _ = y * (z⁻¹ * (z * rootDiagUnit Tag.E6 a₀)) * y⁻¹ := by rw [hzt]
      _ = y * rootDiagUnit Tag.E6 a₀ * y⁻¹ := by group
  have huG : u ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hu]
    exact mul_mem hyG (inv_mem ((toralRootGroup_le a₀ hz).1))
  have hFu' : Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) p e)) u = u := by
    have h := hFu
    rw [hF] at h
    exact h
  obtain ⟨b, j, hjC, hbj⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed
    (iterateFrobenius (AlgebraicClosure K) p e) hFr
    (bijective_iterateFrobenius (AlgebraicClosure K) p e) huG hFu'
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ = rootDiagUnit Tag.E6 b * j := ⟨_, rfl⟩
  rw [← hg₀] at hbj
  have hxg : x = g₀ * rootDiagUnit Tag.E6 (e6LineChar ω) * g₀⁻¹ := by
    apply baseChangeGL_injective (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
    rw [map_mul, map_mul, map_inv, ← hbj, hd, hut]
  have hdx : rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 (e6LineChar ω) =
      rootDiagUnit Tag.E6 (e6LineChar ω) * rootDiagUnit Tag.E6 b := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hc0 : (rootDiagUnit Tag.E6 b * j * (rootDiagUnit Tag.E6 b)⁻¹)⁻¹ ∈
      adjointGroup Tag.E6 K := inv_mem (conj_rootDiagUnit_mem_adjointGroup b hjC)
  refine ⟨_, hc0, ?_⟩
  rw [hxg, hg₀]
  calc (rootDiagUnit Tag.E6 b * j * (rootDiagUnit Tag.E6 b)⁻¹)⁻¹ *
        (rootDiagUnit Tag.E6 b * j * rootDiagUnit Tag.E6 (e6LineChar ω) *
          (rootDiagUnit Tag.E6 b * j)⁻¹) *
        (rootDiagUnit Tag.E6 b * j * (rootDiagUnit Tag.E6 b)⁻¹)⁻¹⁻¹ =
      rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 (e6LineChar ω) *
        (rootDiagUnit Tag.E6 b)⁻¹ := by group
    _ = rootDiagUnit Tag.E6 (e6LineChar ω) := by rw [hdx]; group

theorem e6ThreeA2Conj_holds : E6ThreeA2ConjStmt :=
  fun _ _ _ _ h3 h1 _ hx hx3 hdim => exists_conj_e6Line_of_finrank h3 h1 hx hx3 hdim

end Conj

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
