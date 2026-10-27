module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureBlockDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportCharts
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open CFSG.RankThree.OrthogonalInvolutions
open Module QuadraticMap
open scoped commutatorElement

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

section TwoDimensional

variable {k V : Type} [Field k] [Finite k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [CharP k 2] {Q : QuadraticForm k V}

theorem omegaGroup_le_orthDerived_of_finrank_two
    (hQ : (polarBilin Q).Nondegenerate) (h2 : finrank k V = 2) :
    omegaGroup Q hQ ≤ orthDerived Q := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have : Finite V := Module.finite_of_finite k
  have : Finite (V ≃ₗ[k] V) := Finite.of_injective (fun e : V ≃ₗ[k] V => (e : V → V))
    (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  obtain ⟨a, ha⟩ := exists_map_ne_zero hQ
  let : Invertible (Q a) := invertibleOfNonzero ha
  let s : V ≃ₗ[k] V := TauCeti.QuadraticMap.reflection Q a
  have hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q a
  have hs1 : finrank k (commSpace s) = 1 := finrank_commSpace_reflection hQ a
  have hss : s * s = 1 := mul_self_eq_one_of_finrank_commSpace_eq_one hQ hsO hs1
  have hsδ : dicksonHom Q hQ ⟨s, hsO⟩ = Multiplicative.ofAdd (1 : ZMod 2) := by
    rw [dicksonHom_apply]
    simp only [hs1, Nat.cast_one]
  have key : ∀ u : V ≃ₗ[k] V, u ∈ omegaGroup Q hQ → s * u * s = u⁻¹ := by
    intro u hu
    have huO : u ∈ TauCeti.QuadraticMap.orthogonalGroup Q := (mem_omegaGroup.mp hu).1
    have hδu : dicksonHom Q hQ ⟨u, huO⟩ = 1 := by
      rw [dicksonHom_apply, show (finrank k (commSpace u) : ZMod 2) = 0 from
        ZMod.natCast_eq_zero_iff_even.mpr (mem_omegaGroup.mp hu).2]
      rfl
    have hus : u * s ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem huO hsO
    have hδus : dicksonHom Q hQ ⟨u * s, hus⟩ = Multiplicative.ofAdd (1 : ZMod 2) := by
      have h1 : (⟨u * s, hus⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) =
          ⟨u, huO⟩ * ⟨s, hsO⟩ := rfl
      rw [h1, map_mul, hδu, hsδ, one_mul]
    have hodd : (finrank k (commSpace (u * s)) : ZMod 2) = 1 := by
      rw [dicksonHom_apply] at hδus
      exact Multiplicative.ofAdd.injective hδus
    have hle : finrank k (commSpace (u * s)) ≤ 2 := (Submodule.finrank_le _).trans h2.le
    have h1' : finrank k (commSpace (u * s)) = 1 := by
      generalize finrank k (commSpace (u * s)) = n at hodd hle
      interval_cases n
      · exact absurd hodd (by decide)
      · rfl
      · exact absurd hodd (by decide)
    have hsq : (u * s) * (u * s) = 1 :=
      mul_self_eq_one_of_finrank_commSpace_eq_one hQ hus h1'
    apply eq_inv_of_mul_eq_one_right
    calc u * (s * u * s) = u * s * (u * s) := by simp only [mul_assoc]
      _ = 1 := hsq
  have hno2 : ∀ u : ↥(omegaGroup Q hQ), orderOf u ≠ 2 := by
    intro u hu2
    have hu2' : (u : V ≃ₗ[k] V) ^ 2 = 1 := by
      have h : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
      simpa using congrArg Subtype.val h
    have hne : (u : V ≃ₗ[k] V) ≠ 1 := by
      intro h
      have h1 : u = 1 := Subtype.ext h
      rw [h1] at hu2
      exact absurd hu2 (by rw [orderOf_one]; decide)
    have hneg : ∀ x : V, -x = x := fun x => by
      rw [neg_eq_iff_add_eq_zero, ← two_smul k x, CharTwo.two_eq_zero, zero_smul]
    have hlefix : commSpace (u : V ≃ₗ[k] V) ≤ fixSpace (u : V ≃ₗ[k] V) := by
      rintro x ⟨y, rfl⟩
      rw [mem_fixSpace]
      change (u : V ≃ₗ[k] V) ((u : V ≃ₗ[k] V) y - y) =
        (u : V ≃ₗ[k] V) y - y
      have hvv : (u : V ≃ₗ[k] V) ((u : V ≃ₗ[k] V) y) = y := by
        have h := congrArg (fun e : V ≃ₗ[k] V => e y) hu2'
        simpa [pow_two, LinearEquiv.mul_apply] using h
      rw [map_sub, hvv, sub_eq_add_neg, sub_eq_add_neg, hneg, hneg, add_comm]
    have hfr : finrank k (commSpace (u : V ≃ₗ[k] V)) ≤
        finrank k (fixSpace (u : V ≃ₗ[k] V)) := Submodule.finrank_mono hlefix
    have hsum := finrank_commSpace_add_finrank_fixSpace (u : V ≃ₗ[k] V)
    have hpos : 1 ≤ finrank k (commSpace (u : V ≃ₗ[k] V)) := one_le_finrank_commSpace hne
    have heven : Even (finrank k (commSpace (u : V ≃ₗ[k] V))) :=
      (mem_omegaGroup.mp u.2).2
    obtain ⟨m, hm⟩ := heven
    omega
  have hodd : Odd (Nat.card ↥(omegaGroup Q hQ)) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    obtain ⟨u, hu2⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(omegaGroup Q hQ)) 2 (even_iff_two_dvd.mp heven)
    exact hno2 u hu2
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  intro u hu
  have hdvd : orderOf u ∣ Nat.card ↥(omegaGroup Q hQ) :=
    Subgroup.orderOf_dvd_natCard (omegaGroup Q hQ) hu
  have huord : Odd (orderOf u) := Odd.of_dvd_nat hodd hdvd
  obtain ⟨n, hn⟩ := huord
  let h : V ≃ₗ[k] V := u ^ (n + 1)
  have hhOmega : h ∈ omegaGroup Q hQ := by
    change u ^ (n + 1) ∈ omegaGroup Q hQ
    exact Subgroup.pow_mem (omegaGroup Q hQ) hu (n + 1)
  have hkey : s * h * s = h⁻¹ := key h hhOmega
  have hpow : h ^ 2 = u := by
    dsimp only [h]
    rw [← pow_mul, show (n + 1) * 2 = orderOf u + 1 by omega,
      pow_succ, pow_orderOf_eq_one, one_mul]
  have hcomm : ⁅s, h⁆ = u⁻¹ := by
    rw [commutatorElement_def, hsinv, hkey, ← mul_inv_rev, ← pow_two, hpow]
  have hmem : ⁅s, h⁆ ∈ orthDerived Q :=
    Subgroup.commutator_mem_commutator hsO
      (show h ∈ TauCeti.QuadraticMap.orthogonalGroup Q from (mem_omegaGroup.mp hhOmega).1)
  rw [hcomm] at hmem
  simpa only [inv_inv] using Subgroup.inv_mem (orthDerived Q) hmem

end TwoDimensional

section AnchoredIntersection

variable {k V : Type} [Field k] [Finite k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [CharP k 2] {Q : QuadraticForm k V}

theorem supportedDerived_sup_inf_sup_of_finrank_two
    (hQ : (polarBilin Q).Nondegenerate) {A B C : Submodule k V}
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (polarBilin (Q.comp B.subtype)).Nondegenerate)
    (hC : (polarBilin (Q.comp C.subtype)).Nondegenerate)
    (hAdim : finrank k A = 2)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, polar Q a c = 0)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, polar Q b c = 0) :
    supportedDerived Q (A ⊔ B) ⊓ supportedDerived Q (A ⊔ C) = supportedDerived Q A := by
  have hABreg : (polarBilin (Q.comp (A ⊔ B).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
      (CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup
        (polarNondegOn_of_nondegenerate hA) (polarNondegOn_of_nondegenerate hB) hAB)
  have hACreg : (polarBilin (Q.comp (A ⊔ C).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
      (CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup
        (polarNondegOn_of_nondegenerate hA) (polarNondegOn_of_nondegenerate hC) hAC)
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgAB, hgAC⟩ := hg
    have hgorth : g ∈ orthDerived Q := supportedDerived_le_orthDerived_of_regular hABreg hgAB
    have hgomega : g ∈ omegaGroup Q hQ :=
      CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ hgorth
    have hfix : ∀ x ∈ suppPerp Q A, g x = x := fun x hx =>
      supportedDerived_apply_perp_of_mem_two_supports hB hAB hBC hgAB hgAC hx
    have hpres : ∀ a ∈ A, g a ∈ A := fun a ha =>
      supportedDerived_apply_mem_of_mem_two_supports hB hAB hBC hgAB hgAC ha
    have hAmap : A.map (g : V →ₗ[k] V) = A := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact hpres a ha
      · intro a ha
        refine ⟨g.symm a, ?_, g.apply_symm_apply a⟩
        exact supportedDerived_apply_mem_of_mem_two_supports hB hAB hBC
          (Subgroup.inv_mem _ hgAB) (Subgroup.inv_mem _ hgAC) ha
    let h : A ≃ₗ[k] A := LinearEquiv.ofSubmodules (e := g) A A hAmap
    have hcoe : ∀ a : A, ((h a : A) : V) = g (a : V) := fun a =>
      LinearEquiv.ofSubmodules_apply (e := g) (p := A) (q := A) hAmap a
    have hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp A.subtype) := by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro a
      have hgO : ∀ x, Q (g x) = Q x :=
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
          (orthDerived_le_orthogonalGroup_of_commutator Q hgorth)
      show Q ((h a : A) : V) = Q (a : V)
      rw [hcoe]
      exact hgO (a : V)
    have hcommspace : (commSpace h).map A.subtype = commSpace g := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨a, rfl⟩ := mem_commSpace.mp hy
        refine mem_commSpace.mpr ⟨(a : V), ?_⟩
        change g (a : V) - (a : V) = ((h a - a : A) : V)
        rw [Submodule.coe_sub, hcoe]
      · rintro ⟨w, rfl⟩
        obtain ⟨a, ha, z, hz, rfl⟩ :=
          suppExists_add_of_isCompl (isCompl_suppPerp (polarNondegOn_of_nondegenerate hA)) w
        have hgz : g z = z := hfix z hz
        have hga : g (a : V) ∈ A := hpres a ha
        have hsub : g ((a : V) + z) - ((a : V) + z) = g (a : V) - (a : V) := by
          rw [map_add, hgz]
          abel
        change g ((a : V) + z) - ((a : V) + z) ∈ (commSpace h).map A.subtype
        rw [hsub]
        refine Submodule.mem_map.mpr ⟨⟨g (a : V) - (a : V), A.sub_mem hga ha⟩, ?_, rfl⟩
        refine mem_commSpace.mpr ⟨⟨(a : V), ha⟩, ?_⟩
        apply Subtype.ext
        rw [Submodule.coe_sub, hcoe]
    have hfr : finrank k (commSpace h) = finrank k (commSpace g) := by
      rw [← Submodule.finrank_map_subtype_eq A (commSpace h), hcommspace]
    have heven : Even (finrank k (commSpace h)) := by
      rw [hfr]
      exact (mem_omegaGroup.mp hgomega).2
    have hhomega : h ∈ omegaGroup (Q.comp A.subtype) hA := mem_omegaGroup.mpr ⟨hhO, heven⟩
    have hhder : h ∈ orthDerived (Q.comp A.subtype) :=
      omegaGroup_le_orthDerived_of_finrank_two hA hAdim hhomega
    exact mem_supportedDerived.mpr ⟨hfix, h, hhder, hcoe⟩
  · refine le_inf ?_ ?_
    · exact supportedDerived_le_supportedDerived_of_le le_sup_left hA hABreg
    · exact supportedDerived_le_supportedDerived_of_le le_sup_left hA hACreg

end AnchoredIntersection

section Model

omit [Finite K] [CharP K 2] in
private theorem finrank_coordAnchor_refl (n : ℕ) :
    Module.finrank F (coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K)))) = 2 := by
  have hdim : Module.finrank F (coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K)))) =
      Module.finrank F (F × F) := by
    dsimp only [coordAnchor]
    exact LinearMap.finrank_range_of_inj LinearMap.inl_injective
  rw [hdim, Module.finrank_prod, Module.finrank_self]

private theorem finrank_coordPlane_refl (E : QuadExt F K (unitaryInvolution K 2 f))
    (n : ℕ) (i : Fin n) :
    Module.finrank F (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i) = 2 := by
  have hdim : Module.finrank F (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i) =
      Module.finrank F K := by
    let L : K →ₗ[F] (Fin n → K) := LinearMap.single F (fun _ => K) i
    have hL : Function.Injective L := by
      intro x y hxy
      have h := congrFun hxy i
      simpa [L] using h
    have hinj : Function.Injective
        ((LinearMap.inr F (F × F) (Fin n → K)).comp L) :=
      LinearMap.inr_injective.comp hL
    dsimp only [coordPlane]
    exact LinearMap.finrank_range_of_inj hinj
  rw [hdim, E.finrank_eq]

theorem normPureBlock_mono (n : ℕ) : Monotone (normPureBlock E n) := by
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  let ψ := LinearEquiv.refl F ((F × F) × (Fin n → K))
  have hψ := normHypForm_apply_coord E n
  have hUpoly : ∀ i, PolarNondegOn (normHypForm E n) (coordPlane ψ i) :=
    fun i => coordPlane_polarNondegOn ψ hψ (normQuad_polarBilin_nondegenerate E) i
  have hUorth : ∀ i j, i ≠ j → ∀ x ∈ coordPlane ψ i, ∀ y ∈ coordPlane ψ j,
      polar (normHypForm E n) x y = 0 :=
    fun i j hij x hx y hy => polar_coordPlane_plane ψ hψ hij hx hy
  intro S T hST
  simp only [normPureBlock]
  refine Subgroup.subgroupOf_mono (normOmega E n) ?_
  refine supportedDerived_le_supportedDerived_of_le (Finset.sup_mono hST) ?_ ?_
  · exact nondegenerate_finset_sup (coordPlane ψ) hUpoly hUorth S
  · exact nondegenerate_finset_sup (coordPlane ψ) hUpoly hUorth T

theorem normPureBlock_le_normBlock (n : ℕ) (S : Finset (Fin n)) :
    normPureBlock E n S ≤ normBlock E n S := by
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  let ψ := LinearEquiv.refl F ((F × F) × (Fin n → K))
  have hψ := normHypForm_apply_coord E n
  have hUpoly : ∀ i, PolarNondegOn (normHypForm E n) (coordPlane ψ i) :=
    fun i => coordPlane_polarNondegOn ψ hψ (normQuad_polarBilin_nondegenerate E) i
  have hUorth : ∀ i j, i ≠ j → ∀ x ∈ coordPlane ψ i, ∀ y ∈ coordPlane ψ j,
      polar (normHypForm E n) x y = 0 :=
    fun i j hij x hx y hy => polar_coordPlane_plane ψ hψ hij hx hy
  simp only [normPureBlock, normBlock, coordSupport]
  refine Subgroup.subgroupOf_mono (normOmega E n) ?_
  exact supportedDerived_le_supportedDerived_of_le le_sup_right
    (nondegenerate_finset_sup (coordPlane ψ) hUpoly hUorth S)
    (coordSupport_nondegenerate ψ hψ (normHypForm_polarBilin_nondegenerate E n)
      (normQuad_polarBilin_nondegenerate E) S)

theorem commute_of_mem_normPureBlock_of_mem_normBlock {n : ℕ} {S T : Finset (Fin n)}
    (hST : Disjoint S T) {x y : normOmega E n} (hx : x ∈ normPureBlock E n S)
    (hy : y ∈ normBlock E n T) : Commute x y := by
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  let ψ := LinearEquiv.refl F ((F × F) × (Fin n → K))
  have hψ := normHypForm_apply_coord E n
  have hQ := normHypForm_polarBilin_nondegenerate E n
  have hQE := normQuad_polarBilin_nondegenerate E
  have hUpoly : ∀ i, PolarNondegOn (normHypForm E n) (coordPlane ψ i) :=
    fun i => coordPlane_polarNondegOn ψ hψ hQE i
  have hUorth : ∀ i j, i ≠ j → ∀ x ∈ coordPlane ψ i, ∀ y ∈ coordPlane ψ j,
      polar (normHypForm E n) x y = 0 :=
    fun i j hij x hx y hy => polar_coordPlane_plane ψ hψ hij hx hy
  have hx' : x.1 ∈ supportedDerived (normHypForm E n) (S.sup (coordPlane ψ)) :=
    Subgroup.mem_subgroupOf.mp hx
  have hy' : y.1 ∈ supportedDerived (normHypForm E n) (coordSupport ψ T) :=
    Subgroup.mem_subgroupOf.mp hy
  have hy'' : y.1 ∈ supportedDerived (normHypForm E n)
      (coordAnchor ψ ⊔ T.sup (coordPlane ψ)) := by
    simpa only [coordSupport] using hy'
  have hAreg : (polarBilin ((normHypForm E n).comp (S.sup (coordPlane ψ)).subtype)).Nondegenerate :=
    nondegenerate_finset_sup (coordPlane ψ) hUpoly hUorth S
  have hBreg : (polarBilin ((normHypForm E n).comp (coordSupport ψ T).subtype)).Nondegenerate :=
    coordSupport_nondegenerate ψ hψ hQ hQE T
  have hSle : S.sup (coordPlane ψ) ≤ suppPerp (normHypForm E n) (coordAnchor ψ) := by
    refine Finset.sup_le fun i _ => ?_
    intro u hu
    rw [mem_suppPerp]
    intro w hw
    exact polar_coordAnchor_plane ψ hψ hw hu
  have horth : ∀ a ∈ S.sup (coordPlane ψ), ∀ b ∈ coordSupport ψ T,
      polar (normHypForm E n) a b = 0 := by
    intro a ha b hb
    rw [coordSupport] at hb
    obtain ⟨w, hw, t, ht, rfl⟩ := Submodule.mem_sup.mp hb
    have haw : polar (normHypForm E n) a w = 0 := by
      have h := mem_suppPerp.mp (hSle ha) w hw
      rwa [polar_comm] at h
    have hat : polar (normHypForm E n) a t = 0 :=
      polar_eq_zero_of_mem_finset_sup_disjoint (coordPlane ψ) hUorth hST ha ht
    rw [polar_add_right, haw, hat, add_zero]
  have hcomm := supportedDerived_commute_of_orthogonal_supports hAreg hBreg horth hx' hy''
  exact Subtype.ext hcomm.eq

theorem normBlock_singleton_inf_singleton {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    normBlock E n {i} ⊓ normBlock E n {j} = normBlock E n ∅ := by
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  let ψ := LinearEquiv.refl F ((F × F) × (Fin n → K))
  have hψ := normHypForm_apply_coord E n
  have hQ := normHypForm_polarBilin_nondegenerate E n
  have hQE := normQuad_polarBilin_nondegenerate E
  have hAreg : (polarBilin ((normHypForm E n).comp (coordAnchor ψ).subtype)).Nondegenerate :=
    coordAnchor_nondegenerate ψ hψ hQ hQE
  have hBreg : (polarBilin ((normHypForm E n).comp (coordPlane ψ i).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
      (coordPlane_polarNondegOn ψ hψ hQE i)
  have hCreg : (polarBilin ((normHypForm E n).comp (coordPlane ψ j).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
      (coordPlane_polarNondegOn ψ hψ hQE j)
  have hmain := supportedDerived_sup_inf_sup_of_finrank_two hQ hAreg hBreg hCreg
    (finrank_coordAnchor_refl (F := F) (K := K) n)
    (fun a ha b hb => polar_coordAnchor_plane ψ hψ ha hb)
    (fun a ha c hc => polar_coordAnchor_plane ψ hψ ha hc)
    (fun b hb c hc => polar_coordPlane_plane ψ hψ hij hb hc)
  have h1 : normBlock E n {i} =
      (supportedDerived (normHypForm E n) (coordAnchor ψ ⊔ coordPlane ψ i)).subgroupOf
        (normOmega E n) := by
    simp only [normBlock, coordSupport, Finset.sup_singleton]
    rfl
  have h2 : normBlock E n {j} =
      (supportedDerived (normHypForm E n) (coordAnchor ψ ⊔ coordPlane ψ j)).subgroupOf
        (normOmega E n) := by
    simp only [normBlock, coordSupport, Finset.sup_singleton]
    rfl
  have h3 : normBlock E n ∅ =
      (supportedDerived (normHypForm E n) (coordAnchor ψ)).subgroupOf (normOmega E n) := by
    simp only [normBlock, coordSupport_empty]
    rfl
  rw [h1, h2, h3]
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [← Subgroup.mem_inf, hmain]

theorem normPureBlock_pair_inf_pair {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    normPureBlock E n {i, j} ⊓ normPureBlock E n {i, k} = normPureBlock E n {i} := by
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  let ψ := LinearEquiv.refl F ((F × F) × (Fin n → K))
  have hψ := normHypForm_apply_coord E n
  have hQ := normHypForm_polarBilin_nondegenerate E n
  have hQE := normQuad_polarBilin_nondegenerate E
  have hAreg : (polarBilin ((normHypForm E n).comp (coordPlane ψ i).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
      (coordPlane_polarNondegOn ψ hψ hQE i)
  have hBreg : (polarBilin ((normHypForm E n).comp (coordPlane ψ j).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
      (coordPlane_polarNondegOn ψ hψ hQE j)
  have hCreg : (polarBilin ((normHypForm E n).comp (coordPlane ψ k).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
      (coordPlane_polarNondegOn ψ hψ hQE k)
  have hmain := supportedDerived_sup_inf_sup_of_finrank_two hQ hAreg hBreg hCreg
    (finrank_coordPlane_refl E n i)
    (fun b hb c hc => polar_coordPlane_plane ψ hψ hij hb hc)
    (fun a ha c hc => polar_coordPlane_plane ψ hψ hik ha hc)
    (fun b hb c hc => polar_coordPlane_plane ψ hψ hjk hb hc)
  have h1 : normPureBlock E n {i, j} =
      (supportedDerived (normHypForm E n)
        (coordPlane ψ i ⊔ coordPlane ψ j)).subgroupOf (normOmega E n) := by
    simp only [normPureBlock, Finset.sup_insert, Finset.sup_singleton]
    rfl
  have h2 : normPureBlock E n {i, k} =
      (supportedDerived (normHypForm E n)
        (coordPlane ψ i ⊔ coordPlane ψ k)).subgroupOf (normOmega E n) := by
    simp only [normPureBlock, Finset.sup_insert, Finset.sup_singleton]
    rfl
  have h3 : normPureBlock E n {i} =
      (supportedDerived (normHypForm E n) (coordPlane ψ i)).subgroupOf (normOmega E n) := by
    simp only [normPureBlock, Finset.sup_singleton]
    rfl
  rw [h1, h2, h3]
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [← Subgroup.mem_inf, hmain]

end Model

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
