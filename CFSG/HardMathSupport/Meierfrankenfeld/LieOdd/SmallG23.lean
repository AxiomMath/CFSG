module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Small
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.RouteADihedral
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.LieType.HighestRoot.CentG2Main
public import CFSG.RankThree.PartOne.S11c.G2Plane
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeFixedPoints
public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27G2Facts
public import CFSG.LieType.Multipliers.G23Bridge
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.G23Witness
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Cooperstein.Coordinator TauCeti

theorem g23_parseWord_append (s t : String) :
    CFSG.LieType.Multipliers.G23.parseWord (s ++ t) =
      CFSG.LieType.Multipliers.G23.parseWord s ++ CFSG.LieType.Multipliers.G23.parseWord t := by
  simp [CFSG.LieType.Multipliers.G23.parseWord, String.toList_append, List.filterMap_append]

theorem g23_parseWord_rep (k : ℕ) (s : String) :
    CFSG.LieType.Multipliers.G23.parseWord (CFSG.LieType.Multipliers.G23.rep k s) =
      (List.replicate k (CFSG.LieType.Multipliers.G23.parseWord s)).flatten := by
  induction k with
  | zero => simp [CFSG.LieType.Multipliers.G23.rep, CFSG.LieType.Multipliers.G23.parseWord]
  | succ k ih =>
    have h : CFSG.LieType.Multipliers.G23.rep (k + 1) s =
        s ++ CFSG.LieType.Multipliers.G23.rep k s := by
      simp [CFSG.LieType.Multipliers.G23.rep, List.replicate_succ, String.join_cons]
    rw [h, g23_parseWord_append, ih, List.replicate_succ, List.flatten_cons]

theorem gens_rels_G23 {K : Type} [Field K] [Finite K]
    (σ : K ≃+* ZMod 3) :
    CFSG.LieType.Multipliers.G23.gens σ 0 ^ 2 = 1 ∧
      (CFSG.LieType.Multipliers.G23.gens σ 0 *
        ((CFSG.LieType.Multipliers.G23.gens σ 1)⁻¹ * CFSG.LieType.Multipliers.G23.gens σ 0 *
          CFSG.LieType.Multipliers.G23.gens σ 1)) ^ 13 = 1 := by
  have hmem : ∀ s ∈ CFSG.LieType.Multipliers.G23.relStrings,
      FreeGroup.lift (CFSG.LieType.Multipliers.G23.gens σ)
        (FreeGroup.mk (CFSG.LieType.Multipliers.G23.parseWord s)) = 1 := fun s hs =>
    CFSG.LieType.Multipliers.G23.lift_gens_rels σ _
      (List.mem_map_of_mem (List.mem_map_of_mem hs))
  have h1 := hmem "aa" (by simp [CFSG.LieType.Multipliers.G23.relStrings])
  have h2 := hmem (CFSG.LieType.Multipliers.G23.rep 13 "aBab")
    (by simp [CFSG.LieType.Multipliers.G23.relStrings])
  have hw1 : CFSG.LieType.Multipliers.G23.parseWord "aa" = [(0, true), (0, true)] := by decide
  have hw2 : CFSG.LieType.Multipliers.G23.parseWord "aBab" =
      [(0, true), (1, false), (0, true), (1, true)] := by decide
  rw [hw1, FreeGroup.lift_mk] at h1
  rw [g23_parseWord_rep, hw2, FreeGroup.lift_mk, List.map_flatten, List.map_replicate,
    List.prod_flatten, List.map_replicate, List.prod_replicate] at h2
  refine ⟨?_, ?_⟩
  · simpa [sq] using h1
  · simpa [mul_assoc] using h2


theorem card_mulAut_adjointGroup_G2_three {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3) :
    Nat.card (MulAut (adjointGroup ReeTag.G2.tag K)) ≤
      2 * Nat.card (adjointGroup ReeTag.G2.tag K) := by
  obtain ⟨-, hNF, -⟩ :=
    G2_three_exact_automorphism_normal_form (f := 1) le_rfl K (by rw [hK, pow_one])
  have : Finite (adjointGroup ReeTag.G2.tag K) := inferInstance
  have hsurj : Function.Surjective (fun gk : adjointGroup ReeTag.G2.tag K × Fin (2 * 1) =>
      MulAut.conj gk.1 * ReeTag.G2.finiteExceptionalAut K ^ (gk.2 : ℕ)) := fun α => by
    obtain ⟨gk, hgk, -⟩ := hNF α
    exact ⟨gk, hgk.symm⟩
  calc Nat.card (MulAut (adjointGroup ReeTag.G2.tag K))
      ≤ Nat.card (adjointGroup ReeTag.G2.tag K × Fin (2 * 1)) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = 2 * Nat.card (adjointGroup ReeTag.G2.tag K) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin (2 * 1)), Fintype.card_fin]
        ring

theorem two_rank_adjointGroup_G2
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K))
    (B : Subgroup (adjointGroup .G2 K)) (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (h2 : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 2 ^ 3 := by
  have : Finite (ModGL .G2 K) := finite_modGL
  let ψ : ↥(adjointGroup .G2 K) →* ModGL .G2 K := (adjointGroup .G2 K).subtype
  have hψ : Function.Injective ψ := fun a b hab => Subtype.ext hab
  have hR : B.map ψ ≤ adjointGroup .G2 K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have : IsElementaryAbelian 2 ↥(B.map ψ) :=
    { is_comm := ⟨fun a b => by
        obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
        obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
        apply Subtype.ext
        show ψ x * ψ y = ψ y * ψ x
        rw [← map_mul, ← map_mul, hc x hx y hy]⟩
      exponent_dvd_p := by
        refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
        obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
        apply Subtype.ext
        show ψ x ^ 2 = 1
        rw [← map_pow, sq, h2 x hx, map_one] }
  have h8 := (CFSG.RankThree.PartOne.g2_elementary_two hK hR).1
  rwa [Subgroup.card_map_of_injective hψ] at h8

section Outer

open CFSG.LocalAnalysis.EvenBN.LinearThree.G2Three (aut_cases phi_sq phi_not_mem_range
  exists_conj_eq_conj_mul_phi)

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem finiteReeAut_zero_eq (hK : Nat.card K = 3) :
    ReeTag.G2.finiteReeAut K 0 = ReeTag.G2.finiteExceptionalAut K := by
  obtain ⟨-, -, -, -, -, -, hodd⟩ :=
    G2_three_exact_automorphism_normal_form le_rfl K (by rw [hK, pow_one])
  obtain ⟨-, hF, -⟩ := hodd 0 rfl
  rw [pow_one] at hF
  exact hF.symm

theorem exists_inverted_of_fixed (hK : Nat.card K = 3) {u t : adjointGroup ReeTag.G2.tag K}
    (hu : ReeTag.G2.finiteExceptionalAut K u = u) (ht : ReeTag.G2.finiteExceptionalAut K t = t)
    (hu2 : u * u = 1) (hut : u * t * u⁻¹ = t⁻¹) :
    ∃ x : adjointGroup ReeTag.G2.tag K, orderOf x = orderOf t ∧
      ReeTag.G2.finiteExceptionalAut K x = x⁻¹ := by
  set φ := ReeTag.G2.finiteExceptionalAut K with hφdef
  have hφ2 : φ * φ = 1 := by rw [← sq]; exact phi_sq hK
  have hψ2 : (MulAut.conj u * φ) ^ 2 = 1 := by
    rw [sq]
    calc MulAut.conj u * φ * (MulAut.conj u * φ)
        = MulAut.conj u * (φ * MulAut.conj u * φ⁻¹) * (φ * φ) := by group
      _ = 1 := by
        rw [CFSG.LieType.Chevalley.mulAut_mul_conj_mul_inv, hφ2, hu, ← map_mul, hu2, map_one,
          mul_one]
  obtain ⟨b, hb⟩ := exists_conj_eq_conj_mul_phi hK u hψ2
  rw [← hφdef] at hb
  have hφ' : φ = (MulAut.conj b)⁻¹ * (MulAut.conj u * φ) * MulAut.conj b := by
    rw [← hb]; group
  have hψt : (MulAut.conj u * φ) t = t⁻¹ := by
    rw [MulAut.mul_apply, ht, MulAut.conj_apply, hut]
  refine ⟨(MulAut.conj b)⁻¹ t, MulEquiv.orderOf_eq _ _, ?_⟩
  calc φ ((MulAut.conj b)⁻¹ t)
      = ((MulAut.conj b)⁻¹ * (MulAut.conj u * φ) * MulAut.conj b) ((MulAut.conj b)⁻¹ t) := by
        rw [← hφ']
    _ = (MulAut.conj b)⁻¹ ((MulAut.conj u * φ) t) := by
        simp only [MulAut.mul_apply, MulAut.apply_inv_self]
    _ = ((MulAut.conj b)⁻¹ t)⁻¹ := by rw [hψt, map_inv]

theorem exists_inverted_of_outer (hK : Nat.card K = 3) {x₀ : adjointGroup ReeTag.G2.tag K}
    (hx₀ : ReeTag.G2.finiteExceptionalAut K x₀ = x₀⁻¹)
    (ψ : MulAut (adjointGroup ReeTag.G2.tag K))
    (hψ : ψ ∉ (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
      MulAut (adjointGroup ReeTag.G2.tag K)).range) (hψ2 : ψ * ψ = 1) :
    ∃ x : adjointGroup ReeTag.G2.tag K, orderOf x = orderOf x₀ ∧ ψ x = x⁻¹ := by
  rcases aut_cases hK ψ with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact absurd ⟨g, rfl⟩ hψ
  · obtain ⟨b, hb⟩ := exists_conj_eq_conj_mul_phi hK g (by rw [sq]; exact hψ2)
    refine ⟨MulAut.conj b x₀, MulEquiv.orderOf_eq _ _, ?_⟩
    rw [← hb]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self, hx₀, map_inv]

theorem exists_dihedral_seven_fixed (hK : Nat.card K = 3)
    (hH9 : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 8 →
      ∃ u t : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F),
        u * u = 1 ∧ u ≠ 1 ∧ orderOf t = 7 ∧ u * t * u⁻¹ = t⁻¹) :
    ∃ u t : adjointGroup ReeTag.G2.tag K, ReeTag.G2.finiteExceptionalAut K u = u ∧
      ReeTag.G2.finiteExceptionalAut K t = t ∧ u * u = 1 ∧ orderOf t = 7 ∧
        u * t * u⁻¹ = t⁻¹ := by
  obtain ⟨-, -, -, -, hcm, -⟩ :=
    CFSG.ComponentClassification.LiteratureLocal.G2_reeGamma_zero_structure (K := K)
      (by rw [hK]; norm_num)
  obtain ⟨F, _, _, hF, ⟨e₈⟩⟩ := hcm.2
  obtain ⟨u₀, t₀, hu₀, -, ht₀, hut₀⟩ := hH9 F (by rw [hF]; norm_num)
  set Fix := ReeTag.G2.finiteReeFixedGroup K 0 with hFix
  let eqv : ↥Fix ≃* ↥(Fix.map (adjointGroup ReeTag.G2.tag K).subtype) :=
    Subgroup.equivMapOfInjective Fix _ Subtype.val_injective
  let j : ↥(commutator ↥(ReeTag.G2.reeGamma K 0)) →* adjointGroup ReeTag.G2.tag K :=
    Fix.subtype.comp (eqv.symm.toMonoidHom.comp
      (commutator ↥(ReeTag.G2.reeGamma K 0)).subtype)
  have hj : Function.Injective j :=
    Fix.subtype_injective.comp (eqv.symm.injective.comp Subtype.val_injective)
  have hfix : ∀ x, ReeTag.G2.finiteExceptionalAut K (j x) = j x := fun x => by
    rw [← finiteReeAut_zero_eq hK]
    exact (ReeTag.mem_finiteReeFixedGroup).1 (eqv.symm (x : ↥(ReeTag.G2.reeGamma K 0))).2
  refine ⟨j (e₈.symm u₀), j (e₈.symm t₀), hfix _, hfix _, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hu₀, map_one, map_one]
  · rw [orderOf_injective j hj, MulEquiv.orderOf_eq, ht₀]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, hut₀, map_inv,
      map_inv]

end Outer

section Inner

theorem exists_conj_orderOf_thirteen
    {K : Type} [Field K] [Finite K] [CharP K 3]
    (σ : K ≃+* ZMod 3)
    (hH10 : orderOf (CFSG.LieType.Multipliers.G23.gens σ 0) = 2 ∧
      orderOf (CFSG.LieType.Multipliers.G23.gens σ 0 *
        ((CFSG.LieType.Multipliers.G23.gens σ 1)⁻¹ * CFSG.LieType.Multipliers.G23.gens σ 0 *
          CFSG.LieType.Multipliers.G23.gens σ 1)) = 13)
    (t : adjointGroup .G2 K) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ c : adjointGroup .G2 K, orderOf (t * (c * t * c⁻¹)) = 13 := by
  set a := CFSG.LieType.Multipliers.G23.gens σ 0
  set b := CFSG.LieType.Multipliers.G23.gens σ 1
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.LieType.HighestRoot.g2_involutions_isConj hchar t a hto hH10.1)
  refine ⟨c⁻¹ * b⁻¹ * c, ?_⟩
  have key : t * ((c⁻¹ * b⁻¹ * c) * t * (c⁻¹ * b⁻¹ * c)⁻¹) =
      MulAut.conj c⁻¹ (a * (b⁻¹ * a * b)) := by
    rw [← hc]
    simp only [MulAut.conj_apply, inv_inv]
    group
  rw [key, MulEquiv.orderOf_eq, hH10.2]

theorem orderOf_gens_G23_of_rels {K : Type} [Field K] [Finite K]
    (σ : K ≃+* ZMod 3) (hK : Nat.card K = 3)
    (ha2 : CFSG.LieType.Multipliers.G23.gens σ 0 ^ 2 = 1)
    (hx13 : (CFSG.LieType.Multipliers.G23.gens σ 0 *
      ((CFSG.LieType.Multipliers.G23.gens σ 1)⁻¹ * CFSG.LieType.Multipliers.G23.gens σ 0 *
        CFSG.LieType.Multipliers.G23.gens σ 1)) ^ 13 = 1) :
    orderOf (CFSG.LieType.Multipliers.G23.gens σ 0) = 2 ∧
      orderOf (CFSG.LieType.Multipliers.G23.gens σ 0 *
        ((CFSG.LieType.Multipliers.G23.gens σ 1)⁻¹ * CFSG.LieType.Multipliers.G23.gens σ 0 *
          CFSG.LieType.Multipliers.G23.gens σ 1)) = 13 := by
  set a := CFSG.LieType.Multipliers.G23.gens σ 0 with ha
  set b := CFSG.LieType.Multipliers.G23.gens σ 1 with hb
  have hgen := CFSG.LieType.Multipliers.G23.closure_range_gens σ
  have hcen : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hcard := CFSG.LieType.Multipliers.G23.card_adjointGroup_G2_eq (K := K) hK
  have hcentral : ∀ g : adjointGroup .G2 K, g * a = a * g → g * b = b * g → g = 1 := by
    intro g hga hgb
    have hle : Subgroup.closure (Set.range (CFSG.LieType.Multipliers.G23.gens σ)) ≤
        Subgroup.centralizer {g} := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      fin_cases i
      · exact hga.symm
      · exact hgb.symm
    have hg : g ∈ Subgroup.center (adjointGroup .G2 K) := by
      rw [Subgroup.mem_center_iff]
      intro h
      have := hle (hgen ▸ Subgroup.mem_top h)
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    rw [hcen, Subgroup.mem_bot] at hg
    exact hg
  have ha1 : a ≠ 1 := by
    intro h1
    have hb1 : b = 1 := hcentral b (by rw [h1, one_mul, mul_one]) rfl
    have htop : (⊤ : Subgroup (adjointGroup .G2 K)) = ⊥ := by
      rw [← hgen, eq_bot_iff, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact h1
      · exact hb1
    have h1' : Nat.card (adjointGroup .G2 K) = 1 := by
      rw [← Subgroup.card_top (G := adjointGroup .G2 K), htop, Subgroup.card_bot]
    rw [hcard] at h1'
    norm_num at h1'
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ha2)
  have hx1 : a * (b⁻¹ * a * b) ≠ 1 := by
    intro h1
    apply ha1
    refine hcentral a rfl ?_
    have h2 : b⁻¹ * a * b = a := by
      have := eq_inv_of_mul_eq_one_right h1
      rw [hainv] at this
      exact this
    calc a * b = b * (b⁻¹ * a * b) := by group
      _ = b * a := by rw [h2]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact ⟨orderOf_eq_prime ha2 ha1, orderOf_eq_prime hx13 hx1⟩

theorem orderOf_gens_G23 {K : Type} [Field K] [Finite K]
    (σ : K ≃+* ZMod 3) (hK : Nat.card K = 3) :
    orderOf (CFSG.LieType.Multipliers.G23.gens σ 0) = 2 ∧
      orderOf (CFSG.LieType.Multipliers.G23.gens σ 0 *
        ((CFSG.LieType.Multipliers.G23.gens σ 1)⁻¹ * CFSG.LieType.Multipliers.G23.gens σ 0 *
          CFSG.LieType.Multipliers.G23.gens σ 1)) = 13 :=
  orderOf_gens_G23_of_rels σ hK (gens_rels_G23 σ).1 (gens_rels_G23 σ).2

end Inner

section Assembly


theorem noIrrFFOffender_adjointGroup_G2_three_of {K : Type} [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K = 3) (σ : K ≃+* ZMod 3)
    (hH9 : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 8 →
      ∃ u t : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F),
        u * u = 1 ∧ u ≠ 1 ∧ orderOf t = 7 ∧ u * t * u⁻¹ = t⁻¹)
    (hH10 : orderOf (CFSG.LieType.Multipliers.G23.gens σ 0) = 2 ∧
      orderOf (CFSG.LieType.Multipliers.G23.gens σ 0 *
        ((CFSG.LieType.Multipliers.G23.gens σ 1)⁻¹ * CFSG.LieType.Multipliers.G23.gens σ 0 *
          CFSG.LieType.Multipliers.G23.gens σ 1)) = 13) :
    NoIrrFFOffender (adjointGroup .G2 K) := by
  have : CharP K ReeTag.G2.prime := ‹CharP K 3›
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨u, t, hu, ht, hu2, hto, hut⟩ := exists_dihedral_seven_fixed hK hH9
  obtain ⟨x₀, hx₀o, hx₀⟩ := exists_inverted_of_fixed hK hu ht hu2 hut
  refine FFToolkit.noIrrFFOffender_of_route_A_dihedral (r := 3) (ρ := 6) (p := 13)
    center_adjointGroup_eq_bot (card_mulAut_adjointGroup_G2_three hK) (by norm_num) (by norm_num)
    (by rw [orderOf_two_zmod_thirteen]; norm_num)
    (two_rank_adjointGroup_G2 (by rw [hK]; decide)) (exists_conj_orderOf_thirteen σ hH10) ?_
  intro ψ hψ hψ2
  obtain ⟨x, hxo, hx⟩ := exists_inverted_of_outer hK hx₀ ψ hψ hψ2
  exact ⟨7, ⟨by norm_num⟩, x, by norm_num, by rw [FFToolkit.orderOf_two_zmod_seven],
    hxo.trans (hx₀o.trans hto), hx⟩

theorem smallG23_of
    (hH9 : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 8 →
      ∃ u t : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F),
        u * u = 1 ∧ u ≠ 1 ∧ orderOf t = 7 ∧ u * t * u⁻¹ = t⁻¹)
    (hH10 : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* ZMod 3), Nat.card K = 3 →
      orderOf (CFSG.LieType.Multipliers.G23.gens σ 0) = 2 ∧
        orderOf (CFSG.LieType.Multipliers.G23.gens σ 0 *
          ((CFSG.LieType.Multipliers.G23.gens σ 1)⁻¹ * CFSG.LieType.Multipliers.G23.gens σ 0 *
            CFSG.LieType.Multipliers.G23.gens σ 1)) = 13) :
    SmallG23 := by
  intro d q hq hd
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  apply noFFModule_of_noIrrFFOffender
  have hp2 : q.p ≠ 2 := by
    intro h
    have h1 := PrimePower.card_def q
    rw [h, hq] at h1
    have h2 : 2 ∣ 3 := by rw [h1]; exact dvd_pow_self 2 q.exponent_pos.ne'
    norm_num at h2
  obtain ⟨K, hKf, hKfin, hK⟩ := exists_field_of_index q hv (LieTypeIndex.fieldOrder_G2 q)
  have hKq : Nat.card K = q.card := by rw [hK, PrimePower.card_def]
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hp2 K hKq
  have hK3 : Nat.card K = 3 := hKq.trans hq
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime_pow (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK3, pow_one])
  obtain ⟨σ⟩ : Nonempty (K ≃+* ZMod 3) :=
    ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK3, ZMod.card])⟩
  have hY := noIrrFFOffender_adjointGroup_G2_three_of hK3 σ hH9 (hH10 K σ hK3)
  let e1 : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  exact FFSporadic.noIrrFFOffender_transfer hY ⟨e1.symm.trans φ⟩

theorem smallG23 :
    SmallG23 :=
  smallG23_of (fun _ _ _ hF => Proving.exists_dihedral_seven_psl2 hF)
    (fun _ _ _ σ hK => orderOf_gens_G23 σ hK)

end Assembly

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
