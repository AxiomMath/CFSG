module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWKind
import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSLFourA8
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternating
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWSwap

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (alternating_schreier_of_nonempty_equiv)

@[expose] def LSixFieldNOneLiftInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 6 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 6) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 10 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsComponent Kc → seitzLeviHat e c W₁ < Kc →
      Kc.map (MulAut.conj (seitzHatMap W₁ ⟨t, htN⟩)).toMonoidHom = Kc →
      seitzHatMap W₁ ⟨t, htN⟩ ∉ Kc → center Kc = ⊥ → LieModel Kc .PSL 5 2 2 →
    ∀ (a b : Fin 6), a ≠ b → c ≠ a → c ≠ b → ∀ X₀ : Subgroup (LinearFlag.projectiveSL 6 K),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∃ P : Subgroup G, P ≤ centralizer (modelToG e X₀ : Set G) ∧ ⁅P, P⁆ = P ∧
        ∃ (N : Subgroup P) (_ : N.Normal), LieModel (P ⧸ N) .PSL 3 2 2

theorem nat_card_alternatingGroup_fin_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 8)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 8), Fintype.card_fin] at h2
  have h8 : Nat.factorial 8 = 40320 := by decide
  omega

theorem range_commutator_eq_of_perfect {G Y : Type*} [Group G] [Group Y] {P : Subgroup G}
    (hP : ⁅P, P⁆ = P) (f : P →* Y) : ⁅f.range, f.range⁆ = f.range := by
  have hTop : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hP]
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hTop]

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem lSixFieldNOneExclusionInput_of_lift
    (hlift : LSixFieldNOneLiftInput) : LSixFieldNOneExclusionInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc hLK hKt' htK hZ
    hmodel a b hab hca hcb X₀ hX₀ hX₀c htX hswap
  obtain ⟨P, hPX, hPperf, N, _, hNL⟩ := hlift G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN
    hLN Kc hKc hLK hKt' htK hZ hmodel a b hab hca hcb X₀ hX₀ hX₀c
  obtain ⟨Kx, hKx, hDKK, hKxt, hcomm, hZx, ⟨φx⟩⟩ := hswap
  have htC : t ∈ centralizer (L : Set G) := by
    have h := mem_zpowers t
    rw [← hKt] at h
    exact (Subgroup.mem_inf.1 h).1
  obtain ⟨-, -, -, -, hcomp, hsyl, -, -⟩ :=
    neighbour_hyps_linear_two (X := modelToG e X₀)
      (D := modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 6))ᶜ))) hset hK e (by norm_num)
      htC ht hab hX₀ hX₀c rfl htX rfl
  obtain ⟨-, -, ⟨eD⟩⟩ := nonempty_map_oddCore_mulEquiv_specialLinear_two
    (X := modelToG e X₀) (D := modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 6))ᶜ))) hK e
    (by norm_num) htC hab hX₀ hX₀c rfl rfl
  set s := QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ with hs_def
  have hs : orderOf s = 2 := orderOf_mk_oddCore (by rw [orderOf_mk]; exact ht)
  have hsD : s ∈ centralizer
      (((modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 6))ᶜ))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) : Set _) :=
    mem_centralizer_iff.2 fun d hd => mem_centralizer_singleton_iff.1 (hcomp.1 hd)
  have eA : Kx ≃* alternatingGroup (Fin 8) :=
    (SporadicRefine.nonempty_mulEquiv_alternating_of_SL_four hK (φx.trans eD)).some
  set Kx' := Kx.map (MulAut.conj s).toMonoidHom with hKx'
  have eConj : Kx ≃* Kx' := Kx.equivMapOfInjective _ (MulAut.conj s).injective
  have eA' : Kx' ≃* alternatingGroup (Fin 8) := eConj.symm.trans eA
  have hA : CFSG.ComponentClassification.CatLeaf.IsAltType Kx :=
    ⟨Fin 8, inferInstance, inferInstance, by simp, ⟨eA⟩⟩
  have hA' : CFSG.ComponentClassification.CatLeaf.IsAltType Kx' :=
    ⟨Fin 8, inferInstance, inferInstance, by simp, ⟨eA'⟩⟩
  have hZx' : center Kx' = ⊥ := by
    rw [← map_center_eq eConj, hZx, Subgroup.map_bot]
  have hcardKx : Nat.card Kx = 20160 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup_fin_eight]
  have hcardKx' : Nat.card Kx' = 20160 := by
    rw [Nat.card_congr eA'.toEquiv, nat_card_alternatingGroup_fin_eight]
  have hOut : Group.IsSolvable (Outer Kx) :=
    alternating_schreier_of_nonempty_equiv 8 (by norm_num) ⟨eA⟩
  have hOut' : Group.IsSolvable (Outer Kx') :=
    alternating_schreier_of_nonempty_equiv 8 (by norm_num) ⟨eA'⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hQ₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := Kx) 2 (n := 2)
    (by rw [hcardKx]; norm_num)
  have hQc : Nat.card (Q₀.map Kx.subtype) = 2 ^ 2 := by
    rw [Subgroup.card_map_of_injective Kx.subtype_injective, hQ₀]
  have hor := map_conj_eq_or_eq_of_swap hKx hDKK hsyl (IsPGroup.of_card hQc) (map_subtype_le _)
    (by rw [hQc]; norm_num)
  set ψ : P →* centralizer (modelToG e X₀ : Set G) ⧸
      oddCore (centralizer (modelToG e X₀ : Set G)) :=
    (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))).comp
      (Subgroup.inclusion hPX) with hψ
  have hψle : ψ.range ≤ Kx ⊔ Kx' :=
    perfect_le_sup_of_swap (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hs hsD hDKK hKxt
      hcomm hor hsyl hOut hOut' (range_commutator_eq_of_perfect hPperf ψ)
  have hodd : Odd (Nat.card ψ.ker) := by
    have hle : ψ.ker.map (Subgroup.inclusion hPX) ≤
        oddCore (centralizer (modelToG e X₀ : Set G)) := by
      rintro _ ⟨p, hp, rfl⟩
      have hp' : ψ p = 1 := hp
      rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hp'
      exact hp'
    have hcard := Subgroup.card_map_of_injective (K := ψ.ker) (Subgroup.inclusion_injective hPX)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcard] at hdvd
    exact Odd.of_dvd_nat CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd hdvd
  have hcardS := card_of_lieModel_PSL_three_four hNL
  exact false_of_lieModel_quotient_of_range_le_sup hcomm hZx' hA hA' ψ hψle hodd hNL
    (by rw [hcardS, hcardKx]) (by rw [hcardS, hcardKx'])

theorem linearTwoSwapRowAtInput_six_of_lift
    (hW : LinearTwoWOneAtInput 6) (hcat : SLmCatalogueClausesAt 5) (hdet : SLmEvenTypeDetAt 5)
    (hstd : LSixNOneStandardInput) (hlift : LSixFieldNOneLiftInput)
    (hswap : LSixSwapNOneInput) : LinearTwoSwapRowAtInput 6 :=
  linearTwoSwapRowAtInput_six_of hW hcat hdet hstd (lSixFieldNOneExclusionInput_of_lift hlift) hswap

end CFSG.SeitzReduction.LinearPilot
