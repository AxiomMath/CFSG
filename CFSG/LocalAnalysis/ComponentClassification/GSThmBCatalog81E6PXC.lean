module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXA
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerComp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Small

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211X

open CFSG Subgroup Matrix CFSG.ComponentClassification.UnbalancedLayer P211
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def CompOrd (Q : ℕ → Prop) (G : Type*) [Group G] : Prop :=
  ∀ L : Subgroup G, IsComponent L → Q (Nat.card (L ⧸ center L))

variable {X : Type} [Group X] {Q : ℕ → Prop}

theorem card_centerQuotient_congr {L M : Type*} [Group L] [Group M] (e : L ≃* M) :
    Nat.card (L ⧸ center L) = Nat.card (M ⧸ center M) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv

theorem CompOrd.of_mulEquiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H)
    (h : CompOrd Q H) : CompOrd Q G := by
  intro L hL
  have := h _ (LocalCores.isComponent_map_mulEquiv Φ hL)
  rwa [← card_centerQuotient_congr (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)] at this

theorem CompOrd.prod {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂]
    (h₁ : CompOrd Q G₁) (h₂ : CompOrd Q G₂) : CompOrd Q (G₁ × G₂) := by
  intro L hL
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      hL with h2 | h1
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component (MulEquiv.refl _) hL h2
    rw [card_centerQuotient_congr (MonoidHom.ofInjective hρi)]
    exact h₁ _ hρc
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component MulEquiv.prodComm hL h1
    rw [card_centerQuotient_congr (MonoidHom.ofInjective hρi)]
    exact h₂ _ hρc

theorem card_psl_eq_ordA {k : Type} [Field k] [Finite k] {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (SpecialLinearGroup (Fin n) k ⧸ center (SpecialLinearGroup (Fin n) k)) =
      Open.ordA (n - 1) (Nat.card k) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := k) hn
  rw [← Nat.card_congr
    (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n k).toEquiv] at h
  rw [show (SpecialLinearGroup (Fin n) k ⧸ center (SpecialLinearGroup (Fin n) k)) =
    ProjectiveSpecialLinearGroup (Fin n) k from rfl, h, Open.ordA, Nat.sub_add_cancel hn,
    mul_comm (n - 1) n]

theorem CompOrd.GL {k : Type} [Field k] [Finite k] {n : ℕ} (hn : 1 ≤ n)
    (hQ : 2 ≤ n → Q (Open.ordA (n - 1) (Nat.card k))) : CompOrd Q (GL (Fin n) k) := by
  intro L hL
  by_cases hsmall : n = 1 ∨ n = 2 ∧ (Nat.card k = 2 ∨ Nat.card k = 3)
  · have := CatalogueBGeneralLinear.generalLinear_small_solvable n k hsmall
    exact absurd hL (CatLeafProof.OddInner.not_isComponent_of_isSolvable L)
  obtain ⟨hn2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters n k hn hsmall
  have : Group.IsPerfect L := hL.1.1
  have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
  obtain rfl := CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange n k hn2 h22 h23
    L hL.2
  rw [← card_centerQuotient_congr (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective),
    card_psl_eq_ordA hn]
  exact hQ hn2

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ u v : G, u * v ≠ v * u) : center G = ⊥ := by
  rcases (center G).normal_of_characteristic.eq_bot_or_eq_top with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨u, v, huv⟩ := h
    exact huv ((mem_center_iff.mp (h1 ▸ mem_top v : v ∈ center G)) u)

theorem v2_centerQuotient_eq [Finite X] {K : Subgroup X}
    (hK : center (K ⧸ pPrimeCore 2 K) = ⊥) :
    padicValNat 2 (Nat.card (K ⧸ center K)) =
      padicValNat 2 (Nat.card (K ⧸ pPrimeCore 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZO : center K ≤ pPrimeCore 2 K := by
    intro z hz
    have h1 : (QuotientGroup.mk' (pPrimeCore 2 K)) z ∈ center (K ⧸ pPrimeCore 2 K) :=
      map_center_le_center (QuotientGroup.mk'_surjective _) (mem_map_of_mem _ hz)
    rw [hK, mem_bot] at h1
    exact (QuotientGroup.eq_one_iff z).mp h1
  have hodd : ¬ 2 ∣ Nat.card (center K) := fun h2 =>
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card).not_two_dvd_nat
      (h2.trans (Subgroup.card_dvd_of_le hZO))
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  rw [← v2_card_quot, hc, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', v2_odd' hodd,
    add_zero]

theorem exists_fixed_component [Finite X] (hC : centralizer (generalizedFitting X : Set X) = ⊥)
    (hQS : CatLeaf.FixedTwoComponentsQuasisimple ↥(generalizedFitting X)) {b : X}
    (hb : b * b = 1) (hb1 : b ≠ 1) {K : Subgroup X} (hKC : K ≤ centralizer ({b} : Set X))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set X))))
    (hKF : K ≤ generalizedFitting X) (hKs : center (K ⧸ pPrimeCore 2 K) = ⊥) :
    ∃ β : MulAut ↥(generalizedFitting X), orderOf β = 2 ∧
      ∃ L : Subgroup (fixedSubgroup β), IsComponent L ∧
        padicValNat 2 (Nat.card (L ⧸ center L)) =
          padicValNat 2 (Nat.card (K ⧸ pPrimeCore 2 K)) := by
  classical
  have : (generalizedFitting X).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := X)).2
  set F := generalizedFitting X with hFdef
  set β : MulAut ↥F := MulAut.conjNormal b with hβ
  have hβ2 : β * β = 1 := by rw [hβ, ← map_mul, hb, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    exact hb1 (conjNormal_injective' F hC (h.trans (map_one _).symm))
  have hfix : fixedSubgroup β = (centralizer ({b} : Set X)).subgroupOf F := by
    ext x
    rw [mem_subgroupOf, mem_centralizer_iff]
    change β x = x ↔ _
    constructor
    · intro h y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h1 := congrArg Subtype.val h
      simp only [hβ, MulAut.conjNormal_apply] at h1
      calc b * (x : X) = b * (x : X) * b⁻¹ * b := by group
        _ = x * b := by rw [h1]
    · intro h
      apply Subtype.ext
      simp only [hβ, MulAut.conjNormal_apply]
      rw [h b rfl, mul_inv_cancel_right]
  have hK₀C : K.subgroupOf F ≤ (centralizer ({b} : Set X)).subgroupOf F :=
    fun x hx => hKC hx
  have hK₀ : IsPComponent 2 ((K.subgroupOf F).subgroupOf (fixedSubgroup β)) := by
    rw [hfix, ← CatFactsSp4.isPComponent_map_subgroupOf_iff 2 F.subtype F.subtype_injective hK₀C,
      subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hKF]
    exact CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hKC hKF) inf_le_left hK
  have hq := hQS β hβ2 hβ1 _ hK₀
  obtain ⟨-, -, hsub, -⟩ := hK₀
  refine ⟨β, orderOf_eq_prime (by rw [pow_two]; exact hβ2) hβ1, _, ⟨hq, hsub⟩, ?_⟩
  have hle : K.subgroupOf F ≤ fixedSubgroup β := hfix ▸ hK₀C
  rw [card_centerQuotient_congr ((subgroupOfEquivOfLe hle).trans (subgroupOfEquivOfLe hKF)),
    v2_centerQuotient_eq hKs]

theorem center_socle_eq_bot [Finite X] {K : Subgroup X} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hKt : IsSec8Socle (K ⧸ pPrimeCore 2 K) p f) :
    center (K ⧸ pPrimeCore 2 K) = ⊥ := by
  obtain ⟨hs, hna⟩ := cfSec8Simple (K ⧸ pPrimeCore 2 K) p f hp hp2 hf hKt
  exact center_eq_bot_of_simple hna

end P211X

end CFSG.ComponentClassification.GSThmB
