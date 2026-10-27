module

public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitCycOddJ
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoDefs
import CFSG.LocalAnalysis.OddStandard.ChildL34
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.SolAltLit

open CFSG Subgroup

@[expose] def AltStdCyclicOddTwoFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), OddStandard.StandardSetting G L →
    ∀ n : ℕ, Odd n → 9 ≤ n → ∀ θ : L ≃* alternatingGroup (Fin n),
      (∀ e : L, orderOf e = 2 →
        ((θ e : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).support.card = 4 →
          CFSG.oddCore (centralizer ({(e : G)} : Set G)) = ⊥) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) → False

namespace SCATTwo

theorem oddCore_eq_pPrimeCore (X : Type*) [Group X] : CFSG.oddCore X = pPrimeCore 2 X := by
  unfold CFSG.oddCore pPrimeCore
  congr 1
  ext N
  exact and_congr_right fun _ => Nat.coprime_two_left.symm

def centralizerConjEquiv {X : Type*} [Group X] (x j : X) :
    centralizer ({j⁻¹ * x * j} : Set X) ≃* centralizer ({x} : Set X) where
  toFun c := ⟨j * c * j⁻¹, by
    rw [mem_centralizer_singleton_iff]
    have hc := mem_centralizer_singleton_iff.mp c.2
    calc j * c * j⁻¹ * x = j * (c * (j⁻¹ * x * j)) * j⁻¹ := by group
      _ = j * ((j⁻¹ * x * j) * c) * j⁻¹ := by rw [hc]
      _ = x * (j * c * j⁻¹) := by group⟩
  invFun c := ⟨j⁻¹ * c * j, by
    rw [mem_centralizer_singleton_iff]
    have hc := mem_centralizer_singleton_iff.mp c.2
    calc j⁻¹ * c * j * (j⁻¹ * x * j) = j⁻¹ * (c * x) * j := by group
      _ = j⁻¹ * (x * c) * j := by rw [hc]
      _ = j⁻¹ * x * j * (j⁻¹ * c * j) := by group⟩
  left_inv c := Subtype.ext (by dsimp only; group)
  right_inv c := Subtype.ext (by dsimp only; group)
  map_mul' a b := Subtype.ext
    (show j * ((a : X) * b) * j⁻¹ = (j * a * j⁻¹) * (j * b * j⁻¹) by group)

theorem pPrimeCore_eq_bot_of_theta {X : Type*} [Group X] [Finite X] {E : Subgroup X} {b : X}
    (hb : b ∈ E) (hθ : thetaFunctor E b = ⊥) :
    pPrimeCore 2 (centralizer ({b} : Set X)) = ⊥ := by
  set A : Subgroup X :=
    (pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype with hAdef
  set B : Subgroup X :=
    (pPrimeCore 2 (centralizer (E : Set X))).map (centralizer (E : Set X)).subtype with hBdef
  have h1 : ⁅A, E⁆ = ⊥ := le_bot_iff.1 (hθ ▸ le_sup_left)
  have h2 : A ⊓ B = ⊥ := le_bot_iff.1 (hθ ▸ le_sup_right)
  have hAE : A ≤ centralizer (E : Set X) := commutator_eq_bot_iff_le_centralizer.1 h1
  have hEb : centralizer (E : Set X) ≤ centralizer ({b} : Set X) := fun c hc =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc b hb).symm
  have hAn : (A.subgroupOf (centralizer (E : Set X))).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [mem_subgroupOf] at ha ⊢
    obtain ⟨m, hm, hma⟩ := ha
    let g' : centralizer ({b} : Set X) := ⟨(g : X), hEb g.2⟩
    have hgm : g' * m * g'⁻¹ ∈ pPrimeCore 2 (centralizer ({b} : Set X)) :=
      pPrimeCore_normal.conj_mem m hm g'
    refine ⟨g' * m * g'⁻¹, hgm, ?_⟩
    rw [map_mul, map_mul, map_inv, hma]
    rfl
  have hAc : Nat.Coprime 2 (Nat.card (A.subgroupOf (centralizer (E : Set X)))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAE).toEquiv, hAdef,
      card_map_of_injective (centralizer ({b} : Set X)).subtype_injective]
    exact pPrimeCore_coprime_card
  have hAB : A ≤ B := by
    intro a ha
    have hle : A.subgroupOf (centralizer (E : Set X)) ≤ pPrimeCore 2 (centralizer (E : Set X)) :=
      le_sSup ⟨hAn, hAc⟩
    exact ⟨⟨a, hAE ha⟩, hle (mem_subgroupOf.mpr ha), rfl⟩
  have hA : A = ⊥ := by rw [← inf_eq_left.mpr hAB, h2]
  exact (map_eq_bot_iff_of_injective _ (centralizer ({b} : Set X)).subtype_injective).1 hA

theorem support_card_eq_four {n : ℕ} {σ : alternatingGroup (Fin n)} (h2 : orderOf σ = 2)
    {D : Finset (Fin n)} (hD : D.card = 4) (hfix : ∀ ω ∉ D, (σ : Equiv.Perm (Fin n)) ω = ω) :
    (σ : Equiv.Perm (Fin n)).support.card = 4 := by
  have h2' : orderOf (σ : Equiv.Perm (Fin n)) = 2 := by rw [Subgroup.orderOf_coe]; exact h2
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (h2' ▸ Nat.prime_two)
  have hsum := Equiv.Perm.sum_cycleType (σ : Equiv.Perm (Fin n))
  rw [hk, h2', Multiset.sum_replicate, smul_eq_mul] at hsum
  have hsign := Equiv.Perm.sign_of_cycleType (σ : Equiv.Perm (Fin n))
  rw [hk, h2', Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    Equiv.Perm.mem_alternatingGroup.mp σ.2] at hsign
  have hle : (σ : Equiv.Perm (Fin n)).support.card ≤ 4 := by
    rw [← hD]
    refine Finset.card_le_card fun ω hω => ?_
    by_contra h
    exact (Equiv.Perm.mem_support.mp hω) (hfix ω h)
  have heven : Even ((k + 1) * 2 + (k + 1)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  rw [Nat.even_iff] at heven
  omega

theorem cycleType_eq_of_support_four {n : ℕ} {σ : Equiv.Perm (Fin n)} (h2 : orderOf σ = 2)
    (h4 : σ.support.card = 4) : σ.cycleType = Multiset.replicate 2 2 := by
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (h2 ▸ Nat.prime_two)
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hk, h2, Multiset.sum_replicate, smul_eq_mul, h4] at hsum
  rw [hk, h2]
  congr 1
  omega

theorem isConj_of_support_four {n : ℕ} (hn : 6 ≤ n) {σ τ : alternatingGroup (Fin n)}
    (hσ2 : orderOf σ = 2) (hτ2 : orderOf τ = 2)
    (hσ4 : (σ : Equiv.Perm (Fin n)).support.card = 4)
    (hτ4 : (τ : Equiv.Perm (Fin n)).support.card = 4) : IsConj σ τ := by
  refine alternatingGroup.isConj_of ?_ (by rw [hσ4, Fintype.card_fin]; omega)
  rw [Equiv.Perm.isConj_iff_cycleType_eq,
    cycleType_eq_of_support_four (by rw [Subgroup.orderOf_coe]; exact hσ2) hσ4,
    cycleType_eq_of_support_four (by rw [Subgroup.orderOf_coe]; exact hτ2) hτ4]

theorem mul_self_eq_one_kleinFour (a : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    a * a = 1 := by
  revert a
  decide

theorem fourPointBalance_of_one {X : Type} [Group X] [Finite X]
    {K : Subgroup X} {n : ℕ} (hn : 6 ≤ n)
    {θ : K ≃* alternatingGroup (Fin n)} {b : K}
    (hb2 : orderOf b = 2)
    (hb4 : ((θ b : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).support.card = 4)
    (h0 : CFSG.oddCore (centralizer ({(b : X)} : Set X)) = ⊥) :
    CFSG.OddStandard.AltStdCycTwo.FourPointBalance K θ := by
  intro x hx2 hx4
  have hθx2 : orderOf (θ x) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hx2
  have hθb2 : orderOf (θ b) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hb2
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_support_four (by omega) hθx2 hθb2 hx4 hb4)
  set j : K := θ.symm c with hjdef
  have hj : j * x * j⁻¹ = b := θ.injective (by
    rw [map_mul, map_mul, map_inv, hjdef, MulEquiv.apply_symm_apply, hc])
  have hxb : (x : X) = (j : X)⁻¹ * b * (j : X) := by
    have h1 := congrArg Subtype.val hj
    simp only [coe_mul, coe_inv] at h1
    rw [← h1]
    group
  have h0p : pPrimeCore 2 (centralizer ({(b : X)} : Set X)) = ⊥ := by
    rw [← oddCore_eq_pPrimeCore]
    exact h0
  rw [oddCore_eq_pPrimeCore, hxb]
  have hmap := pPrimeCore_map_iso 2 (centralizerConjEquiv (b : X) (j : X))
  rw [h0p] at hmap
  exact (map_eq_bot_iff_of_injective _ (centralizerConjEquiv (b : X) (j : X)).injective).1 hmap

theorem exists_iso_oddCore_eq_bot_of_pair {X : Type} [Group X] [Finite X] {t : X}
    {J : Subgroup X} {n : ℕ} (hn : 9 ≤ n) (hpair : SignalizerTrivialPair t J n)
    (hJ : Nonempty (J ≃* alternatingGroup (Fin n))) :
    ∃ θ : J ≃* alternatingGroup (Fin n), ∀ x : J, orderOf x = 2 →
      ((θ x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).support.card = 4 →
        CFSG.oddCore (centralizer ({(x : X)} : Set X)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨ht, hJC, -, -⟩, e, E, hEJ, ⟨eE⟩, ⟨D, hD, hDfix⟩, hθ⟩ := hpair
  obtain ⟨θJ⟩ := hJ
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using (show 5 ≤ n by omega))
  have : IsSimpleGroup J := θJ.isSimpleGroup
  have hJ2 : 2 ∣ Nat.card J := by
    rw [Nat.card_congr θJ.toEquiv]
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have h1 : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
      rw [Nat.card_eq_fintype_card, two_mul_card_alternatingGroup, Fintype.card_perm,
        Fintype.card_fin]
    have h4 : 2 * 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    rw [← h1] at h4
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
  have hOJ : pPrimeCore 2 J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 J) with h | h
    · exact h
    · exfalso
      have hcop := pPrimeCore_coprime_card (p := 2) (G := J)
      rw [h, card_top] at hcop
      exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) (dvd_refl 2) hJ2) hcop
  let q : J ≃* J ⧸ pPrimeCore 2 J := MulEquiv.ofBijective (QuotientGroup.mk' (pPrimeCore 2 J))
    ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk']; exact hOJ),
      QuotientGroup.mk'_surjective _⟩
  let θ : J ≃* alternatingGroup (Fin n) := q.trans e
  refine ⟨θ, fun x hx2 hx4 => ?_⟩
  have htE : t ∈ centralizer (E : Set X) :=
    mem_centralizer_iff.2 fun y hy => mem_centralizer_singleton_iff.1 (hJC (hEJ hy))
  have htK : t ∈ UnbalancedLayer.coreActionKernel J := by
    refine ⟨centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun j hj => mem_centralizer_singleton_iff.1 (hJC hj)),
      fun j hj => ?_⟩
    have hc := mem_centralizer_singleton_iff.1 (hJC hj)
    have h1 : j⁻¹ * t⁻¹ * j * t = 1 := by
      calc j⁻¹ * t⁻¹ * j * t = j⁻¹ * t⁻¹ * (j * t) := by group
        _ = j⁻¹ * t⁻¹ * (t * j) := by rw [hc]
        _ = 1 := by group
    rw [h1]
    exact one_mem _
  have htJ : t ∉ J := not_mem_of_le_centralizer (by omega) e ht hJC
  have hE4 : Nat.card E = 4 := by
    rw [Nat.card_congr eE.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  obtain ⟨e₀, he₀E, he₀1'⟩ := (bot_or_exists_ne_one E).resolve_left fun h => by
    rw [h, card_bot] at hE4
    omega
  have he₀2 : e₀ * e₀ = 1 := by
    have h1 : eE (⟨e₀, he₀E⟩ * ⟨e₀, he₀E⟩) = 1 := by rw [map_mul]; exact mul_self_eq_one_kleinFour _
    rw [map_eq_one_iff eE eE.injective] at h1
    exact congrArg Subtype.val h1
  have h0 : pPrimeCore 2 (centralizer ({e₀} : Set X)) = ⊥ :=
    pPrimeCore_eq_bot_of_theta he₀E (hθ t ht htE htK htJ e₀ (mem_sup_left he₀E) he₀1')
  set e₀' : J := ⟨e₀, hEJ he₀E⟩ with he₀'def
  have he₀'2 : orderOf e₀' = 2 := orderOf_eq_prime (by
    rw [pow_two]
    exact Subtype.ext he₀2) (fun h => he₀1' (congrArg Subtype.val h))
  have hθ2 : orderOf (θ e₀') = 2 := by rw [MulEquiv.orderOf_eq]; exact he₀'2
  have hθ4 : ((θ e₀' : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).support.card = 4 :=
    support_card_eq_four hθ2 hD (hDfix e₀' he₀E)
  have h0odd : CFSG.oddCore (centralizer ({(e₀ : X)} : Set X)) = ⊥ := by
    rw [oddCore_eq_pPrimeCore]
    exact h0
  exact fourPointBalance_of_one (by omega) he₀'2 hθ4 h0odd x hx2 hx4

end SCATTwo

theorem altStdCyclicOddJ_of_scatTwo (h : AltStdCyclicOddTwoFalse) : AltStdCyclicOddJ := by
  intro G _ _ _ hnonab hK hz hU t J n hno hn hmax hpair hJ hJiso S hcyc
  have hS : OddStandard.StandardSetting G J :=
    ⟨inferInstance, hnonab, hK, OddStandard.standardComponentIsStandard_of_cfsgStandard hJ⟩
  obtain ⟨θ, hθ⟩ := SCATTwo.exists_iso_oddCore_eq_bot_of_pair hn hpair hJiso
  exact h G J hS n hno hn θ hθ S hcyc

end CFSG.ComponentClassification.SolAltLit
