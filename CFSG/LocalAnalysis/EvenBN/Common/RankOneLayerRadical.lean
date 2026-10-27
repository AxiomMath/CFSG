module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialClosuresExact
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.EvenBN.Common.TwoElementary
import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusThree
import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusFour
import CFSG.LocalAnalysis.EvenBN.Common.ProductClosure
import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LocalAnalysis.EvenBN.Common.SL2Torus

public section

namespace CFSG.LocalAnalysis.EvenBN.Common.RankOneLayerRadical

open Subgroup CFSG.Blueprint
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer
  (ExactClosure ClosureSelection SmallSurvivorsNoElementary closure_layer_selection
    exactClosure_of_selection)
open scoped MatrixGroups

section NormalClosure

variable {G : Type*} [Group G]

@[expose] def normalClosureInNormalizer (X Y : Subgroup G) : Subgroup G :=
  closure {x : G | ∃ g ∈ normalizer (X : Set G), ∃ y ∈ Y ⊔ X, x = g⁻¹ * y * g}

theorem sup_le_normalClosureInNormalizer (X Y : Subgroup G) :
    Y ⊔ X ≤ normalClosureInNormalizer X Y := fun y hy =>
  subset_closure ⟨1, one_mem _, y, hy, by simp⟩

theorem normalClosureInNormalizer_le_normalizer {X Y : Subgroup G}
    (hY : Y ≤ normalizer (X : Set G)) :
    normalClosureInNormalizer X Y ≤ normalizer (X : Set G) := by
  rw [normalClosureInNormalizer, closure_le]
  rintro _ ⟨g, hg, y, hy, rfl⟩
  exact mul_mem (mul_mem (inv_mem hg) (sup_le hY le_normalizer hy)) hg

theorem normal_subgroupOf_normalClosureInNormalizer {X Y : Subgroup G}
    (hY : Y ≤ normalizer (X : Set G)) :
    ((normalClosureInNormalizer X Y).subgroupOf (normalizer (X : Set G))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  have key : ∀ x ∈ normalClosureInNormalizer X Y, (g : G) * x * (g : G)⁻¹ ∈
      normalClosureInNormalizer X Y := by
    intro x hx
    refine closure_induction (p := fun x _ => (g : G) * x * (g : G)⁻¹ ∈
      normalClosureInNormalizer X Y) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨g', hg', y, hy, rfl⟩
      refine subset_closure ⟨g' * (g : G)⁻¹, mul_mem hg' (inv_mem g.2), y, hy, ?_⟩
      group
    · simp
    · intro x y _ _ hx hy
      have := mul_mem hx hy
      rwa [show (g : G) * x * (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) = (g : G) * (x * y) *
        (g : G)⁻¹ by group] at this
    · intro x _ hx
      have := inv_mem hx
      rwa [show ((g : G) * x * (g : G)⁻¹)⁻¹ = (g : G) * x⁻¹ * (g : G)⁻¹ by group] at this
  exact key _ hn

theorem barSub_normalClosureInNormalizer {G : Type} [Group G] {X Y : Subgroup G}
    (hY : Y ≤ normalizer (X : Set G)) :
    barSub X (normalClosureInNormalizer X Y) = normalClosure (barSub X Y : Set (BarM X)) :=
  Sp4.BothTrivialRankOne.barSub_eq_normalClosure hY
    (normal_subgroupOf_normalClosureInNormalizer hY) rfl

end NormalClosure

section Involution

variable {G : Type} [Group G]

theorem mem_sup_zpowers_iff_of_involution {A : Subgroup G} {t : G} (htt : t * t = 1)
    (htA : t ∈ normalizer (A : Set G)) {x : G} :
    x ∈ A ⊔ zpowers t ↔ x ∈ A ∨ ∃ a ∈ A, x = a * t := by
  constructor
  · intro hx
    obtain ⟨a, ha, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htA) x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [show m + m = 2 * m by ring, zpow_mul, zpow_two, htt, one_zpow, mul_one]
      exact ha
    · right
      refine ⟨a, ha, ?_⟩
      rw [zpow_add_one, zpow_mul, zpow_two, htt, one_zpow, one_mul]
  · rintro (hx | ⟨a, ha, rfl⟩)
    · exact mem_sup_left hx
    · exact mul_mem (mem_sup_left ha) (mem_sup_right (mem_zpowers t))

theorem centralizer_barMap_eq {X : Subgroup G} {t : G} (ht : t ∈ normalizer (X : Set G))
    (htX : t ∉ X) (ht2 : t * t = 1) :
    centralizer ({barMap X ⟨t, ht⟩} : Set (BarM X)) =
      barSub X (normalizer ((X ⊔ zpowers t : Subgroup G) : Set G)) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set C : Subgroup G := X ⊔ zpowers t with hC
  have hXC : X ≤ normalizer (C : Set G) := le_sup_left.trans le_normalizer
  have htC : t ∈ C := mem_sup_right (mem_zpowers t)
  have hconj : ∀ k : G, k ∈ normalizer (X : Set G) → k * t * k⁻¹ ∈ C → ∀ c ∈ C,
      k * c * k⁻¹ ∈ C := by
    intro k hk hkt c hc
    rcases (mem_sup_zpowers_iff_of_involution ht2 ht).1 hc with hcX | ⟨a, ha, rfl⟩
    · exact mem_sup_left ((mem_normalizer_iff.1 hk c).1 hcX)
    · have e : k * (a * t) * k⁻¹ = (k * a * k⁻¹) * (k * t * k⁻¹) := by group
      rw [e]
      exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hk a).1 ha)) hkt
  ext y
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (X.subgroupOf (normalizer (X : Set G))) y
  have hy : y = barMap X g := hg.symm
  rw [hy, mem_centralizer_singleton_iff,
    CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff hXC g,
    ← map_mul, ← map_mul,
    CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_iff]
  have hgX : ∀ x : G, x ∈ X ↔ (g : G) * x * (g : G)⁻¹ ∈ X := fun x => mem_normalizer_iff.1 g.2 x
  have hgiX : ∀ x : G, x ∈ X ↔ (g : G)⁻¹ * x * (g : G)⁻¹⁻¹ ∈ X := fun x =>
    mem_normalizer_iff.1 (inv_mem g.2) x
  have e1 : (((g * ⟨t, ht⟩ : normalizer (X : Set G)) : G))⁻¹ *
      ((⟨t, ht⟩ * g : normalizer (X : Set G)) : G) = t * (g : G)⁻¹ * t * (g : G) := by
    change ((g : G) * t)⁻¹ * (t * (g : G)) = _
    rw [mul_inv_rev, htinv]
    group
  rw [e1]
  constructor
  · intro hu
    have e2 : t * (t * (g : G)⁻¹ * t * (g : G)) = (g : G)⁻¹ * t * (g : G) := by
      calc t * (t * (g : G)⁻¹ * t * (g : G)) = (t * t) * (g : G)⁻¹ * t * (g : G) := by group
        _ = _ := by rw [ht2, one_mul]
    have hgit : (g : G)⁻¹ * t * (g : G) ∈ C := by
      refine (mem_sup_zpowers_iff_of_involution ht2 ht).2 (Or.inr
        ⟨t * (t * (g : G)⁻¹ * t * (g : G)) * t⁻¹, (mem_normalizer_iff.1 ht _).1 hu, ?_⟩)
      rw [← e2]
      group
    have hgt : (g : G) * t * (g : G)⁻¹ ∈ C := by
      have e3 : (g : G) * t * (g : G)⁻¹ =
          t * ((g : G) * (t * (g : G)⁻¹ * t * (g : G))⁻¹ * (g : G)⁻¹) := by
        have : (g : G) * (t * (g : G)⁻¹ * t * (g : G))⁻¹ * (g : G)⁻¹ =
            t⁻¹ * (g : G) * t⁻¹ * (g : G)⁻¹ := by group
        rw [this, htinv]
        calc (g : G) * t * (g : G)⁻¹ = (t * t) * (g : G) * t * (g : G)⁻¹ := by
              rw [ht2, one_mul]
          _ = _ := by group
      have hb : (g : G) * (t * (g : G)⁻¹ * t * (g : G))⁻¹ * (g : G)⁻¹ ∈ X :=
        (hgX _).1 (inv_mem hu)
      refine (mem_sup_zpowers_iff_of_involution ht2 ht).2 (Or.inr
        ⟨t * ((g : G) * (t * (g : G)⁻¹ * t * (g : G))⁻¹ * (g : G)⁻¹) * t⁻¹,
          (mem_normalizer_iff.1 ht _).1 hb, ?_⟩)
      rw [e3]
      group
    refine mem_normalizer_iff.2 fun h => ⟨fun hh => hconj g g.2 hgt h hh, fun hh => ?_⟩
    have := hconj (g : G)⁻¹ (inv_mem g.2) (by rwa [inv_inv]) _ hh
    rwa [show (g : G)⁻¹ * ((g : G) * h * (g : G)⁻¹) * (g : G)⁻¹⁻¹ = h by group] at this
  · intro hgC
    have h1 : (g : G)⁻¹ * t * (g : G)⁻¹⁻¹ ∈ C := (mem_normalizer_iff.1 (inv_mem hgC) t).1 htC
    rcases (mem_sup_zpowers_iff_of_involution ht2 ht).1 h1 with hX | ⟨a, ha, e⟩
    · exact absurd ((hgiX t).2 hX) htX
    · rw [inv_inv] at e
      have e4 : t * (g : G)⁻¹ * t * (g : G) = t * a * t⁻¹ := by
        calc t * (g : G)⁻¹ * t * (g : G) = t * ((g : G)⁻¹ * t * (g : G)) := by group
          _ = t * (a * t) := by rw [e]
          _ = t * a * t⁻¹ := by rw [htinv]; group
      rw [e4]
      exact (mem_normalizer_iff.1 ht a).1 ha

end Involution

section Data

variable {M : Type} [Group M]

@[expose] def commutatorWith (V : Subgroup M) (τ : M) : Subgroup M :=
  closure {x | ∃ v ∈ V, x = v⁻¹ * (τ⁻¹ * v * τ)}

structure RankOneData (A : Subgroup M) {k : Type} [Field k] (α : A ≃* SL(2, k)) (τ : M)
    (V : Subgroup M) (n : ℕ) : Prop where
  kGroup : CFSG.SectionRank.IsKGroupCat M
  two_le : 2 ≤ n
  card_k : Nat.card k = 2 ^ n
  orderOf_tau : orderOf τ = 2
  le_centralizer : A ≤ centralizer ({τ} : Set M)
  normal_in_centralizer : (A.subgroupOf (centralizer ({τ} : Set M))).Normal
  sylow : ∃ S : Sylow 2 ↥(centralizer (A : Set M) ⊓ centralizer ({τ} : Set M)),
    (S : Subgroup _).map (centralizer (A : Set M) ⊓ centralizer ({τ} : Set M)).subtype =
      zpowers τ
  sq_eq_one : ∀ v ∈ V, v * v = 1
  card_V : Nat.card V = (2 ^ n) ^ 2
  le_normalClosure : V ≤ normalClosure (A : Set M)
  tau_mem_normalizer : τ ∈ normalizer (V : Set M)
  commutatorWith_ne_bot : commutatorWith V τ ≠ ⊥
  commutatorWith_le : commutatorWith V τ ≤ A

end Data

theorem RankOneData.exactClosure
    {M : Type} [Group M] [Finite M] {A : Subgroup M} {k : Type}
    [Field k] {α : A ≃* SL(2, k)} {τ : M} {V : Subgroup M} {n : ℕ}
    (hsel : GMSK.FixedRootSelector fun D _ => Catalog D) (hsmall : SmallSurvivorsNoElementary)
    (h : RankOneData A α τ V n) : ExactClosure A α τ V n := by
  classical
  have hk0 : Nat.card k ≠ 0 := by rw [h.card_k]; positivity
  have : Finite k := Nat.finite_of_card_ne_zero hk0
  have : Fintype k := Fintype.ofFinite k
  have hk : Fintype.card k = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact h.card_k
  have hcs := closure_layer_selection hsel hsmall h.kGroup h.two_le hk α h.orderOf_tau
    h.le_centralizer h.normal_in_centralizer h.sylow h.sq_eq_one h.card_V h.le_normalClosure
    h.tau_mem_normalizer
  have h2 : (2 : k) = 0 := GMSK.two_eq_zero_of_card (by have := h.two_le; omega) hk
  have hk4 : 4 ≤ Fintype.card k :=
    hk ▸ (Nat.pow_le_pow_right (by norm_num) h.two_le : 2 ^ 2 ≤ 2 ^ n)
  have : IsSimpleGroup SL(2, k) := GMSK.sl2_isSimpleGroup h2 hk4
  have : IsSimpleGroup A := α.isSimpleGroup
  have hnab : ∃ x y : A, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := k)
    exact ⟨α.symm x, α.symm y, fun e => hxy (by simpa using congrArg α e)⟩
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have hxy := h.sq_eq_one _ (mul_mem hx hy)
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h.sq_eq_one x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h.sq_eq_one y hy)
    calc x * y = y⁻¹ * x⁻¹ := by rw [← mul_inv_rev, inv_eq_of_mul_eq_one_right hxy]
      _ = y * x := by rw [hx', hy']
  have : CFSG.IsElementaryAbelian 2 V :=
    CFSG.IsElementaryAbelian.two_of_forall_mul_self hVcomm h.sq_eq_one
  obtain ⟨hperf, hcent, -⟩ :=
    ComponentInitial.elementary_involution_commutator_centralizes_odd_normal_core
      (L := normalClosure (A : Set M)) h.orderOf_tau hnab h.le_centralizer
      h.normal_in_centralizer h.tau_mem_normalizer h.commutatorWith_ne_bot h.commutatorWith_le rfl
  exact exactClosure_of_selection h.two_le hk α hcs hperf
    (hcent _ inferInstance (GMSK.odd_card_standardComponentOddCore M)) h.card_V
    h.le_normalClosure

section Generation

open CFSG.SL2MinimalFaithful

theorem prod_eq_top_of_diag {k : Type} [Field k] [Fintype k] {n : ℕ} (hn : 2 ≤ n)
    (hk : Fintype.card k = 2 ^ n) {T V : Subgroup (SL(2, k) × SL(2, k))}
    (hdiag : ∀ g : SL(2, k), (g, g) ∈ T) (hV : IsPGroup 2 V)
    (hVcard : Nat.card V = (2 ^ n) ^ 2) (hVT : V ≤ T) : T = ⊤ := by
  classical
  have h2 : (2 : k) = 0 := CFSG.LocalAnalysis.EvenBN.GMSK.two_eq_zero_of_card (by omega) hk
  have hk4 : 4 ≤ Fintype.card k := hk ▸ (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  have : IsSimpleGroup SL(2, k) := CFSG.LocalAnalysis.EvenBN.GMSK.sl2_isSimpleGroup h2 hk4
  set H : Subgroup SL(2, k) := T.comap (MonoidHom.inl SL(2, k) SL(2, k)) with hH
  have hHn : H.Normal := by
    refine ⟨fun g hg x => ?_⟩
    have hg' : (g, (1 : SL(2, k))) ∈ T := hg
    have := mul_mem (mul_mem (hdiag x) hg') (inv_mem (hdiag x))
    show (x * g * x⁻¹, (1 : SL(2, k))) ∈ T
    simpa using this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with hHbot | hHtop
  · exfalso
    have hdiagV : ∀ v ∈ V, v.1 = v.2 := by
      intro v hv
      have h1 : (v.1 * v.2⁻¹, (1 : SL(2, k))) ∈ T := by
        have := mul_mem (hVT hv) (inv_mem (hdiag v.2))
        have e : v * (v.2, v.2)⁻¹ = (v.1 * v.2⁻¹, (1 : SL(2, k))) :=
          Prod.ext (by simp) (by simp)
        rwa [e] at this
      have : v.1 * v.2⁻¹ ∈ H := h1
      rw [hHbot, mem_bot] at this
      exact mul_inv_eq_one.1 this
    have hinj : Function.Injective ((MonoidHom.fst SL(2, k) SL(2, k)).domRestrict V) := by
      intro v w hvw
      have h1 : (v : SL(2, k) × SL(2, k)).1 = (w : SL(2, k) × SL(2, k)).1 := hvw
      apply Subtype.ext
      apply Prod.ext h1
      rw [← hdiagV _ v.2, ← hdiagV _ w.2]
      exact h1
    have hcard : Nat.card (V.map (MonoidHom.fst SL(2, k) SL(2, k))) = (2 ^ n) ^ 2 := by
      rw [← hVcard, ← MonoidHom.domRestrict_range]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have hle := Common.card_le_of_isPGroup_SL2 (K := k) (f := n) (by omega) hk
      (hV.map (MonoidHom.fst SL(2, k) SL(2, k)))
    rw [hcard] at hle
    have h2n : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  · refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨a, b⟩ := v
    have h1 : (a * b⁻¹, (1 : SL(2, k))) ∈ T := by
      have : a * b⁻¹ ∈ H := hHtop ▸ mem_top _
      exact this
    have := mul_mem h1 (hdiag b)
    simpa using this

theorem exists_conj_unipotent_eq {k : Type} [Field k] (X : SL(2, k))
    (hX : (X : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (t' : k) :
    ∃ t : k, X * unipotent t * X⁻¹ = unipotent t' := by
  obtain ⟨a, b, c, d, hdet, rfl⟩ := Common.exists_eq_mkSL X
  have hc : c = 0 := by simpa [Common.coe_mkSL] using hX
  subst hc
  have ha : a ≠ 0 := by
    intro h0
    subst h0
    simp at hdet
  refine ⟨(a ^ 2)⁻¹ * t', Common.eq_of_coe_eq ?_⟩
  rw [Common.coe_mkSL_conj_unipotent, coe_unipotent]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  field_simp

theorem field_eq_top_of_frobenius {k : Type} [Field k] [Fintype k] [CharP k 2] {n : ℕ}
    (hk : Fintype.card k = (2 ^ n) ^ 2) {T V : Subgroup SL(2, k)}
    (hA : ∀ g : SL(2, k), (∀ i j, (g : Matrix (Fin 2) (Fin 2) k) i j ^ 2 ^ n =
      (g : Matrix (Fin 2) (Fin 2) k) i j) → g ∈ T)
    (hVcard : Nat.card V = Nat.card k) (hVT : V ≤ T)
    (hσ : ∀ v ∈ V, Matrix.SpecialLinearGroup.map (iterateFrobenius k 2 n) v ∈ V) : T = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hq : Nat.card k = 2 ^ (2 * n) := by
    rw [Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem Nat.prime_two hq hVcard
  have hVeq : V = (Common.upperSL k).map (MulAut.conj g).toMonoidHom := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨_, hu, rfl⟩
      obtain ⟨c, rfl⟩ := Common.mem_upperSL_iff.1 hu
      exact hg c
    · rw [hVcard, Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Common.card_upperSL]
  have hσ1 := hσ _ (hg 1)
  rw [hVeq] at hσ1
  obtain ⟨_, hu, hut⟩ := hσ1
  obtain ⟨t₀, rfl⟩ := Common.mem_upperSL_iff.1 hu
  obtain ⟨G, hG⟩ : ∃ G : SL(2, k), G = Matrix.SpecialLinearGroup.map (iterateFrobenius k 2 n) g :=
    ⟨_, rfl⟩
  have hGentry : ∀ i j, (G : Matrix (Fin 2) (Fin 2) k) i j =
      (g : Matrix (Fin 2) (Fin 2) k) i j ^ 2 ^ n := fun i j => by rw [hG]; rfl
  have hmapu : Matrix.SpecialLinearGroup.map (iterateFrobenius k 2 n) (unipotent (1 : k)) =
      unipotent 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_unipotent]
    all_goals first | rfl | simp [iterateFrobenius_def]
  have e1 : g * unipotent t₀ * g⁻¹ = G * unipotent 1 * G⁻¹ := by
    have h1 : (MulAut.conj g).toMonoidHom (unipotent t₀) = g * unipotent t₀ * g⁻¹ := rfl
    rw [← h1, hut, map_mul, map_mul, map_inv, hmapu, hG]
  obtain ⟨h, hh⟩ : ∃ h : SL(2, k), h = g⁻¹ * G := ⟨_, rfl⟩
  have e2 : h * unipotent 1 = unipotent t₀ * h := by
    rw [hh]
    calc (g⁻¹ * G) * unipotent 1 = g⁻¹ * (G * unipotent 1 * G⁻¹) * G := by group
      _ = g⁻¹ * (g * unipotent t₀ * g⁻¹) * G := by rw [e1]
      _ = unipotent t₀ * (g⁻¹ * G) := by group
  have hh10 : (h : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    have e3 := congrArg (fun X : SL(2, k) => (X : Matrix (Fin 2) (Fin 2) k) 1 1) e2
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      coe_unipotent] using e3
  have hGh : G = g * h := by rw [hh]; group
  have hp : (h : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0 := by
    have hdet := h.det_coe
    rw [Matrix.det_fin_two, hh10, mul_zero, sub_zero] at hdet
    exact left_ne_zero_of_mul_eq_one hdet
  have hcol : ∀ i : Fin 2, (g : Matrix (Fin 2) (Fin 2) k) i 0 ^ 2 ^ n =
      (g : Matrix (Fin 2) (Fin 2) k) i 0 * (h : Matrix (Fin 2) (Fin 2) k) 0 0 := by
    intro i
    have e4 := congrArg (fun X : SL(2, k) => (X : Matrix (Fin 2) (Fin 2) k) i 0) hGh
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hh10,
      mul_zero, add_zero, hGentry] at e4
    exact e4
  have hex : ∃ s : SL(2, k), s ∈ T ∧ ((s * g : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    by_cases hc0 : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
    · exact ⟨1, one_mem _, by simpa using hc0⟩
    · have hr : ((g : Matrix (Fin 2) (Fin 2) k) 0 0 / (g : Matrix (Fin 2) (Fin 2) k) 1 0) ^ 2 ^ n =
          (g : Matrix (Fin 2) (Fin 2) k) 0 0 / (g : Matrix (Fin 2) (Fin 2) k) 1 0 := by
        rw [div_pow, hcol 0, hcol 1, mul_div_mul_right _ _ hp]
      refine ⟨Common.mkSL 0 1 1 ((g : Matrix (Fin 2) (Fin 2) k) 0 0 /
        (g : Matrix (Fin 2) (Fin 2) k) 1 0) (by rw [zero_mul, one_mul, zero_sub, CharTwo.neg_eq]),
        hA _ ?_, ?_⟩
      · intro i j
        fin_cases i <;> fin_cases j <;> simp [Common.coe_mkSL, hr] <;> first | rfl | skip
      · simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
          Common.coe_mkSL]
        field_simp
        rw [one_add_one_eq_two, h2, mul_zero]
  obtain ⟨s, hsT, hs10⟩ := hex
  have hU : ∀ t' : k, unipotent t' ∈ T := by
    intro t'
    obtain ⟨t, ht⟩ := exists_conj_unipotent_eq (s * g) hs10 t'
    have hgt : g * unipotent t * g⁻¹ ∈ T := hVT (hg t)
    have := mul_mem (mul_mem hsT hgt) (inv_mem hsT)
    rw [← ht]
    convert this using 1
    group
  have hW : Common.weylSL k ∈ T := by
    refine hA _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Common.coe_weylSL]
  have hL : ∀ t' : k, Common.lowerUnipotent t' ∈ T := by
    intro t'
    have := mul_mem (mul_mem hW (hU t')) (inv_mem hW)
    rwa [Common.weylSL_conj_unipotent] at this
  refine eq_top_iff.2 ?_
  rw [← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := k), closure_le]
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact hU c
  · exact hL c

end Generation

theorem RankOneData.sup_eq {M : Type} [Group M] [Finite M] {A : Subgroup M} {k : Type}
    [Field k] {α : A ≃* SL(2, k)} {τ : M} {V : Subgroup M} {n : ℕ}
    (h : RankOneData A α τ V n) (hex : ExactClosure A α τ V n) :
    V ⊔ A = normalClosure (A : Set M) := by
  classical
  have hk0 : Nat.card k ≠ 0 := by rw [h.card_k]; positivity
  have : Finite k := Nat.finite_of_card_ne_zero hk0
  have : Fintype k := Fintype.ofFinite k
  have hk : Fintype.card k = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact h.card_k
  have hAN : A ≤ normalClosure (A : Set M) := fun a ha => subset_normalClosure ha
  set N := normalClosure (A : Set M) with hN
  obtain ⟨-, -, hVN, ⟨P, hP⟩, hxor⟩ := hex
  refine le_antisymm (sup_le hVN hAN) ?_
  set T : Subgroup N := (V ⊔ A).subgroupOf N with hT
  have hTA : ∀ x : N, (x : M) ∈ A → x ∈ T := fun x hx => mem_subgroupOf.2 (mem_sup_right hx)
  have hxV : ∀ x ∈ (P : Subgroup N), (x : M) ∈ V := by
    intro x hx
    rw [← hP]
    exact ⟨x, hx, rfl⟩
  have hPT : ∀ x ∈ (P : Subgroup N), x ∈ T := fun x hx => mem_subgroupOf.2 (mem_sup_left (hxV x hx))
  suffices hTtop : T = ⊤ by
    intro x hx
    have : (⟨x, hx⟩ : N) ∈ T := hTtop ▸ mem_top _
    exact mem_subgroupOf.1 this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hxor with ⟨hPr, -⟩ | ⟨hF, -⟩
  ·
    obtain ⟨ψ, hψA, -⟩ := hPr
    have : CharP k 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by have := h.two_le; omega) h.card_k
    have hdiag : ∀ g : SL(2, k), (g, g) ∈ T.map ψ.toMonoidHom := by
      intro g
      refine ⟨⟨((α.symm g : A) : M), hAN (α.symm g).2⟩, hTA _ (α.symm g).2, ?_⟩
      have := hψA (α.symm g) ⟨((α.symm g : A) : M), hAN (α.symm g).2⟩ rfl
      rw [MulEquiv.apply_symm_apply] at this
      exact this
    have hVcard : Nat.card ((P : Subgroup N).map ψ.toMonoidHom) = (2 ^ n) ^ 2 := by
      rw [Subgroup.card_map_of_injective ψ.injective, Common.card_sylow_two_eq_prod ψ P,
        h.card_k]
    have htop := prod_eq_top_of_diag h.two_le hk hdiag
      ((P.isPGroup').map ψ.toMonoidHom) hVcard
      (Subgroup.map_mono (fun x hx => hPT x hx))
    refine eq_top_iff.2 fun x _ => ?_
    have hx : ψ x ∈ T.map ψ.toMonoidHom := htop ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    exact (ψ.injective hyx) ▸ hy
  ·
    obtain ⟨k₂, hk₂F, hk₂Fin, hk₂, ψ, hψτ, hψA⟩ := hF
    have hk₂' : Nat.card k₂ = 2 ^ (2 * n) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
    have : CharP k₂ 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by have := h.two_le; omega) hk₂'
    have hVcard : Nat.card ((P : Subgroup N).map ψ.toMonoidHom) = Nat.card k₂ := by
      rw [Subgroup.card_map_of_injective ψ.injective, Common.card_sylow_two_eq ψ P]
    have hσ : ∀ v ∈ (P : Subgroup N).map ψ.toMonoidHom,
        Matrix.SpecialLinearGroup.map (iterateFrobenius k₂ 2 n) v ∈
          (P : Subgroup N).map ψ.toMonoidHom := by
      rintro _ ⟨x, hxP, rfl⟩
      have hyN : τ⁻¹ * (x : M) * τ ∈ N := by
        have := (normalClosure_normal (s := (A : Set M))).conj_mem (x : M) x.2 τ⁻¹
        simpa using this
      have hyV : τ⁻¹ * (x : M) * τ ∈ V := by
        have := (mem_normalizer_iff.1 (inv_mem h.tau_mem_normalizer) (x : M)).1 (hxV x hxP)
        simpa using this
      have hyP : (⟨τ⁻¹ * (x : M) * τ, hyN⟩ : N) ∈ (P : Subgroup N) := by
        rw [← hP] at hyV
        obtain ⟨y', hy'P, hy'⟩ := hyV
        have : y' = ⟨τ⁻¹ * (x : M) * τ, hyN⟩ := Subtype.ext hy'
        exact this ▸ hy'P
      refine ⟨_, hyP, ?_⟩
      have hσψ := hψτ x ⟨τ⁻¹ * (x : M) * τ, hyN⟩ rfl
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      exact hσψ
    have htop := field_eq_top_of_frobenius hk₂ (T := T.map ψ.toMonoidHom)
      (V := (P : Subgroup N).map ψ.toMonoidHom)
      (fun g hg => by
        obtain ⟨x, hx, rfl⟩ := (hψA g).2 hg
        exact ⟨x, hTA x hx, rfl⟩)
      hVcard (Subgroup.map_mono (fun x hx => hPT x hx)) hσ
    refine eq_top_iff.2 fun x _ => ?_
    have hx : ψ x ∈ T.map ψ.toMonoidHom := htop ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    exact (ψ.injective hyx) ▸ hy

theorem isSylowOf_normalClosureInNormalizer {G : Type} [Group G] [Finite G]
    {X Y P : Subgroup G} (hX : IsPGroup 2 X) (hXP : X ≤ P)
    (hPN : P ≤ normalizer (X : Set G)) (hY : Y ≤ normalizer (X : Set G))
    (hP : ∃ S : Sylow 2 (normalClosure (barSub X Y : Set (BarM X))),
      (S : Subgroup _).map (normalClosure (barSub X Y : Set (BarM X))).subtype = barSub X P) :
    CFSG.ABGLocalTools.IsSylowOf 2 P (normalClosureInNormalizer X Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalClosureInNormalizer X Y with hN
  have hXN : X ≤ N := le_trans le_sup_right (sup_le_normalClosureInNormalizer X Y)
  have hNN : N ≤ normalizer (X : Set G) := normalClosureInNormalizer_le_normalizer hY
  have hbar : barSub X N = normalClosure (barSub X Y : Set (BarM X)) :=
    barSub_normalClosureInNormalizer hY
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (barSub X P) (barSub X N) := by
    rw [hbar]
    exact hP
  have hPle : P ≤ N := by
    intro p hp
    have hpN : p ∈ normalizer (X : Set G) := hPN hp
    have h1 : barMap X ⟨p, hpN⟩ ∈ barSub X P := ⟨⟨p, hpN⟩, mem_subgroupOf.mpr hp, rfl⟩
    have h2 := hSyl.le h1
    rwa [CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff hXN] at h2
  refine CFSG.ABGLocalTools.isSylowOf_of_card hPle ?_
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hX
  have hcP := CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.card_barSub hXP hPN
  have hcN := CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.card_barSub hXN hNN
  have hs := hSyl.card_eq
  have hpos : Nat.card (barSub X N) ≠ 0 := Nat.card_pos.ne'
  rw [← hcN, Nat.factorization_mul hpos (by rw [hm]; positivity), hm,
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, Nat.Prime.factorization_self
      Nat.prime_two, smul_eq_mul, mul_one, pow_add, ← hs, ← hcP, hm]

end CFSG.LocalAnalysis.EvenBN.Common.RankOneLayerRadical
