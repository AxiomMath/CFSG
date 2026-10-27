module

public import CFSG.ClassicalInvolution.Balance.Delta
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.TwoSignalizer

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.SignalizerFunctorTheorem CFSG.Assembly.Dichotomy
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def centralOddCore (A : Subgroup G) : Subgroup G :=
  oddCoreIn (Subgroup.centralizer (A : Set G))

@[expose] def deltaStar (A : Subgroup G) (a : G) : Subgroup G :=
  involutionOddCore a ⊔ centralOddCore A

@[expose] def deltaStarCompletion (A : Subgroup G) : Subgroup G :=
  ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), deltaStar A a

@[expose] def WeakBalanced (A : Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
    ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b

end Defs

section Basic

variable {G : Type} [Group G]

theorem mem_normalizer_inf {H K : Subgroup G} {x : G}
    (hH : x ∈ Subgroup.normalizer (H : Set G)) (hK : x ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH y, hK y]

theorem odd_card_sup_of_le_normalizer [Finite G] {H N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hH : Odd (Nat.card H)) (hN : Odd (Nat.card N)) :
    Odd (Nat.card (H ⊔ N : Subgroup G)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hN

theorem centralOddCore_le_centralizer (A : Subgroup G) :
    centralOddCore A ≤ Subgroup.centralizer (A : Set G) :=
  oddCoreIn_le _

theorem centralOddCore_le_centralizer_singleton {A : Subgroup G} {a : G} (ha : a ∈ A) :
    centralOddCore A ≤ Subgroup.centralizer {a} :=
  (centralOddCore_le_centralizer A).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))

theorem centralOddCore_le_normalizer {A : Subgroup G} {a : G} (ha : a ∈ A) :
    centralOddCore A ≤ Subgroup.normalizer (involutionOddCore a : Set G) :=
  (centralOddCore_le_centralizer_singleton ha).trans (normalizer_oddCoreIn _)

theorem odd_card_centralOddCore [Finite G] (A : Subgroup G) :
    Odd (Nat.card (centralOddCore A)) :=
  odd_card_oddCoreIn _

theorem deltaStar_le_centralizer {A : Subgroup G} {a : G} (ha : a ∈ A) :
    deltaStar A a ≤ Subgroup.centralizer {a} :=
  sup_le (involutionOddCore_le_centralizer a) (centralOddCore_le_centralizer_singleton ha)

theorem odd_card_deltaStar [Finite G] {A : Subgroup G} {a : G} (ha : a ∈ A) :
    Odd (Nat.card (deltaStar A a)) := by
  rw [deltaStar, sup_comm]
  exact odd_card_sup_of_le_normalizer (centralOddCore_le_normalizer ha)
    (odd_card_centralOddCore A) (odd_card_oddCoreIn _)

theorem mem_centralizer_singleton_of_mem {A : Subgroup G} (hA : IsMulCommutative A) {x a : G}
    (hx : x ∈ A) (ha : a ∈ A) : x ∈ Subgroup.centralizer {a} :=
  Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.is_comm.comm (⟨x, hx⟩ : A) ⟨a, ha⟩))

theorem le_normalizer_deltaStar {A : Subgroup G} (hA : IsMulCommutative A) {a : G} (ha : a ∈ A) :
    A ≤ Subgroup.normalizer (deltaStar A a : Set G) := by
  have key : ∀ x ∈ A, ∀ y ∈ deltaStar A a, x * y * x⁻¹ ∈ deltaStar A a := by
    intro x hx y hy
    obtain ⟨n, hn, t, ht, rfl⟩ :=
      (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing _ _
        (centralOddCore_le_normalizer ha) y).mp hy
    have hxt : x * t = t * x :=
      Subgroup.mem_centralizer_iff.mp (centralOddCore_le_centralizer A ht) x hx
    have hxt' : t * x⁻¹ = x⁻¹ * t := by
      calc t * x⁻¹ = x⁻¹ * (x * t) * x⁻¹ := by group
        _ = x⁻¹ * (t * x) * x⁻¹ := by rw [hxt]
        _ = x⁻¹ * t := by group
    have : x * (n * t) * x⁻¹ = (x * n * x⁻¹) * t := by
      calc x * (n * t) * x⁻¹ = x * n * (t * x⁻¹) := by group
        _ = x * n * (x⁻¹ * t) := by rw [hxt']
        _ = (x * n * x⁻¹) * t := by group
    rw [this]
    exact (deltaStar A a).mul_mem
      (Subgroup.mem_sup_left (conj_mem_oddCoreIn (mem_centralizer_singleton_of_mem hA hx ha) hn))
      (Subgroup.mem_sup_right ht)
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key x hx y hy, fun hy => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ hy
  simpa [mul_assoc] using this

end Basic

section Balance

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_le_centralOddCore {A Y : Subgroup G} (hYodd : Odd (Nat.card Y))
    (hY : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Y : Set G)) :
    Y ⊓ Subgroup.centralizer (A : Set G) ≤ centralOddCore A := by
  refine le_oddCoreIn_of_normalizes inf_le_right ?_ ?_
  · exact fun x hx => mem_normalizer_inf (hY hx) (Subgroup.le_normalizer hx)
  · exact hYodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem inf_centralizer_le_deltaStar {A P : Subgroup G} {b : G} (hA : IsElemAbelian 2 A)
    (hb : b ∈ A) (hP : A ≤ Subgroup.normalizer (P : Set G)) (hPodd : Odd (Nat.card P))
    (hPC : P ⊓ Subgroup.centralizer (A : Set G) ≤ centralOddCore A)
    (hbal : ⁅P ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b) :
    P ⊓ Subgroup.centralizer {b} ≤ deltaStar A b := by
  have hAQ : A ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_inf (hP hx)
      (Subgroup.le_normalizer (mem_centralizer_singleton_of_mem hA.1 hx hb))
  have hQodd : Odd (Nat.card (P ⊓ Subgroup.centralizer {b} : Subgroup G)) :=
    hPodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two A (P ⊓ Subgroup.centralizer {b})
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 A hA) hAQ
    (Nat.coprime_two_left.mpr hQodd)
  refine hfac.symm.trans_le (sup_le (hbal.trans le_sup_left) ?_)
  exact ((inf_le_inf_right _ inf_le_left).trans hPC).trans le_sup_right

theorem deltaStar_inf_centralizer_le {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hW : WeakBalanced A) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1) :
    deltaStar A a ⊓ Subgroup.centralizer {b} ≤ deltaStar A b := by
  intro x hx
  obtain ⟨n, hn, t, ht, hnt⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing _ _
    (centralOddCore_le_normalizer ha) x).mp hx.1
  have htb : t ∈ Subgroup.centralizer {b} := centralOddCore_le_centralizer_singleton hb ht
  have hnb : n ∈ involutionOddCore a ⊓ Subgroup.centralizer {b} := by
    refine ⟨hn, ?_⟩
    have : n = x * t⁻¹ := by rw [← hnt]; group
    rw [this]
    exact (Subgroup.centralizer {b}).mul_mem hx.2 ((Subgroup.centralizer {b}).inv_mem htb)
  have hPA : A ≤ Subgroup.normalizer (involutionOddCore a : Set G) := fun y hy =>
    normalizer_oddCoreIn _ (mem_centralizer_singleton_of_mem hA.1 hy ha)
  have hPC : involutionOddCore a ⊓ Subgroup.centralizer (A : Set G) ≤ centralOddCore A :=
    inf_centralizer_le_centralOddCore (odd_card_oddCoreIn _) fun y hy =>
      normalizer_oddCoreIn _
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha) hy)
  have h1 := inf_centralizer_le_deltaStar hA hb hPA (odd_card_oddCoreIn _) hPC
    (hW a ha ha1 b hb hb1) hnb
  rw [← hnt]
  exact (deltaStar A b).mul_mem h1 (Subgroup.mem_sup_right ht)

omit [Finite G] in
theorem deltaStar_le_deltaStarCompletion {A : Subgroup G} {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    deltaStar A a ≤ deltaStarCompletion A :=
  le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl)

omit [Finite G] in
theorem centralOddCore_le_deltaStarCompletion {A : Subgroup G} {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) : centralOddCore A ≤ deltaStarCompletion A :=
  le_sup_right.trans (deltaStar_le_deltaStarCompletion ha ha1)

theorem deltaStar_isCompletion {A : Subgroup G} (hA : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A)
    (hW : WeakBalanced A) :
    Odd (Nat.card (deltaStarCompletion A)) ∧
      A ≤ Subgroup.normalizer (deltaStarCompletion A : Set G) ∧
      (∀ a ∈ A, a ≠ 1 → deltaStarCompletion A ⊓ Subgroup.centralizer {a} = deltaStar A a) ∧
      (∀ Y : Subgroup G, A ≤ Subgroup.normalizer (Y : Set G) →
        (∀ a ∈ A, a ≠ 1 → Y ⊓ Subgroup.centralizer {a} ≤ deltaStar A a) →
          Y ≤ deltaStarCompletion A) ∧
      Group.IsSolvable (deltaStarCompletion A) :=
  two_signalizer_completion A hA h8 (deltaStar A) (fun _ ha _ => deltaStar_le_centralizer ha)
    (fun _ ha _ => odd_card_deltaStar ha) (fun _ ha _ => le_normalizer_deltaStar hA.1 ha)
    (fun _ ha ha1 _ hb hb1 => deltaStar_inf_centralizer_le hA hW ha ha1 hb hb1)

theorem deltaCore_le_deltaStarCompletion {A F : Subgroup G} (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) (hW : WeakBalanced A) (hFA : F ≤ A) {d : G} (hd : d ∈ F)
    (hd1 : d ≠ 1)
    (hF : ∀ a ∈ A, a ≠ 1 → ⁅deltaCore F ⊓ Subgroup.centralizer {a}, A⁆ ≤ involutionOddCore a) :
    deltaCore F ≤ deltaStarCompletion A := by
  obtain ⟨-, -, -, hmax, -⟩ := deltaStar_isCompletion hA h8 hW
  have hodd := odd_card_deltaCore hd hd1
  have hnorm := normalizer_deltaCore hA.1 hFA
  refine hmax _ hnorm fun a ha ha1 => ?_
  refine inf_centralizer_le_deltaStar hA ha hnorm hodd ?_ (hF a ha ha1)
  refine inf_centralizer_le_centralOddCore hodd fun y hy => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hyF : ∀ f ∈ F, y * f = f * y := fun f hf =>
    (Subgroup.mem_centralizer_iff.mp hy f (hFA hf)).symm
  have hyF' : ∀ f ∈ F, y⁻¹ * f = f * y⁻¹ := fun f hf => by
    have := hyF f hf
    calc y⁻¹ * f = y⁻¹ * (f * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * f) * y⁻¹ := by rw [this]
      _ = f * y⁻¹ := by group
  refine ⟨fun hz => conj_mem_deltaCore hyF hz, fun hz => ?_⟩
  have := conj_mem_deltaCore hyF' hz
  simpa [mul_assoc] using this

theorem odd_card_iSup_involutionOddCore {A F : Subgroup G} (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) (hW : WeakBalanced A) (hFA : F ≤ A) :
    Odd (Nat.card (⨆ f ∈ F, ⨆ (_ : f ≠ 1), involutionOddCore f : Subgroup G)) := by
  obtain ⟨hodd, -⟩ := deltaStar_isCompletion hA h8 hW
  refine hodd.of_dvd_nat (Subgroup.card_dvd_of_le ?_)
  refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
  exact le_sup_left.trans (deltaStar_le_deltaStarCompletion (hFA hf) hf1)

end Balance

end CFSG.ClassicalInvolution.Balance.Bootstrap
