module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.Sec85c
import CFSG.Goldschmidt.Steps.Sec89a
import CFSG.Goldschmidt.Steps.Sec89c
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec89

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem commutator_le_self (K : Subgroup G) : ⁅K, K⁆ ≤ K :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

theorem exists_mem_commutator_not_mem (hset : GoldSetting G S A)
    (hD : ¬ ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ A) :
    ∃ z ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆, z ∉ A ∧
      ∀ s ∈ (S : Subgroup G), z⁻¹ * s⁻¹ * z * s ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A' := A.subgroupOf (S : Subgroup G) with hA'
  have : A'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hset.le).mpr (Sec8.le_normalizer hset)
  set D := ⁅(S : Subgroup G), (S : Subgroup G)⁆ with hDdef
  have hDS : D ≤ (S : Subgroup G) := commutator_le_self _
  have hDn : (D.subgroupOf (S : Subgroup G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDS).mpr fun s hs =>
      Sec8.mem_normalizer_commutator (Subgroup.le_normalizer hs)
  set H := (D.subgroupOf (S : Subgroup G)).map (QuotientGroup.mk' A') with hH
  have : H.Normal := Subgroup.Normal.map hDn _ (QuotientGroup.mk'_surjective A')
  have : Group.IsNilpotent ((S : Subgroup G) ⧸ A') := (S.isPGroup'.to_quotient A').isNilpotent
  have hH1 : H ≠ ⊥ := by
    obtain ⟨z, hzD, hzA⟩ := Set.not_subset.mp hD
    intro h
    have hmem : QuotientGroup.mk' A' ⟨z, hDS hzD⟩ ∈ H :=
      ⟨⟨z, hDS hzD⟩, Subgroup.mem_subgroupOf.mpr hzD, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hmem
    exact hzA hmem
  obtain ⟨⟨q, hqH, hqZ⟩, hq1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hH1)
  obtain ⟨y, hyD, rfl⟩ := hqH
  refine ⟨y, Subgroup.mem_subgroupOf.mp hyD, fun hyA => hq1 ?_, fun s hs => ?_⟩
  · apply Subtype.ext
    change QuotientGroup.mk' A' y = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hyA
  · have hc := Subgroup.mem_center_iff.mp hqZ (QuotientGroup.mk' A' ⟨s, hs⟩)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf] at hc
    have e : ((((⟨s, hs⟩ : (S : Subgroup G)) * y)⁻¹ * (y * ⟨s, hs⟩) : (S : Subgroup G)) : G) =
        (y : G)⁻¹ * s⁻¹ * y * s := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [e] at hc

theorem exists_T1 (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hDc : IsMulCommutative (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G))
    (hΩD : A = Omega1 ⁅(S : Subgroup G), (S : Subgroup G)⁆)
    (hD : ¬ ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ A) {x : G}
    (hxS : x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) :
    ∃ T₁ : Subgroup G, T₁ ≤ (S : Subgroup G) ∧ A ≤ T₁ ∧
      (S : Subgroup G) ≤ Subgroup.normalizer (T₁ : Set G) ∧
      x ∈ Subgroup.normalizer (T₁ : Set G) ∧ (∀ s ∈ (S : Subgroup G), s ^ 2 ∈ T₁) ∧
      (∀ s ∈ (S : Subgroup G), (∀ w ∈ T₁, w * s = s * w) → s ∈ T₁) ∧
      ∃ y₀ ∈ T₁, (∀ w ∈ T₁, w * y₀ = y₀ * w) ∧ y₀ ^ 2 ∈ A ∧ y₀ ^ 2 ≠ 1 := by
  set D := ⁅(S : Subgroup G), (S : Subgroup G)⁆ with hDdef
  have hDS : D ≤ (S : Subgroup G) := commutator_le_self _
  have hAD : A ≤ D := by
    rw [hΩD]
    exact (Subgroup.closure_le _).mpr fun t ht => ht.1
  have hinvD : ∀ t ∈ D, t ^ 2 = 1 → t ∈ A := fun t ht ht2 => by
    rw [hΩD]
    exact Subgroup.subset_closure ⟨ht, ht2⟩
  have hDcomm : ∀ y ∈ D, ∀ y' ∈ D, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hDc.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  set X : Set G := {y | y ∈ D ∧ ∀ s ∈ (S : Subgroup G), y⁻¹ * s⁻¹ * y * s ∈ A} with hX
  have hXS : ∀ y ∈ X, y ∈ (S : Subgroup G) := fun y hy => hDS hy.1
  have hXg : ∀ g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      g ∈ Subgroup.normalizer (A : Set G) → ∀ y ∈ X, g⁻¹ * y * g ∈ X := by
    intro g hgS hgA y hy
    refine ⟨conj_mem_of_mem_normalizer (Sec8.mem_normalizer_commutator hgS) hy.1, fun s hs => ?_⟩
    have hs' : g * s * g⁻¹ ∈ (S : Subgroup G) := by
      have := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hgS) hs
      simpa using this
    have := conj_mem_of_mem_normalizer hgA (hy.2 _ hs')
    have e : g⁻¹ * (y⁻¹ * (g * s * g⁻¹)⁻¹ * y * (g * s * g⁻¹)) * g =
        (g⁻¹ * y * g)⁻¹ * s⁻¹ * (g⁻¹ * y * g) * s := by group
    rwa [e] at this
  have hXs : ∀ s ∈ (S : Subgroup G), ∀ y ∈ X, s⁻¹ * y * s ∈ X := by
    intro s hs y hy
    obtain ⟨c, hcA, hce⟩ : ∃ c ∈ A, s⁻¹ * y * s = y * c := ⟨_, hy.2 s hs, by group⟩
    rw [hce]
    refine ⟨D.mul_mem hy.1 (hAD hcA), fun s' hs' => ?_⟩
    have hcs' : c * s' = s' * c := comm_of_mem hset h4 hs' hcA
    have ha := hy.2 s' hs'
    have hcy := Sec8.comm hset.elem hcA ha
    have e2 : (y * c)⁻¹ * s'⁻¹ * (y * c) * s' = c⁻¹ * ((y⁻¹ * s'⁻¹ * y * s') * c) := by
      calc (y * c)⁻¹ * s'⁻¹ * (y * c) * s' = c⁻¹ * (y⁻¹ * s'⁻¹ * y * (c * s')) := by group
        _ = c⁻¹ * ((y⁻¹ * s'⁻¹ * y * s') * c) := by rw [hcs']; group
    rw [e2, ← hcy, inv_mul_cancel_left]
    exact ha
  have hXsq : ∀ y ∈ X, y ^ 2 ∈ X := by
    intro y hy
    refine ⟨D.pow_mem hy.1 2, fun s hs => ?_⟩
    obtain ⟨c, hcA, hce⟩ : ∃ c ∈ A, s⁻¹ * y * s = y * c := ⟨_, hy.2 s hs, by group⟩
    have hcy : c * y = y * c := comm_of_mem hset h4 (hXS y hy) hcA
    have hc2 : c * c = 1 := Sec8.mul_self_eq_one hset.elem hcA
    have e : s⁻¹ * y ^ 2 * s = y ^ 2 := by
      calc s⁻¹ * y ^ 2 * s = (s⁻¹ * y * s) * (s⁻¹ * y * s) := by rw [pow_two]; group
        _ = y * (c * y) * c := by rw [hce]; group
        _ = y ^ 2 * (c * c) := by rw [hcy, pow_two]; group
        _ = y ^ 2 := by rw [hc2, mul_one]
    have e' : (y ^ 2)⁻¹ * s⁻¹ * y ^ 2 * s = 1 := by
      calc (y ^ 2)⁻¹ * s⁻¹ * y ^ 2 * s = (y ^ 2)⁻¹ * (s⁻¹ * y ^ 2 * s) := by group
        _ = 1 := by rw [e, inv_mul_cancel]
    rw [e']
    exact A.one_mem
  set T₁ := (S : Subgroup G) ⊓ Subgroup.centralizer X with hT₁
  have hXT : ∀ y ∈ X, y ∈ T₁ := fun y hy => ⟨hXS y hy,
    Subgroup.mem_centralizer_iff.mpr fun y' hy' => hDcomm y' hy'.1 y hy.1⟩
  have hconjT : ∀ g : G, g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) →
      (∀ y ∈ X, g * y * g⁻¹ ∈ X) → g ∈ Subgroup.normalizer (T₁ : Set G) := by
    intro g hgS hgX
    refine Sec8.mem_normalizer_of_conj_le fun w hw => ⟨conj_mem_of_mem_normalizer hgS hw.1,
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hc := Subgroup.mem_centralizer_iff.mp hw.2 _ (hgX y hy)
    calc y * (g⁻¹ * w * g) = g⁻¹ * ((g * y * g⁻¹) * w) * g := by group
      _ = g⁻¹ * (w * (g * y * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * w * g * y := by group
  obtain ⟨z, hzD, hzA, hzS⟩ := exists_mem_commutator_not_mem hset hD
  obtain ⟨y₀, hy₀X, hy₀A, hy₀1⟩ : ∃ y₀ ∈ X, y₀ ^ 2 ∈ A ∧ y₀ ^ 2 ≠ 1 := by
    by_contra hno
    push Not at hno
    have key := mem_of_forall_sq (A := A) (Z := X) hXsq (fun y hy hy2 => hinvD y hy.1 hy2) hno
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨z, hDS hzD⟩
    exact hzA (key k z ⟨hzD, hzS⟩ (by simpa using congrArg Subtype.val hk))
  refine ⟨T₁, inf_le_left, fun a ha => ⟨hset.le ha, Subgroup.mem_centralizer_iff.mpr
      fun y hy => (comm_of_mem hset h4 (hXS y hy) ha).symm⟩,
    fun s hs => hconjT s (Subgroup.le_normalizer hs) fun y hy => by
      have := hXs s⁻¹ ((S : Subgroup G).inv_mem hs) y hy
      simpa using this,
    hconjT x hxS (fun y hy => by
      have := hXg x⁻¹ (Subgroup.inv_mem _ hxS) (Subgroup.inv_mem _ hxA) y hy
      simpa using this),
    fun s hs => ⟨(S : Subgroup G).pow_mem hs 2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩,
    fun s hs h => ⟨hs, Subgroup.mem_centralizer_iff.mpr fun y hy => h y (hXT y hy)⟩,
    y₀, hXT y₀ hy₀X, fun w hw => (Subgroup.mem_centralizer_iff.mp hw.2 y₀ hy₀X).symm,
    hy₀A, hy₀1⟩
  obtain ⟨c, hcA, hce⟩ : ∃ c ∈ A, s⁻¹ * y * s = y * c := ⟨_, hy.2 s hs, by group⟩
  have hsc : s⁻¹ * c * s = c := by rw [mul_assoc, comm_of_mem hset h4 hs hcA]; group
  have hc2 := Sec8.mul_self_eq_one hset.elem hcA
  have e : (s ^ 2)⁻¹ * y * s ^ 2 = y := by
    calc (s ^ 2)⁻¹ * y * s ^ 2 = s⁻¹ * (s⁻¹ * y * s) * s := by rw [pow_two]; group
      _ = s⁻¹ * (y * c) * s := by rw [hce]
      _ = (s⁻¹ * y * s) * (s⁻¹ * c * s) := by group
      _ = y := by rw [hce, hsc, mul_assoc, hc2, mul_one]
  calc y * s ^ 2 = s ^ 2 * ((s ^ 2)⁻¹ * y * s ^ 2) := by group
    _ = s ^ 2 * y := by rw [e]

end CFSG.Goldschmidt.Sec89
