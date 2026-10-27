module

public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.OddCoreEliminationStatements
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry
import CFSG.GroupTheory.ElemAbelianClosure

public section

open scoped commutatorElement

namespace CFSG.Assembly.Dichotomy

namespace CentralizerContainment

@[expose] def twoCorePreimage {G : Type*} [Group G] (t : G) :
    Subgroup (Subgroup.centralizer ({t} : Set G)) :=
  (pCore 2 (Subgroup.centralizer ({t} : Set G) ⧸
      oddCore (Subgroup.centralizer ({t} : Set G)))).comap
    (QuotientGroup.mk' (oddCore (Subgroup.centralizer ({t} : Set G))))

theorem mem_twoCorePreimage {G : Type*} [Group G] {t : G}
    {x : Subgroup.centralizer ({t} : Set G)} :
    x ∈ twoCorePreimage t ↔ QuotientGroup.mk' (oddCore (Subgroup.centralizer ({t} : Set G))) x ∈
      pCore 2 (Subgroup.centralizer ({t} : Set G) ⧸
        oddCore (Subgroup.centralizer ({t} : Set G))) :=
  Iff.rfl

theorem elemAbelian_commute {G : Type*} [Group G] {U : Subgroup G} (hU : IsElemAbelian 2 U)
    {a b : G} (ha : a ∈ U) (hb : b ∈ U) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hU ha hb

theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] : Odd (Nat.card (oddCore X)) := by
  rw [oddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

variable {G : Type*} [Group G] [Finite G]

private theorem card_le_two_mul_card_centralizer {S U : Subgroup G} (hS : IsPGroup 2 S)
    (hUS : U ≤ S) (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hU : IsElemAbelian 2 U)
    (hUcard : Nat.card U = 4) :
    Nat.card S ≤ 2 * Nat.card (S ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) := by
  let V := U.subgroupOf S
  have : V.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUS).mpr hSU
  have hV : CFSG.Open.IsElemAbelian 2 V :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport 2 U V
      (Subgroup.subgroupOfEquivOfLe hUS).symm hU
  have hVcard : Nat.card V = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv).trans hUcard
  obtain ⟨-, -, hindex⟩ := CFSG.ProperTwoGeneratedCore.normal_four_centralizer_index hS V hV hVcard
  set C := Subgroup.centralizer (V : Set S)
  change C.index ≤ 2 at hindex
  have hC : C.map S.subtype = S ⊓ Subgroup.centralizer (U : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hx ⟨a, hUS ha⟩ (Subgroup.mem_subgroupOf.mpr ha))
    · rintro ⟨hyS, hyC⟩
      refine ⟨⟨y, hyS⟩, Subgroup.mem_centralizer_iff.mpr fun v hv => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hyC v (Subgroup.mem_subgroupOf.mp hv)
  have hcard : Nat.card C = Nat.card (S ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) := by
    rw [← hC, Subgroup.card_map_of_injective S.subtype_injective]
  have hmul := C.card_mul_index
  rw [hcard] at hmul
  calc Nat.card S = Nat.card (S ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) * C.index :=
        hmul.symm
    _ ≤ Nat.card (S ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) * 2 :=
        Nat.mul_le_mul_left _ hindex
    _ = 2 * Nat.card (S ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) := mul_comm _ _

private theorem exists_conj_sylow {p : ℕ} [Fact p.Prime] (S S₁ : Sylow p G) :
    ∃ g : G, ∀ y : G, y ∈ (S₁ : Subgroup G) ↔ g⁻¹ * y * g ∈ (S : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S₁
  refine ⟨g, fun y => ?_⟩
  rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

private theorem commutator_eq_one_or_eq {S : Sylow 2 G} {U : Subgroup G} (hUS : U ≤ S)
    (hSU : (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G))
    (hU : IsElemAbelian 2 U) (hUcard : Nat.card U = 4)
    (hpref : (∃ V : Subgroup G, V ≤ subgroupCenter S ∧ IsElemAbelian 2 V ∧ Nat.card V = 4) →
      U ≤ subgroupCenter S)
    {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) {P : Subgroup G}
    (hPu : P ≤ Subgroup.centralizer ({u} : Set G)) (hP : IsPGroup 2 P)
    (hTP : (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) ≤ P)
    {x : G} (hx : x ∈ P) {a : G} (ha : a ∈ U) :
    x * a * x⁻¹ * a⁻¹ = 1 ∨ x * a * x⁻¹ * a⁻¹ = u := by
  set T := (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)
  have hUT : U ≤ T := fun b hb =>
    ⟨hUS hb, Subgroup.mem_centralizer_iff.mpr fun c hc => elemAbelian_commute hU hc hb⟩
  have hTU : ∀ t ∈ T, ∀ b ∈ U, t * b = b * t := fun t ht b hb =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht).2 b hb).symm
  have haT : a ∈ T := hUT ha
  by_cases hxT : x ∈ T
  · left
    rw [hTU x hxT a ha, mul_inv_cancel_right, mul_inv_cancel]
  have hSidx : Nat.card (S : Subgroup G) ≤ 2 * Nat.card T :=
    card_le_two_mul_card_centralizer S.isPGroup' hUS hSU hU hUcard
  obtain ⟨S₁, hPS₁⟩ := hP.exists_le_sylow
  have hS₁card : Nat.card (S₁ : Subgroup G) = Nat.card (S : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hPS : Nat.card P ≤ Nat.card (S : Subgroup G) :=
    hS₁card ▸ Subgroup.card_le_of_le hPS₁
  let T' := T.subgroupOf P
  have hT'card : Nat.card T' = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv
  have hmul : Nat.card T * T'.index = Nat.card P := hT'card ▸ T'.card_mul_index
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hidx0 : T'.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hidx1 : T'.index ≠ 1 := by
    intro h
    rw [Subgroup.index_eq_one] at h
    have hxT' : (⟨x, hx⟩ : P) ∈ T' := by rw [h]; exact Subgroup.mem_top _
    exact hxT (Subgroup.mem_subgroupOf.mp hxT')
  have hidx2 : T'.index ≤ 2 := by
    apply Nat.le_of_mul_le_mul_left _ hTpos
    rw [hmul]
    omega
  have hidx : T'.index = 2 := by omega
  have hPcard : Nat.card P = 2 * Nat.card T := by rw [← hmul, hidx, mul_comm]
  have hPeq : P = S₁ := Subgroup.eq_of_le_of_card_ge hPS₁ (by omega)
  have hnormal : T'.Normal := Subgroup.normal_of_index_eq_two hidx
  have hconj : ∀ g ∈ P, ∀ t ∈ T, g * t * g⁻¹ ∈ T := fun g hg t ht =>
    Subgroup.mem_subgroupOf.mp
      (hnormal.conj_mem ⟨t, hTP ht⟩ (Subgroup.mem_subgroupOf.mpr ht) ⟨g, hg⟩)
  have hxnot : (⟨x, hx⟩ : P) ∉ T' := fun h => hxT (Subgroup.mem_subgroupOf.mp h)
  have hsq : x * x ∈ T := Subgroup.mem_subgroupOf.mp
    ((Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨x, hx⟩)).mpr Iff.rfl)
  have hcoset : ∀ y ∈ P, y ∉ T → x⁻¹ * y ∈ T := by
    intro y hy hyT
    have hynot : (⟨y, hy⟩ : P) ∉ T' := fun h => hyT (Subgroup.mem_subgroupOf.mp h)
    have hxinv : (⟨x, hx⟩ : P)⁻¹ ∉ T' := fun h => hxnot (by simpa using T'.inv_mem h)
    exact Subgroup.mem_subgroupOf.mp
      ((Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hxinv hynot))
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hU.2 a ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  obtain ⟨b, hb⟩ : ∃ b, x * a * x⁻¹ = b := ⟨_, rfl⟩
  have hbT : b ∈ T := hb ▸ hconj x hx a haT
  have hb2 : b * b = 1 := by
    rw [← hb]
    calc x * a * x⁻¹ * (x * a * x⁻¹) = x * (a * a) * x⁻¹ := by group
      _ = 1 := by rw [ha2, mul_one, mul_inv_cancel]
  have hab : b * a = a * b := hTU b hbT a ha
  have hTb : ∀ t ∈ T, t * b = b * t := by
    intro t ht
    have ht' : x⁻¹ * t * x ∈ T := by simpa only [inv_inv] using hconj x⁻¹ (P.inv_mem hx) t ht
    have hc := hTU _ ht' a ha
    rw [← hb]
    calc t * (x * a * x⁻¹) = x * ((x⁻¹ * t * x) * a) * x⁻¹ := by group
      _ = x * (a * (x⁻¹ * t * x)) * x⁻¹ := by rw [hc]
      _ = x * a * x⁻¹ * t := by group
  have hsa : x * x * a = a * (x * x) := hTU _ hsq a ha
  have hxb : x * b = a * x := by
    rw [← hb]
    calc x * (x * a * x⁻¹) = x * x * a * x⁻¹ := by group
      _ = a * (x * x) * x⁻¹ := by rw [hsa]
      _ = a * x := by group
  have hbx : b * x = x * a := by rw [← hb]; group
  rw [hb, hainv]
  obtain ⟨c, hc⟩ : ∃ c, b * a = c := ⟨_, rfl⟩
  rw [hc]
  have hcT : ∀ t ∈ T, t * c = c * t := by
    intro t ht
    calc t * c = t * b * a := by rw [← hc, mul_assoc]
      _ = b * t * a := by rw [hTb t ht]
      _ = b * (t * a) := by rw [mul_assoc]
      _ = b * (a * t) := by rw [hTU t ht a ha]
      _ = c * t := by rw [← hc, mul_assoc]
  have hc2 : c * c = 1 := by
    rw [← hc]
    calc b * a * (b * a) = b * (a * b) * a := by group
      _ = b * (b * a) * a := by rw [hab]
      _ = (b * b) * (a * a) := by group
      _ = 1 := by rw [hb2, ha2, mul_one]
  have hxc : x * c = c * x := by
    rw [← hc]
    calc x * (b * a) = (x * b) * a := by group
      _ = a * (b * x) := by rw [hxb, hbx]; group
      _ = (a * b) * x := by group
      _ = (b * a) * x := by rw [hab]
  have hcZ : ∀ y ∈ P, y * c = c * y := by
    intro y hy
    by_cases hyT : y ∈ T
    · exact hcT y hyT
    · have ht := hcoset y hy hyT
      calc y * c = x * ((x⁻¹ * y) * c) := by group
        _ = x * (c * (x⁻¹ * y)) := by rw [hcT _ ht]
        _ = (x * c) * (x⁻¹ * y) := by group
        _ = (c * x) * (x⁻¹ * y) := by rw [hxc]
        _ = c * y := by group
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  right
  by_contra hcu
  have huo : orderOf u = 2 := orderOf_eq_prime (hU.2 u hu) hu1
  have hco : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
  have haP : a ∈ P := hTP haT
  have hcP : c ∈ P := by
    rw [← hc, ← hb]
    exact P.mul_mem (P.mul_mem (P.mul_mem hx haP) (P.inv_mem hx)) haP
  have huP : u ∈ P := hTP (hUT hu)
  have huZ : ∀ y ∈ P, y * u = u * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hPu hy)
  obtain ⟨g, hg⟩ := exists_conj_sylow S S₁
  rw [← hPeq] at hg
  have hcenter : ∀ w ∈ P, (∀ y ∈ P, y * w = w * y) → g⁻¹ * w * g ∈ subgroupCenter S := by
    intro w hw hwZ
    refine Subgroup.mem_inf.mpr ⟨(hg w).mp hw, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs' : g * s * g⁻¹ ∈ P := (hg _).mpr (by
      have hgs : g⁻¹ * (g * s * g⁻¹) * g = s := by group
      rw [hgs]
      exact hs)
    have hsw := hwZ _ hs'
    calc s * (g⁻¹ * w * g) = g⁻¹ * ((g * s * g⁻¹) * w) * g := by group
      _ = g⁻¹ * (w * (g * s * g⁻¹)) * g := by rw [hsw]
      _ = g⁻¹ * w * g * s := by group
  have hu' := hcenter u huP huZ
  have hc' := hcenter c hcP hcZ
  have hconjorder (w : G) : orderOf (g⁻¹ * w * g) = orderOf w := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) w
    rwa [MulAut.conj_apply, inv_inv] at h
  have hu'o : orderOf (g⁻¹ * u * g) = 2 := (hconjorder u).trans huo
  have hc'o : orderOf (g⁻¹ * c * g) = 2 := (hconjorder c).trans hco
  have hconjinj (w w' : G) (h : g⁻¹ * w * g = g⁻¹ * w' * g) : w = w' := by
    have h' := congrArg (fun y => g * y * g⁻¹) h
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at h'
    exact h'
  have hc'notin : g⁻¹ * c * g ∉ Subgroup.zpowers (g⁻¹ * u * g) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← zpow_mod_orderOf, hu'o, Nat.cast_ofNat] at hk
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h, zpow_zero] at hk
      apply hc1
      apply hconjinj
      rw [← hk]
      group
    · rw [h, zpow_one] at hk
      exact hcu (hconjinj _ _ hk.symm)
  have hcommZ : Subgroup.zpowers (g⁻¹ * u * g) ≤
      Subgroup.centralizer (Subgroup.zpowers (g⁻¹ * c * g) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hcomm : Commute (g⁻¹ * u * g) (g⁻¹ * c * g) := by
      change (g⁻¹ * u * g) * (g⁻¹ * c * g) = (g⁻¹ * c * g) * (g⁻¹ * u * g)
      calc (g⁻¹ * u * g) * (g⁻¹ * c * g) = g⁻¹ * (u * c) * g := by group
        _ = g⁻¹ * (c * u) * g := by rw [hcZ u huP]
        _ = (g⁻¹ * c * g) * (g⁻¹ * u * g) := by group
    exact (hcomm.zpow_right k).eq.symm
  obtain ⟨V, -, -, hVel, hVcard, hVle⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product (prime := 2)
      (firstRank := 1) (secondRank := 1) (Subgroup.zpowers (g⁻¹ * u * g))
      (Subgroup.zpowers (g⁻¹ * c * g))
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary _ hu'o)
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary _ hc'o)
      (by rw [Nat.card_zpowers, hu'o, pow_one]) (by rw [Nat.card_zpowers, hc'o, pow_one])
      hcommZ (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint _ _ hc'o hc'notin)
  have hVZ : V ≤ subgroupCenter S :=
    hVle.trans (sup_le (Subgroup.zpowers_le.mpr hu') (Subgroup.zpowers_le.mpr hc'))
  have hUZ := hpref ⟨V, hVZ, hVel, by rw [hVcard]; norm_num⟩
  have hST : (S : Subgroup G) ≤ T := fun s hs =>
    ⟨hs, Subgroup.mem_centralizer_iff.mpr fun a' ha' =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hUZ ha')).2 s hs).symm⟩
  have := Subgroup.card_le_of_le hST
  omega

end CentralizerContainment

open CentralizerContainment

theorem preferred_normal_four_core_containment {G : Type} [Group G] [Finite G]
    (hcomp : ¬ IsComponentType G) (S : Sylow 2 G) {U : Subgroup G} (hUS : U ≤ S)
    (hSU : (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G))
    (hU : IsElemAbelian 2 U) (hUcard : Nat.card U = 4)
    (hpref : (∃ V : Subgroup G, V ≤ subgroupCenter S ∧ IsElemAbelian 2 V ∧ Nat.card V = 4) →
      U ≤ subgroupCenter S)
    {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) :
    U ≤ Subgroup.centralizer ({u} : Set G) ∧
      U.subgroupOf (Subgroup.centralizer ({u} : Set G)) ≤ twoCorePreimage u ∧
      (∀ P : Sylow 2 (Subgroup.centralizer ({u} : Set G)),
        ((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)).subgroupOf
            (Subgroup.centralizer ({u} : Set G)) ≤ P →
        (∀ x ∈ (P : Subgroup (Subgroup.centralizer ({u} : Set G))), ∀ a ∈ U,
            ⁅(x : G), a⁆ ∈ Subgroup.zpowers u) ∧
          U.subgroupOf (Subgroup.centralizer ({u} : Set G)) ≤
            (P : Subgroup (Subgroup.centralizer ({u} : Set G))) ⊓ twoCorePreimage u) ∧
      ∀ Y : Subgroup G, Odd (Nat.card Y) → U ≤ Subgroup.normalizer (Y : Set G) →
        ∀ y ∈ Y, y ∈ Subgroup.centralizer ({u} : Set G) → ∀ a ∈ U,
          ⁅y, a⁆ ∈ involutionOddCore u := by
  set C := Subgroup.centralizer ({u} : Set G)
  set T := (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)
  have hUC : U ≤ C := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (elemAbelian_commute hU ha hu)
  have hUT : U ≤ T := fun b hb =>
    ⟨hUS hb, Subgroup.mem_centralizer_iff.mpr fun c hc => elemAbelian_commute hU hc hb⟩
  have hTC : T ≤ C := fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht).2 u hu).symm
  have huo : orderOf u = 2 := orderOf_eq_prime (hU.2 u hu) hu1
  have hchar : dichotomyCharP 2 (C ⧸ oddCore C) :=
    (CFSG.Milestones.cls_component_free_centralizer_quotient_characteristic_two G hcomp u huo).1
  let π := QuotientGroup.mk' (oddCore C)
  let u₀ : C := ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hu₀center : π u₀ ∈ Subgroup.center (C ⧸ oddCore C) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (oddCore C) q
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2))
  have hu₀order : orderOf (π u₀) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      have : u₀ ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hU.2 u hu)
      rw [this, map_one]
    · intro h
      have hmem : u₀ ∈ oddCore C := (QuotientGroup.eq_one_iff u₀).mp h
      have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
      rw [Subgroup.orderOf_mk, huo] at hdvd
      exact (Nat.not_even_iff_odd.mpr (odd_card_oddCore C)) (even_iff_two_dvd.mpr hdvd)
  obtain ⟨-, hK, -⟩ := central_involution_core_action_kernel hchar hu₀center hu₀order
  have hPpart : ∀ P : Sylow 2 C, T.subgroupOf C ≤ P →
      (∀ x ∈ (P : Subgroup C), ∀ a ∈ U, ⁅(x : G), a⁆ ∈ Subgroup.zpowers u) ∧
        U.subgroupOf C ≤ (P : Subgroup C) ⊓ twoCorePreimage u := by
    intro P hTP
    have hP'C : (P : Subgroup C).map C.subtype ≤ C := Subgroup.map_subtype_le _
    have hP' : IsPGroup 2 ((P : Subgroup C).map C.subtype) := P.isPGroup'.map C.subtype
    have hTP' : T ≤ (P : Subgroup C).map C.subtype := fun t ht =>
      ⟨⟨t, hTC ht⟩, hTP (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
    have hcomm : ∀ x ∈ (P : Subgroup C), ∀ a ∈ U, ⁅(x : G), a⁆ = 1 ∨ ⁅(x : G), a⁆ = u := by
      intro x hx a ha
      rw [commutatorElement_def]
      exact commutator_eq_one_or_eq hUS hSU hU hUcard hpref hu hu1 hP'C hP' hTP' ⟨x, hx, rfl⟩ ha
    refine ⟨fun x hx a ha => ?_, fun a ha => Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rcases hcomm x hx a ha with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers u
    · exact hTP (Subgroup.mem_subgroupOf.mpr (hUT (Subgroup.mem_subgroupOf.mp ha)))
    · rw [mem_twoCorePreimage]
      apply hK
      intro q hq
      have hQP : pCore 2 (C ⧸ oddCore C) ≤ (P : Subgroup C).map π := by
        have h := IsPGroup.le_sylow_of_normal (pCore_isPGroup_assembly 2 _)
          (P.mapSurjective (QuotientGroup.mk'_surjective (oddCore C)))
        rwa [Sylow.coe_mapSurjective] at h
      obtain ⟨x, hx, rfl⟩ := hQP hq
      rw [← map_commutatorElement]
      rcases hcomm x hx a (Subgroup.mem_subgroupOf.mp ha) with h | h
      · have h' : ⁅x, a⁆ = 1 := Subtype.ext h
        rw [h', map_one]
        exact one_mem _
      · have h' : ⁅x, a⁆ = u₀ := Subtype.ext h
        rw [h']
        exact Subgroup.mem_zpowers _
  have hF : U.subgroupOf C ≤ twoCorePreimage u := by
    have hT2 : IsPGroup 2 (T.subgroupOf C) := S.isPGroup'.to_inf_left.comap_subtype
    obtain ⟨P, hP⟩ := hT2.exists_le_sylow
    exact fun a ha => ((hPpart P hP).2 ha).2
  refine ⟨hUC, hF, hPpart, ?_⟩
  intro Y hY hUY y hy hyC a ha
  let y₀ : C := ⟨y, hyC⟩
  let a₀ : C := ⟨a, hUC ha⟩
  have ha₀ : π a₀ ∈ pCore 2 (C ⧸ oddCore C) :=
    mem_twoCorePreimage.mp (hF (Subgroup.mem_subgroupOf.mpr ha))
  have hcY : ⁅y, a⁆ ∈ Y := by
    have h1 : a * y⁻¹ * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hUY ha) y⁻¹).mp (Y.inv_mem hy)
    have h2 : ⁅y, a⁆ = y * (a * y⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact Y.mul_mem hy h1
  have hπ : π ⁅y₀, a₀⁆ ∈ pCore 2 (C ⧸ oddCore C) := by
    rw [map_commutatorElement, commutatorElement_def]
    exact mul_mem ((pCore_normal_assembly 2 _).conj_mem _ ha₀ _) (inv_mem ha₀)
  have hodd : Odd (orderOf (π ⁅y₀, a₀⁆)) := by
    refine Odd.of_dvd_nat (odd_orderOf_of_mem hY hcY) ((orderOf_map_dvd π _).trans ?_)
    rw [← Subgroup.orderOf_coe]
    rfl
  have h1 : π ⁅y₀, a₀⁆ = 1 :=
    eq_one_of_mem_of_odd_orderOf (pCore_isPGroup_assembly 2 _) hπ hodd
  exact ⟨⁅y₀, a₀⁆, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

end CFSG.Assembly.Dichotomy
