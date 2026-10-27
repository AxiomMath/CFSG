module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Sh
public import CFSG.GH74.E2.TermBasic
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.Walter.TwoRank
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
public import CFSG.LieType.SteinbergBRTwoRankBound
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abOPrime
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped commutatorElement

section TwoElements

variable {G : Type*} [Group G]

theorem mem_oPrimeResidualOf_of_pow {X : Subgroup G} {x : G} (hx : x ∈ X) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ∈ oPrimeResidualOf 2 X := by
  rw [oPrimeResidualOf_eq_closure']
  exact Subgroup.subset_closure ⟨hx, k, hk⟩

theorem subgroupOf_oPrimeResidualOf (X : Subgroup G) :
    (oPrimeResidualOf 2 X).subgroupOf X = oPrimeResidual 2 ↥X :=
  Subgroup.comap_map_eq_self_of_injective X.subtype_injective _

end TwoElements


section Tools

theorem pCore_two_le_centralizer_layer {G : Type*} [Group G] [Finite G] :
    pCore 2 G ≤ centralizer (layer G : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.WholeGroup.pCore_le_centralizer_layer 2

theorem map_center_layer_le_pCore_two {G : Type*} [Group G] [Finite G] (hO : pPrimeCore 2 G = ⊥) :
    (center ↥(layer G)).map (layer G).subtype ≤ pCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot 2 hO

theorem isSimpleGroup_of_isQuasisimple_center {K : Type*} [Group K] (hK : IsQuasisimple K)
    (hZ : center K = ⊥) : IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨-, hs, a, b, hab⟩ := hK
  let e : K ⧸ center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨e.symm.isSimpleGroup, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem exists_four_group_of_simple {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) :
    ∃ V : Subgroup K, (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x ^ 2 = 1) ∧
      Nat.card V = 4 := by
  classical
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab).1
  have h2 : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup K) := CFSG.Walter.two_le_twoRank K hnab heven
  obtain ⟨E, -, hE, hEcard⟩ := SectionRank.exists_pRank (G := K) (p := 2) one_lt_two ⊤
  obtain ⟨E', hE'4, -, hE'E⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := ⊥) (L := E) (n := 2) (by rw [card_bot]; exact one_dvd _)
    (by rw [hEcard]; exact pow_dvd_pow 2 h2) bot_le
  refine ⟨E', ?_, ?_, hE'4⟩
  · intro x hx y hy
    have := hE.1.is_comm.comm (⟨x, hE'E hx⟩ : E) ⟨y, hE'E hy⟩
    exact congrArg Subtype.val this
  · intro x hx
    exact hE.2 x (hE'E hx)

theorem exists_elementary_sixteen' {S : Type*} [Group S] {V₁ V₂ : Subgroup S}
    (h₁c : ∀ x ∈ V₁, ∀ y ∈ V₁, x * y = y * x) (h₂c : ∀ x ∈ V₂, ∀ y ∈ V₂, x * y = y * x)
    (h₁2 : ∀ x ∈ V₁, x ^ 2 = 1) (h₂2 : ∀ x ∈ V₂, x ^ 2 = 1) (h₁4 : Nat.card V₁ = 4)
    (h₂4 : Nat.card V₂ = 4) (h12 : ∀ x ∈ V₁, ∀ y ∈ V₂, x * y = y * x) (hinf : V₁ ⊓ V₂ = ⊥) :
    ∃ V : Subgroup S, (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x ^ 2 = 1) ∧
      Nat.card V = 16 := by
  have hcomm : ∀ (a : V₁) (b : V₂), Commute (V₁.subtype a) (V₂.subtype b) :=
    fun a b => h12 a a.2 b b.2
  set f : V₁ × V₂ →* S := V₁.subtype.noncommCoprod V₂.subtype hcomm with hf
  have hfapp : ∀ x : V₁ × V₂, f x = (x.1 : S) * (x.2 : S) := fun x => rfl
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hx
    rw [MonoidHom.mem_ker, hfapp] at hx
    have ha : (a : S) = (b : S)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have hab : (a : S) ∈ V₁ ⊓ V₂ := ⟨a.2, ha ▸ V₂.inv_mem b.2⟩
    rw [hinf, mem_bot] at hab
    have hb : (b : S) = 1 := by rw [hab] at ha; exact inv_eq_one.mp ha.symm
    exact mem_bot.mpr (Prod.ext (Subtype.ext hab) (Subtype.ext hb))
  have hfc : ∀ x y : V₁ × V₂, f x * f y = f y * f x := by
    intro x y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (Subtype.ext (h₁c _ x.1.2 _ y.1.2)) (Subtype.ext (h₂c _ x.2.2 _ y.2.2))
  refine ⟨f.range, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hfc x y
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Prod.ext (Subtype.ext (h₁2 _ x.1.2)) (Subtype.ext (h₂2 _ x.2.2))
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, h₁4, h₂4]

theorem le_centralizer_of_components' {Y : Type*} [Group Y] [Finite Y] {K K' : Subgroup Y}
    (hK : IsComponent K) (hK' : IsComponent K') (hne : K ≠ K') :
    K ≤ centralizer (K' : Set Y) := by
  rcases LocalCores.distinct_components_commute hK hK' with h | h
  · exact absurd h hne
  · exact commutator_eq_bot_iff_le_centralizer.1 h

end Tools

section PCore

variable {H : Type} [Group H] [Finite H]

theorem pCore_two_eq_bot_of_shape {z u : H} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (S : Shape ↥(oPrimeResidualOf 2 (centralizer ({z} : Set H))) F₁ F₂) (hzS : (S.z : H) = z)
    (hJ₁ : S.J₁ ≤ layer H) (hJ₂ : S.J₂ ≤ layer H) (P : Sylow 2 H)
    (hPz : ∀ s ∈ (P : Subgroup H), s * z = z * s) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hconj : IsConj z u) : pCore 2 H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ q ∈ pCore 2 H, q = 1 ∨ q = z := by
    intro q hq
    have hqP : q ∈ (P : Subgroup H) := IsPGroup.le_sylow_of_normal (pCore_isPGroup (G := H) (p := 2)) P hq
    have hqC : q ∈ centralizer ({z} : Set H) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hPz q hqP)
    obtain ⟨k, hk⟩ := (pCore_isPGroup (G := H) (p := 2)) ⟨q, hq⟩
    have hqY : q ∈ oPrimeResidualOf 2 (centralizer ({z} : Set H)) :=
      mem_oPrimeResidualOf_of_pow hqC (k := k) (by simpa using congrArg Subtype.val hk)
    have hcl : q ∈ centralizer ((layer H : Subgroup H) : Set H) :=
      pCore_two_le_centralizer_layer hq
    have h₁ : ∀ x ∈ S.J₁, q * x = x * q := fun x hx =>
      (Subgroup.mem_centralizer_iff.1 hcl x (hJ₁ hx)).symm
    have h₂ : ∀ x ∈ S.J₂, q * x = x * q := fun x hx =>
      (Subgroup.mem_centralizer_iff.1 hcl x (hJ₂ hx)).symm
    rcases S.eq_one_or_eq_zH_of_centralizes hqY h₁ h₂ with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hzS)
  rw [eq_bot_iff]
  intro q hq
  rw [mem_bot]
  rcases key q hq with h | h
  · exact h
  · exfalso
    have hz : z ∈ pCore 2 H := h ▸ hq
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    have hu : u ∈ pCore 2 H := hc ▸ (pCore_normal (p := 2) (G := H)).conj_mem z hz c
    rcases key u hu with h' | h'
    · exact hu1 h'
    · exact huz h'

end PCore


section Simple

variable {H : Type} [Group H] [Finite H]

theorem center_layer_eq_bot (hO : pPrimeCore 2 H = ⊥) (hO₂ : pCore 2 H = ⊥) :
    center ↥(layer H) = ⊥ := by
  have h := map_center_layer_le_pCore_two hO
  rw [hO₂, le_bot_iff] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ (layer H).subtype_injective).1 h

theorem center_component_eq_bot (hcen : center ↥(layer H) = ⊥) {C : Subgroup H}
    (hC : IsComponent C) : center ↥C = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxz := CFSG.LocalCores.center_component_le_centralizer_layer hC
    (Subgroup.mem_map_of_mem C.subtype hx)
  have hCL : C ≤ layer H := le_sSup hC
  have hxL : (x : H) ∈ layer H := hCL x.2
  have hmem : (⟨x, hxL⟩ : ↥(layer H)) ∈ center ↥(layer H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxz) g.1 g.2)
  rw [hcen, mem_bot] at hmem
  rw [mem_bot]
  have h3 : (x : H) = 1 := congrArg Subtype.val hmem
  exact Subtype.ext h3

omit [Finite H] in
theorem exists_isComponent_of_layer_ne_bot (hne : layer H ≠ ⊥) : ∃ C : Subgroup H, IsComponent C := by
  by_contra hcon
  push Not at hcon
  apply hne
  have : {K : Subgroup H | IsComponent K} = ∅ := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact hcon K
  simp only [CFSG.layer.eq_sSup]
  rw [this, sSup_empty]

theorem le_pRank_two_of_comm_sq {V : Subgroup H} (hc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (h2 : ∀ x ∈ V, x ^ 2 = 1) {k : ℕ} (hk : Nat.card V = 2 ^ k) : k ≤ CFSG.pRank 2 H := by
  have : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
  have hE : CFSG.IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using h2 x x.2) }
  exact CFSG.LieType.SteinbergBR.le_pRank_of_card (by norm_num) V hE hk

theorem false_of_two_components (hcen : center ↥(layer H) = ⊥)
    (hr : CFSG.pRank 2 H ≤ 3) {C₁ C₂ : Subgroup H} (h₁ : IsComponent C₁) (h₂ : IsComponent C₂)
    (hne : C₁ ≠ C₂) : False := by
  have hZ₁ := center_component_eq_bot hcen h₁
  have hZ₂ := center_component_eq_bot hcen h₂
  obtain ⟨hs₁, hnab₁⟩ := isSimpleGroup_of_isQuasisimple_center h₁.1 hZ₁
  obtain ⟨hs₂, hnab₂⟩ := isSimpleGroup_of_isQuasisimple_center h₂.1 hZ₂
  obtain ⟨V₁, hV₁c, hV₁2, hV₁4⟩ := exists_four_group_of_simple (K := ↥C₁) hnab₁
  obtain ⟨V₂, hV₂c, hV₂2, hV₂4⟩ := exists_four_group_of_simple (K := ↥C₂) hnab₂
  have h12 : C₁ ≤ centralizer (C₂ : Set H) := le_centralizer_of_components' h₁ h₂ hne
  have hcomm : ∀ x ∈ V₁.map C₁.subtype, ∀ y ∈ V₂.map C₂.subtype, x * y = y * x := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (h12 a.2) b b.2).symm
  have hinf : V₁.map C₁.subtype ⊓ V₂.map C₂.subtype = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, -, rfl⟩, ⟨b, -, hb⟩⟩
    have hxZ : a ∈ center ↥C₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hbx : (b : H) = (a : H) := hb
      have h3 := (Subgroup.mem_centralizer_iff.mp (h12 g.2)) b b.2
      rw [hbx] at h3
      exact Subtype.ext h3.symm
    rw [hZ₁, mem_bot] at hxZ
    rw [mem_bot, hxZ]
    rfl
  obtain ⟨V, hVc, hV2, hV16⟩ := exists_elementary_sixteen'
    (V₁ := V₁.map C₁.subtype) (V₂ := V₂.map C₂.subtype)
    (by rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩; exact congrArg Subtype.val (hV₁c a ha b hb))
    (by rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩; exact congrArg Subtype.val (hV₂c a ha b hb))
    (by rintro _ ⟨a, ha, rfl⟩; exact congrArg Subtype.val (hV₁2 a ha))
    (by rintro _ ⟨a, ha, rfl⟩; exact congrArg Subtype.val (hV₂2 a ha))
    (by rw [Subgroup.card_map_of_injective C₁.subtype_injective, hV₁4])
    (by rw [Subgroup.card_map_of_injective C₂.subtype_injective, hV₂4])
    hcomm hinf
  have := le_pRank_two_of_comm_sq hVc hV2 (k := 4) (by rw [hV16]; norm_num)
  omega

theorem isSimpleGroup_layer (hO : pPrimeCore 2 H = ⊥)
    (hO₂ : pCore 2 H = ⊥) (hne : layer H ≠ ⊥) (hr : CFSG.pRank 2 H ≤ 3) :
    IsSimpleGroup ↥(layer H) ∧ ∃ a b : ↥(layer H), a * b ≠ b * a := by
  have hcen := center_layer_eq_bot hO hO₂
  obtain ⟨C, hC⟩ := exists_isComponent_of_layer_ne_bot hne
  have hset : {K : Subgroup H | IsComponent K} = {C} := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hK
      by_contra hKC
      exact false_of_two_components hcen hr hK hC hKC
    · rintro rfl
      exact hC
  have hL : layer H = C := by
    simp only [CFSG.layer.eq_sSup]
    rw [hset, sSup_singleton]
  have hZ := center_component_eq_bot hcen hC
  have e : ↥(layer H) ≃* ↥C := MulEquiv.subgroupCongr hL
  obtain ⟨hs, hnab⟩ := isSimpleGroup_of_isQuasisimple_center hC.1 hZ
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

end Simple


section Balance

variable {H : Type} [Group H] [Finite H] {F₁ F₂ : Type} [Field F₁] [Field F₂]

omit [Finite H] in
theorem isComponent_J₁ {X : Subgroup H} (S : Shape ↥(oPrimeResidualOf 2 X) F₁ F₂) [Finite F₁]
    (h4 : 4 ≤ Nat.card F₁) : IsComponent (S.J₁.subgroupOf X) := by
  have hJX : S.J₁ ≤ X := S.J₁_le.trans (Subgroup.map_subtype_le _)
  have hq : IsQuasisimple ↥(S.J₁.subgroupOf X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJX).symm
      (S.J₁_quasisimple h4)
  have hN : (oPrimeResidual 2 ↥X).Normal := CFSG.GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal 2 ↥X
  have hle : S.J₁.subgroupOf X ≤ oPrimeResidual 2 ↥X := by
    rw [← subgroupOf_oPrimeResidualOf X]
    exact Subgroup.subgroupOf_mono X S.J₁_le
  have hnorm : ((S.J₁.subgroupOf X).subgroupOf (oPrimeResidual 2 ↥X)).Normal := by
    refine ⟨fun a ha n => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at ha ⊢
    have hnY : (((n : ↥(oPrimeResidual 2 ↥X)) : ↥X) : H) ∈ oPrimeResidualOf 2 X :=
      Subgroup.mem_map_of_mem X.subtype n.2
    have := S.J₁_conj _ hnY _ ha
    simpa using this
  exact ⟨hq, Subgroup.IsSubnormal.trans hle hnorm.isSubnormal hN.isSubnormal⟩

omit [Finite H] in
theorem isComponent_J₂ {X : Subgroup H} (S : Shape ↥(oPrimeResidualOf 2 X) F₁ F₂) [Finite F₂]
    (h4 : 4 ≤ Nat.card F₂) : IsComponent (S.J₂.subgroupOf X) := by
  have hJX : S.J₂ ≤ X := S.J₂_le.trans (Subgroup.map_subtype_le _)
  have hq : IsQuasisimple ↥(S.J₂.subgroupOf X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJX).symm
      (S.J₂_quasisimple h4)
  have hN : (oPrimeResidual 2 ↥X).Normal := CFSG.GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal 2 ↥X
  have hle : S.J₂.subgroupOf X ≤ oPrimeResidual 2 ↥X := by
    rw [← subgroupOf_oPrimeResidualOf X]
    exact Subgroup.subgroupOf_mono X S.J₂_le
  have hnorm : ((S.J₂.subgroupOf X).subgroupOf (oPrimeResidual 2 ↥X)).Normal := by
    refine ⟨fun a ha n => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at ha ⊢
    have hnY : (((n : ↥(oPrimeResidual 2 ↥X)) : ↥X) : H) ∈ oPrimeResidualOf 2 X :=
      Subgroup.mem_map_of_mem X.subtype n.2
    have := S.J₂_conj _ hnY _ ha
    simpa using this
  exact ⟨hq, Subgroup.IsSubnormal.trans hle hnorm.isSubnormal hN.isSubnormal⟩

theorem J₁_le_layer {z : H} (hz : orderOf z = 2) (hcore : pPrimeCore 2 H = ⊥)
    (S : Shape ↥(oPrimeResidualOf 2 (centralizer ({z} : Set H))) F₁ F₂) [Finite F₁]
    (h4 : 4 ≤ Nat.card F₁) : S.J₁ ≤ layer H := by
  have hzz : z * z = 1 := by rw [← pow_two, ← hz]; exact pow_orderOf_eq_one z
  exact CFSG.GH74.E2.component_le_layer_of_balance hcore hzz (M := centralizer ({z} : Set H))
    (fun m => Subgroup.mem_centralizer_singleton_iff) (S.J₁_le.trans (Subgroup.map_subtype_le _))
    (isComponent_J₁ S h4)

theorem J₂_le_layer {z : H} (hz : orderOf z = 2) (hcore : pPrimeCore 2 H = ⊥)
    (S : Shape ↥(oPrimeResidualOf 2 (centralizer ({z} : Set H))) F₁ F₂) [Finite F₂]
    (h4 : 4 ≤ Nat.card F₂) : S.J₂ ≤ layer H := by
  have hzz : z * z = 1 := by rw [← pow_two, ← hz]; exact pow_orderOf_eq_one z
  exact CFSG.GH74.E2.component_le_layer_of_balance hcore hzz (M := centralizer ({z} : Set H))
    (fun m => Subgroup.mem_centralizer_singleton_iff) (S.J₂_le.trans (Subgroup.map_subtype_le _))
    (isComponent_J₂ S h4)

end Balance

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
