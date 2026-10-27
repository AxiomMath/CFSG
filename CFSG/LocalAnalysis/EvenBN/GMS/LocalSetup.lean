module

public import CFSG.LocalAnalysis.SteinbergBNGMSLinearLocalApplication
public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearData
public import CFSG.LocalAnalysis.SteinbergBTGMSNormalRootSinger
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (even_SL2_full_automorphism_semilinear_model)
open scoped MatrixGroups

structure LocalSetting {H : Type*} [Group H] [Finite H] (A : Subgroup H) (t : H)
    (U V D : Subgroup H) (n : ℕ) : Prop where
  oddCore_eq_bot : CFSG.Open.standardComponentOddCore H = ⊥
  app : GMSLinearLocalApplication A t U V D n

namespace LocalSetting

variable {H : Type*} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H} {n : ℕ}

section Basic

variable (h : LocalSetting A t U V D n)
include h

theorem two_le : 2 ≤ n := h.app.1

theorem four_le : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le

theorem orderOf_t : orderOf t = 2 := h.app.2.1

theorem t_mul_t : t * t = 1 := by
  rw [← sq, ← h.orderOf_t, pow_orderOf_eq_one]

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t

theorem t_ne_one : t ≠ 1 := by
  intro ht
  have h2 := h.orderOf_t
  rw [ht, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem isStandard : CFSG.Assembly.ComponentType.IsStandardSubgroup A := h.app.2.2.1.1

theorem not_normal : ¬ A.Normal := h.app.2.2.1.2.1

theorem t_mem_centralizer : t ∈ centralizer (A : Set H) := h.app.2.2.2.1.1

theorem exists_sylow_centralizer : ∃ S : Sylow 2 (centralizer (A : Set H)),
    (S : Subgroup (centralizer (A : Set H))) = (zpowers t).subgroupOf (centralizer (A : Set H)) :=
  h.app.2.2.2.1.2.1

theorem le_centralizer : A ≤ centralizer ({t} : Set H) := h.app.2.2.2.1.2.2.1

theorem centralizer_le_normalizer : centralizer ({t} : Set H) ≤ normalizer (A : Set H) :=
  (normal_subgroupOf_iff_le_normalizer h.le_centralizer).mp h.app.2.2.2.1.2.2.2

theorem normalizer_zpowers : normalizer (zpowers t : Set H) = centralizer ({t} : Set H) :=
  CFSG.SeitzReduction.RankOne.normalizer_zpowers_eq_centralizer_of_involution h.orderOf_t

theorem U_le : U ≤ A := h.app.2.2.2.2.1.1

theorem exists_sylow_U : ∃ S : Sylow 2 A, (S : Subgroup A) = U.subgroupOf A :=
  h.app.2.2.2.2.1.2.1

theorem isSylowOf_U : IsSylowOf 2 U A := by
  obtain ⟨S, hS⟩ := h.exists_sylow_U
  exact ⟨S, by rw [hS, subgroupOf_map_subtype, inf_of_le_left h.U_le]⟩

theorem U_le_centralizer : U ≤ centralizer ({t} : Set H) := h.U_le.trans h.le_centralizer

theorem isElementaryAbelian_V : IsElementaryAbelian 2 V := h.app.2.2.2.2.1.2.2.1

theorem card_V : Nat.card V = (2 ^ n) ^ 2 := h.app.2.2.2.2.1.2.2.2.1

theorem t_mem_normalizer_V : t ∈ normalizer (V : Set H) := h.app.2.2.2.2.1.2.2.2.2.1

theorem V_inf_centralizer : V ⊓ centralizer ({t} : Set H) = U :=
  h.app.2.2.2.2.1.2.2.2.2.2.2.1

theorem closure_commutator : closure {x | ∃ v ∈ V, x = v⁻¹ * (t⁻¹ * v * t)} = U :=
  h.app.2.2.2.2.1.2.2.2.2.2.2.2

theorem U_le_V : U ≤ V := h.app.le.1

theorem D_le : D ≤ A ⊓ normalizer (U : Set H) := h.app.2.2.2.2.2.1.1

theorem D_le_A : D ≤ A := h.D_le.trans inf_le_left

theorem card_D : Nat.card D = 2 ^ n - 1 := h.app.2.2.2.2.2.1.2.2.1

theorem D_le_centralizer : D ≤ centralizer ({t} : Set H) := h.app.2.2.2.2.2.1.2.2.2.2.2.2.1

theorem odd_card_D : Odd (Nat.card D) := by
  rw [h.card_D]
  have : 2 ^ n % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by have := h.two_le; omega))
  have := h.four_le
  exact Nat.odd_iff.mpr (by omega)

theorem D_ne_bot : D ≠ ⊥ := by
  intro hD
  have h1 := h.card_D
  rw [hD, Subgroup.card_bot] at h1
  have := h.four_le
  omega

theorem nonempty_mulEquiv_psl2 : Nonempty (A ≃* PSL(2, GaloisField 2 n)) := by
  obtain ⟨hn, -, ⟨-, -, k, _, _, hk, ⟨α⟩⟩, -⟩ := h.app
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk' : Nat.card k = 2 ^ n := by rw [Nat.card_eq_fintype_card, hk]
  exact ⟨α.trans ((CFSG.ClassicalModels.specialLinearFieldEquiv
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField k 2 n (by omega) hk') (Fin 2)).trans
    CFSG.Walter.psl2MulEquivSL2OfCharTwo.symm)⟩

theorem isSimpleGroup : IsSimpleGroup A := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_psl2
  exact CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
    (Or.inl ⟨n, h.two_le, ⟨e⟩⟩)

theorem center_eq_bot : center A = ⊥ := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_psl2
  let e' : A ≃* SL(2, GaloisField 2 n) := e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
  have h1 : (center A).map e'.toMonoidHom = ⊥ := by
    have h2 : (center A).map e'.toMonoidHom = center SL(2, GaloisField 2 n) := map_center_eq e'
    rw [h2, CFSG.Walter.sl2_center_eq_bot_of_charTwo]
  exact (map_eq_bot_iff_of_injective _ e'.injective).mp h1

theorem inf_centralizer_eq_bot : A ⊓ centralizer (A : Set H) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxC⟩ := mem_inf.mp hx
  have hZ : (⟨x, hxA⟩ : A) ∈ center A :=
    mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp hxC y y.2)
  rw [h.center_eq_bot, mem_bot] at hZ
  exact mem_bot.mpr (congrArg Subtype.val hZ)

theorem isElementaryAbelian_U : IsElementaryAbelian 2 U := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_psl2
  exact (CFSG.SeitzReduction.RankOne.exists_singer_torus_of_psl2 h.two_le e h.U_le
    h.exists_sylow_U).1

theorem card_U : Nat.card U = 2 ^ n := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_psl2
  exact (CFSG.SeitzReduction.RankOne.exists_singer_torus_of_psl2 h.two_le e h.U_le
    h.exists_sylow_U).2.1

theorem U_comm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.isElementaryAbelian_U.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem U_mul_self : ∀ u ∈ U, u * u = 1 := fun u hu => by
  have := h.isElementaryAbelian_U
  rw [← sq]
  exact elemPow_eq_one_of_isElementaryAbelian u hu

theorem t_mul_comm : ∀ u ∈ U, u * t = t * u := fun _ hu =>
  mem_centralizer_singleton_iff.mp (h.U_le_centralizer hu)

theorem U_inf_zpowers : U ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxU, hxt⟩ := mem_inf.mp hx
  have h1 : x ∈ A ⊓ centralizer (A : Set H) :=
    mem_inf.mpr ⟨h.U_le hxU, zpowers_le.mpr h.t_mem_centralizer hxt⟩
  rwa [h.inf_centralizer_eq_bot] at h1

theorem t_not_mem_U : t ∉ U := fun ht => h.t_ne_one (by
  have h1 : t ∈ U ⊓ zpowers t := mem_inf.mpr ⟨ht, mem_zpowers t⟩
  rwa [h.U_inf_zpowers, mem_bot] at h1)

theorem card_le_two {X : Subgroup H} (hXC : X ≤ centralizer (A : Set H)) (hX : IsPGroup 2 X) :
    Nat.card X ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := h.exists_sylow_centralizer
  have hX' : IsPGroup 2 (X.subgroupOf (centralizer (A : Set H))) :=
    hX.of_equiv (subgroupOfEquivOfLe hXC).symm
  obtain ⟨P, hP⟩ := hX'.exists_le_sylow
  have h1 : Nat.card (X.subgroupOf (centralizer (A : Set H))) ≤ Nat.card P := card_le_of_le hP
  have h2 : Nat.card P = Nat.card S := Nat.card_congr (Sylow.equiv P S).toEquiv
  have h3 : Nat.card (S : Subgroup (centralizer (A : Set H))) = 2 := by
    rw [hS, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr h.t_mem_centralizer)).toEquiv,
      Nat.card_zpowers, h.orderOf_t]
  have h4 : Nat.card (X.subgroupOf (centralizer (A : Set H))) = Nat.card X :=
    Nat.card_congr (subgroupOfEquivOfLe hXC).toEquiv
  have h5 : Nat.card (S : Subgroup (centralizer (A : Set H))) = Nat.card S := rfl
  omega

theorem isPGroup_zpowers : IsPGroup 2 (zpowers t) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_t, pow_one])

theorem mem_zpowers_of_pow_eq_one {c : H} (hcA : c ∈ centralizer (A : Set H))
    (hct : c ∈ centralizer ({t} : Set H)) {e : ℕ} (hce : c ^ 2 ^ e = 1) : c ∈ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : IsPGroup 2 (zpowers c) := fun g => ⟨e, by
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hce, one_zpow, OneMemClass.coe_one]⟩
  have hle : zpowers c ≤ normalizer (zpowers t : Set H) := by
    rw [h.normalizer_zpowers]
    exact zpowers_le.mpr hct
  have hK := IsPGroup.to_sup_of_normal_right' hc h.isPGroup_zpowers hle
  have hKC : zpowers c ⊔ zpowers t ≤ centralizer (A : Set H) :=
    sup_le (zpowers_le.mpr hcA) (zpowers_le.mpr h.t_mem_centralizer)
  have hcard := h.card_le_two hKC hK
  have heq : zpowers t = zpowers c ⊔ zpowers t :=
    eq_of_le_of_card_ge le_sup_right (by rw [Nat.card_zpowers, h.orderOf_t]; exact hcard)
  rw [heq]
  exact mem_sup_left (mem_zpowers c)

theorem exists_isSylowOf : ∃ T : Subgroup H, IsSylowOf 2 T (centralizer ({t} : Set H)) ∧ U ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (U.subgroupOf (centralizer ({t} : Set H))) :=
    (@IsElementaryAbelian.isPGroup 2 U _ h.isElementaryAbelian_U).of_equiv
      (subgroupOfEquivOfLe h.U_le_centralizer).symm
  obtain ⟨P, hP⟩ := hU2.exists_le_sylow
  refine ⟨(P : Subgroup (centralizer ({t} : Set H))).map (centralizer ({t} : Set H)).subtype,
    ⟨P, rfl⟩, fun u hu => ⟨⟨u, h.U_le_centralizer hu⟩, hP ?_, rfl⟩⟩
  exact hu

end Basic

section Sylow

variable (h : LocalSetting A t U V D n) {T : Subgroup H}
  (hT : IsSylowOf 2 T (centralizer ({t} : Set H)))
include h hT

theorem mem_T : t ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : T ≤ normalizer (zpowers t : Set H) := by
    rw [h.normalizer_zpowers]
    exact hT.le
  have hK := IsPGroup.to_sup_of_normal_right' hT.isPGroup h.isPGroup_zpowers hle
  have hKC : T ⊔ zpowers t ≤ centralizer ({t} : Set H) :=
    sup_le hT.le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  rw [← hT.eq_of_le le_sup_left hKC hK]
  exact mem_sup_right (mem_zpowers t)

theorem T_le_normalizer_A : T ≤ normalizer (A : Set H) := hT.le.trans h.centralizer_le_normalizer

end Sylow

section SylowU

variable (h : LocalSetting A t U V D n) {T : Subgroup H}
  (hT : IsSylowOf 2 T (centralizer ({t} : Set H))) (hUT : U ≤ T)
include h hT hUT

theorem T_inf_A : T ⊓ A = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.isSylowOf_U.eq_of_le (le_inf hUT h.U_le) inf_le_right (hT.isPGroup.to_le inf_le_left)

theorem T_le_normalizer_U : T ≤ normalizer (U : Set H) := by
  rw [← h.T_inf_A hT hUT]
  exact (le_inf le_normalizer (h.T_le_normalizer_A hT)).trans inf_normalizer_le_normalizer_inf

theorem B_le_T : U ⊔ zpowers t ≤ T := sup_le hUT (zpowers_le.mpr (h.mem_T hT))

theorem T_le_normalizer_B : T ≤ normalizer ((U ⊔ zpowers t : Subgroup H) : Set H) := by
  have htN : T ≤ normalizer (zpowers t : Set H) := by
    rw [h.normalizer_zpowers]
    exact hT.le
  exact (le_inf (h.T_le_normalizer_U hT hUT) htN).trans (inf_normalizer_le_normalizer_sup _ _)

theorem B_normal : ((U ⊔ zpowers t).subgroupOf T).Normal :=
  (normal_subgroupOf_iff_le_normalizer (h.B_le_T hT hUT)).mpr (h.T_le_normalizer_B hT hUT)

theorem mem_of_inner {x : H} (hx : x ∈ T) {a : H} (ha : a ∈ A)
    (hxa : ∀ y ∈ A, x * y * x⁻¹ = a * y * a⁻¹) : x ∈ U ⊔ zpowers t := by
  have hc : a⁻¹ * x ∈ centralizer (A : Set H) := mem_centralizer_iff.mpr fun y hy => by
    calc y * (a⁻¹ * x) = a⁻¹ * (a * y * a⁻¹) * x := by group
      _ = a⁻¹ * (x * y * x⁻¹) * x := by rw [hxa y hy]
      _ = a⁻¹ * x * y := by group
  have hct : a⁻¹ * x ∈ centralizer ({t} : Set H) :=
    mul_mem (inv_mem (h.le_centralizer ha)) (hT.le hx)
  obtain ⟨e, he⟩ := hT.isPGroup ⟨x, hx⟩
  have hxe : x ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  have hcomm : Commute a (a⁻¹ * x) := mem_centralizer_iff.mp hc a ha
  have h1 : a ^ 2 ^ e * (a⁻¹ * x) ^ 2 ^ e = 1 := by
    rw [← hcomm.mul_pow, mul_inv_cancel_left, hxe]
  have h2 : (a⁻¹ * x) ^ 2 ^ e ∈ A ⊓ centralizer (A : Set H) := by
    refine mem_inf.mpr ⟨?_, pow_mem hc _⟩
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_mem (pow_mem ha _)
  rw [h.inf_centralizer_eq_bot, mem_bot] at h2
  have hcz := h.mem_zpowers_of_pow_eq_one hc hct h2
  have haT : a ∈ T := by
    have h3 : a = x * (a⁻¹ * x)⁻¹ := by group
    rw [h3]
    exact mul_mem hx (inv_mem (zpowers_le.mpr (h.mem_T hT) hcz))
  have haU : a ∈ U := by
    rw [← h.T_inf_A hT hUT]
    exact mem_inf.mpr ⟨haT, ha⟩
  have h4 : x = a * (a⁻¹ * x) := by group
  rw [h4]
  exact mul_mem (mem_sup_left haU) (mem_sup_right hcz)

theorem T_inf_sup : T ⊓ (A ⊔ centralizer (A : Set H)) = U ⊔ zpowers t := by
  refine le_antisymm (fun x hx => ?_) (le_inf (h.B_le_T hT hUT)
    (sup_le (h.U_le.trans le_sup_left) (zpowers_le.mpr (mem_sup_right h.t_mem_centralizer))))
  obtain ⟨hxT, hxAC⟩ := mem_inf.mp hx
  have hAN : A ≤ normalizer (centralizer (A : Set H) : Set H) :=
    (le_centralizer_iff.mpr le_rfl).trans (Subgroup.centralizer_le_normalizer _)
  have hxAC' : x ∈ ((A ⊔ centralizer (A : Set H) : Subgroup H) : Set H) := hxAC
  rw [coe_mul_of_left_le_normalizer_right A _ hAN] at hxAC'
  obtain ⟨a, ha, c, hc, rfl⟩ := hxAC'
  refine h.mem_of_inner hT hUT hxT ha fun y hy => ?_
  have hcy : c * y = y * c := (mem_centralizer_iff.mp hc y hy).symm
  calc a * c * y * (a * c)⁻¹ = a * (c * y) * c⁻¹ * a⁻¹ := by group
    _ = a * (y * c) * c⁻¹ * a⁻¹ := by rw [hcy]
    _ = a * y * a⁻¹ := by group

theorem T_inf_centralizer_U : T ⊓ centralizer (U : Set H) = U ⊔ zpowers t := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_psl2
  refine le_antisymm (fun x hx => ?_) (le_inf (h.B_le_T hT hUT) (sup_le
    (fun u hu => mem_centralizer_iff.mpr fun v hv => h.U_comm v hv u hu)
    (zpowers_le.mpr (mem_centralizer_iff.mpr fun u hu => h.t_mul_comm u hu))))
  obtain ⟨hxT, hxC⟩ := mem_inf.mp hx
  obtain ⟨r, hr, hxr⟩ := CFSG.SeitzReduction.RankOne.exists_inner_of_centralizes_sylow_psl2
    h.two_le e h.U_le h.exists_sylow_U (h.T_le_normalizer_A hT hxT) hxC
  exact h.mem_of_inner hT hUT hxT (h.U_le hr) hxr

theorem isCyclic_quotient [((U ⊔ zpowers t).subgroupOf T).Normal] :
    IsCyclic (T ⧸ (U ⊔ zpowers t).subgroupOf T) ∧
      Nat.card (T ⧸ (U ⊔ zpowers t).subgroupOf T) ∣ n := by
  classical
  obtain ⟨hn, -, ⟨-, -, k, _, _, hk, ⟨α⟩⟩, -⟩ := h.app
  have hk' : Nat.card k = 2 ^ n := by rw [Nat.card_eq_fintype_card, hk]
  obtain ⟨-, -, hcyc, hcard, -⟩ :=
    even_SL2_full_automorphism_semilinear_model (F := k) (n := n) (by omega) hk'
  have hcycA : IsCyclic (Outer A) := (equivalence α).isCyclic.mpr hcyc
  have hcardA : Nat.card (Outer A) = n := (Nat.card_congr (equivalence α).toEquiv).trans hcard
  let φ : T →* Outer A := (QuotientGroup.mk' (inner A)).comp
    (A.normalizerMonoidHom.comp (inclusion (h.T_le_normalizer_A hT)))
  have hφ : ∀ x : T, φ x = 1 ↔ ∃ a : A, ∀ y : A,
      ((a : H) * y * (a : H)⁻¹ : H) = (x : H) * y * (x : H)⁻¹ := by
    intro x
    change QuotientGroup.mk' (inner A) (A.normalizerMonoidHom
      (inclusion (h.T_le_normalizer_A hT) x)) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, fun y => ?_⟩
      have h1 := congrArg (fun β : MulAut A => ((β y : A) : H)) ha
      simpa using h1
    · rintro ⟨a, ha⟩
      refine ⟨a, MulEquiv.ext fun y => Subtype.ext ?_⟩
      simpa using ha y
  have hker : φ.ker = (U ⊔ zpowers t).subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hφ]
    constructor
    · rintro ⟨a, ha⟩
      exact h.mem_of_inner hT hUT x.2 a.2 fun y hy => (ha ⟨y, hy⟩).symm
    · intro hx
      have hle : zpowers t ≤ normalizer (U : Set H) := zpowers_le.mpr
        (Subgroup.centralizer_le_normalizer _
          (mem_centralizer_iff.mpr fun u hu => h.t_mul_comm u hu))
      have hx' : (x : H) ∈ ((U ⊔ zpowers t : Subgroup H) : Set H) := hx
      rw [coe_mul_of_right_le_normalizer_left U _ hle] at hx'
      obtain ⟨u, hu, c, hc, hxuc⟩ := hx'
      refine ⟨⟨u, h.U_le hu⟩, fun y => ?_⟩
      have hcA : c ∈ centralizer (A : Set H) := zpowers_le.mpr h.t_mem_centralizer hc
      have hcy : c * (y : H) = y * c := (mem_centralizer_iff.mp hcA y y.2).symm
      rw [← hxuc]
      calc (u : H) * y * u⁻¹ = u * (c * y * c⁻¹) * u⁻¹ := by rw [hcy, mul_inv_cancel_right]
        _ = u * c * y * (u * c)⁻¹ := by group
  let eQ : T ⧸ (U ⊔ zpowers t).subgroupOf T ≃* φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  refine ⟨eQ.isCyclic.mpr inferInstance, ?_⟩
  rw [Nat.card_congr eQ.toEquiv, ← hcardA]
  exact Subgroup.card_subgroup_dvd_card φ.range

theorem gmsNormalRootData (hn : 3 ≤ n) :
    GMSNormalRootData (centralizer (A : Set H)) (zpowers t) A U T n := by
  have hstd := h.isStandard
  have hNC := h.normalizer_zpowers
  obtain ⟨-, -, -, -, -, ⟨hDle, hDcyc, hDcard, -, hUD, -, -, hreg, -⟩, -⟩ := h.app
  have hU1 : ∃ x ∈ U, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : U = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    have h1 := h.card_U
    rw [hbot, Subgroup.card_bot] at h1
    have := h.four_le
    omega
  obtain ⟨hQcyc, hQcard, hQreg⟩ :=
    CFSG.SeitzReduction.RankOne.gmsNormalizerQuotient_of_regular_complement h.U_le h.U_comm
      (hDle.trans inf_le_left) (hDle.trans inf_le_right) hUD.symm.le hDcyc hreg hU1
  refine ⟨hn, CFSG.Open.standardComponentIsStandard.tightlyEmbedded_centralizer hstd,
    ⟨IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← h.orderOf_t]; exact pow_orderOf_eq_one t),
      zpowers_le.mpr h.t_mem_centralizer, h.exists_sylow_centralizer⟩,
    ⟨hNC ▸ h.le_centralizer, by rw [hNC]; exact h.app.2.2.2.1.2.2.2, fun a ha => ?_⟩,
    ⟨h.isElementaryAbelian_U, h.U_le, h.exists_sylow_U, h.card_U⟩,
    ⟨hQcyc, hQcard.trans hDcard, hQreg⟩,
    ⟨hNC ▸ hT.le, ?_, hUT, zpowers_le.mpr (h.mem_T hT), h.T_le_normalizer_U hT hUT,
      h.U_inf_zpowers, h.T_inf_centralizer_U hT hUT, h.B_normal hT hUT⟩⟩
  · refine mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (mem_centralizer_iff.mp h.t_mem_centralizer a ha).symm k).eq
  · rw [hNC]
    exact hT.exists_sylow_eq_subgroupOf

theorem card_inf_centralizer_sq_le {p : H} (hp : p ∈ T) (hpB : p ∉ U ⊔ zpowers t) :
    Nat.card (U ⊓ centralizer ({p} : Set H) : Subgroup H) ^ 2 ≤ 2 ^ n := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · have hn2 : n = 2 := by have := h.two_le; omega
    have hne : U ⊓ centralizer ({p} : Set H) ≠ U := by
      intro heq
      apply hpB
      rw [← h.T_inf_centralizer_U hT hUT]
      refine mem_inf.mpr ⟨hp, mem_centralizer_iff.mpr fun u hu => ?_⟩
      have hu' : u ∈ U ⊓ centralizer ({p} : Set H) := by rw [heq]; exact hu
      exact mem_centralizer_singleton_iff.mp (mem_inf.mp hu').2
    have hlt : Nat.card (U ⊓ centralizer ({p} : Set H) : Subgroup H) < Nat.card U :=
      card_lt_of_lt (lt_of_le_of_ne inf_le_left hne)
    have hdvd : Nat.card (U ⊓ centralizer ({p} : Set H) : Subgroup H) ∣ Nat.card U :=
      card_dvd_of_le inf_le_left
    rw [h.card_U, hn2] at hdvd
    rw [h.card_U, hn2] at hlt
    rw [hn2]
    obtain ⟨j, hj, hcj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hcj] at hlt ⊢
    interval_cases j <;> simp_all
  · obtain ⟨⟨K, _, _, _, hKcard, e, -, -, φ, hequiv, -, hker⟩, -⟩ :=
      SteinbergBT.gms_normal_root_singer_action_and_weak_closure (h.gmsNormalRootData hT hUT hn)
    have hφ : φ ⟨p, hp⟩ ≠ 1 := fun h1 => hpB (by
      have hmem : (⟨p, hp⟩ : T) ∈ φ.ker := h1
      rw [hker] at hmem
      exact hmem)
    exact SteinbergBT.card_inf_centralizer_sq_le hKcard e φ hequiv (h.T_le_normalizer_U hT hUT)
      ⟨p, hp⟩ hφ

end SylowU

end LocalSetting

end CFSG.LocalAnalysis.EvenBN.GMS
