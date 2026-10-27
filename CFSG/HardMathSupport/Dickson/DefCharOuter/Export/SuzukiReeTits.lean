module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Shapes
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeG2Outer
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeFixedPoints
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallReeDescent
import CFSG.Adapters.StatedSmallProjOrders
import CFSG.RankThree.Chevalley.SteinbergCFSmallReeComponentCores

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Yardstones.Md42047359a2a (LieFamily lieFamily)
open scoped commutatorElement

namespace SuzukiReeTits

section Generic

theorem center_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center H := by
    rw [← Subgroup.map_center_eq e]
    exact ⟨z, hz, rfl⟩
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact e.injective (hz'.trans (map_one e).symm)

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnc : ∃ x y : G, x * y ≠ y * x) : Subgroup.center G = ⊥ := by
  rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)

theorem eq_one_of_forall_commute_commutator {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) (hs : IsSimpleGroup ↥(commutator G))
    (hnc : ∃ x y : ↥(commutator G), x * y ≠ y * x) {x : G}
    (hx : ∀ d ∈ commutator G, x * d = d * x) : x = 1 := by
  have hZD : Subgroup.center ↥(commutator G) = ⊥ := center_eq_bot_of_simple hnc
  have hcen : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    set c := x * g * x⁻¹ * g⁻¹ with hc
    have hcD : c ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top g)
    have hcc : ∀ d ∈ commutator G, c * d = d * c := by
      intro d hd
      have hd' : g⁻¹ * d * g ∈ commutator G := by
        have := (inferInstance : (commutator G).Normal).conj_mem d hd g⁻¹
        simpa using this
      have h1 : x * d = d * x := hx d hd
      have h2 : x * (g⁻¹ * d * g) = (g⁻¹ * d * g) * x := hx _ hd'
      have h3 : x⁻¹ * (g⁻¹ * d * g) = (g⁻¹ * d * g) * x⁻¹ := by
        calc x⁻¹ * (g⁻¹ * d * g) = x⁻¹ * ((g⁻¹ * d * g) * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * (g⁻¹ * d * g)) * x⁻¹ := by rw [h2]
          _ = (g⁻¹ * d * g) * x⁻¹ := by group
      calc c * d = x * (g * (x⁻¹ * (g⁻¹ * d * g)) * g⁻¹) := by rw [hc]; group
        _ = x * (g * ((g⁻¹ * d * g) * x⁻¹) * g⁻¹) := by rw [h3]
        _ = (x * d) * (g * x⁻¹ * g⁻¹) := by group
        _ = (d * x) * (g * x⁻¹ * g⁻¹) := by rw [h1]
        _ = d * c := by rw [hc]; group
    have hcZ : (⟨c, hcD⟩ : ↥(commutator G)) ∈ Subgroup.center ↥(commutator G) := by
      rw [Subgroup.mem_center_iff]
      intro d
      exact Subtype.ext (hcc d.1 d.2).symm
    rw [hZD, Subgroup.mem_bot] at hcZ
    have hc1 : c = 1 := congrArg Subtype.val hcZ
    calc g * x = (x * g * x⁻¹ * g⁻¹)⁻¹ * (x * g) := by group
      _ = x * g := by rw [← hc, hc1, inv_one, one_mul]
  rw [hZ, Subgroup.mem_bot] at hcen
  exact hcen

theorem card_of_isLTwoTwentySeven {X : Type} [Group X] (h : IsLTwoTwentySeven X) :
    Nat.card X = 9828 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd (by rw [hF]; decide), hF]
  norm_num

theorem ree_order_lt {q₁ q₀ : ℕ} (h2 : 2 ≤ q₁) (hlt : q₁ < q₀) :
    q₁ ^ 3 * (q₁ ^ 3 + 1) * (q₁ - 1) < q₀ ^ 3 * (q₀ ^ 3 + 1) * (q₀ - 1) := by
  have h1 : q₁ ^ 3 < q₀ ^ 3 := Nat.pow_lt_pow_left hlt (by norm_num)
  have h3 : q₁ - 1 < q₀ - 1 := by omega
  have h4 : 0 < q₁ - 1 := by omega
  calc q₁ ^ 3 * (q₁ ^ 3 + 1) * (q₁ - 1) < q₀ ^ 3 * (q₀ ^ 3 + 1) * (q₁ - 1) := by
        apply Nat.mul_lt_mul_of_pos_right _ h4
        exact Nat.mul_lt_mul'' h1 (by omega)
    _ < q₀ ^ 3 * (q₀ ^ 3 + 1) * (q₀ - 1) := by
        apply Nat.mul_lt_mul_of_pos_left h3
        exact Nat.mul_pos (pow_pos (by omega) 3) (by omega)

theorem mulAut_congr_self {G : Type*} [Group G] (δ φ : MulAut G) :
    MulAut.congr δ φ = δ * φ * δ⁻¹ := by
  ext x
  rfl

theorem mul_conj_mul_inv {G : Type*} [Group G] (φ : MulAut G) (z : G) :
    φ * MulAut.conj z * φ⁻¹ = MulAut.conj (φ z) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

theorem conj_injective_of_center_eq_bot {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥)
    {z₁ z₂ : G} (h : MulAut.conj z₁ = MulAut.conj z₂) : z₁ = z₂ := by
  have hc : z₂⁻¹ * z₁ ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : z₁ * g * z₁⁻¹ = z₂ * g * z₂⁻¹ := by
      have := congrArg (fun φ : MulAut G => φ g) h
      simpa only [MulAut.conj_apply] using this
    calc g * (z₂⁻¹ * z₁) = z₂⁻¹ * (z₂ * g * z₂⁻¹) * z₁ := by group
      _ = z₂⁻¹ * (z₁ * g * z₁⁻¹) * z₁ := by rw [h1]
      _ = z₂⁻¹ * z₁ * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

end Generic

section Ree


theorem reeG2_valid {b : ℕ} (hb : 1 ≤ b) : (TauCeti.LieTypeIndex.reeG2 b).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  exact ⟨hb, fun h => h⟩

theorem nonempty_reeGamma_equiv_catalog (b : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 b).Valid)
    (k : Type) [Field k] [Finite k] [CharP k ReeTag.G2.prime] (hk : Nat.card k = 3 ^ (2 * b + 1)) :
    Nonempty (ReeTag.G2.reeGamma k b ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 b, hv⟩).Group) := by
  have hmodel := CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2
    (S := (TauCeti.CFSGIndex.lie ⟨.reeG2 b, hv⟩).Group) b ⟨hv, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, -, -, -, hmain⟩ := small_Ree_model_Schreier _ 3 (2 * b + 1) hmodel
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.reeG2Bridge b hv k hk
  obtain ⟨E⟩ := hmain b k rfl hk ⟨φ.symm⟩
  exact ⟨E.symm⟩

theorem three_dvd_card_commutator_reeGamma (b : ℕ) (k : Type) [Field k] [Finite k]
    [CharP k ReeTag.G2.prime] (hk : Nat.card k = 3 ^ (2 * b + 1)) :
    3 ∣ Nat.card ↥(commutator (ReeTag.G2.reeGamma k b)) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
    obtain ⟨-, -, -, -, hzero, -⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components 0 k hk
    obtain ⟨-, h504, -⟩ := hzero rfl w₀ hw₀
    rw [h504]
    norm_num
  · obtain ⟨htop, -, -⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hb k hk
    rw [htop, Subgroup.card_top, CFSG.ComponentClassification.LiteratureLocal.G2_card_reeGamma b hk]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (dvd_pow (dvd_pow_self 3 (by omega)) (by norm_num)) _) _

theorem not_isLTwoTwentySeven_commutator_reeGamma (b : ℕ) (k : Type) [Field k] [Finite k]
    [CharP k ReeTag.G2.prime] (hk : Nat.card k = 3 ^ (2 * b + 1)) :
    ¬ IsLTwoTwentySeven ↥(commutator (ReeTag.G2.reeGamma k b)) := by
  intro h
  have h9828 := card_of_isLTwoTwentySeven h
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
    obtain ⟨-, -, -, -, hzero, -⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components 0 k hk
    obtain ⟨-, h504, -⟩ := hzero rfl w₀ hw₀
    omega
  · obtain ⟨htop, -, -⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hb k hk
    rw [htop, Subgroup.card_top, CFSG.ComponentClassification.LiteratureLocal.G2_card_reeGamma b hk]
      at h9828
    have hq : 27 ≤ 3 ^ (2 * b + 1) := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq3 : 27 ^ 3 ≤ (3 ^ (2 * b + 1)) ^ 3 := Nat.pow_le_pow_left hq 3
    have hpos : 1 ≤ ((3 ^ (2 * b + 1)) ^ 3 + 1) * (3 ^ (2 * b + 1) - 1) :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have hge : (3 ^ (2 * b + 1)) ^ 3 ≤
        (3 ^ (2 * b + 1)) ^ 3 * ((3 ^ (2 * b + 1)) ^ 3 + 1) * (3 ^ (2 * b + 1) - 1) := by
      rw [mul_assoc]
      exact Nat.le_mul_of_pos_right _ hpos
    omega

theorem isChevSimple_commutator_reeGamma (b : ℕ) (k : Type)
    [Field k] [Finite k] [CharP k ReeTag.G2.prime] (hk : Nat.card k = 3 ^ (2 * b + 1)) :
    IsChevSimple 3 ↥(commutator (ReeTag.G2.reeGamma k b)) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain ⟨-, -, -, ⟨e⟩, -, -⟩ :=
      CFSG.ComponentClassification.LiteratureLocal.G2_reeGamma_zero_structure hk
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let q8 : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
    have hv8 : (TauCeti.LieTypeIndex.A 1 q8).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [TauCeti.PrimePower.card_def, q8]
      norm_num
    exact Or.inr ⟨.lie ⟨.A 1 q8, hv8⟩, Or.inr ⟨by simp [q8, TauCeti.PrimePower.card_def], rfl⟩,
      ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q8 hv8).symm⟩⟩
  · obtain ⟨htop, -, -⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hb k hk
    have hv := reeG2_valid hb
    obtain ⟨φ⟩ := nonempty_reeGamma_equiv_catalog b hv k hk
    exact Or.inl ⟨.lie ⟨.reeG2 b, hv⟩, TauCeti.LieTypeIndex.characteristic_reeG2 b,
      ⟨((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans φ⟩⟩

theorem simpleNormalData_of_fixed_equiv {S : Type} [Group S]
    {β : MulAut S} {b : ℕ} {k : Type} [Field k] [Finite k] [CharP k ReeTag.G2.prime]
    (hk : Nat.card k = 3 ^ (2 * b + 1)) (eC : ↥(fixSubgroup β) ≃* ReeTag.G2.reeGamma k b) :
    SimpleNormalData 3 β ((commutator ↥(fixSubgroup β)).map (fixSubgroup β).subtype) ∧
      ¬ IsLTwoTwentySeven ↥((commutator ↥(fixSubgroup β)).map (fixSubgroup β).subtype) := by
  set C := fixSubgroup β with hC
  set D := commutator ↥C with hD
  set M := D.map C.subtype with hM
  have hNC : M.subgroupOf C = D := Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  let eD : ↥D ≃* ↥(commutator (ReeTag.G2.reeGamma k b)) :=
    (D.equivMapOfInjective eC.toMonoidHom eC.injective).trans
      (MulEquiv.subgroupCongr
        (CFSG.ComponentClassification.CatalogueBSmallRee.map_commutator_mulEquiv eC))
  let eMD : ↥D ≃* ↥M := D.equivMapOfInjective C.subtype C.subtype_injective
  let eM : ↥M ≃* ↥(commutator (ReeTag.G2.reeGamma k b)) := eMD.symm.trans eD
  obtain ⟨hs, hnc, -, -, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components b k hk
  have hZk := (small_Ree_fixed_group_center_trivial b k hk).1
  have hZC : Subgroup.center ↥C = ⊥ := center_eq_bot_of_mulEquiv eC hZk
  have hsD : IsSimpleGroup ↥D := eD.isSimpleGroup
  have hncD : ∃ x y : ↥D, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eD.symm x, eD.symm y, fun h => hxy (by simpa using congrArg eD h)⟩
  haveI hMn : (M.subgroupOf C).Normal := by
    rw [hNC]
    infer_instance
  refine ⟨⟨Subgroup.map_subtype_le _, hMn, eM.isSimpleGroup, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eM.symm x, eM.symm y, fun h => hxy (by simpa using congrArg eM h)⟩
  · refine Group.isSolvable_of_comm fun x y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hNC]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [h1, hD, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · intro x hx hxm
    have h1 := eq_one_of_forall_commute_commutator hZC hsD hncD (x := ⟨x, hx⟩)
      (fun d hd => Subtype.ext (hxm d.1 ⟨d, hd, rfl⟩))
    exact congrArg Subtype.val h1
  · exact CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv eM.symm
      (isChevSimple_commutator_reeGamma b k hk)
  · rw [Nat.card_congr eM.toEquiv]
    exact three_dvd_card_commutator_reeGamma b k hk
  · intro hL
    exact not_isLTwoTwentySeven_commutator_reeGamma b k hk
      (CFSG.HardMathSupport.Dickson.I271.isLTwoTwentySeven_of_mulEquiv eM hL)

theorem fixSubgroup_eq_fixSub {T : Type} [Group T] (α : MulAut T) :
    fixSubgroup α = CFSG.RankThree.PartOne.Sec66T.fixSub α :=
  Subgroup.ext fun y => by rw [mem_fixSubgroup, CFSG.RankThree.PartOne.Sec66T.mem_fixSub]

theorem cent_reeGamma_fieldAut {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) (w : MulAut (ReeTag.G2.reeGamma K a)) (hw : Nat.Coprime 3 (orderOf w))
    (hwσ : w * ReeTag.G2.reeGammaFieldAut K a σ = ReeTag.G2.reeGammaFieldAut K a σ * w)
    (hfix : ∀ x ∈ fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ), w x = x) :
    w ∈ innerAut (ReeTag.G2.reeGamma K a) := by
  classical
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨b, hb, hk, hchar, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.reeG2_fixed_data hK Nat.prime_three
      (by norm_num) hσ
  haveI := hchar
  let eC' : ↥(fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)) ≃*
      ReeTag.G2.reeGamma (fixSubfield σ) b :=
    (MulEquiv.subgroupCongr (fixSubgroup_eq_fixSub _)).trans eC
  have hZΓ : Subgroup.center ↥(ReeTag.G2.reeGamma K a) = ⊥ :=
    (small_Ree_fixed_group_center_trivial a K hK).1
  have hZC : Subgroup.center ↥(fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)) = ⊥ :=
    center_eq_bot_of_mulEquiv eC' (small_Ree_fixed_group_center_trivial b _ hk).1
  have hpowfix : ∀ j : ℕ, ∀ x ∈ fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ), (w ^ j) x = x := by
    intro j
    induction j with
    | zero => intro x _; rfl
    | succ j ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply, hfix x hx, ih x hx]
  have hA : ∀ j : ℕ, w ^ j ∈ innerAut (ReeTag.G2.reeGamma K a) → w ^ j = 1 := by
    rintro j ⟨z, hz⟩
    have hcomm : ReeTag.G2.reeGammaFieldAut K a σ * w ^ j =
        w ^ j * ReeTag.G2.reeGammaFieldAut K a σ := (Commute.pow_left hwσ j).eq.symm
    have hσz : ReeTag.G2.reeGammaFieldAut K a σ z = z := by
      apply conj_injective_of_center_eq_bot hZΓ
      rw [← mul_conj_mul_inv, hz, hcomm, mul_inv_cancel_right]
    have hzC : z ∈ fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ) := hσz
    have hzZ : (⟨z, hzC⟩ : ↥(fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ))) ∈
        Subgroup.center ↥(fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := hpowfix j y.1 y.2
      rw [← hz, MulAut.conj_apply] at h1
      refine Subtype.ext ?_
      change (y : ReeTag.G2.reeGamma K a) * z = z * y
      calc (y : ReeTag.G2.reeGamma K a) * z = z * y * z⁻¹ * z := by rw [h1]
        _ = z * y := by group
    rw [hZC, Subgroup.mem_bot] at hzZ
    have hz1 : z = 1 := congrArg Subtype.val hzZ
    rw [← hz, hz1, map_one]
  by_contra hwinn
  have hn0 : orderOf w ≠ 0 := by
    intro h0
    rw [h0, Nat.coprime_zero_right] at hw
    omega
  have hn1 : orderOf w ≠ 1 := by
    intro h1
    rw [orderOf_eq_one_iff] at h1
    rw [h1] at hwinn
    exact hwinn (innerAut _).one_mem
  have hℓ : (orderOf w).minFac.Prime := Nat.minFac_prime hn1
  have hℓn : (orderOf w).minFac ∣ orderOf w := Nat.minFac_dvd _
  have hu : orderOf (w ^ (orderOf w / (orderOf w).minFac)) = (orderOf w).minFac :=
    orderOf_pow_orderOf_div hn0 hℓn
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = (orderOf w).minFac := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u, u = w ^ (orderOf w / (orderOf w).minFac) := ⟨_, rfl⟩
  rw [← hudef, ← hℓdef] at hu
  rw [← hℓdef] at hℓ hℓn
  have huℓ : u ^ ℓ = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hu_out : u ∉ innerAut (ReeTag.G2.reeGamma K a) := by
    intro h
    rw [hudef] at h
    have h1 := hA _ h
    rw [← hudef] at h1
    have h2 : orderOf u = 1 := by rw [h1, orderOf_one]
    rw [hu] at h2
    exact hℓ.one_lt.ne' h2
  have hℓ3 : ℓ ≠ 3 := by
    intro h3
    rw [h3] at hℓn
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hw hℓn
  have hℓ2 : ℓ ≠ 2 := by
    intro h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, -, -, -, hodd, -⟩ := small_Ree_outer_three_kernel_field_complement a ha K hK
    have hu2 : u ^ 2 = 1 := h2 ▸ huℓ
    have ho1 : (QuotientGroup.mk u :
        CFSG.ComponentClassification.OuterAutomorphisms.Outer (ReeTag.G2.reeGamma K a)) ≠ 1 :=
      fun h => hu_out (show u ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ from
        (QuotientGroup.eq_one_iff u).1 h)
    have ho2 : (QuotientGroup.mk u :
        CFSG.ComponentClassification.OuterAutomorphisms.Outer (ReeTag.G2.reeGamma K a)) ^ 2 =
          1 := by
      rw [← QuotientGroup.mk_pow, hu2, QuotientGroup.mk_one]
    have hord := orderOf_eq_prime ho2 ho1
    have hdvd : 2 ∣ Nat.card
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer (ReeTag.G2.reeGamma K a)) := by
      rw [← hord]
      exact orderOf_dvd_natCard _
    rw [Nat.odd_iff] at hodd
    omega
  have hℓ5 : 5 ≤ ℓ := by
    have h2 := hℓ.two_le
    have h4 : ℓ ≠ 4 := by
      intro h4
      rw [h4] at hℓ
      norm_num at hℓ
    omega
  obtain ⟨-, δ, ρ, hρ, hδ, -, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha K hK hℓ hℓ2 u
      huℓ hu_out
  obtain ⟨b', hb', hk', hchar', ⟨eρ⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.reeG2_fixed_data hK hℓ hℓ2 hρ
  haveI := hchar'
  have hcardu : Nat.card ↥(fixSubgroup u) =
      (3 ^ (2 * b' + 1)) ^ 3 * ((3 ^ (2 * b' + 1)) ^ 3 + 1) * (3 ^ (2 * b' + 1) - 1) := by
    rw [← Subgroup.card_map_of_injective (f := δ.toMonoidHom) δ.injective,
      ← CFSG.HardMathSupport.Dickson.I271.fixSubgroup_congr δ u, mulAut_congr_self, hδ,
      fixSubgroup_eq_fixSub, Nat.card_congr eρ.toEquiv]
    exact CFSG.ComponentClassification.LiteratureLocal.G2_card_reeGamma b' hk'
  have hcardC : Nat.card ↥(fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)) =
      (3 ^ (2 * b + 1)) ^ 3 * ((3 ^ (2 * b + 1)) ^ 3 + 1) * (3 ^ (2 * b + 1) - 1) := by
    rw [Nat.card_congr eC'.toEquiv]
    exact CFSG.ComponentClassification.LiteratureLocal.G2_card_reeGamma b hk
  have hle : Nat.card ↥(fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)) ≤
      Nat.card ↥(fixSubgroup u) :=
    Subgroup.card_le_of_le fun x hx => by
      rw [mem_fixSubgroup, hudef]
      exact hpowfix _ x hx
  have hbb : b' < b := by
    have h1 : (2 * b' + 1) * 5 ≤ (2 * b' + 1) * ℓ := Nat.mul_le_mul_left _ hℓ5
    nlinarith
  have hq : 3 ^ (2 * b' + 1) < 3 ^ (2 * b + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hq2 : 2 ≤ 3 ^ (2 * b' + 1) := by
    calc 2 ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (2 * b' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt := ree_order_lt hq2 hq
  rw [hcardC, hcardu] at hle
  omega

theorem outerCentData_reeGamma_fieldAut {a : ℕ} (ha : 1 ≤ a)
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    OuterCentData 3 (ReeTag.G2.reeGammaFieldAut K a σ) := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨b, -, hk, hchar, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.reeG2_fixed_data hK Nat.prime_three
      (by norm_num) hσ
  haveI := hchar
  obtain ⟨hdata, hL⟩ := simpleNormalData_of_fixed_equiv hk
    ((MulEquiv.subgroupCongr (fixSubgroup_eq_fixSub _)).trans eC)
  exact OuterCentData.ofSimpleNormal Nat.prime_three hdata
    (fun _ w hw hwσ hfix => cent_reeGamma_fieldAut ha hK hσ w hw hwσ hfix)
    (fun _ hL' => absurd hL' hL)

theorem outerCentData_reeGamma {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    {β : MulAut (ReeTag.G2.reeGamma K a)} (hβ : orderOf β = 3)
    (hout : β ∉ innerAut (ReeTag.G2.reeGamma K a)) : OuterCentData 3 β := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have hβ3 : β ^ 3 = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  obtain ⟨-, δ, σ, hσ, hδ, -, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha K hK
      Nat.prime_three (by norm_num) β hβ3 hout
  refine OuterCentData.of_congr Nat.prime_three δ ?_
  rw [mulAut_congr_self, hδ]
  exact outerCentData_reeGamma_fieldAut ha hK hσ

end Ree

end SuzukiReeTits

theorem outerCentOn_suzukiReeTits :
    OuterCentOn .suzukiReeTits := by
  intro S _ _ hS hnc idx hfam he p hp hp2 hpc β hβ hout
  obtain ⟨d, hv⟩ := idx
  cases d with
  | suzuki m => exact absurd (hpc.trans (TauCeti.LieTypeIndex.characteristic_suzuki m)) hp2
  | reeG2 m =>
    have h3 : p = 3 := hpc.trans (TauCeti.LieTypeIndex.characteristic_reeG2 m)
    subst h3
    obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ :=
      CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel
        (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, he⟩)
    have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
    refine OuterCentData.of_congr hp e ?_
    refine SuzukiReeTits.outerCentData_reeGamma ha hK (by rw [MulEquiv.orderOf_eq]; exact hβ) ?_
    rintro ⟨t, ht⟩
    apply hout
    refine ⟨e.symm t, ?_⟩
    apply (MulAut.congr e).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact ht
  | reeF4 m => exact absurd (hpc.trans (TauCeti.LieTypeIndex.characteristic_reeF4 m)) hp2
  | tits => exact absurd (hpc.trans TauCeti.LieTypeIndex.characteristic_tits) hp2
  | _ => simp [lieFamily] at hfam

theorem carrierOn_suzukiReeTits :
    CarrierOn .suzukiReeTits := by
  intro d hfam hchar
  obtain ⟨d, hv⟩ := d
  cases d with
  | suzuki m => exact absurd (TauCeti.LieTypeIndex.characteristic_suzuki m) hchar
  | reeG2 m =>
    obtain ⟨X, _, _, _, hm, hX, ⟨e⟩⟩ :=
      CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.exists_reeG2_model
        (K := (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group) ⟨hv, ⟨MulEquiv.refl _⟩⟩
    have : Finite (ModGL ReeTag.G2.tag X) := finite_modGL
    obtain ⟨-, hs, x, y, hxy⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hm X hX
    haveI := hs
    refine ⟨Finite.of_equiv _ e.symm.toEquiv, e.isSimpleGroup, e.symm x, e.symm y,
      fun h => hxy ?_⟩
    simpa using congrArg e h
  | reeF4 m => exact absurd (TauCeti.LieTypeIndex.characteristic_reeF4 m) hchar
  | tits => exact absurd TauCeti.LieTypeIndex.characteristic_tits hchar
  | _ => simp [lieFamily] at hfam

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
