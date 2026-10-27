module

import CFSG.GroupTheory.QuasiDihedralFusion.Structure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeDoubleCommutator
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.Assembly.Subnormal
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.Goldschmidt.Sec82

open CFSG.Open

section Cyclic

variable {G : Type*} [Group G]

theorem mulAut_mul_comm_of_isCyclic {C : Type*} [Group C] [IsCyclic C] (σ τ : MulAut C) :
    σ * τ = τ * σ := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ.toMonoidHom
  obtain ⟨n, hn⟩ := MonoidHom.map_cyclic τ.toMonoidHom
  ext g
  change σ (τ g) = τ (σ g)
  have h1 : σ (τ g) = (τ g) ^ m := hm (τ g)
  have h2 : τ (σ g) = (σ g) ^ n := hn (σ g)
  have h3 : τ g = g ^ n := hn g
  have h4 : σ g = g ^ m := hm g
  rw [h1, h2, h3, h4, ← zpow_mul, ← zpow_mul, mul_comm]

theorem mem_centralizer_of_noIndexTwo [Finite G] {X C : Subgroup G}
    (hX : ∀ Y : Subgroup G, Y ≤ X → (Y.subgroupOf X).index ≠ 2) (hC : IsCyclic C)
    (hXC : X ≤ Subgroup.normalizer (C : Set G)) {s : G} (hs : s ∈ X) {k : ℕ}
    (hk : s ^ 2 ^ k = 1) : s ∈ Subgroup.centralizer (C : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : X →* MulAut C := C.normalizerMonoidHom.comp (Subgroup.inclusion hXC)
  set R := φ.range with hR
  have hcomm : ∀ x y : R, x * y = y * x := fun x y =>
    Subtype.ext (mulAut_mul_comm_of_isCyclic (x : MulAut C) y)
  let _ : CommGroup R := { (inferInstance : Group R) with mul_comm := hcomm }
  have hnil : Group.IsNilpotent R := inferInstance
  have hpc := CFSG.BenderSuzuki.External.hkt_hasNormalPComplement_of_nilpotent (p := 2) hnil
  have hno : ∀ K : Subgroup R, K.index ≠ 2 := by
    intro K hK
    let K' : Subgroup X := K.comap φ.rangeRestrict
    have hK' : K'.index = 2 := by
      rw [Subgroup.index_comap_of_surjective K φ.rangeRestrict_surjective, hK]
    refine hX (K'.map X.subtype) (Subgroup.map_subtype_le _) ?_
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    exact hK'
  have hodd := CFSG.QuasiDihedralFusion.odd_card_of_hasNormalPComplement hpc hno
  have h1 : (φ.rangeRestrict ⟨s, hs⟩ : R) = 1 := by
    have hpow : (φ.rangeRestrict ⟨s, hs⟩ : R) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨s, hs⟩ : X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have h2 : orderOf (φ.rangeRestrict ⟨s, hs⟩ : R) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
    have h3 : orderOf (φ.rangeRestrict ⟨s, hs⟩ : R) ∣ Nat.card R := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ k) (Nat.card R) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h3)
  have h1' : φ ⟨s, hs⟩ = 1 := congrArg Subtype.val h1
  refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
  have h5 := congrArg (fun f : MulAut C => ((f ⟨c, hc⟩ : C) : G)) h1'
  change s * c * s⁻¹ = c at h5
  calc c * s = s * c * s⁻¹ * s := by rw [h5]
    _ = s * c := by group

end Cyclic

section Coprime

variable {G : Type*} [Group G]

theorem le_centralizer_of_coprime_of_fitting [Finite G] {X R : Subgroup G}
    (hsolv : Group.IsSolvable X) (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hcop : Nat.Coprime (Nat.card R) (Nat.card X))
    (hF : CFSG.fittingSubgroupOf X ≤ Subgroup.centralizer (R : Set G)) :
    X ≤ Subgroup.centralizer (R : Set G) := by
  have hFXn := GorensteinWalter.fittingSubgroupOf_isNormalIn X
  have hXR : ⁅X, R⁆ ≤ CFSG.fittingSubgroupOf X := by
    rw [Subgroup.commutator_le]
    intro x hx r hr
    have hrf : ∀ f ∈ CFSG.fittingSubgroupOf X, r * f = f * r := fun f hf =>
      Subgroup.mem_centralizer_iff.mp (hF hf) r hr
    have h1 : x * r * x⁻¹ * r⁻¹ ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hRX hr) x⁻¹).mp (X.inv_mem hx)
      simpa [mul_assoc] using X.mul_mem hx this
    have h2 : x * r * x⁻¹ * r⁻¹ ∈
        Subgroup.centralizer (CFSG.fittingSubgroupOf X : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
      have hf' : x⁻¹ * f * x ∈ CFSG.fittingSubgroupOf X := by
        exact (by simpa using hFXn.2 x⁻¹ (X.inv_mem hx) f hf :
          x⁻¹ * f * x ∈ CFSG.GorensteinWalter.fittingSubgroupOf X)
      have e1 := hrf f hf
      have e2 := hrf _ hf'
      calc f * (x * r * x⁻¹ * r⁻¹) = x * (x⁻¹ * f * x) * r * x⁻¹ * r⁻¹ := by group
        _ = x * r * (x⁻¹ * f * x) * x⁻¹ * r⁻¹ := by rw [mul_assoc x, ← e2, ← mul_assoc]
        _ = x * r * x⁻¹ * f * r⁻¹ := by group
        _ = x * r * x⁻¹ * r⁻¹ * (r * f) * r⁻¹ := by group
        _ = x * r * x⁻¹ * r⁻¹ * f := by rw [e1]; group
    have h3 : (⟨_, h1⟩ : X) ∈ Subgroup.centralizer (fittingSubgroup X : Set X) := by
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => Subtype.ext ?_
      exact Subgroup.mem_centralizer_iff.mp h2 y ⟨y, hy, rfl⟩
    exact ⟨_, CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv h3, rfl⟩
  have hdouble : ⁅⁅X, R⁆, R⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hXR.trans hF)
  have h := GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot X R hRX hcop
    hdouble
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem mem_of_odd_index [Finite G] {Y N : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd ((N.subgroupOf Y).index)) {s : G}
    (hs : s ∈ Y) {k : ℕ} (hk : s ^ 2 ^ k = 1) : s ∈ N := by
  have : (N.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYN
  set x := (QuotientGroup.mk (⟨s, hs⟩ : Y) : Y ⧸ N.subgroupOf Y) with hx
  have h1 : orderOf x ∣ 2 ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [hx, ← QuotientGroup.mk_pow]
    have : (⟨s, hs⟩ : Y) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, QuotientGroup.mk_one]
  have h2 : orderOf x ∣ (N.subgroupOf Y).index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard x
  have hcop : Nat.Coprime (2 ^ k) ((N.subgroupOf Y).index) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h3 : x = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  rw [hx, QuotientGroup.eq_one_iff] at h3
  exact h3

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

theorem mem_normalizer_of_conj_mem [Finite G] {V : Subgroup G} {b : G}
    (h : ∀ v ∈ V, b * v * b⁻¹ ∈ V) : b ∈ Subgroup.normalizer (V : Set G) := by
  have hle : V.map (MulAut.conj b).toMonoidHom ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj b).injective).ge)

theorem le_centralizer_of_inf_eq_bot {X Y : Subgroup G}
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hYX : Y ≤ Subgroup.normalizer (X : Set G))
    (hdisj : X ⊓ Y = ⊥) : X ≤ Subgroup.centralizer (Y : Set G) := by
  intro x hx
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ Y :=
    Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXY hx) y).mp hy) (Y.inv_mem hy)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (hYX hy) x⁻¹).mp (X.inv_mem hx)
    simpa [mul_assoc] using X.mul_mem hx this
  have h3 : x * y * x⁻¹ * y⁻¹ = 1 := by
    have : x * y * x⁻¹ * y⁻¹ ∈ X ⊓ Y := ⟨h2, h1⟩
    rwa [hdisj, Subgroup.mem_bot] at this
  calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
    _ = x * y := by rw [h3, inv_one, one_mul]

theorem card_sup_le_mul_of_le_normalizer [Finite G] {H N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (H ⊔ N : Subgroup G) ≤ Nat.card H * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _))

end Coprime

section Quasisimple

variable {A B : Type*} [Group A] [Group B]

theorem isQuasisimple_of_mulEquiv (e : A ≃* B) (hA : CFSG.Open.IsQuasisimple A) :
    CFSG.Open.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

end Quasisimple

end CFSG.Goldschmidt.Sec82
