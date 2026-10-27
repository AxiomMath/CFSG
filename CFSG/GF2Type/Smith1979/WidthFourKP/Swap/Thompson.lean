module

public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Lift
public import CFSG.GF2Type.Smith1979.W4O83Local
public import CFSG.LargeExtraspecial.AS35TFOdd
public import CFSG.LocalAnalysis.GLTheoremB.I2810.Induced

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Swap.Thompson

open CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
open Subgroup Module CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g x : G} {K Y : Subgroup S.O}

@[expose] noncomputable def UCore (S : Setting G) (x : G) : Subgroup G :=
  pCoreOf 2 (centralizer ({x} : Set G))

@[expose] noncomputable def Wbar (S : Setting G) (x : G) : Subgroup S.O :=
  ((UCore S x ⊓ S.M).subgroupOf S.M).map S.ρ

theorem Wbar_le_Y (T : ThompsonInput S g x K Y) : Wbar S x ≤ Y := by
  intro w hw
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hw
  have hmU : (m : G) ∈ UCore S x := (Subgroup.mem_subgroupOf.mp hm).1
  have hmcomm : (m : G) * x = x * (m : G) :=
    mem_centralizer_singleton_iff.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hmU)
  refine (T.mem_Y (S.ρ m)).mpr ⟨⟨m, rfl⟩, ?_⟩
  rw [S.ρ_cl m T.mem_QG]
  congr 1
  calc (m : G) * x * (m : G)⁻¹ = x * (m : G) * (m : G)⁻¹ := by rw [hmcomm]
    _ = x := by group

theorem conj_mem_Wbar (T : ThompsonInput S g x K Y) {m w : S.O} (hm : m ∈ Y)
    (hw : w ∈ Wbar S x) : m * w * m⁻¹ ∈ Wbar S x := by
  obtain ⟨s, hsρ, hsx⟩ := exists_lift T hm
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
  have huU : (u : G) ∈ UCore S x := (Subgroup.mem_subgroupOf.mp hu).1
  have huM : (u : G) ∈ S.M := u.2
  have hsH : (s : G) ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr hsx
  have hnorm : (s : G) ∈ normalizer (UCore S x : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hsH
  have hconjU : (s : G) * (u : G) * (s : G)⁻¹ ∈ UCore S x :=
    (Subgroup.mem_normalizer_iff.mp hnorm (u : G)).mp huU
  have hconjM : (s : G) * (u : G) * (s : G)⁻¹ ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem s.2 huM) (S.M.inv_mem s.2)
  refine Subgroup.mem_map.mpr ⟨s * u * s⁻¹, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr ⟨hconjU, hconjM⟩
  · rw [map_mul, map_mul, map_inv, hsρ]

theorem Wbar_normal (T : ThompsonInput S g x K Y) :
    ((Wbar S x).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Wbar_le_Y T)]
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact conj_mem_Wbar T hm hw
  · intro hw
    have hmem := conj_mem_Wbar T (Y.inv_mem hm) hw
    have heq : m⁻¹ * (m * w * m⁻¹) * (m⁻¹)⁻¹ = w := by group
    rwa [heq] at hmem

theorem Wbar_isPGroup : IsPGroup 2 ↥(Wbar S x) := by
  have h1 : IsPGroup 2 ↥(UCore S x ⊓ S.M) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_inf_left
  have h2 : IsPGroup 2 ↥((UCore S x ⊓ S.M).subgroupOf S.M) :=
    h1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  exact h2.map S.ρ

theorem Wbar_isSolvable : Group.IsSolvable (Wbar S x) := by
  haveI : Group.IsNilpotent (Wbar S x) := (Wbar_isPGroup (S := S) (x := x)).isNilpotent
  exact IsNilpotent.to_isSolvable

theorem commute_Wbar_K (T : ThompsonInput S g x K Y) :
    ∀ u (hu : u ∈ UCore S x ⊓ S.M) (k : S.O), k ∈ K →
      S.ρ ⟨u, hu.2⟩ * k = k * S.ρ ⟨u, hu.2⟩ := by
  have hKY : K ≤ Y := K_le_Y T
  have hWY : Wbar S x ≤ Y := Wbar_le_Y T
  have hKq : CFSG.IsQuasisimple K :=
    ⟨Group.isPerfect_def.mpr T.quasisimple.1, T.quasisimple.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
        T.quasisimple⟩
  have hKqY : CFSG.IsQuasisimple (K.subgroupOf Y) :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKY) hKq
  have hKsub : (K.subgroupOf Y).IsSubnormal :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hKY).mp T.subnormal
  have hWsub : ((Wbar S x).subgroupOf Y).IsSubnormal :=
    (Wbar_normal T).isSubnormal
  have hWsolv : Group.IsSolvable ((Wbar S x).subgroupOf Y) := by
    haveI := Wbar_isSolvable (S := S) (x := x)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hWY).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hWY).injective
  have hcomm : ⁅K.subgroupOf Y, (Wbar S x).subgroupOf Y⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hWsolv hWsub).1 (K.subgroupOf Y)
      ⟨hKqY, hKsub⟩
  have hcent : K.subgroupOf Y ≤ centralizer ((Wbar S x).subgroupOf Y : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro u hu k hk
  have hw : S.ρ ⟨u, hu.2⟩ ∈ Wbar S x :=
    Subgroup.mem_map.mpr ⟨⟨u, hu.2⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  have hwY : (⟨S.ρ ⟨u, hu.2⟩, hWY hw⟩ : Y) ∈ (Wbar S x).subgroupOf Y := hw
  have hkY : (⟨k, hKY hk⟩ : Y) ∈ K.subgroupOf Y := hk
  have hcomm' := Subgroup.mem_centralizer_iff.mp (hcent hkY) _ hwY
  exact congrArg Subtype.val hcomm'

theorem conj_mem_UCore_inf_QG {y : S.M} (hyx : (y : G) * x = x * (y : G)) {u : G}
    (hu : u ∈ UCore S x ⊓ S.QG) : (y : G) * u * (y : G)⁻¹ ∈ UCore S x ⊓ S.QG := by
  have hyH : (y : G) ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr hyx
  have hnorm : (y : G) ∈ normalizer (UCore S x : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hyH
  exact ⟨(Subgroup.mem_normalizer_iff.mp hnorm u).mp hu.1, S.conj_mem_QG y.2 hu.2⟩

theorem mapsTo_clSub_UCore {y : S.M} (hyx : (y : G) * x = x * (y : G)) :
    ∀ v ∈ S.clSub (UCore S x),
      ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (UCore S x) := by
  intro v hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro v ⟨u, hu, huQ, rfl⟩
    rw [S.ρ_cl y huQ]
    exact S.cl_mem_clSub (conj_mem_UCore_inf_QG hyx ⟨hu, huQ⟩).1
      (conj_mem_UCore_inf_QG hyx ⟨hu, huQ⟩).2
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem not_centralize_UCore (hchar : IsCharTwoType G) (T : ThompsonInput S g x K Y)
    {y : S.M} (hyodd : Odd (orderOf (y : G))) (hy1 : (y : G) ≠ 1)
    (hyx : (y : G) * x = x * (y : G)) :
    ¬ ∀ u ∈ UCore S x, (y : G) * u = u * (y : G) := by
  intro hc
  have hyH : (y : G) ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr hyx
  have hyU : (y : G) ∈ UCore S x :=
    CFSG.GF2Type.Smith1979.W4O83.centralizer_pCoreOf_le hchar T.orderOf_eq (y : G) hyH hc
  have hU2 : IsPGroup 2 ↥(UCore S x) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hU2
  have hdvd : orderOf (y : G) ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.orderOf_dvd_natCard (UCore S x) hyU
  have hcop : Nat.Coprime (orderOf (y : G)) (2 ^ n) :=
    ((Nat.coprime_two_left.mpr hyodd).symm).pow_right n
  have hone : orderOf (y : G) = 1 := hcop.eq_one_of_dvd hdvd
  exact hy1 (orderOf_eq_one_iff.mp hone)

theorem not_centralize_inf_M (hchar : IsCharTwoType G) (T : ThompsonInput S g x K Y)
    {k : S.O} (hkK : k ∈ K) {y : S.M}
    (hyodd : Odd (orderOf (y : G))) (hy1 : (y : G) ≠ 1)
    (hyx : (y : G) * x = x * (y : G)) (hk1 : k ≠ 1) :
    ¬ ∀ p ∈ UCore S x ⊓ S.M, (y : G) * p = p * (y : G) := by
  intro hfixM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnotU := not_centralize_UCore hchar T hyodd hy1 hyx
  apply hnotU
  have hyH : (y : G) ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr hyx
  have hyNorm : (y : G) ∈ normalizer (UCore S x : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hyH
  have hzH : S.z ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (S.z_comm (S.QG_le_M T.mem_QG)).symm
  have hzNorm : S.z ∈ normalizer (UCore S x : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hzH
  have hP : IsPGroup 2 ↥(UCore S x) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers (y : G))) 2 := by
    rw [Nat.card_zpowers]
    exact (Nat.coprime_two_left.mpr hyodd).symm
  have hB : IsPGroup 2 ↥(Subgroup.zpowers S.z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, S.orderOf_z, pow_one])
  have hRP : Subgroup.zpowers (y : G) ≤ normalizer (UCore S x : Set G) :=
    Subgroup.zpowers_le.mpr hyNorm
  have hBP : Subgroup.zpowers S.z ≤ normalizer (UCore S x : Set G) :=
    Subgroup.zpowers_le.mpr hzNorm
  have hRB : ⁅Subgroup.zpowers (y : G), Subgroup.zpowers S.z⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le,
      Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    exact ((show Commute (y : G) S.z from S.z_comm y.2).zpow_right n).eq.symm
  have hfix : UCore S x ⊓ centralizer (Subgroup.zpowers S.z : Set G) ≤
      centralizer (Subgroup.zpowers (y : G) : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    have hpz : S.z * p = p * S.z :=
      Subgroup.mem_centralizer_iff.mp hp.2 S.z (Subgroup.mem_zpowers S.z)
    have hpM : p ∈ S.M := mem_centralizer_singleton_iff.mpr hpz.symm
    have hyp : (y : G) * p = p * (y : G) := hfixM p ⟨hp.1, hpM⟩
    exact ((show Commute (y : G) p from hyp).zpow_left n).eq
  have hN := CFSG.Goldschmidt.N10 G (p := 2) (UCore S x) (Subgroup.zpowers (y : G))
    (Subgroup.zpowers S.z) hP hcop hB hRP hBP hRB hfix
  intro u hu
  exact Subgroup.mem_centralizer_iff.mp (hN hu) (y : G) (Subgroup.mem_zpowers (y : G))

theorem not_centralize_inf_QG (hchar : IsCharTwoType G) (T : ThompsonInput S g x K Y)
    {k : S.O} (hkK : k ∈ K) {y : S.M} (hyρ : S.ρ y = k)
    (hyodd : Odd (orderOf (y : G))) (hyx : (y : G) * x = x * (y : G))
    (hnotM : ¬ ∀ p ∈ UCore S x ⊓ S.M, (y : G) * p = p * (y : G)) :
    ¬ ∀ q ∈ UCore S x ⊓ S.QG, (y : G) * q = q * (y : G) := by
  intro hcQ
  apply hnotM
  have hyH : (y : G) ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr hyx
  have hyNorm : (y : G) ∈ normalizer (UCore S x : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hyH
  intro p hp
  have hP2 : IsPGroup 2 ↥(UCore S x ⊓ S.M) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_inf_left
  have hQP : UCore S x ⊓ S.QG ≤ UCore S x ⊓ S.M :=
    le_inf inf_le_left (inf_le_right.trans S.QG_le_M)
  have h := CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.odd_trivial_of_series
    (X := G) hyodd hP2 hQP ?_ ?_ ?_ p hp
  · calc (y : G) * p = ((y : G) * p * (y : G)⁻¹) * (y : G) := by group
      _ = p * (y : G) := by rw [h]
  · intro q hq
    exact ⟨(Subgroup.mem_normalizer_iff.mp hyNorm q).mp hq.1,
      S.M.mul_mem (S.M.mul_mem y.2 hq.2) (S.M.inv_mem y.2)⟩
  · intro q hq
    calc (y : G) * q * (y : G)⁻¹ = (q * (y : G)) * (y : G)⁻¹ := by rw [hcQ q hq]
      _ = q := by group
  · intro q hq
    have hcommU : ⁅(y : G), q⁆ ∈ UCore S x := by
      have h1 : (y : G) * q * (y : G)⁻¹ ∈ UCore S x :=
        (Subgroup.mem_normalizer_iff.mp hyNorm q).mp hq.1
      have h2 : q⁻¹ ∈ UCore S x := (UCore S x).inv_mem hq.1
      simpa [commutatorElement_def] using (UCore S x).mul_mem h1 h2
    have hcommM : ⁅(y : G), q⁆ ∈ S.M :=
      S.M.mul_mem (S.M.mul_mem (S.M.mul_mem y.2 hq.2) (S.M.inv_mem y.2))
        (S.M.inv_mem hq.2)
    have hrho : S.ρ ⟨⁅(y : G), q⁆, hcommM⟩ = 1 := by
      let u : S.M := ⟨q, hq.2⟩
      let v : S.M := ⁅y, u⁆
      have hv : v = ⟨⁅(y : G), q⁆, hcommM⟩ := by
        ext
        simp [v, u, commutatorElement_def]
      rw [← hv]
      rw [map_commutatorElement, hyρ]
      have hcu : S.ρ u * k = k * S.ρ u := commute_Wbar_K T q hq k hkK
      rw [commutatorElement_def, ← hcu]
      group
    exact ⟨hcommU, (S.ρ_eq_one_iff _).mp hrho⟩

theorem centralize_inf_QG_of_fix (T : ThompsonInput S g x K Y) {k : S.O} (hkK : k ∈ K)
    {y : S.M} (hyρ : S.ρ y = k) (hyodd : Odd (orderOf (y : G)))
    (hyx : (y : G) * x = x * (y : G))
    (hfix : ∀ v ∈ S.clSub (UCore S x),
      ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    ∀ q ∈ UCore S x ⊓ S.QG, (y : G) * q = q * (y : G) := by
  have hyH : (y : G) ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr hyx
  have hyNorm : (y : G) ∈ normalizer (UCore S x : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hyH
  have hP2 : IsPGroup 2 ↥(UCore S x ⊓ S.QG) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_inf_left
  intro q hq
  let Q0 : Subgroup G := (UCore S x ⊓ S.QG) ⊓ Subgroup.zpowers S.z
  have hQ0 : Q0 ≤ UCore S x ⊓ S.QG := inf_le_left
  have h := CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.odd_trivial_of_series
    (X := G) hyodd hP2 hQ0 ?_ ?_ ?_ q hq
  · calc (y : G) * q = ((y : G) * q * (y : G)⁻¹) * (y : G) := by group
      _ = q * (y : G) := by rw [h]
  · intro r hr
    exact ⟨(Subgroup.mem_normalizer_iff.mp hyNorm r).mp hr.1, S.conj_mem_QG y.2 hr.2⟩
  · intro r hr
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr.2
    have hconjz : (y : G) * S.z * (y : G)⁻¹ = S.z := by
      rw [show (y : G) * S.z = S.z * (y : G) from S.z_comm y.2]
      group
    rw [← conj_zpow, hconjz]
  · intro r hr
    have hconjQ : (y : G) * r * (y : G)⁻¹ ∈ S.QG := S.conj_mem_QG y.2 hr.2
    have hcommP : ⁅(y : G), r⁆ ∈ UCore S x ⊓ S.QG := by
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact (UCore S x).mul_mem ((Subgroup.mem_normalizer_iff.mp hyNorm r).mp hr.1)
          ((UCore S x).inv_mem hr.1)
      · rw [commutatorElement_def]
        exact (S.QG).mul_mem hconjQ ((S.QG).inv_mem hr.2)
    have hcommZ : ⁅(y : G), r⁆ ∈ Subgroup.zpowers S.z := by
      have hcl : S.cl ((y : G) * r * (y : G)⁻¹) = S.cl r := by
        have h1 := hfix (S.cl r) (S.cl_mem_clSub hr.1 hr.2)
        rwa [← hyρ, S.ρ_cl y hr.2] at h1
      rcases (S.cl_eq_cl_iff hr.2 hconjQ).mp hcl.symm with h | h
      · have hone : ⁅(y : G), r⁆ = 1 := by
          rw [commutatorElement_def, h]
          group
        rw [hone]
        exact Subgroup.one_mem _
      · have hz : ⁅(y : G), r⁆ = S.z := by
          rw [commutatorElement_def, h]
          calc r * S.z * r⁻¹ = S.z * r * r⁻¹ := by rw [S.z_comm (S.QG_le_M hr.2)]
            _ = S.z := by group
        rw [hz]
        exact Subgroup.mem_zpowers S.z
    exact ⟨hcommP, hcommZ⟩

theorem exists_moved (hchar : IsCharTwoType G) (T : ThompsonInput S g x K Y) {k : S.O}
    (hkK : k ∈ K) (hk5 : k ^ 5 = 1) (hk1 : k ≠ 1) :
    ∃ u ∈ UCore S x ⊓ S.QG,
      ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u) ≠ S.cl u := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hkodd : Odd (orderOf k) := by rw [orderOf_eq_prime hk5 hk1]; norm_num
  obtain ⟨y, hyρ, hyx, hyodd, hy1⟩ := exists_odd_order_lift T hkK hkodd hk1
  have hnotM := not_centralize_inf_M hchar T hkK hyodd hy1 hyx hk1
  have hnotQ := not_centralize_inf_QG hchar T hkK hyρ hyodd hyx hnotM
  by_contra hcon
  push Not at hcon
  have hfix : ∀ v ∈ S.clSub (UCore S x),
      ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro v ⟨u, hu, huQ, rfl⟩
      exact hcon u ⟨hu, huQ⟩
    · rw [map_zero]
    · intro a b _ _ ha hb
      rw [map_add, ha, hb]
    · intro c a _ ha
      rw [map_smul, ha]
  exact hnotQ (centralize_inf_QG_of_fix T hkK hyρ hyodd hyx hfix)

theorem commSpace_le_clSub (hchar : IsCharTwoType G) (T : ThompsonInput S g x K Y)
    (hw : S.width = 4) {k : S.O} (hkK : k ∈ K) (hk5 : k ^ 5 = 1) :
    commSpace ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ S.clSub (UCore S x) := by
  by_cases hk1 : k = 1
  · subst k
    intro v hv
    have hv0 : v = 0 := by
      simpa [commSpace, eq_comm] using hv
    rw [hv0]
    exact Submodule.zero_mem _
  · classical
    have hklin : ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun h => hk1 (Subtype.ext h)
    have hk5' : (((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) ^ 5 = 1 := by
      simpa using congrArg (fun z : S.O => ((z : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) hk5
    obtain ⟨u, hu, hmu⟩ := exists_moved hchar T hkK hk5 hk1
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨y, hyρ, hyx, hyodd, hy1⟩ := exists_odd_order_lift T hkK
      (by rw [orderOf_eq_prime hk5 hk1]; norm_num) hk1
    set W : Submodule (ZMod 2) S.Qt := S.clSub (UCore S x) with hW
    set C : Submodule (ZMod 2) S.Qt :=
      commSpace ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hC
    set D : Submodule (ZMod 2) S.Qt := W ⊓ C with hD
    have hkfixx : ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x :=
      ((T.mem_Y k).mp (K_le_Y T hkK)).2
    have hxcl0 : S.cl x ≠ 0 := by
      intro h0
      rcases (S.cl_eq_zero_iff T.mem_QG).mp h0 with h | h
      · have ho := T.orderOf_eq
        rw [h, orderOf_one] at ho
        omega
      · exact T.ne_z h
    have hfixne : fixSpace ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ ⊥ := by
      intro hbot
      have hmem : S.cl x ∈ fixSpace ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
        mem_fixSpace.mpr hkfixx
      rw [hbot, Submodule.mem_bot] at hmem
      exact hxcl0 hmem
    have hfixpos : 0 < finrank (ZMod 2) (fixSpace ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
      have h := (Submodule.one_le_finrank_iff).mpr hfixne
      omega
    have hdim8 : finrank (ZMod 2) S.Qt = 8 := by
      rw [S.finrank_Qt_eq_two_mul_width, hw]
    have hCfix : C ⊓ fixSpace ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
      rw [hC]
      exact CFSG.LargeExtraspecial.Setting.AS35T.commSpace_inf_fixSpace_of_pow_odd
        (V := S.Qt) (σ := ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) (m := 5) (by norm_num) hk5'
    have h4C : 4 ∣ finrank (ZMod 2) C := by
      rw [hC]
      refine S2.four_dvd_finrank_of_pow_five_of_mapsTo hk5' ?_ hCfix
      intro v hv
      obtain ⟨w, hw⟩ := mem_commSpace.mp hv
      refine mem_commSpace.mpr ⟨((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w, ?_⟩
      rw [← hw, map_sub]
    have hCpos : 0 < finrank (ZMod 2) C := by
      rw [hC]
      have h := one_le_finrank_commSpace hklin
      omega
    have hdimC : finrank (ZMod 2) C = 4 := by
      have hsum := finrank_commSpace_add_finrank_fixSpace
        (((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
      rw [hdim8] at hsum
      rw [← hC] at hsum
      obtain ⟨m, hm⟩ := h4C
      omega
    have hWinv : ∀ v ∈ W, ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W := by
      intro v hv
      rw [← hyρ]
      exact mapsTo_clSub_UCore hyx v hv
    have hCinv : ∀ v ∈ C, ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ C := by
      intro v hv
      obtain ⟨w, hw⟩ := mem_commSpace.mp hv
      refine mem_commSpace.mpr ⟨((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w, ?_⟩
      rw [← hw, map_sub]
    have hvW : S.cl u ∈ W := S.cl_mem_clSub hu.1 hu.2
    have hsub : ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u) - S.cl u ∈ D := by
      refine ⟨?_, ?_⟩
      · exact W.sub_mem (hWinv (S.cl u) hvW) hvW
      · exact sub_mem_commSpace _ _
    have hsubne : ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u) - S.cl u ≠ 0 := by
      intro h0
      exact hmu (sub_eq_zero.mp h0)
    have hDne : D ≠ ⊥ := fun hbot => by
      have h0 : ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u) - S.cl u = 0 := by
        have hmem : ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u) - S.cl u ∈
            (⊥ : Submodule (ZMod 2) S.Qt) := by
          rw [← hbot]
          exact hsub
        exact (Submodule.mem_bot _).mp hmem
      exact hsubne h0
    have hDpos : 0 < finrank (ZMod 2) D := by
      have h := (Submodule.one_le_finrank_iff).mpr hDne
      omega
    have hDfix : D ⊓ fixSpace ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have hmem : v ∈ C ⊓ fixSpace ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hv.1.2, hv.2⟩
      rw [hCfix, Submodule.mem_bot] at hmem
      exact hmem
    have hDinv : ∀ v ∈ D, ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ D := by
      intro v hv
      exact ⟨hWinv v hv.1, hCinv v hv.2⟩
    have h4D : 4 ∣ finrank (ZMod 2) D :=
      S2.four_dvd_finrank_of_pow_five_of_mapsTo hk5' hDinv hDfix
    obtain ⟨m, hm⟩ := h4D
    have hle : finrank (ZMod 2) D ≤ 4 := by
      rw [← hdimC]
      exact Submodule.finrank_mono inf_le_right
    have hdimD : finrank (ZMod 2) D = 4 := by omega
    have hDC : D = C :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hdimD, hdimC])
    intro v hv
    have hle : C ≤ W := hDC ▸ inf_le_left
    exact hle hv

theorem six_le_finrank_clSub (hchar : IsCharTwoType G) (T : ThompsonInput S g x K Y)
    (hw : S.width = 4) : 6 ≤ finrank (ZMod 2) (S.clSub (UCore S x)) := by
  set W : Submodule (ZMod 2) S.Qt := S.clSub (UCore S x) with hW
  have hdim8 : finrank (ZMod 2) S.Qt = 8 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hfixK : ∀ v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin W, ∀ k ∈ K,
      ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv k hk
    refine Subgroup.closure_induction
      (p := fun k _ => ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ?_ ?_ ?_ ?_
      (T.le_closure hk)
    · intro x hx
      have hc : commSpace ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ W :=
        commSpace_le_clSub hchar T hw hx.1 hx.2
      have hv' : v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin
          (commSpace ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
        (LinearMap.BilinForm.orthogonal_le hc) hv
      rw [← fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate x.2] at hv'
      exact mem_fixSpace.mp hv'
    · rfl
    · intro x y _ _ hx hy
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, hx, hy]
    · intro x _ hx
      have := congrArg
        (fun w => (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))⁻¹ w) hx
      simpa using this.symm
  have hperp_le : LinearMap.BilinForm.orthogonal S.q.polarBilin W ≤ fixSub S K := by
    intro v hv
    rw [mem_fixSub]
    exact fun k hk => hfixK v hv k hk
  have hdimfix : finrank (ZMod 2) (fixSub S K) ≤ 2 :=
    T.finrank_le (fixSub S K) (fun v hv => (mem_fixSub (S := S) (X := K)).mp hv)
  have hdimperp : finrank (ZMod 2) (LinearMap.BilinForm.orthogonal S.q.polarBilin W) ≤ 2 :=
    (Submodule.finrank_mono hperp_le).trans hdimfix
  have horth := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
  have hleW : finrank (ZMod 2) W ≤ 8 := by
    rw [← hdim8]
    exact Submodule.finrank_le W
  omega

end CFSG.GF2Type.Smith1979.W4Swap.Thompson
