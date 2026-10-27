module

public import CFSG.LocalAnalysis.GH72.G3a
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.LocalAnalysis.GH72.G3bNine

public section

namespace CFSG.GH72

open Subgroup
open CFSG.CGT.Foote81L6 CFSG.CGT.Foote81L6.TStruct CFSG.GorensteinWalter.TwoClassFusion
open CFSG.ABGLocalTools
open scoped Pointwise

namespace Sec3Setting

variable {G : Type*} [Group G] [Finite G]

private theorem pResidual_two_eq_top_of_noIndexTwo (𝔖 : Sec3Setting G) :
    CFSG.Quasithin.pResidual 2 G = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_top_iff.mpr ?_
  intro x _
  rw [CFSG.Quasithin.pResidual]
  refine Subgroup.mem_iInf.mpr ?_
  intro N
  refine Subgroup.mem_iInf.mpr ?_
  intro hN
  refine Subgroup.mem_iInf.mpr ?_
  intro hpow
  have hquot : IsPGroup 2 (G ⧸ N) := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨k, hk⟩ := hpow g
    refine ⟨k, orderOf_dvd_iff_pow_eq_one.mpr ?_⟩
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (x := g ^ 2 ^ k)).mpr hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hquot
  have hNindex : N.index = 2 ^ n := by
    rw [Subgroup.index_eq_card]
    exact hn
  have hn0 : n = 0 := by
    by_contra hn0
    have hpos : 1 ≤ n := Nat.pos_of_ne_zero hn0
    haveI : N.Normal := hN
    obtain ⟨M, hM⟩ := CFSG.QuasiDihedralFusion.exists_index_two_of_two_pow_index
      (G := G) (K := N) hNindex hpos
    exact 𝔖.noIndexTwo M (Subgroup.normal_of_index_eq_two hM) hM
  have hNtop : N = ⊤ := by
    rw [← Subgroup.index_eq_one, hNindex, hn0, pow_zero]
  rw [hNtop]
  exact Subgroup.mem_top x

private structure PairData (𝔖 : Sec3Setting G) where
  a : ℕ
  ha : 2 ≤ a
  e : ↥𝔖.S₂ ≃* DihedralGroup (2 ^ a)
  c : G
  d : G
  z₂ : G
  hc : c ∈ 𝔖.S₂
  hd : d ∈ 𝔖.S₂
  hz : z₂ ∈ 𝔖.S₂
  hc2 : c * c = 1
  hd2 : d * d = 1
  hz2 : z₂ * z₂ = 1
  hgen : 𝔖.S₂ = Subgroup.closure {c, d}
  hzc : ∀ s ∈ 𝔖.S₂, s * z₂ = z₂ * s
  hce : e ⟨c, hc⟩ = DihedralGroup.sr 0
  hde : e ⟨d, hd⟩ = DihedralGroup.sr 1
  hze : e ⟨z₂, hz⟩ = CFSG.CGT.Foote81L6.zc a

private lemma exists_pairData (𝔖 : Sec3Setting G) : Nonempty (PairData 𝔖) := by
  classical
  obtain ⟨a, ha, ⟨e⟩⟩ := 𝔖.decomp.dih₂
  let cS : ↥𝔖.S₂ := e.symm (DihedralGroup.sr 0)
  let dS : ↥𝔖.S₂ := e.symm (DihedralGroup.sr 1)
  let zS : ↥𝔖.S₂ := e.symm (CFSG.CGT.Foote81L6.zc a)
  have hgen : 𝔖.S₂ = Subgroup.closure {(cS : G), (dS : G)} := by
    have htop : (⊤ : Subgroup ↥𝔖.S₂) = Subgroup.closure {cS, dS} := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective, MonoidHom.map_closure]
      have himg : e.toMonoidHom '' ({cS, dS} : Set ↥𝔖.S₂) =
          ({DihedralGroup.sr 0, DihedralGroup.sr 1} : Set (DihedralGroup (2 ^ a))) := by
        simp [cS, dS]
      rw [himg]
      exact (CFSG.QuasithinUnique.Setup.Family.dihedral_two_reflections_generate (2 ^ a)).symm
    have := congrArg (Subgroup.map (𝔖.S₂).subtype) htop
    simpa [Subgroup.map_top, MonoidHom.map_closure] using this
  have hzc : ∀ s ∈ 𝔖.S₂, s * (zS : G) = (zS : G) * s := by
    intro s hs
    have hzmem : zS ∈ Subgroup.center ↥𝔖.S₂ := dih_symm_zc_mem_center e (by omega)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzmem ⟨s, hs⟩)
  have hc2 : ((cS : G) * (cS : G) = 1) := by
    change ((cS * cS : ↥𝔖.S₂) : G) = 1
    have : cS * cS = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      simp [cS]
    rw [this, Subgroup.coe_one]
  have hd2 : ((dS : G) * (dS : G) = 1) := by
    change ((dS * dS : ↥𝔖.S₂) : G) = 1
    have : dS * dS = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      simp [dS]
    rw [this, Subgroup.coe_one]
  have hz2 : ((zS : G) * (zS : G) = 1) := by
    change ((zS * zS : ↥𝔖.S₂) : G) = 1
    have : zS * zS = 1 := dih_symm_zc_mul_self e (by omega)
    rw [this, Subgroup.coe_one]
  let P : PairData 𝔖 := {
    a := a
    ha := ha
    e := e
    c := (cS : G)
    d := (dS : G)
    z₂ := (zS : G)
    hc := cS.2
    hd := dS.2
    hz := zS.2
    hc2 := hc2
    hd2 := hd2
    hz2 := hz2
    hgen := hgen
    hzc := hzc
    hce := by simp [cS]
    hde := by simp [dS]
    hze := by simp [zS] }
  exact ⟨P⟩

private lemma zpowers_two_eq {a x : G} (ha : orderOf a = 2) (hx : x ∈ Subgroup.zpowers a) :
    x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, ha]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; simp [h]
  · right; simp [h]

private lemma center_eq_sup (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) (P : PairData 𝔖) :
    (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (𝔖.S : Set G) =
      𝔖.S₁ ⊔ Subgroup.zpowers P.z₂ := by
  haveI : IsKleinFour ↥𝔖.S₁ := h₁
  have hz_ne : P.z₂ ≠ 1 := by
    intro h
    have h1 : (⟨P.z₂, P.hz⟩ : ↥𝔖.S₂) = 1 := Subtype.ext h
    have h2 : CFSG.CGT.Foote81L6.zc P.a = 1 := by
      rw [← P.hze, h1, map_one]
    exact zc_ne_one (le_trans (by norm_num : 1 ≤ 2) P.ha) h2
  have hZ₂ : 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers P.z₂ := by
    obtain ⟨z, hzS, hzord, hZ⟩ :=
      CFSG.GH72.IsDihNonab.exists_inf_centralizer_self_eq 𝔖.decomp.dih₂
    have hZ' : 𝔖.S₂ ⊓ Subgroup.centralizer ((𝔖.S₂ : Subgroup G) : Set G) =
        Subgroup.zpowers z := by simpa using hZ
    have hzP : P.z₂ ∈ Subgroup.zpowers z := by
      rw [← hZ']
      refine ⟨P.hz, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro s hs
      exact P.hzc s hs
    have hzP' : P.z₂ = z := by
      rcases zpowers_two_eq hzord hzP with h | h
      · exact absurd h hz_ne
      · exact h
    rw [← hzP'] at hZ'
    exact hZ'
  have hS₁ : 𝔖.S₁ ⊓ Subgroup.centralizer (𝔖.S₁ : Set G) = 𝔖.S₁ := by
    letI : IsMulCommutative ↥𝔖.S₁ := IsKleinFour.isMulCommutative
    rw [inf_of_le_left]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (congrArg Subtype.val (IsMulCommutative.is_comm.comm
      (⟨x, hx⟩ : ↥𝔖.S₁) ⟨y, hy⟩)).symm
  calc
    (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (𝔖.S : Set G)
        = (𝔖.S₁ ⊓ Subgroup.centralizer (𝔖.S₁ : Set G)) ⊔
            (𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G)) :=
          𝔖.decomp.inf_centralizer_self
    _ = 𝔖.S₁ ⊔ Subgroup.zpowers P.z₂ := by rw [hS₁, hZ₂]

private lemma isFourIn_sup_t_z (𝔖 : Sec3Setting G) (P : PairData 𝔖) {t : G}
    {j : ZMod (2 ^ P.a)} (ht : t ∈ 𝔖.S₂) (hte : P.e ⟨t, ht⟩ = DihedralGroup.sr j) :
    IsFourIn 𝔖.S₂ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂) := by
  have hlift_sup : ∀ A B : Subgroup (DihedralGroup (2 ^ P.a)),
      liftSub P.e (A ⊔ B) = liftSub P.e A ⊔ liftSub P.e B := by
    intro A B
    simp [liftSub, Subgroup.map_sup]
  have hlift_zp : ∀ x : DihedralGroup (2 ^ P.a),
      liftSub P.e (Subgroup.zpowers x) =
        Subgroup.zpowers ((P.e.symm x : ↥𝔖.S₂) : G) := by
    intro x
    simp [liftSub]
  have ht_eq : t = (P.e.symm (DihedralGroup.sr j) : G) := by
    have h := congrArg P.e.symm hte
    exact congrArg Subtype.val (by simpa using h)
  have hz_eq : P.z₂ = (P.e.symm (zc P.a) : G) := by
    have h := congrArg P.e.symm P.hze
    exact congrArg Subtype.val (by simpa using h)
  have hVeq : Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂ =
      liftSub P.e (dihFour P.a j) := by
    rw [dihFour, hlift_sup, hlift_zp, hlift_zp, ht_eq, hz_eq]
  rw [hVeq]
  exact isFourIn_liftSub_dihFour P.e (le_trans (by norm_num : 1 ≤ 2) P.ha) j

private lemma c_ne_one {𝔖 : Sec3Setting G} (P : PairData 𝔖) : P.c ≠ 1 := by
  intro h
  have hsub : (⟨P.c, P.hc⟩ : ↥𝔖.S₂) = 1 := Subtype.ext h
  have h1 : DihedralGroup.sr (0 : ZMod (2 ^ P.a)) = 1 := by
    rw [← P.hce, hsub, map_one]
  exact sr_ne_one' 0 h1

private lemma d_ne_one {𝔖 : Sec3Setting G} (P : PairData 𝔖) : P.d ≠ 1 := by
  intro h
  have hsub : (⟨P.d, P.hd⟩ : ↥𝔖.S₂) = 1 := Subtype.ext h
  have h1 : DihedralGroup.sr (1 : ZMod (2 ^ P.a)) = 1 := by
    rw [← P.hde, hsub, map_one]
  exact sr_ne_one' 1 h1

private lemma z₂_ne_one {𝔖 : Sec3Setting G} (P : PairData 𝔖) : P.z₂ ≠ 1 := by
  intro h
  have hsub : (⟨P.z₂, P.hz⟩ : ↥𝔖.S₂) = 1 := by
    apply Subtype.ext
    exact h
  have h1 : zc P.a = 1 := by
    rw [← P.hze, hsub, map_one]
  exact zc_ne_one (le_trans (by norm_num : 1 ≤ 2) P.ha) h1

private lemma orderOf_c {𝔖 : Sec3Setting G} (P : PairData 𝔖) : orderOf P.c = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact P.hc2) (c_ne_one P)

private lemma orderOf_d {𝔖 : Sec3Setting G} (P : PairData 𝔖) : orderOf P.d = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact P.hd2) (d_ne_one P)

private lemma orderOf_z₂ {𝔖 : Sec3Setting G} (P : PairData 𝔖) : orderOf P.z₂ = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact P.hz2) (z₂_ne_one P)

private lemma center_S₂ (𝔖 : Sec3Setting G) (P : PairData 𝔖) :
    𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers P.z₂ := by
  obtain ⟨z, hzS, hzord, hZ⟩ :=
    CFSG.GH72.IsDihNonab.exists_inf_centralizer_self_eq 𝔖.decomp.dih₂
  have hZ' : 𝔖.S₂ ⊓ Subgroup.centralizer ((𝔖.S₂ : Subgroup G) : Set G) =
      Subgroup.zpowers z := by simpa using hZ
  have hzP : P.z₂ ∈ Subgroup.zpowers z := by
    rw [← hZ']
    refine ⟨P.hz, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro s hs
    exact P.hzc s hs
  have hzP' : P.z₂ = z := by
    rcases zpowers_two_eq hzord hzP with h | h
    · exact absurd h (z₂_ne_one P)
    · exact h
  rw [← hzP'] at hZ'
  exact hZ'

private lemma isE16_A (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) (P : PairData 𝔖) {t : G}
    (hfour : IsFourIn 𝔖.S₂ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂)) :
    IsE16 (𝔖.S₁ ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂)) :=
  𝔖.decomp.isE16_sup (CFSG.GH72.IsDih.isFourIn_self_of_isKleinFour h₁) hfour

private lemma A_le_S (𝔖 : Sec3Setting G) (P : PairData 𝔖) {t : G} (ht : t ∈ 𝔖.S₂) :
    𝔖.S₁ ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂) ≤ 𝔖.S := by
  rw [← 𝔖.decomp.sup_eq]
  exact sup_le le_sup_left (sup_le ((Subgroup.zpowers_le.mpr ht).trans le_sup_right)
    ((Subgroup.zpowers_le.mpr P.hz).trans le_sup_right))

private lemma A_le_centralizer_t (𝔖 : Sec3Setting G) (P : PairData 𝔖) {t : G}
    (ht : t ∈ 𝔖.S₂) :
    𝔖.S₁ ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂) ≤
      Subgroup.centralizer ({t} : Set G) := by
  refine sup_le ?_ (sup_le ?_ ?_)
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (𝔖.decomp.comm hx ht).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk]
    exact (Commute.zpow_left (Commute.refl t) k).eq.symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk]
    exact (Commute.zpow_left (P.hzc t ht).symm k).eq.symm

private lemma cd_image {𝔖 : Sec3Setting G} (P : PairData 𝔖) :
    P.e ⟨P.c * P.d, mul_mem P.hc P.hd⟩ = DihedralGroup.r 1 := by
  have hprod : (⟨P.c * P.d, mul_mem P.hc P.hd⟩ : ↥𝔖.S₂) = ⟨P.c, P.hc⟩ * ⟨P.d, P.hd⟩ := rfl
  rw [hprod, map_mul, P.hce, P.hde]
  simp [DihedralGroup.sr_mul_sr]

private lemma orderOf_cd {𝔖 : Sec3Setting G} (P : PairData 𝔖) : orderOf (P.c * P.d) = 2 ^ P.a := by
  have hcdS₂ : P.c * P.d ∈ 𝔖.S₂ := mul_mem P.hc P.hd
  change orderOf ((⟨P.c * P.d, hcdS₂⟩ : ↥𝔖.S₂) : G) = 2 ^ P.a
  rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq P.e ⟨P.c * P.d, hcdS₂⟩,
    cd_image P, DihedralGroup.orderOf_r_one]

private lemma z₂_eq_cd_pow (𝔖 : Sec3Setting G) (P : PairData 𝔖) :
    P.z₂ = (P.c * P.d) ^ 2 ^ (P.a - 1) := by
  have hcd : P.c * P.d ∈ 𝔖.S₂ := mul_mem P.hc P.hd
  have hk : 1 ≤ P.a := le_trans (by norm_num : 1 ≤ 2) P.ha
  have h1 : P.e ((⟨P.c * P.d, hcd⟩ : ↥𝔖.S₂) ^ 2 ^ (P.a - 1)) =
      P.e ⟨P.z₂, P.hz⟩ := by
    rw [map_pow, cd_image P, DihedralGroup.r_one_pow, P.hze,
      CFSG.CGT.Foote81L6.TStruct.zc_eq_r hk]
  have h2 := congrArg Subtype.val (P.e.injective h1)
  simpa using h2.symm

private lemma relIndex_R (𝔖 : Sec3Setting G) (P : PairData 𝔖) :
    (𝔖.S₁ ⊔ Subgroup.zpowers (P.c * P.d)).relIndex (𝔖.S : Subgroup G) = 2 := by
  have hle : Subgroup.zpowers (P.c * P.d) ≤ 𝔖.S₂ :=
    Subgroup.zpowers_le.mpr (mul_mem P.hc P.hd)
  rw [𝔖.decomp.relIndex_sup_left hle]
  have hcardS₂ : Nat.card ↥𝔖.S₂ = 2 * 2 ^ P.a := by
    rw [Nat.card_congr P.e.toEquiv, DihedralGroup.nat_card]
  have hcard_cyc : Nat.card ↥(Subgroup.zpowers (P.c * P.d)) = 2 ^ P.a := by
    rw [Nat.card_zpowers, orderOf_cd P]
  have hrel := Subgroup.relIndex_mul_card (H := Subgroup.zpowers (P.c * P.d)) (K := 𝔖.S₂)
  rw [inf_of_le_left hle, hcard_cyc, hcardS₂] at hrel
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) P.a) hrel

private lemma involution_in_R_mem_center (𝔖 : Sec3Setting G) (P : PairData 𝔖) {v : G}
    (hvR : v ∈ 𝔖.S₁ ⊔ Subgroup.zpowers (P.c * P.d)) (hv2 : v * v = 1) :
    v ∈ 𝔖.S₁ ⊔ Subgroup.zpowers P.z₂ := by
  have hcdS₂ : P.c * P.d ∈ 𝔖.S₂ := mul_mem P.hc P.hd
  have hcomm : ∀ a ∈ 𝔖.S₁, ∀ b ∈ Subgroup.zpowers (P.c * P.d), a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hk]
    exact (Commute.zpow_right (𝔖.decomp.comm ha hcdS₂) k).eq
  obtain ⟨x, hx, y, hy, rfl⟩ :=
    (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcomm)).mp hvR
  have hyS₂ : y ∈ 𝔖.S₂ := (Subgroup.zpowers_le.mpr hcdS₂) hy
  have hxy := (𝔖.decomp.mul_self_iff hx hyS₂).mp hv2
  have hy2 : y * y = 1 := hxy.2
  by_cases hy1 : y = 1
  · rw [hy1, mul_one]
    exact Subgroup.mem_sup_left hx
  have hyord : orderOf y = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
  have hmem_e : P.e ⟨y, hyS₂⟩ ∈ Subgroup.zpowers (DihedralGroup.r 1) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hmap : P.e ⟨y, hyS₂⟩ = (DihedralGroup.r 1) ^ k := by
      have hsub : (⟨y, hyS₂⟩ : ↥𝔖.S₂) = (⟨P.c * P.d, hcdS₂⟩ : ↥𝔖.S₂) ^ k := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow]
        exact hk.symm
      rw [hsub, map_zpow, cd_image P]
    rw [hmap]
    exact Subgroup.zpow_mem (K := Subgroup.zpowers (DihedralGroup.r 1)) (Subgroup.mem_zpowers _) k
  have hrot : P.e ⟨y, hyS₂⟩ =
      DihedralGroup.r ((2 ^ (P.a - 1) : ℕ) : ZMod (2 ^ P.a)) := by
    have hord_e : orderOf (P.e ⟨y, hyS₂⟩) = 2 := by
      have hsq : P.e ⟨y, hyS₂⟩ * P.e ⟨y, hyS₂⟩ = 1 := by
        rw [← map_mul, show (⟨y, hyS₂⟩ : ↥𝔖.S₂) * ⟨y, hyS₂⟩ = 1 by
          apply Subtype.ext
          simpa using hy2, map_one]
      have hne : P.e ⟨y, hyS₂⟩ ≠ 1 := by
        intro h
        apply hy1
        have h1 : (⟨y, hyS₂⟩ : ↥𝔖.S₂) = 1 := P.e.injective (by rw [h, map_one])
        exact congrArg Subtype.val h1
      exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
    rcases eq_r_half_or_sr_of_orderOf_eq_two P.ha hord_e with h | ⟨k, hk⟩
    · exact h
    · exfalso
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem_e
      rw [hk, DihedralGroup.r_one_zpow] at hj
      exact (by cases hj)
  have hyz : y = P.z₂ := by
    have h1 : P.e ⟨y, hyS₂⟩ = P.e ⟨P.z₂, P.hz⟩ := by
      rw [P.hze, hrot, ← zc_eq_r (le_trans (by norm_num : 1 ≤ 2) P.ha)]
    exact congrArg Subtype.val (P.e.injective h1)
  rw [hyz]
  exact mul_mem (Subgroup.mem_sup_left hx)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers P.z₂))

private lemma R_le_S (𝔖 : Sec3Setting G) (P : PairData 𝔖) :
    𝔖.S₁ ⊔ Subgroup.zpowers (P.c * P.d) ≤ 𝔖.S := by
  rw [← 𝔖.decomp.sup_eq]
  exact sup_le le_sup_left ((Subgroup.zpowers_le.mpr (mul_mem P.hc P.hd)).trans le_sup_right)

private lemma exists_conj_into_R (𝔖 : Sec3Setting G) (P : PairData 𝔖) {t : G}
    (htord : orderOf t = 2) :
    ∃ x : G, x⁻¹ * t * x ∈ 𝔖.S₁ ⊔ Subgroup.zpowers (P.c * P.d) := by
  by_contra hno
  push Not at hno
  have hnot := CFSG.Quasithin.thompson_transfer_lemma 𝔖.S (R_le_S 𝔖 P) (relIndex_R 𝔖 P)
    htord hno
  rw [pResidual_two_eq_top_of_noIndexTwo 𝔖] at hnot
  exact hnot (Subgroup.mem_top t)

private lemma Z_le_centralizer_S (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) (P : PairData 𝔖) :
    𝔖.S₁ ⊔ Subgroup.zpowers P.z₂ ≤ Subgroup.centralizer (𝔖.S : Set G) := by
  haveI : IsKleinFour ↥𝔖.S₁ := h₁
  letI : IsMulCommutative ↥𝔖.S₁ := IsKleinFour.isMulCommutative
  refine sup_le ?_ ?_
  · intro x hx s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := 𝔖.decomp.mem_iff.mp hs
    calc (a * b) * x = a * (b * x) := by group
      _ = a * (x * b) := by rw [(𝔖.decomp.comm hx hb).symm]
      _ = (a * x) * b := by group
      _ = (x * a) * b := by
          have hax : a * x = x * a :=
            congrArg Subtype.val (IsMulCommutative.is_comm.comm
              (⟨a, ha⟩ : ↥𝔖.S₁) ⟨x, hx⟩)
          rw [hax]
      _ = x * (a * b) := by group
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk]
    obtain ⟨a, ha, b, hb, rfl⟩ := 𝔖.decomp.mem_iff.mp hs
    calc (a * b) * P.z₂ ^ k = a * (b * P.z₂ ^ k) := by group
      _ = a * (P.z₂ ^ k * b) := by
          rw [(Commute.zpow_left (P.hzc b hb).symm k).eq]
      _ = (a * P.z₂ ^ k) * b := by group
      _ = (P.z₂ ^ k * a) * b := by
          rw [(Commute.zpow_left (𝔖.decomp.comm ha P.hz).symm k).eq]
      _ = P.z₂ ^ k * (a * b) := by group

private lemma exists_conj_le_of_isSylowOf' {K P Q : Subgroup G}
    (hP : IsSylowOf 2 P K) (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) :
    ∃ c ∈ K, ∀ q ∈ Q, c * q * c⁻¹ ∈ P := by
  obtain ⟨P₀, hP₀⟩ := hP.exists_sylow_eq_subgroupOf
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K R P₀
  refine ⟨c, c.2, fun q hq => ?_⟩
  have h1 : MulAut.conj c • (⟨q, hQK hq⟩ : K) ∈ MulAut.conj c • (R : Subgroup K) :=
    smul_mem_pointwise_smul _ (MulAut.conj c) (R : Subgroup K) (hR (mem_subgroupOf.mpr hq))
  rw [← Sylow.coe_subgroup_smul, hc, hP₀, mem_subgroupOf] at h1
  simpa [MulAut.conj_apply] using h1

private lemma exists_conj_extremal' {S : Subgroup G} (hS : IsPGroup 2 S) {u v h : G}
    (hv : IsSylowOf 2 (S ⊓ Subgroup.centralizer ({v} : Set G))
      (Subgroup.centralizer ({v} : Set G)))
    (huv : h⁻¹ * v * h = u) :
    ∃ g : G, g⁻¹ * u * g = v ∧
      ∀ x ∈ S ⊓ Subgroup.centralizer ({u} : Set G),
        g⁻¹ * x * g ∈ S ⊓ Subgroup.centralizer ({v} : Set G) := by
  set P := S ⊓ Subgroup.centralizer ({u} : Set G)
  set P' := P.map (MulAut.conj h).toMonoidHom
  have hP'K : P' ≤ Subgroup.centralizer ({v} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxu : x * u = u * x := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
    rw [mem_centralizer_singleton_iff]
    change h * x * h⁻¹ * v = v * (h * x * h⁻¹)
    have hv' : v = h * u * h⁻¹ := by rw [← huv]; group
    rw [hv']
    calc h * x * h⁻¹ * (h * u * h⁻¹) = h * (x * u) * h⁻¹ := by group
      _ = h * (u * x) * h⁻¹ := by rw [hxu]
      _ = h * u * h⁻¹ * (h * x * h⁻¹) := by group
  have hP' : IsPGroup 2 P' := (hS.to_le inf_le_left).map _
  obtain ⟨c, hcK, hc⟩ := exists_conj_le_of_isSylowOf' hv hP'K hP'
  refine ⟨h⁻¹ * c⁻¹, ?_, fun x hx => ?_⟩
  · have hcv : c * v = v * c := mem_centralizer_singleton_iff.mp hcK
    rw [← huv]
    calc (h⁻¹ * c⁻¹)⁻¹ * (h⁻¹ * v * h) * (h⁻¹ * c⁻¹) = c * v * c⁻¹ := by group
      _ = v := by rw [hcv]; group
  · have hx' : h * x * h⁻¹ ∈ P' := ⟨x, hx, rfl⟩
    have := hc (h * x * h⁻¹) hx'
    rwa [show c * (h * x * h⁻¹) * c⁻¹ = (h⁻¹ * c⁻¹)⁻¹ * x * (h⁻¹ * c⁻¹) by group] at this

private lemma exists_good_conj (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) (P : PairData 𝔖)
    {t : G} (ht : t ∈ 𝔖.S₂) (htord : orderOf t = 2)
    (hfour : IsFourIn 𝔖.S₂ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂)) :
    ∃ g v : G, g * t * g⁻¹ = v ∧ v ∈ 𝔖.S₁ ⊔ Subgroup.zpowers P.z₂ ∧ v * v = 1 ∧
      (𝔖.S₁ ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂)).map
          (MulAut.conj g).toMonoidHom =
        (𝔖.S₁ ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂)) ∧
      (𝔖.S₁ ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂)).map
          (MulAut.conj g⁻¹).toMonoidHom =
        (𝔖.S₁ ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂)) := by
  classical
  let A : Subgroup G := 𝔖.S₁ ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂)
  have hA16 : IsE16 A := isE16_A 𝔖 h₁ P hfour
  have hAS : A ≤ 𝔖.S := A_le_S 𝔖 P ht
  have hAC : A ≤ Subgroup.centralizer ({t} : Set G) := A_le_centralizer_t 𝔖 P ht
  obtain ⟨x, hxR⟩ := exists_conj_into_R 𝔖 P htord
  set v : G := x⁻¹ * t * x with hv_def
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← htord]
    exact pow_orderOf_eq_one t
  have hv2 : v * v = 1 := by
    rw [hv_def]
    calc (x⁻¹ * t * x) * (x⁻¹ * t * x) = x⁻¹ * (t * t) * x := by group
      _ = 1 := by rw [ht2]; group
  have hvZ : v ∈ 𝔖.S₁ ⊔ Subgroup.zpowers P.z₂ := involution_in_R_mem_center 𝔖 P hxR hv2
  have hvcent : (𝔖.S : Subgroup G) ≤ Subgroup.centralizer ({v} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp (Z_le_centralizer_S 𝔖 h₁ P hvZ) s hs).symm
  have hSyl : IsSylowOf 2 (𝔖.S : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, 𝔖.S.isPGroup', by simpa using 𝔖.S.not_dvd_index⟩
  have hvSyl : IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({v} : Set G))
      (Subgroup.centralizer ({v} : Set G)) := by
    rw [inf_of_le_left hvcent]
    exact IsSylowOf.of_le hSyl hvcent le_top
  have huv : (x⁻¹)⁻¹ * v * x⁻¹ = t := by
    rw [hv_def]
    group
  obtain ⟨g, hgc, hgmap⟩ := exists_conj_extremal'
    (S := (𝔖.S : Subgroup G)) (u := t) (v := v) (h := x⁻¹) 𝔖.S.isPGroup' hvSyl huv
  have hA'le : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ (𝔖.S : Subgroup G) := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) :=
      ⟨hAS hz, hAC hz⟩
    have hmem := (hgmap z hz').1
    change g⁻¹ * z * g ∈ (𝔖.S : Subgroup G) at hmem
    simpa [MulAut.conj_apply, inv_inv, mul_assoc] using hmem
  have hA'16 : IsE16 (A.map (MulAut.conj g⁻¹).toMonoidHom) :=
    hA16.map _ (MulAut.conj g⁻¹).injective
  have hgg : (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
    rw [CFSG.CGT.Foote81L6.TStruct.map_conj_map_conj, mul_inv_cancel, map_conj_one]
  obtain ⟨s, hsS, hsA⟩ :=
    lemma_3_1 𝔖 (A.map (MulAut.conj g⁻¹).toMonoidHom) A hA'le hAS hA'16 hA16 g hgg
  have hAfix : A.map (MulAut.conj (s * g⁻¹)).toMonoidHom = A := by
    rw [CFSG.CGT.Foote81L6.TStruct.map_conj_map_conj] at hsA
    exact hsA
  have hAfix' : A.map (MulAut.conj (s * g⁻¹)⁻¹).toMonoidHom = A := by
    have h1 : (A.map (MulAut.conj (s * g⁻¹)).toMonoidHom).map
        (MulAut.conj (s * g⁻¹)⁻¹).toMonoidHom = A.map (MulAut.conj (s * g⁻¹)⁻¹).toMonoidHom := by
      rw [hAfix]
    rw [CFSG.CGT.Foote81L6.TStruct.map_conj_map_conj, inv_mul_cancel, map_conj_one] at h1
    exact h1.symm
  refine ⟨s * g⁻¹, v, ?_, hvZ, hv2, hAfix, ?_⟩
  · have hstep : (s * g⁻¹) * t * (s * g⁻¹)⁻¹ = s * (g⁻¹ * t * g) * s⁻¹ := by
      group
    rw [hstep, hgc]
    have hcomm : s * v = v * s :=
      Subgroup.mem_centralizer_iff.mp (Z_le_centralizer_S 𝔖 h₁ P hvZ) s hsS
    rw [hcomm]
    group
  · simpa [A] using hAfix'

private lemma map_centralizer_conj (S : Subgroup G) (h : G) :
    (Subgroup.centralizer (S : Set G)).map (MulAut.conj h).toMonoidHom =
      Subgroup.centralizer ((S.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (hy w hw)
  · intro hx
    refine ⟨(MulAut.conj h).symm x, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hcomm := hx ((MulAut.conj h) z) (Subgroup.mem_map_of_mem _ hz)
    have hconj := congrArg ((MulAut.conj h).symm) hcomm
    simpa [MulAut.conj_apply, mul_assoc] using hconj

private lemma center_map_conj (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) (P : PairData 𝔖)
    (h : G) :
    ((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (𝔖.S : Set G)).map
        (MulAut.conj h).toMonoidHom =
      ((𝔖.S : Subgroup G).map (MulAut.conj h).toMonoidHom) ⊓
        Subgroup.centralizer
          (((𝔖.S : Subgroup G).map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj h).injective]
  congr 1
  exact map_centralizer_conj (𝔖.S : Subgroup G) h

private lemma two_element_normalizer_centralizes {S Z : Subgroup G}
    (hS : IsSylowOf 2 S ⊤)
    (hZ : Z = S ⊓ Subgroup.centralizer (S : Set G))
    {y : G} (hyN : y ∈ Subgroup.normalizer (Z : Set G))
    (hy2 : IsPGroup 2 (Subgroup.zpowers y)) :
    y ∈ Subgroup.centralizer (Z : Set G) := by
  have hSN : S ≤ Subgroup.normalizer (Z : Set G) := by
    have hconj_mem : ∀ s ∈ S, ∀ x ∈ Z, s * x * s⁻¹ ∈ Z := by
      intro s hs x hx
      rw [hZ] at hx
      obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.mp hx
      rw [hZ]
      refine ⟨S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs), ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hxC
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro t ht
      calc t * (s * x * s⁻¹) = (t * s) * x * s⁻¹ := by group
        _ = (s * (s⁻¹ * t * s)) * x * s⁻¹ := by group
        _ = s * ((s⁻¹ * t * s) * x) * s⁻¹ := by group
        _ = s * (x * (s⁻¹ * t * s)) * s⁻¹ := by
            rw [hxC (s⁻¹ * t * s) (S.mul_mem (S.mul_mem (S.inv_mem hs) ht) hs)]
        _ = (s * x * s⁻¹) * t := by group
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj_mem s hs x
    · intro hx
      have := hconj_mem s⁻¹ (S.inv_mem hs) (s * x * s⁻¹) hx
      simpa [mul_assoc] using this
  have hSylN : IsSylowOf 2 S (Subgroup.normalizer (Z : Set G)) :=
    IsSylowOf.of_le hS hSN le_top
  have hyN' : Subgroup.zpowers y ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.zpowers_le.mpr hyN
  obtain ⟨c, hcN, hcS⟩ := exists_conj_le_of_isSylowOf' hSylN hyN' hy2
  have hycS : c * y * c⁻¹ ∈ S := hcS y (Subgroup.mem_zpowers y)
  have hSCZ : S ≤ Subgroup.centralizer (Z : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hZ] at hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 s hs).symm
  have hycC : c * y * c⁻¹ ∈ Subgroup.centralizer (Z : Set G) := hSCZ hycS
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : c * z * c⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hcN z).mp hz
  have hcomm := Subgroup.mem_centralizer_iff.mp hycC (c * z * c⁻¹) hz'
  have := congrArg (fun t => c⁻¹ * t * c) hcomm
  simpa [mul_assoc] using this

private lemma neg_half_zmod {m : ℕ} (hm : 1 ≤ m) :
    -((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  have hpow : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  rw [neg_eq_iff_add_eq_zero]
  rw [← Nat.cast_add, hpow, ZMod.natCast_self]

private lemma exists_conj_c_z₂ (𝔖 : Sec3Setting G) (P : PairData 𝔖) :
    ∃ y ∈ 𝔖.S₂, y * P.c * y⁻¹ = P.c * P.z₂ ∧ y * P.d * y⁻¹ = P.d * P.z₂ ∧
      y * P.z₂ * y⁻¹ = P.z₂ := by
  classical
  let k : ℕ := 2 ^ (P.a - 2)
  let yD : DihedralGroup (2 ^ P.a) := DihedralGroup.r (-(k : ZMod (2 ^ P.a)))
  let yS : ↥𝔖.S₂ := P.e.symm yD
  let y : G := yS
  have hyS₂ : y ∈ 𝔖.S₂ := yS.2
  have hyD : P.e yS = yD := P.e.apply_symm_apply yD
  have hkadd : (k : ZMod (2 ^ P.a)) + (k : ZMod (2 ^ P.a)) =
      ((2 ^ (P.a - 1) : ℕ) : ZMod (2 ^ P.a)) := by
    rw [← Nat.cast_add]
    congr 1
    have hpa : 2 ≤ P.a := P.ha
    have h2 : 2 ^ (P.a - 1) = 2 ^ (P.a - 2) * 2 := by
      rw [show P.a - 1 = (P.a - 2) + 1 by omega, pow_succ]
    rw [h2]
    ring
  have hneg := neg_half_zmod (m := P.a) (le_trans (by norm_num : 1 ≤ 2) P.ha)
  have hc : y * P.c * y⁻¹ = P.c * P.z₂ := by
    let lhs : ↥𝔖.S₂ := ⟨y * P.c * y⁻¹,
      𝔖.S₂.mul_mem (𝔖.S₂.mul_mem hyS₂ P.hc) (𝔖.S₂.inv_mem hyS₂)⟩
    let rhs : ↥𝔖.S₂ := ⟨P.c * P.z₂, 𝔖.S₂.mul_mem P.hc P.hz⟩
    have h : P.e lhs = P.e rhs := by
      have hlhs : lhs = yS * ⟨P.c, P.hc⟩ * yS⁻¹ := by ext; rfl
      have hrhs : rhs = ⟨P.c, P.hc⟩ * ⟨P.z₂, P.hz⟩ := by ext; rfl
      simp only [hlhs, hrhs, map_mul, map_inv, hyD, P.hce, P.hze,
        CFSG.CGT.Foote81L6.TStruct.zc_eq_r (le_trans (by norm_num : 1 ≤ 2) P.ha)]
      show DihedralGroup.r (-(k : ZMod (2 ^ P.a))) * DihedralGroup.sr 0 *
          (DihedralGroup.r (-(k : ZMod (2 ^ P.a))))⁻¹ =
        DihedralGroup.sr 0 * DihedralGroup.r ((2 ^ (P.a - 1) : ℕ) : ZMod (2 ^ P.a))
      calc
        DihedralGroup.r (-(k : ZMod (2 ^ P.a))) * DihedralGroup.sr 0 *
            (DihedralGroup.r (-(k : ZMod (2 ^ P.a))))⁻¹
            = DihedralGroup.r (-(k : ZMod (2 ^ P.a))) * DihedralGroup.sr 0 *
                DihedralGroup.r (k : ZMod (2 ^ P.a)) := by
                rw [DihedralGroup.inv_r, neg_neg]
        _ = DihedralGroup.sr (0 - -(k : ZMod (2 ^ P.a))) *
                DihedralGroup.r (k : ZMod (2 ^ P.a)) := by rw [DihedralGroup.r_mul_sr]
        _ = DihedralGroup.sr (0 - -(k : ZMod (2 ^ P.a)) + (k : ZMod (2 ^ P.a))) := by
              rw [DihedralGroup.sr_mul_r]
        _ = DihedralGroup.sr 0 * DihedralGroup.r ((2 ^ (P.a - 1) : ℕ) : ZMod (2 ^ P.a)) := by
              rw [DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq]
              rw [show (0 : ZMod (2 ^ P.a)) - -(k : ZMod (2 ^ P.a)) +
                  (k : ZMod (2 ^ P.a)) = (k : ZMod (2 ^ P.a)) + (k : ZMod (2 ^ P.a)) by ring,
                hkadd]
              ring
    exact congrArg Subtype.val (P.e.injective h)
  have hd : y * P.d * y⁻¹ = P.d * P.z₂ := by
    let lhs : ↥𝔖.S₂ := ⟨y * P.d * y⁻¹,
      𝔖.S₂.mul_mem (𝔖.S₂.mul_mem hyS₂ P.hd) (𝔖.S₂.inv_mem hyS₂)⟩
    let rhs : ↥𝔖.S₂ := ⟨P.d * P.z₂, 𝔖.S₂.mul_mem P.hd P.hz⟩
    have h : P.e lhs = P.e rhs := by
      have hlhs : lhs = yS * ⟨P.d, P.hd⟩ * yS⁻¹ := by ext; rfl
      have hrhs : rhs = ⟨P.d, P.hd⟩ * ⟨P.z₂, P.hz⟩ := by ext; rfl
      simp only [hlhs, hrhs, map_mul, map_inv, hyD, P.hde, P.hze,
        CFSG.CGT.Foote81L6.TStruct.zc_eq_r (le_trans (by norm_num : 1 ≤ 2) P.ha)]
      show DihedralGroup.r (-(k : ZMod (2 ^ P.a))) * DihedralGroup.sr 1 *
          (DihedralGroup.r (-(k : ZMod (2 ^ P.a))))⁻¹ =
        DihedralGroup.sr 1 * DihedralGroup.r ((2 ^ (P.a - 1) : ℕ) : ZMod (2 ^ P.a))
      calc
        DihedralGroup.r (-(k : ZMod (2 ^ P.a))) * DihedralGroup.sr 1 *
            (DihedralGroup.r (-(k : ZMod (2 ^ P.a))))⁻¹
            = DihedralGroup.r (-(k : ZMod (2 ^ P.a))) * DihedralGroup.sr 1 *
                DihedralGroup.r (k : ZMod (2 ^ P.a)) := by
                rw [DihedralGroup.inv_r, neg_neg]
        _ = DihedralGroup.sr (1 - -(k : ZMod (2 ^ P.a))) *
                DihedralGroup.r (k : ZMod (2 ^ P.a)) := by rw [DihedralGroup.r_mul_sr]
        _ = DihedralGroup.sr (1 - -(k : ZMod (2 ^ P.a)) + (k : ZMod (2 ^ P.a))) := by
              rw [DihedralGroup.sr_mul_r]
        _ = DihedralGroup.sr 1 * DihedralGroup.r ((2 ^ (P.a - 1) : ℕ) : ZMod (2 ^ P.a)) := by
              rw [DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq]
              rw [show (1 : ZMod (2 ^ P.a)) - -(k : ZMod (2 ^ P.a)) +
                  (k : ZMod (2 ^ P.a)) = 1 + ((k : ZMod (2 ^ P.a)) + (k : ZMod (2 ^ P.a))) by ring,
                hkadd]
    exact congrArg Subtype.val (P.e.injective h)
  have hz : y * P.z₂ * y⁻¹ = P.z₂ := by
    rw [P.hzc y hyS₂]
    group
  exact ⟨y, hyS₂, hc, hd, hz⟩

private lemma card_Z (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) (P : PairData 𝔖) :
    Nat.card ↥(𝔖.S₁ ⊔ Subgroup.zpowers P.z₂) = 8 := by
  have hdisj : 𝔖.S₁ ⊓ Subgroup.zpowers P.z₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases zpowers_two_eq (orderOf_z₂ P) hx.2 with h | h
    · exact h
    · exfalso
      have hxbot : x ∈ 𝔖.S₁ ⊓ 𝔖.S₂ := ⟨hx.1, h ▸ P.hz⟩
      rw [𝔖.decomp.inf_eq, Subgroup.mem_bot] at hxbot
      exact z₂_ne_one P (h.symm.trans hxbot)
  have hcomm : ∀ a ∈ 𝔖.S₁, ∀ b ∈ Subgroup.zpowers P.z₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hk]
    exact (Commute.zpow_right (𝔖.decomp.comm ha P.hz) k).eq
  rw [CFSG.CGT.Foote81L6.card_sup_of_le_normalizer (le_normalizer_of_comm hcomm) hdisj,
    @IsKleinFour.card_four ↥𝔖.S₁ _ h₁, Nat.card_zpowers, orderOf_z₂ P]

private lemma z₂_not_mem_Zstar (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) (P : PairData 𝔖)
    {t : G} (ht : t ∈ 𝔖.S₂) (A : Subgroup G)
    (hA : A = 𝔖.S₁ ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂))
    {g v y : G} (hg : g * t * g⁻¹ = v)
    (hvZ : v ∈ 𝔖.S₁ ⊔ Subgroup.zpowers P.z₂)
    (hAfix' : A.map (MulAut.conj g⁻¹).toMonoidHom = A)
    (hyS₂ : y ∈ 𝔖.S₂) (hyt : y * t * y⁻¹ = t * P.z₂)
    (hyz : y * P.z₂ * y⁻¹ = P.z₂) :
    P.z₂ ∉ (𝔖.S₁ ⊔ Subgroup.zpowers P.z₂).map (MulAut.conj g⁻¹).toMonoidHom := by
  classical
  let S₁ : Subgroup G := 𝔖.S₁
  let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂
  let Z : Subgroup G := S₁ ⊔ Subgroup.zpowers P.z₂
  let Sstar : Subgroup G := (𝔖.S : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom
  let Zstar : Subgroup G := Z.map (MulAut.conj g⁻¹).toMonoidHom
  intro hz₂
  have hZeq : Z = (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (𝔖.S : Set G) := by
    simpa [Z] using (center_eq_sup 𝔖 h₁ P).symm
  have hZstar_center : Zstar = Sstar ⊓ Subgroup.centralizer (Sstar : Set G) := by
    have h := center_map_conj 𝔖 h₁ P g⁻¹
    rw [← hZeq] at h
    exact h
  have htZstar : t ∈ Zstar := by
    have ht_eq : t = (MulAut.conj g⁻¹) v := by
      rw [MulAut.conj_apply, inv_inv]
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = g⁻¹ * v * g := by rw [hg]
    rw [ht_eq]
    exact Subgroup.mem_map_of_mem _ hvZ
  have hVZ : V ≤ Zstar :=
    sup_le (Subgroup.zpowers_le.mpr htZstar) (Subgroup.zpowers_le.mpr hz₂)
  let Astar : Subgroup G := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hAstar : Astar = A := hAfix'
  have hZcard : Nat.card ↥Z = 8 := card_Z 𝔖 h₁ P
  have hZstar_card : Nat.card ↥Zstar = 8 := by
    change Nat.card ↥(Z.map (MulAut.conj g⁻¹).toMonoidHom) = 8
    rw [Subgroup.card_map_of_injective (K := Z) (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective]
    exact hZcard
  have hZA : Z ≤ A := by
    rw [hA]
    exact sup_le le_sup_left (le_trans (le_sup_right : Subgroup.zpowers P.z₂ ≤ V) le_sup_right)
  have hZstar_le_A : Zstar ≤ A := by
    change Z.map (MulAut.conj g⁻¹).toMonoidHom ≤ A
    rw [← hAstar]
    exact Subgroup.map_mono hZA
  have hSstarSylow : IsSylowOf 2 Sstar ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · exact 𝔖.S.isPGroup'.map _
    · rw [Subgroup.relIndex_top_right]
      have hindex : Sstar.index = (𝔖.S : Subgroup G).index := by
        change ((𝔖.S : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom).index =
          (𝔖.S : Subgroup G).index
        rw [Subgroup.index_map_of_bijective (MulAut.conj g⁻¹).bijective]
      rw [hindex]
      exact 𝔖.S.not_dvd_index
  have hdisjS₁V : S₁ ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    have hwbot : w ∈ 𝔖.S₁ ⊓ 𝔖.S₂ :=
      ⟨hw.1, (sup_le (Subgroup.zpowers_le.mpr ht) (Subgroup.zpowers_le.mpr P.hz)) hw.2⟩
    rw [𝔖.decomp.inf_eq, Subgroup.mem_bot] at hwbot
    exact hwbot
  have hcommS₁V : ∀ a ∈ S₁, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    exact 𝔖.decomp.comm ha ((sup_le (Subgroup.zpowers_le.mpr ht)
      (Subgroup.zpowers_le.mpr P.hz)) hb)
  have hyt' : (MulEquiv.toMonoidHom (MulAut.conj y)) t = t * P.z₂ := hyt
  have hyz' : (MulEquiv.toMonoidHom (MulAut.conj y)) P.z₂ = P.z₂ := hyz
  have htV : Subgroup.zpowers ((MulEquiv.toMonoidHom (MulAut.conj y)) t) ≤ V := by
    rw [congrArg Subgroup.zpowers hyt']
    exact Subgroup.zpowers_le.mpr (V.mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers P.z₂)))
  have hzV : Subgroup.zpowers ((MulEquiv.toMonoidHom (MulAut.conj y)) P.z₂) ≤ V := by
    rw [congrArg Subgroup.zpowers hyz']
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers P.z₂))
  have hVmap : V.map (MulAut.conj y).toMonoidHom ≤ V := by
    rw [show V = Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂ from rfl,
      Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le htV hzV
  have hys : ∀ s ∈ S₁, y * s * y⁻¹ = s := by
    intro s hs
    rw [show y * s = s * y from (𝔖.decomp.comm hs hyS₂).symm]
    group
  have hmap_le : Zstar.map (MulAut.conj y).toMonoidHom ≤ Zstar := by
    rintro _ ⟨z, hz, rfl⟩
    have hzA : z ∈ S₁ ⊔ V := by
      simpa [hA] using hZstar_le_A hz
    obtain ⟨s, hs, v, hv, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcommS₁V)).mp hzA
    have hyv : y * v * y⁻¹ ∈ V := hVmap ⟨v, hv, rfl⟩
    have hsZ : s ∈ Zstar := by
      have hsv : s = (s * v) * v⁻¹ := by group
      rw [hsv]
      exact Zstar.mul_mem hz (Zstar.inv_mem (hVZ hv))
    have hys' : y * s = s * y := by
      have h := hys s hs
      calc y * s = (y * s * y⁻¹) * y := by group
        _ = s * y := by rw [h]
    have hEq : (MulEquiv.toMonoidHom (MulAut.conj y)) (s * v) =
        s * (y * v * y⁻¹) := by
      change y * (s * v) * y⁻¹ = s * (y * v * y⁻¹)
      calc y * (s * v) * y⁻¹ = (y * s) * v * y⁻¹ := by group
        _ = (s * y) * v * y⁻¹ := by rw [hys']
        _ = s * (y * v * y⁻¹) := by group
    rw [hEq]
    exact Zstar.mul_mem hsZ (hVZ hyv)
  have hmap_eq : Zstar.map (MulAut.conj y).toMonoidHom = Zstar := by
    apply eq_of_le_of_card_ge hmap_le
    rw [Subgroup.card_map_of_injective (K := Zstar) (f := (MulAut.conj y).toMonoidHom)
      (MulAut.conj y).injective]
  have hyN : y ∈ Subgroup.normalizer (Zstar : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap_eq
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
    (𝔖.decomp.isDih₂.isPGroup).to_le (Subgroup.zpowers_le.mpr hyS₂)
  have hyC := two_element_normalizer_centralizes hSstarSylow hZstar_center hyN hy2
  have hcy : y * t = t * y :=
    (Subgroup.mem_centralizer_iff.mp hyC t htZstar).symm
  have hthis : y * t * y⁻¹ = t := by rw [hcy]; group
  rw [hyt] at hthis
  have hz₁ : P.z₂ = 1 := by
    have h := congrArg (fun s => t⁻¹ * s) hthis
    simpa [mul_assoc] using h
  exact z₂_ne_one P hz₁

private lemma exists_eps_of_mem (𝔖 : Sec3Setting G) (P : PairData 𝔖) {t w : G}
    (ht : t ∈ 𝔖.S₂) (htord : orderOf t = 2)
    (hwA : w ∈ 𝔖.S₁ ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂))
    (hwZ : w ∉ 𝔖.S₁ ⊔ Subgroup.zpowers P.z₂) :
    ∃ ε ∈ 𝔖.S₁, w = t * ε ∨ w = t * P.z₂ * ε := by
  classical
  have hcommS₁V : ∀ a ∈ 𝔖.S₁, ∀ b ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂),
      a * b = b * a := by
    intro a ha b hb
    exact 𝔖.decomp.comm ha ((sup_le (Subgroup.zpowers_le.mpr ht)
      (Subgroup.zpowers_le.mpr P.hz)) hb)
  obtain ⟨s, hsS₁, v, hvV, rfl⟩ :=
    (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcommS₁V)).mp hwA
  have hcommV : ∀ a ∈ Subgroup.zpowers t, ∀ b ∈ Subgroup.zpowers P.z₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hi, ← hj]
    exact ((show Commute t P.z₂ from P.hzc t ht).zpow_zpow i j).eq
  obtain ⟨u, hu, r, hr, rfl⟩ :=
    (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcommV)).mp hvV
  rcases zpowers_two_eq htord hu with hu1 | hu1
  · rcases zpowers_two_eq (orderOf_z₂ P) hr with hr1 | hr1
    · exfalso
      apply hwZ
      rw [hu1, hr1, mul_one, mul_one]
      exact Subgroup.mem_sup_left hsS₁
    · exfalso
      apply hwZ
      rw [hu1, hr1, one_mul]
      exact (𝔖.S₁ ⊔ Subgroup.zpowers P.z₂).mul_mem
        (Subgroup.mem_sup_left hsS₁) (Subgroup.mem_sup_right (Subgroup.mem_zpowers P.z₂))
  · rcases zpowers_two_eq (orderOf_z₂ P) hr with hr1 | hr1
    · refine ⟨s, hsS₁, Or.inl ?_⟩
      rw [hu1, hr1, mul_one]
      exact 𝔖.decomp.comm hsS₁ ht
    · refine ⟨s, hsS₁, Or.inr ?_⟩
      rw [hu1, hr1]
      calc s * (t * P.z₂) = (s * t) * P.z₂ := by group
        _ = (t * s) * P.z₂ := by rw [𝔖.decomp.comm hsS₁ ht]
        _ = t * (s * P.z₂) := by group
        _ = t * (P.z₂ * s) := by rw [𝔖.decomp.comm hsS₁ P.hz]
        _ = t * P.z₂ * s := by group

private lemma isConj_of_good_conj (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) (P : PairData 𝔖)
    {t : G} (ht : t ∈ 𝔖.S₂) (htord : orderOf t = 2)
    (hfour : IsFourIn 𝔖.S₂ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂))
    {y : G} (hyS₂ : y ∈ 𝔖.S₂) (hyt : y * t * y⁻¹ = t * P.z₂)
    (hyz : y * P.z₂ * y⁻¹ = P.z₂) :
    ∃ ε ∈ 𝔖.S₁, IsConj P.z₂ (t * ε) := by
  classical
  let A : Subgroup G := 𝔖.S₁ ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers P.z₂)
  let Z : Subgroup G := 𝔖.S₁ ⊔ Subgroup.zpowers P.z₂
  obtain ⟨g, v, hg, hvZ, -, hAfix, hAfix'⟩ := exists_good_conj 𝔖 h₁ P ht htord hfour
  have hz₂A : P.z₂ ∈ A :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers P.z₂))
  have hz₂gA : g * P.z₂ * g⁻¹ ∈ A := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hz₂A
    rw [hAfix] at h
    simpa [MulAut.conj_apply] using h
  have hz₂gZ : g * P.z₂ * g⁻¹ ∉ Z := by
    intro hZ
    have hnot := z₂_not_mem_Zstar 𝔖 h₁ P ht A rfl hg hvZ hAfix' hyS₂ hyt hyz
    apply hnot
    refine Subgroup.mem_map.mpr ⟨g * P.z₂ * g⁻¹, hZ, ?_⟩
    change g⁻¹ * (g * P.z₂ * g⁻¹) * (g⁻¹)⁻¹ = P.z₂
    group
  obtain ⟨ε, hε, hw | hw⟩ := exists_eps_of_mem 𝔖 P ht htord hz₂gA hz₂gZ
  · exact ⟨ε, hε, by rw [← hw]; exact isConj_iff.mpr ⟨g, rfl⟩⟩
  · refine ⟨ε, hε, ?_⟩
    have hconj_w : IsConj P.z₂ (t * P.z₂ * ε) := by
      rw [← hw]
      exact isConj_iff.mpr ⟨g, rfl⟩
    have hyε : y * ε * y⁻¹ = ε := by
      have h := Subgroup.mem_centralizer_iff.mp (𝔖.decomp.commute hyS₂) ε hε
      rw [← h]
      group
    have hyw : y * (t * P.z₂ * ε) * y⁻¹ = t * ε := by
      calc y * (t * P.z₂ * ε) * y⁻¹
          = (y * t * y⁻¹) * (y * P.z₂ * y⁻¹) * (y * ε * y⁻¹) := by group
        _ = (t * P.z₂) * P.z₂ * ε := by rw [hyt, hyz, hyε]
        _ = t * (P.z₂ * P.z₂) * ε := by group
        _ = t * ε := by rw [P.hz2]; group
    exact hconj_w.trans (isConj_iff.mpr ⟨y, hyw⟩)

theorem lemma_3_3 (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) :
    ∃ S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) 𝔖.S₁ S₂' ∧
      ∀ x ∈ S₂', ∀ y ∈ S₂', orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  classical
  obtain ⟨P⟩ := exists_pairData 𝔖
  haveI hKF : IsKleinFour ↥𝔖.S₁ := h₁
  have hcomm₁ : ∀ a ∈ 𝔖.S₁, ∀ b ∈ 𝔖.S₁, a * b = b * a := by
    intro a ha b hb
    letI : IsMulCommutative ↥𝔖.S₁ := IsKleinFour.isMulCommutative
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
      (⟨a, ha⟩ : ↥𝔖.S₁) ⟨b, hb⟩)
  have hsq : ∀ a ∈ 𝔖.S₁, a * a = 1 := by
    intro a ha
    have h := Subgroup.pow_exponent_eq_one (H := 𝔖.S₁) ha
    rw [IsKleinFour.exponent_two (G := ↥𝔖.S₁)] at h
    simpa [pow_two] using h
  obtain ⟨y, hyS₂, hyc, hyd, hyz⟩ := exists_conj_c_z₂ 𝔖 P
  obtain ⟨ε₁, hε₁, hconj₁⟩ := isConj_of_good_conj 𝔖 h₁ P P.hc (orderOf_c P)
    (isFourIn_sup_t_z 𝔖 P P.hc P.hce) hyS₂ hyc hyz
  obtain ⟨ε₂, hε₂, hconj₂⟩ := isConj_of_good_conj 𝔖 h₁ P P.hd (orderOf_d P)
    (isFourIn_sup_t_z 𝔖 P P.hd P.hde) hyS₂ hyd hyz
  obtain ⟨U, hdU, ⟨eU⟩, hU⟩ :=
    dd_corrected_complement_right 𝔖.decomp P.hc P.hd P.hc2 P.hd2 P.hgen hε₁ hε₂
      (fun e he => hcomm₁ e he ε₁ hε₁) (fun e he => hcomm₁ e he ε₂ hε₂)
      (hsq ε₁ hε₁) (hsq ε₂ hε₂)
  refine ⟨U, hdU, ?_⟩
  have hone_mem : ∀ z : G, z ∈ Subgroup.centralizer ({(1 : G)} : Set G) := by
    intro z
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    simp
  have hconj₁' : ConjIn (Subgroup.centralizer ({(1 : G)} : Set G)) (P.c * ε₁) P.z₂ := by
    obtain ⟨z, hz⟩ := isConj_iff.mp hconj₁.symm
    exact ⟨z, hone_mem z, hz⟩
  have hconj₂' : ConjIn (Subgroup.centralizer ({(1 : G)} : Set G)) (P.d * ε₂) P.z₂ := by
    obtain ⟨z, hz⟩ := isConj_iff.mp hconj₂.symm
    exact ⟨z, hone_mem z, hz⟩
  have hY_comm : 𝔖.S₁ ≤ Subgroup.centralizer (𝔖.S₂ : Set G) :=
    Subgroup.le_centralizer_iff.mp 𝔖.decomp.commute
  have hcore := corrected_factor_core (S := (𝔖.S : Subgroup G)) (X := 𝔖.S₂)
    (Y := 𝔖.S₁) (W := U) 𝔖.decomp.dih₂ P.ha P.hc P.hd P.hc2 P.hd2 P.hgen P.hz P.hz2
    (z₂_ne_one P) (center_S₂ 𝔖 P) (z₂_eq_cd_pow 𝔖 P) hY_comm (Subgroup.one_mem 𝔖.S₁)
    hε₁ hε₂ (fun e he => hcomm₁ e he ε₁ hε₁) (fun e he => hcomm₁ e he ε₂ hε₂)
    (hsq ε₁ hε₁) (hsq ε₂ hε₂) hU ⟨eU⟩ (Subgroup.one_mem _) hconj₁' hconj₂'
  intro x hx y' hy' hx2 hy2
  obtain ⟨z, -, hz⟩ := hcore.2.2 x hx y' hy' hx2 hy2
  exact isConj_iff.mpr ⟨z, hz⟩

end Sec3Setting

end CFSG.GH72
