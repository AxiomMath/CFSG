module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs
import CFSG.LieType.CentralExt.CoprimeLift
import CFSG.GroupTheory.CoprimeNormalizerSup
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

private theorem mem_sup_of_commute {G : Type*} [Group G] {H L : Subgroup G}
    (hc : ∀ h ∈ H, ∀ l ∈ L, h * l = l * h) {x : G} (hx : x ∈ H ⊔ L) :
    ∃ h ∈ H, ∃ l ∈ L, x = h * l := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, L.one_mem, by simp⟩
      · exact ⟨1, H.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, H.one_mem, 1, L.one_mem, by simp⟩
  | mul a b ha hb iha ihb =>
      obtain ⟨h1, hh1, l1, hl1, rfl⟩ := iha
      obtain ⟨h2, hh2, l2, hl2, rfl⟩ := ihb
      refine ⟨h1 * h2, H.mul_mem hh1 hh2, l1 * l2, L.mul_mem hl1 hl2, ?_⟩
      calc (h1 * l1) * (h2 * l2)
          = h1 * (l1 * h2) * l2 := by group
        _ = h1 * (h2 * l1) * l2 := by rw [hc h2 hh2 l1 hl1]
        _ = (h1 * h2) * (l1 * l2) := by group
  | inv a ha iha =>
      obtain ⟨h, hh, l, hl, rfl⟩ := iha
      refine ⟨h⁻¹, H.inv_mem hh, l⁻¹, L.inv_mem hl, ?_⟩
      calc (h * l)⁻¹ = l⁻¹ * h⁻¹ := by group
        _ = h⁻¹ * l⁻¹ := by simpa using congrArg Inv.inv (hc h hh l hl)

theorem iv_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S B K : Subgroup Ω} {x : Ω} (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S))
    (hB : IsElemAbelian p B) (hxB : x ∈ B) (hxC : x ∈ Subgroup.centralizer (S : Set Ω))
    (hBx : B = Subgroup.zpowers x ⊔ B ⊓ S) (hKS : K ≤ S) (hK : CFSG.Open.IsQuasisimple ↥K)
    {B' U : Subgroup (↥S ⧸ Subgroup.center ↥S)} (hB' : IsElemAbelian p B')
    (hle : modCentreImage S B ≤ B') (hne : modCentreImage S B ≠ B')
    (hBK : B' ≤ Subgroup.normalizer (modCentreImage S K : Set (↥S ⧸ Subgroup.center ↥S)))
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hUK : U ≤ modCentreImage S K)
    (hdec : B' = (B' ⊓ modCentreImage S K) ⊔
      (B' ⊓ Subgroup.normalizer (U : Set (↥S ⧸ Subgroup.center ↥S)))) :
    ∃ B₁ U₁ : Subgroup Ω, IsElemAbelian p B₁ ∧ B₁ ≤ S ⊔ B ∧ B ≤ B₁ ∧ B ≠ B₁ ∧ U₁ ≠ ⊥ ∧
      IsPGroup 2 U₁ ∧ U₁ ≤ K ∧
      B₁ = (B₁ ⊓ K) ⊔ (B₁ ⊓ Subgroup.normalizer (U₁ : Set Ω)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup ↥S := Subgroup.center ↥S
  let π : ↥S →* ↥S ⧸ Z := QuotientGroup.mk' Z
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hcen : π.ker ≤ Subgroup.center ↥S := by rw [hker]
  have hC : ¬ p ∣ Nat.card π.ker := by rw [hker]; exact hZ
  let BS : Subgroup ↥S := B.subgroupOf S
  have hmci : modCentreImage S B = BS.map π := rfl
  let KS : Subgroup ↥S := K.subgroupOf S
  let Kbar : Subgroup (↥S ⧸ Z) := KS.map π
  have hB'pg : IsPGroup p B' := hB'.isPGroup
  let Pp : Subgroup ↥S := CFSG.LieType.CentralExt.liftSubgroup p π B'
  have hPp_comap : Pp ≤ B'.comap π :=
    CFSG.LieType.CentralExt.liftSubgroup_le_comap hcen hB'pg
  have hPp_pg : IsPGroup p Pp := CFSG.LieType.CentralExt.liftSubgroup_isPGroup hcen hB'pg
  have hPp_elem : IsElemAbelian p Pp := by
    set e := CFSG.LieType.CentralExt.liftSubgroupEquiv hπsurj hcen hC hB'pg with he
    refine ⟨IsMulCommutative.of_comm (fun a b => e.injective ?_), fun y hy => ?_⟩
    · show e (a * b) = e (b * a)
      rw [map_mul, map_mul]
      exact Subtype.ext (hB'.comm (e a).2 (e b).2)
    · have hpow : (⟨y, hy⟩ : ↥Pp) ^ p = 1 := by
        apply e.injective
        rw [map_pow, map_one]
        exact Subtype.ext (hB'.2 (e ⟨y, hy⟩) (e ⟨y, hy⟩).2)
      simpa using congrArg Subtype.val hpow
  let PpΩ : Subgroup Ω := Pp.map S.subtype
  have hPpΩ_elem : IsElemAbelian p PpΩ := IsElemAbelian.map hPp_elem S.subtype
  have hBS_le_Pp : BS ≤ Pp := by
    intro y hy
    rw [CFSG.LieType.CentralExt.mem_liftSubgroup_iff hcen hB'pg]
    refine ⟨hle (Subgroup.mem_map_of_mem π hy), ?_⟩
    exact CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_pow_eq_one (p := p) (x := y) (n := 1)
      (by
        have h := hB.2 (y : Ω) (Subgroup.mem_subgroupOf.mp hy)
        apply Subtype.ext
        simpa [pow_one] using h)
  let B₁ : Subgroup Ω := Subgroup.zpowers x ⊔ PpΩ
  have hB₁elem : IsElemAbelian p B₁ := by
    refine IsElemAbelian.sup_of_commute (isElemAbelian_zpowers (hB.2 x hxB)) hPpΩ_elem ?_
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hb
    have hxs : (s : Ω) * x = x * (s : Ω) := (Subgroup.mem_centralizer_iff.mp hxC) (s : Ω) s.2
    have hcomm : Commute x (s : Ω) := hxs.symm
    exact (hcomm.zpow_left k).eq
  have hB_le_B₁ : B ≤ B₁ := by
    rw [hBx]
    refine sup_le le_sup_left ?_
    intro y hy
    obtain ⟨hyB, hyS⟩ := Subgroup.mem_inf.mp hy
    have hmem : (⟨y, hyS⟩ : ↥S) ∈ BS := Subgroup.mem_subgroupOf.mpr hyB
    exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem S.subtype (hBS_le_Pp hmem))
  have hB₁_le : B₁ ≤ S ⊔ B := by
    refine sup_le ?_ ?_
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hxB)
    · exact (Subgroup.map_subtype_le Pp).trans le_sup_left
  have hmap_Pp : Pp.map π = B' := by
    apply le_antisymm
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
      exact hPp_comap hs
    · intro y hy
      obtain ⟨s, hs⟩ :=
        (CFSG.LieType.CentralExt.liftSubgroupEquiv hπsurj hcen hC hB'pg).surjective ⟨y, hy⟩
      have hys : y = π (s : ↥S) := (congrArg Subtype.val hs).symm
      rw [hys]
      exact Subgroup.mem_map_of_mem π s.2
  have hB_ne_B₁ : B ≠ B₁ := by
    intro heq
    apply hne
    refine le_antisymm hle ?_
    rw [← hmap_Pp]
    intro y hy
    obtain ⟨s, hs, hys⟩ := Subgroup.mem_map.mp hy
    have hsB : s ∈ BS := by
      apply Subgroup.mem_subgroupOf.mpr
      have : (s : Ω) ∈ B₁ :=
        Subgroup.mem_sup_right (Subgroup.mem_map_of_mem S.subtype hs)
      rwa [← heq] at this
    rw [← hys]
    exact Subgroup.mem_map_of_mem π hsB
  let H : Subgroup ↥S := (KS.map π).comap π
  have hH_eq : H = KS ⊔ Z := by
    show (KS.map π).comap π = KS ⊔ Z
    rw [Subgroup.comap_map_eq, hker]
  have hKSH : KS ≤ H := Subgroup.le_comap_map π KS
  haveI hKperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hK.1
  haveI hKSperf : Group.IsPerfect ↥KS :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKS).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKS).symm.surjective
  have hKS_perfect : ⁅KS, KS⁆ = KS := Subgroup.commutator_eq_self
  have hHK : ⁅H, H⁆ = KS := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro y hy z hz
      rw [hH_eq] at hy hz
      obtain ⟨k1, hk1, z1, hz1, rfl⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := KS) (t := Z)).mp hy
      obtain ⟨k2, hk2, z2, hz2, rfl⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := KS) (t := Z)).mp hz
      have hz1c : ∀ g : ↥S, z1 * g = g * z1 :=
        fun g => (Subgroup.mem_center_iff.mp hz1 g).symm
      have hz2c : ∀ g : ↥S, z2 * g = g * z2 :=
        fun g => (Subgroup.mem_center_iff.mp hz2 g).symm
      have h1 : ⁅k1, z2⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hz2c k1).symm
      have h2 : ⁅z1, k2⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hz1c k2)
      have h3 : ⁅z1, z2⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hz1c z2)
      have hmem : ⁅k1, k2⁆ ∈ KS := by
        rw [← hKS_perfect]
        exact Subgroup.commutator_mem_commutator hk1 hk2
      have heq : ⁅k1 * z1, k2 * z2⁆ = ⁅k1, k2⁆ := by
        rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_mul_left_eq_conj_mul,
          commutatorElement_mul_left_eq_conj_mul, h1, h2, h3]
        group
      rwa [heq]
    · rw [← hKS_perfect]
      exact Subgroup.commutator_mono hKSH hKSH
  let V : Subgroup ↥S := CFSG.LieType.CentralExt.liftSubgroup 2 π U
  have hVmem : ∀ w : ↥S, w ∈ V ↔ π w ∈ U ∧ ∃ n, orderOf w = 2 ^ n :=
    fun w => CFSG.LieType.CentralExt.mem_liftSubgroup_iff hcen hU2
  let U₁S : Subgroup ↥S := V ⊓ KS
  let U₁ : Subgroup Ω := U₁S.map S.subtype
  have hKmap : KS.map S.subtype = K := by
    show (K.subgroupOf S).map S.subtype = K
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKS]
  have hU₁S_2 : IsPGroup 2 U₁S :=
    (CFSG.LieType.CentralExt.liftSubgroup_isPGroup hcen hU2).to_inf_left
  have hU₁_2 : IsPGroup 2 U₁ := hU₁S_2.map S.subtype
  have hU₁_le_K : U₁ ≤ K := by
    change (V ⊓ KS).map S.subtype ≤ K
    rw [← hKmap]
    exact Subgroup.map_mono inf_le_right
  have hU₁_le_S : U₁ ≤ S := Subgroup.map_subtype_le U₁S
  have hU₁_ne : U₁ ≠ ⊥ := by
    obtain ⟨u, hu_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
    have huK : (u : ↥S ⧸ Z) ∈ Kbar := hUK u.2
    obtain ⟨k0, hk0, hk0eq⟩ := Subgroup.mem_map.mp huK
    have hk0R : k0 ∈ KS ⊓ U.comap π := by
      refine ⟨hk0, ?_⟩
      change π k0 ∈ U
      rw [hk0eq]
      exact u.2
    obtain ⟨j, hj⟩ := hU2.exists_orderOf_eq_pow u
    have hj1 : 1 ≤ j := by
      by_contra hlt
      have hj0 : j = 0 := by omega
      exact hu_ne (orderOf_eq_one_iff.mp (by rw [hj, hj0, pow_zero]))
    have h2u : 2 ∣ orderOf u := by
      rw [hj]
      exact pow_dvd_pow 2 hj1
    have hdvd_u : orderOf u ∣ orderOf k0 := by
      rw [← Subgroup.orderOf_coe u, ← hk0eq]
      exact orderOf_map_dvd π k0
    have h2k0 : 2 ∣ orderOf k0 := h2u.trans hdvd_u
    have h2R : 2 ∣ Nat.card ↥(KS ⊓ U.comap π) := by
      have h1 : orderOf k0 ∣ Nat.card ↥(KS ⊓ U.comap π) := by
        have h := orderOf_dvd_natCard (⟨k0, hk0R⟩ : ↥(KS ⊓ U.comap π))
        rwa [Subgroup.orderOf_mk k0 hk0R] at h
      exact h2k0.trans h1
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2R
    have hyV : (y : ↥S) ∈ V := by
      rw [hVmem]
      refine ⟨show π (y : ↥S) ∈ U from y.2.2, 1, ?_⟩
      rw [Subgroup.orderOf_coe, hy, pow_one]
    have hyKS : (y : ↥S) ∈ KS := y.2.1
    have hy_ne : y ≠ 1 := by
      intro h
      rw [h] at hy
      simp at hy
    intro hbot
    have hmem : (y : Ω) ∈ U₁ :=
      Subgroup.mem_map_of_mem S.subtype (show (y : ↥S) ∈ U₁S from ⟨hyV, hyKS⟩)
    rw [hbot] at hmem
    exact hy_ne (Subtype.ext (by simpa using hmem))
  have hcKS_of : ∀ c : ↥S, c ∈ Pp → π c ∈ Subgroup.normalizer (Kbar : Set (↥S ⧸ Z)) →
      c ∈ Subgroup.normalizer (KS : Set ↥S) := by
    intro c _ hcN
    have hcH : c ∈ Subgroup.normalizer (H : Set ↥S) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      show y ∈ H ↔ c * y * c⁻¹ ∈ H
      simp only [H, Subgroup.mem_comap]
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hcN) (π y)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hHmap : H.map (MulAut.conj c) = H :=
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hcH)
    calc KS.map (MulAut.conj c)
        = (⁅H, H⁆).map (MulAut.conj c) := by rw [hHK]
      _ = ⁅H.map (MulAut.conj c), H.map (MulAut.conj c)⁆ := by
            rw [Subgroup.map_commutator]
      _ = ⁅H, H⁆ := by rw [hHmap]
      _ = KS := hHK
  have hcV_of : ∀ c : ↥S, π c ∈ Subgroup.normalizer (U : Set (↥S ⧸ Z)) →
      c ∈ Subgroup.normalizer (V : Set ↥S) := by
    intro c hcU
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hVmem y, hVmem (c * y * c⁻¹)]
    have hUiff : π y ∈ U ↔ π (c * y * c⁻¹) ∈ U := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hcU) (π y)
    have ho : orderOf (c * y * c⁻¹) = orderOf y :=
      (SemiconjBy.orderOf_eq c (x := y) (y := c * y * c⁻¹)
        (by simp [SemiconjBy, mul_assoc])).symm
    exact and_congr hUiff (exists_congr fun n => by rw [ho])
  have hdecomp : B₁ = (B₁ ⊓ K) ⊔ (B₁ ⊓ Subgroup.normalizer (U₁ : Set Ω)) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨a, ha, s, hs, rfl⟩ :=
        mem_sup_of_commute (fun a ha b hb =>
          hB₁elem.comm (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)) hy
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hs
      have hs'B' : π s' ∈ B' := hPp_comap hs'
      have hs'dec : π s' ∈ (B' ⊓ modCentreImage S K) ⊔
          (B' ⊓ Subgroup.normalizer (U : Set (↥S ⧸ Z))) := by
        rwa [hdec] at hs'B'
      obtain ⟨mb, hmb, cb, hcb, hs_eq⟩ :=
        mem_sup_of_commute (fun a ha b hb =>
          hB'.comm (Subgroup.mem_inf.mp ha).1 (Subgroup.mem_inf.mp hb).1) hs'dec
      rw [Subgroup.mem_inf] at hmb hcb
      obtain ⟨k0, hk0, hk0eq⟩ := Subgroup.mem_map.mp hmb.2
      let m : ↥S := CFSG.LieType.CentralExt.pLift p π mb
      let cc : ↥S := CFSG.LieType.CentralExt.pLift p π cb
      have hmb_p : ∃ n, orderOf mb = p ^ n :=
        CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_mem hB'pg ⟨mb, hmb.1⟩
      have hcb_p : ∃ n, orderOf cb = p ^ n :=
        CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_mem hB'pg ⟨cb, hcb.1⟩
      have hm_map : π m = mb := CFSG.LieType.CentralExt.map_pLift hπsurj hC hmb_p
      have hcc_map : π cc = cb := CFSG.LieType.CentralExt.map_pLift hπsurj hC hcb_p
      have hm_mem : m ∈ Pp :=
        CFSG.LieType.CentralExt.pLift_mem_liftSubgroup hπsurj hcen hC hB'pg hmb.1
      have hcc_mem : cc ∈ Pp :=
        CFSG.LieType.CentralExt.pLift_mem_liftSubgroup hπsurj hcen hC hB'pg hcb.1
      have hs'_eq : s' = m * cc := by
        apply CFSG.LieType.CentralExt.eq_of_pElement hcen hC
        · rw [map_mul, hm_map, hcc_map, ← hs_eq]
        · exact ((CFSG.LieType.CentralExt.mem_liftSubgroup_iff hcen hB'pg).1 hs').2
        · exact ((CFSG.LieType.CentralExt.mem_liftSubgroup_iff hcen hB'pg).1
            (Pp.mul_mem hm_mem hcc_mem)).2
      have hm_in_sup : m ∈ KS ⊔ Z := by
        have hz : k0⁻¹ * m ∈ Z := by
          rw [← hker]
          exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hm_map, hk0eq, inv_mul_cancel])
        have := Subgroup.mul_mem_sup hk0 hz
        rwa [mul_inv_cancel_left] at this
      obtain ⟨mp, hmp⟩ := ((CFSG.LieType.CentralExt.mem_liftSubgroup_iff hcen hB'pg).1 hm_mem).2
      have hm_zpow : IsPGroup p (Subgroup.zpowers m) := by
        apply IsPGroup.of_card (n := mp)
        rw [Nat.card_zpowers, hmp]
      have hm_KS : m ∈ KS :=
        CFSG.GroupTheory.le_of_le_sup_of_isPGroup_of_not_dvd_card hp
          (Subgroup.center_le_normalizer (KS : Set ↥S)) hm_zpow
          (Subgroup.zpowers_le.mpr hm_in_sup) (show ¬ p ∣ Nat.card Z from hZ)
          (Subgroup.mem_zpowers m)
      have hm_K : (m : Ω) ∈ K := Subgroup.mem_subgroupOf.mp hm_KS
      have hccN_Kbar : π cc ∈ Subgroup.normalizer (Kbar : Set (↥S ⧸ Z)) := by
        rw [hcc_map]
        exact hBK hcb.1
      have hccKS : cc ∈ Subgroup.normalizer (KS : Set ↥S) := hcKS_of cc hcc_mem hccN_Kbar
      have hccV : cc ∈ Subgroup.normalizer (V : Set ↥S) :=
        hcV_of cc (by rw [hcc_map]; exact hcb.2)
      have hccU₁S : cc ∈ Subgroup.normalizer (U₁S : Set ↥S) := by
        rw [Subgroup.mem_normalizer_iff]
        intro w
        rw [Subgroup.mem_inf, Subgroup.mem_inf]
        exact and_congr ((Subgroup.mem_normalizer_iff.mp hccV w))
          ((Subgroup.mem_normalizer_iff.mp hccKS w))
      have hccU₁ : (cc : Ω) ∈ Subgroup.normalizer (U₁ : Set Ω) :=
        Subgroup.le_normalizer_map (H := U₁S) S.subtype
          (Subgroup.mem_map_of_mem S.subtype hccU₁S)
      have hxU₁ : x ∈ Subgroup.normalizer (U₁ : Set Ω) :=
        Subgroup.centralizer_le_normalizer (U₁ : Set Ω)
          (Subgroup.centralizer_le hU₁_le_S hxC)
      have hxzN : x ^ z ∈ Subgroup.normalizer (U₁ : Set Ω) :=
        Subgroup.zpowers_le.mpr hxU₁ (Subgroup.zpow_mem_zpowers x z)
      have hmB₁ : (m : Ω) ∈ B₁ :=
        Subgroup.mem_sup_right (Subgroup.mem_map_of_mem S.subtype hm_mem)
      have hccB₁ : (cc : Ω) ∈ B₁ :=
        Subgroup.mem_sup_right (Subgroup.mem_map_of_mem S.subtype hcc_mem)
      have hxzB₁ : x ^ z ∈ B₁ :=
        Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
          (Subgroup.zpow_mem_zpowers x z)
      have hxz_m : x ^ z * (m : Ω) = (m : Ω) * x ^ z := by
        have hxm : x * (m : Ω) = (m : Ω) * x :=
          ((Subgroup.mem_centralizer_iff.mp hxC) (m : Ω) m.2).symm
        exact (show Commute x (m : Ω) from hxm).zpow_left z |>.eq
      rw [hs'_eq]
      change x ^ z * ((m : Ω) * (cc : Ω)) ∈
        (B₁ ⊓ K) ⊔ (B₁ ⊓ Subgroup.normalizer (U₁ : Set Ω))
      rw [← mul_assoc, hxz_m, mul_assoc]
      exact Subgroup.mul_mem_sup ⟨hmB₁, hm_K⟩
        ⟨B₁.mul_mem hxzB₁ hccB₁,
          (Subgroup.normalizer (U₁ : Set Ω)).mul_mem hxzN hccU₁⟩
    · exact sup_le inf_le_left inf_le_left
  exact ⟨B₁, U₁, hB₁elem, hB₁_le, hB_le_B₁, hB_ne_B₁, hU₁_ne, hU₁_2, hU₁_le_K, hdecomp⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
