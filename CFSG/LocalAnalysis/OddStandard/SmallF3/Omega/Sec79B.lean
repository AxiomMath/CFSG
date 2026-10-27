module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79Fr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec79_t_mem_A [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) : t ∈ ASub S B := by
  rw [ASub, omega1]
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · refine ⟨hc.ctx.t_mem_S, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hc.ctx.sylow.1 (hc.normalE16.1 hb).1)
  · rw [← hc.ctx.involution]
    exact pow_orderOf_eq_one t

theorem sec79_B_le_A [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) : B ≤ ASub S B := by
  haveI : IsMulCommutative B := hc.normalE16.2.1.1.1
  intro b hb
  rw [ASub, omega1]
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · exact ⟨(hc.normalE16.1 hb).1,
      Subgroup.mem_centralizer_iff.mpr fun b' hb' => setLike_mul_comm hb' hb⟩
  · simpa [pow_two] using CFSG.Open.IsElemAbelian.mul_self_eq_one hc.normalE16.2.1.1 hb

theorem sec79_R_sylow [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) {t : G}
    {L S : Subgroup G} {z : G} (hctx : Sec7Ctx G t L S z) :
    IsSylow2Of (zpowers t) (centralizer ({t} : Set G) ⊓ centralizer (L : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := centralizer ({t} : Set G)
  let R : Subgroup G := H ⊓ centralizer (L : Set G)
  change IsSylow2Of (Subgroup.zpowers t) R
  have htR : t ∈ R :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hctx.t_mem_centralizer⟩
  have hztR : Subgroup.zpowers t ≤ R := Subgroup.zpowers_le.mpr htR
  have hcard : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers, hctx.involution]
  have hzt2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  obtain ⟨Q, hQ⟩ := (hzt2.of_equiv (Subgroup.subgroupOfEquivOfLe hztR).symm).exists_le_sylow
  let Q' : Subgroup G := (Q : Subgroup ↥R).map R.subtype
  have hQ'sylow : IsSylow2Of Q' R := isSylow2Of_map_sylow Q
  have hztQ' : Subgroup.zpowers t ≤ Q' := by
    intro y hy
    exact Subgroup.mem_map_of_mem R.subtype
      (hQ (Subgroup.mem_subgroupOf (h := ⟨y, hztR hy⟩) |>.mpr hy))
  have hQ'2 : IsPGroup 2 Q' := hQ'sylow.2.1
  have hQ'H : Q' ≤ H := hQ'sylow.1.trans inf_le_left
  have hQ'Y : Q' ≤ Subgroup.zpowers t := by
    intro q hq
    obtain ⟨d, hdH, hdconj⟩ := exists_conj_le_of_isSylow2Of hctx.sylow hQ'2 hQ'H
    have hdqS : d * q * d⁻¹ ∈ S := hdconj q hq
    have hqR : q ∈ R := hQ'sylow.1 hq
    have hdn : d ∈ normalizer (L : Set G) := hctx.cent_le_normalizer h36 d hdH
    have hdqC : d * q * d⁻¹ ∈ centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      have hdl : d⁻¹ * l * d ∈ L := (Subgroup.mem_normalizer_iff''.mp hdn l).mp hl
      have hcl := Subgroup.mem_centralizer_iff.mp hqR.2 (d⁻¹ * l * d) hdl
      calc l * (d * q * d⁻¹) = d * ((d⁻¹ * l * d) * q) * d⁻¹ := by group
        _ = d * (q * (d⁻¹ * l * d)) * d⁻¹ := by rw [hcl]
        _ = (d * q * d⁻¹) * l := by group
    have hdqzt : d * q * d⁻¹ ∈ Subgroup.zpowers t := by
      rw [h76 G t L S z hctx]
      exact ⟨hdqS, hdqC⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdqzt
    have hdt : Commute d t := Subgroup.mem_centralizer_singleton_iff.mp hdH
    have hdtinv : Commute d⁻¹ t := hdt.inv_left
    have hqeq : q = d⁻¹ * t ^ k * d := by
      calc q = d⁻¹ * (d * q * d⁻¹) * d := by group
        _ = d⁻¹ * t ^ k * d := by rw [← hk]
    rw [hqeq]
    have hconj : d⁻¹ * t ^ k * d = t ^ k := by
      calc d⁻¹ * t ^ k * d = (d⁻¹ * t ^ k) * d := by group
        _ = (t ^ k * d⁻¹) * d := by rw [(hdtinv.zpow_right k).eq]
        _ = t ^ k := by group
    rw [hconj]
    exact Subgroup.zpow_mem_zpowers t k
  have hQ'eq : Q' = Subgroup.zpowers t := le_antisymm hQ'Y hztQ'
  simpa [hQ'eq] using hQ'sylow

theorem sec79_oddCore_cent_A_le_R [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    oddCoreIn (centralizer (ASub S B : Set G)) ≤
      centralizer ({t} : Set G) ⊓ centralizer (L : Set G) := by
  classical
  intro x hx
  have hxC : x ∈ centralizer (ASub S B : Set G) := (oddCoreIn_normal _).1 hx
  have hxodd : Odd (orderOf x) := odd_orderOf_of_mem_oddCoreIn hx
  have hxA : ∀ a ∈ ASub S B, a * x = x * a := Subgroup.mem_centralizer_iff.mp hxC
  have htA : t ∈ ASub S B := sec79_t_mem_A hc
  have hxH : x ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hxA t htA).symm
  have hxN : x ∈ normalizer (L : Set G) := hc.ctx.cent_le_normalizer h36 x hxH
  have hinner : InnerOn L x := hP.out_two G L hc.ctx.isOm6P x hxN hxodd
  obtain ⟨l, hlL, c, hcC, hxlc⟩ := innerOn_decompose hinner
  have hBl : ∀ b ∈ B, b * l = l * b := by
    intro b hb
    have hbA : b ∈ ASub S B := sec79_B_le_A hc hb
    have hbL : b ∈ L := (hc.normalE16.1 hb).2
    have hbxc : b * (l * c) = (l * c) * b := by
      rw [← hxlc]
      exact hxA b hbA
    have hbc : b * c = c * b := Subgroup.mem_centralizer_iff.mp hcC b hbL
    have : (b * l) * c = (l * b) * c := by
      calc (b * l) * c = b * (l * c) := by group
        _ = (l * c) * b := hbxc
        _ = l * (c * b) := by group
        _ = l * (b * c) := by rw [hbc]
        _ = (l * b) * c := by group
    exact mul_right_cancel this
  have hlB : l ∈ B := by
    have hAutB :=
      hP.aut_B G L hc.ctx.isOm6P (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B hc.normalE16
    have hlLB : l ∈ L ⊓ centralizer (B : Set G) :=
      ⟨hlL, Subgroup.mem_centralizer_iff.mpr hBl⟩
    rwa [hAutB.2.1] at hlLB
  have hl2 : l * l = 1 :=
    CFSG.Open.IsElemAbelian.mul_self_eq_one hc.normalE16.2.1.1 hlB
  have hlc : Commute l c := Subgroup.mem_centralizer_iff.mp hcC l hlL
  have h1 : l ^ orderOf x * c ^ orderOf x = 1 := by
    rw [← hlc.mul_pow (orderOf x), ← hxlc, pow_orderOf_eq_one]
  obtain ⟨m, hm⟩ := hxodd
  have hl2' : l ^ 2 = 1 := by rw [pow_two]; exact hl2
  have hln : l ^ orderOf x = l := by
    rw [hm, pow_succ, pow_mul, hl2', one_pow, one_mul]
  have hl_eq : l = (c ^ orderOf x)⁻¹ := by
    have hmul : l * c ^ orderOf x = 1 := by rw [← hln]; exact h1
    exact eq_inv_of_mul_eq_one_left hmul
  have hlcent : l ∈ centralizer (L : Set G) := by
    rw [hl_eq]
    exact (centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).pow_mem hcC _)
  have hlbot : l = 1 := by
    have hinf : L ⊓ centralizer (L : Set G) ≤ centerIn L := fun y hy =>
      Subgroup.mem_map.mpr ⟨⟨y, hy.1⟩,
        Subgroup.mem_center_iff.mpr fun z =>
          Subtype.ext (Subgroup.mem_centralizer_iff.mp hy.2 z z.2), rfl⟩
    have hmem : l ∈ centerIn L := hinf ⟨hlL, hlcent⟩
    rw [hP.center_triv G L hc.ctx.isOm6P] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hxc : x = c := by rw [hxlc, hlbot, one_mul]
  exact ⟨hxH, by rw [hxc]; exact hcC⟩

theorem sec79_oddCore_cent_A_le_cent_t [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76)
    (hP : Asc82Tab6P) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    oddCoreIn (centralizer (ASub S B : Set G)) ≤ oddCoreIn (centralizer ({t} : Set G)) := by
  classical
  intro x hx
  have hxR : x ∈ centralizer ({t} : Set G) ⊓ centralizer (L : Set G) :=
    sec79_oddCore_cent_A_le_R h36 hP hc hx
  have hxodd : Odd (orderOf x) := odd_orderOf_of_mem_oddCoreIn hx
  have hRnorm : ((centralizer ({t} : Set G) ⊓ centralizer (L : Set G)).subgroupOf
      (centralizer ({t} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro r h hr hh
    refine ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hr.1) (Subgroup.inv_mem _ hh)
    · have hhN : h ∈ normalizer (L : Set G) := hc.ctx.cent_le_normalizer h36 h hh
      exact (Subgroup.normal_subgroupOf_iff (Subgroup.centralizer_le_normalizer (L : Set G))).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer (L : Set G)) r h hr.2 hhN
  have hRsylow : IsSylow2Of (Subgroup.zpowers t)
      (centralizer ({t} : Set G) ⊓ centralizer (L : Set G)) := sec79_R_sylow h36 h76 hc.ctx
  have hcentral : ∀ k ∈ centralizer ({t} : Set G) ⊓ centralizer (L : Set G),
      ∀ z ∈ Subgroup.zpowers t, z * k = k * z := by
    intro k hk z hz
    have hkt : Commute t k := (Subgroup.mem_centralizer_singleton_iff.mp hk.1).symm
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (hkt.zpow_left m).eq
  have hxO : x ∈ oddCoreIn (centralizer ({t} : Set G) ⊓ centralizer (L : Set G)) :=
    (mem_oddCoreIn_iff_of_central_sylow hRsylow hcentral).mpr ⟨hxR, hxodd⟩
  exact oddCoreIn_le_of_normal inf_le_left hRnorm hxO

theorem sec79_oddCore_cent_t_le [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P)
    (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    oddCoreIn (centralizer ({t} : Set G)) ≤ centralizer (ASub S B : Set G) := by
  classical
  let H : Subgroup G := centralizer ({t} : Set G)
  intro x hx
  have hxH : x ∈ H := (oddCoreIn_normal H).1 hx
  have hxN : x ∈ normalizer (L : Set G) := hc.ctx.cent_le_normalizer h36 x hxH
  let N : Subgroup G := L ⊓ oddCoreIn H
  have hNle : N ≤ oddCoreIn H := inf_le_right
  have hNnorm : (N.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro n l' hn hl'
    refine ⟨?_, ?_⟩
    · exact L.mul_mem (L.mul_mem hl' hn.1) (L.inv_mem hl')
    · exact conj_mem_oddCoreIn
        (Subgroup.le_normalizer (H := H) (hc.ctx.le_centralizer hl')) hn.2
  have hNodd : Odd (Nat.card N) :=
    (odd_card_oddCoreIn H).of_dvd_nat (Subgroup.card_dvd_of_le hNle)
  have hNleO : N ≤ oddCoreIn L := le_oddCoreIn_of_normal inf_le_left hNnorm hNodd
  have hoddL_bot : oddCoreIn L = ⊥ := by
    have hOpen : CFSG.Open.IsQuasisimple ↥L :=
      ⟨Group.isPerfect_def.mp hc.ctx.isOm6P.1.1, hc.ctx.isOm6P.1.2.1⟩
    have hodd_le : CFSG.oddCore ↥L ≤ Subgroup.center ↥L :=
      CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple hOpen
    have hle : oddCoreIn L ≤ centerIn L := by
      simpa [oddCoreIn, centerIn, CFSG.inSubgroup] using
        Subgroup.map_mono (f := L.subtype) hodd_le
    rw [hP.center_triv G L hc.ctx.isOm6P] at hle
    exact le_bot_iff.mp hle
  have hxcommL : ∀ l ∈ L, l * x = x * l := by
    intro l hl
    have hkL : x * l * x⁻¹ * l⁻¹ ∈ L := by
      have hxlxL : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxN l).mp hl
      exact L.mul_mem hxlxL (L.inv_mem hl)
    have hxl : l * x⁻¹ * l⁻¹ ∈ oddCoreIn H :=
      conj_mem_oddCoreIn (Subgroup.le_normalizer (H := H) (hc.ctx.le_centralizer hl))
        ((oddCoreIn H).inv_mem hx)
    have hkO : x * l * x⁻¹ * l⁻¹ ∈ oddCoreIn H := by
      have : x * (l * x⁻¹ * l⁻¹) ∈ oddCoreIn H := (oddCoreIn H).mul_mem hx hxl
      simpa [mul_assoc] using this
    have hk1 : x * l * x⁻¹ * l⁻¹ = 1 := by
      have hmem : x * l * x⁻¹ * l⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hoddL_bot]
        exact hNleO ⟨hkL, hkO⟩
      exact Subgroup.mem_bot.mp hmem
    have hxl' : x * l * x⁻¹ = l := by
      have h := congrArg (fun w => w * l) hk1
      calc x * l * x⁻¹ = (x * l * x⁻¹ * l⁻¹) * l := by group
        _ = 1 * l := h
        _ = l := by group
    have : x * l = l * x := by
      calc x * l = (x * l * x⁻¹) * x := by group
        _ = l * x := by rw [hxl']
    exact this.symm
  rw [h78 G t L S z g B hc]
  refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  have hAcent : Subgroup.zpowers t ⊔ B ≤ centralizer ({x} : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hxH).symm
    · intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hxcommL b (hc.normalE16.1 hb).2)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hAcent ha)

theorem sec79_oddCore_M_le_cent_A [Finite G] {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    oddCoreIn (MSub S B) ≤ centralizer (ASub S B : Set G) := by
  classical
  let A : Subgroup G := ASub S B
  let M : Subgroup G := MSub S B
  change oddCoreIn M ≤ centralizer (A : Set G)
  have hAleS : A ≤ S := by
    change omega1 (S ⊓ centralizer (B : Set G)) ≤ S
    rw [omega1]
    exact (Subgroup.closure_le S).mpr fun x hx => hx.1.1
  have hP2 : IsPGroup 2 A := hc.ctx.sylow.2.1.to_le hAleS
  have hAM : A ≤ M := Subgroup.le_normalizer
  have hAn : (A.subgroupOf M).Normal := by
    change (A.subgroupOf (Subgroup.normalizer (A : Set G))).Normal
    infer_instance
  have hOn : ((oddCoreIn M).subgroupOf M).Normal := (oddCoreIn_normal M).2
  have hOodd : Odd (Nat.card (oddCoreIn M)) := odd_card_oddCoreIn M
  have hcomm :=
    commute_of_normal_two_odd hAM (oddCoreIn_normal M).1 hAn hOn hP2 hOodd
  intro o ho
  exact Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha o ho

theorem sec79_cent_A_decomp [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76)
    (hP : Asc82Tab6P) (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G}
    {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    ASub S B ⊔ oddCoreIn (centralizer (ASub S B : Set G)) = centralizer (ASub S B : Set G) := by
  classical
  have hnoalt : S ⊓ centralizer (B : Set G) ≤ ASub S B := sec79_no_alt2 h36 h76 hP h77b h78 hc
  have hAle : ASub S B ≤ S ⊓ centralizer (B : Set G) := by
    rw [ASub, omega1]
    exact (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hAeq : ASub S B = S ⊓ centralizer (B : Set G) := le_antisymm hAle hnoalt
  have hY : IsSylow2Of (S ⊓ centralizer (B : Set G)) (centralizer (ASub S B : Set G)) :=
    sec79_Y_sylow h36 h76 hP h78 hc
  rw [hAeq] at hY ⊢
  exact sup_oddCoreIn_of_central_sylow hY
    (fun k hk z hz => Subgroup.mem_centralizer_iff.mp hk z hz)

theorem asc82Lemma79b_of (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) :
    ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
      Sec7Choice G t L S z g B →
        ASub S B ⊔ oddCoreIn (centralizer ({t} : Set G)) = ASub S B ⊔ oddCoreIn (MSub S B) ∧
          ASub S B ⊔ oddCoreIn (MSub S B) = centralizer (ASub S B : Set G) := by
  intro G _ _ t L S z g B hc
  have hAd : ASub S B ⊔ oddCoreIn (centralizer (ASub S B : Set G)) =
      centralizer (ASub S B : Set G) := sec79_cent_A_decomp h36 h76 hP h77b h78 hc
  have hOAR : oddCoreIn (centralizer (ASub S B : Set G)) ≤
      oddCoreIn (centralizer ({t} : Set G)) := sec79_oddCore_cent_A_le_cent_t h36 h76 hP hc
  have hHO : oddCoreIn (centralizer ({t} : Set G)) ≤ centralizer (ASub S B : Set G) :=
    sec79_oddCore_cent_t_le h36 hP h78 hc
  have hOM : oddCoreIn (MSub S B) ≤ centralizer (ASub S B : Set G) :=
    sec79_oddCore_M_le_cent_A hc
  have hOCM : oddCoreIn (centralizer (ASub S B : Set G)) ≤ oddCoreIn (MSub S B) :=
    oddCoreIn_le_of_normal (Subgroup.centralizer_le_normalizer (ASub S B : Set G))
      (Subgroup.normal_subgroupOf_centralizer_normalizer (ASub S B : Set G))
  have hA_le_C : ASub S B ≤ centralizer (ASub S B : Set G) := by
    have hElem : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers t ⊔ B) := by
      have ht2 : t ^ 2 = 1 := by rw [← hc.ctx.involution]; exact pow_orderOf_eq_one t
      have hzt : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers t) :=
        CFSG.Open.isElemAbelian_zpowers (p := 2) ht2
      have hB : CFSG.Open.IsElemAbelian 2 B := hc.normalE16.2.1.1
      have hcomm : ∀ a ∈ Subgroup.zpowers t, ∀ b ∈ B, a * b = b * a := by
        intro a ha b hb
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        have htb : t * b = b * t :=
          (Subgroup.mem_centralizer_singleton_iff.mp
            (hc.ctx.sylow.1 (hc.normalE16.1 hb).1)).symm
        exact ((show Commute t b from htb).zpow_left k).eq
      exact CFSG.Open.IsElemAbelian.sup_of_commute hzt hB hcomm
    haveI : IsMulCommutative (ASub S B) := (h78 G t L S z g B hc).symm ▸ hElem.1
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun a' ha' => setLike_mul_comm ha' ha
  have hH : ASub S B ⊔ oddCoreIn (centralizer ({t} : Set G)) =
      centralizer (ASub S B : Set G) := by
    apply le_antisymm
    · exact sup_le hA_le_C hHO
    · rw [← hAd]
      exact sup_le le_sup_left (hOAR.trans le_sup_right)
  have hM : ASub S B ⊔ oddCoreIn (MSub S B) = centralizer (ASub S B : Set G) := by
    apply le_antisymm
    · exact sup_le hA_le_C hOM
    · rw [← hAd]
      exact sup_le le_sup_left (hOCM.trans le_sup_right)
  exact ⟨hH.trans hM.symm, hM⟩

end CFSG.OddStandard.SmallF3.Omega
