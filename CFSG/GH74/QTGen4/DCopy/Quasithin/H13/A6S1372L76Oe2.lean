module

public import CFSG.Quasithin.H13.A6S1372L76Oe2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76P4d

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section Config

variable {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
  {K : Subgroup G} (hK : K ∈ cComp H)
  {Kt : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))}
  (hKt : Kt = autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
include hH hK hKt

theorem exists_odd_config_of_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4)
    {g : ↥(Subgroup.normalizer (V : Set G))} (hgX : (g : G) ∈ S.X1375)
    (hg : S.frame.ρ g = swap 0 1 * swap 1 2) :
    ∃ (a : MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (P : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))))
      (v₂ : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))),
      a = A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
        ⟨g, X1375_le_H hH hgX⟩ ∧
      P = ((T ⊓ K).subgroupOf H).map
        (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)) ∧
      v₂ = InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨S.v2, S.v2_mem_UH H⟩ ∧
      (∀ y ∈ Kt, a * y * a⁻¹ ∈ Kt) ∧ P ≤ Kt ∧ IsPGroup 2 ↥P ∧ Odd (P.subgroupOf Kt).index ∧
      (∀ p ∈ P, p v₂ = v₂) ∧ (∀ p ∈ P, p (a v₂) = a v₂ ∨ p (a v₂) = v₂ * a v₂) ∧
      a (a v₂) = v₂ * a v₂ ∧ v₂ ∉ fixV Kt := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hKt
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hXK := X1375_le_normalizer h38 hH hK
  have hgH : (g : G) ∈ H := X1375_le_H hH hgX
  have hgK : (g : G) ∈ Subgroup.normalizer (K : Set G) := hXK hgX
  have hv2U := S.v2_mem_UH H

  have hgv : (g : G) * S.v2 * (g : G)⁻¹ ∈ S.V3 := by
    refine S.mem_pre.2 ⟨S.conj_v2_mem_V g, ?_⟩
    show InW3 ((S.frame.ψ ⟨_, S.conj_v2_mem_V g⟩ : ↥W4) : P6)
    rw [S.psi_conj_v2, hg]
    exact A6L76G.w4_facts.2.2.2.2.2.1
  refine ⟨A6Mod.secAct hHU hHV ⟨g, hgH⟩, ((T ⊓ K).subgroupOf H).map (A6Mod.secAct hHU hHV),
    InternalSec.secMk _ ⟨S.v2, hv2U⟩, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro y hy
    obtain ⟨f, hfK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hy
    refine (A6Mod.mem_autSec_iff hHU hHV hKH).2
      ⟨⟨g, hgH⟩ * f * ⟨g, hgH⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp hgK f).mp hfK
  ·
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : G) ∈ T ⊓ K := ht
    exact (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨t, ht'.2, rfl⟩
  ·
    have h1 : IsPGroup 2 ↥((T ⊓ K).subgroupOf H) := by
      intro x
      have hx := x.2
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨n, hn⟩ := hTs.2.1 ⟨((x : ↥H) : G), hx.1⟩
      exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
    exact h1.map _
  ·
    let κ : ↥K →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
      ((A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH)).codRestrict _
        fun k => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, k.2, rfl⟩
    have hκ : Function.Surjective κ := by
      rintro ⟨ψ, hψ⟩
      obtain ⟨f, hfK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hψ
      exact ⟨⟨f, hfK⟩, rfl⟩
    have heq : (((T ⊓ K).subgroupOf H).map (A6Mod.secAct hHU hHV)).subgroupOf
        (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) =
        ((T ⊓ K).subgroupOf K).map κ := by
      ext y
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨t, ht, hty⟩
        have ht' : (t : G) ∈ T ⊓ K := ht
        exact ⟨⟨t, ht'.2⟩, (ht' : ((⟨t, ht'.2⟩ : ↥K) : G) ∈ T ⊓ K), Subtype.ext hty⟩
      · rintro ⟨k, hk, rfl⟩
        have hk' : (k : G) ∈ T ⊓ K := hk
        exact ⟨Subgroup.inclusion hKH k, (hk' : ((Subgroup.inclusion hKH k : ↥H) : G) ∈ T ⊓ K),
          rfl⟩
    have hsyl := S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hK) hTs
    have hdvd := Subgroup.index_map_dvd ((T ⊓ K).subgroupOf K) hκ
    rw [heq]
    rw [Nat.odd_iff]
    by_contra hev
    apply hsyl.2.2
    exact (Nat.dvd_of_mod_eq_zero (by omega)).trans hdvd
  ·
    rintro _ ⟨t, ht0, rfl⟩
    have ht : (t : G) ∈ T ⊓ K := ht0
    rw [A6Mod.secAct_secMk]
    apply secMk_eq_of_mem_V1
    rw [Setup.rho_apply_coe]
    have htN : (t : G) ∈ Subgroup.normalizer (S.V2 : Set G) := S.T_le_normalizer_V2 ht.1
    have h1 : (t : G) * S.v2 * (t : G)⁻¹ ∈ S.V2 :=
      (Subgroup.mem_normalizer_iff.mp htN _).mp S.v2_mem_V2
    rcases S.mem_V1_or_of_mem_V2 S.v2_mem_V2 S.v2_not_mem_V1 h1 with h2 | h2
    · exfalso
      apply S.v2_not_mem_V1
      have h3 := (Subgroup.mem_normalizer_iff.mp (S.T_le_NV1 (T.inv_mem ht.1)) _).mp h2
      have e : (t : G)⁻¹ * ((t : G) * S.v2 * (t : G)⁻¹) * (t : G)⁻¹⁻¹ = S.v2 := by group
      rwa [e] at h3
    · exact h2
  ·
    rintro _ ⟨t, ht0, rfl⟩
    have ht : (t : G) ∈ T ⊓ K := ht0
    rw [A6Mod.secAct_secMk, A6Mod.secAct_secMk]
    have hw := comm_T_V3 ht.1 hgv
    rcases S.mem_V1_or_of_mem_V2 S.v2_mem_V2 S.v2_not_mem_V1 hw with h2 | h2
    · left
      apply secMk_eq_of_mem_V1
      rw [Setup.rho_apply_coe, Setup.rho_apply_coe]
      exact h2
    · right
      rw [← map_mul]
      apply secMk_eq_of_mem_V1
      rw [Setup.rho_apply_coe, Subgroup.coe_mul, Setup.rho_apply_coe]
      have e : (t : G) * ((g : G) * S.v2 * (g : G)⁻¹) * (t : G)⁻¹ *
          (S.v2 * ((g : G) * S.v2 * (g : G)⁻¹))⁻¹ =
          (t : G) * ((g : G) * S.v2 * (g : G)⁻¹) * (t : G)⁻¹ * ((g : G) * S.v2 * (g : G)⁻¹)⁻¹ *
            S.v2⁻¹ := by
        group
      rw [e]
      exact h2
  ·
    rw [A6Mod.secAct_secMk, A6Mod.secAct_secMk, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Setup.rho_apply_coe, Setup.rho_apply_coe, Subgroup.coe_mul, Setup.rho_apply_coe]
    have h1 := S.v2_mul_conj hg
    rw [h1]
    simp only [pow_two, Subgroup.coe_mul]
    group
  ·
    intro hfix
    have hainv : ∀ y ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)),
        (A6Mod.secAct hHU hHV ⟨g, hgH⟩)⁻¹ * y * A6Mod.secAct hHU hHV ⟨g, hgH⟩ ∈
          autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
      intro y hy
      obtain ⟨f, hfK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hy
      refine (A6Mod.mem_autSec_iff hHU hHV hKH).2
        ⟨⟨g, hgH⟩⁻¹ * f * ⟨g, hgH⟩, ?_, by rw [map_mul, map_mul, map_inv]⟩
      have h1 : (g : G)⁻¹ * (f : G) * (g : G)⁻¹⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgK) f).mp hfK
      rw [inv_inv] at h1
      exact h1
    have hafix : ∀ w ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))), A6Mod.secAct hHU hHV ⟨g, hgH⟩ w ∈
          fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
      intro w hw y hy
      have h1 := hw _ (hainv y hy)
      calc y (A6Mod.secAct hHU hHV ⟨g, hgH⟩ w) = A6Mod.secAct hHU hHV ⟨g, hgH⟩
            (((A6Mod.secAct hHU hHV ⟨g, hgH⟩)⁻¹ * y * A6Mod.secAct hHU hHV ⟨g, hgH⟩) w) := by
            rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
        _ = A6Mod.secAct hHU hHV ⟨g, hgH⟩ w := by rw [h1]
    have hmul : ∀ (u w : G) (hu : u ∈ conjClosure S.V3 H) (hw : w ∈ conjClosure S.V3 H),
        InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
          ⟨u * w, (conjClosure S.V3 H).mul_mem hu hw⟩ =
        InternalSec.secMk _ ⟨u, hu⟩ * InternalSec.secMk _ ⟨w, hw⟩ := by
      intro u w hu hw
      rw [← map_mul]
      rfl

    have hgvU : (g : G) * S.v2 * (g : G)⁻¹ ∈ conjClosure S.V3 H := le_conjClosure _ _ hgv
    have hfix1 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨_, hgvU⟩ ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
      have e : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨_, hgvU⟩ =
          A6Mod.secAct hHU hHV ⟨g, hgH⟩ (InternalSec.secMk _ ⟨S.v2, hv2U⟩) := by
        rw [A6Mod.secAct_secMk]
        congr 1
      rw [e]
      exact hafix _ hfix
    have hg2U : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) * S.v2 *
        ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ ∈ conjClosure S.V3 H := by
      rw [← S.v2_mul_conj hg]
      exact (conjClosure S.V3 H).mul_mem hv2U hgvU
    have hfix2 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨_, hg2U⟩ ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
      have e : (⟨_, hg2U⟩ : ↥(conjClosure S.V3 H)) = ⟨S.v2, hv2U⟩ * ⟨_, hgvU⟩ :=
        Subtype.ext (S.v2_mul_conj hg).symm
      rw [e, map_mul]
      exact Subgroup.mul_mem _ hfix hfix1

    have hall : ∀ u (hu : u ∈ S.V3), InternalSec.secMk
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨u, le_conjClosure _ _ hu⟩ ∈
          fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
      intro u hu
      have huU : u ∈ conjClosure S.V3 H := le_conjClosure _ _ hu
      have hinv : ∀ (w : G) (hw : w ∈ conjClosure S.V3 H), u * w ∈ fsuV1 T V →
          InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨w, hw⟩ ∈
            fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) →
          InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨u, huU⟩ ∈
            fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
        intro w hw huw hwf
        have h1 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
            ⟨u * w, (conjClosure S.V3 H).mul_mem huU hw⟩ = 1 :=
          (A6Mod.secMk_eq_one_iff _).2 huw
        rw [hmul u w huU hw] at h1
        rw [eq_inv_of_mul_eq_one_left h1]
        exact Subgroup.inv_mem _ hwf
      rcases S.mem_V3_cases hg hu with h | h | h | h
      · have h1 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
            ⟨u, huU⟩ = 1 := (A6Mod.secMk_eq_one_iff _).2 h
        rw [h1]
        exact Subgroup.one_mem _
      · exact hinv _ hv2U h hfix
      · exact hinv _ hgvU h hfix1
      · exact hinv _ hg2U h hfix2

    have hKV : ∀ u ∈ S.V3, ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V := by
      intro u hu k hk
      have hk' : A6Mod.secAct hHU hHV ⟨k, hKH hk⟩ ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :=
        (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨⟨k, hKH hk⟩, hk, rfl⟩
      have h1 := hall u hu _ hk'
      rw [A6Mod.secAct_secMk] at h1
      have h2 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
          (Setup.rho (conjClosure S.V3 H) H hHU ⟨k, hKH hk⟩ ⟨u, le_conjClosure _ _ hu⟩ *
            (⟨u, le_conjClosure _ _ hu⟩ : ↥(conjClosure S.V3 H))⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      rw [A6Mod.secMk_eq_one_iff, Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] at h2
      exact h2
    have hKG : K ≤ S.G1 := hKH.trans hH.2.1
    have hKC := le_centralizer_V3_of_mem_V1 (perfect_of_mem_cComp hK) hKG hKV
    exact (S.lem13812_one_F4 h139 h37 h38 hH hK).1
      (hKC.trans ((S.centralizer_V3_le_F4 h13315).trans S.NV_le_M))

theorem exists_odd_config_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) :
    ∃ (a : MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (P : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))))
      (v₂ : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))),
      (∀ y ∈ Kt, a * y * a⁻¹ ∈ Kt) ∧ P ≤ Kt ∧ IsPGroup 2 ↥P ∧ Odd (P.subgroupOf Kt).index ∧
      (∀ p ∈ P, p v₂ = v₂) ∧ (∀ p ∈ P, p (a v₂) = a v₂ ∨ p (a v₂) = v₂ * a v₂) ∧
      a (a v₂) = v₂ * a v₂ ∧ v₂ ∉ fixV Kt := by
  obtain ⟨g, hgX, hg⟩ := S.exists_X1375_c012
  obtain ⟨a, P, v₂, -, -, -, h⟩ := exists_odd_config_of_F4 hH hK hKt h139 h37 h38 h13315 hgX hg
  exact ⟨a, P, v₂, h⟩

end Config

end Setting4

theorem lem1376OddNCA5_of_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) : Lem1376OddNCA5_F4 := by
  intro G _ _ T L V S _ _ H hH _ _ K hK hmod _
  exfalso
  obtain ⟨π, hπ⟩ := hmod
  obtain ⟨a, P, v₂, haY, hPY, hP2, hPodd, hPv, hPa, ha2, hv⟩ :=
    Setting4.exists_odd_config_F4 hH hK rfl h139 h37 h38 h13315
  exact A6L76Oe.false_of_altDn5 (S.isPerfect_tilde hH hK) hπ haY hPY hP2 hPodd hPv hPa ha2 hv

end CFSG.Quasithin.H13.A6
