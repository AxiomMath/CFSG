module

public import CFSG.Quasithin.H13.A6S1372L76Of4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76Oe2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76W

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem normal_of_natSL3_F4 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) (h38 : A38ForSQTK) {H : Subgroup G}
    (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G}
    (hK : K ∈ cComp H) {F : Type} [Field F] [Finite F] {n : ℕ} (hn3 : 3 ≤ n)
    (hF : Nat.card F = 2 ^ n)
    {U Z : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    (hR : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).Realizes
      (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) U Z) :
    ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨eK⟩ := S.exists_quotEquiv_of_realizes_F4 hNS h13315 h1356two hH hK
    (FFModel.nat_faithful _) hR
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  have hK₀ : K.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp hK
  obtain ⟨r, hr, hrd, -⟩ := A3Facts.exists_prime_dvd_two_pow_sub_one hn3
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have hrank : 1 < CFSG.Open.pRank r (K.subgroupOf H) := by
    rw [Vol2.Ch11.SecA.pRank_subgroupOf_eq hKH hr hr2]
    have : Finite (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).Gam :=
      Finite.of_equiv _ eK.toEquiv
    have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := r) hr.one_lt eK
    have h2 := A6L76Of.two_le_pRank_statedSL3 (F := F) hr (by rw [hF]; exact hrd)
    have h3 : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) := by
      rw [h1]
      exact h2
    omega
  have hKn : (K.subgroupOf H).Normal := A318.normal_of_pRank_gt_one hSQ
    (h38 _ (SQTKHyp.of_sqtkGroup ↥H hSQ)) hK₀ hr hr2 hrank
  intro h hh k hk
  have := Subgroup.mem_subgroupOf.1 (hKn.conj_mem ⟨k, hKH hk⟩ hk ⟨h, hh⟩)
  simpa using this

theorem false_of_natSL3_odd_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (hNS : ¬ LieModel G .PSp 3 2 1) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H) {n : ℕ}
    (hn : Odd n) (hn3 : 3 ≤ n)
    (hSL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hSL
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  obtain ⟨g, hgX, hg⟩ := S.exists_X1375_c012
  obtain ⟨a, P, v₂, rfl, -, -, haY, -, hP2, hPodd, hPv, hPa, ha2, hv⟩ :=
    S.exists_odd_config_of_F4 hH hK rfl h139 h37 h38 h13315 hgX hg
  obtain ⟨t, htT, j, hj⟩ := S.exists_inverting hgX hg
  have hHK := S.normal_of_natSL3_F4 hNS h13315 h1356two h38 hH hK hn3 hF ⟨π, hπ⟩
  have htH : t ∈ H := hTH htT
  refine A6L76Of.false_of_natSL3 (S.isPerfect_tilde hH hK) hn hn3 hF hπ haY hP2 hPodd hPv
    hPa ha2 hv (t := A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
      ⟨t, htH⟩) (fun y hy => ?_) (j := j) ?_
  ·
    obtain ⟨f, hfK, rfl⟩ := (A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H)
      (S.le_normalizer_UV1 hH) hKH).1 hy
    refine (A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
      hKH).2 ⟨⟨t, htH⟩ * f * ⟨t, htH⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact hHK t htH f hfK
  ·
    have h1 : ((⟨t, htH⟩ : ↥H) * ⟨(g : G), X1375_le_H hH hgX⟩ * (⟨t, htH⟩ : ↥H)⁻¹ *
        ⟨(g : G), X1375_le_H hH hgX⟩) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hj)
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, h1, map_one]

end Setting4

theorem lem1376OddNCBig_of_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) :
    Lem1376OddNCBig_F4 := by
  intro G _ _ T L V S hNS _ H hH _ _ K hK hmod _
  obtain ⟨n, hn, hn3, hSL⟩ := hmod
  exact (S.false_of_natSL3_odd_F4 h139 h37 h38 h13315 h1356two hNS hH hK hn hn3 hSL).elim

end CFSG.Quasithin.H13.A6
