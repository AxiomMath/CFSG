module

public import CFSG.Quasithin.H13.A6S1372L76H
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L24b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76G

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

variable {S}

namespace Ctx76_F4
open CFSG.Quasithin.H13.A6.Setting4.Ctx76_F4

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)] {D : FFModel}
  (C : S.Ctx76_F4 H K D)
include C

theorem βU_V1_F4 {w : G} (hw : w ∈ fsuV1 T V) (hwU : w ∈ conjClosure S.V3 H) :
    C.βU_F4 ⟨w, hwU⟩ = 1 := by
  rw [C.βU_eq_one_iff_F4]
  intro k hk
  rw [S.conj_V1_of_mem C.hH (C.hKH_F4 hk) hw, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem βU_v2_ne_one_F4 : C.βU_F4 ⟨S.v2, S.v2_mem_UH H⟩ ≠ 1 := by
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  intro h
  exact S.comm_v2_not_mem_V1 hg ((C.βU_eq_one_iff_F4 _).1 h g (C.hL1K hgL))

end Ctx76_F4

end Setting4

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace Ctx76_F4
open CFSG.Quasithin.H13.A6.Setting4.Ctx76_F4

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]

theorem false_eight_F4 (h13314 : Stmt13_3_14_F4)
    (C : S.Ctx76_F4 H K (FFModel.altDn 8)) : False := by
  obtain ⟨⟨m, hm⟩, hxm⟩ := QuotientGroup.mk_surjective (C.βU_F4 ⟨S.v2, S.v2_mem_UH H⟩)
  obtain ⟨hE, ha, hb⟩ := A6L76E.check8 m (G6.mem_coreMod.1 hm)
  obtain ⟨hs1, hs2⟩ := A6L76E.sign_wit 8 m
  exact C.not_e9_F4 h13314 hm hxm.symm (a := ⟨_, Perm.mem_alternatingGroup.2 hs1⟩)
    (b := ⟨_, Perm.mem_alternatingGroup.2 hs2⟩) (A6L76H.e9_of_perm hE)
    ((A6L76C.act_mul_inv_mem_ker_iff hm _).2 ha) ((A6L76C.act_mul_inv_mem_ker_iff hm _).2 hb)

theorem false_ge_nine_F4 {n : ℕ} (hn : 9 ≤ n)
    (C : S.Ctx76_F4 H K (FFModel.altDn n)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (FFModel.altDn n).Gam) :=
    A6L76E.three_le_pRank_alt hn
  have h2 : (⊤ : Subgroup ↥K).map C.α_F4 = ⊤ := Subgroup.map_top_of_surjective _ C.α_surj_F4
  have h3 := A6L76B.pRank_map_le C.α_F4 C.not_three_dvd_ker_F4 ⊤
  rw [h2] at h3
  have h4 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = CFSG.Open.pRank 3 K :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
  have h5 : CFSG.Open.pRank 3 K ≤ CFSG.Open.pRank 3 H :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) C.hKH_F4
  have h6 := pRank_le_two_of_pCoreOf_ne_bot S.h13.qtke C.hH.1.2 Nat.prime_three (by norm_num)
  omega

theorem exists_rep_F4 {n : ℕ} (C : S.Ctx76_F4 H K (FFModel.altDn n)) :
    ∃ (m : G6.PermMod n) (hm : m ∈ (FFModel.altDn n).sec),
      C.βU_F4 ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨m, hm⟩ := by
  obtain ⟨⟨m, hm⟩, hxm⟩ := QuotientGroup.mk_surjective (C.βU_F4 ⟨S.v2, S.v2_mem_UH H⟩)
  exact ⟨m, hm, hxm.symm⟩

set_option maxHeartbeats 400000 in
theorem classes_odd_F4 {n : ℕ} (hodd : (∑ _i : Fin n, (1 : ZMod 2)) ≠ 0)
    (C : S.Ctx76_F4 H K (FFModel.altDn n)) {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgL : (g : G) ∈ S.L1) (hg : S.frame.ρ g = swap 0 1 * swap 1 2)
    {m : G6.PermMod n} (hm : m ∈ (FFModel.altDn n).sec)
    (hxm : C.βU_F4 ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨m, hm⟩) :
    m ≠ 1 ∧ m * G6.permAct n (A6L76C.permOf (C.α_F4 ⟨g, C.hL1K hgL⟩)) m =
      G6.permAct n (A6L76C.permOf (C.α_F4 ⟨g, C.hL1K hgL⟩) ^ 2) m := by
  have hgK : (g : G) ∈ K := C.hL1K hgL
  have hgU : (g : G) * S.v2 * (g : G)⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (C.hKH_F4 hgK)) _).mp
      (S.v2_mem_UH H)
  have hg2K : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ K := by
    rw [Subgroup.coe_pow]
    exact K.pow_mem hgK 2
  have hg2U : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) * S.v2 *
      ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (C.hKH_F4 hg2K)) _).mp
      (S.v2_mem_UH H)
  have hy := C.βU_equiv_F4 ⟨g, hgK⟩ ⟨S.v2, S.v2_mem_UH H⟩ hgU hm hxm
  have hz := C.βU_equiv_F4 ⟨_, hg2K⟩ ⟨S.v2, S.v2_mem_UH H⟩ hg2U hm hxm
  have hα2 : C.α_F4 ⟨_, hg2K⟩ = C.α_F4 ⟨g, hgK⟩ ^ 2 := by
    rw [← map_pow]
    congr 1
  have hprod : (⟨_, hg2U⟩ : ↥(conjClosure S.V3 H)) = ⟨S.v2, S.v2_mem_UH H⟩ * ⟨_, hgU⟩ :=
    Subtype.ext (S.v2_mul_conj hg).symm
  rw [hprod, map_mul, hxm, hy, ← QuotientGroup.mk_mul] at hz
  have hz' := congrArg Subtype.val (A6L76H.eq_of_mk_eq hodd hz)
  simp only [Subgroup.coe_mul] at hz'
  rw [hα2] at hz'
  refine ⟨fun h => C.βU_v2_ne_one_F4 ?_, hz'⟩
  rw [hxm]
  have e : (⟨m, hm⟩ : ↥(FFModel.altDn n).sec) = 1 := Subtype.ext h
  rw [e, QuotientGroup.mk_one]

theorem fix_O2L1_F4 {n : ℕ}
    (hodd : (∑ _i : Fin n, (1 : ZMod 2)) ≠ 0) (C : S.Ctx76_F4 H K (FFModel.altDn n)) {x : G}
    (hx : x ∈ pCoreOf 2 S.L1) {u : G} (hu3 : u ∈ S.V3) (huU : u ∈ conjClosure S.V3 H)
    {w : G6.PermMod n} (hw : w ∈ (FFModel.altDn n).sec)
    (hu : C.βU_F4 ⟨u, huU⟩ = QuotientGroup.mk ⟨w, hw⟩) :
    G6.permAct n (A6L76C.permOf (C.α_F4 ⟨x, C.hL1K (pCoreOf_le 2 S.L1 hx)⟩)) w = w := by
  have hxK : x ∈ K := C.hL1K (pCoreOf_le 2 S.L1 hx)
  have hxu : x * u * x⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (C.hKH_F4 hxK)) u).mp huU
  have h1 := C.βU_equiv_F4 ⟨x, hxK⟩ ⟨u, huU⟩ hxu hw hu
  have hcU : x * u * x⁻¹ * u⁻¹ ∈ conjClosure S.V3 H :=
    (conjClosure S.V3 H).mul_mem hxu ((conjClosure S.V3 H).inv_mem huU)
  have e : (⟨x * u * x⁻¹, hxu⟩ : ↥(conjClosure S.V3 H)) = ⟨_, hcU⟩ * ⟨u, huU⟩ :=
    Subtype.ext (inv_mul_cancel_right (x * u * x⁻¹) u).symm
  have h0 : C.βU_F4 ⟨x * u * x⁻¹, hxu⟩ = QuotientGroup.mk ⟨w, hw⟩ := by
    rw [e, map_mul, C.βU_V1_F4 (S.comm_O2L1_V3 hx hu3) hcU, one_mul, hu]
  have h2 := congrArg Subtype.val (A6L76H.eq_of_mk_eq hodd (h0.symm.trans h1))
  exact (A6L76C.act_eq _ _).symm.trans h2.symm

theorem permOf_α_pow_F4 {n : ℕ} (C : S.Ctx76_F4 H K (FFModel.altDn n)) {x : G} (hx : x ∈ K) {k : ℕ}
    (hk : x ^ k = 1) : A6L76C.permOf (C.α_F4 ⟨x, hx⟩) ^ k = 1 := by
  have h1 : (⟨x, hx⟩ : ↥K) ^ k = 1 := Subtype.ext (by simpa using hk)
  rw [show A6L76C.permOf (C.α_F4 ⟨x, hx⟩) ^ k = A6L76C.permOf (C.α_F4 ⟨x, hx⟩ ^ k) from rfl,
    ← map_pow, h1, map_one]
  rfl

theorem permOf_α_ne_one_F4 {n : ℕ}
    (C : S.Ctx76_F4 H K (FFModel.altDn n)) {x : G} (hx : x ∈ K) (hxQ : x ∉ pCoreOf 2 H) :
    A6L76C.permOf (C.α_F4 ⟨x, hx⟩) ≠ 1 := by
  intro h
  apply hxQ
  show ((⟨x, hx⟩ : ↥K) : G) ∈ pCoreOf 2 H
  rw [← C.α_eq_one_iff_F4]
  exact A6L76C.permOf_injective h

theorem not_hat_of_five_F4 (C : S.Ctx76_F4 H K (FFModel.altDn 5)) :
    ¬ IsHatA6 L := by
  intro hhat
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := S.two_le_pRank_L1_of_hat hhat
  have h2 : CFSG.Open.pRank 3 S.L1 ≤ CFSG.Open.pRank 3 K :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) C.hL1K
  have h3 : CFSG.Open.pRank 3 K = CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup K
  have h4 := A6L76F.pRank_le_map_of_not_dvd C.α_F4 C.not_three_dvd_ker_F4 ⊤
  have h5 : CFSG.Open.pRank 3 ((⊤ : Subgroup ↥K).map C.α_F4) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (FFModel.altDn 5).Gam) :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
  have h6 : CFSG.Open.pRank 3 (⊤ : Subgroup (FFModel.altDn 5).Gam) ≤ 1 :=
    A6L76H.pRank_alt5_le_one
  omega

theorem isKl_of_conj_F4 (C : S.Ctx76_F4 H K (FFModel.altDn 5))
    {c : G} (hcL : c ∈ S.L1) (hc3 : c ^ 3 = 1) (hcQ : c ∉ pCoreOf 2 H) {o₁ : G}
    (ho₁ : o₁ ∈ pCoreOf 2 S.L1) (ho₁Q : o₁ ∉ pCoreOf 2 H)
    (ho₂ : c * o₁ * c⁻¹ ∈ pCoreOf 2 S.L1) :
    A6L19.IsKl (A6L76C.permOf (C.α_F4 ⟨o₁, C.hL1K (pCoreOf_le 2 S.L1 ho₁)⟩))
      (A6L76C.permOf (C.α_F4 ⟨c * o₁ * c⁻¹, C.hL1K (pCoreOf_le 2 S.L1 ho₂)⟩)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOK : ∀ x ∈ pCoreOf 2 S.L1, x ∈ K := fun x hx => C.hL1K (pCoreOf_le 2 S.L1 hx)
  have hpow : ∀ x (hx : x ∈ pCoreOf 2 S.L1), ∃ k : ℕ,
      A6L76C.permOf (C.α_F4 ⟨x, hOK x hx⟩) ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨x, hx⟩
    exact ⟨k, C.permOf_α_pow_F4 (hOK x hx) (by simpa using congrArg Subtype.val hk)⟩
  have hsq : ∀ x (hx : x ∈ pCoreOf 2 S.L1),
      A6L76C.permOf (C.α_F4 ⟨x, hOK x hx⟩) * A6L76C.permOf (C.α_F4 ⟨x, hOK x hx⟩) = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hpow x hx
    exact A6L19.sq_check _ (A6L19.pow_eight_of_pow hk) (A6L76C.permOf_sign _)
  have ha1 := C.permOf_α_ne_one_F4 (hOK _ ho₁) ho₁Q
  have hb1 : A6L76C.permOf (C.α_F4 ⟨c * o₁ * c⁻¹, hOK _ ho₂⟩) ≠ 1 := by
    refine C.permOf_α_ne_one_F4 _ fun h => ho₁Q ?_
    have e : o₁ = c⁻¹ * (c * o₁ * c⁻¹) * c⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 H (H.inv_mem (C.hL1H_F4 hcL))) _).mp h
  have hba : A6L76C.permOf (C.α_F4 ⟨c * o₁ * c⁻¹, hOK _ ho₂⟩) =
      A6L76C.permOf (C.α_F4 ⟨c, C.hL1K hcL⟩) * A6L76C.permOf (C.α_F4 ⟨o₁, hOK _ ho₁⟩) *
        (A6L76C.permOf (C.α_F4 ⟨c, C.hL1K hcL⟩))⁻¹ := by
    have e : (⟨c * o₁ * c⁻¹, hOK _ ho₂⟩ : ↥K) =
        ⟨c, C.hL1K hcL⟩ * ⟨o₁, hOK _ ho₁⟩ * (⟨c, C.hL1K hcL⟩ : ↥K)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    rfl
  have hab : A6L76C.permOf (C.α_F4 ⟨o₁, hOK _ ho₁⟩) ≠
      A6L76C.permOf (C.α_F4 ⟨c * o₁ * c⁻¹, hOK _ ho₂⟩) := by
    intro h
    rw [hba] at h
    have hcomm : A6L76C.permOf (C.α_F4 ⟨o₁, hOK _ ho₁⟩) * A6L76C.permOf (C.α_F4 ⟨c, C.hL1K hcL⟩) =
        A6L76C.permOf (C.α_F4 ⟨c, C.hL1K hcL⟩) * A6L76C.permOf (C.α_F4 ⟨o₁, hOK _ ho₁⟩) := by
      conv_lhs => rw [h]
      group
    obtain ⟨k, hk⟩ := hpow _ ho₁
    exact ha1 (A6L24.eq_one_of_commute5 (C.permOf_α_pow_F4 _ hc3) (C.permOf_α_ne_one_F4 _ hcQ)
      (C.α_F4 ⟨o₁, hOK _ ho₁⟩).2 hcomm hk)
  have hmem : o₁ * (c * o₁ * c⁻¹) ∈ pCoreOf 2 S.L1 := (pCoreOf 2 S.L1).mul_mem ho₁ ho₂
  have hab8 : (A6L76C.permOf (C.α_F4 ⟨o₁, hOK _ ho₁⟩) *
      A6L76C.permOf (C.α_F4 ⟨c * o₁ * c⁻¹, hOK _ ho₂⟩)) ^ 8 = 1 := by
    obtain ⟨k, hk⟩ := hpow _ hmem
    have e : A6L76C.permOf (C.α_F4 ⟨o₁ * (c * o₁ * c⁻¹), hOK _ hmem⟩) =
        A6L76C.permOf (C.α_F4 ⟨o₁, hOK _ ho₁⟩) * A6L76C.permOf (C.α_F4 ⟨c * o₁ * c⁻¹, hOK _ ho₂⟩) := by
      rw [← A6L76C.permOf_mul, ← map_mul]
      rfl
    rw [e] at hk
    exact A6L19.pow_eight_of_pow hk
  exact ⟨hsq _ ho₁, hsq _ ho₂, A6L76E.comm5 _ _ (A6L76C.permOf_sign _) (A6L76C.permOf_sign _)
    (hsq _ ho₁) (hsq _ ho₂) hab8, ha1, hb1, hab, A6L76C.permOf_sign _, A6L76C.permOf_sign _⟩

theorem exists_kl5_F4 (C : S.Ctx76_F4 H K (FFModel.altDn 5))
    (hhat : ¬ IsHatA6 L) : ∃ (x₁ : G) (h₁ : x₁ ∈ pCoreOf 2 S.L1) (x₂ : G)
      (h₂ : x₂ ∈ pCoreOf 2 S.L1),
      A6L19.IsKl (A6L76C.permOf (C.α_F4 ⟨x₁, C.hL1K (pCoreOf_le 2 S.L1 h₁)⟩))
        (A6L76C.permOf (C.α_F4 ⟨x₂, C.hL1K (pCoreOf_le 2 S.L1 h₂)⟩)) := by
  have hcL : (S.cL1 hhat : G) ∈ S.L1 := S.cL1_mem hhat
  have hcQ : (S.cL1 hhat : G) ∉ pCoreOf 2 H :=
    S.not_mem_QH_of_L1_F4 C.hNS C.h13315 C.h1356two C.hH hcL (S.cL1_not_mem hhat)
  obtain ⟨o, ho, hoQ⟩ := S.exists_comm_not_mem_A5 hhat C.hH C.hKH_F4 C.hHK C.hL1K
    (α := C.α_F4) C.α_surj_F4 C.α_eq_one_iff_F4 hcL (S.cL1_cube hhat) hcQ
  have hcN := le_normalizer_pCoreOf 2 S.L1 hcL
  have ho₁ : (S.cL1 hhat : G) * o * (S.cL1 hhat : G)⁻¹ * o⁻¹ ∈ pCoreOf 2 S.L1 :=
    (pCoreOf 2 S.L1).mul_mem ((Subgroup.mem_normalizer_iff.mp hcN o).mp ho)
      ((pCoreOf 2 S.L1).inv_mem ho)
  have ho₂ := (Subgroup.mem_normalizer_iff.mp hcN _).mp ho₁
  exact ⟨_, ho₁, _, ho₂, C.isKl_of_conj_F4 hcL (S.cL1_cube hhat) hcQ ho₁ hoQ ho₂⟩

theorem false_five_F4 (C : S.Ctx76_F4 H K (FFModel.altDn 5)) :
    False := by
  have hodd := A6L76H.sum_one_five
  obtain ⟨x₁, h₁, x₂, h₂, hKl⟩ := C.exists_kl5_F4 C.not_hat_of_five_F4
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  obtain ⟨m, hm, hxm⟩ := C.exists_rep_F4
  obtain ⟨hm1, hmz⟩ := C.classes_odd_F4 hodd hgL hg hm hxm
  have hgU : (g : G) * S.v2 * (g : G)⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (C.hL1H_F4 hgL)) _).mp
      (S.v2_mem_UH H)
  have hy := C.βU_equiv_F4 ⟨g, C.hL1K hgL⟩ ⟨S.v2, S.v2_mem_UH H⟩ hgU hm hxm
  have hym : G6.permAct 5 (A6L76C.permOf (C.α_F4 ⟨g, C.hL1K hgL⟩)) m ∈ (FFModel.altDn 5).sec :=
    G6.permAct_mem_coreMod _ hm
  have hy1 : G6.permAct 5 (A6L76C.permOf (C.α_F4 ⟨g, C.hL1K hgL⟩)) m ≠ 1 := fun h =>
    hm1 ((MulEquiv.map_eq_one_iff _).1 h)
  have hmy : m ≠ G6.permAct 5 (A6L76C.permOf (C.α_F4 ⟨g, C.hL1K hgL⟩)) m := fun h => by
    rw [← h, G6.permMod_mul_self] at hmz
    exact hm1 ((MulEquiv.map_eq_one_iff _).1 hmz.symm)
  exact hmy (A6L76E.kl5_eq hKl (G6.mem_coreMod.1 hm) (G6.mem_coreMod.1 hym) hm1 hy1
    (C.fix_O2L1_F4 hodd h₁ S.v2_mem_V3 (S.v2_mem_UH H) hm hxm)
    (C.fix_O2L1_F4 hodd h₂ S.v2_mem_V3 (S.v2_mem_UH H) hm hxm)
    (C.fix_O2L1_F4 hodd h₁ (S.conj_v2_mem_V3 hg) hgU hym hy)
    (C.fix_O2L1_F4 hodd h₂ (S.conj_v2_mem_V3 hg) hgU hym hy))

end Ctx76_F4

end Setting4

end CFSG.Quasithin.H13.A6
