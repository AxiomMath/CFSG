module

public import CFSG.Quasithin.H13.A6S1372L76U
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76T

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge Matrix
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

variable {S}

namespace Ctx76_F4
open CFSG.Quasithin.H13.A6.Setting4.Ctx76_F4

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]
  {α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2)}

theorem false_hat_a7_F4 (C : S.Ctx76_F4 H K (FFModel.a7Four α))
    (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) (hhat : IsHatA6 L) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 C.hH
  obtain ⟨w, hwL1, hwV, hw3, hwQ⟩ := S.exists_w hhat
  obtain ⟨n, hnT, hnρ, hnw⟩ := S.exists_comm_T hhat hwV hw3 hwQ
  have hnH : (n : G) ∈ H := C.hTH_F4 hnT

  have hmem : A6Mod.secAct hHU hHV ⟨n, hnH⟩ ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
    rw [← C.tilde_eq_a7_F4 hfix]
    exact (A6Mod.mem_autSec_iff hHU hHV le_rfl).2 ⟨⟨n, hnH⟩, hnH, rfl⟩
  obtain ⟨⟨k₀, hk₀H⟩, hk₀K, hk₀⟩ := (A6Mod.mem_autSec_iff hHU hHV C.hKH_F4).1 hmem
  set k : ↥K := ⟨k₀, hk₀K⟩ with hkdef
  have hk : ((C.κ_F4 k : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) =
      A6Mod.secAct hHU hHV ⟨n, hnH⟩ := by
    rw [C.κ_coe_F4]
    exact hk₀
  set wK : ↥K := ⟨w, C.hL1K hwL1⟩ with hwK

  have hκ : C.κ_F4 k * C.κ_F4 wK = C.κ_F4 wK * C.κ_F4 k := by
    apply Subtype.ext
    have e : (⟨n, hnH⟩ : ↥H) * ⟨w, C.hKH_F4 wK.2⟩ = ⟨w, C.hKH_F4 wK.2⟩ * ⟨n, hnH⟩ := Subtype.ext hnw
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hk, C.κ_coe_F4, ← map_mul, e, map_mul]
  have hσb' : C.α_F4 k * C.α_F4 wK = C.α_F4 wK * C.α_F4 k := by
    show C.eπ_F4.symm (C.κ_F4 k) * C.eπ_F4.symm (C.κ_F4 wK) = C.eπ_F4.symm (C.κ_F4 wK) * C.eπ_F4.symm (C.κ_F4 k)
    rw [← map_mul, hκ, map_mul]
  have hwK3 : wK ^ 3 = 1 := Subtype.ext (by
    have := congrArg Subtype.val hw3
    simpa using this)
  have hb3' : C.α_F4 wK ^ 3 = 1 := by rw [← map_pow, hwK3, map_one]
  have hb1' : C.α_F4 wK ≠ 1 := by
    intro h
    have hwK1 : wK ≠ 1 := by
      intro h1
      apply hwQ
      have h2 : ((wK : ↥K) : G) = 1 := congrArg Subtype.val h1
      have : w = 1 := Subtype.ext h2
      rw [this, QuotientGroup.mk_one]
    have hker : wK ∈ C.α_F4.ker := h
    have ho : orderOf (⟨wK, hker⟩ : ↥C.α_F4.ker) = 3 :=
      orderOf_eq_prime (Subtype.ext (by simpa using hwK3))
        (fun h1 => hwK1 (congrArg Subtype.val h1))
    exact C.not_three_dvd_ker_F4 (ho ▸ orderOf_dvd_natCard _)
  have hbfix' : A6L76T.mat7 α (C.α_F4 wK) *ᵥ C.cls7_F4 ⟨S.v2, S.v2_mem_UH H⟩ =
      C.cls7_F4 ⟨S.v2, S.v2_mem_UH H⟩ := by
    have hku := C.conj_mem_UH_F4 wK.2 (S.v2_mem_UH H)
    rw [← C.cls7_equiv_F4 wK _ hku]
    congr 1
    apply Subtype.ext
    show (w : G) * S.v2 * (w : G)⁻¹ = S.v2
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.mp hwV S.v2 S.v2_mem_V).symm

  obtain ⟨e, he⟩ := S.h13.sylow.1 ⟨n, hnT⟩
  have hne : (⟨n, hnH⟩ : ↥H) ^ (2 ^ e) = 1 := Subtype.ext (by
    have := congrArg Subtype.val he
    simpa using this)
  have h1 : C.κ_F4 k ^ (2 ^ e) = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, hk, ← map_pow, hne, map_one]
    rfl
  have hσe' : C.α_F4 k ^ (2 ^ e) = 1 := by
    show C.eπ_F4.symm (C.κ_F4 k) ^ (2 ^ e) = 1
    rw [← map_pow, h1, map_one]

  obtain ⟨b, hb⟩ : ∃ b : ↥(alternatingGroup (Fin 7)), b = C.α_F4 wK := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥(alternatingGroup (Fin 7)), σ = C.α_F4 k := ⟨_, rfl⟩
  have hσb : σ * b = b * σ := by rw [hσ, hb]; exact hσb'
  have hb3 : b ^ 3 = 1 := by rw [hb]; exact hb3'
  have hb1 : b ≠ 1 := by rw [hb]; exact hb1'
  have hbfix : A6L76T.mat7 α b *ᵥ C.cls7_F4 ⟨S.v2, S.v2_mem_UH H⟩ =
      C.cls7_F4 ⟨S.v2, S.v2_mem_UH H⟩ := by rw [hb]; exact hbfix'
  have hb3c : ¬ (b : Perm (Fin 7)).IsThreeCycle := by
    intro hc
    have h0 := A6L76S.fpf_of_isThreeCycle α hc _ hbfix
    exact C.βU_v2_ne_one_F4 ((C.cls7_eq_zero_iff_F4 _).1 h0)
  have hσe : σ ^ (2 ^ e) = 1 := by rw [hσ]; exact hσe'
  have hσ8 : σ ^ 8 = 1 := by
    obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hσe)
    have hd : orderOf σ ∣ 2520 := by
      have := orderOf_dvd_natCard σ
      rwa [nat_card_alternatingGroup, Nat.card_fin] at this
    have hj3 : j ≤ 3 := by
      by_contra hj3
      push Not at hj3
      have h16 : 2 ^ 4 ∣ 2520 := (Nat.pow_dvd_pow 2 hj3).trans (hjo ▸ hd)
      norm_num at h16
    rw [show (8 : ℕ) = 2 ^ 3 from rfl, ← orderOf_dvd_iff_pow_eq_one, hjo]
    exact Nat.pow_dvd_pow 2 hj3

  have hσ1 : (σ : Perm (Fin 7)) = 1 :=
    A6L76S.eq_one_of_comm_order_three
      (by rw [← Subgroup.coe_pow, hb3]; rfl)
      (fun h => hb1 (Subtype.ext h)) hb3c (congrArg Subtype.val hσb)
      (Perm.mem_alternatingGroup.1 σ.2)
      (by rw [← Subgroup.coe_pow, hσ8]; rfl)
  have hκ1 : C.κ_F4 k = 1 := by
    have h2 : σ = 1 := Subtype.ext hσ1
    have h3 : C.eπ_F4.symm (C.κ_F4 k) = 1 := hσ.symm.trans h2
    rwa [MulEquiv.map_eq_one_iff] at h3
  have hsec1 : A6Mod.secAct hHU hHV ⟨n, hnH⟩ = 1 := by
    rw [← hk, hκ1]
    rfl

  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  have h1 := (A6Mod.secAct_eq_one_iff hHU hHV _).1 hsec1 _
    (C.conj_mem_UH_F4 (C.hL1K hgL) (S.v2_mem_UH H))
  have hng : (n : G) * ((g : G) * S.v2 * (g : G)⁻¹) * (n : G)⁻¹ =
      ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) * S.v2 *
        ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ := by
    have e1 : (n : G) * ((g : G) * S.v2 * (g : G)⁻¹) * (n : G)⁻¹ =
        ((n * g : ↥(Subgroup.normalizer (V : Set G))) : G) * S.v2 *
          ((n * g : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ := by
      rw [Subgroup.coe_mul]
      group
    rw [e1]
    have h2 : S.frame.ψ ⟨_, S.conj_v2_mem_V (n * g)⟩ = S.frame.ψ ⟨_, S.conj_v2_mem_V (g ^ 2)⟩ := by
      apply Subtype.ext
      rw [S.psi_conj_v2, S.psi_conj_v2, map_mul, map_pow, hnρ, hg]
      decide
    exact congrArg Subtype.val (S.frame.ψ.injective h2)
  rw [hng, ← S.v2_mul_conj hg, mul_inv_cancel_right] at h1
  exact S.v2_not_mem_V1 h1

end Ctx76_F4

variable (S)
include S

theorem lem1376_four_F4 (hB : Lem1376L1K_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) (h1337 : Stmt13_3_7_F4)
    (hNS : ¬ LieModel G .PSp 3 2 1) (hNU : ¬ LieModel G .PSU 4 3 1) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H) :
    ¬ A7Four (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) := by
  intro hA
  have hL1K := hB G T L V S hNS hNU H hH hab K hK
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA)))))
  obtain ⟨α, π, hπ⟩ := id hA
  have : IsSimpleGroup (FFModel.a7Four α).Gam := A6L76A.isSimpleGroup_alt (n := 7) (by norm_num)
  obtain ⟨C⟩ := S.exists_ctx_F4 h37 h38 h13315 h1356two hNS hH hab hK hL1K
    (A6L76A.not_isSolvable_alt (n := 7) (by norm_num)) ⟨π, hπ⟩
  have hfix := A6L76R.fixV_eq_bot_of_a7Four _ _ (fun v => (sq v).symm.trans (C.sq_tildeU_F4 v))
    C.top_F4 hA
  exact C.false_hat_a7_F4 hfix (C.hat_of_a7_F4 h1337 hfix)

end Setting4

end CFSG.Quasithin.H13.A6
