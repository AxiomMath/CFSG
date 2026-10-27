module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
public import CFSG.Blueprint.Chevalley
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UFix
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylPlusLiftTorus
import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.Blueprint.Chevalley CFSG.StandardType

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

theorem le_four_of_torusLift (h : QSNL 5 S B T x D K) (hF : catalogIs (PSimple 5 K) (tyFUni 5))
    {R : Type} [Group R] (θ : ↥S ⧸ Subgroup.center ↥S ≃* R) {r : ℕ} (hT : GGTorusLift 5 r R) :
    r ≤ 4 := by
  have h1 := SF.pow_mul_card_le_of_torusLift h.cfg.prime h.cfg.quasi.1 θ hT
    (CFSG.Open.isElemAbelian_bot 5) bot_le
  rw [Subgroup.card_bot, mul_one] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1
    ((h1.trans h.cfg.rank).trans (card_eq_of_qsnl h hF).le)

section Cert


private theorem false_of_four_lt_rank_of_dvd_sub_one (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) {τ : Tag} (hτ : 4 < τ.rank) {d : ℕ}
    (hdet : τ.cartan.det = d) (hd : Nat.Coprime d 5) {F : Type} [Field F] [Finite F]
    [CharP F 2] (h5 : 5 ∣ Nat.card F - 1) (θ : ↥S ⧸ Subgroup.center ↥S ≃* adjointGroup τ F) :
    False := by
  have := le_four_of_torusLift h hF θ (TableBExc.ggTorusLift_adjoint (by omega) Nat.prime_five
    (by norm_num) h5 (TableBExc.isUnit_det_cartan_of_eq Nat.prime_five hdet hd))
  omega

theorem false_of_E6_dvd_sub_one (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) {F : Type} [Field F] [Finite F] [CharP F 2]
    (h5 : 5 ∣ Nat.card F - 1) (θ : ↥S ⧸ Subgroup.center ↥S ≃* adjointGroup .E6 F) : False :=
  false_of_four_lt_rank_of_dvd_sub_one h hF (by decide) CFSG.LieType.Chevalley.det_cartan_E6
    (by norm_num) h5 θ

theorem false_of_E7_dvd_sub_one (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) {F : Type} [Field F] [Finite F] [CharP F 2]
    (h5 : 5 ∣ Nat.card F - 1) (θ : ↥S ⧸ Subgroup.center ↥S ≃* adjointGroup .E7 F) : False :=
  false_of_four_lt_rank_of_dvd_sub_one h hF (by decide) CFSG.LieType.Chevalley.det_cartan_E7
    (by norm_num) h5 θ

theorem false_of_E8_dvd_sub_one (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) {F : Type} [Field F] [Finite F] [CharP F 2]
    (h5 : 5 ∣ Nat.card F - 1) (θ : ↥S ⧸ Subgroup.center ↥S ≃* adjointGroup .E8 F) : False :=
  false_of_four_lt_rank_of_dvd_sub_one h hF (by decide) CFSG.LieType.Chevalley.det_cartan_E8
    (by norm_num) h5 θ


theorem false_of_E7_dvd_add_one (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) {F : Type} [Field F] [Finite F] [CharP F 2]
    (h5 : 5 ∣ Nat.card F + 1) (θ : ↥S ⧸ Subgroup.center ↥S ≃* adjointGroup .E7 F) : False := by
  have := le_four_of_torusLift h hF θ (GGPlusLiftTorus.ggTorusLift_of_commutingSL2
    Nat.prime_five (by norm_num) h5 (TableBExcTwo.rho F TableBExcTwo.frameE7)
    (TableBExcTwo.rho_injective _) fun _ _ hij => TableBExcTwo.commute_rho _ hij)
  omega

theorem false_of_E8_dvd_add_one (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) {F : Type} [Field F] [Finite F] [CharP F 2]
    (h5 : 5 ∣ Nat.card F + 1) (θ : ↥S ⧸ Subgroup.center ↥S ≃* adjointGroup .E8 F) : False := by
  have := le_four_of_torusLift h hF θ (GGPlusLiftTorus.ggTorusLift_of_commutingSL2
    Nat.prime_five (by norm_num) h5 (TableBExcTwo.rho F TableBExcTwo.frameE8)
    (TableBExcTwo.rho_injective _) fun _ _ hij => TableBExcTwo.commute_rho _ hij)
  omega

end Cert

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
