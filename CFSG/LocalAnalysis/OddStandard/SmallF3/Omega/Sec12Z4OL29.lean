module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Statements
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OSq
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121A
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Inv
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Pow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Prod
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aComp
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Rank

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem z4o_conj_mem_centralizer {J : Subgroup G} {g c : G} (hg : g ∈ normalizer (J : Set G))
    (hc : c ∈ centralizer (J : Set G)) : g⁻¹ * c * g ∈ centralizer (J : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hj' : g * j * g⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hg j).mp hj
  have h := Subgroup.mem_centralizer_iff.mp hc _ hj'
  calc j * (g⁻¹ * c * g) = g⁻¹ * ((g * j * g⁻¹) * c) * g := by group
    _ = g⁻¹ * (c * (g * j * g⁻¹)) * g := by rw [h]
    _ = g⁻¹ * c * g * j := by group

theorem sec123z4_false_of_l29 [Finite G] (h65 : Asc82Lemma65) (hH : Asc82Hyp62 G) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 E : Subgroup G} (hctx : Sec12Ctx G t L S z K1 K2 E)
    (F : Sec12Frame t L S)
    (hZ : IsZ4Pow4 (secV t S L E)) {s : G} (hs : orderOf s = 2) (hsS : s ∈ S)
    (hsL : s ∉ L ⊔ centralizer (L : Set G))
    (h64 : Nat.card (secV t S L E ⊓ centralizer ({s} : Set G) : Subgroup G) = 2 ^ 6)
    (hCB : ¬ secB S L ≤ centralizer ({s} : Set G))
    (hJ29 : IsL29 (layerCent L s))
    (hI : IsComponentIn (layerCent L s) (centralizer ({s} : Set G)))
    (hN : centralizer ({s} : Set G) ≤ normalizer (layerCent L s : Set G)) : False := by
  classical
  have hS : Sec3SettingLB G t L := hctx.toSec10Z.toSec10Setting.toSec3SettingLB
  have hq : IsQuasisimple ↥(layerCent L s) := hI.isQuasisimple
  have hBV : secB S L ≤ secV t S L E := sec121_B_le_V F hctx.sylowE
  have hB2 : ∀ b ∈ secB S L, b * b = 1 := fun b hb => sec12E_B_sq F hb
  have hVc := sec124_z4_comm hZ
  have htinv := sec124_t_inv F hctx.sylowE hZ
  have hJL : layerCent L s ≤ L := by
    unfold layerCent CFSG.inSubgroup
    exact (Subgroup.map_subtype_le _).trans inf_le_left
  have htJ : t ∈ centralizer (layerCent L s : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp F.htC x (hJL hx)
  have hsJ : s ∈ centralizer (layerCent L s : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hI.le hx)
  have hts : t ∈ centralizer ({s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hsS)).symm
  obtain ⟨D2, hD2B, hD2sq, hDcard⟩ := z4o_exists_sq hZ hBV F.bdata.2.1 hB2
    (inf_le_left : secV t S L E ⊓ centralizer ({s} : Set G) ≤ secV t S L E)
  have hDB := z4o_card_inf_le F.bdata.2.1 hCB
    (inf_le_right : secV t S L E ⊓ centralizer ({s} : Set G) ≤ centralizer ({s} : Set G))
  have hD2card : 2 ^ 3 ≤ Nat.card D2 := by
    have h1 : 2 ^ 6 ≤ 2 ^ 3 * Nat.card D2 := by
      rw [← h64, hDcard]
      exact Nat.mul_le_mul_right _ hDB
    norm_num at h1 ⊢
    omega
  have hD2J : D2 ≤ centralizer (layerCent L s : Set G) := by
    intro x hx
    obtain ⟨v, hvD, rfl⟩ := (hD2sq x).mp hx
    have hvN : v ∈ normalizer (layerCent L s : Set G) := hN hvD.2
    have e : v * v = ((v⁻¹ * t * v) * t⁻¹)⁻¹ := by
      rw [show v⁻¹ * t * v * t⁻¹ = v⁻¹ * (t * v * t⁻¹) by group, htinv v hvD.1, mul_inv_rev,
        inv_inv]
    rw [e]
    exact inv_mem (mul_mem (z4o_conj_mem_centralizer hvN htJ) (inv_mem htJ))
  have hD2s : D2 ≤ centralizer ({s} : Set G) := by
    intro x hx
    obtain ⟨v, hvD, rfl⟩ := (hD2sq x).mp hx
    exact mul_mem hvD.2 hvD.2
  have hD2el : CFSG.Open.IsElemAbelian 2 D2 :=
    ⟨⟨⟨fun a b => Subtype.ext (hVc a (hBV (hD2B a.2)) b (hBV (hD2B b.2)))⟩⟩,
      fun x hx => by rw [sq]; exact hB2 x (hD2B hx)⟩
  have ht2 : t ^ 2 = 1 := by rw [← F.ht2]; exact pow_orderOf_eq_one t
  have hs2 : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have htD2 : t ∉ D2 := fun h => sec120_t_not_mem_L F (F.bdata.1 (hD2B h))
  have hcD2t : ∀ h ∈ D2, h * t = t * h := fun h hh => (sec12E_t_comm_B F (hD2B hh)).symm
  have hE0card := z4o_card_sup_zpowers F.ht2 htD2 hcD2t
  have hE0el : CFSG.Open.IsElemAbelian 2 (D2 ⊔ zpowers t) := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute hD2el (CFSG.Open.isElemAbelian_zpowers ht2) ?_
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a t from hcD2t a ha) i).eq
  have hE0K : D2 ⊔ zpowers t ≤ L ⊔ centralizer (L : Set G) :=
    sup_le ((hD2B.trans F.bdata.1).trans le_sup_left) (zpowers_le.mpr (mem_sup_right F.htC))
  have hsE0 : s ∉ D2 ⊔ zpowers t := fun h => hsL (hE0K h)
  have hE0s : D2 ⊔ zpowers t ≤ centralizer ({s} : Set G) := sup_le hD2s (zpowers_le.mpr hts)
  have hcE0s : ∀ h ∈ D2 ⊔ zpowers t, h * s = s * h := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (hE0s hh)
  have hE1card := z4o_card_sup_zpowers hs hsE0 hcE0s
  have hE1el : CFSG.Open.IsElemAbelian 2 (D2 ⊔ zpowers t ⊔ zpowers s) := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute hE0el (CFSG.Open.isElemAbelian_zpowers hs2) ?_
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a s from hcE0s a ha) i).eq
  have hE1J : D2 ⊔ zpowers t ⊔ zpowers s ≤ centralizer (layerCent L s : Set G) :=
    sup_le (sup_le hD2J (zpowers_le.mpr htJ)) (zpowers_le.mpr hsJ)
  obtain ⟨K, hKJ, hKel, hK4⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := 2) Nat.prime_two
      (H := layerCent L s) (k := 2) (sec63_two_le_pRank hq (Or.inl hJ29))
  have hKE1 : K ⊓ (D2 ⊔ zpowers t ⊔ zpowers s) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    have hx2 : orderOf x = 2 := orderOf_eq_prime (hKel.2 x hx.1) hx1
    have hJx : layerCent L s ≤ centralizer ({x} : Set G) := fun j hj =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hE1J hx.2) j hj)
    exact sec63_involution_not_mem hx2 hJx hq (Or.inl hJ29) (hKJ hx.1)
  have hcKE1 : ∀ a ∈ K, ∀ b ∈ D2 ⊔ zpowers t ⊔ zpowers s, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hE1J hb) a (hKJ ha)
  have hE2card := sec124_card_sup hcKE1 hKE1
  have hE2el : CFSG.Open.IsElemAbelian 2 (K ⊔ (D2 ⊔ zpowers t ⊔ zpowers s)) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hKel hE1el hcKE1
  have hE2N : K ⊔ (D2 ⊔ zpowers t ⊔ zpowers s) ≤ normalizer (layerCent L s : Set G) :=
    sup_le (hKJ.trans Subgroup.le_normalizer)
      (hE1J.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨k, hk⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card Nat.prime_two hE2el
  have h7 : k ≤ CFSG.Open.pRank 2 (normalizer (layerCent L s : Set G)) :=
    CFSG.SectionRank.le_pRank (by norm_num) hE2N hE2el hk
  have h6 := h65 G t L hS hH (layerCent L s) ⟨s, hs, hI⟩ (sec123_inFStar_of_isL29 hq hJ29)
  have hbig : 2 ^ 7 ≤ 2 ^ k := by
    rw [← hk, hE2card, hE1card, hE0card, hK4]
    norm_num at hD2card ⊢
    omega
  have hk7 : 7 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hbig
  omega

end CFSG.OddStandard.SmallF3.Omega
