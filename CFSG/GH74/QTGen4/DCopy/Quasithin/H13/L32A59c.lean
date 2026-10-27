module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A53c
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.EmptyFaithful.S1417Rank
public import CFSG.Quasithin.H13.L32A59b

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.T53.Ctx

variable {T L V V₂ Y : Subgroup G} (C : Ctx_F4 G T L V V₂ Y)
include C

theorem le_normalizer_of_comm_F4
    (hc : ∀ x ∈ xL L V₂, Odd (orderOf x) → ∀ y ∈ Y, Odd (orderOf y) →
      y * x * y⁻¹ * x⁻¹ ∈ Subgroup.centralizer (vH T L V V₂ Y : Set G)) :
    Y ≤ Subgroup.normalizer ((xL L V₂ ⊔ cH T L V V₂ Y : Subgroup G) : Set G) := by
  have hCn : hY T L V₂ Y ≤ Subgroup.normalizer (cH T L V V₂ Y : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      le_normalizer_centralizer_vH le_rfl hg⟩
  set K := xL L V₂ ⊔ cH T L V V₂ Y with hK
  have h : oTwoUpper Y ≤ Subgroup.normalizer (K : Set G) := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨hyY, hyo⟩ := hy
    have hyH : y ∈ hY T L V₂ Y := Subgroup.mem_sup_left (Subgroup.mem_sup_right hyY)
    have hle : K ≤ conjSub y⁻¹ K := by
      refine sup_le ((Subgroup.closure_le _).mpr fun x hx => ?_) fun c hc' => ?_
      · obtain ⟨hxL, m, hm, hxm⟩ := hx
        have hxX : x ∈ xL L V₂ := Subgroup.subset_closure ⟨hxL, m, hm, hxm⟩
        have hxo : Odd (orderOf x) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hxm)
        have hxH : x ∈ hY T L V₂ Y := Subgroup.mem_sup_left (Subgroup.mem_sup_left hxX)
        have hcx : y * x * y⁻¹ * x⁻¹ ∈ cH T L V V₂ Y :=
          Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem hyH hxH) (inv_mem hyH)) (inv_mem hxH),
            hc x hxX hxo y hyY hyo⟩
        rw [SetLike.mem_coe, mem_conjSub, inv_inv,
          show y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x by group]
        exact mul_mem (Subgroup.mem_sup_right hcx) (Subgroup.mem_sup_left hxX)
      · rw [mem_conjSub, inv_inv]
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hCn hyH) c).mp hc')
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have := hle hn
    rwa [mem_conjSub, inv_inv] at this
  rwa [C.hYo] at h

theorem inf_le_pCoreOf_of_normal_F4 (h4 : Lemma14_7_4_two_three_F4) {N : Subgroup G}
    (hN : hY T L V₂ Y ≤ Subgroup.normalizer (N : Set G)) (hX : ¬ xL L V₂ ≤ N) (hYN : ¬ Y ≤ N) :
    T ⊓ N ≤ pCoreOf 2 (hY T L V₂ Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ hY T L V₂ Y := le_sup_right
  have hXH : xL L V₂ ⊔ T ≤ hY T L V₂ Y := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hYH : Y ⊔ T ≤ hY T L V₂ Y := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hnorm : ∀ {P : Subgroup G}, P ≤ hY T L V₂ Y →
      P ≤ Subgroup.normalizer ((P ⊓ N : Subgroup G) : Set G) := fun hP x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hN (hP hx)⟩
  set R := T ⊓ N with hR
  have hXT : (xL L V₂ ⊔ T) ⊓ N = R := by
    refine le_antisymm (le_inf ?_ inf_le_right) (inf_le_inf_right _ le_sup_right)
    refine (le_pCoreOf_of_normal_of_S3 (C.quot_xT_F4 h4).1 inf_le_left (hnorm hXH) ?_).trans
      (pCoreOf_le_of_le C.hyp le_sup_right)
    rw [C.oTwoUpper_xT_F4]
    exact fun h => hX (h.trans inf_le_right)
  have hYT : (Y ⊔ T) ⊓ N = R := by
    refine le_antisymm (le_inf ?_ inf_le_right) (inf_le_inf_right _ le_sup_right)
    refine (le_pCoreOf_of_normal_of_S3 C.hS3 inf_le_left (hnorm hYH) ?_).trans
      (pCoreOf_le_of_le C.hyp le_sup_right)
    rw [C.oTwoUpper_yT_F4]
    exact fun h => hYN (h.trans inf_le_right)
  have hXN : xL L V₂ ⊔ T ≤ Subgroup.normalizer (R : Set G) := hXT ▸ hnorm hXH
  have hYN' : Y ⊔ T ≤ Subgroup.normalizer (R : Set G) := hYT ▸ hnorm hYH
  have hHN : hY T L V₂ Y ≤ Subgroup.normalizer (R : Set G) :=
    sup_le (sup_le (le_sup_left.trans hXN) (le_sup_left.trans hYN')) (le_sup_right.trans hXN)
  exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hTH) hHN
    (C.hyp.fsu.sylow.1.to_le inf_le_left)

theorem thompsonJ_le_centralizer_F4 (h4 : Lemma14_7_4_two_three_F4)
    (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) (hsolv : Group.IsSolvable ↥(hY T L V₂ Y)) :
    thompsonJ T ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
  by_contra hJ
  set H := hY T L V₂ Y with hHdef
  have hVe : IsElemAbelian 2 (vH T L V V₂ Y) := (C.vH_le_center_F4 hQ).2
  have hred := C.isTwoReducedIn_vH_F4 hQ
  have hMN : H ≤ Subgroup.normalizer (vH T L V V₂ Y : Set G) := hred.2.1
  have hT : IsSylowTwoOf T H := C.isSylowTwoOf_T_F4 le_sup_right
  obtain ⟨I, -, hYeq, hcomm, hindep, hnat, hsup, hinf, hindepV, hperm⟩ :=
    B2F.structure_of_not_le_of_quot hVe hred (B2F.isSolvable_autI hVe hMN hsolv) hT hJ
  have hS : S1417.BlockSystem (autI hVe H) (autI hVe (thompsonJ H)) I :=
    ⟨hYeq, hcomm, hindep, hnat, hsup, hinf, hindepV, hperm⟩
  have hI : I.card ≤ 2 :=
    hS.card_le_two hVe hMN (stronglyQuasithin_of_pCoreOf_ne_bot C.hyp.fsu.qtke hQ)
  have hJH : thompsonJ H ≤ H := B6.thompsonJ_le H
  have hYX : autI hVe (thompsonJ H) ≤ autI hVe H := autI_mono hVe hJH
  have hXY := S1417.conjAut_autI_thompsonJ (V := vH T L V V₂ Y) (H := H) hVe

  have key : ∀ {a b : G}, a ∈ H → b ∈ thompsonJ H → Odd (orderOf a) → Odd (orderOf b) →
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
    intro a b ha hb hao hbo
    have haN := hMN ha
    have hbN := hMN (hJH hb)
    have hgo : Odd (orderOf (convI hVe ⟨a, haN⟩)) := hao.of_dvd_nat (by
      have := orderOf_map_dvd (convI hVe) ⟨a, haN⟩
      rwa [Subgroup.orderOf_mk] at this)
    have hko : Odd (orderOf (convI hVe ⟨b, hbN⟩)) := hbo.of_dvd_nat (by
      have := orderOf_map_dvd (convI hVe) ⟨b, hbN⟩
      rwa [Subgroup.orderOf_mk] at this)
    have hc := Blk.comm_of_odd hS hYX hI hXY (convI_mem_autI hVe ha haN) hgo
      (convI_mem_autI hVe hb hbN) hko
    have h1 : convI hVe (⟨a, haN⟩ * ⟨b, hbN⟩ * ⟨a, haN⟩⁻¹ * ⟨b, hbN⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    exact (convI_eq_one_iff hVe _).mp h1
  have hXsub : xL L V₂ ≤ H := le_sup_left.trans le_sup_left
  have hYsub : Y ≤ H := le_sup_right.trans le_sup_left

  have hXJ : ¬ xL L V₂ ≤ thompsonJ H := by
    intro hX
    exact C.not_le_normalizer_F4 (C.le_normalizer_of_comm_F4 fun x hx hxo y hy hyo =>
      key (hYsub hy) (hX hx) hyo hxo)
  have hYJ : ¬ Y ≤ thompsonJ H := by
    intro hYJ
    refine C.not_le_normalizer_F4 (C.le_normalizer_of_comm_F4 fun x hx hxo y hy hyo => ?_)
    have h1 := inv_mem (key (hXsub hx) (hYJ hy) hxo hyo)
    rwa [show (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ by group] at h1
  apply hJ
  calc thompsonJ T ≤ T ⊓ thompsonJ H :=
        le_inf (B6.thompsonJ_le T) (CFSG.Quasithin.thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
    _ ≤ pCoreOf 2 H := C.inf_le_pCoreOf_of_normal_F4 h4 (B6.le_normalizer_thompsonJ H) hXJ hYJ
    _ = T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) := C.pCoreOf_hY_eq_F4 h4 hQ
    _ ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) := inf_le_right

theorem le_normalizer_thompsonJ_F4 (h4 : Lemma14_7_4_two_three_F4)
    (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) (hsolv : Group.IsSolvable ↥(hY T L V₂ Y)) :
    hY T L V₂ Y ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
  have hJQ : thompsonJ T ≤ pCoreOf 2 (hY T L V₂ Y) := by
    rw [C.pCoreOf_hY_eq_F4 h4 hQ]
    exact le_inf (B6.thompsonJ_le T) (C.thompsonJ_le_centralizer_F4 h4 hQ hsolv)
  have he := B6.thompsonJ_eq_of_le hJQ (pCoreOf_le_of_le C.hyp le_sup_right)
  rw [← he]
  intro x hx
  exact CFSG.Quasithin.normalizer_le_normalizer_thompsonJ _ (le_normalizer_pCoreOf 2 _ hx)

end Ctx_F4

end CFSG.Quasithin.H13.L32A.T53
