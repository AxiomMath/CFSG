module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A513b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A53c
public import CFSG.Quasithin.Vol2.Ch6Vocab

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx_F4

variable {T L V V₂ Y : Subgroup G} (C : Ctx_F4 G T L V V₂ Y)
include C

theorem pCoreOf_xT_eq_F4 (hO : pCoreOf 2 (xL L V₂ ⊔ T) = pCoreOf 2 (Y ⊔ T)) :
    pCoreOf 2 (xL L V₂ ⊔ T) = pCoreOf 2 (hY T L V₂ Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXH : xL L V₂ ⊔ T ≤ hY T L V₂ Y := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hYH : Y ⊔ T ≤ hY T L V₂ Y := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hgen : hY T L V₂ Y = (xL L V₂ ⊔ T) ⊔ (Y ⊔ T) := by
    apply le_antisymm
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
        (le_sup_right.trans le_sup_right)
    · exact sup_le hXH hYH
  apply le_antisymm
  · refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hXH) ?_ (pCoreOf_isPGroup 2 _)
    rw [hgen]
    refine sup_le ?_ ?_
    · exact (Subgroup.le_normalizer).trans (normalizer_le_normalizer_pCoreOf 2 _)
    · rw [hO]
      exact (Subgroup.le_normalizer).trans (normalizer_le_normalizer_pCoreOf 2 _)
  · refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ (pCoreOf_isPGroup 2 _)
    · exact (pCoreOf_two_le_of_isSylowTwoOf (C.isSylowTwoOf_T_F4 (K := hY T L V₂ Y)
        le_sup_right)).trans le_sup_right
    · exact hXH.trans ((Subgroup.le_normalizer).trans (normalizer_le_normalizer_pCoreOf 2 _))

theorem relIndex_pCoreOf_xT_F4
    (hXS3 : quasithinO2QuotientIso (xL L V₂ ⊔ T) (Equiv.Perm (Fin 3))) :
    (pCoreOf 2 (xL L V₂ ⊔ T)).relIndex T = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := C.isSylowTwoOf_T_F4 (K := xL L V₂ ⊔ T) le_sup_right
  have h6 : (pCoreOf 2 (xL L V₂ ⊔ T)).relIndex (xL L V₂ ⊔ T) = 6 := by
    rw [U3.relIndex_pCoreOf_of_quot hXS3, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have h3 := U3.relIndex_eq_three_of_quot hXS3 hS
  have hOS : pCoreOf 2 (xL L V₂ ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hS
  have hm := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (xL L V₂ ⊔ T)) T (xL L V₂ ⊔ T) hOS hS.1
  rw [h6, h3] at hm
  omega

theorem inf_xT_le'_F4 (hXS3 : quasithinO2QuotientIso (xL L V₂ ⊔ T) (Equiv.Perm (Fin 3))) :
    (xL L V₂ ⊔ T) ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) ≤
      pCoreOf 2 (xL L V₂ ⊔ T) := by
  have hXH : xL L V₂ ⊔ T ≤ hY T L V₂ Y := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  refine le_pCoreOf_of_normal_of_S3 hXS3 inf_le_left ?_ ?_
  · intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx,
        CFSG.Quasithin.H13.L32A.T53.Ctx.le_normalizer_centralizer_vH hXH hx⟩
  · rw [C.oTwoUpper_xT_F4]
    intro h
    exact C.xL_not_le_centralizer_F4 (h.trans inf_le_right)

theorem not_thompsonJk_le_F4 (hXS3 : quasithinO2QuotientIso (xL L V₂ ⊔ T) (Equiv.Perm (Fin 3)))
    (hX1 : xL L V₂ = ⁅xL L V₂, thompsonJk 1 T⁆) :
    ¬ thompsonJk 1 T ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hJ
  have hJT : thompsonJk 1 T ≤ T := iSup₂_le fun A hA => hA.1
  have hJO : thompsonJk 1 T ≤ pCoreOf 2 (xL L V₂ ⊔ T) := fun g hg =>
    C.inf_xT_le'_F4 hXS3 ⟨Subgroup.mem_sup_right (hJT hg), hJ hg⟩
  have hXO' : ⁅xL L V₂, thompsonJk 1 T⁆ ≤ pCoreOf 2 (xL L V₂ ⊔ T) := by
    rw [Subgroup.commutator_le]
    intro x hx q hq
    have hqO := hJO hq
    have hxN : x ∈ Subgroup.normalizer (pCoreOf 2 (xL L V₂ ⊔ T) : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 _ (Subgroup.le_normalizer (Subgroup.mem_sup_left hx))
    rw [commutatorElement_def]
    exact (pCoreOf 2 _).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN q).mp hqO)
      ((pCoreOf 2 _).inv_mem hqO)
  have hXO : xL L V₂ ≤ pCoreOf 2 (xL L V₂ ⊔ T) := hX1.trans_le hXO'
  obtain ⟨z, a, x, hz, hz1, ha, haV, hx, hx3, hxz, hxa⟩ := C.exists_rot_X_F4
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (xL L V₂ ⊔ T) ⟨x, hXO hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd
    ((Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one hx3)) (orderOf_dvd_of_pow_eq_one hk')
  rw [orderOf_eq_one_iff] at h1
  apply haV
  rw [← hxz, h1, one_mul, inv_one, mul_one]
  exact hz

theorem inf_T_eq_F4 (hXS3 : quasithinO2QuotientIso (xL L V₂ ⊔ T) (Equiv.Perm (Fin 3)))
    (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) (hX1 : xL L V₂ = ⁅xL L V₂, thompsonJk 1 T⁆)
    (hO : pCoreOf 2 (xL L V₂ ⊔ T) = pCoreOf 2 (Y ⊔ T)) :
    T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) = pCoreOf 2 (hY T L V₂ Y) := by
  have hQX := C.pCoreOf_xT_eq_F4 hO
  have hQT : pCoreOf 2 (hY T L V₂ Y) ≤ T := by
    rw [← hQX]
    exact pCoreOf_two_le_of_isSylowTwoOf (C.isSylowTwoOf_T_F4 (K := xL L V₂ ⊔ T) le_sup_right)
  have hQC : pCoreOf 2 (hY T L V₂ Y) ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (((C.vH_le_center_F4 hQ).1 hw).2 q hq).symm
  have hle : pCoreOf 2 (hY T L V₂ Y) ≤ T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) :=
    le_inf hQT hQC
  have h2 := C.relIndex_pCoreOf_xT_F4 hXS3
  rw [hQX] at h2
  have hm := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (hY T L V₂ Y))
    (T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G)) T hle inf_le_left
  rw [h2] at hm
  have hne : (T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G)).relIndex T ≠ 1 := by
    intro h1
    apply C.not_thompsonJk_le_F4 hXS3 hX1
    have hTC : T ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) :=
      (Subgroup.relIndex_eq_one.mp h1).trans inf_le_right
    exact (iSup₂_le fun A hA => hA.1).trans hTC
  have h1 : (pCoreOf 2 (hY T L V₂ Y)).relIndex
      (T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ hm) with h | h
    · exact h
    · rw [h] at hm
      omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle

theorem exists_J1_F4 (hXS3 : quasithinO2QuotientIso (xL L V₂ ⊔ T) (Equiv.Perm (Fin 3)))
    (hX1 : xL L V₂ = ⁅xL L V₂, thompsonJk 1 T⁆) :
    ∃ A : Subgroup G, A ≤ T ∧ IsElemAbelian 2 A ∧
      (∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → Nat.card B ≤ 2 ^ 1 * Nat.card A) ∧
      ¬ A ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  apply C.not_thompsonJk_le_F4 hXS3 hX1
  exact iSup₂_le fun A hA => hcon A hA.1 hA.2.1 hA.2.2

theorem card_le_four_mul_F4 (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) {A : Subgroup G} (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A)
    (hmax : ∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → Nat.card B ≤ 2 ^ 1 * Nat.card A)
    (hA2 : (A ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G)).relIndex A = 2) :
    Nat.card (vH T L V V₂ Y) ≤
      4 * Nat.card ↥(vH T L V V₂ Y ⊓ Subgroup.centralizer (A : Set G)) := by
  set W := vH T L V V₂ Y with hW
  set A₀ := A ⊓ Subgroup.centralizer (W : Set G) with hA₀
  have hWe := (C.vH_le_center_F4 hQ).2
  have hWZ := (C.vH_le_center_F4 hQ).1
  have hWT : W ≤ T := fun w hw =>
    (pCoreOf_two_le_of_isSylowTwoOf (C.isSylowTwoOf_T_F4 (K := hY T L V₂ Y) le_sup_right))
      (hWZ hw).1
  have hcomm : ∀ a ∈ A₀, ∀ w ∈ W, a * w = w * a := fun a ha w hw =>
    (Subgroup.mem_centralizer_iff.mp ha.2 w hw).symm
  have hA₀e : IsElemAbelian 2 A₀ := B2F.isElemAbelian_mono inf_le_left hA
  have hBe : IsElemAbelian 2 (A₀ ⊔ W) := B2F.isElemAbelian_sup_of_commute hA₀e hWe hcomm
  have hBT : A₀ ⊔ W ≤ T := sup_le (inf_le_left.trans hAT) hWT
  have hcard := hmax _ hBT hBe
  have e1 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have e2 := Subgroup.relIndex_mul_card (H := A₀) (K := A)
  rw [inf_eq_left.mpr (inf_le_left : A₀ ≤ A), hA2] at e2
  have hle : A₀ ⊓ W ≤ W ⊓ Subgroup.centralizer (A : Set G) := by
    intro w hw
    refine ⟨hw.2, ?_⟩
    show w ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := hA.1.is_comm.comm ⟨a, ha⟩ ⟨w, hw.1.1⟩
    exact congrArg Subtype.val this
  have hc3 := Subgroup.card_le_of_le hle
  have hpos : 0 < Nat.card A₀ := Nat.card_pos
  have key : Nat.card A₀ * Nat.card W ≤ Nat.card A₀ * (4 * Nat.card ↥(W ⊓ Subgroup.centralizer
      (A : Set G))) := by
    calc Nat.card A₀ * Nat.card W = Nat.card ↥(A₀ ⊔ W) * Nat.card ↥(A₀ ⊓ W) := e1.symm
      _ ≤ (2 ^ 1 * Nat.card A) * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) :=
          Nat.mul_le_mul hcard hc3
      _ = Nat.card A₀ * (4 * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G))) := by
          rw [← e2]; ring
  exact Nat.le_of_mul_le_mul_left key hpos

end Ctx_F4

end CFSG.Quasithin.H13.L32A.T53

end
