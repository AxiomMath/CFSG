module

public import CFSG.ClassicalInvolution.Asc77.AscT8T3
public import CFSG.ClassicalInvolution.Asc77.AscT8YB2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Balance.Theorem5

namespace T8YY

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J W : Subgroup G} {z t : G}

namespace FrameData

theorem mul_ne_oneE (F : FrameData Ω W K J z t) (i j : Fin 4) (hij : i ≠ j) :
    F.zz i * F.zz j ≠ 1 := by
  intro h
  have : F.zz i = F.zz j := by
    have h' := congrArg (· * F.zz j) h
    simpa [mul_assoc, (F.hz j).sq] using h'
  exact F.hinj i j hij this

end FrameData

theorem alphaOf_vGroup_eqE (F : FrameData Ω W K J z t)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {R₃ : Fin 3 → Subgroup G}
    (hF : T8T.TriFrame Ω ![K, J, (F.ρ 2).K] ![z, t, F.zz 2] R₃)
    (hHyp : Hyp51 (Subgroup.closure ({z, t, F.zz 2} : Set G)))
    (hc01 : z * t = t * z) (hc02 : z * F.zz 2 = F.zz 2 * z) (hc12 : t * F.zz 2 = F.zz 2 * t)
    (V : Subgroup G) (hVdef : V = Subgroup.closure ({F.zz 0 * F.zz 1, F.zz 0 * F.zz 2} : Set G)) :
    IsElemAbelian2 V 2 ∧ alphaOf V = alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  have hz2 : z * z = 1 := hF.sq 0
  have ht2 : t * t = 1 := hF.sq 1
  have hw2 : F.zz 2 * F.zz 2 = 1 := hF.sq 2
  have hz1 : z ≠ 1 := hF.ne_one 0
  have ht1 : t ≠ 1 := hF.ne_one 1
  have hzt : z ≠ t := hF.x_ne hnt (i := 0) (j := 1) (by decide)
  have hDB : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, t, F.zz 2} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair ht2 hz2 ht1 hz1 hzt.symm hc01.symm
  have h3 : ∀ A : Subgroup G, A ≤ Subgroup.closure ({z, t, F.zz 2} : Set G) →
      IsElemAbelian2 A 2 → alphaOf A = alphaOf (Subgroup.closure ({t, z} : Set G)) :=
    (lemma54_odd_and_eq hHyp hDB hD).2
  have hzB : z ∈ Subgroup.closure ({z, t, F.zz 2} : Set G) :=
    Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, t, F.zz 2} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hwB : F.zz 2 ∈ Subgroup.closure ({z, t, F.zz 2} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hztB : z * t ∈ Subgroup.closure ({z, t, F.zz 2} : Set G) := Subgroup.mul_mem _ hzB htB
  have hzwB : z * F.zz 2 ∈ Subgroup.closure ({z, t, F.zz 2} : Set G) :=
    Subgroup.mul_mem _ hzB hwB
  have hVB : V ≤ Subgroup.closure ({z, t, F.zz 2} : Set G) := by
    rw [hVdef, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · rw [F.hz0, F.hz1]; exact hztB
    · rw [F.hz0]; exact hzwB
  have hVa : (F.zz 0 * F.zz 1) * (F.zz 0 * F.zz 1) = 1 := by
    rw [F.hz0, F.hz1]; exact T8.mul_self_of_commute hz2 ht2 hc01
  have hVb : (F.zz 0 * F.zz 2) * (F.zz 0 * F.zz 2) = 1 := by
    rw [F.hz0]; exact T8.mul_self_of_commute hz2 hw2 hc02
  have hVcomm : (F.zz 0 * F.zz 1) * (F.zz 0 * F.zz 2) = (F.zz 0 * F.zz 2) * (F.zz 0 * F.zz 1) := by
    rw [F.hz0, F.hz1]
    have h1 : Commute (z * t) z :=
      Commute.mul_left (Commute.refl z) (show Commute t z from hc01.symm)
    have h2 : Commute (z * t) (F.zz 2) :=
      Commute.mul_left (show Commute z (F.zz 2) from hc02) (show Commute t (F.zz 2) from hc12)
    exact (Commute.mul_right h1 h2).eq
  have hV : IsElemAbelian2 V 2 := by
    rw [hVdef]; exact T7A.isElemAbelian2_closure_pair hVa hVb (F.mul_ne_oneE 0 1 (by decide))
      (F.mul_ne_oneE 0 2 (by decide))
      (fun h => F.hinj 1 2 (by decide) (mul_left_cancel h)) hVcomm
  exact ⟨hV, h3 _ hVB hV⟩

theorem alphaOf_oddE (F : FrameData Ω W K J z t)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {R₃ : Fin 3 → Subgroup G}
    (hF : T8T.TriFrame Ω ![K, J, (F.ρ 2).K] ![z, t, F.zz 2] R₃)
    (hHyp : Hyp51 (Subgroup.closure ({z, t, F.zz 2} : Set G))) (hc01 : z * t = t * z) :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({t, z} : Set G)))) := by
  have hz2 : z * z = 1 := hF.sq 0
  have ht2 : t * t = 1 := hF.sq 1
  have hz1 : z ≠ 1 := hF.ne_one 0
  have ht1 : t ≠ 1 := hF.ne_one 1
  have hzt : t ≠ z := (hF.x_ne hnt (i := 0) (j := 1) (by decide)).symm
  have hDB : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, t, F.zz 2} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair ht2 hz2 ht1 hz1 hzt hc01.symm
  exact (lemma54_odd_and_eq hHyp hDB hD).1

theorem centralizer_le_normalizer_alpha_of_frattiniE (F : FrameData Ω W K J z t)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {R₃ : Fin 3 → Subgroup G}
    (hF : T8T.TriFrame Ω ![K, J, (F.ρ 2).K] ![z, t, F.zz 2] R₃)
    (hind : F.zz 2 ∉ Subgroup.closure ({z, t} : Set G))
    (hHyp : Hyp51 (Subgroup.closure ({z, t, F.zz 2} : Set G)))
    (hc01 : z * t = t * z) (hc02 : z * F.zz 2 = F.zz 2 * z) (hc12 : t * F.zz 2 = F.zz 2 * t)
    (V : Subgroup G) (hVdef : V = Subgroup.closure ({F.zz 0 * F.zz 1, F.zz 0 * F.zz 2} : Set G))
    {Y : Subgroup G} (hoY : oddCoreOf Y ≤ oddCoreOf (Subgroup.centralizer ({z * t} : Set G)))
    (hfr : ∀ c ∈ Subgroup.centralizer ({z * t} : Set G),
      ∃ o ∈ oddCoreOf Y, conjSub (o * c) V = V) :
    Subgroup.centralizer ({z * t} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hz2 : z * z = 1 := hF.sq 0
  have ht2 : t * t = 1 := hF.sq 1
  have hw2 : F.zz 2 * F.zz 2 = 1 := hF.sq 2
  have hz1 : z ≠ 1 := hF.ne_one 0
  have ht1 : t ≠ 1 := hF.ne_one 1
  have hw1 : F.zz 2 ≠ 1 := hF.ne_one 2
  have hzt : z ≠ t := hF.x_ne hnt (i := 0) (j := 1) (by decide)
  have hB : IsElemAbelian 2 (Subgroup.closure ({z, t, F.zz 2} : Set G)) :=
    T8T.isElemAbelian_closure_three hz2 ht2 hw2 hc01 hc02 hc12
  have hB8 : Nat.card ↥(Subgroup.closure ({z, t, F.zz 2} : Set G)) = 8 :=
    T8T.natCard_closure_three hz2 ht2 hw2 hc01 hc02 hc12 hz1 ht1 hzt hw1 (by simpa using hind)
  have hDB : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, t, F.zz 2} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair ht2 hz2 ht1 hz1 hzt.symm hc01.symm
  have h3 : ∀ A : Subgroup G, A ≤ Subgroup.closure ({z, t, F.zz 2} : Set G) →
      IsElemAbelian2 A 2 → alphaOf A = alphaOf (Subgroup.closure ({t, z} : Set G)) :=
    (lemma54_odd_and_eq hHyp hDB hD).2
  have hzB : z ∈ Subgroup.closure ({z, t, F.zz 2} : Set G) :=
    Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, t, F.zz 2} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hwB : F.zz 2 ∈ Subgroup.closure ({z, t, F.zz 2} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hztB : z * t ∈ Subgroup.closure ({z, t, F.zz 2} : Set G) := Subgroup.mul_mem _ hzB htB
  have hzwB : z * F.zz 2 ∈ Subgroup.closure ({z, t, F.zz 2} : Set G) :=
    Subgroup.mul_mem _ hzB hwB
  have hVB : V ≤ Subgroup.closure ({z, t, F.zz 2} : Set G) := by
    rw [hVdef, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · rw [F.hz0, F.hz1]; exact hztB
    · rw [F.hz0]; exact hzwB
  have hVa : (F.zz 0 * F.zz 1) * (F.zz 0 * F.zz 1) = 1 := by
    rw [F.hz0, F.hz1]; exact T8.mul_self_of_commute hz2 ht2 hc01
  have hVb : (F.zz 0 * F.zz 2) * (F.zz 0 * F.zz 2) = 1 := by
    rw [F.hz0]; exact T8.mul_self_of_commute hz2 hw2 hc02
  have hVcomm : (F.zz 0 * F.zz 1) * (F.zz 0 * F.zz 2) = (F.zz 0 * F.zz 2) * (F.zz 0 * F.zz 1) := by
    rw [F.hz0, F.hz1]
    have h1 : Commute (z * t) z :=
      Commute.mul_left (Commute.refl z) (show Commute t z from hc01.symm)
    have h2 : Commute (z * t) (F.zz 2) :=
      Commute.mul_left (show Commute z (F.zz 2) from hc02) (show Commute t (F.zz 2) from hc12)
    exact (Commute.mul_right h1 h2).eq
  have hV : IsElemAbelian2 V 2 := by
    rw [hVdef]; exact T7A.isElemAbelian2_closure_pair hVa hVb (F.mul_ne_oneE 0 1 (by decide))
      (F.mul_ne_oneE 0 2 (by decide))
      (fun h => F.hinj 1 2 (by decide) (mul_left_cancel h)) hVcomm
  have hαV : alphaOf V = alphaOf (Subgroup.closure ({t, z} : Set G)) := h3 _ hVB hV
  intro c hc
  obtain ⟨o, ho, hn⟩ := hfr c hc
  have hoN : o ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) :=
    T8T.oddCoreOf_centralizer_le_normalizer hB hB8 hztB h3 (hoY ho)
  have hnN : o * c ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, ← hαV, ← alphaOf_conjSub, hn]
  have hc' : c = o⁻¹ * (o * c) := by group
  rw [hc']
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hoN) hnN

end T8YY

end CFSG.ClassicalInvolution.Asc77
