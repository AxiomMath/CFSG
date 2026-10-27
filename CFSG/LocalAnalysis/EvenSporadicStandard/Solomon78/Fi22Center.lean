module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.AutModelRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Classes
public import Certificates.Certificate25611
public import Certificates.Certificate25612

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.Fi22

theorem centerInv_fi22_rep
    {k : ℕ} (hk : k < 3) :
    ∀ z ∈ fi22P, z * z = 1 → z * fi22ExtRep k = fi22ExtRep k * z →
      (∀ y ∈ fi22P, y * fi22ExtRep k = fi22ExtRep k * y → z * y = y * z) →
      z = 1 ∨ z = fi22ExtRep k :=
  Certificates.certificate25611.1 k hk

theorem centerInv_fi22 :
    ∀ a ∈ fi22P, orderOf a = 2 → ∀ z ∈ fi22P, z * z = 1 → z * a = a * z →
      (∀ y ∈ fi22P, y * a = a * y → z * y = y * z) → z = 1 ∨ z = a := by
  intro a ha ha2
  obtain ⟨r, hr, c, hc, har⟩ := cover_P a ha ha2
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
  exact centerInv_conj hc har (centerInv_fi22_rep (List.mem_range.1 hk))

theorem centerInv_fi22_outer_rep
    {k : ℕ} (hk3 : 3 ≤ k) (hk : k < 5) :
    ∀ z ∈ fi22R, z * z = 1 → z * fi22ExtRep k = fi22ExtRep k * z →
      (∀ y ∈ fi22R, y * fi22ExtRep k = fi22ExtRep k * y → z * y = y * z) →
      z = 1 ∨ z = fi22ExtRep k :=
  Certificates.certificate25611.2 k hk3 hk

theorem card_fixSubgroup_eq {M : Type} [Group M] {P : Subgroup M} {α : MulAut ↥P} {w : M}
    (hα : ∀ p : P, ((α p : P) : M) = w * p * w⁻¹) :
    Nat.card ↥(fixSubgroup α) = Nat.card ↥(centralizerIn P w) := by
  refine Nat.card_congr
    { toFun := fun p => ⟨(p.1 : M), p.1.2, mem_centralizer_singleton_iff.2 (by
        have := hα p.1
        have h2 : ((α p.1 : P) : M) = (p.1 : M) := congrArg Subtype.val p.2
        rw [h2] at this
        calc (p.1 : M) * w = (w * (p.1 : M) * w⁻¹) * w := by rw [← this]
          _ = w * (p.1 : M) := by group)⟩
      invFun := fun p => ⟨⟨(p.1 : M), (mem_centralizerIn.1 p.2).1⟩, by
        have h1 : (p.1 : M) * w = w * (p.1 : M) := (mem_centralizerIn.1 p.2).2
        apply Subtype.ext
        show ((α ⟨(p.1 : M), (mem_centralizerIn.1 p.2).1⟩ : P) : M) = (p.1 : M)
        rw [hα]
        calc w * (p.1 : M) * w⁻¹ = (p.1 : M) * w * w⁻¹ := by rw [h1]
          _ = p.1 := by group⟩
      left_inv := fun p => rfl
      right_inv := fun p => rfl }

theorem fi22_outerCentre
    (α : MulAut ↥fi22P) (w : Equiv.Perm (Fin 3510)) (hw : w ∈ fi22R) (hwP : w ∉ fi22P)
    (hα : ∀ p : fi22P, ((α p : fi22P) : Equiv.Perm (Fin 3510)) = w * p * w⁻¹)
    (hww : w * w = 1) (z : Equiv.Perm (Fin 3510)) (hz : z ∈ fi22P) (hz2 : orderOf z = 2)
    (hzw : z * w = w * z) (hall : ∀ y ∈ fi22P, y * w = w * y → y * z = z * y) :
    Nat.card (fixSubgroup α) = 2903040 := by
  have hw1 : w ≠ 1 := fun e => hwP (e ▸ fi22P.one_mem)
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
  have hzz : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  obtain ⟨k, hk3, hk6, g, hg, rfl⟩ := cover_outer hw hw2 hwP
  rw [card_fixSubgroup_eq hα]
  by_cases hk5 : k = 5
  · subst hk5
    rw [← Nat.card_congr (centralizerInConjEquiv fi22P hg (fi22ExtRep 5)).toEquiv]
    rw [show 5 = 3 + 2 from rfl, card_centralizerIn_P_outer (k := 2) (by norm_num)]
    rfl
  · exfalso
    have hk : k < 5 := by omega
    have htR : fi22ExtRep k ∈ fi22R ∧ fi22ExtRep k ∉ fi22P := by
      have := (CTUC_Fi22_all_extension_involutions_covered.2.1 (k - 3) (by omega))
      rwa [show 3 + (k - 3) = k by omega] at this
    obtain ⟨htR, htP⟩ := htR
    have htt : fi22ExtRep k * fi22ExtRep k = 1 :=
      mul_self_eq_one_of_orderOf_eq_two (orderOf_fi22ExtRep hk6)
    have hz'P : g⁻¹ * z * g ∈ fi22P := fi22P.mul_mem (fi22P.mul_mem (fi22P.inv_mem hg) hz) hg
    have hz'z' : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
      calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [hzz]; group
    have hz't : (g⁻¹ * z * g) * fi22ExtRep k = fi22ExtRep k * (g⁻¹ * z * g) := by
      calc (g⁻¹ * z * g) * fi22ExtRep k = g⁻¹ * (z * (g * fi22ExtRep k * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * fi22ExtRep k * g⁻¹) * z) * g := by rw [hzw]
        _ = fi22ExtRep k * (g⁻¹ * z * g) := by group
    have hP : ∀ y ∈ fi22P, y * fi22ExtRep k = fi22ExtRep k * y →
        (g⁻¹ * z * g) * y = y * (g⁻¹ * z * g) := by
      intro y hy hyt
      have hy' : g * y * g⁻¹ ∈ fi22P := fi22P.mul_mem (fi22P.mul_mem hg hy) (fi22P.inv_mem hg)
      have h2 := hall (g * y * g⁻¹) hy' (by
        calc g * y * g⁻¹ * (g * fi22ExtRep k * g⁻¹) = g * (y * fi22ExtRep k) * g⁻¹ := by group
          _ = g * (fi22ExtRep k * y) * g⁻¹ := by rw [hyt]
          _ = (g * fi22ExtRep k * g⁻¹) * (g * y * g⁻¹) := by group)
      calc (g⁻¹ * z * g) * y = g⁻¹ * (z * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * z) * g := by rw [← h2]
        _ = y * (g⁻¹ * z * g) := by group
    have hcent : ∀ y ∈ fi22R, y * fi22ExtRep k = fi22ExtRep k * y →
        (g⁻¹ * z * g) * y = y * (g⁻¹ * z * g) := by
      intro y hy hyt
      by_cases hyP : y ∈ fi22P
      · exact hP y hyP hyt
      · have h0 : (fi22ExtRep k)⁻¹ * y ∈ fi22P := fi22_index_two _ htR htP y hy hyP
        have h1 : ((fi22ExtRep k)⁻¹ * y) * fi22ExtRep k =
            fi22ExtRep k * ((fi22ExtRep k)⁻¹ * y) := by
          calc ((fi22ExtRep k)⁻¹ * y) * fi22ExtRep k = (fi22ExtRep k)⁻¹ * (y * fi22ExtRep k) := by
                group
            _ = (fi22ExtRep k)⁻¹ * (fi22ExtRep k * y) := by rw [hyt]
            _ = fi22ExtRep k * ((fi22ExtRep k)⁻¹ * y) := by
              have : (fi22ExtRep k)⁻¹ = fi22ExtRep k := inv_eq_of_mul_eq_one_right htt
              rw [this]
        have h2 := hP _ h0 h1
        have hti : (fi22ExtRep k)⁻¹ = fi22ExtRep k := inv_eq_of_mul_eq_one_right htt
        rw [hti] at h2
        calc (g⁻¹ * z * g) * y = (g⁻¹ * z * g) * (fi22ExtRep k * (fi22ExtRep k * y)) := by
              rw [← mul_assoc (fi22ExtRep k), htt, one_mul]
          _ = ((g⁻¹ * z * g) * fi22ExtRep k) * (fi22ExtRep k * y) := by group
          _ = (fi22ExtRep k * (g⁻¹ * z * g)) * (fi22ExtRep k * y) := by rw [hz't]
          _ = fi22ExtRep k * ((g⁻¹ * z * g) * (fi22ExtRep k * y)) := by group
          _ = fi22ExtRep k * ((fi22ExtRep k * y) * (g⁻¹ * z * g)) := by rw [h2]
          _ = (fi22ExtRep k * fi22ExtRep k) * y * (g⁻¹ * z * g) := by group
          _ = y * (g⁻¹ * z * g) := by rw [htt, one_mul]
    rcases centerInv_fi22_outer_rep hk3 hk _ (fi22P_le_R hz'P) hz'z' hz't hcent with h | h
    · apply ne_one_of_orderOf_eq_two hz2
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · apply hwP
      have : g * fi22ExtRep k * g⁻¹ = z := by
        calc g * fi22ExtRep k * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h]
          _ = z := by group
      rw [this]
      exact hz

theorem exists_commuting_rep_fi22
    {i j : ℕ} (hi : i < 3) (hj : j < 6) :
    ∃ x ∈ fi22P, (x * fi22ExtRep i * x⁻¹) * fi22ExtRep j =
      fi22ExtRep j * (x * fi22ExtRep i * x⁻¹) := by
  have h := Certificates.certificate25612
  simp only [fi22UmovData, List.all_eq_true, List.mem_range] at h
  exact umovWit_spec (fun T g hT hs => (siftP_iff hT).1 hs) (rep_tT (by omega))
    (rep_tT hj) (h i hi j hj)

theorem exists_commuting_fi22 :
    ∀ u ∈ fi22P, orderOf u = 2 → ∀ w ∈ fi22R, w * w = 1 →
      ∃ x ∈ fi22P, (x * u * x⁻¹) * w = w * (x * u * x⁻¹) :=
  exists_commuting_conj_of_cover (P := fi22P) (R := fi22R) ((List.range 3).map fi22ExtRep)
    ((List.range 6).map fi22ExtRep) cover_P cover_R
    (fun r hr c hc => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
      exact exists_fi22P_conj (k := k) (by have := List.mem_range.1 hk; omega) hc)
    (fun r hr r' hr' => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr'
      exact exists_commuting_rep_fi22 (List.mem_range.1 hk) (List.mem_range.1 hj))
    fi22P_le_R

end CFSG.EvenSporadicStandard.Solomon78
