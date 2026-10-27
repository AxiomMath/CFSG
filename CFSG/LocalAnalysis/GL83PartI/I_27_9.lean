module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Orbits
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.GenAlt

public section

namespace GL83.PiGen

open GL83.CompFam CFSG.Open

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem le_glbCore_of_centGenI {B K : Subgroup X} (hB : IsElemAbelian p B)
    (hK : IsComponentOf K ⊤) (hgen : K ≤ centGenI p (stab B K) K) :
    K ≤ GLBCore p (pRank p B - 1) B := by
  have hp := (Fact.out : p.Prime)
  have hF := isFam_conjSet hB hK
  have hK₀ := mem_conjSet_self B K
  have hAB : stab B K ≤ B := inf_le_left
  set t := (stab B K).relIndex B with ht
  have hBt : Nat.card B = t * Nat.card (stab B K) := by
    have h := Subgroup.relIndex_mul_card (H := stab B K) (K := B)
    rw [inf_eq_left.2 hAB] at h
    exact h.symm
  have hBp := card_eq_pow_pRank hB
  obtain ⟨a, -, hta⟩ : ∃ a ≤ pRank p B, t = p ^ a := by
    refine (Nat.dvd_prime_pow hp).1 ?_
    rw [← hBp, hBt]
    exact Dvd.intro _ rfl
  have hlay := hF.layer_le_centGenI a hK₀ (by rw [hBt, hta]) hgen
  refine (le_layer hK₀).trans (hlay.trans (iSup_le fun E => ?_))
  obtain ⟨hEB, hEi⟩ := E.2
  have hEel : IsElemAbelian p E.1 := elem_mono hB hEB
  obtain ⟨j, hj⟩ := exists_card_eq_pow hEel
  have hjr : pRank p B - 1 ≤ j := by
    have h1 : p ^ pRank p B ≤ p ^ (j + 1) := by
      calc p ^ pRank p B = Nat.card B := hBp.symm
        _ ≤ p * Nat.card E.1 := hEi
        _ = p ^ (j + 1) := by rw [hj, pow_succ, mul_comm]
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    omega
  have hrk : j ≤ pRank p E.1 := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEel hj
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (E.1 : Set X)).trans
    (le_sSup ⟨E.1, hEB, hjr.trans hrk, rfl⟩))

theorem le_glbCore_of_alt (hp3 : 3 ≤ p) {B K : Subgroup X} {k n : ℕ} (hk : 1 ≤ k)
    (hnk : n = k * p + 2) (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (hB : IsElemAbelian p B)
    (hK : IsComponentOf K ⊤) (hZ : Subgroup.center K = ⊥)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hrank : GLATwoLocalRank p X ≤ pRank p B) : K ≤ GLBCore p (pRank p B - 1) B := by
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  refine le_glbCore_of_centGenI hB hK ?_
  have hodd : Odd (Nat.card (Subgroup.center K)) := by
    rw [hZ]
    simp
  have hnp : n % p = 2 := by
    rw [hnk, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  exact le_centGenI_of_orbits hp3 (stab_le_normalizer B K)
    (isPGroup_of_elem (elem_mono hB inf_le_left)) hodd hn5 hn6 e hnp
    (fun ω => orbit_card_le hp3 hk hnk hn5 hn6 hB hK hZ e hrank ω)

end GL83.PiGen
