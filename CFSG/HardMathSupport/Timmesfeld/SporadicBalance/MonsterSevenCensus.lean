module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenClasses
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenRank
public import CFSG.YGroups.Y443.Tri.Finiteness
public import Certificates.Certificate13694
public import Certificates.Certificate13695
public import Certificates.Certificate136300
public import Certificates.Certificate136301
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.AutGen

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus

open CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton.MON5_7 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenData CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow CFSG.HardMathSupport.Foote.E27 _root_.Timmesfeld.PcReg _root_.Timmesfeld.PcFus _root_.Timmesfeld.Mon7

theorem gw_powL' (k : ℕ) (w : List Native.Gen) : gw (powL k w) = gw w ^ k :=
  CFSG.KC.KDenseP.MonSeven.AutGen.gw_powL k w

theorem gw_Wrho (wo : List ℕ) : gw (Wrho wo) = (wo.map fun k => gw (wq[k]!)).prod :=
  CFSG.KC.KDenseP.MonSeven.AutGen.gw_Wrho wo

section Checks

@[expose, reducible] noncomputable def gq (k : ℕ) : Gmat := gw wq[k]!

theorem gw_targetW (b : Bool) : gw (targetW b) = if b then zG else dG := by
  cases b <;> rfl

theorem gq_pow {i : ℕ} (hi : i < 6) : gq i ^ 7 = 1 :=
  CFSG.KC.KDenseP.MonSeven.AutGen.gq_pow Certificates.certificate13695.1 hi

theorem gq_conj {i j : ℕ} (hi : i < 6) (hj : j < 6) (hij : i < j) :
    gq i * gq j * (gq i)⁻¹ = (((wordOfVec 6 (cw7[i * 6 + j]!)).map gq).prod) :=
  CFSG.KC.KDenseP.MonSeven.AutGen.gq_conj Certificates.certificate13695.1 hi hj hij

theorem gq_aut {a i : ℕ} (ha : a < 2) (hi : i < 6) :
    gw autW[a]! * gq i * (gw autW[a]!)⁻¹ =
      (((wordOfVec 6 ((alphaVecs[a]!)[i]!)).map gq).prod) := by
  have h := agreeAll_sound (Certificates.certificate13695.2.1)
    (wq[i]! ++ autW[a]!, autW[a]! ++ Wrho (wordOfVec 6 ((alphaVecs[a]!)[i]!)))
    (by
      unfold autPairs
      exact List.mem_flatMap.2
        ⟨a, List.mem_range.2 ha, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩⟩)
  rw [gw_append, gw_append, gw_Wrho] at h
  rw [mul_inv_eq_iff_eq_mul]
  exact h

theorem orb_conj {k : ℕ}
    (hk : k < 22) :
    IsConj (gw (Wrho orbWord[k]!)) (if orbKind[k]! then zG else dG) := by
  have h : gw (Wrho orbWord[k]! ++ orbT[k]!) = gw (orbT[k]! ++ targetW orbKind[k]!) := by
    by_cases hk11 : k < 11
    · exact agreeAll_sound (Certificates.certificate136300)
        (Wrho orbWord[k]! ++ orbT[k]!, orbT[k]! ++ targetW orbKind[k]!)
        (List.mem_map.2 ⟨k, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩)
    · exact agreeAll_sound (Certificates.certificate136301)
        (Wrho orbWord[k]! ++ orbT[k]!, orbT[k]! ++ targetW orbKind[k]!)
        (List.mem_map.2 ⟨k, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩)
  rw [gw_append, gw_append, gw_targetW] at h
  refine isConj_iff.2 ⟨gw orbT[k]!, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact h

end Checks

theorem conj_pow_three_pow {T : Gmat} {c : Gmat} (h : c * T * c⁻¹ = T ^ 3) :
    ∀ m : ℕ, ∃ d : Gmat, d * T * d⁻¹ = T ^ (3 ^ m)
  | 0 => ⟨1, by simp⟩
  | m + 1 => by
    obtain ⟨d, hd⟩ := conj_pow_three_pow h m
    refine ⟨c * d, ?_⟩
    calc c * d * T * (c * d)⁻¹ = c * (d * T * d⁻¹) * c⁻¹ := by group
      _ = c * T ^ (3 ^ m) * c⁻¹ := by rw [hd]
      _ = (c * T * c⁻¹) ^ (3 ^ m) := (conj_pow).symm
      _ = (T ^ 3) ^ (3 ^ m) := by rw [h]
      _ = T ^ (3 ^ (m + 1)) := by rw [← pow_mul, pow_succ, mul_comm]

theorem isConj_pow_of_coprime {T : Gmat} (hT : T ^ 7 = 1) {c : Gmat} (h : c * T * c⁻¹ = T ^ 3)
    {k : ℕ} (hk : Nat.Coprime k 7) : IsConj T (T ^ k) := by
  have hk7 : k % 7 ≠ 0 := fun h0 => by
    have : 7 ∣ k := Nat.dvd_of_mod_eq_zero h0
    have := Nat.Coprime.eq_one_of_dvd hk.symm this
    omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 3 ^ m % 7 = k % 7 := by
    have : k % 7 < 7 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : k % 7
    · exact absurd rfl hk7
    · exact ⟨0, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨4, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨3, by norm_num⟩
  obtain ⟨d, hd⟩ := conj_pow_three_pow h m
  refine isConj_iff.2 ⟨d, ?_⟩
  rw [hd, pow_eq_pow_mod _ hT, hm, ← pow_eq_pow_mod _ hT]

@[expose] def Cl (x : Gmat) : Prop := IsConj x dG ∨ IsConj x zG

section Rat

theorem rat_dG : ∃ c : Gmat, c * dG * c⁻¹ = dG ^ 3 := by
  have h := agreeAll_sound (Certificates.certificate13695.2.2)
    (dW ++ ratDW, ratDW ++ powL 3 dW) (by simp [ratPairs])
  rw [gw_append, gw_append, gw_powL'] at h
  exact ⟨gw ratDW, by rw [mul_inv_eq_iff_eq_mul]; exact h⟩

theorem rat_zG : ∃ c : Gmat, c * zG * c⁻¹ = zG ^ 3 := by
  have h := agreeAll_sound (Certificates.certificate13695.2.2)
    (zW ++ ratZW, ratZW ++ powL 3 zW) (by simp [ratPairs])
  rw [gw_append, gw_append, gw_powL'] at h
  exact ⟨gw ratZW, by rw [mul_inv_eq_iff_eq_mul]; exact h⟩

end Rat

section Closure

variable (hd : dG ^ 7 = 1) (hz : zG ^ 7 = 1)
  (rd : ∃ c : Gmat, c * dG * c⁻¹ = dG ^ 3) (rz : ∃ c : Gmat, c * zG * c⁻¹ = zG ^ 3)

include hd hz rd rz

theorem Cl_pow {x : Gmat} (_hx : x ^ 7 = 1) {k : ℕ} (hk : Nat.Coprime k 7) (h : Cl x) :
    Cl (x ^ k) := by
  rcases h with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    obtain ⟨e, he⟩ := rd
    left
    refine (isConj_iff.2 ⟨c, ?_⟩).trans (isConj_pow_of_coprime hd he hk).symm
    rw [← conj_pow, hc]
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    obtain ⟨e, he⟩ := rz
    right
    refine (isConj_iff.2 ⟨c, ?_⟩).trans (isConj_pow_of_coprime hz he hk).symm
    rw [← conj_pow, hc]

theorem Cl_of_pow {x : Gmat} (hx : x ^ 7 = 1) {k : ℕ} (hk : Nat.Coprime k 7) (h : Cl (x ^ k)) :
    Cl x := by
  obtain ⟨k', -, hk'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk (by norm_num)
  have hc : Nat.Coprime k' 7 := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).2 fun hdv => ?_)
    have : 7 ∣ k * k' := Dvd.dvd.mul_left hdv k
    omega
  have hxk : (x ^ k) ^ 7 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]
  have e : (x ^ k) ^ k' = x := by
    rw [← pow_mul, pow_eq_pow_mod _ hx, hk', pow_one]
  rw [← e]
  exact Cl_pow hd hz rd rz hxk hc h

end Closure

theorem orbWord_targets : ∀ t ∈ CFSG.KC.MonPcSeven.targets,
    ∃ k < 22, orbWord[k]! = CFSG.KC.KDenseP.MonSeven.AutGen.vWord (CFSG.KC.MonPcSeven.dec t) := by
  decide +kernel

section Model

@[expose, reducible] noncomputable def qR : Fin 4 → Gmat := fun i => gq (i.val + 1)

theorem gq_comm_five {i : ℕ} (hi : i < 5) : gq i * gq 5 = gq 5 * gq i :=
  CFSG.KC.KDenseP.MonSeven.AutGen.gq_comm_five Certificates.certificate13695.1 hi

theorem pcHyp_gq : CFSG.KC.MonPcSeven.PcHyp (gq 0) qR (gq 5) :=
  CFSG.KC.KDenseP.MonSeven.AutGen.pcHyp_gq Certificates.certificate13695.1

theorem autRel_gq {j : ℕ} (hj : j < 2) :
    CFSG.KC.MonPcSeven.AutRel (gq 0) qR (gq 5) (gw autW[j]!) (CFSG.KC.MonPcSeven.autAt j) := by
  have h : ∀ i < 6, gw autW[j]! * gq i * (gw autW[j]!)⁻¹ = CFSG.KC.BM.PcFive.psi (gq 0) qR (gq 5)
      (CFSG.KC.MonPcSeven.dec (CFSG.KC.BM.PcFive.nth (CFSG.KC.MonPcSeven.autAt j) i)) :=
    fun i hi => by
      rw [gq_aut hj hi, CFSG.KC.KDenseP.MonSeven.AutGen.wordOfVec_aut j hj i hi,
        CFSG.KC.KDenseP.MonSeven.AutGen.prod_vWord]
  exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num), h 5 (by norm_num)⟩

theorem isConj_gq_five :
    IsConj (gq 5) zG := by
  have h0 := orb_conj (k := 0) (by norm_num)
  have e : gw (Wrho orbWord[0]!) = gq 5 := by
    have : orbWord[0]! = [5] := by decide +kernel
    rw [this, gw_Wrho]
    simp [gq]
  have hk : orbKind[0]! = true := by decide +kernel
  rw [e, hk, ite_eq_left rfl] at h0
  exact h0

theorem gq_five_ne_one :
    gq 5 ≠ 1 := by
  intro h1
  have h := isConj_gq_five
  rw [h1, isConj_one_right] at h
  exact zG_ne_one h

theorem card_PSub_gq [Finite Gmat] :
    Nat.card (CFSG.KC.BM.PcFive.PSub (gq 0) qR) = 7 ^ 6 :=
  CFSG.KC.MonPcSeven.card_P pcHyp_gq gq_five_ne_one

theorem cl_targets :
    ∀ t ∈ CFSG.KC.MonPcSeven.targets,
    Cl (CFSG.KC.BM.PcFive.psi (gq 0) qR (gq 5) (CFSG.KC.MonPcSeven.dec t)) := by
  intro t ht
  obtain ⟨k, hk, hw⟩ := orbWord_targets t ht
  have h := orb_conj hk
  rw [gw_Wrho, hw] at h
  rw [← CFSG.KC.KDenseP.MonSeven.AutGen.prod_vWord]
  unfold Cl
  split_ifs at h
  · exact Or.inr h
  · exact Or.inl h

end Model

section Main

theorem monsterSevenClasses : MonsterSevenClasses dG zG := by
  have hd : dG ^ 7 = 1 := dG_pow
  have hz : zG ^ 7 = 1 := zG_pow
  have rd := rat_dG
  have rz := rat_zG
  have hcardG : Nat.card Gmat = 7 ^ 6 * (2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 *
      29 * 31 * 41 * 47 * 59 * 71) := by
    rw [natCard_Gmat_eq_monsterOrder]
    norm_num [CFSG.Open.monsterOrder]
  have : Finite Gmat := Nat.finite_of_card_ne_zero (by rw [hcardG]; positivity)
  have hm7 : ¬ 7 ∣ (2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 *
      59 * 71) := by norm_num
  intro s hs
  refine Certificates.certificate13694 pcHyp_gq gq_five_ne_one hcardG hm7 Cl
    (fun x c hx => ?_) (fun x hx k hk => ⟨Cl_of_pow hd hz rd rz hx hk, Cl_pow hd hz rd rz hx hk⟩)
    (fun j hj => ⟨_, autRel_gq hj⟩) cl_targets s hs
  have hc : IsConj (c * x * c⁻¹) x := isConj_iff.2 ⟨c⁻¹, by group⟩
  rcases hx with h | h
  · exact Or.inl (hc.trans h)
  · exact Or.inr (hc.trans h)

end Main

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
