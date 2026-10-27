module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HACheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HACheckK
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutModel
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DTools

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dP sP dTab sTab d2Tab dsTab d2sTab rep_dTab
  rep_sTab rep_d2Tab rep_dsTab rep_d2sTab)
open scoped commutatorElement

section Rep

theorem dArr_get : dArr[0]! = idA 693 ∧ dArr[1]! = dTab ∧ dArr[2]! = d2Tab ∧ dArr[3]! = sTab ∧
    dArr[4]! = dsTab ∧ dArr[5]! = d2sTab := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [dArr, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem rep_dArr {q : ℕ} (hq : q < 6) : Rep 693 dArr[q]! (dP ^ (q % 3) * sP ^ (q / 3)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := dArr_get
  interval_cases q
  · rw [h0, show (0 : ℕ) % 3 = 0 from rfl, show (0 : ℕ) / 3 = 0 from rfl, pow_zero, pow_zero,
      mul_one]
    exact rep_idA
  · rw [h1, show (1 : ℕ) % 3 = 1 from rfl, show (1 : ℕ) / 3 = 0 from rfl, pow_one, pow_zero,
      mul_one]
    exact rep_dTab
  · rw [h2, show (2 : ℕ) % 3 = 2 from rfl, show (2 : ℕ) / 3 = 0 from rfl, pow_two, pow_zero,
      mul_one]
    exact rep_d2Tab
  · rw [h3, show (3 : ℕ) % 3 = 0 from rfl, show (3 : ℕ) / 3 = 1 from rfl, pow_zero, pow_one,
      one_mul]
    exact rep_sTab
  · rw [h4, show (4 : ℕ) % 3 = 1 from rfl, show (4 : ℕ) / 3 = 1 from rfl, pow_one, pow_one]
    exact rep_dsTab
  · rw [h5, show (5 : ℕ) % 3 = 2 from rfl, show (5 : ℕ) / 3 = 1 from rfl, pow_two, pow_one]
    exact rep_d2sTab

theorem rep_dArr' {i j : ℕ} (hi : i < 3) (hj : j < 2) :
    Rep 693 dArr[i + 3 * j]! (dP ^ i * sP ^ j) := by
  have h := rep_dArr (q := i + 3 * j) (by omega)
  rwa [show (i + 3 * j) % 3 = i by omega, show (i + 3 * j) / 3 = j by omega] at h

end Rep

theorem rep_get {t : Array ℕ} {g : Equiv.Perm (Fin 693)} (h : Rep 693 t g) (p : Fin 693) :
    t[(p : ℕ)]! = ((g p : Fin 693) : ℕ) :=
  h p

theorem O_mem_gens {c : ChainData} {i : ℕ} (hi : i < c.O.size) :
    ∃ w ∈ c.gens, c.O[i] = wA w :=
  ⟨_, List.getElem_mem _, O_getElem' c hi⟩

theorem exists_of_not_allLt {n : ℕ} {f : ℕ → Bool} (h : allLt n f = false) :
    ∃ p : Fin n, f p = false := by
  by_contra hc
  have : allLt n f = true := allLt_iff.2 fun p hp => by
    cases hf : f p
    · exact absurd ⟨⟨p, hp⟩, hf⟩ hc
    · rfl
  rw [h] at this
  exact Bool.false_ne_true this

section Basic

theorem chZ_eq : chZ.grp = zpowers (gP 14) := by
  rw [ChainData.grp, Subgroup.zpowers_eq_closure]
  congr 1
  ext x
  simp [chZ, wP]

theorem mem_chZ_cases {c : Equiv.Perm (Fin 693)} (hc : c ∈ chZ.grp) : c = 1 ∨ c = gP 14 := by
  rw [chZ_eq] at hc
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  have h2 : gP 14 ^ (2 : ℤ) = 1 := by rw [zpow_two, gP_mul_self (by norm_num)]
  have hk : gP 14 ^ k = gP 14 ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_ediv_mul k 2, zpow_add, mul_comm (k / 2) 2, zpow_mul, h2,
      one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hk, h, zpow_zero]
  · right; rw [hk, h, zpow_one]

theorem labA1_inv : ∀ a ∈ chA1.grp, ∀ p : Fin 693,
    labA1[((a p : Fin 693) : ℕ)]! = labA1[(p : ℕ)]! := by
  have hgen : ∀ w ∈ chA1.gens, ∀ p : Fin 693,
      labA1[((wP w p : Fin 693) : ℕ)]! = labA1[(p : ℕ)]! := by
    intro w hw p
    have h := labA1_check
    unfold labA1Check at h
    rw [Bool.and_eq_true] at h
    have h1 := all_O_spec (p := fun g => allLt 693 fun p => labA1[g[p]!]! == labA1[p]!) h.2 w hw
    have h2 := allLt_spec h1 p.2
    rw [beq_iff_eq, rep_get (rep_wA_gens gensOK_chA1 hw) p] at h2
    exact h2
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact hgen w hw
  | one => intro p; rfl
  | mul x y _ _ hx hy => intro p; rw [Equiv.Perm.mul_apply, hx, hy]
  | inv x _ hx =>
    intro p
    have := hx (x⁻¹ p)
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at this ⊢
    exact this.symm

end Basic

@[expose] def fixCard (g : Equiv.Perm (Fin 693)) : ℕ := (Finset.univ.filter fun p => g p = p).card

theorem fixCnt_eq {a : Array ℕ} {g : Equiv.Perm (Fin 693)} (h : Rep 693 a g) :
    fixCnt a = fixCard g := by
  unfold fixCnt fixCard
  rw [← List.map_coe_finRange_eq_range, List.countP_map, Fin.univ_def]
  rw [Finset.card_def, Finset.filter_val, Multiset.filter_coe, Multiset.coe_card,
    ← List.countP_eq_length_filter]
  congr 1
  funext p
  simp only [Function.comp_apply, rep_get h p]
  rw [beq_eq_decide]
  simp [Fin.ext_iff]

theorem fixCard_conj (y b : Equiv.Perm (Fin 693)) : fixCard (y * b * y⁻¹) = fixCard b := by
  unfold fixCard
  apply Finset.card_bij (fun p _ => y⁻¹ p)
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : y (b (y⁻¹ p)) = p := hp.2
    calc b (y⁻¹ p) = y⁻¹ (y (b (y⁻¹ p))) := by simp
      _ = y⁻¹ p := by rw [h1]
  · intro p _ q _ h
    exact y⁻¹.injective h
  · intro q hq
    rw [Finset.mem_filter] at hq
    refine ⟨y q, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show y (b (y⁻¹ (y q))) = y q
    rw [show y⁻¹ (y q) = q by simp, hq.2]

section Chains

theorem gensOK_chX3A3 : chX3A3.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chX3A3 : chX3A3.baseFin.Nodup := by decide

theorem gensOK_chSigA3 : chSigA3.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chSigA3 : chSigA3.baseFin.Nodup := by decide

theorem card_chX3A3 : Nat.card chX3A3.grp = 8192 := by
  rw [ChainData.card_grp tabs_check gensOK_chX3A3 chX3A3_ok nodup_chX3A3, chX3A3_order]

theorem card_chSigA3 : Nat.card chSigA3.grp = 24576 := by
  rw [ChainData.card_grp tabs_check gensOK_chSigA3 chSigA3_ok nodup_chSigA3, chSigA3_order]

theorem mem_chX3A3_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chX3A3.grp ↔ siftA 693 lvX3A3 chX3A3.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chX3A3 chX3A3_ok nodup_chX3A3 hG

theorem chSigA3_eq : chSigA3.grp = chSig.grp ⊔ chA3.grp := grp_append (by decide)

end Chains

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
