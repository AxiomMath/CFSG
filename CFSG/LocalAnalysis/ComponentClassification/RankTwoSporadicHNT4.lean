module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNLocal
public import CFSG.Sporadic.HNOddCore.SylD
public import Certificates.Certificate2107
public import Certificates.Certificate2096
public import Certificates.Certificate2087
public import Certificates.Certificate2099
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2094
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2089
public import Certificates.Certificate2104
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HN

open Subgroup Equiv CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore
open scoped commutatorElement

section Words

variable {K : Type*} [Group K] (g : ℕ → K)

theorem wordVal_append (u v : List ℤ) : wordVal g (u ++ v) = wordVal g u * wordVal g v := by
  simp [wordVal, List.map_append, List.prod_append]

theorem wordVal_invW : ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0) →
    wordVal g (invW w) = (wordVal g w)⁻¹
  | [], _ => by simp [wordVal, invW]
  | l :: w, hw => by
    have hl0 : l ≠ 0 := hw l (List.mem_cons_self ..)
    have e : invW (l :: w) = invW w ++ [-l] := by simp [invW]
    have e2 : wordVal g [-l] =
        (if 0 < l then g (l.natAbs - 1) else (g (l.natAbs - 1))⁻¹)⁻¹ := by
      simp only [wordVal, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      by_cases hl : 0 < l
      · rw [ite_eq_right (by omega), ite_eq_left hl, Int.natAbs_neg]
      · rw [ite_eq_left (by omega), ite_eq_right hl, Int.natAbs_neg, inv_inv]
    rw [e, wordVal_append, wordVal_invW w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')), e2,
      wordVal_cons, mul_inv_rev]

theorem wordVal_commW (u v : List ℤ) (hu : ∀ l ∈ u, l ≠ 0) (hv : ∀ l ∈ v, l ≠ 0) :
    wordVal g (commW u v) = ⁅wordVal g u, wordVal g v⁆ := by
  rw [commW, wordVal_append, wordVal_append, wordVal_append, wordVal_invW g u hu,
    wordVal_invW g v hv, commutatorElement_def]

theorem plettersOK_ne_zero {j : ℕ} {w : List ℤ} (hw : plettersOK j w = true) :
    ∀ l ∈ w, l ≠ 0 := by
  simp only [plettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne] at hw
  exact fun l hl => (hw l hl).1

theorem plettersOK_append {j : ℕ} {u v : List ℤ} (hu : plettersOK j u = true)
    (hv : plettersOK j v = true) : plettersOK j (u ++ v) = true := by
  simp only [plettersOK, List.all_append, Bool.and_eq_true] at hu hv ⊢
  exact ⟨hu, hv⟩

theorem plettersOK_invW {j : ℕ} {w : List ℤ} (hw : plettersOK j w = true) :
    plettersOK j (invW w) = true := by
  simp only [plettersOK, List.all_eq_true, invW, List.mem_reverse, List.mem_map] at hw ⊢
  rintro _ ⟨l, hl, rfl⟩
  have := hw l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this ⊢
  omega

theorem plettersOK_commW {j : ℕ} {u v : List ℤ} (hu : plettersOK j u = true)
    (hv : plettersOK j v = true) : plettersOK j (commW u v) = true :=
  plettersOK_append (plettersOK_append (plettersOK_append hu hv) (plettersOK_invW hu))
    (plettersOK_invW hv)

theorem plettersOK_mono {j j' : ℕ} (hj : j ≤ j') {w : List ℤ} (hw : plettersOK j w = true) :
    plettersOK j' w = true := by
  simp only [plettersOK, List.all_eq_true] at hw ⊢
  intro l hl
  have := hw l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this ⊢
  omega

end Words

theorem prep_prodP {n : ℕ} {l : List (Array ℕ)} {gs : List (Perm (Fin n))}
    (h : List.Forall₂ (PRep n) l gs) : PRep n (prodP n l) gs.prod := by
  induction h with
  | nil => exact prep_pid
  | cons ha _ ih => exact prep_pcomp ha ih

theorem prep_powP {n : ℕ} {a : Array ℕ} {g : Perm (Fin n)} (h : PRep n a g) (m : ℕ) :
    PRep n (powP n a m) (g ^ m) := by
  have : List.Forall₂ (PRep n) (List.replicate m a) (List.replicate m g) := by
    induction m with
    | zero => exact .nil
    | succ m ih => exact .cons h ih
  have h' := prep_prodP this
  rwa [List.prod_replicate] at h'

theorem orderOf_of_ord4P {n : ℕ} {y : Array ℕ} {g : Perm (Fin n)} (h : PRep n y g)
    (hy : ord4P n y = true) : orderOf g = 4 := by
  simp only [ord4P, Bool.and_eq_true, Bool.not_eq_true'] at hy
  obtain ⟨h1, h2⟩ := hy
  have h2' : g * g * (g * g) = 1 :=
    (peq_iff (prep_pcomp (prep_pcomp h h) (prep_pcomp h h)) prep_pid).1 h2
  have h1' : g * g ≠ 1 := fun e => by
    rw [(peq_iff (prep_pcomp h h) prep_pid).2 e] at h1
    exact Bool.noConfusion h1
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, pow_two]
    exact h1'
  · rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
    exact h2'

theorem isInvP_of_prep {n : ℕ} {x : Array ℕ} {g : Perm (Fin n)} (h : PRep n x g) (h1 : g ≠ 1)
    (h2 : g * g = 1) : isInvP n x = true := by
  simp only [isInvP, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨?_, (peq_iff (prep_pcomp h h) prep_pid).2 h2⟩
  by_contra hne
  rw [Bool.not_eq_false] at hne
  exact h1 ((peq_iff h prep_pid).1 hne)

noncomputable abbrev t4R :
    ↥RH := jR t4J

theorem t4C_val :
    ((t4C : C4) : ↥RH) = t4R := rfl

theorem gR_mem_X
    {s : ℕ} (hs : s < 10) : gR s ∈ JH.subgroupOf RH ⊓ centralizer {t4R} := by
  refine mem_inf.mpr ⟨?_, (gC4' s).2⟩
  have e : gR s = jR (g4 s) := by
    show ((gC4' s : C4) : RH) = jR (g4 s)
    rw [gC4', dite_eq_left (by omega)]
    show gC s = jR (g4 s)
    rw [gC, ite_eq_left hs]
  rw [e, mem_subgroupOf, jR_val]
  exact (g4 s).2

theorem wordVal_gR_mem
    {w : List ℤ} (hw : plettersOK 10 w = true) :
    wordVal gR w ∈ JH.subgroupOf RH ⊓ centralizer {t4R} :=
  wordVal_mem (fun _ hh => gR_mem_X hh) w hw

theorem coe_wordVal_gC4'
    (w : List ℤ) : ((wordVal gC4' w : C4) : ↥RH) = wordVal gR w :=
  map_wordVal C4.subtype gC4' w

theorem rho4_wordVal
    (w : List ℤ) : rho4 (wordVal gC4' w) = wordVal rhoGen w := by
  rw [map_wordVal]
  congr 1
  funext s
  exact rho4_gC4' s

theorem prep_rho4W
    {w : List ℤ} (hw : plettersOK 11 w = true) :
    PRep 800 (rho4W w) (rho4 (wordVal gC4' w)) := by
  rw [rho4_wordVal]
  exact prep_pword_wordVal (fun _ hh => prep_rhoGen hh) (fun _ hh => prep_rhoGen_inv hh) w hw

theorem poolT4_size (pool : Array (List ℤ × List ℤ)) : (poolT4 pool).size = pool.size :=
  Array.size_map ..

theorem poolT4_get {pool : Array (List ℤ × List ℤ)} {f : ℕ} (hf : f < pool.size) :
    (poolT4 pool)[f]! = (rho4W (commW pool[f]!.1 pool[f]!.2),
      rho4W (invW (commW pool[f]!.1 pool[f]!.2))) := by
  rw [poolT4, getElem!_pos _ f (by simpa using hf), Array.getElem_map, ← getElem!_pos pool f hf]

theorem witness_t4
    {pool : Array (List ℤ × List ℤ)} {wits : Array T4Wit}
    (hc : hnT4Check pool wits = true) {b : ↥RH} (hb : b ∈ PR) (hb2 : b ^ 2 = 1)
    (hbt : b ∉ zpowers t4R) :
    ∃ w ∈ Subgroup.closure {y | ∃ c ∈ centDer (JH.subgroupOf RH) t4R, y = ⁅b, c⁆},
      4 ∣ orderOf w := by
  simp only [hnT4Check, t4Run, t4Loop, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at hc
  obtain ⟨⟨hpool, -⟩, hall⟩ := hc
  obtain ⟨x, hxP, rfl⟩ := hb
  have hxbar : rho4 x ∈ Pbar := map_Pc ▸ mem_map_of_mem rho4 hxP
  obtain ⟨⟨k, hk⟩, hkx⟩ := Pbar_subset hxbar
  have hkx' : rho4 (liftC k) = rho4 x := by rw [← ePerm_eq hk]; exact hkx
  set y := liftC k with hy
  have hyx : x = y ∨ x = y * t4C := by
    have h1 : y⁻¹ * x ∈ rho4.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkx', inv_mul_cancel]
    rw [ker_rho4] at h1
    rcases eq_one_or_eq_of_mem_zpowers orderOf_t4C h1 with h | h
    · left
      calc x = y * (y⁻¹ * x) := by group
        _ = y := by rw [h, mul_one]
    · right
      calc x = y * (y⁻¹ * x) := by group
        _ = y * t4C := by rw [h]
  have hb2' : (x : ↥RH) ^ 2 = 1 := hb2
  have hx2 : x ^ 2 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hb2')
  have hy2 : y ^ 2 = 1 := by
    rcases hyx with h | h
    · rw [← h]
      exact hx2
    · rw [← mul_t4C_sq y, ← h]
      exact hx2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hy2)
  have hρ2 : rho4 x * rho4 x = 1 := by rw [← map_mul, ← pow_two, hx2, map_one]
  have hρ1 : rho4 x ≠ 1 := by
    intro h
    have hxk : x ∈ rho4.ker := h
    rw [ker_rho4] at hxk
    apply hbt
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hxk
    exact ⟨j, (SubgroupClass.coe_zpow t4C j).symm⟩
  have hρinv : (rho4 x)⁻¹ = rho4 x := inv_eq_of_mul_eq_one_right hρ2
  have hpE : PRep 800 pE[k]! (rho4 x) := by
    have := prep_pE k hk
    rwa [hkx'] at this
  have hpool' : ∀ f < pool.size, plettersOK 10 pool[f]!.1 = true ∧
      plettersOK 10 pool[f]!.2 = true := by
    intro f hf
    have := hpool pool[f]! (by rw [getElem!_pos pool f hf]; exact Array.getElem_mem _)
    simpa only [Bool.and_eq_true] using this
  set cC : ℕ → C4 := fun f => wordVal gC4' (commW pool[f]!.1 pool[f]!.2) with hcC
  have hcC_mem : ∀ f < pool.size, ((cC f : C4) : ↥RH) ∈ centDer (JH.subgroupOf RH) t4R := by
    intro f hf
    obtain ⟨h1, h2⟩ := hpool' f hf
    rw [hcC, coe_wordVal_gC4', wordVal_commW _ _ _ (plettersOK_ne_zero h1) (plettersOK_ne_zero h2)]
    exact commutator_mem_commutator (wordVal_gR_mem h1) (wordVal_gR_mem h2)
  have hcC_prep : ∀ f < pool.size, PRep 800 (zT4 pE[k]! (poolT4 pool)[f]!) (rho4 ⁅x, cC f⁆) := by
    intro f hf
    obtain ⟨h1, h2⟩ := hpool' f hf
    have hw : plettersOK 11 (commW pool[f]!.1 pool[f]!.2) = true :=
      plettersOK_mono (by norm_num) (plettersOK_commW h1 h2)
    have hc1 := prep_rho4W hw
    have hc2 := prep_rho4W (plettersOK_invW hw)
    have e : wordVal gC4' (invW (commW pool[f]!.1 pool[f]!.2)) = (cC f)⁻¹ := by
      rw [hcC, wordVal_invW _ _ (plettersOK_ne_zero hw)]
    rw [e] at hc2
    have h := prep_pcomp (prep_pcomp hpE hc1) (prep_pcomp hpE hc2)
    rw [poolT4_get hf, zT4, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      hρinv]
    simpa [hcC, mul_assoc] using h
  have hcomm_y : ∀ f, ⁅(x : ↥RH), ((cC f : C4) : ↥RH)⁆ =
      ⁅((y : C4) : ↥RH), ((cC f : C4) : ↥RH)⁆ := by
    intro f
    rcases hyx with h | h
    · rw [h]
    · rw [h, coe_mul]
      have ht : ((t4C : C4) : ↥RH) * ((cC f : C4) : ↥RH) = ((cC f : C4) : ↥RH) * (t4C : C4) := by
        have := congrArg Subtype.val (t4C_comm (cC f)).symm.eq
        rwa [coe_mul, coe_mul] at this
      simp only [commutatorElement_def, mul_inv_rev]
      calc (y : ↥RH) * t4C * cC f * ((t4C : ↥RH)⁻¹ * (y : ↥RH)⁻¹) * (cC f : ↥RH)⁻¹ =
            (y : ↥RH) * (t4C * cC f * (t4C : ↥RH)⁻¹) * (y : ↥RH)⁻¹ * (cC f : ↥RH)⁻¹ := by group
        _ = (y : ↥RH) * cC f * (y : ↥RH)⁻¹ * (cC f : ↥RH)⁻¹ := by
            rw [ht, mul_inv_cancel_right]
  have hmemC : ∀ f < pool.size, ⁅(x : ↥RH), ((cC f : C4) : ↥RH)⁆ ∈
      Subgroup.closure {y | ∃ c ∈ centDer (JH.subgroupOf RH) t4R, y = ⁅(x : ↥RH), c⁆} :=
    fun f hf => subset_closure ⟨_, hcC_mem f hf, rfl⟩
  have hwk := allBelowN_spec hall hk
  rcases hwit : wits[k]! with _ | ⟨fs, m⟩ | ⟨f, p⟩ | p
  ·
    rw [hwit] at hwk
    simp only [t4WitOK, Bool.not_eq_true'] at hwk
    rw [isInvP_of_prep hpE hρ1 hρ2] at hwk
    exact absurd hwk (by decide)
  ·
    rw [hwit] at hwk
    simp only [t4WitOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      poolT4_size] at hwk
    obtain ⟨hfs, hord⟩ := hwk
    set W : C4 := (fs.map fun f => ⁅x, cC f⁆).prod with hW
    have hprep : PRep 800 (prodP 800 (fs.map fun f => zT4 pE[k]! (poolT4 pool)[f]!))
        (rho4 W) := by
      rw [hW, map_list_prod, List.map_map]
      apply prep_prodP
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun f hf => hcC_prep f (hfs f hf)
    have h4 := orderOf_of_ord4P (prep_powP hprep m) hord
    refine ⟨(W : ↥RH), ?_, ?_⟩
    · rw [hW, SubmonoidClass.coe_list_prod, List.map_map]
      refine list_prod_mem fun z hz => ?_
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hz
      show ((⁅x, cC f⁆ : C4) : ↥RH) ∈ _
      rw [coe_commutatorElement]
      exact hmemC f (hfs f hf)
    · rw [Subgroup.orderOf_coe]
      have h1 : orderOf (rho4 (W ^ m)) ∣ orderOf (W ^ m) := orderOf_map_dvd rho4 (W ^ m)
      rw [map_pow, h4] at h1
      exact h1.trans (orderOf_pow_dvd m)
  ·
    rw [hwit] at hwk
    simp only [t4WitOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hwk
    obtain ⟨⟨⟨hf, hp⟩, hz2⟩, hmove⟩ := hwk
    obtain ⟨h1, h2⟩ := hpool' f hf
    set z : C4 := ⁅x, cC f⁆ with hz
    have hz2' : rho4 z * rho4 z = 1 :=
      (peq_iff (prep_pcomp (hcC_prep f hf) (hcC_prep f hf)) prep_pid).1 hz2
    have hz4 : z ^ 4 = 1 := by
      have hk2 : z ^ 2 ∈ rho4.ker := by rw [MonoidHom.mem_ker, map_pow, pow_two, hz2']
      rw [ker_rho4] at hk2
      rcases eq_one_or_eq_of_mem_zpowers orderOf_t4C hk2 with h | h
      · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
      · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, t4C_sq]
    have hw : plettersOK 11 (commW pool[f]!.1 pool[f]!.2) = true :=
      plettersOK_mono (by norm_num) (plettersOK_commW h1 h2)
    have hzv : (z : ↥RH) = ((y : C4) : ↥RH) * wordVal gR (commW pool[f]!.1 pool[f]!.2) *
        ((y : C4) : ↥RH) * wordVal gR (invW (commW pool[f]!.1 pool[f]!.2)) := by
      rw [hz, coe_commutatorElement, hcomm_y f, commutatorElement_def, hcC]
      simp only []
      rw [coe_wordVal_gC4', wordVal_invW _ _ (plettersOK_ne_zero hw), ← coe_inv, hyinv]
    have heval : ∀ q : X, evalZT4 gTabs (pinvs hnsData.n gTabs) k pool[f]! (q : ℕ) =
        ((z : ↥RH) • q : X).val := by
      intro q
      rw [hzv, mul_smul, mul_smul, mul_smul]
      simp only [evalZT4]
      rw [← evalWordPt_spec _ (plettersOK_invW hw) q, ← liftC_smul k, ← evalWordPt_spec _ hw,
        ← liftC_smul k]
    have hz2ne : z ^ 2 ≠ 1 := by
      intro h
      have e := heval ⟨p, hp⟩
      have e2 := heval ((z : ↥RH) • (⟨p, hp⟩ : X))
      simp only at e
      rw [← e] at e2
      rw [e2, ← mul_smul, ← coe_mul, ← pow_two, h, coe_one, one_smul] at hmove
      exact hmove rfl
    refine ⟨(z : ↥RH), ?_, ?_⟩
    · rw [hz, coe_commutatorElement]
      exact hmemC f hf
    · rw [Subgroup.orderOf_coe, orderOf_eq_four hz2ne hz4]
  ·
    rw [hwit] at hwk
    simp only [t4WitOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hwk
    obtain ⟨hp, hmove⟩ := hwk
    exfalso
    apply hmove
    have e1 := liftC_smul k ⟨p, hp⟩
    have e2 := liftC_smul k (((liftC k : C4) : ↥RH) • (⟨p, hp⟩ : X))
    simp only at e1
    rw [e1] at e2
    rw [← e2, ← mul_smul, ← coe_mul, ← pow_two, ← hy, hy2, coe_one, one_smul]

end CFSG.ComponentClassification.RankTwoSporadic.HN
