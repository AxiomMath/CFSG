module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutSpec
public import Certificates.Certificate26962

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native

theorem s5o_spec2
    (hR : s5oS1 ≤ hs100R) :
    (∀ x ∈ s5oS1, x * x = 1 → x ≠ 1 →
      ∃ r ∈ hs100R, r ^ 5 = 1 ∧ r ≠ 1 ∧ r * x = x * r) ∧
    hs100P ≤ Subgroup.closure
      ((fun i => s5ox i * s5ox (i + 1)) '' Set.Iio 6 ∪
        (fun i => s5os * (s5ox i * s5ox (i + 1)) * s5os⁻¹) '' Set.Iio 6) := by
  classical
  have h : s5fOK = true := Certificates.certificate26962
  simp only [s5fOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨henum, hrep⟩, hfive⟩, hconj⟩, hvx⟩, hvs⟩, hlet⟩, hwa⟩, hwb⟩, hevA⟩, hevB⟩ := h
  have hps : ∀ p ∈ s5Keys, p < 100 := by
    intro p hp
    simp only [s5Keys, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps henum
  refine ⟨?_, ?_⟩
  ·
    intro x hx hx2 hx1
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    have hri := rep_of_validA (hval i hi)
    have hc := allLt_spec hconj hi
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    have hisinv : s5fIsInv s5oSCert.pts[i]! = true :=
      (eqA_iff (rep_compA hri hri) rep_idA).2 hx2
    have hne1 : eqA 100 s5oSCert.pts[i]! (idA 100) = false := by
      by_contra hcon
      rw [Bool.not_eq_false] at hcon
      exact hx1 ((eqA_iff hri rep_idA).1 hcon)
    rcases hc with (hc | hc) | ⟨⟨hk, hj⟩, hcj⟩
    · rw [hisinv] at hc
      exact absurd hc (by simp)
    · rw [hne1] at hc
      exact absurd hc (by simp)
    set k := s5fK i with hkdef
    set j := s5fJ i with hjdef
    have hk' : k < s5fRep.size := hk
    have hrepk : s5fRep[k]! < s5oSCert.pts.size := by
      simpa using allLt_spec hrep hk'
    have hrc : Rep 100 (s5fC k) (permOfArr 100 (s5fC k)) := rep_of_validA (hval _ hrepk)
    have hrg : Rep 100 s5oSCert.pts[j]! (permOfArr 100 s5oSCert.pts[j]!) :=
      rep_of_validA (hval j hj)
    have hf := allLt_spec hfive hk'
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
    obtain ⟨⟨⟨⟨hvk, hinP⟩, h5⟩, hnid⟩, hcomm⟩ := hf
    have hrk : Rep 100 (s5fTab k) (permOfArr 100 (s5fTab k)) := rep_of_validA hvk
    set g := permOfArr 100 s5oSCert.pts[j]! with hg
    set c := permOfArr 100 (s5fC k) with hcdef
    set rk := permOfArr 100 (s5fTab k) with hrkdef
    set y := permOfArr 100 s5oSCert.pts[i]! with hy
    have hgc : g * c = y * g := (eqA_iff (rep_compA hrg hrc) (rep_compA hri hrg)).1 hcj
    have hrc' : rk * c = c * rk :=
      (eqA_iff (rep_compA hrk hrc) (rep_compA hrc hrk)).1 hcomm
    have hr5 : rk ^ 5 = 1 := by
      have hr5' : Rep 100 (s5oPow5 (s5fTab k)) (rk * (rk * (rk * (rk * rk)))) :=
        rep_compA hrk (rep_compA hrk (rep_compA hrk (rep_compA hrk hrk)))
      have := (eqA_iff hr5' rep_idA).1 h5
      calc rk ^ 5 = rk * (rk * (rk * (rk * rk))) := by simp [pow_succ, mul_assoc]
        _ = 1 := this
    have hr1 : rk ≠ 1 := by
      intro h1
      have : eqA 100 (s5fTab k) (idA 100) = true := (eqA_iff hrk rep_idA).2 h1
      rw [this] at hnid
      exact absurd hnid (by simp)
    have hrP : rk ∈ hs100P := (s5InP_iff hvk).1 hinP
    have hgR : g ∈ hs100R := hR ((hmem g).2 ⟨j, hj, rfl⟩)
    have hyg : y = g * c * g⁻¹ := by
      calc y = (y * g) * g⁻¹ := by group
        _ = (g * c) * g⁻¹ := by rw [hgc]
    refine ⟨g * rk * g⁻¹, hs100R.mul_mem (hs100R.mul_mem hgR (hs100P_le_R hrP))
      (hs100R.inv_mem hgR), ?_, ?_, ?_⟩
    · rw [conj_pow, hr5]
      group
    · intro h1
      apply hr1
      calc rk = g⁻¹ * (g * rk * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · rw [hyg]
      calc g * rk * g⁻¹ * (g * c * g⁻¹) = g * (rk * c) * g⁻¹ := by group
        _ = g * (c * rk) * g⁻¹ := by rw [hrc']
        _ = g * c * g⁻¹ * (g * rk * g⁻¹) := by group
  ·
    set K : Subgroup (Equiv.Perm (Fin 100)) := Subgroup.closure
      ((fun i => s5ox i * s5ox (i + 1)) '' Set.Iio 6 ∪
        (fun i => s5os * (s5ox i * s5ox (i + 1)) * s5os⁻¹) '' Set.Iio 6) with hK
    have hxv : ∀ i < 7, Rep 100 s5oXs[i]! (s5ox i) := fun i hi =>
      rep_of_validA (allLt_spec hvx hi)
    have hrs : Rep 100 s5oS s5os := rep_of_validA hvs
    set gp : ℕ → Equiv.Perm (Fin 100) := fun k => if k < 6 then s5ox k * s5ox (k + 1) else
      s5os * (s5ox (k - 6) * s5ox (k - 6 + 1)) * s5os⁻¹ with hgp
    have hgpK : ∀ k < 12, gp k ∈ K := by
      intro k hk
      by_cases hk6 : k < 6
      · simp only [hgp, hk6, ite_true]
        exact Subgroup.subset_closure (Or.inl ⟨k, Set.mem_Iio.2 hk6, rfl⟩)
      · simp only [hgp, hk6, ite_false]
        exact Subgroup.subset_closure (Or.inr ⟨k - 6, Set.mem_Iio.2 (by omega), rfl⟩)
    have hgpR : ∀ k < 12, Rep 100 (s5fG k) (gp k) := by
      intro k hk
      by_cases hk6 : k < 6
      · simp only [hgp, hk6, ite_true, s5fG]
        exact rep_compA (hxv k (by omega)) (hxv (k + 1) (by omega))
      · simp only [hgp, hk6, ite_false, s5fG]
        have h1 : Rep 100 (s5fT (k - 6)) (s5ox (k - 6) * s5ox (k - 6 + 1)) :=
          rep_compA (hxv (k - 6) (by omega)) (hxv (k - 6 + 1) (by omega))
        exact rep_conjA hvs h1
    set lp : ℕ → Equiv.Perm (Fin 100) := fun l => if l < 12 then gp l else (gp (l - 12))⁻¹
      with hlp
    have hlpK : ∀ l < 24, lp l ∈ K := by
      intro l hl
      by_cases hl12 : l < 12
      · simp only [hlp, hl12, ite_true]
        exact hgpK l hl12
      · simp only [hlp, hl12, ite_false]
        exact K.inv_mem (hgpK (l - 12) (by omega))
    have hlpR : ∀ l < 24, Rep 100 (s5fLetter l) (lp l) := by
      intro l hl
      by_cases hl12 : l < 12
      · simp only [hlp, hl12, ite_true, s5fLetter]
        exact hgpR l hl12
      · simp only [hlp, hl12, ite_false, s5fLetter]
        have hv : validA 100 (s5fG (l - 12)) = true := by
          have := allLt_spec hlet (by omega : l - 12 < 24)
          simpa [s5fLetter, show l - 12 < 12 by omega] using this
        have h1 := rep_inv_of_validA hv
        rw [permOfArr_eq_of_rep (hgpR (l - 12) (by omega))] at h1
        exact h1
    have hword : ∀ (w : List ℕ), (∀ l ∈ w, l < 24) → ∀ (acc : Array ℕ) (g : Equiv.Perm (Fin 100)),
        Rep 100 acc g →
        Rep 100 (w.foldl (fun acc l => compA 100 acc (s5fLetter l)) acc) (g * (w.map lp).prod) := by
      intro w
      induction w with
      | nil =>
        intro _ acc g hg
        simpa using hg
      | cons a w ih =>
        intro hw acc g hg
        have ha : a < 24 := hw a (by simp)
        have h1 := ih (fun l hl => hw l (by simp [hl])) (compA 100 acc (s5fLetter a)) (g * lp a)
          (rep_compA hg (hlpR a ha))
        simpa [mul_assoc] using h1
    have hwordK : ∀ (w : List ℕ), (∀ l ∈ w, l < 24) → (w.map lp).prod ∈ K := by
      intro w hw
      refine Subgroup.list_prod_mem K ?_
      intro y hy
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
      exact hlpK l (hw l hl)
    have hA : hs100A ∈ K := by
      have hwa' : ∀ l ∈ s5fWA, l < 24 := fun l hl => by
        simpa using List.all_eq_true.1 hwa l hl
      have h1 := hword s5fWA hwa' (idA 100) 1 rep_idA
      have h2 : Rep 100 (s5fEval s5fWA) (1 * (s5fWA.map lp).prod) := h1
      have := (eqA_iff h2 rep_hs100A).1 hevA
      rw [one_mul] at this
      rw [← this]
      exact hwordK s5fWA hwa'
    have hB : hs100B ∈ K := by
      have hwb' : ∀ l ∈ s5fWB, l < 24 := fun l hl => by
        simpa using List.all_eq_true.1 hwb l hl
      have h1 := hword s5fWB hwb' (idA 100) 1 rep_idA
      have h2 : Rep 100 (s5fEval s5fWB) (1 * (s5fWB.map lp).prod) := h1
      have := (eqA_iff h2 rep_hs100B).1 hevB
      rw [one_mul] at this
      rw [← this]
      exact hwordK s5fWB hwb'
    have h0 : hs100Gens 0 = hs100A := Matrix.cons_val_zero _ _
    have h1 : hs100Gens 1 = hs100B :=
      (Matrix.cons_val_one _ _).trans (Matrix.cons_val_zero _ _)
    rw [← closure_hs100Gens, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    revert i
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · rw [h0]
      exact hA
    · rw [h1]
      exact hB

end CFSG.EvenSporadicStandard.HSStd
