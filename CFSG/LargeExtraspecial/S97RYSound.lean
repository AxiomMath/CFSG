module

public import CFSG.LargeExtraspecial.S97RYWit
public import CFSG.LargeExtraspecial.S97RYCore

public section

namespace CFSG.LargeExtraspecial.S11.PairCheck

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75
  CFSG.CGT.Timmesfeld75.WCCheck

variable {P : PData} {M : Subgroup (Equiv.Perm (Fin P.D.n))} {genG : ℤ → M}

section

variable (hn : P.D.n < 2 ^ 32) (hgen : ∀ l, Rep P.D.n (P.D.gens l) (genG l))
  (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (hF : BaseFacts P.D)
  (hpv : ∀ J ∈ allMasks P.D.cls.length, ∃ p ∈ P.pv, p.1 = J ∧ pverdictOK P J p.2 = true)
include hn hgen hinv hF hpv

theorem pairProp_of_le {T : Subgroup M} (hT : IsWC T) (h2 : 2 ≤ P.ord)
    (hTc : Nat.card T = P.ord) (hTS : T ≤ S0 P.D genG) : PairProp T (P.nCount + 1) P.proper := by
  have hT1 : T ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hTc
    omega
  obtain ⟨J, hJ, hnd, h0, hbd, hmemT⟩ := exists_mask hn hgen hinv hF hT hT1 hTS
  have hcard := card_of_idx hn hgen hF hnd h0 hbd hmemT
  have hmemU : ∀ {t : Table} {x : M}, Rep P.D.n t x → t.size = P.D.n →
      (memU P.D J t = true ↔ x ∈ T) := fun ht hts => memU_iff_of_mask hn hgen hmemT ht hts
  have hcontains : ∀ {i : ℕ}, (idxU P.D J).contains i = true → eltG (pcG P.D genG) i ∈ T :=
    fun hi => (hmemT _).2 (Or.inr ⟨_, List.elem_iff.1 hi, rfl⟩)
  obtain ⟨⟨J', v⟩, -, hJ', hok⟩ := hpv J hJ
  simp only at hJ'
  rw [hJ'] at hok
  cases v with
  | size =>
    simp only [pverdictOK, bne_iff_ne, ne_eq] at hok
    omega
  | notClosed i j =>
    simp only [pverdictOK, verdictOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
    obtain ⟨⟨hi, hj⟩, hU⟩ := hok
    have hprod := T.mul_mem (hcontains hi) (hcontains hj)
    have := (hmemU (Rep.compT (rep_el hn hgen i) (rep_el hn hgen j)) (size_compT' _ _)).2 hprod
    rw [hU] at this
    exact absurd this (by decide)
  | bad t y g =>
    simp only [pverdictOK, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
      List.all_eq_true] at hok
    obtain ⟨⟨⟨⟨ht, hy⟩, ht1⟩, hcomm⟩, hU⟩ := hok
    have htT := hcontains ht
    have ht1' : eltG (pcG P.D genG) t ≠ 1 := fun h =>
      ht1 (beq_iff_eq.1 (beq_of_eq (rep_el hn hgen t)
        (by rw [show eltG (pcG P.D genG) t = 1 from h]; exact Rep.idT (G := M) hn)
        (size_el _) size_idT'))
    have hle : conjSubgroup (wG P.D genG g) T ≤
        Subgroup.centralizer ({eltG (pcG P.D genG) t} : Set M) := by
      intro w hw
      rw [mem_conjSubgroup] at hw
      obtain ⟨u, hu, hru⟩ := exists_mem_tabU_of_mem hn hgen hmemT hw
      have hrc := rep_conjW hn hgen hinv g hru
      rw [show wG P.D genG g * ((wG P.D genG g)⁻¹ * w * wG P.D genG g) * (wG P.D genG g)⁻¹ =
        w by group] at hrc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact eq_of_rep ((compT_eq_of_commT (hcomm u hu)) ▸ Rep.compT hrc (rep_el hn hgen t))
        (Rep.compT (rep_el hn hgen t) hrc)
    have hc := (hT.2 _ htT ht1').2 _ hle
    have hyT : wG P.D genG g * eltG (pcG P.D genG) y * (wG P.D genG g)⁻¹ ∈ T := by
      rw [← hc, mem_conjSubgroup]
      simpa [mul_assoc] using hcontains hy
    have := (hmemU (rep_conjW hn hgen hinv g (rep_el hn hgen y)) (size_compT' _ _)).2 hyT
    rw [hU] at this
    exact absurd this (by decide)
  | good c nIdx out =>
    simp only [pverdictOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true'] at hok
    obtain ⟨⟨⟨⟨⟨-, hlen⟩, hnd'⟩, hsub⟩, hchk⟩, hpr⟩ := hok
    have hsub' : ∀ i ∈ nIdx, i ∈ idxU P.D J := fun i hi => List.elem_iff.1 (hsub i hi)
    refine ⟨wG P.D genG c, ?_, fun hp => ?_⟩
    · rw [card_of_idx hn hgen hF hnd' (fun h => h0 (hsub' 0 h)) (fun i hi => hbd i (hsub' i hi))
        (mem_inf_normalizer_iff hn hgen hinv hmemT hT.1 c hsub' hchk), hlen]
    · rcases hpr with hpr | hpr
      · rw [hp] at hpr
        exact absurd hpr (by decide)
      · exact sup_ne_top_of_properOK hn hgen hinv hmemT hpr

end

theorem pairProp_of_pairCheck (hgen : ∀ l, Rep P.D.n (P.D.gens l) (genG l))
    (hinv : ∀ l, genG (-l) = (genG l)⁻¹)
    (hM : ∃ m : ℕ, Odd m ∧ Nat.card M = 2 ^ P.D.pc.length * m) (h : pairCheck P = true)
    {T : Subgroup M} (hT : IsWC T) (hTc : Nat.card T = P.ord) :
    PairProp T (P.nCount + 1) P.proper := by
  unfold pairCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, h2⟩, hbase⟩, hpv⟩ := h
  have hF := baseFacts_of_check hbase
  have hpv' : ∀ J ∈ allMasks P.D.cls.length, ∃ p ∈ P.pv, p.1 = J ∧
      pverdictOK P J p.2 = true := by
    intro J hJ
    obtain ⟨p, hp, hpJ⟩ := List.any_eq_true.1 (List.all_eq_true.1 hpv J hJ)
    simp only [Bool.and_eq_true, beq_iff_eq] at hpJ
    exact ⟨p, hp, hpJ.1, hpJ.2⟩
  obtain ⟨m, hm, hcardM⟩ := hM
  have hp := isPGroup_S0_base hn hgen hinv hF
  have hidx : ¬ 2 ∣ (S0 P.D genG).index := by
    have h := (S0 P.D genG).card_mul_index
    rw [card_S0_base hn hgen hF hinv, hcardM] at h
    have : (S0 P.D genG).index = m := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) h
    rw [this]
    exact hm.not_two_dvd_nat
  let P₀ : Sylow 2 M := hp.toSylow hidx
  obtain ⟨Q, hTQ⟩ := (isPGroup_two_of_isElemAbelian hT.1).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M Q P₀
  have hT'S : conjSubgroup c T ≤ S0 P.D genG := by
    intro x hx
    have h1 : x ∈ conjSubgroup c (Q : Subgroup M) := Subgroup.map_mono hTQ hx
    have h2 : x ∈ ((c • Q : Sylow 2 M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul]
      exact h1
    rw [hc] at h2
    exact h2
  exact PairProp.of_map (MulAut.conj c) (pairProp_of_le hn hgen hinv hF hpv' (hT.conj c) h2
    ((card_conjSubgroup c T).trans hTc) hT'S)

end CFSG.LargeExtraspecial.S11.PairCheck
