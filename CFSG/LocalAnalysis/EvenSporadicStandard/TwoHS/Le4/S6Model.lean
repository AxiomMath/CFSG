module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Fix
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.OddFix

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Sporadic.SmallOddCore.Native (natArr)
open CFSG.EvenSporadicStandard.HSStd (facW tables_spec hsC1_enum wordPerm_mem_hsC1 hs_u2b
  hsOddA hsOddB hsOddA_mem hsOddA_pow hsOddB_mem hsOddB_pow gs_all_iff gs_all_iff2)

@[expose] noncomputable def hsW : Equiv.Perm (Fin 3850) := (s6WWord.map hsC1Perm).prod

@[expose] noncomputable def hsX : Equiv.Perm (Fin 3850) := (s6XWord.map hsC1Perm).prod

theorem s6WWord_lt : ∀ j ∈ s6WWord, j < 2 := by decide

theorem s6XWord_lt : ∀ j ∈ s6XWord, j < 2 := by decide

section Tables


theorem tabRep_s6W : TabRep s6WTab hsW :=
  tabRep_wordTabS tabRep_hsC1Tabs _ fun j hj => by simpa [hsC1Tabs] using s6WWord_lt j hj

theorem tabRep_s6X : TabRep s6XTab hsX :=
  tabRep_wordTabS tabRep_hsC1Tabs _ fun j hj => by simpa [hsC1Tabs] using s6XWord_lt j hj

theorem hsW_mem : hsW ∈ hsC1 := wordPerm_mem_hsC1 s6WWord_lt

theorem hsX_mem : hsX ∈ hsC1 := wordPerm_mem_hsC1 s6XWord_lt

theorem tabRep_s6W2 : TabRep s6W2Tab (hsW * hsW) := tabRep_s6W.comp tabRep_s6W

theorem tabRep_s6W3 : TabRep s6W3Tab (hsW * hsW * hsW) := tabRep_s6W2.comp tabRep_s6W

end Tables

section Strong


theorem s6IsW_spec {z : Tab} {Z : Equiv.Perm (Fin 3850)} (hz : TabRep z Z) (h : s6IsW z = true) :
    Z = 1 ∨ Z = hsW ∨ Z = hsW * hsW ∨ Z = hsW * hsW * hsW := by
  simp only [s6IsW, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · exact Or.inl ((hz.eq_iff TabRep.idTab).1 h)
  · exact Or.inr (Or.inl ((hz.eq_iff tabRep_s6W).1 h))
  · exact Or.inr (Or.inr (Or.inl ((hz.eq_iff tabRep_s6W2).1 h)))
  · exact Or.inr (Or.inr (Or.inr ((hz.eq_iff tabRep_s6W3).1 h)))

theorem s6StrongCheck_spec {H : Subgroup (Equiv.Perm (Fin 3850))} {T : Array Tab}
    (hH : Enumerates H T.toList) {w : Tab} {W : Equiv.Perm (Fin 3850)} (hw : TabRep w W)
    {gs : Array Tab} {G : ℕ → Equiv.Perm (Fin 3850)} (hgs : ∀ j < gs.size, TabRep gs[j]! (G j))
    (h : s6StrongCheck 3850 T w gs = true) :
    (∀ y ∈ H, (∀ j < gs.size, y * G j = G j * y) →
        y = 1 ∨ y = hsW ∨ y = hsW * hsW ∨ y = hsW * hsW * hsW) ∧
      ∀ y ∈ H, (∀ j < gs.size, (W * y) * G j = G j * (W * y)) →
        W * y = 1 ∨ W * y = hsW ∨ W * y = hsW * hsW ∨ W * y = hsW * hsW * hsW := by
  simp only [s6StrongCheck, Array.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  refine ⟨fun y hy hc => ?_, fun y hy hc => ?_⟩
  · obtain ⟨k, hk, hr⟩ := hH.exists_pos hy
    rw [getElem!_pos T k hk] at hr
    rcases (h k hk).1 with h1 | h1
    · rw [Bool.eq_false_iff] at h1
      exact absurd ((gs_all_iff hgs hr).2 hc) h1
    · exact s6IsW_spec hr h1
  · obtain ⟨k, hk, hr⟩ := hH.exists_pos hy
    rw [getElem!_pos T k hk] at hr
    rcases (h k hk).2 with h1 | h1
    · rw [Bool.eq_false_iff] at h1
      exact absurd ((gs_all_iff2 hgs hw hr).2 hc) h1
    · exact s6IsW_spec (hw.comp hr) h1

end Strong

section Main

theorem hs_strong :
    ∀ y ∈ hsR, y * hsOdd1A = hsOdd1A * y → y * hsOdd1B = hsOdd1B * y →
      y = 1 ∨ y = hsW ∨ y = hsW * hsW ∨ y = hsW * hsW * hsW := by
  intro y hy hA hB
  have hyt : y * hsT1 = hsT1 * y := by
    rw [← hsOdd1_prod_pow]
    exact (((show Commute y hsOdd1A from hA).mul_right (show Commute y hsOdd1B from hB)).pow_right
      10).eq
  obtain ⟨-, -, hwt, -, tW, -⟩ := tables_spec
  have hgs : ∀ j < hsOdd1Tabs.size, TabRep hsOdd1Tabs[j]!
      (if j = 0 then hsOdd1A else hsOdd1B) := fun j hj => by
    have hj2 : j < 2 := by simpa [hsOdd1Tabs] using hj
    interval_cases j
    · simpa [hsOdd1Tabs] using tabRep_hsOdd1A
    · simpa [hsOdd1Tabs] using tabRep_hsOdd1B
  have hG : ∀ z : Equiv.Perm (Fin 3850), z * hsOdd1A = hsOdd1A * z → z * hsOdd1B = hsOdd1B * z →
      ∀ j < hsOdd1Tabs.size, z * (if j = 0 then hsOdd1A else hsOdd1B) =
        (if j = 0 then hsOdd1A else hsOdd1B) * z := fun z hzA hzB j hj => by
    have hj2 : j < 2 := by simpa [hsOdd1Tabs] using hj
    interval_cases j
    · simpa using hzA
    · simpa using hzB
  obtain ⟨h1, h2⟩ := s6StrongCheck_spec hsC1_enum tW hgs
    (by simpa [s6Strong] using Certificates.certificate25950.2.1)
  rcases mem_hsC1_or_of_mem_hsR hy hyt with hc | hc
  · exact h1 y hc (hG y hA hB)
  · have e : facW * (facW⁻¹ * y) = y := mul_inv_cancel_left _ _
    have := h2 (facW⁻¹ * y) hc (fun j hj => by rw [e]; exact hG y hA hB j hj)
    rwa [e] at this

theorem hsW_sq :
    hsW * hsW = hsT1 := by
  have h : s6W2Tab = natArr (hsCentTbl 5) := by
    simpa [s6WSq] using Certificates.certificate25950.1
  obtain ⟨-, -, -, -, -, -, tT, -⟩ := tables_spec
  exact (tabRep_s6W2.eq_iff tT).1 h

theorem hsX_sq :
    hsX * hsX = 1 := by
  have h := Certificates.certificate25950.2.2.1
  simp only [s6XRel, Bool.and_eq_true, beq_iff_eq] at h
  exact (((tabRep_s6X.comp tabRep_s6X).eq_iff TabRep.idTab).1 h.1)

theorem hsX_comm_W :
    hsX * hsW = hsW * hsW * hsW * hsX := by
  have h := Certificates.certificate25950.2.2.1
  simp only [s6XRel, Bool.and_eq_true, beq_iff_eq] at h
  exact (((tabRep_s6X.comp tabRep_s6W).eq_iff (tabRep_s6W3.comp tabRep_s6X)).1 h.2)

theorem hsT1_sq :
    hsT1 * hsT1 = 1 := by
  have h := (CFSG.EvenSporadicStandard.HSStd.hsT1_mem_ord).2
  have h1 := pow_orderOf_eq_one hsT1
  rw [h, sq] at h1
  exact h1

theorem hsW_pow_four :
    hsW * hsW * hsW * hsW = 1 := by
  calc hsW * hsW * hsW * hsW = (hsW * hsW) * (hsW * hsW) := by simp only [mul_assoc]
    _ = 1 := by rw [hsW_sq, hsT1_sq]

theorem hsW_inv :
    hsW⁻¹ = hsW * hsW * hsW :=
  inv_eq_of_mul_eq_one_right (by simpa only [mul_assoc] using hsW_pow_four)

end Main

section Tight

theorem hsP_le_hsR :
    hsP ≤ hsR := fun x hx =>
  (hs_normalizing_model.2.2.2.2.2.1 x).2 (Or.inl hx)

theorem e_apply_of_mem {e : hsR ≃* MulAut ↥hsP}
    (he : ∀ (x : hsR) (p : hsP), ((e x p : hsP) : Equiv.Perm (Fin 3850)) =
      (x : Equiv.Perm (Fin 3850)) * p * (x : Equiv.Perm (Fin 3850))⁻¹)
    (y : hsR) (hy : (y : Equiv.Perm (Fin 3850)) ∈ hsP) :
    e y = MulAut.conj (⟨y, hy⟩ : ↥hsP) := by
  ext p
  rw [he]
  simp [MulAut.conj_apply]

theorem commute_odd_conj {e : hsR ≃* MulAut ↥hsP}
    (he : ∀ (x : hsR) (p : hsP), ((e x p : hsP) : Equiv.Perm (Fin 3850)) =
      (x : Equiv.Perm (Fin 3850)) * p * (x : Equiv.Perm (Fin 3850))⁻¹)
    {z : ↥hsP} {ρ : hsR} {φ : MulAut ↥hsP} (hρ : e ρ = φ)
    (hφ : ∀ c ∈ centralizer ({z} : Set ↥hsP), Odd (orderOf c) → φ c = c)
    {g r : Equiv.Perm (Fin 3850)} (hg : g ∈ hsP)
    (hzg : (z : Equiv.Perm (Fin 3850)) = g * r * g⁻¹) :
    ∀ a ∈ hsP, a * r = r * a → ∀ n : ℕ, Odd n → a ^ n = 1 →
      (g⁻¹ * (ρ : Equiv.Perm (Fin 3850)) * g) * a =
        a * (g⁻¹ * (ρ : Equiv.Perm (Fin 3850)) * g) := by
  intro a ha har n hn han
  have hc : g * a * g⁻¹ ∈ hsP ⊓
      centralizer ({(z : Equiv.Perm (Fin 3850))} : Set (Equiv.Perm (Fin 3850))) := by
    refine mem_inf.2 ⟨hsP.mul_mem (hsP.mul_mem hg ha) (hsP.inv_mem hg), ?_⟩
    rw [mem_centralizer_singleton_iff, hzg]
    calc g * a * g⁻¹ * (g * r * g⁻¹) = g * (a * r) * g⁻¹ := by group
      _ = g * (r * a) * g⁻¹ := by rw [har]
      _ = g * r * g⁻¹ * (g * a * g⁻¹) := by group
  have h1 := commute_of_fixes (τ := z) (x := ρ) he
    (fun c hc hodd => by rw [hρ]; exact hφ c hc hodd) hc (n := n)
    (by rw [conj_pow, han]; group) hn
  calc g⁻¹ * (ρ : Equiv.Perm (Fin 3850)) * g * a =
      g⁻¹ * ((ρ : Equiv.Perm (Fin 3850)) * (g * a * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * a * g⁻¹) * (ρ : Equiv.Perm (Fin 3850))) * g := by rw [h1]
    _ = a * (g⁻¹ * (ρ : Equiv.Perm (Fin 3850)) * g) := by group

theorem sq_eq_of_aut_sq
    {e : hsR ≃* MulAut ↥hsP}
    (he : ∀ (x : hsR) (p : hsP), ((e x p : hsP) : Equiv.Perm (Fin 3850)) =
      (x : Equiv.Perm (Fin 3850)) * p * (x : Equiv.Perm (Fin 3850))⁻¹)
    {z : ↥hsP} {ρ : hsR} {φ : MulAut ↥hsP} (hρ : e ρ = φ) (hφ2 : φ * φ = MulAut.conj z) :
    (ρ : Equiv.Perm (Fin 3850)) * ρ = z := by
  have h1 : e (ρ * ρ) = e ⟨z, hsP_le_hsR z.2⟩ := by
    rw [map_mul, hρ, hφ2]
    exact (e_apply_of_mem he ⟨z, hsP_le_hsR z.2⟩ z.2).symm
  exact congrArg Subtype.val (e.injective h1)

theorem hs_not_tight_2B
    (z : ↥hsP)
    (hz : orderOf z = 2) (hf : fixCard (z : Equiv.Perm (Fin 3850)) = 30) (φ : MulAut ↥hsP)
    (hφ2 : φ * φ = MulAut.conj z)
    (hφ : ∀ c ∈ centralizer ({z} : Set ↥hsP), Odd (orderOf c) → φ c = c) : False := by
  obtain ⟨e, he, -⟩ := hs_full_automorphism_model
  obtain ⟨ρ, hρ⟩ := e.surjective φ
  have hz' : orderOf (z : Equiv.Perm (Fin 3850)) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  obtain ⟨g, hg, hzg⟩ := exists_conj_hsT2_of_fixCard z.2 hz' hf
  have hz1 : (z : Equiv.Perm (Fin 3850)) ≠ 1 := ne_one_of_fixCard_lt hf (by norm_num)
  have hρ2 := sq_eq_of_aut_sq he hρ hφ2
  have key := commute_odd_conj he hρ hφ hg hzg
  have hρ'R : g⁻¹ * (ρ : Equiv.Perm (Fin 3850)) * g ∈ hsR :=
    hsR.mul_mem (hsR.mul_mem (hsR.inv_mem (hsP_le_hsR hg)) ρ.2) (hsP_le_hsR hg)
  have hA := key hsOddA (mem_inf.1 hsOddA_mem).1
    (mem_centralizer_singleton_iff.1 (mem_inf.1 hsOddA_mem).2) 5 (by decide) hsOddA_pow
  have hB := key hsOddB (mem_inf.1 hsOddB_mem).1
    (mem_centralizer_singleton_iff.1 (mem_inf.1 hsOddB_mem).2) 3 (by decide) hsOddB_pow
  have h2 := hs_u2b _ hρ'R hA hB
  have h3 : (ρ : Equiv.Perm (Fin 3850)) * ρ = 1 := by
    calc (ρ : Equiv.Perm (Fin 3850)) * ρ =
        g * ((g⁻¹ * (ρ : Equiv.Perm (Fin 3850)) * g) * (g⁻¹ * (ρ : Equiv.Perm (Fin 3850)) * g)) *
          g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  exact hz1 (by rw [← hρ2]; exact h3)

set_option maxHeartbeats 1600000 in
theorem hs_tight_data
    (z : ↥hsP) (hz : orderOf z = 2) (hf : fixCard (z : Equiv.Perm (Fin 3850)) = 170) :
    ∃ w x : ↥hsP, w * w = z ∧
      (∀ φ : MulAut ↥hsP, φ * φ = MulAut.conj z →
        (∀ c ∈ centralizer ({z} : Set ↥hsP), Odd (orderOf c) → φ c = c) →
          φ = MulAut.conj w ∨ φ = MulAut.conj w⁻¹) ∧ x * x = 1 ∧
        x * z = z * x ∧ x * w * x⁻¹ = w⁻¹ ∧ fixCard (x : Equiv.Perm (Fin 3850)) = 170 ∧
        fixCard ((x * z : ↥hsP) : Equiv.Perm (Fin 3850)) = 170 ∧
        fixCard ((x * w : ↥hsP) : Equiv.Perm (Fin 3850)) = 30 := by
  classical
  obtain ⟨e, he, -⟩ := hs_full_automorphism_model
  have hz' : orderOf (z : Equiv.Perm (Fin 3850)) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  obtain ⟨g, hg, hzg⟩ := exists_conj_hsT1_of_fixCard z.2 hz' hf
  have hz1 : (z : Equiv.Perm (Fin 3850)) ≠ 1 := ne_one_of_fixCard_lt hf (by norm_num)
  have hT1ne : hsT1 ≠ 1 := fun h => hz1 (by rw [hzg, h]; group)
  have hWP : hsW ∈ hsP := (mem_inf.1 hsW_mem).1
  have hXP : hsX ∈ hsP := (mem_inf.1 hsX_mem).1
  have hwP : g * hsW * g⁻¹ ∈ hsP := hsP.mul_mem (hsP.mul_mem hg hWP) (hsP.inv_mem hg)
  have hxP : g * hsX * g⁻¹ ∈ hsP := hsP.mul_mem (hsP.mul_mem hg hXP) (hsP.inv_mem hg)
  refine ⟨⟨g * hsW * g⁻¹, hwP⟩, ⟨g * hsX * g⁻¹, hxP⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    calc g * hsW * g⁻¹ * (g * hsW * g⁻¹) = g * (hsW * hsW) * g⁻¹ := by group
      _ = z := by rw [hsW_sq, hzg]
  ·
    intro φ hφ2 hφ
    obtain ⟨ρ, hρ⟩ := e.surjective φ
    have hρ2 := sq_eq_of_aut_sq he hρ hφ2
    set ρp : Equiv.Perm (Fin 3850) := (ρ : Equiv.Perm (Fin 3850)) with hρp
    set ρ' : Equiv.Perm (Fin 3850) := g⁻¹ * ρp * g with hρ'
    have hρ'R : ρ' ∈ hsR :=
      hsR.mul_mem (hsR.mul_mem (hsR.inv_mem (hsP_le_hsR hg)) ρ.2) (hsP_le_hsR hg)
    have hρpg : ρp = g * ρ' * g⁻¹ := by rw [hρ']; group
    have key := commute_odd_conj he hρ hφ hg hzg
    have hA := key hsOdd1A (mem_inf.1 hsOdd1A_mem).1
      (mem_centralizer_singleton_iff.1 (mem_inf.1 hsOdd1A_mem).2) 5 (by decide) hsOdd1A_pow
    have hB := key hsOdd1B (mem_inf.1 hsOdd1B_mem).1
      (mem_centralizer_singleton_iff.1 (mem_inf.1 hsOdd1B_mem).2) 5 (by decide) hsOdd1B_pow
    have hρ'2 : ρ' * ρ' = hsT1 := by
      calc ρ' * ρ' = g⁻¹ * (ρp * ρp) * g := by rw [hρ']; group
        _ = g⁻¹ * (g * hsT1 * g⁻¹) * g := by rw [hρ2, hzg]
        _ = hsT1 := by group
    have hW4 : hsW * hsW * (hsW * hsW) = 1 := by rw [hsW_sq]; exact hsT1_sq
    have hρpP : ρp ∈ hsP := by
      rcases hs_strong ρ' hρ'R hA hB with h | h | h | h
      · exfalso
        rw [h] at hρ'2
        exact hT1ne (by simpa using hρ'2.symm)
      · rw [hρpg, h]; exact hwP
      · exfalso
        rw [h] at hρ'2
        exact hT1ne (by rw [← hρ'2]; exact hW4)
      · rw [hρpg, h]
        exact hsP.mul_mem (hsP.mul_mem hg (hsP.mul_mem (hsP.mul_mem hWP hWP) hWP))
          (hsP.inv_mem hg)
    have hφe : φ = MulAut.conj (⟨ρp, hρpP⟩ : ↥hsP) := by
      rw [← hρ]
      exact e_apply_of_mem he ρ hρpP
    rcases hs_strong ρ' hρ'R hA hB with h | h | h | h
    · exfalso
      rw [h] at hρ'2
      exact hT1ne (by simpa using hρ'2.symm)
    · left
      rw [hφe]
      refine congrArg MulAut.conj (Subtype.ext ?_)
      show ρp = g * hsW * g⁻¹
      rw [hρpg, h]
    · exfalso
      rw [h] at hρ'2
      exact hT1ne (by rw [← hρ'2]; exact hW4)
    · right
      rw [hφe]
      refine congrArg MulAut.conj (Subtype.ext ?_)
      show ρp = (g * hsW * g⁻¹)⁻¹
      rw [hρpg, h, ← hsW_inv]
      group
  · apply Subtype.ext
    calc g * hsX * g⁻¹ * (g * hsX * g⁻¹) = g * (hsX * hsX) * g⁻¹ := by group
      _ = 1 := by rw [hsX_sq]; group
  · apply Subtype.ext
    have hc : hsX * hsT1 = hsT1 * hsX := mem_centralizer_singleton_iff.1 (mem_inf.1 hsX_mem).2
    show g * hsX * g⁻¹ * (z : Equiv.Perm (Fin 3850)) =
      (z : Equiv.Perm (Fin 3850)) * (g * hsX * g⁻¹)
    rw [hzg]
    calc g * hsX * g⁻¹ * (g * hsT1 * g⁻¹) = g * (hsX * hsT1) * g⁻¹ := by group
      _ = g * (hsT1 * hsX) * g⁻¹ := by rw [hc]
      _ = (g * hsT1 * g⁻¹) * (g * hsX * g⁻¹) := by group
  · apply Subtype.ext
    have h1 : hsX * hsW * hsX⁻¹ = hsW⁻¹ := by
      rw [hsX_comm_W, hsW_inv]
      group
    calc g * hsX * g⁻¹ * (g * hsW * g⁻¹) * (g * hsX * g⁻¹)⁻¹ =
        g * (hsX * hsW * hsX⁻¹) * g⁻¹ := by group
      _ = g * hsW⁻¹ * g⁻¹ := by rw [h1]
      _ = (g * hsW * g⁻¹)⁻¹ := by group
  · rw [fixCard_conj, ← fixTab_eq tabRep_s6X]
    exact s6FixOK_parts.2.2.2.2.1
  · obtain ⟨-, -, -, -, -, -, tT, -⟩ := tables_spec
    have hxz : ((⟨g * hsX * g⁻¹, hxP⟩ * z : ↥hsP) : Equiv.Perm (Fin 3850)) =
        g * (hsX * hsT1) * g⁻¹ := by
      show g * hsX * g⁻¹ * (z : Equiv.Perm (Fin 3850)) = _
      rw [hzg]
      group
    rw [hxz, fixCard_conj, ← fixTab_eq (tabRep_s6X.comp tT)]
    exact s6FixOK_parts.2.2.2.2.2.1
  · have hxw : ((⟨g * hsX * g⁻¹, hxP⟩ * ⟨g * hsW * g⁻¹, hwP⟩ : ↥hsP) :
        Equiv.Perm (Fin 3850)) = g * (hsX * hsW) * g⁻¹ := by
      show g * hsX * g⁻¹ * (g * hsW * g⁻¹) = _
      group
    rw [hxw, fixCard_conj, ← fixTab_eq (tabRep_s6X.comp tabRep_s6W)]
    exact s6FixOK_parts.2.2.2.2.2.2

theorem fixCard_involution
    (z : ↥hsP) (hz : orderOf z = 2) :
    fixCard (z : Equiv.Perm (Fin 3850)) = 170 ∨ fixCard (z : Equiv.Perm (Fin 3850)) = 30 := by
  have hz' : orderOf (z : Equiv.Perm (Fin 3850)) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  obtain ⟨-, -, -, -, hcover⟩ := CFSG.Sporadic.SmallOddCore.hs_reps
  obtain ⟨r, hr, g, hg, hzg⟩ := hcover z z.2 hz'
  rw [hzg, fixCard_conj]
  rcases hr with rfl | rfl
  · exact Or.inl fixCard_hsT1
  · exact Or.inr fixCard_hsT2

end Tight

end CFSG.EvenSporadicStandard.TwoHS
