module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathInner
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathOdd
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathPerm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup

variable {X : Type} [Group X] [Finite X] {t : X} {A K : Subgroup X}

theorem card_inf_centralizer_cases_of_alt {J : Subgroup X} (eJ : J ≃* alternatingGroup (Fin 8))
    {s : X} (hs : s ∈ normalizer (J : Set X)) (hs2 : s * s = 1) :
    Nat.card ↥(J ⊓ centralizer ({s} : Set X)) ∈ ({20160, 720, 96, 48, 192} : Finset ℕ) ∧
      (Nat.card ↥(J ⊓ centralizer ({s} : Set X)) = 20160 → ∀ y ∈ J, s * y = y * s) ∧
      ((Nat.card ↥(J ⊓ centralizer ({s} : Set X)) = 720 ∨
          Nat.card ↥(J ⊓ centralizer ({s} : Set X)) = 48) →
        ¬ ∃ k ∈ J, ∀ y ∈ J, s * y * s⁻¹ = k * y * k⁻¹) := by
  classical
  let σ : Equiv.Perm (Fin 8) := AltStdBal.rho eJ (le_refl 8) ⟨s, hs⟩
  have hσ2 : σ * σ = 1 := by
    have hmul : (⟨s, hs⟩ : normalizer (J : Set X)) * ⟨s, hs⟩ = 1 := by
      ext
      exact hs2
    calc σ * σ = AltStdBal.rho eJ (le_refl 8) (⟨s, hs⟩ * ⟨s, hs⟩) := by rw [map_mul]
      _ = AltStdBal.rho eJ (le_refl 8) 1 := by rw [hmul]
      _ = 1 := map_one _
  have hcardCD : Nat.card ↥(J ⊓ centralizer ({s} : Set X)) =
      Nat.card ↥(alternatingGroup (Fin 8) ⊓ centralizer ({σ} : Set (Equiv.Perm (Fin 8)))) := by
    let C : Subgroup X := J ⊓ centralizer ({s} : Set X)
    let D : Subgroup (Equiv.Perm (Fin 8)) :=
      alternatingGroup (Fin 8) ⊓ centralizer ({σ} : Set (Equiv.Perm (Fin 8)))
    change Nat.card ↥C = Nat.card ↥D
    have hfwd : ∀ c : ↥C, ↑(eJ ⟨c.1, c.2.1⟩) ∈ centralizer ({σ} : Set (Equiv.Perm (Fin 8))) := by
      intro c
      have hcs : c.1 * s = s * c.1 := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
      have hcs' : s * c.1 * s⁻¹ = c.1 := by rw [← hcs]; group
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hρ := AltStdBal.rho_conj eJ (le_refl 8) ⟨s, hs⟩ (eJ ⟨c.1, c.2.1⟩)
      rw [MulEquiv.symm_apply_apply] at hρ
      have harg : ((eJ ⟨s * c.1 * s⁻¹,
              (mem_normalizer_iff.mp hs c.1).mp c.2.1⟩ : alternatingGroup (Fin 8)) :
            Equiv.Perm (Fin 8)) =
          ((eJ ⟨c.1, c.2.1⟩ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) :=
        congrArg (fun b : J => ((eJ b : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)))
          (Subtype.ext hcs')
      have hρ' : σ * ↑(eJ ⟨c.1, c.2.1⟩) * σ⁻¹ = ↑(eJ ⟨c.1, c.2.1⟩) := by
        simpa [σ] using hρ.trans harg
      calc ↑(eJ ⟨c.1, c.2.1⟩) * σ = (σ * ↑(eJ ⟨c.1, c.2.1⟩) * σ⁻¹) * σ := by rw [hρ']
        _ = σ * ↑(eJ ⟨c.1, c.2.1⟩) := by group
    let f : ↥C → ↥D := fun c => ⟨↑(eJ ⟨c.1, c.2.1⟩), (eJ ⟨c.1, c.2.1⟩).2, hfwd c⟩
    refine Nat.card_congr (Equiv.ofBijective f ?_)
    constructor
    · intro c c' h
      have h1 : eJ ⟨c.1, c.2.1⟩ = eJ ⟨c'.1, c'.2.1⟩ := by
        apply Subtype.ext
        exact congrArg (fun x : ↥D => x.val) h
      have h2 : (⟨c.1, c.2.1⟩ : J) = ⟨c'.1, c'.2.1⟩ := eJ.injective h1
      exact Subtype.ext (congrArg (fun x : J => (x : X)) h2)
    · intro d
      let j : J := eJ.symm ⟨d.1, d.2.1⟩
      have hjd : ↑(eJ j) = d.1 := by simp [j]
      have hdσ : σ * d.1 * σ⁻¹ = d.1 := by
        have hd : d.1 * σ = σ * d.1 := Subgroup.mem_centralizer_singleton_iff.mp d.2.2
        rw [← hd]; group
      have hρ := AltStdBal.rho_conj eJ (le_refl 8) ⟨s, hs⟩ ⟨d.1, d.2.1⟩
      have hsj : s * (j : X) * s⁻¹ = (j : X) := by
        have h1 : (⟨s * (j : X) * s⁻¹, (mem_normalizer_iff.mp hs (j : X)).mp j.2⟩ : J) = j := by
          apply eJ.injective
          apply Subtype.ext
          rw [hjd]
          exact hρ.symm.trans (by simpa [σ] using hdσ)
        exact congrArg (fun x : J => (x : X)) h1
      have hjs : (j : X) * s = s * (j : X) := by
        have h' : s * (j : X) = (j : X) * s := by
          have := congrArg (fun x : X => x * s) hsj
          simpa [mul_assoc] using this
        exact h'.symm
      refine ⟨⟨(j : X), j.2, Subgroup.mem_centralizer_singleton_iff.mpr hjs⟩, ?_⟩
      apply Subtype.ext
      change ↑(eJ ⟨(j : X), j.2⟩) = d.1
      rw [show (⟨(j : X), j.2⟩ : J) = j from rfl]
      exact hjd
  have hcases := card_alt_inf_centralizer_cases (a := σ) hσ2
  refine ⟨?_, ?_, ?_⟩
  · rw [hcardCD]
    rcases hcases with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> (rw [h]; simp)
  · intro h20 y hy
    have hD : Nat.card ↥(alternatingGroup (Fin 8) ⊓ centralizer ({σ} : Set (Equiv.Perm (Fin 8)))) =
        20160 := by rw [← hcardCD]; exact h20
    have hσ1 : σ = 1 := by
      rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · exact absurd (hD ▸ h1) (by decide)
      · exact absurd (hD ▸ h1) (by decide)
      · exact absurd (hD ▸ h1) (by decide)
      · exact absurd (hD ▸ h1) (by decide)
    have hcent : s ∈ centralizer (J : Set X) :=
      (AltStdBal.rho_eq_one_iff eJ (le_refl 8) ⟨s, hs⟩).mp (by simpa [σ] using hσ1)
    exact (Subgroup.mem_centralizer_iff.mp hcent y hy).symm
  · intro h72 hinner
    rcases hinner with ⟨k, hk, hconj⟩
    have hD : Nat.card ↥(alternatingGroup (Fin 8) ⊓ centralizer ({σ} : Set (Equiv.Perm (Fin 8)))) =
        720 ∨ Nat.card ↥(alternatingGroup (Fin 8) ⊓
          centralizer ({σ} : Set (Equiv.Perm (Fin 8)))) = 48 := by
      rcases h72 with h | h
      · left; rwa [hcardCD] at h
      · right; rwa [hcardCD] at h
    have hsign_neg : Equiv.Perm.sign σ = -1 := by
      rcases hcases with ⟨-, hc⟩ | ⟨hc, hs⟩ | ⟨hc, hs⟩ | ⟨hc, hs⟩ | ⟨hc, hs⟩
      · rcases hD with hD | hD <;> rw [hc] at hD <;> exact absurd hD (by decide)
      · rcases hD with hD | hD
        · exact hs
        · rw [hc] at hD; exact absurd hD (by decide)
      · rcases hD with hD | hD <;> rw [hc] at hD <;> exact absurd hD (by decide)
      · rcases hD with hD | hD
        · rw [hc] at hD; exact absurd hD (by decide)
        · exact hs
      · rcases hD with hD | hD <;> rw [hc] at hD <;> exact absurd hD (by decide)
    have hsign_pos : Equiv.Perm.sign σ = 1 := by
      have hk_norm : k ∈ normalizer (J : Set X) := Subgroup.le_normalizer hk
      have hsk_norm : s * k⁻¹ ∈ normalizer (J : Set X) := mul_mem hs (inv_mem hk_norm)
      have hsk : s * k⁻¹ ∈ centralizer (J : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hky : k⁻¹ * y * k ∈ J := mul_mem (mul_mem (inv_mem hk) hy) hk
        have hcalc : (s * k⁻¹) * y * (s * k⁻¹)⁻¹ = y := by
          calc (s * k⁻¹) * y * (s * k⁻¹)⁻¹ = s * (k⁻¹ * y * k) * s⁻¹ := by group
            _ = k * (k⁻¹ * y * k) * k⁻¹ := hconj (k⁻¹ * y * k) hky
            _ = y := by group
        have hcomm : (s * k⁻¹) * y = y * (s * k⁻¹) := by
          calc (s * k⁻¹) * y = ((s * k⁻¹) * y * (s * k⁻¹)⁻¹) * (s * k⁻¹) := by group
            _ = y * (s * k⁻¹) := by rw [hcalc]
        exact hcomm.symm
      have hone : AltStdBal.rho eJ (le_refl 8) ⟨s * k⁻¹, hsk_norm⟩ = 1 :=
        (AltStdBal.rho_eq_one_iff eJ (le_refl 8) ⟨s * k⁻¹, hsk_norm⟩).mpr hsk
      have hprod : (⟨s * k⁻¹, hsk_norm⟩ : normalizer (J : Set X)) * ⟨k, hk_norm⟩ =
          ⟨s, hs⟩ := by
        apply Subtype.ext
        show (s * k⁻¹) * k = s
        group
      have hsigma_eq : σ = ((eJ ⟨k, hk⟩ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) := by
        calc σ = AltStdBal.rho eJ (le_refl 8) (⟨s * k⁻¹, hsk_norm⟩ * ⟨k, hk_norm⟩) := by
              rw [hprod]
          _ = AltStdBal.rho eJ (le_refl 8) ⟨s * k⁻¹, hsk_norm⟩ *
                AltStdBal.rho eJ (le_refl 8) ⟨k, hk_norm⟩ := by rw [map_mul]
          _ = AltStdBal.rho eJ (le_refl 8) ⟨k, hk_norm⟩ := by rw [hone, one_mul]
          _ = ((eJ ⟨k, hk⟩ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) := by
              simpa using AltStdBal.rho_of_mem eJ (le_refl 8) ⟨k, hk⟩ hk_norm
      calc Equiv.Perm.sign σ =
            Equiv.Perm.sign ((eJ ⟨k, hk⟩ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) := by
              rw [hsigma_eq]
        _ = 1 := Equiv.Perm.mem_alternatingGroup.mp (eJ ⟨k, hk⟩).2
    rw [hsign_pos] at hsign_neg
    exact absurd hsign_neg (by decide)

theorem WreathK.exists_inner_of_mem_layer (hK : WreathK t A K) {s : X} (hs : s ∈ CFSG.layer X) :
    (∃ k ∈ K, ∀ y ∈ K, s * y * s⁻¹ = k * y * k⁻¹) ∧
      (∃ k ∈ conjSub t K, ∀ y ∈ conjSub t K, s * y * s⁻¹ = k * y * k⁻¹) := by
  obtain ⟨k, hk, k', hk', rfl⟩ := (hK.mem_layer_iff).mp hs
  constructor
  · refine ⟨k, hk, fun y hy => ?_⟩
    calc k * k' * y * (k * k')⁻¹ = k * (k' * y * k'⁻¹) * k⁻¹ := by group
      _ = k * y * k⁻¹ := by
            rw [show k' * y * k'⁻¹ = y by rw [← hK.commute hy hk']; group]
  · refine ⟨k', hk', fun y hy => ?_⟩
    have hY : k' * y * k'⁻¹ ∈ conjSub t K := mul_mem (mul_mem hk' hy) (inv_mem hk')
    calc k * k' * y * (k * k')⁻¹ = k * (k' * y * k'⁻¹) * k⁻¹ := by group
      _ = k' * y * k'⁻¹ := by rw [hK.commute hk hY]; group

theorem WreathK.card_centralizer_inner (hE : ExactShape t A 8) (hK : WreathK t A K)
    (hO : CFSG.oddCore X = ⊥) {s : X} (hs : s ∈ normalizer (K : Set X)) (hs2 : s * s = 1)
    (hs1 : s ≠ 1) :
    ∃ c₁ c₂ j : ℕ, Nat.card ↥(centralizer ({s} : Set X)) = c₁ * c₂ * 2 ^ j ∧
      c₁ ∈ ({20160, 720, 96, 48, 192} : Finset ℕ) ∧
      c₂ ∈ ({20160, 720, 96, 48, 192} : Finset ℕ) ∧ ¬ (c₁ = 20160 ∧ c₂ = 20160) ∧
      ((c₁ = 720 ∨ c₁ = 48 ∨ c₂ = 720 ∨ c₂ = 48) → 1 ≤ j) := by
  classical
  let c₁ : ℕ := Nat.card ↥(K ⊓ centralizer ({s} : Set X))
  let c₂ : ℕ := Nat.card ↥(conjSub t K ⊓ centralizer ({s} : Set X))
  have hcases₁ := card_inf_centralizer_cases_of_alt hK.iso.some hs hs2
  have hcases₂ := card_inf_centralizer_cases_of_alt
    ((K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm.trans
      hK.iso.some) (hK.mem_normalizer_conjSub hs) hs2
  have hc₁ : c₁ ∈ ({20160, 720, 96, 48, 192} : Finset ℕ) := hcases₁.1
  have hc₂ : c₂ ∈ ({20160, 720, 96, 48, 192} : Finset ℕ) := hcases₂.1
  obtain ⟨j, hj⟩ := WreathK.exists_card_centralizer_eq hE hK hO s
  have hEcard : Nat.card ↥(CFSG.layer X ⊓ centralizer ({s} : Set X)) = c₁ * c₂ :=
    hK.card_layer_inf_centralizer_inner hs
  have hcard : Nat.card ↥(centralizer ({s} : Set X)) = c₁ * c₂ * 2 ^ j := by
    rw [hj, hEcard]
  have hnotboth : ¬ (c₁ = 20160 ∧ c₂ = 20160) := by
    rintro ⟨h1, h2⟩
    have hcentK : ∀ y ∈ K, s * y = y * s := hcases₁.2.1 h1
    have hcentK' : ∀ y ∈ conjSub t K, s * y = y * s := hcases₂.2.1 h2
    have hmem : s ∈ centralizer ((CFSG.layer X : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := (hK.mem_layer_iff).mp hg
      show (a * b) * s = s * (a * b)
      calc (a * b) * s = a * (b * s) := by group
        _ = a * (s * b) := by rw [hcentK' b hb]
        _ = (a * s) * b := by group
        _ = (s * a) * b := by rw [hcentK a ha]
        _ = s * (a * b) := by group
    have hsbot : s ∈ (⊥ : Subgroup X) := by
      rw [← WreathK.centralizer_layer_eq_bot hE hK hO]
      exact hmem
    exact hs1 (Subgroup.mem_bot.mp hsbot)
  have hj1 : (c₁ = 720 ∨ c₁ = 48 ∨ c₂ = 720 ∨ c₂ = 48) → 1 ≤ j := by
    intro hcond
    by_contra hlt
    have hj0 : j = 0 := by omega
    have hcardC : Nat.card ↥(centralizer ({s} : Set X)) =
        Nat.card ↥(CFSG.layer X ⊓ centralizer ({s} : Set X)) := by
      rw [hcard, hEcard, hj0, pow_zero, mul_one]
    have heq := Subgroup.eq_of_le_of_card_ge
      (inf_le_right : CFSG.layer X ⊓ centralizer ({s} : Set X) ≤ centralizer ({s} : Set X))
      (le_of_eq hcardC)
    have hsC : s ∈ centralizer ({s} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
    have hsE : s ∈ CFSG.layer X := by
      have hmem : s ∈ CFSG.layer X ⊓ centralizer ({s} : Set X) := by
        rw [heq]; exact hsC
      exact hmem.1
    obtain ⟨⟨k, hk, hconjK⟩, ⟨k', hk', hconjK'⟩⟩ := hK.exists_inner_of_mem_layer hsE
    rcases hcond with h1 | h1 | h2 | h2
    · exact hcases₁.2.2 (Or.inl h1) ⟨k, hk, hconjK⟩
    · exact hcases₁.2.2 (Or.inr h1) ⟨k, hk, hconjK⟩
    · exact hcases₂.2.2 (Or.inl h2) ⟨k', hk', hconjK'⟩
    · exact hcases₂.2.2 (Or.inr h2) ⟨k', hk', hconjK'⟩
  exact ⟨c₁, c₂, j, hcard, hc₁, hc₂, hnotboth, hj1⟩

theorem false_of_card_centralizer_arith {c₁ c₂ j m : ℕ}
    (hc₁ : c₁ ∈ ({20160, 720, 96, 48, 192} : Finset ℕ))
    (hc₂ : c₂ ∈ ({20160, 720, 96, 48, 192} : Finset ℕ)) (hn : ¬ (c₁ = 20160 ∧ c₂ = 20160))
    (hj : (c₁ = 720 ∨ c₁ = 48 ∨ c₂ = 720 ∨ c₂ = 48) → 1 ≤ j) (hm : m = 1 ∨ m = 2)
    (h : c₁ * c₂ * 2 ^ j * m ∈ ({161280, 11520, 2304, 1536, 7680} : Finset ℕ)) : False := by
  have hprod_le : c₁ * c₂ * 2 ^ j * m ≤ 161280 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h <;> rw [h] <;> norm_num
  have hc₁48 : 48 ≤ c₁ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc₁
    rcases hc₁ with h | h | h | h | h <;> omega
  have hc₂48 : 48 ≤ c₂ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc₂
    rcases hc₂ with h | h | h | h | h <;> omega
  have hm1 : 1 ≤ m := by rcases hm with h | h <;> omega
  have hbase : 2304 * 2 ^ j ≤ c₁ * c₂ * 2 ^ j * m := by
    have h1 : 2304 ≤ c₁ * c₂ := by
      have := Nat.mul_le_mul hc₁48 hc₂48
      norm_num at this
      exact this
    calc 2304 * 2 ^ j ≤ (c₁ * c₂) * 2 ^ j := Nat.mul_le_mul_right _ h1
      _ ≤ (c₁ * c₂) * 2 ^ j * m := by
            have := Nat.mul_le_mul_left ((c₁ * c₂) * 2 ^ j) hm1
            simpa using this
  have h2j : 2 ^ j ≤ 70 := by
    have := le_trans hbase hprod_le
    omega
  have hjle : j ≤ 6 := by
    by_contra hlt
    push Not at hlt
    have hmono : 2 ^ 7 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hlt
    norm_num at hmono
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc₁ hc₂ hm
  interval_cases j <;>
    (rcases hc₁ with h1 | h1 | h1 | h1 | h1 <;> subst h1 <;>
     rcases hc₂ with h2 | h2 | h2 | h2 | h2 <;> subst h2 <;>
     rcases hm with h3 | h3 <;> subst h3 <;>
     simp only [Finset.mem_insert, Finset.mem_singleton] at h <;> omega)

end CFSG.OddStandard.AltStdSec.SwapPattern
