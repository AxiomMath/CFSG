module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8A6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallModel
public import CFSG.GH74.KGroups.A6
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.A6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA6Inputs
public import Certificates.Certificate2006
public import Certificates.Certificate5108

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.ComponentClassification.GSThmB

local notation "P10" => Equiv.Perm (Fin 10)

namespace A6

theorem pa_mem_P : pa ∈ QP.originalSubgroup := by
  rw [QP_closure]
  exact subset_closure (by simp)

theorem pb_mem_P : pb ∈ QP.originalSubgroup := by
  rw [QP_closure]
  exact subset_closure (by simp)

theorem P_le_A : QP.originalSubgroup ≤ QA.originalSubgroup := by
  rw [QP_closure, closure_le]
  have hA : QA.originalSubgroup = closure {g | g ∈ [pa, pb, sg0, sg1]} := by
    rw [QA, certificate_originalSubgroup]
  rintro g (rfl | rfl) <;> rw [hA] <;> exact subset_closure (by simp)

theorem cent_triv : ∀ g ∈ QA.originalSubgroup,
    (∀ x ∈ QP.originalSubgroup, g * x = x * g) → g = 1 := by
  intro g hg hc
  by_contra hne
  have h1 := List.all_eq_true.1 cent_ok g ((mem_elemsT QA QA_ok g).2 hg)
  simp [hc pa pa_mem_P, hc pb pb_mem_P, hne] at h1

theorem exists_model {J₀ : Type} [Group J₀] (hJ : IsSec8JType J₀ 3 1) :
    ∃ M : AutModel J₀ P10, M.P = QP.originalSubgroup ∧ M.A = QA.originalSubgroup := by
  obtain ⟨e⟩ : Nonempty (J₀ ≃* QP.originalSubgroup) := by
    rcases hJ with h | ⟨-, -, h⟩
    · exact equiv_of_lieModel h
    · exact equiv_of_alt6 h
  exact autModel e

theorem exp_ok : expCheck (elemsT QA) = true :=
  Certificates.certificate2006.1

theorem diag_ok : diagCheck (elemsT QA) (elemsT QP) = true :=
  Certificates.certificate2006.2.1

theorem inner_ok : innerCheck (elemsT QA) (elemsT QP) = true :=
  Certificates.certificate2006.2.2.1

theorem noComm_ok : noCommCheck (elemsT QA) (elemsT QP) = true :=
  Certificates.certificate2006.2.2.2

theorem card_fix_eq (s : P10) :
    Nat.card ↥(QP.originalSubgroup ⊓ centralizer ({s} : Set P10)) = fixCount (elemsT QP) s :=
  card_inf_centralizer QP QP_ok s

theorem pow120 {g : P10} (hg : g ∈ QA.originalSubgroup) : g ^ 120 = 1 := by
  have h := List.all_eq_true.1 exp_ok g ((mem_elemsT QA QA_ok g).2 hg)
  simpa using h

theorem diag_fact {s : P10} (hs : s ∈ QA.originalSubgroup) (hs2 : s * s = 1)
    (hfix : Nat.card ↥(QP.originalSubgroup ⊓ centralizer ({s} : Set P10)) ≠ 10) {o : P10}
    (ho : o ∈ QA.originalSubgroup) (hos : o * s = s * o) (ho1 : o ≠ 1) (ho15 : o ^ 15 = 1) :
    ∃ n ∈ QP.originalSubgroup, n * s = s * n ∧ (o * n * o⁻¹ * n⁻¹) ^ 15 ≠ 1 := by
  rw [card_fix_eq] at hfix
  have h := List.all_eq_true.1 diag_ok s ((mem_elemsT QA QA_ok s).2 hs)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  rcases h with (h | h) | h
  · exact absurd hs2 h
  · exact absurd h hfix
  · have h' := h o ((mem_elemsT QA QA_ok o).2 ho)
    rcases h' with ((h' | h') | h') | ⟨n, hn, hns, hn15⟩
    · exact absurd hos h'
    · exact absurd h' ho1
    · exact absurd ho15 h'
    · exact ⟨n, (mem_elemsT QP QP_ok n).1 hn, hns, hn15⟩

theorem card_centCount (L : RawSchreierDatum 10) (hL : ValidSchreier L) (x : P10) :
    Nat.card ↥(L.originalSubgroup ⊓
      centralizer ((QP.originalSubgroup ⊓ centralizer ({x} : Set P10) : Subgroup P10) :
        Set P10)) = centCount (elemsT L) (elemsT QP) x := by
  refine card_inf_eq_length L hL _ _ fun g _ => ?_
  simp only [mem_centralizer_iff, SetLike.mem_coe, mem_inf, Set.mem_singleton_iff,
    forall_eq, List.all_eq_true, List.mem_filter, decide_eq_true_eq, mem_elemsT QP QP_ok, and_imp]

theorem inner_fact {x : P10} (hx : x ∈ QP.originalSubgroup) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    Nat.card ↥(QP.originalSubgroup ⊓ centralizer ({x} : Set P10)) = 8 ∧
      (∀ a ∈ QA.originalSubgroup, a * x = x * a → a ^ 32 = 1) ∧
      Nat.card ↥(QA.originalSubgroup ⊓
        centralizer ((QP.originalSubgroup ⊓ centralizer ({x} : Set P10) : Subgroup P10) :
          Set P10)) = 4 ∧
      Nat.card ↥(QP.originalSubgroup ⊓
        centralizer ((QP.originalSubgroup ⊓ centralizer ({x} : Set P10) : Subgroup P10) :
          Set P10)) = 2 := by
  rw [card_fix_eq, card_centCount QA QA_ok, card_centCount QP QP_ok]
  have h := List.all_eq_true.1 inner_ok x ((mem_elemsT QP QP_ok x).2 hx)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true] at h
  rcases h with (h | h) | ⟨⟨⟨h8, hpow⟩, h4⟩, h2⟩
  · exact absurd hx2 h
  · exact absurd h hx1
  · refine ⟨h8, fun a ha hax => ?_, h4, h2⟩
    rcases hpow a ((mem_elemsT QA QA_ok a).2 ha) with h' | h'
    · exact absurd hax h'
    · exact h'

theorem noComm_fact {s₁ s₂ : P10} (hs₁ : s₁ ∈ QA.originalSubgroup) (hs₁2 : s₁ * s₁ = 1)
    (hfix : Nat.card ↥(QP.originalSubgroup ⊓ centralizer ({s₁} : Set P10)) = 10)
    (hs₂ : s₂ ∈ QA.originalSubgroup) (hs₂2 : s₂ * s₂ = 1) (hs₂P : s₂ ∉ QP.originalSubgroup)
    (h8 : 8 ∣ Nat.card ↥(QP.originalSubgroup ⊓ centralizer ({s₂} : Set P10))) :
    s₁ * s₂ ≠ s₂ * s₁ := by
  rw [card_fix_eq] at hfix h8
  have h := List.all_eq_true.1 noComm_ok s₁ ((mem_elemsT QA QA_ok s₁).2 hs₁)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true] at h
  rcases h with (h | h) | h
  · exact absurd hs₁2 h
  · exact absurd hfix h
  · rcases h s₂ ((mem_elemsT QA QA_ok s₂).2 hs₂) with ((h' | h') | h') | h'
    · exact absurd hs₂2 h'
    · rw [List.contains_iff_mem, mem_elemsT QP QP_ok] at h'
      exact absurd h' hs₂P
    · exact absurd (Nat.mod_eq_zero_of_dvd h8) h'
    · exact h'

theorem gcd_dvd_fifteen {m : ℕ} (hm : Odd m) : Nat.gcd m 120 ∣ 15 := by
  have h2 : Nat.Coprime (Nat.gcd m 120) 8 := by
    have hodd : Odd (Nat.gcd m 120) := hm.of_dvd_nat (Nat.gcd_dvd_left m 120)
    have hc : Nat.Coprime (Nat.gcd m 120) 2 := Odd.coprime_two_right hodd
    simpa using Nat.Coprime.pow_right 3 hc
  exact h2.dvd_of_dvd_mul_right (by simpa using Nat.gcd_dvd_right m 120)

end A6

open A6

variable {J₀ : Type} [Group J₀]

theorem cfA6Diag : CFA6Diag := by
  intro J₀ _ _ hJ θ hθ hO
  obtain ⟨O, hOC, hO1, hOodd, hON⟩ := hO
  obtain ⟨M, hP, hA⟩ := exists_model hJ
  have hPA : M.P ≤ M.A := by rw [hP, hA]; exact P_le_A
  have hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1 := by
    rw [hP, hA]; exact cent_triv
  by_contra hne
  have hodd15 : ∀ w ∈ O, (M.Φ w : P10) ^ 15 = 1 := by
    intro w hw
    have h1 : (M.Φ w : P10) ^ Nat.card O = 1 := by
      have hw1 : w ^ Nat.card O = 1 := by
        have := pow_card_eq_one' (G := O) (x := ⟨w, hw⟩)
        exact congrArg Subtype.val this
      rw [← M.Φ_pow, hw1, M.Φ_one]
    have h2 : (M.Φ w : P10) ^ 120 = 1 := pow120 (hA ▸ (M.Φ w).2)
    obtain ⟨c, hc⟩ := gcd_dvd_fifteen hOodd
    rw [hc, pow_mul, pow_gcd_eq_one.2 ⟨h1, h2⟩, one_pow]
  obtain ⟨⟨o, hoO⟩, ho1⟩ := (ne_bot_iff_exists_ne_one).1 hO1
  have ho1' : (M.Φ o : P10) ≠ 1 := fun h => ho1 (Subtype.ext ((M.Φ_eq_one).1 h))
  have hs : (M.Φ θ : P10) ∈ QA.originalSubgroup := hA ▸ (M.Φ θ).2
  have hs2 : (M.Φ θ : P10) * (M.Φ θ : P10) = 1 := by rw [← M.Φ_mul, hθ, M.Φ_one]
  have hfix : Nat.card ↥(QP.originalSubgroup ⊓ centralizer ({(M.Φ θ : P10)} : Set P10)) ≠ 10 := by
    rw [← hP, ← card_fixSubgroup M θ]
    exact hne
  have hos : (M.Φ o : P10) * (M.Φ θ : P10) = (M.Φ θ : P10) * (M.Φ o : P10) :=
    M.Φ_comm (mem_centralizer_singleton_iff.1 (hOC hoO))
  obtain ⟨n, hnP, hns, hn15⟩ :=
    diag_fact hs hs2 hfix (hA ▸ (M.Φ o).2) hos ho1' (hodd15 o hoO)
  have hnP' : n ∈ M.P := hP ▸ hnP
  have hjfix : M.e.symm ⟨n, hnP'⟩ ∈ Eight.fixSubgroup θ := by
    rw [Eight.mem_fixSubgroup, apply_eq_self_iff M θ, modelEmb_symm M n hnP']
    exact hns.symm
  have hcj := hON (mem_map_of_mem _ hjfix)
  have hmem : o * (MulAut.conj (M.e.symm ⟨n, hnP'⟩) * o⁻¹ *
      (MulAut.conj (M.e.symm ⟨n, hnP'⟩))⁻¹) ∈ O :=
    O.mul_mem hoO ((mem_normalizer_iff.1 hcj o⁻¹).1 (O.inv_mem hoO))
  apply hn15
  rw [← hodd15 _ hmem]
  have hconj : (M.Φ (MulAut.conj (M.e.symm ⟨n, hnP'⟩)) : P10) = n := by
    rw [Φ_conj M hPA hcent, modelEmb_symm M n hnP']
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hconj]
  group

theorem cfA6InnerInv : CFA6InnerInv := by
  intro J₀ _ _ hJ j hj2 hj1
  obtain ⟨M, hP, hA⟩ := exists_model hJ
  have hPA : M.P ≤ M.A := by rw [hP, hA]; exact P_le_A
  have hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1 := by
    rw [hP, hA]; exact cent_triv
  have hxP : modelEmb M j ∈ QP.originalSubgroup := hP ▸ modelEmb_mem M j
  have hx2 : modelEmb M j * modelEmb M j = 1 := by rw [← map_mul, hj2, map_one]
  have hx1 : modelEmb M j ≠ 1 := fun h => hj1 (modelEmb_injective M (by rw [h, map_one]))
  obtain ⟨h8, hpow, -, -⟩ := inner_fact hxP hx2 hx1
  refine ⟨?_, fun g => ⟨5, ?_⟩⟩
  · rw [card_centralizer_set M, Set.image_singleton, hP]
    exact h8
  · apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact pow_eq_one_of_mem_centralizer_conj M hPA hcent j (2 ^ 5)
      (fun a ha hax => hpow a (hA ▸ ha) hax) g g.2

theorem cfA6SylowCent : CFA6SylowCent := by
  intro J₀ _ _ hJ D hD
  obtain ⟨M, hP, hA⟩ := exists_model hJ
  have hPA : M.P ≤ M.A := by rw [hP, hA]; exact P_le_A
  have hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1 := by
    rw [hP, hA]; exact cent_triv
  have hE : Nat.card (D.map (modelEmb M)) = 8 := by
    rw [card_map_of_injective (modelEmb_injective M), hD]
  have hEP : D.map (modelEmb M) ≤ QP.originalSubgroup := by
    rintro _ ⟨d, -, rfl⟩
    exact hP ▸ modelEmb_mem M d
  obtain ⟨z, hzE, hz2, hz1, hzc⟩ := exists_central_involution _ hE
  obtain ⟨h8, -, h4, h2⟩ := inner_fact (hEP hzE) hz2 hz1
  have hEeq : D.map (modelEmb M) = QP.originalSubgroup ⊓ centralizer ({z} : Set P10) := by
    refine eq_of_le_of_card_ge (fun y hy => ⟨hEP hy, mem_centralizer_singleton_iff.2 ?_⟩) ?_
    · exact hzc y hy
    · rw [hE, h8]
  refine ⟨?_, ?_⟩
  · rw [card_centralizer_map_conj M hPA hcent D, hEeq, hA]
    exact h4
  · rw [card_centralizer_set M, ← coe_map, hEeq, hP]
    exact h2

theorem cfA6NoComm : CFA6NoComm := by
  intro J₀ _ _ hJ θ₁ θ₂ h1 h2 hfix hout D hD hθ₂ hcomm
  obtain ⟨M, hP, hA⟩ := exists_model hJ
  have hPA : M.P ≤ M.A := by rw [hP, hA]; exact P_le_A
  have hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1 := by
    rw [hP, hA]; exact cent_triv
  have hs₁ : (M.Φ θ₁ : P10) ∈ QA.originalSubgroup := hA ▸ (M.Φ θ₁).2
  have hs₂ : (M.Φ θ₂ : P10) ∈ QA.originalSubgroup := hA ▸ (M.Φ θ₂).2
  have hs₁2 : (M.Φ θ₁ : P10) * (M.Φ θ₁ : P10) = 1 := by rw [← M.Φ_mul, h1, M.Φ_one]
  have hs₂2 : (M.Φ θ₂ : P10) * (M.Φ θ₂ : P10) = 1 := by rw [← M.Φ_mul, h2, M.Φ_one]
  have hfix' : Nat.card ↥(QP.originalSubgroup ⊓ centralizer ({(M.Φ θ₁ : P10)} : Set P10)) =
      10 := by
    rw [← hP, ← card_fixSubgroup M θ₁]
    exact hfix
  have hs₂P : (M.Φ θ₂ : P10) ∉ QP.originalSubgroup := by
    rw [← hP, ← mem_range_conj_iff M hPA hcent]
    exact hout
  have hle : D.map (modelEmb M) ≤
      QP.originalSubgroup ⊓ centralizer ({(M.Φ θ₂ : P10)} : Set P10) := by
    have hmap := map_centralizer_map_conj M hPA hcent D
    have hθ₂' : (M.Φ θ₂ : P10) ∈ M.A ⊓ centralizer ((D.map (modelEmb M) : Subgroup P10) :
        Set P10) := by
      rw [← hmap]
      exact mem_map_of_mem _ hθ₂
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨hP ▸ modelEmb_mem M d, mem_centralizer_singleton_iff.2 ?_⟩
    exact (mem_centralizer_iff.1 hθ₂'.2) _ ⟨d, hd, rfl⟩
  have h8 : 8 ∣ Nat.card ↥(QP.originalSubgroup ⊓ centralizer ({(M.Φ θ₂ : P10)} : Set P10)) := by
    have := card_dvd_of_le hle
    rwa [card_map_of_injective (modelEmb_injective M), hD] at this
  exact noComm_fact hs₁ hs₁2 hfix' hs₂ hs₂2 hs₂P h8 (M.Φ_comm hcomm)

end CFSG.ComponentClassification.CatFactsSmall
