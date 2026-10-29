module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGDefs
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwistConjData
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapTgrp

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

private theorem lGC_tau0_orderOf : orderOf τ₀ = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact tau0_mul_self) (by decide)

private theorem lGC_iota_tau0_mul_self (hC : CentData z ι) : ι τ₀ * ι τ₀ = 1 := by
  rw [← map_mul, tau0_mul_self, map_one]

private theorem lGC_iota_liftS8_mem_centralizer (ι : Perm (Fin 10) →* G) (ρ : Perm (Fin 8)) :
    ι (liftS8 ρ) ∈ centralizer ({ι τ₀} : Set G) := by
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, liftS8_mul_τ₀]

private theorem lGC_mem_triple_of_comm {α : Type*} [DecidableEq α] {w : Perm α} {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : w * (swap a b * swap a c) = (swap a b * swap a c) * w) {x : α}
    (hx : x = a ∨ x = b ∨ x = c) : w x = a ∨ w x = b ∨ w x = c := by
  set d := swap a b * swap a c with hd
  have hfix : ∀ y : α, y ≠ a → y ≠ b → y ≠ c → d y = y := by
    intro y hya hyb hyc
    rw [hd, Perm.mul_apply, swap_apply_of_ne_of_ne hya hyc, swap_apply_of_ne_of_ne hya hyb]
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hcomm : w * d = d * w := by rw [hd]; exact h
  have hdx : d x ≠ x := by
    rcases hx with rfl | rfl | rfl
    · rw [hd, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hac.symm hbc.symm]
      exact hac.symm
    · rw [hd, Perm.mul_apply, swap_apply_of_ne_of_ne hab.symm hbc, swap_apply_right]
      exact hab
    · rw [hd, Perm.mul_apply, swap_apply_right, swap_apply_left]
      exact hbc
  have hthis : w (d x) = d (w x) := congrArg (fun f : Perm α => f x) hcomm
  rw [hfix (w x) h1 h2 h3] at hthis
  exact hdx (w.injective hthis)

private theorem lGC_three_mem (a b c : Fin 8) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    swap a b * swap a c ∈ alternatingGroup (Fin 8) :=
  (isThreeCycle_swap_mul_swap_same hab hac hbc).mem_alternatingGroup

private theorem lGC_perm_eight_eq_one_of_centralizes {ρ : Perm (Fin 8)}
    (h : ∀ α ∈ alternatingGroup (Fin 8), ρ * α = α * ρ) : ρ = 1 := by
  refine Equiv.ext fun a => ?_
  by_cases ha : ρ a = a
  · exact ha
  · exfalso
    obtain ⟨b, -, hb_notMem⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card
        (s := ({a, ρ a} : Finset (Fin 8))) (t := Finset.univ) (by
          rw [Finset.card_univ, Fintype.card_fin]
          calc ({a, ρ a} : Finset (Fin 8)).card ≤ ({ρ a} : Finset (Fin 8)).card + 1 :=
                Finset.card_insert_le a {ρ a}
            _ = 2 := by simp
            _ < 8 := by norm_num)
    have hb_ne_a : b ≠ a := fun hh => hb_notMem (by simp [hh])
    have hb_ne_ra : b ≠ ρ a := fun hh => hb_notMem (by simp [hh])
    obtain ⟨c, -, hc_notMem⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card
        (s := (insert b ({a, ρ a} : Finset (Fin 8)))) (t := Finset.univ) (by
          rw [Finset.card_univ, Fintype.card_fin]
          calc (insert b ({a, ρ a} : Finset (Fin 8))).card
                ≤ ({a, ρ a} : Finset (Fin 8)).card + 1 := Finset.card_insert_le b _
            _ ≤ 2 + 1 := by
                gcongr
                calc ({a, ρ a} : Finset (Fin 8)).card ≤ ({ρ a} : Finset (Fin 8)).card + 1 :=
                      Finset.card_insert_le a {ρ a}
                  _ = 2 := by simp
            _ < 8 := by norm_num)
    have hc_ne_a : c ≠ a := fun hh => hc_notMem (by simp [hh])
    have hc_ne_ra : c ≠ ρ a := fun hh => hc_notMem (by simp [hh])
    have hc_ne_b : c ≠ b := fun hh => hc_notMem (by rw [hh]; exact Finset.mem_insert_self b _)
    have hab : a ≠ b := hb_ne_a.symm
    have hac : a ≠ c := hc_ne_a.symm
    have hbc : b ≠ c := hc_ne_b.symm
    have hcomm := h (swap a b * swap a c) (lGC_three_mem a b c hab hac hbc)
    have htri := lGC_mem_triple_of_comm (w := ρ) hab hac hbc hcomm (Or.inl rfl)
    rcases htri with h' | h' | h'
    · exact ha h'
    · exact hb_ne_ra h'.symm
    · exact hc_ne_ra h'.symm

private theorem lGC_perm_ten_eq_one_or_tau_of_centralizes {σ : Perm (Fin 10)}
    (h : ∀ α ∈ alternatingGroup (Fin 8), σ * liftS8 α = liftS8 α * σ) :
    σ = 1 ∨ σ = τ₀ := by
  have hmem : ∀ (a b c : Fin 8), a ≠ b → a ≠ c → b ≠ c →
      ∀ x : Fin 10, x = Fin.castLE (by norm_num) a ∨ x = Fin.castLE (by norm_num) b ∨
        x = Fin.castLE (by norm_num) c →
      σ x = Fin.castLE (by norm_num) a ∨ σ x = Fin.castLE (by norm_num) b ∨
        σ x = Fin.castLE (by norm_num) c := by
    intro a b c hab hac hbc x hx
    refine lGC_mem_triple_of_comm (w := σ) ?_ ?_ ?_ ?_ hx
    · intro hh; exact hab (Fin.castLE_injective (by norm_num : 8 ≤ 10) hh)
    · intro hh; exact hac (Fin.castLE_injective (by norm_num : 8 ≤ 10) hh)
    · intro hh; exact hbc (Fin.castLE_injective (by norm_num : 8 ≤ 10) hh)
    · have hh := h (swap a b * swap a c) (lGC_three_mem a b c hab hac hbc)
      simpa [map_mul, liftS8_swap] using hh
  have hlt : ∀ i : Fin 10, i.val < 8 → (σ i).val < 8 := by
    intro i hi
    fin_cases i <;> simp only [Fin.reduceFinMk] at *
    · have hk := hmem 0 1 2 (by decide) (by decide) (by decide) (0 : Fin 10)
        (Or.inl (by decide))
      rcases hk with hk | hk | hk <;> rw [hk] <;> decide
    · have hk := hmem 1 0 2 (by decide) (by decide) (by decide) (1 : Fin 10)
        (Or.inl (by decide))
      rcases hk with hk | hk | hk <;> rw [hk] <;> decide
    · have hk := hmem 2 0 1 (by decide) (by decide) (by decide) (2 : Fin 10)
        (Or.inl (by decide))
      rcases hk with hk | hk | hk <;> rw [hk] <;> decide
    · have hk := hmem 3 0 1 (by decide) (by decide) (by decide) (3 : Fin 10)
        (Or.inl (by decide))
      rcases hk with hk | hk | hk <;> rw [hk] <;> decide
    · have hk := hmem 4 0 1 (by decide) (by decide) (by decide) (4 : Fin 10)
        (Or.inl (by decide))
      rcases hk with hk | hk | hk <;> rw [hk] <;> decide
    · have hk := hmem 5 0 1 (by decide) (by decide) (by decide) (5 : Fin 10)
        (Or.inl (by decide))
      rcases hk with hk | hk | hk <;> rw [hk] <;> decide
    · have hk := hmem 6 0 1 (by decide) (by decide) (by decide) (6 : Fin 10)
        (Or.inl (by decide))
      rcases hk with hk | hk | hk <;> rw [hk] <;> decide
    · have hk := hmem 7 0 1 (by decide) (by decide) (by decide) (7 : Fin 10)
        (Or.inl (by decide))
      rcases hk with hk | hk | hk <;> rw [hk] <;> decide
    · simp at hi
    · simp at hi
  let S : Finset (Fin 10) := Finset.univ.filter (fun i => i.val < 8)
  have hSdef : ∀ i : Fin 10, i ∈ S ↔ i.val < 8 := by intro i; simp [S]
  have hS_card : S.card = 8 := by decide
  have himage_sub : S.image σ ⊆ S := by
    intro x hx
    obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp hx
    rw [hSdef] at hiS ⊢
    exact hlt i hiS
  have himage_eq : S.image σ = S := by
    refine Finset.eq_of_subset_of_card_le himage_sub ?_
    rw [Finset.card_image_of_injective _ σ.injective]
  have hnot8 : ¬ (σ 8).val < 8 := by
    intro hlt8
    have hmem8 : σ 8 ∈ S.image σ := by
      rw [himage_eq]
      exact (hSdef (σ 8)).mpr hlt8
    obtain ⟨j, hjS, hj⟩ := Finset.mem_image.mp hmem8
    have hji : j = 8 := σ.injective hj
    rw [hji] at hjS
    have : ¬ (8 : Fin 10).val < 8 := by decide
    exact this ((hSdef 8).mp hjS)
  have hnot9 : ¬ (σ 9).val < 8 := by
    intro hlt9
    have hmem9 : σ 9 ∈ S.image σ := by
      rw [himage_eq]
      exact (hSdef (σ 9)).mpr hlt9
    obtain ⟨j, hjS, hj⟩ := Finset.mem_image.mp hmem9
    have hji : j = 9 := σ.injective hj
    rw [hji] at hjS
    have : ¬ (9 : Fin 10).val < 8 := by decide
    exact this ((hSdef 9).mp hjS)
  have h8le : 8 ≤ (σ 8).val := Nat.le_of_not_lt hnot8
  have h9le : 8 ≤ (σ 9).val := Nat.le_of_not_lt hnot9
  have h8cases : σ 8 = 8 ∨ σ 8 = 9 := by
    have hlt := (σ 8).isLt
    rcases (show (σ 8).val = 8 ∨ (σ 8).val = 9 by omega) with hh | hh
    · left; exact Fin.ext (by simpa using hh)
    · right; exact Fin.ext (by simpa using hh)
  have h9cases : σ 9 = 8 ∨ σ 9 = 9 := by
    have hlt := (σ 9).isLt
    rcases (show (σ 9).val = 8 ∨ (σ 9).val = 9 by omega) with hh | hh
    · left; exact Fin.ext (by simpa using hh)
    · right; exact Fin.ext (by simpa using hh)
  rcases h8cases with h88 | h89
  · have h99 : σ 9 = 9 := by
      rcases h9cases with h | h
      · exfalso
        have hh : σ 9 = σ 8 := by rw [h, h88]
        exact (by decide : (9 : Fin 10) ≠ 8) (σ.injective hh)
      · exact h
    obtain ⟨ρ, hρ⟩ := mem_stab2_iff_exists_liftS8.1 (mem_stab2.2 ⟨h88, h99⟩)
    have hρc : ∀ α ∈ alternatingGroup (Fin 8), ρ * α = α * ρ := by
      intro α hα
      have h1 : liftS8 (ρ * α) = liftS8 (α * ρ) := by
        rw [map_mul, map_mul]
        calc liftS8 ρ * liftS8 α = σ * liftS8 α := by rw [hρ]
          _ = liftS8 α * σ := h _ hα
          _ = liftS8 α * liftS8 ρ := by rw [← hρ]
      exact liftS8_injective h1
    have hρ1 : ρ = 1 := lGC_perm_eight_eq_one_of_centralizes hρc
    left
    rw [← hρ, hρ1, map_one]
  · have h98 : σ 9 = 8 := by
      rcases h9cases with h | h
      · exact h
      · exfalso
        have hh : σ 9 = σ 8 := by rw [h, h89]
        exact (by decide : (9 : Fin 10) ≠ 8) (σ.injective hh)
    have h2mem : τ₀ * σ ∈ stab2 8 9 := by
      rw [mem_stab2]
      refine ⟨?_, ?_⟩
      · simp [Perm.mul_apply, h89, τ₀]
      · simp [Perm.mul_apply, h98, τ₀]
    obtain ⟨ρ, hρ⟩ := mem_stab2_iff_exists_liftS8.1 h2mem
    have hσeq : σ = τ₀ * liftS8 ρ := by
      rw [hρ, ← mul_assoc, tau0_mul_self, one_mul]
    have hρc : ∀ α ∈ alternatingGroup (Fin 8), ρ * α = α * ρ := by
      intro α hα
      have h1 : liftS8 (ρ * α) = liftS8 (α * ρ) := by
        rw [map_mul, map_mul]
        calc liftS8 ρ * liftS8 α = τ₀ * σ * liftS8 α := by rw [hρ]
          _ = τ₀ * (σ * liftS8 α) := by group
          _ = τ₀ * (liftS8 α * σ) := by rw [h _ hα]
          _ = (τ₀ * liftS8 α) * σ := by group
          _ = (liftS8 α * τ₀) * σ := by rw [liftS8_mul_τ₀]
          _ = liftS8 α * (τ₀ * σ) := by group
          _ = liftS8 α * liftS8 ρ := by rw [← hρ]
      exact liftS8_injective h1
    have hρ1 : ρ = 1 := lGC_perm_eight_eq_one_of_centralizes hρc
    right
    rw [hσeq, hρ1, map_one, mul_one]

private theorem lGC_pairOrder_z_pow_mul (z : G) (i : Fin 2) (A : G) :
    pairOrder z (z ^ (i : ℕ) * A) = pairOrder z A := by
  have hsub : centralizer ({z} : Set G) ⊓ centralizer ({z ^ (i : ℕ) * A} : Set G) =
      centralizer ({z} : Set G) ⊓ centralizer ({A} : Set G) := by
    apply le_antisymm
    · intro g hg
      rw [Subgroup.mem_inf] at hg
      obtain ⟨hgz, hgzA⟩ := hg
      refine Subgroup.mem_inf.mpr ⟨hgz, ?_⟩
      rw [mem_centralizer_singleton_iff] at hgz hgzA ⊢
      have hzi : g * z ^ (i : ℕ) = z ^ (i : ℕ) * g :=
        ((show Commute g z from hgz).pow_right i).eq
      calc g * A = (z ^ (i : ℕ))⁻¹ * (z ^ (i : ℕ) * (g * A)) := by group
        _ = (z ^ (i : ℕ))⁻¹ * ((z ^ (i : ℕ) * g) * A) := by group
        _ = (z ^ (i : ℕ))⁻¹ * ((g * z ^ (i : ℕ)) * A) := by rw [← hzi]
        _ = (z ^ (i : ℕ))⁻¹ * (g * (z ^ (i : ℕ) * A)) := by group
        _ = (z ^ (i : ℕ))⁻¹ * ((z ^ (i : ℕ) * A) * g) := by rw [hgzA]
        _ = A * g := by group
    · intro g hg
      rw [Subgroup.mem_inf] at hg
      obtain ⟨hgz, hgA⟩ := hg
      refine Subgroup.mem_inf.mpr ⟨hgz, ?_⟩
      rw [mem_centralizer_singleton_iff] at hgz hgA ⊢
      have hzi : g * z ^ (i : ℕ) = z ^ (i : ℕ) * g :=
        ((show Commute g z from hgz).pow_right i).eq
      calc g * (z ^ (i : ℕ) * A) = (g * z ^ (i : ℕ)) * A := by group
        _ = (z ^ (i : ℕ) * g) * A := by rw [hzi]
        _ = z ^ (i : ℕ) * (g * A) := by group
        _ = z ^ (i : ℕ) * (A * g) := by rw [hgA]
        _ = (z ^ (i : ℕ) * A) * g := by group
  rw [pairOrder, pairOrder, hsub]

private theorem lGC_commutator_central_mul {e₁ e₂ a₁ a₂ : G}
    (h₁ : e₁ * a₁ = a₁ * e₁) (h₂ : e₁ * a₂ = a₂ * e₁)
    (h₃ : e₂ * a₁ = a₁ * e₂) (h₄ : e₂ * a₂ = a₂ * e₂)
    (h₅ : e₁ * e₂ = e₂ * e₁) :
    ⁅e₁ * a₁, e₂ * a₂⁆ = ⁅a₁, a₂⁆ := by
  have h₁c : Commute e₁ a₁ := h₁
  have h₂c : Commute e₁ a₂ := h₂
  have h₃c : Commute e₂ a₁ := h₃
  have h₄c : Commute e₂ a₂ := h₄
  have huv : Commute e₁ e₂ := h₅
  have huC : Commute e₁ ⁅a₁, a₂⁆ := by
    rw [commutatorElement_def]
    simpa only [mul_assoc] using
      (h₁c.mul_right h₂c).mul_right (h₁c.inv_right.mul_right h₂c.inv_right)
  have hvC : Commute e₂ ⁅a₁, a₂⁆ := by
    rw [commutatorElement_def]
    simpa only [mul_assoc] using
      (h₃c.mul_right h₄c).mul_right (h₃c.inv_right.mul_right h₄c.inv_right)
  have h6 : ⁅e₁, e₂ * a₂⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    calc e₁ * (e₂ * a₂) = (e₁ * e₂) * a₂ := by group
      _ = (e₂ * e₁) * a₂ := by rw [h₅]
      _ = e₂ * (e₁ * a₂) := by group
      _ = e₂ * (a₂ * e₁) := by rw [h₂]
      _ = (e₂ * a₂) * e₁ := by group
  have h7 : ⁅a₁, e₂⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact h₃.symm
  have h8 : ⁅a₁, e₂ * a₂⁆ = e₂ * ⁅a₁, a₂⁆ * e₂⁻¹ := by
    rw [commutatorElement_mul_right_eq_mul_conj, h7, one_mul]
  rw [commutatorElement_mul_left_eq_conj_mul, h6, h8, mul_one]
  have hX : Commute e₁ (e₂ * ⁅a₁, a₂⁆ * e₂⁻¹) :=
    (huv.mul_right huC).mul_right huv.inv_right
  calc e₁ * (e₂ * ⁅a₁, a₂⁆ * e₂⁻¹) * e₁⁻¹
      = (e₂ * ⁅a₁, a₂⁆ * e₂⁻¹) * e₁ * e₁⁻¹ := by rw [hX.eq]
    _ = e₂ * ⁅a₁, a₂⁆ * e₂⁻¹ := by group
    _ = ⁅a₁, a₂⁆ := by rw [hvC.eq]; group

theorem mem_Siggrp_iff {s : G} : s ∈ Siggrp ι ↔ ∃ ρ : Perm (Fin 8), ι (liftS8 ρ) = s := by
  simp only [Siggrp, MonoidHom.mem_range, MonoidHom.comp_apply]

theorem mem_Agrp_iff {a : G} :
    a ∈ Agrp ι ↔ ∃ ρ ∈ alternatingGroup (Fin 8), ι (liftS8 ρ) = a := by
  simp only [Agrp, Subgroup.mem_map, MonoidHom.comp_apply]

theorem Agrp_le_Siggrp : Agrp ι ≤ Siggrp ι := by
  simpa [Agrp, Siggrp] using Subgroup.map_le_range (ι.comp liftS8) (alternatingGroup (Fin 8))

theorem mem_Egrp_iff (hC : CentData z ι) {e : G} :
    e ∈ Egrp z ι ↔ ∃ i j : Fin 2, e = z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) := by
  classical
  have hE : Egrp z ι = Tgrp z ι (Subgroup.zpowers τ₀) := by
    rw [Egrp, Tgrp, MonoidHom.map_zpowers]
  rw [hE]
  constructor
  · intro he
    obtain ⟨i, q, hq, heq⟩ := (mem_Tgrp_iff hC).mp he
    have hfoτ : IsOfFinOrder τ₀ :=
      isOfFinOrder_iff_pow_eq_one.mpr
        ⟨2, by norm_num, by rw [pow_two]; exact tau0_mul_self⟩
    rw [hfoτ.mem_zpowers_iff_mem_range_orderOf] at hq
    obtain ⟨m, hm, hmq⟩ := Finset.mem_image.mp hq
    have hm2 : m < 2 := by
      have := Finset.mem_range.mp hm
      rwa [lGC_tau0_orderOf] at this
    refine ⟨i, ⟨m, hm2⟩, ?_⟩
    rw [heq, ← hmq, map_pow]
  · rintro ⟨i, j, rfl⟩
    exact (mem_Tgrp_iff hC).mpr
      ⟨i, τ₀ ^ (j : ℕ), pow_mem (Subgroup.mem_zpowers τ₀) j, by rw [map_pow]⟩

theorem mem_CEgrp_iff (hC : CentData z ι) {c : G} :
    c ∈ CEgrp z ι ↔ ∃ (i j : Fin 2) (ρ : Perm (Fin 8)),
      c = z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι (liftS8 ρ) := by
  constructor
  · intro hc
    obtain ⟨hcz, hcx⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨σ, hσ⟩ := hC.cases c hcz
    have hcx' : c * ι τ₀ = ι τ₀ * c := mem_centralizer_singleton_iff.mp hcx
    have hcommτ : σ * τ₀ = τ₀ * σ := by
      apply hC.inj
      rw [map_mul, map_mul]
      rcases hσ with h | h
      · rw [h] at hcx'; exact hcx'
      · have h1 : z * (ι σ * ι τ₀) = z * (ι τ₀ * ι σ) := by
          calc z * (ι σ * ι τ₀) = (z * ι σ) * ι τ₀ := by group
            _ = ι τ₀ * (z * ι σ) := by rw [← h]; exact hcx'
            _ = (ι τ₀ * z) * ι σ := by group
            _ = (z * ι τ₀) * ι σ := by rw [hC.comm τ₀]
            _ = z * (ι τ₀ * ι σ) := by group
        exact mul_left_cancel h1
    have hσcent : σ ∈ centralizer ({τ₀} : Set (Perm (Fin 10))) :=
      mem_centralizer_singleton_iff.mpr hcommτ
    rcases apply_eight_mem_pair_of_mem_centralizer hσcent with ⟨h8, h9⟩ | ⟨h89, h98⟩
    · obtain ⟨ρ, hρ⟩ := mem_stab2_iff_exists_liftS8.1 (mem_stab2.2 ⟨h8, h9⟩)
      rcases hσ with h | h
      · exact ⟨0, 0, ρ, by rw [h, ← hρ]; simp⟩
      · exact ⟨1, 0, ρ, by rw [h, ← hρ]; simp⟩
    · have h2mem : τ₀ * σ ∈ stab2 8 9 := by
        rw [mem_stab2]
        exact ⟨by simp [Perm.mul_apply, h89, τ₀], by simp [Perm.mul_apply, h98, τ₀]⟩
      obtain ⟨ρ, hρ⟩ := mem_stab2_iff_exists_liftS8.1 h2mem
      have hσeq : σ = τ₀ * liftS8 ρ := by
        rw [hρ, ← mul_assoc, tau0_mul_self, one_mul]
      rcases hσ with h | h
      · exact ⟨0, 1, ρ, by rw [h, hσeq, map_mul]; simp⟩
      · exact ⟨1, 1, ρ, by rw [h, hσeq, map_mul]; simp only [Fin.val_zero, Fin.val_one,
          pow_zero, pow_one, one_mul]; group⟩
  · rintro ⟨i, j, ρ, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      have hzC : Commute z (z ^ (i : ℕ)) := (Commute.refl z).pow_right i
      have hxC : Commute z ((ι τ₀) ^ (j : ℕ)) :=
        (show Commute z (ι τ₀) from hC.comm τ₀).pow_right j
      have hrC : Commute z (ι (liftS8 ρ)) :=
        show Commute z (ι (liftS8 ρ)) from hC.comm (liftS8 ρ)
      exact ((hzC.mul_right hxC).mul_right hrC).symm
    · rw [mem_centralizer_singleton_iff]
      have hzC : Commute (ι τ₀) (z ^ (i : ℕ)) :=
        (show Commute (ι τ₀) z from (hC.comm τ₀).symm).pow_right i
      have hxC : Commute (ι τ₀) ((ι τ₀) ^ (j : ℕ)) := (Commute.refl (ι τ₀)).pow_right j
      have hrC : Commute (ι τ₀) (ι (liftS8 ρ)) :=
        (mem_centralizer_singleton_iff.mp (lGC_iota_liftS8_mem_centralizer ι ρ)).symm
      exact ((hzC.mul_right hxC).mul_right hrC).symm

theorem Egrp_le_CEgrp (hC : CentData z ι) : Egrp z ι ≤ CEgrp z ι := by
  rw [Egrp, CEgrp]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
    · rw [mem_centralizer_singleton_iff]; exact hC.comm τ₀
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]; exact (hC.comm τ₀).symm
    · rw [mem_centralizer_singleton_iff]

theorem Siggrp_le_CEgrp (hC : CentData z ι) : Siggrp ι ≤ CEgrp z ι := by
  intro s hs
  rw [mem_Siggrp_iff] at hs
  obtain ⟨ρ, rfl⟩ := hs
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_centralizer_singleton_iff]; exact (hC.comm (liftS8 ρ)).symm
  · rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_singleton_iff.mp (lGC_iota_liftS8_mem_centralizer ι ρ)

theorem Egrp_inf_Siggrp (hC : CentData z ι) : Egrp z ι ⊓ Siggrp ι = ⊥ := by
  rw [eq_bot_iff]
  intro e he
  rw [Subgroup.mem_bot]
  obtain ⟨heE, heS⟩ := Subgroup.mem_inf.mp he
  obtain ⟨i, j, hij⟩ := (mem_Egrp_iff hC).mp heE
  obtain ⟨ρ, hρ⟩ := (mem_Siggrp_iff).mp heS
  have heq : ι (liftS8 ρ) = z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) := hρ.trans hij
  have hx1inv : (ι τ₀)⁻¹ = ι τ₀ := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right tau0_mul_self]
  rw [hij]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at heq ⊢
  · simp
  · exfalso
    rw [one_mul] at heq
    have h2 : liftS8 ρ = τ₀ := hC.inj heq
    have h3 := congrArg (fun f : Perm (Fin 10) => f 8) h2
    rw [liftS8_apply_eight, τ₀] at h3
    simp at h3
  · exfalso
    rw [mul_one] at heq
    exact hC.ne_z (liftS8 ρ) heq
  · exfalso
    have hthis : ι (liftS8 ρ * τ₀) = z := by
      calc ι (liftS8 ρ * τ₀) = ι (liftS8 ρ) * ι τ₀ := by rw [map_mul]
        _ = (z * ι τ₀) * ι τ₀ := by rw [heq]
        _ = z * (ι τ₀ * ι τ₀) := by group
        _ = z * 1 := by rw [lGC_iota_tau0_mul_self hC]
        _ = z := mul_one z
    exact hC.ne_z (liftS8 ρ * τ₀) hthis

theorem card_Egrp (hC : CentData z ι) : Nat.card (Egrp z ι) = 4 := by
  have hE : Egrp z ι = Tgrp z ι (Subgroup.zpowers τ₀) := by
    rw [Egrp, Tgrp, MonoidHom.map_zpowers]
  rw [hE, Tgrp_card hC, Nat.card_zpowers, lGC_tau0_orderOf]

theorem mul_comm_of_mem_Egrp_of_mem_CEgrp (hC : CentData z ι) {e c : G} (he : e ∈ Egrp z ι)
    (hc : c ∈ CEgrp z ι) : e * c = c * e := by
  have hle : Egrp z ι ≤ centralizer ({c} : Set G) := by
    rw [Egrp]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).1).symm
    · rw [Subgroup.zpowers_le]
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2).symm
  exact mem_centralizer_singleton_iff.mp (hle he)

private theorem lGC_Egrp_le_centralizer_Agrp (hC : CentData z ι) :
    Egrp z ι ≤ centralizer (Agrp ι : Set G) := by
  rw [Egrp]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨α, -, rfl⟩ := (mem_Agrp_iff).mp ha
    exact (hC.comm (liftS8 α)).symm
  · rw [Subgroup.zpowers_le]
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨α, -, rfl⟩ := (mem_Agrp_iff).mp ha
    exact mem_centralizer_singleton_iff.mp (lGC_iota_liftS8_mem_centralizer ι α)

theorem centralizer_Agrp_inf_CEgrp (hC : CentData z ι) :
    centralizer (Agrp ι : Set G) ⊓ CEgrp z ι = Egrp z ι := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hcA, hcCE⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨i, j, ρ, rfl⟩ := (mem_CEgrp_iff hC).mp hcCE
    have hzA : z ∈ centralizer (Agrp ι : Set G) :=
      lGC_Egrp_le_centralizer_Agrp hC (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
    have hxA : ι τ₀ ∈ centralizer (Agrp ι : Set G) :=
      lGC_Egrp_le_centralizer_Agrp hC (Subgroup.mem_sup_right (Subgroup.mem_zpowers (ι τ₀)))
    have hρA : ι (liftS8 ρ) ∈ centralizer (Agrp ι : Set G) := by
      have h1 : (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ))⁻¹ ∈ centralizer (Agrp ι : Set G) :=
        inv_mem (mul_mem (pow_mem hzA i) (pow_mem hxA j))
      have h2 := mul_mem h1 hcA
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2
    have hρ_comm : ∀ α ∈ alternatingGroup (Fin 8), ρ * α = α * ρ := by
      intro α hα
      have hαA : ι (liftS8 α) ∈ Agrp ι := (mem_Agrp_iff).mpr ⟨α, hα, rfl⟩
      have hc := (mem_centralizer_iff.mp hρA) (ι (liftS8 α)) hαA
      have h3 : liftS8 (α * ρ) = liftS8 (ρ * α) := by
        rw [map_mul, map_mul]
        apply hC.inj
        rw [map_mul, map_mul]
        exact hc
      exact (liftS8_injective h3).symm
    have hρ1 : ρ = 1 := lGC_perm_eight_eq_one_of_centralizes hρ_comm
    rw [hρ1]
    simp only [map_one, mul_one]
    exact Subgroup.mul_mem_sup (pow_mem (Subgroup.mem_zpowers z) i)
      (pow_mem (Subgroup.mem_zpowers (ι τ₀)) j)
  · exact le_inf (lGC_Egrp_le_centralizer_Agrp hC) (Egrp_le_CEgrp hC)

theorem centralizer_Agrp_inf_centralizer_z (hC : CentData z ι) :
    centralizer (Agrp ι : Set G) ⊓ centralizer ({z} : Set G) = Egrp z ι := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hcA, hcz⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨σ, hσ⟩ := hC.cases c hcz
    have hσ_comm : ∀ α ∈ alternatingGroup (Fin 8), σ * liftS8 α = liftS8 α * σ := by
      intro α hα
      have hαA : ι (liftS8 α) ∈ Agrp ι := (mem_Agrp_iff).mpr ⟨α, hα, rfl⟩
      have hcα := (mem_centralizer_iff.mp hcA) (ι (liftS8 α)) hαA
      rcases hσ with h | h
      · rw [h] at hcα
        apply hC.inj
        rw [map_mul, map_mul]
        exact hcα.symm
      · rw [h] at hcα
        have hzL : z * ι (liftS8 α) = ι (liftS8 α) * z := hC.comm (liftS8 α)
        have h1 : z * (ι (liftS8 α) * ι σ) = z * (ι σ * ι (liftS8 α)) := by
          calc z * (ι (liftS8 α) * ι σ) = (z * ι (liftS8 α)) * ι σ := by group
            _ = (ι (liftS8 α) * z) * ι σ := by rw [hzL]
            _ = ι (liftS8 α) * (z * ι σ) := by group
            _ = (z * ι σ) * ι (liftS8 α) := hcα
            _ = z * (ι σ * ι (liftS8 α)) := by group
        apply hC.inj
        rw [map_mul, map_mul]
        exact (mul_left_cancel h1).symm
    have hperm : σ = 1 ∨ σ = τ₀ := lGC_perm_ten_eq_one_or_tau_of_centralizes hσ_comm
    rcases hσ with hc | hc
    · rcases hperm with h | h
      · rw [hc, h, map_one]; exact one_mem _
      · rw [hc, h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (ι τ₀))
    · rcases hperm with h | h
      · rw [hc, h]
        simp only [map_one, mul_one]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
      · rw [hc, h]
        exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers z)
          (Subgroup.mem_zpowers (ι τ₀))
  · refine le_inf (lGC_Egrp_le_centralizer_Agrp hC) ?_
    rw [Egrp]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, mem_centralizer_singleton_iff]
    · rw [Subgroup.zpowers_le, mem_centralizer_singleton_iff]
      exact (hC.comm τ₀).symm

theorem commutator_CEgrp (hC : CentData z ι) : ⁅CEgrp z ι, CEgrp z ι⁆ = Agrp ι := by
  have hSigComm : ⁅Siggrp ι, Siggrp ι⁆ = Agrp ι := by
    rw [Siggrp, Agrp, MonoidHom.range_eq_map,
      ← Subgroup.map_commutator (H₁ := ⊤) (H₂ := ⊤) (f := ι.comp liftS8)]
    congr 1
    exact alternatingGroup.commutator_perm_eq (α := Fin 8) (by norm_num)
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro c1 hc1 c2 hc2
    obtain ⟨i, j, ρ, rfl⟩ := (mem_CEgrp_iff hC).mp hc1
    obtain ⟨k, l, ρ', rfl⟩ := (mem_CEgrp_iff hC).mp hc2
    have he₁ : z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) ∈ Egrp z ι :=
      Subgroup.mul_mem_sup (pow_mem (Subgroup.mem_zpowers z) i)
        (pow_mem (Subgroup.mem_zpowers (ι τ₀)) j)
    have he₂ : z ^ (k : ℕ) * (ι τ₀) ^ (l : ℕ) ∈ Egrp z ι :=
      Subgroup.mul_mem_sup (pow_mem (Subgroup.mem_zpowers z) k)
        (pow_mem (Subgroup.mem_zpowers (ι τ₀)) l)
    have ha₁ : ι (liftS8 ρ) ∈ CEgrp z ι :=
      Siggrp_le_CEgrp hC ((mem_Siggrp_iff).mpr ⟨ρ, rfl⟩)
    have ha₂ : ι (liftS8 ρ') ∈ CEgrp z ι :=
      Siggrp_le_CEgrp hC ((mem_Siggrp_iff).mpr ⟨ρ', rfl⟩)
    have hcomm := lGC_commutator_central_mul
      (e₁ := z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ))
      (e₂ := z ^ (k : ℕ) * (ι τ₀) ^ (l : ℕ))
      (a₁ := ι (liftS8 ρ)) (a₂ := ι (liftS8 ρ'))
      (mul_comm_of_mem_Egrp_of_mem_CEgrp hC he₁ ha₁)
      (mul_comm_of_mem_Egrp_of_mem_CEgrp hC he₁ ha₂)
      (mul_comm_of_mem_Egrp_of_mem_CEgrp hC he₂ ha₁)
      (mul_comm_of_mem_Egrp_of_mem_CEgrp hC he₂ ha₂)
      (mul_comm_of_mem_Egrp_of_mem_CEgrp hC he₁ (Egrp_le_CEgrp hC he₂))
    rw [hcomm, ← map_commutatorElement, ← map_commutatorElement (f := liftS8)]
    have hmem : ⁅ρ, ρ'⁆ ∈ alternatingGroup (Fin 8) := by
      rw [← alternatingGroup.commutator_perm_eq (α := Fin 8) (by norm_num)]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top ρ) (Subgroup.mem_top ρ')
    exact (mem_Agrp_iff).mpr ⟨⁅ρ, ρ'⁆, hmem, rfl⟩
  · rw [← hSigComm]
    exact Subgroup.commutator_mono (Siggrp_le_CEgrp hC) (Siggrp_le_CEgrp hC)

theorem Egrp_le_centralizer_Agrp (hC : CentData z ι) :
    Egrp z ι ≤ centralizer (Agrp ι : Set G) := lGC_Egrp_le_centralizer_Agrp hC

theorem pairOrder_z_Fgrp (hC : CentData z ι) (i j : Fin 2) :
    pairOrder z (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι ρ₄) = if j = 0 then N10 4 else N10 5 := by
  have hρ₄sq : ρ₄ * ρ₄ = 1 := by
    rw [← liftS8_ρ₄', ← map_mul, ρ₄'_mul_self, map_one]
  have hcardρ₄ : Multiset.card ρ₄.cycleType = 4 := by
    rw [← liftS8_ρ₄', cycleType_liftS8, card_cycleType_ρ₄']
  rw [mul_assoc, lGC_pairOrder_z_pow_mul z i ((ι τ₀) ^ (j : ℕ) * ι ρ₄)]
  fin_cases j
  · simp only [Fin.val_zero, pow_zero, one_mul]
    rw [pairOrder, hC.card_inf_centralizer ρ₄, two_mul_card_centralizer_perm_ten hρ₄sq,
      hcardρ₄]
    simp
  · simp only [Fin.val_one, pow_one]
    rw [← map_mul, pairOrder, hC.card_inf_centralizer (τ₀ * ρ₄),
      two_mul_card_centralizer_perm_ten τ₀_mul_ρ₄_mul_self, card_cycleType_τ₀_mul_ρ₄]
    simp

theorem pairOrder_x₁_Fgrp [Finite G] (hC : CentData z ι) (hx : IsConj z (ι τ₀)) (i j : Fin 2) :
    pairOrder (ι τ₀) (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι ρ₄) =
      if i = 0 then N10 4 else N10 5 := by
  obtain ⟨ι₁, ε, χ, D⟩ := exists_twistData hC hx
  have hε : ε ρ₄' = 1 := by
    rcases D.eps with h | h
    · rw [h]; rfl
    · rw [h]; exact sign_ρ₄'
  have hcond : ¬ ((1 : ℤˣ) = -1) := by decide
  have hp1 : pairOrder (ι τ₀) (ι ρ₄) = N10 4 := by
    have hp := D.pair_one ρ₄' ρ₄'_mul_self
    rw [liftS8_ρ₄', card_cycleType_ρ₄', hε, if_neg hcond, Nat.add_zero] at hp
    exact hp
  have hp2 : pairOrder (ι τ₀) (z * ι ρ₄) = N10 5 := by
    have hp := D.pair_z ρ₄' ρ₄'_mul_self
    rw [liftS8_ρ₄', card_cycleType_ρ₄', hε, if_neg hcond] at hp
    norm_num at hp
    exact hp
  have hx1ρ : ι τ₀ * ι ρ₄ = ι ρ₄ * ι τ₀ := by
    have h := mem_centralizer_singleton_iff.mp (lGC_iota_liftS8_mem_centralizer ι ρ₄')
    rw [liftS8_ρ₄'] at h
    exact h.symm
  have hx1zρ : ι τ₀ * (z * ι ρ₄) = (z * ι ρ₄) * ι τ₀ := by
    calc ι τ₀ * (z * ι ρ₄) = (ι τ₀ * z) * ι ρ₄ := by group
      _ = (z * ι τ₀) * ι ρ₄ := by rw [hC.comm τ₀]
      _ = z * (ι τ₀ * ι ρ₄) := by group
      _ = z * (ι ρ₄ * ι τ₀) := by rw [hx1ρ]
      _ = (z * ι ρ₄) * ι τ₀ := by group
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one]
  · exact hp1
  · rw [pairOrder_mul_right hx1ρ]; exact hp1
  · exact hp2
  · have heq : z * ι τ₀ * ι ρ₄ = ι τ₀ * (z * ι ρ₄) := by
      calc z * ι τ₀ * ι ρ₄ = (z * ι τ₀) * ι ρ₄ := by group
        _ = (ι τ₀ * z) * ι ρ₄ := by rw [hC.comm τ₀]
        _ = ι τ₀ * (z * ι ρ₄) := by group
    rw [heq, pairOrder_mul_right hx1zρ]
    exact hp2

theorem Tgrp_le_CEgrp (hC : CentData z ι) {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) :
    Tgrp z ι Q ≤ CEgrp z ι := by
  rw [Tgrp, CEgrp]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact Egrp_le_CEgrp hC (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]; exact (hC.comm q).symm
    · rw [mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul]
      congr 1
      exact (hQ.τ₀_comm q hq).symm

theorem Egrp_le_Tgrp (hC : CentData z ι) {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) :
    Egrp z ι ≤ Tgrp z ι Q := by
  rw [Egrp, Tgrp]
  refine sup_le ?_ ?_
  · exact le_sup_left
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem ι hQ.τ₀_mem)

end CFSG.OddStandard.AltStdSec.SwapPartner
