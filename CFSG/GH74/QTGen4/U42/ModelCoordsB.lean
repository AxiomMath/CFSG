module

public import CFSG.GH74.QTGen4.U42.ModelCoords

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5 CFSG.Quasithin.H13.F431.U42 U42F431

section Model


theorem ptL_zero : ptL 0 = 0 := by decide

def restrL (l : List ℕ) (σ : Equiv.Perm (Fin 5)) : Prop :=
  ∀ j : Fin 5, l.getD (ptL j : ℕ) 0 = (ptL (σ j) : ℕ)

instance (l : List ℕ) (σ : Equiv.Perm (Fin 5)) : Decidable (restrL l σ) :=
  inferInstanceAs (Decidable (∀ j : Fin 5, l.getD (ptL j : ℕ) 0 = (ptL (σ j) : ℕ)))

theorem permOf_eq_iff_restrL (t : ↥P2) {l : List ℕ} (hl : RepL l ((t : Y) : P45))
    (σ : Equiv.Perm (Fin 5)) : permOf t = σ ↔ restrL l σ := by
  have hval : ∀ j : Fin 5, ((ptL (permOf t j) : Fin 45) : ℕ) = l.getD (ptL j : ℕ) 0 := by
    intro j
    rw [ptL_permOf, hl.2 (ptL j)]
  unfold restrL
  constructor
  · rintro rfl j
    exact (hval j).symm
  · intro h
    apply Equiv.ext
    intro j
    apply ptL_inj
    apply Fin.ext
    rw [hval j]
    exact h j

theorem model_B0_iff_zero (g : ↥P2) : (g : Y) ∈ B0 ↔ permOf g 0 = 0 := by
  rw [mem_B0_iff]
  constructor
  · rintro ⟨h0, -⟩
    apply ptL_inj
    rw [ptL_permOf, ptL_zero]
    exact h0
  · intro h
    refine ⟨?_, (mem_P2_iff _).1 g.2⟩
    have hp := ptL_permOf g 0
    rw [h, ptL_zero] at hp
    exact hp.symm

def InK4z (σ : Equiv.Perm (Fin 5)) : Prop :=
  σ = 1 ∨ σ = Equiv.swap 1 2 * Equiv.swap 3 4 ∨ σ = Equiv.swap 1 3 * Equiv.swap 2 4 ∨
    σ = Equiv.swap 1 4 * Equiv.swap 2 3

theorem chk_T_K4z : ∀ i < 64, restrL (Tl.getD i []) 1 ∨
    restrL (Tl.getD i []) (Equiv.swap 1 2 * Equiv.swap 3 4) ∨
    restrL (Tl.getD i []) (Equiv.swap 1 3 * Equiv.swap 2 4) ∨
    restrL (Tl.getD i []) (Equiv.swap 1 4 * Equiv.swap 2 3) := by
  decide +kernel

theorem wit_one_z : ∃ i < 64, restrL (Tl.getD i []) 1 := by decide +kernel

theorem wit_12_34 : ∃ i < 64, restrL (Tl.getD i []) (Equiv.swap 1 2 * Equiv.swap 3 4) := by
  decide +kernel

theorem wit_13_24 : ∃ i < 64, restrL (Tl.getD i []) (Equiv.swap 1 3 * Equiv.swap 2 4) := by
  decide +kernel

theorem wit_14_23 : ∃ i < 64, restrL (Tl.getD i []) (Equiv.swap 1 4 * Equiv.swap 2 3) := by
  decide +kernel

theorem model_T_iff_z (g : ↥P2) : (g : Y) ∈ T ↔ InK4z (permOf g) := by
  constructor
  · intro hg
    obtain ⟨i, hi, hrep⟩ := (mem_T_iff (g : Y)).1 hg
    unfold InK4z
    rcases chk_T_K4z i hi with h | h | h | h
    · exact Or.inl ((permOf_eq_iff_restrL g hrep 1).2 h)
    · exact Or.inr (Or.inl ((permOf_eq_iff_restrL g hrep _).2 h))
    · exact Or.inr (Or.inr (Or.inl ((permOf_eq_iff_restrL g hrep _).2 h)))
    · exact Or.inr (Or.inr (Or.inr ((permOf_eq_iff_restrL g hrep _).2 h)))
  · intro hK
    obtain ⟨i, hi, hr⟩ : ∃ i < 64, restrL (Tl.getD i []) (permOf g) := by
      unfold InK4z at hK
      rcases hK with h | h | h | h
      · rw [h]; exact wit_one_z
      · rw [h]; exact wit_12_34
      · rw [h]; exact wit_13_24
      · rw [h]; exact wit_14_23
    obtain ⟨t, htT, htR⟩ := exists_Tel (i := i) hi
    let tP : ↥P2 := ⟨t, T_le_P2' htT⟩
    have hpt : permOf tP = permOf g := (permOf_eq_iff_restrL tP htR (permOf g)).2 hr
    have hinv : permOf tP⁻¹ = (permOf tP)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← permOf_mul, inv_mul_cancel, permOf_one])
    have hk : permOf (g * tP⁻¹) = 1 := by
      rw [permOf_mul, hinv, hpt, mul_inv_cancel]
    have hmem : ((g * tP⁻¹ : ↥P2) : Y) ∈ Vsub := (permOf_eq_one_iff _).1 hk
    have hg_eq : (g : Y) = ((g * tP⁻¹ : ↥P2) : Y) * t := by
      simp [tP]
    rw [hg_eq]
    exact T.mul_mem (Vsub_le_T hmem) htT

theorem exists_T_permOf (p : Equiv.Perm (Fin 5)) (hp : InK4z p) :
    ∃ t : ↥P2, (t : Y) ∈ T ∧ permOf t = p := by
  obtain ⟨i, hi, hr⟩ : ∃ i < 64, restrL (Tl.getD i []) p := by
    unfold InK4z at hp
    rcases hp with h | h | h | h
    · rw [h]; exact wit_one_z
    · rw [h]; exact wit_12_34
    · rw [h]; exact wit_13_24
    · rw [h]; exact wit_14_23
  obtain ⟨t, htT, htR⟩ := exists_Tel (i := i) hi
  let tP : ↥P2 := ⟨t, T_le_P2' htT⟩
  exact ⟨tP, htT, (permOf_eq_iff_restrL tP htR p).2 hr⟩

theorem inK4z_iff_conj (p : Equiv.Perm (Fin 5)) :
    InK4z p ↔ InK4 (sigma0 * p * sigma0⁻¹) := by
  constructor
  · intro h
    unfold InK4z at h
    rcases h with rfl | rfl | rfl | rfl <;> unfold InK4 <;> decide
  · intro h
    have hp : p = sigma0⁻¹ * (sigma0 * p * sigma0⁻¹) * sigma0 := by group
    rw [hp]
    unfold InK4 at h
    rcases h with h | h | h | h <;> rw [h] <;> unfold InK4z <;> decide

theorem model_B0_iff (g : ↥P2) : (g : Y) ∈ B0 ↔ permOf4 g 4 = 4 := by
  have h4 : ∀ q : Equiv.Perm (Fin 5), (sigma0 * q * sigma0⁻¹) 4 = Equiv.swap 0 4 (q 0) := by
    intro q
    have hinv4 : sigma0⁻¹ 4 = 0 := by decide
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv4]
  rw [model_B0_iff_zero, permOf4_apply, h4, Equiv.swap_apply_eq_iff]
  have h40 : Equiv.swap (0 : Fin 5) 4 4 = 0 := by decide
  rw [h40]

theorem model_T_iff (g : ↥P2) : (g : Y) ∈ T ↔ InK4 (permOf4 g) := by
  rw [model_T_iff_z]
  exact inK4z_iff_conj (permOf g)

theorem exists_T_permOf4 (σ : Equiv.Perm (Fin 5)) (hσ : InK4 σ) :
    ∃ t : ↥P2, (t : Y) ∈ T ∧ permOf4 t = σ := by
  have hconj : sigma0 * (sigma0⁻¹ * σ * sigma0) * sigma0⁻¹ = σ := by group
  have hz : InK4z (sigma0⁻¹ * σ * sigma0) := by
    rw [inK4z_iff_conj, hconj]
    exact hσ
  obtain ⟨t, htT, htp⟩ := exists_T_permOf _ hz
  exact ⟨t, htT, by rw [permOf4_apply, htp]; exact hconj⟩

end Model

end CFSG.GH74.QTGen4.U42
