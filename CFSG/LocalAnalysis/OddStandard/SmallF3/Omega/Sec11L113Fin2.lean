module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Def

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Equiv

theorem sec113_exists_typeA :
    ∀ σ : Perm (Fin 6), Perm.sign σ = 1 → ((σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) →
      σ ^ 8 = 1 → σ ∉ sec11V4 → ∃ v ∈ sec11V4, Sec113TypeA (σ * v) := by
  unfold sec11V4 Sec113TypeA
  decide +kernel

theorem sec113_exists_typeS :
    ∀ σ : Perm (Fin 6), ((σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) →
      σ ^ 16 = 1 → σ ∉ sec11V4 ∪ sec11V4.image (fun s => swap 0 1 * s) →
      ∃ ε ∈ ({1, swap 0 1} : Finset (Perm (Fin 6))), ∃ v ∈ sec11V4,
        Sec113TypeS (ε * σ * v) := by
  unfold sec11V4 Sec113TypeS
  decide +kernel

theorem sec113_conj_typeA_aux : ∀ σ : Perm (Fin 6),
    ((σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) → ∀ a b : Fin 6, 2 ≤ a → 2 ≤ b → a ≠ b →
      2 ≤ σ a ∧ 2 ≤ σ b ∧ σ a ≠ σ b ∧
        σ * (swap 0 1 * swap a b) * σ⁻¹ = swap 0 1 * swap (σ a) (σ b) := by
  decide +kernel

theorem sec113_conj_typeS_aux : ∀ σ : Perm (Fin 6),
    ((σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) → ∀ a b : Fin 6, 2 ≤ a → 2 ≤ b → a ≠ b →
      2 ≤ σ a ∧ 2 ≤ σ b ∧ σ a ≠ σ b ∧ σ * swap a b * σ⁻¹ = swap (σ a) (σ b) := by
  decide +kernel

theorem Sec113TypeA.conj {σ τ : Perm (Fin 6)}
    (hσ : (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) (hτ : Sec113TypeA τ) :
    Sec113TypeA (σ * τ * σ⁻¹) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hτ
  obtain ⟨h1, h2, h3, h4⟩ := sec113_conj_typeA_aux σ hσ a b ha hb hab
  exact ⟨σ a, σ b, h1, h2, h3, h4⟩

theorem Sec113TypeS.conj {σ τ : Perm (Fin 6)}
    (hσ : (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) (hτ : Sec113TypeS τ) :
    Sec113TypeS (σ * τ * σ⁻¹) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hτ
  obtain ⟨h1, h2, h3, h4⟩ := sec113_conj_typeS_aux σ hσ a b ha hb hab
  exact ⟨σ a, σ b, h1, h2, h3, h4⟩

theorem sec113_conjA6_aux : ∀ a b : Fin 6, 2 ≤ a → 2 ≤ b → a ≠ b →
    ∃ g : Perm (Fin 6), Perm.sign g = 1 ∧
      g * (swap 2 3 * swap 4 5) * g⁻¹ = swap 0 1 * swap a b := by
  decide +kernel

theorem sec113_conjA6 {τ : Perm (Fin 6)} (hτ : Sec113TypeA τ) :
    ∃ g ∈ alternatingGroup (Fin 6), g * (swap 2 3 * swap 4 5) * g⁻¹ = τ := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hτ
  obtain ⟨g, hg, h⟩ := sec113_conjA6_aux a b ha hb hab
  exact ⟨g, Equiv.Perm.mem_alternatingGroup.mpr hg, h⟩

theorem sec113_conjS6_aux : ∀ a b : Fin 6, 2 ≤ a → 2 ≤ b → a ≠ b →
    (swap 0 a * swap 1 b) * swap 0 1 * (swap 0 a * swap 1 b)⁻¹ = swap a b := by
  decide +kernel

theorem sec113_conjS6 {τ : Perm (Fin 6)} (hτ : Sec113TypeS τ) :
    ∃ g : Perm (Fin 6), g * swap 0 1 * g⁻¹ = τ := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hτ
  exact ⟨swap 0 a * swap 1 b, sec113_conjS6_aux a b ha hb hab⟩

theorem sec113_typeA_not_V4 {τ : Perm (Fin 6)} (hτ : Sec113TypeA τ) : τ ∉ sec11V4 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hτ
  revert a b
  unfold sec11V4
  decide +kernel

theorem sec113_typeS_not_F8 {τ : Perm (Fin 6)} (hτ : Sec113TypeS τ) :
    τ ∉ sec11V4 ∪ sec11V4.image (fun s => swap 0 1 * s) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hτ
  revert a b
  unfold sec11V4
  decide +kernel

theorem sec113_cardV4 : sec11V4.card = 4 := by
  unfold sec11V4
  decide +kernel

theorem sec113_cardF8 : (sec11V4 ∪ sec11V4.image (fun s => swap 0 1 * s)).card = 8 := by
  unfold sec11V4
  decide +kernel

theorem Sec113TypeS.fix {τ : Perm (Fin 6)} (hτ : Sec113TypeS τ) :
    τ 0 = 0 ∧ τ 1 = 1 ∧ τ * swap 0 1 = swap 0 1 * τ := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hτ
  revert a b
  decide +kernel

theorem sec113_cent_vec : ∀ v : Fin 6 → ZMod 2,
    (permVec (swap 2 3 * swap 4 5) v + v = 0 ∨
      permVec (swap 2 3 * swap 4 5) v + v = fun _ => 1) →
    (permVec (swap 2 4 * swap 3 5) v + v = 0 ∨
      permVec (swap 2 4 * swap 3 5) v + v = fun _ => 1) →
    (v = 0 ∨ v = fun _ => 1) ∨ (v = Pi.single 0 1 ∨ v = Pi.single 0 1 + fun _ => 1) ∨
      (v = Pi.single 1 1 ∨ v = Pi.single 1 1 + fun _ => 1) ∨
      (v = Pi.single 0 1 + Pi.single 1 1 ∨ v = Pi.single 0 1 + Pi.single 1 1 + fun _ => 1) := by
  decide +kernel

theorem sec113_decomp : ∀ v : Fin 6 → ZMod 2, ∃ w : Fin 6 → ZMod 2,
    (∑ i, w i = 0 ∧ w 0 = w 1) ∧
      (v = w ∨ v = w + Pi.single 0 1 ∨ v = w + Pi.single 2 1 ∨
        v = w + (Pi.single 0 1 + Pi.single 2 1)) := by
  decide +kernel

theorem sec113_seed_vec :
    permVec (swap (2 : Fin 6) 3 * swap 4 5)
        (Pi.single (2 : Fin 6) (1 : ZMod 2) + Pi.single (4 : Fin 6) (1 : ZMod 2)) =
      (Pi.single (0 : Fin 6) (1 : ZMod 2) + Pi.single (1 : Fin 6) (1 : ZMod 2)) +
        (Pi.single (2 : Fin 6) (1 : ZMod 2) + Pi.single (4 : Fin 6) (1 : ZMod 2)) +
          fun _ => (1 : ZMod 2) := by
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
