module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowAltSix
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open scoped Pointwise
open Matrix

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowAltSix

namespace SylowL32

abbrev Γ : Type := GL (Fin 3) (ZMod 2)

theorem card_gl : Nat.card Γ = 168 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem smul_eq (g : Γ) (v : Fin 3 → ZMod 2) :
    g • v = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v := rfl

theorem exists_moved (v : Fin 3 → ZMod 2) (hv : v ≠ 0) : ∃ g : Γ, g • v ≠ v := by
  have hv' : ∃ j, v j ≠ 0 := by
    by_contra h
    exact hv (funext fun j => by_contra fun hj => h ⟨j, hj⟩)
  obtain ⟨j, hj⟩ := hv'
  have hex : ∀ j : Fin 3, ∃ i : Fin 3, i ≠ j := by decide
  obtain ⟨i, hij⟩ := hex j
  have hdet : IsUnit (Matrix.det (Matrix.transvection i j (1 : ZMod 2))) := by
    rw [Matrix.det_transvection_of_ne i j hij]
    exact isUnit_one
  refine ⟨Matrix.GeneralLinearGroup.mk'' _ hdet, ?_⟩
  intro h
  have h2 := congrFun h i
  have hval : ((Matrix.GeneralLinearGroup.mk'' _ hdet : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      Matrix.transvection i j (1 : ZMod 2) := rfl
  rw [smul_eq, hval] at h2
  simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, hij] at h2
  exact hj h2

theorem card_nonzero : Nat.card {w : Fin 3 → ZMod 2 // w ≠ 0} = 7 := by
  rw [Nat.card_eq_fintype_card]
  decide

end SylowL32

open SylowL32 in
theorem exists_order_three_permuting_sylow_two_gl32 (hs : IsSimpleGroup Γ) (S : Subgroup Γ)
    (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.index) :
    ∃ P : Subgroup Γ, Nat.card P = 3 ∧ (S : Set Γ) * P = (P : Set Γ) * S := by
  have hScard : Nat.card S = 8 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hS2
    have h := Subgroup.card_mul_index S
    rw [hn, card_gl] at h
    have hn7 : n ≤ 7 := by
      by_contra hc
      have hc : 7 < n := not_le.mp hc
      have : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc
      have hi : 0 < S.index := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hSidx)
      nlinarith
    interval_cases n <;> first | omega | (exfalso; apply hSidx; omega)
  obtain ⟨v, hv0, hvS⟩ : ∃ v : Fin 3 → ZMod 2, v ≠ 0 ∧ ∀ s : S, (s : Γ) • v = v := by
    have hmod := IsPGroup.card_modEq_card_fixedPoints (p := 2) (G := ↥S) (α := Fin 3 → ZMod 2)
      hS2
    have hcard8 : Nat.card (Fin 3 → ZMod 2) = 8 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [hcard8] at hmod
    have hzero : (0 : Fin 3 → ZMod 2) ∈ MulAction.fixedPoints (↥S) (Fin 3 → ZMod 2) := by
      intro s
      show (s : Γ) • (0 : Fin 3 → ZMod 2) = 0
      rw [smul_eq]
      simp
    by_contra hne
    have hsub : MulAction.fixedPoints (↥S) (Fin 3 → ZMod 2) ⊆ {0} := by
      intro w hw
      by_contra hw0
      exact hne ⟨w, hw0, fun s => hw s⟩
    have hle : Nat.card (MulAction.fixedPoints (↥S) (Fin 3 → ZMod 2)) ≤ 1 := by
      have : Nat.card (MulAction.fixedPoints (↥S) (Fin 3 → ZMod 2)) ≤ Nat.card ({0} : Set (Fin 3 → ZMod 2)) :=
        Nat.card_mono (Set.toFinite _) hsub
      simpa using this
    have hpos : 0 < Nat.card (MulAction.fixedPoints (↥S) (Fin 3 → ZMod 2)) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨0, hzero⟩⟩, inferInstance⟩
    have h1 : Nat.card (MulAction.fixedPoints (↥S) (Fin 3 → ZMod 2)) = 1 := by omega
    rw [h1] at hmod
    exact absurd hmod (by decide)
  set H : Subgroup Γ := MulAction.stabilizer Γ v with hH
  have hSH : S ≤ H := fun x hx => hvS ⟨x, hx⟩
  have horb : Nat.card (MulAction.orbit Γ v) * Nat.card H = 168 := by
    have h1 := Subgroup.card_mul_index H
    rw [MulAction.index_stabilizer, card_gl] at h1
    rw [mul_comm]
    exact h1
  have hle7 : Nat.card (MulAction.orbit Γ v) ≤ 7 := by
    have hsub : MulAction.orbit Γ v ⊆ {w | w ≠ 0} := by
      rintro _ ⟨g, rfl⟩ h0
      apply hv0
      have := congrArg (fun w => g⁻¹ • w) h0
      simpa [smul_eq] using this
    have := Nat.card_mono (Set.toFinite {w : Fin 3 → ZMod 2 | w ≠ 0}) hsub
    rw [show Nat.card {w : Fin 3 → ZMod 2 | w ≠ 0} = 7 from card_nonzero] at this
    exact this
  have h8 : 8 ∣ Nat.card H := hScard ▸ Subgroup.card_dvd_of_le hSH
  have hHcard : Nat.card H = 24 := by
    obtain ⟨m, hm⟩ := h8
    rw [hm] at horb
    have hcases : Nat.card (MulAction.orbit Γ v) = 1 ∨ Nat.card (MulAction.orbit Γ v) = 3 ∨
        Nat.card (MulAction.orbit Γ v) = 7 := by
      generalize Nat.card (MulAction.orbit Γ v) = o at *
      interval_cases o <;> omega
    have hnot : ¬ Nat.card (MulAction.orbit Γ v) ≤ 3 := by
      intro hle3
      set φ := MulAction.toPermHom Γ (MulAction.orbit Γ v) with hφ
      rcases hs.eq_bot_or_eq_top_of_normal φ.ker with hk | hk
      · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hk
        have h1 := Nat.card_le_card_of_injective φ hinj
        rw [Nat.card_perm, card_gl] at h1
        have h2 : (Nat.card (MulAction.orbit Γ v)).factorial ≤ (3 : ℕ).factorial :=
          Nat.factorial_le hle3
        have h3 : (3 : ℕ).factorial = 6 := by decide
        omega
      · obtain ⟨g, hg⟩ := exists_moved v hv0
        have hgk : g ∈ φ.ker := hk ▸ Subgroup.mem_top g
        have h1 : φ g = 1 := hgk
        have h2 := congrArg (fun σ => (σ ⟨v, MulAction.mem_orbit_self v⟩ :
          MulAction.orbit Γ v).1) h1
        apply hg
        simpa [hφ] using h2
    rcases hcases with h | h | h
    · exact absurd (by omega) hnot
    · exact absurd (by omega) hnot
    · rw [h] at horb
      omega
  obtain ⟨P, hPH, hPcard⟩ : ∃ P : Subgroup Γ, P ≤ H ∧ Nat.card P = 3 := by
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 1)
      (by rw [hHcard]; norm_num)
    refine ⟨K.map H.subtype, ?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · rw [Subgroup.card_map_of_injective Subtype.val_injective, hK]
      norm_num
  have hSP : S ⊓ P = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h1 : Nat.card (S ⊓ P : Subgroup Γ) ∣ Nat.card S := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (S ⊓ P : Subgroup Γ) ∣ Nat.card P := Subgroup.card_dvd_of_le inf_le_right
    rw [hScard] at h1
    rw [hPcard] at h2
    have h3 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 8 3 = 1 by norm_num] at h3
    exact Nat.dvd_one.mp h3
  have e1 : (S : Set Γ) * (P : Set Γ) = (H : Set Γ) :=
    set_mul_eq_of_card S P H hSH hPH hSP (by rw [hScard, hPcard, hHcard])
  have e2 : (P : Set Γ) * (S : Set Γ) = (H : Set Γ) :=
    set_mul_eq_of_card P S H hPH hSH (by rw [inf_comm]; exact hSP)
      (by rw [hScard, hPcard, hHcard])
  exact ⟨P, hPcard, by rw [e1, e2]⟩

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
