module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46Fus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46Ktk

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

theorem comm_refl_pTE : ∀ e : ZMod 8, dbit8 e = 0 → ∀ (u : (ZMod 8)ˣ) (b : ZMod 8), dbit8 b = 0 →
    aff8 u b * aff8 (-1) e = aff8 (-1) e * aff8 u b →
      ((pE 0 (-1) e → pE 0 u b) ∧ (pE 2 (-1) e → pE 2 u b)) := by
  intro e he u b hb
  simp only [aff8_mul, aff8_eq_iff]
  revert e u b
  decide

theorem dbit8_add_even : ∀ s e : ZMod 8, (s = 2 ∨ s = 6) → dbit8 e = 0 → dbit8 (s + e) = 0 := by
  decide

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} (S : KDBase A C)

theorem TE_le_C : S.TE ≤ centralizer ({t} : Set X) := (TE_le_T S).trans A.T_le_centralizer

theorem t_mem_TE : t ∈ S.TE := B_le_TE S (mem_B_t S)

theorem k_mem_TE : S.k ∈ S.TE := B_le_TE S (mem_B_k S)

theorem comm_tE {g : X} (hg : g ∈ S.TE) : g * t = t * g := comm_t (TE_le_T S hg)

theorem central_of_mem_B {g : X} (hg : g ∈ S.B) {h : X} (hh : h ∈ S.TE) : g * h = h * g :=
  comm_B_TE S hg hh

theorem z_comm_of_mem_T {g : X} (hg : g ∈ S.TE) : S.z * g = g * S.z := z_comm S (TE_le_T S hg)

theorem conj_mem_B_N {w : X} (hw : w ∈ normalizer (S.TE : Set X)) {b : X} (hb : b ∈ S.B) :
    w * b * w⁻¹ ∈ S.B :=
  conj_mem_B_of_mem_normalizer S hw hb

theorem conj_z_eq {w : X} (hw : w ∈ normalizer (S.TE : Set X)) : w * S.z * w⁻¹ = S.z :=
  conj_z_of_mem_normalizer S hw

theorem mem_B_of_mem_E_inter {g : X} (hy : g ∈ S.E S.y) (hxy : g ∈ S.E (S.x * S.y)) :
    g ∈ S.B := by
  rw [← E₁_inf_E₂ S]
  exact mem_inf.mpr ⟨hy, hxy⟩

theorem mem_E_of_commute {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) {g : X} (hg : g ∈ S.TE)
    (hcomm : ∀ e ∈ S.E yi, g * e = e * g) : g ∈ S.E yi := by
  have hyiR : yi ∈ A.R := by rcases hyi with rfl | rfl; exacts [S.y_mem, xy_mem S]
  obtain ⟨hgT, ⟨u, b, hub, hb⟩⟩ := (mem_TE_iff S).mp hg
  have hc := congrArg (ψX A) (hcomm yi (mem_E_yi S yi))
  rw [ψX_mul hgT hyiR.1, ψX_mul hyiR.1 hgT] at hc
  obtain ⟨e, he, hψy⟩ := ψ_y S
  obtain ⟨e', he', hψyi⟩ : ∃ e' : ZMod 8, dbit8 e' = 0 ∧ ψX A yi = aff8 (-1) e' := by
    rcases hyi with rfl | rfl
    · exact ⟨e, he, hψy⟩
    · rw [ψX_mul (x_mem_T S) (y_mem_T S), hψy]
      rcases ψ_x S with h | h <;> rw [h, aff8_mul, one_mul, Units.val_one, one_mul]
      · exact ⟨2 + e, dbit8_add_even 2 e (Or.inl rfl) he, rfl⟩
      · exact ⟨6 + e, dbit8_add_even 6 e (Or.inr rfl) he, rfl⟩
  rw [hψyi, ← hub] at hc
  have key := comm_refl_pTE e' he' u b hb hc
  have hE : S.E yi = pre A PE₀ ∨ S.E yi = pre A PE₂ := by
    rcases E_cases S with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hyi with rfl | rfl
    · exact Or.inl h1
    · exact Or.inr h2
    · exact Or.inr h1
    · exact Or.inl h2
  rcases hE with h | h <;> rw [h] <;> refine mem_pre.mpr ⟨hgT, ?_⟩ <;> rw [← hub]
  · have hy0 : aff8 (-1) e' ∈ PE₀ := by
      have := (mem_pre.mp (h ▸ mem_E_yi S yi)).2
      rwa [hψyi] at this
    exact mem_PE₀.mpr (key.1 (mem_PE₀.mp hy0))
  · have hy2 : aff8 (-1) e' ∈ PE₂ := by
      have := (mem_pre.mp (h ▸ mem_E_yi S yi)).2
      rwa [hψyi] at this
    exact mem_PE₂.mpr (key.2 (mem_PE₂.mp hy2))

theorem mem_E_of_commute' {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) {g : X} (hg : g ∈ A.T)
    (hcomm : ∀ e ∈ S.E yi, g * e = e * g) : g ∈ S.E yi := by
  refine mem_E_of_commute S hyi (mem_inf.mpr ⟨hg, mem_centralizer_iff.mpr fun b hb => ?_⟩) hcomm
  exact (hcomm b (B_le_E S yi hb)).symm

theorem card_TE : Nat.card S.TE = 32 := by
  classical
  have hmem : ∀ (r : A.R) (a e : Fin 2), (r : X) * t ^ (a : ℕ) * S.k ^ (e : ℕ) ∈ S.TE :=
    fun r a e => mul_mem (mul_mem (R_le_TE S r.2) (pow_mem (t_mem_TE S) _))
      (pow_mem (k_mem_TE S) _)
  let f : A.R × Fin 2 × Fin 2 → S.TE := fun p => ⟨_, hmem p.1 p.2.1 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨r, a, e⟩ ⟨r', a', e'⟩ h
    have h' : (r : X) * t ^ (a : ℕ) * S.k ^ (e : ℕ) = r' * t ^ (a' : ℕ) * S.k ^ (e' : ℕ) :=
      congrArg Subtype.val h
    have hψ := congrArg (ψX A) h'
    have hw : ∀ (r : A.R) (a e : Fin 2), ψX A ((r : X) * t ^ (a : ℕ) * S.k ^ (e : ℕ)) =
        ψX A r * k8 ^ (e : ℕ) := by
      intro r a e
      rw [ψX_mul (mul_mem r.2.1 (pow_mem A.t_mem_T _)) (pow_mem (k_mem_T S) _),
        ψX_mul r.2.1 (pow_mem A.t_mem_T _), ψX_pow A.t_mem_T, ψX_t, one_pow, mul_one,
        ψX_pow (k_mem_T S), ψ_k]
    rw [hw, hw] at hψ
    have he : e = e' := by
      by_contra hne
      have hR : (ψX A r)⁻¹ * ψX A r' ∈ R8 :=
        mul_mem (inv_mem (ψX_mem_R8 r.2)) (ψX_mem_R8 r'.2)
      have hR' : (ψX A r')⁻¹ * ψX A r ∈ R8 :=
        mul_mem (inv_mem (ψX_mem_R8 r'.2)) (ψX_mem_R8 r.2)
      rcases Fin.exists_fin_two.mp ⟨e, rfl⟩ with rfl | rfl <;>
        rcases Fin.exists_fin_two.mp ⟨e', rfl⟩ with rfl | rfl
      · exact hne rfl
      · simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one] at hψ
        have : (ψX A r')⁻¹ * ψX A r = k8 := by
          rw [hψ]; group
        rw [this] at hR'
        exact k8_not_mem_R8 hR'
      · simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one] at hψ
        have : (ψX A r)⁻¹ * ψX A r' = k8 := by
          rw [← hψ]; group
        rw [this] at hR
        exact k8_not_mem_R8 hR
      · exact hne rfl
    subst he
    have hr : (r : X) = r' := eq_of_ψX_eq r.2 r'.2 (mul_right_cancel hψ)
    have ha : t ^ (a : ℕ) = t ^ (a' : ℕ) := by
      rw [hr] at h'
      exact mul_left_cancel (mul_right_cancel h')
    have ha' : a = a' := by
      rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl <;>
        rcases Fin.exists_fin_two.mp ⟨a', rfl⟩ with rfl | rfl
      · rfl
      · exact absurd (by simpa using ha) (t_ne_one' (A := A)).symm
      · exact absurd (by simpa using ha) (t_ne_one' (A := A))
      · rfl
    rw [Subtype.ext hr, ha']
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨hgT, ⟨u, b, hub, hb⟩⟩ := (mem_TE_iff S).mp hg
    obtain ⟨r, hr, a, e, ha, he, rfl, -⟩ := exists_eq_of_mem_T C hgT hub.symm hb
    exact ⟨(⟨r, hr⟩, ⟨a, ha⟩, ⟨e, he⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_prod,
    A.card_R, Nat.card_eq_fintype_card, Fintype.card_fin]

end CFSG.OddStandard.SmallF3.L33.KD.KD46
