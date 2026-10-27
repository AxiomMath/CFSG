module

public import CFSG.LargeExtraspecial.S8KP

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] def conjD (t : S.O) : Set S.O := {e | ∃ x ∈ S.Mbar, e = x * t * x⁻¹}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem finrank_commSpace_of_mem_conjD (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {d : S.O} (hd : d ∈ conjD S t) :
    finrank (ZMod 2) (commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt)) = finrank (ZMod 2) (Vt S g t) := by
  obtain ⟨x, -, rfl⟩ := hd
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
    (commSpace_t_eq H C ht ht1 hVQ).1]

theorem exists_mul_of_mem_sup_of_commute {X : Type*} [Group X] {P K : Subgroup X}
    (hc : ∀ p ∈ P, ∀ k ∈ K, p * k = k * p) {x : X} (hx : x ∈ P ⊔ K) :
    ∃ p ∈ P, ∃ k ∈ K, x = p * k := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, one_mem _, (mul_one y).symm⟩
    · exact ⟨1, one_mem _, y, hy, (one_mul y).symm⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨p₁, hp₁, k₁, hk₁, rfl⟩ := iha
    obtain ⟨p₂, hp₂, k₂, hk₂, rfl⟩ := ihb
    refine ⟨p₁ * p₂, mul_mem hp₁ hp₂, k₁ * k₂, mul_mem hk₁ hk₂, ?_⟩
    calc p₁ * k₁ * (p₂ * k₂) = p₁ * (k₁ * p₂) * k₂ := by group
      _ = p₁ * (p₂ * k₁) * k₂ := by rw [hc p₂ hp₂ k₁ hk₁]
      _ = p₁ * p₂ * (k₁ * k₂) := by group
  | inv a _ ih =>
    obtain ⟨p₁, hp₁, k₁, hk₁, rfl⟩ := ih
    refine ⟨p₁⁻¹, inv_mem hp₁, k₁⁻¹, inv_mem hk₁, ?_⟩
    calc (p₁ * k₁)⁻¹ = (k₁ * p₁)⁻¹ := by rw [hc p₁ hp₁ k₁ hk₁]
      _ = p₁⁻¹ * k₁⁻¹ := by group

namespace Bad4

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad4 D τ)
include B

omit B in
theorem conj_bad (haQ : g * S.z * g⁻¹ ∈ S.QG) {ρ : S.O} (hρ : ρ ∈ conjCentM S t)
    (hρN : ρ ∉ Nbar S g t) {n : S.O} (hn : n ∈ Nbar S g t) :
    n * ρ * n⁻¹ ∈ conjCentM S t ∧ n * ρ * n⁻¹ ∉ Nbar S g t := by
  have hnM : n ∈ S.Mbar := Rbar_le_Mbar (Nbar_le_Rbar hn)
  have hnt : n * t = t * n := commute_of_mem_Rbar haQ (Nbar_le_Rbar hn)
  obtain ⟨hρM, hρt, x, hxM, hxρ⟩ := hρ
  refine ⟨⟨mul_mem (mul_mem hnM hρM) (inv_mem hnM), ?_, n * x, mul_mem hnM hxM, by
    rw [hxρ]; group⟩, fun h => hρN ?_⟩
  · calc n * ρ * n⁻¹ * t = n * (ρ * (n⁻¹ * t * n)) * n⁻¹ := by group
      _ = n * (ρ * t) * n⁻¹ := by
          rw [show n⁻¹ * t * n = t by rw [mul_assoc, ← hnt, inv_mul_cancel_left]]
      _ = n * (t * ρ) * n⁻¹ := by rw [hρt]
      _ = n * ((n⁻¹ * t * n) * ρ) * n⁻¹ := by
          rw [show n⁻¹ * t * n = t by rw [mul_assoc, ← hnt, inv_mul_cancel_left]]
      _ = t * (n * ρ * n⁻¹) := by group
  · have := mul_mem (mul_mem (inv_mem hn) h) hn
    rwa [show n⁻¹ * (n * ρ * n⁻¹) * n = ρ by group] at this

theorem mul_mem_conjD_or {ρ σ : S.O} (hρ : ρ ∈ conjD S t) (hσ : σ ∈ conjD S t)
    (hρY : commSpace (ρ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hσY : commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) (hne : ρ ≠ σ) :
    ρ * σ ∈ conjD S t ∨ commSpace ((ρ * σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have R := B.red
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  obtain ⟨y, hyM, hyρ⟩ := hρ
  obtain ⟨x, hxM, hxσ⟩ := hσ
  have hYy := B.map_eq_of_commSpace_le hyM (hyρ ▸ hρY)
  have hc := commute_of_commSpace_le B.le_perp hρY hσY
  set σ' := y⁻¹ * σ * y with hσ'
  have hσ'M : σ' ∈ S.Mbar := mul_mem (mul_mem (inv_mem hyM) (by
    rw [hxσ]; exact mul_mem (mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM))) hyM
  have hσ't : σ' * t = t * σ' := by
    have e1 : t = y⁻¹ * ρ * y := by rw [hyρ]; group
    calc σ' * t = y⁻¹ * (σ * ρ) * y := by rw [hσ', e1]; group
      _ = y⁻¹ * (ρ * σ) * y := by rw [hc]
      _ = t * σ' := by rw [hσ', e1]; group
  have hσ'C : σ' ∈ conjCentM S t :=
    ⟨hσ'M, hσ't, y⁻¹ * x, mul_mem (inv_mem hyM) hxM, by rw [hσ', hxσ]; group⟩
  have hσ't1 : σ' ≠ t := fun h => hne (by
    rw [hyρ]
    calc y * t * y⁻¹ = y * σ' * y⁻¹ := by rw [h]
      _ = σ := by rw [hσ']; group)
  have hρσ : ρ * σ = y * (t * σ') * y⁻¹ := by rw [hyρ, hσ']; group
  by_cases hσ'N : σ' ∈ Nbar S g t
  ·
    left
    have hσ'1 : σ' ≠ 1 := by
      intro h
      apply ht1
      have e : t = (y⁻¹ * x)⁻¹ * σ' * (y⁻¹ * x) := by rw [hσ', hxσ]; group
      rw [e, h]
      group
    have hσ'z : σ' ∉ zpowers t := fun h => by
      rcases eq_one_or_eq_of_mem_zpowers htt h with h | h
      · exact hσ'1 h
      · exact hσ't1 h
    obtain ⟨n, hn, hnσ⟩ : ∃ n ∈ Nbar S g t, n * σ' * n⁻¹ = t * σ' := by
      have hnc : ¬ ∀ n ∈ Nbar S g t, n * σ' = σ' * n := fun h =>
        hσ'z (Zbar_le_zpowers R.hNo R.hΩ D (mem_Zbar.mpr ⟨hσ'N, h⟩))
      push Not at hnc
      obtain ⟨n, hn, hnσ⟩ := hnc
      refine ⟨n, hn, ?_⟩
      rcases eq_one_or_eq_of_mem_zpowers htt (D.hNc n hn σ' hσ'N) with h | h
      · exfalso
        apply hnσ
        calc n * σ' = (n * σ' * n⁻¹ * σ'⁻¹) * (σ' * n) := by group
          _ = σ' * n := by rw [h, one_mul]
      · calc n * σ' * n⁻¹ = (n * σ' * n⁻¹ * σ'⁻¹) * σ' := by group
          _ = t * σ' := by rw [h]
    have hnM : n ∈ S.Mbar := Rbar_le_Mbar (Nbar_le_Rbar hn)
    refine ⟨y * n * (y⁻¹ * x), mul_mem (mul_mem hyM hnM) (mul_mem (inv_mem hyM) hxM), ?_⟩
    rw [hρσ, ← hnσ, hσ', hxσ]
    group
  ·
    right
    have hσ'V := R.fix_Vt hσ'C
    have hinf := R.inf_eq_bot hσ'C hσ'N
    have h1 := commSpace_mul_eq_sup (x := t) (y := σ')
      (by rw [(commSpace_t_eq H C ht ht1 hVQ).1]; exact hinf) (fun v hv => by
        have hvW := commSpace_le_Wt_of_fix hσ'V hv
        rw [← (commSpace_t_eq H C ht ht1 hVQ).2] at hvW
        exact mem_fixSpace.mp hvW)
    rw [(commSpace_t_eq H C ht ht1 hVQ).1, B.sup_eq hσ'C hσ'N] at h1
    rw [hρσ, S7.commSpace_conj, h1, hYy]

theorem commSpace_le_of_mem_N1bar {ν : S.O} (hν : ν ∈ N1bar S g t τ) :
    commSpace (ν : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  fun v hv => by
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
    exact apply_sub_mem_of_mem_N1bar D (B.red.fix_Vt B.mem) hν u

theorem mem_conjD_of_mem_Fbar {f : S.O} (hf : f ∈ S9.Fbar S g t) (hf1 : f ≠ 1) :
    f ∈ conjD S t := by
  have hkey := hkey_of_hsub D B.red.hsub
  have hkeyM : ∀ σ ∈ S9.conjL S g t, σ ≠ t → ∃ y ∈ S.Mbar, y * σ * y⁻¹ = σ * t := by
    intro σ hσ hσt
    obtain ⟨y, hy, he⟩ := hkey σ hσ hσt
    exact ⟨y, Rbar_le_Mbar (Nbar_le_Rbar hy), he⟩
  exact (S9.mem_conjL_of_mem_Fbar_of_ne_one H C ht hkeyM hf hf1).2

theorem N1bar_le_Fbar_sup : N1bar S g t τ ≤
    S9.Fbar S g t ⊔ (S9.Fbar S g t).map (MulAut.conj (S.ρ D.h)).toMonoidHom := by
  have := B.red.nqHyp
  have hFN : S9.Fbar S g t ≤ Nbar S g t := S9.Fbar_le_of_subset (conjL_subset_Nbar B.red.hsub)
  have hFhN : (S9.Fbar S g t).map (MulAut.conj (S.ρ D.h)).toMonoidHom ≤ Nbar S g t := by
    rintro _ ⟨f, hf, rfl⟩
    exact (nConj ⟨S.ρ D.h, D.hh⟩ ⟨f, hFN hf⟩).2
  have hPN := sup_le hFN hFhN
  have htP : t ∈ S9.Fbar S g t ⊔ (S9.Fbar S g t).map (MulAut.conj (S.ρ D.h)).toMonoidHom :=
    mem_sup_left (S9.self_mem_Fbar ht)
  have h2 : (nqSub S g t (S9.Fbar S g t)).map
      (nqHom S g t ⟨S.ρ D.h, D.hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t) ≤ nqSub S g t
        (S9.Fbar S g t ⊔ (S9.Fbar S g t).map (MulAut.conj (S.ρ D.h)).toMonoidHom) := by
    refine Submodule.map_le_iff_le_comap.mpr fun v hv => ?_
    obtain ⟨n, hnF, rfl⟩ := hv
    change nqHom S g t ⟨S.ρ D.h, D.hh⟩ (nqMk n) ∈ nqSub S g t
      (S9.Fbar S g t ⊔ (S9.Fbar S g t).map (MulAut.conj (S.ρ D.h)).toMonoidHom)
    rw [nqHom_mk]
    exact ⟨_, mem_sup_right ⟨n, hnF, rfl⟩, rfl⟩
  have hle : nqSub S g t (N1bar S g t τ) ≤ nqSub S g t
      (S9.Fbar S g t ⊔ (S9.Fbar S g t).map (MulAut.conj (S.ρ D.h)).toMonoidHom) :=
    (le_of_eq (B.red.nqSub_N1bar_eq B.mem B.not_mem)).trans
      (sup_le (nqSub_mono le_sup_left) h2)
  have hA := (B.red.N1bar_spec B.mem B.not_mem).1
  intro x hx
  exact (mem_nqSub htP ⟨x, hA hx⟩).mp (hle ⟨⟨x, hA hx⟩, hx, rfl⟩)

theorem commute_tau {a : S.O} (ha : a ∈ N1bar S g t τ) : a * τ = τ * a :=
  (B.red.N1bar_spec B.mem B.not_mem).2.2 a ha

theorem mem_or_mul_mem {e : S.O} (he : e ∈ closure (insert τ (N1bar S g t τ : Set S.O))) :
    e ∈ N1bar S g t τ ∨ e * τ ∈ N1bar S g t τ := by
  have hττ : τ * τ = 1 := mul_self_of_mem_conjCentM H ht B.mem
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have hcomm : ∀ a, a * τ ∈ N1bar S g t τ → a * τ = τ * a := fun a ha => by
    have h1 := B.commute_tau ha
    calc a * τ = (a * τ) * τ * τ := by rw [mul_assoc (a * τ), hττ, mul_one]
      _ = τ * (a * τ) * τ := by rw [h1]
      _ = τ * a := by rw [mul_assoc, mul_assoc, hττ, mul_one]
  induction he using closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · right
      rw [hττ]
      exact one_mem _
    · exact Or.inl hy
  | one => exact Or.inl (one_mem _)
  | mul a b _ _ iha ihb =>
    rcases iha with ha | ha <;> rcases ihb with hb | hb
    · exact Or.inl (mul_mem ha hb)
    · right
      rw [mul_assoc]
      exact mul_mem ha hb
    · right
      have h1 := B.commute_tau hb
      have e : a * b * τ = a * τ * b := by
        calc a * b * τ = a * (b * τ) := mul_assoc a b τ
          _ = a * (τ * b) := by rw [h1]
          _ = a * τ * b := (mul_assoc a τ b).symm
      rw [e]
      exact mul_mem ha hb
    · left
      have h2 := hcomm b hb
      have e : a * b = a * τ * (b * τ) := by
        calc a * b = a * b * (τ * τ) := by rw [hττ, mul_one]
          _ = a * (b * τ) * τ := by group
          _ = a * (τ * b) * τ := by rw [h2]
          _ = a * τ * (b * τ) := by group
      rw [e]
      exact mul_mem ha hb
  | inv a _ ih =>
    rcases ih with ha | ha
    · exact Or.inl (inv_mem ha)
    · right
      have h2 := hcomm a ha
      have e : a⁻¹ * τ = (a * τ)⁻¹ := by
        calc a⁻¹ * τ = (τ⁻¹ * a)⁻¹ := by group
          _ = (a * τ)⁻¹ := by rw [hτi, ← h2]
      rw [e]
      exact inv_mem ha

end Bad4

end CFSG.LargeExtraspecial.S8
