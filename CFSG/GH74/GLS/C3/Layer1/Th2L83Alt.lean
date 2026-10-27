module

public import CFSG.GH74.GLS.C3.Layer1.Th2L83GenCore

public section

namespace CFSG.GH74.GLS.Th2.L83

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1

section Alt

variable {K : Type} [Group K] {n : ℕ}

@[expose] noncomputable def altAut (hn : 5 ≤ n) (hn6 : n ≠ 6) (ε : K ≃* alternatingGroup (Fin n)) :
    Perm (Fin n) ≃* MulAut K :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)).trans
    (MulAut.congr ε).symm

@[expose] noncomputable def altEmb (ε : K ≃* alternatingGroup (Fin n)) : K →* Perm (Fin n) :=
  (alternatingGroup (Fin n)).subtype.comp ε.toMonoidHom

theorem altEmb_injective (ε : K ≃* alternatingGroup (Fin n)) : Function.Injective (altEmb ε) := by
  intro x y h
  exact ε.injective (Subtype.ext h)

theorem altEmb_aut (hn : 5 ≤ n) (hn6 : n ≠ 6) (ε : K ≃* alternatingGroup (Fin n))
    (t : Perm (Fin n)) (k : K) :
    altEmb ε (altAut hn hn6 ε t k) = t * altEmb ε k * t⁻¹ := by
  show ((ε (altAut hn hn6 ε t k) : alternatingGroup (Fin n)) : Perm (Fin n)) =
    t * ((ε k : alternatingGroup (Fin n)) : Perm (Fin n)) * t⁻¹
  have : ε (altAut hn hn6 ε t k) =
      (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
        (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)) t (ε k) := by
    show ε ((MulAut.congr ε).symm _ k) = _
    simp
  rw [this]
  exact MulAut.conjNormal_apply t (ε k)

theorem altAut_eq_conj (hn : 5 ≤ n) (hn6 : n ≠ 6) (ε : K ≃* alternatingGroup (Fin n))
    (t : alternatingGroup (Fin n)) :
    altAut hn hn6 ε (t : Perm (Fin n)) = MulAut.conj (ε.symm t) := by
  apply MulEquiv.ext
  intro k
  apply ε.injective
  apply Subtype.ext
  rw [show ((ε (altAut hn hn6 ε (t : Perm (Fin n)) k) : alternatingGroup (Fin n)) : Perm (Fin n)) =
    altEmb ε (altAut hn hn6 ε (t : Perm (Fin n)) k) from rfl, altEmb_aut]
  simp [altEmb, MulAut.conj_apply]

end Alt

section Model

variable {G : Type} [Group G]

structure AltModel {K X : Subgroup G} (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (n : ℕ) where
  Φ : kBar K →* Perm (Fin n)
  ψ : ↥X →* Perm (Fin n)
  inj : Function.Injective Φ
  mem_alt : ∀ z, Φ z ∈ alternatingGroup (Fin n)
  surj_alt : ∀ σ ∈ alternatingGroup (Fin n), ∃ z, Φ z = σ
  equiv : ∀ (x : ↥X) (z : kBar K), Φ (Back.actHom hKX x z) = ψ x * Φ z * (ψ x)⁻¹

variable {K X : Subgroup G} {hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K}

@[expose] noncomputable def AltModel.ofIso (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (ε : kBar K ≃* alternatingGroup (Fin n)) (g : Perm (Fin n)) :
    AltModel hKX n where
  Φ := (MulAut.conj g⁻¹).toMonoidHom.comp (altEmb ε)
  ψ := (MulAut.conj g⁻¹).toMonoidHom.comp
    ((altAut hn hn6 ε).symm.toMonoidHom.comp (Back.actHom hKX))
  inj := (MulAut.conj g⁻¹).injective.comp (altEmb_injective ε)
  mem_alt := fun z => by
    have h1 : altEmb ε z ∈ alternatingGroup (Fin n) := (ε z).2
    rw [Equiv.Perm.mem_alternatingGroup] at h1 ⊢
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [Perm.sign_mul, Perm.sign_mul, h1]
    simp
  surj_alt := fun σ hσ => by
    have hτ : g * σ * g⁻¹ ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
      rw [Perm.sign_mul, Perm.sign_mul, hσ]
      simp
    refine ⟨ε.symm ⟨g * σ * g⁻¹, hτ⟩, ?_⟩
    simp [altEmb]
    group
  equiv := fun x z => by
    set t := (altAut hn hn6 ε).symm (Back.actHom hKX x) with ht
    have h1 : Back.actHom hKX x = altAut hn hn6 ε t := by simp [ht]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← ht]
    rw [h1, altEmb_aut]
    group

theorem AltModel.ofIso_Φ {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) (ε : kBar K ≃* alternatingGroup (Fin n))
    (g : Perm (Fin n)) (z : kBar K) :
    (AltModel.ofIso hKX hn hn6 ε g).Φ z = g⁻¹ * ((ε z : alternatingGroup (Fin n)) : Perm (Fin n)) * g := by
  simp [AltModel.ofIso, altEmb]

theorem AltModel.mem_fixBar_iff {n : ℕ} (M : AltModel hKX n) {F : Subgroup G} {z : kBar K} :
    z ∈ fixBar hKX F ↔ ∀ f : ↥X, (f : G) ∈ F → M.ψ f * M.Φ z = M.Φ z * M.ψ f := by
  rw [_root_.CFSG.GH74.GLS.Th2.L83.mem_fixBar_iff]
  refine forall_congr' fun f => forall_congr' fun _ => ?_
  constructor
  · intro h
    have := M.equiv f z
    rw [h] at this
    calc M.ψ f * M.Φ z = (M.ψ f * M.Φ z * (M.ψ f)⁻¹) * M.ψ f := by group
      _ = M.Φ z * M.ψ f := by rw [← this]
  · intro h
    apply M.inj
    rw [M.equiv, h]
    group

theorem AltModel.ofIso_inner {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (ε : kBar K ≃* alternatingGroup (Fin n)) (g : Perm (Fin n)) {k : G} (hk : k ∈ K) (hkX : k ∈ X) :
    (AltModel.ofIso hKX hn hn6 ε g).ψ ⟨k, hkX⟩ =
      (AltModel.ofIso hKX hn hn6 ε g).Φ (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) := by
  have h1 := Back.actHom_of_mem hKX hk hkX
  have h2 := altAut_eq_conj hn hn6 ε (ε (QuotientGroup.mk (⟨k, hk⟩ : ↥K)))
  have h3 : (altAut hn hn6 ε).symm (Back.actHom hKX ⟨k, hkX⟩) =
      ((ε (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    rw [MulEquiv.symm_apply_eq, h1, h2]
    simp
  simp only [AltModel.ofIso, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h3, altEmb]
  rfl

theorem AltModel.top_of_gen {n : ℕ} (M : AltModel hKX n) (𝔉 : Set (Subgroup G))
    (h : alternatingGroup (Fin n) ≤ ⨆ F ∈ 𝔉, (alternatingGroup (Fin n) ⊓
      ⨅ (f : ↥X) (_ : (f : G) ∈ F), centralizer ({M.ψ f} : Set (Perm (Fin n))))) :
    ⨆ F ∈ 𝔉, fixBar hKX F = ⊤ := by
  have hle : (⨆ F ∈ 𝔉, (alternatingGroup (Fin n) ⊓
      ⨅ (f : ↥X) (_ : (f : G) ∈ F), centralizer ({M.ψ f} : Set (Perm (Fin n))))) ≤
      (⨆ F ∈ 𝔉, fixBar hKX F).map M.Φ := by
    refine iSup₂_le fun F hF σ hσ => ?_
    obtain ⟨hσA, hσc⟩ := Subgroup.mem_inf.1 hσ
    obtain ⟨z, rfl⟩ := M.surj_alt σ hσA
    refine ⟨z, ?_, rfl⟩
    have hz : z ∈ fixBar hKX F := by
      rw [M.mem_fixBar_iff]
      intro f hf
      have := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hσc f) hf)
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this.symm
    exact Subgroup.mem_iSup_of_mem F (Subgroup.mem_iSup_of_mem hF hz)
  rw [eq_top_iff]
  intro z _
  obtain ⟨w, hw, hwz⟩ := hle (h (M.mem_alt z))
  have : w = z := M.inj hwz
  rw [← this]
  exact hw

end Model

section Sub

variable {G : Type} [Group G]

def commSub {S : Type*} [Group S] (X B : Subgroup G) (ψ : ↥X →* S) (c : S) : Subgroup G :=
  ((B.subgroupOf X) ⊓ (centralizer ({c} : Set S)).comap ψ).map X.subtype

theorem mem_commSub {S : Type*} [Group S] {X B : Subgroup G} {ψ : ↥X →* S} {c : S} {b : G} :
    b ∈ commSub X B ψ c ↔ ∃ hbX : b ∈ X, b ∈ B ∧ ψ ⟨b, hbX⟩ * c = c * ψ ⟨b, hbX⟩ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hy
    exact ⟨y.2, Subgroup.mem_subgroupOf.1 h1, Subgroup.mem_centralizer_singleton_iff.1 h2⟩
  · rintro ⟨hbX, hbB, hc⟩
    exact ⟨⟨b, hbX⟩, Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hbB,
      Subgroup.mem_centralizer_singleton_iff.2 hc⟩, rfl⟩

theorem commSub_le {S : Type*} [Group S] {X B : Subgroup G} {ψ : ↥X →* S} {c : S} :
    commSub X B ψ c ≤ B := fun _ hb => (mem_commSub.1 hb).2.1

theorem card_le_two_mul_of_mul_mem [Finite G] {B F : Subgroup G} (hFB : F ≤ B)
    (h : ∀ a ∈ B, ∀ b ∈ B, a ∉ F → b ∉ F → a * b ∈ F) : Nat.card B ≤ 2 * Nat.card F := by
  classical
  by_cases hF : F = B
  · subst hF
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  · obtain ⟨a₀, ha₀B, ha₀F⟩ : ∃ a₀ ∈ B, a₀ ∉ F := by
      by_contra hcon
      push Not at hcon
      exact hF (le_antisymm hFB hcon)
    let φ : ↥B → Bool × ↥F := fun b =>
      if hb : (b : G) ∈ F then (false, ⟨b, hb⟩)
      else (true, ⟨(b : G) * a₀, h b b.2 a₀ ha₀B hb ha₀F⟩)
    have hφ : Function.Injective φ := by
      intro b b' hbb'
      by_cases hb : (b : G) ∈ F <;> by_cases hb' : (b' : G) ∈ F
      · simp only [φ, hb, hb', dite_true, Prod.mk.injEq, true_and] at hbb'
        exact Subtype.ext (Subtype.mk.inj hbb')
      · simp [φ, hb, hb'] at hbb'
      · simp [φ, hb, hb'] at hbb'
      · simp only [φ, hb, hb', dite_false, Prod.mk.injEq, true_and] at hbb'
        have := congrArg Subtype.val hbb'
        exact Subtype.ext (mul_right_cancel this)
    have := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    exact this

end Sub

end CFSG.GH74.GLS.Th2.L83
