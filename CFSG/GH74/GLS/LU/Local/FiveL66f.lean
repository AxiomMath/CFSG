module

public import CFSG.GH74.GLS.LU.Local.FiveL66e

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section ConjIso

variable {G : Type} [Group G] {z : G}

@[expose] def conjIso {s g : G} (hg : g * s * g⁻¹ = z) :
    ↥(centralizer ({s} : Set G)) ≃* ↥(Cz z) where
  toFun x := ⟨g * (x : G) * g⁻¹, by
    have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← hg]
    calc g * (x : G) * g⁻¹ * (g * s * g⁻¹) = g * ((x : G) * s) * g⁻¹ := by group
      _ = g * (s * (x : G)) * g⁻¹ := by rw [hx]
      _ = g * s * g⁻¹ * (g * (x : G) * g⁻¹) := by group⟩
  invFun y := ⟨g⁻¹ * (y : G) * g, by
    have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hs : s = g⁻¹ * z * g := by rw [← hg]; group
    rw [hs]
    calc g⁻¹ * (y : G) * g * (g⁻¹ * z * g) = g⁻¹ * ((y : G) * z) * g := by group
      _ = g⁻¹ * (z * (y : G)) * g := by rw [hy]
      _ = g⁻¹ * z * g * (g⁻¹ * (y : G) * g) := by group⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv y := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

end ConjIso

section C0At

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t u : G} {K₁ K₂ : Subgroup G}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

omit [Finite G] in
theorem ModelPic.c0_at (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    {s r : G} {X₀ : Subgroup G} (ρ : ↥(centralizer ({s} : Set G)) ≃* ↥(Cz z'))
    (hsC : s ∈ centralizer ({s} : Set G)) (hρs : pe ρ s hsC = z')
    (hrC : r ∈ centralizer ({s} : Set G)) (hr2 : r * r = 1) (hr1 : r ≠ 1) (hrs : r ≠ s)
    (hX₀ : X₀ ≤ centralizer ({s} : Set G)) (hX₀c : Nat.card ↥X₀ = 5)
    (hrX₀ : ∀ x ∈ X₀, r * x = x * r)
    (huC : u ∈ centralizer ({s} : Set G)) (hv : pe ρ u huC ∈ normalizer (K₁' : Set Gs))
    (huX₀ : ∀ x ∈ X₀, u * x * u⁻¹ = x⁻¹) :
    ∃ Xs : Subgroup G, Xs ≤ centralizer (X₀ : Set G) ∧ IsElemAb 5 Xs ∧ Nat.card ↥Xs = 25 ∧
      (∀ x ∈ Xs, u * x * u⁻¹ = x⁻¹) ∧
      centralizer ({s} : Set G) ⊓ centralizer (X₀ : Set G) = Xs ⊔ (zpowers s ⊔ zpowers r) ∧
      Xs ⊓ (zpowers s ⊔ zpowers r) = ⊥ ∧
      ∀ g ∈ centralizer ({s} : Set G) ⊓ centralizer (X₀ : Set G), ∀ x ∈ Xs, g * x * g⁻¹ ∈ Xs := by
  classical
  set τ : Gs := pe ρ r hrC with hτ
  set Z : Subgroup Gs := push ρ X₀ with hZ
  have hZC : Z ≤ Cz z' := push_le ρ X₀
  have hpullZ : pull ρ Z = X₀ := pull_push ρ hX₀
  have hZc : Nat.card ↥Z = 5 :=
    (card_pull ρ hZC).symm.trans (by rw [hpullZ]; exact hX₀c)
  have hτ2 : τ * τ = 1 := by
    have h : pe ρ (r * r) ((centralizer ({s} : Set G)).mul_mem hrC hrC) = pe ρ 1 (centralizer ({s} : Set G)).one_mem := (pe_eq_iff ρ _ _).mpr hr2
    rw [pe_mul ρ hrC hrC, pe_one] at h
    exact h
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hr1
    have h' : pe ρ r hrC = pe ρ 1 (centralizer ({s} : Set G)).one_mem := by rw [pe_one]; exact h
    exact (pe_eq_iff ρ hrC (centralizer ({s} : Set G)).one_mem).mp h'
  have hτz : τ ≠ z' := by
    intro h
    apply hrs
    rw [← hρs] at h
    exact (pe_eq_iff ρ hrC hsC).mp h
  have hτC : τ ∈ Cz z' := (ρ ⟨r, hrC⟩).2
  have hZτ : ∀ y ∈ Z, τ * y = y * τ := by
    intro y hy
    obtain ⟨x, hxX, hxX₀, rfl⟩ := exists_pe_of_mem_push ρ hy
    exact (pe_comm_iff ρ hrC hxX).mp (hrX₀ x hxX₀)
  obtain ⟨A, hAK, hAab, hAc, hAT, hCA, hAnorm, hAinv⟩ :=
    pic.facts.diag τ hτC hτ2 hτ1 hτz Z hZC hZc hZτ
  have hAC : A ≤ Cz z' := by
    have : A ≤ centralizer (Z : Set Gs) ⊓ Cz z' := by rw [hCA]; exact le_sup_left
    exact this.trans inf_le_right
  have hz'C : z' ∈ Cz z' := mem_Cz_self z'
  have hTC : zpowers z' ⊔ zpowers τ ≤ Cz z' :=
    sup_le (Subgroup.zpowers_le.mpr hz'C) (Subgroup.zpowers_le.mpr hτC)
  have hcent := pull_centralizer_inf ρ hZC
  rw [hpullZ] at hcent
  have hT : pull ρ (zpowers z' ⊔ zpowers τ) = zpowers s ⊔ zpowers r := by
    rw [pull_sup ρ (Subgroup.zpowers_le.mpr hz'C) (Subgroup.zpowers_le.mpr hτC),
      pull_zpowers ρ hsC hρs, pull_zpowers ρ hrC rfl]
  refine ⟨pull ρ A, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc pull ρ A ≤ pull ρ (A ⊔ (zpowers z' ⊔ zpowers τ)) := pull_mono ρ le_sup_left
      _ = pull ρ (centralizer (Z : Set Gs) ⊓ Cz z') := by rw [hCA]
      _ = centralizer (X₀ : Set G) ⊓ centralizer ({s} : Set G) := hcent
      _ ≤ centralizer (X₀ : Set G) := inf_le_left
  · refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · have hxX := pull_le ρ A hx
      have hyX := pull_le ρ A hy
      have hx' := (mem_pull ρ A hxX).mp hx
      have hy' := (mem_pull ρ A hyX).mp hy
      exact (pe_comm_iff ρ hxX hyX).mpr (hAab.1 _ hx' _ hy')
    · have hxX := pull_le ρ A hx
      have hx' := (mem_pull ρ A hxX).mp hx
      have h5 := hAab.2 _ hx'
      have : pe ρ (x ^ 5) ((centralizer ({s} : Set G)).pow_mem hxX 5) = pe ρ 1 (centralizer ({s} : Set G)).one_mem := by
        rw [pe_pow, pe_one]; exact h5
      exact (pe_eq_iff ρ _ _).mp this
  · exact (card_pull ρ hAC).trans hAc
  · intro x hx
    have hxX := pull_le ρ A hx
    have hx' := (mem_pull ρ A hxX).mp hx
    have hvC : pe ρ u huC ∈ Cz z' := (ρ ⟨u, huC⟩).2
    have hZinv : ∀ y ∈ Z, pe ρ u huC * y * (pe ρ u huC)⁻¹ = y⁻¹ := by
      intro y hy
      obtain ⟨x₀, hx₀X, hx₀, rfl⟩ := exists_pe_of_mem_push ρ hy
      have h := (pe_eq_iff ρ ((centralizer ({s} : Set G)).mul_mem ((centralizer ({s} : Set G)).mul_mem huC hx₀X) ((centralizer ({s} : Set G)).inv_mem huC))
        ((centralizer ({s} : Set G)).inv_mem hx₀X)).mpr (huX₀ x₀ hx₀)
      rw [pe_conj ρ huC hx₀X, pe_inv ρ hx₀X] at h
      exact h
    have h := hAinv _ hvC hv hZinv _ hx'
    have hxinv : x⁻¹ ∈ centralizer ({s} : Set G) := (centralizer ({s} : Set G)).inv_mem hxX
    refine (pe_eq_iff ρ ((centralizer ({s} : Set G)).mul_mem ((centralizer ({s} : Set G)).mul_mem huC hxX) ((centralizer ({s} : Set G)).inv_mem huC)) hxinv).mp ?_
    rw [pe_conj ρ huC hxX, pe_inv ρ hxX]
    exact h
  · have h1 : pull ρ (centralizer (Z : Set Gs) ⊓ Cz z') = pull ρ A ⊔ (zpowers s ⊔ zpowers r) := by
      rw [hCA, pull_sup ρ hAC hTC, hT]
    rw [inf_comm, ← hcent, h1]
  · rw [← hT, ← pull_inf, hAT, pull_bot]
  · intro g hg x hx
    have hgX : g ∈ centralizer ({s} : Set G) := hg.1
    have hg' : g ∈ pull ρ (centralizer (Z : Set Gs) ⊓ Cz z') := by
      rw [hcent]; exact ⟨hg.2, hg.1⟩
    have hgρ := (mem_pull ρ _ hgX).mp hg'
    have hxX := pull_le ρ A hx
    have hx' := (mem_pull ρ A hxX).mp hx
    have h' := hAnorm _ hgρ _ hx'
    have hmem : g * x * g⁻¹ ∈ centralizer ({s} : Set G) :=
      (centralizer ({s} : Set G)).mul_mem ((centralizer ({s} : Set G)).mul_mem hgX hxX)
        ((centralizer ({s} : Set G)).inv_mem hgX)
    have hc : ((ρ ⟨g * x * g⁻¹, hmem⟩ : ↥(Cz z')) : Gs) =
        pe ρ g hgX * pe ρ x hxX * (pe ρ g hgX)⁻¹ := pe_conj ρ hgX hxX
    rw [mem_pull ρ A hmem, hc]
    exact h'

end C0At

end CFSG.GH74.GLS.LU.Local.Five
