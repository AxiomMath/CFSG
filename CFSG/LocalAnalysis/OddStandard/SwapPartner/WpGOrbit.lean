module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProd

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm

private theorem wp_conj_fiber {X : Type*} [Group X] (u a b : X) :
    a * u * a⁻¹ = b * u * b⁻¹ ↔ b⁻¹ * a ∈ centralizer ({u} : Set X) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc (b⁻¹ * a) * u = b⁻¹ * (a * u * a⁻¹) * a := by group
      _ = b⁻¹ * (b * u * b⁻¹) * a := by rw [h]
      _ = u * (b⁻¹ * a) := by group
  · intro h
    calc a * u * a⁻¹ = b * (b⁻¹ * a) * u * a⁻¹ := by group
      _ = b * ((b⁻¹ * a) * u) * a⁻¹ := by group
      _ = b * (u * (b⁻¹ * a)) * a⁻¹ := by rw [h]
      _ = b * u * b⁻¹ := by group

theorem card_le_ncard_mul_card_centralizer {X : Type*} [Group X] [Finite X] (u : X) (S : Set X)
    (h : ∀ f : X, f * u * f⁻¹ ∈ S) :
    Nat.card X ≤ S.ncard * Nat.card (centralizer ({u} : Set X)) := by
  classical
  let φ : X → X := fun f => f * u * f⁻¹
  let ψ : Set.range φ → X := fun b => Classical.choose b.2
  have hψ : ∀ b : Set.range φ, φ (ψ b) = b.1 := fun b => Classical.choose_spec b.2
  have hmem : ∀ f : X, (ψ ⟨φ f, ⟨f, rfl⟩⟩)⁻¹ * f ∈ centralizer ({u} : Set X) := by
    intro f
    exact (wp_conj_fiber u f (ψ ⟨φ f, ⟨f, rfl⟩⟩)).mp (hψ ⟨φ f, ⟨f, rfl⟩⟩).symm
  let Φ : X → Set.range φ × centralizer ({u} : Set X) := fun f =>
    (⟨φ f, ⟨f, rfl⟩⟩, ⟨(ψ ⟨φ f, ⟨f, rfl⟩⟩)⁻¹ * f, hmem f⟩)
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    have hb : (⟨φ f, ⟨f, rfl⟩⟩ : Set.range φ) = ⟨φ g, ⟨g, rfl⟩⟩ :=
      congrArg (fun x : Set.range φ × centralizer ({u} : Set X) => x.1) hfg
    have hψeq : ψ ⟨φ f, ⟨f, rfl⟩⟩ = ψ ⟨φ g, ⟨g, rfl⟩⟩ := congrArg ψ hb
    have h2 : (ψ ⟨φ f, ⟨f, rfl⟩⟩)⁻¹ * f = (ψ ⟨φ g, ⟨g, rfl⟩⟩)⁻¹ * g :=
      congrArg (fun x : Set.range φ × centralizer ({u} : Set X) => ((x.2 : X))) hfg
    rw [hψeq] at h2
    exact mul_left_cancel h2
  have hcard : Nat.card X ≤ (Set.range φ).ncard * Nat.card (centralizer ({u} : Set X)) := by
    have hle := Nat.card_le_card_of_injective Φ hΦ
    simpa [Nat.card_coe_set_eq] using hle
  have hsub : Set.range φ ⊆ S := by
    rintro y ⟨f, rfl⟩
    exact h f
  have hle : (Set.range φ).ncard ≤ S.ncard := Set.ncard_le_ncard hsub
  exact hcard.trans (Nat.mul_le_mul_right _ hle)

theorem ncard_preimage_le {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B) (S : Set B) :
    {a : A | f a ∈ S}.ncard ≤ (S ∩ (f.range : Set B)).ncard * Nat.card f.ker := by
  classical
  letI := Fintype.ofFinite A
  let s : Finset A := Finset.univ.filter (fun a => f a ∈ S)
  have hs : (s : Set A) = {a : A | f a ∈ S} := by
    ext a
    simp [s]
  have hpre : {a : A | f a ∈ S}.ncard = s.card := by
    rw [← Set.ncard_coe_finset s, hs]
  let K : Finset A := Finset.univ.filter (fun a => f a = 1)
  have hK : K.card = Nat.card f.ker := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype (fun a : A => f a = 1)).symm
  have hfib : ∀ b ∈ s.image f, (s.filter (fun a => f a = b)).card ≤ Nat.card f.ker := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨a₀, _, rfl⟩ := hb
    have hle : (s.filter (fun a => f a = f a₀)).card ≤ K.card := by
      refine Finset.card_le_card_of_injOn (fun a => a₀⁻¹ * a) ?_ ?_
      · intro a ha
        simp only [Finset.mem_coe, Finset.mem_filter] at ha
        simp only [Finset.mem_coe, K, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [map_mul, map_inv, ha.2, inv_mul_cancel]
      · intro a _ c _ hac
        exact mul_left_cancel hac
    rw [hK] at hle
    exact hle
  have himg_sub : ((s.image f : Finset B) : Set B) ⊆ S ∩ (f.range : Set B) := by
    intro b hb
    rw [Finset.mem_coe, Finset.mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨(Finset.mem_filter.mp ha).2, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have hfin : (S ∩ (f.range : Set B)).Finite :=
    (Set.finite_range f).inter_of_right S
  have himg_le : (s.image f).card ≤ (S ∩ (f.range : Set B)).ncard := by
    rw [← Set.ncard_coe_finset (s.image f)]
    exact Set.ncard_le_ncard himg_sub hfin
  have hmain := Finset.card_le_mul_card_image s (Nat.card f.ker) hfib
  calc {a : A | f a ∈ S}.ncard = s.card := hpre
    _ ≤ Nat.card f.ker * (s.image f).card := hmain
    _ ≤ Nat.card f.ker * (S ∩ (f.range : Set B)).ncard := Nat.mul_le_mul_left _ himg_le
    _ = (S ∩ (f.range : Set B)).ncard * Nat.card f.ker := Nat.mul_comm _ _

namespace WreathCase

variable {X : Type*} [Group X] {t : X} {Sg V K : Subgroup X}

theorem two_mul_card_range_le [Finite X] (H : WreathCase t Sg V K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) {u : X} (hu : u ∈ normalizer (K : Set X))
    {n : ℕ} (hn : Nat.card (centralizer ({u} : Set X)) ≤ n)
    (R : Perm (Fin 8) × Perm (Fin 8) → Prop)
    (hR : ∀ (f : X) (hf : f * u * f⁻¹ ∈ normalizer (K : Set X)),
      R (theta H e ⟨f * u * f⁻¹, hf⟩)) :
    2 * Nat.card (theta H e).range ≤
      n * {p : Perm (Fin 8) × Perm (Fin 8) |
        R p ∧ p ∈ (((theta H e).range : Subgroup _) : Set _)}.ncard := by
  classical
  let Nsub : Subgroup X := normalizer (K : Set X)
  let Θ : Nsub →* Perm (Fin 8) × Perm (Fin 8) := theta H e
  let pre : Set Nsub := {a | Θ a ∈ {p : Perm (Fin 8) × Perm (Fin 8) | R p}}
  let Sset : Set X := {y | ∃ hy : y ∈ Nsub, R (Θ ⟨y, hy⟩)}
  have hmemS : ∀ f : X, f * u * f⁻¹ ∈ Sset := by
    intro f
    exact ⟨H.normal_normalizer.conj_mem u hu f, hR f (H.normal_normalizer.conj_mem u hu f)⟩
  have h1 : Nat.card X ≤ Sset.ncard * Nat.card (centralizer ({u} : Set X)) :=
    card_le_ncard_mul_card_centralizer u Sset hmemS
  have h1' : Nat.card X ≤ Sset.ncard * n := h1.trans (Nat.mul_le_mul_left _ hn)
  have hSset_eq : Sset = (Subtype.val : Nsub → X) '' pre := by
    ext y
    constructor
    · rintro ⟨hy, hRy⟩
      exact ⟨⟨y, hy⟩, hRy, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, ha⟩
  have hSset : Sset.ncard = pre.ncard := by
    rw [hSset_eq]
    exact Set.ncard_image_of_injective pre Subtype.val_injective
  have h2 := ncard_preimage_le Θ {p : Perm (Fin 8) × Perm (Fin 8) | R p}
  have h2' : pre.ncard ≤
      {p : Perm (Fin 8) × Perm (Fin 8) |
        R p ∧ p ∈ ((Θ.range : Subgroup _) : Set _)}.ncard * Nat.card Θ.ker := by
    have hB : ({p : Perm (Fin 8) × Perm (Fin 8) | R p} ∩ (Θ.range : Set _)) =
        {p : Perm (Fin 8) × Perm (Fin 8) |
          R p ∧ p ∈ ((Θ.range : Subgroup _) : Set _)} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [hB] at h2
    exact h2
  have hcardX : Nat.card X = 2 * Nat.card Θ.ker * Nat.card Θ.range := by
    rw [card_eq_two_mul_card_mul_card_range H e, card_ker_theta H e]
  have hkerpos : 0 < Nat.card Θ.ker :=
    Nat.card_pos_iff.mpr ⟨⟨1, (Θ.ker).one_mem⟩, inferInstance⟩
  have h3 : Nat.card X ≤
      {p : Perm (Fin 8) × Perm (Fin 8) |
        R p ∧ p ∈ ((Θ.range : Subgroup _) : Set _)}.ncard * Nat.card Θ.ker * n := by
    rw [hSset] at h1'
    exact h1'.trans (Nat.mul_le_mul_right n h2')
  have h4 : Nat.card Θ.ker * (2 * Nat.card Θ.range) ≤
      Nat.card Θ.ker *
        ({p : Perm (Fin 8) × Perm (Fin 8) |
          R p ∧ p ∈ ((Θ.range : Subgroup _) : Set _)}.ncard * n) := by
    calc Nat.card Θ.ker * (2 * Nat.card Θ.range)
        = 2 * Nat.card Θ.ker * Nat.card Θ.range := by ring
      _ = Nat.card X := hcardX.symm
      _ ≤ {p : Perm (Fin 8) × Perm (Fin 8) |
            R p ∧ p ∈ ((Θ.range : Subgroup _) : Set _)}.ncard *
            Nat.card Θ.ker * n := h3
      _ = Nat.card Θ.ker *
          ({p : Perm (Fin 8) × Perm (Fin 8) |
            R p ∧ p ∈ ((Θ.range : Subgroup _) : Set _)}.ncard * n) := by ring
  have h5 : 2 * Nat.card Θ.range ≤
      {p : Perm (Fin 8) × Perm (Fin 8) |
        R p ∧ p ∈ ((Θ.range : Subgroup _) : Set _)}.ncard * n :=
    le_of_mul_le_mul_left h4 hkerpos
  calc 2 * Nat.card (theta H e).range = 2 * Nat.card Θ.range := rfl
    _ ≤ {p : Perm (Fin 8) × Perm (Fin 8) |
          R p ∧ p ∈ ((Θ.range : Subgroup _) : Set _)}.ncard * n := h5
    _ = n * {p : Perm (Fin 8) × Perm (Fin 8) |
          R p ∧ p ∈ ((Θ.range : Subgroup _) : Set _)}.ncard := Nat.mul_comm _ _

end WreathCase

end CFSG.OddStandard.AltStdSec.SwapPartner
