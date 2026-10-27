module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Perfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Engine

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

variable {G : Type*} [Group G] {B : Type*} [Group B] {t : G} {B₀ : Subgroup B}
  {ψ : ↥(centralizer ({t} : Set G)) →* Multiplicative (ZMod 2) × B}

theorem sup_conj_perfect [Finite G] (h : ModData t B₀ ψ) {L₁ : Subgroup G}
    (hL₁ : IsComponent L₁) :
    ⁅L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom, L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom⁆ =
        L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom ∧
      L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom ≠ ⊥ := by
  have hL₂ : IsComponent (L₁.map (MulAut.conj t).toMonoidHom) := isComponent_conj hL₁ t
  refine ⟨le_antisymm (Subgroup.commutator_le_self _) (sup_le ?_ ?_), ?_⟩
  · calc L₁ = ⁅L₁, L₁⁆ := (Subgroup.isPerfect_iff.mp hL₁.1.1).symm
      _ ≤ ⁅L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom,
            L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom⁆ :=
        Subgroup.commutator_mono le_sup_left le_sup_left
  · calc L₁.map (MulAut.conj t).toMonoidHom =
          ⁅L₁.map (MulAut.conj t).toMonoidHom, L₁.map (MulAut.conj t).toMonoidHom⁆ :=
        (Subgroup.isPerfect_iff.mp hL₂.1.1).symm
      _ ≤ ⁅L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom,
            L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom⁆ :=
        Subgroup.commutator_mono le_sup_right le_sup_right
  · intro hbot
    exact ((Subgroup.nontrivial_iff_ne_bot L₁).1
      (CFSG.LocalCores.isQuasisimple_nontrivial hL₁.1))
      (le_bot_iff.1 (hbot ▸ le_sup_left))

theorem ModData.imgOf_pair_ne_bot [Finite G] (h : ModData t B₀ ψ) {L₁ : Subgroup G}
    (hL₁ : IsComponent L₁) :
    imgOf ψ ((L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom) ⊓ centralizer ({t} : Set G)) ≠ ⊥ := by
  obtain ⟨hperf, hne⟩ := sup_conj_perfect h hL₁
  exact h.imgOf_ne_bot_of_perfect hperf hne (sup_conj h.t_sq rfl)

theorem rest_eq_bot_mod [Finite G] (h : ModData t B₀ ψ) (hF : CFSG.fittingSubgroup G = ⊥)
    {L₁ : Subgroup G} (hL₁ : IsComponent L₁) :
    Rest G L₁ (L₁.map (MulAut.conj t).toMonoidHom) = ⊥ := by
  have hz := h.t_sq
  obtain ⟨L₂, hL₂def⟩ : ∃ L₂ : Subgroup G, L₂ = L₁.map (MulAut.conj t).toMonoidHom := ⟨_, rfl⟩
  rw [← hL₂def]
  have hL₂ : IsComponent L₂ := by rw [hL₂def]; exact isComponent_conj hL₁ t
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup G, N = L₁ ⊔ L₂ := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup G, R = Rest G L₁ L₂ := ⟨_, rfl⟩
  rw [← hRdef]
  have hE : layer G = N ⊔ R := by rw [hNdef, hRdef]; exact layer_eq_sup_rest hL₁ hL₂
  have hRN : R ≤ centralizer (N : Set G) := by
    rw [hNdef, hRdef]; exact rest_le_centralizer hL₁ hL₂
  have hRperf : ⁅R, R⁆ = R := by rw [hRdef]; exact rest_perfect L₁ L₂
  have hRz : ∀ x ∈ R, t * x * t⁻¹ ∈ R := by rw [hRdef]; exact rest_conj hz hL₂def
  have hNz : ∀ x ∈ N, t * x * t⁻¹ ∈ N := by rw [hNdef]; exact sup_conj hz hL₂def
  have hRc : ∀ r ∈ R, ∀ n ∈ N, n * r = r * n := fun r hr n hn =>
    mem_centralizer_iff.1 (hRN hr) n hn
  have hNR : N ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    exact center_sup_eq_bot hF hL₁ hL₂ x (by rw [← hNdef]; exact hx.1)
      fun y hy => hRc x hx.2 y (by rw [hNdef]; exact hy)
  have hNle : N ≤ layer G := by rw [hE]; exact le_sup_left
  have hRle : R ≤ layer G := by rw [hE]; exact le_sup_right
  have hEc : (layer G).Characteristic := CFSG.LocalCores.layer_characteristic
  have hEn : (layer G).Normal := inferInstance
  have hfix : ∀ m ∈ layer G, t * m = m * t →
      ∃ p ∈ N, ∃ q ∈ R, m = p * q ∧ t * p = p * t ∧ t * q = q * t := by
    intro m hm hmz
    rw [hE] at hm
    obtain ⟨n, hn, r, hr, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hRN hm
    obtain ⟨h1, h2⟩ := fixed_decomp hNR hNz hRz hn hr hmz
    exact ⟨n, hn, r, hr, rfl, h1, h2⟩
  by_contra hR1
  let M : Subgroup G := layer G ⊓ centralizer ({t} : Set G)
  let P : Subgroup G := N ⊓ centralizer ({t} : Set G)
  let Q : Subgroup G := R ⊓ centralizer ({t} : Set G)
  have hM : ∀ c ∈ centralizer ({t} : Set G), ∀ y ∈ M, c * y * c⁻¹ ∈ M := by
    intro c hc y hy
    exact ⟨hEn.conj_mem y hy.1 c, (centralizer ({t} : Set G)).mul_mem
      ((centralizer ({t} : Set G)).mul_mem hc hy.2)
      ((centralizer ({t} : Set G)).inv_mem hc)⟩
  have hMC : M ≤ centralizer ({t} : Set G) := inf_le_right
  have hP : P ≤ M := inf_le_inf_right _ hNle
  have hQ : Q ≤ M := inf_le_inf_right _ hRle
  have hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p := fun p hp q hq => hRc q hq.1 p hp.1
  have hMdec : ∀ m ∈ M, ∃ p ∈ P, ∃ q ∈ Q, m = p * q := by
    intro m hm
    obtain ⟨p, hpN, q, hqR, hmpq, hp, hq⟩ :=
      hfix m hm.1 (mem_centralizer_singleton_iff.1 hm.2).symm
    exact ⟨p, ⟨hpN, mem_centralizer_singleton_iff.2 hp.symm⟩,
      q, ⟨hqR, mem_centralizer_singleton_iff.2 hq.symm⟩, hmpq⟩
  have hP1 : imgOf ψ P ≠ ⊥ := by
    change imgOf ψ (N ⊓ centralizer ({t} : Set G)) ≠ ⊥
    rw [hNdef, hL₂def]
    exact h.imgOf_pair_ne_bot hL₁
  have hQ1 : imgOf ψ Q ≠ ⊥ := by
    change imgOf ψ (R ⊓ centralizer ({t} : Set G)) ≠ ⊥
    exact h.imgOf_ne_bot_of_perfect hRperf hR1 hRz
  exact h.false_of_decomposition hM hMC hP hQ hPQ hMdec hP1 hQ1

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
