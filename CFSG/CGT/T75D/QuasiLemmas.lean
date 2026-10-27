module

public import CFSG.Open.Defs

public section

namespace CFSG.CGT.T75D

open CFSG.Open
open scoped commutatorElement

section Quasi

variable {X : Type*} [Group X]

theorem exists_not_comm (hX : IsQuasisimple X) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have h1 := hX.2
  have : Nontrivial (X ⧸ Subgroup.center X) := h1.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (X ⧸ Subgroup.center X)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [QuotientGroup.eq]
  exact Subgroup.mem_center_iff.2 fun g => hcon g _

theorem normal_le_center (hX : IsQuasisimple X) (N : Subgroup X) [N.Normal] (hN : N ≠ ⊤) :
    N ≤ Subgroup.center X := by
  obtain ⟨hperf, hsimple⟩ := hX
  have := hsimple
  have hn : (N.map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center X))) with h | h
  · intro x hx
    have : (QuotientGroup.mk' (Subgroup.center X)) x ∈ N.map (QuotientGroup.mk' (Subgroup.center X)) :=
      Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  · exfalso
    apply hN
    have hdec : ∀ x : X, ∃ n ∈ N, ∃ z ∈ Subgroup.center X, x = n * z := by
      intro x
      have hx : (QuotientGroup.mk' (Subgroup.center X)) x ∈
          N.map (QuotientGroup.mk' (Subgroup.center X)) := by rw [h]; trivial
      obtain ⟨n, hn', hnx⟩ := hx
      refine ⟨n, hn', n⁻¹ * x, ?_, by group⟩
      exact QuotientGroup.eq.1 hnx
    have hle : commutator X ≤ N := by
      show ⁅(⊤ : Subgroup X), ⊤⁆ ≤ N
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdec a
      obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdec b
      have e : ⁅n₁ * z₁, n₂ * z₂⁆ = ⁅n₁, n₂⁆ := by
        have h1 : z₁ * n₂ = n₂ * z₁ := (Subgroup.mem_center_iff.1 hz₁ n₂).symm
        have h2 : z₂ * n₁ = n₁ * z₂ := (Subgroup.mem_center_iff.1 hz₂ n₁).symm
        have hz12 : z₁ * z₂ = z₂ * z₁ := (Subgroup.mem_center_iff.1 hz₁ z₂).symm
        simp only [commutatorElement_def, mul_inv_rev]
        calc n₁ * z₁ * (n₂ * z₂) * (z₁⁻¹ * n₁⁻¹) * (z₂⁻¹ * n₂⁻¹)
            = n₁ * (z₁ * n₂) * z₂ * z₁⁻¹ * n₁⁻¹ * z₂⁻¹ * n₂⁻¹ := by group
          _ = n₁ * n₂ * (z₁ * z₂ * z₁⁻¹) * n₁⁻¹ * z₂⁻¹ * n₂⁻¹ := by rw [h1]; group
          _ = n₁ * n₂ * z₂ * n₁⁻¹ * z₂⁻¹ * n₂⁻¹ := by rw [hz12]; group
          _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by
            have h3 : z₂ * n₁⁻¹ = n₁⁻¹ * z₂ := by
              have := (Subgroup.mem_center_iff.1 hz₂ n₁⁻¹).symm
              exact this
            calc n₁ * n₂ * z₂ * n₁⁻¹ * z₂⁻¹ * n₂⁻¹ = n₁ * n₂ * (z₂ * n₁⁻¹) * z₂⁻¹ * n₂⁻¹ := by
                  group
              _ = n₁ * n₂ * (n₁⁻¹ * z₂) * z₂⁻¹ * n₂⁻¹ := by rw [h3]
              _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by group
      rw [e, commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)
    rw [eq_top_iff, ← hperf]
    exact hle

end Quasi

section Conj

variable {M : Type*} [Group M] {X : Subgroup M}

theorem mem_centralizer_of_comm_conj [X.Normal] (hX : IsQuasisimple ↥X) {b : M}
    (hb : ∀ g ∈ X, (g * b * g⁻¹) * b = b * (g * b * g⁻¹)) :
    b ∈ Subgroup.centralizer (X : Set M) := by
  set S : Set M := {u | ∃ g ∈ X, u = g * b * g⁻¹} with hS
  set B : Subgroup M := Subgroup.closure S with hB
  have hbS : b ∈ S := ⟨1, X.one_mem, by group⟩
  have hgen : ∀ u ∈ S, ∀ v ∈ S, u * v = v * u := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    have := hb (g⁻¹ * h) (X.mul_mem (X.inv_mem hg) hh)
    calc g * b * g⁻¹ * (h * b * h⁻¹)
        = g * (b * ((g⁻¹ * h) * b * (g⁻¹ * h)⁻¹)) * g⁻¹ := by group
      _ = g * (((g⁻¹ * h) * b * (g⁻¹ * h)⁻¹) * b) * g⁻¹ := by rw [this]
      _ = h * b * h⁻¹ * (g * b * g⁻¹) := by group
  have hBS : ∀ u ∈ B, ∀ s ∈ S, s * u = u * s := by
    intro u hu s hs
    have h1 : B ≤ Subgroup.centralizer S := (Subgroup.closure_le _).2 fun u' hu' =>
      Subgroup.mem_centralizer_iff.2 fun v hv => hgen v hv u' hu'
    exact Subgroup.mem_centralizer_iff.1 (h1 hu) s hs
  have hBcomm : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := by
    intro u hu v hv
    have h1 : B ≤ Subgroup.centralizer ({u} : Set M) := (Subgroup.closure_le _).2 fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.2 (hBS u hu s hs)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (h1 hv)).symm
  have hBconj : ∀ h ∈ X, ∀ u ∈ B, h * u * h⁻¹ ∈ B := by
    intro h hh u hu
    have : B ≤ B.comap (MulAut.conj h).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, hg, rfl⟩
      show h * (g * b * g⁻¹) * h⁻¹ ∈ B
      exact Subgroup.subset_closure ⟨h * g, X.mul_mem hh hg, by group⟩
    exact this hu
  set N : Subgroup M := ⁅X, B⁆ with hN
  have hcomm_eq : ∀ g u : M, ⁅g, u⁆ = (g * u * g⁻¹) * u⁻¹ := fun g u => by
    simp [commutatorElement_def]
  have hNX : N ≤ X := by
    refine Subgroup.commutator_le.2 fun g hg u _ => ?_
    have : ⁅g, u⁆ = g * (u * g⁻¹ * u⁻¹) := by rw [hcomm_eq]; group
    rw [this]
    exact X.mul_mem hg (‹X.Normal›.conj_mem g⁻¹ (X.inv_mem hg) u)
  have hNB : N ≤ B := by
    refine Subgroup.commutator_le.2 fun g hg u hu => ?_
    rw [hcomm_eq]
    exact B.mul_mem (hBconj g hg u hu) (B.inv_mem hu)
  have hNconj : ∀ h ∈ X, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h hh n hn
    have : N ≤ N.comap (MulAut.conj h).toMonoidHom := by
      refine Subgroup.commutator_le.2 fun g hg u hu => ?_
      show h * ⁅g, u⁆ * h⁻¹ ∈ N
      have e : h * ⁅g, u⁆ * h⁻¹ = ⁅h * g * h⁻¹, h * u * h⁻¹⁆ := by
        simp [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator (X.mul_mem (X.mul_mem hh hg) (X.inv_mem hh))
        (hBconj h hh u hu)
    exact this hn
  have hN₀ : (N.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : M) ∈ N := hn
    show ((g * n * g⁻¹ : ↥X) : M) ∈ N
    exact hNconj g g.2 n hn'
  have hN₀top : N.subgroupOf X ≠ ⊤ := by
    intro htop
    obtain ⟨a, c, hac⟩ := exists_not_comm hX
    apply hac
    have ha : (a : M) ∈ N := Subgroup.mem_subgroupOf.1 (htop ▸ Subgroup.mem_top a)
    have hc : (c : M) ∈ N := Subgroup.mem_subgroupOf.1 (htop ▸ Subgroup.mem_top c)
    exact Subtype.ext (hBcomm _ (hNB ha) _ (hNB hc))
  have hN₀c : N.subgroupOf X ≤ Subgroup.center ↥X := normal_le_center hX _ hN₀top
  have hNcent : N ≤ Subgroup.centralizer (X : Set M) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.1 (hN₀c (Subgroup.mem_subgroupOf.2 hn : (⟨n, hNX hn⟩ : ↥X) ∈
      N.subgroupOf X)) ⟨g, hg⟩
    exact congrArg Subtype.val this
  have h1 : ⁅⁅X, B⁆, X⁆ = ⊥ := (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hNcent
  have h2 : ⁅⁅B, X⁆, X⁆ = ⊥ := by rw [Subgroup.commutator_comm B X]; exact h1
  have h3 : ⁅⁅X, X⁆, B⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hXX : X ≤ ⁅X, X⁆ := by
    have hperf := hX.1
    have hle : commutator ↥X ≤ (⁅X, X⁆).subgroupOf X := by
      show ⁅(⊤ : Subgroup ↥X), ⊤⁆ ≤ _
      refine Subgroup.commutator_le.2 fun a _ c _ => ?_
      exact Subgroup.mem_subgroupOf.2 (Subgroup.commutator_mem_commutator a.2 c.2)
    intro x hx
    have : (⟨x, hx⟩ : ↥X) ∈ (⁅X, X⁆).subgroupOf X := hle (hperf ▸ Subgroup.mem_top _)
    exact Subgroup.mem_subgroupOf.1 this
  have h4 : ⁅X, B⁆ = ⊥ := by
    rw [eq_bot_iff, ← h3]
    exact Subgroup.commutator_mono hXX le_rfl
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hmem : ⁅g, b⁆ ∈ (⁅X, B⁆ : Subgroup M) :=
    Subgroup.commutator_mem_commutator hg (Subgroup.subset_closure hbS)
  rw [h4, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem inf_centralizer_eq_bot_of_not_le [X.Normal] (hX : IsQuasisimple ↥X) {P : Subgroup M}
    (h36 : ∀ g ∈ X, (∃ y ∈ P, y ≠ 1 ∧ ∃ y' ∈ P, y = g * y' * g⁻¹) →
      ∀ y₁ ∈ P, ∀ y₂ ∈ P, (g * y₁ * g⁻¹) * y₂ = y₂ * (g * y₁ * g⁻¹))
    (hnot : ¬ P ≤ Subgroup.centralizer (X : Set M)) :
    P ⊓ Subgroup.centralizer (X : Set M) = ⊥ := by
  obtain ⟨b, hbP, hbC⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  rw [eq_bot_iff]
  rintro y ⟨hyP, hyC⟩
  by_contra hy1
  have hy1' : y ≠ 1 := fun h => hy1 (by rw [h]; exact Subgroup.one_mem _)
  obtain ⟨g, hgX, hg⟩ : ∃ g ∈ X, (g * b * g⁻¹) * b ≠ b * (g * b * g⁻¹) := by
    by_contra hcon
    push Not at hcon
    exact hbC (mem_centralizer_of_comm_conj hX hcon)
  have hyg : y = g * y * g⁻¹ := by
    have := Subgroup.mem_centralizer_iff.1 hyC g hgX
    rw [this]; group
  exact hg (h36 g hgX ⟨y, hyP, hy1', y, hyP, hyg⟩ b hbP b hbP)

end Conj

end CFSG.CGT.T75D
