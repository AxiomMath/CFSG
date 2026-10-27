module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.FixPlaneSpThree

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2

theorem closure_comm_planes_of_index
    {d₀ : TauCeti.ValidLieTypeIndex} {P₀ : Type} [Group P₀] [IsSimpleGroup P₀]
    (hnab : ∃ a b : P₀, a * b ≠ b * a) (ε : Cat d₀ ≃* P₀) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ≠ d₀.1.characteristic) (hex : ¬ IsD2SeitzException p d₀.1)
    (hcl : IsClassicalIndex d₀.1) (hrk : RankLE2 p P₀) :
    ∀ E₁ : Subgroup P₀, IsElemAbelian p E₁ → Nat.card E₁ = p ^ 2 →
      Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  intro E₁ hE₁ hc₁
  have hinj0 : Function.Injective (MulAut.conj : P₀ →* MulAut P₀) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center P₀ := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun φ => φ z) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center P₀) with h | h
    · rw [h, Subgroup.mem_bot] at hgc
      exact hgc
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have : a ∈ Subgroup.center P₀ := h ▸ Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.mp this b).symm)
  have hinj : Function.Injective (MulAut.conj : Cat d₀ →* MulAut (Cat d₀)) :=
    conj_injective_of_mulEquiv ε hinj0
  set E₀ : Subgroup (Cat d₀) := E₁.map ε.symm.toMonoidHom with hE₀
  have hE₀a : IsElemAbelian p E₀ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₁ _
  have hE₀c : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective ε.symm.injective, hc₁]
  have hEa : IsElemAbelian p (E₀.map (MulAut.conj : Cat d₀ →* MulAut (Cat d₀))) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀a _
  have hEc : Nat.card (E₀.map (MulAut.conj : Cat d₀ →* MulAut (Cat d₀))) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hE₀c]
  have hEinner : InnerPlane d₀ p (E₀.map (MulAut.conj : Cat d₀ →* MulAut (Cat d₀))) := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have hrk0 : RankLE2 p (Cat d₀) :=
    rankLE2_of_injective ε.toMonoidHom ε.injective hrk
  have hPG : PlaneGen (E₀.map (MulAut.conj : Cat d₀ →* MulAut (Cat d₀))) :=
    seitzInnerLowClassical_of_heisCore unitaryHeisCore d₀ p hp hp2 hpd hex _ hEa hEc
      ⟨hEinner, hrk0, hcl⟩
  have hcl' := closure_comm_of_planeGen_conj hPG
  rw [eq_top_iff]
  intro g _
  have hg : ε.symm g ∈ Subgroup.closure {k : Cat d₀ | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k} := by
    rw [hcl']; trivial
  have h1 := Subgroup.mem_map_of_mem ε.toMonoidHom hg
  rw [MonoidHom.map_closure] at h1
  have h2 : (ε.toMonoidHom '' {k : Cat d₀ | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k}) ⊆
      {k | ∃ x ∈ E₁, x ≠ 1 ∧ k * x = x * k} := by
    rintro _ ⟨k, ⟨x, ⟨y, hy, rfl⟩, hx1, hk⟩, rfl⟩
    refine ⟨y, hy, ?_, ?_⟩
    · rintro rfl
      exact hx1 (map_one _)
    · have := congrArg ε.toMonoidHom hk
      simpa using this
  simpa using Subgroup.closure_mono h2 h1

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
