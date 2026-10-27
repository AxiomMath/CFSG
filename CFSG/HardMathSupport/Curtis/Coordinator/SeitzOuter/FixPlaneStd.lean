module

public import CFSG.LieType.SeitzGeneration.HyperOuterFieldAut
public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP

theorem fixPlaneGen_of_standard {P : Type} [Group P] {p : ℕ} (D : Subgroup (MulAut P))
    (S : Set (MulAut P))
    (hdesc : ∀ α : MulAut P, IsOuterOfOrder p α → ∃ d ∈ D, ∃ f ∈ S, α = d * f * d⁻¹)
    (R : Subgroup P) (hfix : ∀ f ∈ S, fixedSubgroup f = R)
    (hgen : ∀ A : Subgroup P, A ≤ R → IsElemAbelian p A → Nat.card A = p ^ 2 →
      R ≤ Subgroup.closure {k | k ∈ R ∧ ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k}) :
    FixPlaneGen P p := by
  intro σ hσ A hA hAa hAc
  obtain ⟨d, -, f, hf, rfl⟩ := hdesc σ hσ
  have hF : fixedSubgroup (d * f * d⁻¹) = R.map d.toMonoidHom := by
    rw [fixedSubgroup_conj d f, hfix f hf]
  rw [hF] at hA ⊢
  set A' : Subgroup P := A.map d⁻¹.toMonoidHom with hA'
  have hA'R : A' ≤ R := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨r, hr, hra⟩ := hA ha
    have : d⁻¹ a = r := by rw [← hra]; simp
    simpa [this] using hr
  have hA'a : IsElemAbelian p A' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hAa _
  have hA'c : Nat.card A' = p ^ 2 := by
    rw [hA', Subgroup.card_map_of_injective (d⁻¹).injective, hAc]
  have h1 := hgen A' hA'R hA'a hA'c
  have h2 := Subgroup.map_mono (f := d.toMonoidHom) h1
  rw [MonoidHom.map_closure] at h2
  refine h2.trans (Subgroup.closure_mono ?_)
  rintro _ ⟨k, ⟨hkR, b, ⟨a, ha, rfl⟩, hb1, hkb⟩, rfl⟩
  refine ⟨⟨k, hkR, rfl⟩, d (d⁻¹ a), ?_, ?_, ?_⟩
  · simpa using ha
  · intro h
    apply hb1
    have : d (d⁻¹ a) = d 1 := by rw [h]; simp
    simpa using d.injective this
  · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [← map_mul, ← map_mul]
    exact congrArg d hkb

theorem planeGenIn_range {M P : Type} [Group M] [Group P] (ψ : M →* P)
    (hψ : Function.Injective ψ) {p : ℕ}
    (hM : ∀ E : Subgroup M, IsElemAbelian p E → Nat.card E = p ^ 2 →
      Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤) :
    ∀ A : Subgroup P, A ≤ ψ.range → IsElemAbelian p A → Nat.card A = p ^ 2 →
      ψ.range ≤ Subgroup.closure {k | k ∈ ψ.range ∧ ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k} := by
  intro A hA hAa hAc
  set A0 : Subgroup M := A.comap ψ with hA0
  have hmap : A0.map ψ = A := Subgroup.map_comap_eq_self hA
  have hA0a : IsElemAbelian p A0 := by
    obtain ⟨⟨hc⟩, hx⟩ := hAa
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx' => ?_⟩
    · apply Subtype.ext
      apply hψ
      have := hc.comm ⟨ψ (a : M), a.2⟩ ⟨ψ (b : M), b.2⟩
      have h := congrArg Subtype.val this
      change ψ (a : M) * ψ (b : M) = ψ (b : M) * ψ (a : M) at h
      change ψ ((a : M) * b) = ψ ((b : M) * a)
      rw [map_mul, map_mul]
      exact h
    · apply hψ
      rw [map_pow, map_one]
      exact hx _ hx'
  have hA0c : Nat.card A0 = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hψ, hmap, hAc]
  have h1 := hM A0 hA0a hA0c
  have h2 : ψ.range = (Subgroup.closure {k | ∃ x ∈ A0, x ≠ 1 ∧ k * x = x * k}).map ψ := by
    rw [h1, Subgroup.map_top, MonoidHom.range_eq_map]
  refine h2.le.trans ?_
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨k, ⟨x, hx, hx1, hk⟩, rfl⟩
  refine ⟨⟨k, rfl⟩, ψ x, ?_, ?_, ?_⟩
  · rw [← hmap]; exact ⟨x, hx, rfl⟩
  · intro h
    exact hx1 (hψ (by rw [h, map_one]))
  · rw [← map_mul, ← map_mul, hk]

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
