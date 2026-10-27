module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyWrSyl
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyWrPrep

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

theorem d8_center : ∀ d' : D8, (∀ d : D8, d * d' = d' * d) →
    d' = 1 ∨ d' = DihedralGroup.r 2 := by decide

variable {X : Type*} [Group X] [Finite X]

theorem exists_sylow_wreath {K₀ : Type*} [Group K₀]
    (hK₀ : Nat.card K₀ = 8) (Ψ : D8 × K₀ →* X) (hΨ : Function.Injective Ψ)
    (κ : K₀) (hκ1 : κ ≠ 1) (hκc : ∀ b : K₀, b * κ = κ * b)
    (hκZ : ∀ b : K₀, (∀ c : K₀, c * b = b * c) → b = 1 ∨ b = κ)
    {τ v : X} (δ : D8) (hδ : δ = 1 ∨ δ = DihedralGroup.r 2) (hτ : τ = Ψ (DihedralGroup.r 2, 1))
    (hv : v = Ψ (δ, κ))
    (hQ : ∀ y : X, (y * τ = τ * y ∧ y * v = v * y) ↔ y ∈ Ψ.range)
    (hC : Nat.card (centralizer ({τ} : Set X)) = 960)
    {x₀ : X} (hx₀ : x₀ * τ * x₀⁻¹ = v)
    (hnc : ¬ ∃ g : X, τ * v = g * τ * g⁻¹) :
    ∃ P : Sylow 2 X, Nonempty (↥P ≃* W8) := by
  set Q : Subgroup X := Ψ.range with hQdef
  set ρ : D8 →* X := Ψ.comp (MonoidHom.inl D8 K₀) with hρdef
  have hρ : ∀ a, ρ a = Ψ (a, 1) := fun a => rfl
  have hρinj : Function.Injective ρ := fun a b h => by
    have := hΨ h
    exact (Prod.mk.inj this).1
  have hρQ : ∀ a, ρ a ∈ Q := fun a => ⟨(a, 1), rfl⟩
  have hQcard : Nat.card Q = 64 := by
    rw [hQdef, ← Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv, Nat.card_prod,
      DihedralGroup.nat_card, hK₀]
  have hτρ : τ = ρ (DihedralGroup.r 2) := hτ
  have hr2 : (DihedralGroup.r 2 : D8) ≠ 1 := by decide
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hr2
    have : Ψ (DihedralGroup.r 2, 1) = Ψ 1 := by rw [← hτ, h, map_one]
    exact (Prod.mk.inj (hΨ this)).1
  have hv1 : v ≠ 1 := by
    intro h
    apply hκ1
    have : Ψ (δ, κ) = Ψ 1 := by rw [← hv, h, map_one]
    exact (Prod.mk.inj (hΨ this)).2
  have hτv : τ ≠ v := by
    intro h
    apply hκ1
    have : Ψ (DihedralGroup.r 2, 1) = Ψ (δ, κ) := by rw [← hτ, ← hv, h]
    exact (Prod.mk.inj (hΨ this)).2.symm
  have hτvc : τ * v = v * τ := by
    rw [hτ, hv, ← map_mul, ← map_mul]
    congr 1
    refine Prod.ext ?_ (by simp [hκc])
    rcases hδ with rfl | rfl <;> simp
  have hQτ : ∀ q ∈ Q, q * τ = τ * q := fun q hq => ((hQ q).2 hq).1
  have hQv : ∀ q ∈ Q, q * v = v * q := fun q hq => ((hQ q).2 hq).2
  have hvQ : v ∈ Q := ⟨(δ, κ), hv.symm⟩
  have hτQ : τ ∈ Q := ⟨(DihedralGroup.r 2, 1), hτ.symm⟩
  obtain ⟨x, hxQ, hxQ', hxτ⟩ := exists_swap_normalizing Q hQτ hQv hQcard hC hx₀
  have hxv : x * v * x⁻¹ = τ := by
    have hv'Q : x * v * x⁻¹ ∈ Q := hxQ v hvQ
    have hcen : ∀ q ∈ Q, q * (x * v * x⁻¹) = (x * v * x⁻¹) * q := by
      intro q hq
      have h1 := hQv _ (hxQ' q hq)
      calc q * (x * v * x⁻¹) = x * ((x⁻¹ * q * x) * v) * x⁻¹ := by group
        _ = x * (v * (x⁻¹ * q * x)) * x⁻¹ := by rw [h1]
        _ = (x * v * x⁻¹) * q := by group
    obtain ⟨⟨d', b'⟩, hd'b'⟩ := hv'Q
    have hcomm : ∀ d : D8, ∀ b : K₀, d * d' = d' * d ∧ b * b' = b' * b := by
      intro d b
      have := hcen (Ψ (d, b)) ⟨(d, b), rfl⟩
      rw [← hd'b', ← map_mul, ← map_mul] at this
      have := hΨ this
      exact ⟨(Prod.mk.inj this).1, (Prod.mk.inj this).2⟩
    have hd' := d8_center d' (fun d => (hcomm d 1).1)
    have hb' := hκZ b' (fun c => (hcomm 1 c).2)
    have hxτ' : x * τ * x⁻¹ = v := hxτ
    have hnot_one : x * v * x⁻¹ ≠ 1 := by
      intro h
      apply hv1
      calc v = x⁻¹ * (x * v * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    have hnot_v : x * v * x⁻¹ ≠ v := by
      intro h2
      apply hτv
      have : x * v * x⁻¹ = x * τ * x⁻¹ := by rw [h2, hxτ']
      have h3 : v = τ := by
        calc v = x⁻¹ * (x * v * x⁻¹) * x := by group
          _ = x⁻¹ * (x * τ * x⁻¹) * x := by rw [this]
          _ = τ := by group
      exact h3.symm
    have hnot_tv : x * v * x⁻¹ ≠ τ * v := by
      intro h2
      apply hnc
      refine ⟨x * x, ?_⟩
      calc τ * v = x * v * x⁻¹ := h2.symm
        _ = x * (x * τ * x⁻¹) * x⁻¹ := by rw [hxτ']
        _ = x * x * τ * (x * x)⁻¹ := by group
    have hτv1 : τ * v = Ψ (DihedralGroup.r 2 * δ, κ) := by
      rw [hτ, hv, ← map_mul]; simp
    rcases hd' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd (by rw [← hd'b']; exact map_one Ψ) hnot_one
    · rcases hδ with rfl | rfl
      · exact absurd (by rw [← hd'b', hv]) hnot_v
      · refine absurd ?_ hnot_tv
        rw [← hd'b', hτv1]
        congr 2
    · rw [← hd'b']; exact hτ.symm
    · rcases hδ with rfl | rfl
      · refine absurd ?_ hnot_tv
        rw [← hd'b', hτv1]
        congr 2
      · exact absurd (by rw [← hd'b', hv]) hnot_v
  have hctx : WrCtx ρ Q x v :=
    { inj := hρinj
      card := hQcard
      rho_mem := hρQ
      normal := by
        intro q hq a
        obtain ⟨⟨d, b⟩, rfl⟩ := hq
        refine ⟨d * a * d⁻¹, ?_⟩
        rw [hρ, hρ, ← map_mul, ← map_inv, ← map_mul]
        congr 1
        ext <;> simp
      x_conj := hxQ
      x_conj' := hxQ'
      tau := by rw [← hτρ]; exact hxτ
      vtau := by rw [← hτρ]; exact hxv
      v_notin := by
        intro a h
        apply hκ1
        have : Ψ (a, 1) = Ψ (δ, κ) := by rw [← hρ, h, hv]
        exact (Prod.mk.inj (hΨ this)).2.symm }
  have hcomm := hctx.comm
  have hdecomp_inj := fun {a b a' b' : D8} => hctx.decomp_inj (a := a) (b := b) (a' := a')
    (b' := b')
  have hxxQ : x * x ∈ Q := by
    refine (hQ (x * x)).1 ⟨?_, ?_⟩
    · calc x * x * τ = x * (x * τ * x⁻¹) * x := by group
        _ = x * v * x := by rw [hxτ]
        _ = (x * v * x⁻¹) * (x * x) := by group
        _ = τ * (x * x) := by rw [hxv]
    · calc x * x * v = x * (x * v * x⁻¹) * x := by group
        _ = x * τ * x := by rw [hxv]
        _ = (x * τ * x⁻¹) * (x * x) := by group
        _ = v * (x * x) := by rw [hxτ]
  obtain ⟨a₀, b₀, hq₀⟩ := hctx.exists_decomp (x * x) hxxQ
  obtain ⟨b₀', hb₀'⟩ := hctx.normal (x * x) hxxQ b₀
  have h2 : x * x = ρ b₀' * (x * ρ a₀ * x⁻¹) := by
    have h3 : x * x = (x * ρ a₀ * x⁻¹) * ρ b₀' := by
      calc x * x = x * (x * x) * x⁻¹ := by group
        _ = x * (ρ a₀ * (x * ρ b₀ * x⁻¹)) * x⁻¹ := by rw [← hq₀]
        _ = (x * ρ a₀ * x⁻¹) * ((x * x) * ρ b₀ * (x * x)⁻¹) := by group
        _ = (x * ρ a₀ * x⁻¹) * ρ b₀' := by rw [hb₀']
    rw [h3]; exact (hcomm b₀' a₀).symm
  obtain ⟨ha₀, hb₀⟩ := hdecomp_inj (hq₀.symm.trans h2)
  subst hb₀
  have hq₀' : x * x = ρ b₀ * (x * ρ b₀ * x⁻¹) := hq₀
  have hAW : ρ b₀ * (x * ρ b₀ * x⁻¹) = (x * ρ b₀ * x⁻¹) * ρ b₀ := hcomm b₀ b₀
  have hρinv : ρ b₀⁻¹ = (ρ b₀)⁻¹ := map_inv ρ b₀
  have hyy : (x * ρ b₀⁻¹) * (x * ρ b₀⁻¹) = 1 := by
    rw [hρinv]
    calc x * (ρ b₀)⁻¹ * (x * (ρ b₀)⁻¹)
        = (x * ρ b₀ * x⁻¹)⁻¹ * (x * x) * (ρ b₀)⁻¹ := by group
      _ = (x * ρ b₀ * x⁻¹)⁻¹ * (ρ b₀ * (x * ρ b₀ * x⁻¹)) * (ρ b₀)⁻¹ := by rw [hq₀']
      _ = (x * ρ b₀ * x⁻¹)⁻¹ * ((x * ρ b₀ * x⁻¹) * ρ b₀) * (ρ b₀)⁻¹ := by rw [hAW]
      _ = 1 := by group
  have hyconj : ∀ b : D8, (x * ρ b₀⁻¹) * ρ b * (x * ρ b₀⁻¹)⁻¹ =
      x * ρ (b₀⁻¹ * b * b₀) * x⁻¹ := by
    intro b
    rw [map_mul, map_mul, hρinv]
    group
  have hyQ : ∀ q ∈ Q, (x * ρ b₀⁻¹) * q * (x * ρ b₀⁻¹)⁻¹ ∈ Q := by
    intro q hq
    have h1 : ρ b₀⁻¹ * q * (ρ b₀⁻¹)⁻¹ ∈ Q :=
      Q.mul_mem (Q.mul_mem (hρQ _) hq) (Q.inv_mem (hρQ _))
    have : (x * ρ b₀⁻¹) * q * (x * ρ b₀⁻¹)⁻¹ = x * (ρ b₀⁻¹ * q * (ρ b₀⁻¹)⁻¹) * x⁻¹ := by group
    rw [this]; exact hxQ _ h1
  have hyτ : (x * ρ b₀⁻¹) * τ * (x * ρ b₀⁻¹)⁻¹ = v := by
    have h1 := hQτ _ (hρQ b₀⁻¹)
    calc (x * ρ b₀⁻¹) * τ * (x * ρ b₀⁻¹)⁻¹ = x * (ρ b₀⁻¹ * τ) * (ρ b₀⁻¹)⁻¹ * x⁻¹ := by group
      _ = x * (τ * ρ b₀⁻¹) * (ρ b₀⁻¹)⁻¹ * x⁻¹ := by rw [h1]
      _ = x * τ * x⁻¹ := by group
      _ = v := hxτ
  have hyv : (x * ρ b₀⁻¹) * v * (x * ρ b₀⁻¹)⁻¹ = τ := by
    have h1 := hQv _ (hρQ b₀⁻¹)
    calc (x * ρ b₀⁻¹) * v * (x * ρ b₀⁻¹)⁻¹ = x * (ρ b₀⁻¹ * v) * (ρ b₀⁻¹)⁻¹ * x⁻¹ := by group
      _ = x * (v * ρ b₀⁻¹) * (ρ b₀⁻¹)⁻¹ * x⁻¹ := by rw [h1]
      _ = x * v * x⁻¹ := by group
      _ = τ := hxv
  have hc'' : ∀ a b : D8, ρ a * ((x * ρ b₀⁻¹) * ρ b * (x * ρ b₀⁻¹)⁻¹) =
      ((x * ρ b₀⁻¹) * ρ b * (x * ρ b₀⁻¹)⁻¹) * ρ a := by
    intro a b
    rw [hyconj b]
    exact hcomm a _
  have hinf'' : ∀ a b : D8, ρ a = (x * ρ b₀⁻¹) * ρ b * (x * ρ b₀⁻¹)⁻¹ → ρ a = 1 := by
    intro a b h
    rw [hyconj b] at h
    rw [hctx.inf_aux h, map_one]
  have hdec'' : ∀ q ∈ Q, ∃ a b : D8,
      q = ρ a * ((x * ρ b₀⁻¹) * ρ b * (x * ρ b₀⁻¹)⁻¹) := by
    intro q hq
    obtain ⟨a, b', hab⟩ := hctx.exists_decomp q hq
    refine ⟨a, b₀ * b' * b₀⁻¹, ?_⟩
    have : b₀⁻¹ * (b₀ * b' * b₀⁻¹) * b₀ = b' := by group
    rw [hyconj, this]
    exact hab
  exact exists_sylow_of_data ρ hρinj Q hρQ hQ hτρ hyy hyτ hyv hyQ hc'' hinf'' hdec'' hτvc hτ1
    hτv hv1 hnc

end CFSG.EvenSporadicStandard.TwoHS
