module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapKappa
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abMix2

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

namespace MB

@[expose] def inR1 (x : MB) : Bool := !bit x 0

@[expose] def inQ1 (x : MB) : Bool := !bit x 1

@[expose] def inE1 (x : MB) : Bool := !bit x 0 && !bit x 1 && !bit x 2 && !bit x 3

@[expose] def R1h : Subgroup MB := ofPred inR1 (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

@[expose] def Q1h : Subgroup MB := ofPred inQ1 (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

@[expose] def E1h : Subgroup MB := ofPred inE1 (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem card_E1h : Nat.card E1h = 16 := by rw [E1h, card_ofPred]; decide +kernel
theorem card_E0h : Nat.card E0h = 8 := by rw [E0h, card_ofPred]; decide +kernel

@[expose] def gensR1 : List MB := [u, w₁, v, z, y, t, k]

@[expose] def gensQ1 : List MB := [w₂, w₁, v, z, y, t, k]

theorem nfBits_eq (x : MB) : nfBits x =
    [bit x 0, bit x 1, bit x 2, bit x 3, bit x 4, bit x 5, bit x 6, bit x 7] := rfl

theorem nf_bits (x : MB) : x = (if bit x 0 then w₂ else 1) * ((if bit x 1 then u else 1) *
    ((if bit x 2 then w₁ else 1) * ((if bit x 3 then v else 1) * ((if bit x 4 then z else 1) *
    ((if bit x 5 then y else 1) * ((if bit x 6 then t else 1) *
    (if bit x 7 then k else 1))))))) := by
  conv_lhs => rw [nf_spec x, nfBits_eq]
  simp only [gens, nfProd, mul_one]

theorem E1h_span (x : MB) (hx : inE1 x = true) : InSpan [z, y, t, k] x := by
  simp only [inE1, Bool.and_eq_true, Bool.not_eq_true'] at hx
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hx
  refine ⟨[bit x 4, bit x 5, bit x 6, bit x 7], mem_allBits _, ?_⟩
  conv_lhs => rw [nf_bits x]
  simp only [h0, h1, h2, h3, nfProd, mul_one, one_mul, Bool.false_eq_true, ↓reduceIte]

theorem E0h_span (x : MB) (hx : inE0 x = true) : InSpan [z, y, k] x := by
  simp only [inE0, Bool.and_eq_true, Bool.not_eq_true'] at hx
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h6⟩ := hx
  refine ⟨[bit x 4, bit x 5, bit x 7], mem_allBits _, ?_⟩
  conv_lhs => rw [nf_bits x]
  simp only [h0, h1, h2, h3, h6, nfProd, mul_one, one_mul, Bool.false_eq_true, ↓reduceIte]

theorem R1h_normal_gens : ∀ g ∈ gens, ∀ x : MB, inR1 x = true → inR1 (g * x * g⁻¹) = true := by
  decide +kernel

theorem Q1h_normal_gens : ∀ g ∈ gens, ∀ x : MB, inQ1 x = true → inQ1 (g * x * g⁻¹) = true := by
  decide +kernel

theorem conj_of_gens {p : MB → Bool}
    (hp : ∀ g ∈ gens, ∀ x : MB, p x = true → p (g * x * g⁻¹) = true) (g x : MB)
    (hx : p x = true) : p (g * x * g⁻¹) = true := by
  have key : ∀ (gs : List MB), (∀ g ∈ gs, g ∈ gens) → ∀ bs x, p x = true →
      p (nfProd gs bs * x * (nfProd gs bs)⁻¹) = true := by
    intro gs
    induction gs with
    | nil => intro _ bs x hx; simpa [nfProd] using hx
    | cons g gs ih =>
      intro hgs bs x hx
      cases bs with
      | nil => simpa [nfProd] using hx
      | cons b bs =>
        have h' := ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg)) bs x hx
        simp only [nfProd]
        cases b
        · simpa using h'
        · have := hp g (hgs g (List.mem_cons_self ..)) _ h'
          simpa [mul_assoc] using this
  rw [nf_spec g]
  exact key gens (fun _ h => h) _ x hx

theorem R1h_normal (g x : MB) (hx : inR1 x = true) : inR1 (g * x * g⁻¹) = true :=
  conj_of_gens R1h_normal_gens g x hx

theorem Q1h_normal (g x : MB) (hx : inQ1 x = true) : inQ1 (g * x * g⁻¹) = true :=
  conj_of_gens Q1h_normal_gens g x hx

theorem mem_E1h_of_comm : ∀ x : MB, x * z = z * x → x * y = y * x → x * t = t * x →
    x * k = k * x → inE1 x = true := by decide +kernel

theorem eq_of_comm_R1h : ∀ x : MB, (∀ g ∈ gensR1, g * x = x * g) →
    x = 1 ∨ x = z ∨ x = k ∨ x = z * k := by decide +kernel

theorem mem_E0h_of_comm_Q1h : ∀ x : MB, inE1 x = true → (∀ g ∈ gensQ1, g * x = x * g) →
    inE0 x = true := by decide +kernel

theorem inR1_of_inE1 : ∀ x : MB, inE1 x = true → inR1 x = true := by decide +kernel

theorem inQ1_of_inE1 : ∀ x : MB, inE1 x = true → inQ1 x = true := by decide +kernel

theorem gensR1_mem : ∀ g ∈ gensR1, inR1 g = true := by decide +kernel

theorem gensQ1_mem : ∀ g ∈ gensQ1, inQ1 g = true := by decide +kernel

theorem center_mem : ∀ x : MB, z * x = x * z ∧ k * x = x * k := by decide +kernel

end MB

end Sec8

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

structure BData (S : KDBase A C) (T₁ : Subgroup X) where
  G : GData S T₁
  h₁ : G.D₁.q0 = .homocyclic
  h₂ : G.D₂.q0 = .homocyclic

namespace BData

variable (B : BData S T₁)

@[expose] noncomputable def ι : MB →* X := B.G.P₁.ιB B.h₁

theorem ι_w₂ : B.ι MB.w₂ = B.G.D₁.w₂ := (IPair.ιB_spec (P := B.G.P₁) B.h₁).1
theorem ι_u : B.ι MB.u = S.x * S.y := by
  rw [← B.G.hu₁]; exact (IPair.ιB_spec (P := B.G.P₁) B.h₁).2.1
theorem ι_w₁ : B.ι MB.w₁ = B.G.V₁.w₁N := (IPair.ιB_spec (P := B.G.P₁) B.h₁).2.2.1
theorem ι_v : B.ι MB.v = B.G.V₁.vN := (IPair.ιB_spec (P := B.G.P₁) B.h₁).2.2.2.1
theorem ι_z : B.ι MB.z = S.z := (IPair.ιB_spec (P := B.G.P₁) B.h₁).2.2.2.2.1
theorem ι_y : B.ι MB.y = S.y := (IPair.ιB_spec (P := B.G.P₁) B.h₁).2.2.2.2.2.1
theorem ι_t : B.ι MB.t = t := (IPair.ιB_spec (P := B.G.P₁) B.h₁).2.2.2.2.2.2.1
theorem ι_k : B.ι MB.k = S.k := (IPair.ιB_spec (P := B.G.P₁) B.h₁).2.2.2.2.2.2.2

theorem ι_injective : Function.Injective B.ι := IPair.ιB_injective (P := B.G.P₁) B.h₁

theorem range_ι : B.ι.range = B.G.D₁.S₁ := IPair.range_ιB (P := B.G.P₁) B.h₁

theorem ι_mem_S₁ (x : MB) : B.ι x ∈ B.G.D₁.S₁ := B.range_ι ▸ ⟨x, rfl⟩

theorem exists_ι {g : X} (hg : g ∈ B.G.D₁.S₁) : ∃ x : MB, B.ι x = g := by
  rw [← B.range_ι] at hg
  exact hg

theorem card_S₁ : Nat.card B.G.D₁.S₁ = 256 := by
  rw [← B.range_ι, ← Nat.card_congr (MonoidHom.ofInjective B.ι_injective).toEquiv, MB.card_eq]
  norm_num

theorem isPGroup_S₁ : IsPGroup 2 B.G.D₁.S₁ := B.G.D₁.isPGroup_S₁

theorem ι_w₁c : B.ι (MB.w₁ * MB.y) = B.G.V₁.w₁c := by
  rw [map_mul, B.ι_w₁, B.ι_y]
  exact (KD8ab.ISide.w₁c_of_homoc _ B.h₁).symm

@[expose] noncomputable def R1 : Subgroup X := MB.R1h.map B.ι

@[expose] noncomputable def Q1 : Subgroup X := MB.Q1h.map B.ι

theorem Q1_le_S₁ : B.Q1 ≤ B.G.D₁.S₁ := by
  rw [Q1, ← B.range_ι]; exact map_le_range _ _

theorem ι_mem_E₁ {x : MB} (hx : MB.inE1 x = true) : B.ι x ∈ S.E S.y := by
  refine map_mem_of_inSpan B.ι (MB.E1h_span x hx) fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · rw [B.ι_z]; exact Frame.z_mem_E _
  · rw [B.ι_y]; exact Frame.yi_mem_E _
  · rw [B.ι_t]; exact Frame.t_mem_E _
  · rw [B.ι_k]; exact Frame.k_mem_E _

theorem ι_mem_E0 {x : MB} (hx : MB.inE0 x = true) : B.ι x ∈ S.E0 S.y S.k := by
  refine map_mem_of_inSpan B.ι (MB.E0h_span x hx) fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · rw [B.ι_z]; exact B.G.V₁.z_mem_E0
  · rw [B.ι_y]; exact B.G.V₁.yi_mem_E0
  · rw [B.ι_k]; exact B.G.V₁.ki_mem_E0

theorem mem_E₁_of_comm {g : X} (hg : g ∈ B.G.D₁.S₁)
    (hc : ∀ e ∈ S.E S.y, g * e = e * g) : g ∈ S.E S.y := by
  obtain ⟨x, rfl⟩ := B.exists_ι hg
  have key : ∀ m : MB, MB.inE1 m = true → x * m = m * x := fun m hm =>
    B.ι_injective (by rw [map_mul, map_mul]; exact hc _ (B.ι_mem_E₁ hm))
  exact B.ι_mem_E₁ (MB.mem_E1h_of_comm x (key _ (by decide +kernel)) (key _ (by decide +kernel))
    (key _ (by decide +kernel)) (key _ (by decide +kernel)))

end BData

end KD8abB

end CFSG.ComponentClassification.HSFLit
