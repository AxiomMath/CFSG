module

public import CFSG.ClassicalInvolution.AschTight.Sec7L713E
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2NC
public import CFSG.ClassicalInvolution.Asc77.AscIH8Model
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyMat

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
open scoped MatrixGroups

namespace MuTab

section Four

variable {F : Type} [Field F]

@[expose] def wFour (F : Type) [Field F] : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

@[expose] def uOne (F : Type) [Field F] : SL(2, F) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem wFour_mul_self : wFour F * wFour F = -1 := by
  apply Subtype.ext
  show (!![0, 1; -1, 0] * !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) = _
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wFour_not_comm : wFour F * uOne F ≠ uOne F * wFour F := by
  intro h
  have h' := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  change (!![0, 1; -1, 0] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 =
    (!![1, 1; 0, 1] * !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) 0 0 at h'
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h'

end Four

section Charts

variable {X : Type} [Group X] {F F' : Type} [Field F] [Finite F] [Field F']

theorem orderOf_chart_wFour (hodd : Odd (Nat.card F)) {Φ : SL(2, F) →* X}
    (hΦ : Function.Injective Φ) : orderOf (Φ (wFour F)) = 4 := by
  have h2 : Φ (wFour F) ^ 2 = Φ (-1) := by rw [pow_two, ← map_mul, wFour_mul_self]
  have hne : ¬ Φ (wFour F) ^ 2 = 1 := by
    rw [h2]
    intro h
    exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd (hΦ (h.trans (map_one Φ).symm))
  have h4 : Φ (wFour F) ^ 4 = 1 := by
    have e : Φ (wFour F) ^ 4 = (Φ (wFour F) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [e, h2, ← map_pow]
    have : (-1 : SL(2, F)) ^ 2 = 1 := by simp
    rw [this, map_one]
  simpa using orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hne) (by simpa using h4)

theorem exists_orderFour_of_charts (hodd : Odd (Nat.card F))
    {Φ : SL(2, F) →* X} {Ψ : SL(2, F') →* X} (hΦ : Function.Injective Φ)
    (hcomm : ∀ A B, Φ A * Ψ B = Ψ B * Φ A) (hneg : Φ (-1) = Ψ (-1))
    (g₀ : X) :
    ∃ c j d : X, IsUniqueInvolution (conjSub g₀ Φ.range) c ∧ j ∈ conjSub g₀ Φ.range ∧
      orderOf j = 4 ∧ d * d = 1 ∧ d ≠ 1 ∧ d ≠ c ∧ j * d = d * j := by
  set j₀ := Φ (wFour F) with hj₀
  set k₀ := Ψ (wFour F') with hk₀
  set c₀ := Φ (-1) with hc₀
  have hjj : j₀ * j₀ = c₀ := by rw [hj₀, ← map_mul, wFour_mul_self]
  have hkk : k₀ * k₀ = c₀ := by rw [hk₀, ← map_mul, wFour_mul_self, hneg]
  have hcc : c₀ * c₀ = 1 := (isUniqueInvolution_range_sl2 hodd hΦ).sq
  have hjk : j₀ * k₀ = k₀ * j₀ := hcomm _ _
  have hnot : ∀ B : SL(2, F'), j₀ ≠ Ψ B := by
    intro B h
    have h1 := hcomm (uOne F) B
    rw [← h, hj₀, ← map_mul, ← map_mul] at h1
    exact wFour_not_comm (hΦ h1).symm
  have hd : (j₀ * k₀) * (j₀ * k₀) = 1 := by
    calc (j₀ * k₀) * (j₀ * k₀) = j₀ * (k₀ * j₀) * k₀ := by group
      _ = j₀ * (j₀ * k₀) * k₀ := by rw [hjk]
      _ = (j₀ * j₀) * (k₀ * k₀) := by group
      _ = 1 := by rw [hjj, hkk, hcc]
  have hd1 : j₀ * k₀ ≠ 1 := by
    intro h
    refine hnot (wFour F')⁻¹ ?_
    rw [map_inv, ← hk₀]
    exact eq_inv_of_mul_eq_one_left h
  have hdc : j₀ * k₀ ≠ c₀ := by
    intro h
    refine hnot (wFour F') ?_
    rw [← hk₀]
    exact mul_right_cancel (h.trans hkk.symm)
  have hjd : j₀ * (j₀ * k₀) = (j₀ * k₀) * j₀ := by
    calc j₀ * (j₀ * k₀) = j₀ * (k₀ * j₀) := by rw [hjk]
      _ = (j₀ * k₀) * j₀ := by group
  refine ⟨g₀ * c₀ * g₀⁻¹, g₀ * j₀ * g₀⁻¹, g₀ * (j₀ * k₀) * g₀⁻¹,
    (isUniqueInvolution_range_sl2 hodd hΦ).conj g₀, conj_mem_conjSub ⟨wFour F, rfl⟩, ?_, ?_, ?_,
    ?_, ?_⟩
  · have := orderOf_injective (MulAut.conj g₀).toMonoidHom (MulAut.conj g₀).injective j₀
    rw [orderOf_chart_wFour hodd hΦ] at this
    exact this
  · calc g₀ * (j₀ * k₀) * g₀⁻¹ * (g₀ * (j₀ * k₀) * g₀⁻¹) =
        g₀ * ((j₀ * k₀) * (j₀ * k₀)) * g₀⁻¹ := by group
      _ = 1 := by rw [hd]; group
  · intro h
    apply hd1
    have := congrArg (fun x => g₀⁻¹ * x * g₀) h
    simpa [mul_assoc] using this
  · intro h
    apply hdc
    have := congrArg (fun x => g₀⁻¹ * x * g₀) h
    simpa [mul_assoc] using this
  · calc g₀ * j₀ * g₀⁻¹ * (g₀ * (j₀ * k₀) * g₀⁻¹) = g₀ * (j₀ * (j₀ * k₀)) * g₀⁻¹ := by group
      _ = g₀ * ((j₀ * k₀) * j₀) * g₀⁻¹ := by rw [hjd]
      _ = g₀ * (j₀ * k₀) * g₀⁻¹ * (g₀ * j₀ * g₀⁻¹) := by group

end Charts

end MuTab

section Datum

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {t : StatedLieTag} {k e : ℕ} (M : Ih8Model p f Ω t k e)

omit [Finite G] in
theorem muTab_isUniqueInvolution_map {H : Type} [Group H] {ψ : H →* G}
    (hinj : Function.Injective ψ) {R : Subgroup H} {c : H} (hc : IsUniqueInvolution R c) :
    IsUniqueInvolution (R.map ψ) (ψ c) where
  mem := Subgroup.mem_map_of_mem ψ hc.mem
  ne_one := fun h => hc.ne_one (hinj (h.trans (map_one ψ).symm))
  sq := by rw [← map_mul, hc.sq, map_one]
  unique := by
    rintro _ ⟨r, hr, rfl⟩ hy
    have h1 : r * r = 1 := hinj (by rw [map_mul, hy, map_one])
    rcases hc.unique r hr h1 with h2 | h2
    · left
      rw [h2, map_one]
    · right
      rw [h2]

include M in
theorem Ih8Model.muTab_omegaStarNbr_of_orderFour (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hinj : Function.Injective M.ψ)
    (hconj : ∀ u u' : (modelUniv t k p e Fact.out).K, u * u = 1 → u' * u' = 1 → u ≠ 1 → u' ≠ 1 →
      ∃ h, h * u * h⁻¹ = u')
    {R : Subgroup (modelUniv t k p e Fact.out).K} (hR : R ∈ M.cls)
    {c j d : (modelUniv t k p e Fact.out).K} (hc : IsUniqueInvolution R c) (hj : j ∈ R)
    (hj4 : orderOf j = 4) (hd : d * d = 1) (hd1 : d ≠ 1) (hdc : d ≠ c) (hjd : j * d = d * j) :
    ∃ K ∈ Ω, (omegaStarNbr Ω K).Nonempty := by
  obtain ⟨h, hh⟩ := hconj d c hd hc.sq hd1 hc.ne_one
  have hL : conjSub h R ∈ M.cls := M.cls_conj R hR h
  have hJΩ : R.map M.ψ ∈ Ω := M.map_mem hR
  have hLΩ : (conjSub h R).map M.ψ ∈ Ω := M.map_mem hL
  have ha : IsUniqueInvolution (R.map M.ψ) (M.ψ c) := muTab_isUniqueInvolution_map hinj hc
  have hg : M.ψ (h * j * h⁻¹) ∈ (conjSub h R).map M.ψ :=
    Subgroup.mem_map_of_mem _ (conj_mem_conjSub hj)
  have hg4 : orderOf (M.ψ (h * j * h⁻¹)) = 4 := by
    rw [orderOf_injective M.ψ hinj]
    have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective j
    rw [hj4] at this
    exact this
  have hga : M.ψ c * M.ψ (h * j * h⁻¹) * (M.ψ c)⁻¹ = M.ψ (h * j * h⁻¹) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [← hh]
    have hdj : d * j * d⁻¹ = j := by rw [← hjd]; group
    calc h * d * h⁻¹ * (h * j * h⁻¹) * (h * d * h⁻¹)⁻¹ = h * (d * j * d⁻¹) * h⁻¹ := by group
      _ = h * j * h⁻¹ := by rw [hdj]
  rcases AschTight.Sec7.eq_or_mem_omegaStarNbr_of_fixed hp2 hq hΩ hJΩ hLΩ ha hg hga hg4 with
    heq | hmem
  · exfalso
    have hRh : conjSub h R = R := Subgroup.map_injective hinj heq
    have hcc : h * c * h⁻¹ = c := hc.conj_eq hRh
    apply hdc
    calc d = h⁻¹ * (h * d * h⁻¹) * h := by group
      _ = h⁻¹ * c * h := by rw [hh]
      _ = h⁻¹ * (h * c * h⁻¹) * h := by rw [hcc]
      _ = c := by group
  · exact ⟨_, hJΩ, _, hmem⟩

end Datum

end CFSG.ClassicalInvolution.Asc77
