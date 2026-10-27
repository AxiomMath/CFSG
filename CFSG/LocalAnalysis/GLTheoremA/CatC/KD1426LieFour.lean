module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieFourCase
public import CFSG.GroupTheory.FixedPointFreeCommutator

public section

open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalInvolution.Models

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem diagFour_comm {x y : GL (Fin 3) K} (hx : x ∈ diagFour (K := K))
    (hy : y ∈ diagFour (K := K)) : x * y = y * x := by
  obtain ⟨a, b, ha, hb, rfl⟩ := mem_diagFour.mp hx
  obtain ⟨a', b', ha', hb', rfl⟩ := mem_diagFour.mp hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem conj_mem_map_diagFour {g b t : GL (Fin 3) K}
    {σ : Equiv.Perm (Fin 3)}
    (hmono : IsMonomialFor ((g⁻¹ * b * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ)
    (ht : t ∈ (diagFour (K := K)).map (MulAut.conj g).toMonoidHom) :
    b * t * b⁻¹ ∈ (diagFour (K := K)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp ht
  have hnorm : (g⁻¹ * b * g) * d * (g⁻¹ * b * g)⁻¹ ∈ diagFour (K := K) :=
    diagFour_normalized hmono hd
  refine Subgroup.mem_map.mpr ⟨(g⁻¹ * b * g) * d * (g⁻¹ * b * g)⁻¹, hnorm, ?_⟩
  change g * ((g⁻¹ * b * g) * d * (g⁻¹ * b * g)⁻¹) * g⁻¹ =
    b * (g * d * g⁻¹) * b⁻¹
  group

private theorem exists_fourGroup_of_support (hK : PiField π p f K) (hp : 5 ≤ p)
    (hq : ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {B : Subgroup (GL (Fin 3) K)} {g b : GL (Fin 3) K} {σ : Equiv.Perm (Fin 3)}
    (hg : g ∈ glPi π 3 (p ^ f) K) (hb : b ∈ B)
    (hmono_b : IsMonomialFor
      ((g⁻¹ * b * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ)
    (hσ3 : σ ^ 3 = 1) (hσne : σ ≠ 1)
    (hmono : ∀ b' ∈ B, ∃ σ' : Equiv.Perm (Fin 3), IsMonomialFor
      ((g⁻¹ * b' * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ') :
    ∃ T : Subgroup (GL (Fin 3) K), T ≤ slPi π 3 (p ^ f) K ∧ Nat.card T = 4 ∧
      (∀ t ∈ T, t ^ 2 = 1) ∧ T ⊓ zPi π 3 (p ^ f) K = ⊥ ∧
      (∀ b' ∈ B, b' ∈ Subgroup.normalizer (T : Set (GL (Fin 3) K))) ∧
      (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧
      (∀ t ∈ T, b * t * b⁻¹ = t → t = 1) := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  let T : Subgroup (GL (Fin 3) K) := (diagFour (K := K)).map (MulAut.conj g).toMonoidHom
  have hTdef : T = (diagFour (K := K)).map (MulAut.conj g).toMonoidHom := rfl
  have hTleSL : T ≤ slPi π 3 (p ^ f) K := by
    rw [hTdef]
    calc (diagFour (K := K)).map (MulAut.conj g).toMonoidHom
        ≤ (slPi π 3 (p ^ f) K).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono (diagFour_le_slPi hK hp)
      _ = slPi π 3 (p ^ f) K := map_conj_slPi hπ hg
  have hTcard : Nat.card T = 4 := by
    rw [hTdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, card_diagFour hK hp]
  have hTsq : ∀ t ∈ T, t ^ 2 = 1 := by
    intro t ht
    rw [hTdef, Subgroup.mem_map] at ht
    obtain ⟨d, hd, rfl⟩ := ht
    have hd2 : d ^ 2 = 1 := diagFour_sq hd
    calc (MulAut.conj g) d ^ 2 = g * d ^ 2 * g⁻¹ := by
          change (g * d * g⁻¹) ^ 2 = g * d ^ 2 * g⁻¹
          rw [pow_two, pow_two]
          group
      _ = 1 := by rw [hd2]; group
  have hTinf : T ⊓ zPi π 3 (p ^ f) K = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨htT, htZ⟩ := Subgroup.mem_inf.mp ht
    rw [hTdef, Subgroup.mem_map] at htT
    obtain ⟨d, hdD, rfl⟩ := htT
    have hdZ : d ∈ zPi π 3 (p ^ f) K := by
      have h : d = g⁻¹ * (g * d * g⁻¹) * g := by group
      rw [h]
      exact inv_conj_mem_zPi hK hq hτ hτ1 htZ
    have hdDZ : d ∈ diagFour (K := K) ⊓ zPi π 3 (p ^ f) K := ⟨hdD, hdZ⟩
    rw [diagFour_inf_zPi hK hp hq hτ hτ1] at hdDZ
    rw [Subgroup.mem_bot] at hdDZ ⊢
    rw [hdDZ]
    exact map_one _
  have hTnorm : ∀ b' ∈ B, b' ∈ Subgroup.normalizer (T : Set (GL (Fin 3) K)) := by
    intro b' hb'
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      obtain ⟨σ', hσ'⟩ := hmono b' hb'
      rw [hTdef] at ht ⊢
      exact conj_mem_map_diagFour hσ' ht
    · intro ht
      rw [hTdef] at ht ⊢
      have hb'inv : b'⁻¹ ∈ B := B.inv_mem hb'
      obtain ⟨σ', hσ'⟩ := hmono b'⁻¹ hb'inv
      have h' := conj_mem_map_diagFour hσ' ht
      have h'' : b'⁻¹ * (b' * t * b'⁻¹) * (b'⁻¹)⁻¹ = t := by group
      rw [← h'']
      exact h'
  have hTabelian : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    rw [hTdef, Subgroup.mem_map] at hx hy
    obtain ⟨dx, hdx, rfl⟩ := hx
    obtain ⟨dy, hdy, rfl⟩ := hy
    have hcomm := diagFour_comm hdx hdy
    calc g * dx * g⁻¹ * (g * dy * g⁻¹) = g * (dx * dy) * g⁻¹ := by group
      _ = g * (dy * dx) * g⁻¹ := by rw [hcomm]
      _ = g * dy * g⁻¹ * (g * dx * g⁻¹) := by group
  have hfree : ∀ t ∈ T, b * t * b⁻¹ = t → t = 1 := by
    intro t ht hfix
    rw [hTdef, Subgroup.mem_map] at ht
    obtain ⟨d, hdD, rfl⟩ := ht
    have hfix' : (g⁻¹ * b * g) * d * (g⁻¹ * b * g)⁻¹ = d := by
      have h := congrArg (fun x => g⁻¹ * x * g) hfix
      calc (g⁻¹ * b * g) * d * (g⁻¹ * b * g)⁻¹
          = g⁻¹ * (b * (g * d * g⁻¹) * b⁻¹) * g := by group
        _ = g⁻¹ * (g * d * g⁻¹) * g := h
        _ = d := by group
    have hd1 : d = 1 := fixedPointFree_of_threeCycle hK hp hmono_b hσ3 hσne hdD hfix'
    rw [hd1]
    simp
  exact ⟨T, hTleSL, hTcard, hTsq, hTinf, hTnorm, hTabelian, hfree⟩

theorem exists_fourGroup_of_pgl_nine (hK : PiField π p f K) (hp : 5 ≤ p) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {B : Subgroup (GL (Fin 3) K)} (hBH : B ≤ glPi π 3 (p ^ f) K) (hZB : zPi π 3 (p ^ f) K ≤ B)
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K) (hBc : ∀ b ∈ B, ∀ c ∈ B, ⁅b, c⁆ ∈ zPi π 3 (p ^ f) K)
    (hB9 : (zPi π 3 (p ^ f) K).relIndex B = 9)
    (hno : ∀ b ∈ B, ∀ z ∈ zPi π 3 (p ^ f) K, ∀ g ∈ glPi π 3 (p ^ f) K, ∀ e : Kˣ,
      ((e : K) = τ ∨ (e : K) = τ ^ 2) → g⁻¹ * (b * z) * g ≠ diagE e) :
    ∃ T : Subgroup (GL (Fin 3) K), T ≤ slPi π 3 (p ^ f) K ∧ Nat.card T = 4 ∧
      (∀ t ∈ T, t ^ 2 = 1) ∧ T ⊓ zPi π 3 (p ^ f) K = ⊥ ∧
      (∀ b ∈ B, b ∈ Subgroup.normalizer (T : Set (GL (Fin 3) K))) ∧
      ∃ b ∈ B, ⁅T, Subgroup.zpowers b⁆ = T := by
  classical
  haveI : Finite K := hK.finite
  obtain ⟨g, b, σ, hg, hb, hmono_b, hσ3, hσne, hmono⟩ :=
    exists_threeCycle_support hK hq hτ hτ1 hBH hZB hB hBc hB9 hno
  obtain ⟨T, hTle, hTcard, hTsq, hTinf, hTnorm, hTabelian, hfree⟩ :=
    exists_fourGroup_of_support hK hp hq hτ hτ1 hg hb hmono_b hσ3 hσne hmono
  exact ⟨T, hTle, hTcard, hTsq, hTinf, hTnorm, b, hb,
    commutator_zpowers_eq_of_fixedPointFree T b hTabelian (hTnorm b hb) hfree⟩

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

end
