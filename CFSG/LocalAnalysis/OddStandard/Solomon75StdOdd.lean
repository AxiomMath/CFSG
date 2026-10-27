module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalOdd
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalSylow

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

namespace Sec5Ctx

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {N A : Subgroup X} {M : AhatModel X n A}

theorem odd_false' (h : Sec5Ctx X n z N A M)
    (hone : ∀ u v : M.K, orderOf u = 2 → orderOf v = 2 → u ∉ center M.K → v ∉ center M.K →
      IsConj u v)
    (hsimple : IsSimpleGroup X) (hnonab : ∃ a b : X, a * b ≠ b * a)
    (S : Sylow 2 ↥N) (hSyl : IsSylowTwoIn ⊤ ((S : Subgroup ↥N).map N.subtype))
    {s₁ : X} (hs₁N : s₁ ∈ N) (hs₁2 : orderOf s₁ = 2) (hs₁z : s₁ ≠ z)
    (hs₁c : ∃ g : X, g⁻¹ * z * g = s₁) (hs₁even : sign (h.psi ⟨s₁, hs₁N⟩) = 1)
    (hpar : ∀ (t : X) (htN : t ∈ N), t * t = 1 → t ≠ 1 → t ≠ z →
      (∃ g : X, g⁻¹ * z * g = t) → sign (h.psi ⟨t, htN⟩) = 1)
    {t : X} (htN : t ∈ N) (hodd : sign (h.psi ⟨t, htN⟩) = -1) : False := by
  have hn := h.hn
  obtain ⟨y, hyN, hy2, hyψ⟩ := h.exists_involution_odd htN hodd
  set y' : ↥N := ⟨y, hyN⟩ with hy'
  have hy'2 : y' * y' = 1 := Subtype.ext hy2
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow S hy'2
  set t₀ : ↥N := g * y' * g⁻¹ with ht₀
  have ht₀2 : t₀ * t₀ = 1 := by
    rw [ht₀]
    calc g * y' * g⁻¹ * (g * y' * g⁻¹) = g * (y' * y') * g⁻¹ := by group
      _ = 1 := by rw [hy'2]; group
  have hψt₀ : h.psi t₀ = h.psi g * h.psi y' * (h.psi g)⁻¹ := by
    rw [ht₀, map_mul, map_mul, map_inv]
  have hψy' : h.psi y' = oddOne hn ∨ h.psi y' = oddOne hn * dblTwo hn := hyψ
  have hsign : sign (h.psi t₀) = -1 := by
    rw [hψt₀, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv]
    rcases hψy' with h1 | h1
    · rw [h1, sign_oddOne]
      rcases Int.units_eq_one_or (sign (h.psi g)) with h2 | h2 <;> rw [h2] <;> decide
    · rw [h1, sign_oddOne_mul_dblTwo]
      rcases Int.units_eq_one_or (sign (h.psi g)) with h2 | h2 <;> rw [h2] <;> decide
  have hψne : h.psi t₀ ≠ 1 := fun h1 => by
    rw [h1, Perm.sign_one] at hsign
    exact absurd hsign (by decide)
  have ht₀1 : (t₀ : X) ≠ 1 := fun h1 => hψne (by
    have : t₀ = 1 := Subtype.ext h1
    rw [this, map_one])
  have ht₀z : (t₀ : X) ≠ z := fun h1 => hψne (by
    have : t₀ = ⟨z, h.hAN h.hzA⟩ := Subtype.ext h1
    rw [this]
    exact h.psi_z)
  have ht₀2' : (t₀ : X) * t₀ = 1 := congrArg Subtype.val ht₀2
  have ht₀ord : orderOf (t₀ : X) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact ht₀2') ht₀1
  let ε : ↥N →* ℤˣ := Perm.sign.comp h.psi
  let U : Subgroup X := ((S : Subgroup ↥N) ⊓ ε.ker).map N.subtype
  let T : Subgroup X := (S : Subgroup ↥N).map N.subtype
  have hUT : U ≤ T := Subgroup.map_mono inf_le_left
  have hεt₀ : ε t₀ = -1 := hsign
  have hUidx : U.relIndex T = 2 := by
    show (Subgroup.map N.subtype ((S : Subgroup ↥N) ⊓ ε.ker)).relIndex
      (Subgroup.map N.subtype (S : Subgroup ↥N)) = 2
    rw [Subgroup.relIndex_map_map_of_injective _ _ N.subtype_injective, inf_comm,
      Subgroup.inf_relIndex_right]
    show (ε.ker.subgroupOf (S : Subgroup ↥N)).index = 2
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t₀, hg⟩, fun b => ?_⟩
    have hmem : ∀ c : ↥(S : Subgroup ↥N), c ∈ ε.ker.subgroupOf (S : Subgroup ↥N) ↔
        ε (c : ↥N) = 1 := fun c => by
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rw [hmem, hmem]
    have hmul : ε ((b * ⟨t₀, hg⟩ : ↥(S : Subgroup ↥N)) : ↥N) = ε (b : ↥N) * (-1) := by
      rw [Subgroup.coe_mul, map_mul]
      exact congrArg (fun u => ε (b : ↥N) * u) hεt₀
    rw [hmul]
    rcases Int.units_eq_one_or (ε (b : ↥N)) with h1 | h1 <;> rw [h1] <;> decide
  have hT : IsPGroup 2 ↥T := hSyl.2.1
  have hTidx : ¬ 2 ∣ T.index := by
    have := hSyl.2.2
    rwa [Subgroup.relIndex_top_right] at this
  have ht₀T : (t₀ : X) ∈ T := ⟨t₀, hg, rfl⟩
  have ht₀U : (t₀ : X) ∉ U := by
    rintro ⟨c, ⟨_, hc⟩, hct⟩
    have hct' : c = t₀ := Subtype.ext hct
    have hc1 : ε c = 1 := hc
    rw [hct'] at hc1
    rw [hc1] at hεt₀
    exact absurd hεt₀ (by decide)
  obtain ⟨g', hg'⟩ := exists_conj_mem_of_thompson hsimple hnonab hT hTidx hUT hUidx ht₀T ht₀U
    ht₀ord
  obtain ⟨c, ⟨_, hc⟩, hcw⟩ := hg'
  set w : X := g'⁻¹ * (t₀ : X) * g' with hw
  have hwN : w ∈ N := by rw [← hcw]; exact c.2
  have hw2 : w * w = 1 := by
    calc w * w = g'⁻¹ * ((t₀ : X) * t₀) * g' := by rw [hw]; group
      _ = 1 := by rw [ht₀2']; group
  have hw1 : w ≠ 1 := fun h1 => ht₀1 (by
    have : (t₀ : X) = g' * w * g'⁻¹ := by rw [hw]; group
    rw [this, h1]; group)
  have hweven : sign (h.psi ⟨w, hwN⟩) = 1 := by
    have : (⟨w, hwN⟩ : ↥N) = c := Subtype.ext hcw.symm
    rw [this]
    exact hc
  have hconj : ∃ g : X, g⁻¹ * z * g = (t₀ : X) := by
    by_cases hwz : w = z
    · refine ⟨g'⁻¹, ?_⟩
      rw [← hwz, hw]; group
    · have hs₁sq : s₁ * s₁ = 1 := by
        rw [← sq]; rw [← hs₁2]; exact pow_orderOf_eq_one s₁
      have hs₁1 : s₁ ≠ 1 := fun h1 => by
        rw [h1, orderOf_one] at hs₁2
        exact absurd hs₁2 (by norm_num)
      obtain ⟨g'', hg''⟩ := h.exists_conj_of_involutions hone hwN hs₁N hw2 hs₁sq hw1 hs₁1 hwz
        hs₁z hweven hs₁even
      obtain ⟨g₁, hg₁⟩ := hs₁c
      refine ⟨g₁ * g'' * g'⁻¹, ?_⟩
      have h3 : (t₀ : X) = g' * w * g'⁻¹ := by rw [hw]; group
      rw [h3, hg'', ← hg₁]
      group
  have hpar' := hpar (t₀ : X) t₀.2 ht₀2' ht₀1 ht₀z hconj
  rw [show (⟨(t₀ : X), t₀.2⟩ : ↥N) = t₀ from rfl, hsign] at hpar'
  exact absurd hpar' (by decide)

end Sec5Ctx

end CFSG.OddStandard.Solomon75
