module

public import CFSG.CGT.Stroth77.AlperinBridge3x
public import CFSG.CGT.Stroth77.AlperinBridge320
public import CFSG.CGT.Stroth77.Types3ExclusionGL32

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.ONan76

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {D : Subgroup G} {uv t u : G}

theorem false_of_onan_type320
    (hON : ∀ {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (P : Sylow 2 X) {n : ℕ},
      3 ≤ n → ∀ {v₁ v₂ v₃ s t : X}, AlperinFrame n v₁ v₂ v₃ s t →
        Subgroup.closure ({v₁, v₂, v₃, s, t} : Set X) = P → False)
    {m : ℕ} (hm : 3 ≤ m) (e : Additive D ≃+ Torus (Type320.k m))
    (ht : t ∈ Subgroup.normalizer (D : Set G)) (hu : u ∈ Subgroup.normalizer (D : Set G))
    (ht_conj : ∀ x : D,
      e (Additive.ofMul (conjBy ht x)) = (Type320.actionPaper m hm).φt (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D,
      e (Additive.ofMul (conjBy hu x)) = (Type320.actionPaper m hm).φu (e (Additive.ofMul x)))
    (ht2 : t * t = 1) (hu2 : u * u = 1) (huv2 : uv * uv = 1) (htu : t * u = u * uv * t)
    (S : Sylow 2 G) (hS : (S : Subgroup G) = D ⊔ Subgroup.closure {uv, t, u}) : False := by
  obtain ⟨v₁, v₂, v₃, s, r, hF, -, hcl⟩ :=
    exists_alperinFrame_of_type320 hm e ht hu ht_conj hu_conj ht2 hu2 huv2 htu
  exact hON S hm hF (hcl.trans hS.symm)

theorem false_of_onan_type321
    (hON : ∀ {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (P : Sylow 2 X) {n : ℕ},
      3 ≤ n → ∀ {v₁ v₂ v₃ s t : X}, AlperinFrame n v₁ v₂ v₃ s t →
        Subgroup.closure ({v₁, v₂, v₃, s, t} : Set X) = P → False)
    (e : Additive D ≃+ Torus Type321.k)
    (ht : t ∈ Subgroup.normalizer (D : Set G)) (hu : u ∈ Subgroup.normalizer (D : Set G))
    (ht_conj : ∀ x : D,
      e (Additive.ofMul (conjBy ht x)) = Type321.action.φt (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D,
      e (Additive.ofMul (conjBy hu x)) = Type321.action.φu (e (Additive.ofMul x)))
    (ht2 : t * t = 1) (hu2 : u * u = 1) (huv2 : uv * uv = 1) (htu : t * u = u * uv * t)
    (S : Sylow 2 G) (hS : (S : Subgroup G) = D ⊔ Subgroup.closure {uv, t, u}) : False := by
  obtain ⟨v₁, v₂, v₃, s, r, hF, -, hcl⟩ :=
    exists_alperinFrame_of_type321 e ht hu ht_conj hu_conj ht2 hu2 huv2 htu
  exact hON S le_rfl hF (hcl.trans hS.symm)

theorem eq_t310_two_of_stroth41
    (hON : ∀ {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (P : Sylow 2 X) {n : ℕ},
      3 ≤ n → ∀ {v₁ v₂ v₃ s t : X}, AlperinFrame n v₁ v₂ v₃ s t →
        Subgroup.closure ({v₁, v₂, v₃, s, t} : Set X) = P → False)
    {τ : StrothTypeIndex} (hτ : τ.k 0 = τ.k 1) (hn : 2 ≤ τ.k 1) (e : Additive D ≃+ Torus τ.k)
    (huv : uv ∈ Subgroup.normalizer (D : Set G)) (ht : t ∈ Subgroup.normalizer (D : Set G))
    (hu : u ∈ Subgroup.normalizer (D : Set G))
    (huv_conj : ∀ x : D, e (Additive.ofMul (conjBy huv x)) = τ.action.φuv (e (Additive.ofMul x)))
    (ht_conj : ∀ x : D, e (Additive.ofMul (conjBy ht x)) = τ.action.φt (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D, e (Additive.ofMul (conjBy hu x)) = τ.action.φu (e (Additive.ofMul x)))
    (huv2 : uv * uv = 1) (ht2 : t * t = 1) (hu2 : u * u = 1) (htu : t * u = u * uv * t)
    (S : Sylow 2 G) (hS : (S : Subgroup G) = D ⊔ Subgroup.closure {uv, t, u})
    (φ : ↥(Subgroup.normalizer (D : Set G)) →* GL (Fin 3) (ZMod 2)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (D : Set G)).subgroupOf
      (Subgroup.normalizer (D : Set G))) :
    τ = .t310 2 le_rfl := by
  cases τ
  case t300 n =>
    exact (false_of_gl32_type300 hn e huv hu huv_conj hu_conj huv2 hu2 φ hφ hker).elim
  case t310 m hm =>
    obtain rfl | h3 : m = 2 ∨ 3 ≤ m := by omega
    · rfl
    · exact (false_of_gl32_type310 h3 e huv hu huv_conj hu_conj huv2 hu2 φ hφ hker).elim
  case t320 m hm =>
    exact (false_of_onan_type320 hON hm e ht hu ht_conj hu_conj ht2 hu2 huv2 htu S hS).elim
  case t330 m hm =>
    exact (false_of_gl32_type330 hm e huv hu huv_conj hu_conj huv2 hu2 φ hφ hker).elim
  case t321 =>
    exact (false_of_onan_type321 hON e ht hu ht_conj hu_conj ht2 hu2 huv2 htu S hS).elim
  case t331 =>
    exact (false_of_gl32_type331 e huv hu huv_conj hu_conj huv2 hu2 φ hφ hker).elim
  all_goals
    exfalso
    simp [StrothTypeIndex.k, Type100.k, Type101.k, Type110.k, Type111.k, Type120.k, Type121.k,
      Type130.k, Type131.k, Type200.k, Type201.k, Type210.k, Type211.k, Type220.k, Type221.k,
      Type230.k, Type231.k] at hτ

end CFSG.CGT.Stroth77
