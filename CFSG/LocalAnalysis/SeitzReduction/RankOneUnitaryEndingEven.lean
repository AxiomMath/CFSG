module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingNormalizer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingNormalizerBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSylow

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_le_maximal_pGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q N : Subgroup G} (hQ : IsPGroup p Q) (hQN : Q ≤ N) :
    ∃ P : Subgroup G, IsPGroup p P ∧ Q ≤ P ∧ P ≤ N ∧
      ∀ K : Subgroup G, IsPGroup p K → P ≤ K → K ≤ N → K ≤ P := by
  obtain ⟨R, hR⟩ := (hQ.comap_subtype (K := N)).exists_le_sylow
  refine ⟨(R : Subgroup N).map N.subtype, R.isPGroup'.map N.subtype, ?_, map_subtype_le _, ?_⟩
  · intro x hx
    exact ⟨⟨x, hQN hx⟩, hR (show (⟨x, hQN hx⟩ : N) ∈ Q.comap N.subtype from hx), rfl⟩
  · intro K hK hPK hKN
    have hK' : IsPGroup p (K.comap N.subtype) := hK.comap_subtype (K := N)
    have hle : (R : Subgroup N) ≤ K.comap N.subtype := fun x hx => hPK ⟨x, hx, rfl⟩
    have heq := R.is_maximal' hK' hle
    intro k hk
    have hk' : (⟨k, hKN hk⟩ : N) ∈ K.comap N.subtype := hk
    rw [heq] at hk'
    exact ⟨_, hk', rfl⟩

@[expose] def U3EndingNormalConjInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G)
    (s v : G) (Y₁ Y₂ : Subgroup G), U3EndingData G L f t T R₂ U₁ s → v ∈ T → v ^ 2 = 1 →
    v ∉ szT₁ L T ⊔ zpowers t → s * t * s⁻¹ = t * v →
    Y₁ ⊔ Y₂ = U₁ → Y₁ ⊓ Y₂ = ⊥ → (∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) →
    (∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) → (∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) →
    ∀ P : Subgroup G, IsPGroup 2 P → U₁ ⊔ (T ⊓ normalizer (U₁ : Set G)) ≤ P →
      P ≤ normalizer (U₁ : Set G) →
      ∀ g : G, U₁.map (MulAut.conj g).toMonoidHom ≤ P →
        P ≤ normalizer ((U₁.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) →
          U₁.map (MulAut.conj g).toMonoidHom = U₁

theorem u3EndingSylowNormalizerInput_of_normalConj
    (hK : U3EndingNormalConjInput) : U3EndingSylowNormalizerInput := by
  intro G _ _ L f t T R₂ U₁ s v Y₁ Y₂ hD hvT hv2 hvS hsv hY hinf hcomm ht₁ ht₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := hD.u1
  have hQ2 : IsPGroup 2 (U₁ ⊔ (T ⊓ normalizer (U₁ : Set G)) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hU.isPGroup (hD.start.isPGroup.to_le inf_le_left)
      inf_le_right
  have hQN : U₁ ⊔ (T ⊓ normalizer (U₁ : Set G)) ≤ normalizer (U₁ : Set G) :=
    sup_le le_normalizer inf_le_right
  obtain ⟨P, hP2, hQP, hPN, hmax⟩ := exists_le_maximal_pGroup hQ2 hQN
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_normalizer_le hP2 hmax (fun z hz _ => by
    have hPz : P.map (MulAut.conj z).toMonoidHom = P := mem_normalizer_iff_map_conj_eq'.mp hz
    have hle : U₁.map (MulAut.conj z).toMonoidHom ≤ P := by
      rw [← hPz]
      exact map_mono (le_sup_left.trans hQP)
    have hPN' : P ≤ normalizer ((U₁.map (MulAut.conj z).toMonoidHom : Subgroup G) : Set G) := by
      intro y hy
      refine mem_normalizer_map_conj_of_mem_normalizer (hPN ?_)
      have h1 := (mem_normalizer_iff.mp (inv_mem hz) y).mp hy
      rwa [inv_inv] at h1
    exact mem_normalizer_iff_map_conj_eq'.mpr
      (hK G L f t T R₂ U₁ s v Y₁ Y₂ hD hvT hv2 hvS hsv hY hinf hcomm ht₁ ht₂ P hP2 hQP hPN z hle
        hPN'))
  exact ⟨S, hS ▸ hPN⟩

theorem u3EndingSylowInput_of_normalConj
    (hK : U3EndingNormalConjInput) : U3EndingSylowInput :=
  u3EndingSylowInput_of_normalizer (u3EndingSylowNormalizerInput_of_normalConj hK)

end CFSG.SeitzReduction.RankOne
