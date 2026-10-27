module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace D3P

theorem exists_stable_sylow_fixing_pair {G : Type*} [Group G] [Finite G] (α β : MulAut G)
    (hα : α ^ 3 = 1) (hβ : β ^ 3 = 1) (hαβ : α * β = β * α) (A : Subgroup G)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hfα : ∀ a ∈ A, α a = a) (hfβ : ∀ a ∈ A, β a = a) :
    ∃ S : Sylow 3 G, A ≤ (S : Subgroup G) ∧ (S : Subgroup G).map α.toMonoidHom = S ∧
      (S : Subgroup G).map β.toMonoidHom = S := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hA.2 g g.2)⟩
  set H₁ : Subgroup (MulAut G) := A.map (MulAut.conj : G →* MulAut G) with hH₁
  set H₂ : Subgroup (MulAut G) := Subgroup.zpowers α ⊔ Subgroup.zpowers β with hH₂
  have hp3 : ∀ γ : MulAut G, γ ^ 3 = 1 → IsPGroup 3 (Subgroup.zpowers γ) := by
    intro γ hγ
    have hord : orderOf γ ∣ 3 := orderOf_dvd_of_pow_eq_one hγ
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (by simpa using hord : orderOf γ ∣ 3 ^ 1)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hH₁p : IsPGroup 3 H₁ := hAp.map _
  have hcβα : Commute β α := hαβ.symm
  have hαnorm : Subgroup.zpowers α ≤ Subgroup.normalizer (Subgroup.zpowers β : Set (MulAut G)) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro g hg
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((Commute.zpow_zpow hcβα n m)).eq
  have hH₂p : IsPGroup 3 H₂ := (hp3 α hα).to_sup_of_normal_right' (hp3 β hβ) hαnorm
  have hcomm : ∀ a ∈ A, ∀ g ∈ H₂, g * MulAut.conj a = MulAut.conj a * g := by
    intro a ha g hg
    have h1 : ∀ γ : MulAut G, (∀ a ∈ A, γ a = a) → γ ∈ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut G)) := by
      intro γ hγ
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hγ a ha]
    have h2 : H₂ ≤ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut G)) :=
      sup_le (Subgroup.zpowers_le.2 (h1 α hfα)) (Subgroup.zpowers_le.2 (h1 β hfβ))
    exact (Subgroup.mem_centralizer_iff.1 (h2 hg) _ rfl).symm
  have hnorm : H₁ ≤ Subgroup.normalizer (H₂ : Set (MulAut G)) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have key : ∀ g' ∈ H₂, MulAut.conj a * g' * (MulAut.conj a)⁻¹ = g' := fun g' hg' => by
      calc MulAut.conj a * g' * (MulAut.conj a)⁻¹ = (g' * MulAut.conj a) * (MulAut.conj a)⁻¹ := by
            rw [← hcomm a ha g' hg']
        _ = g' := by group
    constructor
    · intro hg
      rw [key g hg]
      exact hg
    · intro h
      have h2 := key _ h
      have : g = (MulAut.conj a)⁻¹ * (MulAut.conj a * g * (MulAut.conj a)⁻¹) * MulAut.conj a := by
        group
      rw [this]
      have h3 := hcomm a ha _ h
      have e : (MulAut.conj a)⁻¹ * (MulAut.conj a * g * (MulAut.conj a)⁻¹) * MulAut.conj a =
          MulAut.conj a * g * (MulAut.conj a)⁻¹ := by
        calc (MulAut.conj a)⁻¹ * (MulAut.conj a * g * (MulAut.conj a)⁻¹) * MulAut.conj a
            = (MulAut.conj a)⁻¹ * ((MulAut.conj a * g * (MulAut.conj a)⁻¹) * MulAut.conj a) := by
              rw [mul_assoc]
          _ = (MulAut.conj a)⁻¹ * (MulAut.conj a * (MulAut.conj a * g * (MulAut.conj a)⁻¹)) := by
              rw [h3]
          _ = MulAut.conj a * g * (MulAut.conj a)⁻¹ := by group
      rw [e]
      exact h
  have hX : IsPGroup 3 (H₁ ⊔ H₂ : Subgroup (MulAut G)) := hH₁p.to_sup_of_normal_right' hH₂p hnorm
  have hmod := hX.card_modEq_card_fixedPoints (Sylow 3 G)
  have hsyl : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hfix' : Nat.card (MulAction.fixedPoints (H₁ ⊔ H₂ : Subgroup (MulAut G)) (Sylow 3 G)) ≡
      1 [MOD 3] := hmod.symm.trans hsyl
  have hne : Nonempty (MulAction.fixedPoints (H₁ ⊔ H₂ : Subgroup (MulAut G)) (Sylow 3 G)) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints (H₁ ⊔ H₂ : Subgroup (MulAut G))
        (Sylow 3 G)) := by
      by_contra h0
      have : Nat.card (MulAction.fixedPoints (H₁ ⊔ H₂ : Subgroup (MulAut G)) (Sylow 3 G)) = 0 := by
        omega
      rw [this] at hfix'
      exact absurd (Nat.ModEq.symm hfix') (by decide)
    exact (Nat.card_pos_iff.1 hpos).1
  obtain ⟨⟨S, hS⟩⟩ := hne
  have hstab : ∀ γ ∈ (H₁ ⊔ H₂ : Subgroup (MulAut G)),
      (S : Subgroup G).map γ.toMonoidHom = S := by
    intro γ hγ
    have h1 : (⟨γ, hγ⟩ : ↥(H₁ ⊔ H₂)) • S = S := hS _
    have h2 : ((((⟨γ, hγ⟩ : ↥(H₁ ⊔ H₂)) • S : Sylow 3 G) : Subgroup G)) = S :=
      congrArg (fun T : Sylow 3 G => (T : Subgroup G)) h1
    have h3 := (Sylow.pointwise_smul_def (g := (⟨γ, hγ⟩ : ↥(H₁ ⊔ H₂))) (P := S)).symm.trans h2
    rw [Subgroup.pointwise_smul_def] at h3
    exact h3
  refine ⟨S, ?_, hstab α ?_, hstab β ?_⟩
  · refine (hAp.sylow_mem_fixedPoints_iff (Q := S)).1 ?_
    rw [MulAction.mem_fixedPoints]
    intro a
    have h1 : (⟨MulAut.conj (a : G), (le_sup_left : H₁ ≤ H₁ ⊔ H₂) ⟨a, a.2, rfl⟩⟩ :
        ↥(H₁ ⊔ H₂)) • S = S := hS _
    exact h1
  · exact (le_sup_right : H₂ ≤ H₁ ⊔ H₂) (Subgroup.mem_sup_left (Subgroup.mem_zpowers α))
  · exact (le_sup_right : H₂ ≤ H₁ ⊔ H₂) (Subgroup.mem_sup_right (Subgroup.mem_zpowers β))



end D3P

end CFSG.LocalAnalysis.GLTheoremA
