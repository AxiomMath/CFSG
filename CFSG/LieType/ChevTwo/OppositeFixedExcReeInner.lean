module

public import CFSG.LieType.ChevTwo.OppositeFixedExcReeCore

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.Ree

theorem map_conj_conj_le_range_conj {G : Type*} [Group G] (g : G) {R : Subgroup (MulAut G)}
    (hR : R ≤ (MulAut.conj : G →* MulAut G).range) :
    R.map (MulAut.conj (MulAut.conj g)).toMonoidHom ≤ (MulAut.conj : G →* MulAut G).range := by
  rintro _ ⟨α, hα, rfl⟩
  obtain ⟨x, rfl⟩ := hR hα
  refine ⟨g * x * g⁻¹, ?_⟩
  ext y
  first
    | (change g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ = g * (x * (g⁻¹ * y * g) * x⁻¹) * g⁻¹; group)
    | simp [MulAut.conj_apply, mul_assoc]

section Cert


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem uniqueNormalFormRee_of_inner (hZ : Subgroup.center ↥(ReeTag.F4.reeGamma K a) = ⊥)
    (hδ : ∀ δ : RingAut K, δ = 1) {R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a))}
    (hR : R ≤ (MulAut.conj : ↥(ReeTag.F4.reeGamma K a) →*
      MulAut ↥(ReeTag.F4.reeGamma K a)).range) :
    UniqueNormalFormRee a R := by
  intro α hα
  obtain ⟨x, rfl⟩ := hR hα
  have h1 : ∀ h : ↥(ReeTag.F4.reeGamma K a),
      Units.map (entrywiseHom ((1 : RingAut K) : K →+* K)) (h : ModGL ReeTag.F4.tag K) = h :=
    fun h => Units.ext (entrywise_id _)
  refine ⟨(x, 1), fun h => ?_, fun p hp => ?_⟩
  · exact (congrArg (fun z : ModGL ReeTag.F4.tag K =>
      (x : ModGL ReeTag.F4.tag K) * z * (x : ModGL ReeTag.F4.tag K)⁻¹) (h1 h)).symm
  · obtain ⟨g, δ⟩ := p
    have hδ1 := hδ δ
    subst hδ1
    have hcent : x⁻¹ * g ∈ Subgroup.center ↥(ReeTag.F4.reeGamma K a) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 : ((x * y * x⁻¹ : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) =
          (g : ModGL ReeTag.F4.tag K) * (y : ModGL ReeTag.F4.tag K) *
            (g : ModGL ReeTag.F4.tag K)⁻¹ :=
        (hp y).trans (congrArg (fun z : ModGL ReeTag.F4.tag K =>
          (g : ModGL ReeTag.F4.tag K) * z * (g : ModGL ReeTag.F4.tag K)⁻¹) (h1 y))
      have e : x * y * x⁻¹ = g * y * g⁻¹ := Subtype.ext h2
      calc y * (x⁻¹ * g) = x⁻¹ * (x * y * x⁻¹) * g := by group
        _ = x⁻¹ * (g * y * g⁻¹) * g := by rw [e]
        _ = x⁻¹ * g * y := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hcent
    exact Prod.ext hcent.symm rfl

theorem oppositeFixedAt_reeGamma_inner (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hDual : ∀ {A : Set (Fin Tag.F4.rank)} {S : Subgroup (GamL Tag.F4 K)},
      (∀ s ∈ S, s.left ∈ adjointGroup Tag.F4 K ∧ s.left ∈ parabolicLevi Tag.F4 K A) →
        Odd (Nat.card S) → ∀ {u : ModGL Tag.F4 K}, u ∈ parabolicRadical Tag.F4 K A → u ≠ 1 →
          (∀ s ∈ S, conjAct Tag.F4 K s u = u) →
            ∃ v ∈ oppRadical Tag.F4 K A, v ≠ 1 ∧ ∀ s ∈ S, conjAct Tag.F4 K s v = v)
    {ι : Type} (A : ι → Set (Fin Tag.F4.rank)) (hA : ∀ j i, ReeTag.F4.perm i ∈ A j ↔ i ∈ A j)
    (hstd : ∀ Q : Subgroup ↥(ReeTag.F4.reeGamma K a), Q ≠ ⊥ → IsPGroup 2 Q →
      ∃ (g : ↥(ReeTag.F4.reeGamma K a)) (j : ι),
        (∀ x ∈ Subgroup.normalizer (Q : Set ↥(ReeTag.F4.reeGamma K a)),
          g⁻¹ * x * g ∈ (parabolicSubgroup Tag.F4 K (A j)).subgroupOf (ReeTag.F4.reeGamma K a)) ∧
        ∀ q ∈ Q, g⁻¹ * q * g ∈
          (parabolicRadical Tag.F4 K (A j)).subgroupOf (ReeTag.F4.reeGamma K a))
    (hNF : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a)),
      IsPGroup p R → R ≤ (MulAut.conj : ↥(ReeTag.F4.reeGamma K a) →*
        MulAut ↥(ReeTag.F4.reeGamma K a)).range → UniqueNormalFormRee a R) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a)),
      IsPGroup p R → R ≤ (MulAut.conj : ↥(ReeTag.F4.reeGamma K a) →*
        MulAut ↥(ReeTag.F4.reeGamma K a)).range →
      ∀ Q : Subgroup ↥(ReeTag.F4.reeGamma K a), OppositeFixedAt R Q :=
  oppositeFixedAt_reeGamma hK hDual A hA hstd
    (fun R => R ≤ (MulAut.conj : ↥(ReeTag.F4.reeGamma K a) →*
      MulAut ↥(ReeTag.F4.reeGamma K a)).range)
    (fun g R hR => map_conj_conj_le_range_conj g⁻¹ hR) hNF

end Cert

end CFSG.LieType.ChevTwo.Semi
