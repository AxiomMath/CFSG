module

public import CFSG.HardMathSupport.Dickson.Bal207.FirstClaim
public import CFSG.HardMathSupport.Dickson.I271.Support.Action

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Dickson.I271 CFSG.LocalAnalysis.GLTheoremB

section Perfect

variable {X : Type} [Group X]

theorem commute_of_actHom_eq_one {J : Subgroup X} (hJ : commutator ↥J = ⊤) {s : X}
    (hs : s ∈ Subgroup.normalizer (J : Set X)) (h1 : actHom J ⟨s, hs⟩ = 1) :
    ∀ j ∈ J, s * j = j * s := by
  have hc : ∀ k : ↥J, (k : X) * s * (k : X)⁻¹ * s⁻¹ ∈ centreOf J := fun k =>
    comm_mem_centreOf_of_fixed J hs k (by rw [h1]; rfl)
  have hJm : ∀ k : ↥J, (k : X) * s * (k : X)⁻¹ * s⁻¹ ∈ J := fun k => centreOf_le J (hc k)
  have hZ : ∀ k : ↥J, (⟨(k : X) * s * (k : X)⁻¹ * s⁻¹, hJm k⟩ : ↥J) ∈ Subgroup.center ↥J :=
    fun k => by
      obtain ⟨_, hz⟩ := mem_centreOf.1 (hc k)
      exact hz
  have hcomm : ∀ k l : ↥J, (k : X) * ((l : X) * s * (l : X)⁻¹ * s⁻¹) =
      ((l : X) * s * (l : X)⁻¹ * s⁻¹) * (k : X) := fun k l =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 (hZ l) k)
  let φ : ↥J →* ↥(Subgroup.center ↥J) :=
    { toFun := fun k => ⟨⟨(k : X) * s * (k : X)⁻¹ * s⁻¹, hJm k⟩, hZ k⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun k l => Subtype.ext (Subtype.ext (by
        change ((k * l : ↥J) : X) * s * ((k * l : ↥J) : X)⁻¹ * s⁻¹ =
          ((k : X) * s * (k : X)⁻¹ * s⁻¹) * ((l : X) * s * (l : X)⁻¹ * s⁻¹)
        rw [Subgroup.coe_mul]
        calc (k : X) * l * s * ((k : X) * l)⁻¹ * s⁻¹ =
            (k : X) * ((l : X) * s * (l : X)⁻¹ * s⁻¹) * s * (k : X)⁻¹ * s⁻¹ := by group
          _ = ((l : X) * s * (l : X)⁻¹ * s⁻¹) * ((k : X) * s * (k : X)⁻¹ * s⁻¹) := by
            rw [hcomm k l]
            group
          _ = ((k : X) * s * (k : X)⁻¹ * s⁻¹) * ((l : X) * s * (l : X)⁻¹ * s⁻¹) :=
            (hcomm ⟨_, hJm k⟩ l).symm)) }
  have hker : commutator ↥J ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hJ] at hker
  intro j hj
  have h2 : φ ⟨j, hj⟩ = 1 := hker (Subgroup.mem_top _)
  have h3 : j * s * j⁻¹ * s⁻¹ = 1 := congrArg (fun z : ↥(Subgroup.center ↥J) => ((z : ↥J) : X)) h2
  calc s * j = (j * s * j⁻¹ * s⁻¹)⁻¹ * (j * s) := by group
    _ = j * s := by rw [h3, inv_one, one_mul]

end Perfect

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ} {X : Type} [Group X]

theorem isStronglyLocallyOneBalanced_of_omegaOne [Finite X] {J B : Subgroup X} {a : X}
    (hJ : CFSG.Open.IsQuasisimple ↥J) (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2)
    (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* primeFormP h (oneGram K n))
    {D : Subgroup (GL (Fin n) K)} (hD : IsOmegaOneTorus D)
    (hBD : ∀ A : primeFormUnitary h (oneGram K n), (A : GL (Fin n) K) ∈ D →
      ∃ (b : X) (hb : b ∈ Subgroup.normalizer (J : Set X)), b ∈ B ∧
        MulAut.congr e (actHom J ⟨b, hb⟩) = primeFormConjHom h _ A) :
    IsStronglyLocallyOneBalanced 3 B a J := by
  intro S hS hS3 hBS
  have hSN : S ≤ Subgroup.normalizer (J : Set X) := fun x hx => (le_inf_iff.1 hS).1 hx
  set ρ : ↥(Subgroup.normalizer (J : Set X)) →* MulAut (primeFormP h (oneGram K n)) :=
    (MulAut.congr e).toMonoidHom.comp (actHom J) with hρ
  set Q := (S.subgroupOf (Subgroup.normalizer (J : Set X))).map ρ with hQ
  have hQ3 : Nat.Coprime 3 (Nat.card Q) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv]
    exact hS3
  have hQbot : Q = ⊥ := by
    refine eq_bot_of_omegaOne h hℓ hf hn hne hD hQ3 ?_
    intro A hA σ hσ
    obtain ⟨b, hb, hbB, hbe⟩ := hBD A hA
    obtain ⟨x, hx, rfl⟩ := hσ
    have hbS : b ∈ Subgroup.normalizer (S : Set X) := hBS ⟨hbB, hb⟩
    refine ⟨⟨b, hb⟩ * x * ⟨b, hb⟩⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · show b * (x : X) * b⁻¹ ∈ S
      exact (Subgroup.mem_normalizer_iff.1 hbS (x : X)).1 (Subgroup.mem_subgroupOf.1 hx)
    · rw [← hbe, map_mul, map_mul, map_inv]
      rfl
  have hcomm : ∀ s ∈ S, ∀ j ∈ J, s * j = j * s := by
    intro s hs
    have h1 : ρ ⟨s, hSN hs⟩ = 1 := by
      have hmem : ρ ⟨s, hSN hs⟩ ∈ Q := ⟨⟨s, hSN hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
      rw [hQbot] at hmem
      exact hmem
    have h2 : actHom J ⟨s, hSN hs⟩ = 1 := by
      apply (MulAut.congr e).injective
      rw [map_one]
      exact h1
    exact commute_of_actHom_eq_one hJ.1 (hSN hs) h2
  have hbot : ⁅J, S⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact hcomm s hs j hj
  rw [hbot]
  exact bot_le

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
