module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2c0
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem abelian_of_rho_inv (Q V B : Subgroup G) (rho : G) (hVB : V ≤ B) (hBQ : B ≤ Q)
    (hVcard : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1)
    (hVc : ∀ v ∈ V, ∀ q ∈ Q, v * q = q * v)
    (hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ V) (hQs : ∀ a ∈ Q, a * a ∈ V)
    (hρ3 : rho * rho * rho = 1) (hρQ : ∀ q ∈ Q, rho * q * rho⁻¹ ∈ Q)
    (hρV : ∀ v ∈ V, rho * v * rho⁻¹ ∈ V) (hfix : ∀ q ∈ Q, rho * q = q * rho → q = 1)
    (hρB : ∀ b ∈ B, rho * b * rho⁻¹ ∈ B) (hB : Nat.card B = 16) :
    ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
  classical
  haveI : Finite V := Finite.of_injective (Subtype.val : V → G) Subtype.val_injective
  have hVQ : V ≤ Q := hVB.trans hBQ
  let φ : MulAut G := MulAut.conj rho
  have hφ_apply : ∀ x : G, φ x = rho * x * rho⁻¹ := fun x => MulAut.conj_apply rho x
  have hρ3' : rho ^ 3 = 1 := by rw [pow_three']; exact hρ3
  have hφ3 : φ ^ 3 = 1 := by
    have h := map_pow (MulAut.conj (G := G)) rho 3
    rw [hρ3', map_one] at h
    simpa [φ] using h.symm
  have hφφφ : ∀ x : G, φ (φ (φ x)) = x := by
    intro x
    have hx : (φ ^ 3) x = x := by rw [hφ3]; rfl
    change φ (φ (φ x)) = x at hx
    exact hx
  have hφQ : ∀ q ∈ Q, φ q ∈ Q := fun q hq => by rw [hφ_apply]; exact hρQ q hq
  have hφV : ∀ v ∈ V, φ v ∈ V := fun v hv => by rw [hφ_apply]; exact hρV v hv
  have hφB : ∀ b ∈ B, φ b ∈ B := fun b hb => by rw [hφ_apply]; exact hρB b hb
  have hH2 : ∀ b ∈ Q, b ∉ V → φ b * b⁻¹ ∉ V := fun b hbQ hbV => by
    rw [hφ_apply]
    exact rho_conj_mul_inv_not_mem Q V rho hVQ hVsq hρV hfix hbQ hbV
  obtain ⟨u, huB, huV⟩ : ∃ u ∈ B, u ∉ V := by
    by_contra h
    rw [not_exists] at h
    have hBV : B ≤ V := fun u hu => by
      by_contra huV
      exact h u ⟨hu, huV⟩
    have := Subgroup.card_le_of_le (H := B) (K := V) hBV
    rw [hB, hVcard] at this
    exact absurd this (by decide)
  have huQ : u ∈ Q := hBQ huB
  let u₁ : G := φ u
  let u₂ : G := φ u₁
  have hu₁B : u₁ ∈ B := hφB u huB
  have hu₁Q : u₁ ∈ Q := hφQ u huQ
  have hu₂B : u₂ ∈ B := hφB u₁ hu₁B
  have hφu₂ : φ u₂ = u := by
    change φ (φ u₁) = u
    exact hφφφ u
  have hu₁V : u₁ ∉ V := by
    intro h
    exact huV (hφu₂ ▸ hφV u₂ (hφV u₁ h))
  have hu₂V : u₂ ∉ V := by
    intro h
    exact huV (hφu₂ ▸ hφV u₂ h)
  have hnorm : ∀ q ∈ Q, ∀ v ∈ V, q * v * q⁻¹ ∈ V := by
    intro q hq v hv
    have h : q * v * q⁻¹ = v := by
      rw [← hVc v hv q hq, mul_assoc, mul_inv_cancel, mul_one]
    rw [h]
    exact hv
  have hnorm_rev : ∀ q ∈ Q, ∀ v : G, q * v * q⁻¹ ∈ V → v ∈ V := by
    intro q hq v hv
    have h := hnorm q⁻¹ (Q.inv_mem hq) (q * v * q⁻¹) hv
    have hq' : q⁻¹ * (q * v * q⁻¹) * (q⁻¹)⁻¹ = v := by group
    rwa [hq'] at h
  have hu₁_not_uV : ¬ ∃ v ∈ V, u₁ = u * v := by
    rintro ⟨v, hv, hv_eq⟩
    apply hH2 u huQ huV
    have h1 : u₁ * u⁻¹ = v := by
      calc u₁ * u⁻¹ = (u * v) * u⁻¹ := by rw [hv_eq]
        _ = u * (v * u⁻¹) := by rw [mul_assoc]
        _ = u * (u⁻¹ * v) := by rw [Commute.inv_right (hVc v hv u huQ)]
        _ = v := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    exact h1.symm ▸ hv
  have hu₂_not_u₁V : ¬ ∃ v ∈ V, u₂ = u₁ * v := by
    rintro ⟨v, hv, hv_eq⟩
    apply hH2 u₁ hu₁Q hu₁V
    have h1 : u₂ * u₁⁻¹ = v := by
      calc u₂ * u₁⁻¹ = (u₁ * v) * u₁⁻¹ := by rw [hv_eq]
        _ = u₁ * (v * u₁⁻¹) := by rw [mul_assoc]
        _ = u₁ * (u₁⁻¹ * v) := by rw [Commute.inv_right (hVc v hv u₁ hu₁Q)]
        _ = v := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    exact h1.symm ▸ hv
  have hu₂_not_uV : ¬ ∃ v ∈ V, u₂ = u * v := by
    rintro ⟨v, hv, hv_eq⟩
    apply hu₁_not_uV
    refine ⟨(φ v)⁻¹, V.inv_mem (hφV v hv), ?_⟩
    have h1 : u = φ u * φ v := by
      have := congrArg φ hv_eq
      rw [hφu₂, map_mul] at this
      exact this
    have h2 : u₁ = u * (φ v)⁻¹ := by
      have := congrArg (fun t => t * (φ v)⁻¹) h1
      rw [mul_assoc, mul_inv_cancel, mul_one] at this
      exact this.symm
    exact h2
  let p : Fin 4 → G := ![1, u, u₁, u * u₁]
  have hpB : ∀ i, p i ∈ B := by
    intro i
    fin_cases i
    exacts [B.one_mem, huB, hu₁B, B.mul_mem huB hu₁B]
  have hu₁Vinv : u₁⁻¹ ∉ V := fun h => hu₁V (by simpa using V.inv_mem h)
  have huu₁V : u * u₁ ∉ V := by
    intro h
    have hu_inv : u⁻¹ = u * (u * u)⁻¹ := by
      rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
    refine hu₁_not_uV ⟨(u * u)⁻¹ * (u * u₁), V.mul_mem (V.inv_mem (hQs u huQ)) h, ?_⟩
    calc u₁ = u⁻¹ * (u * u₁) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = u * ((u * u)⁻¹ * (u * u₁)) := by rw [hu_inv, mul_assoc]
  have huVinv : u⁻¹ ∉ V := fun h => huV (by simpa using V.inv_mem h)
  have huu₁Vinv : (u * u₁)⁻¹ ∉ V := fun h => huu₁V (by simpa using V.inv_mem h)
  have hu_inv_u₁ : u⁻¹ * u₁ ∉ V := by
    intro h
    exact hu₁_not_uV ⟨u⁻¹ * u₁, h, (mul_inv_cancel_left u u₁).symm⟩
  have hu₁_inv_u : u₁⁻¹ * u ∉ V := by
    intro h
    exact hu_inv_u₁ (by simpa [mul_inv_rev] using V.inv_mem h)
  have hu_inv_uu₁ : u⁻¹ * (u * u₁) ∉ V := by
    rw [show u⁻¹ * (u * u₁) = u₁ from by group]
    exact hu₁V
  have hu₁_inv_uu₁ : u₁⁻¹ * (u * u₁) ∉ V := by
    intro h
    refine huV (hnorm_rev u₁⁻¹ (Q.inv_mem hu₁Q) u ?_)
    rw [show u₁⁻¹ * u * (u₁⁻¹)⁻¹ = u₁⁻¹ * (u * u₁) from by group]
    exact h
  have huu₁_inv_u : (u * u₁)⁻¹ * u ∉ V := by
    intro h
    refine hu₁Vinv ?_
    rw [show u₁⁻¹ = (u * u₁)⁻¹ * u from by group]
    exact h
  have huu₁_inv_u₁ : (u * u₁)⁻¹ * u₁ ∉ V := by
    intro h
    refine huV ?_
    have h2 : u⁻¹ ∈ V := hnorm_rev u₁⁻¹ (Q.inv_mem hu₁Q) u⁻¹ ?_
    · simpa using V.inv_mem h2
    · rw [show u₁⁻¹ * u⁻¹ * (u₁⁻¹)⁻¹ = (u * u₁)⁻¹ * u₁ from by group]
      exact h
  have hp_sep : ∀ i j : Fin 4, (p i)⁻¹ * (p j) ∈ V → i = j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      exact huV (by simpa [p] using hij)
    · exfalso
      exact hu₁V (by simpa [p] using hij)
    · exfalso
      exact huu₁V (by simpa [p] using hij)
    · exfalso
      exact huVinv (by simpa [p] using hij)
    · rfl
    · exfalso
      exact hu_inv_u₁ (by simpa [p] using hij)
    · exfalso
      exact hu_inv_uu₁ (by simpa [p] using hij)
    · exfalso
      exact hu₁Vinv (by simpa [p] using hij)
    · exfalso
      exact hu₁_inv_u (by simpa [p] using hij)
    · rfl
    · exfalso
      exact hu₁_inv_uu₁ (by simpa [p] using hij)
    · exfalso
      exact huu₁Vinv (by simpa [p] using hij)
    · exfalso
      exact huu₁_inv_u (by simpa [p] using hij)
    · exfalso
      exact huu₁_inv_u₁ (by simpa [p] using hij)
    · rfl
  let g : Fin 4 × V → G := fun x => p x.1 * (x.2 : G)
  have hg_inj : Function.Injective g := by
    rintro ⟨i, v⟩ ⟨j, w⟩ heq
    have hval : p i * (v : G) = p j * (w : G) := heq
    have hmem : (p i)⁻¹ * (p j) ∈ V := by
      have h1 : ((p i)⁻¹ * (p j)) * (w : G) = (v : G) := by
        have this := congrArg (fun x => (p i)⁻¹ * x) hval
        rw [inv_mul_cancel_left] at this
        rw [mul_assoc]
        exact this.symm
      have h2 : (p i)⁻¹ * (p j) = (v : G) * (w : G)⁻¹ := by
        rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
      rw [h2]
      exact V.mul_mem v.2 (V.inv_mem w.2)
    have hij : i = j := hp_sep i j hmem
    have hvw : v = w := by
      apply Subtype.ext
      rw [hij] at hval
      exact mul_left_cancel hval
    exact Prod.ext hij hvw
  have hrange_ncard : (Set.range g).ncard = 16 := by
    rw [Set.ncard_range_of_injective hg_inj, Nat.card_prod, Nat.card_fin, hVcard]
  have hrange_sub : Set.range g ⊆ (B : Set G) := by
    rintro x ⟨⟨i, v⟩, rfl⟩
    exact B.mul_mem (hpB i) (hVB v.2)
  have hBrange : Set.range g = (B : Set G) := by
    apply Set.eq_of_subset_of_ncard_le hrange_sub
    rw [hrange_ncard, ← Nat.card_coe_set_eq (B : Set G)]
    exact hB.le
  have hu₂_uu₁V : ∃ w ∈ V, u₂ = (u * u₁) * w := by
    have hu₂_range : u₂ ∈ Set.range g := by
      rw [hBrange]
      exact hu₂B
    obtain ⟨⟨i, v⟩, hv⟩ := hu₂_range
    rw [show g (i, v) = p i * (v : G) from rfl] at hv
    fin_cases i
    · exfalso
      apply hu₂V
      rw [← hv]
      simpa [p] using v.2
    · exfalso
      apply hu₂_not_uV
      exact ⟨v, v.2, by
        rw [← hv]
        simp [p]⟩
    · exfalso
      apply hu₂_not_u₁V
      exact ⟨v, v.2, by
        rw [← hv]
        simp [p]⟩
    · exact ⟨v, v.2, by
        rw [← hv]
        simp [p]⟩
  have hcomm_uu₁ : u * u₁ = u₁ * u := by
    have hcomV : ⁅u, u₁⁆ ∈ V := hQc u huQ u₁ hu₁Q
    have hcom_inv : ⁅u, u₁⁆⁻¹ = ⁅u, u₁⁆ :=
      inv_eq_of_mul_eq_one_right (hVsq ⁅u, u₁⁆ hcomV)
    have hφcom : φ ⁅u, u₁⁆ = ⁅u, u₁⁆ := by
      have h1 : φ ⁅u, u₁⁆ = ⁅u₁, u₂⁆ := by
        simp only [commutatorElement_def, map_mul, map_inv]
        rfl
      obtain ⟨w, hwV, hweq⟩ := hu₂_uu₁V
      rw [h1, hweq]
      calc ⁅u₁, (u * u₁) * w⁆
          = ⁅u₁, u * u₁⁆ * (u * u₁) * ⁅u₁, w⁆ * (u * u₁)⁻¹ :=
            commutatorElement_mul_right_eq_mul_conj u₁ (u * u₁) w
        _ = ⁅u₁, u⁆ * (u * u₁) * 1 * (u * u₁)⁻¹ := by
              rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_self,
                Commute.commutator_eq (hVc w hwV u₁ hu₁Q).symm]
              group
        _ = ⁅u₁, u⁆ := by group
        _ = ⁅u, u₁⁆ := by
              rw [← commutatorElement_inv, hcom_inv]
    have hfixeq : rho * ⁅u, u₁⁆ = ⁅u, u₁⁆ * rho := by
      have h := congrArg (fun t => t * rho) hφcom
      rw [hφ_apply] at h
      simpa [mul_assoc] using h
    have hcom1 : ⁅u, u₁⁆ = 1 := hfix ⁅u, u₁⁆ (hVQ hcomV) hfixeq
    exact commutatorElement_eq_one_iff_mul_comm.mp hcom1
  let A : Subgroup G := closure ((V : Set G) ∪ ({u, u₁} : Set G))
  have hA_le_B : A ≤ B := by
    change closure ((V : Set G) ∪ ({u, u₁} : Set G)) ≤ B
    rw [closure_le]
    intro x hx
    rw [Set.mem_union] at hx
    rcases hx with hx | hx
    · exact hVB hx
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact huB
      · exact hu₁B
  have hpair : Set.Pairwise ((V : Set G) ∪ ({u, u₁} : Set G)) Commute := by
    intro a ha b hb _
    rw [Set.mem_union] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hVc a ha b (hVQ hb)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with hb | hb
      · rw [hb]; exact hVc a ha u huQ
      · rw [hb]; exact hVc a ha u₁ hu₁Q
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with ha | ha
      · rw [ha]; exact (hVc b hb u huQ).symm
      · rw [ha]; exact (hVc b hb u₁ hu₁Q).symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [ha, hb]
      · rw [ha, hb]; exact hcomm_uu₁
      · rw [ha, hb]; exact hcomm_uu₁.symm
      · rw [ha, hb]
  have hAcomm : IsMulCommutative A := Subgroup.isMulCommutative_closure hpair
  have hpA : ∀ i, p i ∈ A := by
    intro i
    have huA : u ∈ A := subset_closure (Or.inr (Set.mem_insert _ _))
    have hu₁A : u₁ ∈ A := subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
    fin_cases i
    exacts [A.one_mem, huA, hu₁A, A.mul_mem huA hu₁A]
  have hrange_sub_A : Set.range g ⊆ (A : Set G) := by
    rintro x ⟨⟨i, v⟩, rfl⟩
    exact A.mul_mem (hpA i) (subset_closure (Or.inl v.2))
  have hBA : B ≤ A := by
    intro x hx
    exact hrange_sub_A (by rw [hBrange]; exact hx)
  intro a ha b hb
  have haA : a ∈ A := hBA ha
  have hbA : b ∈ A := hBA hb
  haveI : IsMulCommutative A := hAcomm
  have hcommA : (⟨a, haA⟩ : A) * ⟨b, hbA⟩ = (⟨b, hbA⟩ : A) * ⟨a, haA⟩ :=
    hAcomm.is_comm.comm (⟨a, haA⟩ : A) (⟨b, hbA⟩ : A)
  simpa using congrArg Subtype.val hcommA

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
