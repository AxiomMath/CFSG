module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

open Subgroup MulAction

section Tiling

variable {Γ : Type} {Ω : Type*} [Group Γ] [MulAction Γ Ω] [Fintype Ω]

noncomputable def orbF (A : Subgroup Γ) (q₀ : Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter fun q => ∃ a ∈ A, a • q₀ = q

theorem mem_orbF {A : Subgroup Γ} {q₀ q : Ω} : q ∈ orbF A q₀ ↔ ∃ a ∈ A, a • q₀ = q := by
  unfold orbF
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem orbF_mono {A B : Subgroup Γ} (hAB : A ≤ B) (q₀ : Ω) : orbF A q₀ ⊆ orbF B q₀ := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := mem_orbF.mp hq
  exact mem_orbF.mpr ⟨a, hAB ha, rfl⟩

theorem card_orbF (A : Subgroup Γ) (q₀ : Ω) : (orbF A q₀).card = (stabilizer Γ q₀).relIndex A := by
  have hst : stabilizer (↥A) q₀ = (stabilizer Γ q₀).subgroupOf A := by
    ext a
    simp [mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]
  have hset : ((orbF A q₀ : Finset Ω) : Set Ω) = orbit (↥A) q₀ := by
    ext q
    rw [Finset.mem_coe, mem_orbF, mem_orbit_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
  rw [relIndex, ← hst, index_stabilizer, ← hset, Set.ncard_coe_finset]

@[expose] def Tiles (A₁ A : Subgroup Γ) (q₀ : Ω) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (u : ι → Γ), ∀ (M : Type) [CommMonoid M] (f : Ω → M),
    ∏ q ∈ orbF A₁ q₀, f q = ∏ i, ∏ q ∈ orbF A q₀, f (u i • q)

theorem Tiles.refl (A : Subgroup Γ) (q₀ : Ω) : Tiles A A q₀ :=
  ⟨Unit, inferInstance, fun _ => 1, fun M _ f => by simp⟩

theorem Tiles.trans {A₂ A₁ A : Subgroup Γ} {q₀ : Ω} (h₂ : Tiles A₂ A₁ q₀) (h₁ : Tiles A₁ A q₀) :
    Tiles A₂ A q₀ := by
  obtain ⟨ι₂, _, u₂, h₂⟩ := h₂
  obtain ⟨ι₁, _, u₁, h₁⟩ := h₁
  refine ⟨ι₂ × ι₁, inferInstance, fun i => u₂ i.1 * u₁ i.2, fun M _ f => ?_⟩
  rw [h₂ M f, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i₂ _ => ?_
  rw [h₁ M (fun q => f (u₂ i₂ • q))]
  simp only [mul_smul]

theorem tiles_step [Finite Γ] {p : ℕ} [hp : Fact p.Prime] {A A₁ : Subgroup Γ} (hAA₁ : A ≤ A₁)
    (hA₁ : IsPGroup p A₁) (hidx : A.relIndex A₁ = p) (q₀ : Ω) : Tiles A₁ A q₀ := by
  classical
  by_cases hSt : A₁ ⊓ stabilizer Γ q₀ ≤ A
  ·
    letI : Fintype (↥A₁ ⧸ A.subgroupOf A₁) := Fintype.ofFinite _
    let u : ↥A₁ ⧸ A.subgroupOf A₁ → Γ := fun i => ((Quotient.out i : ↥A₁) : Γ)
    refine ⟨↥A₁ ⧸ A.subgroupOf A₁, inferInstance, u, fun M _ f => ?_⟩
    have hu : ∀ i, u i ∈ A₁ := fun i => (Quotient.out i).2
    have hU : orbF A₁ q₀ = Finset.univ.biUnion fun i => (orbF A q₀).image (u i • ·) := by
      ext q
      simp only [mem_orbF, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨a₁, ha₁, rfl⟩
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (A.subgroupOf A₁) (⟨a₁, ha₁⟩ : ↥A₁)
        have hhA : (((h : ↥A₁) : Γ)) ∈ A := h.2
        refine ⟨QuotientGroup.mk ⟨a₁, ha₁⟩, ((h : ↥A₁) : Γ)⁻¹ • q₀,
          ⟨((h : ↥A₁) : Γ)⁻¹, A.inv_mem hhA, rfl⟩, ?_⟩
        have hui : u (QuotientGroup.mk ⟨a₁, ha₁⟩) = a₁ * ((h : ↥A₁) : Γ) := by
          show (((QuotientGroup.mk (⟨a₁, ha₁⟩ : ↥A₁) : ↥A₁ ⧸ A.subgroupOf A₁).out : ↥A₁) : Γ) = _
          rw [hh]
          rfl
        rw [hui, smul_smul, mul_inv_cancel_right]
      · rintro ⟨i, _, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨u i * a, A₁.mul_mem (hu i) (hAA₁ ha), mul_smul _ _ _⟩
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (↥A₁ ⧸ A.subgroupOf A₁)))
        fun i => (orbF A q₀).image (u i • ·) := by
      intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro q hqi hqj
      simp only [Finset.mem_image, mem_orbF] at hqi hqj
      obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hqi
      obtain ⟨_, ⟨b, hb, rfl⟩, e⟩ := hqj
      apply hij
      have hst : (u j * b)⁻¹ * (u i * a) ∈ A₁ ⊓ stabilizer Γ q₀ := by
        refine Subgroup.mem_inf.mpr ⟨A₁.mul_mem (A₁.inv_mem (A₁.mul_mem (hu j) (hAA₁ hb)))
          (A₁.mul_mem (hu i) (hAA₁ ha)), ?_⟩
        rw [mem_stabilizer_iff, mul_smul, mul_smul, ← e, smul_smul, smul_smul]
        have : (u j * b)⁻¹ * u j * b = 1 := by group
        rw [this, one_smul]
      have hA' := hSt hst
      have hji : (u j)⁻¹ * u i ∈ A := by
        have : (u j)⁻¹ * u i = b * ((u j * b)⁻¹ * (u i * a)) * a⁻¹ := by group
        rw [this]
        exact A.mul_mem (A.mul_mem hb hA') (A.inv_mem ha)
      have : (QuotientGroup.mk (Quotient.out j) : ↥A₁ ⧸ A.subgroupOf A₁) =
          QuotientGroup.mk (Quotient.out i) := by
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [u] using hji
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      exact this.symm
    rw [hU, Finset.prod_biUnion hdisj]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_image (MulAction.injective (u i)).injOn]
  ·
    set St := stabilizer Γ q₀ with hStdef
    have hp0 : p ≠ 0 := hp.out.ne_zero
    have hK : A.relIndex (A₁ ⊓ St) = p := by
      have hle : A.relIndex (A₁ ⊓ St) ≤ p := by
        rw [← hidx]
        exact relIndex_le_of_le_right inf_le_left (by rw [hidx]; exact hp0)
      have hne1 : A.relIndex (A₁ ⊓ St) ≠ 1 := fun h => hSt (relIndex_eq_one.mp h)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hA₁.to_le (inf_le_left : A₁ ⊓ St ≤ A₁))
      have hdvd : A.relIndex (A₁ ⊓ St) ∣ p ^ n := hn ▸ relIndex_dvd_card _ _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
      rw [hj] at hle hne1 ⊢
      have hj1 : j ≤ 1 := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp (by rw [pow_one]; exact hle)
      have hj0 : j ≠ 0 := by rintro rfl; exact hne1 (pow_zero p)
      have : j = 1 := by omega
      rw [this, pow_one]
    have e1 := relIndex_mul_relIndex (A ⊓ St) A A₁ inf_le_left hAA₁
    have e2 := relIndex_mul_relIndex (A ⊓ St) (A₁ ⊓ St) A₁ (inf_le_inf_right _ hAA₁) inf_le_left
    rw [inf_relIndex_left, hidx] at e1
    rw [inf_relIndex_left] at e2
    have e3 : (A ⊓ St).relIndex (A₁ ⊓ St) = p := by
      have : A ⊓ St = A ⊓ (A₁ ⊓ St) := by
        rw [← inf_assoc, inf_of_le_left hAA₁]
      rw [this, inf_relIndex_right, hK]
    rw [e3] at e2
    have heqidx : St.relIndex A₁ = St.relIndex A := by
      have := e1.trans e2.symm
      rw [mul_comm] at this
      exact (Nat.eq_of_mul_eq_mul_left hp.out.pos this).symm
    have heq : orbF A q₀ = orbF A₁ q₀ :=
      Finset.eq_of_subset_of_card_le (orbF_mono hAA₁ q₀)
        (by rw [card_orbF, card_orbF, heqidx])
    refine ⟨Unit, inferInstance, fun _ => 1, fun M _ f => ?_⟩
    simp [heq]

theorem tiles_of_isPGroup [Finite Γ] {p : ℕ} [hp : Fact p.Prime] {E : Subgroup Γ}
    (hE : IsPGroup p E) (q₀ : Ω) : ∀ A : Subgroup Γ, A ≤ E → Tiles E A q₀ := by
  suffices h : ∀ n : ℕ, ∀ A : Subgroup Γ, A ≤ E → Nat.card E - Nat.card A = n → Tiles E A q₀ from
    fun A hAE => h _ A hAE rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hAE hn
  by_cases hAE' : A = E
  · subst hAE'; exact Tiles.refl A q₀
  have hlt : A < E := lt_of_le_of_ne hAE hAE'
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hE.to_le hAE)
  obtain ⟨N, hN⟩ := IsPGroup.iff_card.mp hE
  have hcardlt : Nat.card A < Nat.card E := Subgroup.card_lt_of_lt hlt
  have hmN : m < N := by
    rw [hm, hN] at hcardlt
    exact (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp hcardlt
  have hA'card : Nat.card (A.subgroupOf E) = p ^ m := by
    rw [← hm]
    exact Nat.card_congr (subgroupOfEquivOfLe hAE).toEquiv
  have hdvd : p ^ (m + 1) ∣ Nat.card ↥E := by
    rw [hN]
    exact Nat.pow_dvd_pow p (by omega)
  obtain ⟨K, hKcard, hAK⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hA'card
  set A₁ := K.map E.subtype with hA₁def
  have hAA₁ : A ≤ A₁ := fun a ha => ⟨⟨a, hAE ha⟩, hAK (by simpa [Subgroup.mem_subgroupOf] using ha), rfl⟩
  have hA₁E : A₁ ≤ E := map_subtype_le K
  have hA₁card : Nat.card A₁ = p ^ (m + 1) := by
    rw [hA₁def, Subgroup.card_map_of_injective E.subtype_injective, hKcard]
  have hidx : A.relIndex A₁ = p := by
    have h1 := relIndex_mul_card A A₁
    rw [inf_of_le_left hAA₁, hm, hA₁card, pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos m) (by rw [h1, mul_comm])
  have hcard1 : Nat.card A < Nat.card A₁ := by
    rw [hm, hA₁card]
    exact Nat.pow_lt_pow_right hp.out.one_lt (by omega)
  have hcard2 : Nat.card A₁ ≤ Nat.card E := Subgroup.card_le_of_le hA₁E
  have h₂ := ih (Nat.card E - Nat.card A₁) (by omega) A₁ hA₁E rfl
  exact h₂.trans (tiles_step hAA₁ (hE.to_le hA₁E) hidx q₀)

end Tiling

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

end
