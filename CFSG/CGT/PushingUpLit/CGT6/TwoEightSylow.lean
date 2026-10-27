module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_normalized {Γ Ā : Subgroup G} (hN : Ā ≤ Subgroup.normalizer (Γ : Set G))
    (hĀ : IsPGroup 2 Ā) :
    ∃ P : Sylow 2 Γ, ∀ a ∈ Ā, ∀ x : Γ, x ∈ P → ∃ y : Γ, y ∈ P ∧ (y : G) = a * x * a⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulDistribMulAction Ā Γ := MulDistribMulAction.compHom Γ (Subgroup.inclusion hN)
  have hcard := hĀ.card_modEq_card_fixedPoints (Sylow 2 Γ)
  have hodd : Nat.card (Sylow 2 Γ) ≡ 1 [MOD 2] := card_sylow_modEq_one 2 Γ
  have hne : (MulAction.fixedPoints Ā (Sylow 2 Γ)).Nonempty := by
    rcases (MulAction.fixedPoints Ā (Sylow 2 Γ)).eq_empty_or_nonempty with h | h
    · exfalso
      rw [h] at hcard
      have h0 : Nat.card (Sylow 2 Γ) ≡ 0 [MOD 2] := by simpa using hcard
      have := h0.symm.trans hodd
      exact absurd this (by decide)
    · exact h
  obtain ⟨P, hP⟩ := hne
  refine ⟨P, fun a ha x hx => ?_⟩
  have hfix : (⟨a, ha⟩ : Ā) • P = P := hP ⟨a, ha⟩
  have hmem : (⟨a, ha⟩ : Ā) • x ∈ (⟨a, ha⟩ : Ā) • (P : Subgroup Γ) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hx
  have hsub : ((⟨a, ha⟩ : Ā) • P : Sylow 2 Γ).toSubgroup = (⟨a, ha⟩ : Ā) • (P : Subgroup Γ) :=
    Sylow.pointwise_smul_def
  have hP' : (⟨a, ha⟩ : Ā) • (P : Subgroup Γ) = (P : Subgroup Γ) := by
    rw [← hsub, hfix]
  rw [hP'] at hmem
  exact ⟨(⟨a, ha⟩ : Ā) • x, hmem, rfl⟩

theorem exists_conj_normalizes {Γ Ā S : Subgroup G} (hN : Ā ≤ Subgroup.normalizer (Γ : Set G))
    (hĀ : IsPGroup 2 Ā) (hSΓ : S ≤ Γ) (hS2 : IsPGroup 2 S)
    (hmax : ∀ P : Subgroup G, P ≤ Γ → IsPGroup 2 P → Nat.card P ≤ Nat.card S) :
    ∃ h ∈ Γ, ∀ a ∈ Ā, ∀ s ∈ S, h⁻¹ * a * h * s * (h⁻¹ * a * h)⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_normalized hN hĀ
  have hcardS : Nat.card (S.subgroupOf Γ) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSΓ).toEquiv
  let SS : Sylow 2 Γ :=
    { toSubgroup := S.subgroupOf Γ
      isPGroup' := hS2.comap_subtype
      is_maximal' := fun {Q} hQ hle => by
        have h1 : Nat.card (Q.map Γ.subtype) ≤ Nat.card S := by
          refine hmax _ ?_ (hQ.map _)
          rintro _ ⟨x, -, rfl⟩
          exact x.2
        have h2 : Nat.card (Q.map Γ.subtype) = Nat.card Q :=
          Nat.card_congr (Q.equivMapOfInjective Γ.subtype Γ.subtype_injective).toEquiv.symm
        exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardS]; omega)).symm }
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ SS P
  refine ⟨(g : G), g.2, fun a ha s hs => ?_⟩
  have hsΓ : s ∈ Γ := hSΓ hs
  have hgsub : (P : Subgroup Γ) = MulAut.conj g • (SS : Subgroup Γ) := by
    rw [← hg]
    exact Sylow.coe_subgroup_smul
  have hmem1 : MulAut.conj g (⟨s, hsΓ⟩ : Γ) ∈ (P : Subgroup Γ) := by
    rw [hgsub]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (Subgroup.mem_subgroupOf.mpr hs)
  obtain ⟨y, hyP, hy⟩ := hP a ha _ hmem1
  have hy2 : (MulAut.conj g)⁻¹ y ∈ (SS : Subgroup Γ) := by
    have hyP' : y ∈ (P : Subgroup Γ) := hyP
    rw [hgsub] at hyP'
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hyP'
  have hy3 : ((MulAut.conj g)⁻¹ y : Γ) ∈ S.subgroupOf Γ := hy2
  have hy4 : (((MulAut.conj g)⁻¹ y : Γ) : G) ∈ S := Subgroup.mem_subgroupOf.mp hy3
  have hy5 : (((MulAut.conj g)⁻¹ y : Γ) : G) = (g : G)⁻¹ * (y : G) * (g : G) := by
    simp
  rw [hy5, hy] at hy4
  have hcg : ((MulAut.conj g (⟨s, hsΓ⟩ : Γ) : Γ) : G) = (g : G) * s * (g : G)⁻¹ := by
    simp [MulAut.conj_apply]
  rw [hcg] at hy4
  convert hy4 using 1
  group

theorem card_le_two_mul_inf_of_hom {H : Type*} [Group H] {Ā N : Subgroup G} (φ : Ā →* H)
    (hsq : ∀ a : Ā, a * a = 1)
    (huniq : ∀ x y : H, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y)
    (hker : ∀ a : Ā, φ a = 1 → (a : G) ∈ N) :
    Nat.card Ā ≤ 2 * Nat.card ↥(Ā ⊓ N) := by
  classical
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 : Nat.card (Ā ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have h3 : Nat.card φ.range ≤ 2 := by
    have hinj : Function.Injective (fun x : φ.range => decide ((x : H) = 1)) := by
      rintro ⟨x, a, rfl⟩ ⟨y, b, rfl⟩ h
      simp only [decide_eq_decide] at h
      by_cases hx : φ a = 1
      · exact Subtype.ext (show φ a = φ b by rw [hx, h.mp hx])
      · have hy : φ b ≠ 1 := fun hy => hx (h.mpr hy)
        refine Subtype.ext (show φ a = φ b from huniq _ _ ?_ ?_ hx hy)
        · rw [← map_mul, hsq a, map_one]
        · rw [← map_mul, hsq b, map_one]
    calc Nat.card φ.range ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
      _ = 2 := by simp
  have h4 : Nat.card φ.ker ≤ Nat.card ↥(Ā ⊓ N) := by
    refine Nat.card_le_card_of_injective
      (fun a : φ.ker => (⟨(a.1 : G), a.1.2, hker a.1 a.2⟩ : ↥(Ā ⊓ N))) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(Ā ⊓ N) => (z : G)) hab
  calc Nat.card Ā = Nat.card (Ā ⧸ φ.ker) * Nat.card φ.ker := h1
    _ ≤ 2 * Nat.card ↥(Ā ⊓ N) := Nat.mul_le_mul (h2 ▸ h3) h4

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
