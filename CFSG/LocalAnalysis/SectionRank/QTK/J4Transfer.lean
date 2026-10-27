module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.SectionRank.QTK

open Subgroup CFSG.Assembly.LowTwoRank

section Scalars

variable {F : Type} [Field F]

theorem card_statedScalars_subgroupOf_statedSL_le [Finite F] (hF : Nat.card F = 4) :
    Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) ≤ 3 := by
  calc Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F))
      ≤ Nat.card (StatedScalars (Fin 3) F) := by
        refine Nat.card_le_card_of_injective
          (fun x => (⟨x.1.1, x.2⟩ : StatedScalars (Fin 3) F)) fun x y h => ?_
        have h' : x.1.1 = y.1.1 :=
          congrArg (fun z : StatedScalars (Fin 3) F => (z : GL (Fin 3) F)) h
        exact Subtype.ext (Subtype.ext h')
    _ ≤ Nat.card Fˣ := Nat.card_le_card_of_surjective _
        (Matrix.GeneralLinearGroup.scalar (Fin 3)).rangeRestrict_surjective
    _ = 3 := by rw [Nat.card_units, hF]

theorem mem_statedScalars_of_mem_center {n : ℕ} {x : ↥(StatedSL n F)}
    (hx : x ∈ center ↥(StatedSL n F)) :
    x ∈ (StatedScalars (Fin n) F).subgroupOf (StatedSL n F) := by
  rw [← map_center_eq_statedScalars n F]
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL n F).surjective x
  rw [mem_center_iff] at hx
  refine ⟨A, mem_center_iff.mpr fun B => ?_, rfl⟩
  apply (specialLinearGroupEquivStatedSL n F).injective
  simpa only [map_mul] using hx (specialLinearGroupEquivStatedSL n F B)

end Scalars

theorem commutator_map_ne_bot {A S : Type*} [Group A] [Group S]
    (hA : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤) (f : A →* S) (hker : f.ker ≤ center A)
    {O : Subgroup A} (hO : ⁅O, (⊤ : Subgroup A)⁆ ≠ ⊥) :
    ⁅O.map f, f.range⁆ ≠ ⊥ := by
  intro h
  apply hO
  have h1 : ⁅O, (⊤ : Subgroup A)⁆ ≤ f.ker := by
    rw [← Subgroup.map_eq_bot_iff, map_commutator, ← MonoidHom.range_eq_map]
    exact h
  have h2 : ⁅⁅O, (⊤ : Subgroup A)⁆, (⊤ : Subgroup A)⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y _
    exact mem_center_iff.mp (hker (h1 hx)) y
  have h3 : ⁅⁅(⊤ : Subgroup A), O⁆, (⊤ : Subgroup A)⁆ = ⊥ := by
    rw [commutator_comm (⊤ : Subgroup A) O]
    exact h2
  have h4 := commutator_commutator_eq_bot_of_rotate h3 h2
  rw [hA, commutator_comm] at h4
  exact h4

section PSL

variable {A : Type} [Group A] {F : Type} [Field F] [Finite F]

theorem isPSL_three_two_two_of_central (O : Subgroup A) [O.Normal] (hO : IsPGroup 2 O)
    (e₀ : A ⧸ O ≃* ↥(StatedSL 3 F)) (hF : Nat.card F = 4) (C : Subgroup A) [C.Normal]
    (hC : C ≤ center A) (X : Subgroup A) (hX3 : Nat.card X = 3) (hXC : X ≤ C) :
    CFSG.Quasithin.IsPSL 3 2 2 ((A ⧸ C) ⧸ O.map (QuotientGroup.mk' C)) := by
  set T := (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) with hT
  set g : A →* ↥(StatedSL 3 F) := e₀.toMonoidHom.comp (QuotientGroup.mk' O) with hg
  set ψ : A →* StatedProj (StatedSL 3 F) := (QuotientGroup.mk' T).comp g with hψ
  have hgs : Function.Surjective g := e₀.surjective.comp (QuotientGroup.mk'_surjective O)
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective T).comp hgs
  have hcen : ∀ a ∈ center A, g a ∈ T := fun a ha => mem_statedScalars_of_mem_center
    (mem_center_iff.mpr fun y => by
      obtain ⟨b, rfl⟩ := hgs y
      rw [← map_mul, ← map_mul, mem_center_iff.mp ha b])
  have hXle : X.map g ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcen x (hC (hXC hx))
  have hXne : X.map g ≠ ⊥ := by
    obtain ⟨x, hxX, hx1⟩ : ∃ x ∈ X, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : X = ⊥ := (Subgroup.eq_bot_iff_forall X).2 hcon
      rw [hbot, Subgroup.card_bot] at hX3
      omega
    intro hbot
    have hgx : g x = 1 := by
      have hmem : g x ∈ X.map g := ⟨x, hxX, rfl⟩
      rw [hbot] at hmem
      exact hmem
    have hxO : x ∈ O := by
      have h1 : QuotientGroup.mk' O x = 1 := e₀.injective (by rw [map_one]; exact hgx)
      exact (QuotientGroup.eq_one_iff x).mp h1
    obtain ⟨k, hk⟩ := hO ⟨x, hxO⟩
    have h3 : x ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥X) (x := ⟨x, hxX⟩)
      rw [hX3] at this
      simpa using congrArg Subtype.val this
    have h2k : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hord : orderOf x ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2k)
    have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact hx1 hord
  have hXT : X.map g = T := by
    refine Subgroup.eq_of_le_of_card_ge hXle ?_
    have hdvd : Nat.card (X.map g) ∣ 3 := by
      have h := Subgroup.card_map_dvd X g
      rwa [hX3] at h
    have hne1 : Nat.card (X.map g) ≠ 1 := fun h => hXne (Subgroup.card_eq_one.mp h)
    have h3 : Nat.card (X.map g) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    rw [h3]
    exact card_statedScalars_subgroupOf_statedSL_le hF
  have hker : ψ.ker = O ⊔ C := by
    apply le_antisymm
    · intro a ha
      have hgaT : g a ∈ T := (QuotientGroup.eq_one_iff (g a)).mp ha
      rw [← hXT] at hgaT
      obtain ⟨y, hyX, hy⟩ := hgaT
      have hay : a * y⁻¹ ∈ O := by
        have h1 : g (a * y⁻¹) = 1 := by rw [map_mul, map_inv, ← hy, mul_inv_cancel]
        have h2 : QuotientGroup.mk' O (a * y⁻¹) = 1 := e₀.injective (by rw [map_one]; exact h1)
        exact (QuotientGroup.eq_one_iff _).mp h2
      have hya : a = (a * y⁻¹) * y := by group
      rw [hya]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hay) (Subgroup.mem_sup_right (hXC hyX))
    · refine sup_le (fun o ho => ?_) (fun c hc => ?_)
      · rw [MonoidHom.mem_ker]
        change QuotientGroup.mk' T (e₀ (QuotientGroup.mk' O o)) = 1
        have hoO : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
        rw [hoO, map_one, map_one]
      · rw [MonoidHom.mem_ker]
        exact (QuotientGroup.eq_one_iff _).mpr (hcen c (hC hc))
  have hmapC : (O ⊔ C).map (QuotientGroup.mk' C) = O.map (QuotientGroup.mk' C) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  let e₁ : (A ⧸ C) ⧸ O.map (QuotientGroup.mk' C) ≃* A ⧸ (O ⊔ C) :=
    (QuotientGroup.quotientMulEquivOfEq hmapC.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient C (O ⊔ C) le_sup_right)
  let e₂ : A ⧸ (O ⊔ C) ≃* StatedProj (StatedSL 3 F) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, ?_, ?_⟩, F, inferInstance, inferInstance,
    by rw [hF]; norm_num, ⟨e₁.trans e₂⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega

end PSL

end CFSG.SectionRank.QTK
