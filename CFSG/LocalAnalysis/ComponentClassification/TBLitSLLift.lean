module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitLift

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint
open scoped commutatorElement Pointwise MatrixGroups

theorem commutatorElement_mul_center {G : Type*} [Group G] {z z' : G} (hz : z ∈ center G)
    (hz' : z' ∈ center G) (t t' : G) : ⁅t * z, t' * z'⁆ = ⁅t, t'⁆ := by
  have h1 : ∀ g : G, z * g * z⁻¹ = g := fun g => by
    rw [← mem_center_iff.mp hz g]
    group
  have h2 : ∀ g : G, z' * g * z'⁻¹ = g := fun g => by
    rw [← mem_center_iff.mp hz' g]
    group
  have e1 : ∀ b : G, ⁅t * z, b⁆ = ⁅t, b⁆ := fun b => by
    rw [commutatorElement_def, commutatorElement_def]
    calc t * z * b * (t * z)⁻¹ * b⁻¹ = t * (z * b * z⁻¹) * t⁻¹ * b⁻¹ := by group
      _ = t * b * t⁻¹ * b⁻¹ := by rw [h1]
  have e2 : ∀ a : G, ⁅a, t' * z'⁆ = ⁅a, t'⁆ := fun a => by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * (t' * z') * a⁻¹ * (t' * z')⁻¹ = a * t' * (z' * a⁻¹ * z'⁻¹) * t'⁻¹ := by group
      _ = a * t' * a⁻¹ * t'⁻¹ := by rw [h2]
  rw [e1, e2]

theorem commutator_self_le {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem exists_sl_lift (hGA : GriessMultipliersAllModels) (hGC : GriessMultipliersCentralCovers)
    {Q B : Type} [Group Q] [Group B] [Finite Q] [Finite B] (σ : Q →* B)
    (hker : σ.ker ≤ center Q) (hker2 : IsPGroup 2 σ.ker) {S : Subgroup B} (hSr : S ≤ σ.range)
    (hS : ⁅S, S⁆ = S) {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n)
    (eS : S ≃* SL(2, GaloisField p n)) :
    ⁅S.comap σ, S.comap σ⁆.map σ = S ∧ ∀ x ∈ ⁅S.comap σ, S.comap σ⁆, σ x = 1 → x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₁ := S.comap σ with hT₁
  set T := ⁅T₁, T₁⁆ with hT
  have hT₁S : T₁.map σ = S := map_comap_eq_self hSr
  have hTS : T.map σ = S := by rw [hT, map_commutator, hT₁S, hS]
  have hdec : ∀ x ∈ T₁, ∃ t ∈ T, ∃ z ∈ center Q, x = t * z := by
    intro x hx
    have hx' : σ x ∈ T.map σ := by
      rw [hTS]
      exact hx
    obtain ⟨t, ht, htx⟩ := hx'
    refine ⟨t, ht, t⁻¹ * x, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, htx, inv_mul_cancel]
  have hTT : ⁅T, T⁆ = T := by
    refine le_antisymm (commutator_self_le T) ?_
    change ⁅T₁, T₁⁆ ≤ ⁅T, T⁆
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨t, ht, z, hz, rfl⟩ := hdec x hx
    obtain ⟨t', ht', z', hz', rfl⟩ := hdec y hy
    rw [commutatorElement_mul_center hz hz']
    exact commutator_mem_commutator ht ht'
  have : Group.IsPerfect T := Subgroup.isPerfect_iff.mpr hTT
  have hφmem : ∀ x : T, σ x ∈ S := fun x => by
    rw [← hTS]
    exact mem_map_of_mem σ x.2
  let φ : T →* S := (σ.comp T.subtype).codRestrict S hφmem
  have hφ : Function.Surjective φ := by
    rintro ⟨s, hs⟩
    rw [← hTS] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨⟨t, ht⟩, rfl⟩
  have hφker : φ.ker ≤ center T := by
    intro x hx
    have h1 : σ x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : (x : Q) ∈ center Q := hker (MonoidHom.mem_ker.mpr h1)
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp h2 g)
  have hcomap := Quasisimple.center_comap_of_central_kernel φ hφ hφker
  have : Group.IsPerfect S := Subgroup.isPerfect_iff.mpr hS
  have h5 : 5 ≤ p ^ n :=
    five_le_of_isPerfect_sl hp2 hn
      (Group.IsPerfect.ofSurjective (f := eS.toMonoidHom) eS.surjective)
  have hnn : n ≠ 0 := by omega
  have h4 : 4 ≤ Nat.card (GaloisField p n) := by
    rw [GaloisField.card p n hnn]
    omega
  let ψ : T →* S ⧸ center S := (QuotientGroup.mk' _).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hψker : ψ.ker = center T := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  let eTZ : T ⧸ center T ≃* PSL(2, GaloisField p n) :=
    ((QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).trans
      (QuotientGroup.congr _ _ eS (map_center_mulEquiv eS))
  have hm : LieModel (T ⧸ center T) .PSL 2 p n := lieModel_psl_two_of_equiv_psl (by omega) eTZ
  have hSLq := isQuasisimple_sl_two h4
  have : IsSimpleGroup PSL(2, GaloisField p n) := hSLq.2.1
  have hTq : IsQuasisimple T := ⟨inferInstance, eTZ.isSimpleGroup,
    exists_ne_comm_of_mulEquiv eTZ hSLq.2.2⟩
  have hF : Odd (Nat.card (GaloisField p n)) := by
    rw [GaloisField.card p n hnn]
    exact ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).pow
  have hZS : Nat.card (center S) = 2 := by
    have h1 : Nat.card ((center S).map eS.toMonoidHom) = Nat.card (center S) :=
      card_map_of_injective (by exact eS.injective)
    rw [map_center_mulEquiv eS] at h1
    rw [← h1]
    exact ABGLocalTools.card_center_sl2 hF
  have hZ2 : IsPGroup 2 (center T) := by
    intro z
    have hz : φ z ∈ center S := map_mem_center_of_surjective hφ z.2
    have h1 : (φ z : S) ^ 2 = 1 := by
      have h2 := pow_card_eq_one' (G := center S) (x := ⟨φ z, hz⟩)
      rw [hZS] at h2
      exact congrArg Subtype.val h2
    have h3 : ((z : T) : Q) ^ 2 ∈ σ.ker := by
      rw [MonoidHom.mem_ker]
      have h4 := congrArg Subtype.val h1
      rw [Subgroup.coe_pow] at h4
      rw [map_pow]
      exact h4
    obtain ⟨k, hk⟩ := hker2 ⟨_, h3⟩
    refine ⟨k + 1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have h5 := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h5 ⊢
    rw [pow_succ', pow_mul]
    exact h5
  have hZ1 : center T ≠ ⊥ := by
    intro hbot
    have h1 : (center T).map φ = center S := by
      rw [← hcomap]
      exact map_comap_eq_self_of_surjective hφ _
    rw [hbot, Subgroup.map_bot] at h1
    rw [← h1, Subgroup.card_bot] at hZS
    omega
  obtain ⟨-, hfact, ⟨eT⟩⟩ := psl_two_double_cover hGA hGC hTq hZ2 hZ1 Fact.out hp2 hm
  have hcardT : Nat.card T = Nat.card S :=
    (Nat.card_congr eT.toEquiv).trans (Nat.card_congr eS.toEquiv).symm
  have hcardker : Nat.card φ.ker = 1 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hcardT] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.symm.trans (mul_one _).symm)
  refine ⟨hTS, fun x hx h1 => ?_⟩
  have hx : (⟨x, hx⟩ : T) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext h1
  rw [card_eq_one.mp hcardker, mem_bot] at hx
  exact congrArg Subtype.val hx

end CFSG.ComponentClassification.TBLit
