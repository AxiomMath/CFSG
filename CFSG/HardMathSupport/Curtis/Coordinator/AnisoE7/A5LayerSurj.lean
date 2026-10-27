module

public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.LieType.SeitzGeneration.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

section Factor

theorem exists_factor_of_surj {A B C : Type*} [Group A] [Group B] [Group C] (π : A →* B)
    (hπ : Function.Surjective π) (τ : A →* C) (hτ : Function.Surjective τ)
    (hker : π.ker ≤ τ.ker) (hcent : ∀ z ∈ τ.ker, ∀ a : A, z * a = a * z) :
    ∃ ρ : B →* C, Function.Surjective ρ ∧ (∀ z ∈ ρ.ker, ∀ u : B, z * u = u * z) ∧
      Nat.card ρ.ker ∣ Nat.card τ.ker := by
  classical
  let ρ : B →* C := π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
    ⟨τ, hker⟩
  have hρπ : ∀ a, ρ (π a) = τ a := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply π _ (Function.rightInverse_surjInv hπ) ⟨τ, hker⟩ a
  have hker' : ∀ z ∈ ρ.ker, ∃ a ∈ τ.ker, π a = z := by
    intro z hz
    obtain ⟨a, rfl⟩ := hπ z
    exact ⟨a, by rw [MonoidHom.mem_ker, ← hρπ]; exact hz, rfl⟩
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨a, rfl⟩ := hτ c
    exact ⟨π a, hρπ a⟩
  · intro z hz u
    obtain ⟨a, ha, rfl⟩ := hker' z hz
    obtain ⟨a', rfl⟩ := hπ u
    rw [← map_mul, ← map_mul, hcent a ha a']
  · let g : τ.ker →* ρ.ker := (π.comp τ.ker.subtype).codRestrict ρ.ker fun z => by
      rw [MonoidHom.comp_apply, MonoidHom.mem_ker, Subgroup.coe_subtype, hρπ]
      exact z.2
    refine Subgroup.card_dvd_of_surjective (f := g) ?_
    intro z
    obtain ⟨a, ha, h⟩ := hker' z z.2
    exact ⟨⟨a, ha⟩, Subtype.ext h⟩

end Factor

section Cat

open CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank

theorem exists_catEquiv_statedProj {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) {ℓ f : ℕ} [Fact ℓ.Prime]
    (hqp : q.p = ℓ) (hqe : q.exponent = f) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = (ℓ ^ f) ^ 2) :
    Nonempty (Cat ⟨.twistedA 5 q, hv⟩ ≃* StatedProj (StatedSU 6 (ℓ ^ f) F)) := by
  have hf : f ≠ 0 := hqe ▸ q.exponent_pos.ne'
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 5 q, hv⟩ = ℓ := by
    simpa [TauCeti.ValidLieTypeIndex.characteristic] using hqp
  have he : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 q, hv⟩ = f := by
    simpa [TauCeti.ValidLieTypeIndex.fieldExponent] using hqe
  have key : ∀ (c e : ℕ) [Fact c.Prime], c = ℓ → e = f →
      (Cat ⟨.twistedA 5 q, hv⟩ ≃* StatedProj (StatedSU 6 (c ^ e) (GaloisField c (2 * e)))) →
      Nonempty (Cat ⟨.twistedA 5 q, hv⟩ ≃* StatedProj (StatedSU 6 (ℓ ^ f) F)) := by
    intro c e _ hc he E0
    subst hc
    subst he
    have hG : Nat.card (GaloisField c (2 * e)) = (c ^ e) ^ 2 := by
      rw [GaloisField.card c (2 * e) (by omega), ← pow_mul, mul_comm]
    have : Finite (GaloisField c (2 * e)) :=
      Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero 2 (pow_ne_zero e (Fact.out : c.Prime).ne_zero))
    letI : Fintype F := Fintype.ofFinite F
    letI : Fintype (GaloisField c (2 * e)) := Fintype.ofFinite _
    let ε : GaloisField c (2 * e) ≃+* F := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hG, hF])
    exact ⟨E0.trans (CFSG.Quasithin.Vol2.Ch11.SecS.OE5.statedProjSUEquiv ε 6 (c ^ e))⟩
  exact key _ _ hc he (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 q hv)

end Cat

section FixSU

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.LieType.SeitzGeneration
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem exists_surj_fix_unitary_six {Ω : Type} [Field Ω] {ℓ f : ℕ} {k : Type} [Field k]
    [Algebra k Ω] (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f) [IsAlgClosure k Ω]
    (π : Equiv.Perm (Fin 6)) (Φ : SL(6, Ω) ≃* SL(6, Ω)) (b : Fin 6 → Fin 6 → Ωˣ)
    (hΦ : ∀ (i j : Fin 6) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(6, Ω)) :
        Matrix (Fin 6) (Fin 6) Ω) = 1 + single (π j) (π i) ((b i j : Ω) * t ^ ℓ ^ f))
    {q : TauCeti.PrimePower} (hqp : q.p = ℓ) (hqe : q.exponent = f)
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) :
    Finite (fixSubgroup Φ) ∧ CFSG.IsQuasisimple (fixSubgroup Φ) ∧
      ∃ τ : fixSubgroup Φ →* Cat ⟨.twistedA 5 q, hv⟩, Function.Surjective τ ∧
        (∀ x, τ x = 1 ↔ x ∈ Subgroup.center (fixSubgroup Φ)) ∧
        Nat.card (Subgroup.center (fixSubgroup Φ)) ∣ 6 := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hne : ((6 : ℕ), ℓ ^ f) ≠ (3, 2) := fun h => absurd (congrArg Prod.fst h) (by norm_num)
  obtain ⟨-, ⟨H, hH⟩, hfin, hmain, -⟩ :=
    sln_root_permuting_frobenius_fixed_unitary hℓ hf hk (by norm_num : 3 ≤ 6) π Φ b hΦ
  obtain ⟨hquasi, hcenterchar, hcentercard⟩ := hmain hne
  set F : Subfield Ω := (iterateFrobenius Ω ℓ (2 * f)).eqLocusField (RingHom.id Ω) with hFdef
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hF2 : ∀ c : Ω, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hF : ∀ c : Ω, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hFcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  set Hs : SL(6, Ω) := H with hHs
  let Ψ : StatedSU 6 (ℓ ^ f) F →* SL(6, Ω) := statedSUToSL F 6 (ℓ ^ f)
  let θ : StatedSU 6 (ℓ ^ f) F →* SL(6, Ω) := (MulAut.conj Hs).toMonoidHom.comp Ψ
  have hθ : ∀ Y, θ Y = Hs * Ψ Y * Hs⁻¹ := fun Y => rfl
  have hθmem : ∀ Y, θ Y ∈ fixSubgroup Φ := by
    intro Y
    rw [hH, hθ]
    refine ⟨Matrix.SpecialLinearGroup.toGL (Ψ Y),
      (mem_range_statedSUToSL_iff hℓ F hF hFcard (by omega) _).mp ⟨Y, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hθsurj : ∀ X ∈ fixSubgroup Φ, ∃ Y, θ Y = X := by
    intro X hX
    obtain ⟨Y', hY', hXY⟩ := (hH X).mp hX
    have hW : Matrix.SpecialLinearGroup.toGL (Hs⁻¹ * X * Hs) = Y' := by
      rw [map_mul, map_mul, map_inv, hXY]
      group
    obtain ⟨Y, hY⟩ := (mem_range_statedSUToSL_iff hℓ F hF hFcard (by omega) _).mpr (hW ▸ hY')
    refine ⟨Y, ?_⟩
    rw [hθ, show Ψ Y = Hs⁻¹ * X * Hs from hY]
    group
  let e : StatedSU 6 (ℓ ^ f) F ≃* fixSubgroup Φ := MulEquiv.ofBijective (θ.codRestrict _ hθmem)
    ⟨fun Y Z h => statedSUToSL_injective F 6 (ℓ ^ f)
      ((MulAut.conj Hs).injective (congrArg Subtype.val h)), fun X => by
        obtain ⟨Y, hY⟩ := hθsurj X X.2
        exact ⟨Y, Subtype.ext hY⟩⟩
  obtain ⟨hQ, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU
    (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hFcard (by norm_num : 3 ≤ 6) hne)
    (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F ℓ f hFcard 6
      (by norm_num : 3 ≤ 6) hne)
  obtain ⟨E1⟩ := exists_catEquiv_statedProj hv hqp hqe F hFcard
  let P1 : StatedSU 6 (ℓ ^ f) F →* StatedProj (StatedSU 6 (ℓ ^ f) F) := QuotientGroup.mk' _
  let τ : fixSubgroup Φ →* Cat ⟨.twistedA 5 q, hv⟩ :=
    E1.symm.toMonoidHom.comp (P1.comp e.symm.toMonoidHom)
  refine ⟨Finite.of_equiv _ e.toEquiv, hquasi, τ, ?_, ?_, ?_⟩
  · exact E1.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp e.symm.surjective)
  · intro x
    simp only [τ, P1, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [map_eq_one_iff _ E1.symm.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← hZ]
    exact ⟨fun h => by simpa using symm_mem_center_of_mulEquiv e.symm h,
      fun h => symm_mem_center_of_mulEquiv e h⟩
  · exact hcentercard ▸ Nat.gcd_dvd_left _ _

end FixSU

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
