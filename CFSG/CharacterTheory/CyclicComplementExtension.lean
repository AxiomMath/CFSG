module

public import CFSG.CharacterTheory.DirectProductCharacters
public import CFSG.CharacterTheory.OddOrderBasics.TypeIExtensionSupport
public import CFSG.CharacterTheory.Wreathed.AbelianInertiaInduction

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.CyclicComplement

open TwoRankLowerBound.Helpers CFSG.Wreathed

variable {H : Type} [Group H] (N : Subgroup H) [N.Normal] (h : H)

theorem exists_mul_zpow (hHN : N ⊔ Subgroup.zpowers h = ⊤) (x : H) :
    ∃ n ∈ N, ∃ j : ℤ, n * h ^ j = x := by
  have hx : x ∈ ((N ⊔ Subgroup.zpowers h : Subgroup H) : Set H) := by rw [hHN]; trivial
  rw [Subgroup.normal_mul] at hx
  obtain ⟨n, hn, y, hy, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨n, hn, j, rfl⟩

theorem mem_zpowers_mk (hHN : N ⊔ Subgroup.zpowers h = ⊤) (x : H ⧸ N) :
    x ∈ Subgroup.zpowers (QuotientGroup.mk' N h) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  obtain ⟨n, hn, j, rfl⟩ := exists_mul_zpow N h hHN y
  refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
  rw [map_mul, show QuotientGroup.mk' N n = 1 from (QuotientGroup.eq_one_iff n).mpr hn, one_mul,
    map_zpow]

theorem orderOf_mk (hdisj : N ⊓ Subgroup.zpowers h = ⊥) :
    orderOf (QuotientGroup.mk' N h) = orderOf h := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp (Subgroup.zpowers h).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hy
    have hmem : (y : H) ∈ N ⊓ Subgroup.zpowers h := ⟨hy, y.2⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have h1 := orderOf_injective _ hinj ⟨h, Subgroup.mem_zpowers h⟩
  rw [Subgroup.orderOf_mk] at h1
  exact h1

theorem monoidHom_ext_of_eq_at (hHN : N ⊔ Subgroup.zpowers h = ⊤) {M : Type*} [Group M]
    (η η' : H →* M) (hη : N ≤ η.ker) (hη' : N ≤ η'.ker) (hh : η h = η' h) : η = η' := by
  ext x
  obtain ⟨n, hn, j, rfl⟩ := exists_mul_zpow N h hHN x
  rw [map_mul, map_mul, MonoidHom.mem_ker.mp (hη hn), MonoidHom.mem_ker.mp (hη' hn), map_zpow,
    map_zpow, hh]

theorem exists_extension [Fintype H] (hHN : N ⊔ Subgroup.zpowers h = ⊤)
    (hdisj : N ⊓ Subgroup.zpowers h = ⊥) {θ : N → ℂ} (hθ : θ ∈ BlocksIrr N)
    (hinv : ∀ n : N, θ (MulAut.conjNormal h n) = θ n) :
    ∃ Θ ∈ BlocksIrr H, ∀ n : N, Θ n = θ n := by
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hθ
  let σ : Representation ℂ N V := ρ.comp (MulAut.conjNormal h).toMonoidHom
  have hchar : σ.character = ρ.character := by
    funext n
    exact hinv n
  obtain ⟨U, hU⟩ := CFSG.OddOrderBasics.exists_unit_intertwining_of_character_eq ρ σ hirr hchar
  have hU' : ∀ n : N, (U : Module.End ℂ V) * ρ n = ρ (MulAut.conjNormal h n) * U := hU
  have hpow : ∀ (k : ℤ) (n : N), ((U ^ k : (Module.End ℂ V)ˣ) : Module.End ℂ V) * ρ n =
      ρ (((MulAut.conjNormal h) ^ k) n) * ((U ^ k : (Module.End ℂ V)ˣ) : Module.End ℂ V) := by
    have hUinv : ∀ n : N, (((U⁻¹ : (Module.End ℂ V)ˣ)) : Module.End ℂ V) * ρ n =
        ρ ((MulAut.conjNormal h)⁻¹ n) * (((U⁻¹ : (Module.End ℂ V)ˣ)) : Module.End ℂ V) := by
      intro n
      have h1 := hU' ((MulAut.conjNormal h)⁻¹ n)
      rw [MulAut.apply_inv_self] at h1
      calc (((U⁻¹ : (Module.End ℂ V)ˣ)) : Module.End ℂ V) * ρ n
          = (((U⁻¹ : (Module.End ℂ V)ˣ)) : Module.End ℂ V) * (ρ n * U) *
              (((U⁻¹ : (Module.End ℂ V)ˣ)) : Module.End ℂ V) := by
            rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
        _ = (((U⁻¹ : (Module.End ℂ V)ˣ)) : Module.End ℂ V) *
              ((U : Module.End ℂ V) * ρ ((MulAut.conjNormal h)⁻¹ n)) *
              (((U⁻¹ : (Module.End ℂ V)ˣ)) : Module.End ℂ V) := by rw [h1]
        _ = ρ ((MulAut.conjNormal h)⁻¹ n) * (((U⁻¹ : (Module.End ℂ V)ˣ)) : Module.End ℂ V) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
    intro k
    induction k using Int.induction_on with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      rw [zpow_add_one, zpow_add_one, Units.val_mul, mul_assoc, hU', ← mul_assoc, ih,
        mul_assoc, MulAut.mul_apply]
    | pred k ih =>
      intro n
      rw [zpow_sub_one, zpow_sub_one, Units.val_mul, mul_assoc, hUinv, ← mul_assoc, ih,
        mul_assoc, MulAut.mul_apply]
  let T := Subgroup.zpowers h
  let k : T → ℤ := fun t => (Subgroup.mem_zpowers_iff.mp t.2).choose
  have hk : ∀ t : T, h ^ k t = t := fun t => (Subgroup.mem_zpowers_iff.mp t.2).choose_spec
  let Ut : T → (Module.End ℂ V)ˣ := fun t => U ^ k t
  have hUt : ∀ (t : T) (n : N), (Ut t : Module.End ℂ V) * ρ n =
      ρ (MulAut.conjNormal (t : H) n) * Ut t := by
    intro t n
    rw [← hk t, map_zpow]
    exact hpow (k t) n
  have hcomm : ∀ s t : T, (Ut s : Module.End ℂ V) * Ut t = Ut t * Ut s := by
    intro s t
    rw [← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add, add_comm]
  obtain ⟨W, hW⟩ := CFSG.OddOrderBasics.exists_hom_of_commuting_intertwiners ρ hirr T Ut hUt hcomm
  have hcompl : N.IsComplement' T := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hdisj) ?_
    rw [← Subgroup.normal_mul, hHN, Subgroup.coe_top]
  obtain ⟨ρ', hρ'⟩ := CFSG.OddOrderBasics.exists_extension_of_compatible N T hcompl ρ W hW
  have hres : ρ'.comp N.subtype = ρ := MonoidHom.ext fun n => hρ' n
  have hρ'irr : Representation.IsIrreducible (ρ'.comp N.subtype) := by rw [hres]; exact hirr
  have : IsCyclic (H ⧸ N) := ⟨⟨QuotientGroup.mk' N h, mem_zpowers_mk N h hHN⟩⟩
  have hmem := (irreducible_extension_abelian_quotient_character_twists N ρ' hρ'irr).1 1
  have htw : quotientTwist N ρ'.character 1 = ρ'.character := by
    funext x
    simp [quotientTwist]
  rw [htw] at hmem
  refine ⟨ρ'.character, hmem, fun n => ?_⟩
  rw [← hres]
  rfl

theorem cyclic_complement_invariant_character_extension [Fintype H] (m : ℕ) (hm : 1 ≤ m)
    (hord : orderOf h = m) (hHN : N ⊔ Subgroup.zpowers h = ⊤)
    (hdisj : N ⊓ Subgroup.zpowers h = ⊥) (θ : N → ℂ) (hθ : θ ∈ BlocksIrr N)
    (hinv : ∀ n : N, θ (MulAut.conjNormal h n) = θ n) :
    let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)
    (∃ Θ ∈ BlocksIrr H, ∀ n : N, Θ n = θ n) ∧
    (∀ k : ℕ, ∃! η : H →* ℂˣ, N ≤ η.ker ∧ (η h : ℂ) = ζ ^ k) ∧
    ∀ Θ ∈ BlocksIrr H, (∀ n : N, Θ n = θ n) →
      ∀ η : ℕ → H →* ℂˣ, (∀ k, N ≤ (η k).ker ∧ ((η k) h : ℂ) = ζ ^ k) →
        (∀ k < m, (fun x => Θ x * ((η k) x : ℂ)) ∈ BlocksIrr H ∧
          ∀ n : N, Θ n * ((η k) n : ℂ) = θ n) ∧
        (∀ k < m, ∀ l < m,
          (fun x => Θ x * ((η k) x : ℂ)) = (fun x => Θ x * ((η l) x : ℂ)) → k = l) ∧
        ∀ χ ∈ BlocksIrr H, (∀ n : N, χ n = θ n) →
          ∃ k < m, χ = fun x => Θ x * ((η k) x : ℂ) := by
  intro ζ
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m (by omega)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have : IsCyclic (H ⧸ N) := ⟨⟨QuotientGroup.mk' N h, mem_zpowers_mk N h hHN⟩⟩
  have hordq : orderOf (QuotientGroup.mk' N h) = m := (orderOf_mk N h hdisj).trans hord
  have hmkN : ∀ n ∈ N, QuotientGroup.mk' N n = 1 := fun n hn => (QuotientGroup.eq_one_iff n).mpr hn
  have hex : ∀ k : ℕ, ∃! η : H →* ℂˣ, N ≤ η.ker ∧ (η h : ℂ) = ζ ^ k := by
    intro k
    let u : ℂˣ := Units.mk0 (ζ ^ k) (pow_ne_zero _ hζ0)
    have hu : orderOf u ∣ orderOf (QuotientGroup.mk' N h) := by
      rw [hordq]
      apply orderOf_dvd_of_pow_eq_one
      ext
      simp only [u, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    let lam : H ⧸ N →* ℂˣ := monoidHomOfForallMemZpowers (mem_zpowers_mk N h hHN) hu
    have hlamh : lam (QuotientGroup.mk' N h) = u := monoidHomOfForallMemZpowers_apply_gen _ _
    have hker : N ≤ (lam.comp (QuotientGroup.mk' N)).ker := by
      intro n hn
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hmkN n hn, map_one]
    refine ⟨lam.comp (QuotientGroup.mk' N), ⟨hker, ?_⟩, ?_⟩
    · rw [MonoidHom.comp_apply, hlamh, Units.val_mk0]
    · rintro η' ⟨hker', hh'⟩
      refine monoidHom_ext_of_eq_at N h hHN η' _ hker' hker (Units.ext ?_)
      rw [hh', MonoidHom.comp_apply, hlamh, Units.val_mk0]
  refine ⟨exists_extension N h hHN hdisj hθ hinv, hex, ?_⟩
  intro Θ hΘ hΘN η hη
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hΘ
  have hresN : Representation.character (ρ.comp N.subtype) = θ := funext hΘN
  have hρN : Representation.IsIrreducible (ρ.comp N.subtype) := by
    apply isIrreducible_of_character_mem_blocksIrr
    rw [hresN]
    exact hθ
  obtain ⟨hirrT, hinjT, hiffT, -⟩ := irreducible_extension_abelian_quotient_character_twists N ρ hρN
  let lam : ℕ → H ⧸ N →* ℂˣ := fun k => QuotientGroup.lift N (η k) (hη k).1
  have hlam : ∀ k, quotientTwist N ρ.character (lam k) =
      fun x => ρ.character x * ((η k) x : ℂ) := by
    intro k
    funext x
    simp [quotientTwist, lam]
  refine ⟨fun k _ => ⟨?_, fun n => ?_⟩, fun k hk l hl hkl => ?_, fun χ hχ hχN => ?_⟩
  · rw [← hlam]
    exact hirrT (lam k)
  · rw [MonoidHom.mem_ker.mp ((hη k).1 n.2), Units.val_one, mul_one]
    exact hΘN n
  · rw [← hlam, ← hlam] at hkl
    have h1 := congrArg (fun lam' : H ⧸ N →* ℂˣ => ((lam' (QuotientGroup.mk' N h)) : ℂ))
      (hinjT hkl)
    simp only [lam, QuotientGroup.mk'_apply, QuotientGroup.lift_mk, (hη k).2, (hη l).2] at h1
    exact hζ.pow_inj hk hl h1
  ·
    have hpos : 0 < BlocksInnerProduct (fun n : N => χ n) (fun n : N => ρ.character n) := by
      have h1 : (fun n : N => χ n) = θ := funext hχN
      have h2 : (fun n : N => ρ.character n) = θ := funext hΘN
      rw [h1, h2, CFSG.DirectProduct.blocksInnerProduct_self_of_mem hθ]
      exact zero_lt_one
    obtain ⟨lam', rfl⟩ := (hiffT χ hχ).mp hpos
    have hroot : ((lam' (QuotientGroup.mk' N h) : ℂˣ) : ℂ) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hordq, pow_orderOf_eq_one, map_one,
        Units.val_one]
    have : NeZero m := ⟨by omega⟩
    obtain ⟨k, hk, hζk⟩ := hζ.eq_pow_of_pow_eq_one hroot
    refine ⟨k, hk, ?_⟩
    have heq : lam'.comp (QuotientGroup.mk' N) = η k := by
      refine monoidHom_ext_of_eq_at N h hHN _ _ ?_ (hη k).1 (Units.ext ?_)
      · intro n hn
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hmkN n hn, map_one]
      · rw [MonoidHom.comp_apply, (hη k).2, hζk]
    funext x
    simp only [quotientTwist]
    rw [← heq]
    rfl

end CFSG.CyclicComplement
