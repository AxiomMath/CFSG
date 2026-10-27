module

public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianNormalRank
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicScalarNorm

public section

open CFSG.Open CFSG.LargeEvenClassification.Helpers

namespace CFSG.ProperTwoGeneratedCore

universe u

theorem principal_involution_norm_zero (exponent : ℕ)
    (source : ZMod (2 ^ (exponent + 3))) :
    source + (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3))) * source = 0 ↔
      source + source = 0 := by
  let oddUnit : (ZMod (2 ^ (exponent + 3)))ˣ :=
    ZMod.unitOfCoprime (1 + 2 ^ (exponent + 1)) (by
      apply Nat.Coprime.pow_right
      apply Nat.coprime_two_right.mpr
      exact Odd.add_even (by decide : Odd 1)
        (Even.pow_of_ne_zero (by decide : Even 2) (by omega)))
  have hunit : (oddUnit : ZMod (2 ^ (exponent + 3))) = 1 + 2 ^ (exponent + 1) := by
    change ((1 + 2 ^ (exponent + 1) : ℕ) : ZMod (2 ^ (exponent + 3))) = _
    push_cast
    rfl
  have hnorm : source +
      (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3))) * source =
        oddUnit.val * (source + source) := by
    rw [binaryCongruenceInvolution_val, hunit,
      show (2 : ZMod (2 ^ (exponent + 3))) ^ (exponent + 2) =
        2 * 2 ^ (exponent + 1) by simp only [pow_succ']]
    ring
  rw [hnorm]
  constructor
  · intro hzero
    have hcancel := congrArg (fun entry : ZMod (2 ^ (exponent + 3)) =>
      (oddUnit⁻¹ : (ZMod (2 ^ (exponent + 3)))ˣ).val * entry) hzero
    simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] using hcancel
  · intro hzero
    rw [hzero, mul_zero]

theorem principal_involution_norm_kernel {Cyclic : Type u} [CommGroup Cyclic]
    (exponent : ℕ) (coordinates : Multiplicative (ZMod (2 ^ (exponent + 3))) ≃* Cyclic)
    (automorphism : MulAut Cyclic)
    (hscalar : (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates) automorphism =
      binaryCongruenceInvolution exponent) (source : Cyclic) :
    source * automorphism source = 1 ↔ source ^ 2 = 1 := by
  obtain ⟨original, rfl⟩ := coordinates.surjective source
  rw [cyclicScalarAutEquiv_apply, hscalar, ← map_mul, ← map_pow,
    ← coordinates.map_one, coordinates.injective.eq_iff, coordinates.injective.eq_iff]
  rw [pow_two]
  change original.toAdd +
      (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3))) * original.toAdd = 0 ↔
    original.toAdd + original.toAdd = 0
  exact principal_involution_norm_zero exponent original.toAdd

private theorem central_square_pair_four {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) (hK : IsElemAbelian 2 K) (hcardK : Nat.card K = 2)
    (y : L) (hy : y ^ 2 = 1) (hyK : y ∉ K)
    (hcomm : ∀ k : K, Commute (k : L) y) :
    ∃ V : Subgroup L, IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
      ∀ g : L, g ∈ V ↔ g ∈ K ∨ ∃ k : K, (k : L) * y = g := by
  have hyne : y ≠ 1 := fun heq => hyK (heq ▸ K.one_mem)
  have horder : orderOf y = 2 := orderOf_eq_prime_iff.mpr ⟨hy, hyne⟩
  let Y := Subgroup.zpowers y
  have hcardY : Nat.card Y = 2 := (Nat.card_zpowers y).trans horder
  have hcases : ∀ b : Y, (b : L) = 1 ∨ (b : L) = y := by
    obtain ⟨other, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp hcardY
    have hyinternal : (⟨y, Subgroup.mem_zpowers y⟩ : Y) ≠ 1 := by
      intro heq
      exact hyne (congrArg Subtype.val heq)
    have hyeq := hunique ⟨y, Subgroup.mem_zpowers y⟩ hyinternal
    intro b
    by_cases hb : b = 1
    · exact Or.inl (congrArg Subtype.val hb)
    · exact Or.inr (congrArg Subtype.val ((hunique b hb).trans hyeq.symm))
  let : IsMulCommutative K := hK.1
  let f : K × Y →* L := K.subtype.noncommCoprod Y.subtype (by
    intro k b
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.property
    change Commute (k : L) (b : L)
    rw [← hn]
    exact (hcomm k).zpow_right n)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_antisymm _ bot_le
    intro pair hpair
    have heq : (pair.1 : L) * (pair.2 : L) = 1 := hpair
    have hbK : (pair.2 : L) ∈ K := by
      have hb : (pair.2 : L) = (pair.1 : L)⁻¹ := by
        calc
          (pair.2 : L) = (pair.1 : L)⁻¹ * ((pair.1 : L) * (pair.2 : L)) := by group
          _ = (pair.1 : L)⁻¹ := by rw [heq, mul_one]
      rw [hb]
      exact K.inv_mem pair.1.property
    have hb : (pair.2 : L) = 1 := (hcases pair.2).resolve_right (by
      intro hby
      exact hyK (hby ▸ hbK))
    apply Subgroup.mem_bot.mpr
    apply Prod.ext
    · apply Subtype.ext
      change (pair.1 : L) = 1
      simpa only [hb, mul_one] using heq
    · exact Subtype.ext hb
  refine ⟨f.range, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, ?_⟩
    intro g hg
    obtain ⟨pair, rfl⟩ := hg
    have hk : pair.1 ^ 2 = 1 := Subtype.ext (hK.2 pair.1 pair.1.property)
    have hb : pair.2 ^ 2 = 1 := by
      apply Subtype.ext
      rcases hcases pair.2 with hb | hb
      · simp only [Subgroup.coe_pow, hb, one_pow, Subgroup.coe_one]
      · simpa only [Subgroup.coe_pow, hb, Subgroup.coe_one] using hy
    rw [← map_pow, Prod.pow_mk, hk, hb]
    exact f.map_one
  · have heq := Nat.card_congr (Equiv.ofBijective f.rangeRestrict
      ⟨fun a b hab => hf (congrArg Subtype.val hab), f.rangeRestrict_surjective⟩)
    rw [Nat.card_prod, hcardK, hcardY] at heq
    exact heq.symm
  · intro g
    constructor
    · rintro ⟨pair, rfl⟩
      rcases hcases pair.2 with hb | hb
      · left
        change (pair.1 : L) * (pair.2 : L) ∈ K
        simpa only [hb, mul_one] using pair.1.property
      · right
        exact ⟨pair.1, by change _ = (pair.1 : L) * (pair.2 : L); rw [hb]⟩
    · rintro (hg | ⟨k, rfl⟩)
      · exact ⟨(⟨g, hg⟩, 1), mul_one g⟩
      · exact ⟨(k, ⟨y, Subgroup.mem_zpowers y⟩), rfl⟩

theorem principal_cyclic_extension_characteristic_four {L : Type u} [Group L] [Finite L]
    (H : Subgroup L) [H.Normal] [IsCyclic H] (hindex : H.index = 2)
    (exponent : ℕ) (coordinates : Multiplicative (ZMod (2 ^ (exponent + 3))) ≃* H)
    (x : L) (hx : x ∉ H)
    (hscalar : (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates)
      (MulAut.conjNormal (H := H) x) = binaryCongruenceInvolution exponent) :
    ∃ V : Subgroup L, V.Characteristic ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
      ∀ g : L, g ∈ V ↔ g ^ 2 = 1 := by
  let : CommGroup H := IsCyclic.commGroup
  have hsquare : x ^ 2 ∈ H := H.sq_mem_of_index_two hindex x
  have hsquareFixed : (MulAut.conjNormal (H := H) x) ⟨x ^ 2, hsquare⟩ =
      ⟨x ^ 2, hsquare⟩ := by
    apply Subtype.ext
    change x * x ^ 2 * x⁻¹ = x ^ 2
    group
  have hsquareRange := cyclic_congruence_fixed_square exponent coordinates
    (MulAut.conjNormal (H := H) x) hscalar ⟨x ^ 2, hsquare⟩ hsquareFixed
  have hinverseRange := Subgroup.inv_mem (powMonoidHom 2 : H →* H).range hsquareRange
  obtain ⟨source, hnorm⟩ := cyclic_congruence_norm_surjective exponent coordinates
    (MulAut.conjNormal (H := H) x) hscalar
      ⟨(⟨x ^ 2, hsquare⟩ : H)⁻¹, hinverseRange⟩
  let y := (source : L) * x
  have hy : y ^ 2 = 1 := by
    have hnormL := congrArg (fun entry : H => (entry : L)) hnorm
    change (source : L) * (x * (source : L) * x⁻¹) = (x ^ 2)⁻¹ at hnormL
    calc
      y ^ 2 = ((source : L) * (x * (source : L) * x⁻¹)) * x ^ 2 := by
        dsimp [y]
        simp only [pow_two]
        group
      _ = 1 := by rw [hnormL, inv_mul_cancel]
  have hyH : y ∉ H := by
    intro hmem
    apply hx
    have hprod := H.mul_mem (H.inv_mem source.property) hmem
    simpa only [y, inv_mul_cancel_left] using hprod
  have hsourceAction : MulAut.conjNormal (H := H) (source : L) = 1 := by
    apply MulEquiv.ext
    intro t
    apply Subtype.ext
    change (source : L) * (t : L) * (source : L)⁻¹ = t
    rw [setLike_mul_comm source.property t.property,
      mul_assoc, mul_inv_cancel, mul_one]
  have hactionY : MulAut.conjNormal (H := H) y = MulAut.conjNormal (H := H) x := by
    change MulAut.conjNormal (H := H) ((source : L) * x) = _
    rw [map_mul, hsourceAction, one_mul]
  have hscalarY : (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates)
      (MulAut.conjNormal (H := H) y) = binaryCongruenceInvolution exponent :=
    hactionY ▸ hscalar
  let K := normalElementarySquareKernel H (inferInstance : IsMulCommutative H)
  have hK : IsElemAbelian 2 K := normalElementarySquareKernel_elementary H inferInstance
  have hKle : K ≤ H := Subgroup.map_subtype_le _
  have hKmem : ∀ g : L, g ∈ K ↔ g ∈ H ∧ g ^ 2 = 1 := by
    intro g
    constructor
    · intro hg
      exact ⟨hKle hg, hK.2 g hg⟩
    · rintro ⟨hg, hpow⟩
      exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩, Subtype.ext hpow, rfl⟩
  have hcardH : Nat.card H = 2 ^ (exponent + 3) := by
    rw [← Nat.card_congr coordinates.toEquiv]
    exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod _)
  have htwoDivides : 2 ∣ 2 ^ (exponent + 3) := by
    exact dvd_pow_self 2 (by omega)
  have hcardK : Nat.card K = 2 := by
    change Nat.card ((powMonoidHom 2 : H →* H).ker.map H.subtype) = 2
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      IsCyclic.card_powMonoidHom_ker, hcardH, Nat.gcd_eq_right htwoDivides]
  have hcomm : ∀ k : K, Commute (k : L) y := by
    intro k
    let t : H := ⟨k, hKle k.property⟩
    have ht : t ^ 2 = 1 := Subtype.ext (hK.2 k k.property)
    have hnormt := (principal_involution_norm_kernel exponent coordinates
      (MulAut.conjNormal (H := H) y) hscalarY t).mpr ht
    have hnormL := congrArg (fun entry : H => (entry : L)) hnormt
    change (k : L) * (y * (k : L) * y⁻¹) = 1 at hnormL
    have hfixed : y * (k : L) * y⁻¹ = (k : L) := by
      calc
        y * (k : L) * y⁻¹ = (k : L)⁻¹ * ((k : L) * (y * (k : L) * y⁻¹)) := by group
        _ = (k : L)⁻¹ := by rw [hnormL, mul_one]
        _ = k := by
          have hkpow := hK.2 k k.property
          have hkinv : (k : L) = (k : L)⁻¹ :=
            mul_eq_one_iff_eq_inv.mp (by simpa only [pow_two] using hkpow)
          exact hkinv.symm
    exact (mul_inv_eq_iff_eq_mul.mp hfixed).symm
  obtain ⟨V, hV, hcardV, hmemV⟩ := central_square_pair_four K hK hcardK y hy
    (fun hk => hyH (hKle hk)) hcomm
  have hsquareV : ∀ g : L, g ∈ V ↔ g ^ 2 = 1 := by
    intro g
    constructor
    · exact hV.2 g
    · intro hpow
      by_cases hgH : g ∈ H
      · exact (hmemV g).mpr (Or.inl ((hKmem g).mpr ⟨hgH, hpow⟩))
      · have htH : g * y ∈ H := (H.mul_mem_iff_of_index_two hindex).mpr
          (by simp only [hgH, hyH])
        let t : H := ⟨g * y, htH⟩
        have hgy : (t : L) * y = g := by
          change g * y * y = g
          rw [mul_assoc, ← pow_two, hy, mul_one]
        have hnormt : t * (MulAut.conjNormal (H := H) y) t = 1 := by
          apply Subtype.ext
          change (t : L) * (y * (t : L) * y⁻¹) = 1
          calc
            (t : L) * (y * (t : L) * y⁻¹) = ((t : L) * y) ^ 2 * (y ^ 2)⁻¹ := by
              simp only [pow_two]
              group
            _ = 1 := by rw [hgy, hpow, hy]; simp
        have ht := (principal_involution_norm_kernel exponent coordinates
          (MulAut.conjNormal (H := H) y) hscalarY t).mp hnormt
        have htK : (t : L) ∈ K := (hKmem t).mpr ⟨t.property, congrArg Subtype.val ht⟩
        exact (hmemV g).mpr (Or.inr ⟨⟨t, htK⟩, hgy⟩)
  refine ⟨V, ?_, hV, hcardV, hsquareV⟩
  constructor
  intro automorphism
  ext g
  change automorphism g ∈ V ↔ g ∈ V
  rw [hsquareV, hsquareV, ← map_pow]
  constructor
  · intro hpow
    exact automorphism.injective (hpow.trans automorphism.map_one.symm)
  · intro hpow
    rw [hpow, map_one]

end CFSG.ProperTwoGeneratedCore
