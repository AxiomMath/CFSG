module

public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LieType.CentralExt.SL2Lift

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Matrix Equiv Equiv.Perm

theorem sl2_center_eq_bot (K : Type*) [Field K] [CharP K 2] :
    Subgroup.center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hr1 : r = 1 := by
    have : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [← hrz, hr1]
  simp

theorem sl2_four_equiv_alt5 :
    Nonempty (SpecialLinearGroup (Fin 2) (GaloisField 2 2) ≃* alternatingGroup (Fin 5)) := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hcard : Nat.card (SpecialLinearGroup (Fin 2) (GaloisField 2 2)) = 60 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  have hcen := sl2_center_eq_bot (GaloisField 2 2)
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center
      (SpecialLinearGroup (Fin 2) (GaloisField 2 2)))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcen]
  let e₀ : SpecialLinearGroup (Fin 2) (GaloisField 2 2) ≃*
      ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    MulEquiv.ofBijective _ ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK])
  have : IsSimpleGroup (SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    MulEquiv.isSimpleGroup e₀
  exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hcard

theorem card_sl2_five' : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_zmod]
  norm_num

theorem card_alt5'' : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem exists_sl2_five_alt5' : ∃ ψ : SpecialLinearGroup (Fin 2) (ZMod 5) →*
    alternatingGroup (Fin 5), Function.Surjective ψ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsimple : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
    ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
  have hcen : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 5))) = 2 := by
    rw [Nat.card_congr (SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv,
      show max (Fintype.card (Fin 2)) 1 = 2 by simp]
    exact (IsPrimitiveRoot.neg_one 5 (by norm_num)).card_rootsOfUnity
  have hcard : Nat.card (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) = 60 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 5)))
    rw [card_sl2_five', hcen] at h
    show Nat.card (SpecialLinearGroup (Fin 2) (ZMod 5) ⧸
      Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 5))) = 60
    omega
  obtain ⟨e⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hcard
  exact ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _)⟩

theorem alt5_cover_cases' {E : Type} [Group E] [Finite E] (ρ : E →* alternatingGroup (Fin 5))
    (hρs : Function.Surjective ρ) (hkerc : ρ.ker ≤ Subgroup.center E) (hker2 : IsPGroup 2 ρ.ker)
    (hno2 : ∀ I : Subgroup E, I.Normal → (∀ e : E, ∃ n : ℕ, e ^ 2 ^ n ∈ I) → I = ⊤) :
    Function.Injective ρ ∨
      (Nonempty (E ≃* SpecialLinearGroup (Fin 2) (ZMod 5)) ∧ Nat.card ρ.ker = 2) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ, hψs⟩ := exists_sl2_five_alt5'
  have hk : ringChar (ZMod 5) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hk hρs hkerc hker2 ψ
  have hβx : ∀ g, ρ (β g) = ψ g := fun g => DFunLike.congr_fun hβ g
  have hdecomp : ∀ e : E, ∃ g, (β g)⁻¹ * e ∈ ρ.ker := by
    intro e
    obtain ⟨g, hg⟩ := hψs (ρ e)
    refine ⟨g, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβx, hg, inv_mul_cancel]
  have hIn : β.range.Normal := by
    refine ⟨fun i hi e => ?_⟩
    obtain ⟨g, hg⟩ := hdecomp e
    have he : e = β g * ((β g)⁻¹ * e) := by group
    have hkc := Subgroup.mem_center_iff.mp (hkerc hg)
    obtain ⟨g', rfl⟩ := hi
    rw [he]
    have : β g * ((β g)⁻¹ * e) * β g' * (β g * ((β g)⁻¹ * e))⁻¹ = β g * β g' * (β g)⁻¹ := by
      calc β g * ((β g)⁻¹ * e) * β g' * (β g * ((β g)⁻¹ * e))⁻¹ =
          β g * (((β g)⁻¹ * e) * β g') * ((β g)⁻¹ * e)⁻¹ * (β g)⁻¹ := by group
        _ = β g * (β g' * ((β g)⁻¹ * e)) * ((β g)⁻¹ * e)⁻¹ * (β g)⁻¹ := by rw [← hkc]
        _ = β g * β g' * (β g)⁻¹ := by group
    rw [this, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, rfl⟩
  have hpow : ∀ e : E, ∃ n : ℕ, e ^ 2 ^ n ∈ β.range := by
    intro e
    obtain ⟨g, hg⟩ := hdecomp e
    obtain ⟨n, hn⟩ := hker2 ⟨_, hg⟩
    have hn' : ((β g)⁻¹ * e) ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have hkc := Subgroup.mem_center_iff.mp (hkerc hg)
    have hcomm : Commute (β g) ((β g)⁻¹ * e) := hkc (β g)
    refine ⟨n, ?_⟩
    have : e = β g * ((β g)⁻¹ * e) := by group
    rw [this, hcomm.mul_pow, hn', mul_one, ← map_pow]
    exact ⟨_, rfl⟩
  have htop := hno2 β.range hIn hpow
  have hβs : Function.Surjective β := fun e => by
    have : e ∈ β.range := by rw [htop]; trivial
    exact this
  have hcardE : Nat.card E = 60 * Nat.card ρ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).toEquiv,
      card_alt5''] at h1
    exact h1
  have hle : Nat.card E ≤ 120 := card_sl2_five' ▸ Nat.card_le_card_of_surjective β hβs
  obtain ⟨j, hj⟩ := hker2.exists_card_eq
  have hj1 : j ≤ 1 := by
    by_contra hj1
    have h4 : 4 ≤ 2 ^ j := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hcardE, hj] at hle
    omega
  interval_cases j
  · left
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hj, pow_zero])
  · right
    have hE : Nat.card E = 120 := by rw [hcardE, hj]; norm_num
    have hβi : Function.Injective β :=
      ((Nat.bijective_iff_surjective_and_card β).2 ⟨hβs, by rw [card_sl2_five', hE]⟩).1
    exact ⟨⟨(MulEquiv.ofBijective β ⟨hβi, hβs⟩).symm⟩, by rw [hj, pow_one]⟩

end CFSG.CGT.PushingUpLit.CGT6
