module

public import CFSG.LieType.Ree.LocalBlockSylowAction
public import CFSG.LieType.Ree.LargeReeB2FixedCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial

theorem derivedSeries_eq_bot_of_injective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {n : ℕ} (h : derivedSeries H n = ⊥) : derivedSeries G n = ⊥ := by
  have h1 := map_derivedSeries_le_derivedSeries f n
  rwa [h, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hf] at h1

namespace ReeTag

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] [Module (ZMod 2) K] {a : ℕ}

omit [Module (ZMod 2) K] in
theorem largeReeCoord_mem
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (t v : K) :
    largeReeCoord a K t v ∈ F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ := by
  refine Subgroup.mem_inf.2 ⟨?_, mem_reeGamma_of_fixed (largeReeP_mem_adjointGroup _ _ _ _)
    (finiteReeAut_largeReeCoord hK t v)⟩
  rw [F4_fixedOrbitRoots_one]
  exact largeReeP_mem_rootSpan _ _ _ _

omit [Module (ZMod 2) K] in
theorem exists_largeReeCoord_eq
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : ModGL F4.tag K}
    (hg : g ∈ F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩) :
    ∃ t v : K, largeReeCoord a K t v = g := by
  obtain ⟨⟨t, v⟩, -, h⟩ := (bijOn_largeReeCoord hK).2.2 hg
  exact ⟨t, v, h⟩

omit [Module (ZMod 2) K] [Finite K] in
theorem largeReeCoord_injective
    {t v t' v' : K}
    (h : largeReeCoord a K t v = largeReeCoord a K t' v') : t = t' ∧ v = v' := by
  obtain ⟨h1, -, h3, -⟩ := largeReeP_injective h
  exact ⟨h1, h3⟩

omit [Module (ZMod 2) K] in
theorem largeReeCoord_suzuki_mul
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = largeReeSigma a c) (x z y w : K) :
    largeReeCoord a K (x + y) (z + w + x * σ y + (x + y) * σ (x + y)) =
      largeReeCoord a K x (z + x * σ x) * largeReeCoord a K y (w + y * σ y) := by
  have h2 := F4_two_eq_zero (K := K)
  rw [largeReeCoord_mul hK, ← hσ, map_add]
  congr 1
  linear_combination (x * σ y) * h2

theorem exists_mulEquiv_suzukiA
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = largeReeSigma a c) :
    ∃ e : F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ ≃* SuzukiA K σ,
      ∀ (t v : K) (h : largeReeCoord a K t v ∈ F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩),
        e ⟨_, h⟩ = ⟨t, v + t * σ t⟩ := by
  have h2 := F4_two_eq_zero (K := K)
  let f : SuzukiA K σ →* F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ :=
    MonoidHom.mk' (fun p => ⟨largeReeCoord a K p.fst (p.snd + p.fst * σ p.fst),
      largeReeCoord_mem hK _ _⟩) fun p q => Subtype.ext (by
        change largeReeCoord a K (p * q).fst ((p * q).snd + (p * q).fst * σ (p * q).fst) =
          largeReeCoord a K p.fst (p.snd + p.fst * σ p.fst) *
            largeReeCoord a K q.fst (q.snd + q.fst * σ q.fst)
        rw [suzukiA_mul_fst, suzukiA_mul_snd]
        exact largeReeCoord_suzuki_mul hK σ hσ _ _ _ _)
  have hinj : Function.Injective f := fun p q h => by
    have h' : largeReeCoord a K p.fst (p.snd + p.fst * σ p.fst) =
        largeReeCoord a K q.fst (q.snd + q.fst * σ q.fst) := congrArg Subtype.val h
    obtain ⟨h1, h3⟩ := largeReeCoord_injective h'
    refine BinExt.ext h1 ?_
    rw [h1] at h3
    exact add_right_cancel h3
  have hsurj : Function.Surjective f := fun x => by
    obtain ⟨t, v, htv⟩ := exists_largeReeCoord_eq hK x.2
    refine ⟨⟨t, v + t * σ t⟩, Subtype.ext ?_⟩
    rw [← htv]
    change largeReeCoord a K t (v + t * σ t + t * σ t) = largeReeCoord a K t v
    congr 1
    linear_combination (t * σ t) * h2
  refine ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm, fun t v h => ?_⟩
  rw [MulEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  change largeReeCoord a K t v = largeReeCoord a K t (v + t * σ t + t * σ t)
  congr 1
  linear_combination (-(t * σ t)) * h2

theorem large_Ree_B2_pair_automorphism_bound
    (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K F4.prime] [Module (ZMod 2) K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ (a + 1)) :
    (∃ e : F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ ≃* SuzukiA K σ,
      ∀ (t v : K) (h : largeReeCoord a K t v ∈ F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩),
        e ⟨_, h⟩ = ⟨t, v + t * σ t⟩) ∧
    derivedSeries (MulAut (F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩)) 3 = ⊥ ∧
    derivedSeries (pairAutSubgroup
      ((F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩).subgroupOf
        (F4.reeLocalBlock K a ⟨1, by decide⟩))
      ((F4.reeFixedOrbitNegUnipotent K a ⟨1, by decide⟩).subgroupOf
        (F4.reeLocalBlock K a ⟨1, by decide⟩))) 3 = ⊥ := by
  have : Fact F4.prime.Prime := ⟨Nat.prime_two⟩
  have hσ' : ∀ c, σ c = largeReeSigma a c := fun c => by rw [hσ, largeReeSigma, pow_succ']
  obtain ⟨-, σ₀, -, hσ₀, -, -, -, h4⟩ := large_Ree_field_powers a K hK
  have hσσ₀ : σ = σ₀ := RingEquiv.ext fun c => by rw [hσ', hσ₀, largeReeSigma]
  have hσ4 : σ ^ 4 ≠ 1 := hσσ₀ ▸ h4 ha
  have hA := (suzuki_two_A_automorphism_solvable (K := K) (by omega : 1 ≤ 2 * a + 1) hK σ
    hσ4).2.2.2.2.2.2.2.1
  obtain ⟨e, he⟩ := exists_mulEquiv_suzukiA hK σ hσ'
  have hX : derivedSeries (MulAut (F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩)) 3 = ⊥ :=
    derivedSeries_eq_bot_of_injective (f := (MulAut.congr e).toMonoidHom)
      (MulAut.congr e).injective hA
  refine ⟨⟨e, he⟩, hX, ?_⟩
  have hXM := reeFixedOrbitUnipotent_le_reeLocalBlock (t := F4) (K := K) (a := a)
    ⟨1, by decide⟩
  exact derivedSeries_eq_bot_of_injective
    (f := (MulAut.congr ((Subgroup.subgroupOfEquivOfLe hXM).trans e)).toMonoidHom.comp
      (pairAutRestrict _ _))
    ((MulAut.congr _).injective.comp (injective_pairAutRestrict_reeLocalBlock ⟨1, by decide⟩))
    hA

end ReeTag

end CFSG.LieType.Ree
