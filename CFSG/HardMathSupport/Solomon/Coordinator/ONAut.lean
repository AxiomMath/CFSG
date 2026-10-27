module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma59
public import CFSG.Sporadic.ONOddCore.OuterOrder
public import CFSG.LargeExtraspecial.S12TriG2
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.ON

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] noncomputable def mulAutQuotCenter (K : Type*) [Group K] :
    MulAut K →* MulAut (K ⧸ Subgroup.center K) where
  toFun α := QuotientGroup.congr _ _ α (Subgroup.map_center_eq α)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on
    rfl
  map_mul' := by
    intro α γ
    ext q
    induction q using QuotientGroup.induction_on
    rfl

theorem mulAutQuotCenter_mk {K : Type*} [Group K] (α : MulAut K) (x : K) :
    mulAutQuotCenter K α (QuotientGroup.mk x) = QuotientGroup.mk (α x) := rfl

theorem mulAutQuotCenter_injective {K : Type*} [Group K] (hK : commutator K = ⊤) :
    Function.Injective (mulAutQuotCenter K) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  have hc : ∀ x : K, x⁻¹ * α x ∈ Subgroup.center K := by
    intro x
    have h1 := congrArg (fun φ : MulAut (K ⧸ Subgroup.center K) => φ (QuotientGroup.mk x)) hα
    simp only [mulAutQuotCenter_mk, MulAut.one_apply] at h1
    exact QuotientGroup.eq.1 h1.symm
  let δ : K →* ↥(Subgroup.center K) :=
    { toFun := fun x => ⟨x⁻¹ * α x, hc x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        have hxc := Subgroup.mem_center_iff.1 (hc x) (y⁻¹)
        simp only [Subgroup.coe_mul, mul_inv_rev, map_mul]
        calc y⁻¹ * x⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [← hxc]
          _ = x⁻¹ * α x * (y⁻¹ * α y) := by group }
  have hδ : ∀ x : K, δ x = 1 := fun x =>
    (Abelianization.commutator_subset_ker δ (hK ▸ Subgroup.mem_top x) : x ∈ δ.ker)
  refine MulEquiv.ext fun x => ?_
  have h1 : x⁻¹ * α x = 1 := congrArg Subtype.val (hδ x)
  rw [MulAut.one_apply]
  calc α x = x * (x⁻¹ * α x) := by group
    _ = x := by rw [h1, mul_one]

theorem card_mulAut_onan_dvd :
    Nat.card (MulAut (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group) ∣
      460815505920 * 4 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  have hAut : Nat.card (MulAut (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group) =
      Nat.card (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) :=
    (CFSG.LargeExtraspecial.S12Tri.card_mulAut_congr b').symm
  refine hAut ▸ ?_
  have hs : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  have hcard : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .ONan) = 460815505920 :=
    CFSG.Sporadic.ON.card_ON
  have hnab : ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier .ONan, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hprime := @IsSimpleGroup.prime_card _ ⟨fun a b => hc a b⟩ hs
    rw [hcard] at hprime
    exact absurd hprime (by norm_num)
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .ONan) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  have hinj : Function.Injective (MulAut.conj : CFSG.Blueprint.NativeSporadic.Carrier .ONan →*
      MulAut (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .ONan) := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h2 : g * h * g⁻¹ = h := by
        have := congrArg (fun φ : MulAut (CFSG.Blueprint.NativeSporadic.Carrier .ONan) => φ h) hg
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc h * g = g * h * g⁻¹ * g := by rw [h2]
        _ = g * h := by group
    rw [hZ] at hgZ
    exact Subgroup.mem_bot.1 hgZ
  have hinner : Nat.card (inner (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) = 460815505920 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hout : Nat.card (Outer (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) ∣ 4 :=
    (CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four).1
  rw [← (inner (CFSG.Blueprint.NativeSporadic.Carrier .ONan)).card_mul_index, hinner]
  exact Nat.mul_dvd_mul_left _ hout

theorem inputONAut_holds :
    LocalBalance.Lemma59Ns.InputONAut := by
  intro X _ _ hX A hA
  obtain ⟨hperf, -, ⟨e⟩⟩ := hX
  let f : MulAut X →* MulAut (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group :=
    (MulAut.congr e).toMonoidHom.comp (mulAutQuotCenter X)
  have hf : Function.Injective f :=
    (MulAut.congr e).injective.comp (mulAutQuotCenter_injective hperf)
  have hcardA : Nat.card A = Nat.card (A.map f) :=
    (Subgroup.card_map_of_injective hf).symm
  have hdvd : Nat.card A ∣ 460815505920 * 4 :=
    hcardA ▸ (Subgroup.card_subgroup_dvd_card (A.map f)).trans card_mulAut_onan_dvd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hA
  rw [hk] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have hk5 : 5 ≤ k := by
    by_contra h5
    push Not at h5
    have : 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h243 : 3 ^ 5 ∣ 460815505920 * 4 := (Nat.pow_dvd_pow 3 hk5).trans hdvd
  norm_num at h243

end CFSG.HardMathSupport.Solomon.Coordinator
