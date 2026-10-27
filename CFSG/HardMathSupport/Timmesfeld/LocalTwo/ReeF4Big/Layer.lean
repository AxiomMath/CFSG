module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Plane
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Decomp
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Malle.LocalAction CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

section Generic

theorem mem_sup_of_commute' {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let T : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [h a' ha' b hb]
          _ = a * b * (a' * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [← h a ha b hb] }
  have hle : A ⊔ B ≤ T := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact hle hx

end Generic

section Types

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem suzuki_nonab (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x y : suzukiGroup a K, x * y ≠ y * x := by
  obtain ⟨-, hnt, -⟩ := suzuki_simple ha hK
  obtain ⟨hc, -⟩ := suzuki_perfect ha hK
  by_contra h
  push Not at h
  have hb : commutator (suzukiGroup a K) = ⊥ := by
    rw [commutator_def, eq_bot_iff]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (h g₁ g₂)
  rw [hc] at hb
  obtain ⟨g, hg⟩ := exists_ne (1 : suzukiGroup a K)
  have hg' : g ∈ (⊥ : Subgroup (suzukiGroup a K)) := hb ▸ Subgroup.mem_top g
  exact hg (Subgroup.mem_bot.1 hg')

theorem layerType_props (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {G : Type} [Group G]
    (h : Nonempty (G ≃* suzukiGroup a K) ∨ Nonempty (G ≃* SL2 K)) :
    CFSG.IsQuasisimple G ∧ Subgroup.center G = ⊥ ∧ 2 ^ (2 * a + 1) - 1 ∣ Nat.card G := by
  have hQ1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hcen : ∀ {H : Type} [Group H], (H ≃* G) → Subgroup.center H = ⊥ →
      Subgroup.center G = ⊥ := by
    intro H _ e hH
    refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
    have h1 : e.symm g ∈ Subgroup.center H :=
      (MulEquivClass.apply_mem_center_iff e.symm).2 hg
    rw [hH, Subgroup.mem_bot] at h1
    simpa using congrArg e h1
  rcases h with h | h
  · obtain ⟨e⟩ := h
    haveI := (suzuki_simple ha hK).2.2
    obtain ⟨hq, hz⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (suzuki_nonab ha hK)
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, hcen e.symm hz, ?_⟩
    rw [Nat.card_congr e.toEquiv, suzuki_order hK]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_refl _) _) _
  · obtain ⟨e⟩ := h
    haveI := CFSG.LieType.Ree.LargeReeInvolution.isSimpleGroup_SL2 ha hK
    obtain ⟨hq, hz⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      (CFSG.LieType.Ree.LargeReeInvolution.exists_SL2_mul_ne_mul (K := K))
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, hcen e.symm hz, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    have h2 := Nat.sub_dvd_pow_sub_pow (2 ^ (2 * a + 1)) 1 2
    rw [one_pow] at h2
    exact Dvd.dvd.mul_left h2 _

end Types

section Layer

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a p : ℕ}

@[expose] def IsLayerDecomp (P : ReePlane K a p)
    (z : (rootsOfUnity p (AlgebraicClosure K)) × (rootsOfUnity p (AlgebraicClosure K)))
    (A Sg : Subgroup (ReeTag.F4.reeGamma K a)) : Prop :=
  (∀ γ, γ ∈ A ↔ reeConj P.g₀ γ ∈ ZGrp (L := AlgebraicClosure K)
    (rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ) (z.2 : (AlgebraicClosure K)ˣ) P.U))) ∧
  (∀ α ∈ A, ∀ s ∈ Sg, α * s = s * α) ∧ A ⊓ Sg = ⊥ ∧
  A ⊔ Sg = Subgroup.centralizer ({P.Ψ z} : Set (ReeTag.F4.reeGamma K a)) ∧ P.Ψ z ∈ A ∧
  (Nonempty (Sg ≃* suzukiGroup a K) ∨ Nonempty (Sg ≃* SL2 K))

theorem plane_layer (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (P : ReePlane K a p)
    {z : (rootsOfUnity p (AlgebraicClosure K)) × (rootsOfUnity p (AlgebraicClosure K))}
    (hz : z ≠ 1)
    (hne : rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ) (z.2 : (AlgebraicClosure K)ˣ)
      P.U) ≠ ∅) :
    ∃ A Sg : Subgroup (ReeTag.F4.reeGamma K a), IsLayerDecomp P z A Sg := by
  classical
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  set b : Fin ReeTag.F4.tag.rank → (AlgebraicClosure K)ˣ :=
    expTuple (z.1 : (AlgebraicClosure K)ˣ) (z.2 : (AlgebraicClosure K)ˣ) P.U with hb
  have hxb : reeConj P.g₀ (P.Ψ z) = rootDiagUnit ReeTag.F4.tag b := P.hΨ z
  have hbF : rootDiagUnit ReeTag.F4.tag b ∈ twistedFixed P.D.F
      (canonicalRep (coxeterSystem ReeTag.F4.tag) (AlgebraicClosure K) P.w) := by
    rw [← hxb]
    exact reeConj_mem_twistedFixed P.D P.hg₀ P.hFg₀ _
  have hz5 : (z.1 : (AlgebraicClosure K)ˣ) ^ p = 1 ∧ (z.2 : (AlgebraicClosure K)ˣ) ^ p = 1 :=
    ⟨(mem_rootsOfUnity p _).1 z.1.2, (mem_rootsOfUnity p _).1 z.2.2⟩
  have hbp : ∀ i, b i ^ p = 1 := by
    intro i
    show ((z.1 : (AlgebraicClosure K)ˣ) ^ P.U 0 i * (z.2 : (AlgebraicClosure K)ˣ) ^ P.U 1 i) ^ p = 1
    rw [mul_pow]
    have hzp : ∀ (x : (AlgebraicClosure K)ˣ), x ^ p = 1 → ∀ n : ℤ, (x ^ n) ^ p = 1 := by
      intro x hx n
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
    rw [hzp _ hz5.1, hzp _ hz5.2, mul_one]
  have hb1 : b ≠ 1 := by
    intro h
    apply hz
    apply P.Ψinj
    apply reeConj_injective P.g₀
    rw [hxb, h, rootDiagUnit_one, map_one, map_one]
  obtain ⟨A, Sg, hAm, hc, hi, hs, hxA, hty⟩ := exists_layer_decomp P.D hK hp hp3 P.w P.hg₀ P.hFg₀
    hbF hbp hb1 hne (P.Ψ z) hxb
  exact ⟨A, Sg, hAm, hc, hi, hs, hxA, hty⟩

theorem plane_layer_dvd (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime)
    (hp3 : 3 < p) (P : ReePlane K a p)
    {z : (rootsOfUnity p (AlgebraicClosure K)) × (rootsOfUnity p (AlgebraicClosure K))}
    (hne : rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ) (z.2 : (AlgebraicClosure K)ˣ)
      P.U) ≠ ∅)
    {A Sg : Subgroup (ReeTag.F4.reeGamma K a)} (hd : IsLayerDecomp P z A Sg) :
    ¬ Nat.Coprime p (Nat.card Sg) := by
  classical
  intro hcop
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨hAm, hcAS, hinf, hsup, -, -⟩ := hd
  obtain ⟨β, hβ⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨ξ, hξ⟩ := exists_primitive_root_two (L := AlgebraicClosure K) hp (by omega)
  obtain ⟨s, t, hst⟩ : ∃ s t : ℕ, ¬ ((((s : ℤ) * ∑ i, P.U 0 i * β i +
      (t : ℤ) * ∑ i, P.U 1 i * β i : ℤ) : ZMod p)) = 0 := by
    have hF := P.hF1 β ((mem_rootFinset).2 hβ.1)
    by_cases h0 : (((∑ i, P.U 0 i * β i : ℤ)) : ZMod p) = 0
    · refine ⟨0, 1, ?_⟩
      intro h
      apply hF ⟨h0, ?_⟩
      simpa using h
    · refine ⟨1, 0, ?_⟩
      intro h
      apply h0
      simpa using h
  set y := P.Ψ (planeElt hξ s t) with hy
  have hyC : y ∈ Subgroup.centralizer ({P.Ψ z} : Set (ReeTag.F4.reeGamma K a)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hy, ← map_mul, ← map_mul, mul_comm]
  rw [← hsup] at hyC
  obtain ⟨α, hα, s', hs', hαs⟩ := mem_sup_of_commute' hcAS hyC
  have hy1 : y ^ p = 1 := by
    rw [hy, ← map_pow]
    have : planeElt hξ s t ^ p = 1 := by
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · show (ξ ^ s) ^ p = 1
        rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
      · show (ξ ^ t) ^ p = 1
        rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
    rw [this, map_one]
  have hcomm : Commute α s' := hcAS α hα s' hs'
  have h1 : α ^ p * s' ^ p = 1 := by rw [← hcomm.mul_pow, hαs]; exact hy1
  have hsp : s' ^ p ∈ A ⊓ Sg := by
    refine ⟨?_, Sg.pow_mem hs' p⟩
    have : s' ^ p = (α ^ p)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact A.inv_mem (A.pow_mem hα p)
  rw [hinf, Subgroup.mem_bot] at hsp
  have hs1 : s' = 1 := by
    have h2 : orderOf (⟨s', hs'⟩ : Sg) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext hsp
    have h3 : orderOf (⟨s', hs'⟩ : Sg) ∣ Nat.card Sg := orderOf_dvd_natCard _
    have h4 : orderOf (⟨s', hs'⟩ : Sg) ∣ Nat.gcd p (Nat.card Sg) := Nat.dvd_gcd h2 h3
    rw [hcop.gcd_eq_one] at h4
    have h5 : (⟨s', hs'⟩ : Sg) = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
    exact congrArg Subtype.val h5
  have hyA : y ∈ A := by
    rw [← hαs, hs1, mul_one]
    exact hα
  obtain ⟨c, hc, hcy⟩ := mem_ZGrp.1 ((hAm y).1 hyA)
  have hcb : c = expTuple ((planeElt hξ s t).1 : (AlgebraicClosure K)ˣ)
      ((planeElt hξ s t).2 : (AlgebraicClosure K)ˣ) P.U :=
    rootDiagUnit_injective (hcy.trans (P.hΨ (planeElt hξ s t)))
  have hcβ := hc β hβ
  rw [hcb] at hcβ
  exact hst ((rootChar_expTuple_pow_iff hξ P.U s t β).1 hcβ)

theorem isPLayer_of_layer (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime)
    (hp3 : 3 < p) (P : ReePlane K a p) (γ : ReeTag.F4.reeGamma K a)
    {z : (rootsOfUnity p (AlgebraicClosure K)) × (rootsOfUnity p (AlgebraicClosure K))}
    (hz : z ≠ 1)
    (hne : rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ) (z.2 : (AlgebraicClosure K)ˣ)
      P.U) ≠ ∅)
    {A Sg : Subgroup (ReeTag.F4.reeGamma K a)} (hd : IsLayerDecomp P z A Sg)
    {E : Subgroup (MulAut (ReeTag.F4.reeGamma K a))}
    (hmem : MulAut.conj (γ * P.Ψ z * γ⁻¹) ∈ E) :
    IsPLayer p E (Sg.map (MulAut.conj γ).toMonoidHom) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hinj : Function.Injective
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  have hdvd := plane_layer_dvd ha hK hp hp3 P hne hd
  obtain ⟨hquasi, -, -⟩ := layerType_props ha hK hd.2.2.2.2.2
  obtain ⟨-, hcAS, -, hsup, -, -⟩ := hd
  have hSgC : ∀ t ∈ Sg, P.Ψ z * t * (P.Ψ z)⁻¹ = t := by
    intro t ht
    have htC : t ∈ Subgroup.centralizer ({P.Ψ z} : Set (ReeTag.F4.reeGamma K a)) := by
      rw [← hsup]
      exact (le_sup_right : Sg ≤ A ⊔ Sg) ht
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 htC
    rw [← h1, mul_inv_cancel_right]
  refine ⟨MulAut.conj (γ * P.Ψ z * γ⁻¹), hmem, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    have h2 : γ * P.Ψ z * γ⁻¹ = 1 := hinj (by rw [h1, map_one])
    have h3 : P.Ψ z = 1 := by
      have : P.Ψ z = γ⁻¹ * (γ * P.Ψ z * γ⁻¹) * γ := by group
      rw [this, h2]
      group
    exact hz (P.Ψinj (h3.trans (map_one P.Ψ).symm))
  · rintro _ ⟨t, ht, rfl⟩
    change (γ * P.Ψ z * γ⁻¹) * (γ * t * γ⁻¹) * (γ * P.Ψ z * γ⁻¹)⁻¹ = γ * t * γ⁻¹
    calc (γ * P.Ψ z * γ⁻¹) * (γ * t * γ⁻¹) * (γ * P.Ψ z * γ⁻¹)⁻¹
        = γ * (P.Ψ z * t * (P.Ψ z)⁻¹) * γ⁻¹ := by group
      _ = γ * t * γ⁻¹ := by rw [hSgC t ht]
  · intro f hf t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    have hf' : (γ * P.Ψ z * γ⁻¹) * f * (γ * P.Ψ z * γ⁻¹)⁻¹ = f := hf
    have hfc : (γ * P.Ψ z * γ⁻¹) * f = f * (γ * P.Ψ z * γ⁻¹) := by
      calc (γ * P.Ψ z * γ⁻¹) * f
          = ((γ * P.Ψ z * γ⁻¹) * f * (γ * P.Ψ z * γ⁻¹)⁻¹) * (γ * P.Ψ z * γ⁻¹) := by group
        _ = f * (γ * P.Ψ z * γ⁻¹) := by rw [hf']
    have hf₀ : γ⁻¹ * f * γ ∈ Subgroup.centralizer ({P.Ψ z} : Set (ReeTag.F4.reeGamma K a)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (γ⁻¹ * f * γ) * P.Ψ z
          = γ⁻¹ * (f * (γ * P.Ψ z * γ⁻¹)) * γ := by group
        _ = γ⁻¹ * ((γ * P.Ψ z * γ⁻¹) * f) * γ := by rw [hfc]
        _ = P.Ψ z * (γ⁻¹ * f * γ) := by group
    rw [← hsup] at hf₀
    obtain ⟨α, hα, s', hs, hαs⟩ := mem_sup_of_commute' hcAS hf₀
    refine ⟨s' * t₀ * s'⁻¹, Sg.mul_mem (Sg.mul_mem hs ht₀) (Sg.inv_mem hs), ?_⟩
    have hfeq : f = γ * (α * s') * γ⁻¹ := by
      rw [hαs]; group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hfeq]
    have hαt : α * (s' * t₀ * s'⁻¹) * α⁻¹ = s' * t₀ * s'⁻¹ := by
      have h1 := hcAS α hα (s' * t₀ * s'⁻¹) (Sg.mul_mem (Sg.mul_mem hs ht₀) (Sg.inv_mem hs))
      rw [h1, mul_inv_cancel_right]
    symm
    calc γ * (α * s') * γ⁻¹ * (γ * t₀ * γ⁻¹) * (γ * (α * s') * γ⁻¹)⁻¹
        = γ * (α * (s' * t₀ * s'⁻¹) * α⁻¹) * γ⁻¹ := by group
      _ = γ * (s' * t₀ * s'⁻¹) * γ⁻¹ := by rw [hαt]
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Sg.equivMapOfInjective (MulAut.conj γ).toMonoidHom (MulAut.conj γ).injective) hquasi
  · intro hcop
    apply hdvd
    rwa [Subgroup.card_map_of_injective (MulAut.conj γ).injective] at hcop

end Layer

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big
