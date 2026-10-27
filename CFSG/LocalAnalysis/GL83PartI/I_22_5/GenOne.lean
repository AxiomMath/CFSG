module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Prime
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Descent

public section

namespace GL83.CompFam

open CFSG.Open

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

@[expose] def conjEnd (K : Subgroup G) (a : G) (ha : cj a K = K) : K →* K :=
  (MulEquiv.subgroupCongr ha).toMonoidHom.comp (cjHom a K)

theorem coe_conjEnd (K : Subgroup G) (a : G) (ha : cj a K = K) (x : K) :
    (conjEnd K a ha x : G) = a * x * a⁻¹ := rfl

@[expose] def quotPi (Q : Type*) [Group Q] :
    (ZMod p → Q) →* (ZMod p → Q ⧸ Subgroup.center Q) :=
  MonoidHom.pi fun i => (QuotientGroup.mk' (Subgroup.center Q)).comp
    (Pi.evalMonoidHom (fun _ => Q) i)

omit [Fact p.Prime] in
theorem quotPi_apply (Q : Type*) [Group Q] (f : ZMod p → Q) (i : ZMod p) :
    quotPi (p := p) Q f i = QuotientGroup.mk (f i) := rfl

theorem commute_normPi_central {K : Subgroup G} {b : G} (hc : NormComm p K b)
    (k : ZMod p → K) (hk : ∀ i, k i ∈ Subgroup.center K) (i : ZMod p) (y : K) :
    Commute (cjEmb p K b i y) (normPi hc k) := by
  rw [normPi, MonoidHom.noncommPiCoprod_apply]
  refine Finset.noncommProd_commute _ _ _ _ fun j _ => ?_
  by_cases hij : j = i
  · subst hij
    exact Commute.map (show Commute y (k j) from Subgroup.mem_center_iff.1 (hk j) y)
      (cjEmb p K b j)
  · exact hc (Ne.symm hij) y (k j)

theorem commute_normPi_central' {K : Subgroup G} {b : G} (hc : NormComm p K b)
    (k : ZMod p → K) (hk : ∀ i, k i ∈ Subgroup.center K) (f : ZMod p → K) :
    Commute (normPi hc k) (normPi hc f) := by
  rw [normPi_apply hc f]
  refine Finset.noncommProd_commute _ _ _ _ fun j _ => ?_
  exact (commute_normPi_central hc k hk j (f j)).symm

@[expose] def twistPi (K : Subgroup G) (a : G) (ha : ∀ n : ℕ, cj (a ^ n) K = K) :
    (ZMod p → K) →* (ZMod p → K) :=
  MonoidHom.pi fun i : ZMod p =>
    (conjEnd K (a ^ i.val) (ha _)).comp (Pi.evalMonoidHom (fun _ => K) i)

omit [Fact p.Prime] in
theorem twistPi_mulSingle (K : Subgroup G) (a : G) (ha : ∀ n : ℕ, cj (a ^ n) K = K)
    (i : ZMod p) (y : K) :
    twistPi K a ha (Pi.mulSingle i y) = Pi.mulSingle i (conjEnd K (a ^ i.val) (ha _) y) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [twistPi]
  · simp [twistPi, hj]

theorem normPi_twist {K : Subgroup G} {b a : G} (hab : a * b = b * a)
    (ha : ∀ n : ℕ, cj (a ^ n) K = K) (hc : NormComm p K b) (hc' : NormComm p K (a * b)) :
    normPi hc' = (normPi hc).comp (twistPi K a ha) := by
  refine MonoidHom.pi_ext fun i y => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, twistPi_mulSingle, normPi_mulSingle]
  have hu : Commute a b := hab
  rw [hu.mul_pow, coe_conjEnd]
  have huv : a ^ i.val * b ^ i.val = b ^ i.val * a ^ i.val := (Commute.pow_pow hu _ _).eq
  calc (a ^ i.val * b ^ i.val) * (y : G) * (a ^ i.val * b ^ i.val)⁻¹
      = (b ^ i.val * a ^ i.val) * (y : G) * (b ^ i.val * a ^ i.val)⁻¹ := by rw [huv]
    _ = b ^ i.val * (a ^ i.val * (y : G) * (a ^ i.val)⁻¹) * (b ^ i.val)⁻¹ := by group

theorem normHom_twist {K : Subgroup G} {b a : G} (hab : a * b = b * a)
    (ha : ∀ n : ℕ, cj (a ^ n) K = K) (hc : NormComm p K b) (hc' : NormComm p K (a * b))
    (x : K) :
    normHom hc' x = normPi hc (fun i : ZMod p => conjEnd K (a ^ i.val) (ha _) x) := by
  rw [normHom_apply, normPi_twist hab ha hc hc']
  rfl

variable [Finite G] {B : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem IsFam.layer_le_normJoin_cyclic (hF : IsFam p B 𝒦) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦)
    {b a₀ : G} (hb : b ∈ B) (hbA : b ∉ stab B K₀) (ha₀ : a₀ ∈ stab B K₀)
    (ha₀C : a₀ ∉ cen B K₀) (horb : ∀ K ∈ 𝒦, ∃ i : ZMod p, K = cj (b ^ i.val) K₀) :
    layer 𝒦 ≤ normJoin hF K₀ := by
  classical
  have hQ : IsQuasisimple K₀ := hF.quasi K₀ hK₀
  have hbp : b ^ p = 1 := hF.elem.2 b hb
  have hc : NormComm p K₀ b := hF.normComm hK₀ hb hbA
  have hS : IsSimpleGroup (K₀ ⧸ Subgroup.center K₀) := hQ.2
  have hnab := quasisimple_quotient_nonabelian hQ
  let W := normJoin hF K₀
  let Θ := normPi hc
  let X : Subgroup (ZMod p → K₀ ⧸ Subgroup.center K₀) := (W.comap Θ).map (quotPi K₀)
  have hdiag : ∀ x : K₀, (fun _ : ZMod p => x) ∈ W.comap Θ := by
    intro x
    show Θ (fun _ => x) ∈ W
    exact le_normJoin hF ⟨b, hb, hbA, normSub_mem_normFam hF hK₀ hb hbA⟩ ⟨x, rfl⟩
  have hproj : ∀ (j : ZMod p) (s : K₀ ⧸ Subgroup.center K₀), ∃ x ∈ X, x j = s := by
    intro j s
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨quotPi K₀ (fun _ => x), ⟨_, hdiag x, rfl⟩, rfl⟩
  have hshift : ∀ x ∈ X, shiftHom (p := p) (K₀ ⧸ Subgroup.center K₀) x ∈ X := by
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨shiftHom K₀ f, ?_, ?_⟩
    · show Θ (shiftHom K₀ f) ∈ W
      rw [← normPi_shift hc hbp]
      exact hF.cj_normJoin_le K₀ hb (mul_mem_cj hf)
    · funext i
      rfl
  rcases pi_dichotomy hS hnab X hproj hshift with htop | hfull
  · have hrange : layer 𝒦 ≤ Θ.range := by
      refine iSup₂_le fun K hK => ?_
      obtain ⟨i, rfl⟩ := horb K hK
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨Pi.mulSingle i ⟨x, hx⟩, normPi_mulSingle hc i ⟨x, hx⟩⟩
    have hdec : ∀ z ∈ Θ.range, ∃ u ∈ W, ∃ c ∈ Θ.range, (∀ g ∈ Θ.range, Commute c g) ∧
        z = u * c ∧ u ∈ Θ.range := by
      rintro _ ⟨f, rfl⟩
      have hfX : quotPi K₀ f ∈ X := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨w, hw, hwf⟩ := hfX
      have hk : ∀ i, (w⁻¹ * f) i ∈ Subgroup.center K₀ := by
        intro i
        have := congrFun hwf i
        rw [quotPi_apply, quotPi_apply, QuotientGroup.eq] at this
        simpa using this
      refine ⟨Θ w, hw, Θ (w⁻¹ * f), ⟨_, rfl⟩, ?_, ?_, ⟨w, rfl⟩⟩
      · rintro _ ⟨f', rfl⟩
        exact commute_normPi_central' hc _ hk f'
      · rw [← map_mul]
        congr 1
        group
    have hperf : layer 𝒦 ≤ ⁅layer 𝒦, layer 𝒦⁆ := by
      refine iSup₂_le fun K hK => ?_
      have hKperf : ⁅K, K⁆ = K :=
        Subgroup.isPerfect_iff.1 ((Group.isPerfect_def).2 (hF.quasi K hK).1)
      calc K = ⁅K, K⁆ := hKperf.symm
        _ ≤ ⁅layer 𝒦, layer 𝒦⁆ := Subgroup.commutator_mono (le_layer hK) (le_layer hK)
    refine hperf.trans (Subgroup.commutator_le.2 fun y₁ hy₁ y₂ hy₂ => ?_)
    obtain ⟨u₁, hu₁W, c₁, hc₁R, hc₁c, rfl, hu₁R⟩ := hdec y₁ (hrange hy₁)
    obtain ⟨u₂, hu₂W, c₂, hc₂R, hc₂c, rfl, hu₂R⟩ := hdec y₂ (hrange hy₂)
    rw [commutatorElement_def]
    have e1 : (u₁ * c₁) * (u₂ * c₂) = (u₁ * u₂) * (c₁ * c₂) := by
      calc (u₁ * c₁) * (u₂ * c₂) = u₁ * (c₁ * u₂) * c₂ := by group
        _ = u₁ * (u₂ * c₁) * c₂ := by rw [(hc₁c u₂ hu₂R).eq]
        _ = (u₁ * u₂) * (c₁ * c₂) := by group
    have e2 : (u₂ * c₂) * (u₁ * c₁) = (u₂ * u₁) * (c₁ * c₂) := by
      calc (u₂ * c₂) * (u₁ * c₁) = u₂ * (c₂ * u₁) * c₁ := by group
        _ = u₂ * (u₁ * c₂) * c₁ := by rw [(hc₂c u₁ hu₁R).eq]
        _ = (u₂ * u₁) * (c₂ * c₁) := by group
        _ = (u₂ * u₁) * (c₁ * c₂) := by rw [(hc₁c c₂ hc₂R).eq.symm]
    have key : (u₁ * c₁) * (u₂ * c₂) * (u₁ * c₁)⁻¹ * (u₂ * c₂)⁻¹ = u₁ * u₂ * u₁⁻¹ * u₂⁻¹ := by
      calc (u₁ * c₁) * (u₂ * c₂) * (u₁ * c₁)⁻¹ * (u₂ * c₂)⁻¹
          = ((u₁ * c₁) * (u₂ * c₂)) * ((u₂ * c₂) * (u₁ * c₁))⁻¹ := by group
        _ = ((u₁ * u₂) * (c₁ * c₂)) * ((u₂ * u₁) * (c₁ * c₂))⁻¹ := by rw [e1, e2]
        _ = u₁ * u₂ * u₁⁻¹ * u₂⁻¹ := by group
    rw [key]
    exact W.mul_mem (W.mul_mem (W.mul_mem hu₁W hu₂W) (W.inv_mem hu₁W)) (W.inv_mem hu₂W)
  · exfalso
    have ha₀B : a₀ ∈ B := (mem_stab.1 ha₀).1
    have hab : a₀ * b = b * a₀ := hF.mul_comm_of_mem ha₀B hb
    have hb'B : a₀ * b ∈ B := B.mul_mem ha₀B hb
    have hb'A : a₀ * b ∉ stab B K₀ := by
      intro h
      apply hbA
      have := (stab B K₀).mul_mem ((stab B K₀).inv_mem ha₀) h
      simpa using this
    have hc2 : NormComm p K₀ (a₀ * b) := hF.normComm hK₀ hb'B hb'A
    have hpow : ∀ n : ℕ, cj (a₀ ^ n) K₀ = K₀ :=
      fun n => (mem_stab.1 ((stab B K₀).pow_mem ha₀ n)).2
    have htwW : ∀ x : K₀,
        (fun i : ZMod p => conjEnd K₀ (a₀ ^ i.val) (hpow _) x) ∈ W.comap Θ := by
      intro x
      show Θ _ ∈ W
      rw [← normHom_twist hab hpow hc hc2]
      exact le_normJoin hF ⟨a₀ * b, hb'B, hb'A, normSub_mem_normFam hF hK₀ hb'B hb'A⟩ ⟨x, rfl⟩
    have hxeq : ∀ x : K₀, (QuotientGroup.mk x : K₀ ⧸ Subgroup.center K₀) =
        QuotientGroup.mk (conjEnd K₀ a₀ (mem_stab.1 ha₀).2 x) := by
      intro x
      let e : ZMod p → K₀ ⧸ Subgroup.center K₀ :=
        quotPi K₀ (fun _ => x) *
          (quotPi K₀ (fun i : ZMod p => conjEnd K₀ (a₀ ^ i.val) (hpow _) x))⁻¹
      have heX : e ∈ X := X.mul_mem ⟨_, hdiag x, rfl⟩ (X.inv_mem ⟨_, htwW x, rfl⟩)
      have h0 : conjEnd K₀ (a₀ ^ (0 : ZMod p).val) (hpow _) x = x := by
        apply Subtype.ext
        rw [coe_conjEnd, ZMod.val_zero, pow_zero]
        group
      have h1 : conjEnd K₀ (a₀ ^ (1 : ZMod p).val) (hpow _) x =
          conjEnd K₀ a₀ (mem_stab.1 ha₀).2 x := by
        apply Subtype.ext
        rw [coe_conjEnd, coe_conjEnd, ZMod.val_one, pow_one]
      have he0 : e 0 = 1 := by
        simp only [e, Pi.mul_apply, Pi.inv_apply, quotPi_apply, h0]
        exact mul_inv_cancel _
      have he := congrFun (hfull e heX 0 he0) 1
      simp only [e, Pi.mul_apply, Pi.inv_apply, quotPi_apply, h1, Pi.one_apply] at he
      exact mul_inv_eq_one.1 he
    have hφ : ∀ x : K₀, (conjEnd K₀ a₀ (mem_stab.1 ha₀).2 x)⁻¹ * x ∈ Subgroup.center K₀ := by
      intro x
      have h := QuotientGroup.eq.1 (hxeq x)
      have := (Subgroup.center K₀).inv_mem h
      simpa [mul_inv_rev] using this
    have hid := endo_eq_id_of_central hQ.1 (conjEnd K₀ a₀ (mem_stab.1 ha₀).2) hφ
    apply ha₀C
    refine mem_cen.2 ⟨ha₀B, fun x hx => ?_⟩
    have h := congrArg Subtype.val (hid ⟨x, hx⟩)
    rw [coe_conjEnd] at h
    exact (mul_inv_eq_iff_eq_mul.1 h)

end GL83.CompFam
