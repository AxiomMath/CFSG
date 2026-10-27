module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75D4Comm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75D4Spin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75D4Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L225Theta

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups commutatorElement

namespace F3D4

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem pow_two_mul_apply {S : Type} [Group S] (β : MulAut S) {y : S} (hy : β (β y) = y)
    (j : ℕ) : (β ^ (2 * j)) y = y := by
  induction j with
  | zero => rw [Nat.mul_zero, pow_zero, MulAut.one_apply]
  | succ j ih => rw [Nat.mul_succ, pow_add, MulAut.mul_apply, pow_two, MulAut.mul_apply, hy, ih]

omit [Finite Q] in
theorem apply_eq_of_sq {S : Type} [Group S] (β : MulAut S) {k : ℕ} (hk : Odd k) (hβk : β ^ k = 1)
    {y : S} (hy : β (β y) = y) : β y = y := by
  obtain ⟨j, rfl⟩ := hk
  have h1 := pow_two_mul_apply β hy j
  have h2 : (β ^ (2 * j + 1)) y = y := by rw [hβk, MulAut.one_apply]
  rw [pow_succ', MulAut.mul_apply, h1] at h2
  exact h2

theorem mem_sup_centralizer_d4 (hR1 : Spin8CentreFixedOutAbelian) (hR2 : Harris82Lemma413Three)
    {L M : Subgroup Q} {t : Q} (hLq : IsQuasisimple ↥L) (htL : t ∈ L) (ht : orderOf t = 2)
    (hM : IsSolvableTwoComponentIn M (centralizer {t})) (hMN : M ≤ normalizer (L : Set Q))
    (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* SL(2, ZMod 3))
    {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 3 ^ f) (hf : 1 ≤ f)
    (eL : ↥L ⧸ center ↥L ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) :
    ∀ s ∈ M, (∃ n : ℕ, s ^ 2 ^ n = 1) → s ∈ L ⊔ centralizer (L : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c⟩ := exists_spin_cover hK hf hLq.1 eL
  have hZ4 := spin_center_card hK
  have hZ2 : ∀ z ∈ center (spinGroup (quadPlus 4 K)), z * z = 1 := fun z hz =>
    spin_center_mul_self hK hz
  let τ : ↥(normalizer (L : Set Q)) →* MulAut (spinGroup (quadPlus 4 K)) :=
    { toFun := fun q => c.lift (L.normalizerMonoidHom q)
      map_one' := by rw [map_one, c.lift_one]
      map_mul' := fun a b => by rw [map_mul, c.lift_mul] }
  have hτ : ∀ (q : Q) (hq : q ∈ normalizer (L : Set Q)) (g : spinGroup (quadPlus 4 K)),
      c.θ (τ ⟨q, hq⟩ g) = L.normalizerMonoidHom ⟨q, hq⟩ (c.θ g) := fun q hq g =>
    c.lift_spec _ g
  have hconj : ∀ (q : Q) (hq : q ∈ normalizer (L : Set Q)) (y : spinGroup (quadPlus 4 K)),
      q * ((c.θ y : ↥L) : Q) * q⁻¹ = ((c.θ (τ ⟨q, hq⟩ y) : ↥L) : Q) := fun q hq y => by
    rw [hτ]
    rfl
  let Fix : Subgroup (MulAut (spinGroup (quadPlus 4 K))) :=
    { carrier := {β | ∀ z ∈ center (spinGroup (quadPlus 4 K)), β z = z}
      mul_mem' := fun {a b} ha hb z hz => by
        rw [MulAut.mul_apply, hb z hz, ha z hz]
      one_mem' := fun z _ => rfl
      inv_mem' := fun {a} ha z hz => by
        show a.symm z = z
        rw [MulEquiv.symm_apply_eq, ha z hz] }
  by_cases hodd : ∀ (m : Q) (hm : m ∈ M), Odd (orderOf m) → τ ⟨m, hMN hm⟩ ∈ Fix
  ·
    have hMfix : ∀ (m : Q) (hm : m ∈ M), τ ⟨m, hMN hm⟩ ∈ Fix := by
      have hle : M ≤ (Fix.comap τ).map (normalizer (L : Set Q)).subtype :=
        F3L221.le_of_forall_odd hM fun m hm ho => ⟨⟨m, hMN hm⟩, hodd m hm ho, rfl⟩
      intro m hm
      obtain ⟨q, hq, hqm⟩ := hle hm
      have h1 : q = ⟨m, hMN hm⟩ := Subtype.ext hqm
      rw [← h1]
      exact hq
    have hconj' : ∀ (q : Q) (hq : q ∈ normalizer (L : Set Q)) (y : spinGroup (quadPlus 4 K)),
        q⁻¹ * ((c.θ y : ↥L) : Q) * q = ((c.θ ((τ ⟨q, hq⟩)⁻¹ y) : ↥L) : Q) := by
      intro q hq y
      have h1 := hconj q hq ((τ ⟨q, hq⟩)⁻¹ y)
      rw [MulAut.apply_inv_self] at h1
      rw [← h1]
      group
    have hc : ∀ a ∈ M, ∀ g ∈ M, a * g * a⁻¹ * g⁻¹ ∈ L ⊔ centralizer (L : Set Q) := by
      intro a ha g hg
      obtain ⟨s, hs⟩ := hR1 K f hK (τ ⟨a, hMN ha⟩) (τ ⟨g, hMN hg⟩) (hMfix a ha) (hMfix g hg)
      set l : Q := ((c.θ s : ↥L) : Q) with hl
      have hact : ∀ y ∈ L, (a * g * a⁻¹ * g⁻¹) * y * (a * g * a⁻¹ * g⁻¹)⁻¹ = l * y * l⁻¹ := by
        intro y hy
        obtain ⟨y', hy'⟩ := c.surj ⟨y, hy⟩
        have hyθ : y = ((c.θ y' : ↥L) : Q) := by rw [hy']
        rw [hyθ]
        have h1 : (a * g * a⁻¹ * g⁻¹) * ((c.θ y' : ↥L) : Q) * (a * g * a⁻¹ * g⁻¹)⁻¹ =
            a * (g * (a⁻¹ * (g⁻¹ * ((c.θ y' : ↥L) : Q) * g) * a) * g⁻¹) * a⁻¹ := by group
        rw [h1, hconj' g (hMN hg), hconj' a (hMN ha), hconj g (hMN hg), hconj a (hMN ha)]
        have h2 : τ ⟨a, hMN ha⟩ (τ ⟨g, hMN hg⟩ ((τ ⟨a, hMN ha⟩)⁻¹ ((τ ⟨g, hMN hg⟩)⁻¹ y'))) =
            s * y' * s⁻¹ := by
          have h3 := congrArg (fun β : MulAut (spinGroup (quadPlus 4 K)) => β y') hs
          simp only [MulAut.mul_apply, MulAut.conj_apply] at h3
          exact h3.symm
        rw [h2, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      have hlL : l ∈ L := (c.θ s).2
      have hcz : l⁻¹ * (a * g * a⁻¹ * g⁻¹) ∈ centralizer (L : Set Q) := by
        rw [mem_centralizer_iff]
        intro y hy
        have h1 := hact y hy
        calc y * (l⁻¹ * (a * g * a⁻¹ * g⁻¹)) =
            l⁻¹ * (l * y * l⁻¹) * (a * g * a⁻¹ * g⁻¹) := by group
          _ = l⁻¹ * ((a * g * a⁻¹ * g⁻¹) * y * (a * g * a⁻¹ * g⁻¹)⁻¹) *
              (a * g * a⁻¹ * g⁻¹) := by rw [h1]
          _ = l⁻¹ * (a * g * a⁻¹ * g⁻¹) * y := by group
      have h4 : a * g * a⁻¹ * g⁻¹ = l * (l⁻¹ * (a * g * a⁻¹ * g⁻¹)) := by group
      rw [h4]
      exact mul_mem (mem_sup_left hlL) (mem_sup_right hcz)
    rintro s hs ⟨n, hsn⟩
    exact mem_sup_centralizer_of_commutator hMN e hc hs hsn
  ·
    exfalso
    push Not at hodd
    obtain ⟨m, hm, hmo, hmF⟩ := hodd
    have hmF' : ¬ ∀ z ∈ center (spinGroup (quadPlus 4 K)), τ ⟨m, hMN hm⟩ z = z := hmF
    push Not at hmF'
    obtain ⟨z₁, hz₁, hmz₁⟩ := hmF'
    set α := τ ⟨m, hMN hm⟩ with hαdef
    have hα : ∀ g, c.θ (α g) = L.normalizerMonoidHom ⟨m, hMN hm⟩ (c.θ g) := hτ m (hMN hm)
    have hαk : α ^ orderOf m = 1 := by
      have h1 : (⟨m, hMN hm⟩ : ↥(normalizer (L : Set Q))) ^ orderOf m = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_orderOf_eq_one m)
      rw [hαdef, ← map_pow, h1, map_one]
    have hz₁1 : z₁ ≠ 1 := fun h => hmz₁ (by rw [h, map_one])
    have hsq : ∀ z ∈ center (spinGroup (quadPlus 4 K)), α (α z) = z → α z = z :=
      fun z _ h => apply_eq_of_sq α hmo hαk h
    have hfpf : ∀ z ∈ center (spinGroup (quadPlus 4 K)), α z = z → z = 1 := by
      intro z hz hαz
      by_contra hz1
      have hne : z ≠ z₁ := fun h => hmz₁ (h ▸ hαz)
      have hαz₁ : α z₁ ∈ center (spinGroup (quadPlus 4 K)) := Cover.mem_center_map α hz₁
      rcases mem_klein hZ4 hZ2 hz hz₁ hz1 hz₁1 hne hαz₁ with h | h | h | h
      · exact hz₁1 (α.injective (h.trans (map_one α).symm))
      · exact hne (α.injective (hαz.trans h.symm))
      · exact hmz₁ h
      · apply hmz₁
        apply hsq z₁ hz₁
        rw [h, map_mul, hαz, h, ← mul_assoc, hZ2 z hz, one_mul]
    have hfpf2 : ∀ z ∈ center (spinGroup (quadPlus 4 K)), α (α z) = z → z = 1 :=
      fun z hz h => hfpf z hz (hsq z hz h)
    by_cases hker : ∃ z ∈ center (spinGroup (quadPlus 4 K)), z ≠ 1 ∧ c.θ z = 1
    ·
      obtain ⟨z₂, hz₂, hz₂1, hθz₂⟩ := hker
      have hαz₂ : α z₂ ≠ z₂ := fun h => hz₂1 (hfpf z₂ hz₂ h)
      have hαz₂1 : α z₂ ≠ 1 := fun h => hz₂1 (α.injective (h.trans (map_one α).symm))
      have hθαz₂ : c.θ (α z₂) = 1 := by rw [hα, hθz₂, map_one]
      have hZker : center (spinGroup (quadPlus 4 K)) ≤ c.θ.ker := by
        intro z hz
        rcases mem_klein hZ4 hZ2 hz₂ (Cover.mem_center_map α hz₂) hz₂1 hαz₂1 hαz₂.symm hz with
          h | h | h | h
        · rw [h]
          exact one_mem _
        · rw [h]
          exact hθz₂
        · rw [h]
          exact hθαz₂
        · rw [h, MonoidHom.mem_ker, map_mul, hθz₂, hθαz₂, mul_one]
      obtain ⟨x₀, hx₀⟩ := c.surj ⟨t, htL⟩
      have hmt : m * t = t * m := mem_centralizer_singleton_iff.mp (hM.1 hm)
      have hc₀ : x₀⁻¹ * α x₀ ∈ center (spinGroup (quadPlus 4 K)) := c.ker_le (by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hx₀]
        apply Subtype.ext
        show (t : Q)⁻¹ * (m * t * m⁻¹) = 1
        rw [hmt]
        group)
      have : Finite ↥(center (spinGroup (quadPlus 4 K))) :=
        Nat.finite_of_card_ne_zero (by rw [hZ4]; norm_num)
      let φ : ↥(center (spinGroup (quadPlus 4 K))) →* ↥(center (spinGroup (quadPlus 4 K))) :=
        { toFun := fun z => ⟨(z : spinGroup (quadPlus 4 K)) * α z,
            mul_mem z.2 (Cover.mem_center_map α z.2)⟩
          map_one' := Subtype.ext (by
            show (1 : spinGroup (quadPlus 4 K)) * α 1 = 1
            rw [map_one, one_mul])
          map_mul' := fun a b => Subtype.ext (by
            show ((a : spinGroup (quadPlus 4 K)) * b) * α ((a : spinGroup (quadPlus 4 K)) * b) =
              ((a : spinGroup (quadPlus 4 K)) * α a) * ((b : spinGroup (quadPlus 4 K)) * α b)
            rw [map_mul]
            have h1 :=
              mem_center_iff.mp (Cover.mem_center_map α a.2) (b : spinGroup (quadPlus 4 K))
            calc (a : spinGroup (quadPlus 4 K)) * b * (α a * α b) = a * (b * α a) * α b := by
                  group
              _ = a * (α a * b) * α b := by rw [h1]
              _ = (a : spinGroup (quadPlus 4 K)) * α a *
                  ((b : spinGroup (quadPlus 4 K)) * α b) := by group) }
      have hφ : Function.Injective φ := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro z hz
        have h1 : (z : spinGroup (quadPlus 4 K)) * α z = 1 := by
          have h2 := congrArg Subtype.val hz
          exact h2
        have h2 : α z = z := by
          rw [eq_inv_of_mul_eq_one_right h1]
          exact inv_eq_of_mul_eq_one_right (hZ2 z z.2)
        exact Subtype.ext (hfpf z z.2 h2)
      obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨x₀⁻¹ * α x₀, hc₀⟩
      have hw' : (w : spinGroup (quadPlus 4 K)) * α w = x₀⁻¹ * α x₀ := by
        have h2 := congrArg Subtype.val hw
        exact h2
      set x := x₀ * (w : spinGroup (quadPlus 4 K)) with hxdef
      have hαx : α x = x := by
        rw [hxdef, map_mul]
        have h1 : α x₀ = x₀ * ((w : spinGroup (quadPlus 4 K)) * α w) := by rw [hw']; group
        rw [h1, mul_assoc, mul_assoc, hZ2 _ (Cover.mem_center_map α w.2), mul_one]
      have hxθ : c.θ x = ⟨t, htL⟩ := by rw [hxdef, map_mul, hx₀, hZker w.2, mul_one]
      have hxZ : x ∉ center (spinGroup (quadPlus 4 K)) := by
        intro h
        have h1 : c.θ x = 1 := hZker h
        rw [hxθ] at h1
        have h2 : t = 1 := congrArg Subtype.val h1
        rw [h2, orderOf_one] at ht
        exact absurd ht (by norm_num)
      have hx2 : orderOf x = 2 := by
        have hxx : x * x ∈ center (spinGroup (quadPlus 4 K)) := c.ker_le (by
          rw [MonoidHom.mem_ker, map_mul, hxθ]
          apply Subtype.ext
          show t * t = 1
          rw [← sq, ← ht, pow_orderOf_eq_one])
        have h1 : x * x = 1 := hfpf _ hxx (by rw [map_mul, hαx])
        exact orderOf_eq_prime (by rw [sq]; exact h1) (fun h => hxZ (h ▸ one_mem _))
      obtain ⟨J, hJx, hJiso, hJxz, hJcomm, hJs, hJperm⟩ := hR2 K f hK x hx2 hxZ
      rcases Nat.lt_or_ge f 2 with hf2 | hf2
      ·
        have hf1 : f = 1 := by omega
        have : Fintype K := Fintype.ofFinite K
        have hK3 : Fintype.card K = 3 := by
          rw [← Nat.card_eq_fintype_card, hK, hf1, pow_one]
        obtain ⟨eJ⟩ := hJiso ⟨z₁, hz₁⟩
        have hαz₁ : α z₁ ∈ center (spinGroup (quadPlus 4 K)) := Cover.mem_center_map α hz₁
        exact false_of_sl23 htL hM hMN e (c := c) hZker hxθ hm hmo hα hαx
          (J₂ := J ⟨α z₁, hαz₁⟩) (hJx _) (hJs _) (eJ.trans (slTwoEquivZModThree hK3)) hz₁
          (hJxz _) hxZ (hJperm α ⟨z₁, hz₁⟩ ⟨α z₁, hαz₁⟩ (by
            show α (x * z₁) = x * α z₁
            rw [map_mul, hαx]))
          (hJcomm ⟨z₁, hz₁⟩ ⟨α z₁, hαz₁⟩ (fun h => hmz₁ (congrArg Subtype.val h).symm))
      ·
        have h4 : 4 ≤ Nat.card K := by
          rw [hK]
          calc 4 ≤ 3 ^ 2 := by norm_num
            _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
        obtain ⟨eJ⟩ := hJiso ⟨z₁, hz₁⟩
        exact false_of_component h4 htL hM hMN hxθ hm hα hαx (hJx _) (hJs _) eJ hz₁ (hJxz _) hxZ
          hmz₁
    ·
      push Not at hker
      exact false_of_ker_trivial htL hM hMN e (c := c)
        (fun z hz h => by_contra fun h1 => hker z hz h1 h) hZ2 hm hmo hα hz₁ hmz₁
        (fun h => hz₁1 (hfpf2 z₁ hz₁ h))

end F3D4

namespace F3FG

open F3L225 F3A75 in
theorem fourGroupResidualStepD4_of_inputs (hR1 : Spin8CentreFixedOutAbelian)
    (hR2 : Harris82Lemma413Three) (hθ : Harris82ThetaBalanceThree) :
    FourGroupResidualStepD4 := by
  intro G _ _ _ _ _ _ z₁ z₂ hz₁ hz₂ _ hc L₁ K hL₁ hz₁L₁ _ hK hWN hcomm hz₂K hcat hD
  obtain ⟨f, hD⟩ := hD
  have hD' : StatedClassicalModel (↥K ⧸ Open.fusionZStar ↥K) .POmegaPlus 4 3 f := by
    rcases hD with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num)
  obtain ⟨hadm, F, _, _, hF, ⟨eF⟩⟩ := hD'
  have hf1 : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hz₂K', -⟩ := hz₂K
  set C := centralizer ({z₁} : Set G) with hC
  have hz₂C : z₂ ∈ C := mem_centralizer_singleton_iff.mpr hc.symm
  have hz₁C : z₁ ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hL₁C : L₁ ≤ C := hL₁.1.trans inf_le_left
  have hL₁N : L₁ ≤ normalizer (K : Set G) := hL₁.1.trans hWN
  set t : MBar z₁ := QuotientGroup.mk (⟨z₂, hz₂C⟩ : ↥C) with ht
  obtain ⟨hKc, hKq⟩ := F3L226.isComponentOf_hatIn hK
  have hLs : (hatIn z₁ K).IsSubnormal := F3L226.isSubnormal_of_isComponentOf hKc
  have htL : t ∈ hatIn z₁ K := mk_mem_hatIn hz₂K' hz₂C
  have ht2 : orderOf t = 2 := by
    apply orderOf_mk_mbar_eq_two
    rw [Subgroup.orderOf_mk]
    exact hz₂
  have hM := F3L226.isSolvableTwoComponentIn_hatIn hz₂ hz₂C hL₁
  have hMN : hatIn z₁ L₁ ≤ normalizer ((hatIn z₁ K : Subgroup (MBar z₁)) : Set (MBar z₁)) :=
    F3L226.hatIn_le_normalizer hL₁N
  obtain ⟨eZ⟩ := nonempty_fusionZStar_equiv_hatIn hK
  set z : MBar z₁ := QuotientGroup.mk (⟨z₁, hz₁C⟩ : ↥C) with hz
  have hzM : z ∈ hatIn z₁ L₁ := mk_mem_hatIn hz₁L₁ hz₁C
  have hz2 : orderOf z = 2 := by
    apply orderOf_mk_mbar_eq_two
    rw [Subgroup.orderOf_mk]
    exact hz₁
  have hzc : ∀ k ∈ hatIn z₁ L₁, k * z = z * k := by
    intro k _
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective k
    rw [hz, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp k'.2)
  obtain ⟨e⟩ := F3L221.nonempty_sl23_of_central hM hzM hz2 hzc
  have hinner : ∀ s ∈ hatIn z₁ L₁, (∃ n : ℕ, s ^ 2 ^ n = 1) →
      s ∈ hatIn z₁ K ⊔ centralizer ((hatIn z₁ K : Subgroup (MBar z₁)) : Set (MBar z₁)) :=
    F3D4.mem_sup_centralizer_d4 hR1 hR2 hKq htL ht2 hM hMN e hF hf1 (eZ.symm.trans eF)
  by_contra hnot
  have hnot' : ¬ ∀ s ∈ hatIn z₁ L₁, (∃ n : ℕ, s ^ 2 ^ n = 1) → s ∈ hatIn z₁ K :=
    fun hall => hnot (oPrimeResidualOf_two_le_of_hatIn hK hL₁C hall)
  have h2 : ∀ s ∈ hatIn z₁ L₁, (∃ n : ℕ, s ^ 2 ^ n = 1) →
      ∀ l ∈ hatIn z₁ K, s * l = l * s := by
    rcases mem_or_centralizes htL hM hMN e hzM hz2 hzc hinner with h | h
    · exact absurd h hnot'
    · exact h
  have hθ' := isThetaBalanced_of_mulEquiv eZ (hθ.1 _ hcat)
  have hle := commutator_le_of_centralizes hK hL₁C hL₁N
    (commute_of_three hLs hKq ht2 htL hM hMN h2 hnot' hθ')
  rw [hcomm] at hle
  have hbot : ∀ x : ↥(hatIn z₁ K), x = 1 := by
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    apply Subtype.ext
    have hkK : (k : G) ∈ K := hk
    obtain ⟨k', hk', hk'e⟩ := hle hkK
    have hk'' : (⟨(k : G), hkK⟩ : ↥K) ∈ pPrimeCore 2 ↥K := by
      have h1 : k' = ⟨(k : G), hkK⟩ := Subtype.ext hk'e
      rw [← h1]
      exact hk'
    have h3 := (F3L226.mem_pPrimeCore_iff hK hkK).mp hk''
    show QuotientGroup.mk' (pPrimeCore 2 ↥C) k = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h3
  obtain ⟨a, b, hab⟩ := hKq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [hbot a', hbot b'])

end F3FG

end CFSG.ComponentClassification.HarrisLit.T1
