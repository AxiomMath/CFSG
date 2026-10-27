module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureCases
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureTools
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocksBase
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocksConj
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocksSign
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocksOrder
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocksWreath

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks

variable {k p m : ℕ}

private theorem exists_smul_of_zpowers_eq [NeZero p] {f f' : Fin k → ZMod p}
    {A : Type} [Group A] (ι : A →* Equiv.Perm (Ω k p m)) (hι : Function.Injective ι) {a a' : A}
    (ha : ι a = baseHom (Multiplicative.ofAdd f)) (ha' : ι a' = baseHom (Multiplicative.ofAdd f'))
    (h : a' ∈ Subgroup.zpowers a) : ∃ c : ℤ, f' = c • f := by
  obtain ⟨c, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  refine ⟨c, ?_⟩
  have h1 : baseHom (m := m) (Multiplicative.ofAdd f') =
      baseHom (m := m) (Multiplicative.ofAdd (c • f)) := by
    rw [← ha', map_zpow, ha, ← map_zpow]
    rfl
  exact congrArg Multiplicative.toAdd (baseHom_injective h1)

private theorem zmod_three_aux : ∀ t d : ZMod 3, t = d ^ 2 → t ≠ 1 → t ≠ 0 → False := by
  decide

private theorem exists_move [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k)
    {f : Fin k → ZMod p}
    (hf : f ≠ 0) :
    ∃ (π : Equiv.Perm (Fin k × ZMod p)) (f' : Fin k → ZMod p), Equiv.Perm.sign π = 1 ∧
      π * transl f * π⁻¹ = transl f' ∧ ∀ c : ℤ, f' ≠ c • f := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨r, hr⟩ := exists_sign_scale_eq_neg_one hp hp2 (⟨0, by omega⟩ : Fin k)
  by_cases hz : ∃ i, f i = 0
  ·
    obtain ⟨i, hi⟩ := hz
    obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by
      by_contra h
      push Not at h
      exact hf (funext h)
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    obtain ⟨s, hs⟩ := exists_sign_scale_eq_neg_one hp hp2 j
    let f₁ : Fin k → ZMod p := fun l => if l = j then (s : ZMod p) * f l else f l
    refine ⟨swapB i j * scale j s, f₁ ∘ Equiv.swap i j, ?_, ?_, ?_⟩
    · rw [map_mul, sign_swapB hpo hij, hs]
      rfl
    · rw [mul_inv_rev, show swapB i j * scale j s * transl f * ((scale j s)⁻¹ * (swapB i j)⁻¹) =
          swapB i j * (scale j s * transl f * (scale j s)⁻¹) * (swapB i j)⁻¹ by group,
        scale_mul_transl_mul_inv, swapB_mul_transl_mul_inv]
    · intro c hc
      have h1 := congrFun hc i
      simp only [Function.comp_apply, Equiv.swap_apply_left, f₁, if_pos rfl, Pi.smul_apply,
        hi, smul_zero] at h1
      exact mul_ne_zero s.ne_zero hj h1
  · push Not at hz
    let i₀ : Fin k := ⟨0, by omega⟩
    let i₁ : Fin k := ⟨1, by omega⟩
    have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    by_cases hp3 : p = 3
    ·
      subst hp3
      have hr1 : (r : ZMod 3) ≠ 1 := by
        intro h1
        have : r = 1 := Units.ext h1
        rw [this] at hr
        have h2 : scale (p := 3) i₀ 1 = 1 := by
          ext x <;> simp [scale_apply]
        rw [h2, map_one] at hr
        exact absurd hr (by decide)
      let f₁ : Fin k → ZMod 3 := fun l => if l = i₀ then (r : ZMod 3) * f l else f l
      refine ⟨swapB i₀ i₁ * scale i₀ r, f₁ ∘ Equiv.swap i₀ i₁, ?_, ?_, ?_⟩
      · rw [map_mul, sign_swapB (by decide) h01, hr]
        rfl
      · rw [mul_inv_rev, show swapB i₀ i₁ * scale i₀ r * transl f * ((scale i₀ r)⁻¹ *
            (swapB i₀ i₁)⁻¹) = swapB i₀ i₁ * (scale i₀ r * transl f * (scale i₀ r)⁻¹) *
            (swapB i₀ i₁)⁻¹ by group, scale_mul_transl_mul_inv, swapB_mul_transl_mul_inv]
      · intro c hc
        have h0 := congrFun hc i₀
        have h1 := congrFun hc i₁
        simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, f₁,
          Pi.smul_apply, zsmul_eq_mul, if_neg h01.symm, if_pos rfl, ↓reduceIte] at h0 h1
        have hf0 := hz i₀
        have hc2 : (r : ZMod 3) = (c : ZMod 3) ^ 2 := by
          have : (r : ZMod 3) * f i₀ = ((c : ZMod 3) ^ 2) * f i₀ := by
            rw [h1, h0]; ring
          exact mul_right_cancel₀ hf0 this
        exact zmod_three_aux _ _ hc2 hr1 r.ne_zero
    ·
      have h2 : (2 : ZMod p) ≠ 0 := by
        intro h
        have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
      let u : (ZMod p)ˣ := Units.mk0 2 h2
      have hu : (u : ZMod p) * u ≠ 1 := by
        intro h
        have h3 : ((3 : ℕ) : ZMod p) = 0 := by
          have : (2 : ZMod p) * 2 = 1 := h
          push_cast
          linear_combination this
        have := (ZMod.natCast_eq_zero_iff 3 p).1 h3
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this
        exact hp3 this
      let f₁ : Fin k → ZMod p := fun l => if l = i₁ then ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * f l else f l
      refine ⟨scale i₀ u * scale i₁ u⁻¹,
        fun l => if l = i₀ then (u : ZMod p) * f₁ l else f₁ l, ?_, ?_, ?_⟩
      · rw [map_mul, sign_scale_eq, sign_scale_eq, ← map_mul,
          show Units.mulLeft u⁻¹ = (Units.mulLeft u : Equiv.Perm (ZMod p))⁻¹ from
            (Units.mulLeft_symm u).symm, mul_inv_cancel, map_one]
      · rw [mul_inv_rev, show scale i₀ u * scale i₁ u⁻¹ * transl f * ((scale i₁ u⁻¹)⁻¹ *
            (scale i₀ u)⁻¹) = scale i₀ u * (scale i₁ u⁻¹ * transl f * (scale i₁ u⁻¹)⁻¹) *
            (scale i₀ u)⁻¹ by group, scale_mul_transl_mul_inv, scale_mul_transl_mul_inv]
      · intro c hc
        have h0 : (u : ZMod p) * f i₀ = (c : ZMod p) * f i₀ := by
          have h := congrFun hc i₀
          rw [Pi.smul_apply, zsmul_eq_mul] at h
          rw [← h]
          show (u : ZMod p) * f i₀ = if i₀ = i₀ then (u : ZMod p) * f₁ i₀ else f₁ i₀
          rw [if_pos rfl]
          show (u : ZMod p) * f i₀ = (u : ZMod p) * (if i₀ = i₁ then _ else f i₀)
          rw [if_neg h01]
        have h1 : ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * f i₁ = (c : ZMod p) * f i₁ := by
          have h := congrFun hc i₁
          rw [Pi.smul_apply, zsmul_eq_mul] at h
          rw [← h]
          show ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * f i₁ = if i₁ = i₀ then (u : ZMod p) * f₁ i₁ else f₁ i₁
          rw [if_neg h01.symm]
          show ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * f i₁ = if i₁ = i₁ then _ else f i₁
          rw [if_pos rfl]
        have hc0 : (c : ZMod p) = u := (mul_right_cancel₀ (hz i₀) h0).symm
        have hc1 : (c : ZMod p) = ((u⁻¹ : (ZMod p)ˣ) : ZMod p) :=
          (mul_right_cancel₀ (hz i₁) h1).symm
        apply hu
        calc (u : ZMod p) * u = (u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by rw [← hc0, hc1]
          _ = 1 := Units.mul_inv u

private theorem wcOn_block [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) (hkp : k < p)
    (hm : m < p) :
    WCOn p (alternatingGroup (Ω k p m)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpo : Odd p := hp.odd_of_ne_two hp2
  set Alt := alternatingGroup (Ω k p m)
  have hle : base (k := k) (p := p) (m := m) ≤ Alt := base_le_alternatingGroup hpo
  have hn : k * p + m < p ^ 2 := by nlinarith
  have hn2 : 2 ≤ k * p + m := by nlinarith [hp.two_le]
  have e : Fin (k * p + m) ≃ Ω k p m :=
    (Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, card_Ω])).symm
  have hfac : (Nat.card Alt).factorization p = k := by
    rw [← Nat.card_congr (Equiv.altCongrHom e).toEquiv,
      factorization_card_alternatingGroup_fin hp hp2 hn2 hn]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp.pos, Nat.div_eq_of_lt hm, zero_add]
  have hcard : Nat.card ((base (k := k) (p := p) (m := m)).subgroupOf Alt) =
      p ^ (Nat.card Alt).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_base, hfac]
  let P₀ : Sylow p Alt := Sylow.ofCard _ hcard
  have hP₀ : (P₀ : Subgroup Alt) = (base (k := k) (p := p) (m := m)).subgroupOf Alt :=
    Sylow.coe_ofCard _ _
  refine WCOn.of_sylow P₀ fun _ _ A hAP hA => ?_
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    push Not at h
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    rw [this, Subgroup.card_bot] at hA
    exact hp.one_lt.ne hA
  have hAz : A = Subgroup.zpowers a := by
    have hle' : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).2 haA
    have hord : orderOf a = p := by
      have h1 : orderOf a ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A haA
      rw [hA] at h1
      rcases (Nat.dvd_prime hp).1 h1 with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) ha1
      · exact h
    symm
    apply Subgroup.eq_of_le_of_card_ge hle'
    rw [hA, Nat.card_zpowers, hord]
  have haB : (a : Equiv.Perm (Ω k p m)) ∈ base (k := k) (p := p) (m := m) := by
    have := hAP haA
    rw [hP₀, Subgroup.mem_subgroupOf] at this
    exact this
  obtain ⟨F, hF⟩ := haB
  set f := Multiplicative.toAdd F
  have hF' : baseHom (m := m) (Multiplicative.ofAdd f) = (a : Equiv.Perm (Ω k p m)) := hF
  have hf : f ≠ 0 := by
    intro h0
    apply ha1
    apply Subtype.ext
    rw [← hF]
    show baseHom F = 1
    rw [show F = 1 from congrArg Multiplicative.ofAdd h0, map_one]
  obtain ⟨π, f', hπs, hπ, hf'⟩ := exists_move hp hp2 hk hf
  have hπA : blockPerm (m := m) π ∈ Alt := by
    rw [Equiv.Perm.mem_alternatingGroup, sign_blockPerm, hπs]
  let g : Alt := ⟨blockPerm π, hπA⟩
  have hga : ((g * a * g⁻¹ : Alt) : Equiv.Perm (Ω k p m)) =
      baseHom (Multiplicative.ofAdd f') := by
    have h1 := blockPerm_mul_baseHom_mul_inv (m := m) π f f' hπ
    rw [← h1, hF']
    rfl
  refine ⟨g, ?_, fun heq => ?_⟩
  · rw [hAz, MonoidHom.map_zpowers, Subgroup.zpowers_le]
    show g * a * g⁻¹ ∈ (P₀ : Subgroup Alt)
    rw [hP₀, Subgroup.mem_subgroupOf, hga]
    exact ⟨_, rfl⟩
  · have hmem : g * a * g⁻¹ ∈ Subgroup.zpowers a := by
      rw [← hAz, ← heq, hAz, MonoidHom.map_zpowers]
      exact Subgroup.mem_zpowers _
    obtain ⟨c, hc⟩ := exists_smul_of_zpowers_eq (f := f) (f' := f') Alt.subtype
      Subtype.val_injective (a := a) (a' := g * a * g⁻¹) hF'.symm hga hmem
    exact hf' c hc

theorem wcAlt_holds : WCAlt := by
  intro n hn5 p hp hp2
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hsq : p ^ 2 ≤ n
  · intro P hPab
    exact absurd hPab (not_isMulCommutative_sylow_alternatingGroup hp hp2 hsq P)
  push Not at hsq
  by_cases hk : n / p ≤ 1
  · intro P _ hrank
    exfalso
    have hn2p : n < 2 * p := by
      by_contra h
      push Not at h
      have : 2 ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).2 (by linarith)
      omega
    have hfac := factorization_card_alternatingGroup_le_one_of_lt hp hp2 (by omega) hn2p
    have hcardP : Nat.card (P : Subgroup (alternatingGroup (Fin n))) ≤ p ^ 1 := by
      rw [P.card_eq_multiplicity]
      exact Nat.pow_le_pow_right hp.pos hfac
    have := pRank_le_of_card_le hp hcardP
    omega
  · push Not at hk
    have hkp : n / p < p := by
      rw [Nat.div_lt_iff_lt_mul hp.pos]
      nlinarith
    have hm : n % p < p := Nat.mod_lt _ hp.pos
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have e : Fin n ≃ Ω (n / p) p (n % p) :=
      (Fintype.equivFinOfCardEq (by
        rw [← Nat.card_eq_fintype_card, card_Ω, mul_comm, Nat.div_add_mod])).symm
    exact WCOn.of_mulEquiv (Equiv.altCongrHom e) (wcOn_block hp hp2 hk hkp hm)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
