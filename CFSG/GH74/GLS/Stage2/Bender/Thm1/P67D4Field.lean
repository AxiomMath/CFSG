module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2FieldAux
public import CFSG.GH74.GLS.Stage2.OddAut.FixedCore
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem fixSub_le_fixSub_pow {Y : Type} [Group Y] (α : MulAut Y) (n : ℕ) :
    fixSub α ≤ fixSub (α ^ n) := by
  intro x hx
  rw [mem_fixSub] at hx ⊢
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hx, ih]

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem d4_false_of_field_large {p f r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hr : r.Prime) (hr3 : 3 < r)
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) r V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    (hout : ∃ v ∈ V, v ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) : False := by
  classical
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, hΘker, -⟩, hcyc, hcard, -, hcen, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨-, -, hVe, hVc, -⟩ := id h2
  have := hVe
  obtain ⟨φ, hφV, hφinn⟩ := hout
  have hφ1 : φ ≠ 1 := fun h => hφinn (h ▸ one_mem _)
  have hφr : φ ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian φ hφV
  have hφord : orderOf φ = r := orderOf_eq_prime hφr hφ1
  obtain ⟨hηord, hrf, ⟨g₀, hg₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial hp hf K hK σ hσ Θ hΘ hr
      hr3 ⊤ le_top ⟨φ, Subgroup.mem_top _⟩ hφinn (by rw [Subgroup.orderOf_mk]; exact hφord)
  have hη : orderOf (Θ φ) = r := hηord
  set η : K ≃+* K := Θ φ with hηdef
  obtain ⟨d, hd⟩ : ∃ d, f = d * r := ⟨f / r, (Nat.div_mul_cancel hrf).symm⟩
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, zero_mul] at hd
      omega
    · exact h0
  have hr2 : 2 ≤ r := hr.two_le
  have hm3 : Nat.Coprime r 3 := (Nat.coprime_primes hr Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = p ^ (3 * d * r) := by rw [hK3, hd, mul_assoc]
  have hσ' : ∀ c, σ c = c ^ p ^ (d * r) := fun c => by rw [hσ c, hd]
  set δ : K ≃+* K := iterateFrobeniusEquiv K p (3 * d) with hδdef
  have hδ : ∀ c, δ c = c ^ p ^ (3 * d) := fun c => by
    rw [hδdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, hδord, -, -, -⟩ := triality_canonical_field_facts hp hd1 hr2 hm3 hK' hσ' hδ
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, -, -, -, -, h14, h15⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hp hd1 hr2 hm3 K hK' σ hσ' δ hδ
  have hδpow : δ ^ r = 1 := by rw [← hδord]; exact pow_orderOf_eq_one δ
  have hηpow : η ^ r = 1 := by rw [← hη]; exact pow_orderOf_eq_one η
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have := hcyc
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1
    (mem_zpowers_of_pow_eq_one_of_isCyclic hr.pos hδord hηpow))
  replace hk : δ ^ k = η := hk
  obtain ⟨s, -, hs⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1
    (mem_zpowers_of_pow_eq_one_of_isCyclic hr.pos hη hδpow))
  replace hs : η ^ s = δ := hs
  set α₀ : MulAut C := fieldActor σ δ with hα₀
  set φ' : MulAut C := fieldActor σ η with hφ'
  have hφ'α : φ' = α₀ ^ k := by
    rw [hφ', hα₀, ← hk]
    exact map_pow (fieldActorHom (t := TwistTag.D4) σ) δ k
  have hαφ' : α₀ = φ' ^ s := by
    rw [hα₀, hφ', ← hs]
    exact map_pow (fieldActorHom (t := TwistTag.D4) σ) η s
  have hfix : fixSub φ' = fixSub α₀ :=
    le_antisymm (hαφ' ▸ fixSub_le_fixSub_pow φ' s) (hφ'α ▸ fixSub_le_fixSub_pow α₀ k)
  have hg₀' : MulAut.conj g₀ * φ * (MulAut.conj g₀)⁻¹ = φ' := hg₀
  have hJna : ∀ N : Subgroup ↥(trialityFieldImage σ δ), N.Normal →
      (∀ x y : N, x * y = y * x) → N = ⊥ := by
    intro N hN hc
    have := hN
    rcases h8.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      apply h9
      intro a b
      have ha : a ∈ N := h ▸ Subgroup.mem_top a
      have hb : b ∈ N := h ▸ Subgroup.mem_top b
      exact congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩)
  have hJeq : (fixSub α₀).map C.subtype = trialityFieldImage σ δ := h7
  obtain ⟨e₁⟩ := fixSub_conj_equiv φ (MulAut.conj g₀)
  have hconj_fix : fixSub (MulAut.conj g₀ * φ * (MulAut.conj g₀)⁻¹) = fixSub α₀ := by
    rw [hg₀']
    exact hfix
  let e₂ : ↥(fixSub α₀) ≃* ↥(trialityFieldImage σ δ) :=
    (Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hJeq)
  have hA : ∀ F₀ : Subgroup ↥(fixSub φ), F₀.Normal → (∀ x y : F₀, x * y = y * x) → F₀ = ⊥ := by
    have e : ↥(fixSub φ) ≃* ↥(trialityFieldImage σ δ) :=
      e₁.trans ((MulEquiv.subgroupCongr hconj_fix).trans e₂)
    exact noAbelNormal_of_equiv e hJna
  have hB : ∀ ζ : MulAut C, Odd (orderOf ζ) → Nat.Coprime (orderOf ζ) r → ζ * φ = φ * ζ →
      (∀ c ∈ fixSub φ, ζ c = c) → ζ = 1 := by
    intro ζ hζodd hζcop hζφ hζfix
    set δc : MulAut C := MulAut.conj g₀ with hδc
    set ζ' : MulAut C := δc * ζ * δc⁻¹ with hζ'
    have hord : orderOf ζ' = orderOf ζ := by
      have := MulEquiv.orderOf_eq (MulAut.conj δc) ζ
      rwa [MulAut.conj_apply] at this
    have hcomm : ζ' * φ' = φ' * ζ' := by
      rw [← hg₀']
      calc δc * ζ * δc⁻¹ * (δc * φ * δc⁻¹) = δc * (ζ * φ) * δc⁻¹ := by group
        _ = δc * (φ * ζ) * δc⁻¹ := by rw [hζφ]
        _ = δc * φ * δc⁻¹ * (δc * ζ * δc⁻¹) := by group
    have hfixΦ : ∀ y : C, φ' y = y → ζ' y = y := by
      intro y hy
      have hδy : φ (δc⁻¹ y) = δc⁻¹ y := by
        have h1 : (δc * φ * δc⁻¹) y = y := by rw [hg₀']; exact hy
        simp only [MulAut.mul_apply] at h1
        have h2' : δc⁻¹ (δc (φ (δc⁻¹ y))) = δc⁻¹ y := by rw [h1]
        rwa [MulAut.inv_apply_self] at h2'
      have hζx := hζfix (δc⁻¹ y) hδy
      simp only [hζ', MulAut.mul_apply]
      rw [hζx, MulAut.apply_inv_self]
    have hfixJ : ∀ j : C, (j : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ → ζ' j = j := by
      intro j hj
      have hjα : j ∈ fixSub α₀ := by
        have h1 : (j : ModGL TwistTag.D4.tag K) ∈ (fixSub α₀).map C.subtype := hJeq ▸ hj
        obtain ⟨y, hy, hyj⟩ := h1
        have : y = j := Subtype.ext hyj
        exact this ▸ hy
      exact hfixΦ j (mem_fixSub.1 (hfix ▸ hjα))
    have hcommα : ζ' * α₀ = α₀ * ζ' := by
      rw [hαφ']
      exact (Commute.pow_right (show Commute ζ' φ' from hcomm) s).eq
    have hmem : ζ' ∈ Subgroup.centralizer {α₀} ⊓
        Subgroup.centralizer (trialityFieldInner σ δ : Set (MulAut C)) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 ?_,
        Subgroup.mem_centralizer_iff.2 ?_⟩
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hcommα.symm
      · intro n hn
        obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hn
        have hj' : (j : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ := hj
        have h1 := mulAut_conj_conj ζ' (j : C)
        rw [hfixJ j hj'] at h1
        have h2' : ζ' * MulAut.conj (j : C) = MulAut.conj (j : C) * ζ' := by
          calc ζ' * MulAut.conj (j : C) = (ζ' * MulAut.conj (j : C) * ζ'⁻¹) * ζ' := by group
            _ = MulAut.conj (j : C) * ζ' := by rw [h1]
        exact h2'.symm
    rw [h14] at hmem
    have hζ'r : ζ' ^ r = 1 := by
      have h1 : (⟨ζ', hmem⟩ : ↥(Subgroup.zpowers α₀)) ^ Nat.card ↥(Subgroup.zpowers α₀) = 1 :=
        pow_card_eq_one'
      rw [h15] at h1
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val h1
    have hζ'1 : ζ' = 1 := by
      have hdvd : orderOf ζ' ∣ r := orderOf_dvd_of_pow_eq_one hζ'r
      have hcop' : Nat.Coprime (orderOf ζ') r := by rw [hord]; exact hζcop
      exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop' hdvd)
    have h3' : ζ = δc⁻¹ * ζ' * δc := by rw [hζ']; group
    rw [h3', hζ'1]
    group
  exact false_of_fixed_core hcen h2 h3 hφV hφ1 hA hB

end CFSG.GH74.GLS.Stage2.Bender.Thm1
