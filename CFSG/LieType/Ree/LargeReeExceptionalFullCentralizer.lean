module

public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm

public noncomputable section

namespace CFSG.LieType.Ree.ReeTag

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

section General

variable {G H : Type*} [Group G] [Group H]

theorem mulAut_mul_conj_mul_inv (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) :=
  MulEquiv.ext fun x => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem conj_injective_of_center_eq_bot (h : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro g g' e
  have hc : g'⁻¹ * g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun x => by
    have h1 := congrArg (fun α : MulAut G => α x) e
    simp only [MulAut.conj_apply] at h1
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = g'⁻¹ * g * x := by group
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem oddCore_eq_bot_of_mulEquiv (e : G ≃* H) (h : CFSG.oddCore H = ⊥) :
    CFSG.oddCore G = ⊥ := by
  refine sSup_eq_bot.2 fun M hM => ?_
  have hn : (M.map e.toMonoidHom).Normal := hM.1.map _ e.surjective
  have hodd : Odd (Nat.card (M.map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hM.2
  have hle : M.map e.toMonoidHom ≤ CFSG.oddCore H := le_sSup ⟨hn, hodd⟩
  rw [h, le_bot_iff] at hle
  rw [← Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) M e.injective]
  exact hle

end General

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {m : ℕ}

theorem coe_finiteFrobeniusAut_pow
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2) (k : ℕ)
    (g : adjointGroup F4.tag K) :
    ((F4.finiteFrobeniusAut K ^ k) g : ModGL F4.tag K) =
      Units.map (entrywiseHom (σ ^ k).toRingHom) (g : ModGL F4.tag K) := by
  induction k with
  | zero =>
    refine Units.ext ?_
    simp only [pow_zero, MulAut.one_apply, Units.coe_map]
    exact (entrywise_id _).symm
  | succ k ih =>
    refine Units.ext ?_
    rw [pow_succ', MulAut.mul_apply, coe_finiteFrobeniusAut, entrywiseGL, Units.coe_map,
      ih, Units.coe_map, Units.coe_map]
    change entrywise (frobenius K F4.prime) (entrywise (σ ^ k).toRingHom _) =
      entrywise (σ ^ (k + 1)).toRingHom _
    rw [entrywise_entrywise]
    congr 1
    refine RingHom.ext fun c => ?_
    rw [pow_succ', RingHom.comp_apply]
    change (frobenius K F4.prime) ((σ ^ k) c) = σ ((σ ^ k) c)
    rw [hσ, frobenius_def]
    rfl

theorem finiteExceptionalAut_commute_frobenius :
    F4.finiteExceptionalAut K * F4.finiteFrobeniusAut K =
      F4.finiteFrobeniusAut K * F4.finiteExceptionalAut K := by
  rw [← finiteExceptionalAut_mul_self F4, mul_assoc]

theorem fixed_phi_eq_frobenius
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {x : adjointGroup F4.tag K}
    (hx : x ∈ F4.finiteReeFixedGroup K m) :
    F4.finiteExceptionalAut K x = (F4.finiteFrobeniusAut K ^ (m + 1)) x := by
  have hfix : (F4.finiteExceptionalAut K * F4.finiteFrobeniusAut K ^ m) x = x := hx
  have hFr : F4.finiteFrobeniusAut K ^ (2 * m + 1) = 1 :=
    finiteFrobeniusAut_pow_card F4 hK
  have hcomm : ∀ k : ℕ, F4.finiteExceptionalAut K * F4.finiteFrobeniusAut K ^ k =
      F4.finiteFrobeniusAut K ^ k * F4.finiteExceptionalAut K := fun k =>
    ((Commute.pow_right (finiteExceptionalAut_commute_frobenius (K := K)) k)).eq
  have hx' : (F4.finiteExceptionalAut K * F4.finiteFrobeniusAut K ^ m)
      ((F4.finiteFrobeniusAut K ^ (m + 1)) x) = (F4.finiteFrobeniusAut K ^ (m + 1)) x := by
    rw [← MulAut.mul_apply, mul_assoc, ← pow_add, show m + (m + 1) = (m + 1) + m by ring, pow_add,
      ← mul_assoc, hcomm, mul_assoc, MulAut.mul_apply, hfix]
  calc F4.finiteExceptionalAut K x =
      F4.finiteExceptionalAut K ((F4.finiteFrobeniusAut K ^ (2 * m + 1)) x) := by
        rw [hFr, MulAut.one_apply]
    _ = (F4.finiteExceptionalAut K * F4.finiteFrobeniusAut K ^ m)
        ((F4.finiteFrobeniusAut K ^ (m + 1)) x) := by
        rw [show 2 * m + 1 = m + (m + 1) by ring, pow_add, MulAut.mul_apply, MulAut.mul_apply]
    _ = (F4.finiteFrobeniusAut K ^ (m + 1)) x := hx'

theorem phi_mem_finiteReeFixedGroup
    {x : adjointGroup F4.tag K}
    (hx : x ∈ F4.finiteReeFixedGroup K m) :
    F4.finiteExceptionalAut K x ∈ F4.finiteReeFixedGroup K m := by
  have hcomm : F4.finiteExceptionalAut K * F4.finiteFrobeniusAut K ^ m =
      F4.finiteFrobeniusAut K ^ m * F4.finiteExceptionalAut K :=
    ((Commute.pow_right (finiteExceptionalAut_commute_frobenius (K := K)) m)).eq
  have hfix : (F4.finiteExceptionalAut K * F4.finiteFrobeniusAut K ^ m) x = x := hx
  change (F4.finiteExceptionalAut K * F4.finiteFrobeniusAut K ^ m)
    (F4.finiteExceptionalAut K x) = F4.finiteExceptionalAut K x
  rw [show (F4.finiteExceptionalAut K * F4.finiteFrobeniusAut K ^ m)
      (F4.finiteExceptionalAut K x) = ((F4.finiteExceptionalAut K * F4.finiteFrobeniusAut K ^ m) *
        F4.finiteExceptionalAut K) x from rfl, mul_assoc, ← hcomm, MulAut.mul_apply, hfix]

theorem fixed_phi_pow_eq_entrywise
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2) (j : ℕ) {x : adjointGroup F4.tag K}
    (hx : x ∈ F4.finiteReeFixedGroup K m) :
    ((F4.finiteExceptionalAut K ^ j) x : ModGL F4.tag K) =
      Units.map (entrywiseHom (σ ^ ((m + 1) * j)).toRingHom) (x : ModGL F4.tag K) := by
  have key : ∀ j : ℕ, (F4.finiteExceptionalAut K ^ j) x =
      (F4.finiteFrobeniusAut K ^ ((m + 1) * j)) x ∧
      (F4.finiteExceptionalAut K ^ j) x ∈ F4.finiteReeFixedGroup K m := by
    intro j
    induction j with
    | zero => exact ⟨by simp, by simpa using hx⟩
    | succ j ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ', MulAut.mul_apply, fixed_phi_eq_frobenius hK ih.2, ih.1, ← MulAut.mul_apply,
          ← pow_add, show m + 1 + (m + 1) * j = (m + 1) * (j + 1) by ring]
      · rw [pow_succ', MulAut.mul_apply]
        exact phi_mem_finiteReeFixedGroup ih.2
  rw [(key j).1, coe_finiteFrobeniusAut_pow hσ]

end Fixed

theorem even_F4_canonical_exceptional_full_centralizer
    (m : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    (∀ g : adjointGroup F4.tag K, (F4.finiteExceptionalAut K ^ (2 * m + 1)) g = g ↔
      g ∈ F4.finiteReeFixedGroup K m) ∧
    (F4.finiteReeFixedGroup K m).map (adjointGroup F4.tag K).subtype = F4.reeGamma K m ∧
    (∃ e : F4.finiteReeFixedGroup K m ≃* (F4.finiteReeFixedGroup K m).map
        (MulAut.conj : adjointGroup F4.tag K →* MulAut (adjointGroup F4.tag K)),
      ∀ g, (e g : MulAut (adjointGroup F4.tag K)) = MulAut.conj (g : adjointGroup F4.tag K)) ∧
    CFSG.oddCore ((F4.finiteReeFixedGroup K m).map
      (MulAut.conj : adjointGroup F4.tag K →* MulAut (adjointGroup F4.tag K))) = ⊥ ∧
    (∀ α ∈ Subgroup.centralizer {F4.finiteExceptionalAut K ^ (2 * m + 1)},
      ∃! gj : F4.finiteReeFixedGroup K m × Fin (2 * (2 * m + 1)),
        α = MulAut.conj (gj.1 : adjointGroup F4.tag K) * F4.finiteExceptionalAut K ^ (gj.2 : ℕ)) ∧
    (F4.finiteReeFixedGroup K m).map
        (MulAut.conj : adjointGroup F4.tag K →* MulAut (adjointGroup F4.tag K)) ≤
      Subgroup.centralizer {F4.finiteExceptionalAut K ^ (2 * m + 1)} ∧
    (((F4.finiteReeFixedGroup K m).map
        (MulAut.conj : adjointGroup F4.tag K →* MulAut (adjointGroup F4.tag K))).subgroupOf
      (Subgroup.centralizer {F4.finiteExceptionalAut K ^ (2 * m + 1)})).Normal ∧
    Subgroup.centralizer ((F4.finiteReeFixedGroup K m).map
        (MulAut.conj : adjointGroup F4.tag K →* MulAut (adjointGroup F4.tag K)) :
          Set (MulAut (adjointGroup F4.tag K))) ⊓
        Subgroup.centralizer {F4.finiteExceptionalAut K ^ (2 * m + 1)} =
      Subgroup.zpowers (F4.finiteExceptionalAut K ^ (2 * m + 1)) := by
  set C := adjointGroup F4.tag K
  set φ := F4.finiteExceptionalAut K
  set f := 2 * m + 1 with hf
  set η := φ ^ f with hη
  set Γ := F4.finiteReeFixedGroup K m
  set N := Γ.map (MulAut.conj : C →* MulAut C) with hN
  have hf1 : 1 ≤ f := by omega
  have hK' : Nat.card K = 2 ^ f := hK
  obtain ⟨hord, hNF, -, -, -, -, hodd⟩ :=
    CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form hf1 K hK'
  obtain ⟨-, -, hfix⟩ := hodd m rfl
  have hmemΓ : ∀ g : C, η g = g ↔ g ∈ Γ := fun g => (hfix g).symm
  have hinj := conj_injective_of_center_eq_bot (center_adjointGroup_eq_bot (τ := F4.tag) (K := K))
  have hconj : ∀ (α : MulAut C) (g : C), α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) :=
    mulAut_mul_conj_mul_inv
  let e : Γ ≃* N := (Γ.equivMapOfInjective _ hinj)
  have he : ∀ g, (e g : MulAut C) = MulAut.conj (g : C) := fun g => rfl
  have hΓΓ : (Γ.map C.subtype) = F4.reeGamma K m := rfl
  let e' : Γ ≃* F4.reeGamma K m :=
    (Γ.equivMapOfInjective C.subtype Subtype.val_injective).trans (MulEquiv.subgroupCongr hΓΓ)
  have hoddN : CFSG.oddCore N = ⊥ :=
    oddCore_eq_bot_of_mulEquiv (e.symm.trans e')
      (F4_Ree_fixed_group_odd_core_including_field_two m K hK).1
  have hcentη : ∀ (g : C) (k : ℕ), MulAut.conj g * φ ^ k ∈ Subgroup.centralizer {η} ↔ g ∈ Γ := by
    intro g k
    rw [Subgroup.mem_centralizer_singleton_iff, ← hmemΓ]
    have hφη : φ ^ k * η = η * φ ^ k := by rw [hη, ← pow_add, ← pow_add, add_comm]
    constructor
    · intro h
      have h1 : MulAut.conj g * η = η * MulAut.conj g := by
        have h2 : MulAut.conj g * η * φ ^ k = η * MulAut.conj g * φ ^ k := by
          rw [mul_assoc, ← hφη, ← mul_assoc, h, mul_assoc]
        exact mul_right_cancel h2
      have h3 : η * MulAut.conj g * η⁻¹ = MulAut.conj g := by rw [← h1, mul_inv_cancel_right]
      rw [hconj] at h3
      exact hinj h3
    · intro h
      have h3 : η * MulAut.conj g * η⁻¹ = MulAut.conj g := by rw [hconj, h]
      have h1 : MulAut.conj g * η = η * MulAut.conj g := by
        calc MulAut.conj g * η = η * MulAut.conj g * η⁻¹ * η := by rw [h3]
          _ = η * MulAut.conj g := by group
      rw [mul_assoc, hφη, ← mul_assoc, h1, mul_assoc]
  have hexpr : ∀ α ∈ Subgroup.centralizer {η}, ∃! gj : Γ × Fin (2 * f),
      α = MulAut.conj (gj.1 : C) * φ ^ (gj.2 : ℕ) := by
    intro α hα
    obtain ⟨⟨g, k⟩, hgk, huniq⟩ := hNF α
    have hgΓ : g ∈ Γ := (hcentη g k).1 (hgk ▸ hα)
    refine ⟨(⟨g, hgΓ⟩, k), hgk, fun ⟨g', k'⟩ h' => ?_⟩
    have := huniq ((g' : C), k') h'
    simp only [Prod.mk.injEq] at this
    exact Prod.ext (Subtype.ext this.1) this.2
  have hNle : N ≤ Subgroup.centralizer {η} := by
    rintro _ ⟨g, hg, rfl⟩
    have := (hcentη g 0).2 hg
    rwa [pow_zero, mul_one] at this
  have hαΓ : ∀ α ∈ Subgroup.centralizer {η}, ∀ g ∈ Γ, α g ∈ Γ := by
    intro α hα g hg
    rw [← hmemΓ] at hg ⊢
    have h := Subgroup.mem_centralizer_singleton_iff.1 hα
    rw [← MulAut.mul_apply, ← h, MulAut.mul_apply, hg]
  have hNn : (N.subgroupOf (Subgroup.centralizer {η})).Normal := by
    refine ⟨fun n hn α => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨g, hg, hgn⟩ := hn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hgn, hconj]
    exact ⟨_, hαΓ α α.2 g hg, rfl⟩
  have hηN : η ∈ Subgroup.centralizer (N : Set (MulAut C)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hNle ⟨g, hg, rfl⟩)
  have hcent : Subgroup.centralizer (N : Set (MulAut C)) ⊓ Subgroup.centralizer {η} =
      Subgroup.zpowers η := by
    refine le_antisymm (fun α hα => ?_) ?_
    · obtain ⟨hαN, hαη⟩ := Subgroup.mem_inf.1 hα
      obtain ⟨⟨⟨g, hgΓ⟩, k⟩, hgk₀, -⟩ := hexpr α hαη
      obtain ⟨kk, hklt, hgk⟩ : ∃ kk : ℕ, kk < 2 * f ∧ α = MulAut.conj g * φ ^ kk :=
        ⟨k, k.2, hgk₀⟩
      clear hgk₀
      have hfixΓ : ∀ x ∈ Γ, α x = x := by
        intro x hx
        have h := Subgroup.mem_centralizer_iff.1 hαN (MulAut.conj x) ⟨x, hx, rfl⟩
        have h' : α * MulAut.conj x * α⁻¹ = MulAut.conj x := by rw [← h, mul_inv_cancel_right]
        rw [hconj] at h'
        exact hinj h'
      have key : g = 1 ∧ f ∣ kk := by
        rcases Nat.eq_zero_or_pos m with hm0 | hm
        ·
          refine ⟨?_, by rw [show f = 1 by omega]; exact one_dvd kk⟩
          have hφΓ : ∀ x ∈ Γ, φ x = x := fun x hx => by
            have := (hmemΓ x).2 hx
            rwa [hη, hf, hm0, pow_one] at this
          have hg' : ∀ x ∈ Γ, g * x * g⁻¹ = x := by
            intro x hx
            have h1 := hfixΓ x hx
            rw [hgk, MulAut.mul_apply, MulAut.conj_apply] at h1
            have hφk : (φ ^ kk) x = x := by
              clear h1 hklt hgk
              induction kk with
              | zero => rfl
              | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hφΓ x hx]
            rwa [hφk] at h1
          have hc : (⟨(g : ModGL F4.tag K), ⟨g, hgΓ, rfl⟩⟩ : F4.reeGamma K m) ∈
              Subgroup.center (F4.reeGamma K m) := by
            refine Subgroup.mem_center_iff.2 fun y => Subtype.ext ?_
            obtain ⟨x, hx, hxy⟩ := y.2
            have h1 := congrArg Subtype.val (hg' x hx)
            simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
            change (y : ModGL F4.tag K) * g = g * y
            rw [← hxy, Subgroup.coe_subtype]
            calc (x : ModGL F4.tag K) * g = (g : ModGL F4.tag K) * x * (g : ModGL F4.tag K)⁻¹ * g :=
                  by rw [h1]
              _ = g * x := by group
          rw [large_Ree_fixed_group_center_trivial m K hK, Subgroup.mem_bot] at hc
          have hc' := congrArg Subtype.val hc
          exact Subtype.ext hc'
        ·
          obtain ⟨σ, hσ, hσord, -⟩ :=
            CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
              Nat.prime_two hf1 hK'
          set β : K ≃+* K := σ ^ ((m + 1) * kk) with hβ
          set ĝ : F4.reeGamma K m := ⟨(g : ModGL F4.tag K), ⟨g, hgΓ, rfl⟩⟩ with hĝ
          have hψ : MulAut.conj ĝ * F4.reeGammaFieldAut K m β = 1 := by
            refine MulEquiv.ext fun y => Subtype.ext ?_
            obtain ⟨x, hx, hxy⟩ := y.2
            have h1 := congrArg (Subtype.val : C → ModGL F4.tag K) (hfixΓ x hx)
            rw [hgk, MulAut.mul_apply, MulAut.conj_apply] at h1
            simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
            rw [fixed_phi_pow_eq_entrywise hK hσ kk hx] at h1
            rw [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply]
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            rw [coe_reeGammaFieldAut, ← hxy]
            exact h1
          obtain ⟨-, hNFΓ, -⟩ := large_Ree_full_inner_field_automorphism_normal_form m hm K hK
          obtain ⟨p, -, hp⟩ := hNFΓ 1
          have h1 := hp (ĝ, β) hψ.symm
          have h2 := hp (1, 1) (by
            dsimp only
            rw [map_one, one_mul]
            exact ((F4.reeGammaFieldAutHom K m).map_one).symm)
          rw [← h2] at h1
          simp only [Prod.mk.injEq] at h1
          obtain ⟨hg1, hβ1⟩ := h1
          refine ⟨?_, ?_⟩
          · have := congrArg Subtype.val hg1
            exact Subtype.ext this
          · have hdvd : f ∣ (m + 1) * kk := by
              rw [← hσord]
              exact orderOf_dvd_of_pow_eq_one hβ1
            have hcop : Nat.Coprime f (m + 1) := by
              rw [Nat.coprime_iff_gcd_eq_one]
              have h1 : Nat.gcd f (m + 1) ∣ 2 * (m + 1) - f :=
                Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) 2)
                  (Nat.gcd_dvd_left _ _)
              rw [show 2 * (m + 1) - f = 1 by omega] at h1
              exact Nat.dvd_one.1 h1
            exact hcop.dvd_of_dvd_mul_left hdvd
      obtain ⟨hg1, hk⟩ := key
      rw [hgk, hg1, map_one, one_mul]
      have hk' : kk = 0 ∨ kk = f := by
        obtain ⟨d, hd⟩ := hk
        have : d < 2 := by
          by_contra hd2
          rw [not_lt] at hd2
          have : f * 2 ≤ f * d := Nat.mul_le_mul_left f hd2
          omega
        interval_cases d <;> simp [hd]
      rcases hk' with h0 | h0
      · rw [h0, pow_zero]
        exact one_mem _
      · rw [h0]
        exact Subgroup.mem_zpowers η
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.2 ⟨hηN, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  exact ⟨fun g => hmemΓ g, rfl, ⟨e, he⟩, hoddN, hexpr, hNle, hNn, hcent⟩

end CFSG.LieType.Ree.ReeTag
