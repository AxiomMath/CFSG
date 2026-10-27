module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

variable {K : Type*} [Group K]

@[expose] def GFR3Good (K : Type*) [Group K] (s : K) : Prop :=
  GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set K)) = ⊥ ∧
    ∀ σ : MulAut K, σ ^ 2 = 1 → σ ∉ innerAut K → ∃ t : K, s * t = t * s ∧ σ t ≠ t

theorem gfr3_good_conj {s : K} (h : GFR3Good K s) (g : K) : GFR3Good K (g * s * g⁻¹) := by
  refine ⟨?_, ?_⟩
  · have hψ : Function.Injective (MulAut.conj g : K ≃* K).toMonoidHom :=
      (MulAut.conj g : K ≃* K).injective
    have hmap := map_glaPPrimeCoreOf_of_injective 3 (MulAut.conj g : K ≃* K).toMonoidHom hψ
      (Subgroup.centralizer ({s} : Set K))
    have hc := map_inf_centralizer_of_injective (MulAut.conj g : K ≃* K).toMonoidHom hψ ⊤ s
    rw [top_inf_eq, Subgroup.map_top_of_surjective _ (MulAut.conj g : K ≃* K).surjective,
      top_inf_eq] at hc
    rw [hc, h.1, Subgroup.map_bot] at hmap
    have hs : (MulAut.conj g : K ≃* K).toMonoidHom s = g * s * g⁻¹ := by
      simp [MulAut.conj_apply]
    rw [hs] at hmap
    exact hmap.symm
  · intro σ hσ2 hσi
    set c : MulAut K := MulAut.conj g with hc
    have hcI : c ∈ innerAut K := ⟨g, rfl⟩
    have hσ'2 : (c⁻¹ * σ * c) ^ 2 = 1 := by
      have : (c⁻¹ * σ * c) ^ 2 = c⁻¹ * σ ^ 2 * c := by
        rw [sq, sq]
        group
      rw [this, hσ2]
      group
    have hσ'i : c⁻¹ * σ * c ∉ innerAut K := by
      intro hin
      apply hσi
      have h1 : c * (c⁻¹ * σ * c) * c⁻¹ ∈ innerAut K :=
        (innerAut K).mul_mem ((innerAut K).mul_mem hcI hin) ((innerAut K).inv_mem hcI)
      have h2 : c * (c⁻¹ * σ * c) * c⁻¹ = σ := by group
      rwa [h2] at h1
    obtain ⟨t, hst, hσt⟩ := h.2 _ hσ'2 hσ'i
    refine ⟨g * t * g⁻¹, ?_, ?_⟩
    · calc g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
        _ = g * (t * s) * g⁻¹ := by rw [hst]
        _ = g * t * g⁻¹ * (g * s * g⁻¹) := by group
    · intro hfix
      apply hσt
      have h3 : (c⁻¹ * σ * c) t = c⁻¹ (σ (c t)) := rfl
      have h4 : c t = g * t * g⁻¹ := by rw [hc, MulAut.conj_apply]
      rw [h3, h4, hfix, ← h4]
      exact (MulAut.inv_apply_self K c t)

theorem gfr3_good_of_inner (hall : ∀ α : MulAut K, α ∈ innerAut K) {s : K}
    (h : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set K)) = ⊥) : GFR3Good K s :=
  ⟨h, fun σ _ hσ => absurd (hall σ) hσ⟩

theorem gfr3_card_outer_le_two_of_inner (hall : ∀ α : MulAut K, α ∈ innerAut K) :
    Nat.card (Outer K) ≤ 2 := by
  have : Subsingleton (Outer K) := by
    refine ⟨fun p q => ?_⟩
    induction p using QuotientGroup.induction_on with
    | H α =>
      induction q using QuotientGroup.induction_on with
      | H β =>
        rw [QuotientGroup.eq]
        exact hall _
  rw [Nat.card_unique]
  norm_num

variable {p : ℕ}

theorem gfr3_oneBalanced_at [Finite K] (hp : p.Prime) (hcen : Subgroup.center K = ⊥)
    (hout : Nat.card (Outer K) ≤ 2) {s : K}
    (h1 : GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set K)) = ⊥)
    (h2 : ∀ σ : MulAut K, σ ^ 2 = 1 → σ ∉ innerAut K → ∃ t : K, s * t = t * s ∧ σ t ≠ t)
    (H : Subgroup (MulAut K)) (hH : innerAut K ≤ H) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K))) = ⊥ := by
  have hψ : Function.Injective (MulAut.conj : K →* MulAut K) :=
    conj_injective_of_center_eq_bot hcen
  let q : MulAut K →* Outer K := QuotientGroup.mk' (inner K)
  have hqker : ∀ y : MulAut K, q y = 1 ↔ y ∈ innerAut K := fun y =>
    QuotientGroup.eq_one_iff y
  have hsq : ∀ y : MulAut K, (q y) ^ 2 = 1 := by
    intro y
    have hc : (q y) ^ Nat.card (Outer K) = 1 := pow_card_eq_one'
    have hpos : 0 < Nat.card (Outer K) := Nat.card_pos
    interval_cases hn : Nat.card (Outer K)
    · have : q y = 1 := by simpa using hc
      rw [this, one_pow]
    · exact hc
  set A : Subgroup (MulAut K) := H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K))
    with hA
  set N := GLAPPrimeCoreOf p A with hN
  have hNA : N ≤ A := GLAPPrimeCoreOf_le A
  have hNinn : N ⊓ innerAut K = ⊥ := by
    set B : Subgroup (MulAut K) :=
      innerAut K ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K)) with hB
    have hBA : B ≤ A := inf_le_inf hH le_rfl
    have hOB : GLAPPrimeCoreOf p B = ⊥ := by
      have hmap := map_glaPPrimeCoreOf_of_injective p (MulAut.conj : K →* MulAut K) hψ
        (Subgroup.centralizer ({s} : Set K))
      have hc := map_inf_centralizer_of_injective (MulAut.conj : K →* MulAut K) hψ ⊤ s
      rw [top_inf_eq] at hc
      have hrange : (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) = innerAut K :=
        MonoidHom.range_eq_map _ |>.symm
      rw [hrange] at hc
      rw [h1, Subgroup.map_bot, hc] at hmap
      exact hmap.symm
    rw [eq_bot_iff, ← hOB]
    refine le_GLAPPrimeCoreOf_of_normal (fun y hy => ⟨hy.2, (hNA hy.1).2⟩) ?_ ?_
    · intro g hg y hy
      have hgA := hBA hg
      refine ⟨GLAPPrimeCoreOf_conj_mem g hgA y hy.1, ?_⟩
      exact (inner_normal K).conj_mem y hy.2 g
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_GLAPPrimeCoreOf hp A)
  rw [eq_bot_iff]
  intro σ hσ
  by_contra hσ1
  have hσ1' : σ ≠ 1 := by simpa using hσ1
  have hσinn : σ ∉ innerAut K := fun hi => hσ1 (by
    have : σ ∈ N ⊓ innerAut K := ⟨hσ, hi⟩
    rw [hNinn] at this
    exact this)
  have hqσ : q σ ≠ 1 := fun e => hσinn ((hqker σ).1 e)
  have hσ2 : σ ^ 2 = 1 := by
    have hmem : σ ^ 2 ∈ N ⊓ innerAut K := by
      refine ⟨N.pow_mem hσ 2, (hqker _).1 ?_⟩
      rw [map_pow]
      exact hsq σ
    rw [hNinn] at hmem
    exact hmem
  obtain ⟨t, hts, hσt⟩ := h2 σ hσ2 hσinn
  have hcomm_out : ∀ a : MulAut K, q a * q σ = q σ * q a := by
    intro a
    by_cases ha : q a = 1
    · rw [ha, one_mul, mul_one]
    · rw [eq_of_ne_one_of_card_le_two hout ha hqσ]
  have ht : MulAut.conj t ∈ A := by
    refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh, ← map_mul, ← map_mul, hts]
  have hcent : MulAut.conj t * σ * (MulAut.conj t)⁻¹ = σ := by
    have hmem : MulAut.conj t * σ * (MulAut.conj t)⁻¹ * σ⁻¹ ∈ N ⊓ innerAut K := by
      refine ⟨N.mul_mem (GLAPPrimeCoreOf_conj_mem _ ht σ hσ) (N.inv_mem hσ), (hqker _).1 ?_⟩
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have := hcomm_out (MulAut.conj t)
      calc q (MulAut.conj t) * q σ * (q (MulAut.conj t))⁻¹ * (q σ)⁻¹
          = (q σ * q (MulAut.conj t)) * (q (MulAut.conj t))⁻¹ * (q σ)⁻¹ := by rw [this]
        _ = 1 := by group
    rw [hNinn] at hmem
    have h1' : MulAut.conj t * σ * (MulAut.conj t)⁻¹ * σ⁻¹ = 1 := hmem
    exact mul_inv_eq_one.1 h1'
  have hc2 : σ * MulAut.conj t * σ⁻¹ = MulAut.conj t := by
    have h3 : MulAut.conj t * σ = σ * MulAut.conj t := by
      have := congrArg (fun y => y * MulAut.conj t) hcent
      simpa [mul_assoc] using this
    rw [← h3]
    group
  rw [mulAut_mul_conj_mul_inv] at hc2
  exact hσt (hψ hc2)

theorem gfr3_comap (hcen : Subgroup.center K = ⊥) {D : Subgroup (MulAut K)} (hDi : D ≤ inner K)
    (hD : IsElemAbelian p D) :
    IsElemAbelian p (D.comap (MulAut.conj : K →* MulAut K)) ∧
      Nat.card (D.comap (MulAut.conj : K →* MulAut K)) = Nat.card D := by
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    conj_injective_of_center_eq_bot hcen
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply hinj
    have hab := hD.1.is_comm.comm (⟨MulAut.conj (a : K), a.2⟩ : D) ⟨MulAut.conj (b : K), b.2⟩
    have := congrArg Subtype.val hab
    simpa only [Subgroup.coe_mul, map_mul] using this
  · apply hinj
    rw [map_pow, map_one]
    exact hD.2 _ hx
  · have hmap : (D.comap (MulAut.conj : K →* MulAut K)).map (MulAut.conj : K →* MulAut K) = D := by
      rw [Subgroup.map_comap_eq, inf_eq_right]
      exact hDi
    rw [← Subgroup.card_map_of_injective hinj, hmap]

theorem gfr3_locallyBalanced_of_good [Finite K] (hcen : Subgroup.center K = ⊥)
    (hout : Nat.card (Outer K) ≤ 2)
    (hgood : ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      ∃ s ∈ E, orderOf s = 3 ∧ GFR3Good K s) :
    IsLocallyBalancedAbs 3 2 K := by
  intro D hD hcard H hH _
  have hp : Nat.Prime 3 := Nat.prime_three
  have hcop : Nat.Coprime 3 (Nat.card (Outer K)) :=
    coprime_of_le_two hp (by norm_num) Nat.card_pos.ne' hout
  have hDp : IsPGroup 3 D := fun d => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hD.2 d d.2)⟩
  have hDi : D ≤ inner K := le_inner_of_isPGroup hcop hDp
  obtain ⟨hE, hEc⟩ := gfr3_comap hcen hDi hD
  obtain ⟨s, hsE, hs3, hsg⟩ := hgood _ hE (hEc.trans hcard)
  have hψ : Function.Injective (MulAut.conj : K →* MulAut K) :=
    conj_injective_of_center_eq_bot hcen
  have hsD : (MulAut.conj s : MulAut K) ∈ D := hsE
  have hs1 : s ≠ 1 := fun h => by
    rw [h, orderOf_one] at hs3
    exact absurd hs3 (by norm_num)
  have hd1 : (MulAut.conj s : MulAut K) ≠ 1 := fun h => hs1 (hψ (by rw [h, map_one]))
  rw [eq_bot_iff]
  calc localDeltaIn 3 H D
      ≤ GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K))) :=
        iInf₂_le_of_le (MulAut.conj s) hsD (iInf_le_of_le hd1 le_rfl)
    _ = ⊥ := gfr3_oneBalanced_at hp hcen hout hsg.1 hsg.2 H hH
    _ ≤ ⊥ := le_rfl

theorem gfr3_comm_sup {E : Subgroup K} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {s : K}
    (hs : ∀ e ∈ E, s * e = e * s) : ∀ a ∈ E ⊔ Subgroup.zpowers s, ∀ b ∈ E ⊔ Subgroup.zpowers s,
      a * b = b * a := by
  have h1 : ∀ e ∈ E, ∀ a ∈ E ⊔ Subgroup.zpowers s, e * a = a * e := by
    intro e he a ha
    have : E ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer ({e} : Set K) := by
      refine sup_le (fun x hx => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hE e he x hx).symm
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.2 (hs e he)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (this ha)).symm
  have h2 : ∀ a ∈ E ⊔ Subgroup.zpowers s, s * a = a * s := by
    intro a ha
    have : E ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer ({s} : Set K) := by
      refine sup_le (fun x hx => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hs x hx).symm
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    exact (Subgroup.mem_centralizer_singleton_iff.1 (this ha)).symm
  intro a ha b hb
  have : E ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer ({a} : Set K) := by
    refine sup_le (fun x hx => ?_) ?_
    · exact Subgroup.mem_centralizer_singleton_iff.2 (h1 x hx a ha)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 (h2 a ha)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (this hb)).symm

theorem gfr3_exists_good_of_sylow [Finite K]
    (hnc : ∃ x y : K, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x ∧
      IsPGroup 3 (Subgroup.closure ({x, y} : Set K)))
    (h81 : ¬ 3 ^ 4 ∣ Nat.card K) {z0 : K} (hz0 : orderOf z0 = 3)
    (h27 : 3 ^ 3 ∣ Nat.card (Subgroup.centralizer ({z0} : Set K))) (hgood : GFR3Good K z0) :
    ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      ∃ s ∈ E, orderOf s = 3 ∧ GFR3Good K s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hKpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
  set C := Subgroup.centralizer ({z0} : Set K) with hC
  have hCK : Nat.card C ∣ Nat.card K := Subgroup.card_subgroup_dvd_card C
  have h3K : 3 ^ 3 ∣ Nat.card K := h27.trans hCK
  have hfacK : (Nat.card K).factorization 3 = 3 := by
    have h3 : 3 ≤ (Nat.card K).factorization 3 :=
      (hp.pow_dvd_iff_le_factorization hKpos).mp h3K
    have h4' : ¬ 4 ≤ (Nat.card K).factorization 3 :=
      fun h => h81 ((hp.pow_dvd_iff_le_factorization hKpos).mpr h)
    omega
  have hCpos : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hfacC : (Nat.card C).factorization 3 = 3 := by
    have h3 : 3 ≤ (Nat.card C).factorization 3 :=
      (hp.pow_dvd_iff_le_factorization hCpos).mp h27
    have h4' : ¬ 4 ≤ (Nat.card C).factorization 3 := fun h =>
      h81 ((hp.pow_dvd_iff_le_factorization hCpos).mpr h |>.trans hCK)
    omega
  have hz0C : z0 ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨P0, hP0z, hP0c⟩ : ∃ P0 : Sylow 3 K, z0 ∈ (P0 : Subgroup K) ∧
      ∀ x ∈ (P0 : Subgroup K), z0 * x = x * z0 := by
    have hQp : IsPGroup 3 ((Subgroup.zpowers z0).subgroupOf C) := by
      have : IsPGroup 3 (Subgroup.zpowers z0) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz0, pow_one])
      exact this.comap_of_injective C.subtype C.subtype_injective |>.to_le (by
        intro x hx
        exact hx)
    obtain ⟨S, hS⟩ := hQp.exists_le_sylow
    set P : Subgroup K := (S : Subgroup C).map C.subtype with hP
    have hPcard : Nat.card P = 3 ^ (Nat.card K).factorization 3 := by
      rw [hP, Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity,
        hfacC, hfacK]
    refine ⟨Sylow.ofCard P hPcard, ?_, ?_⟩
    · rw [Sylow.coe_ofCard]
      refine ⟨⟨z0, hz0C⟩, hS ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_zpowers z0
    · intro x hx
      rw [Sylow.coe_ofCard] at hx
      obtain ⟨c, -, rfl⟩ := hx
      exact (Subgroup.mem_centralizer_singleton_iff.1 c.2).symm
  intro E hE hEc
  have hEp : IsPGroup 3 E := IsPGroup.of_card hEc
  obtain ⟨Pe, hEPe⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P0 Pe
  have hPecard : Nat.card (Pe : Subgroup K) = 3 ^ 3 := by
    rw [Sylow.card_eq_multiplicity, hfacK]
  have hmem : ∀ a ∈ (Pe : Subgroup K), ∃ b ∈ (P0 : Subgroup K), a = g * b * g⁻¹ := by
    intro a ha
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact ⟨b, hb, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  have hsPe : g * z0 * g⁻¹ ∈ (Pe : Subgroup K) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul z0 (MulAut.conj g) (P0 : Subgroup K) hP0z
    rwa [MulAut.smul_def, MulAut.conj_apply] at this
  have hscen : ∀ a ∈ (Pe : Subgroup K), (g * z0 * g⁻¹) * a = a * (g * z0 * g⁻¹) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hmem a ha
    calc g * z0 * g⁻¹ * (g * b * g⁻¹) = g * (z0 * b) * g⁻¹ := by group
      _ = g * (b * z0) * g⁻¹ := by rw [hP0c b hb]
      _ = g * b * g⁻¹ * (g * z0 * g⁻¹) := by group
  have hnab : ¬ ∀ a ∈ (Pe : Subgroup K), ∀ b ∈ (Pe : Subgroup K), a * b = b * a := by
    intro hab
    obtain ⟨x, y, -, -, hxy, hP⟩ := hnc
    obtain ⟨Qx, hQx⟩ := hP.exists_le_sylow
    obtain ⟨g', hg'⟩ := MulAction.exists_smul_eq K Qx Pe
    have hconj : ∀ a ∈ (Qx : Subgroup K), g' * a * g'⁻¹ ∈ (Pe : Subgroup K) := by
      intro a ha
      rw [← hg', Sylow.coe_subgroup_smul]
      have := Subgroup.smul_mem_pointwise_smul a (MulAut.conj g') (Qx : Subgroup K) ha
      rwa [MulAut.smul_def, MulAut.conj_apply] at this
    have hx := hconj x (hQx (Subgroup.subset_closure (by simp)))
    have hy := hconj y (hQx (Subgroup.subset_closure (by simp)))
    have := hab _ hx _ hy
    apply hxy
    have h2 : g' * (x * y) * g'⁻¹ = g' * (y * x) * g'⁻¹ := by
      calc g' * (x * y) * g'⁻¹ = g' * x * g'⁻¹ * (g' * y * g'⁻¹) := by group
        _ = g' * y * g'⁻¹ * (g' * x * g'⁻¹) := this
        _ = g' * (y * x) * g'⁻¹ := by group
    have h3 := mul_left_cancel (mul_right_cancel h2)
    exact h3
  have hsE : g * z0 * g⁻¹ ∈ E := by
    by_contra hsE
    apply hnab
    set s := g * z0 * g⁻¹ with hs
    have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hsE' : ∀ e ∈ E, s * e = e * s := fun e he => hscen e (hEPe he)
    have hTP : E ⊔ Subgroup.zpowers s ≤ (Pe : Subgroup K) :=
      sup_le hEPe (by rw [Subgroup.zpowers_le]; exact hsPe)
    have hdvd1 : Nat.card E ∣ Nat.card (E ⊔ Subgroup.zpowers s : Subgroup K) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hdvd2 : Nat.card (E ⊔ Subgroup.zpowers s : Subgroup K) ∣ 3 ^ 3 :=
      hPecard ▸ Subgroup.card_dvd_of_le hTP
    have hne : Nat.card (E ⊔ Subgroup.zpowers s : Subgroup K) ≠ 3 ^ 2 := by
      intro hc
      have heq : E = E ⊔ Subgroup.zpowers s :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc, hEc])
      exact hsE (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
    have hT27 : Nat.card (E ⊔ Subgroup.zpowers s : Subgroup K) = 3 ^ 3 := by
      obtain ⟨m, hm⟩ := hdvd1
      rw [hEc] at hm
      have hm' : Nat.card (E ⊔ Subgroup.zpowers s : Subgroup K) = 9 * m := by
        rw [hm]; norm_num
      have hle : 9 * m ∣ 27 := by rw [← hm']; exact hdvd2
      have hm27 : m ∣ 3 := by
        have : 9 * m ∣ 9 * 3 := by simpa using hle
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
      have h13 : m = 1 ∨ m = 3 := (Nat.dvd_prime hp).1 hm27
      rcases h13 with rfl | rfl
      · exact absurd (by rw [hm']; norm_num) hne
      · rw [hm']; norm_num
    have hTeq : E ⊔ Subgroup.zpowers s = (Pe : Subgroup K) :=
      Subgroup.eq_of_le_of_card_ge hTP (by rw [hT27, hPecard])
    intro a ha b hb
    rw [← hTeq] at ha hb
    exact gfr3_comm_sup hEcomm hsE' a ha b hb
  refine ⟨g * z0 * g⁻¹, hsE, ?_, gfr3_good_conj hgood g⟩
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz0]

end CFSG.HardMathSupport.Solomon.Coordinator
