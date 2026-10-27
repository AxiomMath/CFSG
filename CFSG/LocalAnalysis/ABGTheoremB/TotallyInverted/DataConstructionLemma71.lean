module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstructionP
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstructionQ

public section

namespace CFSG.ABGTheoremB.TotallyInverted.DataConstruction

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ} {J : Subgroup G}

omit [Finite G] in
theorem ON_le_normalizer_of_le_J (hJ : σ.IsLayerComplement J) {Y : Subgroup G} (hY : Y ≤ J) :
    σ.ON ≤ Subgroup.normalizer (Y : Set G) :=
  ((Subgroup.le_centralizer_iff.mp hJ.centralizes).trans (Subgroup.centralizer_le hY)).trans
    (Subgroup.centralizer_le_normalizer _)

theorem isSylowOf_sup_Ps [Fact r.Prime] (hσ : σ.IsValid) (hJ : σ.IsLayerComplement J)
    (hP₀ : IsSylowOf r (σ.Ps r 0) σ.ON) {Y : Subgroup G} (hYJ : Y ≤ J) (hY : IsPGroup r Y) :
    IsSylowOf r (Y ⊔ σ.Ps r 0) (Y ⊔ σ.ON) :=
  isSylowOf_sup ((hYJ.trans (J_le_N hσ hJ)).trans σ.N_le_normalizer_ON) (isSylowOf_self hY) hP₀
    ((hYJ.trans (J_le_N hσ hJ)).trans (N_le_normalizer_Ps_zero σ r))
    (eq_bot_iff.mpr ((inf_le_inf hYJ hP₀.le).trans hJ.inf_eq.le))

theorem isSylowOf_Ps_of_not_dvd [Fact r.Prime] (hσ : σ.IsValid) (hJ : σ.IsLayerComplement J)
    (hP₀ : IsSylowOf r (σ.Ps r 0) σ.ON) {X : Subgroup G} (hXJ : X ≤ J)
    (hX : ¬ r ∣ Nat.card X) : IsSylowOf r (σ.Ps r 0) (X ⊔ σ.ON) := by
  have h := isSylowOf_sup ((hXJ.trans (J_le_N hσ hJ)).trans σ.N_le_normalizer_ON)
    (isSylowOf_bot hX) hP₀ bot_le (bot_inf_eq _)
  rwa [bot_sup_eq] at h

theorem sup_ON_le_normalizer (hσ : σ.IsValid) (hJ : σ.IsLayerComplement J) {Y : Subgroup G}
    (hYJ : Y ≤ J) : Y ⊔ σ.ON ≤ Subgroup.normalizer ((Y ⊔ σ.Ps r 0 : Subgroup G) : Set G) :=
  sup_le (le_normalizer_sup Subgroup.le_normalizer
      ((hYJ.trans (J_le_N hσ hJ)).trans (N_le_normalizer_Ps_zero σ r)))
    (le_normalizer_sup (ON_le_normalizer_of_le_J hJ hYJ)
      (σ.ON_le_N.trans (N_le_normalizer_Ps_zero σ r)))

omit [Finite G] in
theorem isPGroup_sup_ON_inf (hJ : σ.IsLayerComplement J) {U : Subgroup G}
    (hU : IsPGroup r U) (hUN : U ≤ σ.N) : IsPGroup r ((U ⊔ σ.ON) ⊓ J : Subgroup G) := by
  rintro ⟨y, hyUO, hyJ⟩
  have hy : y ∈ ((U ⊔ σ.ON : Subgroup G) : Set G) := hyUO
  rw [Subgroup.coe_mul_of_left_le_normalizer_right U σ.ON
    (hUN.trans σ.N_le_normalizer_ON)] at hy
  obtain ⟨u, hu, o, ho, rfl⟩ := hy
  obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
  have hu' : u ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcomm : Commute (u * o) o⁻¹ :=
    (Subgroup.mem_centralizer_iff.mp (hJ.centralizes hyJ) _ (σ.ON.inv_mem ho)).symm
  have h1 : (u * o) ^ r ^ k * o⁻¹ ^ r ^ k = 1 := by
    rw [← hcomm.mul_pow, mul_inv_cancel_right, hu']
  have h2 : (u * o) ^ r ^ k = o ^ r ^ k := by
    rw [inv_pow] at h1
    exact mul_inv_eq_one.mp h1
  have h3 : (u * o) ^ r ^ k ∈ J ⊓ σ.ON := ⟨J.pow_mem hyJ _, h2 ▸ σ.ON.pow_mem ho _⟩
  rw [hJ.inf_eq, Subgroup.mem_bot] at h3
  exact ⟨k, Subtype.ext (by simpa using h3)⟩

theorem le_sup_ON_inf_sup (hσ : σ.IsValid) (hJ : σ.IsLayerComplement J) {U : Subgroup G}
    (hUL₀ : U ≤ σ.L₀) : U ≤ (U ⊔ σ.ON) ⊓ J ⊔ σ.ON := by
  intro u hu
  have hu' : u ∈ ((J ⊔ σ.ON : Subgroup G) : Set G) := by
    rw [← hJ.sup_eq]
    exact hUL₀ hu
  rw [Subgroup.coe_mul_of_left_le_normalizer_right J σ.ON
    ((J_le_N hσ hJ).trans σ.N_le_normalizer_ON)] at hu'
  obtain ⟨j, hj, o, ho, rfl⟩ := hu'
  have hjX : j ∈ (U ⊔ σ.ON) ⊓ J := by
    refine ⟨?_, hj⟩
    have := (U ⊔ σ.ON).mul_mem (Subgroup.mem_sup_left hu)
      (Subgroup.mem_sup_right (σ.ON.inv_mem ho))
    rwa [mul_inv_cancel_right] at this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hjX) (Subgroup.mem_sup_right ho)

omit [Finite G] in
theorem Ps_sup_inf_J (hJ : σ.IsLayerComplement J) (hP₀ : σ.Ps r 0 ≤ σ.ON) {Y : Subgroup G}
    (hYJ : Y ≤ J) : (σ.Ps r 0 ⊔ Y) ⊓ J = Y := by
  rw [sup_inf_eq_of_le hYJ (hP₀.trans (ON_le_normalizer_of_le_J hJ hYJ)),
    eq_bot_iff.mpr ((inf_le_inf_right J hP₀).trans (inf_comm J σ.ON ▸ hJ.inf_eq.le)),
    bot_sup_eq]

theorem sup_inf_J_le (hσ : σ.IsValid) (hJ : σ.IsLayerComplement J) (hP₀ : σ.Ps r 0 ≤ σ.ON)
    {R Y : Subgroup G} (hYJ : Y ≤ J)
    (hRY : R ≤ Subgroup.normalizer ((Y ⊔ σ.Ps r 0 : Subgroup G) : Set G))
    (hRL : R ⊓ σ.L₀ = ⊥) : (R ⊔ (Y ⊔ σ.Ps r 0)) ⊓ J ≤ Y := by
  have hVL₀ : Y ⊔ σ.Ps r 0 ≤ σ.L₀ := sup_le (hYJ.trans hJ.le) (hP₀.trans hσ.ON_le_L₀)
  have h1 : (R ⊔ (Y ⊔ σ.Ps r 0)) ⊓ σ.L₀ = Y ⊔ σ.Ps r 0 := by
    rw [sup_inf_eq_of_le hVL₀ hRY, hRL, bot_sup_eq]
  calc (R ⊔ (Y ⊔ σ.Ps r 0)) ⊓ J = (R ⊔ (Y ⊔ σ.Ps r 0)) ⊓ σ.L₀ ⊓ J := by
        rw [inf_assoc, inf_eq_right.mpr hJ.le]
    _ = Y := by rw [h1, sup_comm, Ps_sup_inf_J hJ hP₀ hYJ]
    _ ≤ Y := le_rfl

theorem lemma71_zero (hσ : σ.IsValid) (hT : σ.TIFacts) (hr : r.Prime) (hr2 : r ≠ 2)
    (hti : σ.TotallyInverted r) (hJ : σ.IsLayerComplement J)
    (hP₀ : IsSylowOf r (σ.Ps r 0) σ.ON) {Q Qs : Subgroup G} (hQ : QPair σ r J Q Qs) :
    maximals (signalizers σ.N σ.C r) = {σ.Ps r 0 ⊔ Q, σ.Ps r 0 ⊔ Qs} := by
  have : Fact r.Prime := ⟨hr⟩
  have hmem : ∀ Y : Subgroup G, Y ≤ J → IsPGroup r Y →
      σ.C ≤ Subgroup.normalizer (Y : Set G) → σ.Ps r 0 ⊔ Y ∈ signalizers σ.N σ.C r := by
    intro Y hYJ hY hCY
    have hYN : Y ≤ σ.N := hYJ.trans (J_le_N hσ hJ)
    have hp : IsPGroup r (σ.Ps r 0 ⊔ Y : Subgroup G) :=
      (isPGroup_pCoreIn r _).to_sup_of_normal_left' hY (hYN.trans (N_le_normalizer_Ps_zero σ r))
    exact ⟨sup_le (pCoreIn_le r _) hYN, hp,
      le_normalizer_sup (σ.C_le_N.trans (N_le_normalizer_Ps_zero σ r)) hCY,
      inf_C_eq_bot hr hti hp (sup_le (hP₀.le.trans (ON_le_L hσ)) (hYJ.trans (J_le_L hJ)))⟩
  have hcov : ∀ U ∈ signalizers σ.N σ.C r, U ≤ σ.Ps r 0 ⊔ Q ∨ U ≤ σ.Ps r 0 ⊔ Qs := by
    intro U hUsig
    have hUL₀ := hT.signalizer_le r hr hr2 U hUsig
    obtain ⟨hUN, hU, hCU, -⟩ := hUsig
    have hCX : σ.C ≤ Subgroup.normalizer (((U ⊔ σ.ON) ⊓ J : Subgroup G) : Set G) :=
      le_normalizer_inf (le_normalizer_sup hCU (σ.C_le_N.trans σ.N_le_normalizer_ON))
        (σ.C_le_N.trans hJ.normal)
    have hUX := le_sup_ON_inf_sup hσ hJ hUL₀
    have key : ∀ Y : Subgroup G, Y ≤ J → IsPGroup r Y → (U ⊔ σ.ON) ⊓ J ≤ Y →
        U ≤ σ.Ps r 0 ⊔ Y := by
      intro Y hYJ hY hXY
      have hUK : U ≤ Y ⊔ σ.ON := hUX.trans (sup_le_sup_right hXY _)
      rw [sup_comm]
      exact le_of_isSylowOf_of_le_normalizer (isSylowOf_sup_Ps hσ hJ hP₀ hYJ hY) hUK hU
        (hUK.trans (sup_ON_le_normalizer hσ hJ hYJ))
    rcases hQ.cover _ inf_le_right (isPGroup_sup_ON_inf hJ hU hUN) hCX with h | h
    · exact Or.inl (key Q hQ.le hQ.isPGroup h)
    · exact Or.inr (key Qs hQ.le_s hQ.isPGroup_s h)
  have hne : ∀ {Y Y' : Subgroup G}, Y ≤ J → Y' ≤ J → Nat.card Y' ≤ Nat.card Y →
      σ.Ps r 0 ⊔ Y ≤ σ.Ps r 0 ⊔ Y' → σ.Ps r 0 ⊔ Y = σ.Ps r 0 ⊔ Y' := by
    intro Y Y' hYJ hY'J hcard h
    have hYY' : Y ≤ Y' := by
      rw [← Ps_sup_inf_J hJ hP₀.le hYJ, ← Ps_sup_inf_J hJ hP₀.le hY'J]
      exact inf_le_inf_right J h
    rw [Subgroup.eq_of_le_of_card_ge hYY' hcard]
  exact maximals_eq_pair (hmem Q hQ.le hQ.isPGroup hQ.normal)
    (hmem Qs hQ.le_s hQ.isPGroup_s hQ.normal_s) hcov (hne hQ.le hQ.le_s hQ.card_eq.symm.le)
    (hne hQ.le_s hQ.le hQ.card_eq.le)

theorem lemma72_zero (hσ : σ.IsValid) (hT : σ.TIFacts) (hr : r.Prime) (hr2 : r ≠ 2)
    (hti : σ.TotallyInverted r) (hJ : σ.IsLayerComplement J)
    (hP₀ : IsSylowOf r (σ.Ps r 0) σ.ON) {Q Qs : Subgroup G} (hQ : QPair σ r J Q Qs)
    {R : Subgroup G} (hR : IsSylowOf r R σ.C) :
    {U | U ∈ maximals (signalizersPerm σ.N σ.T σ.C r) ∧ R ≤ U} =
      {R ⊔ Q ⊔ σ.Ps r 0, R ⊔ Qs ⊔ σ.Ps r 0} := by
  have : Fact r.Prime := ⟨hr⟩
  have hRC := hR.le
  have hRL : R ⊓ σ.L = ⊥ := inf_L_eq_bot hr hti hR.isPGroup hRC
  have hCP : σ.C ≤ Subgroup.normalizer (σ.Ps r 0 : Set G) :=
    σ.C_le_N.trans (N_le_normalizer_Ps_zero σ r)
  have hCON : σ.C ≤ Subgroup.normalizer (σ.ON : Set G) := σ.C_le_N.trans σ.N_le_normalizer_ON
  have hsyl : ∀ Y : Subgroup G, Y ≤ J → IsPGroup r Y → σ.C ≤ Subgroup.normalizer (Y : Set G) →
      IsSylowOf r (R ⊔ (Y ⊔ σ.Ps r 0)) (σ.C ⊔ (Y ⊔ σ.ON)) := fun Y hYJ hY hCY =>
    isSylowOf_sup (le_normalizer_sup hCY hCON) hR (isSylowOf_sup_Ps hσ hJ hP₀ hYJ hY)
      (hRC.trans (le_normalizer_sup hCY hCP))
      (eq_bot_iff.mpr (hRL ▸ inf_le_inf_left R
        (sup_le (hYJ.trans (J_le_L hJ)) (hP₀.le.trans (ON_le_L hσ)))))
  have hnorm : ∀ Y : Subgroup G, Y ≤ J → σ.C ≤ Subgroup.normalizer (Y : Set G) →
      σ.C ⊔ (Y ⊔ σ.ON) ≤ Subgroup.normalizer ((Y ⊔ σ.Ps r 0 : Subgroup G) : Set G) :=
    fun Y hYJ hCY => sup_le (le_normalizer_sup hCY hCP) (sup_ON_le_normalizer hσ hJ hYJ)
  have hmem : ∀ Y : Subgroup G, Y ≤ J → IsPGroup r Y → σ.C ≤ Subgroup.normalizer (Y : Set G) →
      R ⊔ Y ⊔ σ.Ps r 0 ∈ signalizersPerm σ.N σ.T σ.C r := by
    intro Y hYJ hY hCY
    rw [sup_assoc]
    have hp : IsPGroup r (R ⊔ (Y ⊔ σ.Ps r 0) : Subgroup G) := (hsyl Y hYJ hY hCY).isPGroup
    refine ⟨⟨sup_le (hRC.trans σ.C_le_N) (sup_le (hYJ.trans (J_le_N hσ hJ)) (pCoreIn_le r _)),
      hp, ?_, inf_eq_bot_of_isPGroup hr Nat.prime_two hr2 hp (isPGroup_T hσ)⟩,
      sup_mul_comm_of_le hRC (le_normalizer_sup hCY hCP)⟩
    exact le_normalizer_sup ((Subgroup.le_centralizer_iff.mp hRC).trans
      (Subgroup.centralizer_le_normalizer _)) (le_normalizer_sup ((σ.T_le_C hσ).trans hCY)
        ((σ.T_le_N hσ).trans (N_le_normalizer_Ps_zero σ r)))
  have hcov : ∀ U ∈ signalizersPerm σ.N σ.T σ.C r, R ≤ U →
      U ≤ R ⊔ Q ⊔ σ.Ps r 0 ∨ U ≤ R ⊔ Qs ⊔ σ.Ps r 0 := by
    rintro U ⟨⟨hUN, hU, -, -⟩, hperm⟩ hRU
    obtain ⟨p', X, hp', hX, hUle⟩ :=
      hT.permutable_le J hJ U hUN (odd_card_of_isPGroup hr hr2 hU) hperm
    have hUle' : U ≤ σ.C ⊔ (X ⊔ σ.ON) := by rwa [sup_assoc] at hUle
    have key : ∀ Y : Subgroup G, Y ≤ J → IsPGroup r Y →
        σ.C ≤ Subgroup.normalizer (Y : Set G) → X ≤ Y → U ≤ R ⊔ Y ⊔ σ.Ps r 0 := by
      intro Y hYJ hY hCY hXY
      have hUK : U ≤ σ.C ⊔ (Y ⊔ σ.ON) :=
        hUle'.trans (sup_le_sup_left (sup_le_sup_right hXY _) _)
      rw [sup_assoc]
      exact le_sup_of_isSylowOf_sup (hsyl Y hYJ hY hCY)
        ((hY.to_sup_of_normal_right' (isPGroup_pCoreIn r _)
          ((hYJ.trans (J_le_N hσ hJ)).trans (N_le_normalizer_Ps_zero σ r))))
        hUK hU hRU (hUK.trans (hnorm Y hYJ hCY))
    by_cases hp'r : p' = r
    · rw [hp'r] at hX
      rcases hQ.cover X hX.1 hX.2.1 hX.2.2.1 with h | h
      · exact Or.inl (key Q hQ.le hQ.isPGroup hQ.normal h)
      · exact Or.inr (key Qs hQ.le_s hQ.isPGroup_s hQ.normal_s h)
    · have hXr : ¬ r ∣ Nat.card X := by
        have : Fact p'.Prime := ⟨hp'⟩
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX.2.1
        rw [hk]
        intro h
        exact hp'r ((Nat.prime_dvd_prime_iff_eq hr hp').mp (hr.dvd_of_dvd_pow h)).symm
      have hsylX : IsSylowOf r (R ⊔ σ.Ps r 0) (σ.C ⊔ (X ⊔ σ.ON)) :=
        isSylowOf_sup (le_normalizer_sup hX.2.2.1 hCON) hR
          (isSylowOf_Ps_of_not_dvd hσ hJ hP₀ hX.1 hXr) (hRC.trans hCP)
          (eq_bot_iff.mpr (hRL ▸ inf_le_inf_left R (hP₀.le.trans (ON_le_L hσ))))
      have hKN : σ.C ⊔ (X ⊔ σ.ON) ≤ σ.N :=
        sup_le σ.C_le_N (sup_le (hX.1.trans (J_le_N hσ hJ)) σ.ON_le_N)
      have hUP : U ≤ R ⊔ σ.Ps r 0 := le_sup_of_isSylowOf_sup hsylX (isPGroup_pCoreIn r _)
        hUle' hU hRU ((hUle'.trans hKN).trans (N_le_normalizer_Ps_zero σ r))
      exact Or.inl (hUP.trans (sup_le_sup_right le_sup_left _))
  have hRL₀ : R ⊓ σ.L₀ = ⊥ := eq_bot_iff.mpr (hRL ▸ inf_le_inf_left R L₀_le_L)
  have hne : ∀ {Y Y' : Subgroup G}, Y ≤ J → Y' ≤ J → σ.C ≤ Subgroup.normalizer (Y' : Set G) →
      Nat.card Y' ≤ Nat.card Y → R ⊔ Y ⊔ σ.Ps r 0 ≤ R ⊔ Y' ⊔ σ.Ps r 0 →
        R ⊔ Y ⊔ σ.Ps r 0 = R ⊔ Y' ⊔ σ.Ps r 0 := by
    intro Y Y' hYJ hY'J hCY' hcard h
    have hYY' : Y ≤ Y' := by
      refine le_trans (le_inf ?_ hYJ) (sup_inf_J_le hσ hJ hP₀.le hY'J
        (hRC.trans (le_normalizer_sup hCY' hCP)) hRL₀)
      rw [← sup_assoc]
      exact (le_sup_right.trans le_sup_left).trans h
    rw [Subgroup.eq_of_le_of_card_ge hYY' hcard]
  exact setOf_maximals_ge_eq_pair (hmem Q hQ.le hQ.isPGroup hQ.normal)
    (hmem Qs hQ.le_s hQ.isPGroup_s hQ.normal_s) (le_sup_left.trans le_sup_left)
    (le_sup_left.trans le_sup_left) hcov
    (hne hQ.le hQ.le_s hQ.normal_s hQ.card_eq.symm.le)
    (hne hQ.le_s hQ.le hQ.normal hQ.card_eq.le)

end CFSG.ABGTheoremB.TotallyInverted.DataConstruction
