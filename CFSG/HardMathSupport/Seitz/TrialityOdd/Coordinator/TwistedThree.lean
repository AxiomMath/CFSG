module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.FrameInterface
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.InnerPlanePullback
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.QPlusMain
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.G2Family
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFrame
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Cent

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.SEITZ11.G2Seven CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
  CFSG.HardMathSupport.Seitz.TrialityOdd.Inner


section G2

open G2Anisotropic.Coordinator in
theorem exists_conj_map_eq_closure_std (k : Type) [Field k] [Finite k] (hk : 3 ≤ Nat.card k)
    (h3 : 3 ∣ Nat.card k + 1) (F : Subgroup (adjointGroup .G2 k))
    (hF : CFSG.Open.IsElemAbelian 3 F) (hc : Nat.card F = 3 ^ 2) :
    ∃ x : adjointGroup .G2 k, F.map (MulAut.conj x).toMonoidHom =
      Subgroup.closure {zStd k, eStd k} := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := G2Anisotropic.ExceptionsTransport.finite_adjointGroup_G2 k
  have h3K : ¬ 3 ∣ Nat.card k := fun h => by omega
  obtain ⟨P, hFP, z, hzF, hz1, hzp, hzc⟩ :=
    exists_sylow_central_in_plane (rankLE2_three_adjointGroup_G2 k h3K) hF hc
  have hoz : orderOf z = 3 := orderOf_eq_prime hzp hz1
  obtain ⟨e, heF, hez⟩ : ∃ e ∈ F, e ∉ Subgroup.zpowers z := by
    by_contra hne
    push Not at hne
    have h1 : Nat.card F ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hne
    rw [Nat.card_zpowers, hoz, hc] at h1
    omega
  have he1 : e ≠ 1 := fun h => hez (h ▸ one_mem _)
  obtain ⟨x, hxz, hxe⟩ := G2Anisotropic.UnitaryEmbedding.g2SylowPairNormalForm_of_instances k hk h3 P z
    (hFP hzF) hzc hz1 hzp e (hFP heF) he1 (hF.2 e heF) hez
  have hle : Subgroup.closure {z, e} ≤ F := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [hzF, heF]
  have hFze : Subgroup.closure {z, e} = F := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hdvd : Nat.card (Subgroup.closure {z, e}) ∣ 3 ^ 2 := hc ▸ Subgroup.card_dvd_of_le hle
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hzle : Subgroup.zpowers z ≤ Subgroup.closure {z, e} :=
      Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert _ _))
    have hzc3 : 3 ∣ Nat.card (Subgroup.closure {z, e}) := by
      have := Subgroup.card_dvd_of_le hzle
      rwa [Nat.card_zpowers, hoz] at this
    interval_cases i
    · rw [hci] at hzc3
      norm_num at hzc3
    · exfalso
      have hcz : Nat.card (Subgroup.closure {z, e}) ≤ Nat.card (Subgroup.zpowers z) := by
        simp [Nat.card_zpowers, hoz, hci]
      have heq := Subgroup.eq_of_le_of_card_ge hzle hcz
      exact hez (heq ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    · rw [hci, hc]
  refine ⟨x, ?_⟩
  rw [← hFze, MonoidHom.map_closure, Set.image_pair]
  change Subgroup.closure {x * z * x⁻¹, x * e * x⁻¹} = _
  have hzS : zStd k ∈ Subgroup.closure {x * z * x⁻¹, x * e * x⁻¹} := by
    rcases hxz with h | h
    · exact Subgroup.subset_closure (Or.inl h.symm)
    · rw [← inv_inv (zStd k), ← h]
      exact inv_mem (Subgroup.subset_closure (Or.inl rfl))
  have heS : eStd k ∈ Subgroup.closure {x * z * x⁻¹, x * e * x⁻¹} := by
    rcases hxe with h | h
    · exact Subgroup.subset_closure (Or.inr h.symm)
    · rw [← inv_inv (eStd k), ← h]
      exact inv_mem (Subgroup.subset_closure (Or.inr rfl))
  have hzS' : x * z * x⁻¹ ∈ Subgroup.closure {zStd k, eStd k} := by
    rcases hxz with h | h <;> rw [h]
    · exact Subgroup.subset_closure (Or.inl rfl)
    · exact inv_mem (Subgroup.subset_closure (Or.inl rfl))
  have heS' : x * e * x⁻¹ ∈ Subgroup.closure {zStd k, eStd k} := by
    rcases hxe with h | h <;> rw [h]
    · exact Subgroup.subset_closure (Or.inr rfl)
    · exact inv_mem (Subgroup.subset_closure (Or.inr rfl))
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [hzS', heS']
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [hzS, heS]

theorem exists_conj_of_plane_G2 (k : Type) [Field k] [Finite k] (hk : 3 ≤ Nat.card k)
    (h3 : 3 ∣ Nat.card k + 1) (F₁ F₂ : Subgroup (adjointGroup .G2 k))
    (hF₁ : CFSG.Open.IsElemAbelian 3 F₁) (hc₁ : Nat.card F₁ = 3 ^ 2)
    (hF₂ : CFSG.Open.IsElemAbelian 3 F₂) (hc₂ : Nat.card F₂ = 3 ^ 2) :
    ∃ x : adjointGroup .G2 k, F₂ = F₁.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨x₁, h₁⟩ := exists_conj_map_eq_closure_std k hk h3 F₁ hF₁ hc₁
  obtain ⟨x₂, h₂⟩ := exists_conj_map_eq_closure_std k hk h3 F₂ hF₂ hc₂
  refine ⟨x₂⁻¹ * x₁, ?_⟩
  have h := congrArg (Subgroup.map (MulAut.conj x₂⁻¹).toMonoidHom) (h₂.trans h₁.symm)
  rw [Subgroup.map_map, Subgroup.map_map] at h
  have e1 : (MulAut.conj x₂⁻¹).toMonoidHom.comp (MulAut.conj x₂).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun y => by simp [mul_assoc]
  have e2 : (MulAut.conj x₂⁻¹).toMonoidHom.comp (MulAut.conj x₁).toMonoidHom =
      (MulAut.conj (x₂⁻¹ * x₁)).toMonoidHom := MonoidHom.ext fun y => by simp [mul_assoc]
  rw [e1, e2, Subgroup.map_id] at h
  exact h

end G2

theorem eq_map_conj_of_map_subgroupOf {G G' : Type*} [Group G] [Group G'] {J : Subgroup G}
    (ε : J ≃* G') {A B : Subgroup G} (hA : A ≤ J) (hB : B ≤ J) (x : G')
    (h : (B.subgroupOf J).map ε.toMonoidHom =
      ((A.subgroupOf J).map ε.toMonoidHom).map (MulAut.conj x).toMonoidHom) :
    B = A.map (MulAut.conj ((ε.symm x : J) : G)).toMonoidHom := by
  have hεx : ε (ε.symm x) = x := ε.apply_symm_apply x
  ext y
  constructor
  · intro hy
    have hy' : ε ⟨y, hB hy⟩ ∈ (B.subgroupOf J).map ε.toMonoidHom :=
      ⟨⟨y, hB hy⟩, (Subgroup.mem_subgroupOf).2 hy, rfl⟩
    rw [h] at hy'
    obtain ⟨_, ⟨a, ha, rfl⟩, hya⟩ := hy'
    have hya' : ε.symm x * a * (ε.symm x)⁻¹ = ⟨y, hB hy⟩ := by
      apply ε.injective
      rw [map_mul, map_mul, map_inv, hεx]
      exact hya
    refine ⟨a, (Subgroup.mem_subgroupOf).1 ha, ?_⟩
    change ((ε.symm x : J) : G) * (a : G) * ((ε.symm x : J) : G)⁻¹ = y
    have := congrArg Subtype.val hya'
    simpa using this
  · rintro ⟨a, ha, rfl⟩
    have haJ := hA ha
    have hmem : ε (ε.symm x * ⟨a, haJ⟩ * (ε.symm x)⁻¹) ∈
        ((A.subgroupOf J).map ε.toMonoidHom).map (MulAut.conj x).toMonoidHom := by
      refine ⟨ε ⟨a, haJ⟩, ⟨⟨a, haJ⟩, (Subgroup.mem_subgroupOf).2 ha, rfl⟩, ?_⟩
      change x * ε ⟨a, haJ⟩ * x⁻¹ = _
      rw [map_mul, map_mul, map_inv, hεx]
    rw [← h] at hmem
    obtain ⟨b, hb, hbe⟩ := hmem
    have hb' : b = ε.symm x * ⟨a, haJ⟩ * (ε.symm x)⁻¹ := ε.injective hbe
    have hbB := (Subgroup.mem_subgroupOf).1 hb
    rw [hb'] at hbB
    simpa using hbB

section Twisted

variable {K : Type} [Field K]

theorem isElemAbelian_map_subgroupOf {G G' : Type*} [Group G] [Group G'] {J : Subgroup G}
    (ε : J ≃* G') {H : Subgroup G} (hHJ : H ≤ J) (hHp : ∀ x ∈ H, x ^ 3 = 1)
    (hHc : Nat.card H = 3 ^ 2) :
    CFSG.Open.IsElemAbelian 3 ((H.subgroupOf J).map ε.toMonoidHom) ∧
      Nat.card ((H.subgroupOf J).map ε.toMonoidHom) = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : IsMulCommutative H := IsPGroup.isMulCommutative_of_card_eq_prime_sq hHc
  have hcard : Nat.card ((H.subgroupOf J).map ε.toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective ε.injective, ← hHc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHJ).toEquiv
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, hcard⟩
  · obtain ⟨_, ⟨a', ha', rfl⟩⟩ := a
    obtain ⟨_, ⟨b', hb', rfl⟩⟩ := b
    apply Subtype.ext
    change ε a' * ε b' = ε b' * ε a'
    rw [← map_mul, ← map_mul]
    have hab : a' * b' = b' * a' := by
      apply Subtype.ext
      have h := hcomm.is_comm.comm (⟨(a' : G), (Subgroup.mem_subgroupOf).1 ha'⟩ : H)
        ⟨(b' : G), (Subgroup.mem_subgroupOf).1 hb'⟩
      have h' := congrArg Subtype.val h
      simp only [Subgroup.coe_mul] at h' ⊢
      exact h'
    rw [hab]
  · rintro _ ⟨a', ha', rfl⟩
    change ε a' ^ 3 = 1
    rw [← map_pow]
    have : a' ^ 3 = 1 := Subtype.ext (by
      simpa using hHp _ ((Subgroup.mem_subgroupOf).1 ha'))
    rw [this, map_one]

open Subgroup CFSG.GH74.GLS.Stage4.Hex in
theorem closure_cenGen_twistedGroup_three [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 3 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) (h3q : 3 ∣ q + 1)
    (F : Subgroup (twistedGroup σ.toRingHom)) (hFJ : F ≤ FixedSub σ) (hFp : ∀ x ∈ F, x ^ 3 = 1)
    (hFc : Nat.card F = 3 ^ 2) : Subgroup.closure (cenGen F) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 : 2 ≤ q := by omega
  have hσ3' : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hσ3
  have hcardF : Nat.card (fixedField σ.toRingHom) = q :=
    card_fixedField_of_cube σ.toRingHom hq2 hK hσq
  have hcardX : Nat.card (fixSubfield σ) = q := hcardF
  obtain ⟨M, hM⟩ := exists_sl2_orderOf (fixedField σ.toRingHom) (p := 3)
    (by rw [hcardF]; exact h3q)
  let nh : twistedGroup σ.toRingHom := nHat σ.toRingHom (ng 0) * nHat σ.toRingHom (ng 1)
  let b : twistedGroup σ.toRingHom := slLong σ.toRingHom hσ3' M
  let b₀ : twistedGroup σ.toRingHom := nh * b * nh⁻¹
  let L : Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype M
  let v : twistedGroup σ.toRingHom := slShort σ.toRingHom hσ3' L
  have hLfix : Matrix.SpecialLinearGroup.map σ.toRingHom L = L := by
    refine Subtype.ext ?_
    ext i j
    simp only [L, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact (M.1 i j).2
  have hnhJ : nh ∈ FixedSub σ :=
    mul_mem (nHat_zero_mem_FixedSub σ hσ3) (nHat_one_mem_FixedSub σ hσ3)
  have hbJ : b ∈ FixedSub σ := slLong_mem_FixedSub σ hσ3 M
  have hb₀J : b₀ ∈ FixedSub σ := mul_mem (mul_mem hnhJ hbJ) (inv_mem hnhJ)
  have hvJ : v ∈ FixedSub σ := slShort_mem_FixedSub σ hσ3 L hLfix
  have hob : orderOf b = 3 := by
    rw [orderOf_injective (slLong σ.toRingHom hσ3') (slLong_injective hσ3') M, hM]
  have hob₀ : orderOf b₀ = 3 := by
    have := orderOf_injective (MulAut.conj nh).toMonoidHom (MulAut.conj nh).injective b
    rw [← hob]
    exact this
  have hoL : orderOf L = 3 := by
    rw [orderOf_injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (fixedField σ.toRingHom).subtype) (sl_map_injective _) M, hM]
  have hov : orderOf v = 3 := by
    rw [orderOf_injective (slShort σ.toRingHom hσ3') (slShort_injective hσ3') L, hoL]
  have hb₀theta : ((b₀ : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
      (thetaGroup : Subgroup (adjointGroup d4 K)) := by
    have e : ((b₀ : twistedGroup σ.toRingHom) : adjointGroup d4 K) =
        (nHatE K (ng 0) * nHatE K (ng 1)) * (b : adjointGroup d4 K) *
          (nHatE K (ng 0) * nHatE K (ng 1))⁻¹ := by
      have hn0 : (nHat σ.toRingHom (ng 0) : adjointGroup d4 K) = nHatE K (ng 0) := nHat_val _ _
      have hn1 : (nHat σ.toRingHom (ng 1) : adjointGroup d4 K) = nHatE K (ng 1) := nHat_val _ _
      simp only [b₀, nh, Subgroup.coe_mul, Subgroup.coe_inv, hn0, hn1, mul_assoc, mul_inv_rev]
    rw [e]
    exact conj_mem_thetaGroup (slLong_coe_mem_central σ.toRingHom hσ3' M)
  have hAb : ∀ a ∈ (slShort σ.toRingHom hσ3').range, a * b₀ = b₀ * a := by
    rintro _ ⟨B, rfl⟩
    refine Subtype.ext ?_
    exact (commute_thetaGroup_outerRankOne hb₀theta
      (slShort_coe_mem_outer σ.toRingHom hσ3' B)).eq.symm
  have hcomm : Commute b₀ v := (hAb v ⟨L, rfl⟩).symm
  have hnot : v ∉ zpowers b₀ := by
    intro hv'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hv'
    have hLc : L ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro B
      apply slShort_injective hσ3'
      rw [map_mul, map_mul]
      have h1 : Commute b₀ (slShort σ.toRingHom hσ3' B) := (hAb _ ⟨B, rfl⟩).symm
      have h2 := (h1.zpow_left i).eq
      rw [hi] at h2
      exact h2.symm
    have h2 := sq_eq_one_of_mem_center hLc
    have h3 : orderOf L ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hoL] at h3
    exact absurd h3 (by norm_num)
  obtain ⟨E₀, hbE, -, hE₀p, hE₀c, hE₀le⟩ := exists_plane_of_commute hob₀ hov hcomm hnot
  have hE₀J : E₀ ≤ FixedSub σ := hE₀le _ hb₀J hvJ
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    have : Finite (fixSubfield σ) := inferInstance
    rw [ENat.card_eq_coe_natCard, hcardX]
    exact_mod_cast hq
  let ε : ↥(FixedSub σ) ≃* ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
    (fixedSubEquivJ σ hK2 hq2 hK hσq hσ3).trans (trialityFieldImageEquivG2 σ hk3)
  have hkq : 3 ≤ Nat.card (fixSubfield σ) := by rw [hcardX]; exact hq
  have hk1 : 3 ∣ Nat.card (fixSubfield σ) + 1 := by rw [hcardX]; exact h3q
  obtain ⟨hE₀ea, hE₀cd⟩ := isElemAbelian_map_subgroupOf ε hE₀J hE₀p hE₀c
  obtain ⟨hFea, hFcd⟩ := isElemAbelian_map_subgroupOf ε hFJ hFp hFc
  have hJgen : closure (cenGen (E₀.subgroupOf (FixedSub σ))) = ⊤ :=
    closure_cenGen_eq_top_of_map ε _
      (G2Anisotropic.Coordinator.g2NativePlaneGen_three_of_dvd_add_one (fixSubfield σ) hkq hk1
        _ hE₀ea hE₀cd)
  have hJA : FixedSub σ ⊔ (slShort σ.toRingHom hσ3').range = ⊤ := by
    have h := CFSG.ClassicalInvolution.G2D4Models.range_slLong_sup_range_slShort hσ3'
    rw [eq_top_iff, ← h]
    refine sup_le_sup_right ?_ _
    rintro _ ⟨A, rfl⟩
    exact slLong_mem_FixedSub σ hσ3 A
  have hJle : FixedSub σ ≤ closure (cenGen E₀) := by
    have h1 : (closure (cenGen (E₀.subgroupOf (FixedSub σ)))).map (FixedSub σ).subtype ≤
        closure (cenGen E₀) := by
      rw [MonoidHom.map_closure]
      refine closure_mono ?_
      rintro _ ⟨k, ⟨x, hx, hx1, hk⟩, rfl⟩
      refine ⟨(x : twistedGroup σ.toRingHom), hx, fun h => hx1 (Subtype.ext h), ?_⟩
      exact congrArg Subtype.val hk
    rw [hJgen, Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1
  have hb₀1 : b₀ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hob₀
    exact absurd hob₀ (by norm_num)
  have hAle : (slShort σ.toRingHom hσ3').range ≤ closure (cenGen E₀) := fun a ha =>
    subset_closure ⟨b₀, hbE, hb₀1, hAb a ha⟩
  have htop₀ : closure (cenGen E₀) = ⊤ := by
    rw [eq_top_iff, ← hJA]
    exact sup_le hJle hAle
  obtain ⟨x, hx⟩ := exists_conj_of_plane_G2 (fixSubfield σ) hkq hk1 _ _ hE₀ea hE₀cd hFea hFcd
  have hFE := eq_map_conj_of_map_subgroupOf ε hE₀J hFJ x hx
  rw [hFE]
  change closure (cenGen (cj E₀ _)) = ⊤
  rw [closure_cenGen_cj, htop₀, Subgroup.map_top_of_surjective _ (MulAut.conj _).surjective]

end Twisted

section Frame

open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.RankThree.Chevalley

variable {K : Type} [Field K] [Finite K]

theorem fieldActor_eq_of_twistedTorus {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [CharP L ℓ]
    [IsAlgClosed L] [Algebra K L] (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h3q : 3 ∣ ℓ ^ f + 1) {g₀ : ModGL TwistTag.D4.tag L}
    (hg₀P : diagramMap TwistTag.D4 L * g₀ = g₀ * diagramMap TwistTag.D4 L)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hy3 : y ^ 3 = 1)
    (hyT : g₀⁻¹ * triEmb K σ L y * g₀ ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :
    fieldActor (t := TwistTag.D4) σ σ y = y := by
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  rw [d4Q_twistedTorus] at hyT
  obtain ⟨a, ha, hya⟩ := hyT
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.D4.tag L) := rootDiagUnit_injective
  have hya' : rootDiagUnitHom TwistTag.D4.tag L a = d4MinusPsi σ L g₀ y := by
    rw [d4MinusPsi_apply]
    exact hya
  have ha3 : ∀ i, a i ^ 3 = 1 := fun i => by
    have h2 : a ^ 3 = 1 := by
      apply hinj0
      rw [map_pow, map_one, hya', ← map_pow, hy3, map_one]
    exact congrFun h2 i
  obtain ⟨h1, h3⟩ := d4Q_eq_of_pow_eq_one hFr h3q ha ha3
  have hsym : (fun i => a (TwistTag.D4.perm.symm i)) = a := by
    funext i
    fin_cases i
    · rw [CFSG.RankThree.Chevalley.TrialityFold.perm_symm_i0]
      exact h3
    · rw [CFSG.RankThree.Chevalley.TrialityFold.perm_symm_i1]
      exact h1.symm
    · rw [CFSG.RankThree.Chevalley.TrialityFold.perm_symm_i2]
    · rw [CFSG.RankThree.Chevalley.TrialityFold.perm_symm_i3, h1, h3]
  have hP := (CFSG.RankThree.PartTwo.Sec8.LangTwistedProof.rootDiagUnit_commute_diagramMap_iff
    a).2 hsym
  apply d4MinusPsi_injective g₀
  have hP' : rootDiagUnitHom TwistTag.D4.tag L a * diagramMap TwistTag.D4 L =
      diagramMap TwistTag.D4 L * rootDiagUnitHom TwistTag.D4.tag L a := hP
  rw [d4MinusPsi_fieldActor Fr hcomm hg₀P, ← hya', mul_assoc, hP', inv_mul_cancel_left]

end Frame

open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.ClassicalInvolution.G2D4Models in
theorem twistedTorusPlaneGenAt_three : TwistedTorusPlaneGenAt 3 := by
  intro ℓ f hℓ hℓ2 hf K _ _ hK σ hσ _ h3ℓ h3q E hEea hEc hT0
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨L, _, _, _, _, g₀, ⟨-, hg₀P, -⟩, β, hβ⟩ := hT0
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set E' := E.map (β⁻¹).toMonoidHom with hE'
  have hE'3 : ∀ y ∈ E', y ^ 3 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    change (β⁻¹ e) ^ 3 = 1
    rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian e he, map_one]
  have hE'c : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (β⁻¹).injective, hEc]
  have hfix : ∀ y ∈ E', fieldActor (t := TwistTag.D4) σ σ y = y := by
    rintro _ ⟨e, he, rfl⟩
    exact fieldActor_eq_of_twistedTorus σ hσ h3q hg₀P _ (hE'3 _ ⟨e, he, rfl⟩) (hβ e he)
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, ← pow_mul]
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hq3 : 3 ≤ ℓ ^ f := by
    have h5 : 5 ≤ ℓ := by
      have := hℓ.two_le
      have h4 : ℓ ≠ 4 := fun h => by rw [h] at hℓ; norm_num at hℓ
      omega
    calc 3 ≤ ℓ := by omega
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hq2 : 2 ≤ ℓ ^ f := by omega
  let φ : twistedGroup σ.toRingHom →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (twistedIncl σ.toRingHom).codRestrict _ fun z => twistedIncl_mem_root σ hK2 hq2 hK hσ z
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => twistedIncl_injective σ.toRingHom ?_, ?_⟩
    · have h' := congrArg Subtype.val h
      exact h'
    rintro ⟨g, hg⟩
    have h := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup
      (σ := σ.toRingHom) hK2 hq2 hK hσ
    rw [← h] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    exact ⟨⟨a, ha⟩, rfl⟩
  let eR := MulEquiv.ofBijective φ hφ
  set F := E'.map eR.symm.toMonoidHom with hF
  have hFJ : F ≤ FixedSub σ := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← mem_J_iff σ hK2 hq2 hK hσ hσ3]
    have h1 : twistedIncl σ.toRingHom (eR.symm.toMonoidHom y) =
        ((eR (eR.symm y) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
          ModGL TwistTag.D4.tag K) := rfl
    rw [h1, MulEquiv.apply_symm_apply]
    exact (CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_mem_trialityFieldImage_self_iff σ hσ3 y).2
      (hfix y hy)
  have hFp : ∀ x ∈ F, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change (eR.symm y) ^ 3 = 1
    rw [← map_pow, hE'3 y hy, map_one]
  have hFc : Nat.card F = 3 ^ 2 := by
    rw [hF, Subgroup.card_map_of_injective eR.symm.injective, hE'c]
  have hgen := closure_cenGen_twistedGroup_three σ hσ3 hK2 hq3 hK hσ h3q F hFJ hFp hFc
  have hE'gen : Subgroup.closure (cenGen E') = ⊤ := closure_cenGen_eq_top_of_map eR.symm E' hgen
  change Subgroup.closure (cenGen E') = ⊤ at hE'gen
  have h := Proving.closure_centralizers_map_mulAut (β⁻¹) E
  change Subgroup.closure (cenGen E') = _ at h
  rw [hE'gen, ← Subgroup.map_top_of_surjective (β⁻¹).toMonoidHom (β⁻¹).surjective] at h
  exact (Subgroup.map_injective (β⁻¹).injective h).symm

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
