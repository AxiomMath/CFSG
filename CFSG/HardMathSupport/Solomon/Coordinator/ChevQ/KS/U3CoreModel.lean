module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourIn
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU8Core
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU10
public import CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSU3Core

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourInAux CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

theorem isEntrywiseProj_unique {n : ℕ} {K : Type} [Field K] (H : Subgroup (GL (Fin n) K))
    (σ : K ≃+* K) {ψ₁ ψ₂ : MulAut (StatedProj H)} (h₁ : IsEntrywiseProj H σ ψ₁)
    (h₂ : IsEntrywiseProj H σ ψ₂) : ψ₁ = ψ₂ := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨g₁, hg₁, e₁⟩ := h₁ g
    obtain ⟨g₂, hg₂, e₂⟩ := h₂ g
    have : g₁ = g₂ := Subtype.ext (hg₁.trans hg₂.symm)
    rw [e₁, e₂, this]

theorem exists_unitaryPSU_model_of_fieldAutU {S : Type} [Group S] {φ : MulAut S}
    (hφ : FieldAutU 3 S φ) :
    ∃ (F : Type) (_ : Field F) (h : UnitaryFieldData 2 3 F) (e : S ≃* unitaryPSU h 3),
      MulAut.congr e φ ∉ (psuConj h).range := by
  obtain ⟨K, hK, hfin, e, σ, γ, hcard, hσ1, hodd, hent⟩ := hφ
  have h : UnitaryFieldData 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [hcard]; norm_num⟩
  let U := unitaryPSUEquiv h (n := 3) (by norm_num)
  refine ⟨K, hK, h, e.trans U.symm, ?_⟩
  intro hmem
  have hq : 2 < 2 ^ 3 := by norm_num
  have hN : (psuConj h).range.Normal := (stdPinnedPSU3_stable (h := h) hq).normal
  set c : MulAut (unitaryPSU h 3) := MulAut.congr U.symm γ with hc
  have hψ : MulAut.congr U.symm (γ * MulAut.congr e φ * γ⁻¹) = psuField h σ := by
    have h1 : IsEntrywiseProj (StatedSU 3 (2 ^ 3) K) σ
        (MulAut.congr U (psuField h σ)) := isEntrywiseProj_congr_psuField h σ
    have h2 := isEntrywiseProj_unique _ σ hent h1
    rw [h2]
    ext x
    simp [MulAut.congr_apply]
  have hconj : c * MulAut.congr (e.trans U.symm) φ * c⁻¹ = psuField h σ := by
    rw [← hψ]
    ext x
    simp [hc, MulAut.congr_apply, MulEquiv.trans_apply]
  have hmem' : psuField h σ ∈ (psuConj h).range := by
    rw [← hconj]
    exact hN.conj_mem _ hmem c
  obtain ⟨A, hA⟩ := hmem'
  have h1 : psuConj h A⁻¹ * psuField h σ = 1 := by rw [map_inv, hA]; exact inv_mul_cancel _
  exact hσ1 (eq_one_of_psuConj_mul_psuField_eq_one A⁻¹ σ h1).1

theorem exists_mulEquiv_unitarySU_three_compat
    {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : 2 < p ^ f) {K : Type} [Group K] [Finite K]
    (hK : commutator K = ⊤) (e : K ⧸ Subgroup.center K ≃* unitaryPSU h 3)
    (hz : Subgroup.center K ≠ ⊥) :
    ∃ ψ : unitarySU p f F 3 ≃* K, ∀ s, e (QuotientGroup.mk (ψ s)) = unitaryProj h 3 s := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  let β : unitarySU p f F 3 →* unitaryPSU h 3 := unitaryProj h 3
  let η : K →* unitaryPSU h 3 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hβ : Function.Surjective β := unitaryProj_surjective h 3
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : ∀ z, η z = 1 ↔ z ∈ Subgroup.center K := fun z => by
    change e (QuotientGroup.mk z) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have hcen : η.ker ≤ Subgroup.center K := fun z hz => (hηker z).1 hz
  have hsec := SUOdd.statedSU_odd_exists_section_of_central h.card_eq_sq h.one_le
    (n := 3) (by norm_num) (by decide) (fun hh => by simp only [Prod.mk.injEq] at hh; omega)
    (pullbackFst_surjective (β := β) hη)
    (ker_pullbackFst_le_center (β := β) hcen)
  obtain ⟨α, hα, hαsurj⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift.exists_surjective_lift
    hK hβ hcen hsec
  obtain ⟨⟨z, hzc⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hz
  have hz1 : z ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  obtain ⟨s, hs⟩ := hαsurj z
  have hβker : β.ker = unitaryScalars h 3 := ker_unitaryProj h 3
  have hsker : s ∈ β.ker := by
    rw [MonoidHom.mem_ker, ← hα, hs]
    exact (hηker z).2 hzc
  have hαker : α.ker ≤ unitaryScalars h 3 := fun t ht => by
    rw [← hβker, MonoidHom.mem_ker, ← hα, MonoidHom.mem_ker.1 ht, map_one]
  have hcard : Nat.card (unitaryScalars h 3) ∣ 3 := by
    rw [card_unitaryScalars h (by norm_num)]
    exact Nat.gcd_dvd_left _ _
  have hinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift.ker_eq_bot_of_card_dvd_prime Nat.prime_three
      α hαker hcard ⟨s, hβker ▸ hsker, by rw [hs]; exact hz1⟩
  refine ⟨MulEquiv.ofBijective α ⟨hinj, hαsurj⟩, fun s => ?_⟩
  exact hα s

theorem mem_of_isSCp_of_commute {X : Type} [Group X] {B : Subgroup X} (hB : IsSCp 3 ⊤ B)
    {e : X} (he3 : e ^ 3 = 1) (hcomm : ∀ b ∈ B, b * e = e * b) : e ∈ B := by
  have hz : IsElemAbelian 3 (Subgroup.zpowers e) := by
    have := IsElemAbelian.closure_of_commute (p := 3) (s := ({e} : Set X))
      (by simp) (by simp [he3])
    rwa [← Subgroup.zpowers_eq_closure] at this
  have hsup : IsElemAbelian 3 (B ⊔ Subgroup.zpowers e) :=
    IsElemAbelian.sup_of_commute hB.2.1 hz (fun b hb a ha => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      have hc : Commute b e := hcomm b hb
      exact (hc.zpow_right k).eq)
  have := hB.2.2 _ le_top hsup le_sup_left
  rw [← this]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)

theorem isElemAbelian_autImage {X : Type} [Group X] {B K : Subgroup X}
    (hB : IsElemAbelian 3 B) : IsElemAbelian 3 (autImage B K) :=
  IsElemAbelian.map (IsElemAbelian.subgroupOf (IsElemAbelian.mono hB inf_le_left) _) _

theorem eq_bot_of_fixedPointFree {G : Type*} [Group G] {D T : Subgroup G} {c : G} [Finite T]
    (hexp : ∀ d ∈ D, d ^ 12 = 1)
    (hV : ∀ u ∈ D, ∀ v ∈ D, u ^ 2 = 1 → v ^ 2 = 1 → u * v = v * u → u = 1 ∨ v = 1 ∨ u = v)
    (hTD : T ≤ D) (hT3 : ¬ 3 ∣ Nat.card T) (hc : c ∈ Subgroup.normalizer (T : Set G))
    (hfix : ∀ t ∈ T, c * t = t * c → t = 1) : T = ⊥ := by
  by_contra hne
  haveI : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hne
  have hord : ∀ g : T, g ^ 4 = 1 := by
    intro g
    have h12 : g ^ 12 = 1 := Subtype.ext (by simpa using hexp g (hTD g.2))
    have hd1 : orderOf g ∣ 12 := orderOf_dvd_of_pow_eq_one h12
    have hd2 : orderOf g ∣ Nat.card T := orderOf_dvd_natCard g
    have hcop : Nat.Coprime (orderOf g) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (fun h3 => hT3 (h3.trans hd2))).symm
    have h4 : orderOf g ∣ 4 := hcop.dvd_of_dvd_mul_right (by simpa using hd1)
    exact orderOf_dvd_iff_pow_eq_one.1 h4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 T := fun g => ⟨2, by simpa using hord g⟩
  haveI := hp.center_nontrivial
  obtain ⟨z, hzc, hz1, hz2⟩ : ∃ z : T, z ∈ Subgroup.center T ∧ z ≠ 1 ∧ z ^ 2 = 1 := by
    obtain ⟨z₀, hz₀⟩ := exists_ne (1 : Subgroup.center T)
    have hz₀c : (z₀ : T) ∈ Subgroup.center T := z₀.2
    have hz₀1 : (z₀ : T) ≠ 1 := fun h => hz₀ (Subtype.ext h)
    by_cases h2 : (z₀ : T) ^ 2 = 1
    · exact ⟨z₀, hz₀c, hz₀1, h2⟩
    · refine ⟨(z₀ : T) ^ 2, Subgroup.pow_mem _ hz₀c 2, h2, ?_⟩
      rw [← pow_mul]
      exact hord _
  have hzT : (z : G) ∈ T := z.2
  have huT : c * (z : G) * c⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hc (z : G)).1 hzT
  have hz2G : (z : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hz2
    simpa using this
  have hu2 : (c * (z : G) * c⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hz2G]
    group
  have huv : c * (z : G) * c⁻¹ * (z : G) = (z : G) * (c * (z : G) * c⁻¹) := by
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨_, huT⟩)
    exact this
  rcases hV _ (hTD huT) _ (hTD hzT) hu2 hz2G huv with h | h | h
  · apply hz1
    apply Subtype.ext
    simpa using h
  · exact hz1 (Subtype.ext h)
  · apply hz1
    apply Subtype.ext
    have h1 : c * (z : G) = (z : G) * c := by
      calc c * (z : G) = c * (z : G) * c⁻¹ * c := by group
        _ = (z : G) * c := by rw [h]
    exact hfix _ hzT h1

section G1

variable {F : Type} [Field F]

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

theorem mem_range_suConj_of_coprime (h : UnitaryFieldData 2 3 F)
    {t : MulAut (unitarySU 2 3 F 3)} (ht : Nat.Coprime 3 (orderOf t))
    (htZ : ∀ z ∈ Subgroup.center (unitarySU 2 3 F 3), t z = z) : t ∈ (suConj h).range := by
  have := h.finite
  have hq : 2 < 2 ^ 3 := by norm_num
  obtain ⟨B, δ, hBδ⟩ := exists_suConj_mul_suField h hq t
  have hδ : δ ^ orderOf t = 1 := by
    refine pow_eq_one_of_suConj_mul_suField_pow_eq_one h hq (B := B) ?_
    rw [← hBδ]
    exact pow_orderOf_eq_one t
  have hcard : Nat.card (unitaryScalars h 3) = 3 := by
    rw [card_unitaryScalars h (by norm_num)]
    norm_num
  have hne : unitaryScalars h 3 ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨z, hzmem⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hzC : z ∈ Subgroup.center (unitarySU 2 3 F 3) := by
    rw [center_unitarySU_three (h := h) hq]
    exact hzmem
  obtain ⟨c, -, hc3, hzc⟩ := mem_unitaryScalars.mp hzmem
  have hz1' : z ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  have hc1 : (c : F) ≠ 1 := by
    intro hc
    apply hz1'
    apply Subtype.ext
    rw [hzc]
    have : c = 1 := Units.ext hc
    rw [this, map_one]
    rfl
  have hc3' : (c : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc3]
    rfl
  have hδc : δ (c : F) = c := by
    have h2 := htZ z hzC
    rw [hBδ, MulAut.mul_apply] at h2
    have h3 : suConj h B z = z := by
      apply Subtype.ext
      rw [coe_suConj, hzc, Subgroup.coe_inv, (commute_scalar c _).eq,
        mul_inv_cancel_right]
    have h4 : suField h δ z = z := (suConj h B).injective (h2.trans h3.symm)
    have h5 := congrArg
      (fun w : unitarySU 2 3 F 3 => ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0) h4
    simp only [coe_suField, coe_glAut, hzc] at h5
    simpa using h5
  have hδ1 : δ = 1 :=
    CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.ringEquiv_eq_one h rfl (Or.inr rfl) ht hδ hc3'
      hc1 hδc
  exact ⟨B, by rw [hBδ, hδ1, map_one, mul_one]⟩

end G1

section Model

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.HeisSmall HuppertU38F
  CFSG.RankThree.PartTwo.Sec19.U38F

variable {F : Type} [Field F]

theorem exists_model38 (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    ∃ ι : Q8 →+* F, Function.Surjective ι ∧ IsPrimitiveRoot (ι w0) 3 ∧ σ (ι w0) = ι w0 := by
  have := h.finite
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hK3 : 3 ∣ Nat.card F - 1 := by rw [h.card]; norm_num
  obtain ⟨ω, hω⟩ := CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof.exists_isPrimitiveRoot_three hK3
  obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q8) h (by norm_num)
    (by rw [card_q8]; norm_num) isPrimitiveRoot_w0 hω
  refine ⟨ι, hι, hιω ▸ hω, ?_⟩
  rw [hιω]
  exact CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.ringEquiv_fix_of_cube hσ3 hω.pow_eq_one

theorem toMat_unitary (h : UnitaryFieldData 2 3 F) (ι : Q8 →+* F) {Ym : M3 Q8}
    (hu : unitaryOk Ym = true) : ((toMat ι Ym).map h.bar)ᵀ * toMat ι Ym = 1 := by
  have h1 := toMat_transpose_map h ι Ym
  have hq : 2 ^ 3 = 8 := by norm_num
  rw [hq] at h1
  rw [← h1, ← toMat_mul, of_decide_eq_true hu, toMat_one]

@[expose] noncomputable def toIsom (h : UnitaryFieldData 2 3 F) (ι : Q8 →+* F) (Ym : M3 Q8)
    (hu : unitaryOk Ym = true) : unitaryIsom3 h :=
  ⟨⟨toMat ι Ym, ((toMat ι Ym).map h.bar)ᵀ, mul_eq_one_comm.2 (toMat_unitary h ι hu),
    toMat_unitary h ι hu⟩, toMat_unitary h ι hu⟩

theorem coe_toIsom (h : UnitaryFieldData 2 3 F) (ι : Q8 →+* F) (Ym : M3 Q8)
    (hu : unitaryOk Ym = true) :
    (((toIsom h ι Ym hu : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      toMat ι Ym := rfl

theorem exists_gu2_decomp (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {ι : Q8 →+* F} (hωι : IsPrimitiveRoot (ι w0) 3)
    {W : unitaryIsom3 h}
    (hW : ∃ c : F, ((W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ =
      c • ((W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    ∃ (b : F) (Ym : M3 Q8), b ≠ 0 ∧ entriesL4 Ym = true ∧ unitaryOk Ym = true ∧
      ((W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = b • toMat ι Ym := by
  have := h.finite
  obtain ⟨c, hc⟩ := hW
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F,
      M = ((W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨_, rfl⟩
  rw [← hMdef] at hc ⊢
  have hMu : (M.map h.bar)ᵀ * M = 1 := by rw [hMdef]; exact W.2
  obtain ⟨j0, hb⟩ := CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.exists_apply_ne_zero
    (W : GL (Fin 3) F) 0
  rw [← hMdef] at hb
  set i0 : Fin 3 := 0
  have hcb : σ (M i0 j0) = c * M i0 j0 := by
    have := congrFun (congrFun hc i0) j0
    simpa [Matrix.map_apply, Matrix.smul_apply] using this
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at hcb
    exact hb (σ.injective (by rw [hcb, map_zero]))
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin 3) (Fin 3) F, B' = (M i0 j0)⁻¹ • M := ⟨_, rfl⟩
  have hMB' : M = M i0 j0 • B' := by rw [hB', smul_inv_smul₀ hb]
  have hfix : ∀ i j, σ (B' i j) = B' i j := by
    intro i j
    have hij := congrFun (congrFun hc i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hij
    rw [hB']
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hij, hcb]
    field_simp
  have hfour : ∀ i j, B' i j ^ 4 = B' i j := fun i j => pow_four_of_fixed h hσ (hfix i j)
  have hu : (B'.map h.bar)ᵀ * B' = 1 := unitary_normalize h hb hB' hMu hfour
  obtain ⟨Ym, hYe, hYm⟩ := exists_model_matrix ι rfl hωι hfour
  have hYu : unitaryOk Ym = true := by
    apply decide_eq_true
    apply toMat_inj ι
    rw [toMat_mul, toMat_one]
    have h1 := toMat_transpose_map h ι Ym
    have hq : 2 ^ 3 = 8 := by norm_num
    rw [hq] at h1
    rw [h1, hYm, hu]
  exact ⟨M i0 j0, Ym, hb, hYe, hYu, by rw [hYm, hB', smul_inv_smul₀ hb] <;> exact hMB'⟩

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut) in
theorem suField_not_mem_range (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F} (hσ : σ ≠ 1) :
    suField h σ ∉ (suConj h).range := by
  rintro ⟨W, hW⟩
  have hq : 2 < 2 ^ 3 := by norm_num
  have h1 := congrArg (CFSG.RankThree.PartTwo.Sec19.descPSUHom h hq) hW
  rw [CFSG.RankThree.PartTwo.Sec19.descPSUHom_suConj,
    CFSG.RankThree.PartTwo.Sec19.descPSUHom_suField] at h1
  exact hσ (psuField_mem_range_psuConj_iff.1 ⟨W, h1⟩)

@[expose] def RegularU38 (Y : GL (Fin 3) F) : Prop :=
  (∃ c : F, c ^ 3 = 1 ∧
    ((Y : Matrix (Fin 3) (Fin 3) F)) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) F)) ∧
    ¬ ∃ a b : F, ((Y : Matrix (Fin 3) (Fin 3) F)) ^ 2 =
      a • (Y : Matrix (Fin 3) (Fin 3) F) + b • (1 : Matrix (Fin 3) (Fin 3) F)

end Model

end KSU3Core

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
