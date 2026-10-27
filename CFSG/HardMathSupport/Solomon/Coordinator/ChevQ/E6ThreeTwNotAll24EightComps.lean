module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EightComp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EightRoot
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSEight

open TauCeti CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Seitz CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open scoped MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

section Lang


theorem exists_langSetup_conj_of_inndiag_twE6_iota {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ ℓ ^ f)
    (hmon : MonomialToralAt Tag.E6 p)
    (β : MulAut ↥(twistedE6RootGroup K σ)) (h : ModGL TwistTag.E6.tag K)
    (hh : h ∈ twistedE6InndiagGL K σ)
    (hβ : ∀ c, (β c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹) (hp1 : h ^ p = 1) (hh1 : h ≠ 1) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) p₀)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = ℓ ^ f ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
        S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr) ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      S.D.g0 * rootDiagUnit Tag.E6 a * S.D.g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∧
      ∀ c : twistedE6RootGroup K σ, S.D.g0 * ι c * S.D.g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c =>
    iterateFrobenius_def ℓ f c
  set u : ModGL TwistTag.E6.tag L := baseChangeGL ι₁ h with hu
  have huF : u ∈ twistedFixedGroup TwistTag.E6 L (iterateFrobenius L ℓ f) :=
    map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ (iterateFrobenius L ℓ f) hFr
      ⟨h, hh, rfl⟩
  have huG : u ∈ adjointGroup TwistTag.E6.tag L := huF.1
  have hufix : twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) u = u := huF.2
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hh1 (baseChangeGL_injective ι₁ (by rw [map_one]; exact h'))
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon hpℓ.symm
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) huG hup
  obtain ⟨D, hΦ, hDq, hmem⟩ := exists_langDatum_of_toral_twisted TwistTag.E6 f hf hufix hconj
  set ι₀ : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL ι₁).comp (twistedE6RootGroup K σ).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrange₀ : ι₀.range = (twistedE6RootGroup K σ).map (baseChangeGL ι₁) := by
    rw [hι₀, MonoidHom.range_comp, Subgroup.range_subtype]
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
    rw [hrange₀]
    exact Γ_eq_map_twistedE6RootGroup hℓ hf hK hσ hFr D hΦ
  have hfin : Finite D.model := finite_model_twistedE6 hℓ hf hK hσ hFr D hΦ
  have hβ' : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ (β c : ModGL TwistTag.E6.tag K) = baseChangeGL ι₁ h *
      baseChangeGL ι₁ (c : ModGL TwistTag.E6.tag K) * (baseChangeGL ι₁ h)⁻¹
    rw [hβ c, map_mul, map_mul, map_inv]
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D.q := by
    rw [hDq]
    exact hq₀
  obtain ⟨S, a, -, hSD, hT, hap, h1, -, -, -, hg0⟩ :=
    exists_langSetup_conj_of_toral_datum hℓ hf D hDq hp₀ hp₀ℓ hq' hfin ι₀ hι₀inj hΓ β hβ' hmem
      hup hu1
  subst hSD
  refine ⟨S, a, (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp ι₀, hDq,
    ⟨iterateFrobenius L ℓ f, hFr, hΦ⟩, hT, hap, h1,
    (MulAut.conj S.D.g0⁻¹).injective.comp hι₀inj, ?_, fun c => ?_, hg0, fun c => ?_⟩
  · show _ = S.D.Γ
    rw [hΓ]
    exact MonoidHom.range_comp _ _
  · change (MulAut.conj S.D.g0⁻¹) (ι₀ (β c)) =
      rootDiagUnit _ a * (MulAut.conj S.D.g0⁻¹) (ι₀ c) * (rootDiagUnit _ a)⁻¹
    simp only [MulAut.conj_apply, inv_inv]
    rw [hβ' c, ← hg0]
    group
  · change S.D.g0 * (MulAut.conj S.D.g0⁻¹) (ι₀ c) * S.D.g0⁻¹ = ι₀ c
    rw [MulAut.conj_apply, inv_inv]
    group

end Lang

section Stable

variable {τ : Tag} {L : Type} [Field L]

theorem rationalComponent_le_rootSpan (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (Γ : Subgroup (ModGL τ L)) (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ)
    (i : KernelComponent χ) (hρ : ∀ γ ∈ componentRoots χ i, ρ γ ∈ componentRoots χ i) :
    rationalComponent ρ Γ χ i ≤ rootSpan τ L (componentRoots χ i) := by
  have hsub : rationalRoots ρ χ i ⊆ componentRoots χ i := by
    rintro γ ⟨k, δ, hδ, rfl⟩
    induction k with
    | zero => exact hδ
    | succ k ih => rw [Function.iterate_succ_apply']; exact hρ _ ih
  calc rationalComponent ρ Γ χ i ≤ rationalSpan ρ Γ χ i :=
        Subgroup.commutator_le.2 fun x hx y hy => by
          rw [commutatorElement_def]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
            (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    _ ≤ rootSpan τ L (rationalRoots ρ χ i) := inf_le_left
    _ ≤ rootSpan τ L (componentRoots χ i) := biSup_mono fun γ hγ => hsub hγ

end Stable

section Class


variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem exists_lieIndex_or_slCover_of_conn_class (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    (h3 : ((3 : ℕ) : L) ≠ 0) (hL2 : ringChar L = 2) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) (h3q : 3 ∣ S.D.q + 1)
    (hk : (kernelRoots (rootCharHom a)).ncard = 22 ∨ (kernelRoots (rootCharHom a)).ncard = 30)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    (∃ d : ValidLieTypeIndex,
      Nonempty ((↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≃*
          (CFSGIndex.lie d).Group) ∧
        3 ≠ d.1.characteristic ∧ ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1) ∨
    (∃ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β ∧
      rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
        rootSubgroup Tag.E6 L β ⊔ rootSubgroup Tag.E6 L (-β) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K)
        (g : SL(2, K) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)),
        Function.Surjective g ∧ g.ker ≤ Subgroup.center SL(2, K) ∧ Nat.card K = S.D.q ∧
          ringChar K = 2) := by
  classical
  obtain ⟨m, hm, ψ, σ, π, hψ, hΨ, hπ1, hs1, -, hS1⟩ :=
    KSConn.conn_class_unitary S hFr hΦ h3 hT hap h3q hk i
  have hπ : ∀ x y, x ≠ y → (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x) := fun x y hxy => by
    rw [hs1, Function.iterate_one]
    exact hπ1 x y hxy
  obtain ⟨r, e, hr, hchar, he, hq⟩ := S.exists_char_pow
  have hr2 : r = 2 := (ringChar.eq L r).symm.trans hL2
  subst hr2
  rcases hm with rfl | rfl | rfl
  ·
    right
    obtain ⟨β, hβ, hΨβ⟩ := exists_pair_of_rank_one i (hS1 rfl).2.1
    have hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
        S.ρ γ ∈ componentRoots (rootCharHom a) i := by
      intro γ hγ
      rw [hΨ] at hγ ⊢
      obtain ⟨x, y, hxy, rfl⟩ := hγ
      exact ⟨π y, π x, fun h => hxy (π.injective h).symm, hπ1 x y hxy⟩
    have hle := rationalComponent_le_rootSpan S.ρ S.Γ (rootCharHom a) i hstab
    rw [hΨβ] at hle
    simp only [rootSpan, iSup_insert, iSup_singleton] at hle
    obtain ⟨K, _, _, g, hg, hgk, hKcard, -, hring⟩ :=
      KSConn.exists_slCover_of_rankOne S hT i (hS1 rfl).1 (hS1 rfl).2.1 hQS hr hchar he hq
    rw [hs1, Nat.mul_one, ← hq] at hKcard
    exact ⟨β, hβ, hle, K, inferInstance, inferInstance, g, hg, hgk, hKcard, hring⟩
  ·
    left
    have hmodel := KSExact.rationalComponent_suN_model S hT i (ν := 4 + 1) (by norm_num) hψ hΨ π
      hπ hr hchar he hq (by simp)
    rw [hs1, Nat.mul_one] at hmodel
    obtain ⟨q', hv, hqp, hqf, ⟨eq⟩⟩ := KSExact.exists_twistedA_of_statedClassicalModel_PSU hmodel
    refine ⟨⟨LieTypeIndex.twistedA 4 q', hv⟩, ⟨eq⟩, ?_, ?_⟩
    · simp [hqp]
    · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
  ·
    left
    have hmodel := KSExact.rationalComponent_suN_model S hT i (ν := 5 + 1) (by norm_num) hψ hΨ π
      hπ hr hchar he hq (by simp)
    rw [hs1, Nat.mul_one] at hmodel
    obtain ⟨q', hv, hqp, hqf, ⟨eq⟩⟩ := KSExact.exists_twistedA_of_statedClassicalModel_PSU hmodel
    refine ⟨⟨LieTypeIndex.twistedA 5 q', hv⟩, ⟨eq⟩, ?_, ?_⟩
    · simp [hqp]
    · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]

end Class

noncomputable def mulEquivPSLOfSLCoverCharTwo {R : Type} [Group R] {K : Type} [Field K]
    [CharP K 2] (g : SL(2, K) →* R) (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center SL(2, K)) :
    R ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  have hZ := CFSG.Walter.sl2_center_eq_bot_of_charTwo (K := K)
  have hinj : Function.Injective g :=
    (MonoidHom.ker_eq_bot_iff g).1 (le_bot_iff.1 (hZ ▸ hgk))
  ((MulEquiv.ofBijective g ⟨hinj, hg⟩).symm.trans QuotientGroup.quotientBot.symm).trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)

section Main


theorem twE6EightComps : TwE6EightComps := by
  classical
  intro K _ _ σ q E hcube hq8 f hfE hf1 hdim J hJ
  subst hq8
  obtain ⟨h, hh, hd⟩ := hdim
  have hf3 : f ^ 3 = 1 := hcube.elemAbelian.2 f hfE
  have hinj := twE6_conj_injective K σ 8 hcube.frob hcube.card_field (by norm_num)
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hf1 (hh.symm.trans (map_one _))
  have hh3 : h ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hh, map_one]
    exact hf3
  refine ⟨components_invariant_of_mem K σ 8 hcube.char_ne_three hcube.frob hcube.card_field
    (by norm_num) hcube.elemAbelian hfE h hh hh1 hh3 (by rw [hd]; simp) J hJ, ?_⟩
  subst hh
  have hJ0 := hJ
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨hp, e, he, hqe⟩ :=
    prime_ringChar_and_eq_pow_of_card_sq K 8 hcube.card_field (by norm_num)
  have hK2 : ringChar K = 2 := by
    have h1 : ringChar K ∣ 2 ^ 3 := ⟨ringChar K ^ (e - 1), by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, hqe, ← pow_succ']
      congr 1
      omega⟩
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
  have he3 : e = 3 := by
    rw [hK2, show (8 : ℕ) = 2 ^ 3 by norm_num] at hqe
    exact (Nat.pow_right_injective le_rfl hqe).symm
  have hK' : Nat.card K = (ringChar K ^ e) ^ 2 := by rw [← hqe]; exact hcube.card_field
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ e) := by intro c; rw [← hqe]; exact hcube.frob c
  have hpℓ : 3 ≠ ringChar K := fun h' => hcube.char_ne_three h'.symm
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hp he Nat.prime_three (by norm_num) hpℓ
  have hh3' : (h : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hh3]
    rfl
  have hh1' : (h : ModGL TwistTag.E6.tag K) ≠ 1 := fun h' => hh1 (Subtype.ext h')
  obtain ⟨S, a, ι, hDq, ⟨Fr, hFr, hΦ⟩, hT, hap, h1, hinjι, hrange, hconj, hg0, hιf⟩ :=
    exists_langSetup_conj_of_inndiag_twE6_iota hp he hK' σ hσ' Nat.prime_three hpℓ hp₀ hp₀ℓ hq₀
      monomialToralAt_E6_three (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) hh3' hh1'
  have hker := twE6MatFixDim_eq_of_conj σ h S.D.g0 a hg0
  have h22 : (kernelRoots (rootCharHom a)).ncard = 22 := by omega
  have hL3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne hp Nat.prime_three hK' hpℓ
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hL3 (fun h => absurd h (by decide)) hT
    hap h1
  rw [← fixSubgroup_eq_fixedPoints] at hJ
  obtain ⟨i, hQS, hi⟩ := components_of_langSetup S Nat.prime_three ι hinjι hrange
    (twistedE6InndiagConj K σ h) hconj hT hap h1 hTame hJ
  have eJ : J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinjι).trans (MulEquiv.subgroupCongr hi)
  have h3q' : 3 ∣ S.D.q + 1 := by rw [hDq, ← hqe]; exact hcube.three_dvd
  have hFr' : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hDq]; exact hFr c
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
  have hL2 : ringChar (AlgebraicClosure K) = 2 := by
    rw [ringChar.eq (AlgebraicClosure K) (ringChar K), hK2]
  rcases exists_lieIndex_or_slCover_of_conn_class S hFr' hΦ hL3 hL2 hT hap h3q' (Or.inl h22) i
      hQS with ⟨d, ⟨ed⟩, hd3, hexc⟩ | ⟨β, hβ, hle, K', _, _, g, hg, hgk, hK'card, hK'2⟩
  ·
    left
    have hZ := KSConn.not_three_dvd_center_of_dim K σ 8 hcube.char_ne_three hcube.frob
      hcube.card_field (by norm_num) hcube.three_dvd h hh1 hh3 (Or.inl hd) hJ0
    exact Or.inl ⟨hZ, d, (QuotientGroup.congr (Subgroup.center J) (Subgroup.center _) eJ
      (Subgroup.map_center_eq eJ)).trans ed, hd3, hexc⟩
  ·
    right
    haveI : CharP K' 2 := ringChar.of_eq hK'2
    refine ⟨⟨K', inferInstance, inferInstance, ?_,
      ⟨eJ.trans (mulEquivPSLOfSLCoverCharTwo g hg hgk)⟩⟩, fun s hs hs9 h' => ?_⟩
    · rw [hK'card, hDq, hK2, he3]
    ·
      haveI : CharP K 2 := ringChar.of_eq hK2
      haveI : CharP (AlgebraicClosure K) 2 :=
        charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
      have hsR : ι s ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
        rw [← hi]
        exact Subgroup.mem_map_of_mem ι hs
      have hy9 : orderOf (ι s) = 9 := by rw [orderOf_injective ι hinjι s]; exact hs9
      obtain ⟨B, hB⟩ : ∃ B : ModGL Tag.E6 (AlgebraicClosure K),
          B = baseChangeGL (algebraMap K (AlgebraicClosure K)) (h' : ModGL TwistTag.E6.tag K) :=
        ⟨_, rfl⟩
      obtain ⟨T, hT⟩ : ∃ T : ModGL Tag.E6 (AlgebraicClosure K),
          T = baseChangeGL (algebraMap K (AlgebraicClosure K)) (s : ModGL TwistTag.E6.tag K) :=
        ⟨_, rfl⟩
      have e1 : ι s = S.D.g0⁻¹ * T * S.D.g0 := by
        rw [hT, ← hιf s]
        group
      have hconjk : ∀ k : ℕ, twistedE6InndiagConj K σ h' s = s ^ k →
          (S.D.g0⁻¹ * B * S.D.g0) * ι s * (S.D.g0⁻¹ * B * S.D.g0)⁻¹ = ι s ^ k := by
        intro k hk
        have e3 : baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((twistedE6InndiagConj K σ h' s : twistedE6RootGroup K σ) :
              ModGL TwistTag.E6.tag K) =
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (h' : ModGL TwistTag.E6.tag K) *
              baseChangeGL (algebraMap K (AlgebraicClosure K)) (s : ModGL TwistTag.E6.tag K) *
                (baseChangeGL (algebraMap K (AlgebraicClosure K))
                  (h' : ModGL TwistTag.E6.tag K))⁻¹ := by
          rw [twistedE6InndiagConj_apply, map_mul, map_mul, map_inv]
        have e3' : S.D.g0 * ι (twistedE6InndiagConj K σ h' s) * S.D.g0⁻¹ = B * T * B⁻¹ := by
          rw [hιf, hB, hT]
          exact e3
        have e2 : ι s ^ k = S.D.g0⁻¹ * (B * T * B⁻¹) * S.D.g0 := by
          rw [← e3', ← map_pow, ← hk]
          group
        rw [e2, e1]
        group
      exact ⟨fun h4 => conj_ne_pow_of_mem_rootPair hβ (hle hsR) hy9 _ (k := 4) (Or.inl rfl)
        (hconjk 4 h4), fun h7 => conj_ne_pow_of_mem_rootPair hβ (hle hsR) hy9 _ (k := 7)
        (Or.inr rfl) (hconjk 7 h7)⟩

end Main

end KSEight

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
