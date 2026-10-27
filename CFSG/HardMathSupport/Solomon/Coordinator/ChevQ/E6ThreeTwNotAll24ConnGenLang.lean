module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenPlane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreStab
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourNonInnerData

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn

set_option linter.unusedSectionVars false


theorem exists_langDatum_of_toral_pair_twisted (t : TwistTag) {L : Type} [Field L] [IsAlgClosed L]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (f : ℕ) (hf : 1 ≤ f) {u v : ModGL t.tag L}
    (hfixu : twistHom t L (iterateFrobenius L ℓ f) u = u)
    (hfixv : twistHom t L (iterateFrobenius L ℓ f) v = v)
    {g : ModGL t.tag L} (hg : g ∈ adjointGroup t.tag L) (hgu : g⁻¹ * u * g ∈ torusGroup t.tag L)
    (hgv : g⁻¹ * v * g ∈ torusGroup t.tag L) :
    ∃ D : LangDatum t.tag L, D.Φ = twistHom t L (iterateFrobenius L ℓ f) ∧ D.q = ℓ ^ f ∧
      u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom ∧
      v ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom := by
  set A : Subgroup (ModGL t.tag L) := Subgroup.closure {u, v} with hA
  have hAfix : ∀ x ∈ A, twistHom t L (iterateFrobenius L ℓ f) x = x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => rcases hx with rfl | rfl <;> assumption
    | one => exact map_one _
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    | inv x _ hx => rw [map_inv, hx]
  have hAT : A ≤ (torusGroup t.tag L).comap (MulAut.conj g⁻¹).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x (rfl | rfl)
    · simpa [MulAut.conj_apply] using hgu
    · simpa [MulAut.conj_apply] using hgv
  obtain ⟨w, g0, hg0, hF, hmem⟩ := exists_lang_torus_of_conj_torus_twisted ℓ t f hf
    (A := A) hAfix hg (fun x hx => by simpa [MulAut.conj_apply] using hAT hx)
  exact ⟨LangDatum.ofTwist t (iterateFrobenius L ℓ f) (ℓ ^ f) (iterateFrobenius_def ℓ f) w hg0 hF,
    rfl, rfl, hmem u (Subgroup.subset_closure (Set.mem_insert _ _)),
    hmem v (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩

theorem exists_torus_param_of_mem_map {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L} {p : ℕ}
    {u : ModGL τ L} (hmem : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom) (hup : u ^ p = 1) :
    ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D.torus ∧ (∀ i, a i ^ p = 1) ∧
      D.g0 * rootDiagUnit τ a * D.g0⁻¹ = u := by
  obtain ⟨y, hy, hyu⟩ := hmem
  have hyu' : y = D.g0⁻¹ * u * D.g0 := by
    have h : D.g0 * y * D.g0⁻¹ = u := hyu
    rw [← h]
    group
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hy).1
  have hyp : y ^ p = 1 := by
    have h := conj_pow (a := D.g0⁻¹) (b := u) (i := p)
    rw [inv_inv] at h
    rw [hyu', h, hup]
    group
  refine ⟨a, ha ▸ hy, fun i => ?_, ?_⟩
  · have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      have : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p :=
        (rootDiagUnitHom τ L).map_pow a p
      rw [this, ← ha, hyp, CFSG.LieType.Chevalley.rootDiagUnit_one]
    have h2 : a ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact congrFun h2 i
  · rw [← ha, hyu']
    group

theorem exists_langSetup_pair_of_toral_datum {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hf : 1 ≤ f) (D : LangDatum τ L) (hDq : D.q = ℓ ^ f)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ D.q) {p : ℕ}
    (hfin : Finite D.model) {C : Type} [Group C] (ι₀ : C →* ModGL τ L)
    (hι₀ : Function.Injective ι₀)
    (hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom) (β β' : MulAut C)
    {u u' : ModGL τ L} (hβ : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹)
    (hβ' : ∀ c, ι₀ (β' c) = u' * ι₀ c * u'⁻¹)
    (hmem : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom)
    (hmem' : u' ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom) (hup : u ^ p = 1)
    (hup' : u' ^ p = 1) (hu1 : u ≠ 1) :
    ∃ (S : LangSetup τ L p₀) (a b : Fin τ.rank → Lˣ) (ι : C →* ModGL τ L),
      S.D = D ∧ rootDiagUnit τ a ∈ S.D.torus ∧ rootDiagUnit τ b ∈ S.D.torus ∧
      (∀ i, a i ^ p = 1) ∧ (∀ i, b i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹) ∧
      (∀ c, ι (β' c) = rootDiagUnit τ b * ι c * (rootDiagUnit τ b)⁻¹) ∧
      D.g0 * rootDiagUnit τ a * D.g0⁻¹ = u ∧ D.g0 * rootDiagUnit τ b * D.g0⁻¹ = u' := by
  classical
  obtain ⟨a, haT, hap, hga⟩ := exists_torus_param_of_mem_map hmem hup
  obtain ⟨b, hbT, hbp, hgb⟩ := exists_torus_param_of_mem_map hmem' hup'
  have h1 : rootDiagUnit τ a ≠ 1 := by
    intro h
    apply hu1
    rw [← hga, h]
    group
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    rw [hDq]
    exact ⟨hℓ.isPrimePow.pow (by omega), (CharP.cast_eq_zero_iff L ℓ _).2
      (dvd_pow_self ℓ (by omega))⟩
  have hpq : ¬ p₀ ∣ D.q := by
    rw [hDq]
    intro h
    exact hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow h))
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ L D
  let ι : C →* ModGL τ L := (MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀
  have hι : ∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0 := fun c => by
    change (MulAut.conj D.g0⁻¹) (ι₀ c) = _
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨D.toSetup p₀ ρ hρ hp₀ hq₀ hqpow hpq hfin, a, b, ι, rfl, haT, hbT, hap, hbp, h1,
    (MulAut.conj D.g0⁻¹).injective.comp hι₀, ?_, fun c => ?_, fun c => ?_, hga, hgb⟩
  · show ι.range = D.Γ
    rw [hΓ]
    exact MonoidHom.range_comp (MulAut.conj D.g0⁻¹).toMonoidHom ι₀
  · rw [hι, hι, hβ c, ← hga]
    group
  · rw [hι, hι, hβ' c, ← hgb]
    group

theorem exists_langSetup_pair_of_inndiag_twE6 {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hℓ3 : ℓ ≠ 3) {p₀ : ℕ} (hp₀ : p₀.Prime)
    (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ ℓ ^ f) (h h' : twistedE6InndiagGL K σ)
    (hcomm : h * h' = h' * h) (hh3 : h ^ 3 = 1) (hh'3 : h' ^ 3 = 1) (hh1 : h ≠ 1)
    (hdim : twE6MatFixDim K σ h = 28 ∨ twE6MatFixDim K σ h = 36 ∨ twE6MatFixDim K σ h = 46) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) p₀)
      (a b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K),
      S.D.q = ℓ ^ f ∧ (∀ c, Fr c = c ^ (ℓ ^ f)) ∧ S.D.Φ = twistHom TwistTag.E6 _ Fr ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ rootDiagUnit Tag.E6 b ∈ S.D.torus ∧
      (∀ i, a i ^ 3 = 1) ∧ (∀ i, b i ^ 3 = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (twistedE6InndiagConj K σ h c) =
        rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      (∀ c, ι (twistedE6InndiagConj K σ h' c) =
        rootDiagUnit Tag.E6 b * ι c * (rootDiagUnit Tag.E6 b)⁻¹) ∧
      twE6MatFixDim K σ h = 6 + (kernelRoots (rootCharHom a)).ncard := by
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
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c =>
    iterateFrobenius_def ℓ f c
  set u : ModGL TwistTag.E6.tag L := baseChangeGL ι₁ h with hu
  set u' : ModGL TwistTag.E6.tag L := baseChangeGL ι₁ h' with hu'
  have huF : u ∈ twistedFixedGroup TwistTag.E6 L (iterateFrobenius L ℓ f) :=
    map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ (iterateFrobenius L ℓ f) hFr
      ⟨h, h.2, rfl⟩
  have hu'F : u' ∈ twistedFixedGroup TwistTag.E6 L (iterateFrobenius L ℓ f) :=
    map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ (iterateFrobenius L ℓ f) hFr
      ⟨h', h'.2, rfl⟩
  have huG : u ∈ adjointGroup TwistTag.E6.tag L := huF.1
  have hu'G : u' ∈ adjointGroup TwistTag.E6.tag L := hu'F.1
  have hup : u ^ 3 = 1 := by
    rw [hu, ← map_pow]
    have : (h : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hh3]
      rfl
    rw [this, map_one]
  have hu'p : u' ^ 3 = 1 := by
    rw [hu', ← map_pow]
    have : (h' : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hh'3]
      rfl
    rw [this, map_one]
  have hu1 : u ≠ 1 := fun h' => hh1 (Subtype.ext (baseChangeGL_injective ι₁
    (by rw [Subgroup.coe_one, map_one]; exact h')))
  have hcommu : u * u' = u' * u := by
    rw [hu, hu', ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val hcomm
  have hstab : ∀ c ∈ adjointGroup TwistTag.E6.tag L, ∀ a : Fin Tag.E6.rank → Lˣ,
      c * u * c⁻¹ = rootDiagUnit TwistTag.E6.tag a → (∀ i, a i ^ 3 = 1) →
        rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
    intro c hc a hca hap
    have hg : c⁻¹ * rootDiagUnit TwistTag.E6.tag a * c⁻¹⁻¹ =
        baseChangeGL ι₁ (h : ModGL TwistTag.E6.tag K) := by
      have h1 : c⁻¹ * rootDiagUnit TwistTag.E6.tag a * c⁻¹⁻¹ = u := by
        rw [← hca]
        group
      exact h1.trans hu
    have hker := twE6MatFixDim_eq_of_conj σ h c⁻¹ a hg
    exact e6_stab_le_kernelReflectionGroup_of_conn a hap (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega)
  obtain ⟨C, hC, hCu, hCu'⟩ : ∃ C : ModGL TwistTag.E6.tag L,
      C ∈ adjointGroup TwistTag.E6.tag L ∧ C * u * C⁻¹ ∈ torusGroup TwistTag.E6.tag L ∧
        C * u' * C⁻¹ ∈ torusGroup TwistTag.E6.tag L :=
    exists_conj_pair_mem_torusGroup monomialToralAt_E6_three
      (hℓ3) (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) huG hu'G hcommu hup hu'p hstab
  obtain ⟨D, hΦ, hDq, hmem, hmem'⟩ := exists_langDatum_of_toral_pair_twisted TwistTag.E6 f hf
    huF.2 hu'F.2 (g := C⁻¹) (inv_mem hC) (by rw [inv_inv]; exact hCu) (by rw [inv_inv]; exact hCu')
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
  have hβ' : ∀ c, ι₀ (twistedE6InndiagConj K σ h c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ (twistedE6InndiagConj K σ h c : ModGL TwistTag.E6.tag K) =
      baseChangeGL ι₁ h * baseChangeGL ι₁ (c : ModGL TwistTag.E6.tag K) *
        (baseChangeGL ι₁ h)⁻¹
    rw [twistedE6InndiagConj_apply, map_mul, map_mul, map_inv]
  have hβ'' : ∀ c, ι₀ (twistedE6InndiagConj K σ h' c) = u' * ι₀ c * u'⁻¹ := fun c => by
    change baseChangeGL ι₁ (twistedE6InndiagConj K σ h' c : ModGL TwistTag.E6.tag K) =
      baseChangeGL ι₁ h' * baseChangeGL ι₁ (c : ModGL TwistTag.E6.tag K) *
        (baseChangeGL ι₁ h')⁻¹
    rw [twistedE6InndiagConj_apply, map_mul, map_mul, map_inv]
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D.q := by
    rw [hDq]
    exact hq₀
  obtain ⟨S, a, b, ι, rfl, haT, hbT, hap, hbp, h1, hinj, hrange, hca, hcb, hga, hgb⟩ :=
    exists_langSetup_pair_of_toral_datum hℓ hf D hDq hp₀ hp₀ℓ hq' hfin ι₀ hι₀inj hΓ
      (twistedE6InndiagConj K σ h) (twistedE6InndiagConj K σ h') hβ' hβ'' hmem hmem' hup hu'p hu1
  have hker := twE6MatFixDim_eq_of_conj σ h S.D.g0 a hga
  exact ⟨S, a, b, ι, iterateFrobenius L ℓ f, hDq, hFr, hΦ, haT, hbT, hap, hbp, h1, hinj, hrange,
    hca, hcb, hker⟩

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
