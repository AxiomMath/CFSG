module

public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.LieType.AlgebraicGroups.RootCoordinateLang
public import CFSG.RankThree.Chevalley.SteinbergBTNoninnerLocalCore
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

theorem twisted_E6_field_descent_data_of_prime_order {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * f))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (hp : p.Prime) (hp2 : p ≠ 2) (α' : MulAut (twistedE6RootGroup K σ)) (hα'pow : α' ^ p = 1)
    (hη1 : Θ α' ≠ 1) :
    ∃ d : ℕ, f = p * d ∧ 1 ≤ d ∧ ∃ (r s : ℕ) (T ε : K ≃+* K),
      (∀ c, T c = c ^ ℓ ^ d) ∧ (∀ c, ε c = c ^ ℓ ^ (d * (p + 1))) ∧ (α' ^ r) ^ s = α' ∧
      ∃ ψ : MulAut (twistedE6RootGroup K σ), ψ * α' ^ r * ψ⁻¹ = fieldActor σ ε ∧
        ψ * α' * ψ⁻¹ = fieldActor σ (Θ α') := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  have hα'p : orderOf α' = p := orderOf_eq_prime hα'pow (fun h => hη1 (by rw [h, map_one]))
  obtain ⟨η, hηdef⟩ : ∃ η, Θ α' = η := ⟨_, rfl⟩
  obtain ⟨-, -, -, -, -, hcoeΔ, -, hex, -, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK2 σ hσ
  have hηp : η ^ p = 1 := by rw [← hηdef, ← map_pow, hα'pow, map_one]
  replace hη1 : η ≠ 1 := hηdef ▸ hη1
  have hηo : orderOf η = p := orderOf_eq_prime hηp hη1
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hηmem : η ∈ Subgroup.zpowers fr := by rw [hgen]; exact Subgroup.mem_top η
  obtain ⟨k, -, hkη⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hηmem)
  replace hkη : fr ^ k = η := hkη
  have hp2f : p ∣ 2 * f := by
    rw [← hηo, ← hord, ← hkη]
    exact orderOf_pow_dvd k
  have hpf : p ∣ f :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 (by omega)) hp2f
  obtain ⟨d, hd⟩ := hpf
  have hd0 : 1 ≤ d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * p = f := by rw [hd, mul_comm]
  have hdk : 2 * d ∣ k := by
    have h1 : 2 * f ∣ k * p := by
      rw [← hord]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul, hkη, hηp]
    rw [← hdp, ← mul_assoc] at h1
    exact Nat.dvd_of_mul_dvd_mul_right hp.pos h1
  obtain ⟨j, rfl⟩ := hdk
  obtain ⟨T, hTdef⟩ : ∃ T, fr ^ d = T := ⟨_, rfl⟩
  have hT : ∀ c, T c = c ^ ℓ ^ d := fun c => by
    rw [← hTdef]
    exact ringAut_pow_apply_of_frobenius hfr d c
  have hTη : T ^ (2 * j) = η := by rw [← hTdef, ← pow_mul, ← hkη, mul_left_comm, mul_assoc]
  have hT2p : T ^ (2 * p) = 1 := by
    rw [← hTdef, ← pow_mul, show d * (2 * p) = orderOf fr by rw [hord, ← hdp]; ring,
      pow_orderOf_eq_one]
  have hpj : ¬p ∣ j := by
    rintro ⟨t, rfl⟩
    apply hη1
    rw [← hTη, show 2 * (p * t) = 2 * p * t by ring, pow_mul, hT2p, one_pow]
  obtain ⟨r₀, hr₀⟩ := exists_mul_mod_eq_one hp
    (Nat.pos_of_ne_zero fun h => hpj (Nat.dvd_of_mod_eq_zero h)) (Nat.mod_lt j hp.pos)
  have hr₀' : r₀ * j % p = 1 := by
    rw [Nat.mul_mod] at hr₀ ⊢
    rwa [Nat.mod_mod] at hr₀
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨ε, hεdef⟩ : ∃ ε, T ^ (p + 1) = ε := ⟨_, rfl⟩
  have hε : ∀ c, ε c = c ^ ℓ ^ (d * (p + 1)) := fun c => by
    rw [← hεdef, ← hTdef, ← pow_mul]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  set r := r₀ * (m + 1) with hrdef
  have hT2 : (T ^ 2) ^ p = 1 := by rw [← pow_mul, hT2p]
  have hηr : η ^ r = ε := by
    rw [← hTη, ← pow_mul, show 2 * j * r = 2 * (r₀ * j * (m + 1)) by rw [hrdef]; ring, pow_mul,
      pow_eq_pow_mod _ hT2, Nat.mul_mod, hr₀', one_mul, Nat.mod_mod, ← pow_eq_pow_mod _ hT2,
      ← pow_mul, show 2 * (m + 1) = p + 1 by omega, hεdef]
  have hrs : r * (2 * j) % p = 1 := by
    rw [show r * (2 * j) = r₀ * j * (p + 1) by rw [hrdef, hm]; ring, Nat.mul_mod, hr₀', one_mul,
      Nat.mod_mod, Nat.add_mod_left, Nat.mod_eq_of_lt hp.one_lt]
  have hε2j : ε ^ (2 * j) = η := by
    rw [← hεdef, ← pow_mul, show (p + 1) * (2 * j) = 2 * j * (p + 1) by ring, pow_mul, hTη,
      pow_succ, hηp, one_mul]
  obtain ⟨g, u, δ', hgu⟩ := hex (α' ^ r)
  have hδ' : δ' = ε := by rw [← hΘ _ g u δ' hgu, map_pow, hηdef, hηr]
  obtain ⟨L, _, _, _⟩ : ∃ (L : Type) (_ : Field L) (_ : Algebra K L), IsAlgClosure K L :=
    ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (by omega : 1 ≤ 2 * f) hK
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  obtain ⟨⟨S, hS⟩, hLangS⟩ :=
    (exceptional_Lang_root_coordinate_surjectivity ℓ L).2.1 TwistTag.E6 d hd0 1
  have hLang := hLangS S hS
  have hS' : ∀ g', (S g' : ModGL TwistTag.E6.tag L) =
      twistHom TwistTag.E6 L (iterateFrobenius L ℓ d) g' := fun g' => by
    rw [hS, zpow_one, twistHom_apply]
  have hSk : ∀ (n : ℕ) (g' : adjointGroup TwistTag.E6.tag L),
      (((⇑S)^[n] g' : adjointGroup TwistTag.E6.tag L) : ModGL TwistTag.E6.tag L) =
        (twistHom TwistTag.E6 L (iterateFrobenius L ℓ d))^[n] g' := by
    intro n
    induction n with
    | zero => intro g'; rfl
    | succ n ih =>
      intro g'
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hS', ih]
  have hP2 : diagramMap TwistTag.E6 L ^ 2 = 1 := diagramMap_pow_order TwistTag.E6 L
  have hPp : diagramMap TwistTag.E6 L ^ p = diagramMap TwistTag.E6 L := by
    rw [hm, pow_succ, pow_mul, hP2, one_pow, one_mul]
  have hSn : ∀ g', (((⇑S)^[p] g' : adjointGroup TwistTag.E6.tag L) : ModGL TwistTag.E6.tag L) =
      twistHom TwistTag.E6 L (iterateFrobenius L ℓ d ^ p) g' := fun g' => by
    rw [hSk, twistHom_iterate, hPp, twistHom_apply]
  have hFr : ∀ c : L, (iterateFrobenius L ℓ d ^ p) c = c ^ (ℓ ^ f) := by
    intro c
    rw [RingHom.coe_pow]
    have hit : ∀ n : ℕ, (⇑(iterateFrobenius L ℓ d))^[n] c = c ^ ((ℓ ^ d) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, iterateFrobenius_def, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hdp]
  have hC0le : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤ adjointGroup TwistTag.E6.tag K :=
    (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom).trans inf_le_left
  obtain ⟨ιH, hιH⟩ : ∃ ιH : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →*
      adjointGroup TwistTag.E6.tag L,
      ∀ u, (ιH u : ModGL TwistTag.E6.tag L) = baseChangeGL (algebraMap K L) u :=
    ⟨(adjointBaseChangeHom TwistTag.E6.tag (algebraMap K L)).comp (Subgroup.inclusion hC0le),
      fun _ => rfl⟩
  have hFdι : (iterateFrobenius L ℓ d).comp (algebraMap K L) =
      (algebraMap K L).comp (iterateFrobenius K ℓ d) :=
    RingHom.ext fun c => by
      rw [RingHom.comp_apply, RingHom.comp_apply, iterateFrobenius_def, iterateFrobenius_def,
        map_pow]
  have hεησ : ε.toRingHom = (iterateFrobenius K ℓ d).comp σ.toRingHom := RingHom.ext fun c => by
    change ε c = iterateFrobenius K ℓ d (σ c)
    rw [hε, hσ, iterateFrobenius_def, ← pow_mul, ← pow_add, ← hdp,
      show d * (p + 1) = d * p + d by ring]
  have hFdGL : ∀ w : ModGL TwistTag.E6.tag K,
      Units.map (entrywiseHom (iterateFrobenius L ℓ d)) (baseChangeGL (algebraMap K L) w) =
        baseChangeGL (algebraMap K L) (Units.map (entrywiseHom (iterateFrobenius K ℓ d)) w) := by
    intro w
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hFdι]
  have hP2K : diagramMap TwistTag.E6 K ^ 2 = 1 := diagramMap_pow_order TwistTag.E6 K
  have hPinvK : (diagramMap TwistTag.E6 K)⁻¹ = diagramMap TwistTag.E6 K := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hP2K]
  have hβ : ∀ u', S (ιH u') = ιH (fieldActor σ ε u') := fun u' => by
    apply Subtype.ext
    rw [hS', twistHom_apply, hιH, hιH, coe_fieldActor, hFdGL,
      ← baseChangeGL_diagramMap (algebraMap K L) TwistTag.E6, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    have hfix : twistHom TwistTag.E6 K σ.toRingHom (u' : ModGL TwistTag.E6.tag K) = u' :=
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom u'.2).2
    rw [twistHom_apply] at hfix
    have hσu : Units.map (entrywiseHom σ.toRingHom) (u' : ModGL TwistTag.E6.tag K) =
        (diagramMap TwistTag.E6 K)⁻¹ * u' * diagramMap TwistTag.E6 K := by
      calc Units.map (entrywiseHom σ.toRingHom) (u' : ModGL TwistTag.E6.tag K) =
          (diagramMap TwistTag.E6 K)⁻¹ * (diagramMap TwistTag.E6 K *
            Units.map (entrywiseHom σ.toRingHom) (u' : ModGL TwistTag.E6.tag K) *
              (diagramMap TwistTag.E6 K)⁻¹) * diagramMap TwistTag.E6 K := by group
        _ = _ := by rw [hfix]
    rw [hεησ, ← units_map_entrywiseHom_comp, hσu, map_mul, map_mul, map_inv,
      units_map_entrywiseHom_diagramMap, hPinvK]
  have hD : rootDiagUnit TwistTag.E6.tag (fun i => Units.map (algebraMap K L).toMonoidHom
      (compatDiag TwistTag.E6 σ.toRingHom u i)) ∈ adjointGroup TwistTag.E6.tag L :=
    (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag L _).1
  set x : adjointGroup TwistTag.E6.tag L := ιH g * ⟨_, hD⟩ with hxdef
  have hα : ∀ u', ιH ((α' ^ r) u') = x * S (ιH u') * x⁻¹ := fun u' => by
    apply Subtype.ext
    rw [hβ, hgu, hδ', MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply]
    simp only [hxdef, Subgroup.coe_mul, Subgroup.coe_inv, hιH, hcoeΔ, map_mul,
      map_inv, baseChangeGL_rootDiagUnit]
    group
  have hαrp : (α' ^ r) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hα'pow, one_pow]
  have hq3 : 3 ≤ ℓ ^ f := by
    have h2f : 2 ≤ f := by
      rw [← hdp]
      nlinarith
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ.two_le 2
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos h2f
  obtain ⟨ψ, hψ⟩ := exists_conj_eq_of_pow_eq_twisted_frobenius TwistTag.E6 hℓ hf hq3
    hp.one_lt.le K hK2 σ.toRingHom hσ L (iterateFrobenius L ℓ d ^ p) hFr S hSn hLang ιH hιH
    (fieldActor σ ε) hβ x (α' ^ r) hα hαrp
  have hαβ : α' = (α' ^ r) ^ (2 * j) := by rw [← pow_mul, pow_eq_self_of_mod_eq_one hα'p hrs]
  have hψα : ψ * α' * ψ⁻¹ = fieldActor σ (Θ α') := by
    rw [hηdef, hαβ, ← conj_pow, hψ, ← fieldActorHom_apply, ← map_pow, hε2j, fieldActorHom_apply]
  exact ⟨d, hd, hd0, r, 2 * j, T, ε, hT, hε, hαβ.symm, ψ, hψ, hψα⟩

theorem twisted_E6_field_descent_conj_of_prime_order {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * f))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (hp : p.Prime) (hp2 : p ≠ 2) (α' : MulAut (twistedE6RootGroup K σ)) (hα'pow : α' ^ p = 1)
    (hη1 : Θ α' ≠ 1) :
    ∃ d : ℕ, f = p * d ∧ 1 ≤ d ∧ ∃ (r : ℕ) (ε : K ≃+* K),
      (∀ c, ε c = c ^ ℓ ^ (d * (p + 1))) ∧
      ∃ ψ : MulAut (twistedE6RootGroup K σ), ψ * α' ^ r * ψ⁻¹ = fieldActor σ ε ∧
        ψ * α' * ψ⁻¹ = fieldActor σ (Θ α') := by
  obtain ⟨d, hd, hd0, r, -, -, ε, -, hε, -, ψ, hψ, hψα⟩ :=
    twisted_E6_field_descent_data_of_prime_order hℓ hf K hK σ hσ Θ hΘ hp hp2 α' hα'pow hη1
  exact ⟨d, hd, hd0, r, ε, hε, ψ, hψ, hψα⟩

theorem twisted_E6_field_descent_of_prime_order {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * f))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (hp : p.Prime) (hp2 : p ≠ 2) (α' : MulAut (twistedE6RootGroup K σ)) (hα'pow : α' ^ p = 1)
    (hη1 : Θ α' ≠ 1) :
    ∃ d : ℕ, f = p * d ∧ 1 ≤ d ∧ ∃ (r : ℕ) (ε : K ≃+* K),
      (∀ c, ε c = c ^ ℓ ^ (d * (p + 1))) ∧
      ∃ ψ : MulAut (twistedE6RootGroup K σ), ψ * α' ^ r * ψ⁻¹ = fieldActor σ ε := by
  obtain ⟨d, hd, hd0, r, ε, hε, ψ, hψ, -⟩ :=
    twisted_E6_field_descent_conj_of_prime_order hℓ hf K hK σ hσ Θ hΘ hp hp2 α' hα'pow hη1
  exact ⟨d, hd, hd0, r, ε, hε, ψ, hψ⟩

end CFSG.HardMathSupport.Lang.Coordinator
