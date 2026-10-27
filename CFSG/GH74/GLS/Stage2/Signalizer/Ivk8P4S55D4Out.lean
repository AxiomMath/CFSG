module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55G2TM
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55G2NT
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.Chevalley

section Torus

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

@[expose] def d4Tup (c : Kˣ) : Fin TwistTag.D4.tag.rank → Kˣ := fun i =>
  if (i : ℕ) = 0 then c
  else if (i : ℕ) = 1 then Units.map σ.toRingHom.toMonoidHom c
  else if (i : ℕ) = 3 then Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom c)
  else 1

omit [Finite K] in
theorem d4Tup_idx0 (c : Kˣ) : d4Tup σ c 0 = c := by
  have h : ((0 : Fin TwistTag.D4.tag.rank) : ℕ) = 0 := by decide
  simp only [d4Tup]
  rw [h]
  simp

omit [Finite K] in
theorem d4Tup_idx1 (c : Kˣ) : d4Tup σ c 1 = Units.map σ.toRingHom.toMonoidHom c := by
  have h : ((1 : Fin TwistTag.D4.tag.rank) : ℕ) = 1 := by decide
  simp only [d4Tup]
  rw [h]
  simp

omit [Finite K] in
theorem d4Tup_idx2 (c : Kˣ) : d4Tup σ c 2 = 1 := by
  have h : ((2 : Fin TwistTag.D4.tag.rank) : ℕ) = 2 := by decide
  simp only [d4Tup]
  rw [h]
  simp

omit [Finite K] in
theorem d4Tup_idx3 (c : Kˣ) :
    d4Tup σ c 3 = Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom c) := by
  have h : ((3 : Fin TwistTag.D4.tag.rank) : ℕ) = 3 := by decide
  simp only [d4Tup]
  rw [h]
  simp

omit [Finite K] in
theorem d4Tup_one : d4Tup σ (1 : Kˣ) = 1 := by
  funext i
  fin_cases i <;> simp [d4Tup]

omit [Finite K] in
theorem d4Tup_mul (c c' : Kˣ) : d4Tup σ (c * c') = d4Tup σ c * d4Tup σ c' := by
  funext i
  fin_cases i <;> simp [d4Tup]

theorem d4Tup_map (η : K ≃+* K) (c : Kˣ) :
    (fun i => Units.map η.toRingHom.toMonoidHom (d4Tup σ c i)) =
      d4Tup σ (Units.map η.toRingHom.toMonoidHom c) := by
  funext i
  fin_cases i <;> simp [d4Tup]
  · exact Units.ext (ringEquiv_comm_of_finite σ η c)
  · exact Units.ext (by
      rw [Units.coe_map, Units.coe_map, Units.coe_map, Units.coe_map]
      exact (by
        change η (σ (σ (c : K))) = σ (σ (η (c : K)))
        rw [ringEquiv_comm_of_finite σ η (σ (c : K)), ringEquiv_comm_of_finite σ η (c : K)]))

theorem d4Tup_compat {q : ℕ} (hK : Nat.card K = q ^ 3) (hσ : ∀ c, σ c = c ^ q) (c : Kˣ) :
    d4Tup σ c ∈ compatSubgroup (t := TwistTag.D4) σ.toRingHom := by
  rw [mem_compatSubgroup]
  intro i
  have e0 : TwistTag.D4.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have e1 : TwistTag.D4.perm ⟨1, by decide⟩ = ⟨3, by decide⟩ := by decide
  have e2 : TwistTag.D4.perm ⟨2, by decide⟩ = ⟨2, by decide⟩ := by decide
  have e3 : TwistTag.D4.perm ⟨3, by decide⟩ = ⟨0, by decide⟩ := by decide
  fin_cases i
  · show d4Tup σ c (TwistTag.D4.perm ⟨0, by decide⟩) = _
    rw [e0]
    simp [d4Tup]
  · show d4Tup σ c (TwistTag.D4.perm ⟨1, by decide⟩) = _
    rw [e1]
    simp [d4Tup]
  · show d4Tup σ c (TwistTag.D4.perm ⟨2, by decide⟩) = _
    rw [e2]
    simp [d4Tup]
  · show d4Tup σ c (TwistTag.D4.perm ⟨3, by decide⟩) = _
    rw [e3]
    simp only [d4Tup]
    refine Units.ext ?_
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact (ringEquiv_cube_apply_eq hK hσ c).symm


@[expose] def d4TupHom : Kˣ →* (Fin TwistTag.D4.tag.rank → Kˣ) where
  toFun := d4Tup σ
  map_one' := d4Tup_one σ
  map_mul' := d4Tup_mul σ

@[expose] noncomputable def d4Tor {q : ℕ} (hK : Nat.card K = q ^ 3) (hσ : ∀ c, σ c = c ^ q) :
    Kˣ →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  ((torusGroup TwistTag.D4.tag K).subtype.comp
    ((torusCoordHom TwistTag.D4.tag K).comp (d4TupHom σ))).codRestrict
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) fun c =>
      compatTorus_le_graphFixedRootGroup σ.toRingHom
        ((mem_compatTorus σ.toRingHom).2 ⟨d4Tup σ c, d4Tup_compat σ hK hσ c, rfl⟩)

theorem coe_d4Tor {q : ℕ} (hK : Nat.card K = q ^ 3) (hσ : ∀ c, σ c = c ^ q) (c : Kˣ) :
    ((d4Tor σ hK hσ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) =
        ((torusCoordHom TwistTag.D4.tag K (d4Tup σ c) : torusGroup TwistTag.D4.tag K) :
          ModGL TwistTag.D4.tag K) :=
  rfl

theorem d4Tor_injective {q : ℕ} (hK : Nat.card K = q ^ 3) (hσ : ∀ c, σ c = c ^ q)
    (h2 : (2 : K) ≠ 0) : Function.Injective (d4Tor σ hK hσ) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have h1 : torusCoordHom TwistTag.D4.tag K (d4Tup σ c) = 1 := by
    have h0 := congrArg (fun x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
      (x : ModGL TwistTag.D4.tag K)) hc
    simp only [coe_d4Tor, OneMemClass.coe_one] at h0
    exact Subtype.ext h0
  have h3 := (torusCoordHom_eq_one_iff (τ := Tag.D4) (d4Tup σ c)).1 h1
  have e0 := congrFun h3 ⟨0, by decide⟩
  have e2 := congrFun h3 ⟨2, by decide⟩
  have e0' := (zpowMatrix_apply Tag.D4.cartan (d4Tup σ c) ⟨0, by decide⟩).symm.trans e0
  have e2' := (zpowMatrix_apply Tag.D4.cartan (d4Tup σ c) ⟨2, by decide⟩).symm.trans e2
  have hprod : ∀ f : Fin Tag.D4.rank → Kˣ, ∏ i, f i = f 0 * f 1 * f 2 * f 3 :=
    fun f => Fin.prod_univ_four f
  rw [hprod] at e0' e2'
  have e0'' : d4Tup σ c 0 ^ (2 : ℤ) * d4Tup σ c 1 ^ (0 : ℤ) * d4Tup σ c 2 ^ (-1 : ℤ) *
      d4Tup σ c 3 ^ (0 : ℤ) = 1 := e0'
  have e2'' : d4Tup σ c 0 ^ (-1 : ℤ) * d4Tup σ c 1 ^ (-1 : ℤ) * d4Tup σ c 2 ^ (2 : ℤ) *
      d4Tup σ c 3 ^ (-1 : ℤ) = 1 := e2'
  rw [d4Tup_idx0, d4Tup_idx1, d4Tup_idx2, d4Tup_idx3] at e0'' e2''
  simp at e0'' e2''
  have hc2 : (c : K) * c = 1 := by
    have h0 := congrArg (fun u : Kˣ => (u : K)) e0''
    simpa [pow_two] using h0
  rcases mul_self_eq_one_iff.1 hc2 with hc1 | hc1
  · exact Units.ext (by simpa using hc1)
  · exfalso
    have e := congrArg (fun u : Kˣ => (u : K)) e2''
    simp [hc1] at e
    apply h2
    linear_combination -e

omit [Finite K]
  in
theorem entrywise_torusCoordHom' (δ : K ≃+* K) (b : Fin TwistTag.D4.tag.rank → Kˣ) :
    Units.map (entrywiseHom δ.toRingHom)
        ((torusCoordHom TwistTag.D4.tag K b : torusGroup TwistTag.D4.tag K) :
          ModGL TwistTag.D4.tag K) =
      ((torusCoordHom TwistTag.D4.tag K (fun i => Units.map δ.toRingHom.toMonoidHom (b i)) :
        torusGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) := by
  rw [coe_torusCoordHom, coe_torusCoordHom, map_list_prod, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => ?_)
  exact CFSG.LieType.Chevalley.entrywise_torusElt δ i (b i)

theorem fieldActor_d4Tor {q : ℕ} (hK : Nat.card K = q ^ 3) (hσ : ∀ c, σ c = c ^ q)
    (η : K ≃+* K) (c : Kˣ) :
    fieldActor σ η (d4Tor σ hK hσ c) = d4Tor σ hK hσ (Units.map η.toRingHom.toMonoidHom c) := by
  refine Subtype.ext ?_
  rw [coe_fieldActor, coe_d4Tor, coe_d4Tor, entrywise_torusCoordHom', d4Tup_map]

end Torus

section Large


variable {K : Type} [Field K] [Finite K]

theorem outerFalse_d4_large {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : 3 < p) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    OuterFalse p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  intro α hαinn hαp _ hHH
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, ⟨Θ, hΘ, -, -, -⟩, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact hαinn ⟨1, map_one MulAut.conj⟩
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  have hmem : α ∈ (⊤ : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :=
    Subgroup.mem_top α
  obtain ⟨hηp, hpf, ⟨h₀, hconj⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial hp hf K hK σ hσ Θ hΘ hp
      hp3 ⊤ (fun _ _ => Subgroup.mem_top _) ⟨α, hmem⟩ hαinn
      (by rw [Subgroup.orderOf_mk]; exact hord)
  set η : K ≃+* K := Θ α with hηdef
  have hηp' : orderOf η = p := hηp
  have hconj' : MulAut.conj h₀ * α * (MulAut.conj h₀)⁻¹ = fieldActor σ η := hconj
  obtain ⟨e, he⟩ := hpf
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      omega
    · exact h
  have hq0odd : Odd (p ^ (3 * e)) := (hp.odd_of_ne_two hp2).pow
  have hq03 : 3 ≤ p ^ (3 * e) := le_trans (by omega : 3 ≤ p) (Nat.le_self_pow (by omega) p)
  have hpq0 : p ∣ p ^ (3 * e) := dvd_pow_self p (by omega)
  obtain ⟨r, hr, hr2, hrp, hrdvd, hrnd⟩ :=
    exists_prime_dvd_pow_sub_one_not_dvd hp hp2 hpq0 hq03 hq0odd
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hunits : Nat.card Kˣ = (p ^ (3 * e)) ^ p - 1 := by
    rw [Nat.card_units, hK3, he, ← pow_mul, show 3 * (p * e) = 3 * e * p by ring]
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' r (hunits ▸ hrdvd)
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K p 2).1 h'
    have := Nat.le_of_dvd (by norm_num) this
    omega
  obtain ⟨φ, hφ, hφord, hφtop, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hp (by omega : 1 ≤ 3 * f) hK3
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφtop⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, φ ^ k = η := by
    have h : η ∈ Subgroup.zpowers φ := hφtop ▸ Subgroup.mem_top η
    rwa [← mem_powers_iff_mem_zpowers] at h
  have hφpow : ∀ (n : ℕ) (x : K), (φ ^ n) x = x ^ (p ^ n) :=
    fun n x => ringAut_pow_apply_of_frobenius hφ n x
  set τ₀ := φ ^ (3 * e) with hτ₀def
  have hτ₀ord : orderOf τ₀ = p := by
    rw [hτ₀def, orderOf_pow' _ (by omega), hφord, he]
    have hg : Nat.gcd (3 * (p * e)) (3 * e) = 3 * e :=
      Nat.gcd_eq_right ⟨p, by ring⟩
    rw [hg]
    exact Nat.div_eq_of_eq_mul_left (by omega) (by ring)
  have hzz : Subgroup.zpowers τ₀ = Subgroup.zpowers η :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hτ₀ord, hηp'])
  obtain ⟨j, hj⟩ : ∃ j : ℕ, η ^ j = τ₀ := by
    have h : τ₀ ∈ Subgroup.zpowers η := hzz ▸ Subgroup.mem_zpowers τ₀
    rwa [← mem_powers_iff_mem_zpowers] at h
  have hot : orderOf (d4Tor σ hK hσ c) = r := by
    rw [orderOf_injective (d4Tor σ hK hσ) (d4Tor_injective σ hK hσ h2) c]
    exact hc
  have hηc : Units.map η.toRingHom.toMonoidHom c = c ^ (p ^ k) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    show η (c : K) = (c : K) ^ p ^ k
    rw [← hk, hφpow]
  have hft : fieldActor σ η (d4Tor σ hK hσ c) = (d4Tor σ hK hσ c) ^ (p ^ k) := by
    rw [fieldActor_d4Tor, hηc, map_pow]
  have hne : fieldActor σ η (d4Tor σ hK hσ c) ≠ d4Tor σ hK hσ c := by
    intro h
    rw [fieldActor_d4Tor] at h
    have h1 : Units.map η.toRingHom.toMonoidHom c = c := d4Tor_injective σ hK hσ h2 h
    have h3 : ∀ n : ℕ, (η ^ n) (c : K) = c := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, RingAut.mul_apply]
        have : η (c : K) = c := congrArg Units.val h1
        rw [this, ih]
    have h4 := h3 j
    rw [hj, hτ₀def, hφpow] at h4
    have h5 : c ^ (p ^ (3 * e) - 1) = 1 := by
      apply Units.ext
      have hc0 : (c : K) ≠ 0 := c.ne_zero
      have : (c : K) ^ (p ^ (3 * e) - 1) * c = 1 * c := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul]
        exact h4
      simpa using mul_right_cancel₀ hc0 this
    exact hrnd (hc ▸ orderOf_dvd_of_pow_eq_one h5)
  have hα' : α = (MulAut.conj h₀)⁻¹ * fieldActor σ η * ((MulAut.conj h₀)⁻¹)⁻¹ := by
    rw [← hconj']
    group
  exact false_of_torus_moved_pow hα' hr hr2 hrp hot hft hne hHH

theorem outerFalse_d4_large_model {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : 3 < p) (hf : 1 ≤ f) (hm : LieModel Y .trialityD4 0 p f) :
    OuterFalse p Y := by
  have : Fact p.Prime := ⟨hp⟩
  have htw : TwistedChevalleyModel Y .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  exact OuterFalse.of_mulEquiv e (outerFalse_d4_large hp hp2 hp3 hf hM σ hσ)

end Large

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
