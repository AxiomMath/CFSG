module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open scoped commutatorElement
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model

section Arith

variable {p f r : ℕ}

theorem ppd_ne_prime (hr : r.Prime) (hrd : r ∣ p ^ (2 * f) - 1) (hf : 1 ≤ f) : r ≠ p := by
  rintro rfl
  have h1 : r ∣ r ^ (2 * f) := dvd_pow_self r (by omega)
  have h2 : 1 ≤ r ^ (2 * f) := Nat.one_le_pow _ _ hr.pos
  have : r ∣ 1 := by
    have h3 := Nat.dvd_sub h1 hrd
    rwa [show r ^ (2 * f) - (r ^ (2 * f) - 1) = 1 by omega] at h3
  exact hr.one_lt.ne' (Nat.dvd_one.mp this)

theorem ppd_dvd_add_one (hp : p.Prime) (hr : r.Prime) (hrd : r ∣ p ^ (2 * f) - 1) (hf : 1 ≤ f)
    (hppd : ∀ k : ℕ, 0 < k → k < 2 * f → ¬ r ∣ p ^ k - 1) : r ∣ p ^ f + 1 := by
  have hfac : p ^ (2 * f) - 1 = (p ^ f - 1) * (p ^ f + 1) := by
    zify [Nat.one_le_pow f p hp.pos, Nat.one_le_pow (2 * f) p hp.pos]
    ring
  rw [hfac] at hrd
  rcases (Nat.Prime.dvd_mul hr).mp hrd with h | h
  · exact absurd h (hppd f (by omega) (by omega))
  · exact h

theorem ppd_ne_three (hp : p.Prime) (hr : r.Prime) (hrd : r ∣ p ^ (2 * f) - 1) (hf : 2 ≤ f)
    (hppd : ∀ k : ℕ, 0 < k → k < 2 * f → ¬ r ∣ p ^ k - 1) : r ≠ 3 := by
  rintro rfl
  have h2 := hppd 2 (by omega) (by omega)
  have h3 : ¬ 3 ∣ p := fun h => ppd_ne_prime hr hrd (by omega)
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h)
  apply h2
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have hmod : p ^ 2 % 3 = 1 := by
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  omega

end Arith

theorem card_modEq_of_conj_fixed {G : Type*} [Group G] {V Z : Subgroup G} [Finite V] (c : G)
    {r : ℕ} [hr : Fact r.Prime] (hcr : c ^ r = 1) (hc : c ∈ Subgroup.normalizer (V : Set G))
    (hfix : ∀ v ∈ V, c * v * c⁻¹ = v ↔ v ∈ Z) (hZV : Z ≤ V) :
    Nat.card V ≡ Nat.card Z [MOD r] := by
  classical
  have := Fintype.ofFinite V
  let f : Function.End V := fun v => ⟨c * v * c⁻¹, ((Subgroup.mem_normalizer_iff.1 hc) v).1 v.2⟩
  have hpow : ∀ (n : ℕ) (v : V), ((f ^ n) v : G) = c ^ n * v * (c ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro v; rw [pow_zero]; simp; rfl
    | succ n ih =>
      intro v
      have h1 : (f ^ (n + 1)) v = (f ^ n) (f v) := by rw [pow_succ]; rfl
      rw [h1, ih]
      show c ^ n * (c * v * c⁻¹) * (c ^ n)⁻¹ = _
      group
  have hf : f ^ r ^ 1 = 1 := by
    funext v
    apply Subtype.ext
    rw [pow_one, hpow, hcr]
    simp
    rfl
  have h1 := Equiv.Perm.card_fixedPoints_modEq hf
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card] at h1
  have h2 : Nat.card (Function.fixedPoints f) = Nat.card Z := by
    refine Nat.card_congr
      { toFun := fun v => ⟨v.1.1, (hfix v.1.1 v.1.2).1 (congrArg Subtype.val v.2)⟩
        invFun := fun z => ⟨⟨z.1, hZV z.2⟩, Subtype.ext ((hfix z.1 (hZV z.2)).2 z.2)⟩
        left_inv := fun v => rfl
        right_inv := fun z => rfl }
  rwa [h2] at h1

section Center

variable {K : Type} [Field K] (J : HermitianForm 3 K)

theorem coord_ext {z w : Coord J} (h1 : z.1.1 = w.1.1) (h2 : z.1.2 = w.1.2) : z = w :=
  Subtype.ext (Prod.ext h1 h2)

theorem exists_coord_fst (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution J.conj) (a : K) :
    ∃ z : Coord J, z.1.1 = a := by
  obtain ⟨c, hc⟩ := hσ.trace_surj (a * J.conj a) (by rw [map_mul, hσ.invol, mul_comm])
  exact ⟨⟨(a, -c), by dsimp only; rw [map_neg]; linear_combination -hc⟩, rfl⟩

theorem fst_eq_zero_of_forall_mul_comm
    (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution J.conj) {w : Coord J}
    (h : ∀ z : Coord J, w * z = z * w) : w.1.1 = 0 := by
  have key : ∀ x : K, w.1.1 * J.conj x = x * J.conj w.1.1 := by
    intro x
    obtain ⟨z, rfl⟩ := exists_coord_fst J hσ x
    have := congrArg (fun y : Coord J => (y : K × K).2) (h z)
    simp only [coord_mul_val] at this
    linear_combination -this
  have h1 := key 1
  rw [map_one, mul_one, one_mul] at h1
  obtain ⟨x, hx⟩ := hσ.exists_ne
  have h2 := key x
  rw [← h1] at h2
  have : w.1.1 * (J.conj x - x) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp this with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0) hx

theorem eq_skewCoord_of_fst_eq_zero {z : Coord J} (h : z.1.1 = 0) :
    z = skewCoord J z.1.2 (by have := z.2; simpa [h] using this) :=
  coord_ext J (by simp [skewCoord, h]) rfl

end Center

section PWorld

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

omit [Finite K] [Fact p.Prime] in
theorem torusAction_normOne (κ : Kˣ) (hκ : J.conj (κ : K) * κ = 1) (z : Coord J) :
    (hermitianTorusAction J κ z : K × K) = ((κ : K) ^ 3 * z.1.1, z.1.2) := by
  have h1 : (J.conj (κ : K))⁻¹ = κ := inv_eq_of_mul_eq_one_right hκ
  rw [torusAction_val, h1]
  have hκ0 : (κ : K) ≠ 0 := κ.ne_zero
  ext
  · dsimp only
    ring
  · dsimp only
    field_simp

omit [Finite K] [Fact p.Prime] in
theorem torus_comm_root_iff (κ : Kˣ) (hκ : J.conj (κ : K) * κ = 1) (hκ3 : (κ : K) ^ 3 ≠ 1)
    (z : Coord J) :
    torus J hJ κ * root J hJ z * (torus J hJ κ)⁻¹ = root J hJ z ↔ z.1.1 = 0 := by
  rw [torus_mul_root_mul_inv, (root_injective J hJ).eq_iff]
  constructor
  · intro h
    have h1 := congrArg (fun y : Coord J => (y : K × K).1) h
    simp only [torusAction_normOne J κ hκ] at h1
    have : ((κ : K) ^ 3 - 1) * z.1.1 = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hκ3)
  · intro h
    apply coord_ext
    · simp [torusAction_normOne J κ hκ, h]
    · simp [torusAction_normOne J κ hκ]

include hK hfix

theorem root_mem_center_iff (z : Coord J) :
    root J hJ z ∈ rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ↔ z.1.1 = 0 := by
  have hσ := isUnitaryInvolution_conj J hK hfix
  constructor
  · intro h
    apply fst_eq_zero_of_forall_mul_comm J hσ
    intro w
    have := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 h).2) (root J hJ w)
      (root_mem_rootGroup J hJ w)
    apply root_injective J hJ
    rw [map_mul, map_mul]
    exact this.symm
  · intro h
    refine Subgroup.mem_inf.2 ⟨root_mem_rootGroup J hJ z, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ hw
    obtain ⟨w, rfl⟩ := (mem_rootGroup J hJ).1 hw
    rw [← map_mul, ← map_mul, eq_skewCoord_of_fst_eq_zero J h, skewCoord_central]

omit [Fact p.Prime] in
theorem card_center_rootGroup :
    Nat.card ↥(rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) = p ^ f := by
  rw [← commutator_rootGroup J hJ hK hfix]
  exact card_commutator_rootGroup J hJ hK hfix

theorem exists_ppd_torus (hf : 2 ≤ f) {r : ℕ} (hr : r.Prime) (hrd : r ∣ p ^ (2 * f) - 1)
    (hppd : ∀ k : ℕ, 0 < k → k < 2 * f → ¬ r ∣ p ^ k - 1) :
    ∃ c ∈ Subgroup.normalizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      orderOf c = r ∧ ∀ m : ℕ, ¬ r ∣ m →
        (∃ u ∈ rootGroup J hJ, c ^ m * u * (c ^ m)⁻¹ * u⁻¹ ∉ rootGroup J hJ ⊓
          Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ∧
        ∀ V : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
          rootGroup J hJ ⊓ Subgroup.centralizer
            (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ V →
          V ≤ rootGroup J hJ → c ^ m ∈ Subgroup.normalizer (V : Set _) →
          V = rootGroup J hJ ⊓ Subgroup.centralizer
            (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∨
          V = rootGroup J hJ := by
  have hp : p.Prime := Fact.out
  have : Fact r.Prime := ⟨hr⟩
  have hσ := isUnitaryInvolution_conj J hK hfix
  have hconj := huppert_II_10_4_conj_eq_frobenius J (p ^ f) hK hfix
  have hrp : r ≠ p := ppd_ne_prime hr hrd (by omega)
  have hr3 : r ≠ 3 := ppd_ne_three hp hr hrd hf hppd
  have hrq : r ∣ p ^ f + 1 := ppd_dvd_add_one hp hr hrd (by omega) hppd
  have hrK : r ∣ Nat.card Kˣ := by
    rw [CFSG.ClassicalGroups.Unitary.card_units_of_card hK, ← pow_mul, mul_comm f 2]
    exact hrd
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r hrK
  have hkq : (k : K) ^ (p ^ f + 1) = 1 := by
    have : k ^ (p ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hk ▸ hrq)
    simpa using congrArg Units.val this
  have hnorm : ∀ m : ℕ, J.conj ((k ^ m : Kˣ) : K) * ((k ^ m : Kˣ) : K) = 1 := by
    intro m
    rw [hconj, Units.val_pow_eq_pow_val]
    have : ((k : K) ^ m) ^ p ^ f * (k : K) ^ m = ((k : K) ^ (p ^ f + 1)) ^ m := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    rw [this, hkq, one_pow]
  have hκ3 : ∀ m : ℕ, ¬ r ∣ m → ((k ^ m : Kˣ) : K) ^ 3 ≠ 1 := by
    intro m hm h
    have h1 : k ^ (m * 3) = 1 := by
      apply Units.ext
      rw [pow_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      simpa [Units.val_pow_eq_pow_val] using h
    have h2 : r ∣ m * 3 := hk ▸ orderOf_dvd_of_pow_eq_one h1
    rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
    · exact hm h3
    · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)
  have hpowc : ∀ m : ℕ, torus J hJ k ^ m = torus J hJ (k ^ m) := fun m => (map_pow _ _ _).symm
  have hcr : torus J hJ k ^ r = 1 := by
    rw [hpowc, ← hk, pow_orderOf_eq_one, map_one]
  obtain ⟨z₁, hz₁⟩ := exists_coord_fst J hσ 1
  have hne : ∀ m : ℕ, ¬ r ∣ m → ¬ (z₁.1.1 = 0) := fun m hm h => by
    rw [hz₁] at h
    exact one_ne_zero h
  have hcomm : ∀ m : ℕ, ¬ r ∣ m → ∀ z : Coord J,
      (torus J hJ k ^ m * root J hJ z * (torus J hJ k ^ m)⁻¹ = root J hJ z ↔ z.1.1 = 0) := by
    intro m hm z
    rw [hpowc]
    exact torus_comm_root_iff J hJ (k ^ m) (hnorm m) (hκ3 m hm) z
  have hr1 : ¬ r ∣ 1 := fun h => hr.one_lt.ne' (Nat.dvd_one.mp h)
  refine ⟨torus J hJ k, torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ k),
    ?_, fun m hm => ⟨?_, ?_⟩⟩
  · refine orderOf_eq_prime hcr fun h1 => ?_
    have := (hcomm 1 hr1 z₁).1 (by rw [h1]; simp)
    exact hne 1 hr1 this
  · refine ⟨root J hJ z₁, root_mem_rootGroup J hJ z₁, fun hmem => ?_⟩
    rw [hpowc, torus_mul_root_mul_inv, ← map_inv, ← map_mul,
      root_mem_center_iff J hJ hK hfix] at hmem
    rw [coord_mul_val, coord_inv_val, torusAction_normOne J _ (hnorm m), hz₁] at hmem
    have := hκ3 m hm
    apply this
    simp only at hmem
    linear_combination hmem
  · intro V hZV hVR hc
    have hcrm : (torus J hJ k ^ m) ^ r = 1 := by rw [← pow_mul, mul_comm, pow_mul, hcr, one_pow]
    have hfixV : ∀ v ∈ V, torus J hJ k ^ m * v * (torus J hJ k ^ m)⁻¹ = v ↔ v ∈ rootGroup J hJ ⊓
        Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      intro v hv
      obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 (hVR hv)
      rw [hcomm m hm z, root_mem_center_iff J hJ hK hfix]
    have hmod := card_modEq_of_conj_fixed (torus J hJ k ^ m) hcrm hc hfixV hZV
    have hRcard := card_rootGroup_eq J hJ hK hfix
    have hZcard := card_center_rootGroup J hJ hK hfix
    obtain ⟨s, hs3, hs⟩ := (Nat.dvd_prime_pow hp).1 (hRcard ▸ Subgroup.card_dvd_of_le hVR)
    have hfs : f ≤ s := by
      have : Nat.card ↥(rootGroup J hJ ⊓ Subgroup.centralizer
          (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ∣ Nat.card V :=
        Subgroup.card_dvd_of_le hZV
      rw [hZcard, hs] at this
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 this
    obtain ⟨i, rfl⟩ : ∃ i, s = f + i := ⟨s - f, by omega⟩
    rw [hs, hZcard, pow_add] at hmod
    have hcop : Nat.gcd r (p ^ f) = 1 :=
      Nat.Coprime.pow_right f ((Nat.coprime_primes hr hp).2 hrp)
    have hpi : p ^ i ≡ 1 [MOD r] :=
      Nat.ModEq.cancel_left_of_coprime hcop (by simpa using hmod)
    have hdvd : r ∣ p ^ i - 1 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).1 hpi.symm
    have hi : i = 0 ∨ i = 2 * f := by
      by_contra hcon
      push Not at hcon
      exact hppd i (Nat.pos_of_ne_zero hcon.1) (by omega) hdvd
    rcases hi with rfl | rfl
    · left
      refine (Subgroup.eq_of_le_of_card_ge hZV ?_).symm
      rw [hZcard, hs]
      simp
    · right
      refine Subgroup.eq_of_le_of_card_ge hVR ?_
      rw [hRcard, hs, show f + 2 * f = 3 * f by ring]

end PWorld

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding

open CFSG.UnitaryThreeRecognition.Model (rootGroup)

theorem kFactUnitaryTorusPPD : KFactUnitaryTorusPPD := by
  intro L _ _ p _ d hd hf2 h U r hr hrd hppd
  obtain ⟨-, hf, -, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  have hZ : ((U : Subgroup L) ⊓ Subgroup.centralizer ((U : Subgroup L) : Set L)).map
      e'.toMonoidHom = rootGroup J hJ ⊓ Subgroup.centralizer (rootGroup J hJ : Set _) := by
    ext y
    obtain ⟨x, rfl⟩ := e'.surjective y
    rw [UnitaryModel.mem_map_iff, Subgroup.mem_inf, Subgroup.mem_inf, ← hU,
      UnitaryModel.mem_map_iff, UnitaryModel.mem_centralizer_map_iff]
  obtain ⟨c, hc, hco, hcm⟩ := UnitaryModel.exists_ppd_torus J hJ hK hfix hf2 hr hrd hppd
  refine ⟨e'.symm c, ?_, ?_, fun m hm => ?_⟩
  · rw [← hN] at hc
    exact (UnitaryModel.mem_map_iff e' _ _).1 (by simpa using hc)
  · rw [MulEquiv.orderOf_eq, hco]
  · obtain ⟨⟨u, hu, hu'⟩, hV⟩ := hcm m hm
    refine ⟨⟨e'.symm u, ?_, ?_⟩, fun V hZV hVU hnV => ?_⟩
    · have : e' (e'.symm u) ∈ (U : Subgroup L).map e'.toMonoidHom := by
        rw [hU, MulEquiv.apply_symm_apply]
        exact hu
      exact (UnitaryModel.mem_map_iff e' _ _).1 this
    · intro hmem
      apply hu'
      have h1 := Subgroup.mem_map_of_mem e'.toMonoidHom hmem
      rw [hZ] at h1
      simpa using h1
    · have h1 : rootGroup J hJ ⊓ Subgroup.centralizer (rootGroup J hJ : Set _) ≤
          V.map e'.toMonoidHom := by
        rw [← hZ]
        exact Subgroup.map_mono hZV
      have h2 : V.map e'.toMonoidHom ≤ rootGroup J hJ := by
        rw [← hU]
        exact Subgroup.map_mono hVU
      have h3 : c ^ m ∈ Subgroup.normalizer ((V.map e'.toMonoidHom : Subgroup _) : Set _) := by
        rw [← Subgroup.map_equiv_normalizer_eq]
        have := Subgroup.mem_map_of_mem e'.toMonoidHom hnV
        simpa using this
      rcases hV _ h1 h2 h3 with h4 | h4
      · exact Or.inl (Subgroup.map_injective e'.injective (h4.trans hZ.symm))
      · exact Or.inr (Subgroup.map_injective e'.injective (h4.trans hU.symm))

end CFSG.AGLEmbedding
