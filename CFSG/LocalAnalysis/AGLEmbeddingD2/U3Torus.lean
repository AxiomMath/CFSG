module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus
public import CFSG.Permutation.UnitaryThreeRecognition.ModelBasic

public section

namespace CFSG.AGLEmbeddingD2

section Arith

private def OrbitLen (p m : ℕ) : Prop :=
  (m = p + 1 ∧ ¬ 3 ∣ p + 1) ∨ (3 * m = p + 1 ∧ 3 ∣ p + 1)

private theorem orbit_cases (p : ℕ) : OrbitLen p ((p + 1) / Nat.gcd 3 (p + 1)) := by
  by_cases h : 3 ∣ p + 1
  · right
    rw [Nat.gcd_eq_left h]
    exact ⟨Nat.mul_div_cancel' h, h⟩
  · left
    have hcop : Nat.Coprime 3 (p + 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h
    rw [hcop.gcd_eq_one, Nat.div_one]
    exact ⟨rfl, h⟩

private theorem sq_sub_one_eq {p : ℕ} (hp : 1 ≤ p) : p ^ 2 - 1 = (p + 1) * (p - 1) := by
  zify [Nat.one_le_pow 2 p hp, hp]
  ring

variable {p m : ℕ}

private theorem sq_sub_one_dvd (hp3 : 3 ≤ p)
    (hm : OrbitLen p m) :
    p ^ 2 - 1 ∣ p * (p - 2) * m * (p - 1) := by
  rw [sq_sub_one_eq (by omega)]
  refine Nat.mul_dvd_mul_right ?_ (p - 1)
  rcases hm with ⟨hm1, -⟩ | ⟨hm3, -⟩
  · exact ⟨p * (p - 2), by rw [hm1]; ring⟩
  · have h2 : p - 2 = 3 * (m - 1) := by omega
    refine ⟨p * (m - 1), ?_⟩
    rw [h2, ← hm3]
    ring

private theorem not_sq_sub_one_dvd_mul (hp3 : 3 ≤ p)
    (hm : OrbitLen p m) {j : ℕ} (hj0 : 0 < j)
    (hjm : j < m) : ¬ p ^ 2 - 1 ∣ p * (p - 2) * j * (p - 1) := by
  intro h
  rw [sq_sub_one_eq (by omega)] at h
  have h2 : p + 1 ∣ p * (p - 2) * j := Nat.dvd_of_mul_dvd_mul_right (by omega) h
  have h3 : p + 1 ∣ p * (3 * j) := by
    refine (Nat.dvd_add_right h2).mp ⟨p * j, ?_⟩
    zify [show 2 ≤ p by omega]
    ring
  have hcop : Nat.Coprime (p + 1) p := by simp
  have h4 : p + 1 ∣ 3 * j := hcop.dvd_of_dvd_mul_left h3
  rcases hm with ⟨hm1, h3'⟩ | ⟨hm3, -⟩
  · have hcop3 : Nat.Coprime (p + 1) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3').symm
    have h5 : p + 1 ∣ j := hcop3.dvd_of_dvd_mul_left h4
    have := Nat.le_of_dvd hj0 h5
    omega
  · rw [← hm3] at h4
    have h5 : m ∣ j := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) h4
    have := Nat.le_of_dvd hj0 h5
    omega

private theorem not_sq_sub_one_dvd_pred (hp3 : 3 ≤ p)
    (hm : OrbitLen p m) {j : ℕ} (hj0 : 0 < j)
    (hjp : j < p - 1) : ¬ p ^ 2 - 1 ∣ p * (p - 2) * m * j := by
  intro h
  rw [sq_sub_one_eq (by omega)] at h
  have h2 : p - 1 ∣ p * (p - 2) * j := by
    rcases hm with ⟨hm1, -⟩ | ⟨hm3, -⟩
    · rw [hm1] at h
      have h' : (p + 1) * (p - 1) ∣ (p + 1) * (p * (p - 2) * j) := by
        rwa [show (p + 1) * (p * (p - 2) * j) = p * (p - 2) * (p + 1) * j by ring]
      exact Nat.dvd_of_mul_dvd_mul_left (Nat.succ_pos p) h'
    · rw [← hm3] at h
      have hmpos : 0 < m := by omega
      have h' : m * (3 * (p - 1)) ∣ m * (p * (p - 2) * j) := by
        rwa [show m * (3 * (p - 1)) = 3 * m * (p - 1) by ring,
          show m * (p * (p - 2) * j) = p * (p - 2) * m * j by ring]
      exact (Dvd.intro_left 3 rfl).trans (Nat.dvd_of_mul_dvd_mul_left hmpos h')
  have h3 : p - 1 ∣ p * (p - 2) * j + j :=
    ⟨(p - 1) * j, by
      zify [show 2 ≤ p by omega, show 1 ≤ p by omega]
      ring⟩
  have h4 : p - 1 ∣ j := (Nat.dvd_add_right h2).mp h3
  have := Nat.le_of_dvd hj0 h4
  omega

end Arith

section Field

variable {K : Type} [Field K] {p m : ℕ} {κ : K}

private def IsGen (p : ℕ) (κ : K) : Prop := ∀ n : ℕ, κ ^ n = 1 ↔ p ^ 2 - 1 ∣ n

private theorem IsGen.ne_zero (hp : 1 < p) (hκ : IsGen p κ) : κ ≠ 0 := by
  intro h0
  have h := (hκ (p ^ 2 - 1)).mpr dvd_rfl
  rw [h0, zero_pow] at h
  · exact zero_ne_one h
  · have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp
    omega

private theorem IsGen.pow_sq (hp : 1 < p) (hκ : IsGen p κ) : κ ^ (p ^ 2) = κ := by
  have h := (hκ (p ^ 2 - 1)).mpr dvd_rfl
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  calc κ ^ (p ^ 2) = κ ^ (p ^ 2 - 1 + 1) := by rw [Nat.sub_add_cancel h1]
    _ = κ := by rw [pow_succ, h, one_mul]

private theorem IsGen.mult_eq (hp3 : 3 ≤ p) (hκ : IsGen p κ) (j : ℕ) :
    κ ^ j * ((κ ^ j) ^ p)⁻¹ ^ 2 = κ ^ (p * (p - 2) * j) := by
  have hκ0 := hκ.ne_zero (by omega)
  have hne : ((κ ^ j) ^ p) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ hκ0))
  have key : κ ^ (p * (p - 2) * j) * ((κ ^ j) ^ p) ^ 2 = κ ^ j := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    have h : p * (p - 2) * j + j * (p * 2) = p ^ 2 * j := by
      zify [show 2 ≤ p by omega]
      ring
    rw [h, pow_mul, hκ.pow_sq (by omega)]
  rw [inv_pow, ← div_eq_mul_inv, div_eq_iff hne]
  exact key.symm

private theorem IsGen.pow_prime_iff (hp : 1 < p) (hκ : IsGen p κ) (n : ℕ) :
    (κ ^ n) ^ p = κ ^ n ↔ p ^ 2 - 1 ∣ n * (p - 1) := by
  have hx : κ ^ n ≠ 0 := pow_ne_zero _ (hκ.ne_zero hp)
  rw [← hκ, pow_mul]
  constructor
  · intro h
    have h' : κ ^ n * (κ ^ n) ^ (p - 1) = κ ^ n * 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hp.le, h, mul_one]
    exact mul_left_cancel₀ hx h'
  · intro h
    calc (κ ^ n) ^ p = (κ ^ n) ^ (p - 1 + 1) := by rw [Nat.sub_add_cancel hp.le]
      _ = κ ^ n * (κ ^ n) ^ (p - 1) := pow_succ' _ _
      _ = κ ^ n := by rw [h, mul_one]

section Prime

variable [Fact p.Prime] [CharP K p]

private theorem IsGen.exists_lam (hp3 : 3 ≤ p) (hκ : IsGen p κ) (hm : OrbitLen p m) :
    ∃ lam : ℕ, (lam : K) = κ ^ m * ((κ ^ m) ^ p)⁻¹ ^ 2 ∧ orderOf (lam : ZMod p) = p - 1 := by
  have hp : p.Prime := Fact.out
  rw [hκ.mult_eq hp3 m]
  have hmem : κ ^ (p * (p - 2) * m) ∈ (⊥ : Subfield K) := by
    rw [Subfield.mem_bot_iff_pow_eq_self K p, hκ.pow_prime_iff hp.one_lt]
    exact sq_sub_one_dvd hp3 hm
  obtain ⟨lam, hlam⟩ : ∃ lam : ℕ, (lam : K) = κ ^ (p * (p - 2) * m) := by
    rw [← ZMod.fieldRange_castHom_eq_bot p] at hmem
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a.val, by
      rw [← ha, ← map_natCast (ZMod.castHom (dvd_refl p) K), ZMod.natCast_zmod_val]⟩
  refine ⟨lam, hlam, ?_⟩
  have hpow : ∀ n : ℕ, (lam : ZMod p) ^ n = 1 ↔ p ^ 2 - 1 ∣ p * (p - 2) * m * n := fun n => by
    rw [← (ZMod.castHom (dvd_refl p) K).injective.eq_iff, map_pow, map_one,
      map_natCast (ZMod.castHom (dvd_refl p) K), hlam, ← pow_mul, hκ]
  rw [orderOf_eq_iff (by omega : 0 < p - 1)]
  refine ⟨(hpow _).mpr (sq_sub_one_dvd hp3 hm), fun j hjp hj0 => ?_⟩
  rw [Ne, hpow]
  exact not_sq_sub_one_dvd_pred hp3 hm hj0 hjp

private theorem IsGen.mult_not_mem_bot (hp3 : 3 ≤ p) (hκ : IsGen p κ) (hm : OrbitLen p m)
    {j : ℕ} (hj0 : 0 < j) (hjm : j < m) :
    κ ^ j * ((κ ^ j) ^ p)⁻¹ ^ 2 ∉ (⊥ : Subfield K) := by
  have hp : p.Prime := Fact.out
  rw [hκ.mult_eq hp3 j, Subfield.mem_bot_iff_pow_eq_self K p, hκ.pow_prime_iff hp.one_lt]
  exact not_sq_sub_one_dvd_mul hp3 hm hj0 hjm

end Prime

end Field

section Model

open CFSG.UnitaryThreeRecognition.Model CFSG.AGLEmbedding.UnitaryModel
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

private theorem root_mem_center_of_fst_eq_zero {K : Type} [Field K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {z : Coord J} (hz : z.1.1 = 0) :
    root J hJ z ∈ rootGroup J hJ ⊓
      Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  refine Subgroup.mem_inf.mpr ⟨root_mem_rootGroup J hJ z, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨y, rfl⟩ := (mem_rootGroup J hJ).1 hg
  have hb : z.1.2 + J.conj z.1.2 = 0 := by
    have h := z.2
    rw [hz] at h
    simpa using h
  have hz' : z = skewCoord J z.1.2 hb := Subtype.ext (Prod.ext hz rfl)
  have hc : y * z = z * y := by
    rw [hz']
    exact (skewCoord_central J _ hb y).symm
  rw [← map_mul, ← map_mul, hc]

private theorem torus_conj_eq_pow_mul {K : Type} [Field K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : Kˣ) (lam : ℕ)
    (hlam : (lam : K) = (k : K) * (J.conj (k : K))⁻¹ ^ 2)
    {x : ProjectiveSpecialUnitaryMatrixGroup J} (hx : x ∈ rootGroup J hJ) :
    ∃ z ∈ rootGroup J hJ ⊓
        Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      torus J hJ k * x * (torus J hJ k)⁻¹ = x ^ lam * z := by
  obtain ⟨y, rfl⟩ := (mem_rootGroup J hJ).1 hx
  refine ⟨root J hJ ((y ^ lam)⁻¹ * hermitianTorusAction J k y), ?_, ?_⟩
  · refine root_mem_center_of_fst_eq_zero J hJ ?_
    rw [coord_mul_val, coord_inv_val, coord_pow_val, hermitianTorusAction_fst]
    dsimp only
    rw [hlam]
    ring
  · rw [map_mul, map_inv, map_pow, ← torus_mul_root_mul_inv J hJ k y]
    group

private theorem mult_mem_bot_of_mem_normalizer {K : Type} [Field K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p ^ 2) (hp2 : p ≠ 2) (k : Kˣ)
    {F : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hZF : rootGroup J hJ ⊓
      Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ F)
    (hidx : F.relIndex (rootGroup J hJ) = p)
    (hn : torus J hJ k ∈ Subgroup.normalizer (F : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    (k : K) * (J.conj (k : K))⁻¹ ^ 2 ∈ (⊥ : Subfield K) := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  set F₀ : Subgroup (Coord J) := F.comap (root J hJ) with hF₀
  set L : Subgroup (Multiplicative K) := F₀.map (coordFst J) with hL
  have hsurj : Function.Surjective (coordFst J) := coordFst_surjective J h2
  have hker : (coordFst J).ker ≤ F₀ := by
    intro z hz
    have hz0 : z.1.1 = 0 := by
      have h : Multiplicative.ofAdd z.1.1 = 1 := MonoidHom.mem_ker.mp hz
      simpa using h
    exact Subgroup.mem_comap.mpr (hZF (root_mem_center_of_fst_eq_zero J hJ hz0))
  have hLidx : L.index = p := by
    rw [hL, Subgroup.index_map_eq F₀ hsurj hker, hF₀, Subgroup.index_comap]
    exact hidx
  have hLcard : Nat.card L = p := by
    have h1 := L.card_mul_index
    rw [hLidx, Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K), hK] at h1
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    rw [h1]
    ring
  have hstab : ∀ w ∈ L,
      Multiplicative.ofAdd ((k : K) * (J.conj (k : K))⁻¹ ^ 2 * Multiplicative.toAdd w) ∈ L := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hermitianTorusAction J k z, ?_, ?_⟩
    · refine Subgroup.mem_comap.mpr ?_
      rw [← torus_mul_root_mul_inv J hJ k z]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp (Subgroup.mem_comap.mp hz)
    · show Multiplicative.ofAdd (hermitianTorusAction J k z).1.1 = _
      rw [hermitianTorusAction_fst]
      show _ = Multiplicative.ofAdd (_ * z.1.1)
      congr 1
      ring
  have hL1 : L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hLcard
    exact hp.one_lt.ne hLcard
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hL1
  have hmem := mem_zpowers_of_prime_card hLcard (g := w)
    (g' := ⟨_, hstab (w : Multiplicative K) w.2⟩) hw
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hn' := congrArg (fun x : L => Multiplicative.toAdd (x : Multiplicative K)) hn
  simp only [Subgroup.coe_zpow, toAdd_zpow, toAdd_ofAdd] at hn'
  have hw0 : Multiplicative.toAdd (w : Multiplicative K) ≠ 0 := by
    intro h0
    apply hw
    apply Subtype.ext
    rw [Subgroup.coe_one]
    exact Multiplicative.toAdd.injective h0
  rw [mem_bot_iff_intCast p K]
  refine ⟨n, ?_⟩
  rw [zsmul_eq_mul] at hn'
  exact mul_right_cancel₀ hw0 hn'

private theorem exists_torusLines_rootGroup {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ 1) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ 1) :
    ∃ (t : ProjectiveSpecialUnitaryMatrixGroup J) (lam : ℕ),
      t ∈ Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∧
      orderOf (lam : ZMod p) = p - 1 ∧
      (∀ x ∈ rootGroup J hJ, ∃ z ∈ rootGroup J hJ ⊓ Subgroup.centralizer
          (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
        t ^ ((p + 1) / Nat.gcd 3 (p + 1)) * x * (t ^ ((p + 1) / Nat.gcd 3 (p + 1)))⁻¹ =
          x ^ lam * z) ∧
      ∀ j : ℕ, 0 < j → j < (p + 1) / Nat.gcd 3 (p + 1) →
        ∀ F : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
          rootGroup J hJ ⊓ Subgroup.centralizer
            (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ F →
          F ≤ rootGroup J hJ → F.relIndex (rootGroup J hJ) = p →
          t ^ j ∉ Subgroup.normalizer (F : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hK2 : Nat.card K = p ^ 2 := by rw [hK, pow_one]
  have hchar : CharP K p := charP_of_card hp hK
  have hconj : ∀ x : K, J.conj x = x ^ p := by
    intro x
    rw [huppert_II_10_4_conj_eq_frobenius J (p ^ 1) hK hfix x, pow_one]
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf k = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hk, Nat.card_units, hK2]
  have hgen : IsGen p (k : K) := by
    intro n
    rw [← Units.val_pow_eq_pow_val, Units.val_eq_one, ← orderOf_dvd_iff_pow_eq_one, hord]
  obtain ⟨lam, hlam, hlam1⟩ := hgen.exists_lam hp3 (orbit_cases p)
  refine ⟨torus J hJ k, lam,
    torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ k), hlam1, ?_, ?_⟩
  · intro x hx
    rw [← map_pow]
    refine torus_conj_eq_pow_mul J hJ (k ^ ((p + 1) / Nat.gcd 3 (p + 1))) lam ?_ hx
    rw [hlam, Units.val_pow_eq_pow_val, hconj]
  · intro j hj0 hjm F hZF hFS hidx hnorm
    rw [← map_pow] at hnorm
    have h := mult_mem_bot_of_mem_normalizer J hJ hK2 hp2 (k ^ j) hZF hidx hnorm
    rw [Units.val_pow_eq_pow_val, hconj] at h
    exact hgen.mult_not_mem_bot hp3 (orbit_cases p) hj0 hjm h

end Model

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model in
theorem kFactUnitaryTorusLines :
    ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
      ∀ [Fact p.Prime] (T : Sylow p K),
      ∃ (t : K) (lam : ℕ), t ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) ∧
        orderOf (lam : ZMod p) = p - 1 ∧
        (∀ x ∈ (T : Subgroup K),
          ∃ z ∈ (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K),
            t ^ ((p + 1) / Nat.gcd 3 (p + 1)) * x * (t ^ ((p + 1) / Nat.gcd 3 (p + 1)))⁻¹ =
              x ^ lam * z) ∧
        ∀ j : ℕ, 0 < j → j < (p + 1) / Nat.gcd 3 (p + 1) → ∀ F : Subgroup K,
          (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) ≤ F →
          F ≤ (T : Subgroup K) → F.relIndex (T : Subgroup K) = p →
          t ^ j ∉ Subgroup.normalizer (F : Set K) := by
  intro L _ _ d ⟨e⟩ p hp hp2 ⟨q, hqp, hq1, hd⟩ _ U
  have hdU : CFSG.AGLEmbedding.IsUnitaryIndex p d := ⟨q, hqp, hd⟩
  have hf1 : d.1.fieldExponent = 1 := by rw [hd]; simp [hq1]
  obtain ⟨-, hf, -, K, _, _, J, hJ, hK, hfix, ⟨e0⟩⟩ :=
    CFSG.AGLEmbedding.UnitaryModel.exists_equiv_psu
      (CFSG.AGLEmbedding.UnitaryModel.statedClassicalModel hdU ⟨e⟩)
  obtain ⟨S, hS⟩ := CFSG.AGLEmbedding.UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := CFSG.AGLEmbedding.UnitaryModel.exists_equiv_map_eq e0 U S
  have hU : (U : Subgroup L).map e'.toMonoidHom =
      rootGroup J hJ := he'.trans hS
  rw [hf1] at hK hfix
  obtain ⟨t, lam, ht, hlam, hscal, hlines⟩ := exists_torusLines_rootGroup J hJ hp2 hK hfix
  have hZ : ∀ x : L, e' x ∈ rootGroup J hJ ⊓
        Subgroup.centralizer (rootGroup J hJ :
          Set (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
      x ∈ (U : Subgroup L) ⊓ Subgroup.centralizer ((U : Subgroup L) : Set L) := by
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← hU,
      CFSG.AGLEmbedding.UnitaryModel.mem_map_iff,
      CFSG.AGLEmbedding.UnitaryModel.mem_centralizer_map_iff]
  have hmem : ∀ x : L, x ∈ (U : Subgroup L) ↔
      e' x ∈ rootGroup J hJ := fun x => by
    rw [← hU]
    exact (CFSG.AGLEmbedding.UnitaryModel.mem_map_iff e' _ x).symm
  have hN : ∀ (S : Subgroup L) (x : L), e' x ∈ Subgroup.normalizer
      ((S.map e'.toMonoidHom : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
        Set (ProjectiveSpecialUnitaryMatrixGroup J)) ↔ x ∈ Subgroup.normalizer (S : Set L) := by
    intro S x
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact CFSG.AGLEmbedding.UnitaryModel.mem_map_iff e' _ x
  refine ⟨e'.symm t, lam, ?_, hlam, ?_, ?_⟩
  · have h := hN (U : Subgroup L) (e'.symm t)
    rw [MulEquiv.apply_symm_apply, hU] at h
    exact h.mp ht
  · intro x hx
    obtain ⟨z, hz, heq⟩ := hscal (e' x) ((hmem x).mp hx)
    refine ⟨e'.symm z, ?_, e'.injective ?_⟩
    · apply (hZ _).mp
      rwa [MulEquiv.apply_symm_apply]
    · simp only [map_mul, map_pow, map_inv, MulEquiv.apply_symm_apply]
      exact heq
  · intro j hj0 hjm F hZF hFU hidx hnorm
    refine hlines j hj0 hjm (F.map e'.toMonoidHom) ?_ ?_ ?_ ?_
    · intro y hy
      obtain ⟨x, rfl⟩ := e'.surjective y
      exact ⟨x, hZF ((hZ x).mp hy), rfl⟩
    · rw [← hU]
      exact Subgroup.map_mono hFU
    · rw [← hU, Subgroup.relIndex_map_map_of_injective F _ e'.injective]
      exact hidx
    · have h := (hN F _).mpr hnorm
      rwa [map_pow, MulEquiv.apply_symm_apply] at h

theorem exists_lines_torus_u3 {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup X} {d : TauCeti.ValidLieTypeIndex}
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .twistedA 2 q)
    {R : Sylow p X} (hRK : (R : Subgroup X) ≤ K) :
    ∃ t ∈ K, t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
      ∃ lam : ℕ, orderOf (lam : ZMod p) = p - 1 ∧
      (∀ x ∈ (R : Subgroup X),
        ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
          t ^ ((p + 1) / Nat.gcd 3 (p + 1)) * x * (t ^ ((p + 1) / Nat.gcd 3 (p + 1)))⁻¹ =
            x ^ lam * z) ∧
      ∀ j : ℕ, 0 < j → j < (p + 1) / Nat.gcd 3 (p + 1) → ∀ F : Subgroup X,
        (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ F →
        F ≤ (R : Subgroup X) → F.relIndex (R : Subgroup X) = p →
        t ^ j ∉ Subgroup.normalizer (F : Set X) := by
  have hT := kFactUnitaryTorusLines
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, lam, ht, hlam, hscal, hlines⟩ := hT K d ⟨e⟩ p hp hp2 hd (R.subtype hRK)
  rw [Sylow.coe_subtype] at ht hscal hlines
  have hZ : ∀ z : K, z ∈ (R : Subgroup X).subgroupOf K ⊓
      Subgroup.centralizer (((R : Subgroup X).subgroupOf K : Subgroup K) : Set K) →
      (z : X) ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hz).1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2
      ⟨h, hRK hh⟩ (Subgroup.mem_subgroupOf.mpr hh)
    exact congrArg Subtype.val h1
  refine ⟨(t : X), t.2, ?_, lam, hlam, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    by_cases hhK : h ∈ K
    · have h1 := Subgroup.mem_normalizer_iff.mp ht ⟨h, hhK⟩
      simpa [Subgroup.mem_subgroupOf] using h1
    · constructor
      · intro hh
        exact absurd (hRK hh) hhK
      · intro hh
        exfalso
        apply hhK
        have h2 : h = (t : X)⁻¹ * ((t : X) * h * (t : X)⁻¹) * (t : X) := by group
        rw [h2]
        exact K.mul_mem (K.mul_mem (K.inv_mem t.2) (hRK hh)) t.2
  · intro x hx
    obtain ⟨z, hz, heq⟩ := hscal ⟨x, hRK hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
    refine ⟨(z : X), hZ z hz, ?_⟩
    have h1 := congrArg Subtype.val heq
    simpa using h1
  · intro j hj0 hjm F hZF hFR hidx hnorm
    refine hlines j hj0 hjm (F.subgroupOf K) ?_ ?_ ?_ ?_
    · intro z hz
      exact Subgroup.mem_subgroupOf.mpr (hZF (hZ z hz))
    · intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hFR (Subgroup.mem_subgroupOf.mp hx))
    · rw [Subgroup.relIndex_subgroupOf hRK]
      exact hidx
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      have h1 := Subgroup.mem_normalizer_iff.mp hnorm (h : X)
      simpa [Subgroup.mem_subgroupOf] using h1

theorem one_lt_lineOrbit {p : ℕ} (hp3 : 3 ≤ p) : 1 < (p + 1) / Nat.gcd 3 (p + 1) := by
  rcases orbit_cases p with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

theorem eq_or_eq_of_lines {G : Type*} [Group G] [Finite G] {p m : ℕ} (hp : p.Prime)
    (hm : 1 < m) {R Z V : Subgroup G} {t : G} (hcR : Nat.card R = p ^ 3)
    (hcZ : Nat.card Z = p)
    (hlines : ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup G, Z ≤ F → F ≤ R →
      F.relIndex R = p → t ^ j ∉ Subgroup.normalizer (F : Set G))
    (hZV : Z ≤ V) (hVR : V ≤ R) (hV : t ∈ Subgroup.normalizer (V : Set G)) :
    V = Z ∨ V = R := by
  obtain ⟨k, hk, hkV⟩ := (Nat.dvd_prime_pow hp).mp
    ((Subgroup.card_dvd_of_le hVR).trans (hcR ▸ dvd_rfl : Nat.card R ∣ p ^ 3))
  have hpV : p ∣ Nat.card V := hcZ ▸ Subgroup.card_dvd_of_le hZV
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [pow_zero] at hkV
      have := Nat.le_of_dvd Nat.one_pos (hkV ▸ hpV)
      exact absurd this (by have := hp.two_le; omega)
    · exact h
  interval_cases k
  · left
    exact (Subgroup.eq_of_le_of_card_ge hZV (by rw [hcZ, hkV, pow_one])).symm
  · exfalso
    have hidx : V.relIndex R = p := by
      have h := Subgroup.relIndex_mul_card (H := V) (K := R)
      rw [inf_eq_left.mpr hVR, hkV, hcR] at h
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2)
      rw [h]
      ring
    exact hlines 1 Nat.one_pos hm V hZV hVR hidx (by rwa [pow_one])
  · right
    exact Subgroup.eq_of_le_of_card_ge hVR (by rw [hcR, hkV])

end CFSG.AGLEmbeddingD2
