module

public import CFSG.HardMathSupport.Solomon.Coordinator.I2_5
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIHopf
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem i2326c_glaPComponent {X : Type*} [Group X] [Finite X] {S D : Subgroup X}
    (hD : IsComponentOf D S) (h3 : 3 ∣ Nat.card (↥D ⧸ Subgroup.center ↥D)) :
    GLAPComponent 3 S D := by
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨hDS, hsn, hq⟩ := hD
  set O : Subgroup ↥S := GLAPPrimeCore 3 ↥S with hO
  let ψ : ↥D →* ↥S ⧸ O := (QuotientGroup.mk' O).comp (Subgroup.inclusion hDS)
  have hcop : Nat.Coprime 3 (Nat.card O) := coprime_card_gLAPPrimeCore_aux 3 ↥S
  have hker_ne : ψ.ker ≠ ⊤ := by
    intro htop
    have hmem : ∀ d : ↥D, Subgroup.inclusion hDS d ∈ O := fun d => by
      have : d ∈ ψ.ker := htop ▸ Subgroup.mem_top d
      rw [MonoidHom.mem_ker] at this
      exact (QuotientGroup.eq_one_iff _).1 this
    let f : ↥D →* ↥O := (Subgroup.inclusion hDS).codRestrict O hmem
    have hinj : Function.Injective f := fun a b hab => by
      have h1 : Subgroup.inclusion hDS a = Subgroup.inclusion hDS b :=
        congrArg Subtype.val hab
      exact Subgroup.inclusion_injective hDS h1
    have hdvd : Nat.card ↥D ∣ Nat.card ↥O := by
      rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have h3D : 3 ∣ Nat.card ↥D := h3.trans (Subgroup.card_quotient_dvd_card _)
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop (h3D.trans hdvd)
  have hcen : ψ.ker ≤ Subgroup.center ↥D :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq ψ.ker hker_ne
  have hrange : ψ.range = barX 3 S D := by
    ext y
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨Subgroup.inclusion hDS d, Subgroup.mem_subgroupOf.2 d.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨(s : X), Subgroup.mem_subgroupOf.1 hs⟩, rfl⟩
  have hqbar : CFSG.Open.IsQuasisimple ↥(barX 3 S D) := by
    have := CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hq ψ hker_ne
    rwa [hrange] at this
  refine ⟨hDS, hsn, ⟨le_top, LocalBalance.Lemma512Ns.barX_isSubnormal_top 3 hsn, hqbar⟩, ?_⟩
  intro J hJ hJsn heq
  have hJD : J ≤ D := hJ.le
  have hperf : ⁅D, D⁆ = D := i25_commutator_eq hq
  have hcen' : ∀ n ∈ D, n ∈ GLAPPrimeCoreOf 3 S → ∀ d ∈ D, n * d = d * n := by
    intro n hnD hnO d hd
    obtain ⟨s, hs, hsn'⟩ := hnO
    have hk : (⟨n, hnD⟩ : ↥D) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      show (QuotientGroup.mk' O) (Subgroup.inclusion hDS ⟨n, hnD⟩) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have : Subgroup.inclusion hDS ⟨n, hnD⟩ = s := Subtype.ext hsn'.symm
      rw [this]
      exact hs
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 (hcen hk) ⟨d, hd⟩)).symm
  have hle : barX 3 S D ≤ barX 3 S J := (show barX 3 S J = barX 3 S D from heq).symm.le
  have hDJ : ⁅D, D⁆ ≤ J := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨j1, hj1, hn1⟩ := exists_of_barX_le (X := S) hle ha (hDS ha)
    obtain ⟨j2, hj2, hn2⟩ := exists_of_barX_le (X := S) hle hb (hDS hb)
    have hn1D : j1⁻¹ * a ∈ D := D.mul_mem (D.inv_mem (hJD hj1)) ha
    have hn2D : j2⁻¹ * b ∈ D := D.mul_mem (D.inv_mem (hJD hj2)) hb
    have e1 : a = j1 * (j1⁻¹ * a) := by group
    have e2 : b = j2 * (j2⁻¹ * b) := by group
    have hc1 := hcen' _ hn1D hn1
    have hc2 := hcen' _ hn2D hn2
    have key : ⁅a, b⁆ = ⁅j1, j2⁆ := by
      have h := lbi_commutatorElement_mul_mul (a := j1) (b := j2) (z₁ := j1⁻¹ * a)
        (z₂ := j2⁻¹ * b) (hc1 j2 (hJD hj2)) (hc1 _ hn2D) (hc2 j1 (hJD hj1))
      rwa [← e1, ← e2] at h
    rw [key]
    exact J.mul_mem (J.mul_mem (J.mul_mem hj1 hj2) (J.inv_mem hj1)) (J.inv_mem hj2)
  rw [hperf] at hDJ
  exact (not_le_of_gt hJ) hDJ

theorem i2326c_le_layer_centralizer {X : Type*} [Group X] [Finite X] {L K : Subgroup X} {z : X}
    (hK : IsComponentOf K ⊤) (hKL : K ≤ L) (h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K))
    (hz : ∀ k ∈ K, z * k = k * z) :
    K ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer ({z} : Set X)) := by
  have hle : K ≤ L ⊓ Subgroup.centralizer ({z} : Set X) :=
    le_inf hKL (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hz k hk).symm)
  have hcomp : IsComponentOf K (L ⊓ Subgroup.centralizer ({z} : Set X)) :=
    ⟨hle, isSubnormal_of_le_of_le hK.2.1 hle le_top, hK.2.2⟩
  exact le_sSup (i2326c_glaPComponent hcomp h3)

theorem i2326c_sq_mod {q : ℕ} (h : q % 3 ≠ 0) : (q ^ 2 - 1) % 3 = 0 := by
  have h1 : q ^ 2 % 3 = 1 := by
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  exact Nat.sub_mod_eq_zero_of_mod_eq (by simpa using h1)

theorem i2326c_cube_sub {q : ℕ} (h : q % 3 = 1) : (q ^ 3 - 1) % 3 = 0 := by
  have h1 : q ^ 3 % 3 = 1 := by simp [Nat.pow_mod, h]
  exact Nat.sub_mod_eq_zero_of_mod_eq (by simpa using h1)

theorem i2326c_cube_add {q : ℕ} (h : q % 3 = 2) : (q ^ 3 + 1) % 3 = 0 := by
  have h1 : q ^ 3 % 3 = 2 := by simp [Nat.pow_mod, h]
  omega

theorem i2326c_three_dvd_psl_formula {q : ℕ} (h : q % 3 ≠ 0) :
    3 ∣ q ^ (3 * (3 - 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  have hq3 : q ^ (3 * (3 - 1) / 2) = q ^ 3 := by norm_num
  rw [hq3]
  have hsq := Nat.dvd_of_mod_eq_zero (i2326c_sq_mod h)
  rcases (show q % 3 = 1 ∨ q % 3 = 2 by omega) with h1 | h2
  · have hdvd : 3 ∣ q - 1 := by omega
    rw [Nat.gcd_eq_left hdvd]
    obtain ⟨a, ha⟩ := hsq
    obtain ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero (i2326c_cube_sub h1)
    have : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = 3 * (q ^ 3 * (3 * a * b)) := by
      rw [ha, hb]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    exact Dvd.dvd.mul_left (Dvd.intro (a * b) (by ring)) _
  · have hcop : Nat.Coprime 3 (q - 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    rw [hcop, Nat.div_one]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hsq _) _

theorem i2326c_three_dvd_psu_formula {q : ℕ} (h : q % 3 ≠ 0) :
    3 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
  have hsq := Nat.dvd_of_mod_eq_zero (i2326c_sq_mod h)
  rcases (show q % 3 = 1 ∨ q % 3 = 2 by omega) with h1 | h2
  · have hcop : Nat.Coprime 3 (q + 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    rw [hcop, Nat.div_one]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hsq _) _
  · have hdvd : 3 ∣ q + 1 := by omega
    rw [Nat.gcd_eq_left hdvd]
    obtain ⟨a, ha⟩ := hsq
    obtain ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero (i2326c_cube_add h2)
    have : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) = 3 * (q ^ 3 * (3 * a * b)) := by
      rw [ha, hb]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    exact Dvd.dvd.mul_left (Dvd.intro (a * b) (by ring)) _

theorem i2326c_three_dvd_card_psl {F : Type} [Field F] [Finite F] (h : Nat.card F % 3 ≠ 0) :
    3 ∣ Nat.card (StatedProj (StatedSL 3 F)) := by
  have e := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 3)
    (by norm_num : 1 ≤ 3)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at e
  have goal : 3 ∣ Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSL 3 F)) := by
    rw [e]
    exact i2326c_three_dvd_psl_formula h
  exact goal

theorem i2326c_three_dvd_card_psu {F : Type} [Field F] [Finite F] {q : ℕ}
    (hK : Nat.card F = q ^ 2) (h : q % 3 ≠ 0) :
    3 ∣ Nat.card (StatedProj (StatedSU 3 q F)) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hpc, n, hp, hn⟩ := FiniteField.card' (K := F)
  have hqn : q ^ 2 = p ^ (n : ℕ) := by rw [← hK, Nat.card_eq_fintype_card, hn]
  have hqd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hqn]; ring⟩
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1 hqd
  have hq1 : q ≠ 1 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := F)
    rw [hK] at h1
    simp at h1
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exact absurd (by simpa [h0] using hf) hq1
    · exact h0
  subst hf
  have e := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F) hp hf1 hK
    (by norm_num : 2 ≤ 3)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at e
  have goal : 3 ∣ Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) F)) := by
    rw [e]
    have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
    have h2 : (((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (p ^ f) ^ 2 - 1 := by
      have : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
      rw [show ((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) by
        push_cast [Nat.cast_sub this]; ring]
      exact Int.toNat_natCast _
    have h3 : (((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (p ^ f) ^ 3 + 1 := by
      rw [show ((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = (((p ^ f) ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
      exact Int.toNat_natCast _
    rw [h2, h3]
    simpa using i2326c_three_dvd_psu_formula h
  exact goal

theorem i2326c_three_dvd_of_type (hONG : UniquenessMaximal.InputONGroup) {Y : Type} [Group Y]
    [Finite Y] (h : LocalBalance.Lemma55Ns.IsLThreeEpsOrON Y) : 3 ∣ Nat.card Y := by
  rcases h with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, q, hF, hq, -, ⟨e⟩⟩ | e0
  · rw [Nat.card_congr e.toEquiv]
    exact i2326c_three_dvd_card_psl hF
  · rw [Nat.card_congr e.toEquiv]
    exact i2326c_three_dvd_card_psu hF hq
  · obtain ⟨e⟩ := e0
    rw [Nat.card_congr e.toEquiv, hONG.2]
    unfold orderON
    norm_num

end CFSG.HardMathSupport.Solomon.Coordinator
