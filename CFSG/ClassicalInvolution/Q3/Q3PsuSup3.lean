module

public import CFSG.ClassicalInvolution.Asc77.AscC22G13
public import CFSG.ClassicalInvolution.Phan.Phan3AFinal
public import CFSG.ClassicalInvolution.Q3.Q3WASTLift
public import CFSG.ClassicalInvolution.Q3.Q3T7E9OrthModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PsuSup

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.Q3G CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.C22G
open scoped MatrixGroups

section Center

theorem pow_four_of_mem_center_su_four {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) {z : Phan.Su K p f 4}
    (hz : z ∈ Subgroup.center (Phan.Su K p f 4)) : z ^ 4 = 1 := by
  classical
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨u, hu⟩ := Phan.exists_scalar_of_mem_center hσ (by norm_num) hz
  have h1 := (CFSG.ClassicalGroups.Unitary.mem_SUid_iff
    (σ := CFSG.LieType.BorelTits.unitaryInvolution K p f)).mp z.2
  have h2 := h1.1
  rw [hu, Matrix.scalar_apply, Matrix.det_diagonal] at h2
  have h3 : ((u : Kˣ) : K) ^ 4 = 1 := by simpa using h2
  have h4 : u ^ 4 = 1 := Units.ext (by simpa using h3)
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val]
  have hu' : ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.scalar (Fin 4) (u : K) := hu
  rw [hu', ← map_pow]
  simp [h3]

theorem card_center_su_four_le' {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (Subgroup.center (Phan.Su K p f 4)) ≤ 4 := by
  classical
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  have hu : ∀ z : Subgroup.center (Phan.Su K p f 4), ∃ u : Kˣ,
      (((z : Phan.Su K p f 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        Matrix.scalar (Fin 4) (u : K) := fun z =>
    Phan.exists_scalar_of_mem_center hσ (by norm_num) z.2
  choose φ hφ using hu
  have hdet : ∀ z : Subgroup.center (Phan.Su K p f 4), φ z ^ 4 = 1 := by
    intro z
    have h1 := (CFSG.ClassicalGroups.Unitary.mem_SUid_iff
      (σ := CFSG.LieType.BorelTits.unitaryInvolution K p f)).mp (z : Phan.Su K p f 4).2
    have h2 := h1.1
    rw [hφ z, Matrix.scalar_apply, Matrix.det_diagonal] at h2
    have h3 : ((φ z : Kˣ) : K) ^ 4 = 1 := by simpa using h2
    exact Units.ext (by simpa using h3)
  have hinj : Function.Injective fun z : Subgroup.center (Phan.Su K p f 4) =>
      (⟨φ z, (mem_rootsOfUnity 4 (φ z)).mpr (hdet z)⟩ : rootsOfUnity 4 K) := by
    intro z z' h
    have h1 : φ z = φ z' := congrArg (fun x : rootsOfUnity 4 K => (x : Kˣ)) h
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [hφ z, hφ z', h1]
  have h := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (rootsOfUnity 4 K) ≤ 4 := card_rootsOfUnity K 4
  exact h.trans h2

end Center

section Chain


theorem admissible_psu4_three' : StatedLieAdmissible .PSU 4 3 1 :=
  ⟨Fact.out, Nat.one_pos, by norm_num, by simp⟩

theorem psu_chain_sup_top3 (hC : PhanA3Completion3)
    {R₁ R₂ R₃ : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K}
    (h12 : ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₁ R₂)
    (h23 : ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₂ R₃)
    (h13 : Commutes R₁ R₃) : R₁ ⊔ R₂ ⊔ R₃ = ⊤ := by
  classical
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have hq2 : 3 ^ 1 ≠ 2 := by norm_num
  have hadm := admissible_psu4_three'
  have hfin : Finite (modelUniv .PSU 4 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (by norm_num) Fact.out (by trivial) hadm
  obtain ⟨φ, -⟩ := RouteD.psu_model_equiv (p := 3) (by norm_num) hadm
  have hperf : Group.IsPerfect (modelUniv .PSU 4 3 1 Fact.out).K := by
    have := isPerfect_su3 (n := 4) (by norm_num)
    exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  have := hperf
  set H : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K := R₁ ⊔ R₂ ⊔ R₃ with hH
  have hR₁ : R₁ ≤ H := le_sup_left.trans le_sup_left
  have hR₂ : R₂ ≤ H := le_sup_right.trans le_sup_left
  have hR₃ : R₃ ≤ H := le_sup_right
  obtain ⟨W₁, hW₁⟩ := h12
  obtain ⟨W₂, hW₂⟩ := h23
  have hW₁H : W₁ ≤ H := by
    rw [typeU_standardPair_eq_sup hK hq2 hW₁]
    exact sup_le hR₁ hR₂
  have hW₂H : W₂ ≤ H := by
    rw [typeU_standardPair_eq_sup hK hq2 hW₂]
    exact sup_le hR₂ hR₃
  let U' : Fin 3 → Subgroup ↥H := ![R₁.subgroupOf H, R₂.subgroupOf H, R₃.subgroupOf H]
  have hcomm : ∀ i j : Fin 3, (i : ℕ) + 1 < j → ∀ x ∈ U' i, ∀ y ∈ U' j, x * y = y * x := by
    intro i j hij x hx y hy
    fin_cases i <;> fin_cases j <;> simp at hij
    exact Subtype.ext (h13 _ hx _ hy)
  have hpair : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (U' i) (U' j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact ⟨_, Generic.unitaryBlockStandardPair_subgroupOf hW₁H hW₁⟩
    · exact ⟨_, Generic.unitaryBlockStandardPair_subgroupOf hW₂H hW₂⟩
  have hgen : ⨆ i, U' i = ⊤ := by
    have h1 := Subgroup.subgroupOf_sup (A := R₁ ⊔ R₂) (A' := R₃) (B := H) (sup_le hR₁ hR₂) hR₃
    have h2 := Subgroup.subgroupOf_sup (A := R₁) (A' := R₂) (B := H) hR₁ hR₂
    have h3 : (R₁ ⊔ R₂ ⊔ R₃).subgroupOf H = ⊤ := Subgroup.subgroupOf_self H
    refine eq_top_iff.mpr ?_
    rw [← h3, h1, h2]
    exact sup_le (sup_le (le_iSup U' 0) (le_iSup U' 1)) (le_iSup U' 2)
  have hP₀₁ := hpair 0 1 rfl
  have hP₁₂ := hpair 1 2 rfl
  have hW : Phan.WeakPhanA (GaloisField 3 2) 3 1 3 U' (fun i j => U' i ⊔ U' j) := by
    refine ⟨?_, fun _ _ _ => rfl, hcomm, ?_, hgen⟩
    · intro i
      obtain ⟨W, hW⟩ := hP₀₁
      obtain ⟨W', hW'⟩ := hP₁₂
      fin_cases i
      · exact (Phan.nonempty_mulEquiv_of_standardPair hK hW).1
      · exact (Phan.nonempty_mulEquiv_of_standardPair hK hW).2
      · exact (Phan.nonempty_mulEquiv_of_standardPair hK hW').2
    · intro i j hj
      obtain ⟨W, hW⟩ := hpair i j hj
      rwa [typeU_standardPair_eq_sup hK hq2 hW] at hW
  obtain ⟨E, instE, p, ε, V, hpsurj, hker, hVp, hVε⟩ := hC hW
  have hεsurj : Function.Surjective ε := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine iSup_le fun i => ?_
    have h1 := Subgroup.map_le_range ε (V i)
    rwa [hVε i] at h1
  set Z₃ : Subgroup ↥H := p.ker.map ε with hZ₃
  have hZ₃c : Z₃ ≤ Subgroup.center ↥H := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨hecen, -⟩ := hker e he
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨e', rfl⟩ := hεsurj y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hecen e']
  have hZ₃n : Z₃.Normal := ⟨fun n hn g => by
    have h := Subgroup.mem_center_iff.mp (hZ₃c hn) g
    rw [h, mul_inv_cancel_right]
    exact hn⟩
  let π : E →* ↥H ⧸ Z₃ := (QuotientGroup.mk' Z₃).comp ε
  have hpπ : p.ker ≤ π.ker := by
    intro e he
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' Z₃) (ε e) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨e, he, rfl⟩
  let θ : Su (GaloisField 3 2) 3 1 4 →* ↥H ⧸ Z₃ :=
    MonoidHom.liftOfRightInverse p (Function.surjInv hpsurj) (Function.rightInverse_surjInv hpsurj)
      ⟨π, hpπ⟩
  have hθp : ∀ e, θ (p e) = π e := fun e =>
    MonoidHom.liftOfRightInverse_comp_apply p (Function.surjInv hpsurj)
      (Function.rightInverse_surjInv hpsurj) ⟨π, hpπ⟩ e
  have hθsurj : Function.Surjective θ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, rfl⟩ := hεsurj y
    exact ⟨p e, by rw [hθp]; rfl⟩
  have h24 : 2 ∣ Nat.card ↥H := by
    obtain ⟨e₁⟩ := (Phan.nonempty_mulEquiv_of_standardPair hK hW₁).1
    have hc1 : Nat.card R₁ = 24 := by
      rw [← Nat.card_congr e₁.toEquiv]
      exact card_su2
    have hd : Nat.card R₁ ∣ Nat.card ↥H := Subgroup.card_dvd_of_le hR₁
    rw [hc1] at hd
    exact (by norm_num : 2 ∣ 24).trans hd
  have hnontriv : ∃ k, θ k ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 h24
    obtain ⟨e, rfl⟩ := hεsurj x
    have hmem : ε e ∈ Z₃ := by
      have h := hall (p e)
      rw [hθp] at h
      exact (QuotientGroup.eq_one_iff _).1 h
    obtain ⟨e', he', hee'⟩ := hmem
    obtain ⟨-, k, hk⟩ := hker e' he'
    have hpow : (ε e) ^ 3 ^ k = 1 := by rw [← hee', ← map_pow, hk, map_one]
    have hdvd : 2 ∣ 3 ^ k := hx2 ▸ orderOf_dvd_of_pow_eq_one hpow
    have h23' : 2 ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
    omega
  have hquasi : CFSG.IsQuasisimple (Su (GaloisField 3 2) 3 1 4) := by
    have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK (n := 4)
      (by norm_num) (by
        intro h
        have : (4 : ℕ) = 3 := (Prod.mk.inj h).1
        omega)).1
    exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 4)).symm h
  have hkerθ : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hquasi hnontriv
  have hker4 : Nat.card θ.ker ≤ 4 :=
    (Subgroup.card_le_of_le hkerθ).trans (card_center_su_four_le' hK)
  have hS : Nat.card (Su (GaloisField 3 2) 3 1 4) = Nat.card (↥H ⧸ Z₃) * Nat.card θ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj).toEquiv]
  have hHZ : Nat.card (↥H ⧸ Z₃) ≤ Nat.card ↥H := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z₃
    have hpos : 0 < Nat.card Z₃ := Nat.card_pos
    calc Nat.card (↥H ⧸ Z₃) = Nat.card (↥H ⧸ Z₃) * 1 := (mul_one _).symm
      _ ≤ Nat.card (↥H ⧸ Z₃) * Nat.card Z₃ := Nat.mul_le_mul_left _ hpos
      _ = Nat.card ↥H := h.symm
  have hcardM : Nat.card (modelUniv .PSU 4 3 1 Fact.out).K =
      Nat.card (Su (GaloisField 3 2) 3 1 4) := Nat.card_congr φ.toEquiv
  have hidx : H.index * Nat.card ↥H = Nat.card (modelUniv .PSU 4 3 1 Fact.out).K :=
    Subgroup.index_mul_card H
  have hposH : 0 < Nat.card ↥H := Nat.card_pos
  have h1 : H.index * Nat.card ↥H ≤ 4 * Nat.card ↥H := by
    calc H.index * Nat.card ↥H = Nat.card (modelUniv .PSU 4 3 1 Fact.out).K := hidx
      _ = Nat.card (Su (GaloisField 3 2) 3 1 4) := hcardM
      _ = Nat.card (↥H ⧸ Z₃) * Nat.card θ.ker := hS
      _ ≤ Nat.card ↥H * 4 := Nat.mul_le_mul hHZ hker4
      _ = 4 * Nat.card ↥H := mul_comm _ _
  exact T7Z.eq_top_of_index_le_four H (Nat.le_of_mul_le_mul_right h1 hposH)

theorem psuLayer_sup3 {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (P : PSULayer 3 1 Φ) {K J J' : Subgroup X}
    {RK RJ RJ' : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K}
    (hRJ' : RJ' ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D)
    (hKR : K = RK.map P.ψ) (hJR : J = RJ.map P.ψ) (hJ'R : J' = RJ'.map P.ψ)
    (h1 : ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W RJ' RK)
    (h2 : ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W RK RJ)
    (hc : Commutes J J') : J' ⊔ K ⊔ J = omegaGen Φ := by
  have hadm := admissible_psu4_three'
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  obtain ⟨φ, -⟩ := RouteD.psu_model_equiv (p := 3) (by norm_num) hadm
  have hgen3 : ModelFacts.Gen3 RJ' :=
    Q3T7E9.gen3_of_mem_fundamentalSubgroups_three (t := .PSU) (n := 4) (by trivial) hadm
      (by decide) (by decide) hRJ'
  have hk3 : ∀ x ∈ P.ψ.ker, x ^ 3 = 1 → x = 1 := by
    intro x hx hx3
    have hxc : x ∈ Subgroup.center (modelUniv .PSU 4 3 1 Fact.out).K := P.ker_le hx
    have hφc : φ x ∈ Subgroup.center (Su (GaloisField 3 2) 3 1 4) := by
      rw [Subgroup.mem_center_iff] at hxc ⊢
      intro g
      obtain ⟨y, rfl⟩ := φ.surjective g
      rw [← map_mul, ← map_mul, hxc y]
    have h4 := pow_four_of_mem_center_su_four hK hφc
    have h3 : φ x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    have h5 : φ x = 1 := by
      calc φ x = φ x ^ 4 * (φ x ^ 3)⁻¹ := by group
        _ = 1 := by rw [h4, h3]; simp
    exact φ.injective (h5.trans (map_one φ).symm)
  have hcomm : Commutes RJ' RJ := by
    intro a ha b hb
    refine ModelFacts.commute_of_map_commute_of_gen3 P.ψ P.ker_le hk3 hgen3 (b := b)
      (fun a' ha' => ?_) a ha
    have hb' : P.ψ b ∈ J := by rw [hJR]; exact Subgroup.mem_map_of_mem _ hb
    have ha'' : P.ψ a' ∈ J' := by rw [hJ'R]; exact Subgroup.mem_map_of_mem _ ha'
    exact (hc _ hb' _ ha'').symm
  have htop : RJ' ⊔ RK ⊔ RJ = ⊤ := psu_chain_sup_top3 phanA3Completion3_of_cert h1 h2 hcomm
  rw [hKR, hJR, hJ'R, ← Subgroup.map_sup, ← Subgroup.map_sup, htop, Subgroup.map_top,
    P.range_eq]

end Chain

end CFSG.ClassicalInvolution.Q3.Q3PsuSup
