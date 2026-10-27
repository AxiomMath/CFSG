module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual

public section

namespace CFSG.CGT.PushingUpLit.BHS

open Subgroup CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

variable {H : Type*} [Group H] {F : Type*} [Field F] [CharP F 2]

theorem exists_order_three_sl2 :
    ∃ m : Matrix.SpecialLinearGroup (Fin 2) F, m ^ 3 = 1 ∧ m ≠ 1 := by
  have h2 : (1 : F) + 1 = 0 := by simpa using CharTwo.add_self_eq_zero (1 : F)
  have h1 : (-1 : F) = 1 := CharTwo.neg_eq 1
  obtain ⟨m, hm⟩ : ∃ m : Matrix.SpecialLinearGroup (Fin 2) F,
      (m : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] :=
    ⟨⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two, h1]⟩, rfl⟩
  refine ⟨m, ?_, ?_⟩
  · ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, hm, Matrix.mul_apply, Fin.sum_univ_two, h2]
  · intro h
    have := congrArg
      (fun m : Matrix.SpecialLinearGroup (Fin 2) F => (m : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [hm] at this

theorem not_forall_two_power_sl2 :
    ¬ ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, ∃ k : ℕ, g ^ 2 ^ k = 1 := by
  obtain ⟨m, hm3, hm1⟩ := exists_order_three_sl2 (F := F)
  intro h
  obtain ⟨k, hk⟩ := h m
  have h3 : orderOf m ∣ 3 := orderOf_dvd_of_pow_eq_one hm3
  have h2 : orderOf m ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 : orderOf m ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h3 h2
  rw [hcop] at h1
  exact hm1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))

omit [CharP F 2] in
theorem eq_bot_of_normal_of_fixed {K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hK : K.Normal) {w : Fin 2 → F} (hw : w ≠ 0) (hfix : ∀ k ∈ K, k • w = w) : K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  apply eq_one_of_forall_smul_vec
  intro u
  by_cases hu : u = 0
  · subst hu
    simp
  · obtain ⟨g1, hg1⟩ := exists_smul_e0 hw
    obtain ⟨g2, hg2⟩ := exists_smul_e0 hu
    set A : Matrix.SpecialLinearGroup (Fin 2) F := g2 * g1⁻¹ with hA
    have hAw : A • w = u := by rw [hA, mul_smul, ← hg1, inv_smul_smul, hg2]
    have hmem : A⁻¹ * k * A ∈ K := by
      have := hK.conj_mem k hk A⁻¹
      simpa using this
    have h2 := hfix _ hmem
    have h3 : k • (A • w) = A • w := by
      have e : A • ((A⁻¹ * k * A) • w) = k • (A • w) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        group
      rw [← e, h2]
    rw [hAw] at h3
    exact h3

theorem exists_natQuotSetting_of_sl2 [Finite H] [Finite F] {R M V : Subgroup H}
    (hsyl : IsSylowTwoOf R (⊤ : Subgroup H)) (hnn : ¬ R.Normal) (hRM : R ≤ M) (hMt : M < ⊤)
    (hMu : ∀ Y : Subgroup H, R ≤ Y → Y < ⊤ → Y ≤ M)
    (hVe : IsElemAbelian 2 V) (hVn : V.Normal)
    (α : H →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (hαk : α.ker = Subgroup.centralizer (V : Set H))
    (β : V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβe : ∀ (h : H) (v v' : V), (v' : H) = h * v * h⁻¹ →
      Multiplicative.toAdd (β v') =
        (α h : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.center H).subgroupOf V) :
    ∃ ρ : H →* Gamma F, (∀ h, ((ρ h : Gamma F) : Equiv.Perm (Fin 2 → F)) = slPerm F (α h)) ∧
      IsNatQuotSetting R M V ρ β := by
  classical
  let ρ : H →* Gamma F := (slGamma F).subtype.comp ((slGammaEquiv F).toMonoidHom.comp α)
  have hρ : ∀ h, ((ρ h : Gamma F) : Equiv.Perm (Fin 2 → F)) = slPerm F (α h) :=
    fun h => slGammaEquiv_apply (α h)
  have hρmem : ∀ h, ρ h ∈ slGamma F := fun h => ((slGammaEquiv F) (α h)).2
  have hρker : ∀ h, ρ h = 1 ↔ α h = 1 := by
    intro h
    constructor
    · intro hh
      have h1 : (slGammaEquiv F) (α h) = 1 := Subtype.ext hh
      exact (slGammaEquiv F).injective (by rw [h1, map_one])
    · intro hh
      simp [ρ, hh]
  have hρsurj : ∀ g : Gamma F, g ∈ slGamma F → ∃ h, ρ h = g := by
    intro g hg
    obtain ⟨A, hA⟩ := mem_slGamma_iff.mp hg
    obtain ⟨h, hh⟩ := hα A
    exact ⟨h, Subtype.ext (by rw [hρ h, hh, ← hA])⟩
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    refine top_le_iff.mp fun g _ => normalizer_le_normalizer_oddOrderSubgroup (⊤ : Subgroup H)
      (?_ : g ∈ Subgroup.normalizer ((⊤ : Subgroup H) : Set H))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp
  refine ⟨ρ, hρ, ?_⟩
  refine
    { sylow := hsyl, nonnormal := hnn, le_M := hRM, M_lt := hMt, M_max := hMu, reduced := ?_,
      sl_le := ?_, two_quot := ?_, φ_surj := hβ, φ_equiv := ?_, φ_ker := ?_ }
  · refine ⟨le_top, top_le_iff.mpr (Subgroup.normalizer_eq_top_iff.mpr hVn), hVe, ?_⟩
    intro D _ hDn hDpow
    have hDnorm : ∀ h : H, ∀ d ∈ D, h * d * h⁻¹ ∈ D := fun h d hd =>
      (Subgroup.mem_normalizer_iff.mp (hDn (Subgroup.mem_top h)) d).mp hd
    have hA : D.map ρ = ⊥ := by
      apply eq_bot_of_normal_isPGroup
      · intro a
        obtain ⟨d, hd, hda⟩ := a.2
        obtain ⟨k, hk⟩ := hDpow d hd
        refine ⟨k, Subtype.ext ?_⟩
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        have hk' : d ^ 2 ^ k ∈ α.ker := by rw [hαk]; exact hk
        rw [← hda, ← map_pow]
        exact (hρker _).mpr (MonoidHom.mem_ker.mp hk')
      · intro g hg a ha
        obtain ⟨h, rfl⟩ := hρsurj g hg
        obtain ⟨d, hd, rfl⟩ := ha
        exact ⟨h * d * h⁻¹, hDnorm h d hd, by simp⟩
    intro d hd
    have h1 : ρ d ∈ D.map ρ := ⟨d, hd, rfl⟩
    rw [hA, Subgroup.mem_bot] at h1
    rw [← hαk]
    exact (hρker d).mp h1
  · intro A
    obtain ⟨h, rfl⟩ := hα A
    exact ⟨h, hρ h⟩
  · intro h
    exact ⟨0, by simpa using hρmem h⟩
  · intro h v v' hv'
    rw [hρ h, slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
    exact hβe h v v' hv'
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hv l _
      have h1 : v ∈ β.ker := hv
      rw [hβk, Subgroup.mem_subgroupOf] at h1
      exact Subgroup.mem_center_iff.mp h1 l
    · intro hv
      have hfixL : ∀ l ∈ oddOrderSubgroup (⊤ : Subgroup H),
          α l • Multiplicative.toAdd (β v) = Multiplicative.toAdd (β v) := by
        intro l hl
        have hcomm := hv l hl
        have e : l * (v : H) * l⁻¹ = v := by
          rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        rw [Matrix.SpecialLinearGroup.smul_def]
        exact (hβe l v v e.symm).symm
      by_contra hne
      have hw0 : Multiplicative.toAdd (β v) ≠ 0 := by
        intro h0
        apply hne
        have : β v = Multiplicative.ofAdd (0 : Fin 2 → F) := by
          rw [← h0]; rfl
        rw [this]
        rfl
      have hKn : ((oddOrderSubgroup (⊤ : Subgroup H)).map α).Normal := hLn.map α hα
      have hKbot : (oddOrderSubgroup (⊤ : Subgroup H)).map α = ⊥ :=
        eq_bot_of_normal_of_fixed hKn hw0 (by
          rintro _ ⟨l, hl, rfl⟩
          exact hfixL l hl)
      refine not_forall_two_power_sl2 (F := F) fun g => ?_
      obtain ⟨h, rfl⟩ := hα g
      obtain ⟨j, hj⟩ := exists_pow_mem_oddOrderSubgroup (H := (⊤ : Subgroup H)) (h := h) trivial
      refine ⟨j, ?_⟩
      rw [← map_pow]
      have h2 : α (h ^ 2 ^ j) ∈ (oddOrderSubgroup (⊤ : Subgroup H)).map α := ⟨_, hj, rfl⟩
      rwa [hKbot, Subgroup.mem_bot] at h2

end CFSG.CGT.PushingUpLit.BHS
