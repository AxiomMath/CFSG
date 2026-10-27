module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneFamilies
import all CFSG.LieType.Universal.Unitary.Comparison
import all CFSG.LieType.Universal.Unitary.Roots
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneTorus

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.QuasithinUnique CFSG.AGLEmbedding.BlockCyc CFSG.LieType.BorelTits
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LieType.Universal.SpecialLinear
  CFSG.SectionRank.EvenCover Matrix
open scoped commutatorElement

section Kernel

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}

theorem mem_ker_su_iff (z : SU (unitaryInvolution F 2 1) n) :
    z ∈ ((QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSU n (2 ^ 1) F))).comp
      (equivStatedSU hF n).toMonoidHom).ker ↔
      ∃ u : Fˣ, mat (unitaryInvolution F 2 1) n z = Matrix.scalar (Fin n) (u : F) := by
  set P := (exists_wittMatrix hF n).choose with hP
  have hψ : ∀ z : SU (unitaryInvolution F 2 1) n,
      (((equivStatedSU hF n z : StatedSU n (2 ^ 1) F) : GL (Fin n) F)) =
        P * (z : GL (Fin n) F) * P⁻¹ := fun z => rfl
  have hcen : ∀ u : Fˣ, P * Matrix.GeneralLinearGroup.scalar (Fin n) u =
      Matrix.GeneralLinearGroup.scalar (Fin n) u * P := fun u => by
    have hc : Matrix.GeneralLinearGroup.scalar (Fin n) u ∈ Subgroup.center (GL (Fin n) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩
    exact Subgroup.mem_center_iff.1 hc P
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  show (((equivStatedSU hF n z : StatedSU n (2 ^ 1) F) : GL (Fin n) F)) ∈
    StatedScalars (Fin n) F ↔ _
  rw [hψ]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have hz : (z : GL (Fin n) F) = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
      calc (z : GL (Fin n) F) = P⁻¹ * (P * (z : GL (Fin n) F) * P⁻¹) * P := by group
        _ = P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin n) u * P := by rw [← hu]
        _ = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
          rw [mul_assoc, ← hcen u]; group
    rw [mat_apply, hz, Matrix.GeneralLinearGroup.coe_scalar]
  · rintro ⟨u, hu⟩
    have hz : (z : GL (Fin n) F) = Matrix.GeneralLinearGroup.scalar (Fin n) u :=
      Units.ext (by rw [← mat_apply, hu, Matrix.GeneralLinearGroup.coe_scalar])
    refine ⟨u, ?_⟩
    rw [hz, hcen u]
    group

end Kernel


section Tori

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}

include hF in
theorem exists_unit_orderOf_three : ∃ ω : Fˣ, orderOf ω = 3 := by
  have h3 : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, hF]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [h3])
  exact ⟨ω, hω⟩

include hF in
theorem exists_short_torus {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (c : Fˣ) :
    ∃ g ∈ levelTorus (unitaryInvolution F 2 1) k,
      mat (unitaryInvolution F 2 1) n g = diagonal (tFun (unitaryInvolution F 2 1) k (c : F)) := by
  refine ⟨_, shortTorus_mem_levelTorus (unitaryInvolution_involutive hF) hk c, ?_⟩
  rw [mat_apply, coe_shortTorus _ (unitaryInvolution_involutive hF) _ _ _ (lowIdx_ne_rev _ _)
    c.ne_zero]
  unfold tFun
  rw [dite_eq_left hk]

theorem tFun_short_of_not_supp {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (c : F) {s : Fin n}
    (hs : ¬ (s.val = k.val ∨ s.val = k.val + 1 ∨ s.val = n - 1 - k.val ∨
      s.val = n - 2 - k.val)) : tFun (unitaryInvolution F 2 1) k c s = 1 := by
  unfold tFun
  rw [dite_eq_left hk]
  exact shortTorusFun_of_not_levelSupp hk c hs

theorem tFun_short_self {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (c : F) :
    tFun (unitaryInvolution F 2 1) k c (lowIdx k) = c := by
  unfold tFun
  rw [dite_eq_left hk]
  exact shortTorusFun_left _ _ _

theorem tFun_short_succ {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (c : F) :
    tFun (unitaryInvolution F 2 1) k c (lowIdx (n := n) ⟨k.val + 1, hk⟩) = c⁻¹ := by
  unfold tFun
  rw [dite_eq_left hk]
  exact shortTorusFun_right (lowIdx_ne_succ hk) _

omit [Finite F] [CharP F 2] in
theorem diag_eq_scalar_apply {d : Fin n → F} {u : F}
    (h : diagonal d = Matrix.scalar (Fin n) u) (s : Fin n) : d s = u := by
  have := congrFun (congrFun h s) s
  simpa using this

end Tori

section E9

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}
  {Y : Type} [Group Y]

include hF in
theorem su_exists_E9_short_pair (hn : 7 ≤ n) {π : SU (unitaryInvolution F 2 1) n →* Y}
    {nn : Fin (rootDatum hF n).rank → SU (unitaryInvolution F 2 1) n}
    (h : BorelQuotient (rootDatum hF n) nn (levelTorus (unitaryInvolution F 2 1)) π 3)
    (hker : ∀ z ∈ π.ker, ∃ u : Fˣ,
      mat (unitaryInvolution F 2 1) n z = Matrix.scalar (Fin n) (u : F))
    (k₀ k₁ : Fin (n / 2)) (hk₀ : k₀.val = 0) (hk₁ : k₁.val = 1) :
    ∃ E : Subgroup Y, E ≤ (rankOne (rootDatum hF n).rootGroup k₀).map π ⊔
      (rankOne (rootDatum hF n).rootGroup k₁).map π ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨ω, hω⟩ := exists_unit_orderOf_three hF
  have hk₀' : k₀.val + 1 < n / 2 := by omega
  have hk₁' : k₁.val + 1 < n / 2 := by omega
  obtain ⟨t₀, ht₀, ht₀m⟩ := exists_short_torus hF hk₀' ω
  obtain ⟨t₁, ht₁, ht₁m⟩ := exists_short_torus hF hk₁' ω
  have h03 : t₀ ^ 3 = 1 := h.torus_pow k₀ t₀ ht₀
  have h13 : t₁ ^ 3 = 1 := h.torus_pow k₁ t₁ ht₁
  have hcomm : Commute t₀ t₁ := h.extras.torus_commute k₀ k₁ t₀ ht₀ t₁ ht₁
  have hω1 : ∀ i : ℕ, i < 3 → (ω : F) ^ i = 1 → i = 0 := fun i hi h' => by
    have h1 : ω ^ i = 1 := Units.ext (by simpa using h')
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hω] at this
    exact Nat.eq_zero_of_dvd_of_lt this hi
  have hindep : ∀ i j : ℕ, i < 3 → j < 3 → π t₀ ^ i * π t₁ ^ j = 1 → i = 0 ∧ j = 0 := by
    intro i j hi hj hij
    have hz : t₀ ^ i * t₁ ^ j ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_pow, map_pow]
      exact hij
    obtain ⟨u, hu⟩ := hker _ hz
    have hm : mat (unitaryInvolution F 2 1) n (t₀ ^ i * t₁ ^ j) =
        diagonal (fun s => tFun (unitaryInvolution F 2 1) k₀ (ω : F) s ^ i *
          tFun (unitaryInvolution F 2 1) k₁ (ω : F) s ^ j) := by
      rw [map_mul, map_pow, map_pow, ht₀m, ht₁m, diagonal_pow, diagonal_pow,
        diagonal_mul_diagonal]
      rfl
    rw [hm] at hu
    have hd := diag_eq_scalar_apply hu
    have hs3 := hd ⟨3, by omega⟩
    rw [tFun_short_of_not_supp hk₀' _ (by simp only [hk₀]; omega),
      tFun_short_of_not_supp hk₁' _ (by simp only [hk₁]; omega), one_pow, one_pow, mul_one] at hs3
    have hs0 := hd (lowIdx k₀)
    rw [tFun_short_self hk₀', tFun_short_of_not_supp hk₁' _ (by
      simp only [val_lowIdx, hk₀, hk₁]; omega), one_pow, mul_one, ← hs3] at hs0
    have hs2 := hd (lowIdx (n := n) ⟨k₁.val + 1, hk₁'⟩)
    rw [tFun_short_succ hk₁', tFun_short_of_not_supp hk₀' _ (by
      simp only [val_lowIdx, hk₀, hk₁]; omega), one_pow, one_mul, ← hs3] at hs2
    have hi0 : i = 0 := hω1 i hi hs0
    have hj0 : j = 0 := by
      refine hω1 j hj ?_
      have : ((ω : F)⁻¹) ^ j = 1 := hs2
      rw [inv_pow] at this
      exact inv_eq_one.1 this
    exact ⟨hi0, hj0⟩
  obtain ⟨E, hE, hel, hcard⟩ := exists_E9_le_of_two_elements (e₁ := π t₀) (e₂ := π t₁)
    (hcomm.map π) (by rw [← map_pow, h03, map_one])
    (by rw [← map_pow, h13, map_one]) hindep
  refine ⟨E, hE.trans (sup_le_sup ?_ ?_), hel, hcard⟩
  · exact (Subgroup.zpowers_le).2 ⟨t₀, h.ct.H_le k₀ ht₀, rfl⟩
  · exact (Subgroup.zpowers_le).2 ⟨t₁, h.ct.H_le k₁ ht₁, rfl⟩

include hF in
theorem su_exists_E9_short_last (hodd : ¬ Even n) {π : SU (unitaryInvolution F 2 1) n →* Y}
    {nn : Fin (rootDatum hF n).rank → SU (unitaryInvolution F 2 1) n}
    (h : BorelQuotient (rootDatum hF n) nn (levelTorus (unitaryInvolution F 2 1)) π 3)
    (hker : ∀ z ∈ π.ker, ∃ u : Fˣ,
      mat (unitaryInvolution F 2 1) n z = Matrix.scalar (Fin n) (u : F))
    (k₁ k₂ : Fin (n / 2)) (hk₁ : 1 ≤ k₁.val) (hk₂ : k₂.val = k₁.val + 1)
    (hlast : ¬ k₂.val + 1 < n / 2) :
    ∃ E : Subgroup Y, E ≤ (rankOne (rootDatum hF n).rootGroup k₁).map π ⊔
      (rankOne (rootDatum hF n).rootGroup k₂).map π ∧ CFSG.Open.IsElemAbelian 3 E ∧
        Nat.card E = 9 := by
  obtain ⟨ω, hω⟩ := exists_unit_orderOf_three hF
  have hlt := k₂.isLt
  have hk₁' : k₁.val + 1 < n / 2 := by omega
  have hnodd : n % 2 = 1 := by
    rwa [Nat.not_even_iff_odd, Nat.odd_iff] at hodd
  obtain ⟨t₁, ht₁, ht₁m⟩ := exists_short_torus hF hk₁' ω
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  obtain ⟨z, -, hzm⟩ := exists_heisGen_mem_rankOne (unitaryInvolution_involutive hF) hζ
    (fun _ hx => exists_norm_eq hF hx) (k := k₂) hlast hodd ω
  have hz : z ∈ levelTorus (unitaryInvolution F 2 1) k₂ :=
    heisGen_mem_levelTorus hlast hodd ω hzm
  have hzm' : mat (unitaryInvolution F 2 1) n z =
      diagonal (tFun (unitaryInvolution F 2 1) k₂ (ω : F)) := by
    rw [mat_apply, hzm]
    unfold tFun
    rw [dite_eq_right hlast, ite_eq_right hodd]
  have h13 : t₁ ^ 3 = 1 := h.torus_pow k₁ t₁ ht₁
  have h23 : z ^ 3 = 1 := h.torus_pow k₂ z hz
  have hcomm : Commute t₁ z := h.extras.torus_commute k₁ k₂ t₁ ht₁ z hz
  have hω1 : ∀ i : ℕ, i < 3 → (ω : F) ^ i = 1 → i = 0 := fun i hi h' => by
    have h1 : ω ^ i = 1 := Units.ext (by simpa using h')
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hω] at this
    exact Nat.eq_zero_of_dvd_of_lt this hi
  have hindep : ∀ i j : ℕ, i < 3 → j < 3 → π t₁ ^ i * π z ^ j = 1 → i = 0 ∧ j = 0 := by
    intro i j hi hj hij
    have hzk : t₁ ^ i * z ^ j ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_pow, map_pow]
      exact hij
    obtain ⟨u, hu⟩ := hker _ hzk
    have hm : mat (unitaryInvolution F 2 1) n (t₁ ^ i * z ^ j) =
        diagonal (fun s => tFun (unitaryInvolution F 2 1) k₁ (ω : F) s ^ i *
          tFun (unitaryInvolution F 2 1) k₂ (ω : F) s ^ j) := by
      rw [map_mul, map_pow, map_pow, ht₁m, hzm', diagonal_pow, diagonal_pow,
        diagonal_mul_diagonal]
      rfl
    rw [hm] at hu
    have hd := diag_eq_scalar_apply hu
    have hs0 := hd ⟨0, by omega⟩
    rw [tFun_short_of_not_supp hk₁' _ (by simp only; omega),
      tFun_of_last hlast (s := ⟨0, by omega⟩) (by
        intro e; have := congrArg Fin.val e; simp [lowIdx] at this; omega) (by
        intro e; have := congrArg Fin.val e; simp [lowIdx] at this; omega) (by
        intro e; have := congrArg Fin.val e; simp at this; omega),
      one_pow, one_pow, mul_one] at hs0
    have hs1 := hd (lowIdx k₁)
    rw [tFun_short_self hk₁', tFun_of_last hlast (s := lowIdx k₁) (by
        intro e; have := congrArg Fin.val e; simp [lowIdx] at this; omega) (by
        intro e; have := congrArg Fin.val e; simp [lowIdx] at this; omega) (by
        intro e; have := congrArg Fin.val e; simp [lowIdx] at this; omega),
      one_pow, mul_one, ← hs0] at hs1
    have hs2 := hd (lowIdx k₂)
    have hk₂eq : k₂ = ⟨k₁.val + 1, hk₁'⟩ := Fin.ext hk₂
    rw [show lowIdx k₂ = lowIdx (n := n) ⟨k₁.val + 1, hk₁'⟩ by rw [hk₂eq],
      tFun_short_succ hk₁', ← hk₂eq, tFun_lowIdx_of_last hlast, ← hs0] at hs2
    have hi0 : i = 0 := hω1 i hi hs1
    subst hi0
    have hj0 : j = 0 := by
      refine hω1 j hj ?_
      simpa using hs2
    exact ⟨rfl, hj0⟩
  obtain ⟨E, hE, hel, hcard⟩ := exists_E9_le_of_two_elements (e₁ := π t₁) (e₂ := π z)
    (hcomm.map π) (by rw [← map_pow, h13, map_one]) (by rw [← map_pow, h23, map_one]) hindep
  refine ⟨E, hE.trans (sup_le_sup ?_ ?_), hel, hcard⟩
  · exact (Subgroup.zpowers_le).2 ⟨t₁, h.ct.H_le k₁ ht₁, rfl⟩
  · exact (Subgroup.zpowers_le).2 ⟨z, h.ct.H_le k₂ hz, rfl⟩

end E9

section Six
variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2)
  {Y : Type} [Group Y]

include hF in
theorem su_exists_E9_six {π : SU (unitaryInvolution F 2 1) 6 →* Y}
    {nn : Fin (rootDatum hF 6).rank → SU (unitaryInvolution F 2 1) 6}
    (h : BorelQuotient (rootDatum hF 6) nn (levelTorus (unitaryInvolution F 2 1)) π 3)
    (hker : ∀ z, z ∈ π.ker ↔ ∃ u : Fˣ,
      mat (unitaryInvolution F 2 1) 6 z = Matrix.scalar (Fin 6) (u : F))
    (k₀ k₁ : Fin (6 / 2)) (hk₀ : k₀.val = 0) (hk₁ : k₁.val = 1) :
    ∃ E : Subgroup Y, E ≤ (rankOne (rootDatum hF 6).rootGroup k₀).map π ⊔
      (rankOne (rootDatum hF 6).rootGroup k₁).map π ∧ CFSG.Open.IsElemAbelian 3 E ∧
        Nat.card E = 9 := by
  obtain ⟨ω, hω⟩ := exists_unit_orderOf_three hF
  have hω3 : (ω : F) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ω
    rw [hω] at this
    simpa using congrArg Units.val this
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hk₀' : k₀.val + 1 < 6 / 2 := by omega
  have hk₁' : k₁.val + 1 < 6 / 2 := by omega
  have hk₀e : k₀ = ⟨0, by decide⟩ := Fin.ext hk₀
  have hk₁e : k₁ = ⟨1, by decide⟩ := Fin.ext hk₁
  obtain ⟨t, ht, htm⟩ := exists_short_torus hF hk₁' ω
  have hinv : (ω : F)⁻¹ = (ω : F) ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hω3)
  have hinv2 : ((ω : F) ^ 2)⁻¹ = (ω : F) :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hω3)
  have hf0 : ∀ s : Fin 6, tFun (unitaryInvolution F 2 1) k₁ (ω : F) s =
      ![1, (ω : F), (ω : F)⁻¹, (ω : F) ^ 2, ((ω : F) ^ 2)⁻¹, 1] s := by
    intro s
    subst hk₁e
    unfold tFun
    rw [dite_eq_left hk₁']
    fin_cases s <;> simp [shortTorusFun, lowIdx, unitaryInvolution_apply, frobenius_def, Fin.ext_iff]
  have hf : ∀ s : Fin 6, tFun (unitaryInvolution F 2 1) k₁ (ω : F) s =
      ![1, (ω : F), (ω : F) ^ 2, (ω : F) ^ 2, (ω : F), 1] s := by
    intro s
    rw [hf0 s]
    fin_cases s <;> simp [hinv, hinv2]
  set ρ : Equiv.Perm (Fin 6) := levelPerm k₀ * levelPerm k₁ with hρ
  have hρs : ∀ r, ρ.symm r = ![2, 0, 1, 4, 5, 3] r := by
    rw [hρ, hk₀e, hk₁e]
    decide +kernel
  have hρ3 : ρ ^ 3 = 1 := by
    rw [hρ, hk₀e, hk₁e]
    decide +kernel
  have hρ1 : ρ 0 ≠ 0 := by
    rw [hρ, hk₀e, hk₁e]
    decide +kernel
  have hρ2 : (ρ ^ 2) 0 ≠ 0 := by
    rw [hρ, hk₀e, hk₁e]
    decide +kernel
  have hsign : ∀ k : Fin (6 / 2), k.val + 1 < 6 / 2 →
      levelSign (unitaryInvolution F 2 1) (ζ : F) k = fun _ => 1 := by
    intro k hk
    funext s
    unfold levelSign
    rw [dif_pos hk]
    unfold shortSign
    split_ifs <;> simp [CharTwo.neg_eq]
  set P : SU (unitaryInvolution F 2 1) 6 := levelWeyl hσ ζ k₀ * levelWeyl hσ ζ k₁ with hP
  have hPm : ((P : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = signedPerm ρ (fun _ => 1) := by
    rw [hP, Subgroup.coe_mul, Units.val_mul, coe_levelWeyl hσ hζ, coe_levelWeyl hσ hζ,
      signedPerm_mul_signedPerm, hsign _ hk₀', hsign _ hk₁']
    simp [hρ]
  have hPm' : mat (unitaryInvolution F 2 1) 6 P = signedPerm ρ (fun _ => 1) := by
    rw [mat_apply]; exact hPm
  have hconj : mat (unitaryInvolution F 2 1) 6 (P * t * P⁻¹) =
      diagonal fun r => tFun (unitaryInvolution F 2 1) k₁ (ω : F) (ρ.symm r) := by
    rw [mat_apply]
    exact coe_conj_diagonal hPm (by rw [← mat_apply]; exact htm)
  have hti : mat (unitaryInvolution F 2 1) 6 t⁻¹ =
      diagonal fun s => (tFun (unitaryInvolution F 2 1) k₁ (ω : F) s)⁻¹ :=
    diagonal_inv_eq (tFun_ne_zero k₁ ω.ne_zero) htm
  have hz : mat (unitaryInvolution F 2 1) 6 (P * t * P⁻¹ * t⁻¹) =
      Matrix.scalar (Fin 6) (((ω ^ 2 : Fˣ)) : F) := by
    rw [map_mul, hconj, hti, diagonal_mul_diagonal, Matrix.scalar_apply]
    congr 1
    funext r
    simp only [hρs, hf]
    fin_cases r <;> simp [hinv, hinv2, pow_two] <;> linear_combination (ω : F) * hω3
  have hzk : P * t * P⁻¹ * t⁻¹ ∈ π.ker := (hker _).2 ⟨_, hz⟩
  have hcomm : Commute (π t) (π P) := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hzk
    exact ((commutatorElement_eq_one_iff_commute).1 hzk).symm
  have hP3 : P ^ 3 = 1 := by
    apply mat_injective
    rw [map_pow, map_one, hPm', pow_succ, pow_two, signedPerm_mul_signedPerm,
      signedPerm_mul_signedPerm]
    have : ρ * ρ * ρ = 1 := by
      have := hρ3
      rwa [pow_succ, pow_two] at this
    rw [this, signedPerm_one]
    simp
  have hnz : ∀ s, tFun (unitaryInvolution F 2 1) k₁ (ω : F) s ≠ 0 := tFun_ne_zero k₁ ω.ne_zero
  have key : ∀ (π' : Equiv.Perm (Fin 6)) (ε d : Fin 6 → F) (u : F), (∀ s, d s ≠ 0) →
      (∀ s, ε s ≠ 0) → π' 0 ≠ 0 → diagonal d * signedPerm π' ε ≠ Matrix.scalar (Fin 6) u := by
    intro π' ε d u hd hε h0 heq
    have := congrFun (congrFun heq (π' 0)) 0
    simp [signedPerm_apply, Matrix.diagonal_mul, Matrix.scalar_apply, Matrix.diagonal_apply,
      h0] at this
    exact hd _ (this.resolve_right (hε 0))
  have hω1 : ∀ i : ℕ, i < 3 → (ω : F) ^ i = 1 → i = 0 := fun i hi h' => by
    have h1 : ω ^ i = 1 := Units.ext (by simpa using h')
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hω] at this
    exact Nat.eq_zero_of_dvd_of_lt this hi
  have hindep : ∀ i j : ℕ, i < 3 → j < 3 → π t ^ i * π P ^ j = 1 → i = 0 ∧ j = 0 := by
    intro i j hi hj hij
    have hzk : t ^ i * P ^ j ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_pow, map_pow]
      exact hij
    obtain ⟨u, hu⟩ := (hker _).1 hzk
    have hti' : mat (unitaryInvolution F 2 1) 6 (t ^ i) =
        diagonal (fun s => tFun (unitaryInvolution F 2 1) k₁ (ω : F) s ^ i) := by
      rw [map_pow, htm, diagonal_pow]
      rfl
    rw [map_mul, hti'] at hu
    interval_cases j
    · simp only [pow_zero, map_one, Matrix.mul_one] at hu
      have hd := diag_eq_scalar_apply hu
      have h0 : (1 : F) = u := by
        have := hd ⟨0, by omega⟩
        rw [hf] at this
        simpa using this
      have h1 : (ω : F) ^ i = u := by
        have := hd ⟨1, by omega⟩
        rw [hf] at this
        simpa using this
      exact ⟨hω1 i hi (h1.trans h0.symm), rfl⟩
    · exfalso
      rw [pow_one, hPm'] at hu
      exact key ρ _ _ u (fun s => pow_ne_zero _ (hnz s)) (fun _ => one_ne_zero) hρ1 hu
    · exfalso
      rw [pow_two, map_mul, hPm', signedPerm_mul_signedPerm] at hu
      refine key (ρ * ρ) _ _ u (fun s => pow_ne_zero _ (hnz s)) (fun _ => by simp) ?_ hu
      rw [← pow_two]
      exact hρ2
  obtain ⟨E, hE, hel, hcard⟩ := exists_E9_le_of_two_elements (e₁ := π t) (e₂ := π P) hcomm
    (by rw [← map_pow, h.torus_pow k₁ t ht, map_one]) (by rw [← map_pow, hP3, map_one]) hindep
  refine ⟨E, hE.trans (sup_le ?_ ?_), hel, hcard⟩
  · refine le_trans ?_ le_sup_right
    exact (Subgroup.zpowers_le).2 ⟨t, h.ct.H_le k₁ ht, rfl⟩
  · have hPL : P ∈ rankOne (rootDatum hF 6).rootGroup k₀ ⊔ rankOne (rootDatum hF 6).rootGroup k₁ :=
      mul_mem (Subgroup.mem_sup_left (levelWeyl_mem_rankOne hσ ζ k₀))
        (Subgroup.mem_sup_right (levelWeyl_mem_rankOne hσ ζ k₁))
    exact (Subgroup.zpowers_le).2 (by rw [← Subgroup.map_sup]; exact ⟨P, hPL, rfl⟩)

end Six

section ShortPkg

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}

include hF in
theorem hasTorusSL2_su_short {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) :
    HasTorusSL2 (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) k F := by
  have hσ := unitaryInvolution_involutive hF
  set e := rankOneShortEquiv (hσ := hσ) hk with he
  set p : Fin n := lowIdx k with hpdef
  set q : Fin n := lowIdx ⟨k.val + 1, hk⟩ with hqdef
  have hpq : p ≠ q := lowIdx_ne_succ hk
  have hp : p ≠ Fin.rev p := lowIdx_ne_rev k k
  have hq : q ≠ Fin.rev q := lowIdx_ne_rev _ _
  have hqp : q ≠ Fin.rev p := lowIdx_ne_rev _ _
  have hpq' : p ≠ Fin.rev q := lowIdx_ne_rev _ _
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hn2 : 2 ≤ n := by have := k.isLt; omega
  have hct := isCTGroupDatum hF n hn2 ζ hζ
  have h4 : 4 ≤ Nat.card F := by rw [hF]; norm_num
  obtain ⟨c, hc0, hc2⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card F h4
  set τ : SU (unitaryInvolution F 2 1) n :=
    shortTorus (unitaryInvolution F 2 1) hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k)
      (lowIdx_ne_rev _ _) c with hτ
  have hτT : τ ∈ levelTorus (unitaryInvolution F 2 1) k :=
    shortTorus_mem_levelTorus hσ hk (Units.mk0 c hc0)
  have hτL : τ ∈ rankOne (rootGroup (unitaryInvolution F 2 1) hσ n) k := hct.H_le k hτT
  have hτm : mat (unitaryInvolution F 2 1) n τ =
      diagonal (shortTorusFun (unitaryInvolution F 2 1) p q c) := by
    rw [mat_apply, hτ, coe_shortTorus _ hσ _ _ _ (lowIdx_ne_rev _ _) hc0]
  have hed : e ⟨τ, hτL⟩ = (sl2Rels F).h c := by
    apply Subtype.ext
    change ((rankOneShortHom hk ⟨τ, hτL⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = _
    rw [coe_rankOneShortHom, coe_sl2Rels_h hc0]
    change SUExtras.toBlock p q (mat (unitaryInvolution F 2 1) n τ) = _
    rw [hτm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SUExtras.toBlock, diagonal_apply, shortTorusFun_left, shortTorusFun_right hpq, hpq, hpq.symm]
  have hnc : (sl2Rels F).h c * sl2Upper 1 ≠ sl2Upper 1 * (sl2Rels F).h c := by
    intro hc
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 1) hc
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Rels_h hc0, coe_sl2Upper, Matrix.mul_apply,
      Fin.sum_univ_two] at this
    apply hc2
    field_simp at this
    linear_combination this
  refine ⟨(Subgroup.subtype _).comp e.symm.toMonoidHom,
    Subtype.val_injective.comp e.symm.injective, fun a => ?_, fun a => ?_, ?_,
    (sl2Rels F).h c, sl2Upper 1, hnc, ?_⟩
  · have hx := rootHom_mem hσ hpq hp hq hqp (toStd_short hk).symm (Multiplicative.ofAdd a)
    have key : e ⟨_, Subgroup.mem_sup_left hx⟩ = sl2Upper a := by
      apply Subtype.ext
      change ((rankOneShortHom hk ⟨_, Subgroup.mem_sup_left hx⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
      rw [coe_rankOneShortHom, toBlock_of_mem_pos hk hx, mat_apply, coe_rootHom, toAdd_ofAdd,
        rootMatrix_apply_pq hpq hqp, coe_sl2Upper]
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_eq.2 key.symm,
      Subgroup.coe_subtype]
    exact hx
  · have hy := rootHom_mem hσ hpq.symm hq hp hpq' (toStd_short_neg hk).symm
      (Multiplicative.ofAdd a)
    have key : e ⟨_, Subgroup.mem_sup_right hy⟩ = sl2Lower a := by
      apply Subtype.ext
      change ((rankOneShortHom hk ⟨_, Subgroup.mem_sup_right hy⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
      rw [coe_rankOneShortHom, toBlock_of_mem_neg hk hy, mat_apply, coe_rootHom, toAdd_ofAdd,
        rootMatrix_apply_pq hpq.symm hpq', coe_sl2Lower]
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_eq.2 key.symm,
      Subgroup.coe_subtype]
    exact hy
  · intro g hg
    exact ⟨e ⟨g, hg⟩, by simp⟩
  · have : e.symm ((sl2Rels F).h c) = ⟨τ, hτL⟩ := e.symm_apply_eq.2 hed.symm
    show ((Subgroup.subtype _).comp e.symm.toMonoidHom) ((sl2Rels F).h c) ∈ _
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this]
    exact hτT

end ShortPkg

section Final

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}

omit [Finite F] [CharP F 2] in
theorem su_cartan_far {p f : ℕ} [Fact p.Prime] [CharP F p] [Finite F]
    (hF' : Nat.card F = (p ^ f) ^ 2) {i j : Fin (n / 2)}
    (h : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) : (rootDatum hF' n).cartan i j = 0 := by
  show cartan n i j = 0
  unfold cartan
  have hv : i.val ≠ j.val := by omega
  split_ifs
  · simp [Symplectic.cartanC, Fin.ext_iff, hv]
    omega
  · simp [Symplectic.cartanC, Fin.ext_iff, hv, Ne.symm hv]
    omega

end Final

section Master

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}
  {Y : Type} [Group Y] [Finite Y]

include hF in
theorem su_false_of_cover (hn : 6 ≤ n) {π : SU (unitaryInvolution F 2 1) n →* Y}
    {nn : Fin (rootDatum hF n).rank → SU (unitaryInvolution F 2 1) n}
    (h : BorelQuotient (rootDatum hF n) nn (levelTorus (unitaryInvolution F 2 1)) π 3)
    (hker : ∀ z, z ∈ π.ker ↔ ∃ u : Fˣ,
      mat (unitaryInvolution F 2 1) n z = Matrix.scalar (Fin n) (u : F))
    {C₁ C₂ : Subgroup Y} (hC₁ : SolvFree C₁) (hC₂ : SolvFree C₂)
    (hcov : ∀ i : Fin (n / 2),
      (rankOne (rootDatum hF n).rootGroup i).map π ≤ C₁ ∨
        (rankOne (rootDatum hF n).rootGroup i).map π ≤ C₂) : False := by
  classical
  have h4 : 4 ≤ Nat.card F := by rw [hF]; norm_num
  have hker' : ∀ z ∈ π.ker, ∃ u : Fˣ,
      mat (unitaryInvolution F 2 1) n z = Matrix.scalar (Fin n) (u : F) := fun z hz =>
    (hker z).1 hz
  let col : Fin (n / 2) → Bool := fun i =>
    decide ((rankOne (rootDatum hF n).rootGroup i).map π ≤ C₁)
  have hsame : ∀ i j, col i = col j → ∃ C : Subgroup Y, SolvFree C ∧
      (rankOne (rootDatum hF n).rootGroup i).map π ≤ C ∧
        (rankOne (rootDatum hF n).rootGroup j).map π ≤ C := by
    intro i j hij
    by_cases hi : (rankOne (rootDatum hF n).rootGroup i).map π ≤ C₁
    · have hj : (rankOne (rootDatum hF n).rootGroup j).map π ≤ C₁ := by
        by_contra hj
        simp only [col, hi, hj, decide_true, decide_false] at hij
        exact absurd hij (by decide)
      exact ⟨C₁, hC₁, hi, hj⟩
    · have hj : ¬ (rankOne (rootDatum hF n).rootGroup j).map π ≤ C₁ := by
        intro hj
        simp only [col, hi, hj, decide_true, decide_false] at hij
        exact absurd hij (by decide)
      exact ⟨C₂, hC₂, (hcov i).resolve_left hi, (hcov j).resolve_left hj⟩
  have hnode : ∀ k : Fin (n / 2), k.val + 1 < n / 2 → HasSL2Node (rootDatum hF n) k F :=
    fun k hk => hasSL2Node_su_short hF hk
  have orth : ∀ s t : Fin (n / 2), s.val + 1 < n / 2 → s.val + 2 ≤ t.val → col s ≠ col t := by
    intro s t hs hst hcol
    obtain ⟨C, hC, h1, h2⟩ := hsame s t hcol
    exact false_short_orth h h4 (hnode s hs) (hasOrderThree_su hF t)
      (fun e => by rw [e] at hst; omega) (su_cartan_far hF (Or.inr hst)) hC h1 h2
  have tri : ∀ a b c : Bool, a = b ∨ a = c ∨ b = c := by decide
  by_cases h10 : 10 ≤ n
  · have a02 := orth ⟨0, by omega⟩ ⟨2, by omega⟩ (by simp; omega) (by simp)
    have a24 := orth ⟨2, by omega⟩ ⟨4, by omega⟩ (by simp; omega) (by simp)
    have a04 := orth ⟨0, by omega⟩ ⟨4, by omega⟩ (by simp; omega) (by simp)
    rcases tri (col ⟨0, by omega⟩) (col ⟨2, by omega⟩) (col ⟨4, by omega⟩) with e | e | e
    · exact a02 e
    · exact a04 e
    · exact a24 e
  · have hn' : n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
    have hE : ∀ {s t : Fin (n / 2)} {E : Subgroup Y}, s.val + 1 < n / 2 →
        E ≤ (rankOne (rootDatum hF n).rootGroup s).map π ⊔
          (rankOne (rootDatum hF n).rootGroup t).map π →
        CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 → col s ≠ col t := by
      intro s t E hs hE hel hcard hcol
      obtain ⟨C, hC, h1, h2⟩ := hsame s t hcol
      exact false_of_E9_short h h4 (hnode s hs) hC h1 (hE.trans (sup_le h1 h2)) hel hcard
    have hlong : Even n → ∀ s t : Fin (n / 2), s.val + 1 < n / 2 → ¬ t.val + 1 < n / 2 →
        col s ≠ col t := by
      intro heven s t hs ht hcol
      obtain ⟨C, hC, h1, h2⟩ := hsame s t hcol
      have h6c : Nat.card (rankOne (rootDatum hF n).rootGroup t) = 6 :=
        su_last_even_card hF heven ht
      exact false_short_long h h4 (hasTorusSL2_su_short hF hs) (hasOrderThree_su hF t)
        ⟨h6c, noncomm_of_card_six_of_hasOrderThree h h6c (hasOrderThree_su hF t)⟩ hC h1 h2
    rcases hn' with rfl | rfl | rfl | rfl
    ·
      obtain ⟨E, hEs, hel, hcard⟩ := su_exists_E9_six hF h hker (⟨0, by decide⟩ : Fin (6 / 2))
        ⟨1, by decide⟩ rfl rfl
      have a01 := hE (s := ⟨0, by decide⟩) (t := ⟨1, by decide⟩) (by decide) hEs hel hcard
      have a02 := orth ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide)
      have a12 := hlong (by decide) ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide)
      rcases tri (col ⟨0, by decide⟩) (col ⟨1, by decide⟩) (col ⟨2, by decide⟩) with e | e | e
      · exact a01 e
      · exact a02 e
      · exact a12 e
    ·
      obtain ⟨E, hEs, hel, hcard⟩ := su_exists_E9_short_pair hF (by decide) h hker'
        (⟨0, by decide⟩ : Fin (7 / 2)) ⟨1, by decide⟩ rfl rfl
      have a01 := hE (s := ⟨0, by decide⟩) (t := ⟨1, by decide⟩) (by decide) hEs hel hcard
      have a02 := orth ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide)
      obtain ⟨E', hEs', hel', hcard'⟩ := su_exists_E9_short_last hF (by decide) h hker'
        (⟨1, by decide⟩ : Fin (7 / 2)) ⟨2, by decide⟩ (by decide) rfl (by decide)
      have a12 := hE (s := ⟨1, by decide⟩) (t := ⟨2, by decide⟩) (by decide) hEs' hel' hcard'
      rcases tri (col ⟨0, by decide⟩) (col ⟨1, by decide⟩) (col ⟨2, by decide⟩) with e | e | e
      · exact a01 e
      · exact a02 e
      · exact a12 e
    ·
      have a02 := orth ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide)
      have a03 := orth ⟨0, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide)
      have a23 := hlong (by decide) ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide)
      rcases tri (col ⟨0, by decide⟩) (col ⟨2, by decide⟩) (col ⟨3, by decide⟩) with e | e | e
      · exact a02 e
      · exact a03 e
      · exact a23 e
    ·
      have a02 := orth ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide)
      have a03 := orth ⟨0, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide)
      obtain ⟨E', hEs', hel', hcard'⟩ := su_exists_E9_short_last hF (by decide) h hker'
        (⟨2, by decide⟩ : Fin (9 / 2)) ⟨3, by decide⟩ (by decide) rfl (by decide)
      have a23 := hE (s := ⟨2, by decide⟩) (t := ⟨3, by decide⟩) (by decide) hEs' hel' hcard'
      rcases tri (col ⟨0, by decide⟩) (col ⟨2, by decide⟩) (col ⟨3, by decide⟩) with e | e | e
      · exact a02 e
      · exact a03 e
      · exact a23 e

end Master

section CoverKer

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {nn : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem CoverCtxOne.cover_ker (ctx : CoverCtxOne L S₀ A₁ A₂)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D nn H π M) :
    ∃ π' : K →* ↥L ⧸ Subgroup.center ↥L, BorelQuotient D nn H π' M ∧ π'.ker = π.ker ∧
      ∀ i, (rankOne D.rootGroup i).map π' ≤
          (A₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ∨
        (rankOne D.rootGroup i).map π' ≤
          (A₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSS⟩ := Lie.exists_sylow_of_isSylowTwoOf ctx.syl
  set q : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  set T : Sylow 2 (↥L ⧸ Subgroup.center ↥L) := S.mapSurjective hqs with hT
  have hTc : (T : Subgroup (↥L ⧸ Subgroup.center ↥L)) = (S : Subgroup ↥L).map q := by
    rw [hT, Sylow.coe_mapSurjective]
  obtain ⟨π', hπ', hker, hTπ⟩ := h.exists_conj_eq T
  have hBQ : BorelQuotient D nn H π' M :=
    ⟨h.ct, h.extras, h.pGroup, hπ', h.odd, h.torus_pow,
      fun z hz => h.ker_central z (hker ▸ hz), fun z hz => h.ker_pow z (hker ▸ hz)⟩
  have hT' : (S₀.subgroupOf L).map q = (posUnipotent D).map π' := by
    rw [← hTπ, hTc, hSS]
  exact ⟨π', hBQ, hker, fun i => cover_of_borelQuotient ctx.syl ctx.cov hBQ hT' i⟩

end CoverKer

section FalseSU

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {F : Type} [Field F] [Finite F]
  [CharP F 2]

theorem CoverCtxOne.false_su_six (ctx : CoverCtxOne L S₀ A₁ A₂) {n : ℕ}
    (hF : Nat.card F = (2 ^ 1) ^ 2) (hn : 6 ≤ n)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n (2 ^ 1) F)) : False := by
  have : Finite (SU (unitaryInvolution F 2 1) n) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hq := borelQuotient_su hF (by omega : 2 ≤ n) ζ hζ e
  have hM : Nat.card F - 1 = 3 := by rw [hF]; norm_num
  rw [hM] at hq
  obtain ⟨π', h', hker, hcov⟩ := ctx.cover_ker hq
  refine su_false_of_cover hF hn h' (fun z => ?_) ctx.solv₁ ctx.solv₂ hcov
  rw [hker, ← mem_ker_su_iff hF z]
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  exact MulEquiv.map_eq_one_iff e.symm

end FalseSU

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
