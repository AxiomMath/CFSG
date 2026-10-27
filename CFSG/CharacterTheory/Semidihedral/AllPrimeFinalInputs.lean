module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeSetting
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalInputs
import CFSG.CharacterTheory.Semidihedral.AllPrimeTIFacts.Frontier
public import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI

public section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.MatrixCoverData CFSG.Semidihedral.MatrixTorus
open CFSG.Semidihedral.AllPrime.QDTI CFSG.Wreathed.OriginalAllPrime.TIFacts
open CFSG.ABGTheoremB CFSG.ABGTheoremB.TotallyInverted

section Matrix

variable {F : Type} [Field F]

private theorem comm_rootMat_entries {l : F} {g : Matrix (Fin 2) (Fin 2) F}
    (h : g * (rootMat l 1).1 = (rootMat l 1).1 * g) :
    g 0 1 = -(l ^ 2 * g 1 0) ∧ g 0 0 = g 1 1 + 2 * l * g 1 0 := by
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, rootMat_val] at h00 h10
  exact ⟨by linear_combination -h00, by linear_combination h10⟩

private theorem det_eq_sq_of_comm_rootMat {l : F} {g : Matrix (Fin 2) (Fin 2) F}
    (h : g * (rootMat l 1).1 = (rootMat l 1).1 * g) :
    g.det = (g 1 1 + l * g 1 0) ^ 2 := by
  obtain ⟨h01, h00⟩ := comm_rootMat_entries h
  rw [Matrix.det_fin_two, h01, h00]
  ring

private theorem minusIdentity_mul_val (X : SL F) :
    (OddFieldSL2.minusIdentity F * X).1 = -X.1 := by
  change (OddFieldSL2.minusIdentity F).1 * X.1 = -X.1
  rw [show (OddFieldSL2.minusIdentity F).1 = Matrix.scalar (Fin 2) (-1) from
    OddFieldSL2.minusIdentity_matrix F, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  simp

private theorem mem_rootGroup_of_comm {l : F} {X : SL F}
    (h : X * rootMat l 1 = rootMat l 1 * X) :
    X ∈ rootGroup l ∨ OddFieldSL2.minusIdentity F * X ∈ rootGroup l := by
  have hm : X.1 * (rootMat l 1).1 = (rootMat l 1).1 * X.1 := congrArg Subtype.val h
  obtain ⟨h01, h00⟩ := comm_rootMat_entries hm
  have hdet := sl_det X
  have hsq : (X.1 1 1 + l * X.1 1 0 - 1) * (X.1 1 1 + l * X.1 1 0 + 1) = 0 := by
    rw [h01, h00] at hdet
    linear_combination hdet
  rcases mul_eq_zero.mp hsq with hlam | hlam
  · left
    rw [mem_rootGroup_iff, h01, h00]
    constructor
    · linear_combination l * hlam
    · linear_combination hlam
  · right
    rw [mem_rootGroup_iff, minusIdentity_mul_val]
    simp only [Matrix.neg_apply]
    rw [h01, h00]
    constructor
    · linear_combination -(l * hlam)
    · linear_combination -hlam

private theorem eq_one_of_mem_rootGroup {p : ℕ} [CharP F p] (hp : p.Prime) (hp2 : p ≠ 2)
    {l : F} {X : SL F} (hX : X ∈ rootGroup l) {k : ℕ} (hk : X ^ 2 ^ k = 1) : X = 1 := by
  have h1 : orderOf X ∣ p := orderOf_dvd_of_pow_eq_one (rootGroup_pow_char p hX)
  have h2 : orderOf X ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf X) (2 ^ k) :=
    ((hp.odd_of_ne_two hp2).of_dvd_nat h1).coprime_two_right.pow_right k
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd h2)

private theorem eq_one_or_neg_of_comm {p : ℕ} [CharP F p] (hp : p.Prime) (hp2 : p ≠ 2)
    {l : F} {X : SL F} (h : X * rootMat l 1 = rootMat l 1 * X) {k : ℕ} (hk : X ^ 2 ^ k = 1) :
    X = 1 ∨ X = OddFieldSL2.minusIdentity F := by
  rcases mem_rootGroup_of_comm h with hX | hX
  · exact Or.inl (eq_one_of_mem_rootGroup hp hp2 hX hk)
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · left
      simpa using hk
    · right
      have hc : Commute (OddFieldSL2.minusIdentity F) X :=
        (Subgroup.mem_center_iff.mp (OddFieldSL2.minusIdentity_mem_center F) X).symm
      have hz : (OddFieldSL2.minusIdentity F) ^ 2 ^ k = 1 := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk0
        rw [pow_succ', pow_mul, OddFieldSL2.minusIdentity_square, one_pow]
      have hk' : (OddFieldSL2.minusIdentity F * X) ^ 2 ^ k = 1 := by
        rw [hc.mul_pow, hz, hk, one_mul]
      have h1 := eq_one_of_mem_rootGroup hp hp2 hX hk'
      have hinv : (OddFieldSL2.minusIdentity F)⁻¹ = OddFieldSL2.minusIdentity F :=
        inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact OddFieldSL2.minusIdentity_square F)
      calc X = (OddFieldSL2.minusIdentity F)⁻¹ * (OddFieldSL2.minusIdentity F * X) := by group
        _ = OddFieldSL2.minusIdentity F := by rw [h1, mul_one, hinv]

private theorem torus_not_comm_rootMat {a : Fˣ} (h2 : (2 : F) ≠ 0) {l : F} (hl0 : l ≠ 0)
    {w : SL F} (hw : w ∈ Torus F a) (hw0 : w.1 1 0 ≠ 0) :
    w * rootMat l 1 ≠ rootMat l 1 * w := by
  intro h
  obtain ⟨-, h00⟩ := comm_rootMat_entries (congrArg Subtype.val h)
  obtain ⟨-, h11⟩ := (mem_torus_iff F a w).mp hw
  have h' : (2 * l) * w.1 1 0 = 0 := by linear_combination -h00 - h11
  exact hw0 ((mul_eq_zero.mp h').resolve_left (mul_ne_zero h2 hl0))

end Matrix

section Model

variable {F : Type} [Field F] {a : Fˣ} {A : Subgroup (F ≃+* F)}
  {hfix : ∀ τ : A, (τ : F ≃+* F) (a : F) = a}

private theorem model_eq_one_or_z {p : ℕ} [CharP F p] (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) (l : F) {m : OriginalH F a A hfix} {k : ℕ}
    (hk : m ^ 2 ^ k = 1)
    (hc : m * originalSlInH F a A hfix (rootMat l 1) =
      originalSlInH F a A hfix (rootMat l 1) * m) :
    m = 1 ∨ m = originalZ F a A hfix := by
  have hr : m.right = 1 := by
    have h1 : m.right ^ 2 ^ k = 1 := by
      have := congrArg SemidirectProduct.rightHom hk
      rwa [map_pow, map_one] at this
    have h2 : orderOf m.right ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have h3 : Odd (orderOf m.right) := hA.of_dvd_nat (orderOf_dvd_natCard _)
    exact orderOf_eq_one_iff.mp ((h3.coprime_two_right.pow_right k).eq_one_of_dvd h2)
  have hm := decomp m
  rw [hr, map_one, mul_one] at hm
  set X := m.left.left with hX
  rcases C2_cases m.left.right with he | he
  · rw [he, map_one, map_one, mul_one] at hm
    rw [hm, ← map_mul, ← map_mul] at hc
    rw [hm, ← map_pow] at hk
    have hk' : X ^ 2 ^ k = 1 := slIn_injective (hk.trans (map_one _).symm)
    rcases eq_one_or_neg_of_comm hp hp2 (slIn_injective hc) hk' with h | h
    · left
      rw [hm, h, map_one]
    · right
      rw [hm, h, originalZ_eq]
  · exfalso
    have hu : (SemidirectProduct.inl (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) :
        OriginalH F a A hfix) = originalU F a A hfix := rfl
    rw [he, hu] at hm
    rw [hm] at hc
    have h1 : originalSlInH F a A hfix (X * beta F a (rootMat l 1)) =
        originalSlInH F a A hfix (rootMat l 1 * X) := by
      rw [map_mul, map_mul, ← conj_u_slIn]
      calc originalSlInH F a A hfix X * (originalU F a A hfix *
            originalSlInH F a A hfix (rootMat l 1) * (originalU F a A hfix)⁻¹) =
          originalSlInH F a A hfix X * originalU F a A hfix *
            originalSlInH F a A hfix (rootMat l 1) * (originalU F a A hfix)⁻¹ := by group
        _ = originalSlInH F a A hfix (rootMat l 1) * originalSlInH F a A hfix X := by
          rw [hc, mul_assoc (originalSlInH F a A hfix (rootMat l 1)), mul_inv_cancel_right]
    have hmat : X.1 * (beta F a (rootMat l 1)).1 = (rootMat l 1).1 * X.1 :=
      congrArg Subtype.val (slIn_injective h1)
    have hb := (beta_eq_iff a (rootMat l 1) (beta F a (rootMat l 1))).mp rfl
    have hg : (X.1 * (J F a : Matrix (Fin 2) (Fin 2) F)) * (rootMat l 1).1 =
        (rootMat l 1).1 * (X.1 * (J F a : Matrix (Fin 2) (Fin 2) F)) := by
      rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, hmat, Matrix.mul_assoc]
    have hdet := det_eq_sq_of_comm_rootMat hg
    rw [Matrix.det_mul, X.2, one_mul, J_val, Matrix.det_fin_two_of] at hdet
    apply ha
    rw [SemilinearOuterQuotient.isSquare_unit_iff]
    exact ⟨_, by rw [← pow_two, ← hdet]; ring⟩

end Model

section Transport

variable {G : Type} [Group G] [Finite G] {σ : Setting G}
  {F : Type} [Field F] [Finite F] {a : Fˣ} {A : Subgroup (F ≃+* F)}
  {hfix : ∀ τ : A, (τ : F ≃+* F) (a : F) = a} {φ : σ.N →* OriginalH F a A hfix}

private theorem exists_root_of_signalizer
    (hφ : IsModelMap σ φ (layerM F a A hfix) (originalU F a A hfix)) {J : Subgroup G}
    (hJ : σ.IsLayerComplement J) (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (hq7 : 7 ≤ Nat.card F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {b : F}
    (hb : b ^ 2 = -(a : F)) {P : Subgroup G} (hP : P ∈ signalizers J σ.C p)
    (hcard : Nat.card P = Nat.card F) :
    ∃ l : F, l ^ 2 = -(a : F) ∧ (P.subgroupOf σ.N).map φ = rootM F a A hfix l := by
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  have hc : Nat.card ((P.subgroupOf σ.N).map φ) = Nat.card F :=
    (hφ.card_map hJ hP.1).trans hcard
  rcases signalizer_le_rootM_or hodd ha hq7 hp hp2 hb (hφ.map_mem_signalizers hJ hP) with h | h
  · exact ⟨b, hb, Subgroup.eq_of_le_of_card_ge h (by rw [card_rootM, hc])⟩
  · exact ⟨-b, by rw [neg_sq]; exact hb, Subgroup.eq_of_le_of_card_ge h (by rw [card_rootM, hc])⟩

omit [Finite F] in
private theorem isCyclic_of_le_centralizer
    (hφ : IsModelMap σ φ (layerM F a A hfix) (originalU F a A hfix)) {p : ℕ} [CharP F p]
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) {l : F}
    {P : Subgroup G} (hPl : (P.subgroupOf σ.N).map φ = rootM F a A hfix l) {Y : Subgroup G}
    (hYN : Y ≤ σ.N) (hY : IsPGroup 2 Y) (hYP : Y ≤ Subgroup.centralizer (P : Set G)) :
    IsCyclic Y := by
  have hR : originalSlInH F a A hfix (rootMat l 1) ∈ (P.subgroupOf σ.N).map φ := by
    rw [hPl]
    exact ⟨_, rootHom_mem l (Multiplicative.ofAdd 1), rfl⟩
  obtain ⟨w, hwP, hwR⟩ := hR
  set f₀ : Y →* OriginalH F a A hfix := φ.comp (Subgroup.inclusion hYN) with hf₀
  have hmem : ∀ y : Y, f₀ y ∈ Subgroup.zpowers (originalZ F a A hfix) := by
    intro y
    obtain ⟨k, hk⟩ := hY y
    have hcomm : f₀ y * originalSlInH F a A hfix (rootMat l 1) =
        originalSlInH F a A hfix (rootMat l 1) * f₀ y := by
      rw [← hwR]
      change φ (Subgroup.inclusion hYN y) * φ w = φ w * φ (Subgroup.inclusion hYN y)
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hYP y.2) w (Subgroup.mem_subgroupOf.mp hwP)).symm
    have hk' : f₀ y ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    rcases model_eq_one_or_z hp hp2 ha hA l hk' hcomm with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers _
  have hinj : Function.Injective f₀ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hker : Subgroup.inclusion hYN y ∈ φ.ker := hy
    rw [hφ.ker_eq, Subgroup.mem_subgroupOf] at hker
    obtain ⟨k, hk⟩ := hY y
    have h1 : orderOf (y : G) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one])
    have h2 : Odd (orderOf (y : G)) :=
      σ.odd_card_ON.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hker)
    exact Subtype.ext (orderOf_eq_one_iff.mp ((h2.coprime_two_right.pow_right k).eq_one_of_dvd h1))
  exact isCyclic_of_injective (f₀.codRestrict _ hmem) fun x y h => hinj (congrArg Subtype.val h)

omit [Finite G] in
private theorem not_le_centralizer_of_root
    (hφ : IsModelMap σ φ (layerM F a A hfix) (originalU F a A hfix)) {J : Subgroup G}
    (hJ : σ.IsLayerComplement J) (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (hq7 : 7 ≤ Nat.card F) {l : F} (hl : l ^ 2 = -(a : F)) {P : Subgroup G}
    (hPl : (P.subgroupOf σ.N).map φ = rootM F a A hfix l) :
    ¬ (σ.C ⊓ J ≤ Subgroup.centralizer (P : Set G)) := by
  intro hle
  have h2 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by simpa using hl.symm)
  obtain ⟨w, hwT, hw⟩ := exists_generic_torus hodd ha hq7
  have hwM : originalSlInH F a A hfix w ∈ (J.subgroupOf σ.N).map φ := by
    rw [hφ.map_J hJ]
    exact ⟨w, rfl⟩
  obtain ⟨j, hjJ, hjw⟩ := hwM
  have hjC : (j : G) ∈ σ.C := by
    have hc : φ j * originalU F a A hfix = originalU F a A hfix * φ j := by
      rw [hjw]
      exact Subgroup.mem_centralizer_singleton_iff.mp ((slIn_mem_cenU_iff w).mpr hwT)
    exact (mem_C_iff σ j.2).mpr
      (congrArg Subtype.val (hφ.commute_of_mem_J hJ (Subgroup.mem_subgroupOf.mp hjJ) hc))
  have hR : originalSlInH F a A hfix (rootMat l 1) ∈ (P.subgroupOf σ.N).map φ := by
    rw [hPl]
    exact ⟨_, rootHom_mem l (Multiplicative.ofAdd 1), rfl⟩
  obtain ⟨v, hvP, hvR⟩ := hR
  have hcomm : (v : G) * j = j * v := Subgroup.mem_centralizer_iff.mp
    (hle (Subgroup.mem_inf.mpr ⟨hjC, Subgroup.mem_subgroupOf.mp hjJ⟩)) v
    (Subgroup.mem_subgroupOf.mp hvP)
  apply torus_not_comm_rootMat h2 hl0 hwT (right_ne_zero_of_mul hw)
  apply slIn_injective (a := a) (A := A) (hfix := hfix)
  rw [map_mul, map_mul, ← hjw, ← hvR, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hcomm.symm

end Transport

section Data

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {ρ : ℕ}

omit [Finite G] in
private theorem fi_conjSub_one (X : Subgroup G) : conjSub 1 X = X := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hx
  · intro hy
    exact ⟨y, hy, by simp⟩

private theorem fi_J_inf_eq_bot (Δ : Data σ ρ) (hδ : σ.DeltaEpsMinus) : Δ.J ⊓ σ.ON = ⊥ := by
  refine Δ.J_inf.resolve_right ?_
  rintro ⟨h9, hh, -⟩
  rcases hδ with ⟨-, h3⟩ | ⟨hh', -⟩
  · rw [h9] at h3
    exact absurd h3 (by decide)
  · exact hh' hh

private theorem fi_inf_C_eq_bot (Δ : Data σ ρ) {P : Subgroup G} (hPJ : P ≤ Δ.J)
    (hPp : IsPGroup ρ P) : P ⊓ σ.C = ⊥ := by
  have : Fact ρ.Prime := ⟨Δ.prime⟩
  have hle : P ⊓ σ.C ≤ σ.C ⊓ σ.L :=
    le_inf inf_le_right (inf_le_left.trans (hPJ.trans (Δ.J_le.trans le_sup_left)))
  rcases (hPp.to_le inf_le_left).card_eq_or_dvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exact absurd (h.trans (Subgroup.card_dvd_of_le hle)) Δ.totallyInverted

variable {F : Type} [Field F] [Finite F] {a : Fˣ} {A : Subgroup (F ≃+* F)}
  {hfix : ∀ τ : A, (τ : F ≃+* F) (a : F) = a} {φ : σ.N →* OriginalH F a A hfix}

private theorem roots_of_model (Δ : Data σ ρ)
    (hφ : IsModelMap σ φ (layerM F a A hfix) (originalU F a A hfix)) (hh : σ.height = 1)
    (hcard : Nat.card F = σ.q) (hp : σ.p.Prime) (hp2 : σ.p ≠ 2) (hq7 : 7 ≤ Nat.card F)
    (ha : ¬IsSquare a) (hδ : σ.DeltaEpsMinus ∧ ρ ∣ σ.q) :
    σ.IsLayerComplement Δ.J ∧
      (∃ l : F, l ^ 2 = -(a : F) ∧ ((Δ.Q 0).subgroupOf σ.N).map φ = rootM F a A hfix l) ∧
      (∃ l : F, l ^ 2 = -(a : F) ∧ ((Δ.Qs 0).subgroupOf σ.N).map φ = rootM F a A hfix l) := by
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  have hJ : σ.IsLayerComplement Δ.J :=
    ⟨Δ.J_le, Δ.L₀_eq, fi_J_inf_eq_bot Δ hδ.1, Δ.J_normal, Δ.J_centralizes⟩
  have h3 : Nat.card F % 4 = 3 := by
    rcases hδ.1 with ⟨-, h3⟩ | ⟨hh', -⟩
    · rw [hcard]
      exact h3
    · exact absurd hh hh'
  obtain ⟨b, hb⟩ := (neg_coefficient_square_iff F a hodd ha).mpr h3
  have hl : b ^ 2 = -(a : F) := by
    rw [hb]
    ring
  have hρp : ρ = σ.p := (Nat.prime_dvd_prime_iff_eq Δ.prime hp).mp (Δ.prime.dvd_of_dvd_pow hδ.2)
  obtain ⟨-, hcQ, hcQs, -⟩ := Δ.Q_cases hδ 0
  have hQJ := (Δ.Q_le 0).1
  have hQsJ := (Δ.Q_le 0).2
  simp only [Fin.val_zero, pow_zero, fi_conjSub_one] at hQJ hQsJ
  have hsig : ∀ {P : Subgroup G}, P ≤ Δ.J → IsPGroup ρ P →
      σ.C ≤ Subgroup.normalizer (P : Set G) → P ∈ signalizers Δ.J σ.C σ.p :=
    fun hPJ hPp hCP => ⟨hPJ, hρp ▸ hPp, hCP, fi_inf_C_eq_bot Δ hPJ hPp⟩
  refine ⟨hJ, exists_root_of_signalizer hφ hJ hodd ha hq7 hp hp2 hl
    (hsig hQJ (Δ.Q_pgroup 0).1 (Δ.Q_C 0).1) (hcQ.trans hcard.symm),
    exists_root_of_signalizer hφ hJ hodd ha hq7 hp hp2 hl
    (hsig hQsJ (Δ.Q_pgroup 0).2 (Δ.Q_C 0).2) (hcQs.trans hcard.symm)⟩

private theorem abg_II_4_4_of_model (Δ : Data σ ρ)
    (hφ : IsModelMap σ φ (layerM F a A hfix) (originalU F a A hfix)) (hh : σ.height = 1)
    (hcard : Nat.card F = σ.q) (hp : σ.p.Prime) (hp2 : σ.p ≠ 2) (hq7 : 7 ≤ Nat.card F)
    (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) [CharP F σ.p] :
    Sec11.ABG_II_4_4 Δ := by
  intro hδ Y hYN hY hYP
  obtain ⟨-, ⟨l, -, hQl⟩, ⟨l', -, hQsl⟩⟩ :=
    roots_of_model Δ hφ hh hcard hp hp2 hq7 ha hδ
  rcases hYP with h | h
  · exact isCyclic_of_le_centralizer hφ hp hp2 ha hA hQl hYN hY h
  · exact isCyclic_of_le_centralizer hφ hp hp2 ha hA hQsl hYN hY h

private theorem abg_II_4_10_iii_of_model (Δ : Data σ ρ)
    (hφ : IsModelMap σ φ (layerM F a A hfix) (originalU F a A hfix)) (hh : σ.height = 1)
    (hcard : Nat.card F = σ.q) (hp : σ.p.Prime) (hp2 : σ.p ≠ 2) (hq7 : 7 ≤ Nat.card F)
    (ha : ¬IsSquare a) :
    Sec11.ABG_II_4_10_iii Δ := by
  intro hδ
  obtain ⟨hJ, ⟨l, hl, hQl⟩, ⟨l', hl', hQsl⟩⟩ :=
    roots_of_model Δ hφ hh hcard hp hp2 hq7 ha hδ
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  exact ⟨not_le_centralizer_of_root hφ hJ hodd ha hq7 hl hQl,
    not_le_centralizer_of_root hφ hJ hodd ha hq7 hl' hQsl⟩

end Data

private theorem fi_charP {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ f) : CharP F p := by
  have : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hcard)

private theorem fi_seven_le {p f : ℕ} (hpodd : Odd p) (hq : 5 < p ^ f) : 7 ≤ p ^ f := by
  obtain ⟨k, hk⟩ := hpodd.pow (n := f)
  omega

theorem frontier_abg_II_4_4 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    {ρ : ℕ} (Δ : Data (frontierSetting S fS t p f) ρ) :
    Sec11.ABG_II_4_4 Δ := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, hA, -, ha, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  have := fi_charP hp hcard
  exact abg_II_4_4_of_model Δ hφ rfl hcard hp hp2 (hcard ▸ fi_seven_le hpodd hq) ha hA

theorem frontier_abg_II_4_10_iii {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    {ρ : ℕ} (Δ : Data (frontierSetting S fS t p f) ρ) :
    Sec11.ABG_II_4_10_iii Δ := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, -, -, ha, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  exact abg_II_4_10_iii_of_model Δ hφ rfl hcard hp hp2 (hcard ▸ fi_seven_le hpodd hq) ha

end CFSG.Semidihedral.AllPrime
