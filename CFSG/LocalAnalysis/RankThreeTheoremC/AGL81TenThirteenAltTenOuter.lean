module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveInner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open CFSG.Assembly.LowTwoRank

theorem exists_conj_eq_of_sq_inner {A T : Type*} [Group A] [Group T] {Y : Subgroup A}
    (hY : commutator ↥Y = ⊤) (e : ↥Y ⧸ Subgroup.center ↥Y ≃* T)
    (hT : ∀ β : MulAut T, (∃ k : ℕ, β ^ 2 ^ k = 1) → ∃ w : T, β ^ 2 = MulAut.conj w)
    {t : A} (htY : t ∈ Subgroup.normalizer (Y : Set A)) (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) :
    ∃ y ∈ Y, ∀ x ∈ Y, t ^ 2 * x * (t ^ 2)⁻¹ = y * x * y⁻¹ := by
  have hc : ∀ s ∈ Subgroup.normalizer (Y : Set A), ∀ x ∈ Y, s * x * s⁻¹ ∈ Y :=
    fun s hs x hx => (Subgroup.mem_normalizer_iff.mp hs x).mp hx
  have htn : ∀ n : ℕ, t ^ n ∈ Subgroup.normalizer (Y : Set A) := fun n => pow_mem htY n
  let θ : ↥Y ≃* ↥Y :=
    { toFun := fun x => ⟨t * x * t⁻¹, hc t htY x x.2⟩
      invFun := fun x => ⟨t⁻¹ * x * t⁻¹⁻¹, hc t⁻¹ (inv_mem htY) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let θb : MulAut (↥Y ⧸ Subgroup.center ↥Y) :=
    QuotientGroup.congr _ _ θ (Subgroup.map_center_eq θ)
  let β : MulAut T := (e.symm.trans θb).trans e
  have hβ : ∀ x : ↥Y, β (e (QuotientGroup.mk x)) = e (QuotientGroup.mk (θ x)) := by
    intro x
    change e (θb (e.symm (e (QuotientGroup.mk x)))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hpow : ∀ (n : ℕ) (x : ↥Y), (β ^ n) (e (QuotientGroup.mk x)) =
      e (QuotientGroup.mk (⟨t ^ n * x * (t ^ n)⁻¹, hc _ (htn n) x x.2⟩ : ↥Y)) := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [pow_zero, MulAut.one_apply]
      congr 2
      apply Subtype.ext
      simp
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, hβ, ih]
      congr 2
      apply Subtype.ext
      change t ^ n * (t * (x : A) * t⁻¹) * (t ^ n)⁻¹ = t ^ (n + 1) * x * (t ^ (n + 1))⁻¹
      rw [pow_succ]
      group
  obtain ⟨k, hk⟩ := ht2
  have hβk : β ^ 2 ^ k = 1 := by
    ext z
    obtain ⟨z', rfl⟩ := e.surjective z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z'
    rw [hpow, MulAut.one_apply]
    congr 2
    apply Subtype.ext
    simp [hk]
  obtain ⟨w, hw⟩ := hT β ⟨k, hβk⟩
  obtain ⟨w', hw'⟩ := e.surjective w
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective w'
  have hmod : ∀ u : ↥Y, (y₀ * u * y₀⁻¹)⁻¹ *
      (⟨t ^ 2 * u * (t ^ 2)⁻¹, hc _ (htn 2) u u.2⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
    intro u
    rw [← QuotientGroup.eq]
    apply e.injective
    rw [← hpow, hw, MulAut.conj_apply, ← hw', ← map_inv, ← map_mul, ← map_mul,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  refine ⟨y₀, y₀.2, ?_⟩
  have key := LeviFive.conj_eq_of_conj_mem_center hY (z := (y₀ : A)⁻¹ * t ^ 2) fun u hu => by
    have hm := hmod ⟨u, hu⟩
    set m : ↥Y := (y₀ * ⟨u, hu⟩ * y₀⁻¹)⁻¹ * ⟨t ^ 2 * u * (t ^ 2)⁻¹, hc _ (htn 2) u hu⟩ with hmdef
    have hmA : t ^ 2 * u * (t ^ 2)⁻¹ = (y₀ : A) * u * (y₀ : A)⁻¹ * (m : A) := by
      rw [hmdef]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      group
    have hmc : ∀ v ∈ Y, (m : A) * v = v * (m : A) := fun v hv =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hm ⟨v, hv⟩)).symm
    refine ⟨m, m.2, hmc, ?_⟩
    calc (y₀ : A)⁻¹ * t ^ 2 * u * ((y₀ : A)⁻¹ * t ^ 2)⁻¹
        = (y₀ : A)⁻¹ * (t ^ 2 * u * (t ^ 2)⁻¹) * (y₀ : A) := by group
      _ = u * ((y₀ : A)⁻¹ * ((m : A) * (y₀ : A))) := by rw [hmA]; group
      _ = u * (m : A) := by rw [hmc _ y₀.2]; group
      _ = (m : A) * u := (hmc u hu).symm
  intro x hx
  have := key x hx
  calc t ^ 2 * x * (t ^ 2)⁻¹
      = (y₀ : A) * ((y₀ : A)⁻¹ * t ^ 2 * x * ((y₀ : A)⁻¹ * t ^ 2)⁻¹) * (y₀ : A)⁻¹ := by group
    _ = (y₀ : A) * x * (y₀ : A)⁻¹ := by rw [this]

private theorem ringEquiv_mul_self_of_card_four {K : Type} [Field K] (hK : Nat.card K = 4)
    (σ : K ≃+* K) : σ * σ = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
    Nat.prime_two (by norm_num : 1 ≤ 2) (by rw [hK]; norm_num : Nat.card K = 2 ^ 2)
  haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rw [← pow_two, ← hcard]
  exact pow_card_eq_one'

private theorem unit_pow_three_of_card_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (u : Kˣ) : u ^ 3 = 1 := by
  have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  rw [← h3]
  exact pow_card_eq_one'

theorem sq_inner_projectiveSL_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (β : MulAut (LinearFlag.projectiveSL 4 K)) : ∃ w, β ^ 2 = MulAut.conj w := by
  classical
  obtain ⟨A, σ, ε, hε, rfl⟩ :=
    (LinearFlag.automorphism_generation (n := 4) (K := K) (by norm_num)).2 β
  have hσ := ringEquiv_mul_self_of_card_four hK σ
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ :=
    LinearFlag.standard_automorphism_transport (K := K) (n := 4)
  have hff : LinearFlag.fieldAut 4 K σ * LinearFlag.fieldAut 4 K σ = 1 := by
    rw [h2, hσ, map_one]
  obtain ⟨B, hB⟩ : ∃ B : GL (Fin 4) K, (LinearFlag.conjAut 4 K A * LinearFlag.fieldAut 4 K σ *
      LinearFlag.dualAut 4 K ^ ε) ^ 2 = LinearFlag.conjAut 4 K B := by
    interval_cases ε
    · refine ⟨A * GeneralLinearGroup.map (σ : K →+* K) A, ?_⟩
      rw [pow_zero, mul_one, pow_two]
      calc LinearFlag.conjAut 4 K A * LinearFlag.fieldAut 4 K σ *
            (LinearFlag.conjAut 4 K A * LinearFlag.fieldAut 4 K σ)
          = LinearFlag.conjAut 4 K A * (LinearFlag.fieldAut 4 K σ * LinearFlag.conjAut 4 K A *
              (LinearFlag.fieldAut 4 K σ)⁻¹) *
              (LinearFlag.fieldAut 4 K σ * LinearFlag.fieldAut 4 K σ) := by group
        _ = _ := by rw [h3, hff, mul_one, h1]
    · refine ⟨A * GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose A), ?_⟩
      have hδ : (LinearFlag.dualAut 4 K)⁻¹ = LinearFlag.dualAut 4 K :=
        inv_eq_of_mul_eq_one_right h4
      rw [pow_one, pow_two]
      calc LinearFlag.conjAut 4 K A * LinearFlag.fieldAut 4 K σ * LinearFlag.dualAut 4 K *
            (LinearFlag.conjAut 4 K A * LinearFlag.fieldAut 4 K σ * LinearFlag.dualAut 4 K)
          = LinearFlag.conjAut 4 K A * LinearFlag.fieldAut 4 K σ *
              (LinearFlag.dualAut 4 K * LinearFlag.conjAut 4 K A * LinearFlag.dualAut 4 K) *
              ((LinearFlag.dualAut 4 K)⁻¹ * LinearFlag.fieldAut 4 K σ *
                LinearFlag.dualAut 4 K) := by group
        _ = LinearFlag.conjAut 4 K A * (LinearFlag.fieldAut 4 K σ *
              LinearFlag.conjAut 4 K (GeneralLinearGroup.inverseTranspose A) *
              (LinearFlag.fieldAut 4 K σ)⁻¹) *
              (LinearFlag.fieldAut 4 K σ * LinearFlag.fieldAut 4 K σ) := by
            rw [hδ, h5, h6]; group
        _ = _ := by rw [h3, hff, mul_one, h1]
  set u : Kˣ := GeneralLinearGroup.det B with hu
  have hu3 := unit_pow_three_of_card_four hK u
  have hdet : ((GeneralLinearGroup.scalar (Fin 4) u⁻¹ * B : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← GeneralLinearGroup.val_det_apply,
      ← hu, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    have : u⁻¹ ^ 4 * u = 1 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, inv_pow, hu3, inv_one, one_mul,
        inv_mul_cancel]
    rw [this, Units.val_one]
  obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin 4) K,
      SpecialLinearGroup.toGL g = GeneralLinearGroup.scalar (Fin 4) u⁻¹ * B :=
    ⟨⟨_, hdet⟩, Units.ext rfl⟩
  have hBg : B = GeneralLinearGroup.scalar (Fin 4) u * SpecialLinearGroup.toGL g := by
    rw [hg, map_inv, mul_inv_cancel_left]
  refine ⟨LinearFlag.proj 4 K g, ?_⟩
  rw [hB, hBg, map_mul, LinearFlag.conjAut_scalar, one_mul, LinearFlag.conjAut_toGL]

theorem sq_inner_projectiveSp {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) {r : ℕ}
    (hr : 3 ≤ r) (β : MulAut (StatedProj (StatedSp r K))) (hβ : ∃ k : ℕ, β ^ 2 ^ k = 1) :
    ∃ w, β ^ 2 = MulAut.conj w := by
  classical
  haveI : NeZero r := ⟨by omega⟩
  obtain ⟨A, σ, rfl⟩ := (SymplecticHigher.automorphism_generation (K := K) hr).2 β
  have hσ := ringEquiv_mul_self_of_card_four hK σ
  set B := A * SymplecticHigher.gspFieldMap σ A with hBdef
  have hsq : (SymplecticHigher.conjAut r K A * SymplecticHigher.fieldAut r K σ) ^ 2 =
      SymplecticHigher.conjAut r K B := by
    rw [pow_two, SymplecticHigher.conjAut_mul_fieldAut_mul, hσ, map_one, mul_one]
  obtain ⟨k, hk⟩ := hβ
  have hBk : SymplecticHigher.conjAut r K B ^ 2 ^ k = 1 := by
    rw [← hsq, ← pow_mul, mul_comm, pow_mul, hk, one_pow]
  have hB3 : B ^ 3 ∈ (SymplecticHigher.multiplier r K).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact unit_pow_three_of_card_four hK _
  rw [SymplecticHigher.ker_multiplier, Subgroup.mem_subgroupOf] at hB3
  have hinn3 : SymplecticHigher.conjAut r K B ^ 3 =
      MulAut.conj (SymplecticFlag.proj r K ⟨_, hB3⟩) := by
    rw [← map_pow]
    have h2 : (B ^ 3 : SymplecticHigher.gsp r K) =
        ⟨((⟨_, hB3⟩ : StatedSp r K) : GL (Fin r ⊕ Fin r) K),
          SymplecticHigher.statedSp_le_gsp hB3⟩ := rfl
    exact (congrArg _ h2).trans (SymplecticHigher.conjAut_statedSp _)
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have hbez : (1 : ℤ) =
      ((3 : ℕ) : ℤ) * Nat.gcdA 3 (2 ^ k) + ((2 ^ k : ℕ) : ℤ) * Nat.gcdB 3 (2 ^ k) := by
    have h := Nat.gcd_eq_gcd_ab 3 (2 ^ k)
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    exact h
  refine ⟨SymplecticFlag.proj r K ⟨_, hB3⟩ ^ Nat.gcdA 3 (2 ^ k), ?_⟩
  rw [hsq, map_zpow, ← hinn3]
  calc SymplecticHigher.conjAut r K B
      = SymplecticHigher.conjAut r K B ^ (1 : ℤ) := (zpow_one _).symm
    _ = SymplecticHigher.conjAut r K B ^ (((3 : ℕ) : ℤ) * Nat.gcdA 3 (2 ^ k) +
          ((2 ^ k : ℕ) : ℤ) * Nat.gcdB 3 (2 ^ k)) := by rw [← hbez]
    _ = (SymplecticHigher.conjAut r K B ^ 3) ^ Nat.gcdA 3 (2 ^ k) := by
        rw [_root_.zpow_add, _root_.zpow_mul, _root_.zpow_mul, zpow_natCast, zpow_natCast, hBk,
          _root_.one_zpow, mul_one]

theorem mem_of_mem_normalizer_of_isParabolicTwo {A : Type*} [Group A] [Finite A]
    {Y P : Subgroup A} (hP : IsParabolicTwo Y P) {y : A} (hy : y ∈ Y)
    (hyP : y ∈ Subgroup.normalizer (P : Set A)) : y ∈ P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPY, T, ⟨hTY, hT2, hTi⟩, hNP⟩ := hP
  set J := P.subgroupOf Y with hJ
  let T₀ : Sylow 2 ↥Y := (hT2.comap_of_injective Y.subtype Y.subtype_injective).toSylow hTi
  have hT₀ : (T₀ : Subgroup ↥Y) = T.subgroupOf Y := IsPGroup.toSylow_coe _ _
  have hNJ : Subgroup.normalizer ((T₀ : Subgroup ↥Y) : Set ↥Y) ≤ J := by
    intro g hg
    rw [hJ, Subgroup.mem_subgroupOf]
    refine hNP ⟨g.2, Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp hg ⟨x, hTY hx⟩).mp
        (by rw [hT₀, Subgroup.mem_subgroupOf]; exact hx)
      rw [hT₀, Subgroup.mem_subgroupOf] at h1
      simpa using h1
    · have hxY : x ∈ Y := by
        have h2 := Y.mul_mem (Y.mul_mem (Y.inv_mem g.2) (hTY hx)) g.2
        simpa [mul_assoc] using h2
      have h1 := (Subgroup.mem_normalizer_iff.mp hg ⟨x, hxY⟩).mpr
        (by rw [hT₀, Subgroup.mem_subgroupOf]; simpa using hx)
      rw [hT₀, Subgroup.mem_subgroupOf] at h1
      exact h1
  have hyJ : (⟨y, hy⟩ : ↥Y) ∈ Subgroup.normalizer (J : Set ↥Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hJ, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hyP x
  have hTJ : (T₀ : Subgroup ↥Y) ≤ J := Subgroup.le_normalizer.trans hNJ
  set G' : Subgroup ↥Y := Subgroup.normalizer (J : Set ↥Y) with hG'
  have hJG : J ≤ G' := Subgroup.le_normalizer
  have hTG : (T₀ : Subgroup ↥Y) ≤ G' := hTJ.trans hJG
  let P' : Sylow 2 G' := T₀.subtype hTG
  set N' : Subgroup G' := J.subgroupOf G' with hN'
  haveI hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJG).2 le_rfl
  have hP'N' : (P' : Subgroup G') ≤ N' := by
    rw [Sylow.coe_subtype]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hTJ (Subgroup.mem_subgroupOf.mp hx))
  have hfr := Sylow.normalizer_sup_eq_top' (N := N') P' hP'N'
  have hx' : (⟨⟨y, hy⟩, hyJ⟩ : G') ∈ Subgroup.normalizer (P' : Set G') ⊔ N' := by
    rw [hfr]; exact Subgroup.mem_top _
  obtain ⟨n, hn, m, hm, hnm⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  have hn' : (n : ↥Y) ∈ Subgroup.normalizer ((T₀ : Subgroup ↥Y) : Set ↥Y) := by
    have hc : (P' : Subgroup G') = (T₀ : Subgroup ↥Y).subgroupOf G' := T₀.coe_subtype hTG
    have : n ∈ Subgroup.normalizer (((T₀ : Subgroup ↥Y).subgroupOf G' : Subgroup G') :
        Set G') := by
      rw [← hc]; exact hn
    rw [← Subgroup.subgroupOf_normalizer_eq hTG] at this
    exact Subgroup.mem_subgroupOf.mp this
  have hm' : (m : ↥Y) ∈ J := Subgroup.mem_subgroupOf.mp hm
  have hyeq : (⟨y, hy⟩ : ↥Y) = (n : ↥Y) * (m : ↥Y) := by
    have := congrArg Subtype.val hnm
    simpa using this.symm
  have hmem : (⟨y, hy⟩ : ↥Y) ∈ J := by
    rw [hyeq]
    exact J.mul_mem (hNJ hn') hm'
  rw [hJ, Subgroup.mem_subgroupOf] at hmem
  exact hmem

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen
