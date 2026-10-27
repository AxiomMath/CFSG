module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Conj
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Proj
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

open Matrix Finset CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.GLTheoremA.KD264LieA4

open scoped Classical

variable {p f : ℕ} {K : Type} [Field K]

theorem three_ne_zero_of_dvd (h : UnitaryFieldData p f K) (hQ : 3 ∣ p ^ f - 1) : (3 : K) ≠ 0 := by
  intro h3
  haveI := h.charP
  have hcast : ((3 : ℕ) : K) = 0 := by exact_mod_cast h3
  have hpd : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).mp hcast
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp hpd
  have hpos : 0 < p ^ f := pow_pos h.prime.pos f
  have h3pf : 3 ∣ p ^ f := by
    rw [hp3]
    exact dvd_pow_self 3 (by have := h.one_le; omega)
  omega

theorem exists_zeta_of_dvd (h : UnitaryFieldData p f K) (hQ : 3 ∣ p ^ f - 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ 3 := by
  haveI : Finite K := h.finite
  apply exists_isPrimitiveRoot_three_of_dvd K
  rw [hF_of h]
  obtain ⟨k, hk⟩ := hQ
  have hpos : 0 < p ^ f := pow_pos h.prime.pos f
  have hq : p ^ f = 3 * k + 1 := by omega
  rw [hq]
  have hsq : (3 * k + 1) ^ 2 = 3 * (3 * k * k + 2 * k) + 1 := by ring
  rw [hsq, Nat.add_sub_cancel]
  exact dvd_mul_right 3 _

theorem conj_pow' (A : GL (Fin 7) K) (M : Matrix (Fin 7) (Fin 7) K) (n : ℕ) :
    ((A : Matrix (Fin 7) (Fin 7) K) * M * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) ^ n =
      (A : Matrix (Fin 7) (Fin 7) K) * M ^ n * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹ := by
  induction n with
  | zero =>
    have hAdet : IsUnit (A : Matrix (Fin 7) (Fin 7) K).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
    rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.mul_nonsing_inv _ hAdet]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, ← conj_mul_eq]

@[expose] def kerSubU {G : Type} [Group G] {L : Type} [Field L] (c : G → L)
    (hcmul : ∀ x y, c (x * y) = c x * c y) (hc1 : c 1 = 1) (hcinv : ∀ x, c x⁻¹ = (c x)⁻¹) :
    Subgroup G where
  carrier := {x | c x = 1}
  mul_mem' := fun {a b} ha hb => by
    show c (a * b) = 1
    rw [hcmul, Set.mem_setOf_eq.mp ha, Set.mem_setOf_eq.mp hb, one_mul]
  one_mem' := hc1
  inv_mem' := fun {a} ha => by
    show c a⁻¹ = 1
    rw [hcinv, Set.mem_setOf_eq.mp ha, inv_one]

theorem kerConcl_PSU7 (h : UnitaryFieldData p f K) (hQ : 3 ∣ p ^ f - 1)
    {E : Subgroup (StatedProj (StatedSU 7 (p ^ f) K))}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) : KerConcl E := by
  haveI : Finite K := h.finite
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, hPE, hcomm, hpow, hPcard⟩ := lift_of_elemAbelianU h hE hc
  let P₁ : Subgroup (GL (Fin 7) K) := P.map (StatedSU 7 (p ^ f) K).subtype
  have hmemP₁ : ∀ x ∈ P₁, x ∈ StatedSU 7 (p ^ f) K := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hcommP₁ : ∀ x ∈ P₁, ∀ y ∈ P₁, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    exact congrArg Subtype.val (hcomm x' hx' y' hy')
  have hpowP₁ : ∀ x ∈ P₁, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have := congrArg Subtype.val (hpow x' hx')
    simpa using this
  have hcardP₁ : Nat.card P₁ = 27 := by
    rw [show P₁ = P.map (StatedSU 7 (p ^ f) K).subtype from rfl,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hPcard]
  haveI : Finite P₁ := Nat.finite_of_card_ne_zero (by rw [hcardP₁]; norm_num)
  haveI : Fintype P₁ := Fintype.ofFinite _
  have hcardFin : Fintype.card P₁ = 27 := by rw [← Nat.card_eq_fintype_card, hcardP₁]
  obtain ⟨ζ, hζ⟩ := exists_zeta_of_dvd h hQ
  obtain ⟨A, hA0⟩ := exists_diag_StatedSU h hζ P₁ hmemP₁ hcommP₁ hpowP₁
  have hA : ∀ x : P₁, ∀ i j, i ≠ j →
      ((A : Matrix (Fin 7) (Fin 7) K) * ((x : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
        ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) i j = 0 := by
    intro x i j hij
    have := hA0 x x.2 i j hij
    rwa [Matrix.coe_units_inv] at this
  let d : Fin 7 → P₁ → K := fun i x =>
    ((A : Matrix (Fin 7) (Fin 7) K) * ((x : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
      ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) i i
  have hconjdiag : ∀ x : P₁, (A : Matrix (Fin 7) (Fin 7) K) *
      ((x : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹ =
        Matrix.diagonal (fun i => d i x) := by
    intro x
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [d]
    · rw [Matrix.diagonal_apply_ne _ hij, hA x i j hij]
  have hdmul : ∀ i (x y : P₁), d i (x * y) = d i x * d i y := by
    intro i x y
    simp only [d, Subgroup.coe_mul, Units.val_mul]
    rw [conj_mul_eq]
    exact KA7.diag_mul_apply (hA x) (hA y) i
  have hAdet : IsUnit (A : Matrix (Fin 7) (Fin 7) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
  have hdpow : ∀ i (x : P₁), d i x ^ 3 = 1 := by
    intro i x
    have hx3 : ((x : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) ^ 3 = 1 := by
      have := congrArg (fun g : GL (Fin 7) K => (g : Matrix (Fin 7) (Fin 7) K)) (hpowP₁ x x.2)
      simpa using this
    have hcube : ((A : Matrix (Fin 7) (Fin 7) K) *
        ((x : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) ^ 3
        = 1 := by
      rw [conj_pow', hx3, Matrix.mul_one, Matrix.mul_nonsing_inv _ hAdet]
    have hD : (Matrix.diagonal (fun j => d j x)) ^ 3 = 1 := by
      rw [← hconjdiag x]
      exact hcube
    rw [Matrix.diagonal_pow] at hD
    have := congrFun (congrFun hD i) i
    simpa [Matrix.diagonal_apply_eq] using this
  have hfaith : ∀ x : P₁, (∀ i, d i x = 1) → x = 1 := by
    intro x hx
    have hD1 : (A : Matrix (Fin 7) (Fin 7) K) *
        ((x : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹ = 1 := by
      rw [hconjdiag x]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hx]
      · simp [Matrix.diagonal_apply_ne _ hij, hij]
    have hGL : (A : GL (Fin 7) K) * (x : GL (Fin 7) K) * (A : GL (Fin 7) K)⁻¹ = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Units.val_one]
      exact hD1
    apply Subtype.ext
    calc (x : GL (Fin 7) K)
        = (A : GL (Fin 7) K)⁻¹ * ((A : GL (Fin 7) K) * (x : GL (Fin 7) K) *
            (A : GL (Fin 7) K)⁻¹) * (A : GL (Fin 7) K) := by group
      _ = 1 := by rw [hGL]; group
  have hsymm : ∀ z : P₁, (univ.filter fun i => d i z = ζ).card =
      (univ.filter fun i => d i z = ζ ^ 2).card := by
    intro z
    exact symm_count_of_unitary h hQ hζ A (hmemP₁ z.1 z.2) (hconjdiag z)
  obtain ⟨c, hcmul, hcpow, _hnontriv, hker9, hcount⟩ :=
    KA7.exists_good_char hζ (d := d) hdmul hdpow hsymm hfaith hcardFin
  have hc1 : c 1 = 1 := KA7.char_one hcmul hcpow
  have hcinv : ∀ x, c x⁻¹ = (c x)⁻¹ := fun x => by
    have hh := hcmul x⁻¹ x
    rw [inv_mul_cancel, hc1] at hh
    exact eq_inv_of_mul_eq_one_left hh.symm
  have h3K : (3 : K) ≠ 0 := three_ne_zero_of_dvd h hQ
  have hk0 : ((9 : ℕ) : K) ≠ 0 := KA7.nine_ne_zero_of_three_ne h3K
  have h9 : ((univ.filter fun x : P₁ => c x = 1).card : K) ≠ 0 := by
    rw [hker9]
    exact hk0
  set e : Matrix (Fin 7) (Fin 7) K := projU (univ.filter fun x : P₁ => c x = 1) with he_def
  have he : e * e = e := projU_mul_self c hcmul hcpow h9
  have hedag : dagI h e = e := projU_dag h hmemP₁ c hcmul hcinv
  have hr : e.rank = 3 := by
    rw [he_def, rank_projU A hA c hcmul hcpow hker9 hk0]
    exact hcount
  obtain ⟨A₀, hA₀⟩ := KA7.exists_idem_normal e he hr
  obtain ⟨R, hR, hRe⟩ := exists_unitary_frame h e hedag A₀ hA₀
  let F₁ : Subgroup P₁ := kerSubU c hcmul hc1 hcinv
  let F₀ : Subgroup (GL (Fin 7) K) := F₁.map P₁.subtype
  have hF₀P₁ : F₀ ≤ P₁ := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hF₀S : F₀ ≤ StatedSU 7 (p ^ f) K := fun x hx => hmemP₁ x (hF₀P₁ hx)
  let FS : Subgroup ↥(StatedSU 7 (p ^ f) K) := F₀.subgroupOf (StatedSU 7 (p ^ f) K)
  let PS : Subgroup ↥(StatedSU 7 (p ^ f) K) := P₁.subgroupOf (StatedSU 7 (p ^ f) K)
  have hPS : PS = P := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hEP : E = PS.map (piU p f K) := by rw [hPS, hPE]
  refine kerConcl_of_equiv (conjPU h hR) E ?_
  have hEconj : E.map (conjPU h hR).toMonoidHom =
      (PS.map (conjS h hR).toMonoidHom).map (piU p f K) := by
    rw [hEP, Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hEconj]
  have hP3 : ∀ x ∈ PS.map (conjS h hR).toMonoidHom, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy3 : y ^ 3 = 1 := by
      apply Subtype.ext
      have hyP : (y : GL (Fin 7) K) ∈ P₁ := Subgroup.mem_subgroupOf.mp hy
      have := hpowP₁ _ hyP
      simpa using this
    calc ((conjS h hR).toMonoidHom y) ^ 3 = (conjS h hR) (y ^ 3) := (map_pow _ _ _).symm
      _ = 1 := by rw [hy3, map_one]
  have hFSPS : FS ≤ PS := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hF₀P₁ (Subgroup.mem_subgroupOf.mp hx))
  have hF'P : FS.map (conjS h hR).toMonoidHom ≤ PS.map (conjS h hR).toMonoidHom :=
    Subgroup.map_mono hFSPS
  have hFSc : Nat.card FS = 9 := by
    have e1 : Nat.card FS = Nat.card F₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF₀S).toEquiv
    have e2 : Nat.card F₀ = Nat.card F₁ :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    have e3 : Nat.card F₁ = 9 := by
      have e4 : Nat.card F₁ = Nat.card {x : P₁ // c x = 1} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
      rw [e4, Nat.card_eq_fintype_card, Fintype.card_subtype, ← hker9]
    rw [e1, e2, e3]
  have hF'card : Nat.card (FS.map (conjS h hR).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (conjS h hR).injective, hFSc]
  have hkD : ∀ y : P₁, c y = 1 →
      (((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
          ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * (R : Matrix (Fin 7) (Fin 7) K)) * D0 K =
        D0 K ∧
      D0 K * (((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
          ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * (R : Matrix (Fin 7) (Fin 7) K)) =
        D0 K := by
    intro y hy
    have hyl : ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * e = e :=
      projU_left c hcmul hcpow hy
    have hyr : e * ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = e :=
      projU_right c hcmul hcpow hy
    have hRR : (R : Matrix (Fin 7) (Fin 7) K) * ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = 1 :=
      Units.mul_inv R
    rw [← hRe]
    constructor
    · calc ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
            (R : Matrix (Fin 7) (Fin 7) K) * (((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * e *
            (R : Matrix (Fin 7) (Fin 7) K))
          = ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
              ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
              ((R : Matrix (Fin 7) (Fin 7) K) * ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) *
              e * (R : Matrix (Fin 7) (Fin 7) K) := by simp only [Matrix.mul_assoc]
        _ = ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
              (((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * e) * (R : Matrix (Fin 7) (Fin 7) K) := by
              rw [hRR]
              simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * e * (R : Matrix (Fin 7) (Fin 7) K) := by
              rw [hyl]
    · calc (((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * e * (R : Matrix (Fin 7) (Fin 7) K)) *
            (((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
            (R : Matrix (Fin 7) (Fin 7) K))
          = ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * e *
              ((R : Matrix (Fin 7) (Fin 7) K) * ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) *
              ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * (R : Matrix (Fin 7) (Fin 7) K) := by
              simp only [Matrix.mul_assoc]
        _ = ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * (e * ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) *
              (R : Matrix (Fin 7) (Fin 7) K) := by
              rw [hRR]
              simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * e * (R : Matrix (Fin 7) (Fin 7) K) := by
              rw [hyr]
  have hF'D : ∀ k ∈ FS.map (conjS h hR).toMonoidHom,
      ((k : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * D0 K = D0 K ∧
        D0 K * ((k : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = D0 K := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
    have hcy : c y = 1 := hy
    have hxk : ((conjS h hR x : ↥(StatedSU 7 (p ^ f) K)) : GL (Fin 7) K) =
        (R⁻¹ : GL (Fin 7) K) * (y : GL (Fin 7) K) * R := by
      rw [conjS_apply, ← hyx]
      rfl
    change ((((conjS h hR x : ↥(StatedSU 7 (p ^ f) K))) : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
        D0 K = D0 K ∧ D0 K *
        ((((conjS h hR x : ↥(StatedSU 7 (p ^ f) K))) : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = D0 K
    rw [hxk, Units.val_mul, Units.val_mul]
    exact hkD y hcy
  have hD0sum : D0 K = (((univ.filter fun x : P₁ => c x = 1).card : K))⁻¹ •
      ∑ y ∈ univ.filter (fun y : P₁ => c y = 1),
        (((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
          ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * (R : Matrix (Fin 7) (Fin 7) K)) := by
    rw [← hRe, he_def]
    unfold projU
    rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  have hcent : ∀ g : ↥(StatedSU 7 (p ^ f) K),
      (∀ k ∈ FS.map (conjS h hR).toMonoidHom, g * k = k * g) →
        ((g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * D0 K =
          D0 K * ((g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) := by
    intro g hg
    rw [hD0sum, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    have hcy : c y = 1 := (Finset.mem_filter.mp hy).2
    have hyS : (⟨(y : GL (Fin 7) K), hmemP₁ y y.2⟩ : ↥(StatedSU 7 (p ^ f) K)) ∈ FS :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨y, show y ∈ F₁ from hcy, rfl⟩)
    have hk : conjS h hR ⟨(y : GL (Fin 7) K), hmemP₁ y y.2⟩ ∈ FS.map (conjS h hR).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨_, hyS, rfl⟩
    have hgk := congrArg (fun z : ↥(StatedSU 7 (p ^ f) K) =>
      ((z : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) (hg _ hk)
    simp only [Subgroup.coe_mul, Units.val_mul, conjS_apply] at hgk
    exact hgk
  exact kerConcl_of_blockU h hQ (PS.map (conjS h hR).toMonoidHom) hP3
    (FS.map (conjS h hR).toMonoidHom) hF'P hF'card hF'D hcent

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

end
