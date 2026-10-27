module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUQ8Heis
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUQ8Mat

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
  CFSG.HardMathSupport.Timmesfeld.CrossChar.HeisAux
open scoped Fin.NatCast

section Abstract

variable {G : Type*} [Group G]

theorem pow_inv_mul_pow_fin {a : G} (ha : a ^ 3 = 1) (s t : Fin 3) :
    (a ^ (s : ℕ))⁻¹ * a ^ (t : ℕ) = a ^ ((t - s : Fin 3) : ℕ) := by
  rw [inv_mul_eq_iff_eq_mul, ← pow_add, pow_eq_pow_mod ((s : ℕ) + ((t - s : Fin 3) : ℕ)) ha,
    pow_eq_pow_mod (t : ℕ) ha]
  congr 1
  have h1 := s.is_lt
  have h2 := t.is_lt
  rw [Fin.val_sub]
  omega

end Abstract

variable {L : Type} [Field L] (h₀ : UnitaryFieldData 2 1 L) (ω : Lˣ) (hω3 : ω ^ 3 = 1)

abbrev PU : Type :=
  primeFormP h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)

theorem scalar_eq_one {z : Lˣ} (h : GeneralLinearGroup.scalar (Fin 3) z = 1) : z = 1 := by
  have := congrArg (fun g : GL (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L) 0 0) h
  exact Units.ext (by simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this)

@[expose] noncomputable def sX : gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) :=
  ⟨Xg ω, Xg_mem ω h₀ hω3⟩

@[expose] noncomputable def sP : gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) :=
  ⟨Pg, Pg_mem h₀⟩

@[expose] noncomputable def aE : PU h₀ := QuotientGroup.mk (sX h₀ ω hω3)

@[expose] noncomputable def bE : PU h₀ := QuotientGroup.mk (sP h₀)

theorem aE_pow : aE h₀ ω hω3 ^ 3 = 1 := by
  rw [aE, ← QuotientGroup.mk_pow]
  have : sX h₀ ω hω3 ^ 3 = 1 := Subtype.ext (Xg_pow_three ω hω3)
  rw [this]
  rfl

theorem bE_pow : (bE h₀ : PU h₀) ^ 3 = 1 := by
  rw [bE, ← QuotientGroup.mk_pow]
  have : sP h₀ ^ 3 = 1 := Subtype.ext Pg_pow_three
  rw [this]
  rfl

theorem norm_eq_one_of_cube {c : L} (hc : c ^ 3 = 1) : h₀.norm c = 1 := by
  rw [h₀.norm_eq_pow]
  norm_num
  exact hc

theorem norm_inv_eq_one (hω3 : ω ^ 3 = 1) : h₀.norm ((ω⁻¹ : Lˣ) : L) = 1 :=
  norm_eq_one_of_cube h₀ (by rw [← Units.val_pow_eq_pow_val, inv_pow, hω3, inv_one]; rfl)

theorem ab_comm : aE h₀ ω hω3 * bE h₀ = bE h₀ * aE h₀ ω hω3 := by
  rw [aE, bE, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  refine ⟨ω⁻¹, norm_inv_eq_one h₀ ω hω3, by rw [inv_pow, hω3, inv_one], ?_⟩
  change (((Xg ω : GL (Fin 3) L) * Pg)⁻¹ * (Pg * Xg ω) : GL (Fin 3) L) =
    GeneralLinearGroup.scalar (Fin 3) ω⁻¹
  rw [Xg_mul_Pg ω hω3, map_inv]
  group

@[expose] noncomputable def eP (p : Fin 3 × Fin 3) : PU h₀ :=
  aE h₀ ω hω3 ^ (p.1 : ℕ) * bE h₀ ^ (p.2 : ℕ)

theorem eP_sub (p q : Fin 3 × Fin 3) :
    (eP h₀ ω hω3 q)⁻¹ * eP h₀ ω hω3 p = eP h₀ ω hω3 (p - q) := by
  have ha := aE_pow h₀ ω hω3
  have hb := bE_pow h₀
  have hab : Commute (aE h₀ ω hω3) (bE h₀) := ab_comm h₀ ω hω3
  have hc : Commute (aE h₀ ω hω3 ^ (q.1 : ℕ)) (bE h₀ ^ (q.2 : ℕ)) := hab.pow_pow _ _
  have h1 : Commute ((aE h₀ ω hω3 ^ (q.1 : ℕ))⁻¹ * aE h₀ ω hω3 ^ (p.1 : ℕ))
      ((bE h₀ ^ (q.2 : ℕ))⁻¹) :=
    (hc.inv_left.inv_right).mul_left ((hab.pow_pow _ _).inv_right)
  unfold eP
  calc (aE h₀ ω hω3 ^ (q.1 : ℕ) * bE h₀ ^ (q.2 : ℕ))⁻¹ *
        (aE h₀ ω hω3 ^ (p.1 : ℕ) * bE h₀ ^ (p.2 : ℕ))
      = (bE h₀ ^ (q.2 : ℕ))⁻¹ * ((aE h₀ ω hω3 ^ (q.1 : ℕ))⁻¹ * aE h₀ ω hω3 ^ (p.1 : ℕ)) *
          bE h₀ ^ (p.2 : ℕ) := by simp only [_root_.mul_inv_rev, mul_assoc]
    _ = ((aE h₀ ω hω3 ^ (q.1 : ℕ))⁻¹ * aE h₀ ω hω3 ^ (p.1 : ℕ)) * (bE h₀ ^ (q.2 : ℕ))⁻¹ *
          bE h₀ ^ (p.2 : ℕ) := by rw [h1.symm.eq]
    _ = ((aE h₀ ω hω3 ^ (q.1 : ℕ))⁻¹ * aE h₀ ω hω3 ^ (p.1 : ℕ)) *
          ((bE h₀ ^ (q.2 : ℕ))⁻¹ * bE h₀ ^ (p.2 : ℕ)) := by rw [mul_assoc]
    _ = aE h₀ ω hω3 ^ ((p - q).1 : ℕ) * bE h₀ ^ ((p - q).2 : ℕ) := by
      rw [pow_inv_mul_pow_fin ha q.1 p.1, pow_inv_mul_pow_fin hb q.2 p.2, Prod.fst_sub,
        Prod.snd_sub]

theorem eP_eq_mk (p : Fin 3 × Fin 3) :
    eP h₀ ω hω3 p = QuotientGroup.mk (⟨Xg ω ^ (p.1 : ℕ) * Pg ^ (p.2 : ℕ),
      mul_mem (pow_mem (Xg_mem ω h₀ hω3) _) (pow_mem (Pg_mem h₀) _)⟩ :
        gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) := by
  unfold eP aE bE
  rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul]
  congr 1

theorem W_to_AB {g h : GL (Fin 3) L} {d : Lˣ} (hW : W g h d) :
    g * h = h * g * GeneralLinearGroup.scalar (Fin 3) d := by
  unfold W at hW
  rw [mul_inv_eq_iff_eq_mul] at hW
  rw [hW, mul_assoc, mul_assoc, GeneralLinearGroup.scalar_commute d g]

theorem centL (hω1 : ω ≠ 1) (p : Fin 3 × Fin 3) (hp : p ≠ (0, 0)) {r : PU h₀}
    (hr2 : r ^ 2 = 1) (hc : r * eP h₀ ω hω3 p = eP h₀ ω hω3 p * r) : r = 1 := by
  have : CharP L 2 := h₀.charP
  obtain ⟨rr, rfl⟩ := QuotientGroup.mk_surjective r
  set S : Lˣ →* GL (Fin 3) L := GeneralLinearGroup.scalar (Fin 3) with hS
  have hSc : ∀ (z : Lˣ) (g : GL (Fin 3) L), S z * g = g * S z := fun z g =>
    GeneralLinearGroup.scalar_commute z g
  set Y : GL (Fin 3) L := Xg ω ^ (p.1 : ℕ) * Pg ^ (p.2 : ℕ) with hY
  have hYmem : Y ∈ gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) :=
    mul_mem (pow_mem (Xg_mem ω h₀ hω3) _) (pow_mem (Pg_mem h₀) _)
  set yy : gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := ⟨Y, hYmem⟩ with hyy
  rw [eP_eq_mk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
  obtain ⟨ζ, -, hζ3, hζ⟩ := hc
  have hζ' : (yy : GL (Fin 3) L) * rr = rr * yy * S ζ := by
    have h1 : (((rr * yy)⁻¹ * (yy * rr) : gramSU h₀ ((1 : GL (Fin 3) L) :
        Matrix (Fin 3) (Fin 3) L)) : GL (Fin 3) L) = S ζ := hζ
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc (yy : GL (Fin 3) L) * rr = ((rr : GL (Fin 3) L) * yy) * (((rr : GL (Fin 3) L) * yy)⁻¹ *
          ((yy : GL (Fin 3) L) * rr)) := by group
      _ = _ := by rw [h1]
  have hr2' : (QuotientGroup.mk (rr ^ 2) : PU h₀) = 1 := by
    rw [QuotientGroup.mk_pow]
    exact hr2
  obtain ⟨d, -, -, hd⟩ := (QuotientGroup.eq_one_iff _).1 hr2'
  have hd' : (rr : GL (Fin 3) L) * rr = S d := by
    rw [← pow_two]
    exact hd
  have hζ2 : ζ * ζ = 1 := by
    have h1 : (yy : GL (Fin 3) L) * ((rr : GL (Fin 3) L) * rr) =
        ((rr : GL (Fin 3) L) * rr) * yy * (S ζ * S ζ) := by
      calc (yy : GL (Fin 3) L) * ((rr : GL (Fin 3) L) * rr)
          = ((yy : GL (Fin 3) L) * rr) * rr := (mul_assoc _ _ _).symm
        _ = ((rr : GL (Fin 3) L) * yy * S ζ) * rr := by rw [hζ']
        _ = (rr : GL (Fin 3) L) * yy * (S ζ * rr) := by rw [mul_assoc (rr * (yy : GL (Fin 3) L))]
        _ = (rr : GL (Fin 3) L) * yy * (rr * S ζ) := by rw [hSc ζ rr]
        _ = (rr : GL (Fin 3) L) * ((yy : GL (Fin 3) L) * rr) * S ζ := by simp only [mul_assoc]
        _ = (rr : GL (Fin 3) L) * (rr * yy * S ζ) * S ζ := by rw [hζ']
        _ = ((rr : GL (Fin 3) L) * rr) * yy * (S ζ * S ζ) := by simp only [mul_assoc]
    rw [hd', hSc d yy] at h1
    have h2 : S ζ * S ζ = 1 := mul_eq_left.mp h1.symm
    rw [← map_mul] at h2
    exact scalar_eq_one h2
  have hζ1 : ζ = 1 := by
    calc ζ = ζ * (ζ * ζ) := by rw [hζ2, mul_one]
      _ = ζ ^ 3 := (pow_three ζ).symm
      _ = 1 := hζ3
  rw [hζ1, map_one, mul_one] at hζ'
  set R : Matrix (Fin 3) (Fin 3) L := ((rr : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) with hR
  have hRB : (Y : Matrix (Fin 3) (Fin 3) L) * R = R * Y := by
    have := congrArg (fun g : GL (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L)) hζ'
    simpa [Units.val_mul] using this
  have hR2 : R ^ 2 = (d : L) • (1 : Matrix (Fin 3) (Fin 3) L) := by
    have := congrArg (fun g : GL (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L)) hd'
    simp only [Units.val_mul, hS, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at this
    rw [pow_two, hR, this, Matrix.smul_one_eq_diagonal]
  have key : ∀ (A' : GL (Fin 3) L) (c' : Lˣ), c' ^ 3 = 1 → c' ≠ 1 →
      A' * Y = Y * A' * S c' → ∃ x : L, R = x • (1 : Matrix (Fin 3) (Fin 3) L) :=
    fun A' c' hc3 hc1 hAB' => scalar_of_sq_scalar hc3 hc1 hAB' hRB hR2
  obtain ⟨x, hx⟩ : ∃ x : L, R = x • (1 : Matrix (Fin 3) (Fin 3) L) := by
    have hω3' : (ω⁻¹) ^ 3 = 1 := by rw [inv_pow, hω3, inv_one]
    have hω1' : ω⁻¹ ≠ 1 := fun h => hω1 (inv_eq_one.mp h)
    by_cases hb : (p.2 : ℕ) = 0
    · have hp1 : (p.1 : ℕ) ≠ 0 := fun h => hp (Prod.ext (Fin.ext h) (Fin.ext hb))
      have hW := WB_Yh (A := Xg ω) (B := Pg) (Xg_mul_Pg ω hω3) p
      refine key Pg ((ω⁻¹) ^ (p.1 : ℕ)) ?_ ?_ (W_to_AB hW)
      · rw [← pow_mul, mul_comm, pow_mul, hω3', one_pow]
      · intro h
        exact hp1 (pow_inj3 hω3' hω1' p.1.2 (by norm_num) (h.trans (pow_zero _).symm))
    · have hW := WA_Yh (A := Xg ω) (B := Pg) (Xg_mul_Pg ω hω3) p
      refine key (Xg ω) (ω ^ (p.2 : ℕ)) ?_ ?_ (W_to_AB hW)
      · rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
      · intro h
        exact hb (pow_inj3 hω3 hω1 p.2.2 (by norm_num) (h.trans (pow_zero _).symm))
  have hdet : R.det = 1 := rr.2.2
  have hx3 : x ^ 3 = 1 := by
    rw [hx] at hdet
    simpa using hdet
  have hx0 : x ≠ 0 := fun h => by rw [h] at hx3; simp at hx3
  have hunit := rr.2.1
  change (R.map h₀.bar)ᵀ * ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * R =
    ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) at hunit
  rw [hx, Units.val_one] at hunit
  have hnorm : h₀.norm x = 1 := by
    have h1 := congrFun (congrFun hunit 0) 0
    simp [Matrix.smul_apply, Matrix.transpose_apply] at h1
    rw [UnitaryFieldData.norm]
    linear_combination h1
  refine (QuotientGroup.eq_one_iff _).2 ⟨Units.mk0 x hx0, hnorm, ?_, ?_⟩
  · apply Units.ext
    simpa using hx3
  · apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0,
      ← Matrix.smul_one_eq_diagonal, ← hx]

include hω3 in
theorem eq_bot_of_normal_coprime (hω1 : ω ≠ 1) (R : Subgroup (PU h₀)) [R.Normal]
    (hR : ∀ r ∈ R, Nat.Coprime 3 (orderOf r)) : R = ⊥ := by
  classical
  by_contra hne
  have hfinL : Finite L := h₀.finite
  have hfin : Finite (PU h₀) := by unfold PU primeFormP; infer_instance
  have : Fintype (PU h₀) := Fintype.ofFinite _
  have h72 : Nat.card (PU h₀) = 72 := card_primeFormP_three_two h₀ (by norm_num)
  have hdvd72 : Nat.card R ∣ 72 := h72 ▸ Subgroup.card_subgroup_dvd_card R
  have h3 : ¬ 3 ∣ Nat.card R := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 3 h3
    have h' : Nat.Coprime 3 3 := by simpa [Subgroup.orderOf_coe, hx] using hR x x.2
    exact absurd h' (by norm_num)
  have hcop : Nat.Coprime (Nat.card R) 9 := by
    have h1 : Nat.Coprime (Nat.card R) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
    simpa using Nat.Coprime.pow_right 2 h1
  have h8 : Nat.card R ∣ 8 :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop (by simpa using hdvd72)
  have hgt : 1 < Nat.card R := (Subgroup.one_lt_card_iff_ne_bot R).2 hne
  have h2dvd : 2 ∣ Nat.card R := by
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show Nat.card R ∣ 2 ^ 3 by simpa using h8)
    rcases k with _ | k
    · rw [pow_zero] at hkeq
      omega
    · exact ⟨2 ^ k, by rw [hkeq]; ring⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2dvd
  set r : PU h₀ := (x : PU h₀) with hr
  have hord : orderOf r = 2 := (Subgroup.orderOf_coe x).trans hx
  have hr2 : r ^ 2 = 1 := by
    have := pow_orderOf_eq_one r
    rwa [hord] at this
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hrR : r ∈ R := x.2
  set Rf : Finset (PU h₀) := Finset.univ.filter (fun g => g ∈ R) with hRf
  have hRfc : Rf.card = Nat.card R := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hS : (Rf.erase 1).card ≤ 7 := by
    rw [Finset.card_erase_of_mem (by simp [hRf, R.one_mem])]
    have := Nat.le_of_dvd (by norm_num) h8
    omega
  obtain ⟨p, -, q, -, hpq, hfpq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Finset.univ : Finset (Fin 3 × Fin 3))) (t := Rf.erase 1)
    (f := fun p : Fin 3 × Fin 3 => eP h₀ ω hω3 p * r * (eP h₀ ω hω3 p)⁻¹)
    (by simp; omega) (by
      intro p _
      refine Finset.mem_erase.2 ⟨?_, ?_⟩
      · intro h
        apply hr1
        have := congrArg (fun z => (eP h₀ ω hω3 p)⁻¹ * z * eP h₀ ω hω3 p) h
        simpa [mul_assoc] using this
      · simp only [hRf, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Subgroup.Normal.conj_mem inferInstance r hrR _)
  have hcomm : (eP h₀ ω hω3 q)⁻¹ * eP h₀ ω hω3 p * r =
      r * ((eP h₀ ω hω3 q)⁻¹ * eP h₀ ω hω3 p) := by
    calc (eP h₀ ω hω3 q)⁻¹ * eP h₀ ω hω3 p * r
        = (eP h₀ ω hω3 q)⁻¹ * (eP h₀ ω hω3 p * r * (eP h₀ ω hω3 p)⁻¹) * eP h₀ ω hω3 p := by
          group
      _ = (eP h₀ ω hω3 q)⁻¹ * (eP h₀ ω hω3 q * r * (eP h₀ ω hω3 q)⁻¹) * eP h₀ ω hω3 p := by
          rw [hfpq]
      _ = r * ((eP h₀ ω hω3 q)⁻¹ * eP h₀ ω hω3 p) := by group
  have hne0 : p - q ≠ (0, 0) := fun h => hpq (sub_eq_zero.mp (by rw [h]; rfl))
  exact hr1 (centL h₀ ω hω3 hω1 (p - q) hne0 hr2 (by rw [← eP_sub]; exact hcomm.symm))

end CFSG.HardMathSupport.Solomon.Coordinator
