module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ClassExcGen
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.K159.CoverPSL
public import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

namespace ClassExc

private theorem three_pow_four_le_torus {k : Type} [Field k] {ζ : kˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) {n : ℕ} (hn4 : 4 ≤ n) (hn6 : n ≤ 6) :
    3 ^ 4 ≤ Nat.card (torusPSL ζ hζ n).range := by
  obtain ⟨-, -, h⟩ := torusPSL_package (Y := PSL(n + 1, k)) Nat.prime_three (by norm_num) hζo hζ
    (by omega) (φ := MonoidHom.id _) Function.surjective_id (by
      rw [MonoidHom.ker_id]
      exact bot_le)
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) h
  split_ifs with h3
  · have : n ≠ 4 ∧ n ≠ 6 := by
      constructor <;> rintro rfl <;> norm_num at h3
    omega
  · omega

private theorem exists_orderOf_eq_three {F : Type} [Field F] [Finite F] (h3 : 3 ∣ Nat.card F - 1) :
    ∃ ζ : Fˣ, orderOf ζ = 3 ∧ ζ ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 (by rwa [Nat.card_units F])
  exact ⟨ζ, hζ, by rw [← hζ, pow_orderOf_eq_one]⟩

private theorem toGL_mem_SU {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K) {N : ℕ}
    (A : SL(N, K)) (hA : ((A : Matrix (Fin N) (Fin N) K).map hK.bar)ᵀ * A = 1) :
    Matrix.SpecialLinearGroup.toGL A ∈ StatedSU N (p ^ f) K :=
  (mem_unitarySU_iff hK).2 ⟨A.2, hA⟩

private theorem diagonal_unitary {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K)
    {N : ℕ} {d : Fin N → K} (hd : ∀ i, d i ^ (p ^ f + 1) = 1) :
    ((diagonal d).map hK.bar)ᵀ * diagonal d = 1 := by
  rw [diagonal_map (map_zero hK.bar), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [hK.bar_apply, ← pow_succ, hd i]

private theorem neg_one_pow_succ_eq_one {K : Type} [Field K] {q : ℕ} (hq : Odd q) :
    (-1 : K) ^ (q + 1) = 1 := by
  obtain ⟨k, rfl⟩ := hq
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
  simp

private theorem update_neg_one_pow {K : Type} [Field K] {m q : ℕ} (hq : Odd q)
    (i : Fin (m + 1)) :
    ((Function.update (1 : Fin (m + 1) → Kˣ) (Fin.last m) (-1) i : Kˣ) : K) ^ (q + 1) = 1 := by
  by_cases hi : i = Fin.last m
  · subst hi
    simp only [Function.update_self, Units.val_neg, Units.val_one]
    exact neg_one_pow_succ_eq_one hq
  · simp [Function.update_of_ne hi]

end ClassExc

open ClassExc

theorem p3At_A_of_dvd_sub_one {n : ℕ} (hn4 : 4 ≤ n) (hn6 : n ≤ 6) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A n Q).Valid) (h3 : 3 ∣ Q.card - 1) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  set F := GaloisField Q.p Q.exponent with hFdef
  have hQq : Q.p = q := (TauCeti.LieTypeIndex.characteristic_A n Q).symm.trans hchar
  have hFcard : Nat.card F = Q.card := by
    rw [hFdef, GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hF2 : ringChar F ≠ 2 := by
    rw [ringChar.eq F Q.p, hQq]
    exact H.two
  obtain ⟨ζ, hζo, hζ⟩ := exists_orderOf_eq_three (F := F) (by rwa [hFcard])
  set e₁ := e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n Q hv)
  set π : SL(n + 1, F) →* PSL(n + 1, F) := QuotientGroup.mk' (Subgroup.center SL(n + 1, F))
  have hθ : ∀ a, torusPSL ζ hζ n a = π (torusElem ζ hζ (Multiplicative.toAdd a)) := fun _ => rfl
  have h01 : (⟨0, by omega⟩ : Fin (n + 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  refine H.false_of_torus_hom e₁ (torusPSL ζ hζ n) (three_pow_four_le_torus hζo hζ hn4 hn6)
    (fun j => ⟨π (CFSG.RankThree.PartOne.K159.invElem j), ?_⟩)
    (fun j j' hjj => ⟨π (swapElem j j' hjj), ?_, ?_⟩)
    (t := π (negPairElem h01)) ?_ ?_ ?_
  · rw [hθ, toAdd_ofAdd, ← map_inv, ← map_mul, ← map_mul, CFSG.RankThree.PartOne.K159.invElem_conj,
      map_inv]
  · rw [hθ, hθ, toAdd_ofAdd, toAdd_ofAdd, ← map_inv, ← map_mul, ← map_mul, swapElem_conj]
  · rw [hθ, hθ, toAdd_ofAdd, toAdd_ofAdd, ← map_inv, ← map_mul, ← map_mul, swapElem_comm,
      swapElem_conj]
  · intro h
    refine negPairElem_not_mem_center hF2 h01 (i'' := ⟨2, by omega⟩) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]) ?_
    exact (QuotientGroup.eq_one_iff _).1 h
  · rw [← map_pow, negPairElem_sq, map_one]
  · intro a
    rw [hθ]
    exact (commute_of_coe_diagonal (coe_negPairElem h01) (coe_torusElem ζ hζ _)).map π

theorem p3At_twistedA_of_dvd_add_one {n : ℕ} (hn4 : 4 ≤ n) (hn6 : n ≤ 6) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA n Q).Valid) (h3 : 3 ∣ Q.card + 1) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  set d : TauCeti.ValidLieTypeIndex := ⟨.twistedA n Q, hv⟩ with hd
  set p := d.characteristic with hpdef
  set f := d.fieldExponent with hfdef
  haveI : Fact p.Prime := ⟨d.characteristic_prime⟩
  have hpQ : p = Q.p := TauCeti.LieTypeIndex.characteristic_twistedA n Q
  have hfQ : f = Q.exponent := TauCeti.LieTypeIndex.fieldExponent_twistedA n Q
  have hpq : p = q := hchar
  have hf1 : 1 ≤ f := by rw [hfQ]; exact Q.exponent_pos
  have hqQ : p ^ f = Q.card := by rw [hpQ, hfQ, TauCeti.PrimePower.card_def]
  set K := GaloisField p (2 * f) with hKdef
  have hK : UnitaryFieldData p f K := ⟨Fact.out, hf1, GaloisField.card p (2 * f) (by omega)⟩
  haveI := hK.finite
  have hp2 : p ≠ 2 := hpq ▸ H.two
  have hqodd : Odd (p ^ f) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  set e₁ := e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj n Q hv)
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hK.card, pow_mul', sq]
    have h1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
    have : p ^ f * p ^ f - 1 = (p ^ f + 1) * (p ^ f - 1) := by
      obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by omega⟩
      rw [hk]
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    rw [this]
    exact dvd_mul_of_dvd_left (hqQ ▸ h3) _
  obtain ⟨ζ, hζo, hζ⟩ := exists_orderOf_eq_three h3K
  have hζq : ∀ k : ℕ, ((ζ ^ k : Kˣ) : K) ^ (p ^ f + 1) = 1 := by
    intro k
    obtain ⟨c, hc⟩ : 3 ∣ p ^ f + 1 := by rw [hqQ]; exact h3
    have h1 : (ζ ^ k) ^ (p ^ f + 1) = 1 := by
      rw [hc, ← pow_mul, mul_comm k, pow_mul, pow_mul, hζ, one_pow, one_pow]
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  set W : Subgroup SL(n + 1, K) := (StatedSU (n + 1) (p ^ f) K).comap
    Matrix.SpecialLinearGroup.toGL with hW
  set Z := (StatedScalars (Fin (n + 1)) K).subgroupOf (StatedSU (n + 1) (p ^ f) K)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : W →* StatedProj (StatedSU (n + 1) (p ^ f) K), ∀ w : W,
      ρ w = QuotientGroup.mk' Z ⟨Matrix.SpecialLinearGroup.toGL (w : SL(n + 1, K)), w.2⟩ :=
    ⟨(QuotientGroup.mk' Z).comp
      ((Matrix.SpecialLinearGroup.toGL.comp W.subtype).codRestrict _ fun w => w.2),
      fun _ => rfl⟩
  have hρ1 : ∀ w : W, ρ w = 1 → (w : SL(n + 1, K)) ∈ Subgroup.center SL(n + 1, K) := by
    intro w hw
    rw [hρ] at hw
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hw)
    have hc' : ((Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) = (w : SL(n + 1, K)) := congrArg Units.val hc
    rw [Matrix.GeneralLinearGroup.coe_scalar] at hc'
    refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨(c : K), ?_, hc'⟩
    have hdet := congrArg Matrix.det hc'
    rw [Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Matrix.SpecialLinearGroup.det_coe] at hdet
    exact hdet
  have hT : ∀ a, torusElem ζ hζ a ∈ W := fun a => by
    refine toGL_mem_SU hK _ ?_
    rw [coe_torusElem]
    refine diagonal_unitary hK fun i => ?_
    simp only [torusEntries, zmodPowHom_apply]
    exact hζq _
  have hI : ∀ j : Fin n, CFSG.RankThree.PartOne.K159.invElem j ∈ W := fun j => by
    refine toGL_mem_SU hK _ ?_
    have h := congrArg Units.val (CFSG.RankThree.PartOne.K159.toGL_invElem (k := K) j)
    rw [Units.val_mul] at h
    change ((((Matrix.SpecialLinearGroup.toGL (CFSG.RankThree.PartOne.K159.invElem j) :
      GL (Fin (n + 1)) K)) : Matrix (Fin (n + 1)) (Fin (n + 1)) K).map hK.bar)ᵀ *
      ((Matrix.SpecialLinearGroup.toGL (CFSG.RankThree.PartOne.K159.invElem j) :
        GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = 1
    rw [h]
    exact CFSG.RankThree.Classical2.unitary_mul hK (CFSG.RankThree.Classical2.permGL_unitary hK _)
      (CFSG.RankThree.Classical2.diagHom_unitary hK fun i => update_neg_one_pow hqodd i)
  have hSw : ∀ (j j' : Fin n) (hjj : j ≠ j'), swapElem (k := K) j j' hjj ∈ W := fun j j' hjj => by
    refine toGL_mem_SU hK _ ?_
    have h := congrArg Units.val (toGL_swapElem (k := K) j j' hjj)
    rw [Units.val_mul] at h
    change ((((Matrix.SpecialLinearGroup.toGL (swapElem (k := K) j j' hjj) :
      GL (Fin (n + 1)) K)) : Matrix (Fin (n + 1)) (Fin (n + 1)) K).map hK.bar)ᵀ *
      ((Matrix.SpecialLinearGroup.toGL (swapElem (k := K) j j' hjj) :
        GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = 1
    rw [h]
    exact CFSG.RankThree.Classical2.unitary_mul hK
      (CFSG.RankThree.Classical2.diagHom_unitary hK fun i => update_neg_one_pow hqodd i)
      (CFSG.RankThree.Classical2.permGL_unitary hK _)
  have h01 : (⟨0, by omega⟩ : Fin (n + 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hN : negPairElem (k := K) h01 ∈ W := by
    refine toGL_mem_SU hK _ ?_
    rw [coe_negPairElem]
    refine diagonal_unitary hK fun i => ?_
    split_ifs
    · exact neg_one_pow_succ_eq_one hqodd
    · exact one_pow _
  obtain ⟨θ, hθ⟩ : ∃ θ : Multiplicative (Fin n → ZMod 3) →*
      StatedProj (StatedSU (n + 1) (p ^ f) K),
      ∀ a, θ a = ρ ⟨torusElem ζ hζ (Multiplicative.toAdd a), hT _⟩ :=
    ⟨ρ.comp ((torusSL ζ hζ n).codRestrict W fun a => hT _), fun _ => rfl⟩
  have hker : θ.ker ≤ (torusPSL ζ hζ n).ker := fun a ha => by
    rw [MonoidHom.mem_ker, hθ] at ha
    exact (QuotientGroup.eq_one_iff _).2 (hρ1 _ ha)
  have hcard : 3 ^ 4 ≤ Nat.card θ.range := by
    refine (three_pow_four_le_torus hζo hζ hn4 hn6).trans ?_
    rw [← Subgroup.index_ker, ← Subgroup.index_ker]
    exact Subgroup.index_antitone hker
  have hconj : ∀ x y z : W, x * y * x⁻¹ = z → ρ x * ρ y * (ρ x)⁻¹ = ρ z := fun x y z h => by
    rw [← map_inv, ← map_mul, ← map_mul, h]
  have hW : ∀ {x y z : W}, (x : SL(n + 1, K)) * y * (x : SL(n + 1, K))⁻¹ = z → x * y * x⁻¹ = z :=
    fun h => Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]; exact h)
  set tor : Fin n → W := fun j => ⟨torusElem ζ hζ (Pi.single j 1), hT _⟩ with htor
  have htorinv : ∀ j, (tor j)⁻¹ = ⟨(torusElem ζ hζ (Pi.single j 1))⁻¹, W.inv_mem (hT _)⟩ :=
    fun j => Subtype.ext (Subgroup.coe_inv _ _)
  refine H.false_of_torus_hom e₁ θ hcard
    (fun j => ⟨ρ ⟨CFSG.RankThree.PartOne.K159.invElem j, hI j⟩, ?_⟩)
    (fun j j' hjj => ⟨ρ ⟨swapElem j j' hjj, hSw j j' hjj⟩, ?_, ?_⟩)
    (t := ρ ⟨negPairElem h01, hN⟩) ?_ ?_ ?_
  · rw [hθ, toAdd_ofAdd]
    refine (hconj _ (tor j) (tor j)⁻¹ (hW ?_)).trans (map_inv ρ (tor j))
    rw [htorinv]
    exact CFSG.RankThree.PartOne.K159.invElem_conj ζ hζ j
  · rw [hθ, hθ, toAdd_ofAdd, toAdd_ofAdd]
    exact hconj _ (tor j) (tor j') (hW (swapElem_conj ζ hζ j j' hjj))
  · rw [hθ, hθ, toAdd_ofAdd, toAdd_ofAdd]
    refine hconj _ (tor j') (tor j) (hW ?_)
    change swapElem j j' hjj * torusElem ζ hζ (Pi.single j' 1) * (swapElem j j' hjj)⁻¹ =
      torusElem ζ hζ (Pi.single j 1)
    rw [swapElem_comm, swapElem_conj]
  · intro h
    exact negPairElem_not_mem_center (by rw [ringChar.eq K p]; exact hp2) h01
      (i'' := ⟨2, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (hρ1 _ h)
  · rw [← map_pow]
    rw [show (⟨negPairElem h01, hN⟩ : W) ^ 2 = 1 from Subtype.ext (negPairElem_sq h01), map_one]
  · intro a
    rw [hθ]
    refine Commute.map ?_ ρ
    exact Subtype.ext (commute_of_coe_diagonal (coe_negPairElem h01) (coe_torusElem ζ hζ _)).eq

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
