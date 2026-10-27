module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxSpC
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxL2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxSpA
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxSpB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutCard

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace IdxSp

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup CFSG.ComponentClassification.CatFactsSp4

variable {K : Type} [Field K]

theorem sl2_sq_lt {q : ℕ} (hq : 2 ≤ q) : (q * (q ^ 2 - 1)) ^ 2 < q ^ 2 * ((q ^ 2) ^ 2 - 1) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (q ^ 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  nlinarith [mul_pos (by positivity : (0 : ℤ) < (q : ℤ) ^ 2)
    (by nlinarith : (0 : ℤ) < 2 * (q : ℤ) ^ 2 - 2)]

theorem fixCat_psp [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) :
    Idx.FixCat (StatedProj (StatedSp 2 K)) ((p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2) := by
  intro α τ hα2 hα1 _ _ X hXp hXd hXα hXτ
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hrc : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  have : Fintype K := Fintype.ofFinite K
  have hq3 : 3 ≤ p ^ f := by
    have := hp.two_le
    calc 3 ≤ p := by omega
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hev : 2 ∣ ((p ^ f) ^ 2) ^ 2 - 1 := by
    have h4 : Odd (((p ^ f) ^ 2) ^ 2) := ((hp.odd_of_ne_two hp2).pow.pow).pow
    obtain ⟨r, hr⟩ := h4
    exact ⟨r, by omega⟩
  have h2n : (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 * 2 =
      (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) :=
    Nat.div_mul_cancel (dvd_mul_of_dvd_right hev _)
  have hXn : (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 ≤ Nat.card X :=
    Nat.le_of_dvd Nat.card_pos hXd
  obtain ⟨-, -, hinj⟩ := CFSG.RankThree.PartOne.spProj_facts (r := 2) hp hf hK le_rfl
    (fun h => by omega)
  have hout : α ∉ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range := by
    rintro ⟨u, rfl⟩
    have hu1 : u ≠ 1 := fun h => hα1 (by rw [h, map_one])
    have huu : u * u = 1 := hinj (by rw [map_mul, hα2, map_one])
    have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
    have hXC : X ≤ centralizer {u} := fun x hx => by
      rw [mem_centralizer_singleton_iff]
      have h1 := hXα x hx
      rw [MulAut.conj_apply] at h1
      calc x * u = u * x * u⁻¹ * u := by rw [h1]
        _ = u * x := by group
    have h1 := two_mul_card_le_of_inner hodd hu2 hXC hXp
    rw [GorensteinWalter.sl2_card_formula, hK] at h1
    have h4 := sl2_sq_lt (q := p ^ f) (by omega)
    omega
  have hXfix : X ≤ fixOf α := fun x hx => hXα x hx
  obtain ⟨A, hαA, d, hd0, hdsq, hAA, hμ⟩ := exists_typeII_of_admissible hp hp2 hf hK α hα2 hout
    (hXd.trans (card_dvd_of_le hXfix))
  set θ := conjSp 2 K A with hθ
  have hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g) := fun g => by rw [hαA]; rfl
  have hXle : X ≤ (fixOf θ).map (proj 2 K) := perfect_le_map_fixOf θ hθα hXα hXp
  obtain ⟨hQ, hcardθ⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A hd0 hdsq hAA hμ
  have hZ : ∀ z ∈ spScalars 2 K, θ z = z := by
    intro z hz
    have hz' := hz
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
    have hcomm := Subgroup.mem_center_iff.mp hz' (A : GL (Fin 2 ⊕ Fin 2) K)
    exact Subtype.ext (by rw [hθ, coe_conjSp, hcomm, mul_inv_cancel_right])
  have hcm := card_map_fixOf_mul_two h2 θ hZ
  have hmap : Nat.card ((fixOf θ).map (proj 2 K)) =
      (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 := by
    have h1 := hcm
    rw [hcardθ] at h1
    omega
  have hXeq : X = (fixOf θ).map (proj 2 K) := by
    apply eq_of_le_of_card_ge hXle
    rw [hmap]
    exact hXn
  obtain ⟨B, σ, hτ⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hrc le_rfl τ
  set Bm := ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hBm
  set Am := ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hAm
  have hBg : ∀ g ∈ fixOf θ,
      Bm * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ =
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Bm ∨
      Bm * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ =
        -(((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Bm) := by
    intro g hg
    have h1 : τ (proj 2 K g) = proj 2 K g := hXτ _ (by rw [hXeq]; exact mem_map_of_mem _ hg)
    rw [hτ, MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h1
    have key : (((conjSp 2 K B (fieldSp 2 K σ g) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Bm =
        Bm * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ := by
      rw [coe_conjSp, hBm, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, coe_fieldSp]
    rcases eq_or_eq_neg_of_proj_eq h1 with h | h
    · left
      rw [← key, ← h]
    · right
      rw [← key, h, Matrix.neg_mul, neg_neg]
  set Y : Subgroup (SpecialLinearGroup (Fin 4) K) := (fixOf θ).map psi with hY
  have hYA : ∀ y ∈ Y, (y : Matrix (Fin 4) (Fin 4) K) * R4 Am = R4 Am * y := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : θ g = g := hg
    have hgA : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Am =
        Am * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      have h3 := congrArg (fun y : StatedSp 2 K => (y : GL (Fin 2 ⊕ Fin 2) K)) hg'
      simp only [hθ, coe_conjSp] at h3
      have h4 : (g : GL (Fin 2 ⊕ Fin 2) K) * (A : GL (Fin 2 ⊕ Fin 2) K) =
          (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) := by
        calc (g : GL (Fin 2 ⊕ Fin 2) K) * (A : GL (Fin 2 ⊕ Fin 2) K) =
            (A : GL (Fin 2 ⊕ Fin 2) K) * g * (A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ * A := by rw [h3]
          _ = (A : GL (Fin 2 ⊕ Fin 2) K) * g := by group
      have h5 := congrArg (fun M : GL (Fin 2 ⊕ Fin 2) K =>
        (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h4
      simpa only [Units.val_mul] using h5
    rw [coe_psi, ← map_mul, hgA, map_mul]
  have hYp : ⁅Y, Y⁆ = Y := by
    have hperf : ⁅fixOf θ, fixOf θ⁆ = fixOf θ := Subgroup.isPerfect_iff.mp hQ.1
    rw [hY, ← map_commutator, hperf]
  have hYc : Nat.card K ^ 2 * ((Nat.card K ^ 2) ^ 2 - 1) ≤ Nat.card Y := by
    rw [hY, card_map_of_injective psi_injective, hcardθ, hK]
  have hBY : ∀ y ∈ Y, R4 Bm * (y : Matrix (Fin 4) (Fin 4) K).map σ.toRingHom =
      y * R4 Bm ∨ R4 Bm * (y : Matrix (Fin 4) (Fin 4) K).map σ.toRingHom = -(y * R4 Bm) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [coe_psi, ← R4_map, ← map_mul, ← map_mul, ← map_neg]
    rcases hBg g hg with h | h
    · exact Or.inl (congrArg R4 h)
    · exact Or.inr (congrArg R4 h)
  have hA4 : R4 Am * R4 Am = d • 1 := by rw [← map_mul, hAA, map_smul, map_one]
  have hns : ¬ IsSquare d := by
    rintro ⟨r, hr⟩
    exact hdsq r (by rw [hr, sq])
  have hB4 : IsUnit (R4 Bm).det := by
    rw [det_R4, hBm, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  obtain ⟨hσ, x, z, hxz⟩ := eq_of_semilinear h2 hns hA4 hYA hYp hYc hB4 σ.toRingHom hBY
  have hBeq : Bm = x • 1 + z • Am :=
    R4.injective (by rw [hxz, map_add, map_smul, map_smul, map_one])
  have hx0 := mul_eq_zero_of_mem_gsp h2 hd0 hdsq hAA hμ hBeq (multiplierUnit_spec B)
  have hσ1 : σ = 1 := RingEquiv.ext fun c => hσ c
  rw [hτ, hσ1, map_one, mul_one]
  rcases mul_eq_zero.mp hx0 with hx | hz
  · right
    rw [hαA]
    exact conjAut_eq_of_smul A B (by rw [← hBm, hBeq, hx, zero_smul, zero_add])
  · left
    exact conjAut_eq_one_of_scalar B (by rw [← hBm, hBeq, hz, zero_smul, add_zero])

variable {H : Type} [Group H] [Finite H] (h : GSThmB.Hyp52 H)

theorem T_le_case_psp {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hJ : Blueprint.LieModel (GSThmB.OddBar h.J) .PSL 2 p (2 * f))
    (hKa : conjugate h.K h.a = h.K) (hK : Blueprint.LieModel (GSThmB.OddBar h.K) .PSp 2 p f) :
    h.T ≤ zpowers h.a ⊔ h.B := by
  apply Idx.T_le_of_fixCat h hKa
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hK
  have hc : Nat.card (GSThmB.OddBar h.J) = (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 := by
    rw [Idx.card_of_lieModel_psl2 hp2 hJ, mul_comm 2 f, pow_mul]
  rw [hc]
  exact Idx.FixCat.of_mulEquiv e (fixCat_psp hp hp2 hf hF)

end IdxSp

end CFSG.ComponentClassification.CatFactsL4U4
