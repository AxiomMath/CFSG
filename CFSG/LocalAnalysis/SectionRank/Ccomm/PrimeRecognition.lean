module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeLinear
public import CFSG.StronglyEmbedded.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.Open.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.SectionRank.Ccomm

open Matrix CFSG.Open

theorem DihedralGroup.subsingleton_of_isPerfect {n : ℕ} [Group.IsPerfect (DihedralGroup n)] :
    Subsingleton (DihedralGroup n) := by
  let f : DihedralGroup n →* Multiplicative (ZMod 2) :=
    { toFun := fun g => match g with
        | .r _ => 1
        | .sr _ => Multiplicative.ofAdd 1
      map_one' := rfl
      map_mul' := by
        rintro (a | a) (b | b) <;>
          simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
            DihedralGroup.sr_mul_sr]
        decide }
  have hrot : ∀ g : DihedralGroup n, ∃ i, g = .r i := by
    rintro (i | i)
    · exact ⟨i, rfl⟩
    · have h := perfect_hom_eq_one f (.sr i)
      have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
      exact absurd h hne
  have : IsMulCommutative (DihedralGroup n) := ⟨⟨fun a b => by
    obtain ⟨i, rfl⟩ := hrot a
    obtain ⟨j, rfl⟩ := hrot b
    rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]⟩⟩
  exact Group.IsPerfect.subsingleton_of_isMulCommutative

variable {p : ℕ} [hp : Fact p.Prime]

theorem isOddPrimePower_of_ne_two (hp2 : p ≠ 2) : GorensteinWalter.IsOddPrimePower p :=
  ⟨p, 1, hp.out, hp.out.odd_of_ne_two hp2, le_rfl, (pow_one p).symm⟩

theorem card_PSL2_zmod (hp2 : p ≠ 2) :
    Nat.card (ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) / 2 := by
  have h := GorensteinWalter.psl2_card_formula (ZMod p)
    (by rw [Nat.card_zmod]; exact isOddPrimePower_of_ne_two hp2)
  rwa [Nat.card_zmod] at h

theorem projective_five_alternating :
    Nonempty (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5) ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
    ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
  refine BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five ?_
  rw [card_PSL2_zmod (by norm_num)]
  norm_num

theorem perfect_PSL2_dichotomy (hp2 : p ≠ 2)
    (H : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) [Group.IsPerfect H]
    (hH : H ≠ ⊥) : Nonempty (H ≃* alternatingGroup (Fin 5)) ∨ H = ⊤ := by
  have hHnt : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hH
  have hnotsolv : ¬ Group.IsSolvable H := Group.IsPerfect.not_isSolvable H
  have hnotcomm : ¬ IsMulCommutative H := fun _ =>
    hnotsolv (Group.isSolvable_of_comm fun a b => mul_comm' a b)
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (F := ZMod p) (p := p) (f := 1) (by rw [Nat.card_zmod, pow_one]) H with
    hel | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨eD⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, t, -, -, N, C, hNn, hNel, -, hCcyc, -, -, hNC⟩ | ⟨m, hm0, hm1, ⟨ePSL⟩⟩ | ⟨m, hm, hm2, -⟩
  · exact absurd hel.toIsMulCommutative hnotcomm
  · exact absurd hcyc.isMulCommutative hnotcomm
  · exfalso
    have : Group.IsPerfect (DihedralGroup z) :=
      Group.IsPerfect.ofSurjective (f := eD.toMonoidHom) eD.surjective
    have : Subsingleton (DihedralGroup z) := DihedralGroup.subsingleton_of_isPerfect
    have : Subsingleton H := eD.injective.subsingleton
    exact hH (Subgroup.eq_bot_of_subsingleton H)
  · exfalso
    have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact hnotsolv (Group.isSolvable_of_isSolvable_injective (f := eA4.toMonoidHom) eA4.injective)
  · exfalso
    have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact hnotsolv (Group.isSolvable_of_isSolvable_injective (f := eS4.toMonoidHom) eS4.injective)
  · exact Or.inl ⟨eA5⟩
  · exfalso
    have : IsMulCommutative N := hNel.toIsMulCommutative
    have : Group.IsSolvable N := Group.isSolvable_of_comm fun a b => mul_comm' a b
    have hmapC : C.map (QuotientGroup.mk' N) = ⊤ := by
      have h := congrArg (Subgroup.map (QuotientGroup.mk' N)) hNC
      rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp C.subtype) := by
      intro q
      have hq : q ∈ C.map (QuotientGroup.mk' N) := hmapC ▸ Subgroup.mem_top q
      obtain ⟨c, hc, rfl⟩ := hq
      exact ⟨⟨c, hc⟩, rfl⟩
    have : IsCyclic (H ⧸ N) := isCyclic_of_surjective _ hsurj
    have : Group.IsSolvable (H ⧸ N) :=
      Group.isSolvable_of_comm fun a b => IsCyclic.isMulCommutative.is_comm.comm a b
    exact hnotsolv (Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))
  · right
    have hm : m = 1 := Nat.dvd_one.1 hm1
    subst hm
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_congr ePSL.toEquiv, card_PSL2_zmod hp2]
    have h := GorensteinWalter.psl2_card_formula (GaloisField p 1)
      (by rw [GaloisField.card p 1 one_ne_zero, pow_one]; exact isOddPrimePower_of_ne_two hp2)
    rwa [GaloisField.card p 1 one_ne_zero, pow_one] at h
  · exfalso
    have := Nat.le_of_dvd one_pos hm2
    omega

theorem toGL_val_of_scalar {R : Type*} [CommRing R] {B : SpecialLinearGroup (Fin 2) R} {r : R}
    (h : scalar (Fin 2) r = (B : Matrix (Fin 2) (Fin 2) R)) :
    ((SpecialLinearGroup.toGL B : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = r • 1 := by
  change (B : Matrix (Fin 2) (Fin 2) R) = r • 1
  rw [← h]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem eq_one_or_neg_one_of_sq {R : Type*} [CommRing R] [IsDomain R] {r : R} (h : r ^ 2 = 1) :
    r = 1 ∨ r = -1 := by
  have h' : (r - 1) * (r + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · left; linear_combination h1
  · right; linear_combination h1

theorem perfect_prime_linear_recognition
    (hp2 : p ≠ 2) (J : Subgroup (GL (Fin 2) (ZMod p)))
    [Group.IsPerfect J] (hJ : J ≠ ⊥) :
    5 ≤ p ∧
      (∀ g : J, g ∈ Subgroup.center J ↔
        (g : GL (Fin 2) (ZMod p)) = 1 ∨ (g : GL (Fin 2) (ZMod p)) = -1) ∧
      IsQuasisimple J ∧
      (∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧ (s = p ∨ s = 5) ∧
        Nonempty (J ⧸ Subgroup.center J ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod s))) ∧
      (p ∣ Nat.card J → J = (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) (ZMod p) →*
          GL (Fin 2) (ZMod p)).range ∧
        Nonempty (J ⧸ Subgroup.center J ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) ∧
      (¬ p ∣ Nat.card J →
        Nonempty (J ⧸ Subgroup.center J ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))) := by
  have hneg := neg_one_mem_of_perfect hp2 J hJ
  have h2 := two_ne_zero_zmod hp2
  let sl : J →* SpecialLinearGroup (Fin 2) (ZMod p) :=
    { toFun := fun g => ⟨((g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)),
        det_eq_one_of_perfect J g.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have hsl : ∀ g : J, SpecialLinearGroup.toGL (sl g) = g := fun _ => Units.ext rfl
  let φ : J →* ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) := (QuotientGroup.mk' _).comp sl
  set H := φ.range with hH
  have : Group.IsPerfect H := Group.IsPerfect.range φ
  have hcen : ∀ g : J, g ∈ Subgroup.center J ↔
      (g : GL (Fin 2) (ZMod p)) = 1 ∨ (g : GL (Fin 2) (ZMod p)) = -1 := by
    intro g
    refine ⟨perfect_center_eq_one_or_neg_one J hJ, fun h => ?_⟩
    rw [Subgroup.mem_center_iff]
    intro h'
    apply Subtype.ext
    rcases h with h | h <;> rw [Subgroup.coe_mul, Subgroup.coe_mul, h] <;> simp
  have hscal : ∀ g : J, sl g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) ↔
      (g : GL (Fin 2) (ZMod p)) = 1 ∨ (g : GL (Fin 2) (ZMod p)) = -1 := by
    intro g
    rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
    constructor
    · rintro ⟨r, hr, hrg⟩
      have hv := toGL_val_of_scalar hrg
      rw [hsl] at hv
      rcases eq_one_or_neg_one_of_sq hr with rfl | rfl
      · left
        exact Units.ext (by rw [hv, one_smul, Units.val_one])
      · right
        exact Units.ext (by rw [hv, neg_one_smul, Units.val_neg, Units.val_one])
    · rintro (h | h)
      · refine ⟨1, one_pow _, ?_⟩
        change _ = ((g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p))
        rw [h, Units.val_one]
        ext i j
        simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
      · refine ⟨-1, by rw [neg_one_sq], ?_⟩
        change _ = ((g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p))
        rw [h, Units.val_neg, Units.val_one]
        ext i j
        simp only [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
        split_ifs <;> simp
  have hker : φ.ker = Subgroup.center J := by
    ext g
    rw [MonoidHom.mem_ker, hcen, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hscal]
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hall : ∀ g : J, g ∈ Subgroup.center J := fun g => by
      rw [← hker, MonoidHom.mem_ker]
      have : φ g ∈ H := ⟨g, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    have : IsMulCommutative J := ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (hall b) a)⟩⟩
    have : Subsingleton J := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact hJ (Subgroup.eq_bot_of_subsingleton J)
  have hHnt : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hHne
  let eJH : J ⧸ Subgroup.center J ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  have hcardZ : Nat.card (Subgroup.center J) = 2 := by
    have hle := (perfect_linear_two_basics J hJ).2.2.2
    have hneg1 : (⟨-1, hneg⟩ : J) ≠ 1 := by
      intro h
      have h' := congrArg
        (fun g : J => ((g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
      simp only [Units.val_neg, Units.val_one, Subgroup.coe_one, Matrix.neg_apply,
        Matrix.one_apply_eq] at h'
      exact h2 (by linear_combination -h')
    have hlt : 1 < Nat.card (Subgroup.center J) := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact ⟨⟨⟨⟨-1, hneg⟩, (hcen _).2 (Or.inr rfl)⟩, 1, fun h => hneg1 (congrArg Subtype.val h)⟩⟩
    omega
  have hcardJ : Nat.card J = 2 * Nat.card H := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J),
      Nat.card_congr eJH.toEquiv, hcardZ, mul_comm]
  have hJSL : H = ⊤ → J = (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) (ZMod p) →*
      GL (Fin 2) (ZMod p)).range := by
    intro hHtop
    refine le_antisymm (fun g hg => ⟨sl ⟨g, hg⟩, hsl ⟨g, hg⟩⟩) ?_
    rintro _ ⟨A, rfl⟩
    have hA : QuotientGroup.mk' _ A ∈ H := hHtop ▸ Subgroup.mem_top _
    obtain ⟨g, hg⟩ := hA
    have hc : (sl g)⁻¹ * A ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) :=
      QuotientGroup.eq.1 hg
    rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin] at hc
    obtain ⟨r, hr, hrg⟩ := hc
    have hv := toGL_val_of_scalar hrg
    have hcJ : SpecialLinearGroup.toGL ((sl g)⁻¹ * A) ∈ J := by
      rcases eq_one_or_neg_one_of_sq hr with rfl | rfl
      · rw [show SpecialLinearGroup.toGL ((sl g)⁻¹ * A) = 1 from
          Units.ext (by rw [hv, one_smul, Units.val_one])]
        exact one_mem J
      · rw [show SpecialLinearGroup.toGL ((sl g)⁻¹ * A) = -1 from
          Units.ext (by rw [hv, neg_one_smul, Units.val_neg, Units.val_one])]
        exact hneg
    have e : SpecialLinearGroup.toGL A = g * SpecialLinearGroup.toGL ((sl g)⁻¹ * A) := by
      rw [map_mul, map_inv, hsl]
      group
    rw [e]
    exact mul_mem g.2 hcJ
  have hcardPSL := card_PSL2_zmod hp2
  have h5 : 5 ≤ p := by
    by_contra h5
    have hp3 : p = 3 ∨ p = 4 := by have := hp.out.two_le; omega
    rcases hp3 with rfl | rfl
    · have : Group.IsSolvable (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3)) := by
        have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
        exact Group.isSolvable_of_isSolvable_injective
          (f := GorensteinWalter.psl2_three_equiv_alternatingGroup.toMonoidHom)
          (MulEquiv.injective _)
      exact Group.IsPerfect.not_isSolvable H inferInstance
    · exact absurd hp.out (by norm_num)
  have hsimple : ∀ {s : ℕ} [Fact s.Prime], 5 ≤ s →
      IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) := fun hs =>
    ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hquasi : ∀ {s : ℕ} [Fact s.Prime], 5 ≤ s →
      Nonempty (J ⧸ Subgroup.center J ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) →
      IsQuasisimple J := by
    rintro s _ hs ⟨e⟩
    have := hsimple hs
    exact ⟨Group.IsPerfect.commutator_eq_top, MulEquiv.isSimpleGroup e⟩
  have hAtop : H = ⊤ →
      Nonempty (J ⧸ Subgroup.center J ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    fun hHtop => ⟨(eJH.trans (MulEquiv.subgroupCongr hHtop)).trans Subgroup.topEquiv⟩
  obtain ⟨eA5'⟩ := projective_five_alternating
  rcases perfect_PSL2_dichotomy hp2 H hHne with hA5 | hHtop
  · obtain ⟨eA5⟩ := hA5
    have e5 : Nonempty (J ⧸ Subgroup.center J ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
      ⟨(eJH.trans eA5).trans eA5'.symm⟩
    have hH60 : Nat.card H = 60 := by
      rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    refine ⟨h5, hcen, hquasi (by norm_num) e5, ⟨5, by norm_num, le_rfl, Or.inr rfl, e5⟩, ?_,
      fun _ => e5⟩
    intro hpJ
    rw [hcardJ, hH60] at hpJ
    have hp5 : p = 5 := by
      have hp' := hp.out
      rw [show (2 * 60 : ℕ) = 2 * (2 * (2 * (3 * 5))) by norm_num] at hpJ
      rcases (Nat.Prime.dvd_mul hp').1 hpJ with h | hpJ
      · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
      rcases (Nat.Prime.dvd_mul hp').1 hpJ with h | hpJ
      · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
      rcases (Nat.Prime.dvd_mul hp').1 hpJ with h | hpJ
      · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
      rcases (Nat.Prime.dvd_mul hp').1 hpJ with h | h
      · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
      · exact (Nat.prime_dvd_prime_iff_eq hp' (by norm_num)).1 h
    subst hp5
    have hHtop : H = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, hH60, hcardPSL]
      norm_num
    exact ⟨hJSL hHtop, hAtop hHtop⟩
  · have ep := hAtop hHtop
    refine ⟨h5, hcen, hquasi h5 ep, ⟨p, hp.out, h5, Or.inl rfl, ep⟩, fun _ => ⟨hJSL hHtop, ep⟩,
      fun hpJ => absurd ?_ hpJ⟩
    rw [hcardJ, (Subgroup.card_eq_iff_eq_top H).2 hHtop, hcardPSL]
    have hev : 2 ∣ p * (p ^ 2 - 1) := by
      have hodd := hp.out.odd_of_ne_two hp2
      have : Even (p ^ 2 - 1) := by
        rcases hodd with ⟨k, rfl⟩
        refine ⟨2 * k ^ 2 + 2 * k, ?_⟩
        ring_nf
        omega
      exact Dvd.dvd.mul_left (even_iff_two_dvd.1 this) p
    rw [Nat.mul_div_cancel' hev]
    exact dvd_mul_right p _

theorem prime_field_unipotent_generation
    (hp2 : p ≠ 2) (J : Subgroup (GL (Fin 2) (ZMod p)))
    [Group.IsPerfect J] (hJ : J ≠ ⊥) (hpJ : p ∣ Nat.card J) :
    5 ≤ p ∧ J = (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) (ZMod p) →*
      GL (Fin 2) (ZMod p)).range := by
  obtain ⟨h5, -, -, -, h, -⟩ := perfect_prime_linear_recognition hp2 J hJ
  exact ⟨h5, (h hpJ).1⟩

end CFSG.SectionRank.Ccomm
