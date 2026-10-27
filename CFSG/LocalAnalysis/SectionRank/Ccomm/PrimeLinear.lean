module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.SectionRank.Ccomm

open Matrix

theorem exists_involution_of_two_dvd {G : Type*} [Group G] [Finite G] (h : 2 ∣ Nat.card G) :
    ∃ g : G, g ≠ 1 ∧ g ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h
  refine ⟨g, fun h1 => ?_, by rw [← hg]; exact pow_orderOf_eq_one g⟩
  rw [h1, orderOf_one] at hg
  exact absurd hg (by norm_num)

theorem exists_involution_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : ∃ g : G', g ≠ 1 ∧ g ^ 2 = 1) : ∃ g : G, g ≠ 1 ∧ g ^ 2 = 1 := by
  obtain ⟨g, hg1, hg2⟩ := h
  refine ⟨e.symm g, fun h1 => hg1 ?_, by rw [← map_pow, hg2, map_one]⟩
  rw [← e.apply_symm_apply g, h1, map_one]

theorem exists_involution_PSL2 (F : Type*) [Field F] :
    ∃ h : ProjectiveSpecialLinearGroup (Fin 2) F, h ≠ 1 ∧ h ^ 2 = 1 := by
  let w : SpecialLinearGroup (Fin 2) F := ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩
  refine ⟨QuotientGroup.mk w, ?_, ?_⟩
  · rw [Ne, QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
    rintro ⟨r, -, hr⟩
    have h01 := congrFun (congrFun hr 0) 1
    simp [w] at h01
  · rw [sq, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
      Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by rw [Fintype.card_fin, neg_one_sq], ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply, Fin.sum_univ_two]

variable {p : ℕ} [hp : Fact p.Prime]

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  have := hp.out.two_le
  omega

theorem neg_one_mem_of_involution (hp2 : p ≠ 2) {J : Subgroup (GL (Fin 2) (ZMod p))}
    {g : SpecialLinearGroup (Fin 2) (ZMod p)} (hg : Matrix.SpecialLinearGroup.toGL g ∈ J)
    (hg1 : (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) ≠ 1)
    (hg2 : (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) ^ 2 = 1) :
    (-1 : GL (Fin 2) (ZMod p)) ∈ J := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff] at hg2
  obtain ⟨r, hr, hrg⟩ := hg2
  rw [Fintype.card_fin] at hr
  have hr' : (r - 1) * (r + 1) = 0 := by linear_combination hr
  have hsq : ((g : Matrix (Fin 2) (Fin 2) (ZMod p)) * g) = r • 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← sq, ← hrg]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  rcases mul_eq_zero.1 hr' with h1 | h1
  · exfalso
    apply hg1
    rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
    rw [show r = 1 by linear_combination h1, one_smul] at hsq
    rcases eq_one_or_neg_one_of_sq_eq_one (two_ne_zero_zmod hp2) g.2 hsq with h | h
    · exact ⟨1, one_pow _, by rw [h]; ext i j; simp [Matrix.scalar_apply]⟩
    · refine ⟨-1, by rw [Fintype.card_fin, neg_one_sq], ?_⟩
      rw [h]
      ext i j
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
      split_ifs <;> simp
  · rw [show r = -1 by linear_combination h1, neg_one_smul] at hsq
    have : Matrix.SpecialLinearGroup.toGL g ^ 2 = -1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, sq]
      exact hsq
    rw [← this]
    exact pow_mem hg 2

theorem neg_one_mem_of_perfect
    (hp2 : p ≠ 2) (J : Subgroup (GL (Fin 2) (ZMod p)))
    [Group.IsPerfect J] (hJ : J ≠ ⊥) : (-1 : GL (Fin 2) (ZMod p)) ∈ J := by
  set J₁ := J.comap Matrix.SpecialLinearGroup.toGL with hJ₁
  have hJ₁map : J₁.map Matrix.SpecialLinearGroup.toGL = J := by
    refine le_antisymm (Subgroup.map_comap_le _ _) fun g hg => ?_
    let g' : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
      ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod p)), det_eq_one_of_perfect J hg⟩
    have hgg : Matrix.SpecialLinearGroup.toGL g' = g := Units.ext rfl
    exact ⟨g', show Matrix.SpecialLinearGroup.toGL g' ∈ J by rw [hgg]; exact hg, hgg⟩
  let e : J₁ ≃* J := (J₁.equivMapOfInjective _ Matrix.SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr hJ₁map)
  have : Group.IsPerfect J₁ := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  set H := J₁.map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p))))
    with hH
  have : Group.IsPerfect H := Group.IsPerfect.map _
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hcen : ∀ g ∈ J₁, g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) := by
      intro g hg
      have : QuotientGroup.mk' _ g ∈ H := Subgroup.mem_map_of_mem _ hg
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have : IsMulCommutative J₁ := ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_center_iff.1 (hcen b b.2) a)⟩⟩
    have : Subsingleton J₁ := Group.IsPerfect.subsingleton_of_isMulCommutative
    apply hJ
    rw [← hJ₁map, Subgroup.eq_bot_of_subsingleton J₁, Subgroup.map_bot]
  have hHnt : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hHne
  have key : (∃ h : H, h ≠ 1 ∧ h ^ 2 = 1) → (-1 : GL (Fin 2) (ZMod p)) ∈ J := by
    rintro ⟨⟨_, ⟨g, hg, rfl⟩⟩, h1, h2⟩
    refine neg_one_mem_of_involution hp2 hg (fun h => h1 (Subtype.ext h)) ?_
    exact congrArg Subtype.val h2
  have hnotcomm : ¬ IsMulCommutative H := fun _ => by
    have : Subsingleton H := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact hHne (Subgroup.eq_bot_of_subsingleton H)
  apply key
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (F := ZMod p) (p := p) (f := 1) (by rw [Nat.card_zmod, pow_one]) H with
    hel | ⟨z, -, -, hcyc⟩ | ⟨z, -, hcard, -⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, t, -, -, N, C, hNn, hNel, -, hCcyc, -, -, hNC⟩ | ⟨m, -, -, ⟨ePSL⟩⟩ | ⟨m, hm, hm2, -⟩
  · exact absurd hel.toIsMulCommutative hnotcomm
  · exact absurd hcyc.isMulCommutative hnotcomm
  · exact exists_involution_of_two_dvd ⟨z, hcard⟩
  · refine exists_involution_of_two_dvd ?_
    rw [Nat.card_congr eA4.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · refine exists_involution_of_two_dvd ?_
    rw [Nat.card_congr eS4.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    decide
  · refine exists_involution_of_two_dvd ?_
    rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
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
    have : Group.IsSolvable H := Group.isSolvable_of_ker_le_range N.subtype
      (QuotientGroup.mk' N) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
    exact Group.IsPerfect.not_isSolvable H this
  · exact exists_involution_of_mulEquiv ePSL (exists_involution_PSL2 _)
  · exfalso
    have := Nat.le_of_dvd one_pos hm2
    omega

end CFSG.SectionRank.Ccomm
