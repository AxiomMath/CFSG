module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJPoints
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJProj
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJSyl

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.FrameJ

open CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer CFSG.EvenSporadicStandard.Wong77.Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_sylow_fi22
    (S : Sylow 2 CFSG.Sporadic.Fi22.J) :
    Nat.card (S : Subgroup CFSG.Sporadic.Fi22.J) = 131072 := by
  have hT : IsPGroup 2 (CFSG.Sporadic.Fi22.slvl 0) :=
    IsPGroup.of_card (n := 17) (by rw [CFSG.Sporadic.Fi22.card_slvl_zero]; norm_num)
  have hidx : ¬ 2 ∣ (CFSG.Sporadic.Fi22.slvl 0).index := by
    rw [CFSG.Sporadic.Fi22.slvl_index]
    decide
  rw [Sylow.card_eq_multiplicity S, ← Sylow.card_eq_multiplicity (hT.toSylow hidx),
    IsPGroup.toSylow_coe, CFSG.Sporadic.Fi22.card_slvl_zero]

theorem fjPt_comm_d (i : Fin 23) :
    fjPt i * d = d * fjPt i := by
  have := fjPt_comm i 0
  rwa [fjPt_zero] at this

@[expose] noncomputable def fjHom :
    Multiplicative Word →* J := by
  refine frameHom fjPt ?_ ?_
  · exact fjPt_sq
  · exact fjPt_comm

theorem fjHom_eVec (i : Fin 23) :
    fjHom (eVec i) = fjPt i := by
  unfold fjHom
  exact frameHom_eVec _ _ _ i

theorem fjHom_eq_one_iff (w : Word) :
    fjHom (Multiplicative.ofAdd w) = 1 ↔ w ∈ golayCode := by
  unfold fjHom
  refine frameHom_ofAdd_eq_one_iff fjPt ?_ ?_ ?_ ?_ ?_ ?_ w
  · exact fjPt_rel
  · exact fjPt_ne_one
  · exact fun i j hij => fjPt_mul_ne_one hij
  · exact fun i j k hij hik hjk => fjPt_mul_mul_ne_one hij hik hjk

theorem fjHom_mem_Cd
    (w : Multiplicative Word) : fjHom w ∈ Cd := by
  rw [mem_Cd, ← fjPt_zero, ← fjHom_eVec 0, ← map_mul, ← map_mul, mul_comm]

@[expose] noncomputable def fjProj :
    Multiplicative Word →* CFSG.Sporadic.Fi22.J where
  toFun w := piC ⟨fjHom w, fjHom_mem_Cd w⟩
  map_one' := by
    have : (⟨fjHom 1, fjHom_mem_Cd 1⟩ : Cd) = 1 := Subtype.ext (map_one fjHom)
    rw [this, map_one]
  map_mul' a b := by
    have : (⟨fjHom (a * b), fjHom_mem_Cd (a * b)⟩ : Cd) =
        ⟨fjHom a, fjHom_mem_Cd a⟩ * ⟨fjHom b, fjHom_mem_Cd b⟩ := Subtype.ext (map_mul fjHom a b)
    rw [this, map_mul]

theorem isPGroup_word : IsPGroup 2 (Multiplicative Word) :=
  IsPGroup.of_card (n := 23) (by
    rw [Nat.card_congr (Multiplicative.toAdd (α := Word)), Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin])

@[expose] noncomputable def fjQ
    (i : Fin 23) : Cd :=
  ⟨fjPt i, mem_Cd.2 (fjPt_comm_d i)⟩

theorem fjProj_eVec
    (i : Fin 23) :
    fjProj (eVec i) = piC (fjQ i) :=
  congrArg piC (Subtype.ext (fjHom_eVec i))

theorem fjPt_star
    {i : Fin 23} (hi : i ≠ 0) :
    fjPt i ∈ star :=
  ⟨fjPt_mem i, fun h => fjPt_ne hi (h.trans fjPt_zero.symm), fjPt_comm_d i⟩

theorem fjQ_eq_ofStar
    {i : Fin 23} (hi : i ≠ 0) :
    fjQ i = ofStar ⟨fjPt i, fjPt_star hi⟩ :=
  Subtype.ext rfl

theorem exists_pt_of_image_mem
    {S : Sylow 2 CFSG.Sporadic.Fi22.J}
    (hES : ∀ i : Fin 23, piC (fjQ i) ∈ (S : Subgroup CFSG.Sporadic.Fi22.J)) {x : J}
    (hx : x ∈ star) (hxS : piC (ofStar ⟨x, hx⟩) ∈ (S : Subgroup CFSG.Sporadic.Fi22.J)) :
    ∃ i : Fin 23, i ≠ 0 ∧ fjPt i = x := by
  have hD : ∀ i : {i : Fin 23 // i ≠ 0}, piC (fjQ i.1) ∈ CFSG.Sporadic.Fi22.D := fun i => by
    rw [fjQ_eq_ofStar i.2]
    exact piC_ofStar_mem_D _
  let f : {i : Fin 23 // i ≠ 0} → {y : CFSG.Sporadic.Fi22.J //
      y ∈ CFSG.Sporadic.Fi22.D ∧ y ∈ (S : Subgroup CFSG.Sporadic.Fi22.J)} :=
    fun i => ⟨piC (fjQ i.1), hD i, hES i.1⟩
  have hinj : Function.Injective f := by
    intro i j h
    have h' : piC (fjQ i.1) = piC (fjQ j.1) := congrArg Subtype.val h
    rw [fjQ_eq_ofStar i.2, fjQ_eq_ofStar j.2] at h'
    have hij : fjPt i.1 = fjPt j.1 := congrArg Subtype.val (ofStar_injective_of_piC h')
    by_contra hne
    exact fjPt_ne (fun e => hne (Subtype.ext e)) hij
  have hcard : Nat.card {y : CFSG.Sporadic.Fi22.J //
      y ∈ CFSG.Sporadic.Fi22.D ∧ y ∈ (S : Subgroup CFSG.Sporadic.Fi22.J)} ≤
      Nat.card {i : Fin 23 // i ≠ 0} := by
    refine (card_D_inter_sylow_le S).trans ?_
    rw [Nat.card_eq_fintype_card]
    exact le_of_eq (by decide)
  obtain ⟨⟨i, hi⟩, hfi⟩ := (hinj.bijective_of_nat_card_le hcard).2
    ⟨piC (ofStar ⟨x, hx⟩), piC_ofStar_mem_D _, hxS⟩
  refine ⟨i, hi, ?_⟩
  have h' : piC (fjQ i) = piC (ofStar ⟨x, hx⟩) := congrArg Subtype.val hfi
  rw [fjQ_eq_ofStar hi] at h'
  exact congrArg Subtype.val (ofStar_injective_of_piC h')

end CFSG.EvenSporadicStandard.TwoFi22.FrameJ

namespace CFSG.EvenSporadicStandard.TwoFi22

open CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer CFSG.EvenSporadicStandard.Wong77.Module
open CFSG.EvenSporadicStandard.TwoFi22.FrameJ

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fi23_frame :
    ∃ (φ : Multiplicative Word →* J) (T : Subgroup J),
      (∀ w : Word, φ (Multiplicative.ofAdd w) = 1 ↔ w ∈ golayCode) ∧
      φ (eVec 0) = d ∧ (∀ i, φ (eVec i) ∈ D23) ∧
      T ≤ Subgroup.centralizer {d} ∧ Nat.card T = 2 ^ 18 ∧
      ∀ x ∈ D23, x ∈ T ↔ ∃ i, φ (eVec i) = x := by
  have hE : IsPGroup 2 fjProj.range :=
    isPGroup_word.of_surjective fjProj.rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  have hSi : ∀ i : Fin 23, piC (fjQ i) ∈ (S : Subgroup CFSG.Sporadic.Fi22.J) := fun i =>
    hES ⟨eVec i, fjProj_eVec i⟩
  refine ⟨fjHom, ((S : Subgroup CFSG.Sporadic.Fi22.J).comap piC).map Cd.subtype,
    fjHom_eq_one_iff, by rw [fjHom_eVec, fjPt_zero], fun i => by
      rw [fjHom_eVec]
      exact fjPt_mem i, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    have h1 := Subgroup.card_mul_index ((S : Subgroup CFSG.Sporadic.Fi22.J).comap piC)
    have h2 := Subgroup.card_mul_index (S : Subgroup CFSG.Sporadic.Fi22.J)
    rw [Subgroup.index_comap_of_surjective _ piC_surjective, card_centralizer_d] at h1
    rw [card_sylow_fi22 S, CFSG.Sporadic.Fi22.card_J] at h2
    have hidx : (S : Subgroup CFSG.Sporadic.Fi22.J).index = 492567075 := by omega
    rw [hidx] at h1
    omega
  · intro x hx
    constructor
    · intro hxT
      obtain ⟨c, hcS, hcx⟩ := Subgroup.mem_map.1 hxT
      have hcx' : (c : J) = x := hcx
      by_cases hcd : (c : J) = d
      · exact ⟨0, by rw [fjHom_eVec, fjPt_zero, ← hcx', hcd]⟩
      · have hstar : (c : J) ∈ star := ⟨hcx' ▸ hx, hcd, mem_Cd.1 c.2⟩
        obtain ⟨i, -, hi⟩ := exists_pt_of_image_mem hSi hstar hcS
        exact ⟨i, by rw [fjHom_eVec, hi, hcx']⟩
    · rintro ⟨i, rfl⟩
      rw [fjHom_eVec]
      refine Subgroup.mem_map.2 ⟨fjQ i, ?_, rfl⟩
      exact hSi i

end CFSG.EvenSporadicStandard.TwoFi22
