module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowAll
public import CFSG.RankThree.PartOne.KS.HeKit

public section

namespace CFSG.ComponentClassification.AS81.HeSylow

open Subgroup CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.GrSLit.HeldFix CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
open scoped Pointwise

theorem sylCheck8330_of (h : heSylowCheckS = true) : sylCheck8330S = true := by
  simp only [heSylowCheckS, Bool.and_eq_true] at h
  exact h.1.1

theorem sylCheckRestrict_of (h : heSylowCheckS = true) : sylCheckRestrict = true := by
  simp only [heSylowCheckS, Bool.and_eq_true] at h
  exact h.1.2

theorem sylCheck8330_parts (h : sylCheck8330S = true) :
    (∀ i < 5, lettersOK 9 (heSylWords.getD i []) = true) ∧
    (∀ j < 9, validA 8330 heSylLetters[j]! = true) := by
  simp only [sylCheck8330S, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact ⟨fun i hi => allLt_spec h.2.1 hi, fun j hj => allLt_spec h.2.2 hj⟩

theorem sylCheckRestrict_parts (h : sylCheckRestrict = true) :
    heSyl16.length = 5 ∧ (∀ k < 16, heSylPts[k]! < 8330) ∧
    (∀ k < 15, heSylPts[k]! < heSylPts[k + 1]!) ∧
    ∀ i < 5, validA 16 (heSyl16.getD i #[]) = true ∧
      agreeOK 16 (heSylGen i) heSylPts (heSyl16.getD i #[]) = true := by
  simp only [sylCheckRestrict, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  refine ⟨h.2.1, fun k hk => of_decide_eq_true (allLt_spec h.2.2.1 hk),
    fun k hk => of_decide_eq_true (allLt_spec h.2.2.2.1 hk), fun i hi => ?_⟩
  have := allLt_spec h.2.2.2.2 hi
  simpa only [Bool.and_eq_true] using this

@[expose] noncomputable def heSylP0 : Subgroup (Equiv.Perm (Fin 8330)) :=
  closure (permsA 8330 heSylGens)

theorem heSylGens_size : heSylGens.size = 5 := by simp [heSylGens]

theorem heSylGens_get {k : ℕ} (hk : k < 5) : heSylGens[k]! = heSylGen k := by
  rw [heSylGens, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem heSylLetters_get {j : ℕ} (hj : j < 9) : heSylLetters[j]! = heInnerC1 j := by
  rw [heSylLetters, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

@[expose] noncomputable def heSylLettersP : List (Equiv.Perm (Fin 8330)) :=
  (List.range 9).map heInnerCP1

theorem heSylLettersP_length : heSylLettersP.length = 9 := by simp [heSylLettersP]

theorem heSylLettersP_getD {j : ℕ} (hj : j < 9) : heSylLettersP.getD j 1 = heInnerCP1 j := by
  simp [heSylLettersP, List.getD_eq_getElem?_getD, List.getElem?_range hj]

theorem rep_heSylGen
    (h : sylCheck8330S = true) {i : ℕ} (hi : i < 5) :
    Rep 8330 (heSylGen i) (evalSignedWord heSylLettersP (heSylWords.getD i [])) := by
  have hl := (sylCheck8330_parts h).1
  have hv := (sylCheck8330_parts h).2
  refine rep_wordA_evalSignedWord (fun j hj => ?_) (fun j hj => ?_)
    (by rw [heSylLettersP_length]; exact hl i hi)
  · rw [heSylLettersP_length] at hj
    rw [heSylLettersP_getD hj, heSylLetters_get hj]
    exact rep_heInnerC1 hj
  · rw [heSylLettersP_length] at hj
    have hinv := rep_inv_of_validA (hv j hj)
    rw [heSylLetters_get hj, permOfArr_eq_of_rep (rep_heInnerC1 hj)] at hinv
    rwa [heSylLettersP_getD hj, getElem!_map_eq _ _ (by simpa [heSylLetters] using hj),
      heSylLetters_get hj]

theorem heSylGen_mem
    (h : sylCheck8330S = true) {i : ℕ} (hi : i < 5) : permOfArr 8330 (heSylGen i) ∈ heP := by
  rw [permOfArr_eq_of_rep (rep_heSylGen h hi)]
  refine evalSignedWord_mem heP (fun g hg => ?_) _
  simp only [heSylLettersP, List.mem_map] at hg
  obtain ⟨j, -, rfl⟩ := hg
  exact heInnerCP1_mem _

theorem heSylP0_le_heP
    (h : sylCheck8330S = true) : heSylP0 ≤ heP := by
  rw [heSylP0, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk5 : k < 5 := heSylGens_size ▸ hk
  show permOfArr 8330 heSylGens[k]! ∈ heP
  rw [heSylGens_get hk5]
  exact heSylGen_mem h hk5

theorem heSylDelta_injective (h : sylCheckRestrict = true) :
    Function.Injective (listPt 8330 heSylPts (m := 16)) := by
  exact listPt_injective_of_inc (sylCheckRestrict_parts h).2.1 (sylCheckRestrict_parts h).2.2.1

theorem heSylGen_agree
    (h : heSylowCheckS = true) {i : ℕ} (hi : i < 5) (k : Fin 16) :
    permOfArr 8330 (heSylGen i) (listPt 8330 heSylPts k) =
      listPt 8330 heSylPts (permOfArr 16 (heSyl16.getD i #[]) k) := by
  have hgen := (sylCheckRestrict_parts (sylCheckRestrict_of h)).2.2.2 i hi
  have hlt := (sylCheckRestrict_parts (sylCheckRestrict_of h)).2.1
  have hr := rep_heSylGen (sylCheck8330_of h) hi
  rw [permOfArr_eq_of_rep hr]
  exact agreeOK_spec_of_lt hlt hr (rep_of_validA hgen.1) hgen.2 k

theorem heSylP0_le_stabilizer
    (h : heSylowCheckS = true) :
    heSylP0 ≤ MulAction.stabilizer (Equiv.Perm (Fin 8330))
      (Set.range (listPt 8330 heSylPts (m := 16))) := by
  rw [heSylP0, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk5 : k < 5 := heSylGens_size ▸ hk
  show permOfArr 8330 heSylGens[k]! ∈ _
  rw [heSylGens_get hk5]
  exact mem_stabilizer_of_agree (heSylGen_agree h hk5)

theorem card_X16_of (h : heSylowCheckS = true) : Nat.card X16 = 1024 :=
  card_grpN (sylCheck16_parts (sylCheck16_of h)).1

theorem lt_five_of_lt_length (h : heSylowCheckS = true) {i : ℕ} (hi : i < heSyl16.length) :
    i < 5 :=
  (sylCheckRestrict_parts (sylCheckRestrict_of h)).1 ▸ hi

theorem heSylGen_mem_heSylP0 {i : ℕ} (hi5 : i < 5) : permOfArr 8330 (heSylGen i) ∈ heSylP0 := by
  rw [← heSylGens_get hi5]
  exact subset_closure ⟨i, heSylGens_size ▸ hi5, rfl⟩

theorem restrictHom_mk_eq {δ : Fin 16 → Fin 8330} (hδ : Function.Injective δ)
    {H : Subgroup (Equiv.Perm (Fin 8330))}
    (hH : H ≤ MulAction.stabilizer (Equiv.Perm (Fin 8330)) (Set.range δ))
    (g : Equiv.Perm (Fin 8330)) (hm : g ∈ H) (σ : Equiv.Perm (Fin 16))
    (hag : ∀ k, g (δ k) = δ (σ k)) : restrictHom hδ H hH ⟨g, hm⟩ = σ :=
  restrictHom_eq_of_agree hδ hH ⟨g, hm⟩ hag

@[expose] noncomputable def heSylRestr :
    ↥heSylP0 →* Equiv.Perm (Fin 16) :=
  restrictHom (heSylDelta_injective (sylCheckRestrict_of he_sylowCheck)) heSylP0
    (heSylP0_le_stabilizer he_sylowCheck)

theorem heSylRestr_gen
    {i : ℕ} (hi5 : i < 5)
    (hm : permOfArr 8330 (heSylGen i) ∈ heSylP0) :
    heSylRestr ⟨_, hm⟩ = permOfArr 16 (heSyl16.getD i #[]) :=
  restrictHom_mk_eq (heSylDelta_injective (sylCheckRestrict_of he_sylowCheck))
    (heSylP0_le_stabilizer he_sylowCheck) (permOfArr 8330 (heSylGen i)) hm
    (permOfArr 16 (heSyl16.getD i #[])) (heSylGen_agree he_sylowCheck hi5)

theorem X16_le_range :
    X16 ≤ heSylRestr.range := by
  refine grpN_le fun a ha => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi5 := lt_five_of_lt_length he_sylowCheck hi
  refine ⟨⟨_, heSylGen_mem_heSylP0 hi5⟩, ?_⟩
  rw [heSylRestr_gen hi5, List.getD_eq_getElem _ _ hi]

theorem range_le_X16 :
    heSylRestr.range ≤ X16 := by
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  have hl := (sylCheckRestrict_parts (sylCheckRestrict_of he_sylowCheck)).1
  have hgen : ∀ k < 5, ∀ (y : Equiv.Perm (Fin 8330)) (hy : y ∈ heSylP0),
      y = permOfArr 8330 (heSylGen k) → heSylRestr ⟨y, hy⟩ ∈ X16 := by
    rintro k hk5 y hy rfl
    rw [heSylRestr_gen hk5]
    refine gen_mem_grpN ?_
    rw [List.getD_eq_getElem _ _ (hl ▸ hk5)]
    exact List.getElem_mem _
  have hle : heSylP0 ≤ (X16.comap heSylRestr).map heSylP0.subtype := by
    change closure (permsA 8330 heSylGens) ≤ (X16.comap heSylRestr).map heSylP0.subtype
    refine (closure_le _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk5 : k < 5 := heSylGens_size ▸ hk
    have hm : permOfArr 8330 heSylGens[k]! ∈ heSylP0 := subset_closure ⟨k, hk, rfl⟩
    exact ⟨⟨_, hm⟩, hgen k hk5 _ hm (congrArg (permOfArr 8330) (heSylGens_get hk5)), rfl⟩
  obtain ⟨y, hy, hyg⟩ := hle hg
  have e : y = ⟨g, hg⟩ := Subtype.ext hyg
  rw [← e]
  exact hy

theorem range_heSylRestr :
    heSylRestr.range = X16 :=
  le_antisymm range_le_X16 X16_le_range

theorem map_sylow_eq_top {p : ℕ} [Fact p.Prime] {H K : Type*} [Group H] [Group K] [Finite H]
    {f : H →* K} (hf : Function.Surjective f) (hK : IsPGroup p K) (S : Sylow p H) :
    (S : Subgroup H).map f = ⊤ := by
  have : Finite K := Finite.of_surjective f hf
  obtain ⟨k, hk⟩ := hK.index ((S : Subgroup H).map f)
  have h1 : p ^ k ∣ (S : Subgroup H).index := hk ▸ index_map_dvd _ hf
  have h2 : ¬ p ∣ (S : Subgroup H).index := S.not_dvd_index
  have hk0 : k = 0 := by
    by_contra hne
    exact h2 ((dvd_pow_self p hne).trans h1)
  rw [← index_eq_one, hk, hk0, pow_zero]

theorem exists_sylow_equiv_X16 :
    ∃ S : Subgroup (Equiv.Perm (Fin 8330)), S ≤ heP ∧ Nat.card S = 1024 ∧
      Nonempty (↥S ≃* ↥X16) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := he_sylowCheck
  have hle := heSylP0_le_heP (sylCheck8330_of h)
  have hcK : Nat.card heSylRestr.range = 1024 := by rw [range_heSylRestr, card_X16_of h]
  have hK : IsPGroup 2 heSylRestr.range :=
    IsPGroup.of_card (n := 10) (by rw [hcK]; norm_num)
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 heSylP0))
  have hsurj := MonoidHom.rangeRestrict_surjective heSylRestr
  have hmap := map_sylow_eq_top hsurj hK S
  have hge : 1024 ≤ Nat.card S := by
    have h1 := card_map_dvd (S : Subgroup heSylP0) heSylRestr.rangeRestrict
    rw [hmap, card_top, hcK] at h1
    exact Nat.le_of_dvd Nat.card_pos h1
  set S2 := (S : Subgroup heSylP0).map heSylP0.subtype with hS2
  have hS2le : S2 ≤ heP := by
    rintro _ ⟨x, -, rfl⟩
    exact hle x.2
  have hcS2 : Nat.card S2 = Nat.card S := card_map_of_injective heSylP0.subtype_injective
  have hlt : Nat.card S ≤ 1024 := by
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    have hd : 2 ^ k ∣ Nat.card heP := by
      rw [← hk, ← hcS2]
      exact card_dvd_of_le hS2le
    have hne : Nat.card heP ≠ 0 := Nat.card_pos.ne'
    have hk' := (Nat.prime_two.pow_dvd_iff_le_factorization hne).1 hd
    rw [hk, ← two_pow_factorization_card_heP]
    exact Nat.pow_le_pow_right (by norm_num) hk'
  have hcS : Nat.card S = 1024 := le_antisymm hlt hge
  let ψ : ↥(S : Subgroup heSylP0) →* ↥heSylRestr.range :=
    heSylRestr.rangeRestrict.comp (S : Subgroup heSylP0).subtype
  have hψ : Function.Surjective ψ := by
    intro y
    have hy : y ∈ (S : Subgroup heSylP0).map heSylRestr.rangeRestrict := hmap ▸ mem_top y
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hbij : Function.Bijective ψ := hψ.bijective_of_nat_card_le (by rw [hcS, hcK])
  refine ⟨S2, hS2le, hcS2.trans hcS, ⟨?_⟩⟩
  exact (((S : Subgroup heSylP0).equivMapOfInjective _ heSylP0.subtype_injective).symm.trans
    (MulEquiv.ofBijective ψ hbij)).trans (MulEquiv.subgroupCongr range_heSylRestr)

theorem nonempty_sylow_he_equiv
    (P : Sylow 2 (Carrier .He)) : Nonempty (↥(P : Subgroup (Carrier .He)) ≃* ↥X16) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S0, hS0le, hS0c, ⟨e0⟩⟩ := exists_sylow_equiv_X16
  let θ : Carrier .He ≃* ↥heP := heEquivP
  let f : Carrier .He →* Equiv.Perm (Fin 8330) := heP.subtype.comp θ.toMonoidHom
  have hf : Function.Injective f := heP.subtype_injective.comp θ.injective
  have hP'le : (P : Subgroup (Carrier .He)).map f ≤ heP := by
    rintro _ ⟨x, -, rfl⟩
    exact (θ x).2
  have hcardHe : Nat.card (Carrier .He) = Nat.card heP := Nat.card_congr θ.toEquiv
  have : Finite (Carrier .He) := Finite.of_equiv _ θ.symm.toEquiv
  have hc0 : Nat.card S0 = 2 ^ (Nat.card heP).factorization 2 := by
    rw [two_pow_factorization_card_heP, hS0c]
  have hcP : Nat.card ((P : Subgroup (Carrier .He)).map f) = Nat.card S0 := by
    rw [card_map_of_injective hf, Sylow.card_eq_multiplicity, hcardHe, ← hc0]
  obtain ⟨g, -, hg⟩ := exists_conj_eq_map_of_card hS0le hP'le hc0 hcP
  exact ⟨((P : Subgroup (Carrier .He)).equivMapOfInjective f hf).trans
    ((MulEquiv.subgroupCongr hg).trans
      ((S0.equivMapOfInjective _ (MulAut.conj g).injective).symm.trans e0))⟩

theorem range_hfPhi_eq :
    hfPhi.range = Y32 := by
  have htab := tabRep_resGen hfDelta32_points hfT0_preserves fun j hj => (tabRep_hfT0Tabs j hj).2
  refine (range_restrHom_eq hfDelta32_points hfT0_preserves).trans ?_
  show Subgroup.closure _ = Subgroup.closure (permsA 32 hfT0Tabs32.toList.toArray)
  rw [Array.toArray_toList]
  congr 1
  exact Set.image_congr fun j hj => (permOfArr_eq_of_rep (htab j hj).2).symm

theorem nonempty_sylow_aut_equiv
    {H : Type} [Group H] [Finite H] {K : Subgroup H}
    (hKn : K.Normal) (hK : IsSporadic K .He) (hi : K.index = 2)
    (hC : centralizer (K : Set H) = ⊥) (P : Sylow 2 H) :
    Nonempty (↥(P : Subgroup H) ≃* ↥Y32) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hKn
  obtain ⟨e⟩ := hK
  let θ : ↥K ≃* ↥heP := e.trans heEquivP
  let ι := RankThree.PartOne.heAutModel.embed K θ
  have hι : Function.Injective ι := RankThree.PartOne.heAutModel.embed_injective K θ hC
  have hP'le : (P : Subgroup H).map ι ≤ heAutGroup := by
    rintro _ ⟨x, -, rfl⟩
    exact RankThree.PartOne.heAutModel.embed_mem K θ x
  have hcK : Nat.card K = Nat.card heP := Nat.card_congr θ.toEquiv
  have hcH : Nat.card H = Nat.card heAutGroup := by
    rw [← K.index_mul_card, hi, hcK, card_heP, card_heAutGroup]
  have hcP' : Nat.card ((P : Subgroup H).map ι) = 2048 := by
    rw [card_map_of_injective hι, Sylow.card_eq_multiplicity, hcH,
      two_pow_factorization_card_heAutGroup]
  obtain ⟨g, -, hg⟩ := exists_conj_hfT0 hP'le hcP'
  have e1 : ↥hfT0 ≃* ↥Y32 :=
    (MonoidHom.ofInjective hfPhi_injective).trans (MulEquiv.subgroupCongr range_hfPhi_eq)
  exact ⟨((P : Subgroup H).equivMapOfInjective ι hι).trans
    ((MulEquiv.subgroupCongr hg).trans
      ((hfT0.equivMapOfInjective _ (MulAut.conj g).injective).symm.trans e1))⟩

end CFSG.ComponentClassification.AS81.HeSylow
