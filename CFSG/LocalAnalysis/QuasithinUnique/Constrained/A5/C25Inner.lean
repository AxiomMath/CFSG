module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenUnitary
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.RankThree.SubgroupLists.QuasisimpleRankTwo
public import CFSG.RankThree.CentralLiftU.UnitaryThreeEven

public section

namespace CFSG.QuasithinUnique.A5.C25

open CFSG.Open hiding StatedSL StatedSU StatedLieAdmissible StatedClassicalModel StatedProj
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.RankOneRecog
  CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.RankThree.SubgroupLists CFSG.RankThree.CentralLiftU
  CFSG.LocalAnalysis.ComponentInitial CFSG.Sporadic.Schreier

@[expose] def SylowCentralizingInvolInner (X : Type) [Group X] : Prop :=
  ∀ Q : Subgroup X, IsSylowTwoOf Q ⊤ → ∀ β : X ≃* X, (∀ x, β (β x) = x) → (∀ q ∈ Q, β q = q) →
    ∃ x : X, ∀ y : X, β y = x⁻¹ * y * x

theorem SylowCentralizingInvolInner.of_autInner {X : Type} [Group X]
    (h : SylowCentralizingAutInner X) : SylowCentralizingInvolInner X :=
  fun Q hQ β _ hβ => h Q hQ β hβ

section Inner

variable {X : Type} [Group X] [Finite X]

theorem exists_inner_of_sylow_invol {L : Subgroup X} [L.Normal] (S : Sylow 2 X)
    (hperf : Group.IsPerfect L) (hA : SylowCentralizingInvolInner (L ⧸ Subgroup.center L))
    {w : X} (hw2 : w * w = 1) (hwS : w ∈ Subgroup.centralizer ((S : Subgroup X) : Set X)) :
    ∃ x ∈ L, ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_map_eq_inf_of_subnormal S (Subgroup.Normal.isSubnormal ‹L.Normal›)
  have hwN : w ∈ Subgroup.normalizer (L : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top w
  let c : L ≃* L := conjAutOfNormalizer L hwN
  have hcc : (Subgroup.center L).map c.toMonoidHom = Subgroup.center L :=
    Subgroup.map_center_eq c
  let β : L ⧸ Subgroup.center L ≃* L ⧸ Subgroup.center L :=
    QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) c hcc
  have hβ : ∀ y : L, β (y : L ⧸ Subgroup.center L) = ((c y : L) : L ⧸ Subgroup.center L) :=
    fun y => rfl
  let T : Sylow 2 (L ⧸ Subgroup.center L) := P.mapSurjective (QuotientGroup.mk'_surjective _)
  have hT : IsSylowTwoOf (T : Subgroup (L ⧸ Subgroup.center L)) ⊤ :=
    isSylowTwoOf_top_iff.mpr ⟨T.isPGroup', T.not_dvd_index⟩
  have hTfix : ∀ q ∈ (T : Subgroup (L ⧸ Subgroup.center L)), β q = q := by
    intro q hq
    rw [Sylow.coe_mapSurjective] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hpS : (p : X) ∈ (S : Subgroup X) := by
      have : (p : X) ∈ (P : Subgroup L).map L.subtype := Subgroup.mem_map_of_mem _ hp
      rw [hP] at this
      exact this.1
    have h1 : (p : X) * w = w * (p : X) := Subgroup.mem_centralizer_iff.mp hwS _ hpS
    have h2 : (c p : L) = p := Subtype.ext (by
      change w⁻¹ * (p : X) * w = p
      rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul])
    show β ((QuotientGroup.mk' (Subgroup.center L)) p) = (QuotientGroup.mk' (Subgroup.center L)) p
    change β (p : L ⧸ Subgroup.center L) = (p : L ⧸ Subgroup.center L)
    rw [hβ, h2]
  have hβ2 : ∀ q, β (β q) = q := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hβ, hβ]
    congr 1
    apply Subtype.ext
    change w⁻¹ * (w⁻¹ * (y : X) * w) * w = y
    calc w⁻¹ * (w⁻¹ * (y : X) * w) * w = (w * w)⁻¹ * y * (w * w) := by group
      _ = y := by rw [hw2]; simp
  obtain ⟨xb, hxb⟩ := hA _ hT β hβ2 hTfix
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have hcen : ∀ y : L, (x⁻¹ * y * x)⁻¹ * c y ∈ Subgroup.center L := by
    intro y
    have h1 := hxb (y : L ⧸ Subgroup.center L)
    rw [hβ] at h1
    rw [← QuotientGroup.eq]
    rw [h1]
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hc := eq_conj_of_central_displacement c x hcen
  exact ⟨(x : X), x.2, fun y hy => congrArg (fun z : L => (z : X)) (hc ⟨y, hy⟩)⟩

end Inner

section Families

theorem sixteen_dvd_card_of_elemAbelian {X : Type} [Group X] [Finite X] {E : Subgroup X}
    (hE : IsElemAbelian 2 E) (h16 : 16 ≤ Nat.card E) : 16 ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hE2.exists_card_eq
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1 : 2 ^ 4 ∣ Nat.card E := hk ▸ pow_dvd_pow 2 hk4
  have h2 : 2 ^ 4 ∣ Nat.card X := h1.trans (Subgroup.card_subgroup_dvd_card E)
  simpa using h2

theorem false_of_elemAbelian_linUni {X K : Type} [Group X] [Field K] [Finite K] {p f : ℕ}
    {H : Subgroup (GL (Fin 3) K)}
    (hH : (Nat.card K = p ^ f ∧ H = StatedSL 3 K) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU 3 (p ^ f) K))
    (hodd : Odd (Nat.card K)) (φ : X ≃* ↥H) {E : Subgroup X} (hE : IsElemAbelian 2 E)
    (h16 : 16 ≤ Nat.card E) : False := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  let ψ : X →* GL (Fin 3) K := H.subtype.comp φ.toMonoidHom
  have hψ : Function.Injective ψ := H.subtype_injective.comp φ.injective
  have hle := card_le_four_of_sq_eq_one_sl3 h2 (E.map ψ)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul]
      have : x * x = 1 := by rw [← pow_two]; exact hE.2 x hx
      rw [this, map_one])
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact CFSG.SectionRank.OddCover.det_eq_one_of_linUni hH (φ x).2)
  rw [← Nat.card_congr (E.equivMapOfInjective ψ hψ).toEquiv] at hle
  omega

theorem sylowInvolInner_of_case2
    {X : Type} [Group X] [Finite X]
    (hZ : Nat.card (Subgroup.center X) = 3)
    (hE : ∃ E : Subgroup X, IsElemAbelian 2 E ∧ 16 ≤ Nat.card E) (h2 : A36Case2List X) :
    SylowCentralizingInvolInner (X ⧸ Subgroup.center X) := by
  obtain ⟨E, hEa, hE16⟩ := hE
  have hdvd : 16 ∣ Nat.card X := sixteen_dvd_card_of_elemAbelian hEa hE16
  have hcardX : Nat.card X = Nat.card (X ⧸ Subgroup.center X) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hZ]
  rcases h2 with ⟨s, p, e, hp, he, hcong, hmodel⟩ | h6 | h7 | hM
  · rcases hcong with ⟨rfl, -⟩ | ⟨hp2, rfl⟩
    ·
      cases s
      ·
        obtain ⟨K, hF, hFin, hcard, ⟨φ⟩⟩ := hmodel
        by_cases he1 : e = 1
        · exfalso
          subst he1
          have hUF : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hcard]; norm_num⟩
          have h216 := card_statedSU_three_two hUF rfl
          have hX : Nat.card X = 216 := by rw [Nat.card_congr φ.toEquiv]; exact h216
          rw [hX] at hdvd
          omega
        · have he2 : 2 ≤ e := by omega
          have hne : ((3 : ℕ), 2 ^ e) ≠ (3, 2) := fun h => by
            have h1 : 2 ^ e = 2 := congrArg Prod.snd h
            have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
            omega
          have hadm : StatedLieAdmissible .PSU 3 2 e := ⟨Nat.prime_two, he, le_rfl, hne⟩
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          have hZ' := (isQuasisimple_statedSU_of_card hcard (le_refl 3) hne).2
          let iso : X ⧸ Subgroup.center X ≃* StatedProj (StatedSU 3 (2 ^ e) K) :=
            (QuotientGroup.congr (Subgroup.center X) (Subgroup.center ↥(StatedSU 3 (2 ^ e) K)) φ
              (map_center_mulEquiv φ)).trans (QuotientGroup.quotientMulEquivOfEq hZ')
          have hmodel' : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 e :=
            ⟨hadm, K, hF, hFin, hcard, ⟨iso⟩⟩
          exact SylowCentralizingInvolInner.of_autInner (evenUnitaryAutInner _ e he2 hmodel')
      ·
        obtain ⟨K, hF, hFin, hcard, ⟨φ⟩⟩ := hmodel
        have hne1 : ((3 : ℕ), 2 ^ e) ≠ (2, 2) := fun h => by simp at h
        have hne2 : ((3 : ℕ), 2 ^ e) ≠ (2, 3) := fun h => by simp at h
        have hadm : StatedLieAdmissible .PSL 3 2 e := ⟨Nat.prime_two, he, by norm_num, hne1, hne2⟩
        let e' : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
          φ.trans (specialLinearGroupEquivStatedSL 3 K).symm
        let iso : X ⧸ Subgroup.center X ≃* StatedProj (StatedSL 3 K) :=
          (QuotientGroup.congr (Subgroup.center X)
            (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) e'
            (map_center_mulEquiv e')).trans (projectiveSpecialLinearGroupEquivStatedProj 3 K)
        have hmodel' : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 2 e :=
          ⟨hadm, K, hF, hFin, hcard, ⟨iso⟩⟩
        exact SylowCentralizingInvolInner.of_autInner
          (sylowCentralizingAutInner_of_stated_psl (by norm_num) he hmodel')
    ·
      exfalso
      cases s
      · obtain ⟨K, _, _, hcard, ⟨φ⟩⟩ := hmodel
        have hodd : Odd (Nat.card K) := by
          rw [hcard]
          exact ((hp.odd_of_ne_two hp2).pow : Odd (p ^ 1)).pow
        exact false_of_elemAbelian_linUni (p := p) (f := 1) (Or.inr ⟨hcard, rfl⟩) hodd φ hEa hE16
      · obtain ⟨K, _, _, hcard, ⟨φ⟩⟩ := hmodel
        have hodd : Odd (Nat.card K) := by
          rw [hcard]
          exact (hp.odd_of_ne_two hp2).pow
        exact false_of_elemAbelian_linUni (p := p) (f := 1) (Or.inl ⟨hcard, rfl⟩) hodd φ hEa hE16
  ·
    exfalso
    obtain ⟨-, -, ⟨e⟩⟩ := h6
    have hc : Nat.card (X ⧸ Subgroup.center X) = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    rw [hcardX, hc] at hdvd
    omega
  ·
    exfalso
    obtain ⟨-, -, ⟨e⟩⟩ := h7
    have hc : Nat.card (X ⧸ Subgroup.center X) = 2520 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    rw [hcardX, hc] at hdvd
    omega
  ·
    obtain ⟨-, -, ⟨e⟩⟩ := hM
    intro Q hQ β hβ hfix
    obtain ⟨hQp, hQi⟩ := isSylowTwoOf_top_iff.mp hQ
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let P : Sylow 2 (X ⧸ Subgroup.center X) := hQp.toSylow hQi
    refine autInner_of_equiv_of_outer_card e (m := 443520) (S := ({320, 1344} : Set ℕ)) ?_ ?_ ?_
      β hβ ⟨P, hfix⟩
    · rw [Nat.card_congr e.toEquiv]
      exact m22_card
    · intro c hc k i hk hki
      have hc' : c = 320 ∨ c = 1344 := by simpa using hc
      have hk8 : 2 ^ k ≤ 1344 := by
        rcases hc' with rfl | rfl
        · exact (Nat.le_of_dvd (by norm_num) hk).trans (by norm_num)
        · exact Nat.le_of_dvd (by norm_num) hk
      have hk11 : k < 11 := by
        by_contra hlt
        have : 2 ^ 11 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k <;> rcases hc' with rfl | rfl <;> omega
    · intro α hα2 hα
      exact m22_outer_fixSub_card α hα2 hα

end Families

end CFSG.QuasithinUnique.A5.C25
