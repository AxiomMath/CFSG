module

public import CFSG.LieType.SeitzGeneration.ExcHigh.Classes
public import CFSG.HardMathSupport.Lang.AnisoE6.CatBridge
public import CFSG.HardMathSupport.Malle.SeitzCube.E7High
public import CFSG.HardMathSupport.Lang.TwE6Step3.SylowTorusSix

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Open CFSG.HardMathSupport.Lang.AnisoE6

theorem exists_ne_one_mem_plane_inf_hyperplane {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    {V E F : Subgroup K} (hEV : E ≤ V) (hEc : Nat.card E = p ^ 2) (hFi : F.relIndex V = p)
    (hV : Nat.card V ≠ 0) : ∃ y ∈ E ⊓ F, y ≠ 1 := by
  have hne : E ⊓ F ≠ ⊥ := by
    intro hbot
    have h1 : (E ⊓ F).relIndex V ≤ E.relIndex V * F.relIndex V := Subgroup.relIndex_inf_le
    have h2 : E.relIndex V * Nat.card (E ⊓ V : Subgroup K) = Nat.card V :=
      Subgroup.relIndex_mul_card E V
    rw [inf_of_le_left hEV, hEc] at h2
    rw [hbot, Subgroup.relIndex_bot_left, hFi] at h1
    have hpp := hp.two_le
    set a := E.relIndex V with ha
    have hpos : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · rw [h0, zero_mul] at h2
        exact absurd h2.symm hV
      · exact h0
    have : a * p ^ 2 ≤ a * p := by rw [h2]; exact h1
    have hp2 : p ^ 2 ≤ p := Nat.le_of_mul_le_mul_left this hpos
    nlinarith
  by_contra hcon
  push Not at hcon
  exact hne ((Subgroup.eq_bot_iff_forall _).2 fun y hy => hcon y hy)

theorem hyperClosure_le_cl {K : Type*} [Group K] {p : ℕ} (hp : p.Prime) {V E : Subgroup K}
    (hEV : E ≤ V) (hEc : Nat.card E = p ^ 2) (hV : Nat.card V ≠ 0) :
    hyperClosure p ⊤ V ≤ cl E := by
  unfold hyperClosure
  rw [Subgroup.closure_le]
  rintro k ⟨-, F, hFV, hFi, hFk⟩
  obtain ⟨y, hyE, hy1⟩ := exists_ne_one_mem_plane_inf_hyperplane hp hEV hEc hFi hV
  exact mem_cl_of_commute hyE.1 hy1 (hFk y hyE.2).symm

open TauCeti

theorem exists_conj_of_sylowTorus_cube {G : Type*} [Group G] {p m : ℕ} (hp : p.Prime)
    (hS : SylowTorus G p m) {A B : Subgroup G} (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ m)
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ m) :
    ∃ x : G, B = A.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨T, V0, -, hconj, hV0T, hV0tor, -, hV0c⟩ := hS.exists_torus
  have hfin : ∀ {X : Subgroup G}, Nat.card X = p ^ m → Finite X := fun {X} hX =>
    Nat.finite_of_card_ne_zero (by rw [hX]; exact (pow_pos hp.pos m).ne')
  have key : ∀ {X : Subgroup G}, IsElemAbelian p X → Nat.card X = p ^ m →
      ∃ a : G, X = V0.map (MulAut.conj a).toMonoidHom := by
    intro X hX hXc
    obtain ⟨a, ha⟩ := hconj X (isPGroup_of_isElemAbelian hX)
    refine ⟨a, ?_⟩
    have hle : X ≤ V0.map (MulAut.conj a).toMonoidHom := by
      intro x hx
      obtain ⟨t, ht, hxt⟩ := ha hx
      have htp : t ^ p = 1 := by
        have h1 := hX.2 x hx
        rw [← hxt] at h1
        have : (MulAut.conj a) (t ^ p) = 1 := by
          rw [map_pow]
          exact h1
        exact (MulAut.conj a).injective (this.trans (map_one _).symm)
      exact ⟨t, hV0tor t ht htp, hxt⟩
    haveI : Finite (V0.map (MulAut.conj a).toMonoidHom) := by
      have := hfin hV0c
      exact Finite.of_equiv V0 (V0.equivMapOfInjective _ (MulAut.conj a).injective).toEquiv
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective, hV0c, hXc]
  obtain ⟨a, ha⟩ := key hA hAc
  obtain ⟨b, hb⟩ := key hB hBc
  refine ⟨b * a⁻¹, ?_⟩
  rw [hb, ha, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]


theorem planeGen_of_hyperRegime {d : ValidLieTypeIndex} {p m : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : Cat d →* MulAut (Cat d)))
    (hS : SylowTorus (Cat d) p m)
    (hreg : (∃ E₀ : Subgroup (Cat d), IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ m) →
      ∃ E : Subgroup (Cat d), IsElemAbelian p E ∧ Nat.card E = p ^ m ∧
        (NormalizesRSub d E ∨ HyperGen p ⊤ E))
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hin : InnerPlane d p E) (hN : ¬ NormalizesRSubgroup d E) : PlaneGen E := by
  obtain ⟨E', hE'el, hE'c, hE'map⟩ := exists_map_conj_eq hinj hin hE hEc
  obtain ⟨T, V0, -, hconj, hV0T, hV0tor, hV0el, hV0c⟩ := hS.exists_torus
  obtain ⟨g, hg⟩ := hconj E' (isPGroup_of_isElemAbelian hE'el)
  set V : Subgroup (Cat d) := V0.map (MulAut.conj g).toMonoidHom with hVdef
  have hVel : IsElemAbelian p V := by
    exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hV0el _
  have hVc : Nat.card V = p ^ m := by
    rw [hVdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hV0c]
  have hE'V : E' ≤ V := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := hg hx
    have htp : t ^ p = 1 := by
      have h1 := hE'el.2 x hx
      rw [← hxt] at h1
      have : (MulAut.conj g) (t ^ p) = 1 := by
        rw [map_pow]
        exact h1
      exact (MulAut.conj g).injective (this.trans (map_one _).symm)
    exact ⟨t, hV0tor t ht htp, hxt⟩
  obtain ⟨Ec, hEcel, hEcc, hcase⟩ := hreg ⟨V0, hV0el, hV0c⟩
  obtain ⟨x, hx⟩ := exists_conj_of_sylowTorus_cube hp hS hEcel hEcc hVel hVc
  have hVx : V = Ec.map (MulAut.conj x).toMonoidHom := hx
  rcases hcase with hnorm | hhyp
  ·
    exfalso
    have h1 : NormRSub d.1.characteristic Ec := hnorm
    have h2 : NormRSub d.1.characteristic V := by
      rw [hVx]
      exact normRSub_map (MulAut.conj x).toMonoidHom (MulAut.conj x).injective h1
    obtain ⟨R, hR1, hRp, hRn⟩ := h2
    apply hN
    rw [← hE'map, normalizesR_iff]
    exact ⟨R, hR1, hRp, fun y hy => hRn y (hE'V hy)⟩
  · have hV : HyperGen p ⊤ V := by
      rw [hVx]
      exact hyperGen_conj x hhyp
    have hle : (⊤ : Subgroup (Cat d)) ≤ cl E' :=
      hV.trans (hyperClosure_le_cl hp hE'V hE'c (by rw [hVc]; exact (pow_pos hp.pos m).ne'))
    rw [PlaneGen, ← hE'map, planeClosure_map_conj hinj]
    exact top_le_iff.1 hle

theorem planeGen_of_cube {d : ValidLieTypeIndex} {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : Cat d →* MulAut (Cat d)))
    (hS : SylowTorus (Cat d) p 3)
    (hcube : (∃ E₀ : Subgroup (Cat d), IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 3) →
      ∃ E : Subgroup (Cat d), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        (NormalizesRSub d E ∨ HyperGen p ⊤ E))
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hin : InnerPlane d p E) (hN : ¬ NormalizesRSubgroup d E) : PlaneGen E :=
  planeGen_of_hyperRegime hp hinj hS hcube hE hEc hin hN

section Classes

open CFSG.LieType.SeitzGeneration.ExcHigh CFSG.TauCetiBridge CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Timmesfeld.CrossChar (sylowTorus_of_blocks_of_three_lt not_dvd_of_blocks
  not_dvd_div_of_720)
open CFSG.HardMathSupport.Malle.SeitzCube (ExcCubeHighAt)
open CFSG.Blueprint.Chevalley


theorem not_dvd_sq_sub_one_of_orderOf {p q e : ℕ} (hp : p.Prime) (hq : 1 ≤ q)
    (h : orderOf ((q : ℕ) : ZMod p) = e) (he : ¬ e ∣ 2) : ¬ p ∣ q ^ 2 - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  apply he
  rw [← h]
  apply orderOf_dvd_of_pow_eq_one
  have h0 : ((q ^ 2 - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hd
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h0
  exact h0

theorem seven_le_of_orderOf_three {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : orderOf ((q : ℕ) : ZMod p) = 3) : 7 ≤ p := by
  haveI := Fact.mk hp
  have h0 : ((q : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at h
    omega
  have h3 : 3 ∣ p - 1 := by
    rw [← h]
    exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h0)
  omega

theorem seven_le_of_orderOf_six {p q : ℕ} (hp : p.Prime)
    (h : orderOf ((q : ℕ) : ZMod p) = 6) : 7 ≤ p := by
  haveI := Fact.mk hp
  have h0 : ((q : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at h
    omega
  have h6 : 6 ∣ p - 1 := by
    rw [← h]
    exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h0)
  have := hp.two_le
  omega

theorem not_p1ThreeLieList_exc {p : ℕ} (hp5 : 5 < p) {d : ValidLieTypeIndex}
    (hd : (∃ q, d.1 = .E6 q) ∨ (∃ q, d.1 = .E7 q) ∨ (∃ q, d.1 = .E8 q) ∨
      (∃ q, d.1 = .twistedE6 q)) : ¬ CFSG.AGLEmbedding.P1ThreeLieList p d := by
  unfold CFSG.AGLEmbedding.P1ThreeLieList
  rintro (⟨n, q', hq', -⟩ | ⟨q', -, hq'⟩ | ⟨-, m, hm⟩ | ⟨q', ⟨-, -, hq'⟩ | ⟨-, -, -, hq'⟩⟩ | hch)
  · rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ <;> rw [hq] at hq' <;> cases hq'
  · rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ <;> rw [hq] at hq' <;> cases hq'
  · rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ <;> rw [hq] at hm <;> cases hm
  · rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ <;> rw [hq] at hq' <;> cases hq'
  · rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ <;> rw [hq] at hq' <;> cases hq'
  · unfold CFSG.AGLEmbedding.IsP1ChevTwoIndex at hch
    rcases hch with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨h5, -⟩ <;> omega


theorem sylowTorus_cat_E6_three {q : PrimePower} (hv : (LieTypeIndex.E6 q).Valid) {p : ℕ}
    (hp : p.Prime) (h7 : 7 ≤ p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 3) : SylowTorus (Cat ⟨.E6 q, hv⟩) p 3 := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at he
  have hS : SylowTorus (adjointGroup Tag.E6 K) p ([3, 3, 3].count 3) :=
    sylowTorus_of_blocks_of_three_lt 3 (Or.inl ⟨rfl, rfl⟩) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E6 e6ThreeWord) [3, 3, 3] e6Three_charpoly e6Three_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
  exact (show SylowTorus (adjointGroup Tag.E6 K) p 3 from hS).of_mulEquiv e.symm


theorem sylowTorus_cat_E7_six {q : PrimePower} (hv : (LieTypeIndex.E7 q).Valid) {p : ℕ}
    (hp : p.Prime) (h7 : 7 ≤ p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 6) : SylowTorus (Cat ⟨.E7 q, hv⟩) p 3 := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at he
  have hS : SylowTorus (adjointGroup Tag.E7 K) p ([2, 6, 6, 6].count 6) :=
    sylowTorus_of_blocks_of_three_lt 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E7 e7SixWord) [2, 6, 6, 6] e7Six_charpoly e7Six_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
  exact (show SylowTorus (adjointGroup Tag.E7 K) p 3 from hS).of_mulEquiv e.symm

theorem sylowTorus_cat_twE6_six {q : PrimePower} (hv : (LieTypeIndex.twistedE6 q).Valid) {p : ℕ}
    (hp : p.Prime) (h7 : 7 ≤ p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 6) : SylowTorus (Cat ⟨.twistedE6 q, hv⟩) p 3 := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hpK : ¬ p ∣ q.p ^ q.exponent := by
    rw [← PrimePower.card_def]
    exact not_dvd_card_of_ne hp hpq
  have he' : orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p) = 6 := by
    rw [← PrimePower.card_def]
    exact he
  exact (CFSG.HardMathSupport.Lang.TwE6Step3.sylowTorus_twistedE6_six q.prime_p q.exponent_pos K
    hK σ hσ hp h7 hpK he').of_mulEquiv e.symm

theorem seitzExcHighE6Three_of_cube (hcube : ExcCubeHighAt LieTypeIndex.E6 3) :
    SeitzExcHighE6Three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hFd, hQ, hr, hn⟩
  obtain ⟨hp5, q, hdq, -, hord⟩ := hQ
  have hdq' : d = LieTypeIndex.E6 q := hdq
  subst hdq'
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_E6 q).symm)
  have h7 := seven_le_of_orderOf_three hp hp5 hord
  have hq1 : 1 ≤ q.card := by
    rw [PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  exact planeGen_of_cube hp (conj_injective_cat_E6 q hv) (sylowTorus_cat_E6_three hv hp h7 hpq hord)
    (fun hex' => hcube q hv p hp hp2 hpq
      (not_p1ThreeLieList_exc (by omega) (Or.inl ⟨q, rfl⟩))
      (not_dvd_sq_sub_one_of_orderOf hp hq1 hord (by omega)) hord hex') hE hc hin hn

theorem seitzExcHighE7Six_of_cube (hcube : ExcCubeHighAt LieTypeIndex.E7 6) :
    SeitzExcHighE7Six := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hFd, hQ, hr, hn⟩
  obtain ⟨hp5, q, hdq, -, hord⟩ := hQ
  have hdq' : d = LieTypeIndex.E7 q := hdq
  subst hdq'
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_E7 q).symm)
  have h7 := seven_le_of_orderOf_six hp hord
  have hq1 : 1 ≤ q.card := by
    rw [PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  exact planeGen_of_cube hp (conj_injective_cat_E7 q hv) (sylowTorus_cat_E7_six hv hp h7 hpq hord)
    (fun hex' => hcube q hv p hp hp2 hpq
      (not_p1ThreeLieList_exc (by omega) (Or.inr (Or.inl ⟨q, rfl⟩)))
      (not_dvd_sq_sub_one_of_orderOf hp hq1 hord (by omega)) hord hex') hE hc hin hn

theorem seitzExcHighTwE6Six_of_cube (hcube : ExcCubeHighAt LieTypeIndex.twistedE6 6) :
    SeitzExcHighTwE6Six := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hFd, hQ, hr, hn⟩
  obtain ⟨hp5, q, hdq, -, hord⟩ := hQ
  have hdq' : d = LieTypeIndex.twistedE6 q := hdq
  subst hdq'
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_twistedE6 q).symm)
  have h7 := seven_le_of_orderOf_six hp hord
  have hq1 : 1 ≤ q.card := by
    rw [PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  exact planeGen_of_cube hp (conj_injective_cat_twistedE6 q hv)
    (sylowTorus_cat_twE6_six hv hp h7 hpq hord)
    (fun hex' => hcube q hv p hp hp2 hpq
      (not_p1ThreeLieList_exc (by omega) (Or.inr (Or.inr (Or.inr ⟨q, rfl⟩))))
      (not_dvd_sq_sub_one_of_orderOf hp hq1 hord (by omega)) hord hex') hE hc hin hn

end Classes

end CFSG.LieType.SeitzGeneration.ExcHigh
