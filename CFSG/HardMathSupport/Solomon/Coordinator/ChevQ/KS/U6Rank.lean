module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Fixed

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux OuterFourInAux

section Count

theorem isElemAbelian_zpowers_of_cube {X : Type} [Group X] {x : X} (hx : x ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) := by
  rw [Subgroup.zpowers_eq_closure]
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a rfl b rfl
    rfl
  · rintro a rfl
    exact hx

theorem pRank_add_four_le_of_torus {X : Type} [Group X] [Finite X] {K B J U T : Subgroup X}
    {x : X} (hBel : CFSG.Open.IsElemAbelian 3 B) (hx : x ∈ B) (hxI : ¬ InnerAt K x)
    (hJK : J ≤ K) (hJx : J ≤ Subgroup.centralizer ({x} : Set X))
    (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 ↥U) (hUJ : U ≤ J)
    (hTJ : T ≤ J) (hTel : CFSG.Open.IsElemAbelian 3 T) (hTcard : Nat.card T = 3 ^ 3)
    (hTN : T ≤ Subgroup.normalizer (U : Set X))
    (hTC : T ⊓ Subgroup.centralizer (K : Set X) = ⊥) :
    CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) + 4 ≤
      GLATwoLocalRank 3 X := by
  classical
  have hx3 : x ^ 3 = 1 := hBel.2 x hx
  have hx1 : x ≠ 1 := by
    intro h
    apply hxI
    rw [h]
    exact ⟨1, K.one_mem, by simp⟩
  set D : Subgroup X := B ⊓ Subgroup.centralizer (K : Set X) with hD
  have hDel : CFSG.Open.IsElemAbelian 3 D := CFSG.Open.IsElemAbelian.mono hBel inf_le_left
  have hDcard : Nat.card D = 3 ^ CFSG.Open.pRank 3 D :=
    Bal209TwoAux.card_eq_pow_pRank Nat.prime_three hDel
  have hTK : T ≤ K := hTJ.trans hJK
  have hTD : ∀ a ∈ T, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 a (hTK ha)
  have hTDbot : T ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzT, hzD⟩ := Subgroup.mem_inf.1 hz
    have hz' : z ∈ T ⊓ Subgroup.centralizer (K : Set X) := ⟨hzT, (Subgroup.mem_inf.1 hzD).2⟩
    rw [hTC] at hz'
    exact hz'
  have hTDel : CFSG.Open.IsElemAbelian 3 (T ⊔ D) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hTel hDel hTD
  have hTDcard : Nat.card ↥(T ⊔ D) = 3 ^ (3 + CFSG.Open.pRank 3 D) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.i224_card_sup hTD hTDbot, hTcard, hDcard,
      pow_add]
  have hTDx : T ⊔ D ≤ Subgroup.centralizer ({x} : Set X) := by
    refine sup_le (fun t ht => ?_) (fun d hd => ?_)
    · exact hJx (hTJ ht)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Bal209F4Aux.commute_of_elemAbelian hBel (Subgroup.mem_inf.1 hd).1 hx).eq
  have hWcomm : ∀ a ∈ T ⊔ D, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hax : Commute a x := Subgroup.mem_centralizer_singleton_iff.1 (hTDx ha)
    exact (hax.zpow_right j).eq
  have hTDinner : T ⊔ D ≤ Bal209F4Aux.innerSub K := by
    refine sup_le (fun t ht => ?_) (fun d hd => ?_)
    · refine Bal209F4Aux.mem_innerSub.2 ⟨t, hTK ht, ?_⟩
      rw [inv_mul_cancel]
      exact Subgroup.one_mem _
    · refine Bal209F4Aux.mem_innerSub.2 ⟨1, K.one_mem, ?_⟩
      rw [inv_one, one_mul]
      exact (Subgroup.mem_inf.1 hd).2
  have hWbot : (T ⊔ D) ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz2
    rw [Subgroup.mem_bot]
    by_cases hj : (3 : ℤ) ∣ j
    · obtain ⟨l, rfl⟩ := hj
      have hx3z : x ^ (3 : ℤ) = 1 := by simpa using hx3
      rw [zpow_mul, hx3z, one_zpow]
    · exact absurd (Bal209F4Aux.mem_innerSub.1
        (Bal209F4Aux.mem_of_zpow_mem hx3 hx1 hj (hTDinner hz1))) hxI
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hWcard : Nat.card ↥((T ⊔ D) ⊔ Subgroup.zpowers x) =
      3 ^ (CFSG.Open.pRank 3 D + 4) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.i224_card_sup hWcomm hWbot, hTDcard, hxcard,
      show CFSG.Open.pRank 3 D + 4 = (3 + CFSG.Open.pRank 3 D) + 1 by omega, pow_succ]
  have hWel : CFSG.Open.IsElemAbelian 3 ((T ⊔ D) ⊔ Subgroup.zpowers x) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hTDel (isElemAbelian_zpowers_of_cube hx3) hWcomm
  have hWN : (T ⊔ D) ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set X) := by
    refine sup_le (sup_le hTN (fun d hd => ?_)) (Subgroup.zpowers_le.2 ?_)
    · exact Bal209TwoAux.mem_normalizer_of_mem_centralizer (hUJ.trans hJK)
        (Subgroup.mem_inf.1 hd).2
    · refine Bal209TwoAux.mem_normalizer_of_mem_centralizer hUJ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subgroup.mem_centralizer_singleton_iff.1 (hJx hj)
  exact Bal209TwoAux.le_glaTwoLocalRank_of_elemAb Nat.prime_three hU1 hU2 hWN hWel hWcard

end Count

section Torus


theorem unitary_witness_six {F : Type} [Field F] [Finite F] {Q f d : ℕ} (hQ : Q = 2 ^ f)
    (hF : Nat.card F = Q ^ 2) (hf : 1 ≤ f) (hd6 : 6 ≤ d) (hd3 : 3 ∣ d) (hq3 : 3 ∣ 2 ^ f + 1)
    {J : Type} [Group J] [Finite J] (hperf : commutator J = ⊤)
    (ρ : J →* StatedProj (StatedSU d Q F)) (hρ : Function.Surjective ρ)
    (hρk : ρ.ker = Subgroup.center J) :
    ∃ E P : Subgroup J, CFSG.Open.IsElemAbelian 3 E ∧ E ⊓ Subgroup.center J = ⊥ ∧
      Nat.card E = 3 ^ (d - 3) ∧ P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧
      E ≤ Subgroup.normalizer (P : Set J) := by
  subst hQ
  have hdq : (d, 2 ^ f) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  obtain ⟨U, E, hU0, hU2, hEU, hEab, hEcard, hEker⟩ :=
    CFSG.StandardType.ggTorusLift_unitary (K := F) (n := f) (d := d) (p := 3) hF hf (by omega)
      hdq Nat.prime_three hq3 J ρ hρ hρk.le hperf
  have hrank : CFSG.StandardType.ggUnitaryTorusRank 3 d = d - 3 := by
    simp [CFSG.StandardType.ggUnitaryTorusRank, hd3]
  rw [hrank] at hEcard
  have hEker' : E ⊓ ρ.ker = ⊥ := hEker
  rw [hρk] at hEker'
  exact ⟨E, U, hEab, hEker', hEcard, hU0, hU2, hEU⟩

theorem u6Two_torus {J : Type} [Group J] [Finite J] (hperf : commutator J = ⊤)
    (hLie : IsLieQuot J IsU6TwoIndex) :
    ∃ E P : Subgroup J, CFSG.Open.IsElemAbelian 3 E ∧ E ⊓ Subgroup.center J = ⊥ ∧
      Nat.card E = 3 ^ 3 ∧ P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧ E ≤ Subgroup.normalizer (P : Set J) := by
  obtain ⟨⟨idx, hv⟩, ⟨q, hq, hidx⟩, ⟨e⟩⟩ := hLie
  have hdq : idx = TauCeti.LieTypeIndex.twistedA 5 q := hidx
  subst hdq
  obtain ⟨-, F, hfield, hfinite, hcard, ⟨Φ⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv e
  have hq2 : q.p = 2 := hq.1
  have hq1 : q.exponent = 1 := hq.2
  let ρ : J →* StatedProj (StatedSU (5 + 1) (q.p ^ q.exponent) F) :=
    Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))
  have hρ : Function.Surjective ρ := Φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center J := by
    ext x
    rw [MonoidHom.mem_ker]
    change Φ (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center J
    rw [map_eq_one_iff Φ Φ.injective, QuotientGroup.eq_one_iff]
  have hq3 : 3 ∣ 2 ^ q.exponent + 1 := by rw [hq1]; norm_num
  obtain ⟨E, P, h1, h2, h3, h4, h5, h6⟩ :=
    unitary_witness_six (Q := q.p ^ q.exponent) (f := q.exponent) (d := 5 + 1)
      (by rw [hq2]) hcard (by omega) (by norm_num) (by norm_num) hq3 hperf ρ hρ hρk
  exact ⟨E, P, h1, h2, by simpa using h3, h4, h5, h6⟩

theorem u6_twoLocal_witness {X : Type} [Group X] [Finite X] (hKG : CFSG.Open.IsKGroup X)
    {K B : Subgroup X} {x : X} (hK : CFSG.Open.IsComponentOf K ⊤)
    (hBel : CFSG.Open.IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hLie : IsLieQuot ↥K IsU6EightIndex) (hx : x ∈ B) (hxI : ¬ InnerAt K x)
    (hFx : FieldAutU 6 (↥K ⧸ Subgroup.center ↥K) (actHom K ⟨x, hBN hx⟩)) :
    CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) + 4 ≤
      GLATwoLocalRank 3 X := by
  obtain ⟨J, hJ, -, hJq, hJL⟩ := u6Fixed X K x hK hLie (hBN hx) (hBel.2 x hx) hFx
  obtain ⟨E, P, hEel, hEZ, hEcard, hP1, hP2, hEP⟩ := u6Two_torus hJq.1 hJL
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hJx : J ≤ Subgroup.centralizer ({x} : Set X) := hJ.1.trans inf_le_right
  refine pRank_add_four_le_of_torus (J := J) (U := P.map J.subtype) (T := E.map J.subtype)
    hBel hx hxI hJK hJx ?_ ?_ (Subgroup.map_subtype_le P) (Subgroup.map_subtype_le E)
    (CFSG.SectionRank.isElemAbelian_map hEel J.subtype)
    ((Subgroup.card_map_of_injective J.subtype_injective).trans hEcard)
    ((Subgroup.map_mono hEP).trans (Subgroup.le_normalizer_map J.subtype)) ?_
  · exact fun h => hP1 ((Subgroup.map_eq_bot_iff_of_injective P J.subtype_injective).1 h)
  · exact hP2.map J.subtype
  · rw [eq_bot_iff]
    rintro z ⟨⟨e, he, rfl⟩, hzC⟩
    have hecen : e ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzC (g : X) (hJK g.2))
    have he1 : e ∈ E ⊓ Subgroup.center ↥J := ⟨he, hecen⟩
    rw [hEZ, Subgroup.mem_bot] at he1
    rw [he1]
    exact Subgroup.one_mem _

end Torus

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
