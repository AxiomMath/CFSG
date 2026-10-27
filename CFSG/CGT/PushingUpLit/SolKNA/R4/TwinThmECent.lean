module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.QuatAlg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf4Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmQ8CentEng
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped commutatorElement

namespace ThmE

section Cent

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {X : Subgroup G} [X.Normal]

theorem exists_commutator_of_quat (hr : 3 ≤ r) {P : Subgroup G}
    (e : ↥P ≃* QuaternionGroup (2 ^ (r - 2))) :
    ∃ x ∈ P, ∃ y ∈ P, ⁅x, y⁆ * ⁅x, y⁆ = 1 ∧ ⁅x, y⁆ ≠ 1 := by
  obtain ⟨k, hk⟩ := QSub.Alg.exists_half (m := r - 2) (by omega)
  have hc : ⁅(QuaternionGroup.a k : QuaternionGroup (2 ^ (r - 2))), QuaternionGroup.xa 0⁆ =
      QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) := by
    rw [QSub.Alg.commutator_a_xa, hk]
  refine ⟨(e.symm (QuaternionGroup.a k) : G), (e.symm _).2, (e.symm (QuaternionGroup.xa 0) : G),
    (e.symm _).2, ?_, ?_⟩
  · have h1 : (⁅(e.symm (QuaternionGroup.a k) : G), (e.symm (QuaternionGroup.xa 0) : G)⁆ : G) =
        ((e.symm ⁅(QuaternionGroup.a k : QuaternionGroup (2 ^ (r - 2))), QuaternionGroup.xa 0⁆ :
          ↥P) : G) := by
      simp only [commutatorElement_def, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1, hc]
    have := QSub.Alg.a_n_mul_self (n := 2 ^ (r - 2))
    rw [← Subgroup.coe_mul, ← map_mul, this, map_one, Subgroup.coe_one]
  · have h1 : (⁅(e.symm (QuaternionGroup.a k) : G), (e.symm (QuaternionGroup.xa 0) : G)⁆ : G) =
        ((e.symm ⁅(QuaternionGroup.a k : QuaternionGroup (2 ^ (r - 2))), QuaternionGroup.xa 0⁆ :
          ↥P) : G) := by
      simp only [commutatorElement_def, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1, hc]
    intro h
    have h2 : e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) = 1 :=
      Subtype.ext h
    have h3 : (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) :
        QuaternionGroup (2 ^ (r - 2))) = 1 := by simpa using h2
    exact QSub.Alg.a_n_ne_one h3

theorem eq_of_map_cent (hr : 3 ≤ r) (hΩ : HypOmegaGen Ω)
    (hq : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hXc : X ≤ Subgroup.center G) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : K.map (QuotientGroup.mk' X) = J.map (QuotientGroup.mk' X)) : K = J := by
  by_contra hKJ
  obtain ⟨P, hP, ⟨e⟩⟩ := hq K hK
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  obtain ⟨r₁, hr₁P, r₂, hr₂P, hz₀sq, hz₀1⟩ := exists_commutator_of_quat hr e
  have hr₁K : r₁ ∈ K := hP.1 hr₁P
  have hr₂K : r₂ ∈ K := hP.1 hr₂P
  have hz₀K : ⁅r₁, r₂⁆ ∈ K := by
    simp only [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hr₁K hr₂K) (K.inv_mem hr₁K)) (K.inv_mem hr₂K)
  have hzz : ⁅r₁, r₂⁆ = z := (hz.unique _ hz₀K hz₀sq).resolve_left hz₀1
  have hlift : ∀ r ∈ K, ∃ j ∈ J, ∃ ν ∈ Subgroup.center G, r = j * ν := by
    intro r hr
    have hr' : QuotientGroup.mk' X r ∈ J.map (QuotientGroup.mk' X) :=
      h ▸ Subgroup.mem_map_of_mem _ hr
    obtain ⟨j, hj, hjr⟩ := hr'
    have hν : j⁻¹ * r ∈ X := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' X (j⁻¹ * r) = 1
      rw [map_mul, map_inv, hjr, inv_mul_cancel]
    exact ⟨j, hj, j⁻¹ * r, hXc hν, by group⟩
  obtain ⟨j₁, hj₁, ν₁, hν₁, hr₁e⟩ := hlift r₁ hr₁K
  obtain ⟨j₂, hj₂, ν₂, hν₂, hr₂e⟩ := hlift r₂ hr₂K
  have hzJ : z ∈ J := by
    have : ⁅r₁, r₂⁆ = ⁅j₁, j₂⁆ := by
      rw [hr₁e, hr₂e]
      exact AscE186.commutator_mul_central hν₁ hν₂
    rw [← hzz, this]
    simp only [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem hj₁ hj₂) (J.inv_mem hj₁)) (J.inv_mem hj₂)
  have hzt : z = t := (ht.unique z hzJ hz.sq).resolve_left hz.ne_one
  have hcommKJ := Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ hKJ hz (hzt ▸ ht)
  have hzO : z ∈ oddCoreOf K := by
    have h1 : ⁅r₁, r₂⁆ = ⁅j₁, r₂⁆ := by
      have := AscE186.commutator_mul_central (a := j₁) (b := r₂) (c := ν₁) (d := 1) hν₁
        (Subgroup.one_mem _)
      rw [mul_one] at this
      rw [hr₁e]
      exact this
    have h2 : ⁅j₁, r₂⁆ ∈ ⁅K, J⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hj₁ hr₂K
    rw [← hzz, h1]
    exact (hcommKJ h2).1
  have hz1 := eq_one_of_isPGroup_of_mem_odd (odd_natCard_oddCoreOf K) hzO
    (isPGroup_zpowers_of_involution hz.ne_one hz.sq)
  exact hz.ne_one hz1

theorem normalizer_of_map_cent (hr : 3 ≤ r) (hΩ : HypOmegaGen Ω)
    (hq : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hXc : X ≤ Subgroup.center G) {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : QuotientGroup.mk' X u ∈ Subgroup.normalizer
      ((K.map (QuotientGroup.mk' X) : Subgroup (G ⧸ X)) : Set (G ⧸ X))) :
    u ∈ Subgroup.normalizer (K : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  refine eq_of_map_cent hr hΩ hq hXc (hΩ.conjInvariant u K hK) hK ?_
  rw [AscQuot.map_conjSub]
  exact mem_normalizer_iff_conjSub_eq.mp hu

theorem centQuotGen (hr : 3 ≤ r) (hΩ : HypOmegaGen Ω)
    (hq : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hXc : X ≤ Subgroup.center G) (hmeet : ∀ J ∈ Ω, J ⊓ X = ⊥) : CentQuotGen Ω X where
  hyp := hΩ
  hyp' := CentQ.quotient_hypOmegaGen hΩ X hXc (fun K hK => by
    rw [inf_comm, hmeet K hK, Subgroup.card_bot]
    exact odd_one)
  meet := hmeet
  eq_of_map := fun K hK J hJ h => eq_of_map_cent hr hΩ hq hXc hK hJ h
  normalizer_of_map := fun K hK u hu => normalizer_of_map_cent hr hΩ hq hXc hK hu

theorem quat_quot_cent
    (hq : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hmeet : ∀ J ∈ Ω, J ⊓ X = ⊥) :
    ∀ L ∈ quotFamily Ω X, ∃ P : Subgroup (G ⧸ X), IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
  rintro _ ⟨K, hK, rfl⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hq K hK
  have hPN : P ⊓ X = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right X hP.1).trans (hmeet K hK).le)
  obtain ⟨V₀, hV₀, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := K.map (QuotientGroup.mk' X))
    (IsPGroup.of_bot) bot_le
  have hKcard : Nat.card ↥(K.map (QuotientGroup.mk' X)) = Nat.card K :=
    (Nat.card_congr (AscQuot.quotRestrictEquiv (hmeet K hK)).toEquiv).symm
  have hcard : Nat.card P = Nat.card V₀ := by
    rw [natCard_eq_pow_of_isSylow2In hP, natCard_eq_pow_of_isSylow2In hV₀, hKcard]
  have hmapcard : Nat.card ↥(P.map (QuotientGroup.mk' X)) = Nat.card P :=
    (Nat.card_congr (AscQuot.quotRestrictEquiv hPN).toEquiv).symm
  exact ⟨P.map (QuotientGroup.mk' X),
    hV₀.of_natCard_le (hP.2.1.map _) (Subgroup.map_mono hP.1) (by rw [hmapcard, hcard]),
    ⟨(AscQuot.quotRestrictEquiv hPN).symm.trans e⟩⟩

variable (Ω X) in
structure CentQuot : Prop extends CentQuotGen Ω X where
  central : X ≤ Subgroup.center G
  two : IsPGroup 2 ↥X

theorem centQuot (hr : 3 ≤ r) (hΩ : HypOmegaGen Ω)
    (hq : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hXc : X ≤ Subgroup.center G) (hX2 : IsPGroup 2 ↥X) (hmeet : ∀ J ∈ Ω, J ⊓ X = ⊥) :
    CentQuot Ω X :=
  { centQuotGen hr hΩ hq hXc hmeet with central := hXc, two := hX2 }

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.mem_of_conj_mem_dstar (c : MinCex r Ω K S R W H) {M : Subgroup G}
    (hMS : M ∈ dstarComp Ω K) {u : G} (hu : u ∈ M) (hu4 : orderOf u = 4) {x : G}
    (hx : x * u * x⁻¹ ∈ H) : x ∈ H :=
  E187C.mem_of_conj_mem_dstar_of c.hyp.trans
    (fun hu hu4 hx => e18_2 G Ω K S R W H c _ hu hu4 _ hx) hMS hu hu4 hx

theorem MinCex.cent_quot_stand [PrintedQuotCent r] (hr : 3 ≤ r) (c : MinCex r Ω K S R W H)
    {N : Subgroup G} [N.Normal] (hc : CentQuot Ω N) (hNH : N ≤ H) :
    ∃ (Sb : Sylow 2 (G ⧸ N)) (Rb Wb : Subgroup (G ⧸ N)),
      EStand r (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) Sb Rb Wb ∧
      TwinThmEW.CentPairs (quotFamily Ω N) (Sb : Subgroup (G ⧸ N)) Wb
        (H.map (QuotientGroup.mk' N)) := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  have h3 : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3 G Ω K S R W H c
  have hcls' : Q3CL.ClassicalClause (quotFamily Ω N) :=
    TwinThmE.classicalClause_quot_cent hΩ hc.hyp' c.stand.cls hc.two hc.meet
  have hq' := quat_quot_cent c.stand.quat hc.meet
  have hAΩ : ∀ J ∈ Ω, AEmpty Ω J :=
    aEmpty_forall_of_transitive hΩ.conjInvariant h3 c.stand.aEmpty
  set Sb : Sylow 2 (G ⧸ N) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S with hSbdef
  have hSb : (Sb : Subgroup (G ⧸ N)) = (S : Subgroup G).map (QuotientGroup.mk' N) :=
    Sylow.coe_mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S
  obtain ⟨Wb, hWb, hWbS', hWbn', hCb⟩ :=
    PrintedQuotCent.exists_W G Ω K S R W H N c hc.central hc.two hNH hc.meet
  have hWbS : Wb ≤ (Sb : Subgroup (G ⧸ N)) := hSb ▸ hWbS'
  have hWbn : ∀ s ∈ (Sb : Subgroup (G ⧸ N)), conjSub s Wb = Wb := by
    rw [hSb]; exact hWbn'
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRR hRK
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'tw
  have hR'syl : IsSylow2In R' K' := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hR' hR'K'
  refine ⟨Sb, R.map (QuotientGroup.mk' N), Wb, ?_, by rw [hSb]; exact hCb⟩
  exact
    { hyp := hc.hyp'
      cls := hcls'
      quat := hq'
      two := TwinThmE.two_quot_cent c.stand.two hc.meet
      ih := EIH.mono (natCard_quotient_le N) c.stand.ih
      mem := map_mem_quotFamily hK
      aEmpty := hc.aEmpty_quotFamily hAΩ _ (map_mem_quotFamily hK)
      twin := ⟨K'.map (QuotientGroup.mk' N),
        ⟨map_mem_quotFamily hK'Ω, QuotientGroup.mk' N z,
          AscQuot.isUniqueInvolution_map_mk (hc.meet K hK) hzK,
          AscQuot.isUniqueInvolution_map_mk (hc.meet K' hK'Ω) hzK'⟩,
        hc.map_ne_of_ne hK hK'Ω hK'ne,
        R'.map (QuotientGroup.mk' N),
        mem_RSet_of_isSylow2In (map_mem_quotFamily hK'Ω)
          (TwinThmE.CentEng.isSylow2In_map_cent hc.toCentQuotGen hK'Ω hR'syl),
        Subgroup.map_mono hR'K', hSb ▸ Subgroup.map_mono hR'S⟩
      hR := ⟨mem_RSet_of_isSylow2In (map_mem_quotFamily hK)
          (TwinThmE.CentEng.isSylow2In_map_cent hc.toCentQuotGen hK hRsyl),
        Subgroup.map_mono hRK, hSb ▸ Subgroup.map_mono hRS⟩
      hW := ⟨hWb, hWbS, hWbn⟩ }

theorem MinCex.cent_quot_trans (c : MinCex r Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hc : CentQuot Ω N) :
    ∀ Jb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N)),
      ∃ hb ∈ H.map (QuotientGroup.mk' N),
        conjSub hb (K.map (QuotientGroup.mk' N)) = Jb := by
  intro Jb hJb
  obtain ⟨M, hM, hMeq⟩ := TwinThmE.CentEng.exists_lift_dstarComp hc.toCentQuotGen c.stand.mem hJb
  obtain ⟨h, hhH, hh⟩ := c.hyp.trans M hM
  refine ⟨QuotientGroup.mk' N h, Subgroup.mem_map_of_mem _ hhH, ?_⟩
  rw [← hMeq, ← hh, AscQuot.map_conjSub]

theorem MinCex.eq_bot_of_central [PrintedQuotCent r] (hr : 3 ≤ r) (c : MinCex r Ω K S R W H)
    {N : Subgroup G} [N.Normal] (hNc : N ≤ Subgroup.center G) (hN2 : IsPGroup 2 ↥N) (hNH : N ≤ H)
    (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥) : N = ⊥ := by
  by_contra hne
  have hc : CentQuot Ω N := centQuot hr c.stand.hyp c.stand.quat hNc hN2 hmeet
  obtain ⟨Sb, Rb, Wb, hst, hCb⟩ := c.cent_quot_stand hr hc hNH
  have h1 := c.minimal (G ⧸ N) (AscE186.natCard_quotient_lt hne) (quotFamily Ω N)
    (K.map (QuotientGroup.mk' N)) Sb Rb Wb (H.map (QuotientGroup.mk' N)) hst
    ⟨c.cent_quot_trans hc, hCb⟩
  exact c.proper (AscE186.eq_top_of_map_eq_top hNH h1)

end Cent

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
