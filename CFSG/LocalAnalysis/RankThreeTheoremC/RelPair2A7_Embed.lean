module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.RankThree.PartTwo.Sec4.T444.Lift
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup Equiv

variable {L : Type} [Group L]

@[expose] noncomputable def a7AutEquiv (e : L ≃* alternatingGroup (Fin 7)) :
    MulAut L ≃* Perm (Fin 7) :=
  (MulAut.congr e).trans (MulEquiv.ofBijective
    (MulAut.conjNormal (H := alternatingGroup (Fin 7)) :
      Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))).symm

@[expose] def a7Emb (e : L ≃* alternatingGroup (Fin 7)) : L →* Perm (Fin 7) :=
  (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom

theorem a7Emb_injective (e : L ≃* alternatingGroup (Fin 7)) : Function.Injective (a7Emb e) :=
  (Subgroup.subtype_injective _).comp e.injective

theorem a7Emb_apply (e : L ≃* alternatingGroup (Fin 7)) (k : L) :
    a7Emb e k = ((e k : alternatingGroup (Fin 7)) : Perm (Fin 7)) := rfl

theorem a7AutEquiv_conj (e : L ≃* alternatingGroup (Fin 7)) (k : L) :
    a7AutEquiv e (MulAut.conj k) = a7Emb e k := by
  unfold a7AutEquiv
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  simp [MulEquiv.ofBijective_apply, MulAut.conjNormal_apply, MulAut.conj_apply, MulAut.congr_apply,
    a7Emb_apply]

theorem le_pCore_of_isSubnormal_of_isPGroup {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {S : Subgroup X} (hS : S.IsSubnormal) (hp : IsPGroup p S) :
    S ≤ CFSG.pCore p X := by
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val = p} hS
  rw [← CFSG.pCore_eq_piCore ↥S p, ← CFSG.pCore_eq_piCore X p] at h
  have htop : CFSG.pCore p ↥S = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, hp.of_equiv Subgroup.topEquiv.symm⟩)
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h.le.trans inf_le_right

theorem center_eq_bot_of_isComponent {X : Type} [Group X] [Finite X]
    (h3 : CFSG.pCore 3 X = ⊥) (h3' : CFSG.pPrimeCore 3 X = ⊥) {J : Subgroup X}
    (hJ : CFSG.IsComponent J) : Subgroup.center J = ⊥ := by
  by_contra hne
  have hcard : Nat.card (Subgroup.center J) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hcard
  have hfact : Fact q.Prime := ⟨hq⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center J) q hqd
  set zJ : J := (z : J) with hzJ
  have hzc : ∀ g : J, g * zJ = zJ * g := fun g => (Subgroup.mem_center_iff.mp z.2 g)
  set Zq : Subgroup J := Subgroup.zpowers zJ with hZq
  have hZqN : Zq.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * zJ ^ k * g⁻¹ = zJ ^ k := by
      have hc : Commute g (zJ ^ k) := (Commute.zpow_right (hzc g) k)
      rw [hc.eq]; group
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ _
  set W : Subgroup X := Zq.map J.subtype with hW
  have hWsub : W.IsSubnormal := by
    refine Subgroup.IsSubnormal.step W J (Subgroup.map_subtype_le _) hJ.2 ?_
    have : W.subgroupOf J = Zq := Subgroup.comap_map_eq_self_of_injective J.subtype_injective Zq
    rw [this]
    exact hZqN
  have hWcard : Nat.card W = q := by
    rw [hW, Subgroup.card_map_of_injective J.subtype_injective, hZq, Nat.card_zpowers]
    rw [hzJ]
    exact (Subgroup.orderOf_coe z).trans hz
  have hW1 : W = ⊥ := by
    by_cases hq3 : q = 3
    · subst hq3
      refine le_bot_iff.mp (h3 ▸ le_pCore_of_isSubnormal_of_isPGroup
        hWsub ?_)
      exact IsPGroup.of_card (n := 1) (by rw [hWcard]; simp)
    · refine le_bot_iff.mp (h3' ▸ CFSG.RankThree.PartTwo.Sec4.le_pPrimeCore_of_isSubnormal hWsub ?_)
      rw [hWcard]
      intro h
      exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h).symm
  rw [hW1, Subgroup.card_bot] at hWcard
  exact hq.one_lt.ne hWcard

theorem a7Emb_range (e : L ≃* alternatingGroup (Fin 7)) :
    (a7Emb e).range = alternatingGroup (Fin 7) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact (e k).2
  · intro hx
    exact ⟨e.symm ⟨x, hx⟩, by simp [a7Emb_apply]⟩

theorem exists_isElemAbelian_nine (e : L ≃* alternatingGroup (Fin 7)) :
    ∃ E : Subgroup L, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  open CFSG.RankThree.PartTwo.KFacts.KP2 in
  refine ⟨eNine.comap (a7Emb e), ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply a7Emb_injective e
    obtain ⟨i, j, hij⟩ := x.2
    obtain ⟨k, l, hkl⟩ := y.2
    simp only [Subgroup.coe_mul, map_mul, hij, hkl]
    exact eNineF_comm i j k l
  · apply a7Emb_injective e
    rw [map_pow, map_one]
    obtain ⟨i, j, hij⟩ := hx
    rw [hij]
    exact eNineF_pow_three i j
  · have hle : eNine ≤ (a7Emb e).range :=
      (eNine_le_alternatingGroup).trans (a7Emb_range e).ge
    have h1 := Subgroup.map_comap_eq_self hle
    rw [← card_eNine, ← h1, Subgroup.card_map_of_injective (a7Emb_injective e), h1]

theorem eq_of_isComponent {X : Type} [Group X] [Finite X] (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hrk : ∀ E : Subgroup X, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9)
    {J : Subgroup X} (hJ : CFSG.IsComponent J) (hZ : Subgroup.center J = ⊥)
    (e : J ≃* alternatingGroup (Fin 7)) {K : Subgroup X} (hK : CFSG.IsComponent K) : K = J := by
  by_contra hne
  have hcomm : ⁅K, J⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hK hJ).resolve_left hne
  have hKC : K ≤ Subgroup.centralizer (J : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have h3K : 3 ∣ Nat.card K := CFSG.RankThree.PartTwo.Sec4.three_dvd_card_of_isComponent h3' hK
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3K
  obtain ⟨E, hE, hE9⟩ := exists_isElemAbelian_nine e
  set E₀ : Subgroup X := E.map J.subtype with hE₀
  have hE₀J : ∀ x ∈ E₀, x ∈ J := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hE₀ab : CFSG.Open.IsElemAbelian 3 E₀ := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨x', hx', hxe⟩ := x.2
      obtain ⟨y', hy', hye⟩ := y.2
      apply Subtype.ext
      have := hE.1.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩
      have h2 := congrArg (fun z : E => ((z : J) : X)) this
      simpa [← hxe, ← hye] using h2
    · obtain ⟨y, hy, rfl⟩ := hx
      have := hE.2 y hy
      simp only [Subgroup.subtype_apply, ← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hE₀9 : Nat.card E₀ = 9 := by
    rw [hE₀, Subgroup.card_map_of_injective J.subtype_injective, hE9]
  set k' : X := ((k : K) : X) with hk'
  have hk'3 : orderOf k' = 3 := by
    rw [hk', Subgroup.orderOf_coe]
    exact hk
  have hk'C : ∀ x ∈ J, x * k' = k' * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hKC k.2) x hx
  set F : Subgroup X := Subgroup.closure ((E₀ : Set X) ∪ {k'}) with hF
  have hpair : ((E₀ : Set X) ∪ {k'}).Pairwise Commute := by
    intro x hx y hy hxy
    rcases hx with hx | hx
    · rcases hy with hy | hy
      · exact congrArg Subtype.val (hE₀ab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      · rw [Set.mem_singleton_iff.mp hy]
        exact hk'C x (hE₀J x hx)
    · rcases hy with hy | hy
      · rw [Set.mem_singleton_iff.mp hx]
        exact (hk'C y (hE₀J y hy)).symm
      · exact absurd ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm) hxy
  have hFcomm : IsMulCommutative F := Subgroup.isMulCommutative_closure hpair
  have hF3 : ∀ x ∈ F, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hE₀ab.2 x hx
      · rw [Set.mem_singleton_iff.mp hx, ← hk'3]
        exact pow_orderOf_eq_one k'
    | one => exact one_pow 3
    | mul x y hx hy hx3 hy3 =>
      have hc : Commute x y := congrArg Subtype.val (hFcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [hc.mul_pow, hx3, hy3, one_mul]
    | inv x hx hx3 =>
      rw [inv_pow, hx3, inv_one]
  have hE₀F : E₀ ≤ F := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hk'F : k' ∈ F := Subgroup.subset_closure (Or.inr rfl)
  have hk'E₀ : k' ∉ E₀ := by
    intro h
    have hkJ : k' ∈ J := hE₀J k' h
    have hkz : (⟨k', hkJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hk'C g g.2)
    rw [hZ, Subgroup.mem_bot] at hkz
    have : k' = 1 := congrArg Subtype.val hkz
    rw [this, orderOf_one] at hk'3
    exact absurd hk'3 (by norm_num)
  have hle := hrk F ⟨hFcomm, hF3⟩
  have hFE : E₀ = F := Subgroup.eq_of_le_of_card_ge hE₀F (by rw [hE₀9]; exact hle)
  exact hk'E₀ (hFE ▸ hk'F)

theorem exists_injective_hom_perm_seven {X : Type} [Group X] [Finite X]
    (h3 : CFSG.pCore 3 X = ⊥) (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hrk : ∀ E : Subgroup X, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9)
    {J : Subgroup X} (hJ : CFSG.IsComponent J)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) :
    ∃ ι : X →* Perm (Fin 7), Function.Injective ι ∧ alternatingGroup (Fin 7) ≤ ι.range := by
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ := center_eq_bot_of_isComponent h3 h3' hJ
  let q1 : J ⧸ Subgroup.center J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e' : J ≃* alternatingGroup (Fin 7) := q1.symm.trans e
  have hall : ∀ K : Subgroup X, CFSG.IsComponent K → K = J := fun K hK =>
    eq_of_isComponent h3' hrk hJ hZ e' hK
  have hlayer : CFSG.layer X = J := by
    simp only [CFSG.layer.eq_sSup]
    have : {K : Subgroup X | CFSG.IsComponent K} = {J} :=
      Set.ext fun K => ⟨fun hK => hall K hK, fun hK => hK ▸ hJ⟩
    rw [this, sSup_singleton]
  have hJn : J.Normal := by
    rw [← hlayer]
    have := CFSG.LocalCores.layer_characteristic (G := X)
    infer_instance
  have hF : CFSG.fittingSubgroup X = ⊥ := by
    rw [CFSG.Fitting_eq_pcore X 3 h3', h3]
  have hgf : CFSG.generalizedFitting X = J := by
    rw [CFSG.generalizedFitting, hF, hlayer, bot_sup_eq]
  have hCle : Subgroup.centralizer (J : Set X) ≤ J := by
    have := CFSG.centralizer_generalizedFitting_le X
    rwa [hgf] at this
  let c : X →* MulAut J := MulAut.conjNormal
  let ι : X →* Perm (Fin 7) := (a7AutEquiv e').toMonoidHom.comp c
  refine ⟨ι, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have hcx : c x = 1 := (a7AutEquiv e').injective (by simpa [ι] using hx)
    have hxC : x ∈ Subgroup.centralizer (J : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := congrArg (fun φ : MulAut J => ((φ ⟨l, hl⟩ : J) : X)) hcx
      simp only [c, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      have h2 : x * l = l * x := by
        calc x * l = (x * l * x⁻¹) * x := by group
          _ = l * x := by rw [h1]
      exact h2.symm
    have hxJ : x ∈ J := hCle hxC
    have hxz : (⟨x, hxJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rw [hZ, Subgroup.mem_bot] at hxz
    exact congrArg Subtype.val hxz
  · intro a ha
    refine ⟨((e'.symm ⟨a, ha⟩ : J) : X), ?_⟩
    have hc : c ((e'.symm ⟨a, ha⟩ : J) : X) = MulAut.conj (e'.symm ⟨a, ha⟩) := by
      apply MulEquiv.ext
      intro l
      apply Subtype.ext
      simp [c, MulAut.conjNormal_apply, MulAut.conj_apply]
    simp only [ι, MonoidHom.comp_apply, hc, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [a7AutEquiv_conj, a7Emb_apply]
    simp

end CFSG.LocalAnalysis.RankThreeTheoremC
