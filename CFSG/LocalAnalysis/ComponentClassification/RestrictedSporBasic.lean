module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.DichotomyDefs

public noncomputable section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup

@[expose] def CompsSatisfy (X : Type) [Group X] (Q : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ B : Subgroup X, IsComponent B → Q B

@[expose] def IsoInvariant (Q : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y Y' : Type) [Group Y] [Group Y'], (Y ≃* Y') → Q Y' → Q Y

theorem CompsSatisfy.of_mulEquiv {X X' : Type} [Group X] [Group X']
    {Q : (Y : Type) → [Group Y] → Prop} (hQ : IsoInvariant Q) (e : X ≃* X')
    (h : CompsSatisfy X' Q) : CompsSatisfy X Q := by
  intro B hB
  exact hQ B _ (B.equivMapOfInjective e.toMonoidHom e.injective)
    (h _ (LocalCores.isComponent_map_mulEquiv e hB))

theorem CompsSatisfy.mono {X : Type} [Group X] {Q Q' : (Y : Type) → [Group Y] → Prop}
    (hQQ : ∀ (Y : Type) [Group Y], Q Y → Q' Y) (h : CompsSatisfy X Q) : CompsSatisfy X Q' :=
  fun B hB => hQQ B (h B hB)

theorem isoInvariant_not_three_dvd : IsoInvariant fun Y _ => ¬ 3 ∣ Nat.card Y := by
  intro Y Y' _ _ e h
  rwa [Nat.card_congr e.toEquiv]

theorem isoInvariant_card_quotient_center (N : Set ℕ) :
    IsoInvariant fun Y _ => Nat.card (Y ⧸ center Y) ∈ N := by
  intro Y Y' _ _ e h
  have f : Y ⧸ center Y ≃* Y' ⧸ center Y' :=
    QuotientGroup.congr (center Y) (center Y') e (Subgroup.map_center_eq e)
  rwa [Nat.card_congr f.toEquiv]

theorem isoInvariant_card_dvd (c : ℕ) : IsoInvariant fun Y _ => Nat.card Y ∣ c := by
  intro Y Y' _ _ e h
  rwa [Nat.card_congr e.toEquiv]

theorem compsSatisfy_card_dvd {K : Type} [Group K] :
    CompsSatisfy K fun Y _ => Nat.card Y ∣ Nat.card K :=
  fun B _ => Subgroup.card_subgroup_dvd_card B

theorem compsSatisfy_not_three_of_card {K : Type} [Group K] (h : ¬ 3 ∣ Nat.card K) :
    CompsSatisfy K fun Y _ => ¬ 3 ∣ Nat.card Y :=
  fun B _ h3 => h (h3.trans (Subgroup.card_subgroup_dvd_card B))

@[expose] def centralizerEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    ↥(centralizer ({x} : Set G)) ≃* ↥(centralizer ({e x} : Set H)) where
  toFun g := ⟨e g, mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp g.2])⟩
  invFun g := ⟨e.symm g, mem_centralizer_singleton_iff.mpr (by
    have hg := mem_centralizer_singleton_iff.mp g.2
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hg])⟩
  left_inv g := Subtype.ext (e.symm_apply_apply (g : G))
  right_inv g := Subtype.ext (e.apply_symm_apply (g : H))
  map_mul' g h := Subtype.ext (map_mul e (g : G) h)

@[expose] def centralizerSubtypeEquiv {M : Type*} [Group M] (H : Subgroup M) (t : H) :
    ↥(centralizer ({t} : Set H)) ≃* ↥(H ⊓ centralizer ({(t : M)} : Set M)) where
  toFun g := ⟨g.1, g.1.2, mem_centralizer_singleton_iff.mpr (by
    have := congrArg Subtype.val (mem_centralizer_singleton_iff.mp g.2)
    simpa using this)⟩
  invFun g := ⟨⟨g.1, g.2.1⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext (by
    simpa using mem_centralizer_singleton_iff.mp g.2.2))⟩
  left_inv g := rfl
  right_inv g := rfl
  map_mul' g h := rfl

@[expose] def conjEquiv {M : Type*} [Group M] (K : Subgroup M) (c : M) :
    ↥K ≃* ↥(K.map (MulAut.conj c).toMonoidHom) :=
  K.equivMapOfInjective _ (MulAut.conj c).injective

theorem compsSatisfy_of_charP {X : Type} [Group X] [Finite X]
    (h : Assembly.Dichotomy.dichotomyCharP 2 X) (Q : (Y : Type) → [Group Y] → Prop) :
    CompsSatisfy X Q := by
  intro B hB
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Assembly.Dichotomy.dichotomyCharP at h
  have hp2 : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  have hsolv : Group.IsSolvable (CFSG.pCore 2 X) :=
    have : Group.IsNilpotent (CFSG.pCore 2 X) := hp2.isNilpotent
    inferInstance
  have hc := (LocalCores.component_solvable_centralizer hsolv
    (CFSG.pCore_normal (p := 2) (G := X)).isSubnormal).1 B hB
  have hBle : B ≤ CFSG.pCore 2 X :=
    le_trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc) h
  have hp : IsPGroup 2 B := hp2.to_le hBle
  have : Nontrivial B := LocalCores.isQuasisimple_nontrivial hB.1
  have : Group.IsNilpotent B := hp.isNilpotent
  have : Group.IsPerfect B := hB.1.1
  exact Group.IsPerfect.not_isSolvable B inferInstance

theorem closure_normal_of_conj {K : Type*} [Group K] {S : Set K}
    (hS : ∀ k : K, ∀ s ∈ S, k * s * k⁻¹ ∈ S) : (closure S).Normal := by
  refine ⟨fun n hn k => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem s hs => exact subset_closure (hS k s hs)
  | one => simp
  | mul a b _ _ ha hb =>
    have : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
    rw [this]
    exact mul_mem ha hb
  | inv a _ ha =>
    have : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem ha

theorem not_three_dvd_card_of_witness {K : Type} [Group K] [Finite K] (S : Set K)
    (hS : ∀ k : K, ∀ s ∈ S, k * s * k⁻¹ ∈ S) (hcomm : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s)
    {y : K} (hy : orderOf y = 3) (h9 : ¬ 9 ∣ Nat.card K) (hyS : ∃ s ∈ S, y * s ≠ s * y) :
    CompsSatisfy K fun Y _ => ¬ 3 ∣ Nat.card Y := by
  intro B hB h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := closure S with hQdef
  have hQn : Q.Normal := closure_normal_of_conj hS
  have hpair : S.Pairwise Commute := fun s hs s' hs' _ => hcomm s hs s' hs'
  have hQc := (Subgroup.isMulCommutative_closure hpair).1.1
  have hQs : Group.IsSolvable Q := Group.isSolvable_of_comm hQc
  have hBQ : B ≤ centralizer (Q : Set K) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    ((LocalCores.component_solvable_centralizer hQs hQn.isSubnormal).1 B hB)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 h3
  have hxC : (x : K) ∈ centralizer (Q : Set K) := hBQ x.2
  have hx3 : orderOf (x : K) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hfac : (Nat.card K).factorization 3 = 1 := by
    have hpos : 0 < Nat.card K := Nat.card_pos
    have h3K : 3 ∣ Nat.card K := by
      rw [← hx3]
      exact orderOf_dvd_natCard _
    have h1 : 1 ≤ (Nat.card K).factorization 3 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hpos.ne').1 h3K
    have h2 : (Nat.card K).factorization 3 < 2 := by
      by_contra hge
      push Not at hge
      apply h9
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos.ne').2 hge
      simpa using this
    omega
  let Px : Sylow 3 K := Sylow.ofCard (zpowers (x : K)) (by rw [Nat.card_zpowers, hx3, hfac,
    pow_one])
  let Py : Sylow 3 K := Sylow.ofCard (zpowers y) (by rw [Nat.card_zpowers, hy, hfac, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Px Py
  have hyg : y ∈ (zpowers (x : K)).map (MulAut.conj g).toMonoidHom := by
    have : (Py : Subgroup K) = (g • Px : Sylow 3 K) := by rw [hg]
    have hy' : y ∈ (Py : Subgroup K) := mem_zpowers y
    rw [this, Sylow.coe_subgroup_smul] at hy'
    exact hy'
  have hCn : (centralizer (Q : Set K)).Normal := inferInstance
  have hyC : y ∈ centralizer (Q : Set K) := by
    obtain ⟨z, hz, rfl⟩ := hyg
    have hzC : z ∈ centralizer (Q : Set K) := (zpowers_le.2 hxC) hz
    exact hCn.conj_mem z hzC g
  obtain ⟨s, hs, hne⟩ := hyS
  exact hne (mem_centralizer_iff.mp hyC s (subset_closure hs)).symm

end CFSG.ComponentClassification.RestrictedStd.Spor
