module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4FourAux.Layer
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
open scoped commutatorElement

@[expose] def LayerAt (p : ℕ) {G : Type*} [Group G] (x : G) : Prop :=
  CFSG.IsQuasisimple (⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆ :
    Subgroup G) ∧
  ¬ Nat.Coprime p (Nat.card (⁅Subgroup.centralizer ({x} : Set G),
    Subgroup.centralizer ({x} : Set G)⁆ : Subgroup G))

@[expose] def LayerDichotomy (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ x : G, orderOf x = p →
    (∀ u ∈ Subgroup.centralizer ({x} : Set G), ∀ v ∈ Subgroup.centralizer ({x} : Set G),
      u * v = v * u) ∨ LayerAt p x

theorem localDeltaIn_eq_bot_of_conj_map {M : Type*} [Group M] {p : ℕ} {H D : Subgroup M} {c : M}
    (hc : c ∈ H) (h : localDeltaIn p H (D.map (MulAut.conj c).toMonoidHom) = ⊥) :
    localDeltaIn p H D = ⊥ := by
  have hH : H.map (MulAut.conj c).toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact H.mul_mem (H.mul_mem hc hy) (H.inv_mem hc)
    · intro hx
      refine ⟨c⁻¹ * x * c, H.mul_mem (H.mul_mem (H.inv_mem hc) hx) hc, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hle := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_localDeltaIn_le p (MulAut.conj c).toMonoidHom (MulAut.conj c).injective H D
  rw [hH, h, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c).injective] at hle
  exact hle

theorem not_isSolvable_of_isQuasisimple {G : Type*} [Group G] (h : CFSG.IsQuasisimple G) :
    ¬ Group.IsSolvable G := by
  obtain ⟨hperf, -, a, b, hab⟩ := h
  have : Nontrivial G := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hs : ∀ u v : G ⧸ Subgroup.center G, u = v := fun u v => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
      rw [Subsingleton.elim x y]
    exact hab (hs _ _)
  exact Group.IsPerfect.not_isSolvable G

section Engine

variable {G M₁ M₂ : Type*} [Group G] [Group M₁] [Group M₂] [Finite G] [Finite M₁] [Finite M₂]
  {p : ℕ} [hp : Fact p.Prime]

theorem innerPlaneBalance_of_frames
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (ψA : M₁ →* G) (ψB : M₂ →* G) (hA : Function.Injective ψA) (hB : Function.Injective ψB)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y))
    (hperf₁ : Group.IsPerfect M₁) (hperf₂ : Group.IsPerfect M₂)
    (hC : ∀ H : Subgroup G, ψA.range ⊔ ψB.range ≤ H →
      ¬ H ≤ Subgroup.normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) → H = ⊤)
    (hN : ∀ P : Subgroup G, P ≤ Subgroup.normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) →
      Group.IsSolvable ↥(P ⊓ (ψA.range ⊔ ψB.range)) → Group.IsSolvable ↥P)
    (hcycA : ∀ g : M₁, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M₁)))
    (hcycB : ∀ g : M₂, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M₂)))
    (hAB : ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range))
    (hcard : (Nat.card G).factorization p =
      (Nat.card M₁).factorization p + (Nat.card M₂).factorization p)
    (hthird : ∀ E : Subgroup G, Nat.card E = p ^ 2 → (∀ x ∈ E, x ^ p = 1) →
      ∀ a b : G, a ∈ E → b ∈ E → a ≠ 1 → b ≠ 1 →
        ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
          ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({e} : Set G) ∧ ¬ Group.IsSolvable ↥P)
    (hlayer : LayerDichotomy p G) :
    InnerPlaneBalance p G := by
  classical
  intro E hEin hE hEc H hH
  have hp' : p.Prime := hp.out
  set P : Subgroup G := E.comap (MulAut.conj : G →* MulAut G) with hP
  have hPmap : P.map (MulAut.conj : G →* MulAut G) = E := Subgroup.map_comap_eq_self hEin
  have hPc : Nat.card P = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, hEc]
  have hPp : ∀ y ∈ P, y ^ p = 1 := fun y hy => by
    apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ hy
  obtain ⟨g, a, b, hao, hbo, hEg⟩ :=
    exists_conj_plane_of_twoFrames ψA ψB hA hB hcomm hcycA hcycB hAB hcard P hPp hPc
  set E₁ : Subgroup G := Subgroup.zpowers (ψA a) ⊔ Subgroup.zpowers (ψB b) with hE₁
  have hE' : E.map (MulAut.conj (MulAut.conj g : MulAut G)).toMonoidHom =
      E₁.map (MulAut.conj : G →* MulAut G) := by
    rw [← hPmap, ← hEg, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x y
    simp [MulAut.conj_apply]
  refine localDeltaIn_eq_bot_of_conj_map (c := (MulAut.conj g : MulAut G)) (hH ⟨g, rfl⟩) ?_
  rw [hE', eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hao
    exact hp'.one_lt.ne hao
  have hb1 : b ≠ 1 := fun h => by
    rw [h, orderOf_one] at hbo
    exact hp'.one_lt.ne hbo
  have hA1 : ψA a ≠ 1 := fun h => ha1 (hA (h.trans (map_one ψA).symm))
  have hB1 : ψB b ≠ 1 := fun h => hb1 (hB (h.trans (map_one ψB).symm))
  have hAord : orderOf (ψA a) = p := by rw [orderOf_injective ψA hA a]; exact hao
  have hBord : orderOf (ψB b) = p := by rw [orderOf_injective ψB hB b]; exact hbo
  have haE : ψA a ∈ E₁ := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hbE : ψB b ∈ E₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hnc₁ : ∃ u v : M₁, u * v ≠ v * u := by
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative M₁ := ⟨⟨hcon⟩⟩
    haveI := hperf₁
    have : Subsingleton M₁ := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact ha1 (Subsingleton.elim _ _)
  have hnc₂ : ∃ u v : M₂, u * v ≠ v * u := by
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative M₂ := ⟨⟨hcon⟩⟩
    haveI := hperf₂
    have : Subsingleton M₂ := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact hb1 (Subsingleton.elim _ _)
  have hlayA : LayerAt p (ψA a) := by
    refine (hlayer (ψA a) hAord).resolve_left fun hall => ?_
    obtain ⟨u, v, huv⟩ := hnc₂
    apply huv
    apply hB
    rw [map_mul, map_mul]
    exact hall _ (Subgroup.mem_centralizer_singleton_iff.2 (hcomm a u).symm.eq) _
      (Subgroup.mem_centralizer_singleton_iff.2 (hcomm a v).symm.eq)
  have hrangeB : ψB.range ≤ ⁅Subgroup.centralizer ({ψA a} : Set G),
      Subgroup.centralizer ({ψA a} : Set G)⁆ := by
    haveI : Group.IsPerfect M₂ := hperf₂
    haveI : Group.IsPerfect ψB.range := Group.IsPerfect.range ψB
    have hle : ψB.range ≤ Subgroup.centralizer ({ψA a} : Set G) := by
      rintro _ ⟨u, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm a u).symm.eq
    calc ψB.range = ⁅ψB.range, ψB.range⁆ := (Subgroup.commutator_eq_self (H := ψB.range)).symm
      _ ≤ _ := Subgroup.commutator_mono hle hle
  obtain ⟨-, hzA⟩ := fixes_of_mem_localDeltaIn hp' hinj hH hz ⟨ψA a, haE, rfl⟩ hA1 hlayA.1 hlayA.2
  have hlayB : LayerAt p (ψB b) := by
    refine (hlayer (ψB b) hBord).resolve_left fun hall => ?_
    obtain ⟨u, v, huv⟩ := hnc₁
    apply huv
    apply hA
    rw [map_mul, map_mul]
    exact hall _ (Subgroup.mem_centralizer_singleton_iff.2 (hcomm u b).eq) _
      (Subgroup.mem_centralizer_singleton_iff.2 (hcomm v b).eq)
  have hrangeA : ψA.range ≤ ⁅Subgroup.centralizer ({ψB b} : Set G),
      Subgroup.centralizer ({ψB b} : Set G)⁆ := by
    haveI : Group.IsPerfect M₁ := hperf₁
    haveI : Group.IsPerfect ψA.range := Group.IsPerfect.range ψA
    have hle : ψA.range ≤ Subgroup.centralizer ({ψB b} : Set G) := by
      rintro _ ⟨u, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm u b).eq
    calc ψA.range = ⁅ψA.range, ψA.range⁆ := (Subgroup.commutator_eq_self (H := ψA.range)).symm
      _ ≤ _ := Subgroup.commutator_mono hle hle
  obtain ⟨-, hzB⟩ := fixes_of_mem_localDeltaIn hp' hinj hH hz ⟨ψB b, hbE, rfl⟩ hB1 hlayB.1 hlayB.2
  have hXfix : ψA.range ⊔ ψB.range ≤ fixSub z :=
    sup_le (fun y hy => hzB y (hrangeA hy)) (fun y hy => hzA y (hrangeB hy))
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [← hEg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hPc]
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := by
    rw [← hEg]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hPp y hy, map_one]
  obtain ⟨e, heE, hea, heb, P', hPC, hPs⟩ :=
    hthird E₁ hE₁c hE₁p (ψA a) (ψB b) haE hbE hA1 hB1
  have he1 : e ≠ 1 := fun h => hea (h ▸ Subgroup.one_mem _)
  have heord : orderOf e = p := orderOf_eq_prime (hE₁p e heE) he1
  have hCe : ¬ ∀ u ∈ Subgroup.centralizer ({e} : Set G), ∀ v ∈ Subgroup.centralizer ({e} : Set G),
      u * v = v * u := by
    intro hall
    apply hPs
    apply Group.isSolvable_of_comm
    intro u v
    apply Subtype.ext
    exact hall _ (hPC u.2) _ (hPC v.2)
  have hlayE : LayerAt p e := (hlayer e heord).resolve_left hCe
  obtain ⟨-, hzE⟩ := fixes_of_mem_localDeltaIn hp' hinj hH hz ⟨e, heE, rfl⟩ he1 hlayE.1 hlayE.2
  have hzc : ∀ h ∈ Subgroup.zpowers (ψA a), ∀ k ∈ Subgroup.zpowers (ψB b), Commute h k := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ((hcomm a b).zpow_left i).zpow_right j
  obtain ⟨_, ⟨i, hi0⟩, _, ⟨j, hj0⟩, hce⟩ := exists_mul_of_mem_sup_of_commute hzc heE
  simp only at hi0 hj0
  rw [← hi0, ← hj0] at hce
  have hi : orderOf (a ^ i) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hao,
        pow_orderOf_eq_one, one_zpow]
    · intro h
      apply heb
      have : ψA a ^ i = 1 := by rw [← map_zpow, h, map_one]
      rw [hce, this, one_mul]
      exact Subgroup.mem_zpowers_iff.2 ⟨j, rfl⟩
  have hj : orderOf (b ^ j) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hbo,
        pow_orderOf_eq_one, one_zpow]
    · intro h
      apply hea
      have : ψB b ^ j = 1 := by rw [← map_zpow, h, map_one]
      rw [hce, this, mul_one]
      exact Subgroup.mem_zpowers_iff.2 ⟨i, rfl⟩
  have heq : e = ψA (a ^ i) * ψB (b ^ j) := by rw [hce, map_zpow, map_zpow]
  have hnot : ¬ fixSub z ≤ Subgroup.normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) := by
    intro hle
    have hQN : ⁅Subgroup.centralizer ({e} : Set G), Subgroup.centralizer ({e} : Set G)⁆ ≤
        Subgroup.normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) :=
      fun r hr => hle (hzE r hr)
    have hsol : Group.IsSolvable ↥(⁅Subgroup.centralizer ({e} : Set G),
        Subgroup.centralizer ({e} : Set G)⁆ ⊓ (ψA.range ⊔ ψB.range)) := by
      apply Group.isSolvable_of_comm
      rintro ⟨u, huQ, huX⟩ ⟨u', hu'Q, hu'X⟩
      apply Subtype.ext
      have hue : Commute u (ψA (a ^ i) * ψB (b ^ j)) := by
        rw [← heq]
        exact Subgroup.mem_centralizer_singleton_iff.1 (derivedCentralizer_le e huQ)
      have hu'e : Commute u' (ψA (a ^ i) * ψB (b ^ j)) := by
        rw [← heq]
        exact Subgroup.mem_centralizer_singleton_iff.1 (derivedCentralizer_le e hu'Q)
      exact (commute_of_mem_centralizer_twoFrames ψA ψB hA hB hcomm hcycA hcycB hAB hi hj huX hu'X
        hue hu'e).eq
    exact not_isSolvable_of_isQuasisimple hlayE.1 (hN _ hQN hsol)
  exact fixSub_eq_top_iff.1 (hC _ hXfix hnot)

end Engine

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows
