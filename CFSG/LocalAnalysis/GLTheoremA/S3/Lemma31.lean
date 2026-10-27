module

public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.Basic
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

private theorem l31_isMulCommutative_of_le {R Z : Subgroup G} (hR : IsMulCommutative R)
    (h : Z ≤ R) : IsMulCommutative Z :=
  ⟨⟨fun a b => Subtype.ext (by
    have := hR.is_comm.comm ⟨a.1, h a.2⟩ ⟨b.1, h b.2⟩
    simpa using congrArg Subtype.val this)⟩⟩

private theorem l31_isMulCommutative_of_forall {S : Subgroup G}
    (h : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) : IsMulCommutative S :=
  ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩

private theorem l31_isMulCommutative_map {T : Subgroup G} {A : Subgroup T}
    (hA : IsMulCommutative A) : IsMulCommutative (A.map T.subtype) := by
  apply l31_isMulCommutative_of_forall
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
  exact congrArg (fun z : A => ((z : ↥T) : G)) (hA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem l31_le_normalizer_inf {D S S' : Subgroup G}
    (h1 : D ≤ Subgroup.normalizer (S : Set G)) (h2 : D ≤ Subgroup.normalizer (S' : Set G)) :
    D ≤ Subgroup.normalizer ((S ⊓ S' : Subgroup G) : Set G) := by
  intro d hd
  have e1 := Subgroup.mem_normalizer_iff.mp (h1 hd)
  have e2 := Subgroup.mem_normalizer_iff.mp (h2 hd)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_inf]
  exact and_congr (e1 x) (e2 x)

private theorem l31_coprime_card {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D X : Subgroup G}
    (hD : IsElemAbelian p D) (hX : IsPGroup 2 X) :
    Nat.Coprime (Nat.card D) (Nat.card X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_card_eq_pow_of_isElemAbelian hp hD
  obtain ⟨b, hb⟩ := hX.exists_card_eq
  rw [ha, hb]
  exact Nat.Coprime.pow a b ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

private theorem l31_double_comm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D X : Subgroup G}
    (hD : IsElemAbelian p D) (hX : IsPGroup 2 X) (hDX : D ≤ Subgroup.normalizer (X : Set G)) :
    (⁅⁅X, D⁆, D⁆ : Subgroup G) = ⁅X, D⁆ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent X := IsPGroup.isNilpotent hX
  exact GL83.commutator_double_eq_self D X hDX (l31_coprime_card hp hp2 hD hX) inferInstance

private theorem l31_card_le_two_quaternion (W : Subgroup (QuaternionGroup 2))
    (hW : IsElemAbelian 2 W) : Nat.card W ≤ 2 := by
  have key : ∀ w : QuaternionGroup 2, w ^ 2 = 1 → w = 1 ∨ w = QuaternionGroup.a 2 := by
    decide
  have hle : W ≤ Subgroup.zpowers (QuaternionGroup.a 2 : QuaternionGroup 2) := by
    intro w hw
    rcases key w (hW.2 w hw) with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  have h2 : orderOf (QuaternionGroup.a 2 : QuaternionGroup 2) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  calc Nat.card W ≤ Nat.card (Subgroup.zpowers (QuaternionGroup.a 2 : QuaternionGroup 2)) :=
        Subgroup.card_le_of_le hle
    _ = 2 := by rw [Nat.card_zpowers, h2]

private theorem l31_card_le_two_of_mulEquiv {X U : Subgroup G} (e : X ≃* QuaternionGroup 2)
    (hUX : U ≤ X) (hU : IsElemAbelian 2 U) : Nat.card U ≤ 2 := by
  have hV : IsElemAbelian 2 (U.subgroupOf X) := CFSG.Open.IsElemAbelian.subgroupOf hU X
  have hW : IsElemAbelian 2 ((U.subgroupOf X).map e.toMonoidHom) := hV.map e.toMonoidHom
  have hc1 : Nat.card (U.subgroupOf X) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv
  have hc2 : Nat.card ((U.subgroupOf X).map e.toMonoidHom) = Nat.card (U.subgroupOf X) :=
    Subgroup.card_map_of_injective e.injective
  rw [← hc1, ← hc2]
  exact l31_card_le_two_quaternion _ hW

private theorem l31_abelian_le_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T D : Subgroup G}
    (hT : IsPGroup 2 T) (hD : IsElemAbelian p D) (hDne : D ≠ ⊥)
    (hDT : D ≤ Subgroup.normalizer (T : Set G))
    (hc : ∀ D₀ : Subgroup G, D₀ ≤ D → Nat.card D₀ * p = Nat.card D →
      ∀ U : Subgroup G, U ≤ (⁅D, T ⊓ Subgroup.centralizer (D₀ : Set G)⁆ : Subgroup G) →
        IsElemAbelian 2 U → Nat.card U ≤ 2)
    {R : Subgroup G} (hRT : R ≤ T) (hR : IsMulCommutative R)
    (hDR : D ≤ Subgroup.normalizer (R : Set G)) :
    R ≤ Subgroup.centralizer (D : Set G) := by
  refine (GL83.le_iSup_hyperplane hp hp2 hDne hD (hT.to_le hRT) hDR).trans
    (iSup₂_le fun A hA => ?_)
  obtain ⟨hAD, hAi⟩ := hA
  have hAcard : Nat.card A * p = Nat.card D := P55.I336.card_mul_eq_of_index_eq hAD hAi
  have hDA : D ≤ Subgroup.centralizer (A : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact isElemAbelian_commute hD (hAD ha) hd
  set X : Subgroup G := R ⊓ Subgroup.centralizer (A : Set G) with hXdef
  have hXT : X ≤ T := inf_le_left.trans hRT
  have hX2 : IsPGroup 2 X := hT.to_le hXT
  have hDX : D ≤ Subgroup.normalizer (X : Set G) :=
    l31_le_normalizer_inf hDR (hDA.trans Subgroup.le_normalizer)
  have hDTA : D ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
    l31_le_normalizer_inf hDT (hDA.trans Subgroup.le_normalizer)
  have hZR : (⁅X, D⁆ : Subgroup G) ≤ R := by
    refine (Subgroup.commutator_mono_left (inf_le_left : X ≤ R)).trans ?_
    rw [Subgroup.commutator_comm R D]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hDR
  have hZab : IsMulCommutative (⁅X, D⁆ : Subgroup G) := l31_isMulCommutative_of_le hR hZR
  have hZY : (⁅X, D⁆ : Subgroup G) ≤ ⁅D, T ⊓ Subgroup.centralizer (A : Set G)⁆ := by
    rw [Subgroup.commutator_comm X D]
    exact Subgroup.commutator_mono_right (inf_le_inf_right _ hRT)
  have hYT : (⁅D, T ⊓ Subgroup.centralizer (A : Set G)⁆ : Subgroup G) ≤ T :=
    (Subgroup.le_normalizer_iff_commutator_le_right.mp hDTA).trans inf_le_left
  have hcyc : IsCyclic (⁅X, D⁆ : Subgroup G) :=
    P55.I336.isCyclic_of_isMulCommutative (hT.to_le hYT) (hc A hAD hAcard) hZY hZab
  have hDZ : D ≤ Subgroup.normalizer ((⁅X, D⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right X D
  have hZ2 : IsPGroup 2 (⁅X, D⁆ : Subgroup G) := hT.to_le (hZR.trans hRT)
  have hZC : (⁅⁅X, D⁆, D⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h := P55.I336.cyclic_two_group_centralized hp hp2 hZ2 hcyc (hDZ hd) (hD.2 d hd) hz
    calc d * z = d * z * d⁻¹ * d := by group
      _ = z * d := by rw [h]
  have hXC : (⁅X, D⁆ : Subgroup G) = ⊥ := by
    have hdbl := l31_double_comm hp hp2 hD hX2 hDX
    rw [hZC] at hdbl
    exact hdbl.symm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXC

private theorem l31_exists_hyperplane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T D : Subgroup G}
    (hT : IsPGroup 2 T) (hD : IsElemAbelian p D) (hDne : D ≠ ⊥)
    (hDT : D ≤ Subgroup.normalizer (T : Set G)) (ha : (⁅D, T⁆ : Subgroup G) ≠ ⊥) :
    ∃ A : Subgroup G, A ≤ D ∧ Nat.card A * p = Nat.card D ∧
      (⁅D, T ⊓ Subgroup.centralizer (A : Set G)⁆ : Subgroup G) ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  apply ha
  have hle : T ≤ Subgroup.centralizer (D : Set G) := by
    refine (GL83.le_iSup_hyperplane hp hp2 hDne hD hT hDT).trans (iSup₂_le fun A hA => ?_)
    obtain ⟨hAD, hAi⟩ := hA
    have h1 : (⁅T ⊓ Subgroup.centralizer (A : Set G), D⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_comm (T ⊓ Subgroup.centralizer (A : Set G)) D]
      exact hcon A hAD (P55.I336.card_mul_eq_of_index_eq hAD hAi)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle)

private theorem l31_essential {p : ℕ} {B D D₀ T : Subgroup G} (hB : IsElemAbelian p B)
    (hDB : D ≤ B) (hD₀D : D₀ ≤ D) (hT : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hcomm : (⁅D, T ⊓ Subgroup.centralizer (D₀ : Set G)⁆ : Subgroup G) ≠ ⊥)
    (U : Subgroup G) (hUX : U ≤ T ⊓ Subgroup.centralizer (D₀ : Set G))
    (hUel : IsElemAbelian 2 U) (hUcard : 2 < Nat.card U) :
    ∀ d ∈ D₀, d ≠ 1 → IsEssential p B d := by
  intro d hd hd1
  have hBC : B ≤ Subgroup.centralizer (D₀ : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact isElemAbelian_commute hB (hDB (hD₀D hh)) hb
  have hBX : B ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (D₀ : Set G) : Subgroup G) : Set G) :=
    l31_le_normalizer_inf hBT (hBC.trans Subgroup.le_normalizer)
  have hX2 : IsPGroup 2 (T ⊓ Subgroup.centralizer (D₀ : Set G) : Subgroup G) :=
    hT.to_le inf_le_left
  have hBXc : (⁅T ⊓ Subgroup.centralizer (D₀ : Set G), B⁆ : Subgroup G) ≠ ⊥ := by
    intro h
    apply hcomm
    rw [eq_bot_iff]
    calc (⁅D, T ⊓ Subgroup.centralizer (D₀ : Set G)⁆ : Subgroup G)
        ≤ ⁅B, T ⊓ Subgroup.centralizer (D₀ : Set G)⁆ := Subgroup.commutator_mono_left hDB
      _ = ⁅T ⊓ Subgroup.centralizer (D₀ : Set G), B⁆ := Subgroup.commutator_comm B _
      _ = ⊥ := h
  unfold IsEssential
  refine ⟨hDB (hD₀D hd), hd1, T ⊓ Subgroup.centralizer (D₀ : Set G), ?_, hX2, hBX, hBXc, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact Subgroup.mem_centralizer_iff.mp hx.2 d hd
  · intro _
    refine ⟨fun e => ?_⟩
    have := l31_card_le_two_of_mulEquiv e hUX hUel
    omega

theorem i335 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T D : Subgroup G} (hT : IsPGroup 2 T)
    (hD : IsElemAbelian p D) (hDT : D ≤ Subgroup.normalizer (T : Set G))
    (ha : (⁅D, T⁆ : Subgroup G) ≠ ⊥)
    (hb : ∀ U : Subgroup G, U ≤ T ⊓ Subgroup.centralizer (D : Set G) → IsElemAbelian 2 U →
      Nat.card U ≤ 2)
    (hc : ∀ D₀ : Subgroup G, D₀ ≤ D → Nat.card D₀ * p = Nat.card D →
      ∀ U : Subgroup G, U ≤ (⁅D, T ⊓ Subgroup.centralizer (D₀ : Set G)⁆ : Subgroup G) →
        IsElemAbelian 2 U → Nat.card U ≤ 2) :
    GLASymplecticType T ∧ p = 3 := by
  have hDne : D ≠ ⊥ := by
    rintro rfl
    exact ha (by simp)
  obtain ⟨A₀, hA₀D, hA₀c, hA₀ne⟩ := l31_exists_hyperplane hp hp2 hT hD hDne hDT ha
  have hDA₀ : D ≤ Subgroup.centralizer (A₀ : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro a ha'
    exact isElemAbelian_commute hD (hA₀D ha') hd
  have hX2 : IsPGroup 2 (T ⊓ Subgroup.centralizer (A₀ : Set G) : Subgroup G) :=
    hT.to_le inf_le_left
  have hDX : D ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (A₀ : Set G) : Subgroup G) : Set G) :=
    l31_le_normalizer_inf hDT (hDA₀.trans Subgroup.le_normalizer)
  have hdbl := l31_double_comm hp hp2 hD hX2 hDX
  have hYX : (⁅D, T ⊓ Subgroup.centralizer (A₀ : Set G)⁆ : Subgroup G) ≤
      T ⊓ Subgroup.centralizer (A₀ : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hDX
  have hY2 : IsPGroup 2 (⁅D, T ⊓ Subgroup.centralizer (A₀ : Set G)⁆ : Subgroup G) :=
    hT.to_le (hYX.trans inf_le_left)
  have hDY : D ≤ Subgroup.normalizer
      ((⁅D, T ⊓ Subgroup.centralizer (A₀ : Set G)⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left D _
  have hYD : (⁅⁅D, T ⊓ Subgroup.centralizer (A₀ : Set G)⁆, D⁆ : Subgroup G) ≠ ⊥ := by
    rw [Subgroup.commutator_comm D (T ⊓ Subgroup.centralizer (A₀ : Set G)), hdbl]
    rwa [Subgroup.commutator_comm D (T ⊓ Subgroup.centralizer (A₀ : Set G))] at hA₀ne
  have hp3 : p = 3 :=
    (P55.I336.quat_of_action hp hp2 hY2 (hc A₀ hA₀D hA₀c) hD hDY hYD).1
  refine ⟨?_, hp3⟩
  refine ⟨hT, fun A hAchar hAab => ?_⟩
  have hA'T : A.map T.subtype ≤ T := Subgroup.map_subtype_le A
  have hA'comm : IsMulCommutative (A.map T.subtype) := l31_isMulCommutative_map hAab
  have hDA' : D ≤ Subgroup.normalizer ((A.map T.subtype : Subgroup G) : Set G) := by
    refine P55.I336.le_normalizer_of_forall_mem fun d hd y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxϕ : (T.normalizerMonoidHom ⟨d, hDT hd⟩) x ∈ A := by
      have h2 : x ∈ A.comap (T.normalizerMonoidHom ⟨d, hDT hd⟩ : ↥T ≃* ↥T).toMonoidHom := by
        rw [hAchar.fixed (T.normalizerMonoidHom ⟨d, hDT hd⟩)]
        exact hx
      exact h2
    exact Subgroup.mem_map.mpr
      ⟨_, hxϕ, Subgroup.normalizerMonoidHom_apply_apply_coe T ⟨d, hDT hd⟩ x⟩
  have hAC : A.map T.subtype ≤ T ⊓ Subgroup.centralizer (D : Set G) :=
    le_inf hA'T (l31_abelian_le_centralizer hp hp2 hT hD hDne hDT hc hA'T hA'comm hDA')
  have hcyc : IsCyclic (A.map T.subtype) :=
    P55.I336.isCyclic_of_isMulCommutative (hT.to_le inf_le_left) hb hAC hA'comm
  exact ((Subgroup.equivMapOfInjective A T.subtype T.subtype_injective).isCyclic).mpr hcyc

theorem lemma31 {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m)
    {B D N : Subgroup G} (hB : GLAIsBmax p B) (hDB : D ≤ B) (hDnc : ¬ IsCyclic D)
    (hN : GLAIsMaxTwoLocal N) (hBN : B ≤ N) :
    ∃ D₀ : Subgroup G, D₀ ≤ D ∧ Nat.card D₀ * p = Nat.card D ∧
      (∀ d ∈ D₀, d ≠ 1 → IsEssential p B d) ∧
      (⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₀ : Set G)⁆ : Subgroup G) ≠ ⊥ := by
  have hp' : p.Prime := hp.1.1
  have hp2 : p ≠ 2 := hp.1.2.1
  have hchar : IsCharTwoType G := hctx.1.charTwo
  have hBel : IsElemAbelian p B := hB.1
  have hD : IsElemAbelian p D := isElemAbelian_mono hBel hDB
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 (pCoreOf 2 N) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hBT : B ≤ Subgroup.normalizer ((pCoreOf 2 N : Subgroup G) : Set G) :=
    hBN.trans (le_normalizer_pCoreOf 2 N)
  have hDT : D ≤ Subgroup.normalizer ((pCoreOf 2 N : Subgroup G) : Set G) := hDB.trans hBT
  have hDne : D ≠ ⊥ := by
    rintro rfl
    exact hDnc (by infer_instance)
  have ha : (⁅D, pCoreOf 2 N⁆ : Subgroup G) ≠ ⊥ := by
    intro h
    have hDC : D ≤ Subgroup.centralizer ((pCoreOf 2 N : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hBC := GL83.inf_centralizer_eq_bot_of_pCoreOf hp' hp2 hchar hN.1 hBN hBel
    exact hDne (le_bot_iff.mp ((le_inf hDB hDC).trans hBC.le))
  have hsymp : ¬ (GLASymplecticType (pCoreOf 2 N) ∧ p = 3) := by
    rintro ⟨hsym, rfl⟩
    exact hctx.2 ⟨hp, N, hN, hsym, B, hB, hBN⟩
  by_cases hb : ∀ U : Subgroup G, U ≤ pCoreOf 2 N ⊓ Subgroup.centralizer (D : Set G) →
      IsElemAbelian 2 U → Nat.card U ≤ 2
  · by_cases hc : ∀ D₀ : Subgroup G, D₀ ≤ D → Nat.card D₀ * p = Nat.card D →
        ∀ U : Subgroup G, U ≤ (⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₀ : Set G)⁆ : Subgroup G) →
          IsElemAbelian 2 U → Nat.card U ≤ 2
    · exact absurd (i335 hp' hp2 hT hD hDT ha hb hc) hsymp
    · push Not at hc
      obtain ⟨D₀, hD₀D, hD₀c, U, hUle, hUel, hUcard⟩ := hc
      have hDC0 : D ≤ Subgroup.centralizer (D₀ : Set G) := by
        intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact isElemAbelian_commute hD (hD₀D hh) hd
      have hDX : D ≤ Subgroup.normalizer
          ((pCoreOf 2 N ⊓ Subgroup.centralizer (D₀ : Set G) : Subgroup G) : Set G) :=
        l31_le_normalizer_inf hDT (hDC0.trans Subgroup.le_normalizer)
      have hcomm : (⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₀ : Set G)⁆ : Subgroup G) ≠ ⊥ := by
        intro h
        rw [h] at hUle
        have hU0 : U = ⊥ := le_bot_iff.mp hUle
        rw [hU0] at hUcard
        simp at hUcard
      have hUX : U ≤ pCoreOf 2 N ⊓ Subgroup.centralizer (D₀ : Set G) :=
        hUle.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp hDX)
      exact ⟨D₀, hD₀D, hD₀c, l31_essential hBel hDB hD₀D hT hBT hcomm U hUX hUel hUcard, hcomm⟩
  · push Not at hb
    obtain ⟨U, hUle, hUel, hUcard⟩ := hb
    obtain ⟨A₀, hA₀D, hA₀c, hA₀ne⟩ := l31_exists_hyperplane hp' hp2 hT hD hDne hDT ha
    have hCD : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer (A₀ : Set G) :=
      Subgroup.centralizer_le fun x hx => hA₀D hx
    have hUX : U ≤ pCoreOf 2 N ⊓ Subgroup.centralizer (A₀ : Set G) :=
      le_inf (hUle.trans inf_le_left) ((hUle.trans inf_le_right).trans hCD)
    exact ⟨A₀, hA₀D, hA₀c, l31_essential hBel hDB hA₀D hT hBT hA₀ne U hUX hUel hUcard, hA₀ne⟩

theorem lemma31_hyperplane {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m)
    {B : Subgroup G} (hB : GLAIsBmax p B) :
    ∃ B₀ : Subgroup G, B₀ ≤ B ∧ Nat.card B₀ * p = Nat.card B ∧
      ∀ b ∈ B₀, b ≠ 1 → IsEssential p B b := by
  obtain ⟨N, hN, hBN⟩ := GLAIsBmax.exists_maxTwoLocal hB
  have hBnc : ¬ IsCyclic B := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥B)
    have hpow : g ^ p = 1 := Subtype.ext (by simpa using hB.1.2 g.1 g.2)
    have hord : orderOf g = Nat.card B := orderOf_eq_card_of_forall_mem_zpowers hg
    have hdvd : Nat.card B ∣ p := hord ▸ orderOf_dvd_of_pow_eq_one hpow
    rw [hB.2.1, hp.2.1] at hdvd
    have hp' : p.Prime := hp.1.1
    have h1 : p ^ m ∣ p ^ 1 := by rwa [pow_one]
    have h2 := (Nat.pow_dvd_pow_iff_le_right hp'.one_lt).mp h1
    have h4 := hctx.1.four_le
    omega
  obtain ⟨D₀, h1, h2, h3, -⟩ := lemma31 hctx hp hB le_rfl hBnc hN hBN
  exact ⟨D₀, h1, h2, h3⟩

end CFSG.LocalAnalysis.GLTheoremA
