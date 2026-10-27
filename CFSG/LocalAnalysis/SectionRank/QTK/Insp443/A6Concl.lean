module

public import CFSG.Quasithin.Vol2.KGFactC31Hex
public import CFSG.Quasithin.Vol2.KGFactC31J4Gen
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.KGC31 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4.E443
open scoped IsMulCommutative

theorem isQuasisimple_of_simple_nonab {X : Type*} [Group X] [IsSimpleGroup X]
    (hnc : ∃ a b : X, a * b ≠ b * a) : CFSG.IsQuasisimple X := by
  obtain ⟨a, b, hab⟩ := hnc
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      apply hab
      exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hcomm : commutator X = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      apply hab
      have h' : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊥ := by
        rw [← _root_.commutator_def]; exact h
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h'
      exact (Subgroup.mem_centralizer_iff.mp (h' (Subgroup.mem_top b)) a (Subgroup.mem_top a))
    · exact h
  let e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨hcomm⟩, MulEquiv.isSimpleGroup e, e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem alt6_nonab : ∃ a b : ↥(alternatingGroup (Fin 6)), a * b ≠ b * a := by
  have h1 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl
  have h2 : (Equiv.swap (1 : Fin 6) 2 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl
  have h3 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) * (Equiv.swap 1 2 * Equiv.swap 2 3) ≠
      (Equiv.swap 1 2 * Equiv.swap 2 3) * (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) := by
    decide
  exact ⟨⟨_, h1⟩, ⟨_, h2⟩, fun h => h3 (congrArg Subtype.val h)⟩

theorem card_alt6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem isFFModule_autOn_of_involution {G : Type} [Group G] [Finite G] {V : Subgroup G}
    [IsMulCommutative ↥V] {a : G} (ha : a ∈ Subgroup.normalizer (V : Set G)) (ha2 : a * a = 1)
    (hfix : Nat.card V = 2 * Nat.card {v : V // a * (v : G) * a⁻¹ = v}) :
    IsFFModule (V := ↥V) (autOn (Subgroup.normalizer (V : Set G)) V) := by
  let a' : ↥(Subgroup.normalizer (V : Set G)) := ⟨a, ha⟩
  let φ := conjAct V a'
  have hφ : ∀ v : V, ((φ v : V) : G) = a * v * a⁻¹ := fun v => rfl
  have hφ2 : φ * φ = 1 := by
    ext v
    change ((φ (φ v) : V) : G) = v
    rw [hφ, hφ]
    calc a * (a * ↑v * a⁻¹) * a⁻¹ = (a * a) * ↑v * (a * a)⁻¹ := by group
      _ = ↑v := by rw [ha2]; group
  have hfixV : ∀ v : V, (∀ x ∈ Subgroup.zpowers φ, x v = v) ↔ a * (v : G) * a⁻¹ = v := by
    intro v
    constructor
    · intro h
      have := h φ (Subgroup.mem_zpowers φ)
      rw [← hφ, this]
    · intro h x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hv : φ v = v := Subtype.ext (by rw [hφ]; exact h)
      have hk : ∀ m : ℕ, (φ ^ m) v = v := fun m => by
        induction m with
        | zero => rfl
        | succ m ih => rw [pow_succ, MulAut.mul_apply, hv, ih]
      rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
      · rw [zpow_natCast]; exact hk m
      · rw [zpow_neg, zpow_natCast]
        calc (φ ^ m)⁻¹ v = (φ ^ m)⁻¹ ((φ ^ m) v) := by rw [hk m]
          _ = v := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hcardfix : Nat.card (fixV (Subgroup.zpowers φ)) =
      Nat.card {v : V // a * (v : G) * a⁻¹ = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => hfixV v)
  have hne : φ ≠ 1 := by
    intro h1
    have hall : ∀ v : V, a * (v : G) * a⁻¹ = v := fun v => by
      rw [← hφ, h1, MulAut.one_apply]
    have : Nat.card {v : V // a * (v : G) * a⁻¹ = v} = Nat.card V :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    have hpos : 0 < Nat.card V := Nat.card_pos
    omega
  refine ⟨Subgroup.zpowers φ, ?_, ?_, ⟨fun x hx y hy => ?_, fun x hx => ?_⟩, ?_⟩
  · rw [Subgroup.zpowers_le]
    refine ⟨a', ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact ha
  · intro hb
    apply hne
    have := Subgroup.mem_zpowers φ
    rwa [hb, Subgroup.mem_bot] at this
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h2 : φ ^ 2 = 1 := by rw [sq]; exact hφ2
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  · have hord : orderOf φ = 2 := orderOf_eq_prime (by rw [sq]; exact hφ2) hne
    rw [Nat.card_zpowers, hord, hcardfix, hfix]

theorem KConfig.conclK_of_a6 {G : Type} [Group G] [Finite G] {L V MK : Subgroup G}
    (h : KConfig G L V MK) (hC : Subgroup.centralizer (V : Set G) ≤ V)
    (ψ : ↥(Subgroup.normalizer (V : Set G)) →* Equiv.Perm (Fin 6)) (hψ : Function.Surjective ψ)
    (hker : ∀ g, ψ g = 1 ↔ (g : G) ∈ V)
    {a : G} (ha : a ∈ Subgroup.normalizer (V : Set G)) (ha2 : a * a = 1)
    (hfix : Nat.card V = 2 * Nat.card {v : V // a * (v : G) * a⁻¹ = v}) :
    ConclK G L V MK := by
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := h.le_normalizer
  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    h.normalizer_le_MK.trans h.MK_le_normalizer
  have hVL : V ≤ L := h.le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hO : pCoreOf 2 L = V := le_antisymm (h.pCoreOf_le.trans hC) h.le_pCoreOf
  let φ : ↥L →* Equiv.Perm (Fin 6) := ψ.comp (Subgroup.inclusion hLN)
  have hφker : φ.ker = V.subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker _
  have hperf : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
      commutator_eq_top_of_perfect h.perfect]
  have hnorm : φ.range.Normal := by
    refine ⟨fun x hx σ => ?_⟩
    obtain ⟨l, rfl⟩ := hx
    obtain ⟨m, rfl⟩ := hψ σ
    have hml : (m : G) * l * (m : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hNL m.2) l).mp l.2
    refine ⟨⟨_, hml⟩, ?_⟩
    change ψ (Subgroup.inclusion hLN ⟨_, hml⟩) = ψ m * ψ (Subgroup.inclusion hLN l) * (ψ m)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hA6 : φ.range ≤ alternatingGroup (Fin 6) := by
    intro x hx
    rw [← hperf] at hx
    have hle : ⁅φ.range, φ.range⁆ ≤ (Equiv.Perm.sign : Equiv.Perm (Fin 6) →* ℤˣ).ker := by
      refine (Subgroup.commutator_mono le_top le_top).trans ?_
      rw [← _root_.commutator_def]
      exact Abelianization.commutator_subset_ker _
    exact Equiv.Perm.mem_alternatingGroup.mpr (hle hx)
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hrange : φ.range = alternatingGroup (Fin 6) := by
    have hN : (φ.range.subgroupOf (alternatingGroup (Fin 6))).Normal := hnorm.subgroupOf _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (φ.range.subgroupOf (alternatingGroup (Fin 6))) with hb | ht
    · exfalso
      have hrb : φ.range = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hA6 hx⟩ : ↥(alternatingGroup (Fin 6))) ∈
            φ.range.subgroupOf (alternatingGroup (Fin 6)) := by
          rw [Subgroup.mem_subgroupOf]; exact hx
        rw [hb, Subgroup.mem_bot] at this
        rw [Subgroup.mem_bot]
        exact congrArg Subtype.val this
      have hLV : L ≤ V := fun l hl => by
        have h1 : φ ⟨l, hl⟩ ∈ φ.range := ⟨_, rfl⟩
        rw [hrb, Subgroup.mem_bot] at h1
        have h2 : (⟨l, hl⟩ : ↥L) ∈ φ.ker := h1
        rw [hφker, Subgroup.mem_subgroupOf] at h2
        exact h2
      have hLb : L = ⊥ := by
        rw [← h.perfect, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have := h.elemAbelian.1.is_comm.comm ⟨y, hLV hy⟩ ⟨x, hLV hx⟩
        exact congrArg Subtype.val this
      exact h.ne_bot (le_antisymm (hVL.trans hLb.le) bot_le)
    · refine le_antisymm hA6 fun x hx => ?_
      have : (⟨x, hx⟩ : ↥(alternatingGroup (Fin 6))) ∈
          φ.range.subgroupOf (alternatingGroup (Fin 6)) := by rw [ht]; exact Subgroup.mem_top _
      rwa [Subgroup.mem_subgroupOf] at this
  have hpk : CFSG.pCore 2 ↥L = φ.ker := by
    rw [← Hex.pCoreOf_subgroupOf' L, hO, hφker]
  let eQ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(alternatingGroup (Fin 6)) :=
    (QuotientGroup.quotientMulEquivOfEq hpk).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))
  have : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := MulEquiv.isSimpleGroup eQ
  have hnc : ∃ x y : ↥L ⧸ CFSG.pCore 2 ↥L, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := alt6_nonab
    refine ⟨eQ.symm x, eQ.symm y, fun h' => hxy ?_⟩
    have := congrArg eQ h'
    simpa using this
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := isQuasisimple_of_simple_nonab hnc
  have hcardX : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by
    rw [Nat.card_congr eQ.toEquiv, card_alt6]
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    obtain ⟨x, y, hxy⟩ := hnc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
      with hb | ht
    · exact hb
    · exact absurd (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top y) x) hxy
  have hcommV : IsMulCommutative ↥V := h.elemAbelian.1
  letI : IsMulCommutative ↥V := hcommV
  unfold ConclK
  refine Or.inl ⟨hq, Or.inr (Or.inr (Or.inr (Or.inl ⟨eQ⟩))), Or.inl ⟨⟨hcommV,
    isFFModule_autOn_of_involution ha ha2 hfix⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro h3
    have h1 := LieModel.card_psl_three_two h3
    rw [hcardX] at h1
    norm_num at h1
  ·
    intro h4
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    rw [hcardX] at h1
    norm_num at h1
  ·
    rintro ⟨-, hc, -⟩
    rw [hZ, Subgroup.card_bot] at hc
    norm_num at hc
  ·
    intro hU
    have h1 := LieModel.card_psu_three_three hU
    rw [hcardX] at h1
    norm_num at h1

end CFSG.SectionRank.QTK.Insp443

end
