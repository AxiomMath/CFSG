module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIYCriterion

public section

namespace CFSG.ComponentClassification.RankTwoHypIIY

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic
open scoped commutatorElement

variable {W : Type*} [Group W]

section TwoNilpotentCentral

@[expose] def TwoNilpotentCentral (L : Subgroup W) : Prop :=
  ∀ P : Subgroup W, P ≤ L → L ≤ normalizer (P : Set W) → IsTwoNilpotent P →
    L ≤ centralizer (P : Set W)

theorem twoNilpotentCentral_of_isQuasisimple [Finite W] {L : Subgroup W}
    (hL : Open.IsQuasisimple L) (heven : Even (Nat.card L)) : TwoNilpotentCentral L := by
  intro P hPL hLP hPn
  have : (P.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hPL).mpr hLP
  rcases Quasisimple.normal_le_center_or_eq_top hL (P.subgroupOf L) with hc | htop
  · intro l hl
    rw [mem_centralizer_iff]
    intro p hp
    have hpZ := hc (show (⟨p, hPL hp⟩ : L) ∈ P.subgroupOf L from hp)
    exact congrArg Subtype.val ((mem_center_iff.mp hpZ) ⟨l, hl⟩).symm
  · exfalso
    have hLP' : L ≤ P := fun l hl => by
      have h := (eq_top_iff.mp htop) (mem_top (⟨l, hl⟩ : L))
      exact h
    have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp ((Group.isPerfect_def).2 hL.1)
    exact Nat.not_even_iff_odd.mpr (hPn.odd_card_of_le_of_perfect hLP' hperf) heven

theorem twoNilpotentCentral_of_isSimpleGroup [Finite W] {L : Subgroup W}
    (hL : IsSimpleGroup L) (hLp : ⁅L, L⁆ = L) (heven : Even (Nat.card L)) :
    TwoNilpotentCentral L := by
  have : IsSimpleGroup L := hL
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hLp
  exact twoNilpotentCentral_of_isQuasisimple (Quasisimple.simple_of_perfect L) heven

theorem commutator_eq_self_of_isSimpleGroup {L : Subgroup W} (hL : IsSimpleGroup L)
    (hnc : ¬ ∀ a b : L, a * b = b * a) : ⁅L, L⁆ = L := by
  have : IsSimpleGroup L := hL
  rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with h | h
  · exfalso
    apply hnc
    intro a b
    rw [commutator_def, commutator_eq_bot_iff_le_centralizer] at h
    exact mem_centralizer_iff.mp (h (mem_top b)) a (mem_top a)
  · exact h

theorem TwoNilpotentCentral.map_equiv {L : Subgroup W} (h : TwoNilpotentCentral L)
    (φ : W ≃* W) : TwoNilpotentCentral (L.map φ.toMonoidHom) := by
  intro P hPL hLP hPn
  have h0 := h (P.map φ.symm.toMonoidHom) ?_ ?_ (hPn.map _)
  · intro y hy
    rw [mem_centralizer_iff]
    intro p hp
    have hyL : φ.symm y ∈ L := mem_map_equiv.mp hy
    have := mem_centralizer_iff.mp (h0 hyL) (φ.symm p) ⟨p, hp, rfl⟩
    apply φ.symm.injective
    simpa only [map_mul] using this
  · rintro _ ⟨p, hp, rfl⟩
    exact mem_map_equiv.mp (hPL hp)
  · intro l hl
    have hφl : φ l ∈ normalizer (P : Set W) := hLP ⟨l, hl, rfl⟩
    have := le_normalizer_map φ.symm.toMonoidHom ⟨φ l, hφl, rfl⟩
    simpa using this

end TwoNilpotentCentral

theorem le_centralizer_of_isTwoNilpotent_nE [Finite W] {X E L : Subgroup W}
    (hnil : IsTwoNilpotent (nE X E)) (hLΓ : L ≤ gammaE X E)
    (hEL : E ≤ normalizer (L : Set W)) (hLp : ⁅L, L⁆ = L) (hL : TwoNilpotentCentral L) :
    E ≤ centralizer (L : Set W) := by
  have hPN : ⁅E, L⁆ ≤ nE X E := commutator_mono le_rfl hLΓ
  have hPL : ⁅E, L⁆ ≤ L := (le_normalizer_iff_commutator_le_right).mp hEL
  have hLP : L ≤ normalizer ((⁅E, L⁆ : Subgroup W) : Set W) := normalizer_commutator_ge_right E L
  have hcent : L ≤ centralizer ((⁅E, L⁆ : Subgroup W) : Set W) := hL _ hPL hLP (hnil.mono hPN)
  have h1 : ⁅⁅E, L⁆, L⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcent)
  have h2 : ⁅⁅L, E⁆, L⁆ = ⊥ := by rwa [commutator_comm L E]
  have h3 : ⁅⁅L, L⁆, E⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h2 h1
  rw [hLp, commutator_eq_bot_iff_le_centralizer] at h3
  exact le_centralizer_iff.mp h3

section Rigid

@[expose] def RigidInvolution (X : Subgroup W) (t : W) : Prop :=
  ∃ L : Subgroup W, L ≤ X ∧ L ≤ centralizer ({t} : Set W) ∧
    centralizer ({t} : Set W) ≤ normalizer (L : Set W) ∧ ⁅L, L⁆ = L ∧ TwoNilpotentCentral L ∧
    ∀ s ∈ centralizer ({t} : Set W), s ∈ centralizer (L : Set W) → s ^ 2 = 1 → s = 1 ∨ s = t

theorem RigidInvolution.map_equiv {X : Subgroup W} {t : W} (h : RigidInvolution X t)
    (φ : W ≃* W) (hφX : ∀ x ∈ X, φ x ∈ X) : RigidInvolution X (φ t) := by
  obtain ⟨L, hLX, hLt, hNL, hLp, hL, hinv⟩ := h
  have hC : ∀ s, s ∈ centralizer ({φ t} : Set W) ↔ φ.symm s ∈ centralizer ({t} : Set W) := by
    intro s
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hs
      apply φ.injective
      simp [map_mul, hs]
    · intro hs
      have := congrArg φ hs
      simpa [map_mul] using this
  refine ⟨L.map φ.toMonoidHom, ?_, ?_, ?_, ?_, hL.map_equiv φ, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    exact hφX l (hLX hl)
  · rintro _ ⟨l, hl, rfl⟩
    rw [hC]
    simpa using hLt hl
  · intro s hs
    have h1 := hNL ((hC s).mp hs)
    have := le_normalizer_map φ.toMonoidHom ⟨φ.symm s, h1, rfl⟩
    simpa using this
  · rw [← map_commutator, hLp]
  · intro s hs hsL hs2
    have hsL' : φ.symm s ∈ centralizer (L : Set W) := by
      rw [mem_centralizer_iff]
      intro l hl
      have := mem_centralizer_iff.mp hsL (φ l) ⟨l, hl, rfl⟩
      apply φ.injective
      simpa [map_mul] using this
    rcases hinv (φ.symm s) ((hC s).mp hs) hsL' (by rw [← map_pow, hs2, map_one]) with h1 | h1
    · left
      simpa using congrArg φ h1
    · right
      simpa using congrArg φ h1

theorem RigidInvolution.conj {X : Subgroup W} (hX : X.Normal) {t : W} (h : RigidInvolution X t)
    (w : W) : RigidInvolution X (w * t * w⁻¹) :=
  h.map_equiv (MulAut.conj w) fun x hx => hX.conj_mem x hx w

theorem RigidInvolution.of_isSimpleGroup [Finite W] {X L : Subgroup W} {t : W} (htX : t ∉ X)
    (hLX : L ≤ X) (hLt : L ≤ centralizer ({t} : Set W))
    (hNL : centralizer ({t} : Set W) ≤ normalizer (L : Set W)) (hL : IsSimpleGroup L)
    (heven : Even (Nat.card L))
    (hinv : ∀ s ∈ centralizer ({t} : Set W), s ∈ centralizer (L : Set W) → s ^ 2 = 1 →
      s = 1 ∨ s = t) :
    RigidInvolution X t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnc : ¬ ∀ a b : L, a * b = b * a := by
    intro hcomm
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    have hsC : (s : W) ∈ centralizer (L : Set W) := by
      rw [mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (hcomm ⟨l, hl⟩ s)
    have hs2 : (s : W) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hs, pow_orderOf_eq_one, Subgroup.coe_one]
    rcases hinv s (hLt s.2) hsC hs2 with h1 | h1
    · have : s = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hs
      exact absurd hs (by norm_num)
    · exact htX (h1 ▸ hLX s.2)
  have hLp := commutator_eq_self_of_isSimpleGroup hL hnc
  exact ⟨L, hLX, hLt, hNL, hLp, twoNilpotentCentral_of_isSimpleGroup hL hLp heven, hinv⟩

theorem eq_one_or_eq_of_mem_zpowers {t s : W} (ht : t ^ 2 = 1) (hs : s ∈ zpowers t) :
    s = 1 ∨ s = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
  have ht' : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, ht]
  rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
  · left
    rw [zpow_mul, ht', one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, ht', one_zpow, one_mul]

theorem even_card_of_mem [Finite W] {L : Subgroup W} {x : W} (hx : x ∈ L) (hx1 : x ≠ 1)
    (hx2 : x ^ 2 = 1) : Even (Nat.card L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (⟨x, hx⟩ : L) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hx2 hx1
  exact even_iff_two_dvd.mpr (hord ▸ orderOf_dvd_natCard _)

theorem RigidInvolution.of_isSimpleGroup_of_le_zpowers [Finite W] {X L : Subgroup W} {t : W}
    (htX : t ∉ X) (ht2 : t ^ 2 = 1) (hLX : L ≤ X) (hLt : L ≤ centralizer ({t} : Set W))
    (hNL : centralizer ({t} : Set W) ≤ normalizer (L : Set W)) (hL : IsSimpleGroup L)
    (heven : Even (Nat.card L))
    (hC : centralizer ({t} : Set W) ⊓ centralizer (L : Set W) ≤ zpowers t) :
    RigidInvolution X t :=
  RigidInvolution.of_isSimpleGroup htX hLX hLt hNL hL heven fun _ hs hsL _ =>
    eq_one_or_eq_of_mem_zpowers ht2 (hC ⟨hs, hsL⟩)

theorem false_of_rigidInvolution [Finite W] {X E : Subgroup W} (hE : IsElemAbelian 2 E)
    (h4 : 4 ≤ Nat.card E) (hnil : IsTwoNilpotent (nE X E)) {t : W} (htE : t ∈ E) (ht1 : t ≠ 1)
    (ht : RigidInvolution X t) : False := by
  obtain ⟨L, hLX, hLt, hNL, hLp, hL, hinv⟩ := ht
  have hEt : E ≤ centralizer ({t} : Set W) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hE.1.is_comm.comm ⟨s, hs⟩ ⟨t, htE⟩))
  have hLΓ : L ≤ gammaE X E := by
    have hLD : L ≤ centDer X t :=
      calc L = ⁅L, L⁆ := hLp.symm
        _ ≤ centDer X t := commutator_mono (le_inf hLX hLt) (le_inf hLX hLt)
    exact hLD.trans (le_iSup₂_of_le t htE (le_iSup_of_le ht1 le_rfl))
  have hEC := le_centralizer_of_isTwoNilpotent_nE hnil hLΓ (hEt.trans hNL) hLp hL
  have hEz : E ≤ zpowers t := fun s hs =>
    (hinv s (hEt hs) (hEC hs) (hE.2 s hs)).elim (fun h => h ▸ one_mem _)
      (fun h => h ▸ mem_zpowers t)
  have hcard := Subgroup.card_le_of_le hEz
  rw [Nat.card_zpowers] at hcard
  have := orderOf_le_of_pow_eq_one two_pos (hE.2 t htE)
  omega

end Rigid

theorem hypII_of_rigidInvolution {X₀ : Type*} [Group X₀] [Finite W] {X : Subgroup W}
    (hW : AutModel X₀ W X) (hrig : ∀ t : W, t ∉ X → t ^ 2 = 1 → RigidInvolution X t)
    {A : Type*} [Group A] (hA : commutator A = ⊤) (e : A ⧸ center A ≃* X₀) : HypII A := by
  refine hypII_of_forall hW (fun E hE h4 hEX _ hnil => ?_) hA e
  obtain ⟨t, htE, htX⟩ := IsConcreteLE.not_le_iff_exists.mp hEX
  exact false_of_rigidInvolution hE h4 hnil htE (fun h => htX (h ▸ X.one_mem))
    (hrig t htX (hE.2 t htE))

end CFSG.ComponentClassification.RankTwoHypIIY
