module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem exists_zpow_eq_of_card_dvd_three {Q : Type*} [Group Q] (H : Subgroup Q)
    (hH : Nat.card H ∣ 3) {y x : Q} (hy : y ∈ H) (hy1 : y ≠ 1) (hx : x ∈ H) :
    ∃ j : ℤ, y ^ j = x := by
  have hle : Subgroup.zpowers y ≤ H := Subgroup.zpowers_le.2 hy
  have hdvd : Nat.card (Subgroup.zpowers y) ∣ Nat.card H := Subgroup.card_dvd_of_le hle
  have hord : orderOf y = 3 := by
    rw [Nat.card_zpowers] at hdvd
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ (hdvd.trans hH) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  rw [Nat.card_zpowers, hord] at hdvd
  have h4 : Nat.card H = 3 := Nat.dvd_antisymm hH hdvd
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have heq : Subgroup.zpowers y = H :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [h4, Nat.card_zpowers, hord]))
  have hx' : x ∈ Subgroup.zpowers y := by
    rw [heq]
    exact hx
  exact Subgroup.mem_zpowers_iff.1 hx'

abbrev innerE6 (K : Type) [Field K] : Subgroup (MulAut (adjointGroup Tag.E6 K)) :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.E6 K)

abbrev projE6 (K : Type) [Field K] :
    MulAut (adjointGroup Tag.E6 K) →* Outer (adjointGroup Tag.E6 K) :=
  QuotientGroup.mk' (innerE6 K)

theorem mem_of_mk'_eq_one {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {x : G}
    (h : QuotientGroup.mk' N x = 1) : x ∈ N :=
  (QuotientGroup.eq_one_iff (N := N) x).1 h

theorem exists_conj_of_mem_inner {G : Type*} [Group G] {x : MulAut G}
    (hx : x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G) :
    ∃ c : G, MulAut.conj c = x := by
  have h : x ∈ (MulAut.conj : G →* MulAut G).range := hx
  exact MonoidHom.mem_range.1 h

section ConjClass


@[expose] noncomputable def e6OuterHom (K : Type) [Field K] :
    ↥(e6InndiagGL K) →* Outer (adjointGroup Tag.E6 K) :=
  (projE6 K).comp (e6InndiagConj K)

theorem e6OuterHom_apply (K : Type) [Field K] (g : ↥(e6InndiagGL K)) :
    e6OuterHom K g = projE6 K (e6InndiagConj K g) :=
  rfl

theorem mk_mem_range_of_mem_e6Inndiag (K : Type) [Field K] {d : MulAut (adjointGroup Tag.E6 K)}
    (hd : d ∈ e6Inndiag K) :
    projE6 K d ∈ ((projE6 K).comp (rootDiagAutHom Tag.E6 K)).range := by
  have hdd : d ∈ ((innerE6 K ⊔ (rootDiagAutHom Tag.E6 K).range : Subgroup _) : Set _) := hd
  rw [Subgroup.normal_mul] at hdd
  obtain ⟨i, hi, r, ⟨a, rfl⟩, rfl⟩ := hdd
  refine MonoidHom.mem_range.2 ⟨a, ?_⟩
  have hpi : projE6 K i = 1 := (QuotientGroup.eq_one_iff i).2 hi
  rw [MonoidHom.comp_apply, map_mul, hpi, one_mul]

theorem e6OuterHom_mem_range (K : Type) [Field K] (g : ↥(e6InndiagGL K)) :
    e6OuterHom K g ∈ ((projE6 K).comp (rootDiagAutHom Tag.E6 K)).range := by
  rw [e6OuterHom_apply]
  refine mk_mem_range_of_mem_e6Inndiag K ?_
  have h : e6InndiagConj K g ∈ (e6InndiagConj K).range := MonoidHom.mem_range.2 ⟨g, rfl⟩
  rwa [range_e6InndiagConj K] at h

theorem coe_eq_of_e6InndiagConj_eq_conj (K : Type) [Field K] [Finite K] (hK4 : 4 ≤ Nat.card K)
    {g : ↥(e6InndiagGL K)} {c : adjointGroup Tag.E6 K}
    (h : e6InndiagConj K g = MulAut.conj c) :
    (g : ModGL Tag.E6 K) = (c : ModGL Tag.E6 K) := by
  have hc : e6InndiagConj K ⟨(c : ModGL Tag.E6 K), adjointGroup_le_e6InndiagGL K c.2⟩ =
      MulAut.conj c :=
    MulEquiv.ext fun _ => Subtype.ext rfl
  have hg := e6InndiagConj_injective K hK4 (h.trans hc.symm)
  exact congrArg Subtype.val hg

theorem exists_zpow_mul_mem_adjointGroup {K : Type} [Field K] [Finite K] (hK4 : 4 ≤ Nat.card K)
    {c₀ : ModGL Tag.E6 K} (hc₀ : c₀ ∈ e6InndiagGL K) (hnot : c₀ ∉ adjointGroup Tag.E6 K)
    {a : ModGL Tag.E6 K} (ha : a ∈ e6InndiagGL K) :
    ∃ j : ℤ, a * c₀ ^ j ∈ adjointGroup Tag.E6 K := by
  obtain ⟨Φ, -, hker, hdvd⟩ := exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
  have hle : (e6OuterHom K).range ≤ Φ.ker := by
    rw [hker]
    rintro _ ⟨g, rfl⟩
    exact e6OuterHom_mem_range K g
  have hH3 : Nat.card (e6OuterHom K).range ∣ 3 := by
    refine (Subgroup.card_dvd_of_le hle).trans ?_
    rwa [show Tag.E6.cartan.det.natAbs = 3 by rw [det_cartan_E6]; rfl] at hdvd
  have hy1 : e6OuterHom K (⟨c₀, hc₀⟩ : ↥(e6InndiagGL K)) ≠ 1 := by
    intro h1
    rw [e6OuterHom_apply] at h1
    obtain ⟨c, hc⟩ := exists_conj_of_mem_inner (mem_of_mk'_eq_one h1)
    have hc₀c : c₀ = (c : ModGL Tag.E6 K) := coe_eq_of_e6InndiagConj_eq_conj K hK4 hc.symm
    exact hnot (by rw [hc₀c]; exact c.2)
  obtain ⟨j, hj⟩ := exists_zpow_eq_of_card_dvd_three _ hH3
    (MonoidHom.mem_range.2 ⟨(⟨c₀, hc₀⟩ : ↥(e6InndiagGL K)), rfl⟩) hy1
    (MonoidHom.mem_range.2 ⟨(⟨a, ha⟩ : ↥(e6InndiagGL K)), rfl⟩)
  have hb : e6OuterHom K ((⟨a, ha⟩ : ↥(e6InndiagGL K)) * ((⟨c₀, hc₀⟩ : ↥(e6InndiagGL K)) ^ j)⁻¹)
      = 1 := by
    rw [map_mul, map_inv, map_zpow, hj, mul_inv_cancel]
  rw [e6OuterHom_apply] at hb
  obtain ⟨c, hc⟩ := exists_conj_of_mem_inner (mem_of_mk'_eq_one hb)
  have hab : a * (c₀ ^ j)⁻¹ = (c : ModGL Tag.E6 K) :=
    coe_eq_of_e6InndiagConj_eq_conj K hK4 hc.symm
  refine ⟨-j, ?_⟩
  rw [zpow_neg, hab]
  exact c.2

end ConjClass

end CFSG.LieType.SeitzGeneration.ExcHighThree
