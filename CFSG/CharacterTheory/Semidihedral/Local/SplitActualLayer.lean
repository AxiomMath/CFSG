module

public import CFSG.CharacterTheory.Semidihedral.Local.CentralizingPerfectLift
public import CFSG.CharacterTheory.Semidihedral.OddProjectiveCoverKernel

public section

open scoped Pointwise

namespace CFSG.Semidihedral.Local

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
  CFSG.Semidihedral.OddProjectiveCoverKernel

theorem all_local_prime_covers_split_actual_layer_except_central_three_at_nine {G : Type}
    [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    let L := CFSG.generalizedFitting (Gamma t)
    let T₀ := L.comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let Split : Prop :=
      (Group.IsPerfect J ∧ J ≤ Y ∧ ⁅J, N t⁆ = ⊥ ∧ J.map (nu t) = T₀ ∧
        ∀ J₁ : Subgroup (C t), J₁ ≤ Y → Group.IsPerfect J₁ → ⁅J₁, N t⁆ = ⊥ →
          J₁.map (nu t) = T₀ → J₁ = J) ∧
      J.Normal ∧ tInC t ∈ J ∧ Y = J ⊔ N t ∧
      (p ^ f ≠ 9 → E = ⊥ ∧ (∃ φ : J ≃* T₀, ∀ x : J, (φ x : H t) = nu t x) ∧
        (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
          Nonempty (T₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
        ∃ μ : J × N t ≃* Y, ∀ x : J × N t, (μ x : C t) = x.1 * x.2) ∧
      (p ^ f = 9 → IsCyclic E ∧ (Nat.card E = 1 ∨ Nat.card E = 3) ∧
        E ≤ (Subgroup.center (N t)).map (N t).subtype ∧
        (Subgroup.center J).map J.subtype = E ⊔ Subgroup.zpowers (tInC t) ∧
        E ⊓ Subgroup.zpowers (tInC t) = ⊥ ∧ ⁅E, Subgroup.zpowers (tInC t)⁆ = ⊥ ∧
        (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
          Nonempty (J ⧸ E.subgroupOf J ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
        ∃ μ : J × N t →* Y, Function.Surjective μ ∧ (∀ x : J × N t, (μ x : C t) = x.1 * x.2) ∧
          (∀ x : J × N t, x ∈ μ.ker ↔ (x.1 : C t) ∈ E ∧ (x.2 : C t) = (x.1 : C t)⁻¹) ∧
          μ.ker ≤ Subgroup.center (J × N t))
    ((∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
        (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
          Set (C t)) ⊓ Y).map (nu t) = T₀) ∨
      (∃ s : C t, orderOf s = 2 ∧ s ≠ tInC t ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) →
        ∃ P : Sylow ℓ (N t), s ∈ Subgroup.normalizer
          (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) : Set (C t)) ∧
          ((∀ x : N t, x ∈ P → s * (x : C t) * s⁻¹ = x) ∨
            (∀ x : N t, x ∈ P → s * (x : C t) * s⁻¹ = (x : C t)⁻¹)))) → Split := by
  intro L T₀ Y H₀ J E Split hcov
  have hlift := all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift n hn
    S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hc := hcov.elim hlift.1 hlift.2
  obtain ⟨hJperf, hJnormal, htJ, hJimage, hJN, hYJN, hEodd, hcenterJ, hEt, hEtcomm, ⟨φ, hφ⟩,
    -, ⟨F, hF, hFfin, eta, π, hFcard, hetat, hπ, hπsurj, hπker⟩, -, -, huniq⟩ := hc
  have hJY : J ≤ Y := (Subgroup.map_subtype_le _).trans inf_le_left
  have hJcent : J ≤ Subgroup.centralizer (N t : Set (C t)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJN
  have hNY : N t ≤ Y := fun x hx => by
    change barKappa t (nu t x) ∈ L
    have h1 : nu t x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1, map_one]
    exact L.one_mem
  have hEZN : E ≤ (Subgroup.center (N t)).map (N t).subtype := by
    rintro x ⟨hxJ, hxN⟩
    refine ⟨⟨x, hxN⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hJcent hxJ)) g g.2
  have hEcJ : ∀ e : J, (e : C t) ∈ E → e ∈ Subgroup.center J := by
    intro e he
    have hmem : (e : C t) ∈ (Subgroup.center J).map J.subtype := by
      rw [hcenterJ]
      exact Subgroup.mem_sup_left he
    obtain ⟨e', he', hee'⟩ := hmem
    have : e' = e := Subtype.ext hee'
    rwa [← this]
  have hπt : π ⟨tInC t, htJ⟩ = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
    rw [hπ ⟨tInC t, htJ⟩ (hJY htJ), CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_eq_neg_one]
    exact hetat _
  let ρ : J →* CFSG.Semidihedral.OddProjectiveCoverKernel.S F :=
    (CFSG.Semidihedral.ProjectiveSL2Cover.scalarQuotient F 2).comp π
  have hρt : ρ ⟨tInC t, htJ⟩ = 1 := by
    change CFSG.Semidihedral.ProjectiveSL2Cover.scalarQuotient F 2 (π ⟨tInC t, htJ⟩) = 1
    rw [hπt, ← MonoidHom.mem_ker, CFSG.Semidihedral.ProjectiveSL2Cover.scalarQuotient_two_ker]
    exact Subgroup.mem_zpowers _
  let Zj : Subgroup J := (Subgroup.zpowers (tInC t)).subgroupOf J
  have hZjcenter : Zj ≤ Subgroup.center J := by
    intro z hz
    have hzc : (z : C t) ∈ Subgroup.center (C t) :=
      (Subgroup.zpowers_le.mpr (tInC_central t)) hz
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hzc) w)
  have : Zj.Normal := Subgroup.normal_of_le_center hZjcenter
  have hZjker : Zj ≤ ρ.ker := by
    intro z hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hz' : z = ⟨tInC t, htJ⟩ ^ k := Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk.symm)
    rw [MonoidHom.mem_ker, hz', map_zpow, hρt, one_zpow]
  let ρbar : J ⧸ Zj →* CFSG.Semidihedral.OddProjectiveCoverKernel.S F :=
    QuotientGroup.lift Zj ρ hZjker
  have hρsurj : Function.Surjective ρ :=
    (CFSG.Semidihedral.ProjectiveSL2Cover.scalarQuotient_surjective F 2).comp hπsurj
  have hρbarsurj : Function.Surjective ρbar := by
    intro y
    obtain ⟨x, rfl⟩ := hρsurj y
    exact ⟨(x : J ⧸ Zj), rfl⟩
  have hkerρ : ∀ x : J, ρ x = 1 → ∃ e : J, (e : C t) ∈ E ∧ ∃ k : ℤ,
      x = e * ⟨tInC t, htJ⟩ ^ k := by
    intro x hx
    have hmem : π x ∈ (CFSG.Semidihedral.ProjectiveSL2Cover.scalarQuotient F 2).ker := hx
    rw [CFSG.Semidihedral.ProjectiveSL2Cover.scalarQuotient_two_ker] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨x * (⟨tInC t, htJ⟩ ^ k)⁻¹, ?_, k, by group⟩
    have h1 : π (x * (⟨tInC t, htJ⟩ ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hπt, hk, mul_inv_cancel]
    have h2 : x * (⟨tInC t, htJ⟩ ^ k)⁻¹ ∈ E.subgroupOf J := by
      rw [← hπker]
      exact h1
    exact h2
  let ι : E →* J ⧸ Zj := (QuotientGroup.mk' Zj).comp (Subgroup.inclusion inf_le_left)
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h1 : Subgroup.inclusion (inf_le_left : E ≤ J) e ∈ Zj := (QuotientGroup.eq_one_iff _).mp he
    have h2 : (e : C t) ∈ E ⊓ Subgroup.zpowers (tInC t) := ⟨e.2, h1⟩
    rw [hEt, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hιrange : ι.range = ρbar.ker := by
    ext q
    constructor
    · rintro ⟨e, rfl⟩
      rw [MonoidHom.mem_ker]
      have h1 : Subgroup.inclusion (inf_le_left : E ≤ J) e ∈ π.ker := by
        rw [hπker]
        exact e.2
      change CFSG.Semidihedral.ProjectiveSL2Cover.scalarQuotient F 2
        (π (Subgroup.inclusion inf_le_left e)) = 1
      rw [MonoidHom.mem_ker.mp h1, map_one]
    · intro hq
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      have hx : ρ x = 1 := hq
      obtain ⟨e, heE, k, hxe⟩ := hkerρ x hx
      refine ⟨⟨e, heE⟩, ?_⟩
      have htk : ((⟨tInC t, htJ⟩ ^ k : J) : J ⧸ Zj) = 1 := by
        rw [QuotientGroup.eq_one_iff]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
      change ((Subgroup.inclusion inf_le_left ⟨(e : C t), heE⟩ : J) : J ⧸ Zj) = (x : J ⧸ Zj)
      rw [hxe, QuotientGroup.mk_mul, htk, mul_one]
      rfl
  let eE : E ≃* ρbar.ker := (MonoidHom.ofInjective hιinj).trans (MulEquiv.subgroupCongr hιrange)
  have hkercentral : ρbar.ker ≤ Subgroup.center (J ⧸ Zj) := by
    rw [← hιrange]
    rintro _ ⟨e, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hec := hEcJ (Subgroup.inclusion inf_le_left e) e.2
    change (y : J ⧸ Zj) * ((Subgroup.inclusion inf_le_left e : J) : J ⧸ Zj) =
      ((Subgroup.inclusion inf_le_left e : J) : J ⧸ Zj) * (y : J ⧸ Zj)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.mp hec) y]
  have hkerodd : Odd (Nat.card ρbar.ker) := by
    rw [← Nat.card_congr eE.toEquiv]
    exact hEodd
  have hbound := odd_projective_linear_two_perfect_odd_cover_kernel F hp hpodd hf hFcard ρbar
    hρbarsurj hkercentral hkerodd
  let μ0 : J × N t →* C t := J.subtype.noncommCoprod (N t).subtype fun j a =>
    ((Subgroup.mem_centralizer_iff.mp (hJcent j.2)) a a.2).symm
  have hμ0Y : ∀ x : J × N t, μ0 x ∈ Y := fun x => Y.mul_mem (hJY x.1.2) (hNY x.2.2)
  let μ : J × N t →* Y := μ0.codRestrict Y hμ0Y
  have hμ : ∀ x : J × N t, (μ x : C t) = x.1 * x.2 := fun x => rfl
  have hμsurj : Function.Surjective μ := by
    intro y
    have hy : (y : C t) ∈ ((J ⊔ N t : Subgroup (C t)) : Set (C t)) := by
      rw [← hYJN]
      exact y.2
    rw [Subgroup.mul_normal J (N t)] at hy
    obtain ⟨j, hj, a, ha, hja⟩ := hy
    exact ⟨(⟨j, hj⟩, ⟨a, ha⟩), Subtype.ext hja⟩
  have hμker : ∀ x : J × N t, x ∈ μ.ker ↔ (x.1 : C t) ∈ E ∧ (x.2 : C t) = (x.1 : C t)⁻¹ := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (x.1 : C t) * x.2 = 1 := congrArg Subtype.val hx
      have h2 : (x.2 : C t) = (x.1 : C t)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h3 : (x.1 : C t) = (x.2 : C t)⁻¹ := eq_inv_of_mul_eq_one_left h1
      exact ⟨⟨x.1.2, h3 ▸ (N t).inv_mem x.2.2⟩, h2⟩
    · rintro ⟨-, h2⟩
      apply Subtype.ext
      change (x.1 : C t) * x.2 = 1
      rw [h2, mul_inv_cancel]
  have hmain : (Group.IsPerfect J ∧ J ≤ Y ∧ ⁅J, N t⁆ = ⊥ ∧ J.map (nu t) = T₀ ∧
      ∀ J₁ : Subgroup (C t), J₁ ≤ Y → Group.IsPerfect J₁ → ⁅J₁, N t⁆ = ⊥ →
        J₁.map (nu t) = T₀ → J₁ = J) := ⟨hJperf, hJY, hJN, hJimage, huniq⟩
  refine ⟨hmain, hJnormal, htJ, hYJN, fun hne => ?_, fun h9 => ?_⟩
  ·
    have hker1 := hbound.1 hne
    have hE1 : E = ⊥ := by
      have hcardE : Nat.card E = 1 := by
        rw [Nat.card_congr eE.toEquiv, hker1, Subgroup.card_bot]
      exact Subgroup.card_eq_one.mp hcardE
    let νJ : J →* T₀ := ((nu t).comp J.subtype).codRestrict T₀ fun j => hJY j.2
    have hνJinj : Function.Injective νJ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxN : (x : C t) ∈ N t := (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
      have hxE : (x : C t) ∈ E := ⟨x.2, hxN⟩
      rw [hE1, Subgroup.mem_bot] at hxE
      exact Subtype.ext hxE
    have hνJsurj : Function.Surjective νJ := by
      intro u
      have huJ : (u : H t) ∈ J.map (nu t) := by rw [hJimage]; exact u.2
      obtain ⟨j, hjJ, hjeq⟩ := Subgroup.mem_map.mp huJ
      exact ⟨⟨j, hjJ⟩, Subtype.ext hjeq⟩
    have hμinj : Function.Injective μ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      obtain ⟨h1, h2⟩ := (hμker x).mp hx
      rw [hE1, Subgroup.mem_bot] at h1
      have h1' : x.1 = 1 := Subtype.ext h1
      have h2' : x.2 = 1 := by
        apply Subtype.ext
        rw [h2, h1, inv_one]
        rfl
      exact Prod.ext h1' h2'
    exact ⟨hE1, ⟨MulEquiv.ofBijective νJ ⟨hνJinj, hνJsurj⟩, fun x => rfl⟩,
      ⟨F, hF, hFfin, hFcard, ⟨eta⟩⟩, ⟨MulEquiv.ofBijective μ ⟨hμinj, hμsurj⟩, hμ⟩⟩
  ·
    obtain ⟨hcyc, hcard3⟩ := hbound.2 h9
    have hEcyc : IsCyclic E := isCyclic_of_surjective eE.symm.toMonoidHom eE.symm.surjective
    have hcardE : Nat.card E = 1 ∨ Nat.card E = 3 := by
      have h1 : Nat.card E ≤ 3 := by
        rw [Nat.card_congr eE.toEquiv]
        exact hcard3
      have h0 : 0 < Nat.card E := Nat.card_pos
      have hEodd' : Odd (Nat.card E) := hEodd
      obtain ⟨k, hk⟩ := hEodd'
      omega
    have hμcent : μ.ker ≤ Subgroup.center (J × N t) := by
      intro x hx
      obtain ⟨h1, h2⟩ := (hμker x).mp hx
      have hc1 := hEcJ x.1 h1
      have hc2 : x.2 ∈ Subgroup.center (N t) := by
        have h3 : (x.1 : C t)⁻¹ ∈ E := E.inv_mem h1
        obtain ⟨z, hz, hzx⟩ := hEZN h3
        have hz' : z = x.2 := Subtype.ext (hzx.trans h2.symm)
        rwa [← hz']
      rw [Subgroup.mem_center_iff]
      intro g
      exact Prod.ext ((Subgroup.mem_center_iff.mp hc1) g.1) ((Subgroup.mem_center_iff.mp hc2) g.2)
    exact ⟨hEcyc, hcardE, hEZN, hcenterJ, hEt, hEtcomm, ⟨F, hF, hFfin, hFcard, ⟨φ.trans eta⟩⟩,
      ⟨μ, hμsurj, hμ, hμker, hμcent⟩⟩

end CFSG.Semidihedral.Local
