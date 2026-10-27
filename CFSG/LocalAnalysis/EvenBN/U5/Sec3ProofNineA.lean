module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBGeneric
import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6Four

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

section Generic

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem s2a2_exists_mul_of_mem_sup {N X : Subgroup G} (hXN : X ≤ normalizer (N : Set G)) {x : G}
    (hx : x ∈ N ⊔ X) : ∃ n ∈ N, ∃ y ∈ X, x = n * y := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, one_mem _, (mul_one x).symm⟩
    · exact ⟨1, one_mem _, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, a, ha, rfl⟩ := hx
    obtain ⟨m, hm, b, hb, rfl⟩ := hy
    exact ⟨n * (a * m * a⁻¹), mul_mem hn ((mem_normalizer_iff.1 (hXN ha) m).1 hm), a * b,
      mul_mem ha hb, by group⟩
  | inv x _ hx =>
    obtain ⟨n, hn, a, ha, rfl⟩ := hx
    refine ⟨a⁻¹ * n⁻¹ * a, ?_, a⁻¹, inv_mem ha, by group⟩
    have := (mem_normalizer_iff.1 (hXN (inv_mem ha)) n⁻¹).1 (inv_mem hn)
    simpa using this

theorem s2a2_mem_centralizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ centralizer (A : Set G))
    (hB : x ∈ centralizer (B : Set G)) : x ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  rw [SetLike.mem_coe, Subgroup.sup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact mem_centralizer_iff.1 hA y hy
    · exact mem_centralizer_iff.1 hB y hy
  | one => simp
  | mul y z _ _ hy hz =>
    calc y * z * x = y * (z * x) := mul_assoc _ _ _
      _ = y * (x * z) := by rw [hz]
      _ = (y * x) * z := (mul_assoc _ _ _).symm
      _ = (x * y) * z := by rw [hy]
      _ = x * (y * z) := mul_assoc _ _ _
  | inv y _ hy => exact (Commute.inv_left (show Commute y x from hy))

theorem s2a2_le_normalizer_commutator [Finite G] {M A : Subgroup G} :
    M ≤ normalizer ((⁅M, A⁆ : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_fintype fun x hx => ?_
  rw [Subgroup.commutator_def] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨m, hm, a, ha, rfl⟩ := hx
    have h1 : ⁅g * m, a⁆ * ⁅g, a⁆⁻¹ = g * ⁅m, a⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [← h1]
    exact mul_mem (Subgroup.commutator_mem_commutator (mul_mem hg hm) ha)
      (inv_mem (Subgroup.commutator_mem_commutator hg ha))
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem s2a2_commutator_le_left {M A : Subgroup G} (hA : A ≤ normalizer (M : Set G)) :
    ⁅M, A⁆ ≤ M := by
  rw [Subgroup.commutator_le]
  intro m hm a ha
  rw [commutatorElement_def]
  have h1 := (mem_normalizer_iff.1 (hA ha) m⁻¹).1 (inv_mem hm)
  have h2 : m * a * m⁻¹ * a⁻¹ = m * (a * m⁻¹ * a⁻¹) := by group
  rw [h2]
  exact mul_mem hm h1

theorem s2a2_mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro x
  show x ∈ A ⊓ B ↔ g * x * g⁻¹ ∈ A ⊓ B
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (hA x) (hB x)

theorem s2a2_le_normalizer_of_comm [Finite G] {N X : Subgroup G}
    (h : ∀ x ∈ X, ∀ n ∈ N, x * n = n * x) : X ≤ normalizer (N : Set G) := fun x hx =>
  mem_normalizer_fintype fun n hn => by rw [h x hx n hn, mul_inv_cancel_right]; exact hn

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s2a2_fix {M N J : Subgroup G} (hM : IsPGroup 2 M) (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set G)) (hJM : J ≤ normalizer (M : Set G))
    (hJN : J ≤ normalizer (N : Set G)) (hJ : Odd (Nat.card J)) {m : G} (hm : m ∈ M)
    (hfix : ∀ j ∈ J, m⁻¹ * (j * m * j⁻¹) ∈ N) :
    ∃ c ∈ M ⊓ centralizer (J : Set G), ∃ n ∈ N, m = c * n := by
  haveI : Group.IsNilpotent M := hM.isNilpotent
  exact Common.exists_mem_inf_centralizer_mul_of_coprime hNM hMN hJM hJN inferInstance
    (coprime_card_of_odd hJ hM) hm hfix

theorem s2a2_odd_card_of_le_I {J : Subgroup G} (hJ : J ≤ d.I) : Odd (Nat.card J) :=
  Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le hJ)

theorem Hyp.s2a2_I_le_B₃ (hd : d.Hyp) : d.I ≤ normalizer (d.B₃ : Set G) := fun i hi => by
  rw [← hd.normalizer_B₁_eq]
  exact (hd.I_le_normalizer_B₁ hi).1

theorem Hyp.s2a2_I_le_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.I ≤ normalizer (d.B₆ : Set G) := fun i hi =>
  d.normalizer_le_normalizer_B₆ (hd.normalizer_B₁_le_normalizer_FB₃ hGMS
    (hd.I_le_normalizer_B₁ hi).1)

theorem Hyp.s2a2_I_le_centralizer_t (hd : d.Hyp) : d.I ≤ centralizer ({d.t} : Set G) :=
  fun _ hi => (hd.I_le_normalizer_B₁ hi).2

theorem Hyp.s2a2_psi (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ∃ ψ : d.B₆ →* d.A₃ ⧸ d.A₁.subgroupOf d.A₃, Function.Surjective ψ ∧
      ψ.ker = (d.F ⊔ d.B₃).subgroupOf d.B₆ ∧
      ∀ c ∈ d.I, ∀ (s : d.B₆) (a : d.A₃) (hs : c * s * c⁻¹ ∈ d.B₆) (ha : c * a * c⁻¹ ∈ d.A₃),
        ψ s = QuotientGroup.mk a → ψ ⟨c * s * c⁻¹, hs⟩ = QuotientGroup.mk ⟨c * a * c⁻¹, ha⟩ := by
  obtain ⟨-, -, -, -, ψ, hψs, hψk, -, hψc⟩ := hd.sec3_7 hGMS
  exact ⟨ψ, hψs, hψk, fun c hc s a hs ha => hψc c ⟨hd.s2a2_I_le_B₃ hc,
    hd.s2a2_I_le_centralizer_t hc⟩ s a hs ha⟩

theorem Hyp.s2a2_A₃_le_centralizer_t (hd : d.Hyp) : d.A₃ ≤ centralizer ({d.t} : Set G) :=
  fun _ ha => hd.L_le_centralizer (d.pull_le_L _ ha)

theorem s2a2_isPGroup_A₃ (d : Data G h) : IsPGroup 2 d.A₃ := d.isPGroup_P.to_le d.A₃_le_P

theorem s2a2_A₃_le_normalizer_A₁ (d : Data G h) : d.A₃ ≤ normalizer (d.A₁ : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer d.A₁_le_A₃).1 (normal_A₁_subgroupOf_A₃ d)

theorem Hyp.s2a2_FA₃_centralizer (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {J : Subgroup G} (hJ : J ≤ d.I) (hA : d.A₃ ⊓ centralizer (J : Set G) = ⊥) {y a : G}
    (hy : y ∈ d.F) (ha : a ∈ d.A₃) (hC : y * a ∈ centralizer (J : Set G)) : y * a = 1 := by
  have hJodd : Odd (Nat.card J) := s2a2_odd_card_of_le_I hJ
  have hJA₃ : J ≤ normalizer (d.A₃ : Set G) := fun j hj =>
    hd.normalizer_B₁_le_normalizer_A₃ (hd.I_le_normalizer_B₁ (hJ hj)).1
  have hJA₁ : J ≤ normalizer (d.A₁ : Set G) := hJ.trans d.I_le_normalizer_A₁
  have hFA : d.F ⊓ d.A₃ ≤ d.A₁ := fun z hz => by
    have := mem_inf.2 ⟨hz.1, d.A₃_le_P hz.2⟩
    rwa [hd.F_inf_P hGMS] at this
  have hfix : ∀ j ∈ J, a⁻¹ * (j * a * j⁻¹) ∈ d.A₁ := by
    intro j hj
    have hjy : j * y * j⁻¹ ∈ d.F := (mem_normalizer_iff.1 (hd.I_le_normalizer_F hGMS (hJ hj)) y).1 hy
    have hja : j * a * j⁻¹ ∈ d.A₃ := (mem_normalizer_iff.1 (hJA₃ hj) a).1 ha
    have hjx : j * (y * a) * j⁻¹ = y * a := by
      rw [mem_centralizer_iff.1 hC j hj, mul_inv_cancel_right]
    have h1 : j * a * j⁻¹ = (j * y * j⁻¹)⁻¹ * (y * a) := by
      rw [← hjx]; group
    have h2 : a⁻¹ * (j * a * j⁻¹) = (j * y * j⁻¹)⁻¹ * y := by
      have hc : (j * y * j⁻¹)⁻¹ * y ∈ d.F := mul_mem (inv_mem hjy) hy
      have hcomm := mem_centralizer_iff.1 (hd.F_le_centralizer_A₃ hc) a ha
      calc a⁻¹ * (j * a * j⁻¹) = a⁻¹ * ((j * y * j⁻¹)⁻¹ * y * a) := by rw [h1]; group
        _ = a⁻¹ * (a * ((j * y * j⁻¹)⁻¹ * y)) := by rw [hcomm]
        _ = (j * y * j⁻¹)⁻¹ * y := by group
    refine hFA (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · rw [h2]; exact mul_mem (inv_mem hjy) hy
    · exact mul_mem (inv_mem ha) hja
  obtain ⟨c, hc, n, hn, hcn⟩ := s2a2_fix (M := d.A₃) (N := d.A₁) (J := J)
    (s2a2_isPGroup_A₃ d) d.A₁_le_A₃ (s2a2_A₃_le_normalizer_A₁ d) hJA₃ hJA₁ hJodd ha hfix
  have hc1 : c = 1 := by
    have : c ∈ d.A₃ ⊓ centralizer (J : Set G) := hc
    rw [hA] at this
    exact Subgroup.mem_bot.1 this
  rw [hc1, one_mul] at hcn
  have haA₁ : a ∈ d.A₁ := hcn ▸ hn
  have hxF : y * a ∈ d.F := mul_mem hy (hd.A₁_le_F haA₁)
  have hcr : (y * a)⁻¹ * d.t * (y * a) * d.t = 1 := by
    have hcrA : (y * a)⁻¹ * d.t * (y * a) * d.t ∈ d.A₁ := hd.cr_F_mem hxF
    have hcrC : (y * a)⁻¹ * d.t * (y * a) * d.t ∈ centralizer (J : Set G) := by
      rw [mem_centralizer_iff]
      intro j hj
      have h1 : Commute j (y * a) := mem_centralizer_iff.1 hC j hj
      have h2 : Commute j d.t :=
        (mem_centralizer_iff.1 (hd.s2a2_I_le_centralizer_t (hJ hj)) d.t (Set.mem_singleton _)).symm
      exact (((h1.inv_right.mul_right h2).mul_right h1).mul_right h2)
    have : (y * a)⁻¹ * d.t * (y * a) * d.t ∈ d.A₃ ⊓ centralizer (J : Set G) :=
      Subgroup.mem_inf.2 ⟨d.A₁_le_A₃ hcrA, hcrC⟩
    rw [hA] at this
    exact Subgroup.mem_bot.1 this
  have hxA₁ : y * a ∈ d.A₁ := (hd.cr_F_eq_one_iff hGMS hxF).1 hcr
  have : y * a ∈ d.A₃ ⊓ centralizer (J : Set G) := Subgroup.mem_inf.2 ⟨d.A₁_le_A₃ hxA₁, hC⟩
  rw [hA] at this
  exact Subgroup.mem_bot.1 this

theorem Hyp.s2a2_centralizer_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {J : Subgroup G} (hJ : J ≤ d.I) (hA : d.A₃ ⊓ centralizer (J : Set G) = ⊥) :
    d.B₆ ⊓ centralizer (J : Set G) ≤ zpowers d.t := by
  intro x hx
  obtain ⟨hxB, hxC⟩ := hx
  obtain ⟨ψ, -, hψk, hψc⟩ := hd.s2a2_psi hGMS
  have hJodd : Odd (Nat.card J) := s2a2_odd_card_of_le_I hJ
  have hJA₃ : J ≤ normalizer (d.A₃ : Set G) := fun j hj =>
    hd.normalizer_B₁_le_normalizer_A₃ (hd.I_le_normalizer_B₁ (hJ hj)).1
  have hJA₁ : J ≤ normalizer (d.A₁ : Set G) := hJ.trans d.I_le_normalizer_A₁
  have hxψ : ψ ⟨x, hxB⟩ = 1 := by
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (ψ ⟨x, hxB⟩)
    have hfix : ∀ j ∈ J, (a : G)⁻¹ * (j * (a : G) * j⁻¹) ∈ d.A₁ := by
      intro j hj
      have hjB₆ : j * x * j⁻¹ ∈ d.B₆ :=
        (mem_normalizer_iff.1 (hd.s2a2_I_le_B₆ hGMS (hJ hj)) x).1 hxB
      have hjA₃ : j * (a : G) * j⁻¹ ∈ d.A₃ := (mem_normalizer_iff.1 (hJA₃ hj) a).1 a.2
      have hjx : j * x * j⁻¹ = x := by
        rw [mem_centralizer_iff.1 hxC j hj, mul_inv_cancel_right]
      have h1 := hψc j (hJ hj) ⟨x, hxB⟩ a hjB₆ hjA₃ ha.symm
      have h2 : (⟨j * x * j⁻¹, hjB₆⟩ : d.B₆) = ⟨x, hxB⟩ := Subtype.ext hjx
      rw [h2, ← ha] at h1
      have h3 := QuotientGroup.eq.1 h1
      rw [Subgroup.mem_subgroupOf] at h3
      exact h3
    obtain ⟨c, hc, n, hn, hcn⟩ := s2a2_fix (M := d.A₃) (N := d.A₁) (J := J)
      (s2a2_isPGroup_A₃ d) d.A₁_le_A₃ (s2a2_A₃_le_normalizer_A₁ d) hJA₃ hJA₁ hJodd a.2 hfix
    have hc1 : c = 1 := by
      have : c ∈ d.A₃ ⊓ centralizer (J : Set G) := hc
      rw [hA] at this
      exact Subgroup.mem_bot.1 this
    rw [hc1, one_mul] at hcn
    have hna : (a : G) ∈ d.A₁ := hcn ▸ hn
    rw [← ha]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hna)
  have hxFB : x ∈ d.F ⊔ d.B₃ := by
    have : (⟨x, hxB⟩ : d.B₆) ∈ ψ.ker := hxψ
    rw [hψk, Subgroup.mem_subgroupOf] at this
    exact this
  obtain ⟨y, hy, a, ha, hxe⟩ := hd.exists_of_mem_FB₃ hxFB
  have hat : d.t * a = a * d.t :=
    mem_centralizer_iff.1 (hd.s2a2_A₃_le_centralizer_t ha) d.t (Set.mem_singleton _)
  have hjt : ∀ j ∈ J, Commute j d.t := fun j hj =>
    (mem_centralizer_iff.1 (hd.s2a2_I_le_centralizer_t (hJ hj)) d.t (Set.mem_singleton _)).symm
  rcases hxe with hxe | hxe
  · rw [hxe] at hxC ⊢
    rw [hd.s2a2_FA₃_centralizer hGMS hJ hA hy ha hxC]
    exact one_mem _
  · have hxe' : x = (y * a) * d.t := by rw [hxe, hat, ← mul_assoc]
    have hya : y * a = x * d.t := by rw [hxe', mul_assoc, hd.t_mul_t, mul_one]
    have hC : y * a ∈ centralizer (J : Set G) := by
      rw [hya, mem_centralizer_iff]
      intro j hj
      exact Commute.mul_right (mem_centralizer_iff.1 hxC j hj) (hjt j hj)
    rw [hxe', hd.s2a2_FA₃_centralizer hGMS hJ hA hy ha hC, one_mul]
    exact Subgroup.mem_zpowers _

theorem Hyp.s2a2_hA₁ (hd : d.Hyp) : d.A₃ ⊓ centralizer (d.I₁ : Set G) = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h⟩ := d.sec2_1_two hd.two_le
  refine le_bot_iff.1 fun x hx => ?_
  rw [← h]
  exact Subgroup.mem_inf.2 ⟨hx.1, Subgroup.mem_inf.2 ⟨d.A₃_le_P hx.1, hx.2⟩⟩

theorem Hyp.s2a2_hA₂ (hd : d.Hyp) :
    d.A₃ ⊓ centralizer ((d.I₂ ⊔ (d.I ⊓ d.N₂) : Subgroup G) : Set G) = ⊥ := by
  obtain ⟨-, h, -, -⟩ := d.sec2_1_four hd.two_le
  refine le_bot_iff.1 fun x hx => ?_
  rw [← h]
  have h2 : x ∈ centralizer (d.I₂ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hx.2
  have h3 : x ∈ centralizer ((d.I ⊓ d.N₂ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right) hx.2
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨d.A₃_le_P hx.1, h2⟩, h3⟩

theorem Hyp.s2a2_hA₅ (hd : d.Hyp) :
    d.A₃ ⊓ centralizer ((d.I₅ ⊔ (d.I ⊓ d.N₅) : Subgroup G) : Set G) = ⊥ := by
  obtain ⟨-, -, -, h⟩ := d.sec2_1_four hd.two_le
  refine le_bot_iff.1 fun x hx => ?_
  rw [← h]
  have h2 : x ∈ centralizer (d.I₅ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hx.2
  have h3 : x ∈ centralizer ((d.I ⊓ d.N₅ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right) hx.2
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨d.A₃_le_P hx.1, h2⟩, h3⟩

theorem Hyp.s2a2_D_le_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.D ≤ d.B₆ :=
  s2a2_commutator_le_left fun i hi => hd.s2a2_I_le_B₆ hGMS (d.I₁_le_I hi)

theorem s2a2_B₆_le_normalizer_D (d : Data G h) : d.B₆ ≤ normalizer (d.D : Set G) :=
  s2a2_le_normalizer_commutator (M := d.B₆) (A := d.I₁)

theorem Hyp.s2a2_I_le_D (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.I ≤ normalizer (d.D : Set G) := fun i hi =>
  d.mem_normalizer_D (hd.s2a2_I_le_B₆ hGMS hi)
    (mem_normalizer_of_mem_centralizer' (d.I_le_centralizer_I₁ hi))

theorem Hyp.s2a2_B₆_decomp (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {b : G} (hb : b ∈ d.B₆) : ∃ c ∈ zpowers d.t, ∃ n ∈ d.D, b = c * n := by
  obtain ⟨c, hc, n, hn, rfl⟩ := s2a2_fix (M := d.B₆) (N := d.D) (J := d.I₁) d.isPGroup_B₆
    (hd.s2a2_D_le_B₆ hGMS) (s2a2_B₆_le_normalizer_D d)
    (fun i hi => hd.s2a2_I_le_B₆ hGMS (d.I₁_le_I hi))
    (fun i hi => hd.s2a2_I_le_D hGMS (d.I₁_le_I hi) |> fun _ => by
      exact d.mem_normalizer_D (hd.s2a2_I_le_B₆ hGMS (d.I₁_le_I hi))
        (mem_normalizer_of_mem_centralizer' (d.I_le_centralizer_I₁ (d.I₁_le_I hi))))
    (s2a2_odd_card_of_le_I d.I₁_le_I) hb
    (fun j hj => by
      have h2 := Subgroup.commutator_mem_commutator (inv_mem hb) hj
      rw [commutatorElement_def] at h2
      have h3 : b⁻¹ * (j * b * j⁻¹) ∈ (⁅d.B₆, d.I₁⁆ : Subgroup G) := by
        simpa [mul_assoc] using h2
      exact h3)
  exact ⟨c, hd.s2a2_centralizer_B₆ hGMS d.I₁_le_I hd.s2a2_hA₁ hc, n, hn, rfl⟩

theorem Hyp.s2a2_comm_mem_D (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {b k : G} (hb : b ∈ d.B₆) (hk : k ∈ d.I) : b⁻¹ * (k * b * k⁻¹) ∈ d.D := by
  obtain ⟨c, hc, n, hn, rfl⟩ := hd.s2a2_B₆_decomp hGMS hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hkt : Commute k d.t :=
    (mem_centralizer_iff.1 (hd.s2a2_I_le_centralizer_t hk) d.t (Set.mem_singleton _)).symm
  have hck : k * d.t ^ m = d.t ^ m * k := (hkt.zpow_right m).eq
  have hkn : k * n * k⁻¹ ∈ d.D := (mem_normalizer_iff.1 (hd.s2a2_I_le_D hGMS hk) n).1 hn
  have h1 : k * (d.t ^ m * n) * k⁻¹ = d.t ^ m * (k * n * k⁻¹) := by
    calc k * (d.t ^ m * n) * k⁻¹ = (k * d.t ^ m) * n * k⁻¹ := by group
      _ = (d.t ^ m * k) * n * k⁻¹ := by rw [hck]
      _ = d.t ^ m * (k * n * k⁻¹) := by group
  rw [h1, show (d.t ^ m * n)⁻¹ * (d.t ^ m * (k * n * k⁻¹)) = n⁻¹ * (k * n * k⁻¹) by group]
  exact mul_mem (inv_mem hn) hkn

theorem s2a2_N₅_le_centralizer_I₅ (d : Data G h) : d.N₅ ≤ centralizer (d.I₅ : Set G) := by
  rw [d.N₅_eq, d.sec2_1_five.2.2.2.2.1]
  rintro _ ⟨n, hn, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨i, hi, rfl⟩
  have := mem_centralizer_iff.1 (d.N₂_le_centralizer_I₂ hn) i hi
  rw [← map_mul, ← map_mul, this]

theorem s2a2_N₂_le_M₂ (d : Data G h) : d.N₂ ≤ d.M₂ := le_normalClosureIn d.N₂_le_centralizer_I₂

theorem s2a2_N₅_le_M₅ (d : Data G h) : d.N₅ ≤ d.M₅ := le_normalClosureIn (s2a2_N₅_le_centralizer_I₅ d)

theorem s2a2_M₂_le_centralizer_I₂ (d : Data G h) : d.M₂ ≤ centralizer (d.I₂ : Set G) :=
  normalClosureIn_le_self _ _

theorem s2a2_M₅_le_centralizer_I₅ (d : Data G h) : d.M₅ ≤ centralizer (d.I₅ : Set G) :=
  normalClosureIn_le_self _ _

theorem s2a2_centralizer_I₂_le_normalizer_M₂ (d : Data G h) :
    centralizer (d.I₂ : Set G) ≤ normalizer (d.M₂ : Set G) := le_normalizer_normalClosureIn _ _

theorem s2a2_centralizer_I₅_le_normalizer_M₅ (d : Data G h) :
    centralizer (d.I₅ : Set G) ≤ normalizer (d.M₅ : Set G) := le_normalizer_normalClosureIn _ _

theorem Hyp.s2a2_Y (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {I' N' M' : Subgroup G} (hI' : I' ≤ d.I) (hNM : N' ≤ M')
    (hCM : centralizer (I' : Set G) ≤ normalizer (M' : Set G))
    (hA : d.A₃ ⊓ centralizer ((I' ⊔ (d.I ⊓ N') : Subgroup G) : Set G) = ⊥) {y : G}
    (hy : y ∈ d.B₆ ⊓ centralizer (I' : Set G)) :
    ∃ c ∈ zpowers d.t, ∃ n ∈ d.D ⊓ centralizer (I' : Set G) ⊓ M', y = c * n := by
  have hIC : d.I ≤ centralizer (I' : Set G) := fun i hi =>
    mem_centralizer_iff.2 fun j hj => d.I_comm (hI' hj) hi
  have hKI : d.I ⊓ N' ≤ d.I := inf_le_left
  have hM : IsPGroup 2 ↥(d.B₆ ⊓ centralizer (I' : Set G)) := d.isPGroup_B₆.to_inf_left
  have hNM' : d.D ⊓ centralizer (I' : Set G) ⊓ M' ≤ d.B₆ ⊓ centralizer (I' : Set G) :=
    fun x hx => Subgroup.mem_inf.2 ⟨hd.s2a2_D_le_B₆ hGMS hx.1.1, hx.1.2⟩
  have hMN : d.B₆ ⊓ centralizer (I' : Set G) ≤
      normalizer ((d.D ⊓ centralizer (I' : Set G) ⊓ M' : Subgroup G) : Set G) := fun g hg =>
    s2a2_mem_normalizer_inf (s2a2_mem_normalizer_inf (s2a2_B₆_le_normalizer_D d hg.1)
      (Subgroup.le_normalizer hg.2)) (hCM hg.2)
  have hKM : d.I ⊓ N' ≤ normalizer ((d.B₆ ⊓ centralizer (I' : Set G) : Subgroup G) : Set G) :=
    fun k hk => s2a2_mem_normalizer_inf (hd.s2a2_I_le_B₆ hGMS (hKI hk))
      (Subgroup.le_normalizer (hIC (hKI hk)))
  have hKN : d.I ⊓ N' ≤
      normalizer ((d.D ⊓ centralizer (I' : Set G) ⊓ M' : Subgroup G) : Set G) := fun k hk =>
    s2a2_mem_normalizer_inf (s2a2_mem_normalizer_inf (hd.s2a2_I_le_D hGMS (hKI hk))
      (Subgroup.le_normalizer (hIC (hKI hk)))) (hCM (hIC (hKI hk)))
  obtain ⟨c, hc, n, hn, hcn⟩ := s2a2_fix hM hNM' hMN hKM hKN (s2a2_odd_card_of_le_I hKI) hy
    (fun k hk => by
      have hyB : y ∈ d.B₆ := hy.1
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hd.s2a2_comm_mem_D hGMS hyB (hKI hk), ?_⟩, ?_⟩
      · exact mul_mem (inv_mem hy.2) (mul_mem (mul_mem (hIC (hKI hk)) hy.2) (inv_mem (hIC (hKI hk))))
      · have h1 : y⁻¹ * k * y ∈ M' := by
          have := (mem_normalizer_iff.1 (hCM (inv_mem hy.2)) k).1 (hNM hk.2)
          simpa using this
        have h2 : y⁻¹ * (k * y * k⁻¹) = (y⁻¹ * k * y) * k⁻¹ := by group
        rw [h2]
        exact mul_mem h1 (inv_mem (hNM hk.2)))
  refine ⟨c, hd.s2a2_centralizer_B₆ hGMS (J := I' ⊔ (d.I ⊓ N')) (sup_le hI' hKI) hA
    ⟨hc.1.1, s2a2_mem_centralizer_sup hc.1.2 hc.2⟩, n, hn, hcn⟩

theorem Hyp.s2a2_Y₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {y : G}
    (hy : y ∈ d.B₆ ⊓ centralizer (d.I₂ : Set G)) :
    ∃ c ∈ zpowers d.t, ∃ n ∈ d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂, y = c * n :=
  hd.s2a2_Y hGMS d.I₂_le_I (s2a2_N₂_le_M₂ d) (s2a2_centralizer_I₂_le_normalizer_M₂ d)
    hd.s2a2_hA₂ hy

theorem Hyp.s2a2_Y₅ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {y : G}
    (hy : y ∈ d.B₆ ⊓ centralizer (d.I₅ : Set G)) :
    ∃ c ∈ zpowers d.t, ∃ n ∈ d.D ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅, y = c * n :=
  hd.s2a2_Y hGMS d.I₅_le_I (s2a2_N₅_le_M₅ d) (s2a2_centralizer_I₅_le_normalizer_M₅ d)
    hd.s2a2_hA₅ hy

theorem Hyp.s2a2_S_eq (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hL : d.L₂ = d.E ⊔ d.M₂) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
    (hR : IsSylowOf 2 (S ⊓ centralizer (d.I₂ : Set G)) d.M₂) :
    d.E ≤ S ∧ S ⊓ d.M₂ = S ⊓ centralizer (d.I₂ : Set G) ∧
      S = d.E ⊔ (S ⊓ centralizer (d.I₂ : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : d.E ≤ S := by
    have h := hS.eq_of_le (le_sup_right : S ≤ d.E ⊔ S)
      (sup_le d.E_le_L₂ hS.le)
      (hd.isPGroup_E hGMS |>.to_sup_of_normal_left' hS.isPGroup
        (hS.le.trans (d.L₂_le_normalizer_E)))
    rw [← h]
    exact le_sup_left
  have hSM : S ⊓ d.M₂ = S ⊓ centralizer (d.I₂ : Set G) :=
    hR.eq_of_le (le_inf inf_le_left hR.le) inf_le_right (hS.isPGroup.to_inf_left)
  refine ⟨hE, hSM, le_antisymm (fun x hx => ?_) (sup_le hE inf_le_left)⟩
  have hM₂L : d.M₂ ≤ d.L₂ := hL ▸ le_sup_right
  obtain ⟨e, he, m, hm, rfl⟩ := s2a2_exists_mul_of_mem_sup
    (hM₂L.trans d.L₂_le_normalizer_E) (hL ▸ hS.le hx)
  have hmS : m ∈ S := by
    have := mul_mem (inv_mem (hE he)) hx
    simpa using this
  have hmR : m ∈ S ⊓ centralizer (d.I₂ : Set G) := hSM ▸ Subgroup.mem_inf.2 ⟨hmS, hm⟩
  exact mul_mem (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right hmR)

theorem s2a2_I₂_le_I₆ (d : Data G h) : d.I₂ ≤ d.I₆ := d.pull_mono fun x hx => by
  rw [mem_I₂sub] at hx
  rw [mem_I₆sub]
  exact ⟨hx.1, hx.2.1.trans hx.2.2⟩

theorem s2a2_I₆_le_I (d : Data G h) : d.I₆ ≤ d.I := d.pull_mono (torusEq_le _)

theorem Hyp.s2a2_zpowers_t (hd : d.Hyp) {c : G} (hc : c ∈ zpowers d.t) : c = 1 ∨ c = d.t := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have h2 : d.t ^ (2 : ℤ) = 1 := by rw [zpow_two, hd.t_mul_t]
  rcases Int.even_or_odd' m with ⟨k, rfl | rfl⟩
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem Hyp.s2a2_lift (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {J : Subgroup G} (hJ : J ≤ d.I) {a : G} (ha : a ∈ d.A₁ ⊓ centralizer (J : Set G)) :
    ∃ c ∈ d.F ⊓ centralizer (J : Set G), c⁻¹ * d.t * c * d.t = a := by
  obtain ⟨x, hx, hxa⟩ := hd.exists_F_cr_eq ha.1
  have hJF : J ≤ normalizer (d.F : Set G) := hJ.trans (hd.I_le_normalizer_F hGMS)
  have hJA : J ≤ normalizer (d.A₁ : Set G) := hJ.trans d.I_le_normalizer_A₁
  have hFA : d.F ≤ normalizer (d.A₁ : Set G) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (hd.F_le_centralizer_A₁ hu)
  obtain ⟨c, hc, n, hn, rfl⟩ := s2a2_fix (M := d.F) (N := d.A₁) (J := J) hd.isPGroup_F
    hd.A₁_le_F hFA hJF hJA (s2a2_odd_card_of_le_I hJ) hx fun s hs => by
      have hsC : s ∈ centralizer ({d.t} : Set G) := hd.s2a2_I_le_centralizer_t (hJ hs)
      have hsx : s * x * s⁻¹ ∈ d.F := (mem_normalizer_iff.1 (hJF hs) x).1 hx
      refine hd.inv_mul_mem_A₁_of_cr_eq hGMS hx hsx ?_
      rw [d.cr_conj hsC, hxa, mem_centralizer_iff.1 ha.2 s hs, mul_inv_cancel_right]
  refine ⟨c, hc, ?_⟩
  have hnF := hd.A₁_le_F hn
  have hn1 : n⁻¹ * d.t * n * d.t = 1 := (hd.cr_F_eq_one_iff hGMS hnF).2 hn
  rw [← hxa, hd.cr_F_mul hc.1 hnF, hn1, mul_one]

theorem s2a2_S_comm_V (hLV : d.V ≤ CFSG.centerIn d.L₂) {S : Subgroup G}
    (hS : IsSylowOf 2 S d.L₂) {n w : G} (hn : n ∈ S) (hw : w ∈ d.V) : n * w = w * n :=
  mem_centralizer_iff.1 (hLV hw).2 n (hS.le hn)

theorem Hyp.s2a2_false_of_t_eq (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hLV : d.V ≤ CFSG.centerIn d.L₂) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂) {f n : G}
    (hf : f ∈ d.F) (hn : n ∈ S) (h : f = d.t * n) : False := by
  obtain ⟨w, hw, hne⟩ := hd.exists_V_not_comm_t
  apply hne
  have hnw : n⁻¹ * w = w * n⁻¹ :=
    (Commute.inv_left (show Commute n w from s2a2_S_comm_V hLV hS hn hw)).eq
  have hfw : f * w = w * f := hd.F_comm hGMS f hf w (d.V_le_F hw)
  have ht : d.t = f * n⁻¹ := by rw [h]; group
  rw [ht]
  calc f * n⁻¹ * w = f * (n⁻¹ * w) := mul_assoc _ _ _
    _ = f * (w * n⁻¹) := by rw [hnw]
    _ = (f * w) * n⁻¹ := (mul_assoc _ _ _).symm
    _ = (w * f) * n⁻¹ := by rw [hfw]
    _ = w * (f * n⁻¹) := mul_assoc _ _ _

theorem Hyp.s2a2_F_I₂_le_S (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hLV : d.V ≤ CFSG.centerIn d.L₂) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
    (h1 : d.Sec39a1 S) {f : G} (hf : f ∈ d.F ⊓ centralizer (d.I₂ : Set G)) : f ∈ S := by
  have hFB : d.F ≤ d.B₆ := le_sup_left.trans (hd.FB₃_le_B₆ hGMS)
  obtain ⟨c, hc, n, hn, hfcn⟩ := hd.s2a2_Y₂ hGMS (y := f) (Subgroup.mem_inf.2 ⟨hFB hf.1, hf.2⟩)
  have hnS : n ∈ S := by
    have := hn
    rw [h1.inter₂] at this
    exact this.1
  rcases hd.s2a2_zpowers_t hc with rfl | rfl
  · rw [hfcn, one_mul]; exact hnS
  · exact (hd.s2a2_false_of_t_eq hGMS hLV hS hf.1 hnS hfcn).elim

theorem Hyp.s2a2_F_le_S (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hLV : d.V ≤ CFSG.centerIn d.L₂) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
    (hP : d.P ≤ S) (hE : d.E ≤ S) (h1 : d.Sec39a1 S) : d.F ≤ S := by
  intro f hf
  have haA : f⁻¹ * d.t * f * d.t ∈ d.A₁ := hd.cr_F_mem hf
  obtain ⟨-, ⟨hZ₂, -⟩, ⟨hA₁eq, -⟩, -⟩ := d.sec2_1_two hd.two_le
  have hZ₂A : d.Z₂p ≤ d.A₁ := by rw [hA₁eq]; exact le_sup_left
  have hZpZ₂ : d.Zp ≤ d.Z₂p := by rw [hZ₂]; exact le_sup_left
  have hC₄Z₂ : d.P ⊓ centralizer (d.I₄ : Set G) ≤ d.Z₂p := by rw [hZ₂]; exact le_sup_right
  have hC₆A : d.P ⊓ centralizer (d.I₆ : Set G) ≤ d.A₁ := by rw [hA₁eq]; exact le_sup_right
  have hcomm : ∀ x ∈ d.A₁, ∀ y ∈ d.A₁, x * y = y * x := fun x hx y hy =>
    hd.F_comm hGMS x (hd.A₁_le_F hx) y (hd.A₁_le_F hy)
  obtain ⟨b, hb, c₆, hc₆, hab⟩ := s2a2_exists_mul_of_mem_sup
    (s2a2_le_normalizer_of_comm fun x hx n hn => hcomm x (hC₆A hx) n (hZ₂A hn))
    (hA₁eq ▸ haA : f⁻¹ * d.t * f * d.t ∈ d.Z₂p ⊔ (d.P ⊓ centralizer (d.I₆ : Set G)))
  obtain ⟨z, hz, c₄, hc₄, hbzc⟩ := s2a2_exists_mul_of_mem_sup
    (s2a2_le_normalizer_of_comm fun x hx n hn =>
      hcomm x (hZ₂A (hC₄Z₂ hx)) n (hZ₂A (hZpZ₂ hn)))
    (hZ₂ ▸ hb : b ∈ d.Zp ⊔ (d.P ⊓ centralizer (d.I₄ : Set G)))
  obtain ⟨v, hv, hvz⟩ := hd.exists_V_cr_eq hz
  obtain ⟨f₄, hf₄, hf₄c⟩ := hd.exists_F_I₄_cr_eq hGMS hc₄
  obtain ⟨f₆, hf₆, hf₆c⟩ := hd.s2a2_lift hGMS (s2a2_I₆_le_I d) (a := c₆)
    (Subgroup.mem_inf.2 ⟨hC₆A hc₆, hc₆.2⟩)
  have hvF : v ∈ d.F := d.V_le_F hv
  have hf'F : v * f₄ * f₆ ∈ d.F := mul_mem (mul_mem hvF hf₄.1) hf₆.1
  have hcr : (v * f₄ * f₆)⁻¹ * d.t * (v * f₄ * f₆) * d.t = f⁻¹ * d.t * f * d.t := by
    rw [hd.cr_F_mul (mul_mem hvF hf₄.1) hf₆.1, hd.cr_F_mul hvF hf₄.1, hvz, hf₄c, hf₆c, hab,
      hbzc]
  have ha₁ := hd.inv_mul_mem_A₁_of_cr_eq hGMS hf'F hf hcr
  have hvS : v ∈ S := hE (d.V_le_E hv)
  have hf₄S : f₄ ∈ S := by
    have : f₄ ∈ d.W := by
      rw [hd.W_eq hGMS]; exact Subgroup.mem_sup_right hf₄
    exact hE (d.W_le_E this)
  have hf₆S : f₆ ∈ S := hd.s2a2_F_I₂_le_S hGMS hLV hS h1
    (Subgroup.mem_inf.2 ⟨hf₆.1,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (s2a2_I₂_le_I₆ d)) hf₆.2⟩)
  have : f = (v * f₄ * f₆) * ((v * f₄ * f₆)⁻¹ * f) := by group
  rw [this]
  exact mul_mem (mul_mem (mul_mem hvS hf₄S) hf₆S) (hP (d.A₁_le_P ha₁))

theorem Hyp.s2a2_F_inf_A₃_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ⊓ d.A₃ ≤ d.A₁ := fun z hz => by
  have := Subgroup.mem_inf.2 ⟨hz.1, d.A₃_le_P hz.2⟩
  rwa [hd.F_inf_P hGMS] at this

theorem Hyp.s2a2_comm_A₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {x y : G}
    (hx : x ∈ d.A₃) (hy : y ∈ d.A₃) : x * y * x⁻¹ * y⁻¹ ∈ d.A₁ := by
  have h := (hd.elemAbMod_F_FA₃ hGMS).2 x (Subgroup.mem_sup_right hx) y (Subgroup.mem_sup_right hy)
  rw [commutatorElement_def] at h
  exact hd.s2a2_F_inf_A₃_le hGMS (Subgroup.mem_inf.2 ⟨h,
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)⟩)

theorem Hyp.s2a2_A₃_decomp (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {a : G}
    (ha : a ∈ d.A₃) : ∃ a₁ ∈ d.A₁, ∃ a₂ ∈ d.P ⊓ centralizer (d.I₂ : Set G),
      ∃ a₅ ∈ d.P ⊓ centralizer (d.I₅ : Set G), a = a₁ * a₂ * a₅ := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := d.sec2_1_two hd.two_le
  have hC₂A : d.P ⊓ centralizer (d.I₂ : Set G) ≤ d.A₃ := by
    rw [h8]; exact le_sup_right.trans le_sup_left
  have hC₅A : d.P ⊓ centralizer (d.I₅ : Set G) ≤ d.A₃ := by
    rw [h8]; exact le_sup_right
  have hN : d.A₁ ⊔ (d.P ⊓ centralizer (d.I₂ : Set G)) ≤ d.A₃ := sup_le d.A₁_le_A₃ hC₂A
  obtain ⟨n, hn, a₅, ha₅, rfl⟩ := s2a2_exists_mul_of_mem_sup
    (N := d.A₁ ⊔ (d.P ⊓ centralizer (d.I₂ : Set G))) (X := d.P ⊓ centralizer (d.I₅ : Set G))
    (fun x hx => mem_normalizer_fintype fun m hm => by
      have h1 := hd.s2a2_comm_A₃ hGMS (hC₅A hx) (hN hm)
      have h2 : x * m * x⁻¹ = (x * m * x⁻¹ * m⁻¹) * m := by group
      rw [h2]
      exact mul_mem (Subgroup.mem_sup_left h1) hm) (h8 ▸ ha)
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := s2a2_exists_mul_of_mem_sup
    (fun x hx => s2a2_A₃_le_normalizer_A₁ d (hC₂A hx)) hn
  exact ⟨a₁, ha₁, a₂, ha₂, a₅, ha₅, rfl⟩

theorem Hyp.s2a2_B₆_decomp₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {b : G}
    (hb : b ∈ d.B₆) : ∃ c₂ ∈ d.B₆ ⊓ centralizer (d.I₂ : Set G),
      ∃ c₅ ∈ d.B₆ ⊓ centralizer (d.I₅ : Set G), ∃ n ∈ d.F ⊔ d.B₃, b = c₂ * c₅ * n := by
  obtain ⟨ψ, hψs, hψk, hψc⟩ := hd.s2a2_psi hGMS
  have hFB : d.F ⊔ d.B₃ ≤ d.B₆ := hd.FB₃_le_B₆ hGMS
  have hMN : d.B₆ ≤ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) := by
    have : ((d.F ⊔ d.B₃).subgroupOf d.B₆).Normal := hψk ▸ MonoidHom.normal_ker ψ
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hFB).1 this
  have lift : ∀ J : Subgroup G, J ≤ d.I → ∀ a : d.A₃, (a : G) ∈ centralizer (J : Set G) →
      ∃ c : d.B₆, (c : G) ∈ centralizer (J : Set G) ∧ ψ c = QuotientGroup.mk a := by
    intro J hJ a haJ
    obtain ⟨s, hs⟩ := hψs (QuotientGroup.mk a)
    have hfix : ∀ j ∈ J, (s : G)⁻¹ * (j * (s : G) * j⁻¹) ∈ d.F ⊔ d.B₃ := by
      intro j hj
      have hjB : j * (s : G) * j⁻¹ ∈ d.B₆ :=
        (mem_normalizer_iff.1 (hd.s2a2_I_le_B₆ hGMS (hJ hj)) s).1 s.2
      have hja : j * (a : G) * j⁻¹ = a := by
        rw [mem_centralizer_iff.1 haJ j hj, mul_inv_cancel_right]
      have hjaA : j * (a : G) * j⁻¹ ∈ d.A₃ := by rw [hja]; exact a.2
      have h1 := hψc j (hJ hj) s a hjB hjaA hs
      have h2 : (⟨j * (a : G) * j⁻¹, hjaA⟩ : d.A₃) = a := Subtype.ext hja
      rw [h2, ← hs] at h1
      have h3 : s⁻¹ * (⟨j * (s : G) * j⁻¹, hjB⟩ : d.B₆) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      rw [hψk, Subgroup.mem_subgroupOf] at h3
      exact h3
    obtain ⟨c, hc, n, hn, hcn⟩ := s2a2_fix (M := d.B₆) (N := d.F ⊔ d.B₃) (J := J) d.isPGroup_B₆
      hFB hMN (fun j hj => hd.s2a2_I_le_B₆ hGMS (hJ hj))
      (fun j hj => hd.normalizer_B₁_le_normalizer_FB₃ hGMS (hd.I_le_normalizer_B₁ (hJ hj)).1)
      (s2a2_odd_card_of_le_I hJ) s.2 hfix
    have hnB : n ∈ d.B₆ := hFB hn
    refine ⟨⟨c, hc.1⟩, hc.2, ?_⟩
    have hn1 : ψ ⟨n, hnB⟩ = 1 := by
      have : (⟨n, hnB⟩ : d.B₆) ∈ ψ.ker := by
        rw [hψk, Subgroup.mem_subgroupOf]; exact hn
      exact this
    have : s = ⟨c, hc.1⟩ * ⟨n, hnB⟩ := Subtype.ext hcn
    rw [← hs, this, map_mul, hn1, mul_one]
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (ψ ⟨b, hb⟩)
  obtain ⟨a₁, ha₁, a₂, ha₂, a₅, ha₅, hae⟩ := hd.s2a2_A₃_decomp hGMS a.2
  have hC₂A : d.P ⊓ centralizer (d.I₂ : Set G) ≤ d.A₃ := by
    obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := d.sec2_1_two hd.two_le
    rw [h8]; exact le_sup_right.trans le_sup_left
  have hC₅A : d.P ⊓ centralizer (d.I₅ : Set G) ≤ d.A₃ := by
    obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := d.sec2_1_two hd.two_le
    rw [h8]; exact le_sup_right
  obtain ⟨c₂, hc₂C, hc₂⟩ := lift d.I₂ d.I₂_le_I ⟨a₂, hC₂A ha₂⟩ ha₂.2
  obtain ⟨c₅, hc₅C, hc₅⟩ := lift d.I₅ d.I₅_le_I ⟨a₅, hC₅A ha₅⟩ ha₅.2
  have hψb : ψ ⟨b, hb⟩ = ψ (c₂ * c₅) := by
    rw [map_mul, hc₂, hc₅, ← ha, ← QuotientGroup.mk_mul]
    have h1 : (⟨a₂, hC₂A ha₂⟩ * ⟨a₅, hC₅A ha₅⟩ : d.A₃) = ⟨a₂ * a₅, mul_mem (hC₂A ha₂) (hC₅A ha₅)⟩ :=
      rfl
    have h2 : a = ⟨a₁, d.A₁_le_A₃ ha₁⟩ * ⟨a₂, hC₂A ha₂⟩ * ⟨a₅, hC₅A ha₅⟩ := Subtype.ext hae
    rw [h2, mul_assoc, QuotientGroup.mk_mul]
    have h3 : (QuotientGroup.mk ⟨a₁, d.A₁_le_A₃ ha₁⟩ : d.A₃ ⧸ d.A₁.subgroupOf d.A₃) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 ha₁)
    rw [h3, one_mul, QuotientGroup.mk_mul]
  have hn : (c₂ * c₅)⁻¹ * (⟨b, hb⟩ : d.B₆) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψb, inv_mul_cancel]
  rw [hψk, Subgroup.mem_subgroupOf] at hn
  refine ⟨c₂, Subgroup.mem_inf.2 ⟨c₂.2, hc₂C⟩, c₅, Subgroup.mem_inf.2 ⟨c₅.2, hc₅C⟩,
    ((c₂ * c₅)⁻¹ * ⟨b, hb⟩ : d.B₆), hn, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem Hyp.s2a2_B₆_le_sup (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hLV : d.V ≤ CFSG.centerIn d.L₂) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
    (hP : d.P ≤ S) (hE : d.E ≤ S) (h1 : d.Sec39a1 S) : d.B₆ ≤ S ⊔ zpowers d.t := by
  intro b hb
  obtain ⟨c₂, hc₂, c₅, hc₅, n, hn, rfl⟩ := hd.s2a2_B₆_decomp₂ hGMS hb
  refine mul_mem (mul_mem ?_ ?_) ?_
  · obtain ⟨c, hc, m, hm, hcm⟩ := hd.s2a2_Y₂ hGMS hc₂
    rw [h1.inter₂] at hm
    rw [hcm]
    exact mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hm.1)
  · obtain ⟨c, hc, m, hm, hcm⟩ := hd.s2a2_Y₅ hGMS hc₅
    rw [h1.inter₅] at hm
    rw [hcm]
    exact mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left (hE hm.1))
  · obtain ⟨y, hy, a, ha, hna⟩ := hd.exists_of_mem_FB₃ hn
    have hyS : y ∈ S := hd.s2a2_F_le_S hGMS hLV hS hP hE h1 hy
    have haS : a ∈ S := hP (d.A₃_le_P ha)
    rcases hna with rfl | rfl
    · exact Subgroup.mem_sup_left (mul_mem hyS haS)
    · exact mul_mem (Subgroup.mem_sup_left hyS)
        (mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (Subgroup.mem_sup_left haS))

theorem Hyp.s2a2_normalizes_S (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {S : Subgroup G} (hSeq : S = d.E ⊔ (S ⊓ centralizer (d.I₂ : Set G))) (h1 : d.Sec39a1 S) :
    d.t ∈ normalizer (S : Set G) ∧ d.I ≤ normalizer (S : Set G) := by
  have hSeq' : S = d.E ⊔ (d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂) := by
    rw [h1.inter₂]; exact hSeq
  have hIC : d.I ≤ centralizer (d.I₂ : Set G) := fun i hi =>
    mem_centralizer_iff.2 fun j hj => d.I_comm (d.I₂_le_I hj) hi
  constructor
  · have htC := hd.t_mem_centralizer_I₂
    have := Common.mem_normalizer_sup (hd.t_mem_normalizer_E_caseB hGMS)
      (s2a2_mem_normalizer_inf (s2a2_mem_normalizer_inf hd.t_mem_normalizer_D
        (Subgroup.le_normalizer htC)) (s2a2_centralizer_I₂_le_normalizer_M₂ d htC))
    rwa [← hSeq'] at this
  · intro i hi
    have := Common.mem_normalizer_sup
      (hd.normalizer_B₄_le_normalizer_E hGMS (hd.I_le_normalizer_B₄ hi))
      (s2a2_mem_normalizer_inf (s2a2_mem_normalizer_inf (hd.s2a2_I_le_D hGMS hi)
        (Subgroup.le_normalizer (hIC hi))) (s2a2_centralizer_I₂_le_normalizer_M₂ d (hIC hi)))
    rwa [← hSeq'] at this

theorem Hyp.s2a2_D_le_S (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hLV : d.V ≤ CFSG.centerIn d.L₂) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
    (hP : d.P ≤ S) (hE : d.E ≤ S) (hSeq : S = d.E ⊔ (S ⊓ centralizer (d.I₂ : Set G)))
    (h1 : d.Sec39a1 S) : d.D ≤ S := by
  have hB : d.B₆ ≤ S ⊔ zpowers d.t := hd.s2a2_B₆_le_sup hGMS hLV hS hP hE h1
  obtain ⟨htS, hIS⟩ := hd.s2a2_normalizes_S hGMS hSeq h1
  show ⁅d.B₆, d.I₁⁆ ≤ S
  rw [Subgroup.commutator_le]
  intro b hb i hi
  obtain ⟨s, hs, c, hc, rfl⟩ := s2a2_exists_mul_of_mem_sup (N := S) (X := zpowers d.t)
    (Subgroup.zpowers_le.2 htS) (hB hb)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hiI : i ∈ d.I := d.I₁_le_I hi
  have hit : Commute i d.t :=
    (mem_centralizer_iff.1 (hd.s2a2_I_le_centralizer_t hiI) d.t (Set.mem_singleton _)).symm
  have hci : d.t ^ m * i * (d.t ^ m)⁻¹ = i := by
    have : d.t ^ m * i = i * d.t ^ m := ((hit.zpow_right m).eq).symm
    rw [this, mul_inv_cancel_right]
  rw [commutatorElement_def]
  have h2 : s * d.t ^ m * i * (s * d.t ^ m)⁻¹ * i⁻¹ = s * (i * s⁻¹ * i⁻¹) := by
    calc s * d.t ^ m * i * (s * d.t ^ m)⁻¹ * i⁻¹
        = s * (d.t ^ m * i * (d.t ^ m)⁻¹) * s⁻¹ * i⁻¹ := by group
      _ = s * i * s⁻¹ * i⁻¹ := by rw [hci]
      _ = s * (i * s⁻¹ * i⁻¹) := by group
  rw [h2]
  exact mul_mem hs ((mem_normalizer_iff.1 (hIS hiI) s⁻¹).1 (inv_mem hs) |> fun h => by
    simpa [mul_assoc] using h)

theorem s2a2_A₂_le_normalizer_Zp (d : Data G h) : d.A₂ ≤ normalizer (d.Zp : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer d.Zp_le_A₂).1 (normal_Zp_subgroupOf_A₂ d)

theorem Hyp.s2a2_E_centralizer (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {J : Subgroup G} (hJ : J ≤ d.I) (hA : d.A₂ ⊓ centralizer (J : Set G) = ⊥) :
    d.E ⊓ centralizer (J : Set G) = ⊥ := by
  obtain ⟨ψ, -, hψk, -, hψc⟩ := hd.exists_E_hom hGMS
  have hJodd : Odd (Nat.card J) := s2a2_odd_card_of_le_I hJ
  have hJt : ∀ j ∈ J, j ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G) := fun j hj => by
    rw [← hd.normalizer_B₄_inf_C]
    exact ⟨hd.I_le_normalizer_B₄ (hJ hj), hd.s2a2_I_le_centralizer_t (hJ hj)⟩
  have hJA₂ : J ≤ normalizer (d.A₂ : Set G) := fun j hj =>
    mem_normalizer_fintype fun a ha =>
      hd.conj_mem_A₂ (hd.I_le_H (hJ hj)).1 (hd.I_le_H (hJ hj)).2 ha
  have hJZ : J ≤ normalizer (d.Zp : Set G) := hJ.trans d.I_le_normalizer_Zp
  have hJE : J ≤ normalizer (d.E : Set G) := fun j hj =>
    hd.normalizer_B₄_le_normalizer_E hGMS (hd.I_le_normalizer_B₄ (hJ hj))
  have hcop : ∀ {a : G}, a ∈ d.A₂ → (∀ j ∈ J, a⁻¹ * (j * a * j⁻¹) ∈ d.Zp) → a ∈ d.Zp := by
    intro a ha hfix
    have hA₂p : IsPGroup 2 ↥d.A₂ := d.isPGroup_P.to_le d.A₂_le_P
    obtain ⟨c, hc, n, hn, hcn⟩ := s2a2_fix (M := d.A₂) (N := d.Zp) (J := J) hA₂p d.Zp_le_A₂
      (s2a2_A₂_le_normalizer_Zp d) hJA₂ hJZ hJodd ha hfix
    have hc1 : c = 1 := by
      have : c ∈ d.A₂ ⊓ centralizer (J : Set G) := hc
      rw [hA] at this
      exact Subgroup.mem_bot.1 this
    rw [hc1, one_mul] at hcn
    exact hcn ▸ hn
  refine le_bot_iff.1 fun x hx => ?_
  obtain ⟨hxE, hxC⟩ := hx
  have hxψ : ψ ⟨x, hxE⟩ = 1 := by
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (ψ ⟨x, hxE⟩)
    have hfix : ∀ j ∈ J, (a : G)⁻¹ * (j * (a : G) * j⁻¹) ∈ d.Zp := by
      intro j hj
      have hjE : j * x * j⁻¹ ∈ d.E := (mem_normalizer_iff.1 (hJE hj) x).1 hxE
      have hjA : j * (a : G) * j⁻¹ ∈ d.A₂ := (mem_normalizer_iff.1 (hJA₂ hj) a).1 a.2
      have hjx : j * x * j⁻¹ = x := by
        rw [mem_centralizer_iff.1 hxC j hj, mul_inv_cancel_right]
      have h1 := hψc j (hJt j hj) ⟨x, hxE⟩ a hjE hjA ha.symm
      have h2 : (⟨j * x * j⁻¹, hjE⟩ : d.E) = ⟨x, hxE⟩ := Subtype.ext hjx
      rw [h2, ← ha] at h1
      have h3 := QuotientGroup.eq.1 h1
      rw [Subgroup.mem_subgroupOf] at h3
      exact h3
    have haZ := hcop a.2 hfix
    rw [← ha]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 haZ)
  have hxVA : x ∈ d.V ⊔ d.A₂ := by
    have : (⟨x, hxE⟩ : d.E) ∈ ψ.ker := hxψ
    rw [hψk, Subgroup.mem_subgroupOf] at this
    exact this
  obtain ⟨v, hv, a, ha, rfl⟩ := hd.exists_mul_of_mem_VA hxVA
  have haZ : a ∈ d.Zp := by
    refine hcop ha fun j hj => ?_
    have hjv : j * v * j⁻¹ ∈ d.V := (mem_normalizer_iff.1 (hJ.trans hd.I_le_normalizer_V hj) v).1 hv
    have hja : j * a * j⁻¹ ∈ d.A₂ := (mem_normalizer_iff.1 (hJA₂ hj) a).1 ha
    have hjx : j * (v * a) * j⁻¹ = v * a := by
      rw [mem_centralizer_iff.1 hxC j hj, mul_inv_cancel_right]
    have h1 : j * a * j⁻¹ = (j * v * j⁻¹)⁻¹ * (v * a) := by rw [← hjx]; group
    have hcomm : ((j * v * j⁻¹)⁻¹ * v) * a = a * ((j * v * j⁻¹)⁻¹ * v) :=
      hd.V_comm_A₂ (mul_mem (inv_mem hjv) hv) ha
    have h2 : a⁻¹ * (j * a * j⁻¹) = (j * v * j⁻¹)⁻¹ * v := by
      calc a⁻¹ * (j * a * j⁻¹) = a⁻¹ * (((j * v * j⁻¹)⁻¹ * v) * a) := by rw [h1]; group
        _ = a⁻¹ * (a * ((j * v * j⁻¹)⁻¹ * v)) := by rw [hcomm]
        _ = (j * v * j⁻¹)⁻¹ * v := by group
    have hmem : a⁻¹ * (j * a * j⁻¹) ∈ d.V ⊓ d.A₂ :=
      Subgroup.mem_inf.2 ⟨by rw [h2]; exact mul_mem (inv_mem hjv) hv,
        mul_mem (inv_mem ha) hja⟩
    rwa [hd.V_inf_A₂] at hmem
  have hxV : v * a ∈ d.V := mul_mem hv (hd.Zp_le_V haZ)
  have hcr : (v * a)⁻¹ * d.t * (v * a) * d.t = 1 := by
    have hcrZ : (v * a)⁻¹ * d.t * (v * a) * d.t ∈ d.Zp := hd.cr_mem (hd.V_le_B₄ hxV)
    have hcrC : (v * a)⁻¹ * d.t * (v * a) * d.t ∈ centralizer (J : Set G) := by
      rw [mem_centralizer_iff]
      intro j hj
      have h1 : Commute j (v * a) := mem_centralizer_iff.1 hxC j hj
      have h2 : Commute j d.t :=
        (mem_centralizer_iff.1 (hd.s2a2_I_le_centralizer_t (hJ hj)) d.t (Set.mem_singleton _)).symm
      exact (((h1.inv_right.mul_right h2).mul_right h1).mul_right h2)
    have : (v * a)⁻¹ * d.t * (v * a) * d.t ∈ d.A₂ ⊓ centralizer (J : Set G) :=
      Subgroup.mem_inf.2 ⟨d.Zp_le_A₂ hcrZ, hcrC⟩
    rw [hA] at this
    exact Subgroup.mem_bot.1 this
  have hxt : v * a ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_iff]
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    have h1 : (v * a)⁻¹ * d.t * (v * a) * d.t = 1 := hcr
    have h2 : d.t * (v * a) * d.t = v * a := by
      have := congrArg (fun z => (v * a) * z) h1
      simpa [mul_assoc] using this
    calc d.t * (v * a) = d.t * (v * a) * d.t * d.t := by rw [mul_assoc _ d.t d.t, hd.t_mul_t, mul_one]
      _ = (v * a) * d.t := by rw [h2]
  have hxZ : v * a ∈ d.Zp := by
    rw [← hd.V_inf_centralizer_t]
    exact Subgroup.mem_inf.2 ⟨hxV, hxt⟩
  have : v * a ∈ d.A₂ ⊓ centralizer (J : Set G) := Subgroup.mem_inf.2 ⟨d.Zp_le_A₂ hxZ, hxC⟩
  rw [hA] at this
  exact this

theorem Hyp.s2a2_t_not_mem_S (hd : d.Hyp) (hLV : d.V ≤ CFSG.centerIn d.L₂) {S : Subgroup G}
    (hS : IsSylowOf 2 S d.L₂) : d.t ∉ S := fun ht => by
  obtain ⟨w, hw, hne⟩ := hd.exists_V_not_comm_t
  exact hne (s2a2_S_comm_V hLV hS ht hw)

theorem Hyp.s2a2_S_I₅_le_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hLV : d.V ≤ CFSG.centerIn d.L₂) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
    (hE : d.E ≤ S) (hDS : d.D ≤ S) (hSED : S = d.E ⊔ d.D) (h1 : d.Sec39a1 S) :
    S ⊓ centralizer (d.I₅ : Set G) ≤ d.E ⊓ centralizer (d.I₅ : Set G) := by
  intro x hx
  have hSN : S ≤ normalizer (d.E : Set G) := hS.le.trans d.L₂_le_normalizer_E
  have hIE : d.I ≤ normalizer (d.E : Set G) := fun i hi =>
    hd.normalizer_B₄_le_normalizer_E hGMS (hd.I_le_normalizer_B₄ hi)
  obtain ⟨e, he, δ, hδ, rfl⟩ := s2a2_exists_mul_of_mem_sup (N := d.E) (X := d.D)
    (fun y hy => hSN (hDS hy)) (hSED ▸ hx.1)
  refine Subgroup.mem_inf.2 ⟨?_, hx.2⟩
  have hfix : ∀ j ∈ d.I₅, δ⁻¹ * (j * δ * j⁻¹) ∈ d.E ⊓ d.D := by
    intro j hj
    have hjI : j ∈ d.I := d.I₅_le_I hj
    have hjx : j * (e * δ) * j⁻¹ = e * δ := by
      rw [mem_centralizer_iff.1 hx.2 j hj, mul_inv_cancel_right]
    have hje : j * e * j⁻¹ ∈ d.E := (mem_normalizer_iff.1 (hIE hjI) e).1 he
    have h2 : j * δ * j⁻¹ = (j * e * j⁻¹)⁻¹ * (e * δ) := by rw [← hjx]; group
    have hz : (j * e * j⁻¹)⁻¹ * e ∈ d.E := mul_mem (inv_mem hje) he
    have h3 : δ⁻¹ * ((j * e * j⁻¹)⁻¹ * e) * δ ∈ d.E := by
      have := (mem_normalizer_iff.1 (hSN (hDS (inv_mem hδ))) _).1 hz
      simpa using this
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have : δ⁻¹ * (j * δ * j⁻¹) = δ⁻¹ * ((j * e * j⁻¹)⁻¹ * e) * δ := by rw [h2]; group
      rw [this]; exact h3
    · exact mul_mem (inv_mem hδ)
        ((mem_normalizer_iff.1 (hd.s2a2_I_le_D hGMS hjI) δ).1 hδ)
  have hD2 : IsPGroup 2 ↥d.D := d.isPGroup_B₆.to_le (hd.s2a2_D_le_B₆ hGMS)
  obtain ⟨c, hc, n, hn, hcn⟩ := s2a2_fix (M := d.D) (N := d.E ⊓ d.D) (J := d.I₅) hD2
    inf_le_right
    (fun y hy => s2a2_mem_normalizer_inf (hSN (hDS hy)) (Subgroup.le_normalizer hy))
    (fun j hj => hd.s2a2_I_le_D hGMS (d.I₅_le_I hj))
    (fun j hj => s2a2_mem_normalizer_inf (hIE (d.I₅_le_I hj)) (hd.s2a2_I_le_D hGMS (d.I₅_le_I hj)))
    (s2a2_odd_card_of_le_I d.I₅_le_I) hδ hfix
  obtain ⟨c', hc', m, hm, hcm⟩ := hd.s2a2_Y₅ hGMS (y := c)
    (Subgroup.mem_inf.2 ⟨hd.s2a2_D_le_B₆ hGMS hc.1, hc.2⟩)
  rw [h1.inter₅] at hm
  have hcE : c ∈ d.E := by
    rcases hd.s2a2_zpowers_t hc' with rfl | rfl
    · rw [hcm, one_mul]; exact hm.1
    · exfalso
      apply hd.s2a2_t_not_mem_S hLV hS
      have : d.t = c * m⁻¹ := by rw [hcm]; group
      rw [this]
      exact mul_mem (hDS hc.1) (inv_mem (hE hm.1))
  rw [hcn]
  exact mul_mem he (mul_mem hcE hn.1)

theorem Hyp.s2a2_F_le_D (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ≤ d.D := by
  intro f hf
  have hFB : d.F ≤ d.B₆ := le_sup_left.trans (hd.FB₃_le_B₆ hGMS)
  obtain ⟨c, hc, n, hn, hcn⟩ := s2a2_fix (M := d.F) (N := d.F ⊓ d.D) (J := d.I₁) hd.isPGroup_F
    inf_le_left
    (fun g hg => s2a2_mem_normalizer_inf (Subgroup.le_normalizer hg)
      (s2a2_B₆_le_normalizer_D d (hFB hg)))
    (fun i hi => hd.I_le_normalizer_F hGMS (d.I₁_le_I hi))
    (fun i hi => s2a2_mem_normalizer_inf (hd.I_le_normalizer_F hGMS (d.I₁_le_I hi))
      (hd.s2a2_I_le_D hGMS (d.I₁_le_I hi)))
    (s2a2_odd_card_of_le_I d.I₁_le_I) hf
    (fun j hj => Subgroup.mem_inf.2
      ⟨mul_mem (inv_mem hf) ((mem_normalizer_iff.1 (hd.I_le_normalizer_F hGMS (d.I₁_le_I hj)) f).1 hf),
        hd.s2a2_comm_mem_D hGMS (hFB hf) (d.I₁_le_I hj)⟩)
  have hc1 : c = 1 := by
    have hcB : c ∈ zpowers d.t := hd.s2a2_centralizer_B₆ hGMS d.I₁_le_I hd.s2a2_hA₁
      (Subgroup.mem_inf.2 ⟨hFB hc.1, hc.2⟩)
    rcases hd.s2a2_zpowers_t hcB with h | h
    · exact h
    · exact absurd (Subgroup.mem_sup_left (h ▸ hc.1)) (hd.t_not_mem_FA₃ hGMS)
  rw [hcn, hc1, one_mul]
  exact hn.2

theorem Hyp.s2a2_D_eq (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hLV : d.V ≤ CFSG.centerIn d.L₂) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
    (hP : d.P ≤ S) (hE : d.E ≤ S) (hDS : d.D ≤ S)
    (hSeq : S = d.E ⊔ (S ⊓ centralizer (d.I₂ : Set G))) (h1 : d.Sec39a1 S)
    (hI₅ : S ⊓ centralizer (d.I₅ : Set G) ≤ d.E ⊓ centralizer (d.I₅ : Set G)) :
    d.D = d.F ⊔ (S ⊓ centralizer (d.I₂ : Set G)) ⊔ (S ⊓ centralizer (d.I₅ : Set G)) := by
  set R : Subgroup G := S ⊓ centralizer (d.I₂ : Set G) with hR
  set R₅ : Subgroup G := S ⊓ centralizer (d.I₅ : Set G) with hR₅
  have hFS : d.F ≤ S := hd.s2a2_F_le_S hGMS hLV hS hP hE h1
  have hRD : R ≤ d.D := fun x hx => by
    have hx' := hx
    rw [hR, ← h1.inter₂] at hx'
    exact hx'.1.1
  have hR₅D : R₅ ≤ d.D := fun x hx => by
    have hx' := hI₅ hx
    rw [← h1.inter₅] at hx'
    exact hx'.1.1
  have hH₀S : d.F ⊔ R ⊔ R₅ ≤ S := sup_le (sup_le hFS inf_le_left) inf_le_left
  refine le_antisymm ?_ (sup_le (sup_le (hd.s2a2_F_le_D hGMS) hRD) hR₅D)
  obtain ⟨htS, -⟩ := hd.s2a2_normalizes_S hGMS hSeq h1
  have htIC : ∀ J : Subgroup G, J ≤ d.I → d.t ∈ centralizer (J : Set G) := fun J hJ =>
    mem_centralizer_iff.2 fun j hj =>
      (mem_centralizer_iff.1 (hd.s2a2_I_le_centralizer_t (hJ hj)) d.t (Set.mem_singleton _)).symm
  have htN : d.t ∈ normalizer ((d.F ⊔ R ⊔ R₅ : Subgroup G) : Set G) :=
    Common.mem_normalizer_sup (Common.mem_normalizer_sup hd.t_mem_normalizer_F
      (s2a2_mem_normalizer_inf htS (Subgroup.le_normalizer (htIC d.I₂ d.I₂_le_I))))
      (s2a2_mem_normalizer_inf htS (Subgroup.le_normalizer (htIC d.I₅ d.I₅_le_I)))
  have hA₃H : d.A₃ ≤ d.F ⊔ R ⊔ R₅ := by
    intro a ha
    obtain ⟨a₁, ha₁, a₂, ha₂, a₅, ha₅, rfl⟩ := hd.s2a2_A₃_decomp hGMS ha
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left (hd.A₁_le_F ha₁)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hP ha₂.1, ha₂.2⟩)))) 
      (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hP ha₅.1, ha₅.2⟩))
  have hB₆H : d.B₆ ≤ (d.F ⊔ R ⊔ R₅) ⊔ zpowers d.t := by
    intro b hb
    obtain ⟨c₂, hc₂, c₅, hc₅, n, hn, rfl⟩ := hd.s2a2_B₆_decomp₂ hGMS hb
    refine mul_mem (mul_mem ?_ ?_) ?_
    · obtain ⟨c, hc, m, hm, hcm⟩ := hd.s2a2_Y₂ hGMS hc₂
      rw [h1.inter₂] at hm
      rw [hcm]
      exact mul_mem (Subgroup.mem_sup_right hc)
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hm)))
    · obtain ⟨c, hc, m, hm, hcm⟩ := hd.s2a2_Y₅ hGMS hc₅
      rw [h1.inter₅] at hm
      rw [hcm]
      exact mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.mem_inf.2 ⟨hE hm.1, hm.2⟩)))
    · obtain ⟨y, hy, a, ha, hna⟩ := hd.exists_of_mem_FB₃ hn
      have hyH : y ∈ d.F ⊔ R ⊔ R₅ := Subgroup.mem_sup_left (Subgroup.mem_sup_left hy)
      have haH : a ∈ d.F ⊔ R ⊔ R₅ := hA₃H ha
      rcases hna with rfl | rfl
      · exact Subgroup.mem_sup_left (mul_mem hyH haH)
      · exact mul_mem (Subgroup.mem_sup_left hyH)
          (mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (Subgroup.mem_sup_left haH))
  intro x hx
  obtain ⟨n, hn, c, hc, hxc⟩ := s2a2_exists_mul_of_mem_sup (N := d.F ⊔ R ⊔ R₅) (X := zpowers d.t)
    (Subgroup.zpowers_le.2 htN) (hB₆H (hd.s2a2_D_le_B₆ hGMS hx))
  rcases hd.s2a2_zpowers_t hc with rfl | rfl
  · rw [hxc, mul_one]; exact hn
  · exfalso
    apply hd.s2a2_t_not_mem_S hLV hS
    have : d.t = n⁻¹ * x := by rw [hxc]; group
    rw [this]
    exact mul_mem (inv_mem (hH₀S hn)) (hDS hx)

theorem sec39a_of_hyp (hp : d.CaseHyp) (k8 : d.Know8) (S : Subgroup G)
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (h1 : d.Sec39a1 S) : d.Sec39a S := by
  have hGMS := hp.gms
  have hd := hp.hyp
  obtain ⟨hL, hLV, -, -, -⟩ := k8.s8
  obtain ⟨hE, -, hSeq⟩ := hd.s2a2_S_eq hGMS hL hS h1.sylow₂
  have hDS : d.D ≤ S := hd.s2a2_D_le_S hGMS hLV hS hP hE hSeq h1
  have hRD : S ⊓ centralizer (d.I₂ : Set G) ≤ d.D := fun x hx => by
    have hx' := hx
    rw [← h1.inter₂] at hx'
    exact hx'.1.1
  have hSED : S = d.E ⊔ d.D := by
    refine le_antisymm ?_ (sup_le hE hDS)
    calc S = d.E ⊔ (S ⊓ centralizer (d.I₂ : Set G)) := hSeq
      _ ≤ d.E ⊔ d.D := sup_le_sup_left hRD _
  have hI₅ := hd.s2a2_S_I₅_le_E hGMS hLV hS hE hDS hSED h1
  have hE₂ : d.E ⊓ (S ⊓ centralizer (d.I₂ : Set G)) = ⊥ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨-, hA⟩, -⟩ := d.sec2_1_two hd.two_le
    have hA₂ : d.A₂ ⊓ centralizer (d.I₂ : Set G) = ⊥ := by
      refine le_bot_iff.1 fun x hx => ?_
      rw [← hA]
      exact Subgroup.mem_inf.2 ⟨hx.1, Subgroup.mem_inf.2 ⟨d.A₂_le_P hx.1, hx.2⟩⟩
    refine le_bot_iff.1 fun x hx => ?_
    have := hd.s2a2_E_centralizer hGMS d.I₂_le_I hA₂
    rw [← this]
    exact Subgroup.mem_inf.2 ⟨hx.1, hx.2.2⟩
  refine ⟨hSED, ?_, ?_, h1.sylow₂, ?_, ?_, hSeq, hE₂,
    hd.s2a2_D_eq hGMS hLV hS hP hE hDS hSeq h1 hI₅⟩
  · refine le_antisymm (inf_le_inf_right _ hDS) fun x hx => ?_
    have hx' := hx
    rw [← h1.inter₂] at hx'
    exact Subgroup.mem_inf.2 ⟨hx'.1.1, hx'.1.2⟩
  · refine le_antisymm (inf_le_inf_right _ hDS) fun x hx => ?_
    have hxE := hI₅ hx
    rw [← h1.inter₅] at hxE
    exact Subgroup.mem_inf.2 ⟨hxE.1.1, hxE.1.2⟩
  · have : S ⊓ centralizer (d.I₅ : Set G) = d.E ⊓ centralizer (d.I₅ : Set G) :=
      le_antisymm hI₅ (inf_le_inf_right _ hE)
    rw [this]
    exact h1.sylowE₅
  · refine le_antisymm (fun b hb => ?_) (sup_le (hd.s2a2_D_le_B₆ hGMS) ?_)
    · obtain ⟨c, hc, n, hn, rfl⟩ := hd.s2a2_B₆_decomp hGMS hb
      exact mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hn)
    · exact Subgroup.zpowers_le.2 (hd.FB₃_le_B₆ hGMS
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))))

end Data

namespace CaseBParts

theorem sec39a : Sec39aStatement :=
  fun _ _ _ _ _ _ _ _ hp k8 S hS hP h1 => Data.sec39a_of_hyp hp k8 S hS hP h1

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
