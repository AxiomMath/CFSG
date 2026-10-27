module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageTransportQuot
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageNextStep
public import CFSG.LocalAnalysis.SeitzReduction.RankOneOddStabilizerKProper

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relMk_comm {N W : Subgroup G} [(W.subgroupOf N).Normal] (x r : N) :
    QuotientGroup.mk' (W.subgroupOf N) x * QuotientGroup.mk' (W.subgroupOf N) r *
        (QuotientGroup.mk' (W.subgroupOf N) x)⁻¹ * (QuotientGroup.mk' (W.subgroupOf N) r)⁻¹ =
      QuotientGroup.mk' (W.subgroupOf N) (x * r * x⁻¹ * r⁻¹) := by
  simp only [map_mul, map_inv]

theorem RelSmallRootStage.step {N W R X U P : Subgroup G} {n : ℕ} [(W.subgroupOf N).Normal]
    (h : RelSmallRootStage N W R X U P n)
    (hP : ¬ ∃ S : Sylow 2 (↥N ⧸ W.subgroupOf N), (S : Subgroup _) = relImg N W P)
    (hE : GMSHasRegularNormal (relImg N W U) (relImg N W R)) :
    ∃ Up : Subgroup G, U ≤ Up ∧ Up ≤ N ∧ Up ≤ normalizer (U : Set G) ∧
      (∀ x ∈ Up, x * x ∈ U) ∧ (∀ x ∈ Up, ∀ y ∈ Up, x * y * x⁻¹ * y⁻¹ ∈ U) ∧
      (∀ r ∈ R, r ∉ W → ∀ x ∈ Up, x * r * x⁻¹ * r⁻¹ ∈ U) ∧
      (∀ r ∈ R, r ∉ W → ∀ x ∈ Up, x * r * x⁻¹ * r⁻¹ ∈ W → x ∈ U) ∧
      (∀ r ∈ R, r ∉ W → ∀ u ∈ U, ∃ x ∈ Up, u⁻¹ * (x * r * x⁻¹ * r⁻¹) ∈ W) ∧
      R ≤ normalizer (Up : Set G) ∧ P ≤ normalizer (Up : Set G) ∧
      X ⊓ normalizer (U : Set G) ≤ normalizer (Up : Set G) ∧
      ∀ N' : Subgroup G, N' = N ⊓ normalizer (U : Set G) →
        RelSmallRootStage N' U (U ⊔ R) (Up ⊔ (X ⊓ normalizer (U : Set G))) Up (Up ⊔ P) n := by
  obtain ⟨-, hWR, hWX, hWU, hWP, hRN, hXN, hUN, hPN, hS⟩ := h
  have hS := @hS inferInstance
  obtain ⟨-, -, -, -, -, -, -, hsq, hcomm, Up', h1, h2, -, h4, h5, h6, hc, h7, h8, hnext, -⟩ :=
    smallRoot_step hS hP hE
  obtain ⟨-, -, -, -, -, -, ⟨hPRb, -, hUPb, hRPb, hPUb, -, -, hVPb⟩⟩ := hS.1
  have hWN : W ≤ N := hWU.trans hUN
  have hUp' : relImg N W (relPre N W Up') = Up' := relImg_relPre Up'
  have hWUp : W ≤ relPre N W Up' := le_relPre hWN Up'
  have hUpN : relPre N W Up' ≤ N := relPre_le Up'
  have hW'U : Up' ≤ normalizer ((relImg N W U : Subgroup (↥N ⧸ W.subgroupOf N)) :
      Set (↥N ⧸ W.subgroupOf N)) :=
    h2.trans (inf_le_right.trans (centralizer_le_normalizer _))
  have hPV : relImg N W P ≤ normalizer ((relImg N W U ⊔ relImg N W R :
      Subgroup (↥N ⧸ W.subgroupOf N)) : Set (↥N ⧸ W.subgroupOf N)) :=
    (normal_subgroupOf_iff_le_normalizer (sup_le hUPb hRPb)).mp hVPb
  have hPY : relImg N W P ≤ normalizer ((relImg N W U ⊔ relImg N W R :
      Subgroup (↥N ⧸ W.subgroupOf N)) : Set (↥N ⧸ W.subgroupOf N)) ⊓
      normalizer ((relImg N W R : Subgroup (↥N ⧸ W.subgroupOf N)) :
        Set (↥N ⧸ W.subgroupOf N)) := le_inf hPV hPRb
  have hPUp : relImg N W P ≤ normalizer ((Up' : Subgroup (↥N ⧸ W.subgroupOf N)) :
      Set (↥N ⧸ W.subgroupOf N)) := hPY.trans h5
  have hr : ∀ r ∈ R, r ∉ W → ∃ r' : N, (r' : G) = r ∧
      QuotientGroup.mk' (W.subgroupOf N) r' ∈ relImg N W R ∧
      QuotientGroup.mk' (W.subgroupOf N) r' ≠ 1 := fun r hrR hrW =>
    ⟨⟨r, hRN hrR⟩, rfl, relMk_mem_relImg _ hrR, fun h1 => hrW ((relMk_eq_one_iff _).mp h1)⟩
  have hUpmem : ∀ x ∈ relPre N W Up', ∃ x' : N, (x' : G) = x ∧
      QuotientGroup.mk' (W.subgroupOf N) x' ∈ Up' := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
    exact ⟨x', rfl, hx'⟩
  have hUUp : U ≤ relPre N W Up' := fun u hu =>
    (mem_relPre_iff Up' ⟨u, hUN hu⟩).mpr (h1 (relMk_mem_relImg _ hu))
  have hUpNU : relPre N W Up' ≤ normalizer (U : Set G) := fun x hx => by
    obtain ⟨x', rfl, hx'⟩ := hUpmem x hx
    exact (relMk_mem_normalizer_iff hWU hUN x').mp (hW'U hx')
  have hRU : R ≤ normalizer (U : Set G) := fun r hr =>
    (relMk_mem_normalizer_iff hWU hUN ⟨r, hRN hr⟩).mp (hPUb (hRPb (relMk_mem_relImg _ hr)))
  have hPU : P ≤ normalizer (U : Set G) := fun y hy =>
    (relMk_mem_normalizer_iff hWU hUN ⟨y, hPN hy⟩).mp (hPUb (relMk_mem_relImg _ hy))
  have hnorm : ∀ y : N, QuotientGroup.mk' (W.subgroupOf N) y ∈
      normalizer ((Up' : Subgroup (↥N ⧸ W.subgroupOf N)) : Set (↥N ⧸ W.subgroupOf N)) →
      (y : G) ∈ normalizer ((relPre N W Up' : Subgroup G) : Set G) := fun y hy =>
    (relMk_mem_normalizer_iff hWUp hUpN y).mp (by rw [hUp']; exact hy)
  refine ⟨relPre N W Up', hUUp, hUpN, hUpNU, fun x hx => ?_, fun x hx y hy => ?_,
    fun r hrR hrW x hx => ?_, fun r hrR hrW x hx hxr => ?_, fun r hrR hrW u hu => ?_,
    fun r hrR => hnorm ⟨r, hRN hrR⟩ (hPUp (hRPb (relMk_mem_relImg _ hrR))),
    fun y hy => hnorm ⟨y, hPN hy⟩ (hPUp (relMk_mem_relImg _ hy)),
    fun y hy => hnorm ⟨y, hXN (mem_inf.mp hy).1⟩ (h6 (mem_inf.mpr
      ⟨relMk_mem_relImg _ (mem_inf.mp hy).1,
        (relMk_mem_normalizer_iff hWU hUN _).mpr (mem_inf.mp hy).2⟩)),
    fun N' hN' => ?_⟩
  ·
    obtain ⟨x', rfl, hx'⟩ := hUpmem x hx
    have h1 := hsq _ (h2 hx')
    rw [← map_mul, relMk_mem_relImg_iff hWU] at h1
    exact h1
  ·
    obtain ⟨x', rfl, hx'⟩ := hUpmem x hx
    obtain ⟨y', rfl, hy'⟩ := hUpmem y hy
    have h1 := hcomm _ (h2 hx') _ (h2 hy')
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, relMk_mem_relImg_iff hWU] at h1
    exact h1
  ·
    obtain ⟨r', rfl, hr'R, hr'1⟩ := hr r hrR hrW
    obtain ⟨x', rfl, hx'⟩ := hUpmem x hx
    have h1 := hc _ hr'R hr'1 _ hx'
    rw [relMk_comm, relMk_mem_relImg_iff hWU] at h1
    exact h1
  ·
    obtain ⟨r', rfl, hr'R, hr'1⟩ := hr r hrR hrW
    obtain ⟨x', rfl, hx'⟩ := hUpmem x hx
    have h1 := h7 _ hr'R hr'1 _ hx' (by
      rw [relMk_comm, relMk_eq_one_iff]
      exact hxr)
    exact (relMk_mem_relImg_iff hWU x').mp h1
  ·
    obtain ⟨r', rfl, hr'R, hr'1⟩ := hr r hrR hrW
    obtain ⟨y, hy, hyu⟩ := h8 _ hr'R hr'1 _ (relMk_mem_relImg ⟨u, hUN hu⟩ hu)
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (W.subgroupOf N) y
    refine ⟨x', (mem_relPre_iff Up' x').mpr hy, ?_⟩
    rw [relMk_comm] at hyu
    have h1 : QuotientGroup.mk' (W.subgroupOf N) ((⟨u, hUN hu⟩ : N)⁻¹ * (x' * r' * x'⁻¹ * r'⁻¹)) =
        1 := by
      rw [map_mul, hyu, map_inv, inv_mul_cancel]
    exact (relMk_eq_one_iff _).mp h1
  ·
    have hRbU : relImg N W R ≤ normalizer ((relImg N W U : Subgroup (↥N ⧸ W.subgroupOf N)) :
        Set (↥N ⧸ W.subgroupOf N)) := hRPb.trans hPUb
    refine relSmallRootStage_of_stageQuot hWU hUN hN' le_sup_left (hUUp.trans le_sup_left) hUUp
      (hUUp.trans le_sup_left)
      (by rw [hN']; exact le_inf (sup_le hUN hRN) (sup_le le_normalizer hRU))
      (by rw [hN']; exact le_inf (sup_le hUpN (inf_le_left.trans hXN)) (sup_le hUpNU inf_le_right))
      (by rw [hN']; exact le_inf hUpN hUpNU)
      (by rw [hN']; exact le_inf (sup_le hUpN hPN) (sup_le hUpNU hPU)) ?_
    rw [relImg_sup hUN hRN, stageImg_sup_left hRbU, relImg_sup hUpN (inf_le_left.trans hXN),
      relImg_sup hUpN hPN, hUp', relImg_inf hWX (hWU.trans le_normalizer),
      ← normalizer_relImg hWU hUN]
    rw [← h4, sup_assoc, sup_eq_right.mpr hRPb] at hnext
    exact hnext

theorem catalog_of_relImg [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {N W V : Subgroup G}
    [(W.subgroupOf N).Normal] (hWV : W ≤ V) (hVN : V ≤ N) (hV2 : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    {V' R' : Subgroup (↥N ⧸ W.subgroupOf N)} (hV' : V' = relImg N W V) :
    ∀ S : Subgroup (Equiv.Perm (gmsRootConjugates V' R')),
      S ≤ (gmsRootConjugateAction V' R').range →
      (S.subgroupOf (gmsRootConjugateAction V' R').range).Normal → IsSimpleGroup S →
      (∃ a b : S, a * b ≠ b * a) → CFSG.Blueprint.Catalog S := by
  subst hV'
  intro S hS _ hs hnabS
  have hY : N ⊓ normalizer (V : Set G) ≠ ⊤ := by
    intro htop
    have hVtop : normalizer (V : Set G) = ⊤ := top_unique (by rw [← htop]; exact inf_le_right)
    have hVn : V.Normal := normalizer_eq_top_iff.mp hVtop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V with h | h
    · exact hV1 h
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hG2 : IsPGroup 2 G := by
        rw [h] at hV2
        exact hV2.of_equiv Subgroup.topEquiv
      have hZ : Subgroup.center G ≠ ⊥ :=
        (Subgroup.nontrivial_iff_ne_bot _).mp hG2.center_nontrivial
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h' | h'
      · exact hZ h'
      · obtain ⟨a, b, hab⟩ := hnab
        have hb : b ∈ Subgroup.center G := by rw [h']; exact mem_top b
        exact hab (Subgroup.mem_center_iff.mp hb a)
  let ψ : ↥(N ⊓ normalizer (V : Set G)) →*
      ↥(normalizer ((relImg N W V : Subgroup (↥N ⧸ W.subgroupOf N)) :
        Set (↥N ⧸ W.subgroupOf N))) :=
    ((QuotientGroup.mk' (W.subgroupOf N)).comp
      (inclusion (inf_le_left : N ⊓ normalizer (V : Set G) ≤ N))).codRestrict _ fun y =>
        (relMk_mem_normalizer_iff hWV hVN _).mpr (mem_inf.mp y.2).2
  have hψ : Function.Surjective ψ := fun z => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (W.subgroupOf N) (z : _)
    have hxN : (x : G) ∈ normalizer (V : Set G) :=
      (relMk_mem_normalizer_iff hWV hVN x).mp (hx ▸ z.2)
    exact ⟨⟨x, mem_inf.mpr ⟨x.2, hxN⟩⟩, Subtype.ext hx⟩
  have hrange : ((gmsRootConjugateAction (relImg N W V) R').comp ψ).range =
      (gmsRootConjugateAction (relImg N W V) R').range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ, ← MonoidHom.range_eq_map]
  exact catalog_of_le_range_of_kProper hK hY _ (hrange ▸ hS) hs hnabS

end CFSG.SeitzReduction.RankOne
