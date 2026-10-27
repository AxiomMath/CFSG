module

public import CFSG.LocalAnalysis.GH72.DDAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralNormalSubgroup
public import CFSG.LocalAnalysis.GH72.DDSubgroups

public section

namespace CFSG.GH72

open Subgroup DihedralGroup
open scoped commutatorElement
open CFSG.CGT.Foote81L6 (card_sup_of_le_normalizer le_normalizer_of_comm
  mem_sup_iff_of_le_normalizer)
open CFSG.CGT.Foote81L6.TStruct (IsFourIn isElemAbelian_two_iff comm_of_mul_self eq_dihFour
  sr_mem_dihFour mul_inv_mem_of_card_eq_two_mul)

variable {G : Type*} [Group G]

theorem IsDih.card_inf_normalizer_le {D T V : Subgroup G} (hD : IsDih D) (hTD : T ≤ D)
    (hV : IsFourIn D V) (hVT : V ≤ T) :
    Nat.card ↥(D ⊓ normalizer (T : Set G)) ≤ 2 * Nat.card T := by
  have hTN : T ≤ D ⊓ normalizer (T : Set G) := le_inf hTD le_normalizer
  obtain ⟨m, hm, ⟨e⟩⟩ := hD.of_le inf_le_left hV (hVT.trans hTN)
  have hnormal : (T.subgroupOf (D ⊓ normalizer (T : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hTN).2 inf_le_right
  have hnc : ¬ IsCyclic ↥(T.subgroupOf (D ⊓ normalizer (T : Set G))) := by
    intro hc
    haveI : IsCyclic ↥T := (subgroupOfEquivOfLe hTN).isCyclic.1 hc
    have hVc : IsCyclic ↥V := Subgroup.isCyclic_of_le hVT
    haveI := isKleinFour_of_isFourIn hV
    exact IsKleinFour.not_isCyclic hVc
  have hidx := CFSG.GorensteinWalter.normal_noncyclic_subgroup_dihedral_of_mulEquiv_index_le_two
    hm e _ hnormal hnc
  have h := relIndex_mul_card T (D ⊓ normalizer (T : Set G))
  rw [inf_of_le_left hTN] at h
  rw [← h]
  exact Nat.mul_le_mul_right _ hidx

theorem IsDih.exists_mem_four_mul_self {D V : Subgroup G} (hD : IsDih D) (hV : IsFourIn D V) :
    ∃ s ∈ V, ∀ t ∈ D, t * t = 1 ∨ t * s * (t * s) = 1 := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hD
  obtain ⟨hVD, hV2, hV4⟩ := hV
  have hV' : IsFourIn D V := ⟨hVD, hV2, hV4⟩
  obtain ⟨i, hi⟩ := CFSG.CGT.Foote81L6.TStruct.exists_eq_liftSub_dihFour e hk hV'
  refine ⟨(e.symm (sr i) : G), ?_, fun t ht => ?_⟩
  · rw [hi]
    exact (CFSG.CGT.Foote81L6.TStruct.symm_mem_liftSub e).2 (sr_mem_dihFour i)
  · cases h : e ⟨t, ht⟩ with
    | r j =>
      right
      have h1 : e (⟨t, ht⟩ * e.symm (sr i)) = sr (i - j) := by
        rw [map_mul, h, MulEquiv.apply_symm_apply, r_mul_sr]
      have h2 : (⟨t, ht⟩ * e.symm (sr i)) * (⟨t, ht⟩ * e.symm (sr i)) = (1 : ↥D) := by
        apply e.injective
        rw [map_mul, h1, sr_mul_sr, sub_self, map_one, one_def]
      exact congrArg Subtype.val h2
    | sr j =>
      left
      have h2 : (⟨t, ht⟩ : ↥D) * ⟨t, ht⟩ = 1 := by
        apply e.injective
        rw [map_mul, h, sr_mul_sr, sub_self, map_one, one_def]
      exact congrArg Subtype.val h2

namespace DDDecomp

variable {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂)
include hd

theorem finite : Finite ↥S := by
  rw [← hd.sup_eq]
  haveI := hd.dih₁.finite
  haveI := hd.isDih₂.finite
  exact Nat.finite_of_card_ne_zero (by
    rw [card_sup_of_le_normalizer (le_normalizer_of_comm fun x hx y hy => hd.comm hx hy)
      hd.inf_eq]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')

theorem card_inf_sup_inf (T : Subgroup G) :
    Nat.card ↥((T ⊓ S₁) ⊔ (T ⊓ S₂)) = Nat.card ↥(T ⊓ S₁) * Nat.card ↥(T ⊓ S₂) :=
  card_sup_of_le_normalizer (le_normalizer_of_comm fun x hx y hy => hd.comm hx.2 hy.2)
    (eq_bot_iff.2 ((inf_le_inf inf_le_right inf_le_right).trans hd.inf_eq.le))

theorem mul_mem_inf_sup_inf {T : Subgroup G} {x₁ x₂ : G} (hx₁ : x₁ ∈ S₁) (hx₂ : x₂ ∈ S₂)
    (hx : x₁ * x₂ ∈ T) (hx₁T : x₁ ∈ T) : x₁ * x₂ ∈ (T ⊓ S₁) ⊔ (T ⊓ S₂) := by
  have hx₂T : x₂ ∈ T := by
    have := mul_mem (inv_mem hx₁T) hx
    rwa [inv_mul_cancel_left] at this
  exact mul_mem (mem_sup_left ⟨hx₁T, hx₁⟩) (mem_sup_right ⟨hx₂T, hx₂⟩)

theorem mul_mem_inf_sup_inf' {T : Subgroup G} {x₁ x₂ : G} (hx₁ : x₁ ∈ S₁) (hx₂ : x₂ ∈ S₂)
    (hx : x₁ * x₂ ∈ T) (hx₂T : x₂ ∈ T) : x₁ * x₂ ∈ (T ⊓ S₁) ⊔ (T ⊓ S₂) := by
  have hx₁T : x₁ ∈ T := by
    have := mul_mem hx (inv_mem hx₂T)
    rwa [mul_inv_cancel_right] at this
  exact hd.mul_mem_inf_sup_inf hx₁ hx₂ hx hx₁T

theorem relIndex_inf_sup_le_two {T : Subgroup G} (hTS : T ≤ S) {V : Subgroup G}
    (hV : IsFourIn S₂ V) (hVT : V ≤ T) : ((T ⊓ S₁) ⊔ (T ⊓ S₂)).relIndex T ≤ 2 := by
  haveI := hd.finite
  haveI : Finite ↥T := Finite.of_injective _ (inclusion_injective hTS)
  haveI : Finite ↥(T ⊓ S₁) :=
    Finite.of_injective _ (inclusion_injective (inf_le_left : T ⊓ S₁ ≤ T))
  haveI : Finite ↥(T ⊓ S₂) :=
    Finite.of_injective _ (inclusion_injective (inf_le_left : T ⊓ S₂ ≤ T))
  haveI : Finite ↥S₂ := hd.isDih₂.finite
  haveI : Finite ↥(S₂ ⊓ normalizer ((T ⊓ S₂ : Subgroup G) : Set G)) :=
    Finite.of_injective _ (inclusion_injective
      (inf_le_left : S₂ ⊓ normalizer ((T ⊓ S₂ : Subgroup G) : Set G) ≤ S₂))
  set φ := ddProdEquiv hd
  let π₂ : ↥S →* G := S₂.subtype.comp ((MonoidHom.snd ↥S₁ ↥S₂).comp φ.toMonoidHom)
  let f : ↥T →* G := π₂.comp (inclusion hTS)
  have hdec : ∀ t : ↥T, ((φ (inclusion hTS t)).1 : G) * f t = t := fun t =>
    ddProdEquiv_apply_mul hd (inclusion hTS t)
  have hker : Nat.card f.ker ≤ Nat.card ↥(T ⊓ S₁) := by
    have hle : f.ker.map T.subtype ≤ T ⊓ S₁ := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨t.2, ?_⟩
      have h1 := hdec t
      rw [MonoidHom.mem_ker.1 ht, mul_one] at h1
      rw [coe_subtype, ← h1]
      exact (φ (inclusion hTS t)).1.2
    rw [← card_map_of_injective T.subtype_injective]
    exact card_le_of_le hle
  have hrange : f.range ≤ S₂ ⊓ normalizer ((T ⊓ S₂ : Subgroup G) : Set G) := by
    rintro _ ⟨t, rfl⟩
    have hy : f t ∈ S₂ := (φ (inclusion hTS t)).2.2
    have hx : ((φ (inclusion hTS t)).1 : G) ∈ S₁ := (φ (inclusion hTS t)).1.2
    have hconj : ∀ g ∈ S₂, (t : G) * g * (t : G)⁻¹ = f t * g * (f t)⁻¹ := by
      intro g hg
      rw [← hdec t]
      exact hd.conj_right hx hy hg
    refine mem_inf.2 ⟨hy, mem_normalizer_iff.2 fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
    · obtain ⟨hgT, hgS⟩ := mem_inf.1 (SetLike.mem_coe.1 hg)
      rw [← hconj g hgS]
      refine mem_inf.2 ⟨mul_mem (mul_mem t.2 hgT) (inv_mem t.2), ?_⟩
      rw [hconj g hgS]
      exact mul_mem (mul_mem hy hgS) (inv_mem hy)
    · obtain ⟨hgT, hgS⟩ := mem_inf.1 (SetLike.mem_coe.1 hg)
      have hgS₂ : g ∈ S₂ := by
        have := mul_mem (mul_mem (inv_mem hy) hgS) hy
        rwa [show (f t)⁻¹ * (f t * g * (f t)⁻¹) * f t = g by group] at this
      refine SetLike.mem_coe.2 (mem_inf.2 ⟨?_, hgS₂⟩)
      rw [← hconj g hgS₂] at hgT
      have := mul_mem (mul_mem (inv_mem t.2) hgT) t.2
      rwa [show (t : G)⁻¹ * ((t : G) * g * (t : G)⁻¹) * t = g by group] at this
  have hN := hd.isDih₂.card_inf_normalizer_le (inf_le_right : T ⊓ S₂ ≤ S₂) hV (le_inf hVT hV.1)
  have hcardT : Nat.card ↥T = Nat.card f.ker * Nat.card f.range := (card_ker_mul_card_range f).symm
  have hle12 : (T ⊓ S₁) ⊔ (T ⊓ S₂) ≤ T := sup_le inf_le_left inf_le_left
  have h := relIndex_mul_card ((T ⊓ S₁) ⊔ (T ⊓ S₂)) T
  rw [inf_of_le_left hle12, hd.card_inf_sup_inf T] at h
  have hpos : 0 < Nat.card ↥(T ⊓ S₁) * Nat.card ↥(T ⊓ S₂) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have hT2 : Nat.card ↥T ≤ 2 * (Nat.card ↥(T ⊓ S₁) * Nat.card ↥(T ⊓ S₂)) := by
    rw [hcardT]
    calc Nat.card f.ker * Nat.card f.range
        ≤ Nat.card ↥(T ⊓ S₁) * (2 * Nat.card ↥(T ⊓ S₂)) :=
          Nat.mul_le_mul hker ((card_le_of_le hrange).trans hN)
      _ = 2 * (Nat.card ↥(T ⊓ S₁) * Nat.card ↥(T ⊓ S₂)) := by ring
  by_contra hlt
  push Not at hlt
  have h3 : 3 * (Nat.card ↥(T ⊓ S₁) * Nat.card ↥(T ⊓ S₂)) ≤ Nat.card ↥T := by
    rw [← h]
    exact Nat.mul_le_mul_right _ hlt
  omega

theorem exists_involution_not_mem {T : Subgroup G} (hTS : T ≤ S) {V₁ V₂ : Subgroup G}
    (hV₁ : IsFourIn S₁ V₁) (hV₁T : V₁ ≤ T) (hV₂ : IsFourIn S₂ V₂) (hV₂T : V₂ ≤ T)
    (hne : ¬ T ≤ (T ⊓ S₁) ⊔ (T ⊓ S₂)) :
    ∃ y₁ ∈ S₁, ∃ y₂ ∈ S₂, y₁ ∉ T ∧ y₂ ∉ T ∧ y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ * y₂ ∈ T := by
  rw [SetLike.not_le_iff_exists] at hne
  obtain ⟨t, ht, htT⟩ := hne
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hd.mem_iff.1 (hTS ht)
  have hx₁T : x₁ ∉ T := fun h => htT (hd.mul_mem_inf_sup_inf hx₁ hx₂ ht h)
  have hx₂T : x₂ ∉ T := fun h => htT (hd.mul_mem_inf_sup_inf' hx₁ hx₂ ht h)
  obtain ⟨s₁, hs₁, hs₁'⟩ := hd.dih₁.exists_mem_four_mul_self hV₁
  obtain ⟨s₂, hs₂, hs₂'⟩ := hd.isDih₂.exists_mem_four_mul_self hV₂
  have hpick : ∀ {D V : Subgroup G} {x s : G}, x ∈ D → s ∈ V → V ≤ D → V ≤ T → x ∉ T →
      (x * x = 1 ∨ x * s * (x * s) = 1) →
      ∃ y ∈ D, y ∉ T ∧ y * y = 1 ∧ ∃ w ∈ T, w ∈ D ∧ y = x * w := by
    intro D V x s hxD hsV hVD hVT hxT h
    rcases h with h | h
    · exact ⟨x, hxD, hxT, h, 1, one_mem _, one_mem _, (mul_one x).symm⟩
    · refine ⟨x * s, mul_mem hxD (hVD hsV), fun hm => hxT ?_, h, s, hVT hsV, hVD hsV, rfl⟩
      have := mul_mem hm (inv_mem (hVT hsV))
      rwa [mul_inv_cancel_right] at this
  obtain ⟨y₁, hy₁, hy₁T, hy₁2, w₁, hw₁T, hw₁, rfl⟩ :=
    hpick hx₁ hs₁ hV₁.1 hV₁T hx₁T (hs₁' x₁ hx₁)
  obtain ⟨y₂, hy₂, hy₂T, hy₂2, w₂, hw₂T, hw₂, rfl⟩ :=
    hpick hx₂ hs₂ hV₂.1 hV₂T hx₂T (hs₂' x₂ hx₂)
  refine ⟨_, hy₁, _, hy₂, hy₁T, hy₂T, hy₁2, hy₂2, ?_⟩
  have : x₁ * w₁ * (x₂ * w₂) = x₁ * x₂ * (w₁ * w₂) := by
    rw [mul_assoc x₁, ← mul_assoc w₁, hd.comm hw₁ hx₂, mul_assoc x₂, ← mul_assoc, ← mul_assoc]
  rw [this]
  exact mul_mem ht (mul_mem hw₁T hw₂T)

theorem card_inf_centralizer_of_not_mem {T : Subgroup G} (hTS : T ≤ S) {V₁ V₂ : Subgroup G}
    (hV₁ : IsFourIn S₁ V₁) (hV₁T : V₁ ≤ T) (hV₂ : IsFourIn S₂ V₂) (hV₂T : V₂ ≤ T) {y : G}
    (hyT : y ∈ T) (hy : y ∉ (T ⊓ S₁) ⊔ (T ⊓ S₂)) (hy2 : y * y = 1) :
    Nat.card ↥(T ⊓ C y) = 8 := by
  haveI := hd.finite
  haveI : Finite ↥T := Finite.of_injective _ (inclusion_injective hTS)
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hd.mem_iff.1 (hTS hyT)
  obtain ⟨hy₁2, hy₂2⟩ := (hd.mul_self_iff hy₁ hy₂).1 hy2
  have hy₁T : y₁ ∉ T := fun h => hy (hd.mul_mem_inf_sup_inf hy₁ hy₂ hyT h)
  have hy₂T : y₂ ∉ T := fun h => hy (hd.mul_mem_inf_sup_inf' hy₁ hy₂ hyT h)
  have hN₁ : IsDihNonab S₁ := by
    rcases hd.dih₁.isKleinFour_or_isDihNonab with hK | hN
    · exact absurd (hV₁T ((IsDih.four_eq_of_isKleinFour hK hV₁).symm ▸ hy₁)) hy₁T
    · exact hN
  have hfactor : ∀ {D V : Subgroup G} {x : G}, IsDihNonab D → IsFourIn D V → V ≤ T → x ∈ D →
      x ∉ T → x * x = 1 → Nat.card ↥(T ⊓ (D ⊓ C x)) = 2 := by
    intro D V x hD hV hVT hxD hxT hx2
    obtain ⟨z, hzD, hz2, hzc⟩ := hD.exists_inf_centralizer_self_eq
    have hzcen : ∀ g ∈ D, g * z = z * g := by
      intro g hg
      have hz : z ∈ D ⊓ centralizer (D : Set G) := hzc ▸ mem_zpowers z
      exact mem_centralizer_iff.1 hz.2 g hg
    have hzV : z ∈ V := (isDih_of_isDihNonab hD).mem_four_of_central hV hzD hzcen
    have hnc : ∃ g ∈ D, g * x ≠ x * g := by
      by_contra hc
      push Not at hc
      exact hxT (hVT ((isDih_of_isDihNonab hD).mem_four_of_central hV hxD hc))
    have hW := (isDih_of_isDihNonab hD).isFourIn_inf_centralizer hxD hx2 hnc
    haveI : Finite ↥(D ⊓ C x) := hW.finite
    have hle : T ⊓ (D ⊓ C x) ≤ D ⊓ C x := inf_le_right
    have hdvd : Nat.card ↥(T ⊓ (D ⊓ C x)) ∣ 4 := hW.2.2 ▸ card_dvd_of_le hle
    have hne4 : Nat.card ↥(T ⊓ (D ⊓ C x)) ≠ 4 := by
      intro h4
      have heq : T ⊓ (D ⊓ C x) = D ⊓ C x := eq_of_le_of_card_ge hle (by rw [h4, hW.2.2])
      have hxW : x ∈ D ⊓ C x := ⟨hxD, mem_centralizer_singleton_iff.2 rfl⟩
      rw [← heq] at hxW
      exact hxT hxW.1
    have hne1 : Nat.card ↥(T ⊓ (D ⊓ C x)) ≠ 1 := by
      intro h1
      have hbot := (card_eq_one).1 h1
      have hzT : z ∈ T ⊓ (D ⊓ C x) :=
        ⟨hVT hzV, hzD, mem_centralizer_singleton_iff.2 (hzcen x hxD).symm⟩
      rw [hbot, mem_bot] at hzT
      rw [hzT, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    have : Nat.card ↥(T ⊓ (D ⊓ C x)) ∈ Nat.divisors 4 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have h4 : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [h4] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hc₁ := hfactor hN₁ hV₁ hV₁T hy₁ hy₁T hy₁2
  have hc₂ := hfactor hd.dih₂ hV₂ hV₂T hy₂ hy₂T hy₂2
  set K := (T ⊓ (S₁ ⊓ C y₁)) ⊔ (T ⊓ (S₂ ⊓ C y₂)) with hK
  have hKcard : Nat.card ↥K = 4 := by
    rw [hK, card_sup_of_le_normalizer (le_normalizer_of_comm (H := T ⊓ (S₁ ⊓ C y₁))
      (K := T ⊓ (S₂ ⊓ C y₂)) fun a ha b hb =>
        hd.comm (mem_inf.1 (mem_inf.1 ha).2).1 (mem_inf.1 (mem_inf.1 hb).2).1)
      (eq_bot_iff.2 ((inf_le_inf (inf_le_right.trans inf_le_left)
        (inf_le_right.trans inf_le_left)).trans hd.inf_eq.le)), hc₁, hc₂]
  have hKeq : ((T ⊓ S₁) ⊔ (T ⊓ S₂)) ⊓ C (y₁ * y₂) = K := by
    apply le_antisymm
    · intro w hw'
      obtain ⟨hw, hwc⟩ := mem_inf.1 hw'
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := (mem_sup_iff_of_le_normalizer
        (le_normalizer_of_comm (H := T ⊓ S₁) (K := T ⊓ S₂) fun a ha b hb =>
          hd.comm (mem_inf.1 ha).2 (mem_inf.1 hb).2)).1 hw
      have hw₁' := mem_inf.1 hw₁
      have hw₂' := mem_inf.1 hw₂
      have hcomp := (hd.inf_centralizer_mul hy₁ hy₂).le
        (mem_inf.2 ⟨hd.mem_iff.2 ⟨w₁, hw₁'.2, w₂, hw₂'.2, rfl⟩, hwc⟩)
      obtain ⟨u₁, hu₁, u₂, hu₂, huw⟩ := (mem_sup_iff_of_le_normalizer
        (le_normalizer_of_comm (H := S₁ ⊓ C y₁) (K := S₂ ⊓ C y₂) fun a ha b hb =>
          hd.comm (mem_inf.1 ha).1 (mem_inf.1 hb).1)).1 hcomp
      have hu₁' := mem_inf.1 hu₁
      have hu₂' := mem_inf.1 hu₂
      obtain ⟨rfl, rfl⟩ := hd.eq_and_eq hw₁'.2 hu₁'.1 hw₂'.2 hu₂'.1 huw
      exact mul_mem (mem_sup_left (mem_inf.2 ⟨hw₁'.1, hu₁⟩))
        (mem_sup_right (mem_inf.2 ⟨hw₂'.1, hu₂⟩))
    · refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · obtain ⟨hwT, hwS⟩ := mem_inf.1 hw
        refine mem_inf.2 ⟨mem_sup_left (mem_inf.2 ⟨hwT, (mem_inf.1 hwS).1⟩), ?_⟩
        exact (mem_inf.1 ((hd.inf_centralizer_mul hy₁ hy₂).ge (mem_sup_left hwS))).2
      · obtain ⟨hwT, hwS⟩ := mem_inf.1 hw
        refine mem_inf.2 ⟨mem_sup_right (mem_inf.2 ⟨hwT, (mem_inf.1 hwS).1⟩), ?_⟩
        exact (mem_inf.1 ((hd.inf_centralizer_mul hy₁ hy₂).ge (mem_sup_right hwS))).2
  have hidx : Nat.card ↥T = 2 * Nat.card ↥((T ⊓ S₁) ⊔ (T ⊓ S₂)) := by
    have hle12 : (T ⊓ S₁) ⊔ (T ⊓ S₂) ≤ T := sup_le inf_le_left inf_le_left
    have h := relIndex_mul_card ((T ⊓ S₁) ⊔ (T ⊓ S₂)) T
    rw [inf_of_le_left hle12] at h
    have h2 := hd.relIndex_inf_sup_le_two hTS hV₂ hV₂T
    have hne1 : ((T ⊓ S₁) ⊔ (T ⊓ S₂)).relIndex T ≠ 1 := by
      rw [Ne, relIndex_eq_one]
      exact fun h => hy (h hyT)
    have hne0 : ((T ⊓ S₁) ⊔ (T ⊓ S₂)).relIndex T ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h
      exact (Nat.card_pos (α := ↥T)).ne' h.symm
    have : ((T ⊓ S₁) ⊔ (T ⊓ S₂)).relIndex T = 2 := by omega
    rw [← h, this]
  have hCT : T ⊓ C (y₁ * y₂) = K ⊔ zpowers (y₁ * y₂) := by
    apply le_antisymm
    · intro w hw'
      obtain ⟨hwT, hwc⟩ := mem_inf.1 hw'
      by_cases hw : w ∈ (T ⊓ S₁) ⊔ (T ⊓ S₂)
      · exact mem_sup_left (hKeq ▸ mem_inf.2 ⟨hw, hwc⟩)
      · have hm := mul_inv_mem_of_card_eq_two_mul (sup_le inf_le_left inf_le_left) hidx hwT hyT
          hw hy
        have hmc : w * (y₁ * y₂)⁻¹ ∈ C (y₁ * y₂) := by
          rw [mem_centralizer_singleton_iff] at hwc ⊢
          rw [inv_mul_cancel_right, ← mul_assoc, ← hwc, mul_inv_cancel_right]
        have hK' : w * (y₁ * y₂)⁻¹ ∈ K := hKeq ▸ mem_inf.2 ⟨hm, hmc⟩
        rw [show w = w * (y₁ * y₂)⁻¹ * (y₁ * y₂) by group]
        exact mul_mem (mem_sup_left hK') (mem_sup_right (mem_zpowers _))
    · refine sup_le (fun w hw => ?_) ?_
      · have hw' := mem_inf.1 (hKeq.symm ▸ hw : w ∈ ((T ⊓ S₁) ⊔ (T ⊓ S₂)) ⊓ C (y₁ * y₂))
        exact mem_inf.2 ⟨(sup_le inf_le_left inf_le_left : (T ⊓ S₁) ⊔ (T ⊓ S₂) ≤ T) hw'.1, hw'.2⟩
      · rw [zpowers_le]
        exact mem_inf.2 ⟨hyT, mem_centralizer_singleton_iff.2 rfl⟩
  have hy1 : y₁ * y₂ ≠ 1 := fun h => hy (h ▸ one_mem _)
  have hord : orderOf (y₁ * y₂) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hKle : K ≤ ((T ⊓ S₁) ⊔ (T ⊓ S₂)) ⊓ C (y₁ * y₂) := hKeq.ge
  have hnorm : zpowers (y₁ * y₂) ≤ normalizer (K : Set G) := by
    refine le_normalizer_of_comm fun x hx w hw => ?_
    have hxc : Commute x (y₁ * y₂) := mem_centralizer_singleton_iff.1 (mem_inf.1 (hKle hx)).2
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
    exact (hxc.zpow_right n).eq
  have hinf : K ⊓ zpowers (y₁ * y₂) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwK, hwy⟩
    rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers hy2 hwy with rfl | rfl
    · exact one_mem _
    · exact absurd (mem_inf.1 (hKle hwK)).1 hy
  rw [hCT, card_sup_of_le_normalizer hnorm hinf, hKcard, Nat.card_zpowers, hord]

end DDDecomp

theorem commutator_sup_eq_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ⁅A ⊔ B, A ⊔ B⁆ = ⁅A, A⁆ ⊔ ⁅B, B⁆ := by
  apply le_antisymm
  · rw [commutator_le]
    intro g hg h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc)).1 hg
    obtain ⟨a', ha', b', hb', rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc)).1 hh
    let μ : ↥A × ↥B →* G := A.subtype.noncommCoprod B.subtype fun x y => hc x x.2 y y.2
    have hμ : ∀ p : ↥A × ↥B, μ p = (p.1 : G) * p.2 := fun p => rfl
    have key : ⁅a * b, a' * b'⁆ = ⁅a, a'⁆ * ⁅b, b'⁆ := by
      have h1 := map_commutatorElement μ (⟨a, ha⟩, ⟨b, hb⟩) (⟨a', ha'⟩, ⟨b', hb'⟩)
      rw [hμ, hμ, hμ] at h1
      rw [← h1]
      simp only [commutatorElement_def, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
        coe_mul, coe_inv]
    rw [key]
    exact mul_mem (mem_sup_left (commutator_mem_commutator ha ha'))
      (mem_sup_right (commutator_mem_commutator hb hb'))
  · exact sup_le (commutator_mono le_sup_left le_sup_left)
      (commutator_mono le_sup_right le_sup_right)

theorem dih_eq_of_mem_commutator {k : ℕ} (hk : 1 ≤ k) {x : DihedralGroup (2 ^ k)}
    (hx : x ∈ commutator (DihedralGroup (2 ^ k))) (hx2 : x * x = 1) :
    x = 1 ∨ x = CFSG.CGT.Foote81L6.zc k := by
  have hker := Abelianization.commutator_subset_ker (TauCeti.dihedralReflectionParity (2 ^ k)) hx
  cases x with
  | r i => exact CFSG.CGT.Foote81L6.TStruct.r_eq_of_mul_self hk hx2
  | sr i =>
    exfalso
    rw [MonoidHom.mem_ker, TauCeti.dihedralReflectionParity_sr] at hker
    exact absurd hker (by decide)

theorem dih_zc_mem_commutator {k : ℕ} (hk : 2 ≤ k) :
    CFSG.CGT.Foote81L6.zc k ∈ commutator (DihedralGroup (2 ^ k)) := by
  rw [← CFSG.CGT.Foote81L6.comm_sr_r_pow hk]
  refine pow_mem ?_ _
  have h : ⁅(sr (0 : ZMod (2 ^ k)))⁻¹, (r (1 : ZMod (2 ^ k)))⁻¹⁆ =
      (sr 0)⁻¹ * (r 1)⁻¹ * sr 0 * r 1 := by
    rw [commutatorElement_def, inv_inv, inv_inv]
  rw [← h, _root_.commutator_def]
  exact commutator_mem_commutator (mem_top _) (mem_top _)

theorem commutator_eq_map_commutator (D : Subgroup G) :
    ⁅D, D⁆ = (commutator ↥D).map D.subtype := by
  rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]

theorem IsDihNonab.mem_centralizer_of_mem_commutator {D : Subgroup G} (hD : IsDihNonab D)
    {w : G} (hw : w ∈ ⁅D, D⁆) (hw2 : w * w = 1) : ∀ g ∈ D, g * w = w * g := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hD
  rw [commutator_eq_map_commutator] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  have hew : e w' ∈ commutator (DihedralGroup (2 ^ k)) := by
    have h := mem_map_of_mem e.toMonoidHom hw'
    rwa [_root_.commutator_def, map_commutator, map_top_of_surjective _ e.surjective,
      ← _root_.commutator_def] at h
  have hw2' : e w' * e w' = 1 := by
    rw [← map_mul, ← map_one e]
    exact congrArg e (Subtype.ext hw2)
  intro g hg
  rcases dih_eq_of_mem_commutator (by omega) hew hw2' with h | h
  · rw [show w' = 1 from e.injective (h.trans e.map_one.symm)]
    simp
  · have hwz : w' = e.symm (CFSG.CGT.Foote81L6.zc k) := by rw [← h, MulEquiv.symm_apply_apply]
    rw [hwz]
    have := congrArg e.symm (CFSG.CGT.Foote81L6.zc_comm (by omega) (e ⟨g, hg⟩))
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
    exact congrArg Subtype.val this

theorem IsDihNonab.mem_commutator_of_central {D : Subgroup G} (hD : IsDihNonab D) {c : G}
    (hcD : c ∈ D) (hc1 : c ≠ 1) (hcc : ∀ g ∈ D, g * c = c * g) : c ∈ ⁅D, D⁆ := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hD
  rw [← CFSG.CGT.Foote81L6.TStruct.symm_zc_eq e hk hcD hc1 hcc, commutator_eq_map_commutator]
  refine mem_map_of_mem D.subtype ?_
  have h := mem_map_of_mem e.symm.toMonoidHom (dih_zc_mem_commutator hk)
  rwa [_root_.commutator_def, map_commutator, map_top_of_surjective _ e.symm.surjective,
    ← _root_.commutator_def] at h

theorem IsDihNonab.comm_of_comm_noncentral {D : Subgroup G} (hD : IsDihNonab D) {x a b : G}
    (hx : x ∈ D) (hnc : ∃ g ∈ D, g * x ≠ x * g) (ha : a ∈ D) (hb : b ∈ D) (hax : a * x = x * a)
    (hbx : b * x = x * b) : a * b = b * a := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hD
  have := dih_comm_of_comm_noncentral' e hk (x := ⟨x, hx⟩) (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    (by
      obtain ⟨g, hg, hgx⟩ := hnc
      exact ⟨⟨g, hg⟩, fun h => hgx (congrArg Subtype.val h)⟩)
    (Subtype.ext hax) (Subtype.ext hbx)
  exact congrArg Subtype.val this

private theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  commutator_le.2 fun g hg h hh => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)

theorem IsDihNonab.commutator_inf_centralizer_eq_bot {D : Subgroup G} (hD : IsDihNonab D) {x : G}
    (hx : x ∈ D) (hnc : ∃ g ∈ D, g * x ≠ x * g) : ⁅D ⊓ C x, D ⊓ C x⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  obtain ⟨haD, hax⟩ := mem_inf.1 ha
  obtain ⟨hbD, hbx⟩ := mem_inf.1 hb
  exact hD.comm_of_comm_noncentral hx hnc hbD haD (mem_centralizer_singleton_iff.1 hbx)
    (mem_centralizer_singleton_iff.1 hax)

namespace DDDecomp

variable {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂)
include hd

theorem commutator_inf_centralizer_mul {x₁ x₂ : G} (hx₁ : x₁ ∈ S₁) (hx₂ : x₂ ∈ S₂) :
    ⁅S ⊓ C (x₁ * x₂), S ⊓ C (x₁ * x₂)⁆ =
      ⁅S₁ ⊓ C x₁, S₁ ⊓ C x₁⁆ ⊔ ⁅S₂ ⊓ C x₂, S₂ ⊓ C x₂⁆ := by
  rw [hd.inf_centralizer_mul hx₁ hx₂]
  exact commutator_sup_eq_of_commute fun a ha b hb =>
    hd.comm (mem_inf.1 ha).1 (mem_inf.1 hb).1

theorem commutator_inf_centralizer_of_central_left {x₁ x₂ : G} (hx₁ : x₁ ∈ S₁)
    (hc₁ : ∀ g ∈ S₁, g * x₁ = x₁ * g) (hx₂ : x₂ ∈ S₂) (hnc₂ : ∃ g ∈ S₂, g * x₂ ≠ x₂ * g) :
    ⁅S ⊓ C (x₁ * x₂), S ⊓ C (x₁ * x₂)⁆ = ⁅S₁, S₁⁆ := by
  rw [hd.commutator_inf_centralizer_mul hx₁ hx₂,
    hd.dih₂.commutator_inf_centralizer_eq_bot hx₂ hnc₂, sup_bot_eq,
    inf_of_le_left fun g hg => mem_centralizer_singleton_iff.2 (hc₁ g hg)]

theorem commutator_inf_centralizer_of_central_right (h₁ : IsDihNonab S₁) {x₁ x₂ : G}
    (hx₁ : x₁ ∈ S₁) (hnc₁ : ∃ g ∈ S₁, g * x₁ ≠ x₁ * g) (hx₂ : x₂ ∈ S₂)
    (hc₂ : ∀ g ∈ S₂, g * x₂ = x₂ * g) :
    ⁅S ⊓ C (x₁ * x₂), S ⊓ C (x₁ * x₂)⁆ = ⁅S₂, S₂⁆ := by
  rw [hd.commutator_inf_centralizer_mul hx₁ hx₂, h₁.commutator_inf_centralizer_eq_bot hx₁ hnc₁,
    bot_sup_eq, inf_of_le_left fun g hg => mem_centralizer_singleton_iff.2 (hc₂ g hg)]

theorem le_centralizer_of_mem_commutator (h₁ : IsDihNonab S₁) {w : G} (hw : w ∈ ⁅S, S⁆)
    (hw2 : w * w = 1) : S ≤ C w := by
  have hS₁' := commutator_self_le S₁
  have hS₂' := commutator_self_le S₂
  rw [← hd.sup_eq, commutator_sup_eq_of_commute fun a ha b hb => hd.comm ha hb] at hw
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm
    (H := ⁅S₁, S₁⁆) (K := ⁅S₂, S₂⁆) fun a ha b hb => hd.comm (hS₁' ha) (hS₂' hb))).1 hw
  obtain ⟨h1, h2⟩ := (hd.mul_self_iff (hS₁' hw₁) (hS₂' hw₂)).1 hw2
  exact hd.le_centralizer_mul (hS₁' hw₁) (hS₂' hw₂)
    (h₁.mem_centralizer_of_mem_commutator hw₁ h1)
    (hd.dih₂.mem_centralizer_of_mem_commutator hw₂ h2)

theorem card_inf_centralizer_le_of_noncentral {y₁ y₂ a : G} (hy₁ : y₁ ∈ S₁)
    (hy₁2 : y₁ * y₁ = 1) (hnc : ∃ g ∈ S₁, g * y₁ ≠ y₁ * g) (hy₂ : y₂ ∈ S₂) (ha : a ∈ S₁)
    (ha2 : a * a = 1) (hanc : ∃ g ∈ S₁, g * a ≠ a * g) :
    Nat.card ↥(S ⊓ C (y₁ * y₂)) ≤ Nat.card ↥(S ⊓ C a) := by
  haveI := hd.isDih₂.finite
  have hW₁ := hd.dih₁.isFourIn_inf_centralizer hy₁ hy₁2 hnc
  have hWa := hd.dih₁.isFourIn_inf_centralizer ha ha2 hanc
  haveI : Finite ↥(S₂ ⊓ C y₂) :=
    Finite.of_injective _ (inclusion_injective (inf_le_left : S₂ ⊓ C y₂ ≤ S₂))
  rw [hd.inf_centralizer_mul hy₁ hy₂, hd.inf_centralizer_left ha,
    card_sup_of_le_normalizer (le_normalizer_of_comm (H := S₁ ⊓ C y₁) (K := S₂ ⊓ C y₂)
      fun x hx z hz => hd.comm (mem_inf.1 hx).1 (mem_inf.1 hz).1)
      (eq_bot_iff.2 ((inf_le_inf inf_le_left inf_le_left).trans hd.inf_eq.le)),
    card_sup_of_le_normalizer (le_normalizer_of_comm (H := S₁ ⊓ C a) (K := S₂)
      fun x hx z hz => hd.comm (mem_inf.1 hx).1 hz)
      (eq_bot_iff.2 ((inf_le_inf inf_le_left le_rfl).trans hd.inf_eq.le)),
    hW₁.2.2, hWa.2.2]
  exact Nat.mul_le_mul_left _ (card_le_of_le inf_le_left)

end DDDecomp

end CFSG.GH72
