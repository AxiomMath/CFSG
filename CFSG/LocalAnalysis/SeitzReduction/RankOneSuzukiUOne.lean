module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRTwoBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section Complement

variable {G : Type*} [Group G]

theorem exists_complement_of_coprime {U H : Subgroup G} {t d : G} (hHU : H ≤ U)
    (hUH : U ≤ normalizer (H : Set G))
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ H) (hsq : ∀ x ∈ U, x ^ 2 ∈ H)
    (hdU : d ∈ normalizer (U : Set G)) (hdH : d ∈ normalizer (H : Set G))
    (hodd : Odd (orderOf d)) (htU : t ∈ U) (htH : t ∉ H) (hdt : d * t = t * d)
    (hfix : ∀ w ∈ U, w⁻¹ * (d⁻¹ * w * d) ∈ H → w ∈ H ∨ t⁻¹ * w ∈ H) :
    ∃ U₁ : Subgroup G, H ≤ U₁ ∧ U₁ ≤ U ∧ U ≤ normalizer (U₁ : Set G) ∧ t ∉ U₁ ∧
      U₁ ⊔ zpowers t = U ∧ d ∈ normalizer (U₁ : Set G) := by
  classical
  set m := orderOf d with hm
  have hdm : d ^ m = 1 := pow_orderOf_eq_one d
  have hdiU : ∀ i : ℕ, ∀ x ∈ U, (d ^ i)⁻¹ * x * d ^ i ∈ U := fun i x hx =>
    (mem_normalizer_iff''.mp (pow_mem hdU i) x).mp hx
  have hdiH : ∀ i : ℕ, ∀ x ∈ H, (d ^ i)⁻¹ * x * d ^ i ∈ H := fun i x hx =>
    (mem_normalizer_iff''.mp (pow_mem hdH i) x).mp hx
  let cd : ℕ → U →* U := fun i =>
    { toFun := fun x => ⟨(d ^ i)⁻¹ * x * d ^ i, hdiU i x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcd : ∀ i (x : U), ((cd i x : U) : G) = (d ^ i)⁻¹ * x * d ^ i := fun _ _ => rfl
  set N := H.subgroupOf U with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.mp (hUH g.2) n).mp hn⟩
  have hPc : ∀ p q : U ⧸ N, p * q = q * p := by
    intro p q
    induction p using QuotientGroup.induction_on with | H x => ?_
    induction q using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hN, mem_subgroupOf]
    have e : ((x * y)⁻¹ * (y * x) : U) = (y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ : U) := by group
    rw [e]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hcomm _ (inv_mem y.2) _ (inv_mem x.2)
  let _ : CommGroup (U ⧸ N) := { mul_comm := hPc }
  set mk : U →* U ⧸ N := QuotientGroup.mk' N with hmk
  have hmk1 : ∀ x : U, mk x = 1 ↔ (x : G) ∈ H := fun x => by
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, mem_subgroupOf]
  have hmkeq : ∀ x y : U, mk x = mk y ↔ ((x : G)⁻¹ * y) ∈ H := fun x y => by
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      mem_subgroupOf]
    simp
  let π : U →* U ⧸ N := ∏ i ∈ Finset.range m, mk.comp (cd i)
  have hπ : ∀ x : U, π x = ∏ i ∈ Finset.range m, mk (cd i x) := fun x => by
    simp only [π, MonoidHom.finsetProd_apply, MonoidHom.comp_apply]
  have hσle : N ≤ N.comap (cd 1) := fun x hx => by
    rw [mem_comap, hN, mem_subgroupOf, hcd]
    rw [hN, mem_subgroupOf] at hx
    exact hdiH 1 _ hx
  let σ : U ⧸ N →* U ⧸ N := QuotientGroup.map N N (cd 1) hσle
  have hσ : ∀ x : U, σ (mk x) = mk (cd 1 x) := fun x => QuotientGroup.map_mk N N (cd 1) hσle x
  have hcd_succ : ∀ i (x : U), cd 1 (cd i x) = cd (i + 1) x := fun i x => Subtype.ext (by
    simp only [hcd, pow_succ]
    group)
  have hcd_succ' : ∀ i (x : U), cd i (cd 1 x) = cd (i + 1) x := fun i x => Subtype.ext (by
    simp only [hcd, pow_succ']
    group)
  have hcdm : ∀ x : U, cd m x = x := fun x => Subtype.ext (by simp [hcd, hdm])
  have hcd0 : ∀ x : U, cd 0 x = x := fun x => Subtype.ext (by simp [hcd])
  have hπσ : ∀ x : U, π (cd 1 x) = π x := by
    intro x
    rw [hπ, hπ]
    simp only [hcd_succ']
    have h1 := Finset.prod_range_succ (fun i => mk (cd i x)) m
    have h2 := Finset.prod_range_succ' (fun i => mk (cd i x)) m
    simp only [hcdm, hcd0] at h1 h2
    rw [h1] at h2
    exact (mul_right_cancel h2).symm
  have hσπ : ∀ x : U, σ (π x) = π x := by
    intro x
    calc σ (π x) = π (cd 1 x) := by
          rw [hπ, hπ, map_prod]
          simp only [hσ, hcd_succ, hcd_succ']
      _ = π x := hπσ x
  have hfixσ : ∀ p : U ⧸ N, σ p = p → p = 1 ∨ p = mk ⟨t, htU⟩ := by
    intro p hp
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N p
    have hw : mk w = mk (cd 1 w) := by rw [← hσ]; exact hp.symm
    rw [hmkeq, hcd, pow_one] at hw
    rcases hfix w w.2 hw with h1 | h1
    · exact Or.inl ((hmk1 w).mpr h1)
    · right
      exact ((hmkeq _ _).mpr h1).symm
  have hπ1 : ∀ x : U, π x = 1 ∨ π x = mk ⟨t, htU⟩ := fun x => hfixσ _ (hσπ x)
  have hπH : ∀ x : U, (x : G) ∈ H → π x = 1 := by
    intro x hx
    rw [hπ]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [hmk1, hcd]
    exact hdiH i _ hx
  have hπt : π ⟨t, htU⟩ = mk ⟨t, htU⟩ := by
    have hcdt : ∀ i, cd i ⟨t, htU⟩ = ⟨t, htU⟩ := fun i => Subtype.ext (by
      rw [hcd]
      have e : d ^ i * t = t * d ^ i := (Commute.pow_left hdt i).eq
      calc (d ^ i)⁻¹ * t * d ^ i = (d ^ i)⁻¹ * (t * d ^ i) := by group
        _ = (d ^ i)⁻¹ * (d ^ i * t) := by rw [e]
        _ = t := by group)
    rw [hπ]
    simp only [hcdt, Finset.prod_const, Finset.card_range]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul]
    have ht2 : mk ⟨t, htU⟩ ^ 2 = 1 := by
      rw [← map_pow, hmk1]
      exact hsq t htU
    rw [ht2, one_pow, one_mul]
  have hmkt : mk ⟨t, htU⟩ ≠ 1 := fun h1 => htH ((hmk1 _).mp h1)
  refine ⟨π.ker.map U.subtype, fun x hx => ⟨⟨x, hHU hx⟩, hπH _ hx, rfl⟩,
    map_subtype_le _, ?_, ?_, ?_, ?_⟩
  ·
    intro g hg
    refine mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, ?_, rfl⟩
      simp only [SetLike.mem_coe, MonoidHom.mem_ker] at hy ⊢
      rw [map_mul, map_mul, hy, mul_one, map_inv, mul_inv_cancel]
    · obtain ⟨y, hy, hyx⟩ := hx
      refine ⟨⟨g, hg⟩⁻¹ * y * ⟨g, hg⟩, ?_, ?_⟩
      · simp only [SetLike.mem_coe, MonoidHom.mem_ker] at hy ⊢
        rw [map_mul, map_mul, hy, mul_one, map_inv, inv_mul_cancel]
      · have e : (y : G) = g * x * g⁻¹ := hyx
        show g⁻¹ * (y : G) * g = x
        rw [e]
        group
  ·
    rintro ⟨y, hy, hyt⟩
    have hy' : y = ⟨t, htU⟩ := Subtype.ext hyt
    simp only [SetLike.mem_coe, MonoidHom.mem_ker] at hy
    rw [hy', hπt] at hy
    exact hmkt hy
  ·
    refine le_antisymm (sup_le (map_subtype_le _) (zpowers_le.mpr htU)) fun x hx => ?_
    rcases hπ1 ⟨x, hx⟩ with h1 | h1
    · exact mem_sup_left ⟨⟨x, hx⟩, h1, rfl⟩
    · have hxt : π (⟨x, hx⟩ * ⟨t, htU⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, hπt, mul_inv_cancel]
      have e : x = ((⟨x, hx⟩ * ⟨t, htU⟩⁻¹ : U) : G) * t := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact mul_mem (mem_sup_left ⟨_, hxt, rfl⟩) (mem_sup_right (mem_zpowers t))
  ·
    refine mem_normalizer_iff''.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨cd 1 y, ?_, by rw [coe_subtype, hcd, pow_one]⟩
      simp only [SetLike.mem_coe, MonoidHom.mem_ker] at hy ⊢
      rw [hπσ]
      exact hy
    · obtain ⟨y, hy, hyx⟩ := hx
      have hxU : x ∈ U := by
        have h1 := (mem_normalizer_iff''.mp hdU x).mpr (by rw [← hyx]; exact y.2)
        exact h1
      refine ⟨⟨x, hxU⟩, ?_, rfl⟩
      have e : cd 1 ⟨x, hxU⟩ = y := Subtype.ext (by rw [hcd, pow_one, ← hyx]; rfl)
      simp only [SetLike.mem_coe, MonoidHom.mem_ker] at hy ⊢
      rw [← hπσ, e]
      exact hy

end Complement

end CFSG.SeitzReduction.RankOne
