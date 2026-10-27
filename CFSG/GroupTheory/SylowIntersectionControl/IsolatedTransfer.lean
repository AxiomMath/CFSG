module

public import CFSG.GroupTheory.SylowIntersectionControl.IsolatedEmbedded

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem isPIsolatedOver_sup_iff {H X : Subgroup G} (hH : IsPGroup p H)
    (hXH : X ≤ normalizer (H : Set G)) :
    IsPIsolatedOver p (X ⊔ H) H ↔ IsPIsolatedOver p X (X ⊓ H) := by
  have hHK : H ≤ X ⊔ H := le_sup_right
  have hKN : X ⊔ H ≤ normalizer (H : Set G) := sup_le hXH le_normalizer
  have : (H.subgroupOf (X ⊔ H)).Normal := (normal_subgroupOf_iff_le_normalizer hHK).mpr hKN
  rw [isPIsolatedOver_iff_quotient hHK hH,
    ← isPIsolatedOver_subgroupOf_iff (K := X) (H := X ⊓ H) (K' := X) inf_le_left le_rfl,
    subgroupOf_self]
  set f : X →* (X ⊔ H : Subgroup G) ⧸ H.subgroupOf (X ⊔ H) :=
    (QuotientGroup.mk' _).comp (inclusion le_sup_left) with hf_def
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hk' := hk
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right X H hXH] at hk'
    obtain ⟨x, hx, y, hy, rfl⟩ := hk'
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hf_def, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, mem_subgroupOf]
    simpa [mul_assoc] using hy
  have hker : f.ker = (X ⊓ H).subgroupOf X := by
    ext ⟨x, hx⟩
    rw [MonoidHom.mem_ker, hf_def, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf]
    simp [hx]
  have key := isPIsolatedOver_map_iff (p := p) hf
    (by rw [hker]; exact (hH.to_le inf_le_right).comap_subtype)
    (H := (X ⊓ H).subgroupOf X) (K := ⊤) hker.le le_top
  rwa [map_top_of_surjective _ hf,
    (Subgroup.map_eq_bot_iff ((X ⊓ H).subgroupOf X)).mpr hker.ge] at key

omit [Fact p.Prime] in
theorem IsPIsolatedOver.mem_of_isSubnormal_over {H K Y : Subgroup G}
    (h : IsPIsolatedOver 2 K H) (hH : IsPGroup 2 H) (hHK : H ≤ K)
    (hKN : K ≤ normalizer (H : Set G)) (hHY : H ≤ Y) (hYK : Y ≤ K)
    (hY : (Y.subgroupOf K).IsSubnormal) (hp : 2 ∣ H.relIndex Y) {a : G} (ha : a ∈ K)
    (ha2 : a ^ 2 ∈ H) : a ∈ Y := by
  have : (H.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hHK).mpr hKN
  have hf : Function.Surjective (QuotientGroup.mk' (H.subgroupOf K)) :=
    QuotientGroup.mk'_surjective _
  have hker := QuotientGroup.ker_mk' (H.subgroupOf K)
  set f := QuotientGroup.mk' (H.subgroupOf K)
  have hiso := (isPIsolatedOver_iff_quotient hHK hH).mp h
  have hcard : Nat.card ((Y.subgroupOf K).map f) = H.relIndex Y := by
    rw [← relIndex_ker, hker, relIndex_subgroupOf hYK]
  have hkY : f.ker ≤ Y.subgroupOf K := by
    rw [hker]
    exact fun x hx => hHY hx
  suffices hmem : f ⟨a, ha⟩ ∈ (Y.subgroupOf K).map f by
    obtain ⟨y, hy, hya⟩ := hmem
    have hk : y⁻¹ * ⟨a, ha⟩ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hya, inv_mul_cancel]
    have := mul_mem hy (hkY hk)
    rw [mul_inv_cancel_left] at this
    exact this
  by_cases h1 : f ⟨a, ha⟩ = 1
  · rw [h1]
    exact one_mem _
  · refine hiso.mem_of_isSubnormal (hY.map hf) (even_iff_two_dvd.mpr (hcard ▸ hp)) ?_
    refine orderOf_eq_prime ?_ h1
    rw [← map_pow]
    refine (MonoidHom.mem_ker).mp (hker.ge ?_)
    rw [mem_subgroupOf]
    simpa using ha2

omit [Finite G] [Fact p.Prime] in
private theorem normal_closure_sq_mem (H : Subgroup G) :
    ((closure {a | a ∈ normalizer (H : Set G) ∧ a ^ 2 ∈ H}).subgroupOf
      (normalizer (H : Set G))).Normal := by
  set N := normalizer (H : Set G)
  set s : Set G := {a | a ∈ N ∧ a ^ 2 ∈ H}
  have hsN : ∀ n ∈ N, ∀ a ∈ s, n * a * n⁻¹ ∈ s := fun n hn a ha =>
    ⟨mul_mem (mul_mem hn ha.1) (inv_mem hn), by
      rw [conj_pow]
      exact (mem_normalizer_iff.mp hn _).mp ha.2⟩
  have hmap : ∀ n ∈ N, (closure s).map (MulAut.conj n).toMonoidHom ≤ closure s :=
    fun n hn => by
      rw [MonoidHom.map_closure]
      refine closure_mono ?_
      rintro _ ⟨a, ha, rfl⟩
      exact hsN n hn a ha
  refine (normal_subgroupOf_iff_le_normalizer ((closure_le N).mpr fun _ ha => ha.1)).mpr
    fun n hn => ?_
  refine mem_normalizer_iff.mpr fun y => ⟨fun hy => hmap n hn ⟨y, hy, rfl⟩, fun hy => ?_⟩
  have := hmap n⁻¹ (inv_mem hn) ⟨_, hy, rfl⟩
  rwa [show (MulAut.conj n⁻¹).toMonoidHom (n * y * n⁻¹) = y by
    simp [mul_assoc]] at this

omit [Fact p.Prime] in
theorem IsPIsolatedOver.exists_le_of_sq_mem {H M : Subgroup G}
    (h : IsPIsolatedOver 2 (normalizer (H : Set G)) H) (hH : IsPGroup 2 H)
    (hM : ∀ a ∈ normalizer (H : Set G), a ^ 2 ∈ H → a ∈ M) :
    ∃ K : Subgroup G, H ≤ K ∧ K ≤ normalizer (H : Set G) ∧
      (K.subgroupOf (normalizer (H : Set G))).IsSubnormal ∧ 2 ∣ H.relIndex K ∧ K ≤ M := by
  have hnorm := normal_closure_sq_mem H
  set N := normalizer (H : Set G)
  set s : Set G := {a | a ∈ N ∧ a ^ 2 ∈ H}
  have hHK : H ≤ closure s := fun x hx =>
    subset_closure ⟨le_normalizer hx, pow_mem hx 2⟩
  have hKN : closure s ≤ N := (closure_le N).mpr fun _ ha => ha.1
  refine ⟨closure s, hHK, hKN, hnorm.isSubnormal, ?_,
    (closure_le M).mpr fun a ha => hM a ha.1 ha.2⟩
  have : (H.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl
  have hiso := (isPIsolatedOver_iff_quotient le_normalizer hH).mp h
  obtain ⟨M₀, hM₀⟩ := isPIsolatedOver_top_bot_iff.mp hiso
  have h2 : 2 ∣ Nat.card (N ⧸ H.subgroupOf N) := by
    rw [← card_top (G := N ⧸ H.subgroupOf N)]
    exact hM₀.2.1.trans (card_dvd_of_le le_top)
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨⟨a, haN⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have ha2 : a ^ 2 ∈ H := by
    have := pow_orderOf_eq_one (QuotientGroup.mk' (H.subgroupOf N) ⟨a, haN⟩)
    rw [hq, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at this
    simpa using this
  have hker := QuotientGroup.ker_mk' (H.subgroupOf N)
  have hcard : Nat.card (((closure s).subgroupOf N).map (QuotientGroup.mk' (H.subgroupOf N))) =
      H.relIndex (closure s) := by
    rw [← relIndex_ker, hker, relIndex_subgroupOf hKN]
  rw [← hcard, ← hq]
  have hmem : QuotientGroup.mk' (H.subgroupOf N) ⟨a, haN⟩ ∈
      ((closure s).subgroupOf N).map (QuotientGroup.mk' (H.subgroupOf N)) :=
    ⟨⟨a, haN⟩, subset_closure ⟨haN, ha2⟩, rfl⟩
  have := orderOf_dvd_natCard (⟨_, hmem⟩ :
    ((closure s).subgroupOf N).map (QuotientGroup.mk' (H.subgroupOf N)))
  rwa [orderOf_mk] at this

end CFSG.GroupTheory
