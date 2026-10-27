module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Fusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec5B59Hyp : Prop where
  h36 : Asc82Lemma36
  h37 : Asc82Lemma37
  h52b : Asc82Lemma52b
  h53 : Asc82Lemma53
  tab : Asc82Tab5
  h54 : Asc82Lemma54
  l58b : Asc82Lemma58b

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
  {φ : (Fin 6 → ZMod 2) → G}

private theorem inducesTypeSome_mem_normalizer {L : Subgroup G} {s : G} {n : ℕ} {ε : ℤˣ}
    {r : ℕ} {α : ℤˣ} (h : InducesTypeSome L s n ε r α) :
    s ∈ normalizer (L : Set G) := by
  obtain ⟨V, _, _, _, Q, hQ, e, x, -, -, hind, -⟩ := h
  exact hind.1

private theorem normalizer_conj_mem {A : Subgroup G} {m y : G}
    (hm : m ∈ normalizer (A : Set G)) (hy : y ∈ A) : m * y * m⁻¹ ∈ A := by
  have hiff := (Subgroup.mem_normalizer_iff'' (H := A)).mp hm
  have hEq : m⁻¹ * (m * y * m⁻¹) * m = y := by group
  exact (hiff (m * y * m⁻¹)).mpr (by rw [hEq]; exact hy)

private theorem conjClassIn_normalizer_inv {N : Subgroup G} {z m : G} (hm : m ∈ N)
    {y : G} (hy : y ∈ conjClassIn N z) : m * y * m⁻¹ ∈ conjClassIn N z := by
  obtain ⟨n, hn, rfl⟩ := hy
  exact ⟨m * n, N.mul_mem hm hn, by group⟩

private theorem perm6_mul_comm (hm : Sec5Model58 t L z r A φ) (v w : Fin 6 → ZMod 2) :
    φ v * φ w = φ w * φ v := by
  calc φ v * φ w = φ (v + w) := (hm.perm.map_add v w).symm
    _ = φ (w + v) := by rw [add_comm]
    _ = φ w * φ v := hm.perm.map_add w v

theorem sec5b_zG_inter_A (hy : Sec5B59Hyp) (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ) {x : G} (hxA : x ∈ A) (hx : ∃ g : G, g⁻¹ * z * g = x) :
    x ∈ wclass φ 3 ∪ wclass φ 4 := by
  obtain ⟨g, hgx⟩ := hx
  obtain ⟨k, hk6, hxk⟩ := hm.perm.exists_wclass hxA
  have hz2 : orderOf z = 2 := hR.pocket.1
  have hxcomm : x ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨v, rfl⟩ := (hm.perm.mem_iff x).mp hxA
    rw [← hm.map_one]
    exact perm6_mul_comm hm v (fun _ => 1)
  interval_cases k
  ·
    have hx1 : x = 1 := by
      have h := hm.perm.wclass_zero
      rw [h] at hxk
      simpa using hxk
    have hz1 : z = 1 := by
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = g * x * g⁻¹ := by rw [hgx]
        _ = 1 := by rw [hx1]; group
    rw [hz1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  ·
    have hK2 : Kind5 L x 2 := by
      obtain ⟨v, hv, hxv⟩ := hxk
      have htype := hm.type_one v (Or.inl hv)
      rw [hxv] at htype
      exact htype
    have h54 := hy.h54 G t L S z hR.toSec5Ctx g (by rw [hgx]; exact hxcomm)
    rw [hgx] at h54
    rcases h54 with hzL | hK3
    · obtain ⟨h, hhL, hxh⟩ := hzL
      have hxL : x ∈ L := by
        rw [hxh]
        exact L.mul_mem (L.mul_mem hhL (IsI4PlusIn.mem hR.pocket)) (L.inv_mem hhL)
      exact absurd ((hm.mem_L_iff hxk).mp hxL) (by norm_num : ¬ Even 1)
    · have hx2 : orderOf x = 2 := by rw [← hgx, orderOf_conjugate_eq, hz2]
      have hxN : x ∈ normalizer (L : Set G) := by
        obtain ⟨α, hα⟩ := hK2
        exact inducesTypeSome_mem_normalizer hα
      exact absurd hK3 (hy.tab.excl G L hR.toSec5Ctx.toSec5Setting.isOm6Z2 x hx2 hxN
        2 3 (by norm_num) (by norm_num) (by norm_num) hK2)
  ·
    obtain ⟨a, haH, hax⟩ := hm.perm.exists_conj hxk hm.tz_mem_wclass
    have hconj : (g * a⁻¹)⁻¹ * z * (g * a⁻¹) = t * z := by
      calc (g * a⁻¹)⁻¹ * z * (g * a⁻¹) = a * (g⁻¹ * z * g) * a⁻¹ := by group
        _ = a * x * a⁻¹ := by rw [hgx]
        _ = t * z := hax
    exact absurd hconj
      (sec5_tz_not_conj_z hy.h36 hy.h37 hy.h52b hy.h53 hy.tab hR.toSec5Ctx (g * a⁻¹))
  · exact Or.inl hxk
  · exact Or.inr hxk
  ·
    have hK2 : Kind5 L x 2 := by
      obtain ⟨v, hv, hxv⟩ := hxk
      have htype := hm.type_one v (Or.inr hv)
      rw [hxv] at htype
      exact htype
    have h54 := hy.h54 G t L S z hR.toSec5Ctx g (by rw [hgx]; exact hxcomm)
    rw [hgx] at h54
    rcases h54 with hzL | hK3
    · obtain ⟨h, hhL, hxh⟩ := hzL
      have hxL : x ∈ L := by
        rw [hxh]
        exact L.mul_mem (L.mul_mem hhL (IsI4PlusIn.mem hR.pocket)) (L.inv_mem hhL)
      exact absurd ((hm.mem_L_iff hxk).mp hxL) (by norm_num : ¬ Even 5)
    · have hx2 : orderOf x = 2 := by rw [← hgx, orderOf_conjugate_eq, hz2]
      have hxN : x ∈ normalizer (L : Set G) := by
        obtain ⟨α, hα⟩ := hK2
        exact inducesTypeSome_mem_normalizer hα
      exact absurd hK3 (hy.tab.excl G L hR.toSec5Ctx.toSec5Setting.isOm6Z2 x hx2 hxN
        2 3 (by norm_num) (by norm_num) (by norm_num) hK2)
  ·
    have hxt : x = t := by
      have h := hm.perm.wclass_six
      rw [h] at hxk
      have hx1 : x = φ (fun _ => 1) := hxk
      rw [hx1, hm.map_one]
    exact absurd (hgx.trans hxt) (sec5_t_not_conj_z hy.h37 hR.toSec5Ctx g)

theorem sec5b_zM_eq (hy : Sec5B59Hyp) (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ) :
    conjClassIn (normalizer (A : Set G)) z = wclass φ 3 ∪ wclass φ 4 := by
  apply Set.Subset.antisymm
  · rintro x ⟨m, hmN, rfl⟩
    exact sec5b_zG_inter_A hy hR hm (normalizer_conj_mem hmN hm.mem_A.2.2) ⟨m⁻¹, by group⟩
  · have hTz : z ∈ conjClassIn (normalizer (A : Set G)) z := ⟨1, one_mem _, by group⟩
    have hz2 : orderOf z = 2 := hR.pocket.1
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    have hTA : conjClassIn (normalizer (A : Set G)) z ⊆ (A : Set G) := by
      rintro y ⟨m, hmN, rfl⟩
      exact normalizer_conj_mem hmN hm.mem_A.2.2
    have hTinv : ∀ m ∈ normalizer (A : Set G),
        ∀ y ∈ conjClassIn (normalizer (A : Set G)) z,
          m * y * m⁻¹ ∈ conjClassIn (normalizer (A : Set G)) z :=
      fun m hmN _ hy => conjClassIn_normalizer_inv hmN hy
    have hnotL : ¬ conjClassIn (normalizer (A : Set G)) z ⊆ (L : Set G) :=
      hm.not_subset_L (hirr := hy.l58b G t L S z r B A hR) hTA hTinv ⟨z, hTz, hz1⟩
    obtain ⟨y, hyT, hyL⟩ := Set.not_subset.mp hnotL
    have hy34 : y ∈ wclass φ 3 ∪ wclass φ 4 := by
      rcases hyT with ⟨m, hmN, rfl⟩
      exact sec5b_zG_inter_A hy hR hm (normalizer_conj_mem hmN hm.mem_A.2.2) ⟨m⁻¹, by group⟩
    have hyW4 : y ∉ wclass φ 4 := fun hy4 =>
      hyL ((hm.mem_L_iff hy4).mpr (by norm_num : Even 4))
    have hy3 : y ∈ wclass φ 3 := by
      rcases hy34 with h | h
      · exact h
      · exact absurd h hyW4
    have hW4 : wclass φ 4 ⊆ conjClassIn (normalizer (A : Set G)) z :=
      hm.perm.wclass_subset_of_inter
        (fun _ ha _ hy => conjClassIn_normalizer_inv ha.2 hy)
        ⟨z, hTz, hm.z_mem_wclass⟩
    have hW3 : wclass φ 3 ⊆ conjClassIn (normalizer (A : Set G)) z :=
      hm.perm.wclass_subset_of_inter
        (fun _ ha _ hy => conjClassIn_normalizer_inv ha.2 hy)
        ⟨y, hyT, hy3⟩
    rintro x (hx3 | hx4)
    · exact hW3 hx3
    · exact hW4 hx4

theorem sec5b_zM_ncard (hy : Sec5B59Hyp) (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ) :
    (conjClassIn (normalizer (A : Set G)) z).ncard = 35 := by
  rw [sec5b_zM_eq hy hR hm]
  rw [Set.ncard_union_eq (hm.perm.disjoint_wclass (by norm_num : (3 : ℕ) ≠ 4))]
  rw [IsPerm6.ncard_wclass hm.perm 3, IsPerm6.ncard_wclass hm.perm 4]
  norm_num [Nat.choose]

end CFSG.OddStandard.SmallF3.Omega
