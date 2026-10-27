module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJS
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAutFrame
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJNorm

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem eq_one_of_odd_order_dvd_two_pow {x : G} (hodd : Odd (orderOf x)) {n : ℕ}
    (h : orderOf x ∣ 2 ^ n) : x = 1 := by
  rw [← orderOf_eq_one_iff]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  cases k with
  | zero => simpa using hk
  | succ k =>
      exfalso
      exact (Nat.not_even_iff_odd.mpr hodd)
        (by rw [hk]; exact Even.pow_of_ne_zero even_two (Nat.succ_ne_zero k))

private theorem mem_sup_closure_singleton {H : Subgroup G} {g : G} (hg2 : g ^ 2 = 1)
    (hgH : g ∈ normalizer (H : Set G)) (x : G) :
    x ∈ H ⊔ Subgroup.closure {g} ↔ x ∈ H ∨ ∃ y ∈ H, x = y * g := by
  have hgg : g * g = 1 := by simpa [pow_two] using hg2
  let T : Subgroup G :=
    { carrier := {x : G | x ∈ H ∨ ∃ y ∈ H, x = y * g}
      one_mem' := Or.inl (one_mem H)
      mul_mem' := by
        rintro x z (hx | ⟨y, hy, rfl⟩) (hz | ⟨w, hw, rfl⟩)
        · exact Or.inl (mul_mem hx hz)
        · exact Or.inr ⟨x * w, mul_mem hx hw, (mul_assoc x w g).symm⟩
        · refine Or.inr ⟨y * (g * z * g⁻¹), mul_mem hy ?_, ?_⟩
          · exact (Subgroup.mem_set_normalizer_iff.mp hgH z).mp hz
          · rw [show y * (g * z * g⁻¹) * g = (y * g) * z by group]
        · refine Or.inl ?_
          rw [show (y * g) * (w * g) = y * (g * w * g⁻¹) * (g * g) by group,
            hgg, mul_one]
          exact mul_mem hy ((Subgroup.mem_set_normalizer_iff.mp hgH w).mp hw)
      inv_mem' := by
        rintro x (hx | ⟨y, hy, rfl⟩)
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ⟨g * y⁻¹ * g⁻¹, ?_, ?_⟩
          · exact (Subgroup.mem_set_normalizer_iff.mp hgH y⁻¹).mp (inv_mem hy)
          · show (y * g)⁻¹ = (g * y⁻¹ * g⁻¹) * g
            rw [mul_inv_rev,
              show g⁻¹ * y⁻¹ = g * y⁻¹ by rw [inv_eq_of_mul_eq_one_right hgg]]
            group }
  have hle : H ⊔ Subgroup.closure {g} ≤ T := by
    refine sup_le (fun x hx => Or.inl hx) ?_
    rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact Or.inr ⟨1, one_mem H, (one_mul g).symm⟩
  have hge : T ≤ H ⊔ Subgroup.closure {g} := by
    intro x hx
    rcases hx with hxH | ⟨y, hy, hxy⟩
    · exact Subgroup.mem_sup_left hxH
    · rw [hxy]
      exact mul_mem (Subgroup.mem_sup_left hy)
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have hEq : H ⊔ Subgroup.closure {g} = T := le_antisymm hle hge
  rw [hEq]
  exact Iff.rfl

private theorem Sσ_eq_sup (s : Setting3 G L) (g : G) :
    (frameWith s g).Sσ = s.fr.S ⊔ Subgroup.closure {g} := by
  have hset : ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀, g} : Set G) =
      ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀} : Set G) ∪ {g} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_empty_iff_false]
    tauto
  change Subgroup.closure ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀, g} : Set G) =
    s.fr.S ⊔ Subgroup.closure {g}
  rw [hset, Subgroup.closure_union]
  rfl

theorem s3_g_normalizes_S (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) {g : G} (hg : ActsAs L g s.fr'.σ) :
    g ∈ normalizer (s.fr.S : Set G) := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  refine (mem_normalizer_iff_jSub (L := L) hZ (s3_S_le_L s) (s3_isPGroup_S s) hg).mpr ?_
  rw [s3_jSub_S s]
  exact frame_sigma_normalizes s.fr' s.facts.1

theorem s3_mem_Sσ_iff (s : Setting3 G L) {g : G} (hg2 : g ^ 2 = 1)
    (hgS : g ∈ normalizer (s.fr.S : Set G)) {x : G} :
    x ∈ (frameWith s g).Sσ ↔ x ∈ s.fr.S ∨ ∃ y ∈ s.fr.S, x = y * g := by
  rw [Sσ_eq_sup s g]
  exact mem_sup_closure_singleton (H := s.fr.S) hg2 hgS x

theorem s3_mem_Vg_iff {g : G} (hg2 : g ^ 2 = 1) (hgN : g ∈ normalizer (L : Set G)) {x : G} :
    x ∈ L ⊔ closure {g} ↔ x ∈ L ∨ ∃ y ∈ L, x = y * g :=
  mem_sup_closure_singleton (H := L) hg2 hgN x

theorem s3_Vg_le_normalizer {g : G} (hgN : g ∈ normalizer (L : Set G)) :
    L ⊔ closure {g} ≤ normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer
    ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hgN))

theorem s3_Sσ_le_normalizer (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) {g : G} (hg : ActsAs L g s.fr'.σ) :
    (frameWith s g).Sσ ≤ normalizer (L : Set G) := by
  rw [Sσ_eq_sup s g]
  exact sup_le (s3_S_le_N s)
    ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr (mem_normalizer_of_actsAs L hg)))

theorem s3_mul_g_not_mem_L (hS : HRSetting G L) (hOut : (innerAut (L ⧸ center L)).index = 2)
    (s : Setting3 G L) {g : G} (hg : ActsAs L g s.fr'.σ) {y : G} (hy : y ∈ L) :
    y * g ∉ L := by
  intro hmem
  have hgL : g ∈ L := by
    have h1 : y⁻¹ * (y * g) ∈ L := mul_mem (inv_mem hy) hmem
    rwa [show y⁻¹ * (y * g) = g by group] at h1
  have hconj : ActsAs L g (MulAut.conj (QuotientGroup.mk (⟨g, hgL⟩ : ↥L))) :=
    actsAs_of_mem L hgL
  have hσeq : s.fr'.σ = MulAut.conj (QuotientGroup.mk (⟨g, hgL⟩ : ↥L)) :=
    actsAs_unique L hg hconj
  refine frame_sigma_not_mem_inner s.fr' s.facts.1 hOut ?_
  rw [hσeq, innerAut, MonoidHom.mem_range]
  exact ⟨_, rfl⟩

theorem s3_kernel_Vg (hS : HRSetting G L) (hOut : (innerAut (L ⧸ center L)).index = 2)
    (s : Setting3 G L) {g : G} (hg2 : g ^ 2 = 1) (hg : ActsAs L g s.fr'.σ) {x : G}
    (hx : x ∈ L ⊔ closure {g}) (hxc : x ∈ centralizer (L : Set G)) : x ∈ zL L := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  have hgN : g ∈ normalizer (L : Set G) := mem_normalizer_of_actsAs L hg
  rcases (s3_mem_Vg_iff (L := L) hg2 hgN).mp hx with hxL | ⟨y, hy, hyx⟩
  · exact mem_zL_iff.mpr ⟨hxL, hxc⟩
  · exfalso
    have hx_acts : ActsAs L (y * g) (1 : MulAut (L ⧸ center L)) := by
      rw [← hyx]
      exact actsAs_of_mem_centralizer L hxc
    have hymul : ActsAs L (y * g)
        (MulAut.conj (QuotientGroup.mk (⟨y, hy⟩ : ↥L)) * s.fr'.σ) :=
      actsAs_mul L (actsAs_of_mem L hy) hg
    have hu : (1 : MulAut (L ⧸ center L)) =
        MulAut.conj (QuotientGroup.mk (⟨y, hy⟩ : ↥L)) * s.fr'.σ :=
      actsAs_unique L hx_acts hymul
    have hσeq : s.fr'.σ = (MulAut.conj (QuotientGroup.mk (⟨y, hy⟩ : ↥L)))⁻¹ :=
      eq_inv_of_mul_eq_one_right hu.symm
    have hA_mem : MulAut.conj (QuotientGroup.mk (⟨y, hy⟩ : ↥L)) ∈
        innerAut (L ⧸ center L) := by
      rw [innerAut, MonoidHom.mem_range]
      exact ⟨_, rfl⟩
    refine frame_sigma_not_mem_inner s.fr' s.facts.1 hOut ?_
    rw [hσeq]
    exact inv_mem hA_mem

theorem s3_jOn_Sσ_injective (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (s : Setting3 G L) {g : G} (hg2 : g ^ 2 = 1)
    (hg : ActsAs L g s.fr'.σ) (hP : (frameWith s g).Sσ ≤ normalizer (L : Set G)) :
    Function.Injective (jOn L hP) := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  rw [← MonoidHom.ker_eq_bot_iff (jOn L hP), Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxc : (x : G) ∈ centralizer (L : Set G) := by
    have hx' := hx
    rw [ker_jOn L (V := (frameWith s g).Sσ) hP] at hx'
    exact Subgroup.mem_subgroupOf.mp hx'
  have hgN : g ∈ normalizer (L : Set G) := mem_normalizer_of_actsAs L hg
  have hgS : g ∈ normalizer (s.fr.S : Set G) := s3_g_normalizes_S hS hZ s hg
  have hxSσ : (x : G) ∈ (frameWith s g).Sσ := x.2
  have hxsup : (x : G) ∈ L ⊔ Subgroup.closure {g} := by
    rcases (s3_mem_Sσ_iff s hg2 hgS).mp hxSσ with hxS | ⟨y, hy, hyx⟩
    · exact Subgroup.mem_sup_left (s3_S_le_L s hxS)
    · exact (s3_mem_Vg_iff (L := L) hg2 hgN).mpr (Or.inr ⟨y, s3_S_le_L s hy, hyx⟩)
  have hzL : (x : G) ∈ zL L := s3_kernel_Vg hS hOut s hg2 hg hxsup hxc
  have hxS : (x : G) ∈ s.fr.S := by
    rcases (s3_mem_Sσ_iff s hg2 hgS).mp hxSσ with hxS | ⟨y, hy, hyx⟩
    · exact hxS
    · exfalso
      exact s3_mul_g_not_mem_L hS hOut s hg (s3_S_le_L s hy) (by rw [← hyx]; exact zL_le hzL)
  have hcard : Nat.card ↥(zL L) = Nat.card ↥(center ↥L) :=
    Subgroup.card_map_of_injective (K := Subgroup.center ↥L) (f := L.subtype)
      L.subtype_injective
  have hOddZ : Odd (Nat.card ↥(zL L)) := by rw [hcard]; exact hZ
  have hdvdz : orderOf (x : G) ∣ Nat.card ↥(zL L) := (zL L).orderOf_dvd_natCard hzL
  have hodd : Odd (orderOf (x : G)) := Odd.of_dvd_nat hOddZ hdvdz
  have hp2 : IsPGroup 2 ↥(zpowers (x : G)) := s3_isPGroup_zpowers s hxS
  obtain ⟨k, hk⟩ := hp2.exists_pow_pow_eq_one ⟨(x : G), Subgroup.mem_zpowers (x : G)⟩
  have hkG : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hvd2 : orderOf (x : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hkG
  exact Subtype.ext (eq_one_of_odd_order_dvd_two_pow hodd hvd2)

end CFSG.OddStandard.HigherRank.YamadaG23
