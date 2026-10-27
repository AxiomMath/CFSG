module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4WCycTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped Pointwise

@[expose] def Data.XSW {G : Type} [Group G] (d : Data G) : Subgroup G :=
  d.XW ⊓ normalizer ((d.withT d.W : Subgroup G) : Set G)

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem exists_omegaPermW_eq (S : d.OmW) :
    ∃ x : d.XW, d.omegaPermW x ⟨_, tW_mem_OmW⟩ = S := by
  obtain ⟨y, hy, hS⟩ := S.2
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  rw [Data.omegaPermW_apply]
  change (fun g => y * g * y⁻¹) '' (d.t • (d.W : Set G)) = S
  rw [conj_image_smul_coset (Subgroup.mem_inf.1 hy).2, hS]

omit [Finite G] in
theorem omegaPermW_fix (x : d.XW) (hxt : (x : G) * d.t = d.t * x) :
    d.omegaPermW x ⟨_, tW_mem_OmW⟩ = ⟨_, tW_mem_OmW⟩ := by
  apply Subtype.ext
  rw [Data.omegaPermW_apply]
  change (fun g => (x : G) * g * (x : G)⁻¹) '' (d.t • (d.W : Set G)) = d.t • (d.W : Set G)
  rw [conj_image_smul_coset (Subgroup.mem_inf.1 x.2).2, hxt, mul_inv_cancel_right]

theorem omegaPermW_trans
    (h : d.Hyp)
    (hc : d.CycW) (S S' : d.OmW) (hS : S ≠ ⟨_, tW_mem_OmW⟩) (hS' : S' ≠ ⟨_, tW_mem_OmW⟩) :
    ∃ x : d.XW, (x : G) * d.t = d.t * x ∧ d.omegaPermW x S = S' := by
  rcases (h.mem_OmW_iff hc).1 S.2 with e | ⟨k, e⟩
  · exact absurd (Subtype.ext e) hS
  rcases (h.mem_OmW_iff hc).1 S'.2 with e' | ⟨k', e'⟩
  · exact absurd (Subtype.ext e') hS'
  have hy : orbSU k' * (orbSU k)⁻¹ ∈ CzSub :=
    mul_mem (orbSU_mem_CzSub k') (inv_mem (orbSU_mem_CzSub k))
  have hyX := h.ι_mem_XW_of_mem_CzSub hc hy
  refine ⟨⟨_, hyX⟩, h.ι_comm_t _, Subtype.ext ?_⟩
  rw [Data.omegaPermW_apply, e, e', Data.ptW, Data.ptW]
  change (fun g => d.ι (orbSU k' * (orbSU k)⁻¹) * g * (d.ι (orbSU k' * (orbSU k)⁻¹))⁻¹) ''
    ((d.ι (orbSU k * b₀SU * (orbSU k)⁻¹) * d.t) • (d.W : Set G)) = _
  rw [conj_image_smul_coset (Subgroup.mem_inf.1 hyX).2]
  congr 1
  have hyt := h.ι_comm_t (orbSU k' * (orbSU k)⁻¹)
  calc d.ι (orbSU k' * (orbSU k)⁻¹) * (d.ι (orbSU k * b₀SU * (orbSU k)⁻¹) * d.t) *
        (d.ι (orbSU k' * (orbSU k)⁻¹))⁻¹ =
      d.ι (orbSU k' * (orbSU k)⁻¹) * d.ι (orbSU k * b₀SU * (orbSU k)⁻¹) *
        (d.ι (orbSU k' * (orbSU k)⁻¹))⁻¹ *
        (d.ι (orbSU k' * (orbSU k)⁻¹) * d.t * (d.ι (orbSU k' * (orbSU k)⁻¹))⁻¹) := by group
    _ = d.ι (orbSU k' * (orbSU k)⁻¹ * (orbSU k * b₀SU * (orbSU k)⁻¹) *
        (orbSU k' * (orbSU k)⁻¹)⁻¹) * d.t := by
      rw [hyt, mul_inv_cancel_right, ← map_inv, ← map_mul, ← map_mul]
    _ = d.ι (orbSU k' * b₀SU * (orbSU k')⁻¹) * d.t := by
      congr 2
      group

omit [Finite G] in
theorem omegaPermW_inv_apply (x : d.XW) (S : d.OmW) :
    d.omegaPermW x⁻¹ (d.omegaPermW x S) = S := by
  rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]

theorem isMultiplyPretransitive_omegaW
    (h : d.Hyp) (hc : d.CycW) :
    MulAction.IsMultiplyPretransitive d.omegaPermW.range d.OmW 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c e hab hce
  obtain ⟨x, hx⟩ := exists_omegaPermW_eq a
  obtain ⟨y, hy⟩ := exists_omegaPermW_eq c
  have hb' : d.omegaPermW x⁻¹ b ≠ ⟨_, tW_mem_OmW⟩ := by
    intro he
    apply hab
    rw [← hx, ← he, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply]
  have he' : d.omegaPermW y⁻¹ e ≠ ⟨_, tW_mem_OmW⟩ := by
    intro he
    apply hce
    rw [← hy, ← he, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply]
  obtain ⟨k, hkt, hke⟩ := h.omegaPermW_trans hc _ _ hb' he'
  refine ⟨⟨d.omegaPermW (y * k * x⁻¹), ⟨_, rfl⟩⟩, ?_, ?_⟩
  · change d.omegaPermW (y * k * x⁻¹) a = c
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hx,
      omegaPermW_inv_apply, omegaPermW_fix k hkt, hy]
  · change d.omegaPermW (y * k * x⁻¹) b = e
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hke,
      ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]

theorem t_not_mem_W
    (h : d.Hyp) :
    d.t ∉ d.W := fun ht => by
  have : d.t ∈ d.ZX₄ := by
    rw [← h.W_inf_H]
    exact Subgroup.mem_inf.2 ⟨ht, h.t_mem_H⟩
  exact h.t_not_mem_L (h.F_le_L (d.ZX₄_le_F this))

theorem mem_withT_W_iff
    (h : d.Hyp)
    (hc : d.CycW) {x : G} : x ∈ d.withT d.W ↔ x ∈ d.W ∨ x * d.t ∈ d.W :=
  mem_sup_zpowers_iff h.t_mul_t fun k hk => by
    rw [h.t_conj_W_of_cyc hc hk]
    exact inv_mem hk

theorem crossed_mem_W_of_mem_XSW
    (h : d.Hyp) (hc : d.CycW) {x : G} (hx : x ∈ d.XSW) :
    x * d.t * x⁻¹ * d.t⁻¹ ∈ d.W := by
  obtain ⟨hxX, hxE⟩ := Subgroup.mem_inf.1 hx
  have hxW := (Subgroup.mem_inf.1 hxX).2
  have hm : x * d.t * x⁻¹ ∈ d.withT d.W :=
    (mem_normalizer_iff.1 hxE _).1 (mem_sup_right (mem_zpowers _))
  rw [h.t_inv]
  rcases (h.mem_withT_W_iff hc).1 hm with hm | hm
  · exfalso
    apply h.t_not_mem_W
    have := (mem_normalizer_iff.1 (inv_mem hxW) _).1 hm
    rwa [show x⁻¹ * (x * d.t * x⁻¹) * x⁻¹⁻¹ = d.t by group] at this
  · exact hm

theorem mem_XSW_iff
    (h : d.Hyp)
    (hc : d.CycW) {x : G} (hx : x ∈ d.XW) :
    x ∈ d.XSW ↔ (x * d.t * x⁻¹) • (d.W : Set G) = d.t • (d.W : Set G) := by
  have hxW := (Subgroup.mem_inf.1 hx).2
  rw [leftCoset_eq_iff]
  constructor
  · intro hxS
    have hw := h.crossed_mem_W_of_mem_XSW hc hxS
    rwa [show (x * d.t * x⁻¹)⁻¹ * d.t = x * d.t * x⁻¹ * d.t⁻¹ by
      rw [show (x * d.t * x⁻¹)⁻¹ = x * d.t⁻¹ * x⁻¹ by group, h.t_inv]]
  · intro hw
    refine Subgroup.mem_inf.2 ⟨hx, mem_normalizer_fintype fun y hy => ?_⟩
    have hle : d.withT d.W ≤ (d.withT d.W).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun w hw' => mem_sup_left ((mem_normalizer_iff.1 hxW w).1 hw')) ?_
      rw [zpowers_le]
      change x * d.t * x⁻¹ ∈ d.withT d.W
      rw [show x * d.t * x⁻¹ = d.t * ((x * d.t * x⁻¹)⁻¹ * d.t)⁻¹ by group]
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (inv_mem hw))
    exact hle hy

theorem card_XW_eq
    (h : d.Hyp)
    (hc : d.CycW) : Nat.card d.XW = Nat.card d.OmW * Nat.card d.XSW := by
  let : MulAction d.XW d.OmW := MulAction.compHom _ d.omegaPermW
  have hstab : MulAction.stabilizer d.XW (⟨_, tW_mem_OmW⟩ : d.OmW) =
      d.XSW.subgroupOf d.XW := by
    ext x
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, h.mem_XSW_iff hc x.2, Subtype.ext_iff]
    change (fun g => (x : G) * g * (x : G)⁻¹) '' (d.t • (d.W : Set G)) = _ ↔ _
    rw [conj_image_smul_coset (Subgroup.mem_inf.1 x.2).2]
  have horb : MulAction.orbit d.XW (⟨_, tW_mem_OmW⟩ : d.OmW) = Set.univ := by
    refine Set.eq_univ_of_forall fun S => ?_
    obtain ⟨x, hx⟩ := exists_omegaPermW_eq S
    exact ⟨x, hx⟩
  have hidx := MulAction.index_stabilizer (G := d.XW) (⟨_, tW_mem_OmW⟩ : d.OmW)
  rw [horb, Set.ncard_univ, hstab] at hidx
  rw [← (d.XSW.subgroupOf d.XW).card_mul_index, hidx, mul_comm]
  congr 1
  exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv

theorem comm_z_of_mem_normalizer_W
    (h : d.Hyp) (hc : d.CycW) {x : G}
    (hx : x ∈ normalizer (d.W : Set G)) : x * d.z = d.z * x := by
  have hm : x * d.z * x⁻¹ ∈ d.W := (mem_normalizer_iff.1 hx _).1 h.z_mem_W
  have hsq : x * d.z * x⁻¹ * (x * d.z * x⁻¹) = 1 := by
    rw [show x * d.z * x⁻¹ * (x * d.z * x⁻¹) = x * (d.z * d.z) * x⁻¹ by group, z_mul_z]
    group
  have hZ : x * d.z * x⁻¹ ∈ d.ZX₄ := by
    by_contra hz
    exact z_ne_one ((h.W_sq_of_cyc hc hm hz).symm.trans hsq)
  rcases eq_one_or_eq_z hZ with e | e
  · exfalso
    apply z_ne_one (d := d)
    calc d.z = x⁻¹ * (x * d.z * x⁻¹) * x := by group
      _ = 1 := by rw [e]; group
  · calc x * d.z = x * d.z * x⁻¹ * x := by group
      _ = d.z * x := by rw [e]

theorem mem_normalizer_ZR_of (_h : d.Hyp) {x : G} (hxz : x * d.z = d.z * x)
    (hxt : x * d.t * x⁻¹ * d.t⁻¹ ∈ d.ZX₄) : x ∈ normalizer (d.ZR : Set G) := by
  refine mem_normalizer_fintype fun y hy => ?_
  have hle : d.ZR ≤ d.ZR.comap (MulAut.conj x).toMonoidHom := by
    refine sup_le ?_ ?_
    · intro a ha
      rcases eq_one_or_eq_z ha with rfl | rfl
      · exact one_mem _
      · change x * d.z * x⁻¹ ∈ d.ZR
        rw [hxz, mul_inv_cancel_right]
        exact mem_sup_left z_mem_ZX₄
    · rw [zpowers_le]
      change x * d.t * x⁻¹ ∈ d.ZR
      rw [show x * d.t * x⁻¹ = (x * d.t * x⁻¹ * d.t⁻¹) * d.t by group]
      exact mul_mem (mem_sup_left hxt) (mem_sup_right (mem_zpowers _))
  exact hle hy

theorem mem_ZX₄_of_sq_of_cyc
    (h : d.Hyp)
    (hc : d.CycW) {w : G} (hw : w ∈ d.W) (hw2 : w * w = 1) : w ∈ d.ZX₄ := by
  by_contra hz
  exact z_ne_one ((h.W_sq_of_cyc hc hw hz).symm.trans hw2)

theorem mul_mem_normalizer_ZR_of_cyc
    (h : d.Hyp) (hc : d.CycW) {x x' : G} (hx : x ∈ d.XSW)
    (hx' : x' ∈ d.XSW) (hxN : x ∉ normalizer (d.ZR : Set G))
    (hx'N : x' ∉ normalizer (d.ZR : Set G)) : x⁻¹ * x' ∈ normalizer (d.ZR : Set G) := by
  have hxz := h.comm_z_of_mem_normalizer_W hc (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2
  have hx'z := h.comm_z_of_mem_normalizer_W hc
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx').1).2
  have hw := h.crossed_mem_W_of_mem_XSW hc hx
  have hw' := h.crossed_mem_W_of_mem_XSW hc hx'
  have hwz : x * d.t * x⁻¹ * d.t⁻¹ ∉ d.ZX₄ := fun hz => hxN (h.mem_normalizer_ZR_of hxz hz)
  have hw'z : x' * d.t * x'⁻¹ * d.t⁻¹ ∉ d.ZX₄ := fun hz => hx'N (h.mem_normalizer_ZR_of hx'z hz)
  have hq := h.W_sq_of_cyc hc hw hwz
  have hq' := h.W_sq_of_cyc hc hw' hw'z
  have hr : (x' * d.t * x'⁻¹ * d.t⁻¹) * (x * d.t * x⁻¹ * d.t⁻¹)⁻¹ ∈ d.ZX₄ := by
    refine h.mem_ZX₄_of_sq_of_cyc hc (mul_mem hw' (inv_mem hw)) ?_
    have hcomm := h.Y_comm (d.W_le_Y hw') (d.W_le_Y (inv_mem hw))
    calc (x' * d.t * x'⁻¹ * d.t⁻¹) * (x * d.t * x⁻¹ * d.t⁻¹)⁻¹ *
          ((x' * d.t * x'⁻¹ * d.t⁻¹) * (x * d.t * x⁻¹ * d.t⁻¹)⁻¹) =
        (x' * d.t * x'⁻¹ * d.t⁻¹) * ((x * d.t * x⁻¹ * d.t⁻¹)⁻¹ * (x' * d.t * x'⁻¹ * d.t⁻¹)) *
          (x * d.t * x⁻¹ * d.t⁻¹)⁻¹ := by group
      _ = (x' * d.t * x'⁻¹ * d.t⁻¹) * ((x' * d.t * x'⁻¹ * d.t⁻¹) * (x * d.t * x⁻¹ * d.t⁻¹)⁻¹) *
          (x * d.t * x⁻¹ * d.t⁻¹)⁻¹ := by rw [← hcomm]
      _ = ((x' * d.t * x'⁻¹ * d.t⁻¹) * (x' * d.t * x'⁻¹ * d.t⁻¹)) *
          ((x * d.t * x⁻¹ * d.t⁻¹) * (x * d.t * x⁻¹ * d.t⁻¹))⁻¹ := by group
      _ = 1 := by rw [hq, hq', mul_inv_cancel]
  refine h.mem_normalizer_ZR_of ?_ ?_
  · calc x⁻¹ * x' * d.z = x⁻¹ * (x' * d.z) := by group
      _ = x⁻¹ * (d.z * x') := by rw [hx'z]
      _ = x⁻¹ * (d.z * x) * x⁻¹ * x' := by group
      _ = x⁻¹ * (x * d.z) * x⁻¹ * x' := by rw [hxz]
      _ = d.z * (x⁻¹ * x') := by group
  · rw [show x⁻¹ * x' * d.t * (x⁻¹ * x')⁻¹ * d.t⁻¹ =
        x⁻¹ * ((x' * d.t * x'⁻¹ * d.t⁻¹) * (x * d.t * x⁻¹ * d.t⁻¹)⁻¹) * x by group]
    rcases eq_one_or_eq_z hr with e | e
    · rw [e, mul_one, inv_mul_cancel]
      exact one_mem _
    · rw [e, show x⁻¹ * d.z * x = d.z by
        calc x⁻¹ * d.z * x = x⁻¹ * (d.z * x) := by group
          _ = x⁻¹ * (x * d.z) := by rw [hxz]
          _ = d.z := by group]
      exact z_mem_ZX₄

theorem card_XSW_dvd
    (h : d.Hyp)
    (hc : d.CycW) : Nat.card d.XSW ∣ 2 * Nat.card (normalizer (d.ZR : Set G)) := by
  have hidx : ((d.XSW ⊓ normalizer (d.ZR : Set G)).subgroupOf d.XSW).index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    by_cases hex : ∃ x₀ ∈ d.XSW, x₀ ∉ normalizer (d.ZR : Set G)
    · obtain ⟨x₀, hx₀, hx₀N⟩ := hex
      refine ⟨⟨x₀, hx₀⟩, fun b => ?_⟩
      by_cases hb : (b : G) ∈ normalizer (d.ZR : Set G)
      · exact Or.inr (mem_subgroupOf.mpr (Subgroup.mem_inf.2 ⟨b.2, hb⟩))
      · left
        rw [mem_subgroupOf]
        refine Subgroup.mem_inf.2 ⟨mul_mem b.2 hx₀, ?_⟩
        have hb' : (b : G)⁻¹ ∉ normalizer (d.ZR : Set G) := fun h' => hb (by
          simpa using inv_mem h')
        simpa using h.mul_mem_normalizer_ZR_of_cyc hc (inv_mem b.2) hx₀ hb' hx₀N
    · push Not at hex
      exact ⟨1, fun b => Or.inr (mem_subgroupOf.mpr (Subgroup.mem_inf.2 ⟨b.2, hex b b.2⟩))⟩
  have hcard := ((d.XSW ⊓ normalizer (d.ZR : Set G)).subgroupOf d.XSW).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at hcard
  rw [← hcard, mul_comm 2]
  exact Nat.mul_dvd_mul (card_dvd_of_le inf_le_right) hidx

theorem card_CHz_dvd
    (h : d.Hyp) :
    Nat.card (centralizer ({d.z} : Set G) ⊓ d.H : Subgroup G) ∣ 4 * Nat.card CzSub := by
  have hKH : (centralizer ({d.z} : Set G) ⊓ d.H : Subgroup G) ≤ d.H := inf_le_right
  have hLK : d.L ⊓ (centralizer ({d.z} : Set G) ⊓ d.H) = d.pull CzSub := by
    ext x
    constructor
    · rintro ⟨hxL, hxz, -⟩
      obtain ⟨α, rfl⟩ : x ∈ d.ι.range := d.range_ι.symm ▸ hxL
      refine ⟨α, mem_centralizer_singleton_iff.2 (d.ι_injective ?_), rfl⟩
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.1 hxz
    · rintro ⟨α, hα, rfl⟩
      exact ⟨d.ι_mem α, mem_centralizer_singleton_iff.2 (by
        rw [Data.z, ← map_mul, ← map_mul, comm_of_mem_CzSub hα]), h.L_le_H (d.ι_mem α)⟩
  have h1 := Subgroup.relIndex_mul_card d.L (centralizer ({d.z} : Set G) ⊓ d.H)
  rw [hLK, d.card_pull] at h1
  rw [← h1]
  refine Nat.mul_dvd_mul_right ?_ _
  rw [← Subgroup.relIndex_subgroupOf hKH]
  have := h.normal_subgroupOf
  exact (Subgroup.relIndex_dvd_index_of_normal _ _).trans h.index_L_dvd_four

theorem card_XW_dvd
    (h : d.Hyp)
    (hc : d.CycW) : Nat.card d.XW ∣ 2 ^ 16 * 3 ^ 4 * 7 := by
  rw [h.card_XW_eq hc, h.card_OmW hc]
  have h1 := h.card_XSW_dvd hc
  rw [h.card_normalizer_ZR] at h1
  have h2 := h.card_CHz_dvd
  have h3 := card_CzSub_dvd
  calc 28 * Nat.card d.XSW
      ∣ 28 * (2 * (Nat.card (centralizer ({d.z} : Set G) ⊓ d.H : Subgroup G) * 2)) :=
        Nat.mul_dvd_mul_left 28 h1
    _ ∣ 28 * (2 * ((4 * Nat.card CzSub) * 2)) :=
        Nat.mul_dvd_mul_left 28 (Nat.mul_dvd_mul_left 2 (Nat.mul_dvd_mul_right h2 2))
    _ ∣ 28 * (2 * ((4 * (2 ^ 7 * 648)) * 2)) :=
        Nat.mul_dvd_mul_left 28 (Nat.mul_dvd_mul_left 2 (Nat.mul_dvd_mul_right
          (Nat.mul_dvd_mul_left 4 h3) 2))
    _ = 2 ^ 16 * 3 ^ 4 * 7 := by norm_num

theorem card_range_omegaPermW_dvd
    (h : d.Hyp) (hc : d.CycW) :
    Nat.card d.omegaPermW.range ∣ 2 ^ 16 * 3 ^ 4 * 7 :=
  (Subgroup.card_range_dvd d.omegaPermW).trans (h.card_XW_dvd hc)

omit [Finite G] in
theorem omegaPermW_coset (x : d.XW) (hxt : (x : G) * d.t = d.t * x) {S : d.OmW} {a : G}
    (hS : (S : Set G) = (a * d.t) • (d.W : Set G)) :
    ((d.omegaPermW x S : d.OmW) : Set G) = ((x : G) * a * (x : G)⁻¹ * d.t) • (d.W : Set G) := by
  rw [Data.omegaPermW_apply, hS, conj_image_smul_coset (Subgroup.mem_inf.1 x.2).2]
  congr 1
  calc (x : G) * (a * d.t) * (x : G)⁻¹ = (x : G) * a * (x : G)⁻¹ * ((x : G) * d.t) * (x : G)⁻¹ := by
        group
    _ = _ := by rw [hxt]; group

theorem orbSU_zero : orbSU 0 = 1 := rfl

theorem eightyOne_dvd_card_range
    (h : d.Hyp) (hc : d.CycW) :
    81 ∣ Nat.card d.omegaPermW.range := by
  set P := d.omegaPermW.range with hP
  set s₀ : d.OmW := ⟨_, tW_mem_OmW⟩ with hs₀
  set s₁ : d.OmW := ⟨_, h.ptW_mem_OmW hc 0⟩ with hs₁
  set s₅ : d.OmW := ⟨_, h.ptW_mem_OmW hc 5⟩ with hs₅
  have h10 : s₁ ≠ s₀ := fun e => h.ptW_ne_tW 0 (congrArg Subtype.val e)
  have horb₀ : MulAction.orbit P s₀ = Set.univ := by
    refine Set.eq_univ_of_forall fun S => ?_
    obtain ⟨x, hx⟩ := exists_omegaPermW_eq S
    exact ⟨⟨d.omegaPermW x, ⟨x, rfl⟩⟩, hx⟩
  have hidx₀ := MulAction.index_stabilizer P s₀
  rw [horb₀, Set.ncard_univ, h.card_OmW hc] at hidx₀
  set P₁ := MulAction.stabilizer P s₀ with hP₁
  have horb₁ : MulAction.orbit P₁ s₁ = {S | S ≠ s₀} := by
    ext S
    constructor
    · rintro ⟨σ, rfl⟩ e
      apply h10
      have hσ : (σ : P) • s₀ = s₀ := σ.2
      change (σ : P) • s₁ = s₀ at e
      calc s₁ = (σ : P)⁻¹ • ((σ : P) • s₁) := (inv_smul_smul _ _).symm
        _ = (σ : P)⁻¹ • s₀ := by rw [e]
        _ = (σ : P)⁻¹ • ((σ : P) • s₀) := by rw [hσ]
        _ = s₀ := inv_smul_smul _ _
    · intro hS
      obtain ⟨x, hxt, hx⟩ := h.omegaPermW_trans hc s₁ S h10 hS
      refine ⟨⟨⟨d.omegaPermW x, ⟨x, rfl⟩⟩, ?_⟩, hx⟩
      exact omegaPermW_fix x hxt
  have hidx₁ := MulAction.index_stabilizer P₁ s₁
  have hcard27 : ({S | S ≠ s₀} : Set d.OmW).ncard = 27 := by
    have := Set.ncard_compl ({s₀} : Set d.OmW)
    rw [Set.ncard_singleton, h.card_OmW hc] at this
    rw [show ({S | S ≠ s₀} : Set d.OmW) = ({s₀} : Set d.OmW)ᶜ by ext; simp, this]
  rw [horb₁, hcard27] at hidx₁
  have he₂X := h.ι_mem_XW_of_mem_CzSub hc e₂SU_mem_CzSub
  set ε : d.XW := ⟨_, he₂X⟩ with hε
  have hεt : (ε : G) * d.t = d.t * ε := h.ι_comm_t e₂SU
  have hε₀ : d.omegaPermW ε s₀ = s₀ := omegaPermW_fix ε hεt
  have hε₁ : d.omegaPermW ε s₁ = s₁ := by
    apply Subtype.ext
    rw [omegaPermW_coset ε hεt (a := d.ι (orbSU 0 * b₀SU * (orbSU 0)⁻¹)) rfl]
    change (d.ι e₂SU * d.ι (orbSU 0 * b₀SU * (orbSU 0)⁻¹) * (d.ι e₂SU)⁻¹ * d.t) •
      (d.W : Set G) = d.ptW 0
    rw [Data.ptW, ← map_inv, ← map_mul, ← map_mul]
    refine (h.coset_ι_eq_iff ?_ (orb_mem_A₁sub 0)).2 ?_
    · exact conj_mem_A₁sub_of_comm_z (comm_of_mem_CzSub e₂SU_mem_CzSub) (orb_mem_A₁sub 0)
    · rw [orbSU_zero, one_mul, inv_one, mul_one]
      exact cvec_e₂_b₀SU
  have hε₅ : d.omegaPermW ε s₅ ≠ s₅ := by
    intro e
    have e' := congrArg Subtype.val e
    rw [omegaPermW_coset ε hεt (a := d.ι (orbSU 5 * b₀SU * (orbSU 5)⁻¹)) rfl] at e'
    change (d.ι e₂SU * d.ι (orbSU 5 * b₀SU * (orbSU 5)⁻¹) * (d.ι e₂SU)⁻¹ * d.t) •
      (d.W : Set G) = d.ptW 5 at e'
    rw [Data.ptW, ← map_inv, ← map_mul, ← map_mul] at e'
    have := (h.coset_ι_eq_iff
      (conj_mem_A₁sub_of_comm_z (comm_of_mem_CzSub e₂SU_mem_CzSub) (orb_mem_A₁sub 5))
      (orb_mem_A₁sub 5)).1 e'
    rw [cvec_orb] at this
    exact cvec_e₂_orb this
  have hε3 : ε ^ 3 = 1 := Subtype.ext (by
    change d.ι e₂SU ^ 3 = 1
    rw [← map_pow, ← orderOf_e₂SU, pow_orderOf_eq_one, map_one])
  set ε₁ : P₁ := ⟨⟨d.omegaPermW ε, ⟨ε, rfl⟩⟩, hε₀⟩ with hε₁def
  set ε₂ : MulAction.stabilizer P₁ s₁ := ⟨ε₁, hε₁⟩ with hε₂def
  have hord : orderOf ε₂ = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      change d.omegaPermW ε ^ 3 = 1
      rw [← map_pow, hε3, map_one]
    · intro e
      apply hε₅
      have := congrArg (fun σ : MulAction.stabilizer P₁ s₁ => ((σ : P₁) : P) • s₅) e
      simp only [OneMemClass.coe_one, one_smul] at this
      exact this
  have h3 : 3 ∣ Nat.card (MulAction.stabilizer P₁ s₁) := hord ▸ orderOf_dvd_natCard ε₂
  have hc₀ := (MulAction.stabilizer P s₀).card_mul_index
  have hc₁ := (MulAction.stabilizer P₁ s₁).card_mul_index
  rw [hidx₀] at hc₀
  rw [hidx₁] at hc₁
  rw [← hc₀, ← hc₁]
  obtain ⟨m, hm⟩ := h3
  rw [hm]
  exact ⟨m * 28, by ring⟩

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
