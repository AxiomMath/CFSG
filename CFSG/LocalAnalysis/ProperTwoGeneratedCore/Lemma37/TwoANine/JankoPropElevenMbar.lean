module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenBasic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar
open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {fr : JankoFrame G z}

theorem eq_one_of_conj_eq_self_of_conj_eq_inv {u x : G} (hx : x ^ 3 = 1)
    (h1 : u * x * u⁻¹ = x) (h2 : u * x * u⁻¹ = x⁻¹) : x = 1 := by
  have h3 : x * x = 1 := by
    nth_rewrite 2 [← h1]
    rw [h2, mul_inv_cancel]
  have h4 : x ^ 3 = x := by rw [pow_succ, pow_two, h3, one_mul]
  rw [← h4, hx]

theorem At_comm (p10 : JankoProp10 fr) : ∀ a ∈ fr.At, ∀ b ∈ fr.At, a * b = b * a :=
  fun a ha b hb => p10.M_comm a ha.1 b hb.1

theorem Atz_comm (p10 : JankoProp10 fr) : ∀ a ∈ fr.Atz, ∀ b ∈ fr.Atz, a * b = b * a :=
  fun a ha b hb => p10.M_comm a ha.1 b hb.1

theorem mem_normalizer_At {g : G} (hgM : g ∈ normalizer (fr.M : Set G))
    (hgt : g * fr.t = fr.t * g) : g ∈ normalizer (fr.At : Set G) :=
  inf_mem_normalizer hgM (mem_normalizer_centralizer_singleton hgt)

theorem mem_normalizer_Atz {g : G} (hgM : g ∈ normalizer (fr.M : Set G))
    (hgt : g * (fr.t * z) = fr.t * z * g) : g ∈ normalizer (fr.Atz : Set G) :=
  inf_mem_normalizer hgM (mem_normalizer_centralizer_singleton hgt)

theorem z_comm_tz : z * (fr.t * z) = fr.t * z * z := by
  rw [← mul_assoc, ← t_comm_z]

theorem Atz_inf_centralizer_z (p10 : JankoProp10 fr) :
    fr.Atz ⊓ centralizer ({z} : Set G) = ⊥ := by
  rw [eq_bot_iff, ← p10.At_inf_centralizer_z]
  rintro x ⟨⟨hxM, hx1⟩, hx2⟩
  refine ⟨⟨hxM, mem_centralizer_singleton_iff.mpr ?_⟩, hx2⟩
  replace hx1 : x * (fr.t * z) = fr.t * z * x := mem_centralizer_singleton_iff.mp hx1
  replace hx2 : x * z = z * x := mem_centralizer_singleton_iff.mp hx2
  calc x * fr.t = x * (fr.t * z) * z⁻¹ := by group
    _ = fr.t * z * x * z⁻¹ := by rw [hx1]
    _ = fr.t * (z * x) * z⁻¹ := by group
    _ = fr.t * (x * z) * z⁻¹ := by rw [hx2]
    _ = fr.t * x := by group

theorem At_inf_Atz (p10 : JankoProp10 fr) : fr.At ⊓ fr.Atz = ⊥ := by
  rw [eq_bot_iff, ← p10.At_inf_centralizer_z]
  rintro x ⟨⟨hxM, hx1⟩, ⟨-, hx2⟩⟩
  refine ⟨⟨hxM, hx1⟩, mem_centralizer_singleton_iff.mpr ?_⟩
  replace hx1 : x * fr.t = fr.t * x := mem_centralizer_singleton_iff.mp hx1
  replace hx2 : x * (fr.t * z) = fr.t * z * x := mem_centralizer_singleton_iff.mp hx2
  calc x * z = fr.t⁻¹ * (fr.t * x) * z := by group
    _ = fr.t⁻¹ * (x * fr.t) * z := by rw [hx1]
    _ = fr.t⁻¹ * (x * (fr.t * z)) := by group
    _ = fr.t⁻¹ * (fr.t * z * x) := by rw [hx2]
    _ = z * x := by group

theorem inv_of_mem_At (p10 : JankoProp10 fr) (hz : orderOf z = 2) {a : G} (ha : a ∈ fr.At) :
    z * a * z⁻¹ = a⁻¹ :=
  conj_eq_inv_of_inf_eq_bot (At_comm p10) (z_mul_z hz)
    (fun _ hb => conj_mem_of_mem_normalizer
      (mem_normalizer_At z_mem_normalizer_M t_comm_z.symm) hb) p10.At_inf_centralizer_z ha

theorem inv_of_mem_Atz (p10 : JankoProp10 fr) (hz : orderOf z = 2) {a : G} (ha : a ∈ fr.Atz) :
    z * a * z⁻¹ = a⁻¹ :=
  conj_eq_inv_of_inf_eq_bot (Atz_comm p10) (z_mul_z hz)
    (fun _ hb => conj_mem_of_mem_normalizer
      (mem_normalizer_Atz z_mem_normalizer_M z_comm_tz) hb) (Atz_inf_centralizer_z p10) ha

theorem Mbar_le_M : fr.Mbar ≤ fr.M := sup_le inf_le_left inf_le_left

theorem At_le_Mbar : fr.At ≤ fr.Mbar := le_sup_left

theorem Atz_le_Mbar : fr.Atz ≤ fr.Mbar := le_sup_right

theorem inv_of_mem_Mbar (p10 : JankoProp10 fr) (hz : orderOf z = 2) {x : G}
    (hx : x ∈ fr.Mbar) : z * x * z⁻¹ = x⁻¹ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm p10.M_comm (inf_le_left : fr.At ≤ fr.M)
      (inf_le_left : fr.Atz ≤ fr.M)) hx
  rw [conj_mul_conj, inv_of_mem_At p10 hz ha, inv_of_mem_Atz p10 hz hb, mul_inv_rev]
  exact p10.M_comm _ (inv_mem ha.1) _ (inv_mem hb.1)

theorem mem_Mbar_of_inv [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {x : G} (hxM : x ∈ fr.M) (hx : z * x * z⁻¹ = x⁻¹) : x ∈ fr.Mbar := by
  obtain ⟨b, hbM, c, hcM, hb, hc, rfl⟩ := exists_fixed_mul_inverted p10.M_comm t_mul_t
    (fun _ ha => conj_mem_of_mem_normalizer (t_mem_normalizer_M p7) ha) hxM (p10.M_pow_three x hxM)
  have hbAt : b ∈ fr.At := ⟨hbM, mem_centralizer_singleton_iff_conj.mpr hb⟩
  have hzc : z * c * z⁻¹ = c⁻¹ := by
    have h1 : z * b * z⁻¹ = b⁻¹ := inv_of_mem_At p10 hz hbAt
    have h3 : z * c * z⁻¹ = b * (b * c)⁻¹ := by
      calc z * c * z⁻¹ = (z * b * z⁻¹)⁻¹ * (z * (b * c) * z⁻¹) := by group
        _ = b * (b * c)⁻¹ := by rw [h1, hx, inv_inv]
    rw [h3, mul_inv_rev, ← mul_assoc, p10.M_comm b hbM _ (inv_mem hcM), mul_assoc,
      mul_inv_cancel, mul_one]
  have hcAtz : c ∈ fr.Atz := by
    refine ⟨hcM, mem_centralizer_singleton_iff_conj.mpr ?_⟩
    calc fr.t * z * c * (fr.t * z)⁻¹ = fr.t * (z * c * z⁻¹) * fr.t⁻¹ := by group
      _ = c := by rw [hzc, conj_inv_conj, hc, inv_inv]
  exact mul_mem_sup hbAt hcAtz

theorem mem_Mbar_iff [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {x : G} : x ∈ fr.Mbar ↔ x ∈ fr.M ∧ z * x * z⁻¹ = x⁻¹ :=
  ⟨fun hx => ⟨Mbar_le_M hx, inv_of_mem_Mbar p10 hz hx⟩,
    fun hx => mem_Mbar_of_inv p7 p10 hz hx.1 hx.2⟩

theorem P₁_inf_Mbar (p10 : JankoProp10 fr) (hz : orderOf z = 2) : fr.P₁ ⊓ fr.Mbar = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  have hxE : x ∈ fr.E := P₁_le_E hx1
  refine eq_one_of_conj_eq_self_of_conj_eq_inv (fr.E_pow_three x hxE) ?_
    (inv_of_mem_Mbar p10 hz hx2)
  exact mem_centralizer_singleton_iff_conj.mp (fr.E_le hxE)

theorem card_Mbar (p10 : JankoProp10 fr) : Nat.card fr.Mbar = 81 := by
  have h := card_sup_mul_card_inf (X := fr.At) (Y := fr.Atz)
    (le_normalizer_of_comm p10.M_comm (inf_le_left : fr.At ≤ fr.M)
      (inf_le_left : fr.Atz ≤ fr.M))
  rw [At_inf_Atz p10, Subgroup.card_bot, p10.card_At, p10.card_Atz] at h
  change Nat.card fr.Mbar * 1 = 9 * 9 at h
  omega

theorem exists_P₁_mul_Mbar [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {m : G} (hm : m ∈ fr.M) : ∃ p ∈ fr.P₁, ∃ a ∈ fr.Mbar, p * a = m := by
  obtain ⟨b, hbM, c, hcM, hb, hc, rfl⟩ := exists_fixed_mul_inverted p10.M_comm (z_mul_z hz)
    (fun _ ha => conj_mem_of_mem_normalizer z_mem_normalizer_M ha) hm (p10.M_pow_three _ hm)
  refine ⟨b, ?_, c, mem_Mbar_of_inv p7 p10 hz hcM hc, rfl⟩
  rw [← p10.M_inf_centralizer_z]
  exact ⟨hbM, mem_centralizer_singleton_iff_conj.mpr hb⟩

theorem mem_normalizer_Mbar [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {g : G} (hgM : g ∈ normalizer (fr.M : Set G)) (hgz : g * z = z * g) :
    g ∈ normalizer (fr.Mbar : Set G) := by
  refine mem_normalizer_of_conj_mem fun a ha => ?_
  rw [mem_Mbar_iff p7 p10 hz] at ha ⊢
  refine ⟨conj_mem_of_mem_normalizer hgM ha.1, ?_⟩
  calc z * (g * a * g⁻¹) * z⁻¹ = (z * g) * a * (z * g)⁻¹ := by group
    _ = g * (z * a * z⁻¹) * g⁻¹ := by rw [← hgz]; group
    _ = (g * a * g⁻¹)⁻¹ := by rw [ha.2, conj_inv_conj]

theorem M_le_normalizer_Mbar (p10 : JankoProp10 fr) : fr.M ≤ normalizer (fr.Mbar : Set G) :=
  le_normalizer_of_comm p10.M_comm le_rfl Mbar_le_M

theorem normalizer_P₁_le_normalizer_Mbar [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : normalizer (fr.P₁ : Set G) ≤ normalizer (fr.Mbar : Set G) := by
  rw [p7.normalizer_P₁, p10.centralizer_P₁]
  refine sup_le (sup_le (M_le_normalizer_Mbar p10) fun f hf => ?_) (zpowers_le.mpr ?_)
  · exact mem_normalizer_Mbar p7 p10 hz
      (centralizer_P₁_le_normalizer_M (fr.F_le_centralizer hf))
      (mem_centralizer_singleton_iff.mp (fr.F_le hf))
  · exact mem_normalizer_Mbar p7 p10 hz (t_mem_normalizer_M p7) t_comm_z

theorem commutator_mem_Mbar [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {m w : G} (hm : m ∈ fr.M) (hw : w ∈ centralizer (fr.P₁ : Set G))
    (hwz : w * z = z * w) : ⁅m, w⁆ ∈ fr.Mbar := by
  obtain ⟨p, hp, a, ha, rfl⟩ := exists_P₁_mul_Mbar p7 p10 hz hm
  have hwM : w ∈ normalizer (fr.M : Set G) := centralizer_P₁_le_normalizer_M hw
  have hwMbar := mem_normalizer_Mbar p7 p10 hz hwM hwz
  have haw : ⁅a, w⁆ ∈ fr.Mbar := by
    have h : ⁅a, w⁆ = a * (w * a⁻¹ * w⁻¹) := by rw [commutatorElement_def]; group
    rw [h]
    exact mul_mem ha (conj_mem_of_mem_normalizer hwMbar (inv_mem ha))
  have hpw : ⁅p, w⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp hw p hp
  have hpM : p ∈ fr.M := p10.P₁_le_M hp
  rw [commutatorElement_mul_left_eq_conj_mul, hpw, mul_one,
    p10.M_comm p hpM _ (Mbar_le_M haw), mul_inv_cancel_right]
  exact haw

theorem ZN_le_N : fr.ZN ≤ fr.N := inf_le_left

theorem comm_of_mem_ZN {x n : G} (hx : x ∈ fr.ZN) (hn : n ∈ fr.N) : n * x = x * n :=
  Subgroup.mem_centralizer_iff.mp hx.2 n hn

theorem ZN_le_M (p10 : JankoProp10 fr) : fr.ZN ≤ fr.M := by
  rw [← p10.centralizer_M]
  intro x hx
  refine ⟨Subgroup.mem_centralizer_iff.mpr fun m hm => comm_of_mem_ZN hx (M_le_N hm),
    N_le_centralizer_P₁ hx.1⟩

theorem P₁_le_ZN : fr.P₁ ≤ fr.ZN :=
  le_inf (P₁_le_E.trans E_le_N) (Subgroup.le_centralizer_iff.mp N_le_centralizer_P₁)

theorem mem_ZN_of_mem_M (p10 : JankoProp10 fr) {m : G} (hm : m ∈ fr.M)
    (hE : ∀ e ∈ fr.E, e * m = m * e) : m ∈ fr.ZN := by
  refine ⟨M_le_N hm, Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
  have hle : fr.N ≤ centralizer ({m} : Set G) := sup_le
    (fun e he => mem_centralizer_singleton_iff.mpr (hE e he))
    (fun m' hm' => mem_centralizer_singleton_iff.mpr (p10.M_comm m' hm' m hm))
  exact mem_centralizer_singleton_iff.mp (hle hn)

theorem mem_normalizer_ZN {g : G} (hg : g ∈ normalizer (fr.N : Set G)) :
    g ∈ normalizer (fr.ZN : Set G) :=
  inf_mem_normalizer hg (mem_normalizer_centralizer hg)

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven
