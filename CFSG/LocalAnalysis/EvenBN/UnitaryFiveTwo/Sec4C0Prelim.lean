module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4FusionThree
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckC0

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer
open scoped commutatorElement

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem exists_eq_ι_mul_of_comm_F
    (h : d.Hyp) {x : G} (hxH : x ∈ d.H)
    (hxF : ∀ f ∈ d.F, x * f = f * x) :
    ∃ s : SU52, (∀ z ∈ Fsub, s * z = z * s) ∧ ∃ c ∈ zpowers d.t, x = d.ι s * c := by
  have hfix : ∀ z ∈ Fsub, h.act ⟨x, hxH⟩ z = z := fun z hz => d.ι_injective (by
    rw [h.ι_act_apply]
    change x * d.ι z * x⁻¹ = d.ι z
    rw [hxF _ (d.ι_mem_pull_iff.2 hz), mul_inv_cancel_right])
  obtain ⟨s, hs | hs⟩ := exists_eq_conj_or_eq_conj_mul_fld (h.act ⟨x, hxH⟩)
  · refine ⟨s, fun z hz => ?_, ?_⟩
    · have e := hfix z hz
      rw [hs, MulAut.conj_apply] at e
      calc s * z = s * z * s⁻¹ * s := by group
        _ = z * s := by rw [e]
    · have hl : d.ι s ∈ d.H := h.L_le_H (d.ι_mem s)
      have hk : h.act (⟨d.ι s, hl⟩⁻¹ * ⟨x, hxH⟩) = 1 := by
        rw [map_mul, map_inv, h.act_ι, hs, inv_mul_cancel]
      rw [h.act_eq_one_iff] at hk
      have hk' : (d.ι s)⁻¹ * x ∈ centralizer (d.L : Set G) ⊓ d.H :=
        Subgroup.mem_inf.2 ⟨hk, mul_mem (inv_mem hl) hxH⟩
      rw [h.centralizer_inf_H_eq] at hk'
      exact ⟨_, hk', by group⟩
  · obtain ⟨z, hz, hne⟩ := exists_conj_mul_fld_ne s
    exact absurd (hs ▸ hfix z hz) hne

theorem sq_eq_one_of_mem_zpowers (h : d.Hyp) {c : G} (hc : c ∈ zpowers d.t) : c ^ 2 = 1 := by
  have := congrArg Subtype.val (pow_card_eq_one' (G := zpowers d.t) (x := ⟨c, hc⟩))
  rwa [h.card_zpowers_t] at this

theorem ι_comm_withT_F (h : d.Hyp) {s : SU52} (hs : ∀ z ∈ Fsub, s * z = z * s) {z : G}
    (hz : z ∈ d.withT d.F) : d.ι s * z = z * d.ι s := by
  obtain ⟨_, ⟨φ, hφ, rfl⟩, k, rfl⟩ := h.exists_eq_mul_of_mem_withT_F hz
  have ht : d.ι s * d.t ^ k = d.t ^ k * d.ι s :=
    (Commute.zpow_right (comm_of_mem_centralizer h.t_mem (d.ι_mem s)) k).eq
  rw [← mul_assoc, ← map_mul, hs φ hφ, map_mul, mul_assoc, ht, mul_assoc]

theorem mem_H_of_comm (_h : d.Hyp) {g : G} (hg : ∀ z ∈ d.withT d.F, g * z = z * g) :
    g ∈ d.H ∧ ∀ f ∈ d.F, g * f = f * g :=
  ⟨mem_centralizer_singleton_iff.2 (hg _ (mem_sup_right (mem_zpowers _))),
    fun f hf => hg f (mem_sup_left hf)⟩

theorem mem_withT_A₂_of_comm
    (h : d.Hyp) {g : G}
    (hg : ∀ z ∈ d.withT d.F, g * z = z * g) {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    g ∈ d.withT d.A₂ := by
  obtain ⟨hgH, hgF⟩ := h.mem_H_of_comm hg
  obtain ⟨s, hs, c, hc, rfl⟩ := h.exists_eq_ι_mul_of_comm_F hgH hgF
  have hcomm : Commute (d.ι s) c := comm_of_mem_centralizer (zpowers_le.2 h.t_mem hc) (d.ι_mem s)
  have hk' : (d.ι s * c) ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
  have hc' : c ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ', pow_mul, h.sq_eq_one_of_mem_zpowers hc, one_pow]
  rw [hcomm.mul_pow, hc', mul_one, ← map_pow] at hk'
  have hs1 : s ^ 2 ^ (k + 1) = 1 := d.ι_injective (hk'.trans (map_one _).symm)
  exact mul_mem (mem_sup_left ⟨s, mem_A₂sub_of_comm_Fsub_of_pow hs hs1, rfl⟩) (mem_sup_right hc)

theorem card_withT_A₂_eq
    (h : d.Hyp) : Nat.card (d.withT d.A₂) = 2 ^ 9 := by
  rw [h.card_withT_A₂, h.card_withT_F]
  norm_num

theorem normalizer_withT_F_eq
    (h : d.Hyp) :
    normalizer ((d.withT d.F : Subgroup G) : Set G) =
      normalizer ((d.withT d.A₂ : Subgroup G) : Set G) := by
  refine le_antisymm (fun n hn => mem_normalizer_fintype fun p hp => ?_) h.normalizer_A₂t_le
  refine h.mem_withT_A₂_of_comm (k := 9) (fun z hz => ?_) ?_
  · have hz' : n⁻¹ * z * n ∈ d.withT d.F := by
      have := (mem_normalizer_iff.1 (inv_mem hn) z).1 hz
      simpa using this
    have e := ((h.mem_center_A₂t_iff).2 hz').2 p hp
    calc n * p * n⁻¹ * z = n * (p * (n⁻¹ * z * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * z * n) * p) * n⁻¹ := by rw [e]
      _ = z * (n * p * n⁻¹) := by group
  · have h9 : p ^ 2 ^ 9 = 1 := by
      have := congrArg Subtype.val (pow_card_eq_one' (G := d.withT d.A₂) (x := ⟨p, hp⟩))
      rwa [h.card_withT_A₂_eq] at this
    rw [conj_pow, h9, mul_one, mul_inv_cancel]

theorem commutator_centralizer_eq
    (h : d.Hyp) :
    ⁅centralizer ((d.withT d.F : Subgroup G) : Set G),
      centralizer ((d.withT d.F : Subgroup G) : Set G)⁆ = d.A₂ := by
  set C := centralizer ((d.withT d.F : Subgroup G) : Set G) with hC
  have hcomm : ∀ g ∈ C, ∀ z ∈ d.withT d.F, g * z = z * g := fun g hg z hz =>
    (mem_centralizer_iff.1 hg z hz).symm
  refine le_antisymm ((commutator_le).2 fun g hg g' hg' => ?_) ?_
  · obtain ⟨hgH, hgF⟩ := h.mem_H_of_comm (hcomm g hg)
    obtain ⟨hgH', hgF'⟩ := h.mem_H_of_comm (hcomm g' hg')
    obtain ⟨s, hs, c, hc, rfl⟩ := h.exists_eq_ι_mul_of_comm_F hgH hgF
    obtain ⟨s', hs', c', hc', rfl⟩ := h.exists_eq_ι_mul_of_comm_F hgH' hgF'
    rw [commutatorElement_mul_mul_eq ((h.comm_zpowers_t hc).1 _ (d.ι_mem s')).symm
      ((h.comm_zpowers_t hc).2 c' hc') ((h.comm_zpowers_t hc').1 _ (d.ι_mem s)).symm,
      ← map_commutatorElement]
    exact d.ι_mem_pull_iff.2 (commutator_mem_A₂sub_of_comm_Fsub hs hs')
  · have hE : (zpowers e₂SU ⊔ A₂sub).map d.ι ≤ C := by
      rw [map_le_iff_le_comap]
      refine sup_le (zpowers_le.2 ?_) fun a ha => ?_
      · exact mem_centralizer_iff.2 fun z hz =>
          (h.ι_comm_withT_F (fun _ hy => e₂SU_comm_Fsub hy) hz).symm
      · exact mem_centralizer_iff.2 fun z hz =>
          (h.ι_comm_withT_F (fun _ hy => Fsub_comm_A₂ ha hy) hz).symm
    calc d.A₂ = A₂sub.map d.ι := rfl
      _ ≤ (⁅zpowers e₂SU ⊔ A₂sub, zpowers e₂SU ⊔ A₂sub⁆).map d.ι := map_mono A₂sub_le_commutator
      _ = ⁅(zpowers e₂SU ⊔ A₂sub).map d.ι, (zpowers e₂SU ⊔ A₂sub).map d.ι⁆ := map_commutator _ _ _
      _ ≤ ⁅C, C⁆ := commutator_mono hE hE

theorem normalizer_withT_F_le
    (h : d.Hyp) :
    normalizer ((d.withT d.F : Subgroup G) : Set G) ≤ normalizer (d.A₂ : Set G) := by
  intro n hn
  refine mem_normalizer_fintype fun a ha => ?_
  set C := centralizer ((d.withT d.F : Subgroup G) : Set G) with hC
  rw [← h.commutator_centralizer_eq] at ha ⊢
  have hCn : C.map (MulAut.conj n).toMonoidHom ≤ C := by
    rintro _ ⟨g, hg, rfl⟩
    refine mem_centralizer_iff.2 fun z hz => ?_
    have hz' : n⁻¹ * z * n ∈ d.withT d.F := by
      have := (mem_normalizer_iff.1 (inv_mem hn) z).1 hz
      simpa using this
    have e := mem_centralizer_iff.1 hg _ hz'
    change z * (n * g * n⁻¹) = n * g * n⁻¹ * z
    calc z * (n * g * n⁻¹) = n * ((n⁻¹ * z * n) * g) * n⁻¹ := by group
      _ = n * (g * (n⁻¹ * z * n)) * n⁻¹ := by rw [e]
      _ = n * g * n⁻¹ * z := by group
  have := mem_map_of_mem (MulAut.conj n).toMonoidHom ha
  rw [map_commutator] at this
  exact commutator_mono hCn hCn this

theorem withT_A₂_le_X₀
    (h : d.Hyp) : d.withT d.A₂ ≤ X₀ d := by
  intro p hp
  refine ⟨⟨p, (d.withT d.A₂).le_normalizer hp⟩, ?_, rfl⟩
  change secHom (d.withT d.A₂) ⟨p, (d.withT d.A₂).le_normalizer hp⟩ = 1
  rw [secHom_eq_one_iff]
  intro q hq r hr
  exact ((h.mem_center_A₂t_iff).2 ((h.section_hyps).1 p hp q hq)).2 r hr

theorem mem_withT_A₂_of_mem_X₀
    (h : d.Hyp) {x : G} (hx : x ∈ X₀ d) (hxH : x ∈ d.H) :
    x ∈ d.withT d.A₂ := by
  obtain ⟨s, hs, c, hc, rfl⟩ :=
    h.exists_eq_ι_mul_of_comm_F hxH fun f hf => h.comm_F_of_mem_X₀ hx hf
  obtain ⟨k, hk⟩ := exists_e₂_pow_mul_mem_A₂sub hs
  have hP : d.ι (e₂SU ^ k * s) * c ∈ d.withT d.A₂ :=
    mul_mem (mem_sup_left ⟨_, hk, rfl⟩) (mem_sup_right hc)
  have he : d.ι (e₂SU ^ k) = d.ι (e₂SU ^ k * s) * c * (d.ι s * c)⁻¹ := by
    rw [map_mul]
    group
  have h1 : d.ι (e₂SU ^ k) ∈ d.pull Esub ⊓ X₀ d :=
    Subgroup.mem_inf.2 ⟨⟨_, pow_mem (mem_sup_right (mem_zpowers _)) k, rfl⟩, by
      rw [he]
      exact mul_mem (h.withT_A₂_le_X₀ hP) (inv_mem hx)⟩
  rw [h.torus_inf_X₀, mem_bot] at h1
  have hk1 : e₂SU ^ k = 1 := d.ι_injective (h1.trans (map_one _).symm)
  rw [hk1, one_mul] at hk
  exact mul_mem (mem_sup_left ⟨s, hk, rfl⟩) (mem_sup_right hc)

theorem X₀_inf_H_eq
    (h : d.Hyp) : X₀ d ⊓ d.H = d.withT d.A₂ :=
  le_antisymm (fun _ hx => h.mem_withT_A₂_of_mem_X₀ (Subgroup.mem_inf.1 hx).1
    (Subgroup.mem_inf.1 hx).2)
    (le_inf h.withT_A₂_le_X₀ (sup_le ((d.pull_le_L _).trans h.L_le_H) (zpowers_le.2 h.t_mem_H)))

theorem ι_mem_normalizer
    (h : d.Hyp) {s : SU52}
    (hs : ∀ a ∈ A₂sub, s * a * s⁻¹ ∈ A₂sub) :
    d.ι s ∈ normalizer ((d.withT d.A₂ : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun p hp => ?_
  obtain ⟨_, ⟨α, hα, rfl⟩, c, hc, rfl⟩ := h.exists_eq_mul_of_mem_withT_A₂ hp
  have hct : d.ι s * c * (d.ι s)⁻¹ = c := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (h.comm_zpowers_t hc).1 _ (d.ι_mem s)
  rw [show d.ι s * (d.ι α * c) * (d.ι s)⁻¹ = d.ι s * d.ι α * (d.ι s)⁻¹ * (d.ι s * c * (d.ι s)⁻¹) by
    group, hct, ι_conj]
  exact mul_mem (mem_sup_left (d.ι_mem_pull_iff.2 (hs α hα))) (mem_sup_right hc)

theorem normalizer_inf_H_eq
    (h : d.Hyp) :
    normalizer ((d.withT d.A₂ : Subgroup G) : Set G) ⊓ d.H =
      normalizer (d.A₂ : Set G) ⊓ d.H := by
  ext x
  refine ⟨fun hx => ⟨?_, (Subgroup.mem_inf.1 hx).2⟩, fun hx => ⟨?_, (Subgroup.mem_inf.1 hx).2⟩⟩
  · exact h.normalizer_withT_F_le ((h.normalizer_withT_F_eq).symm ▸ (Subgroup.mem_inf.1 hx).1)
  · obtain ⟨hxN, hxH⟩ := Subgroup.mem_inf.1 hx
    refine mem_normalizer_fintype fun p hp => ?_
    obtain ⟨a, ha, c, hc, rfl⟩ := h.exists_eq_mul_of_mem_withT_A₂ hp
    have hct : x * c * x⁻¹ = c := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      rw [mul_inv_eq_iff_eq_mul]
      exact (Commute.zpow_right (mem_centralizer_singleton_iff.1 hxH) k).eq
    rw [show x * (a * c) * x⁻¹ = x * a * x⁻¹ * (x * c * x⁻¹) by group, hct]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hxN a).1 ha)) (mem_sup_right hc)

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
