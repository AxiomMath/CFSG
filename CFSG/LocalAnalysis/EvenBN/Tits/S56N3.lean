module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56N2
public import CFSG.LocalAnalysis.EvenBN.Tits.S56S3
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.FixedCount
public import CFSG.LocalAnalysis.EvenBN.Tits.S56SevenAll

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem s56_U11_le_F (d : Data G) : d.s56U11 ≤ d.F := (s56_U11_le_U10 d).trans (s56_U10_le_F d)

theorem Hyp.s56_F_comm (hd : d.Hyp) {a b : G} (ha : a ∈ d.F) (hb : b ∈ d.F) : a * b = b * a :=
  congrArg Subtype.val (hd.B_facts.2.2.1.1.is_comm.comm ⟨a, s56_F_le_B d ha⟩ ⟨b, s56_F_le_B d hb⟩)

theorem s56_pv11_mem_F (d : Data G) : d.pv 11 ∈ d.F :=
  s56_U10_le_F d (s56_U11_le_U10 d (s56_pv11_mem_U11 d))

theorem s56_pv11_ne_z (d : Data G) : d.pv 11 ≠ d.z := fun h =>
  Model.parrottV_ne.2.2.1 (d.lift_inj (s56_parrottV_mem_titsD (i := 11) (by omega))
    (by rw [Model.parrottV_twelve]; exact titsZ_mem_titsD) (by
      rw [← s56_pv12 d] at h; exact h))

theorem Hyp.s56_N_conj_CF_P0 (h49 : d.Thm49Statement) (hd : d.Hyp) {n w : G} (hn : n ∈ d.N)
    (hw : w ∈ d.F ⊓ centralizer (d.s56P0 : Set G)) :
    n * w * n⁻¹ ∈ d.F ⊓ centralizer (d.s56P0 : Set G) := by
  obtain ⟨hwF, hwC⟩ := mem_inf.1 hw
  refine mem_inf.2 ⟨hd.s56_N_conj_F h49 hn hwF, mem_centralizer_iff.2 fun p hp => ?_⟩
  have hp' : n⁻¹ * p * n⁻¹⁻¹ ∈ d.s56P0 := s56_N_conj_P0 d (inv_mem hn) hp
  have h := mem_centralizer_iff.1 hwC _ hp'
  calc p * (n * w * n⁻¹) = n * ((n⁻¹ * p * n⁻¹⁻¹) * w) * n⁻¹ := by group
    _ = n * (w * (n⁻¹ * p * n⁻¹⁻¹)) * n⁻¹ := by rw [h]
    _ = n * w * n⁻¹ * p := by group

theorem Hyp.s56_CF_P0_le_U11 (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.F ⊓ centralizer (d.s56P0 : Set G) ≤ d.s56U11 := by
  intro x hx
  obtain ⟨hxF, hxC⟩ := mem_inf.1 hx
  exact s56_CF_K_le_U11 hxF fun k hk =>
    (mem_centralizer_iff.1 hxC k (hd.s56_K_le_P0 h49 hk)).symm

theorem Hyp.s56_CF_P0_eq (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.F ⊓ centralizer (d.s56P0 : Set G) = d.s56U11 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hyNC, -, hy3, hy1, hy10, hy11, hy12⟩ := hd.s56_Y_facts
  have hyN : d.s56Y ∈ d.N := (mem_inf.1 hyNC).1
  have hsub := hd.s56_CF_P0_le_U11 h49
  refine le_antisymm hsub ?_
  set W : Subgroup G := d.F ⊓ centralizer (d.s56P0 : Set G) with hW
  have hWne : ∃ w ∈ W, w ≠ 1 := by
    by_contra hcon
    have hcon' : ∀ w ∈ W, w = 1 := fun w hw => by
      by_contra hne
      exact hcon ⟨w, hw, hne⟩
    have hbot : W = ⊥ := eq_bot_iff.2 fun w hw => by simpa using hcon' w hw
    have hmod := card_modEq_card_inf_centralizer (p := 2) (P := d.s56P0) (A := d.F)
      (s56_P0_isPGroup d) fun x hx a ha => hd.s56_N_conj_F h49 (s56_P0_le_N d hx) ha
    rw [hd.B_facts.1, ← hW, hbot, Subgroup.card_bot] at hmod
    exact absurd hmod (by decide)
  obtain ⟨w, hwW, hw1⟩ := hWne
  have hwU := hsub hwW
  have hyW : ∀ w ∈ W, d.s56Y * w * d.s56Y⁻¹ ∈ W := fun w hw =>
    hd.s56_N_conj_CF_P0 h49 hyN hw
  have hzv : d.z * d.pv 11 = d.pv 11 * d.z :=
    hd.s56_E_comm hd.s56_z_mem_E (s56_pv11_mem_E d)
  have hzz := hd.s56_z_sq
  have hy13 : d.s56Y * (d.pv 11 * d.z) * d.s56Y⁻¹ = d.pv 11 := by
    calc d.s56Y * (d.pv 11 * d.z) * d.s56Y⁻¹ =
        (d.s56Y * d.pv 11 * d.s56Y⁻¹) * (d.s56Y * d.z * d.s56Y⁻¹) := by group
      _ = d.z * (d.pv 11 * d.z) := by rw [hy11, hy12]
      _ = d.pv 11 * (d.z * d.z) := by rw [← mul_assoc, hzv, mul_assoc]
      _ = d.pv 11 := by rw [hzz, mul_one]
  have hall : d.pv 11 ∈ W ∧ d.z ∈ W ∧ d.pv 11 * d.z ∈ W := by
    rcases s56_mem_U11_iff.1 hwU with h | h | h | h
    · exact absurd h hw1
    · subst h
      have h2 := hyW _ hwW
      rw [hy11] at h2
      have h3 := hyW _ h2
      rw [hy12] at h3
      exact ⟨hwW, h2, h3⟩
    · subst h
      have h2 := hyW _ hwW
      rw [hy12] at h2
      have h3 := hyW _ h2
      rw [hy13] at h3
      exact ⟨h3, hwW, h2⟩
    · subst h
      have h2 := hyW _ hwW
      rw [hy13] at h2
      have h3 := hyW _ h2
      rw [hy11] at h3
      exact ⟨h2, h3, hwW⟩
  intro x hx
  rcases s56_mem_U11_iff.1 hx with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2

theorem Hyp.s56_P0_comm_U11 (h49 : d.Thm49Statement) (hd : d.Hyp) {p u : G}
    (hp : p ∈ d.s56P0) (hu : u ∈ d.s56U11) : p * u = u * p := by
  have := hd.s56_CF_P0_eq h49 ▸ hu
  exact mem_centralizer_iff.1 (mem_inf.1 this).2 p hp

theorem Hyp.s56_N_conj_U11 (h49 : d.Thm49Statement) (hd : d.Hyp) {n u : G} (hn : n ∈ d.N)
    (hu : u ∈ d.s56U11) : n * u * n⁻¹ ∈ d.s56U11 := by
  have hu' : u ∈ d.F ⊓ centralizer (d.s56P0 : Set G) := (hd.s56_CF_P0_eq h49).symm ▸ hu
  rw [← hd.s56_CF_P0_eq h49]
  exact hd.s56_N_conj_CF_P0 h49 hn hu'

theorem Hyp.s56_Y_not_comm_pv11 (hd : d.Hyp) : d.s56Y * d.pv 11 ≠ d.pv 11 * d.s56Y := by
  obtain ⟨-, -, -, -, -, hy11, -⟩ := hd.s56_Y_facts
  intro h
  apply s56_pv11_ne_z d
  rw [← hy11, h]
  group

theorem Hyp.s56_CN_U11_eq (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.N ⊓ centralizer (d.s56U11 : Set G) = d.s56P0 := by
  obtain ⟨hyNC, -, hy3, -, -, -, -⟩ := hd.s56_Y_facts
  have hyN : d.s56Y ∈ d.N := (mem_inf.1 hyNC).1
  apply le_antisymm
  · obtain ⟨e⟩ := (hd.thm511 h49).2
    set P : Subgroup ↥d.N := CFSG.pCore 2 ↥d.N with hP
    set H : Subgroup ↥d.N := (d.N ⊓ centralizer (d.s56U11 : Set G)).subgroupOf d.N with hH
    have hPH : P ≤ H := by
      intro p hp
      rw [hH, mem_subgroupOf]
      refine mem_inf.2 ⟨p.2, mem_centralizer_iff.2 fun u hu => ?_⟩
      exact (hd.s56_P0_comm_U11 h49 (s56_mem_P0_of_mem_pCore d hp) hu).symm
    have hHc : ∀ g : ↥d.N, ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
      intro g h hh
      rw [hH, mem_subgroupOf] at hh ⊢
      obtain ⟨-, hhC⟩ := mem_inf.1 hh
      refine mem_inf.2 ⟨(g * h * g⁻¹).2, mem_centralizer_iff.2 fun u hu => ?_⟩
      have hu' : (g : G)⁻¹ * u * (g : G)⁻¹⁻¹ ∈ d.s56U11 :=
        hd.s56_N_conj_U11 h49 (inv_mem g.2) hu
      have hc := mem_centralizer_iff.1 hhC _ hu'
      calc u * ((g * h * g⁻¹ : ↥d.N) : G) = (g : G) * (((g : G)⁻¹ * u * (g : G)⁻¹⁻¹) * (h : G)) *
            (g : G)⁻¹ := by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = (g : G) * ((h : G) * ((g : G)⁻¹ * u * (g : G)⁻¹⁻¹)) * (g : G)⁻¹ := by rw [hc]
        _ = ((g * h * g⁻¹ : ↥d.N) : G) * u := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    have hy3P : (⟨d.s56Y, hyN⟩ : ↥d.N) ^ 3 ∈ P := by
      have : (⟨d.s56Y, hyN⟩ : ↥d.N) ^ 3 = 1 := Subtype.ext hy3
      rw [this]; exact one_mem _
    have hyP : (⟨d.s56Y, hyN⟩ : ↥d.N) ∉ P := fun hmem => by
      have hy' : d.s56Y ∈ d.s56P0 := s56_mem_P0_of_mem_pCore d hmem
      exact hd.s56_Y_not_comm_pv11
        (hd.s56_P0_comm_U11 h49 hy' (s56_pv11_mem_U11 d))
    have hyH : (⟨d.s56Y, hyN⟩ : ↥d.N) ∉ H := fun hmem => by
      rw [hH, mem_subgroupOf] at hmem
      exact hd.s56_Y_not_comm_pv11
        (mem_centralizer_iff.1 (mem_inf.1 hmem).2 _ (s56_pv11_mem_U11 d)).symm
    have hHP : H = P := S56.eq_of_normal_of_s3 e hPH hHc hy3P hyP hyH
    intro g hg
    have hgH : (⟨g, (mem_inf.1 hg).1⟩ : ↥d.N) ∈ H := mem_subgroupOf.2 hg
    rw [hHP] at hgH
    exact s56_mem_P0_of_mem_pCore d hgH
  · intro p hp
    exact mem_inf.2 ⟨s56_P0_le_N d hp,
      mem_centralizer_iff.2 fun u hu => (hd.s56_P0_comm_U11 h49 hp hu).symm⟩

theorem s56_F_not_le_U10 (d : Data G) (hd : d.Hyp) : ¬ d.F ≤ d.s56U10 := fun h => by
  have := Subgroup.card_le_of_le h
  rw [hd.B_facts.1, s56_card_U10] at this
  omega

theorem Hyp.s56_commSub_U11_eq_U10 (h49 : d.Thm49Statement) (hd : d.Hyp) (f : G) :
    f ∈ commSub d.s56P0 d.s56U11 d.F (fun _ ha _ hb => hd.s56_F_comm ha hb) (s56_U11_le_F d) ↔
      f ∈ d.s56U10 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ŵ := commSub d.s56P0 d.s56U11 d.F (fun _ ha _ hb => hd.s56_F_comm ha hb)
    (s56_U11_le_F d) with hŴ
  have hle : ∀ f ∈ Ŵ, f ∈ d.s56U10 := fun f hf =>
    s56_comm_K_le_U10 hf.1 fun k hk => hf.2 k (hd.s56_K_le_P0 h49 hk)
  have hU11 : ∀ u ∈ d.s56U11, u ∈ Ŵ := fun u hu =>
    ⟨s56_U11_le_F d hu, fun p hp => by
      have := hd.s56_P0_comm_U11 h49 hp hu
      rw [this]; simp [one_mem]⟩
  have hFU11 : ¬ d.F ≤ d.s56U11 := fun h => by
    have := Subgroup.card_le_of_le h
    rw [hd.B_facts.1, s56_card_U11] at this
    omega
  obtain ⟨f₀, hf₀F, hf₀U, hf₀c⟩ := exists_comm_mem_of_isPGroup (p := 2) (P := d.s56P0)
    (U := d.s56U11) (V := d.F) (s56_P0_isPGroup d) hd.s56_F_le_P0
    (fun x hx u hu => hd.s56_N_conj_U11 h49 (s56_P0_le_N d hx) hu)
    (fun x hx v hv => hd.s56_N_conj_F h49 (s56_P0_le_N d hx) hv)
    hFU11
  have hf₀W : f₀ ∈ Ŵ := ⟨hf₀F, hf₀c⟩
  have hf₀10 := hle f₀ hf₀W
  have hv10 : d.pv 10 ∈ Ŵ := by
    rcases s56_U10_cases hf₀10 with h | ⟨u, hu, hu'⟩
    · exact absurd h hf₀U
    · have : d.pv 10 = f₀ * u⁻¹ := by rw [hu']; group
      rw [this]
      exact mul_mem hf₀W (inv_mem (hU11 u hu))
  constructor
  · exact hle f
  · intro hf
    rcases s56_U10_cases hf with h | ⟨u, hu, rfl⟩
    · exact hU11 f h
    · exact mul_mem hv10 (hU11 u hu)

theorem Hyp.s56_N_conj_U10 (h49 : d.Thm49Statement) (hd : d.Hyp) {n f : G} (hn : n ∈ d.N)
    (hf : f ∈ d.s56U10) : n * f * n⁻¹ ∈ d.s56U10 := by
  have hf' := (hd.s56_commSub_U11_eq_U10 h49 f).2 hf
  rw [← hd.s56_commSub_U11_eq_U10 h49]
  refine ⟨hd.s56_N_conj_F h49 hn hf'.1, fun p hp => ?_⟩
  have hp' : n⁻¹ * p * n⁻¹⁻¹ ∈ d.s56P0 := s56_N_conj_P0 d (inv_mem hn) hp
  have h := hf'.2 _ hp'
  have h2 := hd.s56_N_conj_U11 h49 hn h
  have e : n * (n⁻¹ * p * n⁻¹⁻¹ * f * (n⁻¹ * p * n⁻¹⁻¹)⁻¹ * f⁻¹) * n⁻¹ =
      p * (n * f * n⁻¹) * p⁻¹ * (n * f * n⁻¹)⁻¹ := by group
  rwa [e] at h2

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
