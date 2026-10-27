module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Iso
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Glue

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.Burgoyne
open scoped Pointwise

theorem eq_bot_of_odd_normal_prod {M : Type*} [Group M] [Finite M] {Z L C : Subgroup M}
    (hsup : Z ⊔ L = C) (hdisj : Disjoint Z L) (hcomm : Z ≤ centralizer (L : Set M))
    (hZ : ∀ h ∈ Z, h * h = 1) (hL : IsSimpleGroup ↥L) (hL2 : ∃ x ∈ L, orderOf x = 2)
    {Nm : Subgroup M} (hNC : Nm ≤ C) (hNn : ∀ c ∈ C, ∀ n ∈ Nm, c * n * c⁻¹ ∈ Nm)
    (hodd : Odd (Nat.card ↥Nm)) : Nm = ⊥ := by
  have hoddord : ∀ n ∈ Nm, Odd (orderOf n) := by
    intro n hn
    have h1 : orderOf n ∣ Nat.card Nm := by
      have := Subgroup.orderOf_dvd_natCard Nm hn
      simpa using this
    exact Odd.of_dvd_nat hodd h1
  have hNL : Nm ≤ L := by
    intro n hn
    have hnC : n ∈ (Z ⊔ L : Subgroup M) := hsup ▸ hNC hn
    have hset : ((Z ⊔ L : Subgroup M) : Set M) = (Z : Set M) * (L : Set M) :=
      Subgroup.coe_mul_of_left_le_normalizer_right Z L
        (hcomm.trans (Subgroup.centralizer_le_normalizer _))
    rw [← SetLike.mem_coe, hset] at hnC
    obtain ⟨h, hh, l, hl, rfl⟩ := hnC
    have hhl : Commute h l := Subgroup.mem_centralizer_iff.mp (hcomm hh) l hl |>.symm
    obtain ⟨k, hk⟩ := hoddord _ hn
    have h1 : (h * l) ^ orderOf (h * l) = 1 := pow_orderOf_eq_one _
    rw [hk, hhl.mul_pow] at h1
    have h2 : h ^ (2 * k + 1) = h := by
      rw [pow_succ, pow_mul, pow_two, hZ h hh, one_pow, one_mul]
    rw [h2] at h1
    have h3 : h = (l ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h4 : h ∈ L := by rw [h3]; exact L.inv_mem (L.pow_mem hl _)
    have h5 : h = 1 := Subgroup.disjoint_def.mp hdisj hh h4
    show h * l ∈ L
    rw [h5, one_mul]
    exact hl
  have hNormL : (Nm.subgroupOf L).Normal := by
    refine ⟨fun n hn d => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hdC : (d : M) ∈ C := hsup ▸ (le_sup_right : L ≤ Z ⊔ L) d.2
    exact hNn _ hdC _ hn
  rcases hL.eq_bot_or_eq_top_of_normal (Nm.subgroupOf L) with hbot | htop
  · rw [eq_bot_iff]
    intro n hn
    have : (⟨n, hNL hn⟩ : ↥L) ∈ Nm.subgroupOf L := hn
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    obtain ⟨x, hxL, hx2⟩ := hL2
    have hxN : x ∈ Nm := by
      have : (⟨x, hxL⟩ : ↥L) ∈ Nm.subgroupOf L := by rw [htop]; exact Subgroup.mem_top _
      exact this
    have := hoddord x hxN
    rw [hx2] at this
    exact absurd this (by decide)

section Crit

variable {Γ : Type} [Group Γ]

theorem mem_inner_iff' (α : MulAut Γ) :
    α ∈ OuterAutomorphisms.inner Γ ↔ ∃ g : Γ, MulAut.conj g = α := Iff.rfl

theorem mem_inner_of_sq_eq_one [Finite Γ] (hodd : Odd (Nat.card (Outer Γ))) {t : MulAut Γ}
    (ht : t * t = 1) : t ∈ OuterAutomorphisms.inner Γ := by
  have h2 : (QuotientGroup.mk t : Outer Γ) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, pow_two, ht, QuotientGroup.mk_one]
  have h3 : orderOf (QuotientGroup.mk t : Outer Γ) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h4 : orderOf (QuotientGroup.mk t : Outer Γ) ∣ Nat.card (Outer Γ) := orderOf_dvd_natCard _
  have h5 : orderOf (QuotientGroup.mk t : Outer Γ) = 1 := by
    have hc : Nat.Coprime 2 (Nat.card (Outer Γ)) := (Nat.coprime_two_left).mpr hodd
    exact Nat.eq_one_of_dvd_coprimes hc h3 h4 |> fun h => by simpa using h
  exact (QuotientGroup.eq_one_iff t).mp (orderOf_eq_one_iff.mp h5)

theorem oddCoreCyclic_of_outCyc [Finite Γ] (hZ : Subgroup.center Γ = ⊥)
    (hcyc : IsCyclic (Outer Γ)) (hodd : Odd (Nat.card (Outer Γ)))
    (hC : ∀ s : Γ, orderOf s = 2 → ∀ N : Subgroup Γ, N ≤ centralizer ({s} : Set Γ) →
      (N.subgroupOf (centralizer ({s} : Set Γ))).Normal → Odd (Nat.card ↥N) → N = ⊥) :
    OddCoreCyclic Γ := by
  intro B hB t htB ht
  have hinj := conj_injective_of_center_eq_bot hZ
  have htt : t * t = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ht])
  obtain ⟨s, hst⟩ := (mem_inner_iff' t).mp (mem_inner_of_sq_eq_one hodd htt)
  subst hst
  have hs : orderOf s = 2 := by rw [← ht]; exact (orderOf_injective _ hinj s).symm
  set W : Subgroup (MulAut Γ) := oddCoreIn B (MulAut.conj s) with hW
  set C : Subgroup (MulAut Γ) := B ⊓ centralizer ({MulAut.conj s} : Set (MulAut Γ)) with hCdef
  have hWodd : Nat.Coprime 2 (Nat.card W) := by
    rw [hW]
    unfold oddCoreIn
    rw [card_map_of_injective (subtype_injective _)]
    exact pPrimeCore_coprime_card
  have hWnorm : ∀ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    obtain ⟨x, hx, rfl⟩ := hw
    have := (pPrimeCore_normal (p := 2) (G := ↥C)).conj_mem x hx ⟨c, hc⟩
    exact ⟨⟨c, hc⟩ * x * ⟨c, hc⟩⁻¹, this, rfl⟩
  have hker : W ⊓ OuterAutomorphisms.inner Γ = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwW, g, rfl⟩
    set N : Subgroup Γ := W.comap (MulAut.conj : Γ →* MulAut Γ) with hN
    have hNs : N ≤ centralizer ({s} : Set Γ) := by
      intro n hn
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := commute_of_mem_oddCoreIn hn
      apply hinj
      rw [map_mul, map_mul]
      exact h1
    have hNnorm : (N.subgroupOf (centralizer ({s} : Set Γ))).Normal := by
      refine ⟨fun n hn d => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hds : (d : Γ) * s = s * (d : Γ) := Subgroup.mem_centralizer_singleton_iff.mp d.2
      have hdcen : MulAut.conj (d : Γ) ∈ centralizer ({MulAut.conj s} : Set (MulAut Γ)) := by
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hds]
      have hdc : (MulAut.conj (d : Γ)) ∈ C := ⟨hB ⟨d, rfl⟩, hdcen⟩
      have := hWnorm _ hdc _ hn
      show MulAut.conj ((d : Γ) * n * (d : Γ)⁻¹) ∈ W
      simpa [map_mul, map_inv] using this
    have hNodd : Odd (Nat.card N) := by
      have h1 : Nat.card N ∣ Nat.card W := by
        have hmap : Nat.card (N.map (MulAut.conj : Γ →* MulAut Γ)) = Nat.card N :=
          Subgroup.card_map_of_injective hinj
        rw [← hmap]
        exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
      exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h1 hWodd)
    have hNbot := hC s hs N hNs hNnorm hNodd
    have hg : g ∈ N := hwW
    rw [hNbot, Subgroup.mem_bot] at hg
    rw [hg, map_one]
    exact Subgroup.one_mem _
  have := hcyc
  refine isCyclic_of_injective ((QuotientGroup.mk' (OuterAutomorphisms.inner Γ)).comp W.subtype) ?_
  rw [injective_iff_map_eq_one]
  intro w hw
  have hw' : (w : MulAut Γ) ∈ OuterAutomorphisms.inner Γ := (QuotientGroup.eq_one_iff _).mp hw
  have : (w : MulAut Γ) ∈ W ⊓ OuterAutomorphisms.inner Γ := ⟨w.2, hw'⟩
  rw [hker, Subgroup.mem_bot] at this
  exact Subtype.ext this

end Crit

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
