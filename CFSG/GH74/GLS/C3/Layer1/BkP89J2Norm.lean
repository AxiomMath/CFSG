module

public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Setup
public import CFSG.Walter.W67.Section6.Util

public section

namespace CFSG.GH74.GLS.Th2.P85.Sp

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.TwoThin
open CFSG.GH74.GLS.C3.Layer1.Bk.J2C
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_eq_card_imgM_mul {M H : Subgroup G} (hHM : H ≤ M) :
    Nat.card ↥H = Nat.card ↥(imgM M H) * Nat.card ↥(H ⊓ pPrimeCoreOf 2 M) := by
  have h1 := Subgroup.card_ker_mul_card_range (toImgM hHM)
  rw [(toImgM hHM).range_eq_top_of_surjective (toImgM_surjective hHM), Subgroup.card_top] at h1
  have h2 : Nat.card (toImgM hHM).ker = Nat.card ↥(H ⊓ pPrimeCoreOf 2 M) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨k.1.1, k.1.2, (mem_ker_toImgM hHM k.1).1 k.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, (mem_ker_toImgM hHM ⟨x.1, x.2.1⟩).2 x.2.2⟩
        left_inv := fun k => rfl
        right_inv := fun x => rfl }
  rw [← h2, mul_comm]
  exact h1.symm

namespace P89Std

variable {M W Q : Subgroup G} {v : G} {Ebar : Subgroup (Mb M)}
variable (h : P89Std M W Q v Ebar)
include h

theorem normalizer_W0_le_cent : normalizer (W0 M W Ebar : Set G) ≤ centralizer ({v} : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hnv : n * v * n⁻¹ ∈ W0 M W Ebar := (Subgroup.mem_normalizer_iff.1 hn v).1 h.v_mem_W0
  have hcen : ∀ y ∈ W0 M W Ebar, (n * v * n⁻¹) * y = y * (n * v * n⁻¹) := by
    intro y hy
    have hy' : n⁻¹ * y * n ∈ W0 M W Ebar := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) y).1 hy
      simpa using this
    have hc := h.v_cent _ (W0_le_W hy')
    calc n * v * n⁻¹ * y = n * (v * (n⁻¹ * y * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * y * n) * v) * n⁻¹ := by rw [hc]
      _ = y * (n * v * n⁻¹) := by group
  rcases h.W0_center _ hnv hcen with h1 | h1
  · exfalso
    have hv1 : v = 1 := by
      have h2 : v = n⁻¹ * (n * v * n⁻¹) * n := by group
      rw [h1] at h2
      simpa using h2
    have hv2 := h.v_two
    rw [hv1, orderOf_one] at hv2
    omega
  · exact mul_inv_eq_iff_eq_mul.1 h1

@[expose] def H0 (M : Subgroup G) (Ebar : Subgroup (Mb M)) (v : G) : Subgroup G :=
  centralizer ({v} : Set G) ⊓ preimgM M Ebar

omit [Finite G] h in
theorem H0_le_M : H0 M Ebar v ≤ M := inf_le_right.trans preimgM_le

omit [Finite G] in
theorem W0_le_H0 : W0 M W Ebar ≤ H0 M Ebar v := by
  intro x hx
  obtain ⟨hxW, hxM, hxE⟩ := mem_W0_iff.1 hx
  exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (h.v_cent x hxW).symm,
    mem_preimgM_iff.2 ⟨hxM, hxE⟩⟩

theorem imgM_H0 : imgM M (H0 M Ebar v) = Ebar := by
  apply le_antisymm
  · intro e he
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 he
    obtain ⟨-, hm2⟩ := hm
    obtain ⟨hmM, hmE⟩ := mem_preimgM_iff.1 hm2
    exact hmE
  · have := imgM_mono (M := M) h.W0_le_H0
    rwa [h.imgM_W0] at this

theorem card_W0_eq_sylow_H0 :
    Nat.card ↥(W0 M W Ebar) = 2 ^ (Nat.card ↥(H0 M Ebar v)).factorization 2 := by
  rw [card_eq_card_imgM_mul (M := M) (H0_le_M), h.imgM_H0, h.facts.card_E,
    Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply]
  have hodd : Odd (Nat.card ↥(H0 M Ebar v ⊓ pPrimeCoreOf 2 M)) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd M) (Subgroup.card_dvd_of_le inf_le_right)
  rw [C3.Layer1.Back.Setup91.factorization_two_of_odd hodd, h.card_W0]
  have : (32 : ℕ) = 2 ^ 5 := by norm_num
  rw [this, Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem imgM_N0 :
    imgM M (normalizer (W0 M W Ebar : Set G) ⊓ M) = centralizer ({h.vb} : Set (Mb M)) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hy
    have hmC := h.normalizer_W0_le_cent (Subgroup.mem_inf.1 hm).1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmv : (m : G) * v = v * m := Subgroup.mem_centralizer_singleton_iff.1 hmC
    show barMk ↥M m * barMk ↥M ⟨v, h.v_mem_M⟩ = barMk ↥M ⟨v, h.v_mem_M⟩ * barMk ↥M m
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hmv
  · intro cb hcb
    have hvM2 : orderOf (⟨v, h.v_mem_M⟩ : ↥M) = 2 :=
      (Subgroup.orderOf_mk v h.v_mem_M).trans h.v_two
    have hcb' : cb ∈ (centralizer ({(⟨v, h.v_mem_M⟩ : ↥M)} : Set ↥M)).map (barMk ↥M) := by
      rw [map_centralizer_barMk hvM2]
      exact hcb
    obtain ⟨c, hcC, rfl⟩ := Subgroup.mem_map.1 hcb'
    have hcv : (c : G) * v = v * c :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hcC)
    have hcmem : (c : G) ∈ normalizer (H0 M Ebar v : Set G) := by
      refine CFSG.GH74.Generic.S45.EvSpor.mem_normalizer_of_conj_le fun x hx => ?_
      obtain ⟨hxC, hxP⟩ := hx
      obtain ⟨hxM, hxE⟩ := mem_preimgM_iff.1 hxP
      have hxv : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.1 hxC
      have hM : (c : G) * x * (c : G)⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem c.2 hxM) (M.inv_mem c.2)
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, mem_preimgM_iff.2 ⟨hM, ?_⟩⟩
      · calc (c : G) * x * (c : G)⁻¹ * v = (c : G) * x * ((c : G)⁻¹ * v) := by group
          _ = (c : G) * x * (v * (c : G)⁻¹) := by
            congr 1
            calc (c : G)⁻¹ * v = (c : G)⁻¹ * (v * c) * (c : G)⁻¹ := by group
              _ = (c : G)⁻¹ * ((c : G) * v) * (c : G)⁻¹ := by rw [hcv]
              _ = v * (c : G)⁻¹ := by group
          _ = (c : G) * (x * v) * (c : G)⁻¹ := by group
          _ = (c : G) * (v * x) * (c : G)⁻¹ := by rw [hxv]
          _ = v * ((c : G) * x * (c : G)⁻¹) := by
            calc (c : G) * (v * x) * (c : G)⁻¹ = ((c : G) * v) * x * (c : G)⁻¹ := by group
              _ = (v * c) * x * (c : G)⁻¹ := by rw [hcv]
              _ = v * ((c : G) * x * (c : G)⁻¹) := by group
      · have h1 : (⟨(c : G) * x * (c : G)⁻¹, hM⟩ : ↥M) = c * ⟨x, hxM⟩ * c⁻¹ := rfl
        rw [h1, map_mul, map_mul, map_inv]
        exact h.facts.E_normal _ hcb _ hxE
    obtain ⟨l, hlH, hln⟩ := CFSG.Walter.W67.Sec6.exists_mul_mem_normalizer_of_sylowIn (r := 2)
      h.W0_le_H0 h.card_W0_eq_sylow_H0 hcmem
    have hlM : l ∈ M := H0_le_M hlH
    have hlE : barMk ↥M ⟨l, hlM⟩ ∈ Ebar := by
      have : barMk ↥M ⟨l, hlM⟩ ∈ imgM M (H0 M Ebar v) := mem_imgM_iff.2 ⟨⟨l, hlM⟩, hlH, rfl⟩
      rwa [h.imgM_H0] at this
    have hlE' : (barMk ↥M ⟨l, hlM⟩)⁻¹ ∈ imgM M (W0 M W Ebar) := by
      rw [h.imgM_W0]
      exact Ebar.inv_mem hlE
    obtain ⟨w, hw, hwe⟩ := mem_imgM_iff.1 hlE'
    have hnM : l * (c : G) ∈ M := M.mul_mem hlM c.2
    have hwN : (w : G) ∈ normalizer (W0 M W Ebar : Set G) := Subgroup.le_normalizer hw
    have hwnM : (w : G) * (l * (c : G)) ∈ M := M.mul_mem w.2 hnM
    refine mem_imgM_iff.2 ⟨⟨(w : G) * (l * (c : G)), hwnM⟩,
      ⟨(normalizer (W0 M W Ebar : Set G)).mul_mem hwN hln, hwnM⟩, ?_⟩
    have h1 : (⟨(w : G) * (l * (c : G)), hwnM⟩ : ↥M) = w * (⟨l, hlM⟩ * c) := rfl
    rw [h1, map_mul, map_mul, hwe, inv_mul_cancel_left]

theorem card_MulAut_W0_le : Nat.card (MulAut ↥(W0 M W Ebar)) ≤ 1920 := by
  obtain ⟨e⟩ := equiv_imgM h.W0_le_M h.W0_pGroup
  let e' : ↥(W0 M W Ebar) ≃* ↥Ebar := e.trans (MulEquiv.subgroupCongr h.imgM_W0)
  rw [Nat.card_congr (MulAut.congr e').toEquiv]
  exact h.facts.aut

theorem card_normalizer_W0_le :
    Nat.card ↥(normalizer (W0 M W Ebar : Set G)) ≤
      1920 * Nat.card ↥(centralizer (W0 M W Ebar : Set G)) := by
  have hker := Subgroup.card_ker_mul_card_range (W0 M W Ebar).normalizerMonoidHom
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  have hD : Nat.card ↥((centralizer (W0 M W Ebar : Set G)).subgroupOf
      (normalizer (W0 M W Ebar : Set G))) = Nat.card ↥(centralizer (W0 M W Ebar : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer _)).toEquiv
  have hrange : Nat.card ↥(W0 M W Ebar).normalizerMonoidHom.range ≤ 1920 :=
    (Subgroup.card_le_card_group _).trans h.card_MulAut_W0_le
  rw [hD] at hker
  rw [← hker]
  exact (Nat.mul_le_mul_left _ hrange).trans (by rw [mul_comm])

theorem cent_W0_le_N0 :
    centralizer (W0 M W Ebar : Set G) ≤ normalizer (W0 M W Ebar : Set G) ⊓ M :=
  le_inf (Subgroup.centralizer_le_normalizer _) h.cent_W0_le_M

theorem card_imgM_cent_W0_le :
    Nat.card ↥(imgM M (centralizer (W0 M W Ebar : Set G))) ≤ 2 := by
  have hle : imgM M (centralizer (W0 M W Ebar : Set G)) ≤ zpowers h.vb := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := mem_imgM_iff.1 hy
    have hdN : (d : G) ∈ normalizer (W0 M W Ebar : Set G) := Subgroup.centralizer_le_normalizer _ hd
    have hdC := h.normalizer_W0_le_cent hdN
    have hdv : (d : G) * v = v * d := Subgroup.mem_centralizer_singleton_iff.1 hdC
    have hdb : barMk ↥M d ∈ centralizer ({h.vb} : Set (Mb M)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      show barMk ↥M d * barMk ↥M ⟨v, h.v_mem_M⟩ = barMk ↥M ⟨v, h.v_mem_M⟩ * barMk ↥M d
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hdv
    have key : ∀ e ∈ Ebar, barMk ↥M d * e = e * barMk ↥M d := by
      intro e he
      have heW : e ∈ imgM M (W0 M W Ebar) := by rw [h.imgM_W0]; exact he
      obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 heW
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hd _ hm).symm)
    rcases h.facts.cent_E _ hdb key with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact Subgroup.mem_zpowers _
  calc Nat.card ↥(imgM M (centralizer (W0 M W Ebar : Set G))) ≤ Nat.card ↥(zpowers h.vb) :=
        Subgroup.card_le_of_le hle
    _ = 2 := by rw [Nat.card_zpowers, h.vb_two]

theorem card_cent_W0_le_mul :
    Nat.card ↥(centralizer (W0 M W Ebar : Set G)) ≤
      2 * Nat.card ↥(normalizer (W0 M W Ebar : Set G) ⊓ M ⊓ pPrimeCoreOf 2 M) := by
  rw [card_eq_card_imgM_mul h.cent_W0_le_M]
  exact Nat.mul_le_mul h.card_imgM_cent_W0_le
    (Subgroup.card_le_of_le (inf_le_inf_right _ h.cent_W0_le_N0))

theorem card_N0 :
    Nat.card ↥(normalizer (W0 M W Ebar : Set G) ⊓ M) =
      1920 * Nat.card ↥(normalizer (W0 M W Ebar : Set G) ⊓ M ⊓ pPrimeCoreOf 2 M) := by
  rw [card_eq_card_imgM_mul (inf_le_right), h.imgM_N0, h.facts.card_cent]

theorem normalizer_W0_le_M : normalizer (W0 M W Ebar : Set G) ≤ M := by
  have hN0Y : normalizer (W0 M W Ebar : Set G) ⊓ M ≤ normalizer (W0 M W Ebar : Set G) := inf_le_left
  have hWY : W ≤ normalizer (W0 M W Ebar : Set G) := h.W_le_normalizer_W0
  have hWN0 : W ≤ normalizer (W0 M W Ebar : Set G) ⊓ M := le_inf hWY h.W_le
  have hsyl : IsSylowOf 2 W (normalizer (W0 M W Ebar : Set G)) := h.W_syl.of_le hWY le_top
  have hodd : ¬ 2 ∣ (normalizer (W0 M W Ebar : Set G) ⊓ M).relIndex (normalizer (W0 M W Ebar : Set G)) := by
    rw [isSylowOf_iff] at hsyl
    obtain ⟨-, -, hnd⟩ := hsyl
    intro hd
    apply hnd
    rw [← Subgroup.relIndex_mul_relIndex W (normalizer (W0 M W Ebar : Set G) ⊓ M)
      (normalizer (W0 M W Ebar : Set G)) hWN0 hN0Y]
    exact hd.mul_left _
  have hmul := Subgroup.relIndex_mul_card (H := normalizer (W0 M W Ebar : Set G) ⊓ M)
    (K := normalizer (W0 M W Ebar : Set G))
  rw [inf_eq_left.2 hN0Y] at hmul
  have h1 := h.card_normalizer_W0_le
  have h2 := h.card_cent_W0_le_mul
  have h3 := h.card_N0
  have hkN : (normalizer (W0 M W Ebar : Set G) ⊓ M).relIndex (normalizer (W0 M W Ebar : Set G)) *
      Nat.card ↥(normalizer (W0 M W Ebar : Set G) ⊓ M) ≤
      2 * Nat.card ↥(normalizer (W0 M W Ebar : Set G) ⊓ M) := by
    rw [hmul, h3]
    calc Nat.card ↥(normalizer (W0 M W Ebar : Set G)) ≤
          1920 * Nat.card ↥(centralizer (W0 M W Ebar : Set G)) := h1
      _ ≤ 1920 * (2 * Nat.card ↥(normalizer (W0 M W Ebar : Set G) ⊓ M ⊓ pPrimeCoreOf 2 M)) :=
          Nat.mul_le_mul_left _ h2
      _ = 2 * (1920 * Nat.card ↥(normalizer (W0 M W Ebar : Set G) ⊓ M ⊓ pPrimeCoreOf 2 M)) := by ring
  have hk2 : (normalizer (W0 M W Ebar : Set G) ⊓ M).relIndex (normalizer (W0 M W Ebar : Set G)) ≤ 2 :=
    Nat.le_of_mul_le_mul_right hkN Nat.card_pos
  have hk0 : (normalizer (W0 M W Ebar : Set G) ⊓ M).relIndex (normalizer (W0 M W Ebar : Set G)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact (Nat.card_pos (α := ↥(normalizer (W0 M W Ebar : Set G)))).ne' hmul.symm
  have hk1 : (normalizer (W0 M W Ebar : Set G) ⊓ M).relIndex (normalizer (W0 M W Ebar : Set G)) = 1 := by
    omega
  exact (Subgroup.relIndex_eq_one.1 hk1).trans inf_le_right

end P89Std

end CFSG.GH74.GLS.Th2.P85.Sp
