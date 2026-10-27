module

public import CFSG.RankThree.PartOne.CTP.StrongPQuotient

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.RankThree.PartOne
open StrongP

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

private theorem relIndex_sup_mul_card_inf {Y N : Subgroup G} [N.Normal] :
    Y.relIndex (Y ⊔ N) * Nat.card (N ⊓ Y : Subgroup G) = Nat.card N := by
  have hA : Y.relIndex (Y ⊔ N) * Nat.card Y = Nat.card (Y ⊔ N : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card (H := Y) (K := Y ⊔ N)
    rwa [inf_eq_left.mpr le_sup_left] at h
  have hB : N.relIndex (Y ⊔ N) * Nat.card N = Nat.card (Y ⊔ N : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card (H := N) (K := Y ⊔ N)
    rwa [inf_eq_left.mpr le_sup_right] at h
  have hC : N.relIndex Y * Nat.card (N ⊓ Y : Subgroup G) = Nat.card Y :=
    Subgroup.relIndex_mul_card (H := N) (K := Y)
  have hD : N.relIndex (Y ⊔ N) = N.relIndex Y :=
    Subgroup.relIndex_sup_right (H := Y) (K := N)
  have hNrel : N.relIndex Y ≠ 0 := by
    intro h0
    have hzero : Nat.card Y = 0 := by rw [← hC, h0, zero_mul]
    exact Nat.card_pos.ne' hzero
  have hcomb : N.relIndex Y * (Y.relIndex (Y ⊔ N) * Nat.card (N ⊓ Y : Subgroup G)) =
      N.relIndex Y * Nat.card N := by
    calc N.relIndex Y * (Y.relIndex (Y ⊔ N) * Nat.card (N ⊓ Y : Subgroup G))
        = Y.relIndex (Y ⊔ N) * (N.relIndex Y * Nat.card (N ⊓ Y : Subgroup G)) := by ring
      _ = Y.relIndex (Y ⊔ N) * Nat.card Y := by rw [hC]
      _ = Nat.card (Y ⊔ N : Subgroup G) := hA
      _ = N.relIndex (Y ⊔ N) * Nat.card N := hB.symm
      _ = N.relIndex Y * Nat.card N := by rw [hD]
  exact mul_left_cancel₀ hNrel hcomb

private theorem not_dvd_relIndex_sup (hp : p.Prime) {Y N : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card N) : ¬ p ∣ Y.relIndex (Y ⊔ N) := by
  intro hdiv
  exact hN (relIndex_sup_mul_card_inf (Y := Y) (N := N) ▸
    dvd_mul_of_dvd_left hdiv (Nat.card (N ⊓ Y : Subgroup G)))

theorem exists_mem_conj_le_of_isPGroup_of_le_sup (hp : p.Prime) {Y N R : Subgroup G}
    [N.Normal] (hN : ¬ p ∣ Nat.card N) (hR : IsPGroup p R) (hRle : R ≤ Y ⊔ N) :
    ∃ n ∈ N, ∀ x ∈ R, n⁻¹ * x * n ∈ Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  let M : Subgroup G := Y ⊔ N
  let S : Sylow p ↥Y := Classical.arbitrary _
  let SY : Subgroup G := (S : Subgroup Y).map Y.subtype
  have hSYle : SY ≤ Y := Subgroup.map_subtype_le _
  have hSYp : IsPGroup p SY := S.isPGroup'.map Y.subtype
  have hSYrelY : SY.relIndex Y = S.index := by
    have hsub : SY.subgroupOf Y = (S : Subgroup Y) := by
      rw [← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
    show (SY.subgroupOf Y).index = S.index
    rw [hsub]
  have hnot : ¬ p ∣ (SY.subgroupOf M).index := by
    have hrel : ¬ p ∣ SY.relIndex M := by
      have hmul := Subgroup.relIndex_mul_relIndex (H := SY) (K := Y) (L := M)
        hSYle (show Y ≤ M from le_sup_left)
      rw [← hmul]
      exact hp.not_dvd_mul (by rw [hSYrelY]; exact S.not_dvd_index)
        (not_dvd_relIndex_sup hp hN)
    exact hrel
  have hSYpM : IsPGroup p (SY.subgroupOf M) := hSYp.comap_subtype (K := M)
  let PMsub : Subgroup ↥M := SY.subgroupOf M
  let PM : Sylow p ↥M := hSYpM.toSylow hnot
  have hPMsub : (PM : Subgroup ↥M) = PMsub := rfl
  have hRM : IsPGroup p (R.subgroupOf M) := hR.comap_subtype
  obtain ⟨T : Sylow p ↥M, hRT⟩ := hRM.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥M) PM T
  have hmemN : (m : G) ∈ N ⊔ Y := by
    rw [sup_comm]
    exact m.2
  obtain ⟨n, hn, y, hy, hny⟩ := Subgroup.mem_sup_of_normal_left.mp hmemN
  refine ⟨n, hn, fun x hx => ?_⟩
  have hxM : x ∈ M := hRle hx
  have hxT : (⟨x, hxM⟩ : ↥M) ∈ (T : Subgroup ↥M) :=
    hRT (show (⟨x, hxM⟩ : ↥M) ∈ R.subgroupOf M from Subgroup.mem_subgroupOf.mpr hx)
  rw [← hm, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxT
  obtain ⟨s, hs, hsm⟩ := hxT
  have hsY : (s : G) ∈ Y := by
    rw [hPMsub] at hs
    exact hSYle (Subgroup.mem_subgroupOf.mp hs)
  have hmsx : (m : G) * (s : G) * (m : G)⁻¹ = x := by
    have h := congrArg Subtype.val hsm
    simpa only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h
  rw [← hny] at hmsx
  have hxeq : x = n * (y * (s : G) * y⁻¹) * n⁻¹ := by
    rw [← hmsx]
    group
  rw [hxeq]
  have hcancel : n⁻¹ * (n * (y * (s : G) * y⁻¹) * n⁻¹) * n = y * (s : G) * y⁻¹ := by
    group
  rw [hcancel]
  exact Y.mul_mem (Y.mul_mem hy hsY) (Y.inv_mem hy)

theorem isStronglyPEmbedded_sup_of_normal (hp : p.Prime) {Y : Subgroup G}
    (hY : IsStronglyPEmbedded p Y) {N : Subgroup G} [N.Normal] (hN : ¬ p ∣ Nat.card N)
    (hne : Y ⊔ N ≠ ⊤) : IsStronglyPEmbedded p (Y ⊔ N) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨hne, hY.2.1.trans (Subgroup.card_dvd_of_le le_sup_left), ?_⟩
  intro g hg hpdiv
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpdiv
  obtain ⟨hxM, hxconj⟩ := Subgroup.mem_inf.mp x.2
  have hxgM : (x : G) ∈ Y ⊔ N := hxM
  have hgxgM : g⁻¹ * (x : G) * g ∈ Y ⊔ N := StrongP.mem_conjSub_iff.mp hxconj
  have hxgp : (x : G) ^ p = 1 := by
    have h1 : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx]
    have h2 := pow_orderOf_eq_one (x : G)
    rwa [h1] at h2
  have hzp : IsPGroup p (Subgroup.zpowers (x : G)) :=
    StrongP.isPGroup_zpowers_of_pow_eq_one hxgp
  have hzp' : IsPGroup p (Subgroup.zpowers (g⁻¹ * (x : G) * g)) := by
    have h := hzp.map (MulAut.conj g⁻¹).toMonoidHom
    rw [MonoidHom.map_zpowers] at h
    change IsPGroup p (Subgroup.zpowers ((MulAut.conj g⁻¹) (x : G))) at h
    rw [show (MulAut.conj g⁻¹) (x : G) = g⁻¹ * (x : G) * g by
      rw [MulAut.conj_apply]; group] at h
    exact h
  obtain ⟨n, hn, hnY⟩ := exists_mem_conj_le_of_isPGroup_of_le_sup hp hN hzp
    (Subgroup.zpowers_le.mpr hxgM)
  obtain ⟨n', hn', hn'Y⟩ := exists_mem_conj_le_of_isPGroup_of_le_sup hp hN hzp'
    (Subgroup.zpowers_le.mpr hgxgM)
  have hx1Y : n⁻¹ * (x : G) * n ∈ Y := hnY _ (Subgroup.mem_zpowers _)
  have hx2Y : n'⁻¹ * (g⁻¹ * (x : G) * g) * n' ∈ Y := hn'Y _ (Subgroup.mem_zpowers _)
  set h : G := n⁻¹ * g * n' with hdef
  have hhconj : h⁻¹ * (n⁻¹ * (x : G) * n) * h = n'⁻¹ * (g⁻¹ * (x : G) * g) * n' := by
    rw [hdef]
    group
  have hx1conj : n⁻¹ * (x : G) * n ∈ conjSub h Y :=
    StrongP.mem_conjSub_iff.mpr (by rw [hhconj]; exact hx2Y)
  have hx1inf : n⁻¹ * (x : G) * n ∈ Y ⊓ conjSub h Y :=
    Subgroup.mem_inf.mpr ⟨hx1Y, hx1conj⟩
  have hx1order : orderOf (n⁻¹ * (x : G) * n) = p := by
    have h1 : orderOf (n⁻¹ * (x : G) * n) = orderOf (x : G) := by
      simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj n⁻¹) (x : G)
    rw [h1, Subgroup.orderOf_coe, hx]
  have hpdvd : p ∣ Nat.card (Y ⊓ conjSub h Y : Subgroup G) := by
    have hle : Subgroup.zpowers (n⁻¹ * (x : G) * n) ≤ Y ⊓ conjSub h Y :=
      Subgroup.zpowers_le.mpr hx1inf
    have h := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hx1order] at h
  have hhY : h ∉ Y := by
    intro hh
    refine hg ?_
    have hg_eq : g = n * h * n'⁻¹ := by rw [hdef]; group
    rw [hg_eq]
    exact (Y ⊔ N).mul_mem ((Y ⊔ N).mul_mem ((le_sup_right : N ≤ Y ⊔ N) hn)
      ((le_sup_left : Y ≤ Y ⊔ N) hh)) ((le_sup_right : N ≤ Y ⊔ N) (N.inv_mem hn'))
  exact hY.2.2 h hhY hpdvd

theorem isStronglyPEmbedded_map_mk_of_sup_ne_top (hp : p.Prime) {Y : Subgroup G}
    (hY : IsStronglyPEmbedded p Y) {N : Subgroup G} [N.Normal] (hN : ¬ p ∣ Nat.card N)
    (hne : Y ⊔ N ≠ ⊤) : IsStronglyPEmbedded p (Y.map (QuotientGroup.mk' N)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsup := isStronglyPEmbedded_sup_of_normal hp hY hN hne
  have h := IsStronglyPEmbedded.map_quotient (H := G) (Y := Y ⊔ N) (N := N) hsup
    le_sup_right hN
  rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h

end CFSG.GroupTheory.ThreeTranspositions
