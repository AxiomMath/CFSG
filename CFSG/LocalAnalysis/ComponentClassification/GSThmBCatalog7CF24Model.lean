module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7CF24J0
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7CF24Grp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7SuzCSMain

public section

namespace CFSG.ComponentClassification.GSThmB.CF24

open CFSG CFSG.LocalCores CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.CatFactsL4U4.SuzCS
  Subgroup

theorem component_of_conj {L : Type} [Group L] (α : MulAut L)
    (Q : L →* Equiv.Perm (Fin 1782)) (hQ : ∀ g ∈ suzM, g ∈ Q.range) (hQM : ∀ x, Q x ∈ suzM)
    (hker : Q.ker ≤ center L) (t : Equiv.Perm (Fin 1782)) (hQα : ∀ x, Q (α x) = t * Q x * t⁻¹)
    (C : Subgroup (Equiv.Perm (Fin 1782))) (hC : ∀ g, g ∈ C ↔ g ∈ suzM ∧ g * t = t * g)
    (K F : Subgroup L) (hF : ∀ y, y ∈ F ↔ α y = y) (hKF : K ≤ F)
    (hKc : IsComponent (K.subgroupOf F)) :
    K.map Q ≤ C ∧ IsComponent ((K.map Q).subgroupOf C) := by
  have hKq : IsQuasisimple K := isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKF) hKc.1
  have hFC : F.map Q ≤ C := by
    rintro _ ⟨y, hy, rfl⟩
    refine (hC _).2 ⟨hQM y, ?_⟩
    have h := hQα y
    rw [(hF y).1 hy] at h
    calc Q y * t = t * Q y * t⁻¹ * t := by rw [← h]
      _ = t * Q y := by group
  have hnorm : ((F.map Q).subgroupOf C).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨hgM, hgt⟩ := (hC _).1 g.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_map_fix Q α t hQα hker F hF (hQ _ hgM) hgt hn
  have hKC : K.map Q ≤ C := (map_mono hKF).trans hFC
  refine ⟨hKC, ?_, isSubnormal_map_subgroupOf Q hKF hKc.2 hFC hnorm⟩
  exact isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKC).symm (isQuasisimple_map Q hker hKq)

theorem sq_eq_one_of_inv
    {L : Type} [Group L]
    (α : MulAut L) (hα : α * α = 1) (q₀ : L →* suzM) (hq₀ : Function.Surjective q₀)
    {a : Equiv.Perm (Fin 1782)} (ha : a ∈ suzT)
    (hQα : ∀ x, ((q₀ (α x) : suzM) : Equiv.Perm (Fin 1782)) = a * q₀ x * a⁻¹) : a * a = 1 := by
  apply suzAutModel.inj (a * a) (suzT.mul_mem ha ha)
  intro p hp
  obtain ⟨x, hx⟩ := hq₀ ⟨p, hp⟩
  have h1 := hQα (α x)
  have hαα : α (α x) = x := by rw [← MulAut.mul_apply, hα, MulAut.one_apply]
  rw [hαα, hQα x, hx] at h1
  have h1' : p = a * (a * p * a⁻¹) * a⁻¹ := h1
  calc a * a * p = a * (a * p * a⁻¹) * a⁻¹ * (a * a) := by group
    _ = p * (a * a) := by rw [← h1']

theorem exists_model
    {L : Type} [Group L]
    (e : L ⧸ center L ≃* Blueprint.NativeSporadic.Suz) (α : MulAut L) (hα : α * α = 1)
    (K F : Subgroup L) (hF : ∀ y, y ∈ F ↔ α y = y) (hKF : K ≤ F)
    (hKc : IsComponent (K.subgroupOf F)) (hK : Nat.card (K ⧸ center K) = 20160) :
    ∃ q : L →* suzM, Function.Surjective q ∧ q.ker = center L ∧
      K.map (suzM.subtype.comp q) = J0 := by
  have hKq : IsQuasisimple K := isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKF) hKc.1
  set θ : L ⧸ center L ≃* suzM := e.trans suzEquivM with hθ
  set q₀ : L →* suzM := θ.toMonoidHom.comp (QuotientGroup.mk' (center L)) with hq₀
  have hq₀s : Function.Surjective q₀ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hq₀k : q₀.ker = center L := by
    ext x
    rw [MonoidHom.mem_ker, hq₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcα : (center L).map (α : L →* L) = center L :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance α
  set αb : MulAut (L ⧸ center L) := QuotientGroup.congr (center L) (center L) α hcα with hαb
  set σ : MulAut suzM := (θ.symm.trans αb).trans θ with hσd
  have hσ : ∀ x, σ (q₀ x) = q₀ (α x) := fun x => by
    simp only [hσd, hq₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, QuotientGroup.mk'_apply, hαb, QuotientGroup.congr_mk]
  obtain ⟨a, haT, ha⟩ := suzAutModel.surj σ
  have hQα : ∀ x, ((q₀ (α x) : suzM) : Equiv.Perm (Fin 1782)) = a * q₀ x * a⁻¹ :=
    fun x => by rw [← hσ, ha]
  have ha2 := sq_eq_one_of_inv α hα q₀ hq₀s haT hQα
  have hQker : (suzM.subtype.comp q₀).ker ≤ center L := by
    intro x hx
    rw [← hq₀k, MonoidHom.mem_ker]
    exact Subtype.ext hx
  have hQrange : ∀ g ∈ suzM, g ∈ (suzM.subtype.comp q₀).range := fun g hg => by
    obtain ⟨x, hx⟩ := hq₀s ⟨g, hg⟩
    exact ⟨x, by rw [MonoidHom.comp_apply, hx]; rfl⟩
  by_cases ha1 : a = 1
  ·
    exfalso
    subst ha1
    obtain ⟨hKC, hB⟩ := component_of_conj α (suzM.subtype.comp q₀) hQrange
      (fun x => (q₀ x).2) hQker 1 (fun x => hQα x) suzM
      (fun g => ⟨fun hg => ⟨hg, by group⟩, fun hg => hg.1⟩) K F hF hKF hKc
    have hcard := card_map_quotient_center (suzM.subtype.comp q₀) hQker hKq
    rw [hK] at hcard
    rcases hB.2.eq_bot_or_top_of_isSimpleGroup suzM_isSimpleGroup with h | h
    · rw [subgroupOf_eq_bot] at h
      have hbot : K.map (suzM.subtype.comp q₀) = ⊥ := (h.eq_bot_of_le hKC)
      have h1 := (center (K.map (suzM.subtype.comp q₀))).card_eq_card_quotient_mul_card_subgroup
      rw [hcard, hbot, Subgroup.card_bot] at h1
      omega
    · rw [subgroupOf_eq_top] at h
      have heq : K.map (suzM.subtype.comp q₀) = suzM := le_antisymm hKC h
      rw [heq] at hcard
      have hc : center suzM = ⊥ := by
        have := suzM_isSimpleGroup
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center suzM) with h' | h'
        · exact h'
        · exfalso
          obtain ⟨x, y, hxy⟩ := suzM_not_comm
          exact hxy (mem_center_iff.mp (h' ▸ mem_top y) x)
      rw [hc, Nat.card_congr (QuotientGroup.quotientBot (G := suzM)).toEquiv, suzM_card] at hcard
      omega
  · have haord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
    obtain ⟨i, ⟨hi, c, hc, hca⟩, -⟩ := suzT_involution_class haT haord
    set q : L →* suzM := (suzConjT ⟨c⁻¹, suzT.inv_mem hc⟩).toMonoidHom.comp q₀ with hqd
    have hqx : ∀ x, ((q x : suzM) : Equiv.Perm (Fin 1782)) = c⁻¹ * q₀ x * c := fun x => by
      rw [hqd, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, suzConjT_apply, inv_inv]
    have hqs : Function.Surjective q :=
      (suzConjT ⟨c⁻¹, suzT.inv_mem hc⟩).surjective.comp hq₀s
    have hqk : q.ker = center L := by
      rw [← hq₀k]
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hqd, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    have hQker : (suzM.subtype.comp q).ker ≤ center L := by
      intro x hx
      rw [← hqk, MonoidHom.mem_ker]
      exact Subtype.ext hx
    have hQrange' : ∀ g ∈ suzM, g ∈ (suzM.subtype.comp q).range := fun g hg => by
      obtain ⟨x, hx⟩ := hqs ⟨g, hg⟩
      exact ⟨x, by rw [MonoidHom.comp_apply, hx]; rfl⟩
    have hQα' : ∀ x, (suzM.subtype.comp q) (α x) =
        suzInv i * (suzM.subtype.comp q) x * (suzInv i)⁻¹ := fun x => by
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [hqx, hqx, hQα, ← hca]
      group
    obtain ⟨hKC, hB⟩ := component_of_conj α (suzM.subtype.comp q) hQrange' (fun x => (q x).2)
      hQker (suzInv i) hQα' (invE i) (fun g => by
        rw [invE_eq_centM hi, centM, mem_inf, mem_centralizer_singleton_iff]
        exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩) K F hF hKF hKc
    have hBcard : Nat.card ((K.map (suzM.subtype.comp q)).subgroupOf (invE i) ⧸
        center ((K.map (suzM.subtype.comp q)).subgroupOf (invE i))) = 20160 := by
      rw [card_quotient_center_equiv (subgroupOfEquivOfLe hKC),
        card_map_quotient_center _ hQker hKq, hK]
    interval_cases i
    · refine ⟨q, hqs, hqk, ?_⟩
      have h := component_eq_J0 _ hB
      rwa [subgroupOf_map_subtype, inf_eq_left.mpr hKC] at h
    · exact absurd hB (CTI_Suz_second_involution_centralizer_has_no_components.2 _)
    · exfalso
      have hd : Nat.card ((K.map (suzM.subtype.comp q)).subgroupOf (invE 2)) ∣ 190080 := by
        have h := Subgroup.card_subgroup_dvd_card ((K.map (suzM.subtype.comp q)).subgroupOf
          (invE 2))
        rwa [card_invE (i := 2) (by norm_num)] at h
      have h7 : 7 ∣ Nat.card ((K.map (suzM.subtype.comp q)).subgroupOf (invE 2)) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center _), hBcard]
        exact (show 7 ∣ 20160 by norm_num).mul_right _
      have := h7.trans hd
      norm_num at this
    · exact (three_model _ hB hBcard).elim

end CFSG.ComponentClassification.GSThmB.CF24
