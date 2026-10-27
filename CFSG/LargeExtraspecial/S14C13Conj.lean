module

public import CFSG.LargeExtraspecial.S14Nine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] noncomputable def cConj {t : S.O} [hN : NQHyp S g t] {z : S.O} (hz : z ∈ Ct S t) :
    Nbar S g t →* Nbar S g t where
  toFun n := ⟨z * n * z⁻¹, conj_mem_Nbar_of_mem_Ct hN.conj_mem hz n.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem coe_cConj {t : S.O} [NQHyp S g t] {z : S.O} (hz : z ∈ Ct S t) (n : Nbar S g t) :
    ((cConj hz n : Nbar S g t) : S.O) = z * n * z⁻¹ :=
  rfl

@[expose] noncomputable def cLin {t : S.O} [hN : NQHyp S g t] {z : S.O} (hz : z ∈ Ct S t) :
    NQ S g t →ₗ[ZMod 2] NQ S g t :=
  (QuotientGroup.map _ _ (cConj hz) (by
    intro n hn
    rw [mem_comap, mem_subgroupOf] at *
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
    change z * n * z⁻¹ ∈ zpowers t
    have hc := (Commute.zpow_right (show Commute z t from
      mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hz).2) k).eq
    rw [← hk, hc, mul_inv_cancel_right]
    exact zpow_mem_zpowers t k)).toAdditive.toZModLinearMap 2

theorem cLin_mk {t : S.O} [NQHyp S g t] {z : S.O} (hz : z ∈ Ct S t) (n : Nbar S g t) :
    cLin hz (nqMk n) = nqMk (cConj hz n) :=
  rfl

theorem cLin_comm_nqRep {t : S.O} [hN : NQHyp S g t] {z : S.O} (hz : z ∈ Ct S t)
    (hzR : ∀ r ∈ Rbar S g t, z * r * z⁻¹ * r⁻¹ ∈ Nbar S g t)
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y) (e : Y)
    (v : NQ S g t) : cLin hz (nqRep S g t hY e v) = nqRep S g t hY e (cLin hz v) := by
  have hv := nqMk_surjective (S := S) (g := g) (t := t) v
  rcases hv with ⟨n, hn⟩
  rw [← hn]
  have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resV hN.conj_mem t).range := by
    rw [range_resV, hY]; exact e.2
  obtain ⟨x, hx⟩ := heR
  have hc : z * x * z⁻¹ * (x : S.O)⁻¹ ∈ Nbar S g t := hzR x x.2
  have hm : (x : S.O) * (z * n * z⁻¹) * (x : S.O)⁻¹ ∈ Nbar S g t :=
    conj_mem_Nbar_of_mem_Rbar hN.conj_mem x.2 (conj_mem_Nbar_of_mem_Ct hN.conj_mem hz n.2)
  have h : ((cConj hz (nConj x n) : Nbar S g t) : S.O)⁻¹ * (nConj x (cConj hz n) : Nbar S g t)
      ∈ zpowers t := by
    have e1 : (z * (x * n * (x : S.O)⁻¹) * z⁻¹)⁻¹ * ((x : S.O) * (z * n * z⁻¹) * (x : S.O)⁻¹) =
        (z * x * z⁻¹ * (x : S.O)⁻¹) * ((x : S.O) * (z * n * z⁻¹) * (x : S.O)⁻¹)⁻¹ *
          (z * x * z⁻¹ * (x : S.O)⁻¹)⁻¹ * ((x : S.O) * (z * n * z⁻¹) * (x : S.O)⁻¹)⁻¹⁻¹ := by
      group
    change (z * (x * n * (x : S.O)⁻¹) * z⁻¹)⁻¹ * ((x : S.O) * (z * n * z⁻¹) * (x : S.O)⁻¹) ∈ _
    rw [e1]
    exact hN.comm _ hc _ (inv_mem hm)
  calc cLin hz (nqRep S g t hY e (nqMk n)) = nqMk (cConj hz (nConj x n)) := by
        rw [nqRep_apply hY hx.symm n]; rfl
    _ = nqMk (nConj x (cConj hz n)) := (nqMk_eq_iff _ _).mpr h
    _ = nqRep S g t hY e (cLin hz (nqMk n)) := (nqRep_apply hY hx.symm _).symm

theorem finrank_NQ_eq_of_card {t : S.O} [NQHyp S g t] (ht1 : t ≠ 1) (htt : t * t = 1)
    (htN : t ∈ Nbar S g t) {e : ℕ} (he : Nat.card (Nbar S g t) = 2 ^ (e + 1)) :
    finrank (ZMod 2) (NQ S g t) = e := by
  have h1 := card_inf_Nbar_eq ht1 htt htN (X := ⊤) (mem_top t)
  have htop : nqSub S g t ⊤ = ⊤ := by
    rw [eq_top_iff]
    intro m _
    obtain ⟨n, rfl⟩ := nqMk_surjective m
    exact ⟨n, mem_top _, rfl⟩
  rw [htop, finrank_top, top_inf_eq, he, pow_succ, mul_comm] at h1
  exact (Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left (by norm_num) h1)).symm

@[expose] noncomputable def cEquiv {t : S.O} [NQHyp S g t] {z : S.O} (hz : z ∈ Ct S t) :
    NQ S g t ≃ₗ[ZMod 2] NQ S g t :=
  LinearEquiv.ofLinearMap (cLin hz) (cLin (inv_mem hz))
    (LinearMap.ext fun m => by
      have hm := nqMk_surjective (S := S) (g := g) (t := t) m
      rcases hm with ⟨n, hn⟩
      rw [← hn]
      show nqMk (cConj hz (cConj (inv_mem hz) n)) = nqMk n
      congr 1
      exact Subtype.ext (by simp [coe_cConj, mul_assoc]))
    (LinearMap.ext fun m => by
      have hm := nqMk_surjective (S := S) (g := g) (t := t) m
      rcases hm with ⟨n, hn⟩
      rw [← hn]
      show nqMk (cConj (inv_mem hz) (cConj hz n)) = nqMk n
      congr 1
      exact Subtype.ext (by simp [coe_cConj, mul_assoc]))

theorem cEquiv_mk {t : S.O} [NQHyp S g t] {z : S.O} (hz : z ∈ Ct S t) (n : Nbar S g t) :
    cEquiv hz (nqMk n) = nqMk (cConj hz n) :=
  rfl

end CFSG.LargeExtraspecial.S14
