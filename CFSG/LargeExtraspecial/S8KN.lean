module

public import CFSG.LargeExtraspecial.S14Cent
public import CFSG.LargeExtraspecial.S8FiveC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem mem_Nbar_of_comm_mem_zpowers (hCE : CentralExtInput.{0}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ)
    (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t)
    {x : S.O} (hx : x ∈ S.Mbar) (hxN : ∀ y ∈ Nbar S g t, x * y * x⁻¹ * y⁻¹ ∈ zpowers t) :
    x ∈ Nbar S g t := by
  have haQ := H.conj_mem
  have hext := timmesfeld_8_5 hNo hΩ D hA7
  have hcase : OmegaCase H C ht ht1 hVQ ∨ SpCase H C ht ht1 hVQ := Or.inl hΩ
  have hperf := S14.commutator_Rbar_eq_of_case hCE H hNo C ht ht1 hVQ hcase h6 hext
  have htN := S6.self_mem_Nbar H ht
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have htc : ∀ y ∈ Nbar S g t, t * y = y * t := fun y hy =>
    (commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)).symm
  have htc' : (⟨t, htN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (htc v v.2).symm
  have ht1' : (⟨t, htN⟩ : Nbar S g t) ≠ 1 := fun e => ht1 (congrArg Subtype.val e)
  obtain ⟨u, huN, hu⟩ := S14.exists_conj_eq_of_comm_mem_zpowers hext htN htt ht1 htc hxN
  have huR : u ∈ Rbar S g t := Nbar_le_Rbar huN
  have hx'M : u⁻¹ * x ∈ S.Mbar := mul_mem (inv_mem (Rbar_le_Mbar huR)) hx
  have hx'c : ∀ y ∈ Nbar S g t, u⁻¹ * x * y = y * (u⁻¹ * x) := fun y hy => by
    calc u⁻¹ * x * y = u⁻¹ * (x * y * x⁻¹) * x := by group
      _ = u⁻¹ * (u * y * u⁻¹) * x := by rw [hu y hy]
      _ = y * (u⁻¹ * x) := by group
  obtain ⟨k, hk⟩ : ∃ k : S.M, S.ρ k = u⁻¹ * x := id hx'M
  have hkt : S.ρ k * t = t * S.ρ k := by rw [hk]; exact hx'c t htN
  have hf : ∀ r ∈ Rbar S g t, r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹ ∈ zpowers t := by
    intro r hr
    have hR : r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹ ∈ Rbar S g t := by
      have h1 := conj_mem_Rbar hkt (inv_mem hr)
      rw [hk] at h1
      have := mul_mem hr h1
      simpa only [mul_assoc] using this
    have hC : ∀ y ∈ Nbar S g t, (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹) * y =
        y * (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹) := by
      intro y hy
      have hw := S14.conj_mem_Nbar_of_mem_Rbar haQ (inv_mem hr) hy
      rw [inv_inv] at hw
      have h1 := hx'c _ hw
      have h2 := hx'c y hy
      have h3 : (u⁻¹ * x)⁻¹ * y = y * (u⁻¹ * x)⁻¹ := by
        calc (u⁻¹ * x)⁻¹ * y = (u⁻¹ * x)⁻¹ * (y * (u⁻¹ * x)) * (u⁻¹ * x)⁻¹ := by group
          _ = (u⁻¹ * x)⁻¹ * (u⁻¹ * x * y) * (u⁻¹ * x)⁻¹ := by rw [h2]
          _ = y * (u⁻¹ * x)⁻¹ := by group
      calc (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹) * y =
          r * (u⁻¹ * x) * r⁻¹ * ((u⁻¹ * x)⁻¹ * y) := by group
        _ = r * (u⁻¹ * x) * r⁻¹ * (y * (u⁻¹ * x)⁻¹) := by rw [h3]
        _ = r * ((u⁻¹ * x) * (r⁻¹ * y * r)) * r⁻¹ * (u⁻¹ * x)⁻¹ := by group
        _ = r * ((r⁻¹ * y * r) * (u⁻¹ * x)) * r⁻¹ * (u⁻¹ * x)⁻¹ := by rw [h1]
        _ = y * (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹) := by group
    have hN := S14.mem_Nbar_of_comm_mem hCE H hNo C ht ht1 hVQ hcase h6 hext hR fun y hy => by
      have e : r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹ * y *
          (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹)⁻¹ * y⁻¹ = 1 := by
        rw [hC y hy]
        group
      rw [e]
      exact one_mem _
    have hz : (⟨_, hN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
      rw [mem_center_iff]
      intro v
      exact Subtype.ext (hC v v.2).symm
    by_cases h1 : (⟨_, hN⟩ : Nbar S g t) = 1
    · have h2 : r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹ = 1 := congrArg Subtype.val h1
      rw [h2]
      exact one_mem _
    · have h2 : r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹ = t :=
        congrArg Subtype.val
          (CFSG.RankThree.Literature.FSmith.eq_of_mem_center hext hz htc' h1 ht1')
      rw [h2]
      exact mem_zpowers t
  have hzr : ∀ e ∈ zpowers t, ∀ r ∈ Rbar S g t, r * e * r⁻¹ = e := by
    rintro e ⟨i, rfl⟩ r hr
    rw [(Commute.zpow_right (show Commute r t from commute_of_mem_Rbar haQ hr) i).eq,
      mul_inv_cancel_right]
  let ψ : Rbar S g t →* Multiplicative (ZMod 2) :=
    { toFun := fun r => Multiplicative.ofAdd
        (S14.ind1 ((r : S.O) * (u⁻¹ * x) * (r : S.O)⁻¹ * (u⁻¹ * x)⁻¹))
      map_one' := by simp [S14.ind1]
      map_mul' := fun r s => by
        have e : ((r * s : Rbar S g t) : S.O) * (u⁻¹ * x) * ((r * s : Rbar S g t) : S.O)⁻¹ *
            (u⁻¹ * x)⁻¹ = ((r : S.O) * ((s : S.O) * (u⁻¹ * x) * (s : S.O)⁻¹ * (u⁻¹ * x)⁻¹) *
              (r : S.O)⁻¹) * ((r : S.O) * (u⁻¹ * x) * (r : S.O)⁻¹ * (u⁻¹ * x)⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
        rw [e, hzr _ (hf s s.2) r r.2, S14.ind1_mul htt (hf s s.2) (hf r r.2), add_comm,
          ofAdd_add] }
  have hψ : commutator (Rbar S g t) ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  rw [S14.commutator_eq_top_of_perfect hperf] at hψ
  have hcomm : ∀ r ∈ Rbar S g t, (u⁻¹ * x) * r = r * (u⁻¹ * x) := by
    intro r hr
    have h1 : ψ ⟨r, hr⟩ = 1 := hψ (mem_top _)
    have h2 : S14.ind1 (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹) = 0 := h1
    have h3 : r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹ = 1 := by
      unfold S14.ind1 at h2
      split_ifs at h2 with h
      · exact h
      · exact absurd h2 (by decide)
    calc u⁻¹ * x * r = (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹)⁻¹ * (r * (u⁻¹ * x)) := by group
      _ = r * (u⁻¹ * x) := by rw [h3, inv_one, one_mul]
  have hx'z := S14.mem_zpowers_of_commute hCE H hNo C ht ht1 hVQ hcase hcomm
  have e : x = u * (u⁻¹ * x) := by group
  rw [e]
  exact mul_mem huN (zpowers_le.mpr htN hx'z)

end CFSG.LargeExtraspecial.S8
