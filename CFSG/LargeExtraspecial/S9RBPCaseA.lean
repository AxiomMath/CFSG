module

public import CFSG.LargeExtraspecial.S9RBPTriA
public import CFSG.LargeExtraspecial.S9PB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem secHom_eq_one_iff {t : S.O} {X Y : Submodule (ZMod 2) S.Qt}
    (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X)
    (hY : ∀ x ∈ Rbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Y) (r : Rbar S g t) :
    secHom S g t X Y hX hY r = 1 ↔ ∀ w ∈ Y, ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ X := by
  constructor
  · intro h1 w hw
    refine (secHom_fix_iff hX hY r hw).mp ?_
    rw [h1]
    rfl
  · intro h
    refine LinearEquiv.ext fun m => ?_
    obtain ⟨w, hw, rfl⟩ := exists_secMk X m
    exact (secHom_fix_iff hX hY r hw).mpr (h w hw)

theorem eq_one_of_forall_commute (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v)
    {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t}
    (he : ∀ x ∈ RmodN S g t, x * e = e * x) : e = 1 := by
  have haQ := H.conj_mem
  have hea : e (aV ht) = aV ht := by
    have hfix : (e (aV ht) : S.Qt) ∈ fixSub S (S.Lbar g) := by
      refine (mem_fixSub S).mpr fun l hl => ?_
      have hlR : resV haQ t ⟨l, Lbar_le_Rbar ht hl⟩ ∈ RmodN S g t := by
        rw [← range_resV haQ t]; exact ⟨_, rfl⟩
      have h1 := LinearEquiv.congr_fun (he _ hlR) (aV ht)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h1
      have hla : resV haQ t ⟨l, Lbar_le_Rbar ht hl⟩ (aV ht) = aV ht := by
        apply Subtype.ext
        rw [coe_resV_apply]
        have := (mem_fixSub S).mp (H.fixSub_eq ▸ Submodule.mem_span_singleton_self
          (S.cl (g * S.z * g⁻¹))) l hl
        exact this
      rw [hla] at h1
      have h2 := congrArg Subtype.val h1
      rw [coe_resV_apply] at h2
      exact h2
    rw [H.fixSub_eq] at hfix
    rcases mem_span_cl_iff.mp hfix with h0 | h0
    · exfalso
      have : e (aV ht) = 0 := Subtype.ext h0
      exact aV_ne_zero H ht (e.injective (this.trans (map_zero e).symm))
    · exact Subtype.ext h0
  refine LinearEquiv.ext fun v => ?_
  by_cases hv0 : v = 0
  · rw [hv0, map_zero, map_zero]
  obtain ⟨x, hx, hxa⟩ := htr v hv0
  have h1 := LinearEquiv.congr_fun (he x hx) (aV ht)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hea] at h1
  rw [← hxa, ← h1]
  rfl

namespace TriHyp

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g} {τ₁ τ₂ : S.O} (T : TriHyp H C ht ht1 hVQ τ₁ τ₂)
include T

theorem forall_comm_of_not_le {k : S.O} (hkR : k ∈ Rbar S g t) (hkN : k ∉ Nbar S g t)
    (hk : ∀ x ∈ Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t) :
    ∀ r s : Rbar S g t,
      Commute (secHom S g t (Vt S g t) (Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt))
          (fun _ hx _ hv => apply_mem_Vt_of_mem_Rbar H.conj_mem hx hv)
          (fun _ hx _ hv => T.apply_mem_U hx hv) r)
        (secHom S g t (Vt S g t) (Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt))
          (fun _ hx _ hv => apply_mem_Vt_of_mem_Rbar H.conj_mem hx hv)
          (fun _ hx _ hv => T.apply_mem_U hx hv) s) := by
  have haQ := H.conj_mem
  have hD := dtEqConj_of_transitive H ht T.data.transitive
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have h15 : 15 ∣ Nat.card (RmodN S g t) :=
    S45Q.fifteen_dvd_card_of_transitive T.data.finrank_eq (aV_ne_zero H ht) T.data.transitive
  obtain ⟨M₀, hM₀X, hM₀n, hM₀s, hM₀i⟩ := S45Q.exists_simple_normal_of_fifteen_dvd
    (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ) T.data.finrank_eq
    (RmodN_le_isometryGroup H C ht ht1 hVQ) h15
  have hrange : ∀ x : Rbar S g t, resV haQ t x ∈ RmodN S g t := fun x => by
    rw [← range_resV haQ t]; exact ⟨x, rfl⟩
  refine forall_comm_of_exists_trivial (resV haQ t) _ (M₀ := M₀) ?_ ?_ hM₀s ?_ ?_
    (τ := ⟨k, hkR⟩) ((secHom_eq_one_iff _ _ _).mpr hk)
    (fun h1 => hkN ((resV_eq_one_iff haQ _).mp h1)) ?_
  · intro m hm
    have hmR := hM₀X hm
    rw [← range_resV haQ t] at hmR
    exact hmR
  · intro x m hm
    have := hM₀n.conj_mem ⟨m, hM₀X hm⟩ (mem_subgroupOf.mpr hm) ⟨resV haQ t x, hrange x⟩
    rw [mem_subgroupOf] at this
    simpa using this
  · intro x y hx hy
    have hx' : (⟨resV haQ t x, hrange x⟩ : RmodN S g t) ∉ M₀.subgroupOf (RmodN S g t) :=
      fun h => hx (mem_subgroupOf.mp h)
    have hy' : (⟨resV haQ t y, hrange y⟩ : RmodN S g t) ∉ M₀.subgroupOf (RmodN S g t) :=
      fun h => hy (mem_subgroupOf.mp h)
    have hI : (M₀.subgroupOf (RmodN S g t)).index = 2 := by
      have h0 : (M₀.subgroupOf (RmodN S g t)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h1 : (M₀.subgroupOf (RmodN S g t)).index ≠ 1 := fun h1 =>
        hx' (by rw [Subgroup.index_eq_one.mp h1]; exact mem_top _)
      have h2 : (M₀.subgroupOf (RmodN S g t)).index ≤ 2 := hM₀i
      omega
    have hiff : (⟨resV haQ t x, hrange x⟩ : RmodN S g t)⁻¹ ∈ M₀.subgroupOf (RmodN S g t) ↔
        (⟨resV haQ t y, hrange y⟩ : RmodN S g t) ∈ M₀.subgroupOf (RmodN S g t) :=
      ⟨fun h => absurd (by simpa using inv_mem h) hx', fun h => absurd h hy'⟩
    have hmem := (Subgroup.mul_mem_iff_of_index_two hI).mpr hiff
    rw [mem_subgroupOf] at hmem
    rw [map_mul, map_inv]
    simpa using hmem
  · intro n hn s
    have hnN : (n : S.O) ∈ Nbar S g t := (resV_eq_one_iff haQ n).mp hn
    refine commute_of_map_commutator_eq_one _ ((secHom_eq_one_iff _ _ _).mpr fun w hw => ?_)
    exact T.data.N0bar_apply (by simpa using commutator_mem_N0bar H hD hnN s.2) (T.U_le_Wt hw)
  · intro hcen
    refine eq_one_of_forall_commute H ht T.data.transitive fun x hx => ?_
    rw [← range_resV haQ t] at hx
    obtain ⟨r, rfl⟩ := hx
    exact hcen r

end TriHyp

end CFSG.LargeExtraspecial.S9.RB
