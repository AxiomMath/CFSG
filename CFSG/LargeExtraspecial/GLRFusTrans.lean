module

public import CFSG.LargeExtraspecial.GLRFusFix
public import CFSG.LargeExtraspecial.GLRFusInj
public import CFSG.LargeExtraspecial.GLRLinGL
public import CFSG.LargeExtraspecial.GLRLinRoot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

namespace Mixed

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} {k : G} {α β : S.Qt}

theorem exists_kerB_notMem (hM : Mixed S X A B k α β) :
    ∃ u ∈ kerB A β, u ∉ Submodule.span (ZMod 2) ({α} : Set S.Qt) := by
  by_contra hc
  push Not at hc
  have h1 := Submodule.finrank_mono (show kerB A β ≤ Submodule.span (ZMod 2) {α} from hc)
  have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({α} : Set S.Qt)) ≤ 1 := by
    have := finrank_span_le_card (R := ZMod 2) ({α} : Set S.Qt)
    simpa using this
  have h3 := hM.finrank_kerB
  have h5 := hM.five_le
  omega

theorem exists_fixed (hM : Mixed S X A B k α β) :
    ∃ u₀ ∈ kerB A β, u₀ ∉ Submodule.span (ZMod 2) ({α} : Set S.Qt) ∧
      ∀ e ∈ S.Lbar k ⊓ X, (e : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀ - u₀ ∈
        Submodule.span (ZMod 2) ({α} : Set S.Qt) := by
  classical
  set K := kerB A β
  set Nα := Submodule.span (ZMod 2) ({α} : Set S.Qt)
  set N : Submodule (ZMod 2) K := Nα.comap K.subtype
  set E₀ := S.Lbar k ⊓ X
  let res : E₀ → (K →ₗ[ZMod 2] K) := fun e =>
    ((e : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap.restrict
      (fun u hu => hM.apply_kerB_mem e.2 hu)
  have hres : ∀ (e : E₀) (u : K),
      ((res e u : K) : S.Qt) = ((e : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u := fun _ _ => rfl
  have hN : ∀ e : E₀, N ≤ N.comap (res e) := by
    intro e u hu
    change ((res e u : K) : S.Qt) ∈ Nα
    rw [hres]
    rcases mem_span_singleton_iff.mp hu with h0 | h1
    · change (u : S.Qt) = 0 at h0
      rw [h0, map_zero]; exact Nα.zero_mem
    · change (u : S.Qt) = α at h1
      rw [h1, (hM.fix_of_mem e.2).1]; exact Submodule.mem_span_singleton_self _
  let act : E₀ → (K ⧸ N) → (K ⧸ N) := fun e => N.mapQ N (res e) (hN e)
  have hact : ∀ (e : E₀) (u : K),
      act e (Submodule.Quotient.mk u) = Submodule.Quotient.mk (res e u) :=
    fun e u => Submodule.mapQ_apply _ _ _ _
  let _ : MulAction E₀ (K ⧸ N) :=
    { smul := act
      one_smul := fun t => by
        refine Submodule.Quotient.induction_on N t fun u => ?_
        change act 1 _ = _
        rw [hact]
        rfl
      mul_smul := fun e₁ e₂ t => by
        refine Submodule.Quotient.induction_on N t fun u => ?_
        change act (e₁ * e₂) _ = act e₁ (act e₂ _)
        rw [hact, hact, hact]
        rfl }
  have hP : IsPGroup 2 E₀ := (isPGroup_Lbar hM.conj_mem).to_le inf_le_left
  have : Finite (K ⧸ N) := Module.finite_of_finite (ZMod 2)
  have hdvd : 2 ∣ Nat.card (K ⧸ N) := by
    obtain ⟨u, hu, huα⟩ := hM.exists_kerB_notMem
    have hlt : N < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun e => huα ?_
      have : (⟨u, hu⟩ : K) ∈ N := e ▸ Submodule.mem_top
      exact this
    have : Nontrivial (K ⧸ N) := Submodule.Quotient.nontrivial_iff.mpr hlt.ne
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 (Module.finrank_pos (R := ZMod 2) (M := K ⧸ N)).ne'
  have h0 : (0 : K ⧸ N) ∈ MulAction.fixedPoints E₀ (K ⧸ N) := by
    rw [MulAction.mem_fixedPoints]
    intro e
    change act e 0 = 0
    exact map_zero _
  obtain ⟨b, hb, hb0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (K ⧸ N) hdvd h0
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective N b
  refine ⟨u, u.2, fun hu => hb0 ?_, fun e he => ?_⟩
  · exact ((Submodule.Quotient.mk_eq_zero N).mpr hu).symm
  · have h1 := (MulAction.mem_fixedPoints.mp hb) ⟨e, he⟩
    change act ⟨e, he⟩ _ = _ at h1
    rw [hact, Submodule.Quotient.eq] at h1
    exact h1

theorem apply_K (hM : Mixed S X A B k α β) {e : S.O} (he : e ∈ S.Lbar k ⊓ X) {u : S.Qt}
    (hu : u ∈ kerB A β) :
    (e : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Submodule.span (ZMod 2) ({α} : Set S.Qt) := by
  set Nα := Submodule.span (ZMod 2) ({α} : Set S.Qt)
  obtain ⟨u₀, hu₀K, hu₀α, hfix⟩ := hM.exists_fixed
  have heα := (hM.fix_of_mem he).1
  have hNα : ∀ v ∈ Nα, (e : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v = 0 := by
    intro v hv
    rcases mem_span_singleton_iff.mp hv with rfl | rfl
    · rw [map_zero, sub_zero]
    · rw [heα, sub_self]
  by_cases huα : u ∈ Nα
  · rw [hNα u huα]; exact Nα.zero_mem
  by_cases hd : u - u₀ ∈ Nα
  · have e1 : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u =
        ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀ - u₀) +
          ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) (u - u₀) - (u - u₀)) := by rw [map_sub]; abel
    rw [e1, hNα _ hd, add_zero]
    exact hfix e he
  set d := u - u₀ with hd_def
  have hdK : d ∈ kerB A β := (kerB A β).sub_mem hu hu₀K
  have hU : Submodule.span (ZMod 2) ({α, d} : Set S.Qt) ≤ A := by
    rw [Submodule.span_le]
    rintro v (rfl | rfl)
    exacts [hM.mem_A, hdK.1]
  have hu₀U : u₀ ∉ Submodule.span (ZMod 2) ({α, d} : Set S.Qt) := by
    intro hm
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hm
    rcases zmod2_eq_zero_or_one b with rfl | rfl
    · rw [zero_smul, add_zero] at hab
      exact hu₀α (hab ▸ Nα.smul_mem _ (Submodule.mem_span_singleton_self α))
    · rw [one_smul, hd_def] at hab
      apply huα
      have e3 : u = -(a • α) + (u₀ + u₀) := by
        calc u = -(a • α) + (u₀ + (a • α + (u - u₀))) := by abel
          _ = -(a • α) + (u₀ + u₀) := by rw [hab]
      rw [e3, two_vec, add_zero]
      exact Nα.neg_mem (Nα.smul_mem _ (Submodule.mem_span_singleton_self α))
  obtain ⟨c, -, hcU, hc1⟩ := hM.pair.exists_polar_sep hU hu₀K.1 hu₀U
  have hαc : polar S.q α c = 0 := hcU α (Submodule.subset_span (by simp))
  have hdc : polar S.q d c = 0 := hcU d (Submodule.subset_span (by simp))
  obtain ⟨t, ht, hta⟩ := hM.pair.exists_transvection hdK.1 hdc
  have htα : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α := by
    rw [hta α hM.mem_A, hαc, zero_smul, add_zero]
  have htβ : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) β = β := by
    refine (hM.pair.apply_eq_self_iff ht hM.mem_B).mpr fun a ha => ?_
    have hdβ : polar S.q d β = 0 := hdK.2
    rw [hta a ha, polar_add_left, polar_smul_left, hdβ, smul_zero, add_zero]
  have htu : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀ = u := by
    rw [hta u₀ hu₀K.1, hc1, one_smul, hd_def]; abel
  have he' := hM.conj_mem_E' ht htα htβ he
  have hcomm : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) u =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (((t⁻¹ * e * t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀) := by
    rw [← htu, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul,
      ← Subgroup.coe_mul, show t * (t⁻¹ * e * t) = e * t by group]
  rw [hcomm, ← htu, ← map_sub]
  rcases mem_span_singleton_iff.mp (hfix _ he') with h0 | h1
  · rw [h0, map_zero]; exact Nα.zero_mem
  · rw [h1, htα]; exact Submodule.mem_span_singleton_self _

end Mixed

end CFSG.LargeExtraspecial.GLR
