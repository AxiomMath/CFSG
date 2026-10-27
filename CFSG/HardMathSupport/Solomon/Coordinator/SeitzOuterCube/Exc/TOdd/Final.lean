module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.LocalGen
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TrialityOddReduce

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding TauCeti
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.HardMathSupport.Seitz.TrialityOdd (exists_trialityD4_model_odd)

set_option linter.unusedSectionVars false


theorem trialityOddLocalGen_holds : TrialityOddLocalGen := by
  intro q hv hq2 hq3 Y _ _ K hKn hC he hno E hE hEc a haEK ha1 k hk hka
  haveI : K.Normal := hKn
  obtain ⟨e₀⟩ := he
  obtain ⟨X, _, _, σ, hX, hσ, ⟨φ⟩⟩ := exists_trialityD4_model_odd hq2 (K := K) ⟨hv, ⟨e₀⟩⟩
  have P : D4ParOdd q.p q.exponent X σ := ⟨q.prime_p, hq2, hq3, q.exponent_pos, hX, hσ⟩
  haveI : Finite (C0 σ) := finite_C0
  have haK : a ∈ K := (Subgroup.mem_inf.1 haEK).2
  have haE : a ∈ E := (Subgroup.mem_inf.1 haEK).1
  set ρ : Y →* MulAut (C0 σ) := (MulAut.congr φ).toMonoidHom.comp MulAut.conjNormal with hρ
  have hρapp : ∀ (y : Y) (m : C0 σ), ρ y m = φ (MulAut.conjNormal y (φ.symm m)) := fun y m => rfl
  have hρK : ∀ k' : K, ρ k' = MulAut.conj (φ k') := by
    intro k'
    ext m
    rw [hρapp, MulAut.conj_apply]
    have : MulAut.conjNormal (k' : Y) (φ.symm m) = k' * φ.symm m * k'⁻¹ :=
      Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
    rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyC : y ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 := congrArg (fun α : MulAut (C0 σ) => φ.symm (α (φ ⟨w, hw⟩))) hy
      simp only [hρapp, MulEquiv.symm_apply_apply, MulAut.one_apply] at h1
      have h2 := congrArg Subtype.val h1
      rw [MulAut.conjNormal_apply] at h2
      calc w * y = (y * w * y⁻¹) * y := by rw [h2]
        _ = y * w := by group
    rw [hC, Subgroup.mem_bot] at hyC
    exact hyC
  set Ê : Subgroup (MulAut (C0 σ)) := E.map ρ with hÊ
  have hÊab : IsElemAbelian 3 Ê := CFSG.Open.IsElemAbelian.map hE ρ
  have hÊc : Nat.card Ê = 27 := by
    rw [hÊ, Subgroup.card_map_of_injective hρinj, hEc]
    norm_num
  set x : C0 σ := φ ⟨a, haK⟩ with hxdef
  have hρa : ρ a = MulAut.conj x := hρK ⟨a, haK⟩
  have hxÊ : MulAut.conj x ∈ Ê := ⟨a, haE, hρa⟩
  have hx1 : x ≠ 1 := by
    intro h
    apply ha1
    have h' : (⟨a, haK⟩ : K) = 1 := φ.injective (by rw [← hxdef, h, map_one])
    exact congrArg Subtype.val h'
  have hA : Nat.card (E ⊓ K : Subgroup Y) = 3 ^ 2 :=
    card_inf_eq_nine_trialityOdd hv hq2 hC ⟨e₀⟩ hno hE hEc
  have ha3 : a ^ 3 = 1 := hE.2 a haE
  obtain ⟨b₀, hb₀, hb₀a⟩ : ∃ b₀ ∈ E ⊓ K, b₀ ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : E ⊓ K ≤ Subgroup.zpowers a := fun b hb => hcon b hb
    have h1 := Subgroup.card_le_of_le hle
    rw [hA, Nat.card_zpowers] at h1
    have h2 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha3
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  have hb₀K : b₀ ∈ K := (Subgroup.mem_inf.1 hb₀).2
  have hb₀E : b₀ ∈ E := (Subgroup.mem_inf.1 hb₀).1
  set b : C0 σ := φ ⟨b₀, hb₀K⟩ with hbdef
  have hρb : ρ b₀ = MulAut.conj b := hρK ⟨b₀, hb₀K⟩
  have hbÊ : MulAut.conj b ∈ Ê := ⟨b₀, hb₀E, hρb⟩
  have hbx : MulAut.conj b ∉ Subgroup.zpowers (MulAut.conj x) := by
    rintro ⟨n, hn⟩
    apply hb₀a
    refine ⟨n, hρinj ?_⟩
    simp only at hn
    rw [map_zpow, hρa, hρb, hn]
  obtain ⟨e₁, he₁E, he₁K⟩ : ∃ e₁ ∈ E, e₁ ∉ K := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ E ⊓ K := fun y hy => Subgroup.mem_inf.2 ⟨hy, hcon y hy⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hA, hEc] at h1
    norm_num at h1
  have heÊ : ρ e₁ ∈ Ê := ⟨e₁, he₁E, rfl⟩
  have hein : ρ e₁ ∉ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range := by
    rintro ⟨m, hm⟩
    apply he₁K
    have h1 : ρ e₁ = ρ (φ.symm m) := by
      rw [hρK, MulEquiv.apply_symm_apply]
      exact hm.symm
    rw [hρinj h1]
    exact (φ.symm m).2
  have key := cen_le_closure_model_odd P hÊab hÊc hxÊ hx1 hbÊ hbx heÊ hein
  have hkx : φ ⟨k, hk⟩ ∈ cenX σ x := by
    rw [Subgroup.mem_centralizer_singleton_iff, hxdef, ← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hka)
  have hmem := key hkx
  set ψ : C0 σ →* Y := K.subtype.comp φ.symm.toMonoidHom with hψ
  have h2 : ψ (φ ⟨k, hk⟩) ∈ (Subgroup.closure {l | l ∈ cenX σ x ∧ ∃ y ∈ Ê,
      y ∉ Subgroup.zpowers (MulAut.conj x : MulAut (C0 σ)) ∧ y l = l}).map ψ := ⟨_, hmem, rfl⟩
  rw [MonoidHom.map_closure] at h2
  have hψk : ψ (φ ⟨k, hk⟩) = k := by
    rw [hψ, MonoidHom.comp_apply]
    show ((φ.symm (φ ⟨k, hk⟩) : K) : Y) = k
    rw [MulEquiv.symm_apply_apply]
  rw [hψk] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨l, ⟨hl, y, ⟨e', he'E, rfl⟩, hyx, hyl⟩, rfl⟩
  have hψl : ψ l = ((φ.symm l : K) : Y) := rfl
  refine ⟨by rw [hψl]; exact (φ.symm l).2, ?_, e', he'E, ?_, ?_⟩
  · rw [hψl]
    have hl' : l * x = x * l := Subgroup.mem_centralizer_singleton_iff.1 hl
    have h3 := congrArg φ.symm hl'
    rw [map_mul, map_mul, hxdef, MulEquiv.symm_apply_apply] at h3
    exact congrArg Subtype.val h3
  · rintro ⟨n, hn⟩
    apply hyx
    refine ⟨n, ?_⟩
    simp only at hn ⊢
    rw [← hρa, ← map_zpow, hn]
  · rw [hψl]
    have h4 : φ.symm (ρ e' l) = φ.symm l := congrArg φ.symm hyl
    rw [hρapp, MulEquiv.symm_apply_apply] at h4
    have h5 := congrArg Subtype.val h4
    rw [MulAut.conjNormal_apply] at h5
    calc ((φ.symm l : K) : Y) * e' = e' * ((φ.symm l : K) : Y) * e'⁻¹ * e' := by rw [h5]
      _ = e' * ((φ.symm l : K) : Y) := by group

theorem trialityOuterCubesThreeOdd_holds : TrialityOuterCubesThreeOdd :=
  trialityOuterCubesThreeOdd_of_localGen trialityOddLocalGen_holds

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
