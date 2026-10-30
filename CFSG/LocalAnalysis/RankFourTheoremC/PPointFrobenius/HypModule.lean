module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.HypDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneModuleLines
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.HypModule

open CFSG.LocalAnalysis.RankThreeTheoremC.PlaneModule
open Subgroup

variable {F : Type*} [Field F] {K : Type*} [Group K] [Fintype K]
  {V : Type*} [AddCommGroup V] [Module F V] {p n : ℕ}

@[expose] def IsHyp (p : ℕ) (U H : Subgroup K) : Prop := H ≤ U ∧ Nat.card U = p * Nat.card H

omit [Fintype K] in
theorem card_cast_ne_zero_of_le [hp : Fact p.Prime] (hpF : (p : F) ≠ 0) {U S : Subgroup K}
    (hU : Nat.card U = p ^ n) (hS : S ≤ U) : ((Nat.card S : ℕ) : F) ≠ 0 := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).1 (hU ▸ Subgroup.card_dvd_of_le hS)
  rw [hk]
  push_cast
  exact pow_ne_zero k hpF

theorem sup_eq_of_isHyp_ne [hp : Fact p.Prime] {U H H' : Subgroup K} (hH : IsHyp p U H)
    (hH' : IsHyp p U H') (hne : H ≠ H') : H ⊔ H' = U := by
  obtain ⟨hHU, hHc⟩ := hH
  obtain ⟨hH'U, hH'c⟩ := hH'
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hcc : Nat.card H' = Nat.card H := by
    have : p * Nat.card H' = p * Nat.card H := by rw [← hHc, ← hH'c]
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos this
  have hsupU : H ⊔ H' ≤ U := sup_le hHU hH'U
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : H ≤ H ⊔ H')
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hsupU
  have h1 : p * Nat.card H = (Nat.card H * k) * m := by rw [← hHc, hm, hk]
  have h2 : p = k * m := by
    have : p * Nat.card H = (k * m) * Nat.card H := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rcases (Nat.dvd_prime hp.out).1 ⟨m, h2⟩ with hk1 | hkp
  · exfalso
    have hMH : Nat.card (H ⊔ H' : Subgroup K) = Nat.card H := by rw [hk, hk1, mul_one]
    have hHM : H = H ⊔ H' := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hMH])
    have hH'H : H' ≤ H := hHM ▸ le_sup_right
    have : H' = H := Subgroup.eq_of_le_of_card_ge hH'H (by rw [hcc])
    exact hne this.symm
  · have h3 : p = p * m := by rw [hkp] at h2; exact h2
    have hm1 : m = 1 := Nat.eq_of_mul_eq_mul_left hp.out.pos (by rw [← h3, mul_one])
    exact Subgroup.eq_of_le_of_card_ge hsupU (le_of_eq (by rw [hm, hm1, mul_one]))

section Proj

variable {U H H' : Subgroup K} (hpF : (p : F) ≠ 0) (ρ : K →* Module.End F V)

section
variable [hp : Fact p.Prime]

include hpF in
theorem hproj_mul_self (hU : Nat.card U = p ^ n) (hH : IsHyp p U H) :
    proj ρ U H * proj ρ U H = proj ρ U H := by
  have cH := card_cast_ne_zero_of_le hpF hU hH.1
  have cU := card_cast_ne_zero_of_le hpF hU (le_refl U)
  have h1 := avg_mul_avg_of_le ρ hH.1 cH
  have h2 := avg_mul_avg_of_le' ρ hH.1 cH
  have h3 := avg_mul_avg_self ρ H cH
  have h4 := avg_mul_avg_self ρ U cU
  simp only [proj_def, sub_mul, mul_sub, h1, h2, h3, h4]
  abel

include hpF in
theorem hproj_mul_proj_of_ne (hU : Nat.card U = p ^ n)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hH : IsHyp p U H) (hH' : IsHyp p U H')
    (hne : H ≠ H') : proj ρ U H * proj ρ U H' = 0 := by
  have hsup := sup_eq_of_isHyp_ne hH hH' hne
  have cH := card_cast_ne_zero_of_le hpF hU hH.1
  have cH' := card_cast_ne_zero_of_le hpF hU hH'.1
  have cU := card_cast_ne_zero_of_le hpF hU (le_refl U)
  have h0 := avg_mul_avg_lines ρ hsup (fun h hh h' hh' => hcomm h (hH.1 hh) h' (hH'.1 hh'))
    cH cH' cU
  have h1 := avg_mul_avg_of_le ρ hH.1 cH
  have h2 := avg_mul_avg_of_le' ρ hH'.1 cH'
  have h4 := avg_mul_avg_self ρ U cU
  simp only [proj_def, sub_mul, mul_sub, h0, h1, h2, h4]
  abel

include hpF in
theorem havg_mul_proj_of_ne (hU : Nat.card U = p ^ n)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hH : IsHyp p U H) (hH' : IsHyp p U H')
    (hne : H' ≠ H) : avg ρ H' * proj ρ U H = 0 := by
  have hsup := sup_eq_of_isHyp_ne hH' hH hne
  have cH := card_cast_ne_zero_of_le hpF hU hH.1
  have cH' := card_cast_ne_zero_of_le hpF hU hH'.1
  have cU := card_cast_ne_zero_of_le hpF hU (le_refl U)
  have h0 := avg_mul_avg_lines ρ hsup (fun h hh h' hh' => hcomm h (hH'.1 hh) h' (hH.1 hh'))
    cH' cH cU
  have h1 := avg_mul_avg_of_le ρ hH'.1 cH'
  rw [proj_def, mul_sub, h0, h1, sub_self]

include hpF in
theorem hfixed_of_mem_range_proj (hU : Nat.card U = p ^ n) (hH : IsHyp p U H) {x : V}
    (hx : x ∈ LinearMap.range (proj ρ U H)) (h : K) (hh : h ∈ H) : ρ h x = x := by
  obtain ⟨y, rfl⟩ := hx
  have cH := card_cast_ne_zero_of_le hpF hU hH.1
  have : proj ρ U H = avg ρ H * (1 - avg ρ U) := by
    rw [proj_def, mul_sub, mul_one, avg_mul_avg_of_le ρ hH.1 cH]
  rw [this, ← Module.End.mul_apply, ← mul_assoc, mul_avg_of_mem ρ hh]

include hpF in
theorem hproj_apply_of_mem_range (hU : Nat.card U = p ^ n) (hH : IsHyp p U H) {x : V}
    (hx : x ∈ LinearMap.range (proj ρ U H)) : proj ρ U H x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [← Module.End.mul_apply, hproj_mul_self hpF ρ hU hH]

include hpF in
theorem hproj_ne_zero_of_fixed (hU : Nat.card U = p ^ n) (hH : IsHyp p U H) {v : V}
    (hv : ∀ h ∈ H, ρ h v = v) (hnv : ∃ u ∈ U, ρ u v ≠ v) : proj ρ U H ≠ 0 := by
  intro h0
  have cH := card_cast_ne_zero_of_le hpF hU hH.1
  have h1 : avg ρ H v = v := avg_apply_of_fixed ρ cH hv
  have h2 : avg ρ U v = v := by
    have h3 := congrArg (fun T : Module.End F V => T v) h0
    simp only [proj_def, LinearMap.sub_apply, h1, LinearMap.zero_apply] at h3
    exact (sub_eq_zero.mp h3).symm
  obtain ⟨u, hu, hne⟩ := hnv
  exact hne (fixed_of_mem_range_avg ρ ⟨v, h2⟩ u hu)

include hpF in
theorem hbil_eq_zero_of_mem_range_proj {W : Type*} [AddCommGroup W] [Module F W]
    (β : V →ₗ[F] V →ₗ[F] W)
    (hinv : ∀ u ∈ U, ∀ v w, β (ρ u v) (ρ u w) = β v w) (hU : Nat.card U = p ^ n)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hH : IsHyp p U H) (hH' : IsHyp p U H')
    (hne : H ≠ H') {v w : V} (hv : v ∈ LinearMap.range (proj ρ U H))
    (hw : w ∈ LinearMap.range (proj ρ U H')) : β v w = 0 ∧ β w v = 0 := by
  classical
  have cH' := card_cast_ne_zero_of_le hpF hU hH'.1
  have hwfix : ∀ h ∈ H', ρ h w = w := fun h hh =>
    hfixed_of_mem_range_proj hpF ρ hU hH' hw h hh
  have havg : avg ρ H' v = 0 := by
    obtain ⟨x, rfl⟩ := hv
    have := havg_mul_proj_of_ne hpF ρ hU hcomm hH hH' hne.symm
    exact congrArg (fun T : Module.End F V => T x) this
  have hsum : ∑ s ∈ Finset.univ.filter (· ∈ H'), ρ s v = 0 := by
    rw [← sumOver_apply, sumOver_eq_card_smul_avg ρ H' cH', LinearMap.smul_apply, havg, smul_zero]
  have hcard : (Finset.univ.filter (· ∈ H')).card = Nat.card H' := card_filter_eq H'
  constructor
  · have h1 : ∑ s ∈ Finset.univ.filter (· ∈ H'), β (ρ s v) w =
        ((Nat.card H' : ℕ) : F) • β v w := by
      have : ∀ s ∈ Finset.univ.filter (· ∈ H'), β (ρ s v) w = β v w := fun s hs => by
        have hs' := (mem_filter_iff H' s).1 hs
        rw [← hinv s (hH'.1 hs') v w, hwfix s hs']
      rw [Finset.sum_congr rfl this, Finset.sum_const, hcard]
      exact (Nat.cast_smul_eq_nsmul F (Nat.card H') _).symm
    have h2 : ∑ s ∈ Finset.univ.filter (· ∈ H'), β (ρ s v) w = 0 := by
      rw [← LinearMap.sum_apply, ← map_sum, hsum, map_zero, LinearMap.zero_apply]
    rw [h2] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_left cH'
  · have h1 : ∑ s ∈ Finset.univ.filter (· ∈ H'), β w (ρ s v) =
        ((Nat.card H' : ℕ) : F) • β w v := by
      have : ∀ s ∈ Finset.univ.filter (· ∈ H'), β w (ρ s v) = β w v := fun s hs => by
        have hs' := (mem_filter_iff H' s).1 hs
        rw [← hinv s (hH'.1 hs') w v, hwfix s hs']
      rw [Finset.sum_congr rfl this, Finset.sum_const, hcard]
      exact (Nat.cast_smul_eq_nsmul F (Nat.card H') _).symm
    have h2 : ∑ s ∈ Finset.univ.filter (· ∈ H'), β w (ρ s v) = 0 := by
      rw [← map_sum, hsum, map_zero]
    rw [h2] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_left cH'

end

section Translates

variable {U H : Subgroup K} {σ : K}

theorem isHyp_map_conj {g : K} (hg : g ∈ normalizer (U : Set K)) (hH : IsHyp p U H) :
    IsHyp p U (H.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg h).mp (hH.1 hh)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hH.2

theorem translate_ne (hσ : MovesHyperplanes p U σ) (hH : IsHyp p U H) {i d : ℕ} (hd1 : 1 ≤ d)
    (hd3 : d ≤ 3) :
    H.map (MulAut.conj (σ ^ i)).toMonoidHom ≠ H.map (MulAut.conj (σ ^ (i + d))).toMonoidHom := by
  intro heq
  obtain ⟨h, hh, hnot⟩ := hσ.2 d hd1 hd3 H hH.1 hH.2
  have hmem : σ ^ (i + d) * h * (σ ^ (i + d))⁻¹ ∈
      H.map (MulAut.conj (σ ^ (i + d))).toMonoidHom := ⟨h, hh, rfl⟩
  rw [← heq] at hmem
  obtain ⟨h'', hh'', he⟩ := hmem
  apply hnot
  have he' : σ ^ i * h'' * (σ ^ i)⁻¹ = σ ^ i * (σ ^ d * h * (σ ^ d)⁻¹) * (σ ^ i)⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
    rw [he, pow_add]
    group
  have : h'' = σ ^ d * h * (σ ^ d)⁻¹ := mul_left_cancel (mul_right_cancel he')
  rw [← this]
  exact hh''

end Translates

omit [Fintype K] in
theorem linearIndependent_of_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Module.End F V) (v : ι → V) (he : ∀ i j, i ≠ j → e i * e j = 0)
    (hv : ∀ i, e i (v i) = v i) (hv0 : ∀ i, v i ≠ 0) : LinearIndependent F v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 : e i (∑ j, g j • v j) = 0 := by rw [hg, map_zero]
  rw [map_sum, Finset.sum_eq_single i] at h1
  · rw [map_smul, hv i] at h1
    exact (smul_eq_zero.mp h1).resolve_right (hv0 i)
  · intro j _ hji
    rw [map_smul]
    have : e i (v j) = 0 := by
      have h2 := congrArg (fun T : Module.End F V => T (v j)) (he i j (Ne.symm hji))
      simpa [Module.End.mul_apply, hv j] using h2
    rw [this, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

section Parts

variable {U H₀ : Subgroup K} {σ : K} [hp : Fact p.Prime] (hpF : (p : F) ≠ 0)
  (ρ : K →* Module.End F V)

include hpF in
theorem exists_parts (hU : Nat.card U = p ^ n) (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    (hσ : MovesHyperplanes p U σ) (hH₀ : IsHyp p U H₀) (hne : proj ρ U H₀ ≠ 0) (m : ℕ)
    (hm : m ≤ 4) :
    ∃ (H : Fin m → Subgroup K) (v : Fin m → V), (∀ i, IsHyp p U (H i)) ∧
      (∀ i j, i ≠ j → H i ≠ H j) ∧ (∀ i, v i ∈ LinearMap.range (proj ρ U (H i))) ∧
      LinearIndependent F v := by
  classical
  let Hs : Fin m → Subgroup K := fun j => H₀.map (MulAut.conj (σ ^ (j : ℕ))).toMonoidHom
  have hnorm : ∀ j : ℕ, σ ^ j ∈ normalizer (U : Set K) := fun j => Subgroup.pow_mem _ hσ.1 j
  have hHyp : ∀ j : Fin m, IsHyp p U (Hs j) := fun j => isHyp_map_conj (hnorm j) hH₀
  have hdist' : ∀ i j : Fin m, i < j → Hs i ≠ Hs j := by
    intro i j hij
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (Fin.lt_def.mp hij)
    have hjm : (j : ℕ) < m := j.2
    have := translate_ne (σ := σ) hσ hH₀ (i := (i : ℕ)) (d := d + 1) (by omega) (by omega)
    have hj : (j : ℕ) = (i : ℕ) + (d + 1) := by omega
    show H₀.map (MulAut.conj (σ ^ (i : ℕ))).toMonoidHom ≠
      H₀.map (MulAut.conj (σ ^ (j : ℕ))).toMonoidHom
    rw [hj]
    exact this
  have hdist : ∀ i j : Fin m, i ≠ j → Hs i ≠ Hs j := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hdist' i j h
    · exact (hdist' j i h).symm
  have hne' : ∀ j : Fin m, proj ρ U (Hs j) ≠ 0 := fun j => proj_conj_ne_zero (hnorm j) hne
  have hW : ∀ j : Fin m, ∃ w, w ∈ LinearMap.range (proj ρ U (Hs j)) ∧ w ≠ 0 := by
    intro j
    have : LinearMap.range (proj ρ U (Hs j)) ≠ ⊥ := by
      rw [Ne, LinearMap.range_eq_bot]
      exact hne' j
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨w, hw, hw0⟩
  choose v hvr hv0 using hW
  refine ⟨Hs, v, hHyp, hdist, hvr, ?_⟩
  exact linearIndependent_of_orthogonal (fun j => proj ρ U (Hs j)) v
    (fun i j hij => hproj_mul_proj_of_ne hpF ρ hU hcomm (hHyp i) (hHyp j) (hdist i j hij))
    (fun j => hproj_apply_of_mem_range hpF ρ hU (hHyp j) (hvr j)) hv0

include hpF in
theorem four_le_finrank_hyp [FiniteDimensional F V] (hU : Nat.card U = p ^ n)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hσ : MovesHyperplanes p U σ)
    (hH₀ : IsHyp p U H₀) (hne : proj ρ U H₀ ≠ 0) : 4 ≤ Module.finrank F V := by
  obtain ⟨H, v, -, -, -, hli⟩ := exists_parts hpF ρ hU hcomm hσ hH₀ hne 4 le_rfl
  simpa using hli.fintype_card_le_finrank

include hpF in
theorem exists_isotropic_three_hyp {W : Type*} [AddCommGroup W] [Module F W]
    (β : V →ₗ[F] V →ₗ[F] W) (hinv : ∀ u ∈ U, ∀ v w, β (ρ u v) (ρ u w) = β v w)
    (halt : ∀ v, β v v = 0) (hU : Nat.card U = p ^ n)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hσ : MovesHyperplanes p U σ)
    (hH₀ : IsHyp p U H₀) (hne : proj ρ U H₀ ≠ 0) :
    ∃ S : Submodule F V, Module.finrank F S = 3 ∧ ∀ s ∈ S, ∀ s' ∈ S, β s s' = 0 := by
  obtain ⟨H, v, hHyp, hdist, hrange, hli⟩ := exists_parts hpF ρ hU hcomm hσ hH₀ hne 3 (by norm_num)
  refine ⟨Submodule.span F (Set.range v), ?_, ?_⟩
  · rw [finrank_span_eq_card hli]
    simp
  · have key : ∀ i j : Fin 3, β (v i) (v j) = 0 := by
      intro i j
      by_cases hij : i = j
      · subst hij
        exact halt _
      · exact (hbil_eq_zero_of_mem_range_proj hpF ρ β hinv hU hcomm (hHyp i) (hHyp j)
          (hdist i j hij) (hrange i) (hrange j)).1
    intro s hs s' hs'
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hs' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact key i j
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
      | smul c y _ hy => rw [map_smul, hy, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

end Parts

end Proj

section Group

theorem not_dvd_card_of_isElementaryAbelian {A : Type*} [Group A] [Finite A] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) [IsElementaryAbelian q A] :
    ¬ p ∣ Nat.card A := by
  intro hd
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup q A).exists_card_eq
  rw [hk] at hd
  exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp
    (Nat.Prime.dvd_of_dvd_pow Fact.out hd))

theorem exists_hyperplane_fixed_not_fixed {J : Type} [Group J] [Finite J] {A : Type} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hpA : ¬ p ∣ Nat.card A) [MulDistribMulAction J A] {U : Subgroup J}
    (hexp : ∀ u ∈ U, u ^ p = 1) (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    (hnt : ∃ u ∈ U, ∃ a : A, u • a ≠ a) :
    ∃ H : Subgroup J, H ≤ U ∧ Nat.card U = p * Nat.card H ∧
      ∃ a : A, (∀ h ∈ H, h • a = a) ∧ ∃ u ∈ U, u • a ≠ a := by
  classical
  haveI : CFSG.IsElementaryAbelian p U := CFSG.IsElementaryAbelian.of_forall hcomm hexp
  obtain ⟨u₀, hu₀, a₀, ha₀⟩ := hnt
  haveI : Nontrivial U := nontrivial_of_ne (⟨u₀, hu₀⟩ : U) 1 (fun h => ha₀ (by
    have h1 : u₀ = 1 := congrArg Subtype.val h
    rw [h1, one_smul]))
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := ↥U) (H := A) hpA
  by_contra hcon
  push Not at hcon
  have hle : (⨆ (B : Subgroup U) (_ : B.index = p), CFSG.fixedPointSubgroup B A) ≤
      CFSG.fixedPointSubgroup (⊤ : Subgroup U) A := by
    refine iSup₂_le fun B hB a ha g => ?_
    have hcard : Nat.card U = p * Nat.card (B.map U.subtype) := by
      rw [Subgroup.card_map_of_injective U.subtype_injective, mul_comm, ← hB]
      exact B.card_mul_index.symm
    have hfix : ∀ h ∈ B.map U.subtype, h • a = a := by
      rintro _ ⟨b, hb, rfl⟩
      exact ha ⟨b, hb⟩
    exact hcon _ (Subgroup.map_subtype_le B) hcard a hfix g.1.1 g.1.2
  rw [hgen] at hle
  exact ha₀ (hle (Subgroup.mem_top a₀) ⟨⟨u₀, hu₀⟩, Subgroup.mem_top _⟩)

end Group

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.HypModule
