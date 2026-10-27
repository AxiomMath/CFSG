module

public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LieType.Chevalley.TwistHolds
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Simplicity.Torus
public import CFSG.LieType.Ree.TitsWeyl
import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedD4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

section Weyl

abbrev twBlock
    (i : Fin d4.rank) : WeylGroup d4 :=
  (coxeterSystem d4).wordProd (twistOrbitWord .D4 i)

theorem twistBlockCheck : ∀ i : Fin d4.rank, ∀ β ∈ prefixRoots d4 (twistOrbitWord .D4 i),
    (∀ k, k ≠ i → k ≠ rhoPerm i → k ≠ rhoPerm (rhoPerm i) → β k = 0) ∧ (∀ k, 0 ≤ β k) ∧
      β ≠ 0 := by
  decide +kernel

theorem isReduced_twistOrbitWord
    (i : Fin d4.rank) :
    (coxeterSystem d4).IsReduced (twistOrbitWord .D4 i) :=
  isReduced_of_reducedCheck (by revert i; decide +kernel)

theorem twistOrbitWord_length_pos (i : Fin d4.rank) : 0 < (twistOrbitWord .D4 i).length := by
  revert i
  decide

theorem twBlock_mul_self
    (i : Fin d4.rank) : twBlock i * twBlock i = 1 := by
  rw [twBlock, ← CoxeterSystem.wordProd_append]
  refine ext_single fun k => ?_
  rw [wordProd_smul, one_smul]
  revert i k
  decide +kernel

variable {w : WeylGroup d4}

theorem height_smul_rhoPerm_neg
    (hw : weylTwist .D4 w = w) {i : Fin d4.rank}
    (hi : height (w • (Pi.single i 1 : Fin d4.rank → ℤ)) < 0) :
    height (w • (Pi.single (rhoPerm i) 1 : Fin d4.rank → ℤ)) < 0 := by
  have h := weylTwist_smul_permLattice .D4 w (Pi.single i 1)
  rw [hw, permLattice_single] at h
  rw [h, height_permLattice]
  exact hi

theorem length_mul_twBlock_add
    (hw : weylTwist .D4 w = w) {i : Fin d4.rank}
    (hi : height (w • (Pi.single i 1 : Fin d4.rank → ℤ)) < 0) :
    (coxeterSystem d4).length (w * twBlock i) + (twistOrbitWord .D4 i).length =
      (coxeterSystem d4).length w := by
  have h1 := height_smul_rhoPerm_neg hw hi
  have h2 := height_smul_rhoPerm_neg hw h1
  refine length_mul_wordProd_add _ w (descentWord_of_prefixRoots _ w fun β hβ => ?_)
  obtain ⟨hsupp, hnn, hne⟩ := twistBlockCheck i β hβ
  refine height_smul_neg_of_support (J := {i, rhoPerm i, rhoPerm (rhoPerm i)})
    (fun j hj => ?_) (fun k hk => hsupp k (fun h => hk (by simp [h]))
      (fun h => hk (by simp [h])) (fun h => hk (by simp [h]))) hnn hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  exacts [hi, h1, h2]

variable {K : Type} [Field K] (σ : K →+* K)

theorem twistOrbitWord_D4 (i : Fin d4.rank) :
    twistOrbitWord .D4 i = if i = nd 2 then [nd 2] else [nd 0, nd 1, nd 3] := by
  revert i
  decide

theorem nrep_twBlock_mem
    (i : Fin d4.rank) :
    Chevalley.nrep d4 K (twBlock i) ∈ twistedGroup σ := by
  rw [Chevalley.nrep_eq_prod d4 K (isReduced_twistOrbitWord i), twistOrbitWord_D4]
  split_ifs
  · have h := nHatE_mem (K := K) σ (ng 0)
    rw [nHatE_zero] at h
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact h
  · have h := nHatE_mem (K := K) σ (ng 1)
    rw [nHatE_one] at h
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ← mul_assoc]
    exact h

theorem nrep_mem_twistedGroup
    (hw : w ∈ relWeylTwist .D4) :
    Chevalley.nrep d4 K w ∈ twistedGroup σ := by
  suffices h : ∀ n (w : WeylGroup d4), (coxeterSystem d4).length w = n →
      weylTwist .D4 w = w → Chevalley.nrep d4 K w ∈ twistedGroup σ from h _ w rfl hw
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn hw
    by_cases h1 : w = 1
    · rw [h1, Chevalley.nrep_one]
      exact one_mem _
    obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one h1
    have hlen := length_mul_twBlock_add hw hi
    have hpos := twistOrbitWord_length_pos i
    have hδ : weylTwist .D4 (w * twBlock i) = w * twBlock i := by
      rw [map_mul, hw, (mem_relWeylTwist .D4).1 (twistOrbitWord_mem .D4 i)]
    have hmem := ih _ (by omega) (w * twBlock i) rfl hδ
    have hb : (coxeterSystem d4).length (twBlock i) = (twistOrbitWord .D4 i).length :=
      isReduced_twistOrbitWord i
    have hw' : w = w * twBlock i * twBlock i := by rw [mul_assoc, twBlock_mul_self, mul_one]
    have hl : (coxeterSystem d4).length (w * twBlock i * twBlock i) =
        (coxeterSystem d4).length (w * twBlock i) + (coxeterSystem d4).length (twBlock i) := by
      rw [← hw', hb]
      omega
    rw [hw', Chevalley.nrep_mul K hl]
    exact mul_mem hmem (nrep_twBlock_mem σ i)

end Weyl

section Borel

variable {K : Type} [Field K] [Finite K] (σ : K →+* K)

theorem nativeData_X_eq
    (α : Root d4) :
    (nativeData d4 K).X α = rootGroup (rootOperatorFamily d4) K α.1 :=
  (rootGroup_of_isRoot α.2).symm

theorem nativeU_le :
    (nativeData d4 K).U ≤
    ⨆ γ ∈ {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧ 0 < ht γ}, rootGroup (rootOperatorFamily d4) K γ :=
  iSup₂_le fun α hα => by
    rw [nativeData_X_eq]
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧ 0 < ht γ}) =>
      rootGroup (rootOperatorFamily d4) K γ) α.1 ⟨α.2, hα⟩ le_rfl

theorem ht_rho (v : Fin d4.rank → ℤ) : ht (rho v) = ht v := by
  rw [← ht_proj, proj_rho, ht_proj]

theorem nativeU_inf_twistFixed_le :
    (nativeData d4 K).U ⊓ twistFixed .D4 K σ ≤ twistedGroup σ := by
  intro u hu
  obtain ⟨hU, hF⟩ := Subgroup.mem_inf.1 hu
  have h := iSup_rootGroup_inf_twistFixed_le σ (f := htHom)
    (fun v => by rw [htHom_apply, htHom_apply, ht_rho])
    (Ψ := {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧ 0 < ht γ}) (fun α hα => hα)
    (fun α hα β hβ hr => ⟨hr, by rw [ht_add]; linarith [hα.2, hβ.2]⟩)
    (fun α hα => ⟨isRoot_rho hα.1, by rw [ht_rho]; exact hα.2⟩)
    (Subgroup.mem_inf.2 ⟨nativeU_le hU, hF⟩)
  refine (iSup₂_le fun β hβ => ?_ : ⨆ β ∈ proj '' {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧
    0 < ht γ}, twistedRootSubgroupD4 σ β ≤ twistedGroup σ) h
  obtain ⟨α, hα, rfl⟩ := hβ
  exact twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj hα.1)

theorem exists_mul_of_mem_B_of_mem_twistFixed
    {b : adjointGroup d4 K}
    (hb : b ∈ (nativeData d4 K).B) (hF : b ∈ twistFixed .D4 K σ) :
    ∃ u ∈ (nativeData d4 K).U, u ∈ twistFixed .D4 K σ ∧
      ∃ h ∈ (nativeData d4 K).H, h ∈ twistFixed .D4 K σ ∧ b = u * h := by
  obtain ⟨u, hu, h, hh, rfl⟩ := CFSG.LieType.Simplicity.exists_mul_of_mem_B hb
  have hFu := twistC_mem_U .D4 K σ hu
  have hFh := twistC_mem_H .D4 K σ hh
  have hF' : twistC .D4 K σ u * twistC .D4 K σ h = u * h := by
    rw [← map_mul]
    exact hF
  have e : u⁻¹ * twistC .D4 K σ u = h * (twistC .D4 K σ h)⁻¹ := by
    calc u⁻¹ * twistC .D4 K σ u
        = u⁻¹ * (twistC .D4 K σ u * twistC .D4 K σ h) * (twistC .D4 K σ h)⁻¹ := by group
      _ = u⁻¹ * (u * h) * (twistC .D4 K σ h)⁻¹ := by rw [hF']
      _ = h * (twistC .D4 K σ h)⁻¹ := by group
  have hmem : u⁻¹ * twistC .D4 K σ u ∈ (nativeData d4 K).H ⊓ (nativeData d4 K).U :=
    Subgroup.mem_inf.2 ⟨by rw [e]; exact mul_mem hh (inv_mem hFh), mul_mem (inv_mem hu) hFu⟩
  have : Fact (ringChar K).Prime := ⟨CharP.prime_ringChar K⟩
  rw [CFSG.LieType.Simplicity.H_inf_U_eq_bot (ringChar K), Subgroup.mem_bot,
    inv_mul_eq_one] at hmem
  have hu' : twistC .D4 K σ u = u := hmem.symm
  rw [hu'] at hF'
  exact ⟨u, hu, hu', h, hh, mul_left_cancel hF', rfl⟩

theorem conj_mem_twistedRootSubgroupD4_of_mem_H
    {h : adjointGroup d4 K}
    (hh : h ∈ (nativeData d4 K).H) (hF : twistC .D4 K σ h = h) {β : Fin (Tag.rank .G2) → ℤ}
    (hβ : IsRoot .G2 β) {x : adjointGroup d4 K} (hx : x ∈ twistedRootSubgroupD4 σ β) :
    h * x * h⁻¹ ∈ twistedRootSubgroupD4 σ β := by
  obtain ⟨α, hα, hp⟩ := exists_proj_eq hβ
  obtain ⟨hx', hxF⟩ := (mem_twistedRootSubgroupD4_iff σ hα hp x).1 hx
  refine (mem_twistedRootSubgroupD4_iff σ hα hp _).2 ⟨?_, ?_⟩
  · have hc : ∀ γ : Fin d4.rank → ℤ, IsRoot d4 γ → ∀ y ∈ rootGroup (rootOperatorFamily d4) K γ,
        h * y * h⁻¹ ∈ rootGroup (rootOperatorFamily d4) K γ := fun γ hγ y hy => by
      rw [← nativeData_X_eq ⟨γ, hγ⟩] at hy ⊢
      exact conj_mem_X_of_mem_H hh hy
    have hle : rootGroup (rootOperatorFamily d4) K α ⊔
        rootGroup (rootOperatorFamily d4) K (rho α) ⊔
          rootGroup (rootOperatorFamily d4) K (rho (rho α)) ≤
        (rootGroup (rootOperatorFamily d4) K α ⊔ rootGroup (rootOperatorFamily d4) K (rho α) ⊔
          rootGroup (rootOperatorFamily d4) K (rho (rho α))).comap
            (MulAut.conj h).toMonoidHom := by
      refine sup_le (sup_le (fun y hy => ?_) (fun y hy => ?_)) (fun y hy => ?_)
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hc α hα y hy))
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (hc _ (isRoot_rho hα) y hy))
      · exact Subgroup.mem_sup_right (hc _ (isRoot_rho (isRoot_rho hα)) y hy)
    exact hle hx'
  · rw [map_mul, map_mul, map_inv, hF, hxF]

theorem conj_mem_twistedGroup_of_mem_H
    {h : adjointGroup d4 K} (hh : h ∈ (nativeData d4 K).H)
    (hF : twistC .D4 K σ h = h) {x : adjointGroup d4 K} (hx : x ∈ twistedGroup σ) :
    h * x * h⁻¹ ∈ twistedGroup σ :=
  conj_mem_of_forall_mem (X := twistedRootSubgroupD4 σ)
    (fun _ hβ _ hy => twistedRootSubgroupD4_le_twistedGroup σ hβ
      (conj_mem_twistedRootSubgroupD4_of_mem_H σ hh hF hβ hy)) hx

end Borel

section Derived

variable {K : Type} [Field K] [Finite K] (σ : K →+* K)

theorem exists_mul_of_mem_twistFixed
    {g : adjointGroup d4 K} (hg : g ∈ twistFixed .D4 K σ) :
    ∃ n ∈ twistedGroup σ, ∃ t ∈ (nativeData d4 K).H, t ∈ twistFixed .D4 K σ ∧ g = n * t := by
  obtain ⟨w, hw, b₁, hb₁, hb₁F, b₂, hb₂, hb₂F, rfl⟩ :=
    twistFixed_bruhat .D4 K σ (surjective_ringHom_of_finite K σ) g hg
  obtain ⟨u₁, hu₁, hu₁F, h₁, hh₁, hh₁F, rfl⟩ := exists_mul_of_mem_B_of_mem_twistFixed σ hb₁ hb₁F
  obtain ⟨u₂, hu₂, hu₂F, h₂, hh₂, hh₂F, rfl⟩ := exists_mul_of_mem_B_of_mem_twistFixed σ hb₂ hb₂F
  have hU : ∀ {u : adjointGroup d4 K}, u ∈ (nativeData d4 K).U → u ∈ twistFixed .D4 K σ →
      u ∈ twistedGroup σ := fun hu hF =>
    nativeU_inf_twistFixed_le σ (Subgroup.mem_inf.2 ⟨hu, hF⟩)
  refine ⟨u₁ * (h₁ * Chevalley.nrep d4 K w * h₁⁻¹) * (h₁ * u₂ * h₁⁻¹), ?_, h₁ * h₂,
    mul_mem hh₁ hh₂, mul_mem hh₁F hh₂F, by group⟩
  exact mul_mem (mul_mem (hU hu₁ hu₁F)
    (conj_mem_twistedGroup_of_mem_H σ hh₁ hh₁F (nrep_mem_twistedGroup σ hw)))
    (conj_mem_twistedGroup_of_mem_H σ hh₁ hh₁F (hU hu₂ hu₂F))

theorem commutator_twistFixed_le :
    ⁅twistFixed .D4 K σ, twistFixed .D4 K σ⁆ ≤ twistedGroup σ := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨n₁, hn₁, t₁, ht₁, ht₁F, rfl⟩ := exists_mul_of_mem_twistFixed σ hg₁
  obtain ⟨n₂, hn₂, t₂, ht₂, ht₂F, rfl⟩ := exists_mul_of_mem_twistFixed σ hg₂
  have hc : t₂ * t₁⁻¹ = t₁⁻¹ * t₂ :=
    ((CFSG.LieType.Simplicity.commute_of_mem_H ht₁ ht₂).inv_left.eq).symm
  have e : ⁅n₁ * t₁, n₂ * t₂⁆ = n₁ * (t₁ * n₂ * t₁⁻¹) * (t₂ * n₁⁻¹ * t₂⁻¹) * n₂⁻¹ := by
    calc ⁅n₁ * t₁, n₂ * t₂⁆ = n₁ * t₁ * n₂ * (t₂ * t₁⁻¹) * n₁⁻¹ * t₂⁻¹ * n₂⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = n₁ * (t₁ * n₂ * t₁⁻¹) * (t₂ * n₁⁻¹ * t₂⁻¹) * n₂⁻¹ := by
          rw [hc]
          group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hn₁ (conj_mem_twistedGroup_of_mem_H σ ht₁ ht₁F hn₂))
    (conj_mem_twistedGroup_of_mem_H σ ht₂ ht₂F (inv_mem hn₁))) (inv_mem hn₂)

omit [Finite K] in
theorem twistedGroup_le_commutator
    (hperf : Group.IsPerfect (twistedGroup σ)) :
    twistedGroup σ ≤ ⁅twistFixed .D4 K σ, twistFixed .D4 K σ⁆ := by
  intro x hx
  have hx' : (⟨x, hx⟩ : twistedGroup σ) ∈ commutator (twistedGroup σ) := by
    rw [Group.isPerfect_def.1 hperf]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem (twistedGroup σ).subtype hx'
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hmap
  exact Subgroup.commutator_mono (twistedGroup_le_twistFixed σ) (twistedGroup_le_twistFixed σ)
    hmap

theorem twistedGroup_eq_commutator
    {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) :
    twistedGroup σ = ⁅twistFixed .D4 K σ, twistFixed .D4 K σ⁆ :=
  le_antisymm (twistedGroup_le_commutator σ (twistedGroup_isPerfect_of_card hq hK hσq))
    (commutator_twistFixed_le σ)

end Derived

end CFSG.LieType.Steinberg.TwistedD4
