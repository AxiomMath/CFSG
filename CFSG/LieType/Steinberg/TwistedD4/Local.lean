module

public import CFSG.LieType.Steinberg.TwistedD4.Roots

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedD4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits

variable {K : Type} [Field K] (σ : K →+* K)

local notation "𝕏" => rootGroup (rootOperatorFamily d4) K

local notation "𝕩" => xPar (rootOperatorFamily d4)

theorem iSup_fibre
    {β : Fin (Tag.rank .G2) → ℤ} {α₀ : Fin d4.rank → ℤ} (hα₀ : IsRoot d4 α₀)
    (hp : proj α₀ = β) :
    (⨆ α ∈ {α : Fin d4.rank → ℤ | IsRoot d4 α},
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • β), 𝕏 α) =
      𝕏 α₀ ⊔ 𝕏 (rho α₀) ⊔ 𝕏 (rho (rho α₀)) := by
  refine le_antisymm (iSup₂_le fun α hα => iSup_le fun ⟨c, hc, hcα⟩ => ?_)
    (sup_le (sup_le ?_ ?_) ?_)
  · rw [← proj_apply, ← hp] at hcα
    have hc1 := eq_one_of_proj_eq_nsmul hα hα₀ hc hcα
    rw [hc1, one_smul] at hcα
    rcases (proj_eq_proj_iff hα₀ hα).1 hcα.symm with rfl | rfl | rfl
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  · exact le_iSup₂_of_le (f := fun α (_ : α ∈ {α : Fin d4.rank → ℤ | IsRoot d4 α}) =>
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • β), 𝕏 α) α₀ hα₀
      (le_iSup_of_le ⟨1, one_pos, by rw [one_smul, ← hp]; rfl⟩ le_rfl)
  · refine le_iSup₂_of_le (f := fun α (_ : α ∈ {α : Fin d4.rank → ℤ | IsRoot d4 α}) =>
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • β), 𝕏 α) (rho α₀) (isRoot_rho hα₀)
      (le_iSup_of_le ⟨1, one_pos, ?_⟩ le_rfl)
    rw [one_smul, ← hp, ← proj_apply, proj_rho]
  · refine le_iSup₂_of_le (f := fun α (_ : α ∈ {α : Fin d4.rank → ℤ | IsRoot d4 α}) =>
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • β), 𝕏 α) (rho (rho α₀))
      (isRoot_rho (isRoot_rho hα₀)) (le_iSup_of_le ⟨1, one_pos, ?_⟩ le_rfl)
    rw [one_smul, ← hp, ← proj_apply, proj_rho, proj_rho]

theorem mem_twistedRootSubgroupD4_iff
    {β : Fin (Tag.rank .G2) → ℤ} {α₀ : Fin d4.rank → ℤ}
    (hα₀ : IsRoot d4 α₀) (hp : proj α₀ = β) (g : adjointGroup d4 K) :
    g ∈ twistedRootSubgroupD4 σ β ↔
      g ∈ 𝕏 α₀ ⊔ 𝕏 (rho α₀) ⊔ 𝕏 (rho (rho α₀)) ∧ twistC .D4 K σ g = g := by
  rw [twistedRootSubgroupD4, twistedRootSubgroup, Subgroup.mem_inf, iSup_fibre hα₀ hp]
  rfl

theorem twistedRootSubgroupD4_le
    {β : Fin (Tag.rank .G2) → ℤ} {α₀ : Fin d4.rank → ℤ}
    (hα₀ : IsRoot d4 α₀) (hp : proj α₀ = β) :
    twistedRootSubgroupD4 σ β ≤ 𝕏 α₀ ⊔ 𝕏 (rho α₀) ⊔ 𝕏 (rho (rho α₀)) := fun g hg =>
  ((mem_twistedRootSubgroupD4_iff σ hα₀ hp g).1 hg).1

theorem mem_sup3_iff
    {a b e : Fin d4.rank → ℤ}
    (hab : ∀ c d : K, Commute (𝕩 a c) (𝕩 b d)) (hae : ∀ c d : K, Commute (𝕩 a c) (𝕩 e d))
    (hbe : ∀ c d : K, Commute (𝕩 b c) (𝕩 e d)) (ha : IsRoot d4 a) (hb : IsRoot d4 b)
    (he : IsRoot d4 e) {g : adjointGroup d4 K} :
    g ∈ 𝕏 a ⊔ 𝕏 b ⊔ 𝕏 e ↔ ∃ c d f, g = 𝕩 a c * 𝕩 b d * 𝕩 e f := by
  constructor
  · intro hg
    let S : Subgroup (adjointGroup d4 K) :=
      { carrier := {g | ∃ c d f, g = 𝕩 a c * 𝕩 b d * 𝕩 e f}
        mul_mem' := by
          rintro _ _ ⟨c, d, f, rfl⟩ ⟨c', d', f', rfl⟩
          refine ⟨c + c', d + d', f + f', ?_⟩
          rw [mul3_mul_mul3' (hab c' d).symm (hae c' f).symm (hbe d' f).symm, ← xPar_add,
            ← xPar_add, ← xPar_add]
        one_mem' := ⟨0, 0, 0, by rw [xPar_zero, xPar_zero, xPar_zero, mul_one, mul_one]⟩
        inv_mem' := by
          rintro _ ⟨c, d, f, rfl⟩
          refine ⟨-c, -d, -f, ?_⟩
          rw [mul_inv_rev, mul_inv_rev, xPar_neg, xPar_neg, xPar_neg, ← (hab (-c) (-d)).eq,
            ← mul_assoc, ← (hae (-c) (-f)).eq, mul_assoc, ← (hbe (-d) (-f)).eq, ← mul_assoc] }
    have hle : 𝕏 a ⊔ 𝕏 b ⊔ 𝕏 e ≤ S := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro y hy
        obtain ⟨c, rfl⟩ := (mem_rootGroup_iff ha y).1 hy
        exact ⟨c, 0, 0, by rw [xPar_zero, xPar_zero, mul_one, mul_one]⟩
      · intro y hy
        obtain ⟨d, rfl⟩ := (mem_rootGroup_iff hb y).1 hy
        exact ⟨0, d, 0, by rw [xPar_zero, xPar_zero, one_mul, mul_one]⟩
      · intro y hy
        obtain ⟨f, rfl⟩ := (mem_rootGroup_iff he y).1 hy
        exact ⟨0, 0, f, by rw [xPar_zero, xPar_zero, one_mul, one_mul]⟩
    exact hle hg
  · rintro ⟨c, d, f, rfl⟩
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left (xPar_mem ha c)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (xPar_mem hb d))))
      (Subgroup.mem_sup_right (xPar_mem he f))

theorem xPar_rho_mul_inj
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α)
    {c d f c' d' f' : K}
    (h : 𝕩 α c * 𝕩 (rho α) d * 𝕩 (rho (rho α)) f = 𝕩 α c' * 𝕩 (rho α) d' * 𝕩 (rho (rho α)) f') :
    c = c' ∧ d = d' ∧ f = f' := by
  classical
  have h1 := isRoot_rho hα
  have h2 := isRoot_rho h1
  have hne1 : rho (rho α) ≠ α := rho_rho_ne hne
  have hne2 : rho (rho α) ≠ rho α := rho_rho_ne_rho hne
  have hht1 : ht (rho α) = ht α := by rw [← ht_proj, proj_rho, ht_proj]
  have hht2 : ht (rho (rho α)) = ht α := by rw [← ht_proj, proj_rho, proj_rho, ht_proj]
  set φ : (Fin d4.rank → ℤ) →+ ℤ := if 0 < ht α then htHom else -htHom with hφ
  have hφv : ∀ v, φ v = (if 0 < ht α then 1 else -1) * ht v := fun v => by
    simp only [hφ]
    split_ifs <;> simp [htHom_apply]
  have hpos : 0 < φ α := by
    rw [hφv]
    have h0 : ht α ≠ 0 := hα.height_ne_zero
    split_ifs with h' <;> omega
  have hinj := prodInjective (F := rootOperatorFamily d4) (K := K) φ [α, rho α, rho (rho α)]
    (by simp [List.nodup_cons, Ne.symm hne, Ne.symm hne1, Ne.symm hne2])
    (by
      intro γ hγ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl | rfl
      · exact ⟨hα, hpos⟩
      · exact ⟨h1, by rw [hφv, hht1, ← hφv]; exact hpos⟩
      · exact ⟨h2, by rw [hφv, hht2, ← hφv]; exact hpos⟩)
    (by simp [hφv, hht1, hht2])
  let F₁ : (Fin d4.rank → ℤ) → adjointGroup d4 K := fun γ =>
    if γ = α then 𝕩 α c else if γ = rho α then 𝕩 (rho α) d else 𝕩 (rho (rho α)) f
  let F₂ : (Fin d4.rank → ℤ) → adjointGroup d4 K := fun γ =>
    if γ = α then 𝕩 α c' else if γ = rho α then 𝕩 (rho α) d' else 𝕩 (rho (rho α)) f'
  have hmem : ∀ (u v w : K), ∀ γ ∈ [α, rho α, rho (rho α)],
      (fun γ : Fin d4.rank → ℤ => if γ = α then 𝕩 α u else if γ = rho α then 𝕩 (rho α) v
        else 𝕩 (rho (rho α)) w) γ ∈ 𝕏 γ := by
    intro u v w γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl
    · simp only [ite_true]
      exact xPar_mem hα u
    · simp only [hne, ite_false, ite_true]
      exact xPar_mem h1 v
    · simp only [hne1, hne2, ite_false]
      exact xPar_mem h2 w
  have hprod : ([α, rho α, rho (rho α)].map F₁).prod = ([α, rho α, rho (rho α)].map F₂).prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, F₁, F₂, hne,
      hne1, hne2, ite_true, ite_false, ← mul_assoc]
    exact h
  have e1 := hinj F₁ F₂ (hmem c d f) (hmem c' d' f') hprod α (by simp)
  have e2 := hinj F₁ F₂ (hmem c d f) (hmem c' d' f') hprod (rho α) (by simp)
  have e3 := hinj F₁ F₂ (hmem c d f) (hmem c' d' f') hprod (rho (rho α)) (by simp)
  simp only [F₁, F₂, hne, hne1, hne2, ite_true, ite_false] at e1 e2 e3
  exact ⟨xPar_injective hα e1, xPar_injective h1 e2, xPar_injective h2 e3⟩

theorem mem_sup_rho_iff
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α)
    {g : adjointGroup d4 K} :
    g ∈ 𝕏 α ⊔ 𝕏 (rho α) ⊔ 𝕏 (rho (rho α)) ↔
      ∃ c d f, g = 𝕩 α c * 𝕩 (rho α) d * 𝕩 (rho (rho α)) f :=
  mem_sup3_iff (commute_xPar_rho hα hne) (commute_xPar_rho_rho hα hne)
    (commute_xPar_rho (isRoot_rho hα) (rho_rho_ne_rho hne)) hα (isRoot_rho hα)
    (isRoot_rho (isRoot_rho hα))

theorem commute_of_mem_sup_rho
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α)
    {g h : adjointGroup d4 K} (hg : g ∈ 𝕏 α ⊔ 𝕏 (rho α) ⊔ 𝕏 (rho (rho α)))
    (hh : h ∈ 𝕏 α ⊔ 𝕏 (rho α) ⊔ 𝕏 (rho (rho α))) : Commute g h := by
  have hself : ∀ (γ : Fin d4.rank → ℤ) (c d : K), Commute (𝕩 γ c) (𝕩 γ d) := fun γ c d => by
    change 𝕩 γ c * 𝕩 γ d = 𝕩 γ d * 𝕩 γ c
    rw [← xPar_add, ← xPar_add, add_comm]
  by_cases hfix : rho α = α
  · rw [hfix, hfix, sup_idem, sup_idem] at hg hh
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hα g).1 hg
    obtain ⟨d, rfl⟩ := (mem_rootGroup_iff hα h).1 hh
    exact hself α c d
  · obtain ⟨c, d, f, rfl⟩ := (mem_sup_rho_iff hα hfix).1 hg
    obtain ⟨c', d', f', rfl⟩ := (mem_sup_rho_iff hα hfix).1 hh
    have h1 := isRoot_rho hα
    have h01 := commute_xPar_rho (K := K) hα hfix
    have h02 := commute_xPar_rho_rho (K := K) hα hfix
    have h12 := commute_xPar_rho (K := K) h1 (rho_rho_ne_rho hfix)
    refine Commute.mul_left (Commute.mul_left ?_ ?_) ?_
    · exact ((hself α c c').mul_right (h01 c d')).mul_right (h02 c f')
    · exact (((h01 c' d).symm).mul_right (hself _ d d')).mul_right (h12 d f')
    · exact (((h02 c' f).symm).mul_right (h12 d' f).symm).mul_right (hself _ f f')

theorem commute_of_mem_twistedRootSubgroupD4
    {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β)
    {g h : adjointGroup d4 K} (hg : g ∈ twistedRootSubgroupD4 σ β)
    (hh : h ∈ twistedRootSubgroupD4 σ β) : Commute g h := by
  obtain ⟨α, hα, hp⟩ := exists_proj_eq hβ
  exact commute_of_mem_sup_rho hα (twistedRootSubgroupD4_le σ hα hp hg)
    (twistedRootSubgroupD4_le σ hα hp hh)

@[expose] def xOrbit
    (γ : Fin d4.rank → ℤ) (c : K) : adjointGroup d4 K :=
  𝕩 γ c * 𝕩 (rho γ) (twistSign σ γ * σ c) *
    𝕩 (rho (rho γ)) (twistSign σ γ * twistSign σ (rho γ) * σ (σ c))

theorem xOrbit_add
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (hne : rho γ ≠ γ) (c d : K) :
    xOrbit σ γ (c + d) = xOrbit σ γ c * xOrbit σ γ d := by
  rw [xOrbit, xOrbit, xOrbit, mul3_mul_mul3' (commute_xPar_rho hγ hne _ _).symm
    (commute_xPar_rho_rho hγ hne _ _).symm
    (commute_xPar_rho (isRoot_rho hγ) (rho_rho_ne_rho hne) _ _).symm, ← xPar_add, ← xPar_add,
    ← xPar_add]
  simp only [map_add, mul_add]

theorem xOrbit_zero
    (γ : Fin d4.rank → ℤ) : xOrbit σ γ 0 = 1 := by
  rw [xOrbit, map_zero, map_zero, mul_zero, mul_zero, xPar_zero, xPar_zero, xPar_zero, mul_one,
    mul_one]

theorem xOrbit_injective
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (hne : rho γ ≠ γ) :
    Function.Injective (xOrbit σ γ) := fun _ _ h => (xPar_rho_mul_inj hγ hne h).1

section Fixed

variable {σ} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem twistC_xOrbit
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (hne : rho γ ≠ γ) (c : K) :
    twistC .D4 K σ (xOrbit σ γ c) = xOrbit σ γ c := by
  have h1 := isRoot_rho hγ
  have h2 := isRoot_rho h1
  have hs := twistSign_mul_rho σ hσ hγ
  rw [xOrbit, map_mul, map_mul, twistC_xPar σ hγ, twistC_xPar σ h1, twistC_xPar σ h2,
    rho_rho_rho]
  simp only [map_mul, map_sign σ (twistSign_eq_one_or σ γ),
    map_sign σ (twistSign_eq_one_or σ (rho γ)), hσ]
  have e : twistSign σ (rho (rho γ)) * (twistSign σ γ * twistSign σ (rho γ) * c) = c := by
    linear_combination c * hs
  rw [e, mul_assoc, ← (commute_xPar_rho_rho hγ hne _ _).eq, ← mul_assoc,
    ← (commute_xPar_rho hγ hne _ _).eq]
  congr 2
  ring

theorem xOrbit_mem
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (hne : rho γ ≠ γ) (c : K) :
    xOrbit σ γ c ∈ twistedRootSubgroupD4 σ (proj γ) := by
  refine (mem_twistedRootSubgroupD4_iff σ hγ rfl _).2 ⟨?_, twistC_xOrbit hσ hγ hne c⟩
  exact (mem_sup_rho_iff hγ hne).2 ⟨_, _, _, rfl⟩

theorem mem_twistedRootSubgroupD4_iff_of_fixed
    {β : Fin (Tag.rank .G2) → ℤ}
    {α₀ : Fin d4.rank → ℤ} (hα₀ : IsRoot d4 α₀) (hp : proj α₀ = β) (hfix : rho α₀ = α₀)
    (g : adjointGroup d4 K) :
    g ∈ twistedRootSubgroupD4 σ β ↔ ∃ c, σ c = c ∧ g = 𝕩 α₀ c := by
  rw [mem_twistedRootSubgroupD4_iff σ hα₀ hp]
  simp only [hfix, sup_idem]
  constructor
  · rintro ⟨hg, hF⟩
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hα₀ g).1 hg
    refine ⟨c, ?_, rfl⟩
    rw [twistC_xPar σ hα₀, hfix, twistSign_of_rho_eq σ hσ hα₀ hfix, one_mul] at hF
    exact xPar_injective hα₀ hF
  · rintro ⟨c, hc, rfl⟩
    refine ⟨xPar_mem hα₀ c, ?_⟩
    rw [twistC_xPar σ hα₀, hfix, twistSign_of_rho_eq σ hσ hα₀ hfix, one_mul, hc]

theorem mem_twistedRootSubgroupD4_iff_of_orbit
    {β : Fin (Tag.rank .G2) → ℤ}
    {α₀ : Fin d4.rank → ℤ} (hα₀ : IsRoot d4 α₀) (hp : proj α₀ = β) (hne : rho α₀ ≠ α₀)
    (g : adjointGroup d4 K) :
    g ∈ twistedRootSubgroupD4 σ β ↔ ∃ c, g = xOrbit σ α₀ c := by
  constructor
  · intro hg
    obtain ⟨hg', hF⟩ := (mem_twistedRootSubgroupD4_iff σ hα₀ hp g).1 hg
    obtain ⟨c, d, f, rfl⟩ := (mem_sup_rho_iff hα₀ hne).1 hg'
    refine ⟨c, ?_⟩
    have h1 := isRoot_rho hα₀
    have h2 := isRoot_rho h1
    rw [map_mul, map_mul, twistC_xPar σ hα₀, twistC_xPar σ h1, twistC_xPar σ h2, rho_rho_rho,
      mul_assoc, ← (commute_xPar_rho_rho hα₀ hne _ _).eq, ← mul_assoc,
      ← (commute_xPar_rho hα₀ hne _ _).eq] at hF
    obtain ⟨-, hd, hf⟩ := xPar_rho_mul_inj hα₀ hne hF
    rw [xOrbit, ← hd, ← hf, ← hd, map_mul, map_sign σ (twistSign_eq_one_or σ α₀)]
    ring_nf
  · rintro ⟨c, rfl⟩
    rw [← hp]
    exact xOrbit_mem hσ hα₀ hne c

theorem xPar_mem_of_fixed
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (hfix : rho γ = γ) {c : K}
    (hc : σ c = c) : 𝕩 γ c ∈ twistedRootSubgroupD4 σ (proj γ) :=
  (mem_twistedRootSubgroupD4_iff_of_fixed hσ hγ rfl hfix _).2 ⟨c, hc, rfl⟩

end Fixed

theorem twistSign_single
    (i : Fin d4.rank) : twistSign σ (Pi.single i 1) = 1 := by
  have h1 := twistC_xPar σ (isRoot_single d4 i) (1 : K)
  rw [twistC_xPar_single, rho_single, map_one, mul_one] at h1
  exact (xPar_injective (isRoot_single d4 (rhoPerm i)) h1).symm

theorem twistSign_neg_single
    (i : Fin d4.rank) : twistSign σ (-Pi.single i 1) = 1 := by
  have h1 := twistC_xPar σ (isRoot_neg_single d4 i) (1 : K)
  rw [twistC_xPar_neg_single, rho_neg_single, map_one, mul_one] at h1
  exact (xPar_injective (isRoot_neg_single d4 (rhoPerm i)) h1).symm

theorem twistSign_smul_single
    {s : ℤ} (hs : s = 1 ∨ s = -1) (i : Fin d4.rank) :
    twistSign σ (s • Pi.single i 1) = 1 := by
  rcases hs with rfl | rfl
  · rw [one_smul, twistSign_single]
  · rw [neg_one_smul, twistSign_neg_single]

theorem rho_smul_single (s : ℤ) (i : Fin d4.rank) :
    rho (s • Pi.single i 1) = s • Pi.single (rhoPerm i) 1 := by
  rw [← rho_single]
  rfl

theorem rho_smul_single_ne {s : ℤ} (hs : s = 1 ∨ s = -1) {i : Fin d4.rank} (hi : rhoPerm i ≠ i) :
    rho (s • Pi.single i 1) ≠ s • Pi.single i 1 := by
  rw [rho_smul_single]
  intro h
  have := congrFun h (rhoPerm i)
  rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hi, smul_eq_mul,
    smul_eq_mul, mul_one, mul_zero] at this
  rcases hs with rfl | rfl <;> omega

theorem xOrbit_smul_single
    {s : ℤ} (hs : s = 1 ∨ s = -1) (c : K) :
    xOrbit σ (s • Pi.single (nd 0) 1) c = xOuter s c (σ c) (σ (σ c)) := by
  rw [xOrbit, rho_smul_single, rho_smul_single, rhoPerm_zero, rhoPerm_one,
    twistSign_smul_single σ hs, twistSign_smul_single σ hs, one_mul, one_mul, one_mul]
  rfl

theorem proj_smul_single {s : ℤ} (hs : s = 1 ∨ s = -1) (a : Fin d4.rank) :
    proj (s • Pi.single a 1) = s • Pi.single (orbitMap a) 1 := by
  rcases hs with rfl | rfl
  · rw [one_smul, one_smul, proj_apply, orbitSum_single]
  · rw [neg_one_smul, neg_one_smul, proj_apply, orbitSum_neg_single]

local notation "𝕃" => CurtisTits.rankOne (rootGroup (rootOperatorFamily d4) K)

theorem commute_xPar_rankOne_outer
    {a b : Fin d4.rank} (ha : a ≠ nd 2) (hb : b ≠ nd 2)
    (hab : a ≠ b) {s : ℤ} (hs : s = 1 ∨ s = -1) (c : K) {y : adjointGroup d4 K}
    (hy : y ∈ 𝕃 b) : Commute (𝕩 (s • Pi.single a 1) c) y := by
  have hle : 𝕃 b ≤ Subgroup.centralizer {𝕩 (s • Pi.single a 1) c} := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨d, rfl⟩ := (mem_rootGroup_iff (isRoot_single d4 b) z).1 hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := commute_xPar_outer ha hb hab hs (Or.inl rfl) c d
      rw [one_smul] at this
      exact this.eq.symm
    · obtain ⟨d, rfl⟩ := (mem_rootGroup_iff (isRoot_neg_single d4 b) z).1 hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := commute_xPar_outer ha hb hab hs (Or.inr rfl) c d
      rw [neg_one_smul] at this
      exact this.eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem commute_rankOne_outer
    {a b : Fin d4.rank} (ha : a ≠ nd 2) (hb : b ≠ nd 2) (hab : a ≠ b)
    {x y : adjointGroup d4 K} (hx : x ∈ 𝕃 a) (hy : y ∈ 𝕃 b) : Commute x y := by
  have hle : 𝕃 a ≤ Subgroup.centralizer {y} := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_single d4 a) z).1 hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := commute_xPar_rankOne_outer ha hb hab (Or.inl rfl) c hy
      rw [one_smul] at this
      exact this.eq
    · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_neg_single d4 a) z).1 hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := commute_xPar_rankOne_outer ha hb hab (Or.inr rfl) c hy
      rw [neg_one_smul] at this
      exact this.eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

theorem steinbergWeyl_mem_rankOne
    (a : Fin d4.rank) (t : Kˣ) :
    CFSG.LieType.Steinberg.weylElement (𝕩) a t ∈ 𝕃 a :=
  mul_mem (mul_mem (Subgroup.mem_sup_left (xPar_mem (isRoot_single d4 a) _))
    (Subgroup.mem_sup_right (xPar_mem (isRoot_neg_single d4 a) _)))
    (Subgroup.mem_sup_left (xPar_mem (isRoot_single d4 a) _))

theorem torusElement_eq
    (a : Fin d4.rank) (t : Kˣ) :
    torusElement d4 K a t = CFSG.LieType.Steinberg.weylElement (𝕩) a t *
      (CFSG.LieType.Steinberg.weylElement (𝕩) a 1)⁻¹ := by
  rw [weylElement_xPar, weylElement_xPar, torusElement_one_eq, one_mul, mul_inv_cancel_right]

theorem torusElement_mem_rankOne
    (a : Fin d4.rank) (t : Kˣ) : torusElement d4 K a t ∈ 𝕃 a := by
  rw [torusElement_eq]
  exact mul_mem (steinbergWeyl_mem_rankOne a t) (inv_mem (steinbergWeyl_mem_rankOne a 1))

theorem weylElement_mem_rankOne'
    (a : Fin d4.rank) : Chevalley.weylElement d4 K a ∈ 𝕃 a :=
  weylElement_mem_rankOne a

theorem mem_twistedRootGroup_of_mem
    {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β)
    {g : adjointGroup d4 K} (hg : g ∈ twistedRootSubgroupD4 σ β) :
    (⟨g, twistedRootSubgroupD4_le_twistedGroup σ hβ hg⟩ : twistedGroup σ) ∈
      twistedRootGroup σ β :=
  hg

theorem isRoot_smul_single_G2 {s : ℤ} (hs : s = 1 ∨ s = -1) (i : Fin (Tag.rank .G2)) :
    IsRoot .G2 (s • Pi.single i 1) := by
  rcases hs with rfl | rfl
  · rw [one_smul]; exact .basis i
  · rw [neg_one_smul]; exact isRoot_neg_single _ i

theorem mem_rankOne_of_mem
    {i : Fin (Tag.rank .G2)} {s : ℤ} (hs : s = 1 ∨ s = -1)
    {g : twistedGroup σ}
    (hg : (g : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (s • Pi.single i 1)) :
    g ∈ rankOne (twistedRootGroup σ) i := by
  rcases hs with rfl | rfl
  · rw [one_smul] at hg
    exact Subgroup.mem_sup_left hg
  · rw [neg_one_smul] at hg
    exact Subgroup.mem_sup_right hg

theorem nHat_mem_rankOne
    (i : Fin (Tag.rank .G2)) : nHat σ i ∈ rankOne (twistedRootGroup σ) i := by
  have hp : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hn : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have h1 : σ (1 : K) = 1 := map_one σ
  have h2 : σ (-1 : K) = -1 := by rw [map_neg, map_one]
  match i with
  | ⟨0, _⟩ =>
    have hx := xPar_two_mem σ hp h1
    have hy := xPar_two_mem σ hn h2
    have hr0 := isRoot_smul_single_G2 hp (ng 0)
    have hr0' := isRoot_smul_single_G2 hn (ng 0)
    have e : nHat σ (ng 0) = ⟨_, twistedRootSubgroupD4_le_twistedGroup σ hr0 hx⟩ *
        ⟨_, twistedRootSubgroupD4_le_twistedGroup σ hr0' hy⟩ *
        ⟨_, twistedRootSubgroupD4_le_twistedGroup σ hr0 hx⟩ :=
      Subtype.ext (nHatE_zero_eq (K := K))
    rw [e]
    exact mul_mem (mul_mem (mem_rankOne_of_mem σ hp hx) (mem_rankOne_of_mem σ hn hy))
      (mem_rankOne_of_mem σ hp hx)
  | ⟨1, _⟩ =>
    have hx := xOuter_mem σ hp (c := 1) (by rw [h1, h1, h1])
    have hy := xOuter_mem σ hn (c := -1) (by rw [h2, h2, h2])
    rw [h1, h1] at hx
    rw [h2, h2] at hy
    have hr1 := isRoot_smul_single_G2 hp (ng 1)
    have hr1' := isRoot_smul_single_G2 hn (ng 1)
    have e : nHat σ (ng 1) = ⟨_, twistedRootSubgroupD4_le_twistedGroup σ hr1 hx⟩ *
        ⟨_, twistedRootSubgroupD4_le_twistedGroup σ hr1' hy⟩ *
        ⟨_, twistedRootSubgroupD4_le_twistedGroup σ hr1 hx⟩ :=
      Subtype.ext (nHatE_one_eq (K := K))
    rw [e]
    exact mul_mem (mul_mem (mem_rankOne_of_mem σ hp hx) (mem_rankOne_of_mem σ hn hy))
      (mem_rankOne_of_mem σ hp hx)

theorem twistC_mem_rankOne
    {a : Fin d4.rank} {y : adjointGroup d4 K} (hy : y ∈ 𝕃 a) :
    twistC .D4 K σ y ∈ 𝕃 (rhoPerm a) := by
  have hle : 𝕃 a ≤ (𝕃 (rhoPerm a)).comap (twistC .D4 K σ) := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_single d4 a) z).1 hz
      rw [Subgroup.mem_comap, twistC_xPar_single]
      exact Subgroup.mem_sup_left (xPar_mem (isRoot_single d4 _) _)
    · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_neg_single d4 a) z).1 hz
      rw [Subgroup.mem_comap, twistC_xPar_neg_single]
      exact Subgroup.mem_sup_right (xPar_mem (isRoot_neg_single d4 _) _)
  exact hle hy

theorem twistC_mem_rankOne_zero
    {y : adjointGroup d4 K} (hy : y ∈ 𝕃 (nd 0)) :
    twistC .D4 K σ y ∈ 𝕃 (nd 1) := by
  have h := twistC_mem_rankOne σ hy
  rwa [rhoPerm_zero] at h

theorem twistC_twistC_mem_rankOne_zero
    {y : adjointGroup d4 K} (hy : y ∈ 𝕃 (nd 0)) :
    twistC .D4 K σ (twistC .D4 K σ y) ∈ 𝕃 (nd 3) := by
  have h := twistC_mem_rankOne σ (twistC_mem_rankOne_zero σ hy)
  rwa [rhoPerm_one] at h

@[expose] def phiShort
    : 𝕃 (nd 0) →* adjointGroup d4 K where
  toFun y := y * twistC .D4 K σ y * twistC .D4 K σ (twistC .D4 K σ y)
  map_one' := by simp
  map_mul' y y' := by
    have h1 : Commute (twistC .D4 K σ y) (y' : adjointGroup d4 K) :=
      (commute_rankOne_outer (a := nd 0) (b := nd 1) (by decide) (by decide) (by decide) y'.2
        (twistC_mem_rankOne_zero σ y.2)).symm
    have h2 : Commute (twistC .D4 K σ (twistC .D4 K σ y)) (y' : adjointGroup d4 K) :=
      (commute_rankOne_outer (a := nd 0) (b := nd 3) (by decide) (by decide) (by decide) y'.2
        (twistC_twistC_mem_rankOne_zero σ y.2)).symm
    have h3 : Commute (twistC .D4 K σ (twistC .D4 K σ y)) (twistC .D4 K σ y') :=
      (commute_rankOne_outer (a := nd 1) (b := nd 3) (by decide) (by decide) (by decide)
        (twistC_mem_rankOne_zero σ y'.2) (twistC_twistC_mem_rankOne_zero σ y.2)).symm
    simp only [Subgroup.coe_mul, map_mul]
    exact (mul3_mul_mul3' h1 h2 h3).symm

theorem phiShort_apply
    (y : 𝕃 (nd 0)) :
    phiShort σ y = y * twistC .D4 K σ y * twistC .D4 K σ (twistC .D4 K σ y) := rfl

theorem phiShort_xPar
    {s : ℤ} (hs : s = 1 ∨ s = -1) (c : K) (h : 𝕩 (s • Pi.single (nd 0) 1) c ∈
    𝕃 (nd 0)) : phiShort σ ⟨_, h⟩ = xOuter s c (σ c) (σ (σ c)) := by
  rw [phiShort_apply, twistC_xPar_smul_single σ hs, twistC_xPar_smul_single σ hs, rhoPerm_zero,
    rhoPerm_one]
  rfl

theorem xPar_single_mem_rankOne'
    (a : Fin d4.rank) {s : ℤ} (hs : s = 1 ∨ s = -1) (c : K) :
    𝕩 (s • Pi.single a 1) c ∈ 𝕃 a := by
  rcases hs with rfl | rfl
  · rw [one_smul]
    exact Subgroup.mem_sup_left (xPar_mem (isRoot_single d4 a) c)
  · rw [neg_one_smul]
    exact Subgroup.mem_sup_right (xPar_mem (isRoot_neg_single d4 a) c)

theorem phiShort_torusElement
    (t : Kˣ) :
    phiShort σ ⟨_, torusElement_mem_rankOne (nd 0) t⟩ = hShortHom σ t := by
  rw [phiShort_apply, hShortHom_apply]
  simp only [twistC_torusElement, rhoPerm_zero, rhoPerm_one]

theorem phiShort_weylElement :
    phiShort σ ⟨_, weylElement_mem_rankOne' (nd 0)⟩ = nHatE K (ng 1) := by
  rw [phiShort_apply, nHatE_one]
  simp only [twistC_weylElement, rhoPerm_zero, rhoPerm_one]

theorem forall_mem_of_rankOne
    {G : Type*} [Group G] (a : Fin d4.rank) (f : 𝕃 a →* G)
    (S : Subgroup G)
    (h : ∀ (s : ℤ) (hs : s = 1 ∨ s = -1) (c : K), f ⟨_, xPar_single_mem_rankOne' a hs c⟩ ∈ S)
    (y : 𝕃 a) : f y ∈ S := by
  have hX : 𝕏 (Pi.single a 1) ≤ 𝕃 a := le_sup_left
  have hY : 𝕏 (-Pi.single a 1) ≤ 𝕃 a := le_sup_right
  have htop : (⊤ : Subgroup (𝕃 a)) =
      (𝕏 (Pi.single a 1)).subgroupOf (𝕃 a) ⊔ (𝕏 (-Pi.single a 1)).subgroupOf (𝕃 a) := by
    rw [← Subgroup.subgroupOf_sup hX hY]
    exact (Subgroup.subgroupOf_self _).symm
  have hle : (⊤ : Subgroup (𝕃 a)) ≤ S.comap f := by
    rw [htop]
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_subgroupOf] at hz
      obtain ⟨c, hc⟩ := (mem_rootGroup_iff (isRoot_single d4 a) _).1 hz
      have e : z = ⟨_, xPar_single_mem_rankOne' a (Or.inl rfl) c⟩ := Subtype.ext (by
        change (z : adjointGroup d4 K) = 𝕩 ((1 : ℤ) • Pi.single a 1) c
        rw [one_smul]
        exact hc.symm)
      rw [Subgroup.mem_comap, e]
      exact h 1 (Or.inl rfl) c
    · rw [Subgroup.mem_subgroupOf] at hz
      obtain ⟨c, hc⟩ := (mem_rootGroup_iff (isRoot_neg_single d4 a) _).1 hz
      have e : z = ⟨_, xPar_single_mem_rankOne' a (Or.inr rfl) c⟩ := Subtype.ext (by
        change (z : adjointGroup d4 K) = 𝕩 ((-1 : ℤ) • Pi.single a 1) c
        rw [neg_one_smul]
        exact hc.symm)
      rw [Subgroup.mem_comap, e]
      exact h (-1) (Or.inr rfl) c
  exact hle (Subgroup.mem_top y)

section Short

variable {σ} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem phiShort_mem_twistedGroup
    (y : 𝕃 (nd 0)) : phiShort σ y ∈ twistedGroup σ :=
  forall_mem_of_rankOne (nd 0) (phiShort σ) (twistedGroup σ) (fun s hs c => by
    rw [phiShort_xPar σ hs]
    exact twistedRootSubgroupD4_le_twistedGroup σ (isRoot_smul_single_G2 hs (ng 1))
      (xOuter_mem σ hs (hσ c))) y

variable (σ) in
@[expose] def phiShortTw :
    𝕃 (nd 0) →* twistedGroup σ :=
  (phiShort σ).codRestrict _ (phiShort_mem_twistedGroup hσ)

theorem phiShortTw_val
    (y : 𝕃 (nd 0)) :
    (phiShortTw σ hσ y : adjointGroup d4 K) = phiShort σ y := rfl

theorem phiShortTw_mem_rankOne
    (y : 𝕃 (nd 0)) :
    phiShortTw σ hσ y ∈ rankOne (twistedRootGroup σ) (ng 1) :=
  forall_mem_of_rankOne (nd 0) (phiShortTw σ hσ) _ (fun s hs c => by
    refine mem_rankOne_of_mem σ hs ?_
    rw [phiShortTw_val, phiShort_xPar σ hs]
    exact xOuter_mem σ hs (hσ c)) y

omit hσ in
@[expose] def xLong
    {s : ℤ} (hs : s = 1 ∨ s = -1) {c : K} (hc : σ c = c) : twistedGroup σ :=
  ⟨_, twistedRootSubgroupD4_le_twistedGroup σ (isRoot_smul_single_G2 hs (ng 0))
    (xPar_two_mem σ hs hc)⟩

omit hσ in
theorem xLong_val
    {s : ℤ} (hs : s = 1 ∨ s = -1) {c : K} (hc : σ c = c) :
    (xLong hs hc : adjointGroup d4 K) = 𝕩 (s • Pi.single (nd 2) 1) c := rfl

omit hσ in
theorem xLong_mem_rankOne
    {s : ℤ} (hs : s = 1 ∨ s = -1) {c : K} (hc : σ c = c) :
    xLong hs hc ∈ rankOne (twistedRootGroup σ) (ng 0) :=
  mem_rankOne_of_mem σ hs (xPar_two_mem σ hs hc)

omit hσ in
theorem exists_hLong
    (t : fixedUnits σ) :
    ∃ g ∈ rankOne (twistedRootGroup σ) (ng 0), (g : adjointGroup d4 K) = hLongHom σ t := by
  have hp : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hn : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have ht : σ ((t : Kˣ) : K) = (t : Kˣ) := (mem_fixedUnits σ).1 t.2
  have ht' : σ (-(((t : Kˣ)⁻¹ : Kˣ) : K)) = -(((t : Kˣ)⁻¹ : Kˣ) : K) := by
    rw [map_neg, Units.val_inv_eq_inv_val, map_inv₀, ht]
  have h1 : σ ((1 : Kˣ) : K) = (1 : Kˣ) := by simp
  have h1' : σ (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) = -(((1 : Kˣ)⁻¹ : Kˣ) : K) := by simp
  refine ⟨xLong hp ht * xLong hn ht' * xLong hp ht *
    (xLong hp h1 * xLong hn h1' * xLong hp h1)⁻¹, ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem (xLong_mem_rankOne hp ht) (xLong_mem_rankOne hn ht'))
      (xLong_mem_rankOne hp ht)) (inv_mem (mul_mem (mul_mem (xLong_mem_rankOne hp h1)
        (xLong_mem_rankOne hn h1')) (xLong_mem_rankOne hp h1)))
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, xLong_val, one_smul, neg_one_smul]
    change _ = torusElement d4 K (nd 2) (t : Kˣ)
    rw [torusElement_eq]
    rfl

theorem hHatE_le_twistedGroup
    (i : Fin (Tag.rank .G2)) : hHatE σ i ≤ twistedGroup σ := by
  match i with
  | ⟨0, _⟩ =>
    rintro _ ⟨t, rfl⟩
    obtain ⟨g, -, hg⟩ := exists_hLong t
    rw [← hg]
    exact g.2
  | ⟨1, _⟩ =>
    rintro _ ⟨t, rfl⟩
    rw [← phiShort_torusElement σ t]
    exact phiShort_mem_twistedGroup hσ _

theorem hHat_le_rankOne
    (i : Fin (Tag.rank .G2)) :
    hHat σ i ≤ rankOne (twistedRootGroup σ) i := by
  intro g hg
  rw [hHat, Subgroup.mem_subgroupOf] at hg
  match i with
  | ⟨0, _⟩ =>
    obtain ⟨t, ht⟩ := hg
    obtain ⟨g', hg', e⟩ := exists_hLong t
    rwa [show g' = g from Subtype.ext (e.trans ht)] at hg'
  | ⟨1, _⟩ =>
    obtain ⟨t, ht⟩ := hg
    have e : phiShortTw σ hσ ⟨_, torusElement_mem_rankOne (nd 0) t⟩ = g :=
      Subtype.ext ((phiShort_torusElement σ t).trans ht)
    rw [← e]
    exact phiShortTw_mem_rankOne hσ _

end Short

end CFSG.LieType.Steinberg.TwistedD4
