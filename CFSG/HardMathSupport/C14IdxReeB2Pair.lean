module

public import CFSG.HardMathSupport.C14IdxReeA2Pair
public import CFSG.RankThree.PartOne.TCX.Ree.Closure
public import CFSG.Quasithin.Background.SmithB42F4Lang
public import CFSG.HardMathSupport.C14IdxRankOne

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.TCX.Ree CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction
  CFSG.LieType.SeitzGeneration.ExcHighThree

theorem reflectionWordProd_map_eq_of_mem_fun
    {τ : Tag}
    {θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} {O : Finset (Fin τ.rank → ℤ)}
    (hOθ : ∀ β ∈ O, θ β ∈ O)
    (hOinj : ∀ β ∈ O, ∀ γ ∈ O, θ β = θ γ → β = γ)
    (hOroot : ∀ β ∈ O, IsRoot τ β)
    (hOorth : ∀ β ∈ O, ∀ γ ∈ O, β ≠ γ → iform β γ = 0) :
    reflectionWordProd (O.toList.map θ) = reflectionWordProd O.toList := by
  classical
  have himage : O.image θ = O := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro γ hγ
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hγ
      exact hOθ β hβ
    · rw [Finset.card_image_of_injOn (fun x hx y hy h => hOinj x hx y hy h)]
  have hnd₁ : (O.toList.map θ).Nodup :=
    List.Nodup.map_on (fun x hx y hy h =>
      hOinj x (Finset.mem_toList.1 hx) y (Finset.mem_toList.1 hy) h) (Finset.nodup_toList O)
  have hnd₂ : O.toList.Nodup := Finset.nodup_toList O
  have hmem : ∀ x, x ∈ O.toList.map θ ↔ x ∈ O.toList := by
    intro x
    constructor
    · intro hx
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      exact Finset.mem_toList.2 (hOθ β (Finset.mem_toList.1 hβ))
    · intro hx
      have hxO : x ∈ O := Finset.mem_toList.1 hx
      have hx' : x ∈ O.image θ := by rw [himage]; exact hxO
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hx'
      exact List.mem_map.2 ⟨β, Finset.mem_toList.2 hβ, rfl⟩
  have hcomm : ∀ x ∈ O.toList.map θ, ∀ y ∈ O.toList.map θ, x ≠ y →
      Commute (rootReflection x) (rootReflection y) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
    have haO : a ∈ O := Finset.mem_toList.1 ha
    have hbO : b ∈ O := Finset.mem_toList.1 hb
    exact rootReflection_commute_of_iform_eq_zero
      (hOroot (θ a) (hOθ a haO)) (hOroot (θ b) (hOθ b hbO))
      (hOorth (θ a) (hOθ a haO) (θ b) (hOθ b hbO) (fun e => hxy (by rw [e])))
  exact list_prod_map_eq_of_mem_iff hnd₁ hnd₂ hmem rootReflection hcomm

theorem weylPerm_rootReflection
    {t : ReeTag}
    {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) :
    t.weylPerm (rootReflection β) = rootReflection (t.dualRoot β) := by
  obtain ⟨u, j, huj⟩ := isRoot_iff_exists_smul_single.1 hβ
  have hβdual : t.dualRoot β = t.weylPerm u • (Pi.single (t.perm j) 1) := by
    rw [← huj, ReeTag.dualRoot_smul u (isRoot_single t.tag j), ReeTag.dualRoot_single]
  rw [rootReflection_eq_conj huj, hβdual, rootReflection_eq_conj rfl]
  simp only [map_mul, map_inv, ReeTag.weylPerm_simple]

theorem weylPerm_reflectionWordProd
    {t : ReeTag}
    {l : List (Fin t.tag.rank → ℤ)} (hl : ∀ β ∈ l, IsRoot t.tag β) :
    t.weylPerm (reflectionWordProd l) =
      reflectionWordProd (l.map fun β => t.dualRoot β) := by
  induction l with
  | nil => rw [reflectionWordProd_nil, map_one, List.map_nil, reflectionWordProd_nil]
  | cons β l ih =>
    rw [reflectionWordProd_cons, map_mul, weylPerm_rootReflection (hl β List.mem_cons_self),
      ih (fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ)), List.map_cons, reflectionWordProd_cons]

theorem reeB2Pair_data
    {L : Type} [Field L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M} {a₀ : ℕ}
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a₀ F)
    {w : WeylGroup ReeTag.F4.tag}
    {α β : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : α ∈ simpleRoots (kernelRoots χ)) (hβ : β ∈ simpleRoots (kernelRoots χ))
    (hβeq : β = w • ReeTag.F4.dualRoot α) (hαeq : w • ReeTag.F4.dualRoot β = α)
    (hne : α ≠ β) (hnz : iform α β ≠ 0) :
    let γ : Fin ReeTag.F4.tag.rank → ℤ := rootReflection β • α
    let x : WeylGroup ReeTag.F4.tag := rootReflection α * rootReflection γ
    γ ∈ kernelRoots χ ∧ x ∈ unionWeylGroup χ Set.univ ∧ x * x = 1 ∧
      x • α = -α ∧ x • β = -β ∧
      x = (rootReflection α * rootReflection β) ^ 2 ∧
      canonicalRep (coxeterSystem ReeTag.F4.tag) L x ∈
        twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
  classical
  have hαroot : IsRoot ReeTag.F4.tag α := simpleRoots_isRoot hα
  have hβroot : IsRoot ReeTag.F4.tag β := simpleRoots_isRoot hβ
  have hαker : α ∈ kernelRoots χ := simpleRoots_subset hα
  have hβker : β ∈ kernelRoots χ := simpleRoots_subset hβ
  have hqmul : ReeTag.F4.quadForm β * ReeTag.F4.quadForm α = 8 := by
    have h := (ReeTag.rootDualityCheck_spec hαroot).2.2.2.2.1
    have hw : ReeTag.F4.quadForm β = ReeTag.F4.quadForm (ReeTag.F4.dualRoot α) := by
      rw [hβeq, quadForm_smul]
    rw [hw]
    simpa [ReeTag.prime] using h
  have hqα : iform α α = 2 ∨ iform α α = 4 :=
    iform_self_cases (τ := ReeTag.F4.tag) noG2_F4 hαroot
  have hqβ : iform β β = 2 ∨ iform β β = 4 :=
    iform_self_cases (τ := ReeTag.F4.tag) noG2_F4 hβroot
  have hqdiff : iform α α ≠ iform β β := by
    intro h
    rw [ReeTag.F4.quadForm_eq_iform, ReeTag.F4.quadForm_eq_iform] at hqmul
    rcases hqα with h1 | h1 <;> rcases hqβ with h2 | h2 <;>
      rw [h1, h2] at hqmul h <;> omega
  have hc : iform α β = -2 := by
    rcases f4_adj_value_kernelRoots hα hβ hne hnz with ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
    · exact absurd (by rw [h1, h2]) hqdiff
    · exact h3
  let k : ℤ := -corootPair β α
  let γ : Fin ReeTag.F4.tag.rank → ℤ := rootReflection β • α
  let x : WeylGroup ReeTag.F4.tag := rootReflection α * rootReflection γ
  have hk : k * iform β β = 4 := by
    have h := corootPair_mul hβroot α
    rw [iform_comm β α, hc] at h
    simp only [k]
    linarith
  have hγeq : γ = α + k • β := by
    change rootReflection β • α = α + k • β
    rw [rootReflection_smul hβroot]
    have : corootPair β α = -k := by simp [k]
    rw [this, neg_smul, sub_neg_eq_add]
  have hqαk : iform α α = 2 * k := by
    rw [ReeTag.F4.quadForm_eq_iform, ReeTag.F4.quadForm_eq_iform] at hqmul
    have hqβpos : iform β β ≠ 0 := (iform_self_pos_of_isRoot hβroot).ne'
    have h2k : (2 * k) * iform β β = 8 := by linarith [hk]
    exact mul_right_cancel₀ hqβpos (by linarith [hqmul, h2k])
  have hαγ0 : iform α γ = 0 := by
    rw [hγeq, iform_add_right, iform_smul_right, hc]
    linarith [hqαk]
  have hγroot : IsRoot ReeTag.F4.tag γ := IsRoot.smul hαroot (rootReflection β)
  have hcommαγ : Commute (rootReflection α) (rootReflection γ) :=
    rootReflection_commute_of_iform_eq_zero hαroot hγroot hαγ0
  have hx2 : x * x = 1 := by
    calc (rootReflection α * rootReflection γ) * (rootReflection α * rootReflection γ)
        = rootReflection α * (rootReflection γ * rootReflection α) * rootReflection γ := by
          group
      _ = rootReflection α * (rootReflection α * rootReflection γ) * rootReflection γ := by
          rw [hcommαγ.eq.symm]
      _ = (rootReflection α * rootReflection α) * (rootReflection γ * rootReflection γ) := by
          group
      _ = 1 := by rw [rootReflection_mul_self hαroot, rootReflection_mul_self hγroot, one_mul]
  have hxα : x • α = -α := by
    change (rootReflection α * rootReflection γ) • α = -α
    rw [mul_smul, rootReflection_smul_of_iform_eq_zero hγroot (by rwa [iform_comm]),
      rootReflection_smul_self hαroot]
  have hxβ : x • β = -β := by
    let j : ℤ := -corootPair α β
    have hj : j * iform α α = 4 := by
      have h := corootPair_mul hαroot β
      rw [hc] at h
      simp only [j]
      linarith
    have hcγβ : corootPair γ β = j := by
      have hif : iform γ β = 2 := by
        rw [hγeq, iform_add_left, iform_smul_left, hc]
        nlinarith [hk]
      have hqγ : iform γ γ = iform α α := by
        rw [hγeq, iform_add_left, iform_add_right, iform_add_right, iform_smul_left,
          iform_smul_right, hc]
        simp only [iform_smul_left, iform_smul_right, iform_comm β α, hc]
        rcases hqβ with hb | hb <;> rw [hb] at hk ⊢ <;> nlinarith [hk, hqαk]
      rw [corootPair, hqγ, hif]
      norm_num
      rw [← hj]
      exact Int.mul_ediv_cancel _ (iform_self_pos_of_isRoot hαroot).ne'
    have hjk : j * k = 2 := by
      rw [ReeTag.F4.quadForm_eq_iform, ReeTag.F4.quadForm_eq_iform] at hqmul
      nlinarith [hj, hk, hqmul]
    change (rootReflection α * rootReflection γ) • β = -β
    rw [mul_smul, rootReflection_smul hγroot, hcγβ]
    rw [smul_sub, smul_comm]
    rw [rootReflection_smul hαroot,
      rootReflection_smul_of_iform_eq_zero hαroot hαγ0,
      show corootPair α β = -j by simp [j]]
    have hγval : γ = α + k • β := hγeq
    rw [hγval]
    simp only [smul_add, smul_smul, neg_smul]
    rw [hjk]
    abel
  have hγker : γ ∈ kernelRoots χ := by
    have hαu : α ∈ unionSimpleRoots χ Set.univ := by
      rw [← mem_simpleRoots_unionRoots_iff, unionRoots_univ_eq_kernelRoots]; exact hα
    have hβu : β ∈ unionSimpleRoots χ Set.univ := by
      rw [← mem_simpleRoots_unionRoots_iff, unionRoots_univ_eq_kernelRoots]; exact hβ
    have h := rootReflection_smul_mem_unionRoots (J := Set.univ) hβu
      (by rw [unionRoots_univ_eq_kernelRoots]; exact hαker)
    simpa [γ, unionRoots_univ_eq_kernelRoots] using h
  have hx : x ∈ unionWeylGroup χ Set.univ := by
    have h := reflectionWordProd_mem_unionWeylGroup_of_mem (M := M) (χ := χ) (J := Set.univ)
      (l := [α, γ]) (by
      intro δ hδ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hδ
      rcases hδ with rfl | rfl
      · rw [unionRoots_univ_eq_kernelRoots]; exact hαker
      · rw [unionRoots_univ_eq_kernelRoots]; exact hγker)
    simpa [x, reflectionWordProd] using h
  have hγeqr : rootReflection γ = rootReflection β * rootReflection α * rootReflection β := by
    rw [show γ = rootReflection β • α from rfl,
      rootReflection_smul_root (rootReflection β) hαroot, rootReflection_inv hβroot]
  have hxsq : x = (rootReflection α * rootReflection β) ^ 2 := by
    rw [show x = rootReflection α * rootReflection γ from rfl, hγeqr, pow_two]; group
  have hxσ : canonicalRep (coxeterSystem ReeTag.F4.tag) L x ∈
      twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
    apply CFSG.Quasithin.B42F4.canonicalRep_mem_twistedFixed hF
    have hweyl : ReeTag.F4.weylPerm x =
        (rootReflection (ReeTag.F4.dualRoot α) *
          rootReflection (ReeTag.F4.dualRoot β)) ^ 2 := by
      rw [hxsq, map_pow, map_mul, weylPerm_rootReflection hαroot,
        weylPerm_rootReflection hβroot]
    rw [hweyl]
    have hprod : w * (rootReflection (ReeTag.F4.dualRoot α) *
          rootReflection (ReeTag.F4.dualRoot β)) * w⁻¹ =
        rootReflection β * rootReflection α := by
      calc w * (rootReflection (ReeTag.F4.dualRoot α) *
            rootReflection (ReeTag.F4.dualRoot β)) * w⁻¹
          = (w * rootReflection (ReeTag.F4.dualRoot α) * w⁻¹) *
              (w * rootReflection (ReeTag.F4.dualRoot β) * w⁻¹) := by group
        _ = rootReflection (w • ReeTag.F4.dualRoot α) *
              rootReflection (w • ReeTag.F4.dualRoot β) := by
            rw [← rootReflection_smul_root w (ReeTag.isRoot_dualRoot hαroot),
              ← rootReflection_smul_root w (ReeTag.isRoot_dualRoot hβroot)]
        _ = rootReflection β * rootReflection α := by rw [← hβeq, ← hαeq]
    have hconj : w * (rootReflection (ReeTag.F4.dualRoot α) *
          rootReflection (ReeTag.F4.dualRoot β)) ^ 2 * w⁻¹ =
        (rootReflection β * rootReflection α) ^ 2 := by
      calc w * (rootReflection (ReeTag.F4.dualRoot α) *
            rootReflection (ReeTag.F4.dualRoot β)) ^ 2 * w⁻¹
          = (w * (rootReflection (ReeTag.F4.dualRoot α) *
              rootReflection (ReeTag.F4.dualRoot β)) * w⁻¹) ^ 2 := by
            simp only [pow_two]; group
        _ = _ := by rw [hprod]
    rw [hconj]
    have hsq : (rootReflection β * rootReflection α) ^ 2 = x := by
      rw [show x = rootReflection α * rootReflection γ from rfl]
      calc (rootReflection β * rootReflection α) ^ 2
          = (rootReflection β * rootReflection α * rootReflection β) * rootReflection α := by
            rw [pow_two]; group
        _ = rootReflection γ * rootReflection α := by rw [hγeqr]
        _ = rootReflection α * rootReflection γ := hcommαγ.eq.symm
    exact hsq
  exact ⟨hγker, hx, hx2, hxα, hxβ, hxsq, hxσ⟩

end CFSG.HardMathSupport.C14Idx
