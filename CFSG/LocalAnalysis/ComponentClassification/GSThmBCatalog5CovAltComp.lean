module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocal
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup Equiv Equiv.Perm

theorem exists_dt_mem_of_component {n : ℕ} (hn : 7 ≤ n)
    {σ : MulAut (alternatingGroup (Fin n))} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1)
    {P : Subgroup (alternatingGroup (Fin n))}
    (hP : CFSG.Assembly.IsComponentOf P (Sporadic.Schreier.fixSub σ)) :
    ∃ a b c d : Fin n, [a, b, c, d].Nodup ∧
      ∃ hmem : swap a b * swap c d ∈ alternatingGroup (Fin n),
        (⟨swap a b * swap c d, hmem⟩ : alternatingGroup (Fin n)) ∈ P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    (by omega) (by omega)
  obtain ⟨τ, rfl⟩ := hbij.2 σ
  set c := (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
    Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) with hcdef
  have hcapp : ∀ x : alternatingGroup (Fin n), ((c τ x : alternatingGroup (Fin n)) : Perm (Fin n))
      = τ * x * τ⁻¹ := fun x => rfl
  have hττ : τ * τ = 1 := by
    apply hbij.1
    rw [map_mul, map_one]
    exact hσ2
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    exact hσ1 (map_one c)
  have hτ2 : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hττ) hτ1
  set Q : Subgroup (Perm (Fin n)) := zpowers τ with hQdef
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ2, pow_one])
  set N := normalizer (Q : Set (Perm (Fin n))) with hNdef
  set F := Sporadic.Schreier.fixSub (c τ) with hFdef
  have hmemF : ∀ x : alternatingGroup (Fin n), x ∈ F ↔ τ * (x : Perm (Fin n)) = x * τ := by
    intro x
    rw [Sporadic.Schreier.mem_fixSub]
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      calc τ * (x : Perm (Fin n)) = τ * x * τ⁻¹ * τ := by group
        _ = x * τ := by rw [h1]
    · intro hx
      apply Subtype.ext
      rw [hcapp, hx]
      group
  have hcN : ∀ g : Perm (Fin n), τ * g = g * τ → g ∈ N := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [hQdef, ← Subgroup.zpowers_le, Subgroup.zpowers_le, mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute τ g from hg) k).eq
  let ι : F →* N := ((alternatingGroup (Fin n)).subtype.comp F.subtype).codRestrict N
    fun x => hcN _ ((hmemF x.1).mp x.2)
  have hι : Function.Injective ι := by
    intro x y hxy
    have h1 : ((x : alternatingGroup (Fin n)) : Perm (Fin n)) = ((y : alternatingGroup (Fin n)) :
        Perm (Fin n)) := congrArg (fun z : N => (z : Perm (Fin n))) hxy
    exact Subtype.ext (Subtype.ext h1)
  set R : Subgroup N := (alternatingGroup (Fin n)).subgroupOf N with hRdef
  have hR : R.Normal := inferInstance
  have hrange : ι.range = R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (x : alternatingGroup (Fin n)).2
    · intro y hy
      have hyA : (y : Perm (Fin n)) ∈ alternatingGroup (Fin n) := hy
      have hyτ : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp y.2 τ).mp (mem_zpowers τ)
      have hyτ' : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ = τ := by
        have hord : orderOf ((y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹) = 2 := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hτ2]
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyτ
        rw [← hk] at hord ⊢
        rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_zero,
            orderOf_one] at hord
          omega
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_one]
      have hcomm : τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ := by
        calc τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ * y := by
              rw [hyτ']
          _ = (y : Perm (Fin n)) * τ := by group
      exact ⟨⟨⟨y, hyA⟩, (hmemF ⟨y, hyA⟩).mpr hcomm⟩, Subtype.ext rfl⟩
  let e₁ : F ≃* R := (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hrange)
  set L₀ := P.subgroupOf F with hL₀def
  have hP' : IsPComponent 2 L₀ := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent
    ((LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hP.1).1 hP)
  have hL₁ : IsPComponent 2 (L₀.map e₁.toMonoidHom) :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e₁ hP'
  have hL := CatalogueBAlternating.pComponent_of_normal_subgroup 2 R (L₀.map e₁.toMonoidHom) hL₁
  set L := (L₀.map e₁.toMonoidHom).map R.subtype with hLdef
  obtain ⟨hdeg, hLeq, -⟩ := CatalogueBAlternating.symmetric_normalizer_pComponent 2 Q hQ L hL
  obtain ⟨emb⟩ : Nonempty (Fin 4 ↪ MulAction.fixedPoints Q (Fin n)) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    omega
  have hnd' : [emb 0, emb 1, emb 2, emb 3].Nodup := by
    simp [List.nodup_cons, emb.injective.eq_iff]
  have hab : emb 0 ≠ emb 1 := fun h => by simp [emb.injective.eq_iff] at h
  have hcd : emb 2 ≠ emb 3 := fun h => by simp [emb.injective.eq_iff] at h
  have hf : swap (emb 0) (emb 1) * swap (emb 2) (emb 3) ∈
      alternatingGroup (MulAction.fixedPoints Q (Fin n)) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hab, sign_swap hcd]
    rfl
  have hfL : CatalogueBAlternating.fixedPointsNormalizerHom Q
      (swap (emb 0) (emb 1) * swap (emb 2) (emb 3)) ∈ L := by
    rw [hLeq]
    exact ⟨_, hf, rfl⟩
  obtain ⟨r, hr, hrv⟩ := hfL
  obtain ⟨l, hl, rfl⟩ := hr
  have hval : (((l : F) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      swap ((emb 0 : MulAction.fixedPoints Q (Fin n)) : Fin n) (emb 1) *
        swap ((emb 2 : MulAction.fixedPoints Q (Fin n)) : Fin n) (emb 3) := by
    have h1 : (((l : F) : alternatingGroup (Fin n)) : Perm (Fin n)) =
        ((CatalogueBAlternating.fixedPointsNormalizerHom Q
          (swap (emb 0) (emb 1) * swap (emb 2) (emb 3)) : N) : Perm (Fin n)) :=
      congrArg (fun z : N => (z : Perm (Fin n))) hrv
    rw [h1, CatalogueBAlternating.fixedPointsNormalizerHom_coe, map_mul, ofSubtype_swap_eq,
      ofSubtype_swap_eq]
  refine ⟨emb 0, emb 1, emb 2, emb 3, hnd'.map Subtype.val_injective, ?_, ?_⟩
  · rw [← hval]
    exact ((l : F) : alternatingGroup (Fin n)).2
  · have hlP : ((l : F) : alternatingGroup (Fin n)) ∈ P := mem_subgroupOf.mp hl
    convert hlP using 1
    exact Subtype.ext hval.symm

end CFSG.ComponentClassification.GSThmB.Cov
