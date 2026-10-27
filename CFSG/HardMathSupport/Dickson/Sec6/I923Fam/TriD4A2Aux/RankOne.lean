module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.Residual
public import Mathlib.GroupTheory.IsPerfect

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

theorem le_of_normal_of_centralizer_trivial {G : Type*} [Group G] {U S : Subgroup G} [S.Normal]
    [Finite U] {b₀ : G} (hb₀S : b₀ ∈ S) (hnorm : ∀ u ∈ U, b₀ * u * b₀⁻¹ ∈ U)
    (hfix : ∀ u ∈ U, b₀ * u = u * b₀ → u = 1) : U ≤ S := by
  let φ : U → U := fun u => ⟨(u : G)⁻¹ * (b₀ * u * b₀⁻¹), U.mul_mem (U.inv_mem u.2) (hnorm _ u.2)⟩
  have hinj : Function.Injective φ := by
    intro u u' h
    have h1 : (u : G)⁻¹ * (b₀ * u * b₀⁻¹) = (u' : G)⁻¹ * (b₀ * u' * b₀⁻¹) := congrArg Subtype.val h
    have hv : b₀ * ((u : G) * (u' : G)⁻¹) = ((u : G) * (u' : G)⁻¹) * b₀ := by
      have e1 : b₀ * u * b₀⁻¹ = (u : G) * ((u' : G)⁻¹ * (b₀ * u' * b₀⁻¹)) := by
        calc b₀ * u * b₀⁻¹ = (u : G) * ((u : G)⁻¹ * (b₀ * u * b₀⁻¹)) := by group
          _ = _ := by rw [h1]
      have e2 : b₀ * (u : G) = (u : G) * ((u' : G)⁻¹ * (b₀ * u' * b₀⁻¹)) * b₀ := by
        calc b₀ * (u : G) = (b₀ * u * b₀⁻¹) * b₀ := by group
          _ = _ := by rw [e1]
      calc b₀ * ((u : G) * (u' : G)⁻¹)
          = (b₀ * (u : G)) * (u' : G)⁻¹ := by group
        _ = ((u : G) * ((u' : G)⁻¹ * (b₀ * u' * b₀⁻¹)) * b₀) * (u' : G)⁻¹ := by rw [e2]
        _ = (u : G) * (u' : G)⁻¹ * b₀ := by group
    have hvU : (u : G) * (u' : G)⁻¹ ∈ U := U.mul_mem u.2 (U.inv_mem u'.2)
    have := hfix _ hvU hv
    exact Subtype.ext (by simpa [mul_inv_eq_one] using this)
  have hsurj : Function.Surjective φ := Finite.surjective_of_injective hinj
  intro u hu
  obtain ⟨w, hw⟩ := hsurj ⟨u, hu⟩
  have hw' : (w : G)⁻¹ * (b₀ * w * b₀⁻¹) = u := congrArg Subtype.val hw
  rw [← hw']
  have : (w : G)⁻¹ * (b₀ * w * b₀⁻¹) = ((w : G)⁻¹ * b₀ * (w : G)) * b₀⁻¹ := by group
  rw [this]
  have hconj : (w : G)⁻¹ * b₀ * (w : G) ∈ S := by
    have := (inferInstance : S.Normal).conj_mem b₀ hb₀S (w : G)⁻¹
    simpa [mul_assoc] using this
  exact S.mul_mem hconj (S.inv_mem hb₀S)

theorem rankOne_simple_normal {G : Type*} [Group G] (B U : Subgroup G) (hUB : U ≤ B)
    (hUnorm : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) (c : G)
    (hcell : ∀ g : G, g ∈ B ∨ ∃ b ∈ B, ∃ u ∈ U, g = b * c * u)
    (hmeet : ∀ u ∈ U, c * u * c⁻¹ ∈ B → u = 1)
    (hKC : ∀ k ∈ B, (∀ u ∈ U, k * u = u * k) → k ∈ U) (hBsolv : Group.IsSolvable B)
    (S : Subgroup G) [S.Normal] (hperf : ⁅S, S⁆ = S) (hUS : U ≤ S) (hSne : S ≠ ⊥)
    (A : Subgroup G) (hAS : A ≤ S) (hAn : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A) :
    A = ⊥ ∨ A = S := by
  have hSB : ¬ S ≤ B := by
    intro hSB
    apply hSne
    have hsolv : Group.IsSolvable S :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hSB) (Subgroup.inclusion_injective hSB)
    haveI : Group.IsPerfect S := Subgroup.isPerfect_iff.2 hperf
    by_contra hne
    haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hne
    exact Group.IsPerfect.not_isSolvable S hsolv
  obtain ⟨g, hgS, hgB⟩ := Set.not_subset.1 hSB
  by_cases hAB : A ≤ B
  ·
    left
    rcases hcell g with hg | ⟨b, hb, u, hu, hgbu⟩
    · exact absurd hg hgB
    have hc' : b * c ∈ S := by
      have : b * c = g * u⁻¹ := by rw [hgbu]; group
      rw [this]
      exact S.mul_mem hgS (S.inv_mem (hUS hu))
    have hAU : ∀ x ∈ A, x ∈ U → x = 1 := by
      intro x hxA hxU
      have h1 : (b * c) * x * (b * c)⁻¹ ∈ A := hAn _ hc' x hxA
      have h2 : c * x * c⁻¹ ∈ B := by
        have := B.mul_mem (B.mul_mem (B.inv_mem hb) (hAB h1)) hb
        have e : b⁻¹ * ((b * c) * x * (b * c)⁻¹) * b = c * x * c⁻¹ := by group
        rwa [e] at this
      exact hmeet x hxU h2
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have hcomm : ∀ u' ∈ U, a * u' = u' * a := by
      intro u' hu'
      have hz1 : a * u' * a⁻¹ * u'⁻¹ ∈ A := by
        have := A.mul_mem ha (hAn u' (hUS hu') a⁻¹ (A.inv_mem ha))
        have e : a * (u' * a⁻¹ * u'⁻¹) = a * u' * a⁻¹ * u'⁻¹ := by group
        rwa [e] at this
      have hz2 : a * u' * a⁻¹ * u'⁻¹ ∈ U := U.mul_mem (hUnorm a (hAB ha) u' hu') (U.inv_mem hu')
      have hz := hAU _ hz1 hz2
      have hc1 : ⁅a, u'⁆ = 1 := by simpa [commutatorElement_def] using hz
      exact commutatorElement_eq_one_iff_mul_comm.1 hc1
    exact hAU a ha (hKC a (hAB ha) hcomm)
  ·
    right
    obtain ⟨a₀, ha₀A, ha₀B⟩ := Set.not_subset.1 hAB
    obtain ⟨b₀, hb₀, u₀, hu₀, ha₀eq⟩ := (hcell a₀).resolve_left ha₀B
    have hdec : ∀ s ∈ S, ∃ a ∈ A, ∃ v ∈ S ⊓ B, s = a * v := by
      intro s hs
      by_cases hsB : s ∈ B
      · exact ⟨1, A.one_mem, s, ⟨hs, hsB⟩, by simp⟩
      obtain ⟨b', hb', u'', hu'', hs''⟩ := (hcell s).resolve_left hsB
      have hc₀ : b₀ * c = a₀ * u₀⁻¹ := by rw [ha₀eq]; group
      have hc₁ : b' * c = s * u''⁻¹ := by rw [hs'']; group
      have hv : b' * b₀⁻¹ ∈ S := by
        have e : b' * b₀⁻¹ = (b' * c) * (b₀ * c)⁻¹ := by group
        rw [e, hc₀, hc₁]
        exact S.mul_mem (S.mul_mem hs (S.inv_mem (hUS hu''))) (S.inv_mem (S.mul_mem (hAS ha₀A)
          (S.inv_mem (hUS hu₀))))
      refine ⟨(b' * b₀⁻¹) * a₀ * (b' * b₀⁻¹)⁻¹, hAn _ hv a₀ ha₀A,
        (b' * b₀⁻¹) * u₀⁻¹ * u'', ⟨?_, ?_⟩, ?_⟩
      · exact S.mul_mem (S.mul_mem hv (S.inv_mem (hUS hu₀))) (hUS hu'')
      · exact B.mul_mem (B.mul_mem (B.mul_mem hb' (B.inv_mem hb₀)) (B.inv_mem (hUB hu₀)))
          (hUB hu'')
      · have e : s = ((b' * b₀⁻¹) * a₀ * (b' * b₀⁻¹)⁻¹) * ((b' * b₀⁻¹) * u₀⁻¹ * u'') := by
          have e1 : (b' * b₀⁻¹) * a₀ * u₀⁻¹ * u'' = s := by
            calc (b' * b₀⁻¹) * a₀ * u₀⁻¹ * u'' = (b' * b₀⁻¹) * (a₀ * u₀⁻¹) * u'' := by group
              _ = (b' * b₀⁻¹) * (b₀ * c) * u'' := by rw [← hc₀]
              _ = (b' * c) * u'' := by group
              _ = s := by rw [hc₁]; group
          calc s = (b' * b₀⁻¹) * a₀ * u₀⁻¹ * u'' := e1.symm
            _ = _ := by group
        exact e
    haveI : Group.IsPerfect S := Subgroup.isPerfect_iff.2 hperf
    set A' : Subgroup S := A.subgroupOf S with hA'
    haveI hA'n : A'.Normal := ⟨fun x hx g => by
      have h1 : (x : G) ∈ A := hx
      exact hAn g.1 g.2 x h1⟩
    by_contra hne
    have hA'ne : A' ≠ ⊤ := by
      intro htop
      apply hne
      refine le_antisymm hAS fun x hx => ?_
      have : (⟨x, hx⟩ : S) ∈ A' := by rw [htop]; trivial
      exact this
    have hsurj : Function.Surjective ((QuotientGroup.mk' A').comp
        ((B.subgroupOf S).subtype)) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨a, haA, v, hv, hxav⟩ := hdec x.1 x.2
      refine ⟨⟨⟨v, hv.1⟩, hv.2⟩, ?_⟩
      show QuotientGroup.mk (⟨v, hv.1⟩ : S) = (QuotientGroup.mk x : S ⧸ A')
      rw [QuotientGroup.eq]
      have : (⟨v, hv.1⟩ : S)⁻¹ * x ∈ A' := by
        show ((v : G)⁻¹ * (x : G)) ∈ A
        have e : (v : G)⁻¹ * (x : G) = v⁻¹ * a * v := by rw [hxav]; group
        rw [e]
        have := hAn v⁻¹ (S.inv_mem hv.1) a haA
        simpa using this
      exact this
    let f : ↥(B.subgroupOf S) →* ↥B :=
      { toFun := fun v => ⟨(v.1 : G), v.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    haveI hBsolv' : Group.IsSolvable ↥(B.subgroupOf S) :=
      Group.isSolvable_of_isSolvable_injective (f := f) (by
        intro a b h
        have h' : ((a.1 : S) : G) = ((b.1 : S) : G) := congrArg (fun z : ↥B => (z : G)) h
        exact Subtype.ext (Subtype.ext h'))
    haveI : Group.IsSolvable (↥S ⧸ A') := Group.isSolvable_of_surjective hsurj
    haveI : Nontrivial (↥S ⧸ A') := by
      obtain ⟨x, hx⟩ : ∃ x : S, x ∉ A' := by
        by_contra hall
        push Not at hall
        exact hA'ne (eq_top_iff.2 fun x _ => hall x)
      exact ⟨⟨QuotientGroup.mk x, 1, fun h => hx ((QuotientGroup.eq_one_iff x).1 h)⟩⟩
    exact Group.IsPerfect.not_isSolvable (↥S ⧸ A') inferInstance

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2
