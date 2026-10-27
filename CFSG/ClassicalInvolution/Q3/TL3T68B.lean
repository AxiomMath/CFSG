module

public import CFSG.ClassicalInvolution.Q3.TL3T68

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open scoped Pointwise

variable {m : ℕ}

private theorem altFix_le_of_alternatingGroup_le (α : Finset (Fin m))
    (H : Subgroup (alternatingGroup (Fin m)))
    (Gs : Subgroup (Equiv.Perm {x : Fin m // x ∉ α}))
    (hGs : ∀ g ∈ Gs, ∃ h ∈ H, (h : Equiv.Perm (Fin m)) = Equiv.Perm.ofSubtype g)
    (key : alternatingGroup {x : Fin m // x ∉ α} ≤ Gs) :
    altFix (α : Set (Fin m)) ≤ H := by
  classical
  intro σ hσ
  have hσα : ∀ x ∈ α, (σ : Equiv.Perm (Fin m)) x = x := fun x hx =>
    hσ x (Finset.mem_coe.mpr hx)
  have h₁ : ∀ x, ((σ : Equiv.Perm (Fin m)) x ∉ α) ↔ (x ∉ α) := by
    intro x
    constructor
    · intro h hx
      apply h
      rw [hσα x hx]
      exact hx
    · intro h hx
      apply h
      have h' : (σ : Equiv.Perm (Fin m)) x = x :=
        (σ : Equiv.Perm (Fin m)).injective (hσα _ hx)
      rw [h'] at hx
      exact hx
  have h₂ : ∀ x, (σ : Equiv.Perm (Fin m)) x ≠ x → x ∉ α := fun x hx hxα => hx (hσα x hxα)
  obtain ⟨τ, hτσ⟩ : ∃ τ : Equiv.Perm {x : Fin m // x ∉ α},
      Equiv.Perm.ofSubtype τ = (σ : Equiv.Perm (Fin m)) :=
    ⟨(σ : Equiv.Perm (Fin m)).subtypePerm (p := fun x => x ∉ α) h₁,
      Equiv.Perm.ofSubtype_subtypePerm (p := fun x => x ∉ α) h₁ h₂⟩
  have hτA : τ ∈ alternatingGroup {x : Fin m // x ∉ α} := by
    rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.Perm.sign_ofSubtype, hτσ]
    exact Equiv.Perm.mem_alternatingGroup.mp σ.2
  obtain ⟨h, hhH, hh⟩ := hGs τ (key hτA)
  rw [hτσ] at hh
  have hhσ : h = σ := Subtype.ext hh
  rw [hhσ] at hhH
  exact hhH

theorem altFix_le_sup' (α P Q : Finset (Fin m)) (hPQ : Disjoint P Q) (hP : P.card ≤ 2)
    (hQ : Q.card ≤ 2) (hαP : Disjoint α P) (hαQ : Disjoint α Q) (hm : α.card + 5 ≤ m) :
    altFix (α : Set (Fin m)) ≤
      altFix ((α ∪ P : Finset (Fin m)) : Set (Fin m)) ⊔
        altFix ((α ∪ Q : Finset (Fin m)) : Set (Fin m)) := by
  classical
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (alternatingGroup (Fin m)), H =
      altFix ((α ∪ P : Finset (Fin m)) : Set (Fin m)) ⊔
        altFix ((α ∪ Q : Finset (Fin m)) : Set (Fin m)) := ⟨_, rfl⟩
  have hHP : altFix ((α ∪ P : Finset (Fin m)) : Set (Fin m)) ≤ H := by
    rw [hH]
    exact le_sup_left
  have hHQ : altFix ((α ∪ Q : Finset (Fin m)) : Set (Fin m)) ≤ H := by
    rw [hH]
    exact le_sup_right
  rw [← hH]
  obtain ⟨Gs, hGs⟩ : ∃ Gs : Subgroup (Equiv.Perm {x : Fin m // x ∉ α}),
      ∀ g, g ∈ Gs ↔ ∃ h ∈ H, (h : Equiv.Perm (Fin m)) = Equiv.Perm.ofSubtype g :=
    ⟨(H.map (alternatingGroup (Fin m)).subtype).comap
      (Equiv.Perm.ofSubtype : Equiv.Perm {x : Fin m // x ∉ α} →* Equiv.Perm (Fin m)),
      fun g => Iff.rfl⟩
  refine altFix_le_of_alternatingGroup_le α H Gs (fun g hg => (hGs g).mp hg) ?_
  have hgen : ∀ R : Finset (Fin m), Disjoint α R →
      altFix ((α ∪ R : Finset (Fin m)) : Set (Fin m)) ≤ H →
      ∀ g : Equiv.Perm {x : Fin m // x ∉ α}, Equiv.Perm.sign g = 1 →
        (∀ x : {x : Fin m // x ∉ α}, (x : Fin m) ∈ R → g x = x) → g ∈ Gs := by
    intro R hαR hle g hsign hfix
    have hg : Equiv.Perm.ofSubtype g ∈ alternatingGroup (Fin m) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
      exact hsign
    refine (hGs g).mpr ⟨⟨Equiv.Perm.ofSubtype g, hg⟩, hle (mem_altFix.mpr fun x hx => ?_), rfl⟩
    show Equiv.Perm.ofSubtype g x = x
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hxα | hxR
    · exact Equiv.Perm.ofSubtype_apply_of_not_mem g (fun h => h hxα)
    · have hxα : x ∉ α := fun h => Finset.disjoint_left.mp hαR h hxR
      rw [Equiv.Perm.ofSubtype_apply_of_mem g hxα]
      exact congrArg Subtype.val (hfix ⟨x, hxα⟩ hxR)
  have hcyc : ∀ R : Finset (Fin m), Disjoint α R →
      altFix ((α ∪ R : Finset (Fin m)) : Set (Fin m)) ≤ H →
      ∀ a b d : {x : Fin m // x ∉ α}, a ≠ b → a ≠ d → b ≠ d →
        (a : Fin m) ∉ R → (b : Fin m) ∉ R → (d : Fin m) ∉ R →
        Equiv.swap a b * Equiv.swap a d ∈ Gs := by
    intro R hαR hle a b d hab had hbd haR hbR hdR
    refine hgen R hαR hle _ ?_ ?_
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap had]
      decide
    · intro x hxR
      have hxa : x ≠ a := fun h => haR (by rw [← h]; exact hxR)
      have hxb : x ≠ b := fun h => hbR (by rw [← h]; exact hxR)
      have hxd : x ≠ d := fun h => hdR (by rw [← h]; exact hxR)
      show Equiv.swap a b (Equiv.swap a d x) = x
      rw [Equiv.swap_apply_of_ne_of_ne hxa hxd, Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have hfree : ∀ R : Finset (Fin m), R.card ≤ 4 → ∃ z : Fin m, z ∉ α ∧ z ∉ R := by
    intro R hR
    by_contra! hcon
    have hsub : (Finset.univ : Finset (Fin m)) ⊆ α ∪ R := fun z _ => by
      by_cases hz : z ∈ α
      · exact Finset.mem_union_left _ hz
      · exact Finset.mem_union_right _ (hcon z hz)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le α R
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hthird : ∀ R : Finset (Fin m), R.card ≤ 2 → ∀ x y : Fin m,
      ∃ z : {x : Fin m // x ∉ α}, (z : Fin m) ∉ R ∧ (z : Fin m) ≠ x ∧ (z : Fin m) ≠ y := by
    intro R hR x y
    obtain ⟨z, hzα, hz⟩ := hfree (insert x (insert y R)) (by
      have h1 := Finset.card_insert_le x (insert y R)
      have h2 := Finset.card_insert_le y R
      omega)
    simp only [Finset.mem_insert, not_or] at hz
    exact ⟨⟨z, hzα⟩, hz.2.2, hz.1, hz.2.1⟩
  obtain ⟨w, hwP, hwQ⟩ : ∃ w : {x : Fin m // x ∉ α}, (w : Fin m) ∉ P ∧ (w : Fin m) ∉ Q := by
    obtain ⟨z, hzα, hz⟩ := hfree (P ∪ Q) (by have := Finset.card_union_le P Q; omega)
    exact ⟨⟨z, hzα⟩, fun h => hz (Finset.mem_union_left _ h),
      fun h => hz (Finset.mem_union_right _ h)⟩
  have hmove : ∀ R : Finset (Fin m), Disjoint α R →
      altFix ((α ∪ R : Finset (Fin m)) : Set (Fin m)) ≤ H → R.card ≤ 2 → (w : Fin m) ∉ R →
      ∀ x : {x : Fin m // x ∉ α}, (x : Fin m) ∉ R → ∃ g ∈ Gs, g w = x := by
    intro R hαR hle hRc hwR x hxR
    by_cases hxw : x = w
    · exact ⟨1, Gs.one_mem, by rw [hxw]; rfl⟩
    · obtain ⟨z, hzR, hzw, hzx⟩ := hthird R hRc w x
      have hwz : w ≠ z := fun h => hzw (congrArg Subtype.val h).symm
      have hwx : w ≠ x := fun h => hxw h.symm
      have hzx' : z ≠ x := fun h => hzx (congrArg Subtype.val h)
      refine ⟨Equiv.swap w z * Equiv.swap w x,
        hcyc R hαR hle w z x hwz hwx hzx' hwR hzR hxR, ?_⟩
      show Equiv.swap w z (Equiv.swap w x w) = x
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxw hzx'.symm]
  haveI : MulAction.IsPretransitive Gs {x : Fin m // x ∉ α} := by
    rw [MulAction.isPretransitive_iff_base w]
    intro x
    obtain ⟨g, hg, hgw⟩ : ∃ g ∈ Gs, g w = x := by
      by_cases hxP : (x : Fin m) ∈ P
      · exact hmove Q hαQ hHQ hQ hwQ x (fun h => Finset.disjoint_left.mp hPQ hxP h)
      · exact hmove P hαP hHP hP hwP x hxP
    exact ⟨⟨g, hg⟩, hgw⟩
  have hprim : MulAction.IsPreprimitive Gs {x : Fin m // x ∉ α} := by
    refine MulAction.IsPreprimitive.of_isTrivialBlock_base w fun {B} hwB hB => ?_
    by_cases hsub : B.Subsingleton
    · exact Or.inl hsub
    right
    obtain ⟨b, hbB, hbw⟩ : ∃ b ∈ B, b ≠ w := by
      by_contra! h
      exact hsub fun a ha b hb => (h a ha).trans (h b hb).symm
    have hS : ∀ R : Finset (Fin m), Disjoint α R →
        altFix ((α ∪ R : Finset (Fin m)) : Set (Fin m)) ≤ H → R.card ≤ 2 → (w : Fin m) ∉ R →
        ∀ y : {x : Fin m // x ∉ α}, (y : Fin m) ∉ R → y ∈ B := by
      intro R hαR hle hRc hwR y hyR
      by_contra hyB
      obtain ⟨z, hzR, hzw, hzy⟩ := hthird R hRc w y
      have hwy : w ≠ y := fun h => hyB (by rw [← h]; exact hwB)
      have hwz : w ≠ z := fun h => hzw (congrArg Subtype.val h).symm
      have hyz : y ≠ z := fun h => hzy (congrArg Subtype.val h).symm
      let c : Gs := ⟨Equiv.swap w y * Equiv.swap w z,
        hcyc R hαR hle w y z hwy hwz hyz hwR hyR hzR⟩
      have hcw : c • w = z := by
        show Equiv.swap w y (Equiv.swap w z w) = z
        rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hwz.symm hyz.symm]
      have hcz : c • z = y := by
        show Equiv.swap w y (Equiv.swap w z z) = y
        rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
      by_cases hzB : z ∈ B
      · have hcB : c • B = B := hB.smul_eq_of_mem (g := c) hwB (by rw [hcw]; exact hzB)
        have h1 : c • z ∈ c • B := Set.smul_mem_smul_set hzB
        rw [hcB, hcz] at h1
        exact hyB h1
      · have hby : b ≠ y := fun h => hyB (by rw [← h]; exact hbB)
        have hbz : b ≠ z := fun h => hzB (by rw [← h]; exact hbB)
        have hcb : c • b = b := by
          show Equiv.swap w y (Equiv.swap w z b) = b
          rw [Equiv.swap_apply_of_ne_of_ne hbw hbz, Equiv.swap_apply_of_ne_of_ne hbw hby]
        have hcB : c • B = B := hB.smul_eq_of_mem (g := c) hbB (by rw [hcb]; exact hbB)
        have h1 : c • w ∈ c • B := Set.smul_mem_smul_set hwB
        rw [hcB, hcw] at h1
        exact hzB h1
    ext y
    simp only [Set.mem_univ, iff_true]
    by_cases hyP : (y : Fin m) ∈ P
    · exact hS Q hαQ hHQ hQ hwQ y (fun h => Finset.disjoint_left.mp hPQ hyP h)
    · exact hS P hαP hHP hP hwP y hyP
  obtain ⟨y, hyP, hyw, -⟩ := hthird P hP w w
  obtain ⟨z, hzP, hzw, hzy⟩ := hthird P hP w y
  have hwy : w ≠ y := fun h => hyw (congrArg Subtype.val h).symm
  have hwz : w ≠ z := fun h => hzw (congrArg Subtype.val h).symm
  have hyz : y ≠ z := fun h => hzy (congrArg Subtype.val h).symm
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same hwy hwz hyz)
    (hcyc P hαP hHP w y z hwy hwz hyz hwP hyP hzP)

end CFSG.ClassicalInvolution.Q3.AE
