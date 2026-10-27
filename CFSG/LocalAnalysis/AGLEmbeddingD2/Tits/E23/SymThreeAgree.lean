module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightThree

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.G6

theorem perm_fix_exists_core3 : ∀ τ : Equiv.Perm (Fin 3), τ ≠ 1 → τ * τ = 1 →
    ∃ w : PermMod 3, (∑ i, Multiplicative.toAdd w i = 0) ∧ w ≠ 1 ∧ permAct 3 τ w = w := by
  decide +kernel

theorem perm_fix_eq_of_core3 : ∀ σ τ : Equiv.Perm (Fin 3), ∀ w : PermMod 3,
    (∑ i, Multiplicative.toAdd w i = 0) → w ≠ 1 → τ ≠ 1 →
    permAct 3 τ w = w → permAct 3 σ w = w → σ = 1 ∨ σ = τ := by
  decide +kernel

theorem exists_mem_agree_of_symData_three {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {E R : Subgroup (MulAut V)} (θ : ↥E ≃* Equiv.Perm (Fin 3)) (β : ↥(commV E) →* coreMod 3)
    (hinv : ∀ x ∈ E, ∀ p ∈ commV E, x p ∈ commV E) (hsurj : Function.Surjective β)
    (hker : β.ker = ⊥)
    (hequiv : ∀ (x : ↥E) (p : ↥(commV E)) (hp : (x : MulAut V) p ∈ commV E),
      β ⟨(x : MulAut V) p, hp⟩ = coreAct 3 (θ x) (β p))
    (hRE : R ≤ E) (hR2 : Nat.card R = 2) {x : MulAut V} (hxE : ∀ p ∈ commV E, x p ∈ commV E)
    (hx : ∀ w ∈ commV E, (∀ r ∈ R, r w = w) → x w = w) :
    ∃ u ∈ R, ∀ w ∈ commV E, x w = u w := by
  classical
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).1 hker
  let βe : ↥(commV E) ≃* coreMod 3 := MulEquiv.ofBijective β ⟨hinj, hsurj⟩
  let xh : ↥(commV E) →* ↥(commV E) :=
    { toFun := fun p => ⟨x (p : V), hxE p p.2⟩
      map_one' := Subtype.ext (map_one x)
      map_mul' := fun p q => Subtype.ext (map_mul x (p : V) (q : V)) }
  have hxinj : Function.Injective xh := by
    intro p q h
    apply Subtype.ext
    exact MulEquiv.injective x (congrArg Subtype.val h)
  let ψ : ↥(commV E) ≃* ↥(commV E) :=
    MulEquiv.ofBijective xh ⟨hxinj, Finite.surjective_of_injective hxinj⟩
  obtain ⟨e, hagree⟩ : ∃ e : ↥E, ∀ p : ↥(commV E), (e : MulAut V) (p : V) = x (p : V) := by
    obtain ⟨π, hπ⟩ :=
      CFSG.CGT.PushingUpLit.CGT6.coreAct_three_surjective (βe.symm.trans (ψ.trans βe))
    refine ⟨θ.symm π, fun p => ?_⟩
    have hp : ((θ.symm π : ↥E) : MulAut V) (p : V) ∈ commV E :=
      hinv _ (θ.symm π).2 (p : V) p.2
    have hb : β ⟨((θ.symm π : ↥E) : MulAut V) (p : V), hp⟩ = β (xh p) := by
      rw [hequiv (θ.symm π) p hp, MulEquiv.apply_symm_apply, hπ]
      have hsy : βe.symm (β p) = p := βe.symm_apply_apply p
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hsy]
      rfl
    exact congrArg Subtype.val (hinj hb)
  have key : ∀ a b : ↥R, a ≠ b → (∀ s : ↥R, s = a ∨ s = b) →
      ∃ r : ↥R, r ≠ 1 ∧ ∀ s : ↥R, s = 1 ∨ s = r := by
    intro a b hab hmem
    rcases hmem 1 with h1 | h1
    · refine ⟨b, fun hb => hab (h1.symm.trans hb.symm), fun s => ?_⟩
      rcases hmem s with h | h
      · exact Or.inl (h.trans h1.symm)
      · exact Or.inr h
    · refine ⟨a, fun ha => hab (ha.trans h1), fun s => ?_⟩
      rcases hmem s with h | h
      · exact Or.inr h
      · exact Or.inl (h.trans h1.symm)
  obtain ⟨r, hr1, hRset⟩ : ∃ r : ↥R, r ≠ 1 ∧ ∀ s : ↥R, s = 1 ∨ s = r := by
    obtain ⟨a, b, hab, huniv⟩ := Nat.card_eq_two_iff.1 hR2
    refine key a b hab fun s => ?_
    have h : s ∈ ({a, b} : Set ↥R) := by
      rw [huniv]
      exact Set.mem_univ s
    simpa using h
  have hrr : (r : MulAut V) * r = 1 := by
    rcases hRset (r * r) with h | h
    · simpa using congrArg Subtype.val h
    · exact absurd (by simpa using h) hr1
  let r' : ↥E := ⟨(r : MulAut V), hRE r.2⟩
  have hr'1 : r' ≠ 1 := fun h => hr1 (Subtype.ext (show (r : MulAut V) = 1 from congrArg Subtype.val h))
  have hr'r' : r' * r' = 1 := Subtype.ext hrr
  have hτ1 : θ r' ≠ 1 := fun h => hr'1 (θ.injective (h.trans (map_one θ).symm))
  have hτ2 : θ r' * θ r' = 1 := by rw [← map_mul, hr'r', map_one]
  obtain ⟨w, hw, hw1, hτw⟩ := perm_fix_exists_core3 (θ r') hτ1 hτ2
  let wU : ↥(coreMod 3) := ⟨w, mem_coreMod.2 hw⟩
  let w₀ : ↥(commV E) := βe.symm wU
  have hβw₀ : β w₀ = wU := βe.apply_symm_apply wU
  have hr_fix : (r' : MulAut V) (w₀ : V) = (w₀ : V) := by
    have hm : (r' : MulAut V) (w₀ : V) ∈ commV E := hinv _ r'.2 (w₀ : V) w₀.2
    have h := hequiv r' w₀ hm
    have h2 : coreAct 3 (θ r') wU = wU := Subtype.ext hτw
    have h3 : β ⟨(r' : MulAut V) (w₀ : V), hm⟩ = β w₀ := by
      rw [h, hβw₀, h2]
    exact congrArg Subtype.val (hinj h3)
  have hR_fix : ∀ s ∈ R, s (w₀ : V) = (w₀ : V) := by
    intro s hs
    rcases hRset ⟨s, hs⟩ with h | h
    · have hs1 : s = 1 := congrArg Subtype.val h
      rw [hs1]
      rfl
    · have hsr : s = (r : MulAut V) := congrArg Subtype.val h
      rw [hsr]
      exact hr_fix
  have hxfix : x (w₀ : V) = (w₀ : V) := hx (w₀ : V) w₀.2 hR_fix
  have hefix : (e : MulAut V) (w₀ : V) = (w₀ : V) := by
    rw [hagree w₀, hxfix]
  have hσ : coreAct 3 (θ e) wU = wU := by
    have hm : (e : MulAut V) (w₀ : V) ∈ commV E := hinv _ e.2 (w₀ : V) w₀.2
    have h := hequiv e w₀ hm
    have hfixSub : (⟨(e : MulAut V) (w₀ : V), hm⟩ : ↥(commV E)) = w₀ := Subtype.ext hefix
    rw [hfixSub, hβw₀] at h
    exact h.symm
  have hσw : permAct 3 (θ e) w = w := congrArg Subtype.val hσ
  have hemem : (e : MulAut V) ∈ R := by
    rcases perm_fix_eq_of_core3 (θ e) (θ r') w hw hw1 hτ1 hτw hσw with h | h
    · have he : e = 1 := θ.injective (h.trans (map_one θ).symm)
      have he' : (e : MulAut V) = 1 := by rw [he]; rfl
      rw [he']
      exact R.one_mem
    · have he : e = r' := θ.injective h
      have he' : (e : MulAut V) = (r : MulAut V) := congrArg Subtype.val he
      rw [he']
      exact r.2
  exact ⟨(e : MulAut V), hemem, fun w hw => (hagree ⟨w, hw⟩).symm⟩

end CFSG.AGLEmbeddingD2.Tits.E23

end
