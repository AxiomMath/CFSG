module

public import CFSG.Fischer.NoF25.Blocks

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

section Main

variable (hE : Pair X E) (hF : Pair Y F)

include hE in
theorem conj_starImg
    (hstar : ∀ {q p : Y}, q ∈ F → p ∈ F → ∀ θ : LocalClass F q ≃ LocalClass F p,
      StarTau hF θ → ∃ r : Y, r * q * r⁻¹ = p ∧ ∀ x, (θ x : Y) = r * x * r⁻¹)
    {B : Set X} (hBE : B ⊆ E) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {e b : X} (he : e ∈ B) (hb : b ∈ B) (hbe : b ≠ e) (Se : StrongPoints hF E e)
    (Sb : StrongPoints hF E b) :
    ∃ r : Y, starImg hF Sb B = (fun x => r * x * r⁻¹) '' starImg hF Se B := by
  have hbE : b ∈ LocalClass E e := mem_localClass_of_mem hBE hBc he hb hbe
  have heB : e ∈ LocalClass E b := mem_localClass_of_mem hBE hBc hb he hbe.symm
  set fb : LocalClass E e := ⟨b, hbE⟩
  set fe : LocalClass E b := ⟨e, heB⟩
  set θ : LocalClass F (Se.L.χ fb : Y) ≃ LocalClass F (Sb.L.χ fe : Y) :=
    ((Se.L.restrictStar hF fb).symm.trans
      (Set.equivOfEq (Set.inter_comm (LocalClass E e) (LocalClass E b)))).trans
      (Sb.L.restrictStar hF fe) with hθdef
  have hθval : ∀ g : ↥(LocalClass E e ∩ LocalClass E b),
      (θ (Se.L.restrictStar hF fb g) : Y) = (Sb.L.χ ⟨g, g.2.2⟩ : Y) := by
    intro g
    rw [hθdef, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  have hθ : StarTau hF θ := by
    intro y z
    set g := (Se.L.restrictStar hF fb).symm y
    set h := (Se.L.restrictStar hF fb).symm z
    have hy : Se.L.restrictStar hF fb g = y := Equiv.apply_symm_apply _ _
    have hz : Se.L.restrictStar hF fb h = z := Equiv.apply_symm_apply _ _
    obtain ⟨hm, e1⟩ := Se.L.restrictStar_tau hF hE fb g h
    have e2 : (⟨(y : Y) * z * y, LocalPoints.mul_mul_mem_localClass hF y z⟩ :
        LocalClass F (Se.L.χ fb : Y)) = Se.L.restrictStar hF fb ⟨_, hm⟩ := by
      apply Subtype.ext
      rw [e1, hy, hz]
    rw [e2, hθval, ← hy, ← hz, hθval, hθval]
    obtain ⟨hm', e3⟩ := Sb.L.restrictStar_tau hF hE fe
      ⟨g, g.2.2, g.2.1⟩ ⟨h, h.2.2, h.2.1⟩
    exact e3
  obtain ⟨r, hrq, hr⟩ := hstar (Se.L.χ fb).2 (Sb.L.χ fe).2 θ hθ
  refine ⟨r, ?_⟩
  ext c
  constructor
  · rintro ⟨g, hgB, rfl⟩
    by_cases hge : (g : X) = e
    ·
      have hg : g = fe := Subtype.ext hge
      refine ⟨Se.L.χ fb, ⟨fb, hb, rfl⟩, ?_⟩
      show r * (Se.L.χ fb : Y) * r⁻¹ = (Sb.L.χ g : Y)
      rw [hg, hrq]
    · have hgE : (g : X) ∈ LocalClass E e := mem_localClass_of_mem hBE hBc he hgB hge
      have hgg : (g : X) ∈ LocalClass E e ∩ LocalClass E b := ⟨hgE, g.2⟩
      refine ⟨Se.L.χ ⟨g, hgE⟩, ⟨⟨g, hgE⟩, hgB, rfl⟩, ?_⟩
      have h1 := hr (Se.L.restrictStar hF fb ⟨g, hgg⟩)
      rw [hθval] at h1
      rw [LocalPoints.restrictStar_val] at h1
      exact h1.symm
  · rintro ⟨_, ⟨g, hgB, rfl⟩, rfl⟩
    by_cases hgb : (g : X) = b
    · have hg : g = fb := Subtype.ext hgb
      refine ⟨fe, he, ?_⟩
      show (Sb.L.χ fe : Y) = r * (Se.L.χ g : Y) * r⁻¹
      rw [hg, hrq]
    · have hgE : (g : X) ∈ LocalClass E b := mem_localClass_of_mem hBE hBc hb hgB hgb
      have hgg : (g : X) ∈ LocalClass E e ∩ LocalClass E b := ⟨g.2, hgE⟩
      refine ⟨⟨g, hgE⟩, hgB, ?_⟩
      have h1 := hr (Se.L.restrictStar hF fb ⟨g, hgg⟩)
      rw [hθval] at h1
      rw [LocalPoints.restrictStar_val] at h1
      exact h1

include hE in
theorem false_of_strongPoints
    (hrig : ∀ σ : tauGroup hF, σ ∈ (innerTau hF).range)
    (hstar : ∀ {q p : Y}, q ∈ F → p ∈ F → ∀ θ : LocalClass F q ≃ LocalClass F p,
      StarTau hF θ → ∃ r : Y, r * q * r⁻¹ = p ∧ ∀ x, (θ x : Y) = r * x * r⁻¹)
    (Bbar : Set Y) (hBF : Bbar ⊆ F) (hB24 : Bbar.ncard = 24)
    (hBc : ∀ x ∈ Bbar, ∀ y ∈ Bbar, x * y = y * x) (h759 : (Oset Bbar 8).ncard = 759)
    {e : X} (he : e ∈ E) (Sall : ∀ b ∈ E, Nonempty (StrongPoints hF E b)) : False := by
  classical
  set Se := (Sall e he).some
  set A : Set (LocalClass E e) := {f | (Se.L.χ f : Y) ∈ Bbar}
  set B : Set X := insert e (Subtype.val '' A)
  have hBfin : Bbar.Finite := Set.finite_of_ncard_ne_zero (by rw [hB24]; norm_num)
  have hAfin : A.Finite := by
    have h := hBfin.preimage (f := fun f : LocalClass E e => (Se.L.χ f : Y))
      (fun f _ g _ h => Se.L.χ.injective (Subtype.ext h))
    exact h
  have hBf : B.Finite := (hAfin.image _).insert e
  have hBE : B ⊆ E := by
    rintro y (rfl | ⟨f, -, rfl⟩)
    · exact he
    · exact f.2.1
  have hBc' : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    have hcomm : ∀ f ∈ A, ∀ g ∈ A, (f : X) * g = g * f := fun f hf g hg =>
      (Se.L.comm f g).2 (hBc _ hf _ hg)
    rintro x (rfl | ⟨f, hf, rfl⟩) y (rfl | ⟨g, hg, rfl⟩)
    · rfl
    · exact g.2.2.2.symm
    · exact f.2.2.2
    · exact hcomm f hf g hg
  have heB : e ∈ B := Set.mem_insert e _
  have hSe : starImg hF Se B = Bbar := by
    ext c
    constructor
    · rintro ⟨f, hfB, rfl⟩
      rcases hfB with hfe | ⟨g, hg, hgf⟩
      · exact absurd hfe f.2.2.1
      · rw [show f = g from Subtype.ext hgf.symm]
        exact hg
    · intro hc
      obtain ⟨f, hf⟩ := Se.L.χ.surjective ⟨c, hBF hc⟩
      refine ⟨f, Or.inr ⟨f, ?_, rfl⟩, by show (Se.L.χ f : Y) = c; rw [hf]⟩
      show (Se.L.χ f : Y) ∈ Bbar
      rw [hf]
      exact hc
  have hB25 : B.ncard = 25 := by
    have h1 : e ∉ Subtype.val '' A := by
      rintro ⟨f, -, hf⟩
      exact f.2.2.1 hf
    rw [Set.ncard_insert_of_notMem h1 (hAfin.image _),
      Set.ncard_image_of_injective _ Subtype.val_injective]
    have h2 : A.ncard = Bbar.ncard := by
      rw [← Set.ncard_image_of_injective A (f := fun f : LocalClass E e => (Se.L.χ f : Y))
        (fun f g h => Se.L.χ.injective (Subtype.ext h))]
      congr 1
      ext c
      constructor
      · rintro ⟨f, hf, rfl⟩
        exact hf
      · intro hc
        obtain ⟨f, hf⟩ := Se.L.χ.surjective ⟨c, hBF hc⟩
        exact ⟨f, by show (Se.L.χ f : Y) ∈ Bbar; rw [hf]; exact hc,
          by show (Se.L.χ f : Y) = c; rw [hf]⟩
    rw [h2, hB24]
  have hdeg : ∀ b ∈ B, {G | G ∈ Oset B 9 ∧ b ∈ G}.ncard = 759 := by
    intro b hb
    set Sb := (Sall b (hBE hb)).some
    rw [ncard_blocks_through hE hF hrig hBE hBc' hb Sb hBf]
    by_cases hbe : b = e
    · subst hbe
      rw [hSe]
      exact h759
    · obtain ⟨r, hr⟩ := conj_starImg hE hF hstar hBE hBc' heB hb hbe Se Sb
      rw [hr, hSe, ncard_Oset_conj]
      exact h759
  refine false_of_double_count hBf hB25 (Oset B 9) ?_ ?_ hdeg
  · rintro G ⟨x, -, -, rfl, -⟩
    exact fun y hy => hy.1
  · rintro G ⟨x, -, -, -, hk⟩
    exact hk

end Main

end CFSG.Fischer
