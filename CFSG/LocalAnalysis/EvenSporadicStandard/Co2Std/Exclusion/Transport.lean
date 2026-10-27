module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Descend
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

private theorem mulAut_congr_apply {A A' : Type*} [Group A] [Group A'] (e : A ≃* A')
    (f : MulAut A) (a' : A') : MulAut.congr e f a' = e (f (e.symm a')) := rfl

private theorem mulAut_congr_symm {A A' : Type*} [Group A] [Group A'] (e : A ≃* A') :
    (MulAut.congr e).symm = MulAut.congr e.symm := by
  ext f a
  rfl

private theorem mulAut_congr_symm_apply {A A' : Type*} [Group A] [Group A'] (e : A ≃* A')
    (f : MulAut A') (a : A) : (MulAut.congr e).symm f a = e.symm (f (e a)) := by
  rw [mulAut_congr_symm, mulAut_congr_apply]
  simp

private theorem mulAut_congr_conj {A A' : Type*} [Group A] [Group A'] (e : A ≃* A')
    (z : A) : MulAut.congr e (MulAut.conj z) = MulAut.conj (e z) := by
  ext f
  simp [mulAut_congr_apply, MulAut.conj_apply, map_mul]

private theorem map_centralizer_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (D : Subgroup G) :
    (Subgroup.centralizer (D : Set G)).map e.toMonoidHom
      = Subgroup.centralizer ((D.map e.toMonoidHom : Subgroup H) : Set H) := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    change g ∈ Subgroup.centralizer (D : Set G) at hg
    rw [Subgroup.mem_centralizer_iff] at hg
    show e g ∈ Subgroup.centralizer ((D.map e.toMonoidHom : Subgroup H) : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨d, hd, rfl⟩
    simpa using congrArg e (hg d hd)
  · intro hh
    refine ⟨e.symm h, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff] at hh
    show e.symm h ∈ Subgroup.centralizer (D : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hh (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)

private theorem map_map_symm {G H : Type*} [Group G] [Group H] (e : G ≃* H) (K : Subgroup H) :
    (K.map e.symm.toMonoidHom).map e.toMonoidHom = K := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id K using 2
  ext x
  simp

private theorem natCard_fixedPoints_map_congr {A A' : Type*} [Group A] [Group A'] (e : A ≃* A')
    (Y' : Subgroup (MulAut A')) :
    Nat.card {a : A // ∀ y ∈ Y'.map (MulAut.congr e).symm.toMonoidHom, y a = a}
      = Nat.card {a' : A' // ∀ y ∈ Y', y a' = a'} := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
  intro a
  constructor
  · intro ha y' hy'
    change y' (e a) = e a
    have hy : (MulAut.congr e).symm y' ∈ Y'.map (MulAut.congr e).symm.toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.congr e).symm.toMonoidHom hy'
    have h := ha ((MulAut.congr e).symm y') hy
    have h' : e.symm (y' (e a)) = a := by
      rw [← mulAut_congr_symm_apply e y' a]
      exact h
    have := congrArg e h'
    simpa using this
  · intro ha y hy
    rcases Subgroup.mem_map.mp hy with ⟨y', hy', rfl⟩
    apply e.injective
    simp only [MulEquiv.coe_toMonoidHom]
    rw [mulAut_congr_symm_apply]
    simpa using ha y' hy'

theorem ModuleFacts.map_mulEquiv {A A' : Type*} [Group A] [Group A'] {Q : Subgroup (MulAut A)}
    {t : A} (h : ModuleFacts Q t) (e : A ≃* A') :
    ModuleFacts (Q.map (MulAut.congr e).toMonoidHom) (e t) := by
  set c : MulAut A ≃* MulAut A' := MulAut.congr e
  set Q' : Subgroup (MulAut A') := Q.map c.toMonoidHom
  have hD : (⁅Q, Q⁆ : Subgroup (MulAut A)).map c.toMonoidHom = ⁅Q', Q'⁆ := by
    rw [Subgroup.map_commutator]
  have hQ' : Q' = Q.map c.toMonoidHom := rfl
  have hmemQ' : ∀ g : MulAut A, c g ∈ Q' ↔ g ∈ Q := by
    intro g
    rw [hQ']
    exact Subgroup.mem_map_iff_mem (f := c.toMonoidHom) c.injective
  have hmemD : ∀ g : MulAut A, c g ∈ ⁅Q', Q'⁆ ↔ g ∈ ⁅Q, Q⁆ := by
    intro g
    rw [← hD]
    exact Subgroup.mem_map_iff_mem (f := c.toMonoidHom) c.injective
  refine
    { card := ?_
      elemAb := ?_
      card_Q := ?_
      invariant_ncard := ?_
      overgroup := ?_
      normalizer_derived := ?_
      derived_simple := ?_
      card_derived := ?_
      centralizer_derived := ?_
      irreducible_derived := ?_
      endo_derived := ?_
      noOffenders := ?_
      noBilin := ?_
      dual_cocycle := ?_
      noWedge := ?_
      noZ4 := ?_
      split_of_fixed := ?_ }
  · rw [← Nat.card_congr e.toEquiv]
    exact h.card
  · exact IsElementaryAbelian.of_mulEquiv e h.elemAb
  · rw [← Nat.card_congr (Subgroup.equivMapOfInjective Q c.toMonoidHom c.injective).toEquiv]
    exact h.card_Q
  · intro S' h1 hS'
    have h1' : (1 : A) ∉ e ⁻¹' S' := by
      intro hmem
      exact h1 (by simpa using hmem)
    have hinv : ∀ g ∈ Q, ∀ s ∈ e ⁻¹' S', g s ∈ e ⁻¹' S' := by
      intro g hg s hs
      have hcg : c g ∈ Q' := (hmemQ' g).mpr hg
      have h := hS' (c g) hcg (e s) hs
      simpa [c, mulAut_congr_apply] using h
    have hmain := h.invariant_ncard (e ⁻¹' S') h1' hinv
    have hcard : S'.ncard = (e ⁻¹' S').ncard := by
      conv_lhs => rw [← Set.image_preimage_eq S' e.surjective]
      rw [Set.ncard_image_of_injective _ e.injective]
    rwa [hcard]
  · intro X' hQX' h31 h37 h43
    set X : Subgroup (MulAut A) := X'.map c.symm.toMonoidHom
    have hQX : Q ≤ X := by
      intro g hg
      have hcg : c g ∈ X' := hQX' ((hmemQ' g).mpr hg)
      have hmem : c.symm (c g) ∈ X := Subgroup.mem_map_of_mem c.symm.toMonoidHom hcg
      simpa using hmem
    have hcardX : Nat.card X = Nat.card X' :=
      (Nat.card_congr
        (Subgroup.equivMapOfInjective X' c.symm.toMonoidHom c.symm.injective).toEquiv).symm
    have hXQ : X = Q :=
      h.overgroup X hQX (by rwa [hcardX]) (by rwa [hcardX]) (by rwa [hcardX])
    have hmap : X.map c.toMonoidHom = X' := map_map_symm c X'
    have hthis := congrArg (fun Y : Subgroup (MulAut A) => Y.map c.toMonoidHom) hXQ
    rw [hmap, ← hQ'] at hthis
    exact hthis
  · intro g' hg'
    have hg : c.symm g' ∈ Q := by
      apply h.normalizer_derived (c.symm g')
      intro hh hhh
      have hch : c hh ∈ ⁅Q', Q'⁆ := by
        rw [← hD]
        exact Subgroup.mem_map_of_mem c.toMonoidHom hhh
      have hstep : c (c.symm g' * hh * (c.symm g')⁻¹) ∈ ⁅Q', Q'⁆ := by
        rw [map_mul, map_mul, map_inv, c.apply_symm_apply]
        exact hg' (c hh) hch
      rw [← hD] at hstep
      exact (Subgroup.mem_map_iff_mem (f := c.toMonoidHom) c.injective).mp hstep
    have hmem : c (c.symm g') ∈ Q' := (hmemQ' (c.symm g')).mpr hg
    simpa using hmem
  · haveI : IsSimpleGroup ↥⁅Q, Q⁆ := h.derived_simple
    rw [← hD]
    exact MulEquiv.isSimpleGroup
      (Subgroup.equivMapOfInjective ⁅Q, Q⁆ c.toMonoidHom c.injective).symm
  · rw [← hD,
      ← Nat.card_congr
        (Subgroup.equivMapOfInjective ⁅Q, Q⁆ c.toMonoidHom c.injective).toEquiv]
    exact h.card_derived
  · have hc : (Subgroup.centralizer
          ((⁅Q, Q⁆ : Subgroup (MulAut A)) : Set (MulAut A))).map c.toMonoidHom
        = Subgroup.centralizer
          ((⁅Q', Q'⁆ : Subgroup (MulAut A')) : Set (MulAut A')) := by
      rw [map_centralizer_mulEquiv, hD]
    have hEq : Q' ⊓ Subgroup.centralizer
          ((⁅Q', Q'⁆ : Subgroup (MulAut A')) : Set (MulAut A'))
        = (Q ⊓ Subgroup.centralizer
          ((⁅Q, Q⁆ : Subgroup (MulAut A)) : Set (MulAut A))).map c.toMonoidHom := by
      rw [Subgroup.map_inf _ _ c.toMonoidHom c.injective, ← hQ', hc]
    rw [hEq, h.centralizer_derived, Subgroup.map_bot]
  · intro U' hU'
    set U : Subgroup A := U'.comap e.toMonoidHom
    have hU : ∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ U, g u ∈ U := by
      intro g hg u hu
      have hch : c g ∈ ⁅Q', Q'⁆ := (hmemD g).mpr hg
      have heu : e u ∈ U' := Subgroup.mem_comap.mp hu
      have hmem : c g (e u) ∈ U' := hU' (c g) hch (e u) heu
      rw [Subgroup.mem_comap]
      simpa [c, mulAut_congr_apply] using hmem
    have hmap : U.map e.toMonoidHom = U' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective U'
    rcases h.irreducible_derived U hU with hbot | htop
    · left
      rw [← hmap, hbot, Subgroup.map_bot]
    · right
      rw [← hmap, htop, Subgroup.map_top,
        MonoidHom.range_eq_top_of_surjective e.toMonoidHom e.surjective]
  · intro f' hf'
    set f : A →* A := e.symm.toMonoidHom.comp (f'.comp e.toMonoidHom)
    have hf : ∀ g ∈ ⁅Q, Q⁆, ∀ a, f (g a) = g (f a) := by
      intro g hg a
      have hch : c g ∈ ⁅Q', Q'⁆ := (hmemD g).mpr hg
      have h := hf' (c g) hch (e a)
      dsimp only [f]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      have h1 : e (g a) = c g (e a) := by simp [c, mulAut_congr_apply]
      have h2 : e (g (e.symm (f' (e a)))) = c g (f' (e a)) := by
        simp [c, mulAut_congr_apply]
      rw [h1, h, ← h2, e.symm_apply_apply]
    rcases h.endo_derived f hf with hf1 | hfid
    · left
      ext a'
      have h := DFunLike.congr_fun hf1 (e.symm a')
      dsimp only [f] at h
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
      have h' : e.symm (f' a') = 1 := by simpa using h
      simpa using congrArg e h'
    · right
      ext a'
      have h := DFunLike.congr_fun hfid (e.symm a')
      dsimp only [f] at h
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
      have h' : f' a' = a' := by
        have := congrArg e h
        simpa using this
      simpa using h'
  · intro Y' hY'Q' hY'elem hY'ne
    set Y : Subgroup (MulAut A) := Y'.map (MulAut.congr e).symm.toMonoidHom
    have hYQ : Y ≤ Q := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨y', hy', rfl⟩
      exact Subgroup.mem_map_equiv.mp (hY'Q' hy')
    haveI hYel : IsElementaryAbelian 2 Y :=
      IsElementaryAbelian.of_mulEquiv
        (Subgroup.equivMapOfInjective Y' (MulAut.congr e).symm.toMonoidHom
          (MulAut.congr e).symm.injective) hY'elem
    have hYne : Y ≠ ⊥ := by
      intro hbot
      apply hY'ne
      have hmap : Y.map (MulAut.congr e).toMonoidHom = Y' := map_map_symm (MulAut.congr e) Y'
      rw [← hmap, hbot, Subgroup.map_bot]
    have hmain := h.noOffenders Y hYQ hYel hYne
    have hcardY' : Nat.card ↥Y' = Nat.card Y :=
      Nat.card_congr (Subgroup.equivMapOfInjective Y' (MulAut.congr e).symm.toMonoidHom
        (MulAut.congr e).symm.injective).toEquiv
    have hfix : Nat.card {a : A // ∀ y ∈ Y, y a = a}
        = Nat.card {a' : A' // ∀ y ∈ Y', y a' = a'} := by
      rw [show Y = Y'.map (MulAut.congr e).symm.toMonoidHom from rfl]
      exact natCard_fixedPoints_map_congr e Y'
    rw [← hcardY', hfix] at hmain
    exact hmain
  · intro β' hlin hrin hinv
    set β : A → A → ZMod 2 := fun a b => β' (e a) (e b)
    have hβ : β = 0 := h.noBilin β ?_ ?_ ?_
    · ext a' b'
      have h := congrFun (congrFun hβ (e.symm a')) (e.symm b')
      simpa [β] using h
    · intro a b c
      dsimp only [β]
      rw [map_mul, hlin]
    · intro a b c
      dsimp only [β]
      rw [map_mul, hrin]
    · intro g hg a b
      have hch : c g ∈ Q' := (hmemQ' g).mpr hg
      dsimp only [β]
      have h1 : e (g a) = c g (e a) := by simp [c, mulAut_congr_apply]
      have h2 : e (g b) = c g (e b) := by simp [c, mulAut_congr_apply]
      rw [h1, h2]
      exact hinv (c g) hch (e a) (e b)
  · intro γ' hγadd hγcoc
    let qiso : ↥Q ≃* ↥Q' := Subgroup.equivMapOfInjective Q c.toMonoidHom c.injective
    let γ : ↥Q → A → ZMod 2 := fun g a => γ' (qiso g) (e a)
    have hγadd' : ∀ g a b, γ g (a * b) = γ g a + γ g b := by
      intro g a b
      show γ' (qiso g) (e (a * b)) = γ' (qiso g) (e a) + γ' (qiso g) (e b)
      rw [map_mul, hγadd]
    have hγcoc' : ∀ g h a, γ (g * h) a = γ g a + γ h ((g : MulAut A)⁻¹ a) := by
      intro g h a
      have hqg : ((qiso g : ↥Q') : MulAut A') = c (g : MulAut A) := rfl
      have h1 : ((qiso g : ↥Q') : MulAut A')⁻¹ (e a) = e ((g : MulAut A)⁻¹ a) := by
        rw [hqg, ← map_inv]
        simp [c, mulAut_congr_apply]
      show γ' (qiso (g * h)) (e a)
        = γ' (qiso g) (e a) + γ' (qiso h) (e ((g : MulAut A)⁻¹ a))
      rw [map_mul, hγcoc, h1]
    rcases h.dual_cocycle γ hγadd' hγcoc' with ⟨f, hfadd, hfcoc⟩
    refine ⟨fun a' => f (e.symm a'), ?_, ?_⟩
    · intro a' b'
      show f (e.symm (a' * b')) = f (e.symm a') + f (e.symm b')
      rw [map_mul, hfadd]
    · intro g' a'
      set g : ↥Q := qiso.symm g'
      have hqg : qiso g = g' := MulEquiv.apply_symm_apply qiso g'
      have hqgM : ((qiso g : ↥Q') : MulAut A') = (g' : MulAut A') := by rw [hqg]
      have hqc : ((qiso g : ↥Q') : MulAut A') = c (g : MulAut A) := rfl
      have harg : e.symm ((g' : MulAut A')⁻¹ a') = ((g : ↥Q) : MulAut A)⁻¹ (e.symm a') := by
        rw [← hqgM, hqc, ← map_inv]
        simp [c, mulAut_congr_apply]
      have h1 : γ' g' a' = γ g (e.symm a') := by
        show γ' g' a' = γ' (qiso g) (e (e.symm a'))
        rw [hqg]
        simp
      rw [h1, hfcoc]
      change f ((g : MulAut A)⁻¹ (e.symm a')) + f (e.symm a')
        = f (e.symm ((g' : MulAut A')⁻¹ a')) + f (e.symm a')
      rw [harg]
  · intro β' hmul hright halt hinv
    let β : A → A → A := fun a b => e.symm (β' (e a) (e b))
    have hβ : ∀ a b, β a b = 1 := h.noWedge β ?_ ?_ ?_ ?_
    · intro a' b'
      have h := hβ (e.symm a') (e.symm b')
      have h' := congrArg e h
      simpa [β] using h'
    · intro a b c
      show e.symm (β' (e (a * b)) (e c))
        = e.symm (β' (e a) (e c)) * e.symm (β' (e b) (e c))
      rw [map_mul e a b, hmul (e a) (e b) (e c), map_mul]
    · intro a b c
      show e.symm (β' (e a) (e (b * c)))
        = e.symm (β' (e a) (e b)) * e.symm (β' (e a) (e c))
      rw [map_mul e b c, hright (e a) (e b) (e c), map_mul]
    · intro a
      show e.symm (β' (e a) (e a)) = 1
      rw [halt (e a), map_one]
    · intro g hg a b
      have hch : c g ∈ Q' := (hmemQ' g).mpr hg
      have h1 : e (g a) = c g (e a) := by simp [c, mulAut_congr_apply]
      have h2 : e (g b) = c g (e b) := by simp [c, mulAut_congr_apply]
      show e.symm (β' (e (g a)) (e (g b))) = g (e.symm (β' (e a) (e b)))
      rw [h1, h2, hinv (c g) hch (e a) (e b)]
      simp [c, mulAut_congr_apply]
  · intro V _ ρ' ι' hι' hρ' hsq hexp hlifts
    let qiso : ↥Q ≃* ↥Q' := Subgroup.equivMapOfInjective Q c.toMonoidHom c.injective
    let ρ : ↥Q →* MulAut V := ρ'.comp qiso.toMonoidHom
    let ι : A →* V := ι'.comp e.toMonoidHom
    refine h.noZ4 V ρ ι ?_ ?_ ?_ ?_ ?_
    · intro a b hab
      apply e.injective
      apply hι'
      simpa [ι] using hab
    · intro g a
      have hqg : ((qiso g : ↥Q') : MulAut A') = c (g : MulAut A) := rfl
      have h1 : ((qiso g : ↥Q') : MulAut A') (e a) = e ((g : MulAut A) a) := by
        rw [hqg]
        simp [c, mulAut_congr_apply]
      have h := hρ' (qiso g) (e a)
      dsimp only [ρ, ι]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [h, h1]
    · intro v
      obtain ⟨a', ha'⟩ := hsq v
      exact ⟨e.symm a', by simpa [ι] using ha'⟩
    · intro v hv
      obtain ⟨a', ha'⟩ := hexp v hv
      exact ⟨e.symm a', by simpa [ι] using ha'⟩
    · intro a
      obtain ⟨v, hv⟩ := hlifts (e a)
      exact ⟨v, by simpa [ι] using hv⟩
  · intro Γ' hΓadd hΓcoc hfix
    let qiso : ↥Q ≃* ↥Q' := Subgroup.equivMapOfInjective Q c.toMonoidHom c.injective
    let Γ : ↥Q → A → A := fun g a => e.symm (Γ' (qiso g) (e a))
    have hΓadd' : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b := by
      intro g a b
      show e.symm (Γ' (qiso g) (e (a * b)))
        = e.symm (Γ' (qiso g) (e a)) * e.symm (Γ' (qiso g) (e b))
      rw [map_mul e a b, hΓadd, map_mul]
    have hΓcoc' : ∀ g h a, Γ (g * h) a
        = Γ g a * (g : MulAut A) (Γ h ((g : MulAut A)⁻¹ a)) := by
      intro g h a
      have hqg : ((qiso g : ↥Q') : MulAut A') = c (g : MulAut A) := rfl
      have h1 : ((qiso g : ↥Q') : MulAut A')⁻¹ (e a) = e ((g : MulAut A)⁻¹ a) := by
        rw [hqg, ← map_inv]
        simp [c, mulAut_congr_apply]
      have hstep : Γ' (qiso (g * h)) (e a)
          = Γ' (qiso g) (e a)
            * ((qiso g : ↥Q') : MulAut A')
              (Γ' (qiso h) (((qiso g : ↥Q') : MulAut A')⁻¹ (e a))) := by
        rw [map_mul qiso g h]
        exact hΓcoc (qiso g) (qiso h) (e a)
      show e.symm (Γ' (qiso (g * h)) (e a))
        = e.symm (Γ' (qiso g) (e a))
          * (g : MulAut A) (e.symm (Γ' (qiso h) (e ((g : MulAut A)⁻¹ a))))
      rw [hstep, map_mul, h1]
      congr 1
      rw [hqg]
      simp [c, mulAut_congr_apply]
    have hfix' : ∃ u : A, ∀ g : ↥Q, (g : MulAut A) t = t → Γ g t = u * (g : MulAut A) u := by
      obtain ⟨u', hu'⟩ := hfix
      refine ⟨e.symm u', ?_⟩
      intro g hg
      have hq : ((qiso g : ↥Q') : MulAut A') (e t) = e t := by
        have hqg : ((qiso g : ↥Q') : MulAut A') = c (g : MulAut A) := rfl
        rw [hqg]
        simp [c, mulAut_congr_apply, hg]
      have h := hu' (qiso g) hq
      show e.symm (Γ' (qiso g) (e t))
        = e.symm u' * (g : MulAut A) (e.symm u')
      rw [h, map_mul]
      congr 1
      rw [show ((qiso g : ↥Q') : MulAut A') = c (g : MulAut A) from rfl]
      simp [c, mulAut_congr_apply]
    obtain ⟨X, hX⟩ := h.split_of_fixed Γ hΓadd' hΓcoc' hfix'
    let X' : A' →* A' := e.toMonoidHom.comp (X.comp e.symm.toMonoidHom)
    refine ⟨X', ?_⟩
    intro g' a'
    set g : ↥Q := qiso.symm g'
    have hqg : qiso g = g' := MulEquiv.apply_symm_apply qiso g'
    have hqgM : ((qiso g : ↥Q') : MulAut A') = (g' : MulAut A') := by rw [hqg]
    have hqc : ((qiso g : ↥Q') : MulAut A') = c (g : MulAut A) := rfl
    have h1 : ((qiso g : ↥Q') : MulAut A')⁻¹ a' = e ((g : MulAut A)⁻¹ (e.symm a')) := by
      rw [hqc, ← map_inv]
      simp [c, mulAut_congr_apply]
    have hΓ : Γ' g' a' = e (Γ g (e.symm a')) := by
      show Γ' g' a' = e (e.symm (Γ' (qiso g) (e (e.symm a'))))
      rw [hqg]
      simp
    have harg : e.symm ((g' : MulAut A')⁻¹ a') = ((g : ↥Q) : MulAut A)⁻¹ (e.symm a') := by
      rw [← hqgM, hqc, ← map_inv]
      simp [c, mulAut_congr_apply]
    rw [hΓ, hX]
    dsimp only [X']
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [map_mul, harg, ← hqgM, hqc]
    simp [c, mulAut_congr_apply]

private theorem mem_normalizer_iff_of_mulEquiv {G G' : Type*} [Group G] [Group G']
    {L A : Subgroup G} {A' : Subgroup G'} (hAL : A ≤ L) (φ : ↥L ≃* G')
    (hA : ∀ x : ↥L, (x : G) ∈ A ↔ φ x ∈ A') (x : ↥L) :
    (x : G) ∈ normalizer (A : Set G) ↔ φ x ∈ normalizer (A' : Set G') := by
  constructor
  · intro hx
    rw [Subgroup.mem_set_normalizer_iff] at hx ⊢
    intro n'
    set y : ↥L := φ.symm n'
    have hy : φ y = n' := by simp [y]
    have h1 : n' ∈ A' ↔ (y : G) ∈ A := by
      rw [← hy, hA y]
    have h3 : φ (x * y * x⁻¹) = φ x * n' * (φ x)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hy]
    calc n' ∈ A' ↔ (y : G) ∈ A := h1
      _ ↔ (x : G) * (y : G) * (x : G)⁻¹ ∈ A := hx _
      _ ↔ φ (x * y * x⁻¹) ∈ A' := hA (x * y * x⁻¹)
      _ ↔ φ x * n' * (φ x)⁻¹ ∈ A' := by rw [h3]
  · intro hx
    rw [Subgroup.mem_set_normalizer_iff] at hx ⊢
    intro n
    constructor
    · intro hn
      have hnL : n ∈ L := hAL hn
      have hxnL : x * n * x⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem x.2 hnL) (L.inv_mem x.2)
      have hφ : φ ⟨x * n * x⁻¹, hxnL⟩ = φ x * φ ⟨n, hnL⟩ * (φ x)⁻¹ := by
        rw [show (⟨x * n * x⁻¹, hxnL⟩ : ↥L) = x * ⟨n, hnL⟩ * x⁻¹ from Subtype.ext rfl,
          map_mul, map_mul, map_inv]
      have hmem : φ x * φ ⟨n, hnL⟩ * (φ x)⁻¹ ∈ A' := (hx _).mp ((hA ⟨n, hnL⟩).mp hn)
      exact (hA ⟨x * n * x⁻¹, hxnL⟩).mpr (by rwa [hφ])
    · intro hn
      have hnL : n ∈ L := by
        have h1 : x⁻¹ * (x * n * x⁻¹) * x ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem x.2) (hAL hn)) x.2
        simpa [mul_assoc] using h1
      have hφ : φ ⟨x * n * x⁻¹, hAL hn⟩ = φ x * φ ⟨n, hnL⟩ * (φ x)⁻¹ := by
        rw [show (⟨x * n * x⁻¹, hAL hn⟩ : ↥L) = x * ⟨n, hnL⟩ * x⁻¹ from Subtype.ext rfl,
          map_mul, map_mul, map_inv]
      have hmem' : φ ⟨x * n * x⁻¹, hAL hn⟩ ∈ A' := (hA _).mp hn
      have hmem : φ x * φ ⟨n, hnL⟩ * (φ x)⁻¹ ∈ A' := by rwa [hφ] at hmem'
      exact (hA ⟨n, hnL⟩).mpr ((hx _).mpr hmem)

private theorem mulAut_congr_conjN {G G' : Type*} [Group G] [Group G']
    {L A : Subgroup G} {A' : Subgroup G'} (hAL : A ≤ L) (φ : ↥L ≃* G')
    (hA : ∀ x : ↥L, (x : G) ∈ A ↔ φ x ∈ A')
    (eA : ↥A ≃* ↥A') (heA : ∀ a : ↥A, ((eA a : ↥A') : G') = φ ⟨a.1, hAL a.2⟩)
    (x : ↥(L ⊓ normalizer (A : Set G)))
    (y : ↥(⊤ ⊓ normalizer (A' : Set G'))) (hy : (y : G') = φ ⟨x.1, x.2.1⟩) :
    MulAut.congr eA (conjN L A x) = conjN ⊤ A' y := by
  ext a'
  have hL : ((MulAut.congr eA (conjN L A x)) a' : G')
      = φ ⟨x.1, x.2.1⟩ * (a' : G') * (φ ⟨x.1, x.2.1⟩)⁻¹ := by
    rw [mulAut_congr_apply, heA (conjN L A x (eA.symm a'))]
    have hsymm : φ ⟨(eA.symm a').1, hAL (eA.symm a').2⟩ = (a' : G') := by
      have hh := heA (eA.symm a')
      rw [eA.apply_symm_apply] at hh
      exact hh.symm
    have hz : (⟨conjN L A x (eA.symm a'), hAL (conjN L A x (eA.symm a')).2⟩ : ↥L)
        = ⟨x.1, x.2.1⟩ * ⟨(eA.symm a').1, hAL (eA.symm a').2⟩
          * ⟨x.1, x.2.1⟩⁻¹ := by
      apply Subtype.ext
      simp [conjN_apply]
    rw [hz, map_mul, map_mul, map_inv, hsymm]
  have hR : ((conjN ⊤ A' y) a' : G') = (y : G') * (a' : G') * (y : G')⁻¹ := by
    rw [conjN_apply]
    simp
  rw [hL, hR, hy]

private theorem autImage_eq_map {G G' : Type*} [Group G] [Group G']
    {L A : Subgroup G} {A' : Subgroup G'} (hAL : A ≤ L) (φ : ↥L ≃* G')
    (hA : ∀ x : ↥L, (x : G) ∈ A ↔ φ x ∈ A')
    (eA : ↥A ≃* ↥A') (heA : ∀ a : ↥A, ((eA a : ↥A') : G') = φ ⟨a.1, hAL a.2⟩) :
    autImage ⊤ A' = (autImage L A).map (MulAut.congr eA).toMonoidHom := by
  rw [autImage, autImage, MonoidHom.map_range]
  apply le_antisymm
  · rintro g' ⟨y, rfl⟩
    set xL : ↥L := φ.symm (y : G')
    have hxN : (xL : G) ∈ normalizer (A : Set G) := by
      refine (mem_normalizer_iff_of_mulEquiv hAL φ hA xL).mpr ?_
      simpa [xL] using y.2.2
    refine ⟨⟨xL, ⟨xL.2, hxN⟩⟩, ?_⟩
    exact mulAut_congr_conjN hAL φ hA eA heA ⟨xL, ⟨xL.2, hxN⟩⟩ y (by simp [xL])
  · rintro g' ⟨x, rfl⟩
    have hxN : φ ⟨x.1, x.2.1⟩ ∈ normalizer (A' : Set G') :=
      (mem_normalizer_iff_of_mulEquiv hAL φ hA ⟨x.1, x.2.1⟩).mp x.2.2
    let y : ↥(⊤ ⊓ normalizer (A' : Set G')) :=
      ⟨φ ⟨x.1, x.2.1⟩, ⟨Subgroup.mem_top _, hxN⟩⟩
    have hy : ((y : ↥(⊤ ⊓ normalizer (A' : Set G'))) : G') = φ ⟨x.1, x.2.1⟩ := rfl
    exact ⟨y, (mulAut_congr_conjN hAL φ hA eA heA x y hy).symm⟩

private def fixedCentralizerEquiv {G G' : Type*} [Group G] [Group G']
    {L : Subgroup G} {t : G} {t' : G'} (φ : ↥L ≃* G') (htL : t ∈ L)
    (ht : φ ⟨t, htL⟩ = t') :
    ↥(L ⊓ centralizer ({t} : Set G)) ≃* ↥(⊤ ⊓ centralizer ({t'} : Set G')) where
  toFun x := by
    have hxL : (x.1 : G) ∈ L := (Subgroup.mem_inf.mp x.2).1
    have hxC : (x.1 : G) ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.mp x.2).2
    refine ⟨φ ⟨x.1, hxL⟩, Subgroup.mem_top _, ?_⟩
    change φ ⟨x.1, hxL⟩ ∈ Subgroup.centralizer ({t'} : Set G')
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxt : (x.1 : G) * t = t * (x.1 : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC
    calc
      φ ⟨x.1, hxL⟩ * t' = φ ⟨x.1, hxL⟩ * φ ⟨t, htL⟩ := by rw [← ht]
      _ = φ (⟨x.1, hxL⟩ * ⟨t, htL⟩) := by rw [← map_mul]
      _ = φ (⟨t, htL⟩ * ⟨x.1, hxL⟩) := congrArg φ (Subtype.ext hxt)
      _ = φ ⟨t, htL⟩ * φ ⟨x.1, hxL⟩ := by rw [map_mul]
      _ = t' * φ ⟨x.1, hxL⟩ := by rw [ht]
  invFun y := by
    have hyC : ((y : G')) ∈ centralizer ({t'} : Set G') := (Subgroup.mem_inf.mp y.2).2
    set z : ↥L := φ.symm (y : G')
    refine ⟨(z : G), ⟨z.2, ?_⟩⟩
    change (z : G) ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy : (y : G') * t' = t' * (y : G') :=
      Subgroup.mem_centralizer_singleton_iff.mp hyC
    have h := congrArg φ.symm hy
    simp only [map_mul] at h
    rw [show φ.symm t' = ⟨t, htL⟩ from by rw [← ht, MulEquiv.symm_apply_apply]] at h
    simpa using congrArg (fun w : ↥L => (w : G)) h
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    have hxL : (x.1 : G) ∈ L := (Subgroup.mem_inf.mp x.2).1
    have hyL : (y.1 : G) ∈ L := (Subgroup.mem_inf.mp y.2).1
    simpa using map_mul φ ⟨x.1, hxL⟩ ⟨y.1, hyL⟩)

theorem JcFacts.of_mulEquiv {G G' : Type*} [Group G] [Group G'] {L A T : Subgroup G} {t : G}
    {A' T' : Subgroup G'} {t' : G'} (φ : ↥L ≃* G') (hAL : A ≤ L) (hTL : T ≤ L) (htL : t ∈ L)
    (hA : ∀ x : ↥L, (x : G) ∈ A ↔ φ x ∈ A') (hT : ∀ x : ↥L, (x : G) ∈ T ↔ φ x ∈ T')
    (ht : φ ⟨t, htL⟩ = t') (h : JcFacts (⊤ : Subgroup G') A' T' t') : JcFacts L A T t := by
  have ht_mem : t ∈ A := by
    refine (hA ⟨t, htL⟩).mpr ?_
    have hm := h.t_mem
    rwa [← ht] at hm
  let eA : ↥A ≃* ↥A' :=
    { toFun := fun a => ⟨φ ⟨a.1, hAL a.2⟩, (hA ⟨a.1, hAL a.2⟩).mp a.2⟩
      invFun := fun a' => ⟨(φ.symm a'.1).1, (hA (φ.symm a'.1)).mpr (by simpa using a'.2)⟩
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun a' => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simpa using map_mul φ ⟨a.1, hAL a.2⟩ ⟨b.1, hAL b.2⟩) }
  have heA : ∀ a : ↥A, ((eA a : ↥A') : G') = φ ⟨a.1, hAL a.2⟩ := fun a => rfl
  haveI hAe : IsElementaryAbelian 2 ↥A := by
    exact IsElementaryAbelian.of_mulEquiv eA.symm h.module.elemAb
  refine
    { le := hAL
      t_mem := ht_mem
      T_le := ?_
      centralizer_eq := ?_
      module := ?_
      perfectE := ?_
      outE := ?_ }
  · intro x hxT
    exact (mem_normalizer_iff_of_mulEquiv hAL φ hA ⟨x, hTL hxT⟩).mpr
      (h.T_le ((hT ⟨x, hTL hxT⟩).mp hxT))
  · apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      have hxL : x ∈ L := hx.1
      have hxC : x ∈ centralizer (A : Set G) := hx.2
      have hφC : φ ⟨x, hxL⟩ ∈ centralizer (A' : Set G') := by
        rw [Subgroup.mem_centralizer_iff] at hxC ⊢
        intro a' ha'
        set a : ↥L := φ.symm a'
        have haA : (a : G) ∈ A := by
          rw [hA a]
          simpa [a]
        have hφa : φ a = a' := by simp [a]
        have hsub : a * ⟨x, hxL⟩ = ⟨x, hxL⟩ * a := Subtype.ext (hxC (a : G) haA)
        have hcomm := congrArg φ hsub
        simpa [hφa] using hcomm
      have hmem : φ ⟨x, hxL⟩ ∈ (⊤ ⊓ centralizer (A' : Set G')) :=
        ⟨Subgroup.mem_top _, hφC⟩
      rw [h.centralizer_eq] at hmem
      exact (hA ⟨x, hxL⟩).mpr hmem
    · intro a ha
      rw [Subgroup.mem_inf]
      exact ⟨hAL ha, Subgroup.le_centralizer A ha⟩
  · have hmod : ModuleFacts (autImage ⊤ A') ⟨t', h.t_mem⟩ := h.module
    have himage : autImage ⊤ A' = (autImage L A).map (MulAut.congr eA).toMonoidHom :=
      autImage_eq_map hAL φ hA eA heA
    have hmap := ModuleFacts.map_mulEquiv hmod eA.symm
    have hsub : (autImage ⊤ A').map (MulAut.congr eA.symm).toMonoidHom = autImage L A := by
      have h := (Subgroup.map_symm_eq_iff_map_eq (H := autImage ⊤ A') (K := autImage L A)
        (e := MulAut.congr eA)).mpr himage.symm
      simpa [mulAut_congr_symm] using h
    have hpt : eA ⟨t, ht_mem⟩ = ⟨t', h.t_mem⟩ := by
      apply Subtype.ext
      rw [heA]
      simpa using ht
    have hpt' : eA.symm ⟨t', h.t_mem⟩ = ⟨t, ht_mem⟩ := by
      rw [← hpt, eA.symm_apply_apply]
    rw [hsub, hpt'] at hmap
    exact hmap
  · let E : Subgroup G := L ⊓ centralizer ({t} : Set G)
    let E' : Subgroup G' := ⊤ ⊓ centralizer ({t'} : Set G')
    let φE : ↥E ≃* ↥E' := fixedCentralizerEquiv φ htL ht
    haveI : Group.IsPerfect ↥E' := ⟨h.perfectE⟩
    haveI : Group.IsPerfect ↥E :=
      Group.IsPerfect.ofSurjective (f := φE.symm.toMonoidHom) φE.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  · let E : Subgroup G := L ⊓ centralizer ({t} : Set G)
    let E' : Subgroup G' := ⊤ ⊓ centralizer ({t'} : Set G')
    let φE : ↥E ≃* ↥E' := fixedCentralizerEquiv φ htL ht
    intro α
    obtain ⟨e', he'⟩ := h.outE (MulAut.congr φE α)
    refine ⟨φE.symm e', ?_⟩
    calc α = (MulAut.congr φE).symm ((MulAut.congr φE) α) :=
          (MulEquiv.symm_apply_apply (MulAut.congr φE) α).symm
      _ = (MulAut.congr φE).symm (MulAut.conj e') := by rw [he']
      _ = MulAut.conj (φE.symm e') := by rw [mulAut_congr_symm, mulAut_congr_conj]

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
