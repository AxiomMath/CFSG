module

public import CFSG.Fischer.Classification.Uniqueness.Star
public import CFSG.Fischer.Uniq.Cover

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

section Fib

variable {P : Type} {M : LocalModel P}

theorem muSet_eq_of_muImg_eq {d : X} (L : LocalPoints M E d) {c c' : X}
    (h : L.muImg c = L.muImg c') : muSet E d c = muSet E d c' := by
  ext s
  constructor
  · intro hs
    have := (L.χ_mem_muImg_iff ⟨s, hs.1⟩).2 hs
    rw [h] at this
    exact (L.χ_mem_muImg_iff ⟨s, hs.1⟩).1 this
  · intro hs
    have := (L.χ_mem_muImg_iff ⟨s, hs.1⟩).2 hs
    rw [← h] at this
    exact (L.χ_mem_muImg_iff ⟨s, hs.1⟩).1 this

theorem Pair.eq_or_eq_of_muSet_eq (hT : TripleProperty E) {d c c' : X} (hd : d ∈ E)
    (hc : c ∈ farSet E d) (hc' : c' ∈ farSet E d) (h : muSet E d c = muSet E d c') :
    c' = c ∨ c' = d * c * d := by
  have hy : c' ∈ ySet E d c := ⟨hc'.1, fun s hs => by rw [h] at hs; exact hs.2⟩
  rcases hT d c hd hc.1 (fun e => hc.2.1 e.symm) hy with h1 | h1 | h1
  · exact (hc'.2.1 (by rw [h1])).elim
  · exact Or.inl h1
  · exact Or.inr h1

theorem fib_of_triple (hT : TripleProperty E) {d : X} (hd : d ∈ E) (L : LocalPoints M E d) :
    ∀ c ∈ farSet E d, ∀ c' ∈ farSet E d, L.muImg c = L.muImg c' → c' = c ∨ c' = d * c * d :=
  fun _ hc _ hc' h => Pair.eq_or_eq_of_muSet_eq hT hd hc hc' (muSet_eq_of_muImg_eq L h)

theorem Pair.conj_nu_eq (hP : Pair X E) {d : X} (hd : d ∈ E) (c f : X) :
    d * (d * c * f * c * d) * d = c * f * c := by
  calc d * (d * c * f * c * d) * d = (d * d) * c * f * c * (d * d) := by group
    _ = c * f * c := by rw [Pair.mul_self hP hd, one_mul, mul_one]

variable (hP : Pair X E) {d : X} (hd : d ∈ E) (L : LocalPoints M E d)
  (hfib : ∀ c ∈ farSet E d, ∀ c' ∈ farSet E d, L.muImg c = L.muImg c' → c' = c ∨ c' = d * c * d)
include hP hd hfib

theorem injOn_of_fib : ∀ O ∈ L.muImg '' farSet E d, Set.InjOn (fun f => M.tv f '' O) Oᶜ := by
  rintro _ ⟨c, hc, rfl⟩ p hp p' hp' h
  have hf : (L.χ.symm p : X) ∉ muSet E d c := by
    rw [← L.χ_mem_muImg_iff, Equiv.apply_symm_apply]; exact hp
  have hf' : (L.χ.symm p' : X) ∉ muSet E d c := by
    rw [← L.χ_mem_muImg_iff, Equiv.apply_symm_apply]; exact hp'
  have e1 := L.muImg_nu hP hd hc.1 hc.2.1 _ hf
  have e2 := L.muImg_nu hP hd hc.1 hc.2.1 _ hf'
  rw [Equiv.apply_symm_apply] at e1 e2
  rcases hfib _ (nu_mem_farSet hP hd hc _ hf) _ (nu_mem_farSet hP hd hc _ hf')
      (by rw [e1, e2]; exact h) with h1 | h1
  · have := Subtype.ext (nu_injective d c h1)
    rwa [L.χ.symm.injective.eq_iff, eq_comm] at this
  · exfalso
    have hcomm := (Pair.nu_mem_localClass hP hd hc.1 hc.2.1 (L.χ.symm p').2).2.2
    rw [h1, Pair.conj_nu_eq hP hd] at hcomm
    have hcc := Pair.mul_self hP hc.1
    have hfc : (L.χ.symm p : X) * c = c * (L.χ.symm p : X) := by
      calc (L.χ.symm p : X) * c = c * (c * (L.χ.symm p : X) * c) := by
            rw [← mul_assoc, ← mul_assoc, hcc, one_mul]
        _ = c * (L.χ.symm p : X) * c * c := hcomm.symm
        _ = c * (L.χ.symm p : X) := by rw [mul_assoc (c * _), hcc, mul_one]
    refine hf ⟨(L.χ.symm p).2, (L.χ.symm p).2.1, fun e => hc.2.1 ?_, hfc⟩
    rw [← e]
    exact (L.χ.symm p).2.2.2

theorem ne_of_fib : ∀ O ∈ L.muImg '' farSet E d, ∀ p ∉ O, M.tv p '' O ≠ O := by
  rintro _ ⟨c, hc, rfl⟩ p hp h
  have hf : (L.χ.symm p : X) ∉ muSet E d c := by
    rw [← L.χ_mem_muImg_iff, Equiv.apply_symm_apply]; exact hp
  have e1 := L.muImg_nu hP hd hc.1 hc.2.1 _ hf
  rw [Equiv.apply_symm_apply, h] at e1
  have hl := Pair.nu_mem_localClass hP hd hc.1 hc.2.1 (L.χ.symm p).2
  rcases hfib _ hc _ (nu_mem_farSet hP hd hc _ hf) e1.symm with h1 | h1
  · exact hl.2.1 h1
  · have hcomm := hl.2.2
    rw [h1] at hcomm
    exact Pair.mul_mul_not_commute_right hP hd hc.1 (fun e => hc.2.1 e.symm) hcomm

end Fib

theorem coverHyp_starPoints (hP : Pair X E) (hT : TripleProperty E) {d : X} (hd : d ∈ E) :
    CoverHyp (starPoints hP d) ((starPoints hP d).muImg '' farSet E d) where
  mem c hc := ⟨c, hc, rfl⟩
  surj _ hO := hO
  inj := injOn_of_fib hP hd _ (fib_of_triple hT hd _)
  ne := ne_of_fib hP hd _ (fib_of_triple hT hd _)
  fib := fib_of_triple hT hd _

theorem Pair.muSet_nonempty_of_triple (hP : Pair X E) (hT : TripleProperty E) {d c : X}
    (hd : d ∈ E) (hne : (LocalClass E d).Nonempty) (hc : c ∈ E) (hcd : c * d ≠ d * c) :
    (muSet E d c).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  obtain ⟨f, hf⟩ := hne
  have hy : f ∈ ySet E d c := ⟨hf.1, by rw [h]; exact Set.empty_subset _⟩
  rcases hT d c hd hc (fun e => hcd e.symm) hy with h1 | h1 | h1
  · exact hf.2.1 h1
  · exact hcd (by rw [← h1]; exact hf.2.2)
  · exact Pair.mul_mul_not_commute_left hP hd (fun e => hcd e.symm) (by rw [← h1]; exact hf.2.2)

section StarEquiv

variable (hE : Pair X E) {d : X} {d' : Y} (φ : LocalClass E d ≃ LocalClass F d')
  (hcomm : ∀ f g : LocalClass E d, (f : X) * g = g * f ↔ (φ f : Y) * φ g = φ g * φ f)
  (htau : ∀ (f g : LocalClass E d) (h : (f : X) * g * f ∈ LocalClass E d),
    (φ ⟨_, h⟩ : Y) = φ f * φ g * φ f)

@[expose] def starEquivPoints : LocalPoints (starModel hE d) F d' where
  χ := φ.symm
  comm f g := by
    have := hcomm (φ.symm f) (φ.symm g)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm
  tau f g h := by
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    have := htau (φ.symm f) (φ.symm g)
      (Pair.mul_mul_mem_localClass_of_mem hE (φ.symm f).2 (φ.symm g).2)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm

theorem starEquivPoints_χ_symm (f : LocalClass E d) :
    (starEquivPoints hE φ hcomm htau).χ.symm f = φ f :=
  rfl

theorem mem_starEquivPoints_muImg {c' : Y} (p : LocalClass E d) :
    p ∈ (starEquivPoints hE φ hcomm htau).muImg c' ↔ (φ p : Y) ∈ LocalClass F c' := by
  rw [LocalPoints.mem_muImg, starEquivPoints_χ_symm]

theorem starEquivPoints_muImg_eq {c : X} {c' : Y}
    (h : muSet F d' c' = starMap φ (muSet E d c)) :
    (starEquivPoints hE φ hcomm htau).muImg c' = (starPoints hE d).muImg c := by
  ext p
  rw [mem_starEquivPoints_muImg, starPoints_muImg]
  change (φ p : Y) ∈ LocalClass F c' ↔ (p : X) ∈ LocalClass E c
  have h1 : (φ p : Y) ∈ LocalClass F c' ↔ (φ p : Y) ∈ muSet F d' c' :=
    ⟨fun h => ⟨(φ p).2, h⟩, fun h => h.2⟩
  have h2 : (p : X) ∈ LocalClass E c ↔ (p : X) ∈ muSet E d c :=
    ⟨fun h => ⟨p.2, h⟩, fun h => h.2⟩
  rw [h1, h2, h, mem_starMap_iff]

theorem coverHyp_starEquivPoints (hTE : TripleProperty E)
    (hTF : TripleProperty F) (hd : d ∈ E) (hd' : d' ∈ F)
    (hmuE : ∀ c ∈ E, c * d ≠ d * c → (muSet E d c).Nonempty)
    (hmuF : ∀ c ∈ F, c * d' ≠ d' * c → (muSet F d' c).Nonempty)
    (hfam : starMap φ '' muFamily E d = muFamily F d') :
    CoverHyp (starEquivPoints hE φ hcomm htau) ((starPoints hE d).muImg '' farSet E d) where
  mem c' hc' := by
    have : muSet F d' c' ∈ starMap φ '' muFamily E d := by
      rw [hfam]; exact muSet_mem_muFamily hc'.1 hc'.2.1
    obtain ⟨_, ⟨c, hc, hcd, rfl⟩, hO⟩ := this
    exact ⟨c, ⟨hc, hcd, hmuE c hc hcd⟩, (starEquivPoints_muImg_eq hE φ hcomm htau hO.symm).symm⟩
  surj O hO := by
    obtain ⟨c, hc, rfl⟩ := hO
    have : starMap φ (muSet E d c) ∈ muFamily F d' := by
      rw [← hfam]; exact ⟨_, muSet_mem_muFamily hc.1 hc.2.1, rfl⟩
    obtain ⟨c', hc', hcd', h⟩ := this
    exact ⟨c', ⟨hc', hcd', hmuF c' hc' hcd'⟩, starEquivPoints_muImg_eq hE φ hcomm htau h⟩
  inj := (coverHyp_starPoints hE hTE hd).inj
  ne := (coverHyp_starPoints hE hTE hd).ne
  fib := fib_of_triple hTF hd' _

end StarEquiv

section XiIso

theorem preimage_muSet (hP : Pair X E) (d c : X) :
    {p : LocalClass E d | (p : X) ∈ muSet E d c} = (starPoints hP d).muImg c := by
  rw [starPoints_muImg]
  ext p
  exact ⟨fun h => h.2, fun h => ⟨p.2, h⟩⟩

theorem image_preimage_of_subset {d : X} {S : Set X} (hS : S ⊆ LocalClass E d) :
    Subtype.val '' {p : LocalClass E d | (p : X) ∈ S} = S := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hx
    exact ⟨⟨x, hS hx⟩, hx, rfl⟩

theorem eq_of_preimage_eq {d : X} {S T : Set X} (hS : S ⊆ LocalClass E d)
    (hT : T ⊆ LocalClass E d)
    (h : {p : LocalClass E d | (p : X) ∈ S} = {p : LocalClass E d | (p : X) ∈ T}) : S = T := by
  rw [← image_preimage_of_subset hS, h, image_preimage_of_subset hT]

@[expose] def muFamilyEquiv (hP : Pair X E) {d : X}
    (hmu : ∀ c ∈ E, c * d ≠ d * c → (muSet E d c).Nonempty) :
    muFamily E d ≃ (starPoints hP d).muImg '' farSet E d where
  toFun O := ⟨{p : LocalClass E d | (p : X) ∈ (O : Set X)}, by
    obtain ⟨_, c, hc, hcd, rfl⟩ := O
    exact ⟨c, ⟨hc, hcd, hmu c hc hcd⟩, (preimage_muSet hP d c).symm⟩⟩
  invFun Q := ⟨Subtype.val '' (Q : Set (LocalClass E d)), by
    obtain ⟨_, c, hc, rfl⟩ := Q
    refine ⟨c, hc.1, hc.2.1, ?_⟩
    show muSet E d c = Subtype.val '' (starPoints hP d).muImg c
    rw [← preimage_muSet hP, image_preimage_of_subset (muSet_subset_localClass d c)]⟩
  left_inv O := Subtype.ext (image_preimage_of_subset (subset_localClass_of_mem_muFamily O.2))
  right_inv Q := Subtype.ext (Set.ext fun _ => Subtype.val_injective.mem_set_image)

theorem muFamilyEquiv_coe (hP : Pair X E) {d : X}
    (hmu : ∀ c ∈ E, c * d ≠ d * c → (muSet E d c).Nonempty) (O : muFamily E d) :
    (muFamilyEquiv hP hmu O : Set (LocalClass E d)) =
      {p : LocalClass E d | (p : X) ∈ (O : Set X)} :=
  rfl

theorem starModel_tv_image (hP : Pair X E) {d : X} (p : LocalClass E d) {S : Set X}
    (hS : S ⊆ LocalClass E d) :
    (starModel hP d).tv p '' {q : LocalClass E d | (q : X) ∈ S} =
      {q : LocalClass E d | (q : X) ∈ (fun s => (p : X) * s * p) '' S} := by
  ext q
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨s, hs, hsq⟩
    exact ⟨⟨s, hS hs⟩, hs, Subtype.ext hsq⟩

theorem image_mul_mul_subset (hP : Pair X E) {d p : X} (hp : p ∈ LocalClass E d) {S : Set X}
    (hS : S ⊆ LocalClass E d) : (fun s => p * s * p) '' S ⊆ LocalClass E d := by
  rintro _ ⟨s, hs, rfl⟩
  exact Pair.mul_mul_mem_localClass_of_mem hP hp (hS hs)

@[expose] def muGraphIso (hP : Pair X E) {d : X}
    (hmu : ∀ c ∈ E, c * d ≠ d * c → (muSet E d c).Nonempty) :
    muGraph E d ≃g (starModel hP d).xi ((starPoints hP d).muImg '' farSet E d) where
  toEquiv := muFamilyEquiv hP hmu
  map_rel_iff' {O Q} := by
    rw [LocalModel.xi_adj, Pair.muGraph_adj hP, muFamilyEquiv_coe, muFamilyEquiv_coe]
    have hO := subset_localClass_of_mem_muFamily O.2
    have hQ := subset_localClass_of_mem_muFamily Q.2
    refine and_congr (muFamilyEquiv hP hmu).injective.ne_iff ⟨?_, ?_⟩
    · rintro ⟨p, hp, h⟩
      refine ⟨p, p.2, hp, ?_⟩
      rw [starModel_tv_image hP p hO] at h
      exact eq_of_preimage_eq (image_mul_mul_subset hP p.2 hO) hQ h
    · rintro ⟨f, hf, hfO, h⟩
      refine ⟨⟨f, hf⟩, hfO, ?_⟩
      rw [starModel_tv_image hP _ hO]
      exact congrArg (fun S => {q : LocalClass E d | (q : X) ∈ S}) h

end XiIso

end CFSG.Fischer.Classification
