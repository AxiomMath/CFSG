module

public import CFSG.Fischer.Uniq.F22
public import CFSG.Fischer.Uniq.Connected
public import CFSG.Fischer.Uniq.Assemble
public import CFSG.Fischer.Uniq.YSize

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

theorem F22.nonempty_compGraphIso
    (hPF : PolarFacts) (hE : F22 X E) (hF : F22 Y F) {d : X}
    {d' : Y} (hd : d ∈ E) (hd' : d' ∈ F) : Nonempty (compGraph E d ≃g compGraph F d') := by
  have hlocE : ∀ f ∈ E, Nonempty (LocalPoints polarModel E f) :=
    fun f hf => F22.nonempty_localPoints hE hf
  have hlocF : ∀ f ∈ F, Nonempty (LocalPoints polarModel F f) :=
    fun f hf => F22.nonempty_localPoints hF hf
  obtain ⟨L, hL⟩ := exists_localPoints_hypOrbit_zero hPF hE.1 hlocE hd
  obtain ⟨L', hL'⟩ := exists_localPoints_hypOrbit_zero hPF hF.1 hlocF hd'
  have h := coverHyp_hypOrbit_zero hPF hE.1 hlocE hd L hL
  have h' := coverHyp_hypOrbit_zero hPF hF.1 hlocF hd' L' hL'
  obtain ⟨β, hβπ, hβadj⟩ := TwoCover.exists_iso xiRoot hPF.xi_D2 hPF.xi_MU hPF.xi_ED
    (coverOf hE.1 hd L h) (coverOf hF.1 hd' L' h')
  let βA : farSet E d ≃ farSet F d' := β
  have hπ : ∀ c, L'.muImg (βA c) = L.muImg c := fun c => congrArg Subtype.val (hβπ c)
  exact ⟨compGraphIso hd hd' L L' βA hπ hβadj⟩

section YSize

variable (hPF : PolarFacts) (hP : Pair X E) (hloc : ∀ f ∈ E, Nonempty (LocalPoints polarModel E f))
include hPF hP hloc

theorem Pair.not_commute_of_muSet_subset {a b y : X} (ha : a ∈ E) (hb : b ∈ E)
    (hab : a * b ≠ b * a) (hne : (muSet E a b).Nonempty) (hyE : y ∈ E)
    (hsub : muSet E a b ⊆ LocalClass E y) (hya : y ≠ a) : y * a ≠ a * y := by
  intro hya'
  obtain ⟨La⟩ := hloc a ha
  have hyl : y ∈ LocalClass E a := ⟨hyE, hya, hya'⟩
  have hO := Pair.isClosedHyperoval_muImg hPF hP ha hb (fun h => hab h.symm) La hloc
  have hOne : (La.muImg b).Nonempty := (La.muImg_nonempty_iff b).2 hne
  by_cases hp : La.χ ⟨y, hyl⟩ ∈ La.muImg b
  · have : y ∈ muSet E a b := (La.χ_mem_muImg_iff ⟨y, hyl⟩).1 hp
    exact (hsub this).2.1 rfl
  · obtain ⟨z, hz, hnp⟩ := hPF.exists_not_perp _ hO hOne _ hp
    have hsmu : (La.χ.symm z : X) ∈ muSet E a b := ⟨(La.χ.symm z).2, La.mem_muImg.1 hz⟩
    have hcomm := (hsub hsmu).2.2
    apply hnp
    have := (La.comm ⟨y, hyl⟩ (La.χ.symm z)).1 hcomm.symm
    rwa [Equiv.apply_symm_apply] at this

theorem Pair.ySet_subset_of_polar {e x : X} (he : e ∈ E) (hx : x ∈ E) (hex : e * x ≠ x * e)
    (hmu : (muSet E e x).Nonempty) : ySet E e x ⊆ {e, x, e * x * e} := by
  have := Pair.finite hP
  rintro y ⟨hyE, hS⟩
  by_cases hye : y = e
  · exact Or.inl hye
  by_cases hyx : y = x
  · exact Or.inr (Or.inl hyx)
  right; right
  have h1 := Pair.not_commute_of_muSet_subset hPF hP hloc he hx hex hmu hyE hS hye
  have hxfar : x ∈ farSet E e := ⟨hx, fun h => hex h.symm, hmu⟩
  have hsub : muSet E e x ⊆ muSet E e y := fun s hs => ⟨hs.1, hS hs⟩
  have hyfar : y ∈ farSet E e := ⟨hyE, h1, hmu.mono hsub⟩
  have heq : muSet E e x = muSet E e y := Set.eq_of_subset_of_ncard_le hsub
    (by rw [Pair.ncard_muSet_of_polar hPF hP hloc he hyfar,
      Pair.ncard_muSet_of_polar hPF hP hloc he hxfar]) (Set.toFinite _)
  obtain ⟨Le⟩ := hloc e he
  have himg : Le.muImg x = Le.muImg y := by
    ext p
    rw [← Equiv.apply_symm_apply Le.χ p, Le.χ_mem_muImg_iff, Le.χ_mem_muImg_iff, heq]
  rcases Le.muImg_fib hPF hP hloc he hxfar hyfar himg with h | h
  · exact absurd h hyx
  · exact h

end YSize

theorem F22.exists_mulEquiv
    (hPF : PolarFacts) (hE : F22 X E) (hF : F22 Y F)
    (hZE : Subgroup.center X = ⊥) (hZF : Subgroup.center Y = ⊥)
    (hSE : IsSimpleGroup (commutator X)) (hSF : IsSimpleGroup (commutator Y)) :
    ∃ φ : X ≃* Y, φ '' E = F := by
  have hlocE : ∀ f ∈ E, Nonempty (LocalPoints polarModel E f) :=
    fun f hf => F22.nonempty_localPoints hE hf
  have hlocF : ∀ f ∈ F, Nonempty (LocalPoints polarModel F f) :=
    fun f hf => F22.nonempty_localPoints hF hf
  have hmem : ∀ {Z : Type} [Group Z] {D : Set Z}, Pair Z D →
      (∀ f ∈ D, Nonempty (LocalPoints polarModel D f)) → ∃ d ∈ D, ∃ f, f ∈ LocalClass D d := by
    intro Z _ D hP hloc
    obtain ⟨e, he⟩ := hP.2.1
    have hd : e ∈ D := by rw [he]; exact IsConj.refl e
    obtain ⟨L⟩ := hloc e hd
    exact ⟨e, hd, L.χ.symm 0, (L.χ.symm 0).2⟩
  obtain ⟨d, hd, f, hf⟩ := hmem hE.1 hlocE
  obtain ⟨d', hd', f', hf'⟩ := hmem hF.1 hlocF
  have hconnE := Pair.connected_of_simple hE.1 hSE ⟨d, f, hd, hf.1, hf.2.1.symm, hf.2.2.symm⟩
  have hconnF := Pair.connected_of_simple hF.1 hSF ⟨d', f', hd', hf'.1, hf'.2.1.symm, hf'.2.2.symm⟩
  have huE : compSet E d = Set.univ :=
    compSet_eq_univ fun c hc hcd => Pair.muSet_nonempty hE.1 hconnE hd hc hcd
  have huF : compSet F d' = Set.univ :=
    compSet_eq_univ fun c hc hcd => Pair.muSet_nonempty hF.1 hconnF hd' hc hcd
  obtain ⟨ι⟩ := F22.nonempty_compGraphIso hPF hE hF hd hd'
  let β : commGraph E ≃g commGraph F :=
    (compGraphIsoTop huE).symm.trans (ι.trans (compGraphIsoTop huF))
  refine Pair.mulEquiv_of_graphIso hE.1 hF.1 hZE hZF β fun e x he hx hex => ?_
  exact Pair.ySet_subset_of_polar hPF hF.1 hlocF he hx hex
    (Pair.muSet_nonempty hF.1 hconnF he hx fun h => hex h.symm)

end CFSG.Fischer
