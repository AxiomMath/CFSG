module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Fischer.Classification.Uniqueness.Family

public section

namespace CFSG.Fischer.Classification.Unitary

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

@[expose] def TripleAt (E : Set X) (d : X) : Prop :=
  ∀ c : X, c ∈ E → d * c ≠ c * d → ySet E d c ⊆ {d, c, d * c * d}

section

variable {d : X}

theorem eq_or_eq_of_muSet_eq_of_tripleAt (hT : TripleAt E d) {c c' : X}
    (hc : c ∈ farSet E d) (hc' : c' ∈ farSet E d) (h : muSet E d c = muSet E d c') :
    c' = c ∨ c' = d * c * d := by
  have hy : c' ∈ ySet E d c := ⟨hc'.1, fun s hs => by rw [h] at hs; exact hs.2⟩
  rcases hT c hc.1 (fun e => hc.2.1 e.symm) hy with h1 | h1 | h1
  · exact (hc'.2.1 (by rw [h1])).elim
  · exact Or.inl h1
  · exact Or.inr h1

theorem fib_of_tripleAt {P : Type} {M : LocalModel P} (hT : TripleAt E d)
    (L : LocalPoints M E d) :
    ∀ c ∈ farSet E d, ∀ c' ∈ farSet E d, L.muImg c = L.muImg c' → c' = c ∨ c' = d * c * d :=
  fun _ hc _ hc' h => eq_or_eq_of_muSet_eq_of_tripleAt hT hc hc' (muSet_eq_of_muImg_eq L h)

theorem muSet_nonempty_of_tripleAt (hP : Pair X E) (hT : TripleAt E d) (hd : d ∈ E)
    (hne : (LocalClass E d).Nonempty) {c : X} (hc : c ∈ E) (hcd : c * d ≠ d * c) :
    (muSet E d c).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  obtain ⟨f, hf⟩ := hne
  have hy : f ∈ ySet E d c := ⟨hf.1, by rw [h]; exact Set.empty_subset _⟩
  rcases hT c hc (fun e => hcd e.symm) hy with h1 | h1 | h1
  · exact hf.2.1 h1
  · exact hcd (by rw [← h1]; exact hf.2.2)
  · exact Pair.mul_mul_not_commute_left hP hd (fun e => hcd e.symm) (by rw [← h1]; exact hf.2.2)

end

theorem Pair.exists_mulEquiv_of_starEquiv_left_tripleAt (hE : Pair X E) (hF : Pair Y F)
    (hZE : Subgroup.center X = ⊥) (hZF : Subgroup.center Y = ⊥)
    (hTE : TripleProperty E) {d : X} {d' : Y} (hTF : TripleAt F d') (hd : d ∈ E)
    (hd' : d' ∈ F) (hne : (LocalClass E d).Nonempty) (φ : LocalClass E d ≃ LocalClass F d')
    (hcomm : ∀ f g : LocalClass E d, (f : X) * g = g * f ↔ (φ f : Y) * φ g = φ g * φ f)
    (htau : ∀ (f g : LocalClass E d) (h : (f : X) * g * f ∈ LocalClass E d),
      (φ ⟨_, h⟩ : Y) = φ f * φ g * φ f)
    (hfam : starMap φ '' muFamily E d = muFamily F d')
    {r : muFamily E d} (hr : CoverRigid (muGraph E d) r) :
    ∃ ψ : X ≃* Y, ψ '' E = F ∧ ψ d = d' ∧ ∀ f : LocalClass E d, ψ f = φ f := by
  have hmuE : ∀ c ∈ E, c * d ≠ d * c → (muSet E d c).Nonempty :=
    fun c hc hcd => Pair.muSet_nonempty_of_triple hE hTE hd hne hc hcd
  have hne' : (LocalClass F d').Nonempty := by
    obtain ⟨f, hf⟩ := hne
    exact ⟨_, (φ ⟨f, hf⟩).2⟩
  have hmuF : ∀ c ∈ F, c * d' ≠ d' * c → (muSet F d' c).Nonempty :=
    fun c hc hcd => muSet_nonempty_of_tripleAt hF hTF hd' hne' hc hcd
  set L := starPoints hE d
  set L' := starEquivPoints hE φ hcomm htau
  have h := coverHyp_starPoints hE hTE hd
  have h' : CoverHyp L' (L.muImg '' farSet E d) :=
    { mem := fun c' hc' => by
        have : muSet F d' c' ∈ starMap φ '' muFamily E d := by
          rw [hfam]; exact muSet_mem_muFamily hc'.1 hc'.2.1
        obtain ⟨_, ⟨c, hc, hcd, rfl⟩, hO⟩ := this
        exact ⟨c, ⟨hc, hcd, hmuE c hc hcd⟩,
          (starEquivPoints_muImg_eq hE φ hcomm htau hO.symm).symm⟩
      surj := fun O hO => by
        obtain ⟨c, hc, rfl⟩ := hO
        have : starMap φ (muSet E d c) ∈ muFamily F d' := by
          rw [← hfam]; exact ⟨_, muSet_mem_muFamily hc.1 hc.2.1, rfl⟩
        obtain ⟨c', hc', hcd', h⟩ := this
        exact ⟨c', ⟨hc', hcd', hmuF c' hc' hcd'⟩, starEquivPoints_muImg_eq hE φ hcomm htau h⟩
      inj := h.inj
      ne := h.ne
      fib := fib_of_tripleAt hTF L' }
  have hr' := hr.map (muGraphIso hE hmuE)
  obtain ⟨β, hβπ, hβadj⟩ := TwoCover.exists_iso _ hr'.exists_adj_adj hr'.connected
    hr'.exists_adj_adj_adj (coverOf hE hd L h) (coverOf hF hd' L' h')
  let βA : farSet E d ≃ farSet F d' := β
  have hπ : ∀ c, L'.muImg (βA c) = L.muImg c := fun c => congrArg Subtype.val (hβπ c)
  have huE : compSet E d = Set.univ := compSet_eq_univ hmuE
  have huF : compSet F d' = Set.univ := compSet_eq_univ hmuF
  let B : commGraph E ≃g commGraph F := (compGraphIsoTop huE).symm.trans
    ((compGraphIso hd hd' L L' βA hπ hβadj).trans (compGraphIsoTop huF))
  have hB : ∀ (e : E) (he : e ∈ compSet E d),
      ((B e : F) : Y) = ((pieceMap hd' L L' βA ⟨e, he⟩ : compSet F d') : F) := fun _ _ => rfl
  obtain ⟨χ, hχ⟩ := exists_mulEquiv_of_tau_eq hF hE hZF hZE B.symm.toEquiv
    (Pair.tau_of_graphIso hF hE B.symm hTE)
  have hψ : ∀ e : E, χ.symm e = B.toEquiv e := fun e => by
    rw [MulEquiv.symm_apply_eq, hχ]
    simp
  refine ⟨χ.symm, image_eq_of_forall_eq B.toEquiv hψ, ?_, fun f => ?_⟩
  · have hd0 : (⟨d, hd⟩ : E) ∈ compSet E d := by rw [huE]; trivial
    rw [show d = ((⟨d, hd⟩ : E) : X) from rfl, hψ, RelIso.coe_fn_toEquiv, hB _ hd0]
    exact pieceMap_d hd hd' L L' βA rfl
  · have hf0 : (⟨f, f.2.1⟩ : E) ∈ compSet E d := by rw [huE]; trivial
    rw [show (f : X) = ((⟨f, f.2.1⟩ : E) : X) from rfl, hψ, RelIso.coe_fn_toEquiv, hB _ hf0]
    exact pieceMap_star hd' L L' βA f.2

theorem Pair.exists_mulEquiv_of_starEquiv_tripleAt (hE : Pair X E) (hF : Pair Y F)
    (hZE : Subgroup.center X = ⊥) (hZF : Subgroup.center Y = ⊥) {d : X} {d' : Y}
    (hTE : TripleAt E d) (hTF : TripleProperty F) (hd : d ∈ E) (hd' : d' ∈ F)
    (hne : (LocalClass F d').Nonempty) (φ : LocalClass E d ≃ LocalClass F d')
    (hcomm : ∀ f g : LocalClass E d, (f : X) * g = g * f ↔ (φ f : Y) * φ g = φ g * φ f)
    (htau : ∀ (f g : LocalClass E d) (h : (f : X) * g * f ∈ LocalClass E d),
      (φ ⟨_, h⟩ : Y) = φ f * φ g * φ f)
    (hfam : starMap φ '' muFamily E d = muFamily F d')
    {r : muFamily F d'} (hr : CoverRigid (muGraph F d') r) :
    ∃ ψ : X ≃* Y, ψ '' E = F ∧ ψ d = d' ∧ ∀ f : LocalClass E d, ψ f = φ f := by
  obtain ⟨χ, h1, h2, h3⟩ := Pair.exists_mulEquiv_of_starEquiv_left_tripleAt hF hE hZF hZE hTF
    hTE hd' hd hne φ.symm (starEquiv_symm_comm φ hcomm) (starEquiv_symm_tau hE φ htau)
    (starMap_symm_image_muFamily φ hfam) hr
  refine ⟨χ.symm, ?_, ?_, fun f => ?_⟩
  · rw [← h1]
    exact image_symm_image χ F
  · rw [MulEquiv.symm_apply_eq, h2]
  · rw [MulEquiv.symm_apply_eq, h3, Equiv.symm_apply_apply]

theorem Pair.exists_mulEquiv_of_muSet_tripleAt (hE : Pair X E) (hF : Pair Y F)
    (hZE : Subgroup.center X = ⊥) (hZF : Subgroup.center Y = ⊥) {d : X} {d' : Y}
    (hTE : TripleAt E d) (hTF : TripleProperty F) (hd : d ∈ E) (hd' : d' ∈ F)
    (hne : (LocalClass F d').Nonempty) (φ : LocalClass E d ≃ LocalClass F d')
    (hcomm : ∀ f g : LocalClass E d, (f : X) * g = g * f ↔ (φ f : Y) * φ g = φ g * φ f)
    (htau : ∀ (f g : LocalClass E d) (h : (f : X) * g * f ∈ LocalClass E d),
      (φ ⟨_, h⟩ : Y) = φ f * φ g * φ f)
    {x : X} (hx : x ∈ E) (hxd : x * d ≠ d * x) {x' : Y} (hx' : x' ∈ F)
    (hxd' : x' * d' ≠ d' * x') (h : starMap φ (muSet E d x) = muSet F d' x')
    (htrE : ∀ c ∈ E, c * d ≠ d * c →
      ∃ g ∈ LocalGroup E d, muSet E d c = (fun s => g * s * g⁻¹) '' muSet E d x)
    {r : muFamily F d'} (hr : CoverRigid (muGraph F d') r) :
    ∃ ψ : X ≃* Y, ψ '' E = F ∧ ψ d = d' ∧ ∀ f : LocalClass E d, ψ f = φ f :=
  Pair.exists_mulEquiv_of_starEquiv_tripleAt hE hF hZE hZF hTE hTF hd hd' hne φ hcomm htau
    (Pair.starMap_image_muFamily hE hF φ htau hx hxd hx' hxd' h htrE
      (Pair.exists_conj_of_connected hF hx' hxd' hr.graph_connected)) hr

end CFSG.Fischer.Classification.Unitary

