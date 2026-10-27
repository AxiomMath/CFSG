module

public import CFSG.Fischer.Classification.Uniqueness.Cover
public import CFSG.Fischer.Uniq.Assemble

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

theorem exists_mulEquiv_of_tau_eq (hE : Pair X E) (hF : Pair Y F) (hZE : Subgroup.center X = ⊥)
    (hZF : Subgroup.center Y = ⊥) (β : E ≃ F)
    (hβ : ∀ e f : E, β (tauE hE e f) = tauE hF (β e) (β f)) :
    ∃ φ : X ≃* Y, ∀ e : E, φ e = β e := by
  set ρ := Pair.conjPerm hE
  set σ := Pair.conjPerm hF
  let c : Equiv.Perm E ≃* Equiv.Perm F := Equiv.permCongrHom β
  have hc : ∀ e : E, c (ρ e) = σ (β e) := by
    intro e
    ext f
    obtain ⟨f0, rfl⟩ := β.surjective f
    show (β (ρ e (β.symm (β f0))) : Y) = _
    rw [Equiv.symm_apply_apply, conjPerm_eq_tau, conjPerm_eq_tau, hβ]
  have hrange : ρ.range.map c.toMonoidHom = σ.range := by
    rw [range_conjPerm, range_conjPerm, MonoidHom.map_closure]
    congr 1
    ext τ
    constructor
    · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
      exact ⟨β e, (hc e).symm⟩
    · rintro ⟨f, rfl⟩
      obtain ⟨e, rfl⟩ := β.surjective f
      exact ⟨ρ e, ⟨e, rfl⟩, hc e⟩
  let eX : X ≃* ρ.range := MonoidHom.ofInjective (Pair.conjPerm_injective hE hZE)
  let eY : Y ≃* σ.range := MonoidHom.ofInjective (Pair.conjPerm_injective hF hZF)
  let eR : ρ.range ≃* σ.range :=
    (ρ.range.equivMapOfInjective c.toMonoidHom c.injective).trans (MulEquiv.subgroupCongr hrange)
  let φ : X ≃* Y := (eX.trans eR).trans eY.symm
  refine ⟨φ, fun e => ?_⟩
  apply Pair.conjPerm_injective hF hZF
  have h1 : (eY (φ e) : Equiv.Perm F) = σ (φ e) := rfl
  have h2 : eY (φ e) = eR (eX e) := by simp [φ]
  rw [← h1, h2]
  exact hc e

theorem image_eq_of_forall_eq {φ : X ≃* Y} (β : E ≃ F) (h : ∀ e : E, φ e = β e) :
    φ '' E = F := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [h ⟨x, hx⟩]
    exact (β ⟨x, hx⟩).2
  · intro hy
    obtain ⟨e, he⟩ := β.surjective ⟨y, hy⟩
    exact ⟨e, e.2, by rw [h e, he]⟩

theorem Pair.exists_mulEquiv_of_starEquiv_left (hE : Pair X E) (hF : Pair Y F)
    (hZE : Subgroup.center X = ⊥) (hZF : Subgroup.center Y = ⊥)
    (hTE : TripleProperty E) (hTF : TripleProperty F) {d : X} {d' : Y} (hd : d ∈ E)
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
    fun c hc hcd => Pair.muSet_nonempty_of_triple hF hTF hd' hne' hc hcd
  set L := starPoints hE d
  set L' := starEquivPoints hE φ hcomm htau
  have h := coverHyp_starPoints hE hTE hd
  have h' := coverHyp_starEquivPoints hE φ hcomm htau hTE hTF hd hd' hmuE hmuF hfam
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
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_of_tau_eq hE hF hZE hZF B.toEquiv
    (Pair.tau_of_graphIso hE hF B hTF)
  refine ⟨ψ, image_eq_of_forall_eq B.toEquiv hψ, ?_, fun f => ?_⟩
  · have hd0 : (⟨d, hd⟩ : E) ∈ compSet E d := by rw [huE]; trivial
    rw [show d = ((⟨d, hd⟩ : E) : X) from rfl, hψ, RelIso.coe_fn_toEquiv, hB _ hd0]
    exact pieceMap_d hd hd' L L' βA rfl
  · have hf0 : (⟨f, f.2.1⟩ : E) ∈ compSet E d := by rw [huE]; trivial
    rw [show (f : X) = ((⟨f, f.2.1⟩ : E) : X) from rfl, hψ, RelIso.coe_fn_toEquiv, hB _ hf0]
    exact pieceMap_star hd' L L' βA f.2

theorem starEquiv_symm_comm {d : X} {d' : Y} (φ : LocalClass E d ≃ LocalClass F d')
    (hcomm : ∀ f g : LocalClass E d, (f : X) * g = g * f ↔ (φ f : Y) * φ g = φ g * φ f)
    (f g : LocalClass F d') :
    (f : Y) * g = g * f ↔ (φ.symm f : X) * φ.symm g = φ.symm g * φ.symm f := by
  have := hcomm (φ.symm f) (φ.symm g)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  exact this.symm

theorem starEquiv_symm_tau (hE : Pair X E) {d : X} {d' : Y} (φ : LocalClass E d ≃ LocalClass F d')
    (htau : ∀ (f g : LocalClass E d) (h : (f : X) * g * f ∈ LocalClass E d),
      (φ ⟨_, h⟩ : Y) = φ f * φ g * φ f)
    (f g : LocalClass F d') (h : (f : Y) * g * f ∈ LocalClass F d') :
    (φ.symm ⟨_, h⟩ : X) = φ.symm f * φ.symm g * φ.symm f := by
  have hm := Pair.mul_mul_mem_localClass_of_mem hE (φ.symm f).2 (φ.symm g).2
  have := htau (φ.symm f) (φ.symm g) hm
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  have h' : φ ⟨_, hm⟩ = ⟨_, h⟩ := Subtype.ext this
  rw [← h', Equiv.symm_apply_apply]

theorem starMap_symm_image_muFamily {d : X} {d' : Y} (φ : LocalClass E d ≃ LocalClass F d')
    (hfam : starMap φ '' muFamily E d = muFamily F d') :
    starMap φ.symm '' muFamily F d' = muFamily E d := by
  rw [← hfam, Set.image_image]
  conv_rhs => rw [← Set.image_id (muFamily E d)]
  exact Set.image_congr fun O hO => starMap_symm_starMap φ (subset_localClass_of_mem_muFamily hO)

theorem Pair.exists_mulEquiv_of_starEquiv (hE : Pair X E) (hF : Pair Y F)
    (hZE : Subgroup.center X = ⊥) (hZF : Subgroup.center Y = ⊥)
    (hTE : TripleProperty E) (hTF : TripleProperty F) {d : X} {d' : Y} (hd : d ∈ E)
    (hd' : d' ∈ F) (hne : (LocalClass F d').Nonempty) (φ : LocalClass E d ≃ LocalClass F d')
    (hcomm : ∀ f g : LocalClass E d, (f : X) * g = g * f ↔ (φ f : Y) * φ g = φ g * φ f)
    (htau : ∀ (f g : LocalClass E d) (h : (f : X) * g * f ∈ LocalClass E d),
      (φ ⟨_, h⟩ : Y) = φ f * φ g * φ f)
    (hfam : starMap φ '' muFamily E d = muFamily F d')
    {r : muFamily F d'} (hr : CoverRigid (muGraph F d') r) :
    ∃ ψ : X ≃* Y, ψ '' E = F ∧ ψ d = d' ∧ ∀ f : LocalClass E d, ψ f = φ f := by
  obtain ⟨χ, h1, h2, h3⟩ := Pair.exists_mulEquiv_of_starEquiv_left hF hE hZF hZE hTF hTE hd' hd
    hne φ.symm (starEquiv_symm_comm φ hcomm) (starEquiv_symm_tau hE φ htau)
    (starMap_symm_image_muFamily φ hfam) hr
  refine ⟨χ.symm, ?_, ?_, fun f => ?_⟩
  · rw [← h1]
    exact image_symm_image χ F
  · rw [MulEquiv.symm_apply_eq, h2]
  · rw [MulEquiv.symm_apply_eq, h3, Equiv.symm_apply_apply]

end CFSG.Fischer.Classification
