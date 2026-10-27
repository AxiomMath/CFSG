module

public import CFSG.Fischer.Classification.Uniqueness.Abstract

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

theorem mul_eq_of_mem_localGroup {d g : X} (hg : g ∈ LocalGroup E d) : g * d = d * g :=
  commute_of_mem_localGroup (fun _ hf => hf.2.2) hg

theorem conj_eq_of_mem_localGroup {d g : X} (hg : g ∈ LocalGroup E d) : g * d * g⁻¹ = d := by
  rw [mul_eq_of_mem_localGroup hg, mul_assoc, mul_inv_cancel, mul_one]

theorem Pair.conj_mem_localClass_of_mem_localGroup (hP : Pair X E) {d g p : X}
    (hg : g ∈ LocalGroup E d) (hp : p ∈ LocalClass E d) : g * p * g⁻¹ ∈ LocalClass E d := by
  have := (Pair.conj_mem_localClass_iff hP g).2 hp
  rwa [conj_eq_of_mem_localGroup hg] at this

theorem Pair.image_conj_muSet_of_mem_localGroup (hP : Pair X E) {d g : X}
    (hg : g ∈ LocalGroup E d) (c : X) :
    (fun s => g * s * g⁻¹) '' muSet E d c = muSet E d (g * c * g⁻¹) := by
  rw [Pair.image_conj_muSet hP, conj_eq_of_mem_localGroup hg]

theorem Pair.exists_conj_starEquiv (hE : Pair X E) (hF : Pair Y F) {d : X} {d' : Y}
    (φ : LocalClass E d ≃ LocalClass F d')
    (htau : ∀ (f g : LocalClass E d) (h : (f : X) * g * f ∈ LocalClass E d),
      (φ ⟨_, h⟩ : Y) = φ f * φ g * φ f)
    {g : X} (hg : g ∈ LocalGroup E d) :
    ∃ g' ∈ LocalGroup F d', ∀ p q : LocalClass E d, (q : X) = g * p * g⁻¹ →
      (φ q : Y) = g' * φ p * g'⁻¹ := by
  change g ∈ Subgroup.closure (LocalClass E d) at hg
  induction hg using Subgroup.closure_induction with
  | mem f hf =>
    refine ⟨φ ⟨f, hf⟩, mem_localGroup (φ ⟨f, hf⟩).2, fun p q hq => ?_⟩
    have hm := Pair.mul_mul_mem_localClass_of_mem hE hf p.2
    have hq' : q = ⟨_, hm⟩ := Subtype.ext (by rw [hq, Pair.inv_eq hE hf.1])
    rw [hq', Pair.inv_eq hF (φ ⟨f, hf⟩).2.1]
    exact htau ⟨f, hf⟩ p hm
  | one =>
    refine ⟨1, one_mem _, fun p q hq => ?_⟩
    have : q = p := Subtype.ext (by rw [hq]; group)
    rw [this]
    group
  | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
    obtain ⟨g₁', hg₁', h₁⟩ := ih₁
    obtain ⟨g₂', hg₂', h₂⟩ := ih₂
    refine ⟨g₁' * g₂', mul_mem hg₁' hg₂', fun p q hq => ?_⟩
    have hr := Pair.conj_mem_localClass_of_mem_localGroup hE hg₂ p.2
    rw [h₁ ⟨_, hr⟩ q (by rw [hq]; group), h₂ p ⟨_, hr⟩ rfl]
    group
  | inv g hg ih =>
    obtain ⟨g', hg', h⟩ := ih
    refine ⟨g'⁻¹, inv_mem hg', fun p q hq => ?_⟩
    rw [h q p (by rw [hq]; group)]
    group

theorem starMap_conj (hE : Pair X E) {d : X} {d' : Y} (φ : LocalClass E d ≃ LocalClass F d')
    {g : X} (hg : g ∈ LocalGroup E d) {g' : Y}
    (h : ∀ p q : LocalClass E d, (q : X) = g * p * g⁻¹ → (φ q : Y) = g' * φ p * g'⁻¹)
    {O : Set X} (hO : O ⊆ LocalClass E d) :
    starMap φ ((fun s => g * s * g⁻¹) '' O) = (fun s => g' * s * g'⁻¹) '' starMap φ O := by
  ext y
  constructor
  · rintro ⟨q, ⟨s, hs, hsq⟩, rfl⟩
    exact ⟨φ ⟨s, hO hs⟩, ⟨⟨s, hO hs⟩, hs, rfl⟩, (h ⟨s, hO hs⟩ q hsq.symm).symm⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨⟨g * p * g⁻¹, Pair.conj_mem_localClass_of_mem_localGroup hE hg p.2⟩, ⟨p, hp, rfl⟩,
      h p _ rfl⟩

theorem Pair.starMap_image_muFamily (hE : Pair X E) (hF : Pair Y F) {d : X} {d' : Y}
    (φ : LocalClass E d ≃ LocalClass F d')
    (htau : ∀ (f g : LocalClass E d) (h : (f : X) * g * f ∈ LocalClass E d),
      (φ ⟨_, h⟩ : Y) = φ f * φ g * φ f)
    {x : X} (hx : x ∈ E) (hxd : x * d ≠ d * x) {x' : Y} (hx' : x' ∈ F)
    (hxd' : x' * d' ≠ d' * x') (h : starMap φ (muSet E d x) = muSet F d' x')
    (htrE : ∀ c ∈ E, c * d ≠ d * c →
      ∃ g ∈ LocalGroup E d, muSet E d c = (fun s => g * s * g⁻¹) '' muSet E d x)
    (htrF : ∀ c ∈ F, c * d' ≠ d' * c →
      ∃ g ∈ LocalGroup F d', muSet F d' c = (fun s => g * s * g⁻¹) '' muSet F d' x') :
    starMap φ '' muFamily E d = muFamily F d' := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨c, hc, hcd, rfl⟩, rfl⟩
    obtain ⟨g, hg, hgc⟩ := htrE c hc hcd
    obtain ⟨g', hg', hgg'⟩ := Pair.exists_conj_starEquiv hE hF φ htau hg
    refine ⟨g' * x' * g'⁻¹, Pair.conj_mem hF hx' g', fun hc' => hxd' ?_, ?_⟩
    · rw [← conj_commute_iff g', conj_eq_of_mem_localGroup hg']
      exact hc'
    · rw [hgc, starMap_conj hE φ hg hgg' (muSet_subset_localClass d x), h,
        Pair.image_conj_muSet_of_mem_localGroup hF hg']
  · rintro _ ⟨c', hc', hcd', rfl⟩
    obtain ⟨g', hg', hgc'⟩ := htrF c' hc' hcd'
    obtain ⟨g, hg, hgg⟩ :=
      Pair.exists_conj_starEquiv hF hE φ.symm (starEquiv_symm_tau hE φ htau) hg'
    have hsym : starMap φ.symm (muSet F d' x') = muSet E d x := by
      rw [← h, starMap_symm_starMap φ (muSet_subset_localClass d x)]
    have hmu : muSet E d (g * x * g⁻¹) = starMap φ.symm (muSet F d' c') := by
      rw [hgc', starMap_conj hF φ.symm hg' hgg (muSet_subset_localClass d' x'), hsym,
        Pair.image_conj_muSet_of_mem_localGroup hE hg]
    refine ⟨muSet E d (g * x * g⁻¹), ⟨g * x * g⁻¹, Pair.conj_mem hE hx g, fun hc => hxd ?_, rfl⟩,
      ?_⟩
    · rw [← conj_commute_iff g, conj_eq_of_mem_localGroup hg]
      exact hc
    · rw [hmu]
      exact starMap_symm_starMap φ.symm (muSet_subset_localClass d' c')

theorem CoverRigid.graph_connected {V : Type*} {G : SimpleGraph V} {r : V} (h : CoverRigid G r) :
    G.Connected := by
  have : Nonempty V := ⟨r⟩
  refine (SimpleGraph.connected_iff_exists_forall_reachable G).2 ⟨r, fun v => ?_⟩
  by_cases h0 : v = r
  · rw [h0]
  · by_cases h1 : G.Adj r v
    · exact h1.reachable
    · obtain ⟨x, hrx, hxv⟩ := h.exists_adj_adj v h0 h1
      exact hrx.reachable.trans hxv.reachable

theorem Pair.exists_conj_of_connected (hP : Pair X E) {d x : X} (hx : x ∈ E)
    (hxd : x * d ≠ d * x) (hconn : (muGraph E d).Connected) :
    ∀ c ∈ E, c * d ≠ d * c →
      ∃ g ∈ LocalGroup E d, muSet E d c = (fun s => g * s * g⁻¹) '' muSet E d x := by
  intro c hc hcd
  refine connected_induction hconn (w₀ := ⟨muSet E d x, muSet_mem_muFamily hx hxd⟩)
    (p := fun O : muFamily E d =>
      ∃ g ∈ LocalGroup E d, (O : Set X) = (fun s => g * s * g⁻¹) '' muSet E d x)
    ⟨1, one_mem _, by simp⟩ ?_ ⟨muSet E d c, muSet_mem_muFamily hc hcd⟩
  rintro O Q hOQ ⟨g, hg, hO⟩
  obtain ⟨-, f, hf, -, hQ⟩ := (Pair.muGraph_adj hP).1 hOQ
  refine ⟨f * g, mul_mem (mem_localGroup hf) hg, ?_⟩
  rw [← hQ, hO, Set.image_image]
  refine Set.image_congr fun s _ => ?_
  rw [mul_inv_rev, Pair.inv_eq hP hf.1]
  group

theorem Pair.exists_localGroup_of_mem_closure_insert (hP : Pair X E) {d g : X}
    (hg : g ∈ Subgroup.closure (insert d (LocalClass E d))) :
    ∃ h ∈ LocalGroup E d, ∀ s ∈ LocalClass E d, g * s * g⁻¹ = h * s * h⁻¹ := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · refine ⟨1, one_mem _, fun s hs => ?_⟩
      rw [← hs.2.2, mul_assoc, mul_inv_cancel, mul_one]
      group
    · exact ⟨y, mem_localGroup hy, fun _ _ => rfl⟩
  | one => exact ⟨1, one_mem _, fun _ _ => rfl⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    obtain ⟨h₁, hh₁, e₁⟩ := ih₁
    obtain ⟨h₂, hh₂, e₂⟩ := ih₂
    refine ⟨h₁ * h₂, mul_mem hh₁ hh₂, fun s hs => ?_⟩
    have hs' := Pair.conj_mem_localClass_of_mem_localGroup hP hh₂ hs
    calc g₁ * g₂ * s * (g₁ * g₂)⁻¹ = g₁ * (g₂ * s * g₂⁻¹) * g₁⁻¹ := by group
      _ = h₁ * (h₂ * s * h₂⁻¹) * h₁⁻¹ := by rw [e₂ s hs, e₁ _ hs']
      _ = h₁ * h₂ * s * (h₁ * h₂)⁻¹ := by group
  | inv g _ ih =>
    obtain ⟨h, hh, e⟩ := ih
    refine ⟨h⁻¹, inv_mem hh, fun s hs => ?_⟩
    have ht := Pair.conj_mem_localClass_of_mem_localGroup hP (inv_mem hh) hs
    have h1 : g * (h⁻¹ * s * h⁻¹⁻¹) * g⁻¹ = s := by
      rw [e _ ht]
      group
    calc g⁻¹ * s * g⁻¹⁻¹ = g⁻¹ * (g * (h⁻¹ * s * h⁻¹⁻¹) * g⁻¹) * g⁻¹⁻¹ := by rw [h1]
      _ = h⁻¹ * s * h⁻¹⁻¹ := by group

theorem Pair.exists_conj_of_transitive (hP : Pair X E) {d x : X}
    (htr : ∀ c ∈ E, c * d ≠ d * c →
      ∃ g ∈ Subgroup.closure (insert d (LocalClass E d)), g * x * g⁻¹ = c) :
    ∀ c ∈ E, c * d ≠ d * c →
      ∃ g ∈ LocalGroup E d, muSet E d c = (fun s => g * s * g⁻¹) '' muSet E d x := by
  intro c hc hcd
  obtain ⟨g, hg, rfl⟩ := htr c hc hcd
  obtain ⟨h, hh, e⟩ := Pair.exists_localGroup_of_mem_closure_insert hP hg
  have hgd : g * d * g⁻¹ = d := by
    have hmem : g ∈ Subgroup.centralizer ({d} : Set X) := by
      refine (Subgroup.closure_le _).2 (fun y hy => ?_) hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hy with rfl | hy
      · rfl
      · exact hy.2.2
    rw [Subgroup.mem_centralizer_singleton_iff.1 hmem, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨h, hh, ?_⟩
  have h1 : (fun s => h * s * h⁻¹) '' muSet E d x = (fun s => g * s * g⁻¹) '' muSet E d x :=
    Set.image_congr fun s hs => (e s hs.1).symm
  rw [h1, Pair.image_conj_muSet hP, hgd]

theorem Pair.exists_mulEquiv_of_muSet (hE : Pair X E) (hF : Pair Y F)
    (hZE : Subgroup.center X = ⊥) (hZF : Subgroup.center Y = ⊥)
    (hTE : TripleProperty E) (hTF : TripleProperty F) {d : X} {d' : Y} (hd : d ∈ E)
    (hd' : d' ∈ F) (hne : (LocalClass F d').Nonempty) (φ : LocalClass E d ≃ LocalClass F d')
    (hcomm : ∀ f g : LocalClass E d, (f : X) * g = g * f ↔ (φ f : Y) * φ g = φ g * φ f)
    (htau : ∀ (f g : LocalClass E d) (h : (f : X) * g * f ∈ LocalClass E d),
      (φ ⟨_, h⟩ : Y) = φ f * φ g * φ f)
    {x : X} (hx : x ∈ E) (hxd : x * d ≠ d * x) {x' : Y} (hx' : x' ∈ F)
    (hxd' : x' * d' ≠ d' * x') (h : starMap φ (muSet E d x) = muSet F d' x')
    (htrE : ∀ c ∈ E, c * d ≠ d * c →
      ∃ g ∈ LocalGroup E d, muSet E d c = (fun s => g * s * g⁻¹) '' muSet E d x)
    {r : muFamily F d'} (hr : CoverRigid (muGraph F d') r) :
    ∃ ψ : X ≃* Y, ψ '' E = F ∧ ψ d = d' ∧ ∀ f : LocalClass E d, ψ f = φ f :=
  Pair.exists_mulEquiv_of_starEquiv hE hF hZE hZF hTE hTF hd hd' hne φ hcomm htau
    (Pair.starMap_image_muFamily hE hF φ htau hx hxd hx' hxd' h htrE
      (Pair.exists_conj_of_connected hF hx' hxd' hr.graph_connected)) hr

end CFSG.Fischer.Classification
