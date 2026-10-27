module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Defs

public section

namespace CFSG.ComponentClassification.Asc76.L28

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G]

section Defs

variable (Ω : Set (Subgroup G))

@[expose] def Adj (K J : Subgroup G) : Prop :=
  J ∈ Ω ∧ J ≠ K ∧ J ≤ normalizer (K : Set G)

@[expose] def nbrGroup (K : Subgroup G) : Subgroup G :=
  ⨆ (J : Subgroup G) (_ : Adj Ω K J), J

@[expose] def common (π : Set (Subgroup G)) : Set (Subgroup G) :=
  {M | M ∈ Ω ∧ ∀ P ∈ π, Adj Ω P M}

end Defs

@[expose] def orbit (X P : Subgroup G) : Set (Subgroup G) :=
  {Q | ∃ x ∈ X, Q = rightConjugate P x}

@[expose] def Preserves (A : Set (Subgroup G)) (z : G) : Prop :=
  ∀ Q, Q ∈ A ↔ rightConjugate Q z ∈ A

theorem rightConjugate_inv_cancel (A : Subgroup G) (y : G) :
    rightConjugate (rightConjugate A y) y⁻¹ = A := by
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

theorem rightConjugate_inv_cancel' (A : Subgroup G) (y : G) :
    rightConjugate (rightConjugate A y⁻¹) y = A := by
  rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]

theorem rightConjugate_injective (y : G) :
    Function.Injective (fun A : Subgroup G => rightConjugate A y) := fun A B h => by
  have := congrArg (fun C => rightConjugate C y⁻¹) h
  simpa only [rightConjugate_inv_cancel] using this

theorem rightConjugate_le {A B : Subgroup G} (h : A ≤ B) (y : G) :
    rightConjugate A y ≤ rightConjugate B y :=
  map_mono h

theorem rightConjugate_eq_of_mem {A : Subgroup G} {y : G}
    (hy : y ∈ normalizer (A : Set G)) : rightConjugate A y = A :=
  (rightConjugate_eq_self_iff A y).mpr hy

theorem Preserves.one (A : Set (Subgroup G)) : Preserves A 1 := fun Q => by
  rw [rightConjugate_one]

theorem Preserves.mul {A : Set (Subgroup G)} {z w : G} (hz : Preserves A z)
    (hw : Preserves A w) : Preserves A (z * w) := fun Q => by
  rw [hz Q, hw (rightConjugate Q z), rightConjugate_mul]

theorem Preserves.of_iSup {A : Set (Subgroup G)} {p : Subgroup G → Prop}
    (h : ∀ J, p J → ∀ z ∈ J, Preserves A z) {x : G}
    (hx : x ∈ ⨆ (J : Subgroup G) (_ : p J), J) : Preserves A x := by
  refine iSup_induction (C := fun x => Preserves A x) _ hx (fun J y hy => ?_) (Preserves.one A)
    (fun _ _ => Preserves.mul)
  exact iSup_induction (C := fun x => Preserves A x) _ hy (fun hJ z hz => h J hJ z hz)
    (Preserves.one A) (fun _ _ => Preserves.mul)

theorem preserves_of_le_normalizer {A : Set (Subgroup G)} {c : Subgroup G}
    (hc : ∀ Q ∈ A, c ≤ normalizer (Q : Set G)) {y : G} (hy : y ∈ c) : Preserves A y := by
  intro Q
  constructor
  · intro hQ
    rw [rightConjugate_eq_of_mem (hc Q hQ hy)]
    exact hQ
  · intro hQ
    have h := rightConjugate_eq_of_mem (hc _ hQ (c.inv_mem hy))
    rw [rightConjugate_inv_cancel] at h
    rw [h]
    exact hQ

theorem mem_orbit_self (X P : Subgroup G) : P ∈ orbit X P :=
  ⟨1, one_mem _, (rightConjugate_one P).symm⟩

theorem orbit_eq_of_mem {X P Q : Subgroup G} (h : Q ∈ orbit X P) : orbit X Q = orbit X P := by
  obtain ⟨x, hx, rfl⟩ := h
  ext R
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨x * y, mul_mem hx hy, by rw [rightConjugate_mul]⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy, ?_⟩
    rw [rightConjugate_mul, ← mul_assoc, mul_inv_cancel, one_mul]

theorem preserves_orbit {X P : Subgroup G} {x : G} (hx : x ∈ X) : Preserves (orbit X P) x := by
  intro Q
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y * x, mul_mem hy hx, by rw [rightConjugate_mul]⟩
  · rintro ⟨y, hy, h⟩
    refine ⟨y * x⁻¹, mul_mem hy (inv_mem hx), ?_⟩
    rw [← rightConjugate_mul, ← h, rightConjugate_inv_cancel]

theorem orbit_mono {X Y P : Subgroup G} (h : X ≤ Y) : orbit X P ⊆ orbit Y P := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

theorem orbit_conj (X P : Subgroup G) (g : G) :
    orbit (rightConjugate X g) (rightConjugate P g) =
      (fun A => rightConjugate A g) '' orbit X P := by
  ext Q
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_rightConjugate_iff] at hx
    refine ⟨rightConjugate P (g * x * g⁻¹), ⟨_, hx, rfl⟩, ?_⟩
    simp only [rightConjugate_mul]
    congr 1
    group
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g⁻¹ * x * g, (mem_rightConjugate_iff _ _ _).mpr (by simpa [mul_assoc] using hx), ?_⟩
    simp only [rightConjugate_mul]
    congr 1
    group

structure Hyp (Ω : Set (Subgroup G)) : Prop where
  conj_mem : ∀ J ∈ Ω, ∀ g : G, rightConjugate J g ∈ Ω
  trans : ∀ J ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = rightConjugate J g
  symm : ∀ K ∈ Ω, ∀ J, Adj Ω K J → Adj Ω J K
  dich : ∀ K ∈ Ω, ∀ J L, Adj Ω K J → Adj Ω K L →
    Adj Ω L J ∨ ∃ x ∈ J ⊔ L, L = rightConjugate J x

variable {Ω : Set (Subgroup G)}

theorem Hyp.adj_conj (hΩ : Hyp Ω) {K J : Subgroup G} (h : Adj Ω K J) (g : G) :
    Adj Ω (rightConjugate K g) (rightConjugate J g) := by
  refine ⟨hΩ.conj_mem J h.1 g, fun e => h.2.1 (rightConjugate_injective g e), fun y hy => ?_⟩
  rw [mem_rightConjugate_iff] at hy
  have h1 := rightConjugate_eq_of_mem (h.2.2 hy)
  rw [← rightConjugate_eq_self_iff, rightConjugate_mul,
    show g * y = (g * y * g⁻¹) * g by group, ← rightConjugate_mul, h1]

theorem Hyp.adj_of_conj (hΩ : Hyp Ω) {K J : Subgroup G} {g : G}
    (h : Adj Ω (rightConjugate K g) (rightConjugate J g)) : Adj Ω K J := by
  have := hΩ.adj_conj h g⁻¹
  rwa [rightConjugate_inv_cancel, rightConjugate_inv_cancel] at this

theorem nbrGroup_le_normalizer (K : Subgroup G) : nbrGroup Ω K ≤ normalizer (K : Set G) :=
  iSup₂_le fun _ hJ => hJ.2.2

theorem le_nbrGroup {K J : Subgroup G} (h : Adj Ω K J) : J ≤ nbrGroup Ω K :=
  le_iSup₂ (f := fun J (_ : Adj Ω K J) => J) J h

theorem Hyp.adj_of_mem_orbit (hΩ : Hyp Ω) {K P Q : Subgroup G} (hP : Adj Ω K P)
    (hQ : Q ∈ orbit (nbrGroup Ω K) P) : Adj Ω K Q := by
  obtain ⟨x, hx, rfl⟩ := hQ
  have := hΩ.adj_conj hP x
  rwa [rightConjugate_eq_of_mem (nbrGroup_le_normalizer K hx)] at this

theorem Hyp.adj_of_not_mem_orbit (hΩ : Hyp Ω) {K J L : Subgroup G} (hK : K ∈ Ω)
    (hJ : Adj Ω K J) (hL : Adj Ω K L) (hn : L ∉ orbit (nbrGroup Ω K) J) : Adj Ω J L := by
  rcases hΩ.dich K hK J L hJ hL with h | ⟨x, hx, hxe⟩
  · exact hΩ.symm L hL.1 J h
  · exact absurd ⟨x, sup_le (le_nbrGroup hJ) (le_nbrGroup hL) hx, hxe⟩ hn

theorem Hyp.exists_conj_of_mem_orbit (hΩ : Hyp Ω) {K P : Subgroup G} (hK : K ∈ Ω)
    (hP : Adj Ω K P) {Q₁ Q₂ : Subgroup G} (h₁ : Q₁ ∈ orbit (nbrGroup Ω K) P)
    (h₂ : Q₂ ∈ orbit (nbrGroup Ω K) P) :
    ∃ x ∈ ⨆ (P' : Subgroup G) (_ : P' ∈ orbit (nbrGroup Ω K) P), P',
      Q₂ = rightConjugate Q₁ x := by
  set π := orbit (nbrGroup Ω K) P with hπ
  set Y := ⨆ (P' : Subgroup G) (_ : P' ∈ π), P' with hY
  have hYX : Y ≤ nbrGroup Ω K := iSup₂_le fun P' hP' => le_nbrGroup (hΩ.adj_of_mem_orbit hP hP')
  have hpres : ∀ x ∈ nbrGroup Ω K, Preserves (orbit Y P) x := by
    intro x hx
    refine Preserves.of_iSup (p := Adj Ω K) (fun c hc z hz => ?_) hx
    by_cases hcπ : c ∈ π
    · exact preserves_orbit (le_iSup₂ (f := fun P' (_ : P' ∈ π) => P') c hcπ hz)
    · refine preserves_of_le_normalizer (fun Q hQ => ?_) hz
      have hQπ : Q ∈ π := orbit_mono hYX hQ
      have hn : c ∉ orbit (nbrGroup Ω K) Q := by
        rw [orbit_eq_of_mem hQπ]
        exact hcπ
      exact (hΩ.adj_of_not_mem_orbit hK (hΩ.adj_of_mem_orbit hP hQπ) hc hn).2.2
  have hsub : π ⊆ orbit Y P := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hpres x hx P).mp (mem_orbit_self Y P)
  obtain ⟨y₁, hy₁, rfl⟩ := hsub h₁
  obtain ⟨y₂, hy₂, rfl⟩ := hsub h₂
  refine ⟨y₁⁻¹ * y₂, mul_mem (inv_mem hy₁) hy₂, ?_⟩
  rw [rightConjugate_mul, ← mul_assoc, mul_inv_cancel, one_mul]

theorem Hyp.nbrGroup_conj (hΩ : Hyp Ω) (K : Subgroup G) (g : G) :
    nbrGroup Ω (rightConjugate K g) = rightConjugate (nbrGroup Ω K) g := by
  apply le_antisymm
  · refine iSup₂_le fun J hJ => ?_
    have h1 : Adj Ω K (rightConjugate J g⁻¹) := by
      have := hΩ.adj_conj hJ g⁻¹
      rwa [rightConjugate_inv_cancel] at this
    have h2 := rightConjugate_le (le_nbrGroup h1) g
    rwa [rightConjugate_inv_cancel'] at h2
  · have h1 : nbrGroup Ω K ≤ rightConjugate (nbrGroup Ω (rightConjugate K g)) g⁻¹ := by
      refine iSup₂_le fun J hJ => ?_
      have h2 := rightConjugate_le (le_nbrGroup (hΩ.adj_conj hJ g)) g⁻¹
      rwa [rightConjugate_inv_cancel] at h2
    have h3 := rightConjugate_le h1 g
    rwa [rightConjugate_inv_cancel'] at h3

variable [Finite G]

theorem Hyp.ncard_orbit_le (hΩ : Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {m : ℕ}
    (hmax : ∀ P, Adj Ω K P → (orbit (nbrGroup Ω K) P).ncard ≤ m) {x R : Subgroup G}
    (hx : x ∈ Ω) (hR : Adj Ω x R) : (orbit (nbrGroup Ω x) R).ncard ≤ m := by
  obtain ⟨h, rfl⟩ := hΩ.trans K hK x hx
  have hR' : Adj Ω K (rightConjugate R h⁻¹) := by
    have := hΩ.adj_conj hR h⁻¹
    rwa [rightConjugate_inv_cancel] at this
  have heq : orbit (nbrGroup Ω (rightConjugate K h)) R =
      (fun A => rightConjugate A h) '' orbit (nbrGroup Ω K) (rightConjugate R h⁻¹) := by
    rw [hΩ.nbrGroup_conj, ← orbit_conj, rightConjugate_inv_cancel']
  rw [heq]
  exact (Set.ncard_image_le (Set.toFinite _)).trans (hmax _ hR')

section Good

variable (hΩ : Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {m : ℕ}
  (hmax : ∀ P, Adj Ω K P → (orbit (nbrGroup Ω K) P).ncard ≤ m) {ρ : Set (Subgroup G)}
  (hρΩ : ρ ⊆ Ω) (hρm : m ≤ ρ.ncard)
  (hρt : ∀ R₁ ∈ ρ, ∀ R₂ ∈ ρ, ∃ y ∈ ⨆ (R' : Subgroup G) (_ : R' ∈ ρ), R', R₂ = rightConjugate R₁ y)
  {x : Subgroup G} (hx : x ∈ Ω) (hxρ : ∀ R ∈ ρ, Adj Ω R x)
include hΩ hK hmax hρΩ hρm hρt hx hxρ

theorem Hyp.orbit_eq {R : Subgroup G} (hR : R ∈ ρ) : orbit (nbrGroup Ω x) R = ρ := by
  have hadj : ∀ R' ∈ ρ, Adj Ω x R' := fun R' hR' => hΩ.symm R' (hρΩ hR') x (hxρ R' hR')
  have hYle : (⨆ (R' : Subgroup G) (_ : R' ∈ ρ), R') ≤ nbrGroup Ω x :=
    iSup₂_le fun R' hR' => le_nbrGroup (hadj R' hR')
  have hsub : ρ ⊆ orbit (nbrGroup Ω x) R := fun R' hR' => by
    obtain ⟨y, hy, e⟩ := hρt R hR R' hR'
    exact ⟨y, hYle hy, e⟩
  exact (Set.eq_of_subset_of_ncard_le hsub
    ((hΩ.ncard_orbit_le hK hmax hx (hadj R hR)).trans hρm) (Set.toFinite _)).symm

theorem Hyp.mem_common_of_adj {y : Subgroup G} (hy : Adj Ω x y) (hyρ : y ∉ ρ) :
    y ∈ common Ω ρ := by
  refine ⟨hy.1, fun R hR => ?_⟩
  have hadj : Adj Ω x R := hΩ.symm R (hρΩ hR) x (hxρ R hR)
  exact hΩ.adj_of_not_mem_orbit hx hadj hy
    (by rw [hΩ.orbit_eq hK hmax hρΩ hρm hρt hx hxρ hR]; exact hyρ)

theorem Hyp.preserves_of_adj {R : Subgroup G} (hR : R ∈ ρ) {y : Subgroup G} (hy : Adj Ω x y)
    {z : G} (hz : z ∈ y) : Preserves ρ z := by
  rw [← hΩ.orbit_eq hK hmax hρΩ hρm hρt hx hxρ hR]
  exact preserves_orbit (le_nbrGroup hy hz)

end Good

omit [Finite G] in
theorem Hyp.common_conj (hΩ : Hyp Ω) (π : Set (Subgroup G)) (g : G) :
    common Ω ((fun A => rightConjugate A g) '' π) =
      (fun A => rightConjugate A g) '' common Ω π := by
  ext M
  constructor
  · rintro ⟨hM, h⟩
    refine ⟨rightConjugate M g⁻¹, ⟨hΩ.conj_mem M hM g⁻¹, fun P hP => ?_⟩,
      rightConjugate_inv_cancel' M g⟩
    exact hΩ.adj_of_conj (g := g) (by rw [rightConjugate_inv_cancel']; exact h _ ⟨P, hP, rfl⟩)
  · rintro ⟨M', ⟨hM', h⟩, rfl⟩
    refine ⟨hΩ.conj_mem M' hM' g, ?_⟩
    rintro _ ⟨P, hP, rfl⟩
    exact hΩ.adj_conj (h P hP) g

omit [Finite G] in
theorem Hyp.preserves_common (hΩ : Hyp Ω) {ρ : Set (Subgroup G)} {z : G}
    (hz : Preserves ρ z) : Preserves (common Ω ρ) z := by
  intro M
  constructor
  · rintro ⟨hM, h⟩
    refine ⟨hΩ.conj_mem M hM z, fun P hP => ?_⟩
    have hP' : rightConjugate P z⁻¹ ∈ ρ := (hz _).mpr (by rw [rightConjugate_inv_cancel']; exact hP)
    have := hΩ.adj_conj (h _ hP') z
    rwa [rightConjugate_inv_cancel'] at this
  · rintro ⟨hM, h⟩
    refine ⟨?_, fun P hP => ?_⟩
    · have := hΩ.conj_mem _ hM z⁻¹
      rwa [rightConjugate_inv_cancel] at this
    · exact hΩ.adj_of_conj (g := z) (h _ ((hz P).mp hP))

theorem Hyp.lemma28 (hΩ : Hyp Ω) (hgen : sSup Ω = ⊤)
    (hconn : ∀ K ∈ Ω, ∀ J ∈ Ω, Relation.ReflTransGen (Adj Ω) K J) {K P₀ : Subgroup G}
    (hK : K ∈ Ω) (hP₀ : Adj Ω K P₀)
    (hmax : ∀ P, Adj Ω K P →
      (orbit (nbrGroup Ω K) P).ncard ≤ (orbit (nbrGroup Ω K) P₀).ncard) :
    (∀ P ∈ orbit (nbrGroup Ω K) P₀, ∀ Q ∈ orbit (nbrGroup Ω K) P₀,
      ∃ x ∈ ⨆ (P' : Subgroup G) (_ : P' ∈ orbit (nbrGroup Ω K) P₀), P',
        Q = rightConjugate P x) ∧
    (∀ g : G, (fun A => rightConjugate A g) '' common Ω (orbit (nbrGroup Ω K) P₀) =
        common Ω (orbit (nbrGroup Ω K) P₀) ∨
      Disjoint ((fun A => rightConjugate A g) '' common Ω (orbit (nbrGroup Ω K) P₀))
        (common Ω (orbit (nbrGroup Ω K) P₀))) ∧
    ∀ P ∈ orbit (nbrGroup Ω K) P₀, ∃ g : G,
      P ∈ (fun A => rightConjugate A g) '' common Ω (orbit (nbrGroup Ω K) P₀) ∧
      (fun A => rightConjugate A g) '' common Ω (orbit (nbrGroup Ω K) P₀) ⊆
        orbit (nbrGroup Ω K) P₀ := by
  set π := orbit (nbrGroup Ω K) P₀ with hπdef
  set α := common Ω π with hαdef
  set m := π.ncard with hmdef
  have hπadj : ∀ P ∈ π, Adj Ω K P := fun P hP => hΩ.adj_of_mem_orbit hP₀ hP
  have hπΩ : π ⊆ Ω := fun P hP => (hπadj P hP).1
  have h1 : ∀ P ∈ π, ∀ Q ∈ π, ∃ x ∈ ⨆ (P' : Subgroup G) (_ : P' ∈ π), P',
      Q = rightConjugate P x := fun P hP Q hQ => hΩ.exists_conj_of_mem_orbit hK hP₀ hP hQ
  have hKα : K ∈ α := ⟨hK, fun P hP => hΩ.symm K hK P (hπadj P hP)⟩
  have hαπ : ∀ M ∈ α, M ∉ π := fun M hM hMπ => (hM.2 M hMπ).2.1 rfl
  set πc : G → Set (Subgroup G) := fun g => (fun A => rightConjugate A g) '' π with hπc
  have hπcΩ : ∀ g, πc g ⊆ Ω := by
    rintro g _ ⟨P, hP, rfl⟩
    exact hΩ.conj_mem P (hπΩ hP) g
  have hπcm : ∀ g, m ≤ (πc g).ncard := fun g =>
    (Set.ncard_image_of_injective _ (rightConjugate_injective g)).ge
  have hπcorb : ∀ g, πc g = orbit (nbrGroup Ω (rightConjugate K g)) (rightConjugate P₀ g) := by
    intro g
    rw [hΩ.nbrGroup_conj, orbit_conj]
  have hπct : ∀ g, ∀ R₁ ∈ πc g, ∀ R₂ ∈ πc g,
      ∃ y ∈ ⨆ (R' : Subgroup G) (_ : R' ∈ πc g), R', R₂ = rightConjugate R₁ y := by
    intro g R₁ hR₁ R₂ hR₂
    rw [hπcorb g] at hR₁ hR₂ ⊢
    exact hΩ.exists_conj_of_mem_orbit (hΩ.conj_mem K hK g) (hΩ.adj_conj hP₀ g) hR₁ hR₂
  have hmax' : ∀ P, Adj Ω K P → (orbit (nbrGroup Ω K) P).ncard ≤ m := hmax
  have hπt := h1
  have hπm : m ≤ π.ncard := le_rfl
  have hαc : ∀ g, common Ω (πc g) = (fun A => rightConjugate A g) '' α := fun g =>
    hΩ.common_conj π g
  have h2 : ∀ g : G, (fun A => rightConjugate A g) '' α = α ∨
      Disjoint ((fun A => rightConjugate A g) '' α) α := by
    intro g
    by_contra hcon
    push Not at hcon
    obtain ⟨hne, hmeet⟩ := hcon
    obtain ⟨M, hMg, hMα⟩ := Set.not_disjoint_iff.mp hmeet
    have hsubC : ∀ g' : G, (∃ M ∈ (fun A => rightConjugate A g') '' α, M ∈ α) →
        (fun A => rightConjugate A g') '' α ≠ α → π ⊆ (fun A => rightConjugate A g') '' α := by
      intro g' ⟨M, hMg', hMα'⟩ hne'
      rw [← hαc g'] at hMg' ⊢
      have hMΩ : M ∈ Ω := hMα'.1
      have hπM : ∀ a ∈ π, Adj Ω M a := fun a ha => hΩ.symm a (hπΩ ha) M (hMα'.2 a ha)
      obtain ⟨R₀, hR₀⟩ : ∃ R₀, R₀ ∈ πc g' := ⟨_, ⟨P₀, mem_orbit_self _ _, rfl⟩⟩
      have hpres : ∀ a ∈ π, ∀ z ∈ a, Preserves (common Ω (πc g')) z := fun a ha z hz =>
        hΩ.preserves_common (hΩ.preserves_of_adj hK hmax' (hπcΩ g') (hπcm g') (hπct g')
          hMΩ hMg'.2 hR₀ (hπM a ha) hz)
      by_cases hmeet' : ∃ a₀ ∈ π, a₀ ∈ common Ω (πc g')
      · obtain ⟨a₀, ha₀, ha₀c⟩ := hmeet'
        intro b hb
        obtain ⟨y, hy, rfl⟩ := h1 a₀ ha₀ b hb
        exact (Preserves.of_iSup (p := (· ∈ π)) hpres hy a₀).mp ha₀c
      · push Not at hmeet'
        exfalso
        apply hne'
        have hsub : π ⊆ πc g' := fun a ha => by
          by_contra hna
          exact hmeet' a ha (hΩ.mem_common_of_adj hK hmax' (hπcΩ g') (hπcm g') (hπct g') hMΩ
            hMg'.2 (hπM a ha) hna)
        have heq : π = πc g' :=
          Set.eq_of_subset_of_ncard_le hsub (by
            rw [Set.ncard_image_of_injective _ (rightConjugate_injective g')]) (Set.toFinite _)
        rw [← hαc g', ← heq]
    have hπα : π ⊆ (fun A => rightConjugate A g) '' α := hsubC g ⟨M, hMg, hMα⟩ hne
    have hπgα : πc g ⊆ α := by
      have hne' : (fun A => rightConjugate A g⁻¹) '' α ≠ α := by
        intro h
        apply hne
        calc (fun A => rightConjugate A g) '' α
            = (fun A => rightConjugate A g) '' ((fun A => rightConjugate A g⁻¹) '' α) := by
              rw [h]
          _ = α := by
              rw [Set.image_image]
              simp only [rightConjugate_inv_cancel', Set.image_id']
      have hmeet'' : ∃ M ∈ (fun A => rightConjugate A g⁻¹) '' α, M ∈ α := by
        obtain ⟨M', hM'α, rfl⟩ := hMg
        exact ⟨M', ⟨rightConjugate M' g, hMα, rightConjugate_inv_cancel M' g⟩, hM'α⟩
      have := hsubC g⁻¹ hmeet'' hne'
      rintro _ ⟨P, hP, rfl⟩
      obtain ⟨M', hM', e⟩ := this hP
      rw [← e]
      simp only [rightConjugate_inv_cancel']
      exact hM'
    obtain ⟨w, hw⟩ : ∃ w, w ∈ πc g := ⟨_, ⟨P₀, mem_orbit_self _ _, rfl⟩⟩
    have hwα : w ∈ α := hπgα hw
    have hstep : ∀ u v, u ∈ π ∨ u ∈ α → Adj Ω u v → v ∈ π ∨ v ∈ α := by
      intro u v hu huv
      rcases hu with hu | hu
      · have huc : u ∈ common Ω (πc g) := by
          rw [hαc g]
          exact hπα hu
        by_cases hvg : v ∈ πc g
        · exact Or.inr (hπgα hvg)
        · have hvc := hΩ.mem_common_of_adj hK hmax' (hπcΩ g) (hπcm g) (hπct g) (hπΩ hu)
            huc.2 huv hvg
          have hwv : Adj Ω w v := hvc.2 w hw
          by_cases hvπ : v ∈ π
          · exact Or.inl hvπ
          · exact Or.inr (hΩ.mem_common_of_adj hK hmax' hπΩ hπm hπt hwα.1 hwα.2 hwv hvπ)
      · by_cases hvπ : v ∈ π
        · exact Or.inl hvπ
        · exact Or.inr (hΩ.mem_common_of_adj hK hmax' hπΩ hπm hπt hu.1 hu.2 huv hvπ)
    have hreach : ∀ J, Relation.ReflTransGen (Adj Ω) K J → J ∈ π ∨ J ∈ α := by
      intro J hr
      induction hr with
      | refl => exact Or.inr hKα
      | tail _ huv ih => exact hstep _ _ ih huv
    have hall : ∀ J ∈ Ω, J ∈ π ∨ J ∈ α := fun J hJ => hreach J (hconn K hK J hJ)
    have hpresG : ∀ z : G, Preserves π z := by
      intro z
      have hz : z ∈ ⨆ (J : Subgroup G) (_ : J ∈ Ω), J := by
        rw [← sSup_eq_iSup, hgen]
        exact mem_top z
      refine Preserves.of_iSup (p := (· ∈ Ω)) (fun J hJ y hy => ?_) hz
      rcases hall J hJ with hJπ | hJα
      · exact preserves_orbit (le_nbrGroup (hπadj J hJπ) hy)
      · exact preserves_of_le_normalizer (fun Q hQ => (hJα.2 Q hQ).2.2) hy
    obtain ⟨z, hz⟩ := hΩ.trans P₀ (hπΩ (mem_orbit_self _ _)) K hK
    have hKπ : K ∈ π := by
      rw [hz]
      exact (hpresG z P₀).mp (mem_orbit_self _ _)
    exact hαπ K hKα hKπ
  refine ⟨h1, h2, fun P hP => ?_⟩
  obtain ⟨h, rfl⟩ := hΩ.trans K hK P (hπΩ hP)
  have hPαh : rightConjugate K h ∈ (fun A => rightConjugate A h) '' α := ⟨K, hKα, rfl⟩
  refine ⟨h, hPαh, ?_⟩
  have hPc : rightConjugate K h ∈ common Ω (πc h) := by
    rw [hαc h]
    exact hPαh
  have hKP : Adj Ω (rightConjugate K h) K := hΩ.symm K hK _ (hπadj _ hP)
  have hcontra : ∀ M ∈ (fun A => rightConjugate A h) '' α, M ∈ α → False := by
    intro M hMh hMα
    rcases h2 h with heq | hdisj
    · exact hαπ _ (heq ▸ hPαh) hP
    · exact Set.disjoint_left.mp hdisj hMh hMα
  have hKρ : K ∈ πc h := by
    by_contra hKρ
    have hKc := hΩ.mem_common_of_adj hK hmax' (hπcΩ h) (hπcm h) (hπct h) (hπΩ hP) hPc.2 hKP hKρ
    rw [hαc h] at hKc
    exact hcontra K hKc hKα
  intro z hz
  have hzc : z ∈ common Ω (πc h) := by
    rw [hαc h]
    exact hz
  have hKz : Adj Ω K z := hzc.2 K hKρ
  by_contra hzπ
  exact hcontra z hz (hΩ.mem_common_of_adj hK hmax' hπΩ hπm hπt hK hKα.2 hKz hzπ)

end CFSG.ComponentClassification.Asc76.L28

namespace CFSG.ComponentClassification.Asc76

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding

theorem asc76Lemma28 : Asc76Lemma28 := by
  intro G _ _ K₀ Ω adj hgen hsym hconn hD K hK π X hπ hmax α
  have hΩ : L28.Hyp Ω :=
    { conj_mem := by
        rintro _ ⟨a, rfl⟩ g
        exact ⟨a * g, (rightConjugate_mul K₀ a g).symm⟩
      trans := by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        exact ⟨a⁻¹ * b, by rw [rightConjugate_mul, ← mul_assoc, mul_inv_cancel, one_mul]⟩
      symm := hsym
      dich := hD }
  obtain ⟨P₀, hP₀, rfl⟩ := hπ
  exact hΩ.lemma28 hgen hconn hK hP₀ hmax

end CFSG.ComponentClassification.Asc76
