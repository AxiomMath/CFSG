module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Graph

open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

@[expose] def nbrGen (A : Subgroup G → Subgroup G → Prop) (K : Subgroup G) : Subgroup G :=
  ⨆ J ∈ {J : Subgroup G | A K J}, J

@[expose] def orbOf (A : Subgroup G → Subgroup G → Prop) (K J : Subgroup G) :
    Set (Subgroup G) :=
  {M | ∃ l ∈ nbrGen A K, conjSub l J = M}

structure OrbitGraph (A : Subgroup G → Subgroup G → Prop) : Prop where
  symm : ∀ {K J : Subgroup G}, A K J → A J K
  irrefl : ∀ K : Subgroup G, ¬ A K K
  conj : ∀ {K J : Subgroup G} (g : G), A K J → A (conjSub g K) (conjSub g J)
  fix : ∀ {K J : Subgroup G}, A K J → ∀ j ∈ J, conjSub j K = K
  sep : ∀ {K J J' : Subgroup G}, A K J → A K J' → J' ∉ orbOf A K J → A J J'

@[expose] def stabOf (K : Subgroup G) : Subgroup G where
  carrier := {g | conjSub g K = K}
  one_mem' := conjSub_one K
  mul_mem' := fun {a b} ha hb => by
    show conjSub (a * b) K = K
    rw [conjSub_mul, show conjSub b K = K from hb, show conjSub a K = K from ha]
  inv_mem' := fun {a} ha => by
    show conjSub a⁻¹ K = K
    calc conjSub a⁻¹ K = conjSub a⁻¹ (conjSub a K) := by rw [show conjSub a K = K from ha]
      _ = K := conjSub_inv_conjSub a K

@[expose] def setStab (S : Set (Subgroup G)) : Subgroup G where
  carrier := {g | ∀ M, conjSub g M ∈ S ↔ M ∈ S}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb M => by
    rw [conjSub_mul]
    exact (ha (conjSub b M)).trans (hb M)
  inv_mem' := fun {a} ha M => by
    have h1 := ha (conjSub a⁻¹ M)
    rw [conjSub_conjSub_inv] at h1
    exact h1.symm

theorem mem_setStab_of_fix {S : Set (Subgroup G)} {g : G} (hg : ∀ M ∈ S, conjSub g M = M)
    (hg' : ∀ M ∈ S, conjSub g⁻¹ M = M) : g ∈ setStab S := by
  intro M
  constructor
  · intro h
    have := hg' _ h
    rw [conjSub_inv_conjSub] at this
    rw [this]
    exact h
  · intro h
    rw [hg M h]
    exact h

variable {A : Subgroup G → Subgroup G → Prop}

theorem le_nbrGen {K J : Subgroup G} (h : A K J) : J ≤ nbrGen A K :=
  le_biSup (fun J => J) (show J ∈ {J : Subgroup G | A K J} from h)

theorem nbrGen_le {K H : Subgroup G} (h : ∀ J, A K J → J ≤ H) : nbrGen A K ≤ H :=
  iSup₂_le fun J hJ => h J hJ

theorem mem_orbOf_self (K J : Subgroup G) : J ∈ orbOf A K J :=
  ⟨1, (nbrGen A K).one_mem, conjSub_one J⟩

section OG

variable (hG : OrbitGraph A)
include hG

theorem nbrGen_le_stabOf (K : Subgroup G) : nbrGen A K ≤ stabOf K :=
  nbrGen_le fun _ hJ j hj => hG.fix hJ j hj

theorem conjSub_self_of_mem_nbrGen {K : Subgroup G} {l : G} (hl : l ∈ nbrGen A K) :
    conjSub l K = K :=
  nbrGen_le_stabOf hG K hl

theorem adj_conjSub_of_mem_nbrGen {K J : Subgroup G} (hKJ : A K J) {l : G}
    (hl : l ∈ nbrGen A K) : A K (conjSub l J) := by
  have h1 := hG.conj l hKJ
  rwa [conjSub_self_of_mem_nbrGen hG hl] at h1

theorem adj_of_mem_orbOf {K J M : Subgroup G} (hKJ : A K J) (hM : M ∈ orbOf A K J) : A K M := by
  obtain ⟨l, hl, rfl⟩ := hM
  exact adj_conjSub_of_mem_nbrGen hG hKJ hl

omit hG in
theorem orbOf_eq_of_mem {K J M : Subgroup G} (hM : M ∈ orbOf A K J) :
    orbOf A K M = orbOf A K J := by
  obtain ⟨l₀, hl₀, rfl⟩ := hM
  ext N
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l * l₀, (nbrGen A K).mul_mem hl hl₀, conjSub_mul l l₀ J⟩
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l * l₀⁻¹, (nbrGen A K).mul_mem hl ((nbrGen A K).inv_mem hl₀), ?_⟩
    rw [conjSub_mul, conjSub_inv_conjSub]

omit hG in
theorem mem_orbOf_comm {K J M : Subgroup G} (hM : M ∈ orbOf A K J) : J ∈ orbOf A K M := by
  rw [orbOf_eq_of_mem hM]
  exact mem_orbOf_self K J

omit hG in
theorem orbOf_eq_of_mem_of_mem {K J J' M : Subgroup G} (h : M ∈ orbOf A K J)
    (h' : M ∈ orbOf A K J') : orbOf A K J = orbOf A K J' := by
  rw [← orbOf_eq_of_mem h, orbOf_eq_of_mem h']

theorem orbOf_subset_gen {K J : Subgroup G} (hKJ : A K J) :
    orbOf A K J ⊆ {M | ∃ a ∈ ⨆ I ∈ orbOf A K J, I, conjSub a J = M} := by
  set X : Subgroup G := ⨆ I ∈ orbOf A K J, I with hX
  set S : Set (Subgroup G) := {M | ∃ a ∈ X, conjSub a J = M} with hS
  have hXL : X ≤ nbrGen A K := iSup₂_le fun I hI => le_nbrGen (adj_of_mem_orbOf hG hKJ hI)
  have hSorb : S ⊆ orbOf A K J := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, hXL ha, rfl⟩
  have hstab : nbrGen A K ≤ setStab S := by
    refine nbrGen_le fun J' hJ' m hm => ?_
    by_cases hJ'o : J' ∈ orbOf A K J
    · have hmX : m ∈ X := le_biSup (fun I => I) hJ'o hm
      intro M
      constructor
      · rintro ⟨a, ha, haM⟩
        refine ⟨m⁻¹ * a, X.mul_mem (X.inv_mem hmX) ha, ?_⟩
        rw [conjSub_mul, haM, conjSub_inv_conjSub]
      · rintro ⟨a, ha, rfl⟩
        exact ⟨m * a, X.mul_mem hmX ha, conjSub_mul m a J⟩
    · have hfix : ∀ g ∈ J', ∀ M ∈ S, conjSub g M = M := by
        intro g hg M hM
        have hMo : M ∈ orbOf A K J := hSorb hM
        have hKM : A K M := adj_of_mem_orbOf hG hKJ hMo
        have hJ'M : J' ∉ orbOf A K M := by rwa [orbOf_eq_of_mem hMo]
        exact hG.fix (hG.sep hKM hJ' hJ'M) g hg
      exact mem_setStab_of_fix (hfix m hm) (hfix m⁻¹ (J'.inv_mem hm))
  rintro _ ⟨l, hl, rfl⟩
  have hJS : J ∈ S := ⟨1, X.one_mem, conjSub_one J⟩
  exact (hstab hl (J)).mpr hJS

theorem orbOf_eq_of_adj_all [Finite G] {x v J : Subgroup G} (hxJ : A x J)
    (hv : ∀ M ∈ orbOf A x J, A v M)
    (hbound : ∀ J', A v J' → (orbOf A v J').ncard ≤ (orbOf A x J).ncard) :
    orbOf A v J = orbOf A x J := by
  have hsub : orbOf A x J ⊆ orbOf A v J := by
    intro M hM
    obtain ⟨a, ha, rfl⟩ := orbOf_subset_gen hG hxJ hM
    have hle : (⨆ I ∈ orbOf A x J, I) ≤ nbrGen A v := iSup₂_le fun I hI => le_nbrGen (hv I hI)
    exact ⟨a, hle ha, rfl⟩
  have hvJ : A v J := hv J (mem_orbOf_self x J)
  exact (Set.eq_of_subset_of_ncard_le hsub (hbound J hvJ) (Set.toFinite _)).symm

theorem nbrGen_conj (K : Subgroup G) (g : G) :
    nbrGen A (conjSub g K) = conjSub g (nbrGen A K) := by
  apply le_antisymm
  · refine nbrGen_le fun J hJ => ?_
    have h1 : A K (conjSub g⁻¹ J) := by
      have := hG.conj g⁻¹ hJ
      rwa [conjSub_inv_conjSub] at this
    have h2 := conjSub_mono (n := g) (le_nbrGen h1)
    rwa [conjSub_conjSub_inv] at h2
  · intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : nbrGen A K ≤ conjSub g⁻¹ (nbrGen A (conjSub g K)) := by
      refine nbrGen_le fun J hJ => ?_
      have h2 := conjSub_mono (n := g⁻¹) (le_nbrGen (hG.conj g hJ) : conjSub g J ≤ _)
      rwa [conjSub_inv_conjSub] at h2
    have h3 := h1 hx
    rw [mem_conjSub_iff] at h3
    simpa [mul_assoc] using h3

theorem orbOf_conj (K J : Subgroup G) (g : G) :
    orbOf A (conjSub g K) (conjSub g J) = conjSub g '' orbOf A K J := by
  ext M
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [nbrGen_conj hG, mem_conjSub_iff] at hl
    refine ⟨conjSub (g⁻¹ * l * g) J, ⟨_, hl, rfl⟩, ?_⟩
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨g * l * g⁻¹, ?_, ?_⟩
    · rw [nbrGen_conj hG, mem_conjSub_iff]
      simpa [mul_assoc] using hl
    · rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group

theorem ncard_orbOf_conj (K J : Subgroup G) (g : G) :
    (orbOf A (conjSub g K) (conjSub g J)).ncard = (orbOf A K J).ncard := by
  rw [orbOf_conj hG]
  exact Set.ncard_image_of_injective _ (conjSub_injective g)

end OG

end CFSG.ClassicalInvolution.Q3.TC.Graph
