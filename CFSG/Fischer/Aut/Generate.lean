module

public import Mathlib.Order.Atoms
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.Fischer

variable {G G' : Type*} [Group G] [Group G']

theorem sup_eq_top_of_maximal {M L L₁ H H₁ : Subgroup G} (hM : IsCoatom M) (hL : L ≤ M)
    (hL₁ : L₁ ≤ M) (hLmax : ∀ K : Subgroup G, L ≤ K → K ≤ M → K = L ∨ K = M) (hne : ¬ L₁ ≤ L)
    (hLH : L ≤ H) (hL₁H₁ : L₁ ≤ H₁) {e : G} (heH : e ∈ H) (heM : e ∉ M) : H ⊔ H₁ = ⊤ := by
  have h1 : L ⊔ L₁ = M := by
    rcases hLmax (L ⊔ L₁) le_sup_left (sup_le hL hL₁) with h | h
    · exact absurd (h ▸ le_sup_right) hne
    · exact h
  have h2 : M ≤ H ⊔ H₁ := h1 ▸ sup_le_sup hLH hL₁H₁
  have h3 : M < H ⊔ H₁ :=
    lt_of_le_of_ne h2 fun h => heM (h ▸ Subgroup.mem_sup_left heH)
  exact hM.2 _ h3

theorem maximal_of_mulEquiv {M : Subgroup G} {Q : Subgroup G'} (φ : M ≃* Q) {L : Subgroup G}
    (hLM : L ≤ M) {C : Subgroup Q} (hC : IsCoatom C) (hφ : ∀ m : M, φ m ∈ C ↔ (m : G) ∈ L) :
    ∀ K : Subgroup G, L ≤ K → K ≤ M → K = L ∨ K = M := by
  have hLC : (L.subgroupOf M).map φ.toMonoidHom = C := by
    ext y
    obtain ⟨m, rfl⟩ := φ.surjective y
    constructor
    · rintro ⟨m', hm', he⟩
      rw [φ.injective he] at hm'
      exact (hφ m).2 hm'
    · intro h
      exact ⟨m, (hφ m).1 h, rfl⟩
  intro K hLK hKM
  have hle : C ≤ (K.subgroupOf M).map φ.toMonoidHom := by
    rw [← hLC]
    exact Subgroup.map_mono (Subgroup.comap_mono hLK)
  rcases eq_or_lt_of_le hle with h | h
  · left
    rw [← hLC] at h
    have h' := Subgroup.map_injective φ.injective h
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hLM, inf_eq_left.2 hKM] at h'
    exact h'.symm
  · right
    have htop := hC.2 _ h
    have h' : K.subgroupOf M = ⊤ := by
      apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      rw [htop, Subgroup.map_top_of_surjective _ φ.surjective]
    rw [Subgroup.subgroupOf_eq_top] at h'
    exact le_antisymm hKM h'

@[expose] def conjCentralizer (c d : G) :
    Subgroup.centralizer ({d} : Set G) ≃* Subgroup.centralizer ({c * d * c⁻¹} : Set G) where
  toFun x := ⟨c * x * c⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2
    calc c * (x : G) * c⁻¹ * (c * d * c⁻¹) = c * ((x : G) * d) * c⁻¹ := by group
      _ = c * (d * (x : G)) * c⁻¹ := by rw [hx]
      _ = c * d * c⁻¹ * (c * (x : G) * c⁻¹) := by group⟩
  invFun y := ⟨c⁻¹ * y * c, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
    calc c⁻¹ * (y : G) * c * d = c⁻¹ * ((y : G) * (c * d * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * d * c⁻¹) * (y : G)) * c := by rw [hy]
      _ = d * (c⁻¹ * (y : G) * c) := by group⟩
  left_inv x := Subtype.ext (by show c⁻¹ * (c * (x : G) * c⁻¹) * c = x; group)
  right_inv y := Subtype.ext (by show c * (c⁻¹ * (y : G) * c) * c⁻¹ = y; group)
  map_mul' x y := Subtype.ext (by
    show c * ((x : G) * y) * c⁻¹ = c * x * c⁻¹ * (c * y * c⁻¹)
    group)

theorem commutator_centralizer_conj (c d : G)
    (h : commutator (Subgroup.centralizer ({d} : Set G)) = ⊤) :
    commutator (Subgroup.centralizer ({c * d * c⁻¹} : Set G)) = ⊤ := by
  have hs := (conjCentralizer c d).surjective
  have e : (commutator (Subgroup.centralizer ({d} : Set G))).map
      (conjCentralizer c d).toMonoidHom =
        commutator (Subgroup.centralizer ({c * d * c⁻¹} : Set G)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hs]
  rw [← e, h, Subgroup.map_top_of_surjective _ hs]

theorem commutator_map_eq_top {H : Type*} [Group H] (f : G →* H) (hf : Function.Injective f)
    {K : Subgroup G} (h : commutator K = ⊤) : commutator (K.map f) = ⊤ := by
  have hs := (K.equivMapOfInjective f hf).surjective
  have e : (commutator K).map (K.equivMapOfInjective f hf).toMonoidHom =
      commutator (K.map f) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hs]
  rw [← e, h, Subgroup.map_top_of_surjective _ hs]

theorem card_centralizer_conj (c d : G) :
    Nat.card (Subgroup.centralizer ({c * d * c⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({d} : Set G)) :=
  (Nat.card_congr (conjCentralizer c d).toEquiv).symm

end CFSG.Fischer
