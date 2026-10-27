module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Defs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace Twin1711

variable {G : Type} [Group G]

@[expose] def blockStab (X : Subgroup G) (B : Set (Subgroup G)) : Subgroup G where
  carrier := {x | x ∈ X ∧ conjSub x '' B = B}
  one_mem' := ⟨X.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
    refine ⟨X.mul_mem ha hb, ?_⟩
    have h : conjSub (a * b) '' B = conjSub a '' (conjSub b '' B) := by
      rw [Set.image_image]
      simp only [conjSub_mul]
    rw [h, hB, hA]
  inv_mem' := by
    rintro a ⟨ha, hA⟩
    refine ⟨X.inv_mem ha, ?_⟩
    calc conjSub a⁻¹ '' B = conjSub a⁻¹ '' (conjSub a '' B) := by rw [hA]
      _ = B := by
        rw [Set.image_image]
        simp only [conjSub_inv_conjSub]
        simp

theorem blockStab_le (X : Subgroup G) (B : Set (Subgroup G)) : blockStab X B ≤ X :=
  fun _ hx => hx.1

namespace SandwichData

variable {X R : Subgroup G} {t : G} {B : Set (Subgroup G)} {N : Subgroup G}

theorem twins_le_blockStab (h : SandwichData X R t B N) :
    X ⊓ Subgroup.centralizer ({t} : Set G) ≤ blockStab X B := by
  intro s hs
  refine ⟨hs.1, ?_⟩
  rcases h.block s hs.1 with h1 | h1
  · exact h1
  · exfalso
    have h2 : conjSub s R ∈ conjSub s '' B := ⟨R, h.mem, rfl⟩
    exact Set.disjoint_left.mp h1 h2 (h.twins s hs)

theorem eq_orbit_blockStab (h : SandwichData X R t B N) :
    B = {J | ∃ m ∈ blockStab X B, conjSub m R = J} := by
  ext J
  constructor
  · intro hJ
    obtain ⟨x, hx, rfl⟩ := h.sub hJ
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    rcases h.block x hx with h1 | h1
    · exact h1
    · exfalso
      have h2 : conjSub x R ∈ conjSub x '' B := ⟨R, h.mem, rfl⟩
      exact Set.disjoint_left.mp h1 h2 hJ
  · rintro ⟨m, ⟨_, hmB⟩, rfl⟩
    have h2 : conjSub m R ∈ conjSub m '' B := ⟨R, h.mem, rfl⟩
    rwa [hmB] at h2

theorem blockStab_ne (h : SandwichData X R t B N) : blockStab X B ≠ X := by
  intro hM
  apply h.proper
  ext J
  constructor
  · exact fun hJ => h.sub hJ
  · rintro ⟨x, hx, rfl⟩
    have hxM : x ∈ blockStab X B := by rw [hM]; exact hx
    have h2 : conjSub x R ∈ conjSub x '' B := ⟨R, h.mem, rfl⟩
    rwa [hxM.2] at h2

theorem involution_eq_conj (h : SandwichData X R t B N) (hR : IsUniqueInvolution R t)
    {J : Subgroup G} (hJ : J ∈ B) {u : G} (hu : IsUniqueInvolution J u) :
    ∃ m ∈ blockStab X B, u = m * t * m⁻¹ := by
  have h1 := h.eq_orbit_blockStab
  rw [h1] at hJ
  obtain ⟨m, hm, rfl⟩ := hJ
  exact ⟨m, hm, (hR.conj m).eq hu |>.symm⟩

theorem inv_mem_conj (h : SandwichData X R t B N) (hR : IsUniqueInvolution R t) {x : G}
    (hx : x ∈ X) (hxN : x * t * x⁻¹ ∈ N) : ∃ m ∈ blockStab X B, x * t * x⁻¹ = m * t * m⁻¹ := by
  obtain ⟨J, hJ, hu⟩ := h.inv x hx hxN
  exact h.involution_eq_conj hR hJ hu

end SandwichData

@[expose] def twinClosure (X R : Subgroup G) (t : G) : Subgroup G :=
  ⨆ s ∈ X ⊓ Subgroup.centralizer ({t} : Set G), conjSub s R

theorem conjSub_le_twinClosure {X R : Subgroup G} {t s : G}
    (hs : s ∈ X ⊓ Subgroup.centralizer ({t} : Set G)) : conjSub s R ≤ twinClosure X R t :=
  le_iSup₂ (f := fun s (_ : s ∈ X ⊓ Subgroup.centralizer ({t} : Set G)) => conjSub s R) s hs

theorem SandwichData.twinClosure_le {X R : Subgroup G} {t : G} {B : Set (Subgroup G)}
    {N : Subgroup G} (h : SandwichData X R t B N) : twinClosure X R t ≤ N :=
  iSup₂_le fun s hs => h.twins_le s hs

theorem false_of_generating {X R : Subgroup G} {t : G} {B : Set (Subgroup G)}
    {N : Subgroup G} (h : SandwichData X R t B N) (hR : IsUniqueInvolution R t)
    {y : G} (hy : y ∈ X) (hyV : y * t * y⁻¹ ∈ twinClosure X R t)
    (hgen : ∀ M : Subgroup G, X ⊓ Subgroup.centralizer ({t} : Set G) ≤ M → M ≤ X → y ∈ M →
      M = X) : False := by
  obtain ⟨m, hm, he⟩ := h.inv_mem_conj hR hy (h.twinClosure_le hyV)
  have hT : m⁻¹ * y ∈ X ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine Subgroup.mem_inf.2 ⟨X.mul_mem (X.inv_mem hm.1) hy, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : m⁻¹ * y * t = t * (m⁻¹ * y) := by
      have h1 : y * t = m * t * m⁻¹ * y := by
        calc y * t = (y * t * y⁻¹) * y := by group
          _ = m * t * m⁻¹ * y := by rw [he]
      calc m⁻¹ * y * t = m⁻¹ * (y * t) := by group
        _ = m⁻¹ * (m * t * m⁻¹ * y) := by rw [h1]
        _ = t * (m⁻¹ * y) := by group
    exact this
  have hyM : y ∈ blockStab X B := by
    have : y = m * (m⁻¹ * y) := by group
    rw [this]
    exact (blockStab X B).mul_mem hm (h.twins_le_blockStab hT)
  exact h.blockStab_ne (hgen _ h.twins_le_blockStab (blockStab_le X B) hyM)

end Twin1711

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
