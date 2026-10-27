module

public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclRFrame
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6P1x

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld
open CFSG.LieType.Steinberg.Adjoint (iform)
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime]

namespace ETCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem mem_center_of_psi_mem_locImg (c : ETCtx p f .E7 0 Ω K z) {r : TypeE8.K7 p f}
    (hr : c.d.ψ r ∈ locImg Ω z K) : r ∈ Subgroup.center (TypeE8.K7 p f) := by
  have hQ : c.d.ψ r ∈ c.d.Q₀ := c.locImg_self_le_Q₀ hr
  have := c.hY.perfK
  refine mem_center_of_comm_mem_center fun s => c.d.ker_le ?_
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact c.d.commutes _ hQ _ ⟨s, rfl⟩

omit [Finite G] in
theorem locElt_mem_locImg_of_eq (c : ETCtx p f .E7 0 Ω K z) {y : G} (hy : y ∈ locLayer Ω z)
    (h : y = z) : locElt Ω z y hy ∈ locImg Ω z K := by
  subst h
  exact locElt_mem_locImg (le_centralizingLayer c.hKz) c.hz.mem

theorem le_centralizer_mul_iff (c : ETCtx p f .E7 0 Ω K z) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) {A : Subgroup (TypeE8.K7 p f)}
    (hA : A ∈ TypeE8.F7 p f) (hNA : locImg Ω z N = A.map c.d.ψ) {w₁ w₂ : G}
    (hw₁ : w₁ ∈ locLayer Ω z) (hw₂ : w₂ ∈ locLayer Ω z) {r₁ r₂ : TypeE8.K7 p f}
    (hr₁ : c.d.ψ r₁ = locElt Ω z w₁ hw₁) (hr₂ : c.d.ψ r₂ = locElt Ω z w₂ hw₂) :
    N ≤ Subgroup.centralizer ({w₁ * w₂} : Set G) ↔
      A ≤ Subgroup.centralizer ({r₁ * r₂} : Set (TypeE8.K7 p f)) := by
  have hmul : Gaps.locMk Ω z ⟨w₁ * w₂, (locLayer Ω z).mul_mem hw₁ hw₂⟩ = c.d.ψ (r₁ * r₂) := by
    rw [map_mul, hr₁, hr₂, locElt_mul]
    rfl
  have h1 := Gaps.le_centralizer_iff_locImg c.hΩ c.hP1 hN
    ⟨w₁ * w₂, (locLayer Ω z).mul_mem hw₁ hw₂⟩
  have h2 := Gaps.le_centralizer_iff_map c.d.ψ c.d.ker_le (c.hY.perfR A hA) (r₁ * r₂)
  rw [hmul, hNA] at h1
  exact h1.trans h2.symm

variable {c : ETCtx p f .E7 0 Ω K z} {g : TypeE8.K7 p f} {δ : Fin 7 → ℤ} {N : Subgroup G}

theorem IsFrameMember.exists_involution (hB8 : TypeE8.E7FrameRelations p f)
    (h : IsFrameMember c g δ N) (hδ : δ ∈ (TypeE8.D7 p f).roots) {w : G}
    (hw : IsClassicalMember p f N w) :
    ∃ r ∈ conjSub g (TypeE8.Rroot p f δ), orderOf r = 2 ∧
      c.d.ψ r = locElt Ω z w (le_centralizingLayer h.1 hw.mem) := by
  obtain ⟨r, ⟨hr, hr2⟩, hψ⟩ := c.exists_involution_of_fund h.1 (hB8 g δ δ hδ hδ).1 h.2.2 hw
  exact ⟨r, hr, hr2, hψ⟩

end ETCtx

end CFSG.ClassicalInvolution.RouteD

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.Adjoint (iform)
open CFSG.ClassicalInvolution.RouteD.NonClassical (card_closure_insert_eq
  eq_one_or_eq_of_mem_closure_singleton mem_closure_insert_involution)

variable {p f : ℕ} [Fact p.Prime]

section Triple

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem card_closure_triple (c : ETCtx p f .E7 0 Ω K z) (hB9 : E7FrameInvolutions p f)
    {g : K7 p f} {γ₁ γ₂ : Fin 7 → ℤ} (hγ₁ : γ₁ ∈ (D7 p f).roots)
    (hγ₂ : γ₂ ∈ (D7 p f).roots) (ho : iform (τ := .E7) γ₁ γ₂ = 0) {W₁ W₂ : Subgroup G}
    (h₁ : ETCtx.IsFrameMember c g γ₁ W₁) (h₂ : ETCtx.IsFrameMember c g γ₂ W₂) {w₁ w₂ : G}
    (hw₁ : IsClassicalMember p f W₁ w₁) (hw₂ : IsClassicalMember p f W₂ w₂)
    {r₁ r₂ : K7 p f} (hr₁ : r₁ ∈ conjSub g (Rroot p f γ₁)) (hr₂ : r₂ ∈ conjSub g (Rroot p f γ₂))
    (ho₁ : orderOf r₁ = 2) (ho₂ : orderOf r₂ = 2)
    (hψ₁ : c.d.ψ r₁ = locElt Ω z w₁ (le_centralizingLayer h₁.1 hw₁.mem))
    (hψ₂ : c.d.ψ r₂ = locElt Ω z w₂ (le_centralizingLayer h₂.1 hw₂.mem))
    (hW₁₂ : Commutes W₁ W₂) :
    Nat.card (Subgroup.closure ({z, w₁, w₂} : Set G)) = 8 := by
  have hz2 : z * z = 1 := DeltaClosure.sq_eq_one c.hz
  have hw₁2 : w₁ * w₁ = 1 := DeltaClosure.sq_eq_one hw₁
  have hw₂2 : w₂ * w₂ = 1 := DeltaClosure.sq_eq_one hw₂
  have hzw₁ : z * w₁ = w₁ * z := h₁.commutes_K z c.hz.mem w₁ hw₁.mem
  have hzw₂ : z * w₂ = w₂ * z := h₂.commutes_K z c.hz.mem w₂ hw₂.mem
  have hw₁₂ : w₁ * w₂ = w₂ * w₁ := hW₁₂ w₁ hw₁.mem w₂ hw₂.mem
  obtain ⟨hn₁, hn₂, hn₁₂, -⟩ := hB9 g γ₁ γ₂ hγ₁ hγ₂ ho r₁ hr₁ r₂ hr₂ ho₁ ho₂
  have hz1 : z ≠ 1 := by
    intro h
    have := c.hz.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hw₁1 : w₁ ≠ 1 := by
    intro h
    have := hw₁.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hw₂1 : w₂ ≠ 1 := by
    intro h
    have := hw₂.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hw₁₂ne : w₁ ≠ w₂ := by
    intro h
    apply hn₁₂
    have e : c.d.ψ r₁ = c.d.ψ r₂ := by
      rw [hψ₁, hψ₂]
      subst h
      rfl
    have hr₁sq : r₁ * r₁ = 1 := by
      rw [← sq]
      exact ho₁ ▸ pow_orderOf_eq_one r₁
    apply c.d.ker_le
    rw [MonoidHom.mem_ker, map_mul, ← e, ← map_mul, hr₁sq, map_one]
  have hz₁ : z ≠ w₁ := fun h => hn₁ (c.mem_center_of_psi_mem_locImg (by
    rw [hψ₁]
    exact c.locElt_mem_locImg_of_eq _ h.symm))
  have hz₂ : z ≠ w₂ := fun h => hn₂ (c.mem_center_of_psi_mem_locImg (by
    rw [hψ₂]
    exact c.locElt_mem_locImg_of_eq _ h.symm))
  have hz₁₂ : z ≠ w₁ * w₂ := fun h => hn₁₂ (c.mem_center_of_psi_mem_locImg (by
    rw [map_mul, hψ₁, hψ₂, locElt_mul]
    exact c.locElt_mem_locImg_of_eq _ h.symm))
  have hN1 : w₁ ∉ Subgroup.closure ({w₂} : Set G) := by
    intro h
    rcases eq_one_or_eq_of_mem_closure_singleton hw₂2 h with h1 | h1
    · exact hw₁1 h1
    · exact hw₁₂ne h1
  have hN2 : z ∉ Subgroup.closure (insert w₁ ({w₂} : Set G)) := by
    intro h
    rcases mem_closure_insert_involution hw₁2 (S := ({w₂} : Set G)) (by
      intro s hs
      rw [Set.mem_singleton_iff.mp hs]
      exact hw₁₂) h with h1 | ⟨g', hg, hzg⟩
    · rcases eq_one_or_eq_of_mem_closure_singleton hw₂2 h1 with h2 | h2
      · exact hz1 h2
      · exact hz₂ h2
    · rcases eq_one_or_eq_of_mem_closure_singleton hw₂2 hg with h2 | h2
      · rw [h2, one_mul] at hzg
        exact hz₁ hzg
      · rw [h2] at hzg
        exact hz₁₂ (hzg.trans hw₁₂.symm)
  have c1 : Nat.card (Subgroup.closure ({w₂} : Set G)) = 2 := by
    have h := card_closure_insert_eq (S := (∅ : Set G)) hw₂2
      (fun s hs => absurd hs (Set.notMem_empty s))
      (by rw [Subgroup.closure_empty, Subgroup.mem_bot]; exact hw₂1)
    rwa [insert_empty_eq, Subgroup.closure_empty, Subgroup.card_bot, mul_one] at h
  have c2 : Nat.card (Subgroup.closure (insert w₁ ({w₂} : Set G))) = 4 := by
    rw [card_closure_insert_eq hw₁2 (S := ({w₂} : Set G)) (by
      intro s hs
      rw [Set.mem_singleton_iff.mp hs]
      exact hw₁₂) hN1, c1]
  rw [card_closure_insert_eq hz2 (S := insert w₁ ({w₂} : Set G)) (by
    rintro s (rfl | hs)
    · exact hzw₁
    · rw [Set.mem_singleton_iff.mp hs]
      exact hzw₂) hN2, c2]

end Triple

end CFSG.ClassicalInvolution.RouteD.TypeE8
