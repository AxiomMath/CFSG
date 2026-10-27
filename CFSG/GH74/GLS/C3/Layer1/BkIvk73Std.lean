module

public import CFSG.GH74.GLS.C3.Layer1.BkIvk73G
public import CFSG.GH74.GLS.C3.Layer1.BkIvk73Q

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

section Data

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

theorem exists_conj_data (hn' : n = 5 ∨ n = 7) (h : IsAConfigW n x K T Q S a)
    (hz : a * x * a⁻¹ ∈ T ⊓ K) (haN : a ∈ NW x) :
    (∀ y ∈ toNWbar x K, (∀ k ∈ toNWbar x K, k * y = y * k) → y = 1) ∧
      ∃ g x' : NWbar x, x' ∈ centralizer ((toNWbar x K : Subgroup (NWbar x)) : Set (NWbar x)) ∧
        x' ≠ 1 ∧ g * x' * g⁻¹ ∈ toNWbar x K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : K ≤ NW x := h.K_le_C.trans (centralizer_le_NW x)
  have hxN : x ∈ NW x := centralizer_le_NW x (mem_centralizer_singleton_iff.2 rfl)
  have hQS : IsSylowOf 2 Q (centralizer (K : Set G)) := isSylowOf_Q_centralizer hn' h
  have hKq : IsQuasisimple ↥K := isQuasisimple_of_isCompIn' h.terminal.2.1
  have hOK := mem_pPrimeCore_of_le hKN (pPrimeCoreOf_le_NW h)
  obtain ⟨eb0⟩ := equiv_map_piO hOK
  obtain ⟨ekbar⟩ := h.kbar
  let ψ : ↥(K.subgroupOf (NW x)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKN
  let e2 : (↥(K.subgroupOf (NW x)) ⧸ pPrimeCore 2 ↥(K.subgroupOf (NW x))) ≃*
      (↥K ⧸ pPrimeCore 2 ↥K) := QuotientGroup.congr _ _ ψ (pPrimeCore_map_iso 2 ψ)
  let eKhat : ↥(toNWbar x K) ≃* alternatingGroup (Fin n) := (eb0.trans e2).trans ekbar
  have hsA : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rcases hn' with rfl | rfl <;> simp)
  have hncA : ∃ a b : ↥(alternatingGroup (Fin n)), a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    exact alt_not_isSolvable n hn'
      ((IsSimpleGroup.comm_iff_isSolvable (G := ↥(alternatingGroup (Fin n)))).1 hc)
  have hcenA : center (alternatingGroup (Fin n)) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hncA).2
  refine ⟨?_, piO ↥(NW x) ⟨a, haN⟩, piO ↥(NW x) ⟨x, hxN⟩, ?_, ?_, ?_⟩
  · intro y hy hyc
    have hmem : eKhat ⟨y, hy⟩ ∈ center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff]
      intro b
      obtain ⟨k, rfl⟩ := eKhat.surjective b
      rw [← map_mul, ← map_mul]
      exact congrArg eKhat (Subtype.ext (hyc k.1 k.2))
    rw [hcenA, Subgroup.mem_bot] at hmem
    have h1 : (⟨y, hy⟩ : ↥(toNWbar x K)) = 1 := eKhat.injective (by rw [hmem, map_one])
    exact congrArg Subtype.val h1
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have h1 : (k : G) * x = x * (k : G) :=
      Subgroup.mem_centralizer_iff.1 (hQS.le h.x_mem_Q) (k : G) hk
    show piO ↥(NW x) k * piO ↥(NW x) ⟨x, hxN⟩ = piO ↥(NW x) ⟨x, hxN⟩ * piO ↥(NW x) k
    rw [← map_mul, ← map_mul]
    exact congrArg (piO ↥(NW x)) (Subtype.ext h1)
  · have hx2 : orderOf (⟨x, hxN⟩ : ↥(NW x)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h.x_order
    intro h1
    have := orderOf_piO_of_orderOf_two hx2
    rw [h1, orderOf_one] at this
    omega
  · have hzN : a * x * a⁻¹ ∈ NW x :=
      (NW x).mul_mem ((NW x).mul_mem haN hxN) ((NW x).inv_mem haN)
    have h1 : piO ↥(NW x) (⟨a, haN⟩ * ⟨x, hxN⟩ * ⟨a, haN⟩⁻¹) =
        piO ↥(NW x) ⟨a, haN⟩ * piO ↥(NW x) ⟨x, hxN⟩ * (piO ↥(NW x) ⟨a, haN⟩)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [← h1]
    exact ⟨⟨a * x * a⁻¹, hzN⟩, hz.2, rfl⟩

end Data

end CFSG.GH74.GLS.C3.Layer1.Bk
