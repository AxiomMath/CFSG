module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9E
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36J

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

variable {X : Type} [Group X]

theorem mul_conj_mem [Finite X] {C N H : Subgroup X} {e₁ : X} (he₁C : e₁ ∈ C)
    (he₁2 : e₁ * e₁ = 1) (hNC : N ≤ C)
    (hNsK : N.map (MulAut.conj e₁).toMonoidHom ≤ UnbalancedLayer.coreActionKernel N)
    (hNO : coreNOf N ≤ coreNOf C) (hCH : centralizer ({e₁} : Set X) ⊓ C ≤ H)
    (hOH : coreNOf C ≤ H) {x : X} (hx : x ∈ N) : x * (e₁ * x * e₁⁻¹) ∈ H := by
  classical
  have he₁inv : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right he₁2
  set y := e₁ * x * e₁⁻¹ with hydef
  have hyK : y ∈ UnbalancedLayer.coreActionKernel N := hNsK ⟨x, hx, rfl⟩
  have ht : y⁻¹ * x⁻¹ * y * x ∈ coreNOf N := by
    have h1 := inv_mem ((UnbalancedLayer.mem_coreActionKernel.mp hyK).2 x hx)
    rwa [show (x⁻¹ * y⁻¹ * x * y)⁻¹ = y⁻¹ * x⁻¹ * y * x by group] at h1
  set c : MulAut X := MulAut.conj e₁ with hcdef
  have hc : ∀ z, c (c z) = z := by
    intro z
    rw [hcdef, MulAut.conj_apply, MulAut.conj_apply, he₁inv]
    calc e₁ * (e₁ * z * e₁) * e₁ = (e₁ * e₁) * z * (e₁ * e₁) := by group
      _ = z := by rw [he₁2]; group
  have hcO : ∀ o ∈ coreNOf C, c o ∈ coreNOf C := by
    intro o ho
    have h1 := le_normalizer_pPrimeCore (le_normalizer he₁C)
    rw [hcdef, MulAut.conj_apply]
    exact (mem_normalizer_iff.mp h1 o).mp ho
  have hcxy : c (x * y) = y * x := by
    rw [hcdef, MulAut.conj_apply, hydef, he₁inv]
    calc e₁ * (x * (e₁ * x * e₁)) * e₁ = e₁ * x * e₁ * x * (e₁ * e₁) := by group
      _ = e₁ * x * e₁ * x := by rw [he₁2, mul_one]
  have hw : (x * y)⁻¹ * c (x * y) ∈ coreNOf C := by
    apply hNO
    rw [hcxy, show (x * y)⁻¹ * (y * x) = y⁻¹ * x⁻¹ * y * x by group]
    exact ht
  obtain ⟨o, ho, hfix⟩ := GrSLit.exists_fixed_mul_of_inv_mul_mem c hc hcO (odd_coreNOf C) hw
  have hoC : o ∈ C := map_subtype_le _ ho
  have hxyC : x * y ∈ C := mul_mem (hNC hx) (mul_mem (mul_mem he₁C (hNC hx)) (inv_mem he₁C))
  have h1 : x * y * o ∈ centralizer ({e₁} : Set X) ⊓ C := by
    refine mem_inf.mpr ⟨?_, mul_mem hxyC hoC⟩
    rw [mem_centralizer_singleton_iff]
    have h2 : e₁ * (x * y * o) * e₁⁻¹ = x * y * o := hfix
    calc x * y * o * e₁ = e₁ * (x * y * o) * e₁⁻¹ * e₁ := by rw [h2]
      _ = e₁ * (x * y * o) := by group
  have h2 := mul_mem (hCH h1) (inv_mem (hOH ho))
  rwa [mul_inv_cancel_right] at h2

theorem conj_mem_of_mul_conj_mem {N H : Subgroup X} {e₁ : X}
    (hNsK : N.map (MulAut.conj e₁).toMonoidHom ≤ UnbalancedLayer.coreActionKernel N)
    (hOH : coreNOf N ≤ H) (hδ : ∀ x ∈ N, x * (e₁ * x * e₁⁻¹) ∈ H) {x k : X} (hx : x ∈ N)
    (hk : k ∈ N) (hkH : k ∈ H) : x * k * x⁻¹ ∈ H := by
  set y := e₁ * x * e₁⁻¹ with hydef
  have hyK : y⁻¹ ∈ UnbalancedLayer.coreActionKernel N := inv_mem (hNsK ⟨x, hx, rfl⟩)
  have ho : k⁻¹ * y * k * y⁻¹ ∈ coreNOf N := by
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp hyK).2 k hk
    rwa [inv_inv] at h1
  have hxo : x * (k⁻¹ * y * k * y⁻¹) * x⁻¹ ∈ coreNOf N :=
    (mem_normalizer_iff.mp (le_normalizer_pPrimeCore (le_normalizer hx)) _).mp ho
  have hxy : x * y ∈ H := hδ x hx
  have h1 := mul_mem (mul_mem (mul_mem hxy hkH) (inv_mem hxy)) (inv_mem (hOH hxo))
  rwa [show x * y * k * (x * y)⁻¹ * (x * (k⁻¹ * y * k * y⁻¹) * x⁻¹)⁻¹ = x * k * x⁻¹ by group]
    at h1

theorem le_of_conj_mem [Finite X] {N H : Subgroup X} (hN : ⁅N, N⁆ = N) {k : ℕ} (hk : 5 ≤ k)
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin k)) (hOH : coreNOf N ≤ H)
    (hnorm : ∀ x ∈ N, ∀ y ∈ N, y ∈ H → x * y * x⁻¹ ∈ H) {c : ↥N} (hcH : (c : X) ∈ H)
    (hcZ : c ∉ Open.fusionZStar ↥N) : N ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := H.subgroupOf N with hKdef
  have hKn : K.Normal := ⟨fun y hy x => hnorm x x.2 y y.2 hy⟩
  set Z := Open.fusionZStar ↥N with hZdef
  set π : ↥N →* alternatingGroup (Fin k) := ψ.toMonoidHom.comp (QuotientGroup.mk' Z) with hπdef
  have hπs : Function.Surjective π := ψ.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hπ : ∀ n, π n = 1 ↔ n ∈ Z := fun n => by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsimple : IsSimpleGroup (alternatingGroup (Fin k)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have hKtop : K.map π = ⊤ := by
    have : (K.map π).Normal := Normal.map hKn π hπs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map π) with h | h
    · exfalso
      apply hcZ
      have h1 : π c ∈ K.map π := ⟨c, hcH, rfl⟩
      rw [h, mem_bot] at h1
      exact (hπ c).mp h1
    · exact h
  set O := pPrimeCore 2 ↥N with hOdef
  set q : ↥N →* ↥N ⧸ O := QuotientGroup.mk' O with hqdef
  have hNb : commutator (↥N ⧸ O) = ⊤ := by
    have hNc : commutator ↥N = ⊤ := by
      apply map_injective N.subtype_injective
      rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
      exact hN
    have h1 := map_commutator (⊤ : Subgroup ↥N) ⊤ q
    rw [← _root_.commutator_def, hNc, map_top_of_surjective q (QuotientGroup.mk'_surjective O),
      ← _root_.commutator_def] at h1
    exact h1.symm
  have hsup : K.map q ⊔ center (↥N ⧸ O) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective O g
    change q n ∈ K.map q ⊔ center (↥N ⧸ O)
    obtain ⟨y, hyK, hyn⟩ : π n ∈ K.map π := hKtop ▸ mem_top _
    have hz : y⁻¹ * n ∈ Z := by
      rw [← hπ, map_mul, map_inv, hyn, inv_mul_cancel]
    have hzc : q (y⁻¹ * n) ∈ center (↥N ⧸ O) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective O g
      have h1 := GSThmB.OddQuot.mem_fusionZStar_iff.mp hz m
      have h2 : q ⁅y⁻¹ * n, m⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2.symm
    have h1 : q n = q y * q (y⁻¹ * n) := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [h1]
    exact mul_mem (mem_sup_left ⟨y, hyK, rfl⟩) (mem_sup_right hzc)
  have hKq : K.map q = ⊤ := eq_top_of_sup_center_of_perfect hNb hsup
  intro n hn
  obtain ⟨y, hyK, hyn⟩ : q ⟨n, hn⟩ ∈ K.map q := hKq ▸ mem_top _
  rw [hqdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hyn
  have h1 : y⁻¹ * ⟨n, hn⟩ ∈ O := QuotientGroup.eq.mp hyn
  have h2 := mul_mem (show (y : X) ∈ H from hyK) (hOH ⟨_, h1, rfl⟩)
  simpa using h2

end CFSG.ComponentClassification.SolMax
