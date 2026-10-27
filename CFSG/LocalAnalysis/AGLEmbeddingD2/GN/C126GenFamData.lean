module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenPerm

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B2F CFSG.Quasithin.E2 Equiv
  Equiv.Perm

variable {N : ℕ}

section Emb

variable {A : Type*} [Group A] (L : Subgroup A) (θ : ↥L ≃* Perm (Fin N))

@[expose] def embL : Perm (Fin N) →* A := L.subtype.comp θ.symm.toMonoidHom

theorem embL_injective : Function.Injective (embL L θ) :=
  L.subtype_injective.comp θ.symm.injective

theorem embL_apply (σ : Perm (Fin N)) : embL L θ σ = ((θ.symm σ : ↥L) : A) := rfl

theorem embL_mem (σ : Perm (Fin N)) : embL L θ σ ∈ L := (θ.symm σ).2

theorem embL_theta (x : ↥L) : embL L θ (θ x) = (x : A) := by
  simp [embL_apply]

variable {L θ}

theorem mem_normalizer_map_embL [Finite A] {x : A} (hx : x ∈ L) {B : Subgroup (Perm (Fin N))}
    (hxB : θ ⟨x, hx⟩ ∈ Subgroup.normalizer (B : Set (Perm (Fin N)))) :
    x ∈ Subgroup.normalizer ((B.map (embL L θ) : Subgroup A) : Set A) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨b, hb, rfl⟩ := hn
  refine ⟨θ ⟨x, hx⟩ * b * (θ ⟨x, hx⟩)⁻¹, (Subgroup.mem_normalizer_iff.1 hxB b).1 hb, ?_⟩
  rw [map_mul, map_mul, map_inv, embL_theta]

end Emb

section Fam

variable {A : Type*} [Group A]

theorem mem_normalizer_of_commute' {B : Subgroup A} {a : A} (h : ∀ c ∈ B, a * c = c * a) :
    a ∈ Subgroup.normalizer (B : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have h2 : a * b * a⁻¹ = b := by
      rw [h b hb]
      group
    rw [h2]
    exact hb
  · intro hb
    have h1 := h _ hb
    have h3 : a * (a * b * a⁻¹) = a * b := by
      rw [h1]
      group
    have h2 : a * b * a⁻¹ = b := mul_left_cancel h3
    rw [h2] at hb
    exact hb

theorem iSup_inf_le_normalizer' (I : Finset (Subgroup A))
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    {L₀ : Subgroup A} (hL₀ : L₀ ∈ I) {B : Subgroup A} (hBL : B ≤ L₀) (E : Subgroup A)
    (hB : L₀ ⊓ E ≤ Subgroup.normalizer (B : Set A)) :
    (⨆ L ∈ I, L ⊓ E) ≤ Subgroup.normalizer (B : Set A) := by
  refine iSup₂_le fun L hL => ?_
  by_cases hLe : L = L₀
  · rw [hLe]
    exact hB
  · intro a ha
    exact mem_normalizer_of_commute' fun c hc => hcomm L hL L₀ hL₀ hLe a ha.1 c (hBL hc)

end Fam

theorem card_closure_c3 {a b c : Fin N} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Nat.card (Subgroup.closure {c3 a b c} : Subgroup (Perm (Fin N))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  exact orderOf_c3 hab hbc hac

theorem mem_normalizer_closure_of_conj {a b c : Fin N} {g : Perm (Fin N)}
    (hg : g * c3 a b c * g⁻¹ ∈ Subgroup.zpowers (c3 a b c)) :
    g ∈ Subgroup.normalizer (Subgroup.closure {c3 a b c} : Set (Perm (Fin N))) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hn' : n ∈ Subgroup.zpowers (c3 a b c) := by
    rw [Subgroup.zpowers_eq_closure]
    exact hn
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn'
  have : g * c3 a b c ^ k * g⁻¹ ∈ Subgroup.zpowers (c3 a b c) := by
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hg k
  rw [Subgroup.zpowers_eq_closure] at this
  exact this

section Main

variable {G : Type} [Group G] [Finite G]

structure GenFamData (N : ℕ) (H T V : Subgroup G) (hV : IsElemAbelian 2 V) where
  hN : 5 ≤ N
  hodd : Odd N
  L : Subgroup (MulAut (IntMod V hV))
  θ : ↥L ≃* Perm (Fin N)
  β : ↥(commV L) ≃* Multiplicative (evenWeight N)
  hβ : SymCoreWith L N θ β
  a : Fin N
  b : Fin N
  p : Fin N
  hab : a ≠ b
  hbp : b ≠ p
  hap : a ≠ p
  C : Subgroup (MulAut (IntMod V hV))
  C_card : Nat.card C = 3
  C_le : C ≤ L
  C_θ : ∀ φ ∈ C, ∃ hφ : φ ∈ L, θ ⟨φ, hφ⟩ ∈ Subgroup.closure {c3 a b p}
  L_J : L ≤ autI hV (thompsonJ H)
  J_N : autI hV (thompsonJ H) ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hV)))
  JT_C : autI hV (thompsonJ T) ≤ Subgroup.normalizer (C : Set (MulAut (IntMod V hV)))
  baum_C : autI hV (baum T) ≤ Subgroup.normalizer (C : Set (MulAut (IntMod V hV)))
  gen_L : ∀ X : Subgroup (MulAut (IntMod V hV)), autI hV T ≤ X → C ≤ X → L ≤ X
  gen_J : ∀ X : Subgroup (MulAut (IntMod V hV)), autI hV T ≤ X → L ≤ X →
    autI hV (thompsonJ H) ≤ X
  t_lift : ∃ φ ∈ autI hV (thompsonJ T), ∃ hφ : φ ∈ L, θ ⟨φ, hφ⟩ = swap a b

theorem autI_le_normalizer_autI' {H K V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hK : H ≤ Subgroup.normalizer (K : Set G)) :
    autI hV H ≤ Subgroup.normalizer (autI hV K : Set (MulAut (IntMod V hV))) := by
  intro φ hφ
  obtain ⟨g, hgH, rfl⟩ := (mem_autI hV).1 hφ
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨k, hkK, rfl⟩ := (mem_autI hV).1 hn
  refine (mem_autI hV).2 ⟨g * k * g⁻¹, ?_, by simp [map_mul, map_inv]⟩
  have := (Subgroup.mem_normalizer_iff.1 (hK hgH) (k : G)).1 hkK
  simpa using this

end Main

end CFSG.AGLEmbeddingD2.GN
