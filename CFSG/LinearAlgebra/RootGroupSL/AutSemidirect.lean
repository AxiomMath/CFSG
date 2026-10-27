module

public import CFSG.LinearAlgebra.RootGroupSL.AutSemidirectAux
import Mathlib.Tactic.Group

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {S G : Type} [Group S] [Group G] [Finite S]

open AutSemidirect

theorem exists_conj_of_aut_semidirect (ε : S →* G) (hε : Function.Injective ε)
    (A K J : Subgroup S) (Sg Yg : Subgroup G) (hAK : A ⊓ K = ⊥)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hJK : J ≤ K) (hCA : ∀ a ∈ A, (∀ j ∈ J, j * a = a * j) → a = 1)
    (hSA : ∀ s ∈ Sg, ∀ a ∈ A, ∃ a' ∈ A, ε a' = s * ε a * s⁻¹)
    (hSK : ∀ s ∈ Sg, ∀ g ∈ K, ∃ g' ∈ K, ε g' = s * ε g * s⁻¹)
    (hSJ : ∀ s ∈ Sg, ∀ j ∈ J, s * ε j = ε j * s)
    (hYA : ∀ y ∈ Yg, ∀ a ∈ A, ∃ a' ∈ A, ε a' = y * ε a * y⁻¹)
    (hYK : ∀ y ∈ Yg, ∀ g ∈ K, y * ε g = ε g * y)
    (H12 : ∀ β : MulAut ↥K, (∀ j : ↥K, (j : S) ∈ J → β j = j) →
      ∃ s ∈ Sg, ∀ g : ↥K, ε ((β g : ↥K) : S) = s * ε (g : S) * s⁻¹)
    (EndA : ∀ γ : MulAut ↥A,
      (∀ (g : ↥K) (a : ↥A), ((γ ⟨(g : S) * (a : S) * (g : S)⁻¹, hKA g g.2 a a.2⟩ : ↥A) : S) =
        (g : S) * ((γ a : ↥A) : S) * (g : S)⁻¹) →
      ∃ y ∈ Yg, ∀ a : ↥A, ε ((γ a : ↥A) : S) = y * ε (a : S) * y⁻¹)
    (H1 : ∀ δ : ↥K → ↥A,
      (∀ g h : ↥K, ((δ (g * h) : ↥A) : S) = (δ g : S) * ((g : S) * (δ h : S) * (g : S)⁻¹)) →
      ∃ a : ↥A, ∀ g : ↥K, (δ g : S) = (a : S) * ((g : S) * (a : S)⁻¹ * (g : S)⁻¹))
    (α : MulAut ↥(A ⊔ K)) (hαJ : ∀ j : ↥(A ⊔ K), (j : S) ∈ J → α j = j)
    (hαA : ∀ x : ↥(A ⊔ K), (x : S) ∈ A ↔ ((α x : ↥(A ⊔ K)) : S) ∈ A) :
    ∃ s ∈ Sg, ∃ y ∈ Yg, ∀ p : ↥(A ⊔ K),
      ε ((α p : ↥(A ⊔ K)) : S) = s * y * ε (p : S) * (s * y)⁻¹ := by
  let inclA : ↥A →* ↥(A ⊔ K) := Subgroup.inclusion le_sup_left
  let inclK : ↥K →* ↥(A ⊔ K) := Subgroup.inclusion le_sup_right
  let βHom : ↥K →* ↥K :=
    (projKHom A K hAK hKA).comp ((α : ↥(A ⊔ K) →* ↥(A ⊔ K)).comp inclK)
  have hβHom_apply : ∀ k : ↥K, βHom k = projK A K hKA (α (inclK k)) := fun _ => rfl
  have hβHom_ker : ∀ k : ↥K, βHom k = 1 → k = 1 := by
    intro k hk
    have hkval : ((projK A K hKA (α (inclK k)) : ↥K) : S) = 1 := by
      have := congrArg (fun x : ↥K => (x : S)) hk
      rwa [hβHom_apply] at this
    obtain ⟨a, ha, haeq⟩ := projK_spec A K hKA (α (inclK k))
    have hαkA : ((α (inclK k) : ↥(A ⊔ K)) : S) ∈ A := by
      have hval : ((α (inclK k) : ↥(A ⊔ K)) : S) = a := by
        rw [← haeq, hkval, mul_one]
      rw [hval]; exact ha
    have hkA : (k : S) ∈ A := (hαA (inclK k)).mpr hαkA
    have hkbot : (k : S) ∈ A ⊓ K := ⟨hkA, k.2⟩
    rw [hAK] at hkbot
    exact Subtype.ext (by simpa using hkbot)
  have hβHom_inj : Function.Injective βHom := by
    intro k k' hkk'
    have h1 : βHom (k * k'⁻¹) = 1 := by
      rw [map_mul, hkk', map_inv, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hβHom_ker _ h1)
  let β : MulAut ↥K := MulEquiv.ofBijective βHom (Finite.injective_iff_bijective.mp hβHom_inj)
  have hβ_apply : ∀ k : ↥K, β k = projK A K hKA (α (inclK k)) := by
    intro k
    change βHom k = projK A K hKA (α (inclK k))
    rw [hβHom_apply]
  have hβJ : ∀ j : ↥K, (j : S) ∈ J → β j = j := by
    intro j hj
    have hαj : α (inclK j) = inclK j := hαJ (inclK j) hj
    have hproj : β j = projK A K hKA (inclK j) := by
      change βHom j = projK A K hKA (inclK j)
      rw [hβHom_apply, hαj]
    rw [hproj]
    apply Subtype.ext
    exact (projK_unique A K hAK hKA (inclK j) j.2
      ⟨1, A.one_mem, by simp [inclK]⟩).symm
  obtain ⟨s, hsSg, hs_conj⟩ := H12 β hβJ
  have hsA : ∀ a ∈ A, ∃ a' ∈ A, ε a' = s⁻¹ * ε a * s⁻¹⁻¹ :=
    fun a ha => hSA s⁻¹ (Sg.inv_mem hsSg) a ha
  have hsK : ∀ g ∈ K, ∃ g' ∈ K, ε g' = s⁻¹ * ε g * s⁻¹⁻¹ :=
    fun g hg => hSK s⁻¹ (Sg.inv_mem hsSg) g hg
  let α₁ : MulAut ↥(A ⊔ K) := conjAut A K hKA hε s⁻¹ hsA hsK * α
  have hα₁_spec : ∀ p : ↥(A ⊔ K),
      ε ((α₁ p : ↥(A ⊔ K)) : S) = s⁻¹ * ε ((α p : ↥(A ⊔ K)) : S) * s := by
    intro p
    have h := conjAut_spec A K hKA hε s⁻¹ (hsA := hsA) (hsK := hsK) (α p)
    simpa [α₁, MulAut.mul_apply] using h
  have hα₁_j : ∀ j : ↥(A ⊔ K), (j : S) ∈ J → α₁ j = j := by
    intro j hj
    apply Subtype.ext
    apply hε
    rw [hα₁_spec, hαJ j hj]
    have hcomm : s * ε (j : S) = ε (j : S) * s := hSJ s hsSg j hj
    calc s⁻¹ * ε (j : S) * s = s⁻¹ * (ε (j : S) * s) := by group
      _ = s⁻¹ * (s * ε (j : S)) := by rw [hcomm.symm]
      _ = ε (j : S) := by group
  have hδ_exists : ∀ k : ↥K, ∃ a : ↥A,
      ((α₁ (inclK k) : ↥(A ⊔ K)) : S) = (a : S) * (k : S) := by
    intro k
    obtain ⟨a, ha, haeq⟩ := projK_spec A K hKA (α (inclK k))
    obtain ⟨a', ha', ha'eq⟩ := hSA s⁻¹ (Sg.inv_mem hsSg) a ha
    refine ⟨⟨a', ha'⟩, ?_⟩
    apply hε
    rw [hα₁_spec, map_mul, ← haeq, map_mul, ha'eq]
    have hb : ε ((projK A K hKA (α (inclK k)) : ↥K) : S) = s * ε (k : S) * s⁻¹ := by
      rw [← hβ_apply k]
      exact hs_conj k
    rw [hb]
    group
  let δ : ↥K → ↥A := fun k => Classical.choose (hδ_exists k)
  have hδ_spec : ∀ k : ↥K,
      ((α₁ (inclK k) : ↥(A ⊔ K)) : S) = (δ k : S) * (k : S) :=
    fun k => Classical.choose_spec (hδ_exists k)
  have hδ_cocycle : ∀ g h : ↥K,
      ((δ (g * h) : ↥A) : S) = (δ g : S) * ((g : S) * (δ h : S) * (g : S)⁻¹) := by
    intro g h
    have hmul : ((α₁ (inclK (g * h)) : ↥(A ⊔ K)) : S) =
        ((α₁ (inclK g) : ↥(A ⊔ K)) : S) * ((α₁ (inclK h) : ↥(A ⊔ K)) : S) := by
      have h1 : inclK (g * h) = inclK g * inclK h := map_mul inclK g h
      rw [h1, map_mul]
      rfl
    rw [hδ_spec (g * h), hδ_spec g, hδ_spec h] at hmul
    have hmul' : (δ (g * h) : S) * (g : S) * (h : S) =
        (δ g : S) * (g : S) * (δ h : S) * (h : S) := by
      have hgh : ((g * h : ↥K) : S) = (g : S) * (h : S) := rfl
      rw [hgh] at hmul
      simpa only [mul_assoc] using hmul
    have h2 : (δ (g * h) : S) * (g : S) = (δ g : S) * (g : S) * (δ h : S) := by
      have hh : ((δ (g * h) : S) * (g : S)) * (h : S) =
          ((δ g : S) * (g : S) * (δ h : S)) * (h : S) := by
        simpa only [mul_assoc] using hmul'
      exact mul_right_cancel hh
    have h3 : (δ (g * h) : S) = (δ g : S) * (g : S) * (δ h : S) * (g : S)⁻¹ := by
      calc (δ (g * h) : S) = (δ (g * h) : S) * (g : S) * (g : S)⁻¹ := by group
        _ = ((δ g : S) * (g : S) * (δ h : S)) * (g : S)⁻¹ := by rw [h2]
        _ = (δ g : S) * (g : S) * (δ h : S) * (g : S)⁻¹ := by group
    rw [h3]; group
  have hα₁_A : ∀ a : ↥A, ((α₁ (inclA a) : ↥(A ⊔ K)) : S) ∈ A := by
    intro a
    have hαa : ((α (inclA a) : ↥(A ⊔ K)) : S) ∈ A := (hαA (inclA a)).mp a.2
    have := conjAut_mem_A A K hKA hε s⁻¹ (hsA := hsA) (hsK := hsK) hαa
    simpa [α₁, MulAut.mul_apply] using this
  let γfun : ↥A → ↥A := fun a => ⟨α₁ (inclA a), hα₁_A a⟩
  have hγfun_mul : ∀ a b : ↥A, γfun (a * b) = γfun a * γfun b := by
    intro a b
    apply Subtype.ext
    show ((α₁ (inclA (a * b)) : ↥(A ⊔ K)) : S) =
        ((α₁ (inclA a) : ↥(A ⊔ K)) : S) * ((α₁ (inclA b) : ↥(A ⊔ K)) : S)
    rw [map_mul inclA a b, map_mul α₁ (inclA a) (inclA b)]
    rfl
  let γHom : ↥A →* ↥A := MonoidHom.mk' γfun hγfun_mul
  have hγHom_inj : Function.Injective γHom := by
    intro a b hab
    change γfun a = γfun b at hab
    have h1 : ((α₁ (inclA a) : ↥(A ⊔ K)) : S) = ((α₁ (inclA b) : ↥(A ⊔ K)) : S) := by
      have := congrArg (fun x : ↥A => (x : S)) hab
      simpa [γfun] using this
    have h1' : α₁ (inclA a) = α₁ (inclA b) := Subtype.ext h1
    have h2 : inclA a = inclA b := α₁.injective h1'
    have h3 : (a : S) = (b : S) := by
      have := congrArg (fun x : ↥(A ⊔ K) => (x : S)) h2
      simpa [inclA, Subgroup.coe_inclusion] using this
    exact Subtype.ext h3
  let γ : MulAut ↥A := MulEquiv.ofBijective γHom (Finite.injective_iff_bijective.mp hγHom_inj)
  have hγ_apply : ∀ a : ↥A, ((γ a : ↥A) : S) = ((α₁ (inclA a) : ↥(A ⊔ K)) : S) :=
    fun _ => rfl
  have hγ_comm : ∀ (g : ↥K) (a : ↥A),
      ((γ ⟨(g : S) * (a : S) * (g : S)⁻¹, hKA g g.2 a a.2⟩ : ↥A) : S) =
        (g : S) * ((γ a : ↥A) : S) * (g : S)⁻¹ := by
    intro g a
    set ca : ↥A := ⟨(g : S) * (a : S) * (g : S)⁻¹, hKA g g.2 a a.2⟩ with hca_def
    have hca : inclA ca = inclK g * inclA a * (inclK g)⁻¹ := by
      apply Subtype.ext
      show (ca : S) = (g : S) * (a : S) * (g : S)⁻¹
      rw [hca_def]
    have hkey : ((α₁ (inclA ca) : ↥(A ⊔ K)) : S) =
        (δ g : S) * (g : S) * ((γ a : ↥A) : S) * ((δ g : S) * (g : S))⁻¹ := by
      rw [hca]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hδ_spec g]
      rw [← hγ_apply a]
    have hfinal : (δ g : S) * (g : S) * ((γ a : ↥A) : S) * ((δ g : S) * (g : S))⁻¹ =
        (g : S) * ((γ a : ↥A) : S) * (g : S)⁻¹ := by
      have hd : (δ g : S) ∈ A := (δ g).2
      have hc : (g : S) * ((γ a : ↥A) : S) * (g : S)⁻¹ ∈ A :=
        hKA g g.2 (γ a) (γ a).2
      have hcomm : (δ g : S) * ((g : S) * ((γ a : ↥A) : S) * (g : S)⁻¹) =
          ((g : S) * ((γ a : ↥A) : S) * (g : S)⁻¹) * (δ g : S) := hAc _ hd _ hc
      rw [mul_inv_rev]
      rw [show (δ g : S) * (g : S) * ((γ a : ↥A) : S) * ((g : S)⁻¹ * (δ g : S)⁻¹) =
          (δ g : S) * ((g : S) * ((γ a : ↥A) : S) * (g : S)⁻¹) * (δ g : S)⁻¹ from by
        group]
      rw [hcomm]; group
    calc ((γ ca : ↥A) : S) = ((α₁ (inclA ca) : ↥(A ⊔ K)) : S) := hγ_apply ca
      _ = (δ g : S) * (g : S) * ((γ a : ↥A) : S) * ((δ g : S) * (g : S))⁻¹ := hkey
      _ = (g : S) * ((γ a : ↥A) : S) * (g : S)⁻¹ := hfinal
  obtain ⟨y, hyY, hy⟩ := EndA γ hγ_comm
  have hyA : ∀ a ∈ A, ∃ a' ∈ A, ε a' = y⁻¹ * ε a * y⁻¹⁻¹ :=
    fun a ha => hYA y⁻¹ (Yg.inv_mem hyY) a ha
  have hyK : ∀ g ∈ K, ∃ g' ∈ K, ε g' = y⁻¹ * ε g * y⁻¹⁻¹ := by
    intro g hg
    refine ⟨g, hg, ?_⟩
    have hcomm : y * ε g = ε g * y := hYK y hyY g hg
    calc ε g = y⁻¹ * (y * ε g) := by group
      _ = y⁻¹ * (ε g * y) := by rw [hcomm]
      _ = y⁻¹ * ε g * y⁻¹⁻¹ := by group
  let α₂ : MulAut ↥(A ⊔ K) := conjAut A K hKA hε y⁻¹ hyA hyK * α₁
  have hα₂_spec : ∀ p : ↥(A ⊔ K),
      ε ((α₂ p : ↥(A ⊔ K)) : S) = y⁻¹ * ε ((α₁ p : ↥(A ⊔ K)) : S) * y := by
    intro p
    have h := conjAut_spec A K hKA hε y⁻¹ (hsA := hyA) (hsK := hyK) (α₁ p)
    simpa [α₂, MulAut.mul_apply] using h
  have hα₂_A : ∀ a : ↥A, α₂ (inclA a) = inclA a := by
    intro a
    apply Subtype.ext
    apply hε
    rw [hα₂_spec, ← hγ_apply a, hy a]
    show y⁻¹ * (y * ε (a : S) * y⁻¹) * y = ε (a : S)
    group
  have hδ₂_exists : ∀ k : ↥K, ∃ a : ↥A,
      ((α₂ (inclK k) : ↥(A ⊔ K)) : S) = (a : S) * (k : S) := by
    intro k
    obtain ⟨a, ha, haeq⟩ := hYA y⁻¹ (Yg.inv_mem hyY) (δ k) (δ k).2
    refine ⟨⟨a, ha⟩, ?_⟩
    apply hε
    rw [hα₂_spec, hδ_spec k]
    have hcomm : y * ε (k : S) = ε (k : S) * y := hYK y hyY k k.2
    calc y⁻¹ * ε ((δ k : S) * (k : S)) * y
        = y⁻¹ * (ε (δ k : S) * ε (k : S)) * y := by rw [map_mul]
      _ = y⁻¹ * ε (δ k : S) * (ε (k : S) * y) := by group
      _ = y⁻¹ * ε (δ k : S) * (y * ε (k : S)) := by rw [hcomm.symm]
      _ = (y⁻¹ * ε (δ k : S) * y) * ε (k : S) := by group
      _ = ε ((a : S) * (k : S)) := by
            rw [map_mul, haeq]
            group
  let δ₂ : ↥K → ↥A := fun k => Classical.choose (hδ₂_exists k)
  have hδ₂_spec : ∀ k : ↥K,
      ((α₂ (inclK k) : ↥(A ⊔ K)) : S) = (δ₂ k : S) * (k : S) :=
    fun k => Classical.choose_spec (hδ₂_exists k)
  have hδ₂_cocycle : ∀ g h : ↥K,
      ((δ₂ (g * h) : ↥A) : S) = (δ₂ g : S) * ((g : S) * (δ₂ h : S) * (g : S)⁻¹) := by
    intro g h
    have hmul : ((α₂ (inclK (g * h)) : ↥(A ⊔ K)) : S) =
        ((α₂ (inclK g) : ↥(A ⊔ K)) : S) * ((α₂ (inclK h) : ↥(A ⊔ K)) : S) := by
      have h1 : inclK (g * h) = inclK g * inclK h := map_mul inclK g h
      rw [h1, map_mul]
      rfl
    rw [hδ₂_spec (g * h), hδ₂_spec g, hδ₂_spec h] at hmul
    have hmul' : (δ₂ (g * h) : S) * (g : S) * (h : S) =
        (δ₂ g : S) * (g : S) * (δ₂ h : S) * (h : S) := by
      have hgh : ((g * h : ↥K) : S) = (g : S) * (h : S) := rfl
      rw [hgh] at hmul
      simpa only [mul_assoc] using hmul
    have h2 : (δ₂ (g * h) : S) * (g : S) = (δ₂ g : S) * (g : S) * (δ₂ h : S) := by
      have hh : ((δ₂ (g * h) : S) * (g : S)) * (h : S) =
          ((δ₂ g : S) * (g : S) * (δ₂ h : S)) * (h : S) := by
        simpa only [mul_assoc] using hmul'
      exact mul_right_cancel hh
    have h3 : (δ₂ (g * h) : S) = (δ₂ g : S) * (g : S) * (δ₂ h : S) * (g : S)⁻¹ := by
      calc (δ₂ (g * h) : S) = (δ₂ (g * h) : S) * (g : S) * (g : S)⁻¹ := by group
        _ = ((δ₂ g : S) * (g : S) * (δ₂ h : S)) * (g : S)⁻¹ := by rw [h2]
        _ = (δ₂ g : S) * (g : S) * (δ₂ h : S) * (g : S)⁻¹ := by group
    rw [h3]; group
  obtain ⟨a₀, ha₀⟩ := H1 δ₂ hδ₂_cocycle
  have hδ₂_j : ∀ j : ↥K, (j : S) ∈ J → δ₂ j = 1 := by
    intro j hj
    have hα₂j : α₂ (inclK j) = inclK j := by
      apply Subtype.ext
      apply hε
      rw [hα₂_spec, hα₁_j (inclK j) hj]
      have hcomm : y * ε (j : S) = ε (j : S) * y := hYK y hyY j (hJK hj)
      calc y⁻¹ * ε (j : S) * y = y⁻¹ * (ε (j : S) * y) := by group
        _ = y⁻¹ * (y * ε (j : S)) := by rw [hcomm.symm]
        _ = ε (j : S) := by group
    have h := congrArg (fun x : ↥(A ⊔ K) => (x : S)) hα₂j
    rw [hδ₂_spec j] at h
    apply Subtype.ext
    have hh : (δ₂ j : S) * (j : S) = 1 * (j : S) := by
      simpa [inclK, Subgroup.coe_inclusion] using h
    exact mul_right_cancel hh
  have ha₀_comm : ∀ j ∈ J, j * (a₀ : S) = (a₀ : S) * j := by
    intro j hj
    have hjK : j ∈ K := hJK hj
    have h := ha₀ ⟨j, hjK⟩
    have h1 : (δ₂ ⟨j, hjK⟩ : S) = 1 := congrArg (fun x : ↥A => (x : S)) (hδ₂_j ⟨j, hjK⟩ hj)
    rw [h1] at h
    have h3 : (a₀ : S) * ((j : S) * (a₀ : S)⁻¹ * (j : S)⁻¹) = 1 := h.symm
    have h4 : (a₀ : S) * (j : S) * (a₀ : S)⁻¹ = (j : S) := by
      calc (a₀ : S) * (j : S) * (a₀ : S)⁻¹ =
          (a₀ : S) * ((j : S) * (a₀ : S)⁻¹ * (j : S)⁻¹) * (j : S) := by group
        _ = 1 * (j : S) := by rw [h3]
        _ = (j : S) := by group
    calc (j : S) * (a₀ : S) = ((a₀ : S) * (j : S) * (a₀ : S)⁻¹) * (a₀ : S) := by rw [h4]
      _ = (a₀ : S) * (j : S) := by group
  have ha₀_one : (a₀ : S) = 1 := hCA (a₀ : S) a₀.2 ha₀_comm
  have hδ₂_one : ∀ k : ↥K, δ₂ k = 1 := by
    intro k
    apply Subtype.ext
    rw [ha₀ k, ha₀_one]
    simp
  have hα₂_K : ∀ k : ↥K, α₂ (inclK k) = inclK k := by
    intro k
    apply Subtype.ext
    rw [hδ₂_spec k, hδ₂_one k]
    simp [inclK, Subgroup.coe_inclusion]
  have hα₂_id : ∀ p : ↥(A ⊔ K), α₂ p = p := by
    intro p
    obtain ⟨a, ha, k, hk, hpk⟩ := (mem_sup_decomp A K hKA).mp p.2
    have hdecomp : inclA ⟨a, ha⟩ * inclK ⟨k, hk⟩ = p := by
      apply Subtype.ext
      show (a : S) * (k : S) = (p : S)
      exact hpk
    rw [← hdecomp, map_mul, hα₂_A, hα₂_K]
  refine ⟨s, hsSg, y, hyY, ?_⟩
  intro p
  have h1 : y⁻¹ * ε ((α₁ p : ↥(A ⊔ K)) : S) * y = ε (p : S) := by
    have := congrArg (fun x : ↥(A ⊔ K) => ε (x : S)) (hα₂_id p)
    rwa [hα₂_spec] at this
  rw [hα₁_spec p] at h1
  have hgoal : ε ((α p : ↥(A ⊔ K)) : S) = s * y * ε (p : S) * y⁻¹ * s⁻¹ := by
    calc ε ((α p : ↥(A ⊔ K)) : S)
        = s * y * (y⁻¹ * (s⁻¹ * ε ((α p : ↥(A ⊔ K)) : S) * s) * y) * y⁻¹ * s⁻¹ := by
          group
      _ = s * y * ε (p : S) * y⁻¹ * s⁻¹ := by rw [h1]
  rw [mul_inv_rev]
  simpa only [mul_assoc] using hgoal

end CFSG.LinearAlgebra.RootGroupSL