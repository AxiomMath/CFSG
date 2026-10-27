module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Witness

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open Equiv Equiv.Perm

section Nu

variable {G : Type} [Group G] {K : Subgroup G} {π : OddQuot K →* A7} {zE : OddQuot K}

theorem autPerm_conj_eq (cov : IsDoubleCoverA7 π zE) (e : OddQuot K) :
    cov.autPerm (MulAut.conj e) = (π e : Perm (Fin 7)) := by
  set σ₁ : Perm (Fin 7) := cov.autPerm (MulAut.conj e) with hσ₁
  set σ₂ : Perm (Fin 7) := (π e : Perm (Fin 7)) with hσ₂
  have key : ∀ a : A7, σ₁ * (a : Perm (Fin 7)) * σ₁⁻¹ = σ₂ * (a : Perm (Fin 7)) * σ₂⁻¹ := by
    intro a
    obtain ⟨x, rfl⟩ := cov.surjective a
    have h3 := cov.autPerm_spec (MulAut.conj e) x
    rw [← hσ₁, MulAut.conj_apply, map_mul, map_mul, map_inv] at h3
    rw [← h3]
    simp [hσ₂]
  have h4 : conjEquiv (σ₂⁻¹ * σ₁) = 1 := by
    refine MulEquiv.ext (fun a => Subtype.ext ?_)
    rw [conjEquiv_apply, MulAut.one_apply]
    calc σ₂⁻¹ * σ₁ * (a : Perm (Fin 7)) * (σ₂⁻¹ * σ₁)⁻¹
        = σ₂⁻¹ * (σ₁ * (a : Perm (Fin 7)) * σ₁⁻¹) * σ₂ := by group
      _ = (a : Perm (Fin 7)) := by rw [key a]; group
  have h5 : σ₂⁻¹ * σ₁ = 1 := conjEquiv.injective (by rw [h4, map_one])
  have h6 : σ₁ = σ₂ := by
    calc σ₁ = σ₂ * (σ₂⁻¹ * σ₁) := by group
      _ = σ₂ := by rw [h5, mul_one]
  exact h6

variable (cov : IsDoubleCoverA7 π zE)

@[expose] noncomputable def nuK : Subgroup.normalizer (K : Set G) →* Perm (Fin 7) :=
  cov.autPerm.comp (actHom K (Subgroup.normalizer (K : Set G)) le_rfl)

@[expose] noncomputable def nuG (x : G) : Perm (Fin 7) := by
  classical
  exact if hx : x ∈ Subgroup.normalizer (K : Set G) then nuK cov ⟨x, hx⟩ else 1

theorem nuG_of_mem {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    nuG cov x = nuK cov ⟨x, hx⟩ := by
  simp [nuG, hx]

theorem nuG_mul {a b : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (hb : b ∈ Subgroup.normalizer (K : Set G)) :
    nuG cov (a * b) = nuG cov a * nuG cov b := by
  have hmul : (⟨a * b, Subgroup.mul_mem _ ha hb⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [nuG_of_mem cov ha, nuG_of_mem cov hb, nuG_of_mem cov (Subgroup.mul_mem _ ha hb), hmul,
    map_mul]

theorem nuG_inv {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G)) :
    nuG cov a⁻¹ = (nuG cov a)⁻¹ := by
  have hinv : (⟨a⁻¹, Subgroup.inv_mem _ ha⟩ : Subgroup.normalizer (K : Set G)) = ⟨a, ha⟩⁻¹ := rfl
  rw [nuG_of_mem cov ha, nuG_of_mem cov (Subgroup.inv_mem _ ha), hinv, map_inv]

theorem nuG_conj {a b : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (hb : b ∈ Subgroup.normalizer (K : Set G)) :
    nuG cov (a * b * a⁻¹) = nuG cov a * nuG cov b * (nuG cov a)⁻¹ := by
  rw [nuG_mul cov (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha), nuG_mul cov ha hb,
    nuG_inv cov ha]

theorem nuG_one : nuG cov (1 : G) = 1 := by
  have hone : (⟨1, Subgroup.one_mem _⟩ : Subgroup.normalizer (K : Set G)) = 1 := rfl
  rw [nuG_of_mem cov (Subgroup.one_mem _), hone, map_one]

theorem nuG_eq_one_iff {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    nuG cov n = 1 ↔ oddQuotAut K (conjOn K n hn) = 1 := by
  rw [nuG_of_mem cov hn]
  constructor
  · intro h
    apply cov.autPerm_injective
    rw [map_one]
    exact h
  · intro h
    show cov.autPerm (oddQuotAut K (conjOn K n hn)) = 1
    rw [h, map_one]

theorem nuG_of_mem_K {k : G} (hk : k ∈ K) :
    nuG cov k = (π (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) : Perm (Fin 7)) := by
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
  rw [nuG_of_mem cov hkN]
  have : actHom K (Subgroup.normalizer (K : Set G)) le_rfl ⟨k, hkN⟩ =
      MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : OddQuot K) := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    show oddQuotAut K (conjOn K k hkN) (x : OddQuot K) = _
    rw [oddQuotAut_mk]
    have e1 : (conjOn K k hkN x : ↥K) = (⟨k, hk⟩ : ↥K) * x * (⟨k, hk⟩ : ↥K)⁻¹ := rfl
    rw [e1, MulAut.conj_apply]
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  show cov.autPerm (actHom K (Subgroup.normalizer (K : Set G)) le_rfl ⟨k, hkN⟩) = _
  rw [this]
  exact autPerm_conj_eq cov _

theorem exists_mem_K_nuG_eq {τ : A7} : ∃ k : G, k ∈ K ∧ nuG cov k = (τ : Perm (Fin 7)) := by
  obtain ⟨e, rfl⟩ := cov.surjective τ
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective e
  exact ⟨x, x.2, nuG_of_mem_K cov x.2⟩

@[expose] noncomputable def epsK : Subgroup.normalizer (K : Set G) →* ℤˣ :=
  Equiv.Perm.sign.comp (nuK cov)

@[expose] noncomputable def epsG (x : G) : ℤˣ := Equiv.Perm.sign (nuG cov x)

theorem epsG_of_mem {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    epsG cov x = epsK cov ⟨x, hx⟩ := by
  rw [epsG, nuG_of_mem cov hx]
  rfl

theorem epsG_one : epsG cov (1 : G) = 1 := by rw [epsG, nuG_one cov, map_one]

theorem exists_mem_K_nuG_eq_one_of_epsG_eq_one {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G))
    (hε : epsG cov n = 1) : ∃ k : G, k ∈ K ∧ nuG cov (k⁻¹ * n) = 1 := by
  have hA : nuG cov n ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    exact hε
  obtain ⟨k, hkK, hk⟩ := exists_mem_K_nuG_eq cov (τ := ⟨nuG cov n, hA⟩)
  refine ⟨k, hkK, ?_⟩
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
  rw [nuG_mul cov (Subgroup.inv_mem _ hkN) hn, nuG_inv cov hkN, hk]
  simp

end Nu

end CFSG.ClassicalInvolution.Hat2A7
