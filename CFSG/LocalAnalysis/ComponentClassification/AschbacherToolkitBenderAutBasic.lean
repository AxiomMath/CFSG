module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

variable {G : Type*} [Group G]

@[expose] def AutControlAt (S : Subgroup G) : Prop :=
  ∀ α : MulAut G, (∀ s ∈ S, α s ∈ S) → (∀ z ∈ sylowCenter S, α z = z) →
    (∃ n : ℕ, α ^ (2 ^ n) = 1) → (∀ s ∈ S, α ≠ MulAut.conj s) →
      (∃ s ∈ S, α ^ 2 = MulAut.conj s) ∧
      ((∃ z ∈ sylowCenter S, α ^ 2 = MulAut.conj z) → ∀ t ∈ S, α t = t → t ∈ sylowCenter S) ∧
      ∃ t ∈ S, t⁻¹ * α t ∉ sylowCenter S

@[expose] def CentPairAt (S : Subgroup G) : Prop :=
  ∀ s ∈ S, s ∉ sylowCenter S → ∃ n ∈ Subgroup.normalizer (S : Set G),
    ∀ t ∈ S, t * s = s * t → t * (n⁻¹ * s * n) = n⁻¹ * s * n * t → t ∈ sylowCenter S

namespace AutTransport

variable {G' : Type*} [Group G']

theorem mem_map_iff (e : G ≃* G') {S : Subgroup G} {g : G} :
    e g ∈ S.map e.toMonoidHom ↔ g ∈ S := by
  constructor
  · rintro ⟨g', hg', hgg'⟩
    have : g' = g := e.injective hgg'
    rwa [← this]
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem mem_map_iff' (e : G ≃* G') {S : Subgroup G} {g' : G'} :
    g' ∈ S.map e.toMonoidHom ↔ e.symm g' ∈ S := by
  rw [← mem_map_iff e, MulEquiv.apply_symm_apply]

theorem mem_sylowCenter_map (e : G ≃* G') {S : Subgroup G} {g : G} :
    e g ∈ sylowCenter (S.map e.toMonoidHom) ↔ g ∈ sylowCenter S := by
  rw [mem_sylowCenter, mem_sylowCenter, mem_map_iff]
  constructor
  · rintro ⟨hg, hc⟩
    refine ⟨hg, fun t ht => e.injective ?_⟩
    rw [map_mul, map_mul]
    exact hc (e t) ((mem_map_iff e).mpr ht)
  · rintro ⟨hg, hc⟩
    refine ⟨hg, fun t' ht' => ?_⟩
    have ht := (mem_map_iff' e).mp ht'
    have h := congrArg e (hc _ ht)
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h

theorem mem_sylowCenter_map' (e : G ≃* G') {S : Subgroup G} {g' : G'} :
    g' ∈ sylowCenter (S.map e.toMonoidHom) ↔ e.symm g' ∈ sylowCenter S := by
  rw [← mem_sylowCenter_map e, MulEquiv.apply_symm_apply]

theorem congr_conj (e : G ≃* G') (s : G) : MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext g'
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem congr_apply' (e : G ≃* G') (α : MulAut G) (g : G) : MulAut.congr e α (e g) = e (α g) := by
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

theorem congr_symm_apply' (e : G ≃* G') (α' : MulAut G') (g : G) :
    (MulAut.congr e).symm α' g = e.symm (α' (e g)) := rfl

theorem mem_normalizer_map (e : G ≃* G') {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) :
    e n ∈ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup G') : Set G') := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro g'
  rw [mem_map_iff' e, mem_map_iff' e]
  have h : e.symm (e n * g' * (e n)⁻¹) = n * e.symm g' * n⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rw [h]
  exact hn _

end AutTransport

open AutTransport in
theorem AutControlAt.map_mulEquiv {G' : Type*} [Group G'] {S : Subgroup G} (h : AutControlAt S)
    (e : G ≃* G') : AutControlAt (S.map e.toMonoidHom) := by
  intro α' hn hz hpow hout
  set α := (MulAut.congr e).symm α' with hαdef
  have hα' : α' = MulAut.congr e α := by rw [hαdef, MulEquiv.apply_symm_apply]
  have happ : ∀ g, α g = e.symm (α' (e g)) := fun g => congr_symm_apply' e α' g
  have hn' : ∀ s ∈ S, α s ∈ S := by
    intro s hs
    rw [happ, ← mem_map_iff' e]
    exact hn _ ((mem_map_iff e).mpr hs)
  have hz' : ∀ z ∈ sylowCenter S, α z = z := by
    intro z hz₀
    rw [happ, hz _ ((mem_sylowCenter_map e).mpr hz₀), MulEquiv.symm_apply_apply]
  have hpow' : ∃ n : ℕ, α ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn₀⟩ := hpow
    refine ⟨n, ?_⟩
    rw [hαdef, ← map_pow, hn₀, map_one]
  have hout' : ∀ s ∈ S, α ≠ MulAut.conj s := by
    intro s hs heq
    apply hout (e s) ((mem_map_iff e).mpr hs)
    rw [hα', heq, congr_conj]
  obtain ⟨⟨s, hs, hs2⟩, hfix, ⟨t, ht, htZ⟩⟩ := h α hn' hz' hpow' hout'
  refine ⟨⟨e s, (mem_map_iff e).mpr hs, ?_⟩, ?_, ⟨e t, (mem_map_iff e).mpr ht, ?_⟩⟩
  · rw [hα', ← map_pow, hs2, congr_conj]
  · rintro ⟨z', hz'Z, hz'2⟩ t' ht' hfix'
    have hzZ : e.symm z' ∈ sylowCenter S := (mem_sylowCenter_map' e).mp hz'Z
    have h2 : α ^ 2 = MulAut.conj (e.symm z') := by
      apply (MulAut.congr e).injective
      rw [map_pow, ← hα', hz'2, congr_conj, MulEquiv.apply_symm_apply]
    have htS : e.symm t' ∈ S := (mem_map_iff' e).mp ht'
    have hαt : α (e.symm t') = e.symm t' := by
      rw [happ, MulEquiv.apply_symm_apply, hfix']
    have := hfix ⟨e.symm z', hzZ, h2⟩ _ htS hαt
    exact (mem_sylowCenter_map' e).mpr this
  · intro hcon
    apply htZ
    have h1 : e (t⁻¹ * α t) = (e t)⁻¹ * α' (e t) := by
      rw [map_mul, map_inv, happ, MulEquiv.apply_symm_apply]
    rw [← mem_sylowCenter_map e, h1]
    exact hcon

open AutTransport in
theorem CentPairAt.map_mulEquiv {G' : Type*} [Group G'] {S : Subgroup G} (h : CentPairAt S)
    (e : G ≃* G') : CentPairAt (S.map e.toMonoidHom) := by
  intro s' hs' hs'Z
  have hs : e.symm s' ∈ S := (mem_map_iff' e).mp hs'
  have hsZ : e.symm s' ∉ sylowCenter S := fun hZ => hs'Z ((mem_sylowCenter_map' e).mpr hZ)
  obtain ⟨n, hn, hpair⟩ := h _ hs hsZ
  refine ⟨e n, mem_normalizer_map e hn, fun t' ht' hc₁ hc₂ => ?_⟩
  have ht : e.symm t' ∈ S := (mem_map_iff' e).mp ht'
  apply (mem_sylowCenter_map' e).mpr
  apply hpair _ ht
  · apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hc₁
  · apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc₂

theorem autControlAt_of_one_sylow [Finite G] (R : Sylow 2 G) (h : AutControlAt (R : Subgroup G))
    (T : Sylow 2 G) : AutControlAt (T : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R T
  have hT : (T : Subgroup G) = (R : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [hT]
  exact h.map_mulEquiv (MulAut.conj g)

theorem centPairAt_of_one_sylow [Finite G] (R : Sylow 2 G) (h : CentPairAt (R : Subgroup G))
    (T : Sylow 2 G) : CentPairAt (T : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R T
  have hT : (T : Subgroup G) = (R : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [hT]
  exact h.map_mulEquiv (MulAut.conj g)

theorem autControlAt_of_mulEquiv [Finite G] {G' : Type*} [Group G'] (e : G ≃* G')
    (hG' : ∀ T : Sylow 2 G', AutControlAt (T : Subgroup G')) (T : Sylow 2 G) :
    AutControlAt (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (hG' (T.mapSurjective (f := e.toMonoidHom) e.surjective)).map_mulEquiv e.symm
  have h' : AutControlAt (((T : Subgroup G).map e.toMonoidHom).map e.symm.toMonoidHom) := h
  rw [Subgroup.map_map] at h'
  convert h'
  ext x
  simp

theorem centPairAt_of_mulEquiv [Finite G] {G' : Type*} [Group G'] (e : G ≃* G')
    (hG' : ∀ T : Sylow 2 G', CentPairAt (T : Subgroup G')) (T : Sylow 2 G) :
    CentPairAt (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (hG' (T.mapSurjective (f := e.toMonoidHom) e.surjective)).map_mulEquiv e.symm
  have h' : CentPairAt (((T : Subgroup G).map e.toMonoidHom).map e.symm.toMonoidHom) := h
  rw [Subgroup.map_map] at h'
  convert h'
  ext x
  simp

theorem centPairAt_of_abelian {S : Subgroup G} (hab : S ≤ sylowCenter S) : CentPairAt S :=
  fun _ hs hsZ => absurd (hab hs) hsZ

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
