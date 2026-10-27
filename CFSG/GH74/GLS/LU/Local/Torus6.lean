module

public import CFSG.GH74.GLS.LU.Local.Torus5
public import CFSG.GH74.GLS.LU.Local.Torus4

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
  CFSG.ComponentClassification
open scoped Pointwise MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

theorem exists_conj_le_sylow_sub {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) {Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsPGroup p Q) :
    ∃ c ∈ H, ∀ q ∈ Q, c * q * c⁻¹ ∈ (P : Subgroup G) := by
  classical
  have hp : IsPGroup p (Q.subgroupOf H) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H T (P.subtype hPH)
  refine ⟨c, c.2, fun q hq => ?_⟩
  have hqT : (⟨q, hQH hq⟩ : H) ∈ (T : Subgroup H) := hT (Subgroup.mem_subgroupOf.mpr hq)
  have hmem : MulAut.conj c (⟨q, hQH hq⟩ : H) ∈ ((c • T : Sylow p H) : Subgroup H) := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hqT
  rw [hc, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

variable {G : Type} [Group G] [Finite G] {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
  {p f : ℕ} {ε : ℤ}

theorem cyclic_of_embed {q : ℕ} (hc : LUComps G q z K₁ K₂) [IsCyclic ↥(A0 z)] {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) (hq : Odd q) {Γ : Type} [Group Γ] (hΓ : IsPGroup 2 Γ) (φ : Γ →* G)
    (hφ : Function.Injective φ) (hφK : ∀ γ, φ γ ∈ K) {y a k : G} (hy : y = a * k) (ha : a ∈ A0 z)
    (hk : k ∈ K) (hnc : ¬ ∀ k' ∈ K, y * k' = k' * y) (hφy : ∀ γ, φ γ * y = y * φ γ) : IsCyclic Γ := by
  have hsl : HasSL2Model ↥K (fun r => r = q) := by
    rcases hK with rfl | rfl
    · exact hc.sl₁
    · exact hc.sl₂
  obtain ⟨F, hF, hFin, hFq, -⟩ := id hsl
  obtain ⟨e⟩ := exists_mulEquiv_SL2 hsl F hFq
  have hodd : Odd (Nat.card F) := by rw [hFq]; exact hq
  have hh2 := two_ne_zero_of_odd_card hodd
  subst hy
  have hab := cent_abelian hc hK ha hk hnc
  let ψ : Γ →* SL(2, F) := e.symm.toMonoidHom.comp (φ.codRestrict K hφK)
  have hψ : Function.Injective ψ := by
    intro γ γ' h
    apply hφ
    have h1 : φ.codRestrict K hφK γ = φ.codRestrict K hφK γ' := e.symm.injective h
    exact congrArg Subtype.val h1
  have hψφ : ∀ γ, ((e (ψ γ) : ↥K) : G) = φ γ := by
    intro γ
    show ((e (e.symm (φ.codRestrict K hφK γ)) : ↥K) : G) = φ γ
    simp
  have hcyc : IsCyclic ↥ψ.range := by
    refine sl2_abelian_two_group_cyclic hh2 ψ.range ?_ ?_
    · rintro _ ⟨γ, rfl⟩ _ ⟨γ', rfl⟩
      apply e.injective
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul, hψφ]
      exact hab _ (hφK γ) _ (hφK γ') (hφy γ) (hφy γ')
    · rintro _ ⟨γ, rfl⟩
      obtain ⟨n, hn⟩ := hΓ γ
      exact ⟨n, by rw [← map_pow, hn, map_one]⟩
  exact isCyclic_of_surjective (MonoidHom.ofInjective hψ).symm.toMonoidHom
    (MonoidHom.ofInjective hψ).symm.surjective

omit [Finite G] in
theorem conj_comm_of {c g k : G} (h : g * (c⁻¹ * k * c) = (c⁻¹ * k * c) * g) :
    (c * g * c⁻¹) * k = k * (c * g * c⁻¹) := by
  calc (c * g * c⁻¹) * k = c * (g * (c⁻¹ * k * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * k * c) * g) * c⁻¹ := by rw [h]
    _ = k * (c * g * c⁻¹) := by group

theorem cyclic_two_subgroup (X : LUCtx G p f z S K₁ K₂ t u ε) {x : G} {r : ℕ}
    (hx : XData z K₁ K₂ x r) {Γ : Type} [Group Γ] (hΓ : IsPGroup 2 Γ) (φ : Γ →* G)
    (hφ : Function.Injective φ) (hφz : ∀ γ, φ γ * z = z * φ γ)
    (hφK : ∀ γ, ∀ k ∈ K₁, φ γ * k = k * φ γ) (hφx : ∀ γ, φ γ * x = x * φ γ) : IsCyclic Γ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic ↥(A0 z) := X.eps.A0_cyc
  have hc := X.comps
  have hs := X.syl
  have hQC : φ.range ≤ Cz z := by
    rintro _ ⟨γ, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hφz γ)
  have hQp : IsPGroup 2 ↥φ.range := hΓ.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨c, hcC, hcS⟩ := exists_conj_le_sylow_sub S hs.S_le_Cz hQC hQp
  obtain ⟨a, ha, k, hk, hxak, -⟩ := hx.dec
  have hca : c * a * c⁻¹ ∈ A0 z :=
    (mem_normalizer_iff.mp (mem_normalizer_pPrimeCoreOf hcC) a).mp ha
  have hcx_dec : c * x * c⁻¹ = (c * a * c⁻¹) * (c * k * c⁻¹) := by rw [hxak]; group
  have hφS : ∀ γ, c * φ γ * c⁻¹ ∈ (S : Subgroup G) := fun γ => hcS _ ⟨γ, rfl⟩
  let φ' : Γ →* G := (MulAut.conj c).toMonoidHom.comp φ
  have hφ' : Function.Injective φ' := (MulAut.conj c).injective.comp hφ
  have hφ'x : ∀ γ, φ' γ * (c * x * c⁻¹) = (c * x * c⁻¹) * φ' γ := fun γ => conj_comm_conj (hφx γ)
  have key : ∀ Kj : Subgroup G, (Kj = K₁ ∨ Kj = K₂) → (∀ y ∈ K₂, c * y * c⁻¹ ∈ Kj) →
      (∀ γ, c * φ γ * c⁻¹ ∈ Kj) → IsCyclic Γ := by
    intro Kj hKj hfwd hmem
    refine cyclic_of_embed hc hKj X.odd_q hΓ φ' hφ' hmem hcx_dec hca (hfwd k hk) ?_ hφ'x
    intro h
    apply hx.nc₂
    intro k₂ hk₂
    have h1 := h _ (hfwd k₂ hk₂)
    have h2 : c * (x * k₂) * c⁻¹ = c * (k₂ * x) * c⁻¹ := by
      calc c * (x * k₂) * c⁻¹ = (c * x * c⁻¹) * (c * k₂ * c⁻¹) := by group
        _ = (c * k₂ * c⁻¹) * (c * x * c⁻¹) := h1
        _ = c * (k₂ * x) * c⁻¹ := by group
    have h3 := mul_right_cancel h2
    exact mul_left_cancel h3
  rcases hc.perm hcC with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine key K₂ (Or.inr rfl) (fun y hy => LUComps.mem_of_map e2 hy) (fun γ => ?_)
    have hq'K : ∀ k' ∈ K₁, (c * φ γ * c⁻¹) * k' = k' * (c * φ γ * c⁻¹) := fun k' hk' =>
      conj_comm_of (hφK γ _ (mem_of_map_inv e1 hk'))
    exact cs₁ hc hs (hφS γ) hq'K
  · refine key K₁ (Or.inl rfl) (fun y hy => LUComps.mem_of_map e2 hy) (fun γ => ?_)
    have hq'K : ∀ k' ∈ K₂, (c * φ γ * c⁻¹) * k' = k' * (c * φ γ * c⁻¹) := fun k' hk' =>
      conj_comm_of (hφK γ _ (mem_of_map_inv e1 hk'))
    exact cs₂ hc hs (hφS γ) hq'K

theorem cyclic_sylow_CY (X : LUCtx G p f z S K₁ K₂ t u ε) {x : G} {r : ℕ} (hx : XData z K₁ K₂ x r)
    (T : Sylow 2 ↥(centralizer
      ((K₁.subgroupOf (centralizer ({x} : Set G)) : Subgroup (CY G x)) : Set (CY G x)))) :
    IsCyclic ↥T := by
  have hc := X.comps
  have hK₁C : K₁ ≤ centralizer ({x} : Set G) := fun k hk =>
    mem_centralizer_singleton_iff.mpr (hx.c₁ k hk).symm
  let ι : ↥(T : Subgroup ↥(centralizer
      ((K₁.subgroupOf (centralizer ({x} : Set G)) : Subgroup (CY G x)) : Set (CY G x)))) →* G :=
    (centralizer ({x} : Set G)).subtype.comp ((centralizer
      ((K₁.subgroupOf (centralizer ({x} : Set G)) : Subgroup (CY G x)) : Set (CY G x))).subtype.comp
      (T : Subgroup ↥(centralizer
      ((K₁.subgroupOf (centralizer ({x} : Set G)) : Subgroup (CY G x)) : Set (CY G x)))).subtype)
  have hι : Function.Injective ι := fun γ γ' h => Subtype.ext (Subtype.ext (Subtype.ext h))
  have hK : ∀ (γ : ↥(T : Subgroup ↥(centralizer
      ((K₁.subgroupOf (centralizer ({x} : Set G)) : Subgroup (CY G x)) : Set (CY G x))))),
      ∀ k ∈ K₁, ι γ * k = k * ι γ := by
    intro γ k hk
    have hkY : (⟨k, hK₁C hk⟩ : CY G x) ∈ K₁.subgroupOf (centralizer ({x} : Set G)) :=
      Subgroup.mem_subgroupOf.mpr hk
    have := mem_centralizer_iff.mp γ.1.2 _ hkY
    exact (congrArg Subtype.val this).symm
  refine cyclic_two_subgroup X hx T.isPGroup' ι hι (fun γ => hK γ z hc.z_mem₁) hK (fun γ => ?_)
  exact mem_centralizer_singleton_iff.mp γ.1.1.2

end CFSG.GH74.GLS.LU.Local
