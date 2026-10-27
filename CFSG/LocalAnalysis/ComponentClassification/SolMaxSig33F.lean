module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33E

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem coreImage_conj_of_cak {J : Subgroup X} {n : ℕ}
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) {g : X}
    (hg : g ∈ UnbalancedLayer.coreActionKernel J) {x : X} (hx : x ∈ J)
    (hgx : g * x * g⁻¹ ∈ J) : coreImage θ hgx = coreImage θ hx := by
  have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hg)).2 x hx
  rw [inv_inv] at h1
  obtain ⟨o, ho, hoeq⟩ := h1
  have hoeq' : (o : X) = x⁻¹ * (g * x * g⁻¹) := by
    rw [show x⁻¹ * (g * x * g⁻¹) = x⁻¹ * g * x * g⁻¹ by group]
    exact hoeq
  have h2 : ((⟨g * x * g⁻¹, hgx⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) =
      ((⟨x, hx⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) := by
    symm
    rw [QuotientGroup.eq]
    have h3 : (⟨x, hx⟩ : ↥J)⁻¹ * ⟨g * x * g⁻¹, hgx⟩ = o := Subtype.ext (by
      rw [hoeq']
      rfl)
    rw [h3]
    exact ho
  unfold coreImage
  rw [h2]

theorem coreImage_conj_of_mem {J : Subgroup X} {n : ℕ}
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) {g x : X} (hg : g ∈ J)
    (hx : x ∈ J) (hgx : g * x * g⁻¹ ∈ J) :
    coreImage θ hgx = coreImage θ hg * coreImage θ hx * (coreImage θ hg)⁻¹ := by
  unfold coreImage
  have h1 : (⟨g * x * g⁻¹, hgx⟩ : ↥J) = ⟨g, hg⟩ * ⟨x, hx⟩ * (⟨g, hg⟩ : ↥J)⁻¹ := rfl
  rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
    map_inv]
  rfl

theorem coreImage_conj_of_acts {J : Subgroup X} {n : ℕ}
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) {c e : X} (he : e ∈ J)
    (hce : c * e⁻¹ ∈ UnbalancedLayer.coreActionKernel J) {x : X} (hx : x ∈ J)
    (hcx : c * x * c⁻¹ ∈ J) :
    coreImage θ hcx = coreImage θ he * coreImage θ hx * (coreImage θ he)⁻¹ := by
  have hex : e * x * e⁻¹ ∈ J := mul_mem (mul_mem he hx) (inv_mem he)
  have h1 : c * x * c⁻¹ = (c * e⁻¹) * (e * x * e⁻¹) * (c * e⁻¹)⁻¹ := by group
  have hcx' : (c * e⁻¹) * (e * x * e⁻¹) * (c * e⁻¹)⁻¹ ∈ J := h1 ▸ hcx
  have h2 : coreImage θ hcx = coreImage θ hcx' := by
    unfold coreImage
    congr 3
    exact Subtype.ext h1
  rw [h2, coreImage_conj_of_cak θ hce hex hcx', coreImage_conj_of_mem θ he hx hex]

theorem mem_normalizer_of_fixed_component [Finite X] {J Je : Subgroup X} {n : ℕ}
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) {c : X} {τ : Perm (Fin n)}
    (hJeC : Je ≤ centralizer ({c} : Set X))
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Je = ⊤)
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ τ.supportᶜ → x ∈ Je)
    (hsubP : ∀ x ∈ Je, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ τ.supportᶜ)
    {g : X} (hgN : g ∈ normalizer (J : Set X)) (hgc : g * c = c * g)
    (hgs : ∀ (x : X) (hx : x ∈ J), (coreImage θ hx).support ⊆ τ.supportᶜ →
      (coreImage θ ((mem_normalizer_iff.mp hgN x).mp hx)).support ⊆ τ.supportᶜ) :
    g ∈ normalizer (Je : Set X) := by
  classical
  have hconj : ∀ z ∈ Je, g * z * g⁻¹ ∈ Je := by
    set K : Subgroup X := Je.comap (MulAut.conj g).toMonoidHom with hKdef
    have hK : K.subgroupOf Je = ⊤ := by
      rw [eq_top_iff, ← hres]
      refine sSup_le fun P hP => ?_
      intro p hp
      rw [mem_subgroupOf]
      change g * (p : X) * g⁻¹ ∈ Je
      obtain ⟨hzJ, hzs⟩ := hsubP p p.2
      have hzc : (p : X) * c = c * p := mem_centralizer_singleton_iff.mp (hJeC p.2)
      have hgzJ : g * (p : X) * g⁻¹ ∈ J := (mem_normalizer_iff.mp hgN p).mp hzJ
      refine hinv _ hgzJ ?_ ?_ (hgs p hzJ hzs)
      · have hginv : g⁻¹ * c = c * g⁻¹ := by
          calc g⁻¹ * c = g⁻¹ * (c * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * c) * g⁻¹ := by rw [hgc]
            _ = c * g⁻¹ := by group
        calc g * (p : X) * g⁻¹ * c = g * (p : X) * (g⁻¹ * c) := by group
          _ = g * (p : X) * (c * g⁻¹) := by rw [hginv]
          _ = g * ((p : X) * c) * g⁻¹ := by group
          _ = g * (c * p) * g⁻¹ := by rw [hzc]
          _ = (g * c) * p * g⁻¹ := by group
          _ = (c * g) * p * g⁻¹ := by rw [hgc]
          _ = c * (g * (p : X) * g⁻¹) := by group
      · obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
        refine ⟨k, ?_⟩
        have hk' : (p : X) ^ 2 ^ k = 1 := by
          have := congrArg (fun w : ↥P => ((w : ↥Je) : X)) hk
          simpa using this
        rw [conj_pow, hk']
        group
    intro z hz
    have h1 : (⟨z, hz⟩ : ↥Je) ∈ K.subgroupOf Je := hK ▸ mem_top _
    exact h1
  rw [mem_normalizer_iff_map_conj_eq]
  have hle : Je.map (MulAut.conj g).toMonoidHom ≤ Je := by
    rintro _ ⟨z, hz, rfl⟩
    exact hconj z hz
  refine eq_of_le_of_card_ge hle ?_
  rw [card_map_of_injective (MulAut.conj g).injective]

end CFSG.ComponentClassification.SolMax
