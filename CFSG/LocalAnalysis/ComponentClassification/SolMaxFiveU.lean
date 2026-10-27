module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveT

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_eq_of_le_sup_sup [Finite X] {Y A₁ A₂ B₁ B₂ K : Subgroup X}
    (hA₁ : A₁ ≤ Y) (hA₁p : IsPComponent 2 (A₁.subgroupOf Y))
    (hA₂ : A₂ ≤ Y) (hA₂p : IsPComponent 2 (A₂.subgroupOf Y))
    (hB₁ : B₁ ≤ Y) (hB₁p : IsPComponent 2 (B₁.subgroupOf Y))
    (hB₂ : B₂ ≤ Y) (hB₂p : IsPComponent 2 (B₂.subgroupOf Y))
    (hKperf : ⁅K, K⁆ = K) (hKq : Nontrivial (↥K ⧸ pPrimeCore 2 ↥K))
    (hKA : K ≤ A₁ ⊔ A₂) (hKB : K ≤ B₁ ⊔ B₂) :
    A₁ = B₁ ∨ A₁ = B₂ ∨ A₂ = B₁ ∨ A₂ = B₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  obtain ⟨h11, h12, h21, h22⟩ := hne
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥Y) with hπ
  have hcomm : ∀ P Q : Subgroup X, P ≤ Y → IsPComponent 2 (P.subgroupOf Y) → Q ≤ Y →
      IsPComponent 2 (Q.subgroupOf Y) → P ≠ Q →
      (P.subgroupOf Y).map π ≤ centralizer ((Q.subgroupOf Y).map π : Set _) := by
    intro P Q hP hPp hQ hQp hPQ
    have hne' : P.subgroupOf Y ≠ Q.subgroupOf Y := fun h => by
      rw [subgroupOf_inj, inf_of_le_left hP, inf_of_le_left hQ] at h
      exact hPQ h
    obtain ⟨-, -, hc, -⟩ :=
      (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hPp hQp).2
        hne'
    rw [← commutator_eq_bot_iff_le_centralizer, ← map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    obtain ⟨-, -, hs, -, -⟩ := id hPp
    refine hc.trans (inf_le_left.trans ?_)
    rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs]
    exact inf_le_right
  have hBsup : (B₁ ⊔ B₂).subgroupOf Y = B₁.subgroupOf Y ⊔ B₂.subgroupOf Y :=
    subgroupOf_sup hB₁ hB₂
  have hAsup : (A₁ ⊔ A₂).subgroupOf Y = A₁.subgroupOf Y ⊔ A₂.subgroupOf Y :=
    subgroupOf_sup hA₁ hA₂
  have hcentA : ∀ P : Subgroup X, P ≤ Y → IsPComponent 2 (P.subgroupOf Y) → P ≠ B₁ → P ≠ B₂ →
      (P.subgroupOf Y).map π ≤ centralizer (((B₁ ⊔ B₂).subgroupOf Y).map π : Set _) := by
    intro P hP hPp h1 h2
    rw [hBsup, Subgroup.map_sup]
    exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp (hcomm P B₁ hP hPp hB₁ hB₁p h1))
      (le_centralizer_iff.mp (hcomm P B₂ hP hPp hB₂ hB₂p h2)))
  have hKcA : (K.subgroupOf Y).map π ≤ centralizer (((B₁ ⊔ B₂).subgroupOf Y).map π : Set _) := by
    refine (map_mono fun x hx => mem_subgroupOf.mpr (hKA (mem_subgroupOf.mp hx))).trans ?_
    rw [hAsup, Subgroup.map_sup]
    exact sup_le (hcentA A₁ hA₁ hA₁p h11 h12) (hcentA A₂ hA₂ hA₂p h21 h22)
  have hKB' : (K.subgroupOf Y).map π ≤ ((B₁ ⊔ B₂).subgroupOf Y).map π :=
    map_mono fun x hx => mem_subgroupOf.mpr (hKB (mem_subgroupOf.mp hx))
  have hab : (K.subgroupOf Y).map π ≤ centralizer ((K.subgroupOf Y).map π : Set _) :=
    hKcA.trans (centralizer_le hKB')
  have hbot : ⁅(K.subgroupOf Y).map π, (K.subgroupOf Y).map π⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr hab
  have hKY : K ≤ Y := hKA.trans (sup_le hA₁ hA₂)
  have hKsub : ⁅K.subgroupOf Y, K.subgroupOf Y⁆ = K.subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKY, hKperf]
  rw [← Subgroup.map_commutator, hKsub, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  have hodd : Nat.Coprime 2 (Nat.card K) := by
    have h1 : Nat.card ↥(K.subgroupOf Y) ∣ Nat.card ↥(pPrimeCore 2 ↥Y) := card_dvd_of_le hbot
    rw [Nat.card_congr (subgroupOfEquivOfLe hKY).toEquiv] at h1
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have htop : pPrimeCore 2 ↥K = ⊤ := by
    rw [eq_top_iff]
    exact le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
  have : Subsingleton (↥K ⧸ pPrimeCore 2 ↥K) := QuotientGroup.subsingleton_iff.mpr htop
  exact false_of_nontrivial_of_subsingleton (↥K ⧸ pPrimeCore 2 ↥K)

theorem map_conj_comm {c t : X} (h : c * t = t * c) (M : Subgroup X) :
    (M.map (MulAut.conj c).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      (M.map (MulAut.conj t).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext z
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply]
  rw [show t * (c * z * c⁻¹) * t⁻¹ = (t * c) * z * (t * c)⁻¹ by group, ← h]
  group

theorem coreImage_conj_eq_of_cak [Finite X] {J Jb : Subgroup X} {n : ℕ}
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} {τ : Perm (Fin n)}
    (hJbJ : Jb ≤ J)
    (χb : ↥Jb ⧸ pPrimeCore 2 ↥Jb ≃* alternatingGroup ↥(τ.supportᶜ : Finset (Fin n)))
    (hχb : ∀ (x : ↥Jb) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χb (x : ↥Jb ⧸ pPrimeCore 2 ↥Jb) : alternatingGroup _) :
        Perm ↥(τ.supportᶜ : Finset (Fin n))) = coreImage θ hx)
    {g : X} (hgK : g ∈ UnbalancedLayer.coreActionKernel Jb) {x : X} (hx : x ∈ Jb)
    (hgx : g * x * g⁻¹ ∈ J) : coreImage θ hgx = coreImage θ (hJbJ hx) := by
  classical
  have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hgK)).2 x hx
  rw [inv_inv] at h1
  obtain ⟨o, ho, hoeq⟩ := h1
  have hoeq' : ((o : ↥Jb) : X) = x⁻¹ * (g * x * g⁻¹) := by
    rw [show x⁻¹ * (g * x * g⁻¹) = x⁻¹ * g * x * g⁻¹ by group]
    exact hoeq
  have hoJ : ((o : ↥Jb) : X) ∈ J := hJbJ o.2
  have ho1 : coreImage θ hoJ = 1 := by
    rw [← hχb o hoJ, (QuotientGroup.eq_one_iff (o : ↥Jb)).mpr ho, map_one]
    exact map_one _
  have h2 : g * x * g⁻¹ = x * ((o : ↥Jb) : X) := by rw [hoeq']; group
  have h3 : coreImage θ hgx = coreImage θ (hJbJ hx) * coreImage θ hoJ := by
    unfold coreImage
    have h4 : (⟨g * x * g⁻¹, hgx⟩ : ↥J) = ⟨x, hJbJ hx⟩ * ⟨_, hoJ⟩ := Subtype.ext h2
    rw [h4, QuotientGroup.mk_mul, map_mul]
    rfl
  rw [h3, ho1, mul_one]

end CFSG.ComponentClassification.SolMax
