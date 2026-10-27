module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32C

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem sign_eq_one_of_commute_altFour : ∀ w : Perm (Fin 4),
    (∀ k : alternatingGroup (Fin 4), k * k = 1 → w * (k : Perm (Fin 4)) = (k : Perm (Fin 4)) * w) →
      Perm.sign w = 1 := by
  decide

theorem sign_eq_one_of_commute_klein {n : ℕ} {D : Finset (Fin n)} (hD : D.card = 4)
    {σ : Perm (Fin n)} (hσD : ∀ ω ∉ D, σ ω = ω)
    (hσV : ∀ u : alternatingGroup (Fin n), u * u = 1 → (∀ ω ∉ D, (u : Perm (Fin n)) ω = ω) →
      σ * u = u * σ) : Perm.sign σ = 1 := by
  classical
  have hcardD : Fintype.card ↥D = 4 := by rw [Fintype.card_coe, hD]
  set e : ↥D ≃ Fin 4 := Fintype.equivFinOfCardEq hcardD with hedef
  have hmem : σ ∈ (Perm.ofSubtype : Perm (Subtype (· ∈ D)) →* Perm (Fin n)).range := by
    rw [Perm.mem_range_ofSubtype_iff]
    intro ω hω
    by_contra hωD
    exact (Perm.mem_support.mp hω) (hσD ω hωD)
  obtain ⟨s, rfl⟩ := hmem
  rw [Perm.sign_ofSubtype, ← Perm.sign_permCongr e]
  refine sign_eq_one_of_commute_altFour _ fun k hk => ?_
  set k' : Perm ↥D := e.symm.permCongr (k : Perm (Fin 4)) with hk'def
  have hk'A : k' ∈ alternatingGroup ↥D := by
    rw [Perm.mem_alternatingGroup, hk'def, Perm.sign_permCongr]
    exact k.2
  set u : alternatingGroup (Fin n) := alternatingGroup.ofSubtype D ⟨k', hk'A⟩ with hudef
  have hu : (u : Perm (Fin n)) = Perm.ofSubtype k' := rfl
  have hk'2 : k' * k' = 1 := by
    rw [hk'def, ← Equiv.permCongr_mul]
    have : (k : Perm (Fin 4)) * k = 1 := congrArg Subtype.val hk
    rw [this]
    ext x
    simp
  have hu2 : u * u = 1 := by
    apply Subtype.ext
    change (u : Perm (Fin n)) * u = 1
    rw [hu, ← map_mul, hk'2, map_one]
  have huD : ∀ ω ∉ D, (u : Perm (Fin n)) ω = ω := fun ω hω => by
    rw [hu]
    exact Perm.ofSubtype_apply_of_not_mem _ hω
  have h1 := hσV u hu2 huD
  rw [hu, ← map_mul, ← map_mul] at h1
  have h2 := Perm.ofSubtype_injective h1
  have h3 := congrArg e.permCongr h2
  rw [Equiv.permCongr_mul, Equiv.permCongr_mul] at h3
  have hk'' : e.permCongr k' = (k : Perm (Fin 4)) := by
    ext x
    simp [hk'def]
  rw [hk''] at h3
  exact h3

theorem exists_split {n : ℕ} (D : Finset (Fin n)) {π : Perm (Fin n)}
    (hπ : ∀ v, π v ∈ D ↔ v ∈ D) :
    ∃ σD σF : Perm (Fin n), π = σD * σF ∧ (∀ v ∉ D, σD v = v) ∧ (∀ v ∈ D, σF v = v) ∧
      (∀ v ∈ D, σD v = π v) ∧ ∀ v ∉ D, σF v = π v := by
  classical
  have hπ' : ∀ v, π v ∉ D ↔ v ∉ D := fun v => not_congr (hπ v)
  set σD := Perm.ofSubtype (π.subtypePerm (p := fun v => v ∈ D) hπ) with hσDdef
  set σF := Perm.ofSubtype (π.subtypePerm (p := fun v => v ∉ D) hπ') with hσFdef
  have h1 : ∀ v ∉ D, σD v = v := fun v hv =>
    Perm.ofSubtype_apply_of_not_mem (p := fun v => v ∈ D) _ hv
  have h2 : ∀ v ∈ D, σF v = v := fun v hv =>
    Perm.ofSubtype_apply_of_not_mem (p := fun v => v ∉ D) _ (not_not.mpr hv)
  have h3 : ∀ v ∈ D, σD v = π v := fun v hv =>
    Perm.ofSubtype_subtypePerm_of_mem (p := fun v => v ∈ D) hπ hv
  have h4 : ∀ v ∉ D, σF v = π v := fun v hv =>
    Perm.ofSubtype_subtypePerm_of_mem (p := fun v => v ∉ D) hπ' hv
  refine ⟨σD, σF, Equiv.ext fun v => ?_, h1, h2, h3, h4⟩
  rw [Perm.mul_apply]
  by_cases hv : v ∈ D
  · rw [h2 v hv, h3 v hv]
  · rw [h4 v hv, h1 _ ((hπ' v).mpr hv)]

theorem eq_of_support_subset_pair {n : ℕ} {S : Finset (Fin n)} (hS : S.card = 2)
    {σ₁ σ₂ : Perm (Fin n)} (h₁ : σ₁.support ⊆ S) (h₂ : σ₂.support ⊆ S) (h₁1 : σ₁ ≠ 1)
    (h₂1 : σ₂ ≠ 1) : σ₁ = σ₂ := by
  classical
  have hcard : ∀ σ : Perm (Fin n), σ.support ⊆ S → σ ≠ 1 → σ.support = S := by
    intro σ hσ hσ1
    refine Finset.eq_of_subset_of_card_le hσ ?_
    rw [hS]
    have h0 : σ.support.card ≠ 0 := fun h =>
      hσ1 (Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h))
    have h1 : σ.support.card ≠ 1 := Perm.card_support_ne_one σ
    omega
  have hs₁ := hcard σ₁ h₁ h₁1
  have hs₂ := hcard σ₂ h₂ h₂1
  obtain ⟨x, y, hxy, rfl⟩ := Perm.card_support_eq_two.mp (by rw [hs₁, hS])
  obtain ⟨x', y', hxy', rfl⟩ := Perm.card_support_eq_two.mp (by rw [hs₂, hS])
  rw [Perm.support_swap hxy, Perm.support_swap hxy'] at *
  have hx : x ∈ ({x', y'} : Finset (Fin n)) := by rw [hs₂, ← hs₁]; simp
  have hy : y ∈ ({x', y'} : Finset (Fin n)) := by rw [hs₂, ← hs₁]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · rfl
  · exact swap_comm _ _
  · exact absurd rfl hxy

variable {X : Type} [Group X]

theorem eq_of_isPComponent_of_le_inf [Finite X] {Y L₁ L₂ K : Subgroup X} (h₁ : L₁ ≤ Y)
    (h₂ : L₂ ≤ Y) (hp₁ : IsPComponent 2 (L₁.subgroupOf Y)) (hp₂ : IsPComponent 2 (L₂.subgroupOf Y))
    (hK₁ : K ≤ L₁) (hK₂ : K ≤ L₂) (hKperf : ⁅K, K⁆ = K)
    (hKq : Nontrivial (↥K ⧸ pPrimeCore 2 ↥K)) : L₁ = L₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have h1 := commutator_le_core_join h₁ h₂ hp₁ hp₂ hne
  have hKO : K ≤ (pPrimeCore 2 ↥(L₁ ⊔ L₂)).map (L₁ ⊔ L₂).subtype := by
    rw [← hKperf]
    exact (commutator_mono hK₁ hK₂).trans h1
  have hodd : Nat.Coprime 2 (Nat.card K) := by
    have h2 : Nat.card K ∣ Nat.card ((pPrimeCore 2 ↥(L₁ ⊔ L₂)).map (L₁ ⊔ L₂).subtype) :=
      Subgroup.card_dvd_of_le hKO
    rw [card_map_of_injective (L₁ ⊔ L₂).subtype_injective] at h2
    exact Nat.Coprime.coprime_dvd_right h2 pPrimeCore_coprime_card
  have htop : pPrimeCore 2 ↥K = ⊤ := by
    rw [eq_top_iff]
    exact le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
  have : Subsingleton (↥K ⧸ pPrimeCore 2 ↥K) := QuotientGroup.subsingleton_iff.mpr htop
  exact false_of_nontrivial_of_subsingleton (↥K ⧸ pPrimeCore 2 ↥K)

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.exists_lift_of_isPGroup (hρ : IsPermAction θ ρ) [Finite X]
    {B : Subgroup X} (hBN : B ≤ normalizer (M : Set X)) (hB2 : IsPGroup 2 B)
    {b : alternatingGroup (Fin r)}
    (hb : ∀ (g : X) (hg : g ∈ B), (b : Perm (Fin r)) * ρ ⟨g, hBN hg⟩ = ρ ⟨g, hBN hg⟩ * b) :
    ∃ x : ↥M, (x : X) ∈ centralizer (B : Set X) ∧ θ (x : ↥M ⧸ pPrimeCore 2 ↥M) = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 ↥M with hOdef
  let α : ↥B →* MulAut ↥M := M.normalizerMonoidHom.comp (inclusion hBN)
  have hα : ∀ (g : ↥B) (m : ↥M), ((α g m : ↥M) : X) = (g : X) * m * (g : X)⁻¹ := fun _ _ => rfl
  have hαO : ∀ (g : ↥B) (o : ↥M), o ∈ O → α g o ∈ O := fun g o ho => by
    have h1 := Subgroup.characteristic_iff_map_eq.mp (inferInstance : O.Characteristic) (α g)
    rw [← h1]
    exact ⟨o, ho, rfl⟩
  obtain ⟨q, hq⟩ := θ.surjective b
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hfix : ∀ g : ↥B, ((α g w₀ : ↥M) : ↥M ⧸ O) = (w₀ : ↥M ⧸ O) := by
    intro g
    apply θ.injective
    apply Subtype.ext
    have h1 := hρ (inclusion hBN g) w₀
    have h2 : (M.normalizerMonoidHom (inclusion hBN g) w₀ : ↥M) = α g w₀ := rfl
    rw [h2] at h1
    rw [h1, hq]
    have h3 : (b : Perm (Fin r)) * ρ (inclusion hBN g) = ρ (inclusion hBN g) * b := hb g g.2
    calc ρ (inclusion hBN g) * (b : Perm (Fin r)) * (ρ (inclusion hBN g))⁻¹ =
        (b : Perm (Fin r)) * ρ (inclusion hBN g) * (ρ (inclusion hBN g))⁻¹ := by rw [h3]
      _ = b := by group
  have hinv : ∀ (g : ↥B) (x : ↥M), w₀⁻¹ * x ∈ O → w₀⁻¹ * α g x ∈ O := by
    intro g x hx
    have h1 : w₀⁻¹ * α g w₀ ∈ O := QuotientGroup.eq.mp (hfix g).symm
    have h2 : α g (w₀⁻¹ * x) ∈ O := hαO g _ hx
    have h3 : w₀⁻¹ * α g x = (w₀⁻¹ * α g w₀) * α g (w₀⁻¹ * x) := by
      rw [map_mul, map_inv]
      group
    rw [h3]
    exact mul_mem h1 h2
  obtain ⟨c, hc, hcfix⟩ :=
    (Semidihedral.Principal.coprime_invariant_coset_fixed 2 hB2 α O
      (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp (Nat.coprime_two_left.mp pPrimeCore_coprime_card)))
      w₀).2 hinv
  refine ⟨c, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro g hg
    have h1 := congrArg Subtype.val (hcfix ⟨g, hg⟩)
    rw [hα] at h1
    calc g * (c : X) = g * c * g⁻¹ * g := by group
      _ = c * g := by rw [h1]
  · have h1 : (c : ↥M ⧸ O) = (w₀ : ↥M ⧸ O) := (QuotientGroup.eq.mpr hc).symm
    rw [h1, hq]

theorem exists_centralizing_of_ne_one [Finite X] {X₀ A : Subgroup X}
    (hX₀N : X₀ ≤ normalizer (M : Set X)) (hodd : Odd (Nat.card X₀)) (hA2 : IsPGroup 2 A)
    (hAX : A ≤ normalizer (X₀ : Set X)) (hAN : A ≤ normalizer (M : Set X))
    (hA1 : ∀ (g : X) (hg : g ∈ A), ρ ⟨g, hAN hg⟩ = 1) {x : X} (hx : x ∈ X₀)
    (hx1 : ρ ⟨x, hX₀N hx⟩ ≠ 1) :
    ∃ (x' : X) (hx' : x' ∈ X₀), x' ∈ centralizer (A : Set X) ∧ ρ ⟨x', hX₀N hx'⟩ ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let α : ↥A →* MulAut ↥X₀ := X₀.normalizerMonoidHom.comp (inclusion hAX)
  have hα : ∀ (g : ↥A) (y : ↥X₀), ((α g y : ↥X₀) : X) = (g : X) * y * (g : X)⁻¹ :=
    fun _ _ => rfl
  set K : Subgroup ↥X₀ := (ρ.comp (inclusion hX₀N)).ker with hKdef
  have hKodd : ¬ 2 ∣ Nat.card K := by
    have h1 : Nat.card K ∣ Nat.card X₀ := Subgroup.card_subgroup_dvd_card K
    exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h.trans h1))
  have hρα : ∀ (g : ↥A) (y : ↥X₀), ρ (inclusion hX₀N (α g y)) = ρ (inclusion hX₀N y) := by
    intro g y
    have h1 : inclusion hX₀N (α g y) =
        ⟨g, hAN g.2⟩ * inclusion hX₀N y * (⟨g, hAN g.2⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, hA1 g g.2, one_mul, inv_one, mul_one]
  have hinv : ∀ (g : ↥A) (y : ↥X₀), (⟨x, hx⟩ : ↥X₀)⁻¹ * y ∈ K →
      (⟨x, hx⟩ : ↥X₀)⁻¹ * α g y ∈ K := by
    intro g y hy
    rw [hKdef, MonoidHom.mem_ker] at hy ⊢
    rw [map_mul, map_inv] at hy ⊢
    change (ρ (inclusion hX₀N ⟨x, hx⟩))⁻¹ * ρ (inclusion hX₀N (α g y)) = 1
    rw [hρα]
    exact hy
  obtain ⟨c, hc, hcfix⟩ :=
    (Semidihedral.Principal.coprime_invariant_coset_fixed 2 hA2 α K hKodd ⟨x, hx⟩).2 hinv
  refine ⟨c, c.2, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro g hg
    have h1 := congrArg Subtype.val (hcfix ⟨g, hg⟩)
    rw [hα] at h1
    calc g * (c : X) = g * c * g⁻¹ * g := by group
      _ = c * g := by rw [h1]
  · have h1 : ρ (inclusion hX₀N ((⟨x, hx⟩ : ↥X₀)⁻¹ * c)) = 1 := hc
    simp only [map_mul, map_inv] at h1
    rw [inv_mul_eq_one] at h1
    intro h2
    apply hx1
    rw [show (⟨x, hX₀N hx⟩ : ↥(normalizer (M : Set X))) = inclusion hX₀N ⟨x, hx⟩ from rfl, h1]
    exact h2

end CFSG.ComponentClassification.SolMax
