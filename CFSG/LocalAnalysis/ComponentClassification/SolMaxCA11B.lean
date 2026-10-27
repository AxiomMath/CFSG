module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9H
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDiagB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDiagC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36K

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem le_of_diagonal [Finite X] {H : Subgroup X} {e₀ e₁ : X} (he₁2 : e₁ * e₁ = 1)
    (he₁C : e₁ ∈ centralizer ({e₀} : Set X))
    (hCC : centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X) ≤ H)
    (hOC : coreNOf (centralizer ({e₀} : Set X)) ≤ H)
    {L₀ F : Subgroup X} (hL₀C : L₀ ≤ centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hL₀pc : IsPComponent 2
      (L₀.subgroupOf (centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X))))
    (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 7)) (hFL₀ : F ≤ L₀)
    (hF2 : IsPGroup 2 F) (hFH : normalizer (F : Set X) ≤ H) {DY : Finset (Fin 7)}
    (hDY : DY.card = 4)
    (hFY : ∀ l : ↥L₀, (l : X) ∈ F → ∀ y ∉ DY,
      ((χ (l : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) y = y)
    {N : Subgroup X} (hNC : N ≤ centralizer ({e₀} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X))))
    (hL₀N : L₀ ≤ N ⊔ N.map (MulAut.conj e₁).toMonoidHom)
    (hne : N.map (MulAut.conj e₁).toMonoidHom ≠ N)
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin 7)) : N ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  obtain ⟨hNsC, hNspc⟩ := isPComponent_conj hNC hNpc he₁C
  have hNsK : N.map (MulAut.conj e₁).toMonoidHom ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNC hNsC hNpc hNspc (Ne.symm hne)
  have hNsN : N.map (MulAut.conj e₁).toMonoidHom ≤ normalizer (N : Set X) :=
    fun z hz => (hNsK hz).1
  have hL₀NN : L₀ ≤ normalizer (N : Set X) := hL₀N.trans (sup_le le_normalizer hNsN)
  have hNO : coreNOf N ≤ coreNOf (centralizer ({e₀} : Set X)) :=
    pPrimeCore_le_of_isPComponent hNC hNpc
  have hOH : coreNOf N ≤ H := hNO.trans hOC
  have hL₀H : L₀ ≤ H := hL₀C.trans hCC
  have hL₀perf : ⁅L₀, L₀⁆ = L₀ := UnbalancedCorr.commutator_eq_of_isPComponent hL₀C hL₀pc
  have hres := primeResidual_eq_top_of_isPComponent hL₀C hL₀pc
  obtain ⟨ρZ, hρZ⟩ := exists_isPermActionZ (N := N) (by norm_num) (by norm_num) ψ
  obtain ⟨DN, hDN, hDNs⟩ := exists_support_of_diagonal hNC hNpc he₁C hL₀N
    (hL₀C.trans inf_le_left) hL₀perf hres hne χ hρZ hL₀NN hFL₀ hFY
  obtain ⟨c, hcZ, hcF⟩ := exists_three_element hρZ (hFL₀.trans hL₀NN) (hDN.trans hDY) hDNs
  have hcH : (c : X) ∈ H := by
    have h1 : (c : X)⁻¹ ∈ H := by
      refine mem_of_map_conj_le_sup_odd hFH (hFL₀.trans hL₀H) hOH hF2
        (fun f hf => le_normalizer_pPrimeCore (hL₀NN (hFL₀ hf))) (odd_coreNOf N) ?_
      rintro _ ⟨f, hf, rfl⟩
      have ho : (c : X)⁻¹ * (f * c * f⁻¹) ∈ coreNOf N := ⟨_, hcF f hf, rfl⟩
      have h4 : (MulAut.conj (c : X)⁻¹).toMonoidHom f = (c : X)⁻¹ * (f * c * f⁻¹) * f := by
        change (c : X)⁻¹ * f * (c : X)⁻¹⁻¹ = _
        group
      rw [h4]
      exact mul_mem (mem_sup_right ho) (mem_sup_left hf)
    simpa using inv_mem h1
  have hδ : ∀ x ∈ N, x * (e₁ * x * e₁⁻¹) ∈ H := fun x hx =>
    mul_conj_mem he₁C he₁2 hNC hNsK hNO hCC hOC hx
  exact le_of_conj_mem hN (by norm_num) ψ hOH
    (fun x hx y hy hyH => conj_mem_of_mul_conj_mem hNsK hOH hδ hx hy hyH) hcH hcZ

theorem le_card_range_of_fusionZStar [Finite X] {G : Type*} [Group G] {N : Subgroup X}
    (hN : ⁅N, N⁆ = N) {k : ℕ} (hk : 5 ≤ k)
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin k)) (f : ↥N →* G)
    (hO : ∀ x ∈ pPrimeCore 2 ↥N, f x = 1) (hf : ∃ x, f x ≠ 1) :
    k.factorial / 2 ≤ Nat.card f.range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Open.fusionZStar ↥N with hZdef
  set π : ↥N →* alternatingGroup (Fin k) := ψ.toMonoidHom.comp (QuotientGroup.mk' Z) with hπdef
  have hπs : Function.Surjective π := ψ.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hπ : ∀ n, π n = 1 ↔ n ∈ Z := fun n => by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsimple : IsSimpleGroup (alternatingGroup (Fin k)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have : (f.ker.map π).Normal := Normal.map f.normal_ker π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map π) with h | h
  ·
    have hKZ : f.ker ≤ Z := fun x hx => (hπ x).mp (by
      have h1 : π x ∈ f.ker.map π := mem_map_of_mem π hx
      rwa [h, mem_bot] at h1)
    have hidx := index_dvd_of_le hKZ
    rw [index_ker] at hidx
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hZidx : Z.index = k.factorial / 2 := by
      rw [Subgroup.index, Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rw [hZidx] at hidx
    have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
    exact Nat.le_of_dvd Nat.card_pos hidx
  · exfalso
    obtain ⟨x₀, hx₀⟩ := hf
    have hdec : ∀ x : ↥N, ∃ z ∈ Z, f x = f z := by
      intro x
      obtain ⟨y, hy, hyx⟩ : π x ∈ f.ker.map π := by rw [h]; exact mem_top _
      refine ⟨y⁻¹ * x, (hπ _).mp (by rw [map_mul, map_inv, hyx, inv_mul_cancel]), ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hy, inv_one, one_mul]
    have hZc : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, f z₁ * f z₂ = f z₂ * f z₁ := by
      intro z₁ hz₁ z₂ _
      rw [hZdef, Sol78.fusionZStar_eq_comap, mem_comap] at hz₁
      have hc := mem_center_iff.mp hz₁ (QuotientGroup.mk' (pPrimeCore 2 ↥N) z₂)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at hc
      have h2 := hO _ hc
      rw [map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at h2
      exact h2.symm
    have hle : commutator ↥N ≤ f.ker := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      obtain ⟨z₁, hz₁, h1⟩ := hdec a
      obtain ⟨z₂, hz₂, h2⟩ := hdec b
      rw [h1, h2]
      exact hZc z₁ hz₁ z₂ hz₂
    have hNc : commutator ↥N = ⊤ := by
      apply map_injective N.subtype_injective
      rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
      exact hN
    rw [hNc] at hle
    exact hx₀ (hle (mem_top x₀))

variable {M : Subgroup X} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)}

theorem false_of_two_components_of_kerZ (hρ : IsPermAction θ ρ) [Finite X]
    {H : Subgroup X} (hHN : H ≤ normalizer (M : Set X)) {e₀ : X} (he₀H : e₀ ∈ H)
    (he₀2 : e₀ * e₀ = 1) (he₀4 : (ρ ⟨e₀, hHN he₀H⟩).support.card = 4)
    (hOH : (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype ≤ H)
    {N N' : Subgroup X} (hNC : N ≤ centralizer ({e₀} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X))))
    (hN'C : N' ≤ centralizer ({e₀} : Set X))
    (hN'pc : IsPComponent 2 (N'.subgroupOf (centralizer ({e₀} : Set X)))) (hne : N ≠ N')
    (hNH : N ≤ H) (hN'H : N' ≤ H) (hNK : ¬ N ≤ UnbalancedLayer.coreActionKernel M)
    (hN'K : ¬ N' ≤ UnbalancedLayer.coreActionKernel M)
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin 7))
    (ψ' : ↥N' ⧸ Open.fusionZStar ↥N' ≃* alternatingGroup (Fin 7)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he₀N : e₀ ∈ normalizer (M : Set X) := hHN he₀H
  have hNN : N ≤ normalizer (M : Set X) := hNH.trans hHN
  have hN'N : N' ≤ normalizer (M : Set X) := hN'H.trans hHN
  have hNperf : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  have hN'perf : ⁅N', N'⁆ = N' := UnbalancedCorr.commutator_eq_of_isPComponent hN'C hN'pc
  have hρO : ∀ (o : X) (ho : o ∈ (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype), ρ ⟨o, hHN (hOH ho)⟩ = 1 := fun o ho =>
    rho_eq_one_of_mem_oddCore hρ (by norm_num) he₀N he₀2 he₀4 (hOH.trans hHN) ho
  set f : ↥N →* Perm (Fin 11) := ρ.comp (inclusion hNN) with hfdef
  set f' : ↥N' →* Perm (Fin 11) := ρ.comp (inclusion hN'N) with hf'def
  have hN'K' : N' ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNC hN'C hNpc hN'pc hne
  have hcomm : ∀ x : ↥N, ∀ x' : ↥N', f x * f' x' = f' x' * f x := by
    intro x x'
    obtain ⟨-, hK⟩ := UnbalancedLayer.mem_coreActionKernel.mp (hN'K' x'.2)
    obtain ⟨c, hc, hceq⟩ := hK (x : X) x.2
    have hcO : (x : X)⁻¹ * (x' : X)⁻¹ * x * x' ∈
        (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map (centralizer ({e₀} : Set X)).subtype :=
      pPrimeCore_le_of_isPComponent hNC hNpc ⟨c, hc, hceq⟩
    have h1 := hρO _ hcO
    have h2 : (⟨(x : X)⁻¹ * (x' : X)⁻¹ * x * x', hHN (hOH hcO)⟩ : ↥(normalizer (M : Set X))) =
        (inclusion hNN x)⁻¹ * (inclusion hN'N x')⁻¹ * inclusion hNN x * inclusion hN'N x' := rfl
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    change ρ (inclusion hNN x) * ρ (inclusion hN'N x') =
      ρ (inclusion hN'N x') * ρ (inclusion hNN x)
    calc ρ (inclusion hNN x) * ρ (inclusion hN'N x') =
        ρ (inclusion hN'N x') * ρ (inclusion hNN x) *
          ((ρ (inclusion hNN x))⁻¹ * (ρ (inclusion hN'N x'))⁻¹ * ρ (inclusion hNN x) *
            ρ (inclusion hN'N x')) := by group
      _ = ρ (inclusion hN'N x') * ρ (inclusion hNN x) := by rw [h1, mul_one]
  set K₀ := (fixAlt (ρ ⟨e₀, he₀N⟩)).map (alternatingGroup (Fin 11)).subtype with hK₀def
  have hfK : f.range ≤ K₀ := by
    rintro _ ⟨x, rfl⟩
    have hxo : (x : X) ∈ oddGen N := by rw [oddGen_eq_of_perfect hNperf]; exact x.2
    exact rho_mem_fixAlt_of_mem_oddGen he₀N he₀2 he₀4.le hNN hNC hxo (hNN x.2)
  have hf'K : f'.range ≤ K₀ := by
    rintro _ ⟨x, rfl⟩
    have hxo : (x : X) ∈ oddGen N' := by rw [oddGen_eq_of_perfect hN'perf]; exact x.2
    exact rho_mem_fixAlt_of_mem_oddGen he₀N he₀2 he₀4.le hN'N hN'C hxo (hN'N x.2)
  have hK₀card : Nat.card K₀ = 2520 := by
    rw [hK₀def, card_map_of_injective (alternatingGroup (Fin 11)).subtype_injective,
      card_fixAlt (by rw [he₀4]; norm_num), he₀4]
    rfl
  have hbig : ∀ {P : Subgroup X} (hPN : P ≤ normalizer (M : Set X)), ⁅P, P⁆ = P →
      P ≤ centralizer ({e₀} : Set X) →
      IsPComponent 2 (P.subgroupOf (centralizer ({e₀} : Set X))) →
      ¬ P ≤ UnbalancedLayer.coreActionKernel M →
      (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 7)) →
      2520 ≤ Nat.card (ρ.comp (inclusion hPN)).range := by
    intro P hPN hPperf hPC hPpc hPK ψP
    have h1 := le_card_range_of_fusionZStar hPperf (by norm_num) ψP (ρ.comp (inclusion hPN))
      (fun x hx => hρO _ (pPrimeCore_le_of_isPComponent hPC hPpc ⟨x, hx, rfl⟩)) (by
        by_contra hall
        push Not at hall
        exact hPK fun x hx => hρ.mem_coreActionKernel (hPN hx) (hall ⟨x, hx⟩))
    exact h1
  have hf2520 : 2520 ≤ Nat.card f.range := hbig hNN hNperf hNC hNpc hNK ψ
  have hf'2520 : 2520 ≤ Nat.card f'.range := hbig hN'N hN'perf hN'C hN'pc hN'K ψ'
  have hfeq : f.range = K₀ := eq_of_le_of_card_ge hfK (by rw [hK₀card]; exact hf2520)
  have hf'eq : f'.range = K₀ := eq_of_le_of_card_ge hf'K (by rw [hK₀card]; exact hf'2520)
  have hab : ∀ a ∈ f.range, ∀ b ∈ f.range, a * b = b * a := by
    rintro a ⟨x, rfl⟩ b hb
    rw [hfeq, ← hf'eq] at hb
    obtain ⟨x', rfl⟩ := hb
    exact hcomm x x'
  have htriv : f.range = ⊥ := by
    have h1 : ⁅f.range, f.range⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [mem_centralizer_iff]
      intro b hb
      exact (hab a ha b hb).symm
    have h2 : ⁅f.range, f.range⁆ = f.range := by
      have hNc : commutator ↥N = ⊤ := by
        apply map_injective N.subtype_injective
        rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
        exact hNperf
      rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def, hNc]
    exact h2.symm.trans h1
  have h3 : Nat.card f.range = 1 := by rw [htriv, card_bot]
  omega

end CFSG.ComponentClassification.SolMax
