module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP3

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapP2

theorem fixedLayer_fixedLayer_facts [Finite X] {C L : Subgroup X} {n : ℕ} (hLC : L ≤ C)
    (hLpc : IsPComponent 2 (L.subgroupOf C))
    {θ : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (L : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {c r : X}
    (hcN : c ∈ normalizer (L : Set X)) (hc2 : c * c = 1)
    (h4 : (ρ ⟨c, hcN⟩).support.card ≤ 4) (h5 : 5 ≤ n - (ρ ⟨c, hcN⟩).support.card)
    (hcC : centralizer ({c} : Set X) ≤ C) (hrc : r * c = c * r) (hr2 : r * r = 1) (hr1 : r ≠ 1)
    (hrN : r ∈ normalizer (L : Set X))
    (hrK : r ∈ UnbalancedLayer.coreActionKernel L ∨
      r * c⁻¹ ∈ UnbalancedLayer.coreActionKernel L) :
    GSLit.fixedLayer (GSLit.fixedLayer L (zpowers c)) (zpowers r) ≤
        centralizer ({r} : Set X) ⊓ centralizer ({c} : Set X) ∧
      IsPComponent 2 ((GSLit.fixedLayer (GSLit.fixedLayer L (zpowers c)) (zpowers r)).subgroupOf
        (centralizer ({r} : Set X) ⊓ centralizer ({c} : Set X))) ∧
      GSLit.fixedLayer (GSLit.fixedLayer L (zpowers c)) (zpowers r) ≤ L ∧
      ∀ (x : X) (hx : x ∈ L), x * c = c * x → x * r = r * x → x * x = 1 →
        (coreImage θ hx).support ⊆ (ρ ⟨c, hcN⟩).supportᶜ →
        x ∈ GSLit.fixedLayer (GSLit.fixedLayer L (zpowers c)) (zpowers r) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Jb, hJb, hJbpc, hmem, -, -, -⟩ := exists_fixed_component_of_perm hLC hLpc hρ hcN hc2 h5
  obtain ⟨hAle, hApc, -⟩ := fixedLayer_facts_of_perm hLC hLpc hρ hcN hc2 h4 h5
  have hCc : C ⊓ centralizer ({c} : Set X) = centralizer ({c} : Set X) := inf_eq_right.mpr hcC
  rw [hCc] at hAle hApc hJbpc
  set A := GSLit.fixedLayer L (zpowers c) with hAdef
  set Y : Subgroup X := L ⊓ centralizer ({c} : Set X) with hYdef
  have hJbA : Jb ≤ A := by
    have hfl : A = (pLayer ↥Y 2).map Y.subtype := by
      rw [hAdef]
      unfold GSLit.fixedLayer
      rw [centralizer_zpowers_eq' c]
    have hJbpc' : IsPComponent 2 (Jb.subgroupOf Y) :=
      CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hJb inf_le_right hJbpc
    have hle : Jb.subgroupOf Y ≤ pLayer ↥Y 2 := le_sSup hJbpc'
    rw [hfl]
    intro x hx
    exact ⟨⟨x, hJb hx⟩, hle hx, rfl⟩
  obtain ⟨-, -, hAq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 A _ hAle).mp hApc
  have hAsub : (A.subgroupOf (centralizer ({c} : Set X))).IsSubnormal := hApc.choose_spec.2.1
  have hAL : A ≤ L := (GSLit.fixedLayer_le_inf L (zpowers c)).trans inf_le_left
  have hrcC : r ∈ centralizer ({c} : Set X) := mem_centralizer_singleton_iff.mpr hrc
  have hrA : r ∈ normalizer (A : Set X) := by
    refine GSLit.mem_normalizer_fixedLayer hrN (centralizer_le_normalizer _ ?_)
    rw [centralizer_zpowers_eq' c]
    exact hrcC
  have hcA : c ∈ normalizer (A : Set X) :=
    GSLit.mem_normalizer_fixedLayer hcN (le_normalizer (mem_zpowers c))
  have hrKA : r ∈ UnbalancedLayer.coreActionKernel A := by
    rcases hrK with h | h
    · exact mem_coreActionKernel_of_le hAL h hrA
    · have h1 : r * c⁻¹ ∈ UnbalancedLayer.coreActionKernel A :=
        mem_coreActionKernel_of_le hAL h (mul_mem hrA (inv_mem hcA))
      have h2 : c ∈ UnbalancedLayer.coreActionKernel A := by
        refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨hcA, fun j hj => ?_⟩
        have hjc : j * c = c * j := mem_centralizer_singleton_iff.mp (hAle hj)
        have h4 : j⁻¹ * c⁻¹ * j * c = 1 := by
          rw [show j⁻¹ * c⁻¹ * j * c = j⁻¹ * c⁻¹ * (j * c) by group, hjc]
          group
        rw [h4]
        exact one_mem _
      have h3 := mul_mem h1 h2
      rwa [inv_mul_cancel_right] at h3
  have hr2' : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hr2) hr1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2', pow_one])
  have hArpc := GSLit.fixedLayer_isPComponent hAle hAsub (zpowers_le.mpr hrcC)
    (zpowers_le.mpr hrKA) hR2 hAq
  rw [centralizer_zpowers_eq' r, inf_comm (centralizer ({c} : Set X))] at hArpc
  have hArle : GSLit.fixedLayer A (zpowers r) ≤
      centralizer ({r} : Set X) ⊓ centralizer ({c} : Set X) := by
    have h1 := GSLit.fixedLayer_le_inf A (zpowers r)
    rw [centralizer_zpowers_eq' r] at h1
    exact le_inf (h1.trans inf_le_right) ((h1.trans inf_le_left).trans hAle)
  refine ⟨hArle, hArpc, (GSLit.fixedLayer_le_inf A (zpowers r)).trans (inf_le_left.trans hAL),
    fun x hx hxc hxr hx2 hsupp => ?_⟩
  have hxA : x ∈ A := hJbA (hmem x hx hxc ⟨1, by rw [pow_one, sq]; exact hx2⟩ hsupp)
  have hle : zpowers x ≤ GSLit.fixedLayer A (zpowers r) := by
    refine le_fixedLayer_of_primeResidual hAq (zpowers_le.mpr hrKA) hR2 ?_ ?_
    · rw [zpowers_le, centralizer_zpowers_eq' r]
      exact ⟨hxA, mem_centralizer_singleton_iff.mpr hxr⟩
    · exact eq_top_iff.mpr (CatalogueBPrimeJoin.pSubgroup_le_residual 2 ⊤
        ((isPGroup_zpowers_of_mul_self hx2).to_subgroup ⊤))
  exact hle (mem_zpowers x)

theorem le_coreActionKernel_of_commute_pump [Finite X] {r e₀ : X} {A B N : Subgroup X} {k m : ℕ}
    (hk : 7 ≤ k) (he₀r : e₀ ∈ centralizer ({r} : Set X)) (he₀o : orderOf e₀ = 2)
    (hAC : A ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hApc : IsPComponent 2
      (A.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    (χ : ↥A ⧸ pPrimeCore 2 ↥A ≃* alternatingGroup (Fin k))
    (hBC : B ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hBpc : IsPComponent 2
      (B.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    (hBA : ∀ x ∈ B, ∀ z ∈ A, x * z * x⁻¹ * z⁻¹ ∈ (pPrimeCore 2 ↥A).map A.subtype)
    (hNC : N ≤ centralizer ({r} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({r} : Set X))))
    (hAN : A ≤ N ⊔ N.map (MulAut.conj e₀).toMonoidHom)
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin m)) (hkm : k ≤ m) (hmk : m ≤ k + 4)
    (hcase : m = k ∨ (N.map (MulAut.conj e₀).toMonoidHom = N ∧
      IsPComponent 2 (A.subgroupOf (N ⊓ centralizer ({e₀} : Set X))))) :
    B ≤ UnbalancedLayer.coreActionKernel N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq, ← he₀o, pow_orderOf_eq_one]
  have hcase' : m = k ∨ ∃ t : X, t ∈ normalizer (N : Set X) ∧ t * t = 1 ∧ A ≤ N ∧
      A ≤ centralizer ({t} : Set X) ∧
      IsPComponent 2 (A.subgroupOf (N ⊓ centralizer ({t} : Set X))) := by
    rcases hcase with h | ⟨hfix, hpc⟩
    · exact Or.inl h
    · refine Or.inr ⟨e₀, mem_normalizer_iff_map_conj_eq.mpr hfix, he₀2, ?_,
        hAC.trans inf_le_right, hpc⟩
      have h1 := hAN
      rwa [hfix, sup_idem] at h1
  set Nx := N.map (MulAut.conj e₀).toMonoidHom with hNxdef
  obtain ⟨hNxC, hNxpc⟩ := isPComponent_conj hNC hNpc he₀r
  have hNxN : Nx ≤ normalizer (N : Set X) := by
    by_cases h : Nx = N
    · rw [h]
      exact le_normalizer
    · exact fun z hz =>
        (GSThmB.B5a.le_coreActionKernel_of_ne hNC hNxC hNpc hNxpc (Ne.symm h) hz).1
  have hYN : N ⊔ Nx ≤ normalizer (N : Set X) := sup_le le_normalizer hNxN
  have hAN' : A ≤ normalizer (N : Set X) := hAN.trans hYN
  have hm6 : m ≠ 6 := by omega
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := N) (by omega) hm6 θN
  have hAperf : ⁅A, A⁆ = A := UnbalancedCorr.commutator_eq_of_isPComponent hAC hApc
  obtain ⟨-, hAres, hAq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 A _ hAC).mp hApc
  have hne := exists_ne_one_of_pump hNC hNpc he₀r hAN (hAC.trans inf_le_right) hAperf
    (LocalCores.isQuasisimple_nontrivial hAq) (r := m) (by omega) hρ hAN'
  obtain ⟨τ, hτk, ψ, hψ⟩ := exists_image_equiv (M := N) (Je := A) hk hkm hm6 θN hρ hAN' hAres
    hAperf (Fintype.card_fin k) χ hne hcase'
  have hsm : τ.support.card ≤ m := by
    have h1 := Finset.card_le_univ τ.support
    rwa [Fintype.card_fin] at h1
  have h4 : τ.support.card ≤ 4 := by omega
  have h5 : 5 ≤ m - τ.support.card := by omega
  have hρO : ∀ (w : X) (hw : w ∈ (pPrimeCore 2 ↥A).map A.subtype),
      ρ ⟨w, hAN' (map_subtype_le _ hw)⟩ = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hψ w
    rw [(QuotientGroup.eq_one_iff w).mpr hw, map_one] at h1
    have h2 : ρ ⟨(w : X), hAN' w.2⟩ = 1 := by rw [← h1]; rfl
    exact h2
  obtain ⟨N₃, hN₃C, hN₃pc, hBN₃, -⟩ := exists_pump_in he₀r he₀o hBC hBpc
  obtain ⟨hN₃xC, hN₃xpc⟩ := isPComponent_conj hN₃C hN₃pc he₀r
  by_cases hcov : N₃ = N ∨ N₃ = Nx
  swap
  · push Not at hcov
    have hK1 : N₃ ≤ UnbalancedLayer.coreActionKernel N :=
      GSThmB.B5a.le_coreActionKernel_of_ne hNC hN₃C hNpc hN₃pc (Ne.symm hcov.1)
    have hcc : (N₃.map (MulAut.conj e₀).toMonoidHom).map (MulAut.conj e₀).toMonoidHom = N₃ :=
      conjBy_conjBy_of_mul_self N₃ he₀2
    have hN₃x : N₃.map (MulAut.conj e₀).toMonoidHom ≠ N := by
      intro h
      apply hcov.2
      rw [hNxdef, ← h, hcc]
    have hK2 : N₃.map (MulAut.conj e₀).toMonoidHom ≤ UnbalancedLayer.coreActionKernel N :=
      GSThmB.B5a.le_coreActionKernel_of_ne hNC hN₃xC hNpc hN₃xpc (Ne.symm hN₃x)
    exact hBN₃.trans (sup_le hK1 hK2)
  have hBN : B ≤ normalizer (N : Set X) := by
    rcases hcov with h | h
    · rw [h] at hBN₃
      exact hBN₃.trans hYN
    · have hcc : (N.map (MulAut.conj e₀).toMonoidHom).map (MulAut.conj e₀).toMonoidHom = N :=
        conjBy_conjBy_of_mul_self N he₀2
      have h1 : N₃.map (MulAut.conj e₀).toMonoidHom = N := by
        rw [h, hNxdef, hcc]
      rw [h1, h, sup_comm] at hBN₃
      exact hBN₃.trans hYN
  set φ : ↥B →* Perm (Fin m) := ρ.comp (inclusion hBN) with hφdef
  have hBperf : ⁅B, B⁆ = B := UnbalancedCorr.commutator_eq_of_isPComponent hBC hBpc
  have htop : ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hBperf]
  have hPperf : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, htop]
  have hc : ∀ p ∈ φ.range, ∀ σ ∈ fixAlt τ, p * (σ : Perm (Fin m)) = σ * p := by
    rintro _ ⟨x, rfl⟩ σ hσ
    obtain ⟨q, hq⟩ := ψ.surjective ⟨σ, hσ⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    have hzσ : ρ ⟨z, hAN' z.2⟩ = (σ : Perm (Fin m)) := by rw [← hψ z, hq]
    have hw := hBA x x.2 z z.2
    have hw1 := hρO _ hw
    have e1 : (⟨(x : X) * z * (x : X)⁻¹ * (z : X)⁻¹, hAN' (map_subtype_le _ hw)⟩ :
        ↥(normalizer (N : Set X))) = ⟨x, hBN x.2⟩ * ⟨z, hAN' z.2⟩ * (⟨x, hBN x.2⟩)⁻¹ *
          (⟨z, hAN' z.2⟩)⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hzσ] at hw1
    change ρ ⟨x, hBN x.2⟩ * σ = σ * ρ ⟨x, hBN x.2⟩
    calc ρ ⟨x, hBN x.2⟩ * σ = (ρ ⟨x, hBN x.2⟩ * σ * (ρ ⟨x, hBN x.2⟩)⁻¹ * (σ : Perm (Fin m))⁻¹) *
        (σ * ρ ⟨x, hBN x.2⟩) := by group
      _ = σ * ρ ⟨x, hBN x.2⟩ := by rw [hw1, one_mul]
  have hP := eq_bot_of_perfect_of_commute_fixAlt h4 h5 hPperf hc
  intro x hx
  have h1 : φ ⟨x, hx⟩ = 1 := by
    have h2 : φ ⟨x, hx⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hP, mem_bot] at h2
    exact h2
  exact hρ.mem_coreActionKernel (hBN hx) h1

end SwapP2

end CFSG.ComponentClassification.SolMax
