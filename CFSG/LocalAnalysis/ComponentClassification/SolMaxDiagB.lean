module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDiagA
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36H

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

variable {X : Type} [Group X]

theorem exists_support_of_diagonal [Finite X] {Y N L₀ F : Subgroup X} {x : X} (hNY : N ≤ Y)
    (hNpc : IsPComponent 2 (N.subgroupOf Y)) (hxY : x ∈ Y)
    (hL₀N : L₀ ≤ N ⊔ N.map (MulAut.conj x).toMonoidHom)
    (hL₀C : L₀ ≤ centralizer ({x} : Set X)) (hL₀perf : ⁅L₀, L₀⁆ = L₀)
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥L₀ = ⊤)
    (hne : N.map (MulAut.conj x).toMonoidHom ≠ N)
    (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 7))
    {ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin 7)}
    {ρ : ↥(normalizer (N : Set X)) →* Perm (Fin 7)} (hρ : IsPermActionZ ψ ρ)
    (hL₀NN : L₀ ≤ normalizer (N : Set X)) (hFL₀ : F ≤ L₀) {DY : Finset (Fin 7)}
    (hFY : ∀ l : ↥L₀, (l : X) ∈ F → ∀ y ∉ DY,
      ((χ (l : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) y = y) :
    ∃ DN : Finset (Fin 7), DN.card = DY.card ∧
      ∀ (f : X) (hf : f ∈ F), ∀ ω ∉ DN, ρ ⟨f, hL₀NN (hFL₀ hf)⟩ ω = ω := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNY hNpc
  have hL₀q : Nontrivial (↥L₀ ⧸ pPrimeCore 2 ↥L₀) := by
    have : Nontrivial (Fin 7) := Fin.nontrivial_iff_two_le.mpr (by norm_num)
    have : Nontrivial (alternatingGroup (Fin 7)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; norm_num)
    exact χ.toEquiv.nontrivial
  have hne' : ∃ l : ↥L₀, ρ (inclusion hL₀NN l) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply not_le_coreActionKernel_of_pump hNY hNpc hxY hL₀N hL₀C hL₀perf hL₀q hne
    intro l hl
    exact hρ.mem_coreActionKernel hN (hL₀NN hl) (hall ⟨l, hl⟩)
  have hA : ∀ l : ↥L₀, ρ (inclusion hL₀NN l) ∈ alternatingGroup (Fin 7) := by
    intro l
    have hperf : Group.IsPerfect ↥L₀ := (Subgroup.isPerfect_iff).mpr hL₀perf
    have h1 := Abelianization.commutator_subset_ker
      (Perm.sign.comp (ρ.comp (inclusion hL₀NN)))
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact h1 (mem_top l)
  let φ : ↥L₀ →* alternatingGroup (Fin 7) :=
    (ρ.comp (inclusion hL₀NN)).codRestrict (alternatingGroup (Fin 7)) hA
  obtain ⟨l₀, hl₀⟩ := hne'
  have hφ : φ l₀ ≠ 1 := fun h => hl₀ (congrArg Subtype.val h)
  have hQ : ∀ l, φ l ∈ fixAlt (1 : Perm (Fin 7)) := by
    intro l
    rw [mem_fixAlt]
    simp
  have hQc : Nat.card (fixAlt (1 : Perm (Fin 7))) ≤ Nat.factorial 7 / 2 := by
    rw [card_fixAlt (by simp)]
    simp
  obtain ⟨ψL, hψL⟩ := exists_coreQuot_equiv_of_hom hres (by norm_num) χ φ ⟨l₀, hφ⟩ hQ hQc
  obtain ⟨DN, hDN, -, hDNs⟩ := exists_support_of_mulEquiv_fixAlt (r := 7) (τ := 1)
    (le_refl 7) (Fintype.card_fin 7) (by simp) (χ.symm.trans ψL) DY
  refine ⟨DN, hDN, fun f hf ω hω => ?_⟩
  have h1 := hDNs (χ ((⟨f, hFL₀ hf⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀)) (hFY ⟨f, hFL₀ hf⟩ hf) ω hω
  have h2 : (χ.symm.trans ψL) (χ ((⟨f, hFL₀ hf⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀)) =
      ψL ((⟨f, hFL₀ hf⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) := by
    change ψL (χ.symm (χ _)) = _
    rw [MulEquiv.symm_apply_apply]
  rw [h2, hψL ⟨f, hFL₀ hf⟩] at h1
  exact h1

theorem mem_pPrimeCore_of_pow_three {G : Type*} [Group G] [Finite G] (α : MulAut G) {c : G}
    {s : ℕ} (hc : c ^ (3 ^ s) = 1) (hw : c⁻¹ * α c ∈ Open.fusionZStar G) :
    c⁻¹ * α c ∈ pPrimeCore 2 G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 G with hOdef
  set w := c⁻¹ * α c with hwdef
  set q : G →* G ⧸ O := QuotientGroup.mk' O with hqdef
  have hwc : q w ∈ center (G ⧸ O) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective O g
    have h1 := GSThmB.OddQuot.mem_fusionZStar_iff.mp hw m
    have h2 : q ⁅w, m⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  have hpow : (q w) ^ (3 ^ s) = 1 := by
    have h1 : α c = c * w := by rw [hwdef]; group
    have h2 : (c * w) ^ (3 ^ s) = 1 := by rw [← h1, ← map_pow, hc, map_one]
    have h3 : (q c * q w) ^ (3 ^ s) = 1 := by rw [← map_mul, ← map_pow, h2, map_one]
    have hcomm : Commute (q c) (q w) := mem_center_iff.mp hwc (q c)
    have h4 : (q c) ^ (3 ^ s) = 1 := by rw [← map_pow, hc, map_one]
    rw [hcomm.mul_pow, h4, one_mul] at h3
    exact h3
  have hnorm : (zpowers (q w)).Normal := ⟨fun z hz g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have hk : (q w) ^ k ∈ center (G ⧸ O) := zpow_mem hwc k
    rw [mem_center_iff.mp hk g, mul_assoc, mul_inv_cancel, mul_one]
    exact zpow_mem (mem_zpowers _) k⟩
  have hodd : Nat.Coprime 2 (Nat.card (zpowers (q w))) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hpow)
      (Nat.Coprime.pow_right s (by norm_num))
  have hbot :=
    (pPrimeCore_eq_bot_iff.mp (pPrimeCore_quotient_eq_bot Nat.prime_two)) _ hnorm hodd
  have h1 : q w = 1 := by
    have h2 : q w ∈ zpowers (q w) := mem_zpowers _
    rw [hbot, mem_bot] at h2
    exact h2
  exact (QuotientGroup.eq_one_iff w).mp h1

theorem exists_three_element [Finite X] {N F : Subgroup X}
    {ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin 7)}
    {ρ : ↥(normalizer (N : Set X)) →* Perm (Fin 7)} (hρ : IsPermActionZ ψ ρ)
    (hFN : F ≤ normalizer (N : Set X)) {DN : Finset (Fin 7)} (hDN : DN.card = 4)
    (hDNs : ∀ (f : X) (hf : f ∈ F), ∀ ω ∉ DN, ρ ⟨f, hFN hf⟩ ω = ω) :
    ∃ c : ↥N, c ∉ Open.fusionZStar ↥N ∧
      ∀ (f : X) (hf : f ∈ F), c⁻¹ * N.normalizerMonoidHom ⟨f, hFN hf⟩ c ∈ pPrimeCore 2 ↥N := by
  classical
  have hc3 : DNᶜ.card = 3 := by rw [Finset.card_compl, Fintype.card_fin, hDN]
  obtain ⟨a, b, d, hab, had, hbd, habd⟩ := Finset.card_eq_three.mp hc3
  have ha : a ∉ DN := Finset.mem_compl.mp (by rw [habd]; simp)
  have hb : b ∉ DN := Finset.mem_compl.mp (by rw [habd]; simp)
  have hd : d ∉ DN := Finset.mem_compl.mp (by rw [habd]; simp)
  set γ : Perm (Fin 7) := swap a b * swap a d with hγdef
  have hγ3 : γ.IsThreeCycle := Perm.isThreeCycle_swap_mul_swap_same hab had hbd
  have hγA : γ ∈ alternatingGroup (Fin 7) := hγ3.mem_alternatingGroup
  have hγD : ∀ ω ∈ DN, γ ω = ω := by
    intro ω hω
    have h1 : ω ≠ a := fun h => ha (h ▸ hω)
    have h2 : ω ≠ b := fun h => hb (h ▸ hω)
    have h3 : ω ≠ d := fun h => hd (h ▸ hω)
    rw [hγdef, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2]
  have hcomm : ∀ (f : X) (hf : f ∈ F), Commute (ρ ⟨f, hFN hf⟩) γ := by
    intro f hf
    refine Perm.Disjoint.commute fun ω => ?_
    by_cases hω : ω ∈ DN
    · exact Or.inr (hγD ω hω)
    · exact Or.inl (hDNs f hf ω hω)
  obtain ⟨q, hq⟩ := ψ.surjective ⟨γ, hγA⟩
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨s, m, hm3, hsm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c₀).ne' 3 (by norm_num)
  set c := c₀ ^ m with hcdef
  have hc : c ^ (3 ^ s) = 1 := by
    rw [hcdef, ← pow_mul, mul_comm, ← hsm, pow_orderOf_eq_one]
  have hψc : ((ψ (c : ↥N ⧸ Open.fusionZStar ↥N) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      γ ^ m := by
    rw [hcdef, QuotientGroup.mk_pow, map_pow, hq, SubgroupClass.coe_pow]
  refine ⟨c, fun hcZ => ?_, fun f hf => ?_⟩
  ·
    have h1 : (c : ↥N ⧸ Open.fusionZStar ↥N) = 1 := (QuotientGroup.eq_one_iff c).mpr hcZ
    rw [h1, map_one] at hψc
    have h2 : γ ^ m = 1 := by rw [← hψc]; rfl
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hγ3.orderOf] at h3
    exact hm3 h3
  · apply mem_pPrimeCore_of_pow_three _ hc
    apply hρ.mem_fusionZStar_of_commute
    rw [hψc]
    exact ((hcomm f hf).pow_right m).eq

end CFSG.ComponentClassification.SolMax
