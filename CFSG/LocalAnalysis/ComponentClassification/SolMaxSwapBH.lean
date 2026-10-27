module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBG
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBF

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

variable {X : Type} [Group X]

namespace SwapP2

theorem commutatorElement_mul_center_left {G : Type*} [Group G] {a c : G} (hc : c ∈ center G)
    (x : G) : ⁅a * c, x⁆ = ⁅a, x⁆ := by
  have h1 : c * x * c⁻¹ = x := by
    rw [← (mem_center_iff.mp hc x), mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * x * (a * c)⁻¹ * x⁻¹ = a * (c * x * c⁻¹) * a⁻¹ * x⁻¹ := by group
    _ = a * x * a⁻¹ * x⁻¹ := by rw [h1]

theorem commutatorElement_mul_center_right {G : Type*} [Group G] {b d : G} (hd : d ∈ center G)
    (x : G) : ⁅x, b * d⁆ = ⁅x, b⁆ := by
  have h1 : d * x⁻¹ * d⁻¹ = x⁻¹ := by
    rw [← (mem_center_iff.mp hd x⁻¹), mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (b * d) * x⁻¹ * (b * d)⁻¹ = x * b * (d * x⁻¹ * d⁻¹) * b⁻¹ := by group
    _ = x * b * x⁻¹ * b⁻¹ := by rw [h1]

theorem le_of_map_fusionZStar_eq_top [Finite X] {N H : Subgroup X} {m : ℕ} (hN : ⁅N, N⁆ = N)
    (ψN : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin m))
    (hOH : (pPrimeCore 2 ↥N).map N.subtype ≤ H)
    (hY : (H.subgroupOf N).map
      (ψN.toMonoidHom.comp (QuotientGroup.mk' (Open.fusionZStar ↥N))) = ⊤) :
    N ≤ H := by
  classical
  set πN := ψN.toMonoidHom.comp (QuotientGroup.mk' (Open.fusionZStar ↥N)) with hπNdef
  set q := QuotientGroup.mk' (pPrimeCore 2 ↥N) with hqdef
  have hdec : ∀ x : ↥N, ∃ h ∈ H.subgroupOf N, h⁻¹ * x ∈ Open.fusionZStar ↥N := by
    intro x
    obtain ⟨h, hh, hhx⟩ : πN x ∈ (H.subgroupOf N).map πN := by rw [hY]; exact mem_top _
    refine ⟨h, hh, ?_⟩
    have h1 : πN (h⁻¹ * x) = 1 := by rw [map_mul, map_inv, hhx, inv_mul_cancel]
    rw [hπNdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hcen : ∀ z ∈ Open.fusionZStar ↥N, q z ∈ center (↥N ⧸ pPrimeCore 2 ↥N) := by
    intro z hz
    rw [mem_center_iff]
    intro g
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥N) g
    have h1 := GSThmB.OddQuot.mem_fusionZStar_iff.mp hz w
    have h2 : q ⁅z, w⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  set L : Subgroup ↥N := H.subgroupOf N ⊔ pPrimeCore 2 ↥N with hLdef
  have htop : ⁅(⊤ : Subgroup ↥N), (⊤ : Subgroup ↥N)⁆ = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hN]
  have hL : (⊤ : Subgroup ↥N) ≤ L := by
    rw [← htop, commutator_le]
    intro x _ y _
    obtain ⟨h₁, hh₁, hz₁⟩ := hdec x
    obtain ⟨h₂, hh₂, hz₂⟩ := hdec y
    have key : ⁅h₁, h₂⁆⁻¹ * ⁅x, y⁆ ∈ pPrimeCore 2 ↥N := by
      rw [← QuotientGroup.eq_one_iff (N := pPrimeCore 2 ↥N)]
      change q (⁅h₁, h₂⁆⁻¹ * ⁅x, y⁆) = 1
      have hx : q x = q h₁ * q (h₁⁻¹ * x) := by rw [← map_mul, mul_inv_cancel_left]
      have hy : q y = q h₂ * q (h₂⁻¹ * y) := by rw [← map_mul, mul_inv_cancel_left]
      rw [map_mul, map_inv, map_commutatorElement, map_commutatorElement, hx, hy,
        commutatorElement_mul_center_left (hcen _ hz₁),
        commutatorElement_mul_center_right (hcen _ hz₂), inv_mul_cancel]
    have h3 : ⁅h₁, h₂⁆ ∈ L := by
      refine mem_sup_left ?_
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hh₁ hh₂) (inv_mem hh₁)) (inv_mem hh₂)
    have h4 := mul_mem h3 (mem_sup_right key)
    rwa [mul_inv_cancel_left] at h4
  have hO' : pPrimeCore 2 ↥N ≤ H.subgroupOf N := fun z hz => hOH ⟨z, hz, rfl⟩
  intro x hx
  exact (sup_le le_rfl hO') (hL (mem_top (⟨x, hx⟩ : ↥N)))

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X}

theorem le_of_diagonalZ (hs : Setting t J n e E D M) (hn : n = 11)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    (hOr : core (centralizer ({r} : Set X)) ≤ Hn E)
    (hFH : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E)
    (χr : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin 7))
    (hArle : fixA M e₀ r ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hArpc : IsPComponent 2 ((fixA M e₀ r).subgroupOf
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    {N : Subgroup X} (hNC : N ≤ centralizer ({r} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({r} : Set X))))
    (hcov : fixA M e₀ r ≤ N ⊔ conjBy N e₀) (hdiag : conjBy N e₀ ≠ N)
    (ψN : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin 7)) : N ≤ Hn E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  set Ar := fixA M e₀ r with hArdef
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) hd.e₀1
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  obtain ⟨hNxC, hNxpc⟩ := isPComponent_conj hNC hNpc he₀r
  have hNxK : conjBy N e₀ ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNC hNxC hNpc hNxpc (Ne.symm hdiag)
  set Y := N ⊔ conjBy N e₀ with hYdef
  have hYN : Y ≤ normalizer (N : Set X) := sup_le le_normalizer (fun z hz => (hNxK hz).1)
  have hArN : Ar ≤ normalizer (N : Set X) := hcov.trans hYN
  have hArM : Ar ≤ M :=
    ((GSLit.fixedLayer_le_inf _ (zpowers r)).trans inf_le_left).trans
      ((GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left)
  have hN : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  have hArperf : ⁅Ar, Ar⁆ = Ar := UnbalancedCorr.commutator_eq_of_isPComponent hArle hArpc
  obtain ⟨ρ, hρ, hsurj, -, -⟩ := exists_permActionZ_of_diagonal (k := 7) (by norm_num) (by norm_num)
    he₀r hArle hArpc χr hNC hNpc hcov hdiag ψN hArN
  have hYC : Y ≤ centralizer ({r} : Set X) := sup_le hNC hNxC
  have hYsub : (Y.subgroupOf (centralizer ({r} : Set X))).IsSubnormal := by
    rw [hYdef, subgroupOf_sup hNC hNxC]
    exact CFSG.GroupTheory.isSubnormal_sup hNpc.choose_spec.2.1 hNxpc.choose_spec.2.1
  have hOY : (pPrimeCore 2 ↥Y).map Y.subtype ≤ Hn E :=
    (pPrimeCore_map_le_of_isSubnormal hYC hYsub).trans hOr
  have hON : (pPrimeCore 2 ↥N).map N.subtype ≤ (pPrimeCore 2 ↥Y).map Y.subtype := by
    refine le_pPrimeCore_map ((map_subtype_le _).trans le_sup_left) (sup_le ?_ ?_) ?_
    · exact fun y hy => le_normalizer_pPrimeCore (le_normalizer hy)
    · exact fun y hy => le_normalizer_pPrimeCore (hNxK hy).1
    · rw [card_map_of_injective N.subtype_injective]
      exact pPrimeCore_coprime_card
  have hOYodd : Odd (Nat.card ↥((pPrimeCore 2 ↥Y).map Y.subtype)) := by
    rw [card_map_of_injective Y.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hcc : (conjBy N e₀).map (MulAut.conj e₀).toMonoidHom = N :=
    conjBy_conjBy_of_mul_self N he₀2
  have hcovx : Ar ≤ conjBy N e₀ ⊔ (conjBy N e₀).map (MulAut.conj e₀).toMonoidHom := by
    rw [hcc, sup_comm]
    exact hcov
  have hdiagx : (conjBy N e₀).map (MulAut.conj e₀).toMonoidHom ≠ conjBy N e₀ := by
    rw [hcc]
    exact Ne.symm hdiag
  let ψNx : ↥(conjBy N e₀) ⧸ Open.fusionZStar ↥(conjBy N e₀) ≃* alternatingGroup (Fin 7) :=
    (Sol78.fusionZStarQuotCongr (N.equivMapOfInjective (MulAut.conj e₀).toMonoidHom
      (MulAut.conj e₀).injective)).symm.trans ψN
  have hK : ∀ B : Subgroup X, B ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X) →
      IsPComponent 2 (B.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))) →
      (∀ x ∈ B, ∀ z ∈ Ar, x * z * x⁻¹ * z⁻¹ ∈ (pPrimeCore 2 ↥Ar).map Ar.subtype) →
      B ≤ UnbalancedLayer.coreActionKernel N ∧
        B ≤ UnbalancedLayer.coreActionKernel (conjBy N e₀) := fun B hBC hBpc hBA =>
    ⟨le_coreActionKernel_of_commute_pumpZ (k := 7) (by norm_num) (by norm_num) he₀r he₀o hArle
        hArpc χr hBC hBpc hBA hNC hNpc hcov hdiag ψN,
      le_coreActionKernel_of_commute_pumpZ (k := 7) (by norm_num) (by norm_num) he₀r he₀o hArle
        hArpc χr hBC hBpc hBA hNxC hNxpc hcovx hdiagx ψNx⟩
  obtain ⟨f, -, -, hfF, -, -, hf1, -, -, -, -, -⟩ := exists_three_of_klein hd.Fk
  obtain ⟨a, ha, ha2, hfaY, -⟩ :=
    exists_side_involution hs (by omega) hd he₀H hNC hNpc hK f hfF
  have hf2 : f * f = 1 := by rw [← sq]; exact (card_sq_of_klein hd.Fk).2 f hfF
  have haY : a ∈ Y := hcov ha
  have hfNY : f ∈ normalizer (Y : Set X) := by
    rw [show f = (f * a⁻¹) * a by group]
    exact mul_mem hfaY.1 (le_normalizer haY)
  set σa := ρ ⟨a, hArN ha⟩ with hσadef
  have hσa2 : σa * σa = 1 := by
    rw [hσadef, ← map_mul]
    have h1 : (⟨a, hArN ha⟩ : ↥(normalizer (N : Set X))) * ⟨a, hArN ha⟩ = 1 := Subtype.ext ha2
    rw [h1, map_one]
  have hσaA : σa ∈ alternatingGroup (Fin 7) :=
    IsPermAction.mem_alternatingGroup_of_perfect hArN hArperf ha
  have hσa4 : σa.support.card ≤ 4 := by
    have h1 := four_dvd_card_support_of_mem_alternating hσa2 hσaA
    have h2 : σa.support.card ≤ 7 := by simpa using Finset.card_le_univ σa.support
    omega
  obtain ⟨DN, hDNs, -, hDN⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ σa.support) hσa4 (by simp)
  have hFN : zpowers a ≤ normalizer (N : Set X) := zpowers_le.mpr (hArN ha)
  have hDNfix : ∀ (g : X) (hg : g ∈ zpowers a), ∀ ω ∉ DN, ρ ⟨g, hFN hg⟩ ω = ω := by
    intro g hg ω hω
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hg
    have e1 : (⟨a ^ j, hFN hg⟩ : ↥(normalizer (N : Set X))) =
        (⟨a, hArN ha⟩ : ↥(normalizer (N : Set X))) ^ j := Subtype.ext (by simp)
    rw [e1, map_zpow, ← hσadef]
    exact Perm.zpow_apply_eq_self_of_apply_eq_self
      (Perm.notMem_support.mp fun h => hω (hDNs h)) j
  obtain ⟨c, hcZ, hcO⟩ := exists_three_element hρ hFN hDN hDNfix
  have hca : a * c * a⁻¹ * (c : X)⁻¹ ∈ (pPrimeCore 2 ↥N).map N.subtype := by
    have h1 := hcO a (mem_zpowers a)
    have h3 : (c : X)⁻¹ * (a * c * a⁻¹) ∈ (pPrimeCore 2 ↥N).map N.subtype := ⟨_, h1, rfl⟩
    have h4 := (mem_normalizer_iff.mp (le_normalizer_pPrimeCore (le_normalizer c.2)) _).mp h3
    rwa [show (c : X) * ((c : X)⁻¹ * (a * c * a⁻¹)) * (c : X)⁻¹ = a * c * a⁻¹ * (c : X)⁻¹ by
      group] at h4
  have hcY : (c : X) ∈ Y := mem_sup_left c.2
  have hgN : f * a⁻¹ ∈ normalizer (((pPrimeCore 2 ↥Y).map Y.subtype : Subgroup X) : Set X) :=
    le_normalizer_pPrimeCore hfaY.1
  have hg1 : (f * a⁻¹) * c * (f * a⁻¹)⁻¹ * (c : X)⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype := by
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hfaY)).2 (c : X)⁻¹
      (inv_mem hcY)
    rw [inv_inv, inv_inv] at h1
    have h2 := inv_mem h1
    rwa [show ((c : X) * (f * a⁻¹) * (c : X)⁻¹ * (f * a⁻¹)⁻¹)⁻¹ =
      (f * a⁻¹) * c * (f * a⁻¹)⁻¹ * (c : X)⁻¹ by group] at h2
  have hfc : f * c * f⁻¹ * (c : X)⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype := by
    have h1 := (mem_normalizer_iff.mp hgN _).mp (hON hca)
    have h2 := mul_mem h1 hg1
    rwa [show (f * a⁻¹) * (a * c * a⁻¹ * (c : X)⁻¹) * (f * a⁻¹)⁻¹ *
      ((f * a⁻¹) * c * (f * a⁻¹)⁻¹ * (c : X)⁻¹) = f * c * f⁻¹ * (c : X)⁻¹ by group] at h2
  have hfo : orderOf f = 2 := orderOf_eq_prime (by rw [sq]; exact hf2) hf1
  have hx : ∀ w ∈ zpowers f, w * c * w⁻¹ * (c : X)⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype := by
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    have hk : f ^ k = 1 ∨ f ^ k = f := by
      rw [← zpow_mod_orderOf, hfo]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        rw [Nat.cast_ofNat, h, zpow_zero]
      · right
        rw [Nat.cast_ofNat, h, zpow_one]
    rcases hk with h | h <;> rw [h]
    · simp
    · exact hfc
  obtain ⟨v, hv, hvf⟩ := exists_fixed_in_coset (isPGroup_zpowers_of_mul_self hf2) hOYodd
    (zpowers_le.mpr (le_normalizer_pPrimeCore hfNY))
    (le_normalizer_pPrimeCore (le_normalizer hcY)) hx
  have hcvC : (c : X) * v ∈ centralizer ({f} : Set X) := by
    have h1 := hvf f (mem_zpowers f)
    rw [mem_centralizer_singleton_iff]
    calc (c : X) * v * f = (f * ((c : X) * v) * f⁻¹) * f := by rw [h1]
      _ = f * ((c : X) * v) := by group
  have hcH : (c : X) ∈ Hn E := by
    have h3 := mul_mem (hFH f hfF hf1 hcvC) (inv_mem (hOY hv))
    rwa [mul_inv_cancel_right] at h3
  set πN : ↥N →* alternatingGroup (Fin 7) :=
    ψN.toMonoidHom.comp (QuotientGroup.mk' (Open.fusionZStar ↥N)) with hπNdef
  have hπρ : ∀ x : ↥N, ((πN x : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ρ ⟨x, le_normalizer x.2⟩ := fun x => (hρ.apply_of_mem (by norm_num) x).symm
  set I := ((Hn E).subgroupOf N).map πN with hIdef
  have hInorm : I.Normal := by
    refine ⟨fun i hi σ => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hi
    obtain ⟨z, hz⟩ := hsurj σ
    have hzy : (z : X) * y * (z : X)⁻¹ ∈ N := (mem_normalizer_iff.mp (hArN z.2) y).mp y.2
    have hzH : (z : X) ∈ Hn E := hs.le (hArM z.2)
    refine ⟨⟨_, hzy⟩, mul_mem (mul_mem hzH hy) (inv_mem hzH), ?_⟩
    apply Subtype.ext
    have e1 : (⟨(z : X) * y * (z : X)⁻¹, le_normalizer hzy⟩ : ↥(normalizer (N : Set X))) =
        ⟨z, hArN z.2⟩ * ⟨y, le_normalizer y.2⟩ * (⟨z, hArN z.2⟩)⁻¹ := rfl
    rw [hπρ, e1, map_mul, map_mul, map_inv, hz, ← hπρ y]
    rfl
  have hIne : I ≠ ⊥ := by
    intro hI
    have h1 : πN c ∈ I := ⟨c, hcH, rfl⟩
    rw [hI, mem_bot] at h1
    apply hcZ
    change ψN ((c : ↥N) : ↥N ⧸ Open.fusionZStar ↥N) = 1 at h1
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact h1
  have := alternatingGroup.isSimpleGroup (α := Fin 7) (by rw [Nat.card_fin]; norm_num)
  have hItop : I = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal I).resolve_left hIne
  exact le_of_map_fusionZStar_eq_top hN ψN
    ((pPrimeCore_le_of_isPComponent hNC hNpc).trans hOr) hItop

end SwapP2

end CFSG.ComponentClassification.SolMax
