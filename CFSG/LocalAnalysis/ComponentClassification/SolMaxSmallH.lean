module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9J
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36J
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv CFSG.Sporadic.HeldB
open scoped commutatorElement

theorem exists_eq_conj_of_odd_held
    {G : Type} [Group G] (Θ : G ≃* heP) (s : MulAut G) (hs : Odd (orderOf s)) :
    ∃ g : G, s = MulAut.conj g := by
  have hbij := ctbh_full_automorphism_permutation_model.1
  obtain ⟨x, hx⟩ := hbij.2 (MulAut.congr Θ s)
  have hox : orderOf x = orderOf s := by
    rw [← orderOf_injective heConjR hbij.1 x, hx]
    exact orderOf_injective (MulAut.congr Θ).toMonoidHom (MulAut.congr Θ).injective s
  have hidx : (heP.subgroupOf heAutGroup).index = 2 := heP_relIndex_heAutGroup
  have hxP : (x : Equiv.Perm (Fin 8330)) ∈ heP := by
    have h2 : x ^ 2 ∈ heP.subgroupOf heAutGroup := Subgroup.sq_mem_of_index_two hidx x
    rw [← hox] at hs
    obtain ⟨k, hk⟩ := hs
    have h3 : x = (x ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    have h4 : x ∈ heP.subgroupOf heAutGroup := by
      rw [h3]
      exact pow_mem h2 _
    exact mem_subgroupOf.mp h4
  refine ⟨Θ.symm ⟨x, hxP⟩, ?_⟩
  apply (MulAut.congr Θ).injective
  rw [← hx]
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [heConjR_apply]
  change _ = ((Θ (Θ.symm ⟨x, hxP⟩ * Θ.symm g * (Θ.symm ⟨x, hxP⟩)⁻¹) : heP) :
    Equiv.Perm (Fin 8330))
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rfl

theorem eq_one_of_conj_eq_one_held
    {G : Type} [Group G]
    (Θ : G ≃* heP) {g : G} (hg : MulAut.conj g = 1) : g = 1 := by
  have hc : Θ g ∈ center heP := by
    rw [mem_center_iff]
    intro h
    have h1 := congrArg (fun φ : MulAut G => φ (Θ.symm h)) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    have h2 := congrArg Θ h1
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
    calc h * Θ g = Θ g * h * (Θ g)⁻¹ * Θ g := by rw [h2]
      _ = Θ g * h := by group
  rw [heP_center_eq_bot, mem_bot] at hc
  exact Θ.injective (by rw [hc, map_one])

variable {X : Type} [Group X]

theorem mem_coreActionKernel_iff_oddQuotAction {M : Subgroup X} {g : X}
    (hg : g ∈ normalizer (M : Set X)) :
    g ∈ UnbalancedLayer.coreActionKernel M ↔ TBLit.oddQuotAction M ⟨g, hg⟩ = 1 := by
  constructor
  · intro hgK
    rw [TBLit.oddQuotAction_eq_one_iff]
    intro s hs
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hgK)).2 s⁻¹ (inv_mem hs)
    simpa [commutatorElement_def] using h1
  · intro h1
    have h2 : TBLit.oddQuotAction M ⟨g, hg⟩⁻¹ = 1 := by rw [map_inv, h1, inv_one]
    rw [TBLit.oddQuotAction_eq_one_iff] at h2
    refine ⟨hg, fun j hj => ?_⟩
    have h3 := h2 j⁻¹ (inv_mem hj)
    simpa [commutatorElement_def] using h3

theorem le_coreActionKernel_of_held_pump
    [Finite X] {M X₀ : Subgroup X} {c s m : X} (hMC : M ≤ centralizer ({c} : Set X))
    (hM : ⁅M, M⁆ = M) (ψ : ↥M ⧸ Open.fusionZStar ↥M ≃* Blueprint.NativeSporadic.He)
    (hm : m ∈ M) (hsN : s ∈ normalizer (M : Set X)) (hs2 : s * s = 1)
    (hsm : m⁻¹ * s ∈ UnbalancedLayer.coreActionKernel M)
    (hsK : s ∉ UnbalancedLayer.coreActionKernel M)
    (hodd : Odd (Nat.card X₀)) (hX₀N : X₀ ≤ normalizer (M : Set X))
    (hX₀s : X₀ ≤ centralizer ({s} : Set X))
    (hX₀n : ∀ g ∈ centralizer ({s} : Set X) ⊓ centralizer ({c} : Set X), ∀ x ∈ X₀,
      g * x * g⁻¹ ∈ X₀) :
    X₀ ≤ UnbalancedLayer.coreActionKernel M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMc : commutator ↥M = ⊤ := by
    apply map_injective M.subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hM
  obtain ⟨ψb⟩ := nonempty_coreQuot_held hMc ψ
  let Θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* heP := ψb.trans heEquivP
  set A := TBLit.oddQuotAction M with hAdef
  have hAM : ∀ (x : X) (hx : x ∈ M), A ⟨x, le_normalizer hx⟩ =
      MulAut.conj ((⟨x, hx⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) := by
    intro x hx
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [hAdef, TBLit.oddQuotAction_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
  have hcakA : ∀ (g : X) (hg : g ∈ normalizer (M : Set X)), A ⟨g, hg⟩ = 1 →
      g ∈ UnbalancedLayer.coreActionKernel M :=
    fun g hg h => (mem_coreActionKernel_iff_oddQuotAction hg).mpr h
  have hmN : m ∈ normalizer (M : Set X) := le_normalizer hm
  set mb : ↥M ⧸ pPrimeCore 2 ↥M := ((⟨m, hm⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) with hmbdef
  have hAs : A ⟨s, hsN⟩ = MulAut.conj mb := by
    have hk1 : A ⟨m⁻¹ * s, mul_mem (inv_mem hmN) hsN⟩ = 1 :=
      (mem_coreActionKernel_iff_oddQuotAction _).mp hsm
    have h1 : (⟨s, hsN⟩ : ↥(normalizer (M : Set X))) =
        ⟨m, hmN⟩ * ⟨m⁻¹ * s, mul_mem (inv_mem hmN) hsN⟩ :=
      Subtype.ext (by change s = m * (m⁻¹ * s); group)
    rw [h1, map_mul, hk1, mul_one, hAM m hm]
  have hconj_inj : Function.Injective
      (MulAut.conj : (↥M ⧸ pPrimeCore 2 ↥M) →* MulAut (↥M ⧸ pPrimeCore 2 ↥M)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    exact eq_one_of_conj_eq_one_held Θ hg
  have hmb1 : mb ≠ 1 := by
    intro h
    apply hsK
    refine hcakA s hsN ?_
    rw [hAs, h, map_one]
  have hmb2 : mb * mb = 1 := by
    apply hconj_inj
    rw [map_mul, ← hAs, ← map_mul, map_one]
    have : (⟨s, hsN⟩ : ↥(normalizer (M : Set X))) * ⟨s, hsN⟩ = 1 := Subtype.ext hs2
    rw [this, map_one]
  set P : Subgroup (MulAut (↥M ⧸ pPrimeCore 2 ↥M)) :=
    (X₀.subgroupOf (normalizer (M : Set X))).map A with hPdef
  set Q : Subgroup (↥M ⧸ pPrimeCore 2 ↥M) := P.comap MulAut.conj with hQdef
  have hPodd : Odd (Nat.card P) := by
    have h1 : Nat.card P ∣ Nat.card (X₀.subgroupOf (normalizer (M : Set X))) :=
      card_map_dvd _ _
    rw [Nat.card_congr (subgroupOfEquivOfLe hX₀N).toEquiv] at h1
    exact hodd.of_dvd_nat h1
  have hQodd : Odd (Nat.card Q) := by
    let f : Q →* P := ((MulAut.conj : (↥M ⧸ pPrimeCore 2 ↥M) →* MulAut _).comp
      Q.subtype).codRestrict P fun q => q.2
    have hf : Function.Injective f := fun a b h =>
      Subtype.ext (hconj_inj (congrArg Subtype.val h))
    exact hPodd.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)
  have hPinner : ∀ (x : X) (hx : x ∈ X₀), ∃ q ∈ Q, A ⟨x, hX₀N hx⟩ = MulAut.conj q := by
    intro x hx
    have hxodd : Odd (orderOf (A ⟨x, hX₀N hx⟩)) := by
      have h1 : orderOf (A ⟨x, hX₀N hx⟩) ∣
          orderOf (⟨x, hX₀N hx⟩ : ↥(normalizer (M : Set X))) := orderOf_map_dvd A _
      rw [Subgroup.orderOf_mk] at h1
      have h2 : orderOf x ∣ Nat.card X₀ := by
        have := orderOf_dvd_natCard (⟨x, hx⟩ : X₀)
        rwa [Subgroup.orderOf_mk] at this
      exact (hodd.of_dvd_nat h2).of_dvd_nat h1
    obtain ⟨q, hq⟩ := exists_eq_conj_of_odd_held Θ _ hxodd
    refine ⟨q, ?_, hq⟩
    change MulAut.conj q ∈ P
    rw [← hq]
    exact ⟨⟨x, hX₀N hx⟩, hx, rfl⟩
  have hQC : ∀ q ∈ Q, q * mb = mb * q := by
    intro q hq
    obtain ⟨⟨x, hxN⟩, hx, hxq⟩ := hq
    have hxs : x * s = s * x := mem_centralizer_singleton_iff.mp (hX₀s hx)
    have h1 : A ⟨x, hxN⟩ * A ⟨s, hsN⟩ = A ⟨s, hsN⟩ * A ⟨x, hxN⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxs
    rw [hxq, hAs, ← map_mul, ← map_mul] at h1
    exact hconj_inj h1
  have hQn : ∀ cb : ↥M ⧸ pPrimeCore 2 ↥M, cb * mb = mb * cb → ∀ q ∈ Q, cb * q * cb⁻¹ ∈ Q := by
    intro cb hcb q hq
    obtain ⟨⟨x, hxN⟩, hx, hxq⟩ := hq
    obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective cb
    have hc₀s : (c₀ : X)⁻¹ * (s * c₀ * s⁻¹) ∈ coreNOf M := by
      have h1 : A ⟨s, hsN⟩ (c₀ : ↥M ⧸ pPrimeCore 2 ↥M) = (c₀ : ↥M ⧸ pPrimeCore 2 ↥M) := by
        rw [hAs, MulAut.conj_apply, ← hcb]
        group
      rw [hAdef, TBLit.oddQuotAction_mk] at h1
      have h2 := QuotientGroup.eq.mp h1.symm
      exact ⟨_, h2, rfl⟩
    obtain ⟨k, hkO, hkc⟩ := exists_commute_of_mem_coset (odd_coreNOf M) hs2
      (fun o ho => (mem_normalizer_iff.mp (le_normalizer_pPrimeCore hsN) o).mp ho) hc₀s
    obtain ⟨k', hk', hk'eq⟩ := hkO
    have hkM : k ∈ M := by rw [← hk'eq]; exact k'.2
    have hc'M : (c₀ : X) * k ∈ M := mul_mem c₀.2 hkM
    have hc'b : ((⟨(c₀ : X) * k, hc'M⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) =
        (c₀ : ↥M ⧸ pPrimeCore 2 ↥M) := by
      have h1 : (⟨(c₀ : X) * k, hc'M⟩ : ↥M) = c₀ * k' :=
        Subtype.ext (by change (c₀ : X) * k = (c₀ : X) * (k' : X); rw [← hk'eq]; rfl)
      rw [h1, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k').mpr hk', mul_one]
    have hc's : (c₀ : X) * k ∈ centralizer ({s} : Set X) :=
      mem_centralizer_singleton_iff.mpr hkc.symm
    have hc'c : (c₀ : X) * k ∈ centralizer ({c} : Set X) := hMC hc'M
    have hx' : ((c₀ : X) * k) * x * ((c₀ : X) * k)⁻¹ ∈ X₀ := hX₀n _ ⟨hc's, hc'c⟩ x hx
    refine ⟨⟨((c₀ : X) * k) * x * ((c₀ : X) * k)⁻¹, hX₀N hx'⟩, hx', ?_⟩
    have hc'N : (c₀ : X) * k ∈ normalizer (M : Set X) := le_normalizer hc'M
    have h3 : (⟨((c₀ : X) * k) * x * ((c₀ : X) * k)⁻¹, hX₀N hx'⟩ :
        ↥(normalizer (M : Set X))) = ⟨(c₀ : X) * k, hc'N⟩ * ⟨x, hxN⟩ * ⟨(c₀ : X) * k, hc'N⟩⁻¹ :=
      rfl
    rw [h3, map_mul, map_mul, map_inv, hxq, hAM _ hc'M, hc'b, ← map_inv, ← map_mul, ← map_mul]
  have hQbot : Q = ⊥ := by
    have hh₀2 : orderOf (Θ mb) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [sq, ← map_mul, hmb2, map_one]
      · exact fun h => hmb1 (Θ.injective (by rw [h, map_one]))
    have hO := (ctbhi_held_inner_involution_centralizers_odd_core).2 (Θ mb) hh₀2
    have hWH : Q.map Θ.toMonoidHom ≤ centralizer ({Θ mb} : Set heP) := by
      rintro _ ⟨q, hq, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have h1 := congrArg Θ (hQC q hq)
      rw [map_mul, map_mul] at h1
      exact h1
    have hWn : ((Q.map Θ.toMonoidHom).subgroupOf (centralizer ({Θ mb} : Set heP))).Normal := by
      constructor
      intro w hw h
      rw [mem_subgroupOf] at hw ⊢
      obtain ⟨q, hq, hqw⟩ := hw
      have hh : (h : heP) * Θ mb = Θ mb * h := mem_centralizer_singleton_iff.mp h.2
      have hcb : Θ.symm h * mb = mb * Θ.symm h := by
        apply Θ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hh
      refine ⟨Θ.symm h * q * (Θ.symm h)⁻¹, hQn _ hcb q hq, ?_⟩
      have h2 : Θ (Θ.symm h * q * (Θ.symm h)⁻¹) = (h : heP) * Θ q * (h : heP)⁻¹ := by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      change Θ (Θ.symm h * q * (Θ.symm h)⁻¹) = _
      rw [h2]
      change _ = ((h * w * h⁻¹ : centralizer ({Θ mb} : Set heP)) : heP)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hqw]
      rfl
    have hWodd : Nat.Coprime 2
        (Nat.card ((Q.map Θ.toMonoidHom).subgroupOf (centralizer ({Θ mb} : Set heP)))) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv,
        card_map_of_injective Θ.injective]
      exact Nat.coprime_two_left.mpr hQodd
    have hWle : (Q.map Θ.toMonoidHom).subgroupOf (centralizer ({Θ mb} : Set heP)) ≤
        pPrimeCore 2 (centralizer ({Θ mb} : Set heP)) := le_sSup ⟨hWn, hWodd⟩
    rw [hO, le_bot_iff, subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hWH] at hWle
    rw [eq_bot_iff]
    intro q hq
    have h1 : Θ q ∈ Q.map Θ.toMonoidHom := ⟨q, hq, rfl⟩
    rw [hWle, mem_bot] at h1
    rw [mem_bot]
    exact Θ.injective (by rw [h1, map_one])
  intro x hx
  obtain ⟨q, hq, hxq⟩ := hPinner x hx
  rw [hQbot, mem_bot] at hq
  refine hcakA x (hX₀N hx) ?_
  rw [hxq, hq, map_one]

end CFSG.ComponentClassification.SolMax
