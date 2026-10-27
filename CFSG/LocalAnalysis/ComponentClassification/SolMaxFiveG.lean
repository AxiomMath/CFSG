module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36U
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallC

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem card_support_of_three_fix {r : ℕ} {τ σy σj : Perm (Fin r)}
    (hy : ∀ v, v ∉ τ.support → σy v = v) (hj : σj.support ⊆ τ.supportᶜ)
    (hjA : σj ∈ alternatingGroup (Fin r)) (hj2 : σj * σj = 1)
    (h5 : r - τ.support.card = 5) (h3 : (σy * σj).supportᶜ.card = 3) :
    σj.support.card = 4 ∧ σy.support.card + 7 = r := by
  classical
  have hyτ : σy.support ⊆ τ.support := by
    intro v hv
    by_contra hvτ
    exact (Perm.mem_support.mp hv) (hy v hvτ)
  have hdisj : σy.Disjoint σj := by
    rw [Perm.disjoint_iff_disjoint_support]
    exact Finset.disjoint_of_subset_left hyτ
      (Finset.disjoint_of_subset_right hj disjoint_compl_right)
  have hmul := hdisj.card_support_mul
  have hτle : τ.support.card ≤ r := by
    have := Finset.card_le_univ τ.support
    rwa [Fintype.card_fin] at this
  have hsle : (σy * σj).support.card ≤ r := by
    have := Finset.card_le_univ (σy * σj).support
    rwa [Fintype.card_fin] at this
  have hcompl : (σy * σj).supportᶜ.card = r - (σy * σj).support.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hjle : σj.support.card ≤ 5 := by
    have h1 := Finset.card_le_card hj
    rw [Finset.card_compl, Fintype.card_fin] at h1
    omega
  have hyle : σy.support.card ≤ τ.support.card := Finset.card_le_card hyτ
  have hev : 2 ∣ σj.support.card := Perm.two_dvd_card_support (by rw [sq]; exact hj2)
  have h4 : σj.support.card ≠ 0 → 4 ≤ σj.support.card := by
    intro h0
    refine four_le_card_support_of_mem_alternatingGroup hjA hj2 fun h1 => h0 ?_
    rw [h1, Perm.support_one, Finset.card_empty]
  obtain ⟨k, hk⟩ := hev
  rcases Nat.eq_zero_or_pos σj.support.card with h0 | hpos
  · omega
  · have := h4 hpos.ne'
    omega

theorem false_of_orderOf_seven_commute {m : ℕ} (hm : m < 14) {σ π : Perm (Fin m)}
    (hσ : σ * σ = 1) (hfix : m - σ.support.card < 7) (hπ : orderOf π = 7)
    (hc : π * σ = σ * π) : False := by
  classical
  have h7 : Nat.Prime 7 := by norm_num
  have hcyc : π.IsCycle := Perm.isCycle_of_prime_order' (by rw [hπ]; exact h7)
    (by rw [Fintype.card_fin, hπ]; omega)
  have hπ1 : π ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hπ
    omega
  have hsub := support_subset_compl_of_prime_cycle hσ h7 (by norm_num)
    (by rw [← hπ]; exact pow_orderOf_eq_one π) hπ1 hc hcyc
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_compl, Fintype.card_fin, ← hcyc.orderOf, hπ] at h1
  omega

variable {X : Type} [Group X]

theorem mem_coreNOf_of_mem_cak [Finite X] {L : Subgroup X} {s : ℕ} (hs : 4 ≤ s)
    (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin s)) {z : X} (hzL : z ∈ L)
    (hzK : z ∈ UnbalancedLayer.coreActionKernel L) : z ∈ coreNOf L := by
  set Z : ↥L := ⟨z, hzL⟩ with hZdef
  have hZc : QuotientGroup.mk' (pPrimeCore 2 ↥L) Z ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have h1 := hzK.2 j j.2
    have h2 : QuotientGroup.mk' (pPrimeCore 2 ↥L) (j⁻¹ * Z⁻¹ * j * Z) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨w, hw, hwe⟩ := h1
      have : w = j⁻¹ * Z⁻¹ * j * Z := Subtype.ext (by simpa [Z] using hwe)
      rwa [← this]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc QuotientGroup.mk' (pPrimeCore 2 ↥L) j * QuotientGroup.mk' (pPrimeCore 2 ↥L) Z =
        QuotientGroup.mk' (pPrimeCore 2 ↥L) Z * QuotientGroup.mk' (pPrimeCore 2 ↥L) j *
          ((QuotientGroup.mk' (pPrimeCore 2 ↥L) j)⁻¹ * (QuotientGroup.mk' (pPrimeCore 2 ↥L) Z)⁻¹ *
            QuotientGroup.mk' (pPrimeCore 2 ↥L) j * QuotientGroup.mk' (pPrimeCore 2 ↥L) Z) := by
          group
      _ = _ := by rw [h2, mul_one]
  have hT1 : QuotientGroup.mk' (pPrimeCore 2 ↥L) Z = 1 := by
    have h1 : θL (QuotientGroup.mk' (pPrimeCore 2 ↥L) Z) ∈ center (alternatingGroup (Fin s)) := by
      rw [← Subgroup.map_center_eq θL]
      exact ⟨_, hZc, rfl⟩
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega), mem_bot] at h1
    exact (map_eq_one_iff _ θL.injective).mp h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hT1
  exact ⟨Z, hT1, rfl⟩

theorem mk_conj_eq_of_mem_cak {L : Subgroup X} {g : X}
    (hg : g ∈ UnbalancedLayer.coreActionKernel L) (x : ↥L) (hgx : g * x * g⁻¹ ∈ L) :
    ((⟨g * x * g⁻¹, hgx⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) = (x : ↥L ⧸ pPrimeCore 2 ↥L) := by
  have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hg)).2 x x.2
  rw [inv_inv] at h1
  obtain ⟨o, ho, hoeq⟩ := h1
  have hoeq' : (o : X) = (x : X)⁻¹ * (g * x * g⁻¹) := by
    rw [show (x : X)⁻¹ * (g * x * g⁻¹) = (x : X)⁻¹ * g * x * g⁻¹ by group]
    exact hoeq
  symm
  rw [QuotientGroup.eq]
  have h2 : x⁻¹ * (⟨g * x * g⁻¹, hgx⟩ : ↥L) = o := Subtype.ext (by rw [hoeq']; rfl)
  rw [h2]
  exact ho

theorem exists_involution_of_acts [Finite X] {L : Subgroup X} {s : ℕ} (hs : 4 ≤ s)
    (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin s)) {a j' : X} (ha2 : a * a = 1)
    (hj' : j' ∈ L) (haj : a * j'⁻¹ ∈ UnbalancedLayer.coreActionKernel L) :
    ∃ j ∈ L, j * j = 1 ∧ a * j = j * a ∧ a * j⁻¹ ∈ UnbalancedLayer.coreActionKernel L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haN : a ∈ normalizer (L : Set X) := by
    have h1 : a = a * j'⁻¹ * j' := by group
    rw [h1]
    exact mul_mem haj.1 (le_normalizer hj')
  set O := pPrimeCore 2 ↥L with hOdef
  set cL : MulAut ↥L := L.normalizerMonoidHom ⟨a, haN⟩ with hcLdef
  have hcapp : ∀ x : ↥L, ((cL x : ↥L) : X) = a * x * a⁻¹ := fun x => rfl
  have hc : ∀ x, cL (cL x) = x := by
    intro x
    apply Subtype.ext
    rw [hcapp, hcapp, hainv]
    calc a * (a * (x : X) * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [ha2]; group
  have hw : ((cL ⟨j', hj'⟩ : ↥L) : ↥L ⧸ O) = ((⟨j', hj'⟩ : ↥L) : ↥L ⧸ O) := by
    have hgx : a * j'⁻¹ * j' * (a * j'⁻¹)⁻¹ ∈ L := by
      have h1 : a * j'⁻¹ * j' * (a * j'⁻¹)⁻¹ = a * j' * a⁻¹ := by group
      rw [h1]
      exact (mem_normalizer_iff.mp haN j').mp hj'
    have h1 := mk_conj_eq_of_mem_cak haj ⟨j', hj'⟩ hgx
    have h2 : cL ⟨j', hj'⟩ = ⟨a * j'⁻¹ * j' * (a * j'⁻¹)⁻¹, hgx⟩ := Subtype.ext (by
      rw [hcapp]
      change a * j' * a⁻¹ = _
      group)
    rw [h2]
    exact h1
  obtain ⟨x, hxc, hxx⟩ := exists_fixed_of_mk_eq cL hc hw
  have hax : a * (x : X) = x * a := by
    have h1 := congrArg Subtype.val hxc
    rw [hcapp] at h1
    calc a * (x : X) = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h1]
  have hxO : x⁻¹ * ⟨j', hj'⟩ ∈ O := QuotientGroup.eq.mp hxx
  have hxO' : (x : X)⁻¹ * j' ∈ coreNOf L := ⟨_, hxO, rfl⟩
  have hjxO : (j' : X) * (x : X)⁻¹ ∈ coreNOf L := by
    have h1 := (mem_normalizer_iff.mp (le_normalizer_pPrimeCore (le_normalizer hj')) _).mp hxO'
    have h2 : j' * ((x : X)⁻¹ * j') * j'⁻¹ = j' * (x : X)⁻¹ := by group
    rwa [h2] at h1
  have hax' : a * (x : X)⁻¹ ∈ UnbalancedLayer.coreActionKernel L := by
    have h1 : a * (x : X)⁻¹ = (a * j'⁻¹) * (j' * (x : X)⁻¹) := by group
    rw [h1]
    exact mul_mem haj (coreNOf_le_coreActionKernel L hjxO)
  have hx2K : (x : X) * x ∈ UnbalancedLayer.coreActionKernel L := by
    have h1 : ((x : X) * x)⁻¹ = (a * (x : X)⁻¹) * (a * (x : X)⁻¹) := by
      have h2 : a * (x : X)⁻¹ = (x : X)⁻¹ * a := by
        calc a * (x : X)⁻¹ = (x : X)⁻¹ * (x * a) * (x : X)⁻¹ := by group
          _ = (x : X)⁻¹ * (a * x) * (x : X)⁻¹ := by rw [hax]
          _ = (x : X)⁻¹ * a := by group
      calc ((x : X) * x)⁻¹ = (x : X)⁻¹ * (a * a) * (x : X)⁻¹ := by rw [ha2]; group
        _ = ((x : X)⁻¹ * a) * (a * (x : X)⁻¹) := by group
        _ = (a * (x : X)⁻¹) * (a * (x : X)⁻¹) := by rw [← h2]
    have h3 : ((x : X) * x)⁻¹ ∈ UnbalancedLayer.coreActionKernel L := by
      rw [h1]
      exact mul_mem hax' hax'
    simpa using inv_mem h3
  have hx2O := mem_coreNOf_of_mem_cak hs θL (mul_mem x.2 x.2) hx2K
  obtain ⟨m, hm⟩ : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  set w : X := (x : X) * x with hwdef
  have hwk : w ^ Nat.card O = 1 := by
    obtain ⟨w', hw', hw'e⟩ := hx2O
    have h1 : (⟨w', hw'⟩ : ↥O) ^ Nat.card O = 1 := pow_card_eq_one'
    have h2 := congrArg (fun z : ↥O => ((z : ↥L) : X)) h1
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    rw [← hw'e]
    exact h2
  have hxw : Commute (x : X) w := (Commute.refl (x : X)).mul_right (Commute.refl (x : X))
  have haw : Commute a w := by
    have h1 : Commute a (x : X) := hax
    exact h1.mul_right h1
  have hxwm : Commute (x : X) (w ^ m) := hxw.pow_right m
  refine ⟨(x : X) * w ^ m, mul_mem x.2 (pow_mem (mul_mem x.2 x.2) m), ?_, ?_, ?_⟩
  · calc (x : X) * w ^ m * ((x : X) * w ^ m) = (x : X) * (w ^ m * x) * w ^ m := by group
      _ = (x : X) * (x * w ^ m) * w ^ m := by rw [hxwm.eq]
      _ = ((x : X) * x) * (w ^ m * w ^ m) := by simp only [mul_assoc]
      _ = w * (w ^ m * w ^ m) := by rw [← hwdef]
      _ = w ^ (2 * m + 1) := by rw [pow_succ', two_mul, pow_add]
      _ = 1 := by rw [← hm, hwk]
  · exact (Commute.mul_right hax (haw.pow_right m)).eq
  · have h2 : Commute (x : X)⁻¹ (w ^ m)⁻¹ := hxwm.inv_left.inv_right
    have h1 : a * ((x : X) * w ^ m)⁻¹ = (a * (x : X)⁻¹) * (w ^ m)⁻¹ := by
      rw [mul_inv_rev, ← h2.eq, mul_assoc]
    rw [h1]
    exact mul_mem hax' (inv_mem (pow_mem (coreNOf_le_coreActionKernel L hx2O) m))

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.image_eq_of_le (hρ : IsPermAction θ ρ) [Finite X] {L : Subgroup X}
    (hLN : L ≤ normalizer (M : Set X)) {s : ℕ} (hs : 5 ≤ s)
    (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin s)) (hperf : ⁅L, L⁆ = L)
    (hLK : ¬ L ≤ UnbalancedLayer.coreActionKernel M) {Q : Subgroup (Perm (Fin r))}
    (hQ : Nat.card Q ≤ s.factorial / 2)
    (hLQ : ∀ (z : X) (hz : z ∈ L), ρ ⟨z, hLN hz⟩ ∈ Q) :
    (∀ g ∈ Q, ∃ (z : X) (hz : z ∈ L), ρ ⟨z, hLN hz⟩ = g) ∧
      ∀ (z : X) (hz : z ∈ L), z ∈ coreNOf L → ρ ⟨z, hLN hz⟩ = 1 := by
  classical
  have hk := mem_coreNOf_of_rho_eq_one_of_not_le hρ hLN hs θL hperf hLK
  set L' := L.subgroupOf (normalizer (M : Set X)) with hL'def
  set A := L'.map ρ with hAdef
  set K := L' ⊓ ρ.ker with hKdef
  set O' := (coreNOf L).subgroupOf (normalizer (M : Set X)) with hO'def
  have hAQ : A ≤ Q := by
    rintro _ ⟨w, hw, rfl⟩
    exact hLQ w hw
  have hKO : K ≤ O' := by
    rintro w ⟨hw, hwk⟩
    exact hk w hw hwk
  have hcardL := card_eq_of_alt (by omega) θL
  have hk₁ := card_eq_card_map_mul_card_inf_ker' ρ L'
  have hLs : Nat.card L' = Nat.card L := Nat.card_congr (subgroupOfEquivOfLe hLN).toEquiv
  have hOs : Nat.card O' = Nat.card (coreNOf L) :=
    Nat.card_congr (subgroupOfEquivOfLe ((map_subtype_le _).trans hLN)).toEquiv
  have hKle : Nat.card K ≤ Nat.card (coreNOf L) := hOs ▸ Subgroup.card_le_of_le hKO
  have hAle : Nat.card A ≤ s.factorial / 2 := (Subgroup.card_le_of_le hAQ).trans hQ
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hs2 : 2 ≤ s.factorial := by
    have := Nat.self_le_factorial s
    omega
  have hspos : 0 < s.factorial / 2 := Nat.div_pos hs2 two_pos
  have heq : s.factorial / 2 * Nat.card (coreNOf L) = Nat.card A * Nat.card K := by
    rw [← hcardL, ← hLs, hk₁]
  have hA : Nat.card A = s.factorial / 2 := by
    by_contra hne
    have hlt : Nat.card A < s.factorial / 2 := lt_of_le_of_ne hAle hne
    have h1 : Nat.card A * Nat.card K < s.factorial / 2 * Nat.card (coreNOf L) :=
      calc Nat.card A * Nat.card K < s.factorial / 2 * Nat.card K :=
            Nat.mul_lt_mul_of_pos_right hlt hKpos
        _ ≤ s.factorial / 2 * Nat.card (coreNOf L) := Nat.mul_le_mul_left _ hKle
    omega
  have hK : Nat.card K = Nat.card (coreNOf L) := by
    rw [hA] at heq
    exact (Nat.eq_of_mul_eq_mul_left hspos heq).symm
  have hAQeq : A = Q := Subgroup.eq_of_le_of_card_ge hAQ (by rw [hA]; exact hQ)
  have hKeq : K = O' := Subgroup.eq_of_le_of_card_ge hKO (by rw [hOs, hK])
  refine ⟨fun g hg => ?_, fun z hz hzO => ?_⟩
  · rw [← hAQeq] at hg
    obtain ⟨w, hw, rfl⟩ := hg
    exact ⟨w, hw, rfl⟩
  · have h1 : (⟨z, hLN hz⟩ : ↥(normalizer (M : Set X))) ∈ K := by
      rw [hKeq]
      exact hzO
    exact h1.2

theorem apply_eq_of_mem_cak_of_onto [Finite X] {L : Subgroup X}
    (hLN : L ≤ normalizer (M : Set X)) {τ : Perm (Fin r)} (h4 : 4 ≤ r - τ.support.card)
    (hsurj : ∀ b ∈ fixAlt τ, ∃ (z : X) (hz : z ∈ L), ρ ⟨z, hLN hz⟩ = (b : Perm (Fin r)))
    (hO : ∀ (z : X) (hz : z ∈ L), z ∈ coreNOf L → ρ ⟨z, hLN hz⟩ = 1)
    {g : X} (hgN : g ∈ normalizer (M : Set X)) (hgL : g ∈ UnbalancedLayer.coreActionKernel L)
    {v : Fin r} (hv : v ∉ τ.support) : ρ ⟨g, hgN⟩ v = v := by
  refine apply_eq_of_commute_fixAlt h4 (fun b hb => ?_) hv
  obtain ⟨z, hz, hzb⟩ := hsurj b hb
  have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hgL)).2 z hz
  rw [inv_inv] at h1
  have hw : z⁻¹ * g * z * g⁻¹ ∈ L := map_subtype_le _ h1
  have h2 := hO _ hw h1
  have h3 : (⟨z⁻¹ * g * z * g⁻¹, hLN hw⟩ : ↥(normalizer (M : Set X))) =
      (⟨z, hLN hz⟩)⁻¹ * ⟨g, hgN⟩ * ⟨z, hLN hz⟩ * (⟨g, hgN⟩)⁻¹ := rfl
  rw [h3, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  rw [← hzb]
  calc ρ ⟨g, hgN⟩ * ρ ⟨z, hLN hz⟩ = ρ ⟨z, hLN hz⟩ * ((ρ ⟨z, hLN hz⟩)⁻¹ * ρ ⟨g, hgN⟩ *
        ρ ⟨z, hLN hz⟩ * (ρ ⟨g, hgN⟩)⁻¹) * ρ ⟨g, hgN⟩ := by group
    _ = ρ ⟨z, hLN hz⟩ * ρ ⟨g, hgN⟩ := by rw [h2, mul_one]

theorem IsPermAction.exists_conj_of_cover (hρ : IsPermAction θ ρ) [Finite X] (hr : 7 ≤ r)
    {J L : Subgroup X} (e : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin r)) (hLJ : L ≤ J)
    (hLsupJ : L ⊔ (pPrimeCore 2 ↥J).map J.subtype = J) (hLM : L ≤ M)
    (hLsupM : L ⊔ (pPrimeCore 2 ↥M).map M.subtype = M) :
    ∃ ε : Perm (Fin r), ∀ {g e₀ : X} (hgM : g ∈ normalizer (M : Set X)),
      g ∈ normalizer (L : Set X) → ∀ (he₀ : e₀ ∈ J),
      g * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J →
        ρ ⟨g, hgM⟩ = ε * coreImage e he₀ * ε⁻¹ := by
  classical
  obtain ⟨θ', hθ'⟩ := exists_coreQuot_of_sup hLJ hLsupJ e
  obtain ⟨θ'', hθ''⟩ := exists_coreQuot_of_sup hLM hLsupM θ
  obtain ⟨ε₀, hε₀⟩ := exists_equiv_of_mulEquiv_alt (Fintype.card_fin r) (Fintype.card_fin r) hr
    (θ'.symm.trans θ'')
  set ε : Perm (Fin r) := ε₀ with hεdef
  have hconj : ∀ b : alternatingGroup (Fin r),
      ((θ'.symm.trans θ'' b : alternatingGroup (Fin r)) : Perm (Fin r)) = ε * b * ε⁻¹ := by
    intro b
    rw [hε₀ b]
    ext v
    simp [Perm.mul_apply, Perm.inv_def, hεdef]
  have hL : ∀ (x : X) (hx : x ∈ L),
      ρ ⟨x, le_normalizer (hLM hx)⟩ = ε * coreImage e (hLJ hx) * ε⁻¹ := by
    intro x hx
    have h1 : ρ ⟨x, le_normalizer (hLM hx)⟩ =
        (θ ((⟨x, hLM hx⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) :=
      hρ.apply_of_mem (by omega) ⟨x, hLM hx⟩
    have h2 : θ ((⟨x, hLM hx⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) =
        (θ'.symm.trans θ'') (e ((⟨x, hLJ hx⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J)) := by
      rw [MulEquiv.trans_apply, ← hθ' ⟨x, hx⟩, MulEquiv.symm_apply_apply, hθ'' ⟨x, hx⟩]
    rw [h1, h2, hconj]
    rfl
  have hsurj : ∀ b : alternatingGroup (Fin r), ∃ (x : X) (hx : x ∈ L),
      ρ ⟨x, le_normalizer (hLM hx)⟩ = b := by
    intro b
    obtain ⟨q, hq⟩ := θ''.surjective b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨x, x.2, ?_⟩
    have h1 : ρ ⟨x, le_normalizer (hLM x.2)⟩ =
        (θ ((⟨x, hLM x.2⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) :=
      hρ.apply_of_mem (by omega) ⟨x, hLM x.2⟩
    rw [h1, ← hθ'' x, hq]
  refine ⟨ε, fun {g e₀} hgM hgL he₀ hge => ?_⟩
  set σ : Perm (Fin r) := ε * coreImage e he₀ * ε⁻¹ with hσdef
  have hcomm : ∀ (x : X) (hx : x ∈ L), ρ ⟨g, hgM⟩ * ρ ⟨x, le_normalizer (hLM hx)⟩ *
      (ρ ⟨g, hgM⟩)⁻¹ = σ * ρ ⟨x, le_normalizer (hLM hx)⟩ * σ⁻¹ := by
    intro x hx
    have hgx : g * x * g⁻¹ ∈ L := (mem_normalizer_iff.mp hgL x).mp hx
    have h1 : ρ ⟨g, hgM⟩ * ρ ⟨x, le_normalizer (hLM hx)⟩ * (ρ ⟨g, hgM⟩)⁻¹ =
        ρ ⟨g * x * g⁻¹, le_normalizer (hLM hgx)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1, hL _ hgx, hL _ hx, coreImage_conj_of_acts e he₀ hge (hLJ hx) (hLJ hgx), hσdef]
    group
  have hδ : σ⁻¹ * ρ ⟨g, hgM⟩ = 1 := by
    refine eq_one_of_commute_fixAlt (τ := 1) (by simp)
      (by rw [Perm.support_one, Finset.card_empty]; omega) fun b _ => ?_
    obtain ⟨x, hx, hxb⟩ := hsurj b
    rw [← hxb]
    have h1 := hcomm x hx
    calc σ⁻¹ * ρ ⟨g, hgM⟩ * ρ ⟨x, le_normalizer (hLM hx)⟩ =
        σ⁻¹ * (ρ ⟨g, hgM⟩ * ρ ⟨x, le_normalizer (hLM hx)⟩ * (ρ ⟨g, hgM⟩)⁻¹) *
          ρ ⟨g, hgM⟩ := by group
      _ = σ⁻¹ * (σ * ρ ⟨x, le_normalizer (hLM hx)⟩ * σ⁻¹) * ρ ⟨g, hgM⟩ := by rw [h1]
      _ = ρ ⟨x, le_normalizer (hLM hx)⟩ * (σ⁻¹ * ρ ⟨g, hgM⟩) := by group
  calc ρ ⟨g, hgM⟩ = σ * (σ⁻¹ * ρ ⟨g, hgM⟩) := by group
    _ = σ := by rw [hδ, mul_one]

theorem false_of_alt_seven_of_four {H : Type*} [Group H] [Finite H] {r m : ℕ}
    (φ : H →* Perm (Fin r)) (φ₁ : H →* Perm (Fin m)) (hm : m < 14) {σ : Perm (Fin m)}
    (hσ2 : σ * σ = 1) (hσ7 : m - σ.support.card < 7) (hφ₁σ : ∀ h, φ₁ h * σ = σ * φ₁ h)
    {τ : Perm (Fin r)} (h7 : r - τ.support.card = 7)
    (hφτ : ∀ h, φ h ∈ (fixAlt τ).map (alternatingGroup (Fin r)).subtype)
    (hsurj : ∀ b ∈ fixAlt τ, ∃ h, φ h = (b : Perm (Fin r)))
    (hker : ∀ h, φ h = 1 → Odd (orderOf h)) {j : H} (hj2 : j * j = 1) (hj1 : φ₁ j ≠ 1) :
    False := by
  classical
  have hA : ∀ h, φ h ∈ alternatingGroup (Fin r) := fun h => by
    obtain ⟨b, -, hbe⟩ := hφτ h
    rw [← hbe]
    exact b.2
  let φA : H →* alternatingGroup (Fin r) := φ.codRestrict _ hA
  have hF : ∀ h, φA h ∈ fixAlt τ := fun h => by
    obtain ⟨b, hb, hbe⟩ := hφτ h
    have : φA h = b := Subtype.ext hbe.symm
    rw [this]
    exact hb
  let ψ : H →* fixAlt τ := φA.codRestrict _ hF
  have hψ : ∀ h, (((ψ h : fixAlt τ) : alternatingGroup (Fin r)) : Perm (Fin r)) = φ h :=
    fun h => rfl
  have hψs : Function.Surjective ψ := by
    rintro ⟨b, hb⟩
    obtain ⟨h, hh⟩ := hsurj b hb
    exact ⟨h, Subtype.ext (Subtype.ext hh)⟩
  have : IsSimpleGroup (fixAlt τ) := isSimpleGroup_fixAlt (by omega)
  have hnorm : (φ₁.ker.map ψ).Normal := (inferInstance : φ₁.ker.Normal).map ψ hψs
  have hj2' : orderOf (φ₁ j) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, hj2, map_one]) hj1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ₁.ker.map ψ) with hbot | htop
  ·
    have hle : φ₁.ker ≤ ψ.ker := fun h hh => by
      have h1 : ψ h ∈ φ₁.ker.map ψ := ⟨h, hh, rfl⟩
      rw [hbot, mem_bot] at h1
      exact h1
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv,
      card_fixAlt (by omega), h7] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ₁.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ₁).toEquiv] at h2
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
    have h3 : Nat.card φ₁.range = Nat.factorial 7 / 2 * k := by
      have hpos : 0 < Nat.card φ₁.ker := Nat.card_pos
      rw [hk] at h1
      have h4 : Nat.card φ₁.range * Nat.card φ₁.ker =
          Nat.factorial 7 / 2 * k * Nat.card φ₁.ker := by
        rw [← h2, h1]
        ring
      exact Nat.eq_of_mul_eq_mul_right hpos h4
    have h7d : 7 ∣ Nat.card φ₁.range := by
      rw [h3]
      exact Dvd.dvd.mul_right (by decide) k
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 h7d
    obtain ⟨h, hh⟩ := g.2
    have hgo : orderOf (φ₁ h) = 7 := by
      rw [hh, Subgroup.orderOf_coe, hg]
    exact false_of_orderOf_seven_commute hm hσ2 hσ7 hgo (hφ₁σ h)
  ·
    have hjm : ψ j ∈ φ₁.ker.map ψ := by
      rw [htop]
      exact mem_top _
    obtain ⟨n, hn, hnj⟩ := hjm
    have hk1 : φ (n⁻¹ * j) = 1 := by
      rw [← hψ, map_mul, map_inv, hnj, inv_mul_cancel]
      rfl
    have hodd := hker _ hk1
    have h1 : φ₁ (n⁻¹ * j) = φ₁ j := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn, inv_one, one_mul]
    have h2 : orderOf (φ₁ j) ∣ orderOf (n⁻¹ * j) := by
      rw [← h1]
      exact orderOf_map_dvd φ₁ _
    rw [hj2'] at h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end CFSG.ComponentClassification.SolMax
