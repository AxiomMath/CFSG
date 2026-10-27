module

public import CFSG.CGT.Stroth77.Extension24Basic
public import CFSG.CGT.Stroth77.Extension22FourComm

public section

namespace CFSG.CGT.Stroth77

open scoped commutatorElement

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S}

theorem isMulCommutative_of_relIndex_four_Idx4 {τ : StrothTypeIndex}
    [hN : (B.subgroupOf C).Normal] (D : StrothTypeData B τ)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C))
    (hfix : ∀ y : B, conjBy D.ρ_mem y = y → conjBy D.t_mem y = y → y = 1) :
    IsMulCommutative C := by
  classical
  let Bc : Subgroup C := B.subgroupOf C
  have hBcCenter : Bc ≤ Subgroup.center C := by
    simpa [Bc] using subgroupOf_le_center hBC hC
  haveI : Bc.Normal := Subgroup.normal_of_le_center hBcCenter
  have hncyc' : ¬ IsCyclic (C ⧸ Bc) := by
    simpa [Bc] using hncyc
  have hcardQ : Nat.card (C ⧸ Bc) = 4 := by
    simpa [Bc] using card_quotient_four (B := B) (C := C) hBC hC hrel
  have hexpQ : ∀ q : C ⧸ Bc, q * q = 1 := by
    rcases cyclic_or_sq_eq_one hcardQ with hcyc | h
    · exact absurd hcyc hncyc'
    · exact h
  have hcommQ : IsMulCommutative (C ⧸ Bc) := isMulCommutative_of_forall_mul_self hexpQ
  have hcomm_le_Bc : _root_.commutator C ≤ Bc :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommQ
  have hsqBc : ∀ x : C, x * x ∈ Bc := by
    intro x
    have h : (QuotientGroup.mk' Bc x) * (QuotientGroup.mk' Bc x) = 1 := hexpQ _
    have h' : QuotientGroup.mk' Bc (x * x) = 1 := by rwa [map_mul]
    exact (QuotientGroup.eq_one_iff (N := Bc) (x * x)).mp (by simpa using h')
  haveI : Fintype (C ⧸ Bc) := Fintype.ofFinite _
  have hone_lt : 1 < Fintype.card (C ⧸ Bc) := by
    rw [Fintype.card_eq_nat_card, hcardQ]
    norm_num
  obtain ⟨q₁, hq₁⟩ := Fintype.exists_ne_of_one_lt_card hone_lt (1 : C ⧸ Bc)
  have hq₁top : Subgroup.zpowers q₁ ≠ ⊤ := by
    intro htop
    exact hncyc' (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨q₁, htop⟩)
  have hnot_subset : ¬ (⊤ : Set (C ⧸ Bc)) ⊆ (Subgroup.zpowers q₁ : Set (C ⧸ Bc)) := by
    intro h
    exact hq₁top (le_antisymm le_top h)
  obtain ⟨q₂, -, hq₂⟩ := Set.not_subset.mp hnot_subset
  have hq₂one : q₂ ≠ 1 := by
    intro h
    apply hq₂
    rw [h]
    exact Subgroup.one_mem _
  have hq₁₂ : q₁ ≠ q₂ := by
    intro h
    apply hq₂
    rw [← h]
    exact Subgroup.mem_zpowers q₁
  haveI : Nontrivial (C ⧸ Bc) := Fintype.one_lt_card_iff_nontrivial.mp hone_lt
  haveI : IsKleinFour (C ⧸ Bc) := by
    refine ⟨hcardQ, ?_⟩
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro q hq
    have hq2 : q * q = 1 := hexpQ q
    have hdvd : orderOf q ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hq2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hq
    · exact h2
  have hgen : Subgroup.closure ({q₁, q₂} : Set (C ⧸ Bc)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have huniv : ({q₁ * q₂, q₁, q₂, (1 : C ⧸ Bc)} : Finset (C ⧸ Bc)) = Finset.univ :=
      IsKleinFour.eq_finset_univ hq₁ hq₂one hq₁₂
    have hx : x ∈ ({q₁ * q₂, q₁, q₂, (1 : C ⧸ Bc)} : Finset (C ⧸ Bc)) := by
      rw [huniv]
      exact Finset.mem_univ x
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.one_mem _
  obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective Bc q₁
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective Bc q₂
  let E : Subgroup C := Subgroup.zpowers e
  let F : Subgroup C := Subgroup.zpowers f
  have hmapH : (Bc ⊔ E ⊔ F).map (QuotientGroup.mk' Bc) = ⊤ := by
    change ((Bc ⊔ Subgroup.zpowers e) ⊔ Subgroup.zpowers f).map
      (QuotientGroup.mk' Bc) = ⊤
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    have hker : Bc.map (QuotientGroup.mk' Bc) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hker, bot_sup_eq, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    simpa [Set.pair_comm] using hgen
  have hHtop : Bc ⊔ E ⊔ F = ⊤ :=
    eq_top_of_le_of_map_quotient_eq_top (N := Bc) (K := Bc ⊔ E ⊔ F)
      (le_sup_of_le_left le_sup_left) hmapH
  let z : C := ⁅e, f⁆
  let N : Subgroup C := Subgroup.zpowers z
  have hzBc : z ∈ Bc := by
    have hzC : z ∈ _root_.commutator C := by
      rw [commutator_eq_closure]
      exact Subgroup.subset_closure (commutator_mem_commutatorSet e f)
    exact hcomm_le_Bc hzC
  have hzCenter : z ∈ Subgroup.center C := hBcCenter hzBc
  have hNleBc : N ≤ Bc := Subgroup.zpowers_le.mpr hzBc
  have hNcenter : N ≤ Subgroup.center C := hNleBc.trans hBcCenter
  haveI : N.Normal := Subgroup.normal_of_le_center hNcenter
  have hz2 : z * z = 1 := by
    have hcomm_e_z : Commute e z := Subgroup.mem_center_iff.mp hzCenter e
    have hpow := hcomm_e_z.commutatorElement_pow_left 2
    have he2 : Commute (e * e) f :=
      (Subgroup.mem_center_iff.mp (hBcCenter (hsqBc e)) f).symm
    calc
      z * z = ⁅e, f⁆ ^ 2 := by
        change ⁅e, f⁆ * ⁅e, f⁆ = ⁅e, f⁆ ^ 2
        rw [pow_two]
      _ = ⁅e ^ 2, f⁆ := hpow
      _ = ⁅e * e, f⁆ := by rw [pow_two]
      _ = 1 := he2.commutator_eq
  let Te : Subgroup C := commutatorFiberLeft N e
  have hBc_le_Te : Bc ≤ Te := by
    intro b hb
    rw [mem_commutatorFiberLeft]
    have hcomm : Commute e b := Subgroup.mem_center_iff.mp (hBcCenter hb) e
    rw [hcomm.commutator_eq]
    exact N.one_mem
  have hE_le_Te : E ≤ Te := by
    change Subgroup.zpowers e ≤ Te
    rw [Subgroup.zpowers_le, mem_commutatorFiberLeft]
    simpa using N.one_mem
  have hfTe : f ∈ Te := by
    rw [mem_commutatorFiberLeft]
    simpa [z, N] using Subgroup.mem_zpowers z
  have hTeTop : Te = ⊤ := by
    rw [eq_top_iff, ← hHtop]
    exact sup_le (sup_le hBc_le_Te hE_le_Te) (Subgroup.zpowers_le.mpr hfTe)
  let Tf : Subgroup C := commutatorFiberLeft N f
  have hBc_le_Tf : Bc ≤ Tf := by
    intro b hb
    rw [mem_commutatorFiberLeft]
    have hcomm : Commute f b := Subgroup.mem_center_iff.mp (hBcCenter hb) f
    rw [hcomm.commutator_eq]
    exact N.one_mem
  have heTf : e ∈ Tf := by
    rw [mem_commutatorFiberLeft]
    rw [← commutatorElement_inv]
    exact N.inv_mem (by simpa [z, N] using Subgroup.mem_zpowers z)
  have hF_le_Tf : F ≤ Tf := by
    change Subgroup.zpowers f ≤ Tf
    rw [Subgroup.zpowers_le, mem_commutatorFiberLeft]
    simpa using N.one_mem
  have hTfTop : Tf = ⊤ := by
    rw [eq_top_iff, ← hHtop]
    exact sup_le (sup_le hBc_le_Tf (Subgroup.zpowers_le.mpr heTf)) hF_le_Tf
  let Ssub : Subgroup C := commutatorCentralizer N
  have hBc_le_S : Bc ≤ Ssub := by
    intro b hb
    rw [mem_commutatorCentralizer]
    intro y
    have hcomm : Commute b y := (Subgroup.mem_center_iff.mp (hBcCenter hb) y).symm
    rw [hcomm.commutator_eq]
    exact N.one_mem
  have heS : e ∈ Ssub := by
    rw [mem_commutatorCentralizer]
    intro y
    have hyTe : y ∈ Te := by rw [hTeTop]; exact Subgroup.mem_top y
    exact mem_commutatorFiberLeft.mp hyTe
  have hfS : f ∈ Ssub := by
    rw [mem_commutatorCentralizer]
    intro y
    have hyTf : y ∈ Tf := by rw [hTfTop]; exact Subgroup.mem_top y
    exact mem_commutatorFiberLeft.mp hyTf
  have hStop : Ssub = ⊤ := by
    rw [eq_top_iff, ← hHtop]
    exact sup_le (sup_le hBc_le_S (Subgroup.zpowers_le.mpr heS))
      (Subgroup.zpowers_le.mpr hfS)
  have hcomm_le_N : _root_.commutator C ≤ N := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have hxS : x ∈ Ssub := by rw [hStop]; exact Subgroup.mem_top x
    exact (mem_commutatorCentralizer.mp hxS) y
  let C' : Subgroup C := _root_.commutator C
  have hC'_le_N : C' ≤ N := hcomm_le_N
  have hC'_le_Bc : C' ≤ Bc := hC'_le_N.trans hNleBc
  haveI : C'.Characteristic := by
    change (_root_.commutator C).Characteristic
    infer_instance
  have hNcard : Nat.card N ≤ 2 := by
    change Nat.card (Subgroup.zpowers z) ≤ 2
    rw [Nat.card_zpowers]
    have hdvd : orderOf z ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [pow_two] using hz2
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hC'_card : Nat.card C' ≤ 2 := (Subgroup.card_le_of_le hC'_le_N).trans hNcard
  haveI : IsCyclic N := by
    change IsCyclic (Subgroup.zpowers z)
    infer_instance
  haveI : IsCyclic C' := Subgroup.isCyclic_of_le hC'_le_N
  have hAutcard : Nat.card (MulAut C') = 1 := by
    rw [IsCyclic.card_mulAut]
    rw [Nat.totient_eq_one_iff]
    have hpos : 0 < Nat.card C' := Nat.card_pos
    omega
  haveI : Subsingleton (MulAut C') := (Nat.card_eq_one_iff_unique.mp hAutcard).1
  have hfixρ : ∀ x : C, x ∈ C' →
      D.ρ⁻¹ * (x : S) * D.ρ = (x : S) := by
    intro x hx
    let ψ : MulAut C' :=
      MulAut.characteristic C' (conjAutOfMemNormalizer D.ρ⁻¹ (Subgroup.inv_mem _ (hL D.ρ_mem_L)))
    have hψ : ψ = 1 := Subsingleton.elim _ _
    have h := congrArg Subtype.val (congrArg (fun φ : MulAut C' => φ ⟨x, hx⟩) hψ)
    have hS := congrArg (fun y : C => (y : S)) h
    simpa [ψ, conjAutOfMemNormalizer_apply] using hS
  have hfixt : ∀ x : C, x ∈ C' →
      D.t⁻¹ * (x : S) * D.t = (x : S) := by
    intro x hx
    let ψ : MulAut C' :=
      MulAut.characteristic C' (conjAutOfMemNormalizer D.t⁻¹ (Subgroup.inv_mem _ (hL D.t_mem_L)))
    have hψ : ψ = 1 := Subsingleton.elim _ _
    have h := congrArg Subtype.val (congrArg (fun φ : MulAut C' => φ ⟨x, hx⟩) hψ)
    have hS := congrArg (fun y : C => (y : S)) h
    simpa [ψ, conjAutOfMemNormalizer_apply] using hS
  have hC'bot : C' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxB : (x : S) ∈ B := Subgroup.mem_subgroupOf.mp (hC'_le_Bc hx)
    have hρ : conjBy D.ρ_mem ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
      apply Subtype.ext
      have h := hfixρ x hx
      simpa [conjBy] using h
    have ht : conjBy D.t_mem ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
      apply Subtype.ext
      have h := hfixt x hx
      simpa [conjBy] using h
    have hx1 : (⟨x, hxB⟩ : B) = 1 := hfix _ hρ ht
    have hxS : (x : S) = 1 := by
      have := congrArg Subtype.val hx1
      simpa using this
    exact Subtype.ext hxS
  have hcomm_bot : _root_.commutator C = ⊥ := by
    simpa [C'] using hC'bot
  exact (commutator_eq_bot_iff C).mp hcomm_bot

theorem isMulCommutative_of_relIndex_four_t300_of_data {n : ℕ}
    [hN : (B.subgroupOf C).Normal] (D : StrothTypeData B (StrothTypeIndex.t300 n))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    IsMulCommutative C :=
  isMulCommutative_of_relIndex_four_Idx4 D hBC hC hrel hL hncyc
    fun _ hρ ht => t300_fixed_rho_t_of_mem D hρ ht

end CFSG.CGT.Stroth77
