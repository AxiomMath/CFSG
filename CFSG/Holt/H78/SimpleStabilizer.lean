module

public import CFSG.Holt.H78.Bridge
public import CFSG.GH74.GLS.Stage4.T6Grp
public import CFSG.Holt.H78.SEModelFive
public import CFSG.Holt.General.CaseIPrimitiveBasic
public import CFSG.Holt.General.AltGood
public import CFSG.Holt.General.OddOrbitsBasic

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.GH74.Uniqueness.Bender

private theorem false_of_centralizer_bot {X : Type} [Group X] {Y : Subgroup X}
    [IsSimpleGroup Y] {t : X} {O : Subgroup X} {K : Subgroup Y}
    (htY : t ∈ Y) (ht2 : t * t = 1) (ht_ne_one : t ≠ 1)
    (hna : ∃ a c : Y, a * c ≠ c * a) (hbot : K = ⊥)
    (hK : K = (Subgroup.centralizer (O : Set X)).subgroupOf Y)
    (hinv : ∀ y : Y, ∀ o ∈ O, (y : X) * t * (y : X)⁻¹ * o * ((y : X) * t * (y : X)⁻¹)⁻¹
      = o⁻¹) (h_inv_t : ∀ o ∈ O, t * o * t⁻¹ = o⁻¹) : False := by
  have hcenter : (⟨t, htY⟩ : Y) ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hmem : (⟨t * ((y : X) * t * (y : X)⁻¹), by
        exact mul_mem htY (mul_mem (mul_mem y.2 htY) (inv_mem y.2))⟩ : Y) ∈ K := by
      rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro o ho
      have h2 : t * ((y : X) * t * (y : X)⁻¹) * o *
          (t * ((y : X) * t * (y : X)⁻¹))⁻¹ = o := by
        calc t * ((y : X) * t * (y : X)⁻¹) * o *
            (t * ((y : X) * t * (y : X)⁻¹))⁻¹
            = t * (((y : X) * t * (y : X)⁻¹) * o *
              ((y : X) * t * (y : X)⁻¹)⁻¹) * t⁻¹ := by group
          _ = t * o⁻¹ * t⁻¹ := by rw [hinv y o ho]
          _ = (t * o * t⁻¹)⁻¹ := by group
          _ = (o⁻¹)⁻¹ := by rw [h_inv_t o ho]
          _ = o := by group
      calc o * (t * ((y : X) * t * (y : X)⁻¹))
          = ((t * ((y : X) * t * (y : X)⁻¹)) * o *
            (t * ((y : X) * t * (y : X)⁻¹))⁻¹) *
            (t * ((y : X) * t * (y : X)⁻¹)) := by rw [h2]
        _ = (t * ((y : X) * t * (y : X)⁻¹)) * o := by group
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : t * ((y : X) * t * (y : X)⁻¹) = 1 := congrArg Subtype.val hmem
    have h2 : t * (y : X) * t = (y : X) := by
      have := congrArg (· * (y : X)) h1
      simpa [mul_assoc] using this
    have h3 : t * (y : X) = (y : X) * t := by
      calc t * (y : X) = t * (y : X) * (t * t) := by rw [ht2, mul_one]
        _ = (t * (y : X) * t) * t := by group
        _ = (y : X) * t := by rw [h2]
    exact Subtype.ext h3.symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with hc | hc
  · have h1 : (⟨t, htY⟩ : Y) = 1 := by
      rw [hc, Subgroup.mem_bot] at hcenter
      exact hcenter
    exact ht_ne_one (congrArg Subtype.val h1)
  · have hcomm : IsMulCommutative Y := Subgroup.center_eq_top_iff.mp hc
    obtain ⟨a, c, hac⟩ := hna
    exact hac (hcomm.is_comm.comm a c)

private theorem oddCore_eq_bot_of_centralizer_top {X : Type} [Group X] {t : X} {O : Subgroup X}
    (htcentral : t ∈ Subgroup.centralizer (O : Set X)) (hO_odd : Odd (Nat.card O))
    (h_inv_t : ∀ o ∈ O, t * o * t⁻¹ = o⁻¹) : O = ⊥ := by
  apply le_bot_iff.mp
  intro o ho
  rw [Subgroup.mem_bot]
  have hcomm : o * t = t * o := (Subgroup.mem_centralizer_iff.mp htcentral) o ho
  have hto : t * o * t⁻¹ = o := by
    calc t * o * t⁻¹ = o * t * t⁻¹ := by rw [← hcomm]
      _ = o := by group
  have hoinv : o = o⁻¹ := hto.symm.trans (h_inv_t o ho)
  have hsq : o * o = 1 := by
    calc o * o = o⁻¹ * o := by nth_rewrite 1 [hoinv]; rfl
      _ = 1 := inv_mul_cancel o
  have h2dvd : orderOf o ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa [pow_two] using hsq
  have hord1 : orderOf o = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hO_odd) h2dvd
      (Subgroup.orderOf_dvd_natCard O ho)
  exact orderOf_eq_one_iff.mp hord1

private theorem oddCore_eq_bot {X : Type} [Group X] {Y : Subgroup X} [IsSimpleGroup Y]
    {t : X} {O : Subgroup X} (htY : t ∈ Y) (ht : orderOf t = 2)
    (hna : ∃ a c : Y, a * c ≠ c * a) (hO_norm : O.Normal) (hO_odd : Odd (Nat.card O))
    (hO_inf_Y : O ⊓ Y = ⊥) (h_inv_t : ∀ o ∈ O, t * o * t⁻¹ = o⁻¹) : O = ⊥ := by
  have ht2 : t * t = 1 := by
    simpa [pow_two] using (orderOf_eq_prime_iff.mp ht).1
  have ht_ne_one : t ≠ 1 := by
    intro h
    have h1 : orderOf t = 1 := by rw [h, orderOf_one]
    omega
  let K : Subgroup Y := (Subgroup.centralizer (O : Set X)).subgroupOf Y
  have hinv : ∀ y : Y, ∀ o ∈ O, (y : X) * t * (y : X)⁻¹ * o * ((y : X) * t * (y : X)⁻¹)⁻¹
      = o⁻¹ := by
    intro y o ho
    have hy : (y : X)⁻¹ * o * (y : X) ∈ O := by
      simpa using hO_norm.conj_mem o ho (y : X)⁻¹
    calc (y : X) * t * (y : X)⁻¹ * o * ((y : X) * t * (y : X)⁻¹)⁻¹
        = (y : X) * (t * ((y : X)⁻¹ * o * (y : X)) * t⁻¹) * (y : X)⁻¹ := by group
      _ = (y : X) * ((y : X)⁻¹ * o * (y : X))⁻¹ * (y : X)⁻¹ := by rw [h_inv_t _ hy]
      _ = o⁻¹ := by group
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hbot | htop
  · exfalso
    exact false_of_centralizer_bot htY ht2 ht_ne_one hna hbot rfl hinv h_inv_t
  · have htK : (⟨t, htY⟩ : Y) ∈ K := by rw [htop]; trivial
    have htcentral : t ∈ Subgroup.centralizer (O : Set X) := by
      rwa [Subgroup.mem_subgroupOf] at htK
    exact oddCore_eq_bot_of_centralizer_top htcentral hO_odd h_inv_t

private theorem IsHoltFactor.exists_mem_ne_one_fixed
    {Δ : Type} [Fintype Δ] [DecidableEq Δ]
    {M : Subgroup (Equiv.Perm Δ)} (hM : IsHoltFactor M) (δ : Δ) :
    ∃ m ∈ M, m ≠ 1 ∧ m δ = δ := by
  classical
  rcases hM with ⟨rfl, h7⟩ | hSE
  · have h4 : 4 ≤ Fintype.card Δ := by omega
    obtain ⟨γ, -, hγ⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({δ} : Finset Δ)) (t := Finset.univ) (by
        rw [Finset.card_univ, Finset.card_singleton]; omega)
    have hγ' : γ ≠ δ := by simpa using hγ
    obtain ⟨ε, -, hε⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({δ, γ} : Finset Δ)) (t := Finset.univ) (by
        rw [Finset.card_univ, Finset.card_pair (Ne.symm hγ')]; omega)
    have hε' : ε ≠ δ ∧ ε ≠ γ := by simpa using hε
    obtain ⟨m, hmA, hmδ, hmγ⟩ := exists_mem_alternatingGroup_fix_apply_eq h4 hγ' hε'.1
    refine ⟨m, hmA, ?_, hmδ⟩
    intro h1
    have h2 : γ = ε := by
      rw [← hmγ, h1]
      rfl
    exact hε'.2 h2.symm
  · have hSE' : IsNaturalSE M := hSE
    obtain ⟨-, hEven, -⟩ := IsNaturalSE.isStronglyEmbedded_stabilizer hSE' δ
    rw [Nat.card_eq_fintype_card] at hEven
    have hcard : 1 < Fintype.card (MulAction.stabilizer M δ) := by
      obtain ⟨k, hk⟩ := hEven
      have hpos : 0 < Fintype.card (MulAction.stabilizer M δ) := Fintype.card_pos
      omega
    haveI : Nontrivial (MulAction.stabilizer M δ) :=
      Fintype.one_lt_card_iff_nontrivial.mp hcard
    obtain ⟨m, hm⟩ := exists_ne (1 : MulAction.stabilizer M δ)
    refine ⟨(m : M), (m : M).2, ?_, ?_⟩
    · intro h1
      exact hm (Subtype.ext (Subtype.ext h1))
    · simpa [Subgroup.smul_def] using MulAction.mem_stabilizer_iff.mp m.2

private theorem core_faithful {X : Type} [Group X] {Y : Subgroup X} [IsSimpleGroup Y]
    {t : X} (htY : t ∈ Y) (hfix : ∀ g : X, g * t * g⁻¹ ∈ Y → g ∈ Y)
    (hY : Y ≠ ⊤) :
    Subgroup.normalCore Y = ⊥ ∧ FaithfulSMul X (X ⧸ Y) ∧
      Subgroup.centralizer ({t} : Set X) ≤ Y := by
  have hcore : Subgroup.normalCore Y = ⊥ := by
    have hsub : (Subgroup.normalCore Y).subgroupOf Y = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((Subgroup.normalCore Y).subgroupOf Y) with h | h
      · exact h
      · exfalso
        have hYcore : Subgroup.normalCore Y = Y :=
          le_antisymm (Subgroup.normalCore_le Y) ((Subgroup.subgroupOf_eq_top
            (H := Subgroup.normalCore Y) (K := Y)).mp h)
        have hnormal : Y.Normal := hYcore ▸ Subgroup.normalCore_normal Y
        have htop : Y = ⊤ := by
          rw [eq_top_iff]
          intro g _
          exact hfix g (hnormal.conj_mem t htY g)
        exact hY htop
    rw [Subgroup.subgroupOf_eq_bot] at hsub
    exact hsub.eq_bot_of_le (Subgroup.normalCore_le Y)
  refine ⟨hcore, ?_, ?_⟩
  · rw [faithfulSMul_iff]
    intro g hg
    have hger : g ∈ (MulAction.toPermHom X (X ⧸ Y)).ker := by
      rw [MonoidHom.mem_ker]
      ext a
      simpa using hg a
    rw [← Subgroup.normalCore_eq_ker] at hger
    rw [hcore, Subgroup.mem_bot] at hger
    exact hger
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have h1 : g * t * g⁻¹ = t := by
      rw [hg]
      group
    exact hfix g (by rw [h1]; exact htY)

private theorem oddCore_normal_odd_inf {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    [IsSimpleGroup Y] {t : X} (htY : t ∈ Y) (ht : orderOf t = 2) (hY : Y ≠ ⊤) :
    (oddCoreOf (⊤ : Subgroup X)).Normal ∧
      Odd (Nat.card (oddCoreOf (⊤ : Subgroup X))) ∧
      oddCoreOf (⊤ : Subgroup X) ⊓ Y = ⊥ := by
  have hO_odd : Odd (Nat.card (oddCoreOf (⊤ : Subgroup X))) := by
    rw [show oddCoreOf (⊤ : Subgroup X) =
      (CFSG.pPrimeCore 2 (⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype from rfl]
    rw [Subgroup.card_map_of_injective (⊤ : Subgroup X).subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hO_norm : (oddCoreOf (⊤ : Subgroup X)).Normal := by
    rw [show oddCoreOf (⊤ : Subgroup X) =
      (CFSG.pPrimeCore 2 (⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype from rfl]
    exact Subgroup.Normal.map CFSG.pPrimeCore_normal (⊤ : Subgroup X).subtype
      fun x => ⟨⟨x, trivial⟩, rfl⟩
  have hO_inf_Y : oddCoreOf (⊤ : Subgroup X) ⊓ Y = ⊥ := by
    have hnormal : ((oddCoreOf (⊤ : Subgroup X) ⊓ Y).subgroupOf Y).Normal := by
      rw [inf_comm, Subgroup.inf_subgroupOf_left]
      exact hO_norm.subgroupOf Y
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((oddCoreOf (⊤ : Subgroup X) ⊓ Y).subgroupOf Y) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact h.eq_bot_of_le inf_le_right
    · exfalso
      have hYleO : Y ≤ oddCoreOf (⊤ : Subgroup X) := by
        have h1 : Y ≤ oddCoreOf (⊤ : Subgroup X) ⊓ Y :=
          (Subgroup.subgroupOf_eq_top (H := oddCoreOf (⊤ : Subgroup X) ⊓ Y)
            (K := Y)).mp h
        exact h1.trans inf_le_left
      have hYodd : Odd (Nat.card Y) := hO_odd.of_dvd_nat (Subgroup.card_dvd_of_le hYleO)
      have h2dvd : 2 ∣ Nat.card Y := by
        rw [← ht]
        exact Subgroup.orderOf_dvd_natCard Y htY
      exact absurd hYodd (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2dvd))
  exact ⟨hO_norm, hO_odd, hO_inf_Y⟩

private theorem involution_inverts_oddCore {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    [IsSimpleGroup Y] {t : X} (htY : t ∈ Y) (ht : orderOf t = 2)
    (hC_t : Subgroup.centralizer ({t} : Set X) ≤ Y)
    (hO_norm : (oddCoreOf (⊤ : Subgroup X)).Normal)
    (hO_inf_Y : oddCoreOf (⊤ : Subgroup X) ⊓ Y = ⊥) :
    ∀ o ∈ oddCoreOf (⊤ : Subgroup X), t * o * t⁻¹ = o⁻¹ := by
  have ht2 : t * t = 1 := by
    simpa [pow_two] using (orderOf_eq_prime_iff.mp ht).1
  have hfix_O : ∀ o ∈ oddCoreOf (⊤ : Subgroup X), t * o * t⁻¹ = o → o = 1 := by
    intro o ho h
    have h1 : o ∈ Subgroup.centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      rw [htinv] at h
      have h' : t * o = o * t := by
        calc t * o = t * o * (t * t) := by rw [ht2, mul_one]
          _ = (t * o * t) * t := by group
          _ = o * t := by rw [h]
      exact h'.symm
    have h2 : o ∈ oddCoreOf (⊤ : Subgroup X) ⊓ Y := ⟨ho, hC_t h1⟩
    rw [hO_inf_Y, Subgroup.mem_bot] at h2
    exact h2
  have := CFSG.GH74.GLS.Stage4.Rest.T6.t6_inv_of_fpf ht2
    (by intro o ho; exact hO_norm.conj_mem o ho t) hfix_O
  exact this.1

private theorem isHoltTriple_quotient {X : Type} [Group X] {Y : Subgroup X}
    [IsSimpleGroup Y] {t : X} (α : X ⧸ Y) (htY : t ∈ Y) (ht : orderOf t = 2)
    (hfix : ∀ g : X, g * t * g⁻¹ ∈ Y → g ∈ Y)
    (hsyl : ∃ S : Sylow 2 X, t ∈ (S : Subgroup X) ∧
      (S : Subgroup X) ≤ Subgroup.centralizer {t})
    (hstab : MulAction.stabilizer X α = Y) : IsHoltTriple X (X ⧸ Y) t α := by
  refine ⟨inferInstance, ht, ?_, hsyl⟩
  intro ω
  constructor
  · intro hω
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X α ω
    have h1 : g⁻¹ * t * g ∈ Y := by
      rw [← hstab, MulAction.mem_stabilizer_iff]
      calc (g⁻¹ * t * g) • α
          = g⁻¹ • (t • (g • α)) := by rw [mul_smul, mul_smul]
        _ = g⁻¹ • (g • α) := by rw [hω]
        _ = α := by rw [← mul_smul, inv_mul_cancel, one_smul]
    have hgY : g ∈ Y := by simpa using inv_mem (hfix g⁻¹ (by simpa using h1))
    have : g ∈ MulAction.stabilizer X α := hstab.symm ▸ hgY
    simpa [MulAction.mem_stabilizer_iff] using this
  · intro hω
    rw [hω]
    have : t ∈ MulAction.stabilizer X α := hstab.symm ▸ htY
    simpa [MulAction.mem_stabilizer_iff] using this

private theorem mem_longInv_quotient {X : Type} [Group X] {Y : Subgroup X}
    [IsSimpleGroup Y] {t : X} (α : X ⧸ Y) (htY : t ∈ Y) (ht : orderOf t = 2)
    (hfix : ∀ g : X, g * t * g⁻¹ ∈ Y → g ∈ Y)
    (hstab : MulAction.stabilizer X α = Y) : t ∈ longInv X (X ⧸ Y) := by
  refine ⟨ht, α, ?_, ?_⟩
  · have : t ∈ MulAction.stabilizer X α := hstab.symm ▸ htY
    simpa [MulAction.mem_stabilizer_iff] using this
  · intro ω hω
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X α ω
    have h1 : g⁻¹ * t * g ∈ Y := by
      rw [← hstab, MulAction.mem_stabilizer_iff]
      calc (g⁻¹ * t * g) • α
          = g⁻¹ • (t • (g • α)) := by rw [mul_smul, mul_smul]
        _ = g⁻¹ • (g • α) := by rw [hω]
        _ = α := by rw [← mul_smul, inv_mul_cancel, one_smul]
    have hgY : g ∈ Y := by simpa using inv_mem (hfix g⁻¹ (by simpa using h1))
    have : g ∈ MulAction.stabilizer X α := hstab.symm ▸ hgY
    simpa [MulAction.mem_stabilizer_iff] using this

private theorem holtData_oddCore_bot (h : HoltTheorem1) {X : Type} [Group X] [Finite X]
    {Y : Subgroup X} [IsSimpleGroup Y] {t : X} {α : X ⧸ Y} (ht2 : t * t = 1)
    (hfaith : FaithfulSMul X (X ⧸ Y))
    (hO_bot : oddCoreOf (⊤ : Subgroup X) = ⊥)
    (htriple : IsHoltTriple X (X ⧸ Y) t α) :
    ∃ D : HoltData X (X ⧸ Y), jOddCore X (X ⧸ Y) = ⊥ := by
  have hstar : IsStarGroup X (X ⧸ Y) := IsHoltTriple.isStarGroup htriple (by
    have h3 : 3 ≤ Nat.card (X ⧸ Y) := IsHoltTriple.three_le_card htriple
    exact h3)
  obtain ⟨D⟩ := h X (X ⧸ Y) hstar
  have hO_top : oddCoreOf (⊤ : Subgroup X) = CFSG.pPrimeCore 2 X := by
    apply CFSG.Holt.General.OddOrbits.oddCoreOf_eq_pPrimeCore (B := ⊤) (z := t)
    · simpa [pow_two] using ht2
    · simp
  have hpc_bot : CFSG.pPrimeCore 2 X = ⊥ := by
    rw [← hO_top]
    exact hO_bot
  refine ⟨D, ?_⟩
  exact le_bot_iff.mp ((jOddCore_le_pPrimeCore (G := X) (Ω := X ⧸ Y)).trans hpc_bot.le)

private theorem le_jHull_of_simple {X : Type} [Group X] {Y : Subgroup X} [IsSimpleGroup Y]
    {t : X} {Ω : Type} [MulAction X Ω] (htY : t ∈ Y) (ht_ne_one : t ≠ 1)
    (ht_jHull : t ∈ jHull X Ω) : Y ≤ jHull X Ω := by
  have hY_inf : Y ⊓ jHull X Ω = Y := by
    have hinf_normal : ((Y ⊓ jHull X Ω).subgroupOf Y).Normal := by
      rw [Subgroup.inf_subgroupOf_left]
      exact jHull_normal.subgroupOf Y
    have hne : Y ⊓ jHull X Ω ≠ ⊥ := by
      intro h
      have ht_inf : t ∈ Y ⊓ jHull X Ω := ⟨htY, ht_jHull⟩
      rw [h, Subgroup.mem_bot] at ht_inf
      exact ht_ne_one ht_inf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Y ⊓ jHull X Ω).subgroupOf Y) with hbot | htop
    · exfalso
      rw [Subgroup.subgroupOf_eq_bot] at hbot
      exact hne (hbot.eq_bot_of_le (inf_le_left : Y ⊓ jHull X Ω ≤ Y))
    · exact le_antisymm inf_le_left (Subgroup.subgroupOf_eq_top.mp htop)
  exact inf_eq_left.mp hY_inf

private theorem inf_L_ne_bot {X : Type} [Group X] [Finite X]
    {Y : Subgroup X} [IsSimpleGroup Y] {Ω : Type} [MulAction X Ω]
    (D : HoltData X Ω) {α : Ω} {i : D.ι} (hO : jOddCore X Ω = ⊥)
    (hstab : MulAction.stabilizer X α = Y) : D.L i ⊓ Y ≠ ⊥ := by
  obtain ⟨m, hmM, hmne, hmfix⟩ := (D.factor i).exists_mem_ne_one_fixed (D.coord α i)
  obtain ⟨h, hhL, hhρ⟩ := D.mem_M.mp hmM
  have hcoord : D.coord ((h : X) • α) = D.coord α := by
    funext j
    rw [D.coord_smul h α j]
    rcases eq_or_ne j i with rfl | hj
    · rw [hhρ]
      exact hmfix
    · rw [D.rho_eq_one_of_mem_L hj.symm hhL]
      exact Equiv.Perm.one_apply _
  have hfixα : (h : X) • α = α := by
    have horb : (h : X) • α ∈ MulAction.orbit (jOddCore X Ω) α :=
      (D.coord_eq_iff α ((h : X) • α)).mp hcoord.symm
    rwa [orbit_jOddCore_eq_singleton hO, Set.mem_singleton_iff] at horb
  have hhY : (h : X) ∈ Y := by
    have hs : (h : X) ∈ MulAction.stabilizer X α := by
      rw [MulAction.mem_stabilizer_iff]
      exact hfixα
    exact (congrArg (fun H : Subgroup X => (h : X) ∈ H) hstab).mp hs
  have hne_one : (h : X) ≠ 1 := by
    intro h1
    have hm1 : m = 1 := by
      rw [← hhρ, show h = 1 from Subtype.ext h1, map_one]
    exact hmne hm1
  intro hbot
  have hmem : (h : X) ∈ D.L i ⊓ Y := ⟨hhL, hhY⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hne_one hmem

private theorem le_L {X : Type} [Group X] {Y : Subgroup X} [IsSimpleGroup Y]
    {Ω : Type} [MulAction X Ω] (D : HoltData X Ω) {α : Ω}
    (hO : jOddCore X Ω = ⊥) (hstab : MulAction.stabilizer X α = Y)
    (hY_le_H : Y ≤ jHull X Ω) (hne : ∀ i, D.L i ⊓ Y ≠ ⊥) : ∀ i, Y ≤ D.L i := by
  intro i
  have hY_normal : ((D.L i ⊓ Y).subgroupOf Y).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    have hD_normal : ((D.L i).subgroupOf (jHull X Ω)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      exact (D.le_normalizer i g.property n).mp hn
    refine ⟨fun n hn g => ?_⟩
    have hnJ : (⟨n, hY_le_H n.2⟩ : jHull X Ω) ∈
        (D.L i).subgroupOf (jHull X Ω) := Subgroup.mem_subgroupOf.mpr hn
    have hconj := hD_normal.conj_mem ⟨n, hY_le_H n.2⟩ hnJ ⟨g, hY_le_H g.2⟩
    exact Subgroup.mem_subgroupOf.mp hconj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((D.L i ⊓ Y).subgroupOf Y) with hbot | htop
  · exfalso
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact hne i (hbot.eq_bot_of_le (inf_le_right : D.L i ⊓ Y ≤ Y))
  · exact ((Subgroup.subgroupOf_eq_top (H := D.L i ⊓ Y) (K := Y)).mp htop).trans inf_le_left

private theorem false_of_alternating {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    [IsSimpleGroup Y] {Ω : Type} [MulAction X Ω] [Finite Ω] (D : HoltData X Ω) {α : Ω}
    {i₀ : D.ι} (hO : jOddCore X Ω = ⊥) (hι : ∀ i, i = i₀)
    (hstab : MulAction.stabilizer X α = Y) (hYL : ∀ i, Y ≤ D.L i)
    (hA : D.M i₀ = alternatingGroup (D.Ψc i₀))
    (halt : ∀ m : ℕ, IsEmpty (Y ≃* alternatingGroup (Fin (2 * m)))) : False := by
  classical
  haveI : Fintype Ω := Fintype.ofFinite Ω
  have hodd : Odd (Nat.card Ω) := by
    rw [Nat.card_congr (D.coordEquiv hO hι), Nat.card_eq_fintype_card]
    exact D.odd_card_Ψc i₀
  obtain ⟨m, hm⟩ := hodd
  haveI : IsSimpleGroup (D.L i₀) := HoltData.isSimpleGroup_L (D := D) hO i₀
  haveI : FaithfulSMul (D.L i₀) Ω := D.faithfulSMul_L hO hι
  obtain ⟨hm2, e, he⟩ :=
    CFSG.Holt.General.exists_mulEquiv_alternatingGroup_of_le_range
      (D.exists_mul_ne_mul_L hO i₀) hm
      (D.alternatingGroup_le_range_L hO hι hA) α
  have hYsub : Y.subgroupOf (D.L i₀) = MulAction.stabilizer (D.L i₀) α := by
    calc Y.subgroupOf (D.L i₀) = (MulAction.stabilizer X α).subgroupOf (D.L i₀) :=
          congrArg (fun H : Subgroup X => H.subgroupOf (D.L i₀)) hstab.symm
      _ = MulAction.stabilizer (D.L i₀) α := MulAction.stabilizer_subgroupOf (D.L i₀) α
  let eY1 : Y ≃* MulAction.stabilizer (D.L i₀) α :=
    (Subgroup.subgroupOfEquivOfLe (hYL i₀)).symm.trans (MulEquiv.subgroupCongr hYsub)
  let eS : MulAction.stabilizer (D.L i₀) α ≃*
      MulAction.stabilizer (alternatingGroup (Fin (2 * m + 1)))
        (0 : Fin (2 * m + 1)) :=
    (Subgroup.equivMapOfInjective (MulAction.stabilizer (D.L i₀) α) e.toMonoidHom
      e.injective).trans (MulEquiv.subgroupCongr he)
  let eA : MulAction.stabilizer (alternatingGroup (Fin (2 * m + 1)))
      (0 : Fin (2 * m + 1)) ≃* alternatingGroup {x : Fin (2 * m + 1) // x ≠ 0} :=
    (alternatingStabilizerZeroEquiv (n := 2 * m + 1)).symm
  have hcard : Fintype.card {x : Fin (2 * m + 1) // x ≠ 0} = 2 * m := by
    rw [Fintype.card_subtype]
    have hf : (Finset.univ.filter fun x : Fin (2 * m + 1) => x ≠ 0) =
        Finset.univ.erase 0 := by
      ext x
      simp
    rw [hf, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
      Fintype.card_fin]
    omega
  let eF : alternatingGroup {x : Fin (2 * m + 1) // x ≠ 0} ≃*
      alternatingGroup (Fin (2 * m)) := (Fintype.equivFinOfCardEq hcard).altCongrHom
  exact (halt m).false (eY1.trans (eS.trans (eA.trans eF)))

private theorem bender_le_normalizer {X : Type} [Group X]
    [Finite X] {Y : Subgroup X} [IsSimpleGroup Y] {t : X} {Ω : Type} [MulAction X Ω]
    (D : HoltData X Ω) {α : Ω} {i₀ : D.ι} {n i e : ℕ}
    (hB : IsBenderAction (D.L i₀) Ω n i e) (hstab : MulAction.stabilizer X α = Y)
    (hYL : ∀ i, Y ≤ D.L i)
    (hsyl : ∃ S : Sylow 2 X, t ∈ (S : Subgroup X) ∧
      (S : Subgroup X) ≤ Subgroup.centralizer {t})
    (hC_t : Subgroup.centralizer ({t} : Set X) ≤ Y) :
    ∃ S : Sylow 2 X, t ∈ (S : Subgroup X) ∧ (S : Subgroup X) ≤ Y ∧
      Y ≤ Subgroup.normalizer (S : Set X) := by
  obtain ⟨S, htS, hSle⟩ := hsyl
  have hSY : S ≤ Y := hSle.trans hC_t
  have hSleL : (S : Subgroup X) ≤ D.L i₀ := hSY.trans (hYL i₀)
  let Q : Sylow 2 (D.L i₀) := S.subtype hSleL
  have hQ : (Q : Subgroup (D.L i₀)) ≤ MulAction.stabilizer (D.L i₀) α := by
    rw [show (Q : Subgroup (D.L i₀)) = S.subgroupOf (D.L i₀) from
      Sylow.coe_subtype (P := S) hSleL]
    calc S.subgroupOf (D.L i₀) ≤ Y.subgroupOf (D.L i₀) :=
          Subgroup.subgroupOf_mono _ hSY
      _ = MulAction.stabilizer (D.L i₀) α := by
          rw [← MulAction.stabilizer_subgroupOf, hstab]
  have hstab_borel : MulAction.stabilizer (D.L i₀) α =
      borel (Q : Subgroup (D.L i₀)) := hB.stabilizer_eq_borel hQ
  have hQN : Subgroup.normalizer (Q : Subgroup (D.L i₀)) =
      (Subgroup.normalizer (S : Set X)).subgroupOf (D.L i₀) := by
    calc Subgroup.normalizer (Q : Subgroup (D.L i₀))
        = Subgroup.normalizer ((S : Subgroup X).subgroupOf (D.L i₀)) := by
          rw [Sylow.coe_subtype (P := S) hSleL]
      _ = (Subgroup.normalizer (S : Set X)).subgroupOf (D.L i₀) :=
          (Subgroup.subgroupOf_normalizer_eq (H := (S : Subgroup X))
            (N := D.L i₀) hSleL).symm
  have hYN : Y ≤ Subgroup.normalizer (S : Set X) := by
    intro y hy
    have hyα : y • α = α := MulAction.mem_stabilizer_iff.mp (hstab.symm ▸ hy)
    have hyL : (⟨y, hYL i₀ hy⟩ : D.L i₀) ∈ MulAction.stabilizer (D.L i₀) α := by
      rw [MulAction.mem_stabilizer_iff]
      simpa [Subgroup.smul_def] using hyα
    rw [hstab_borel] at hyL
    change (⟨y, hYL i₀ hy⟩ : D.L i₀) ∈
      Subgroup.normalizer (Q : Subgroup (D.L i₀)) at hyL
    rw [hQN] at hyL
    exact Subgroup.mem_subgroupOf.mp hyL
  exact ⟨S, htS, hSY, hYN⟩

private theorem false_of_bender {X : Type} [Group X] {Y : Subgroup X} [IsSimpleGroup Y]
    [Finite Y] {t : X} (htY : t ∈ Y) (ht_ne_one : t ≠ 1)
    (hna : ∃ a c : Y, a * c ≠ c * a)
    (hS : ∃ S : Sylow 2 X, t ∈ (S : Subgroup X) ∧ (S : Subgroup X) ≤ Y ∧
      Y ≤ Subgroup.normalizer (S : Set X)) : False := by
  obtain ⟨S, htS, hSY, hYN⟩ := hS
  have hNormS : (S.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSY).mpr hYN
  have htSY : (⟨t, htY⟩ : Y) ∈ S.subgroupOf Y := Subgroup.mem_subgroupOf.mpr htS
  have hStop : S.subgroupOf Y = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf Y) with h | h
    · exfalso
      rw [h, Subgroup.mem_bot] at htSY
      exact ht_ne_one (congrArg Subtype.val htSY)
    · exact h
  have hYleS : Y ≤ S := by
    intro y hy
    have hmem : (⟨y, hy⟩ : Y) ∈ S.subgroupOf Y := by rw [hStop]; trivial
    exact Subgroup.mem_subgroupOf.mp hmem
  have hP : IsPGroup 2 Y := (S.isPGroup').to_le hYleS
  haveI : IsPGroup 2 Y := hP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcenter_ne : Subgroup.center Y ≠ ⊥ :=
    (IsPGroup.bot_lt_center (p := 2) (G := Y) hP).ne'
  have hcenter_top : Subgroup.center Y = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · exact absurd h hcenter_ne
    · exact h
  have hcomm : IsMulCommutative Y := Subgroup.center_eq_top_iff.mp hcenter_top
  obtain ⟨a, c, hac⟩ := hna
  exact hac (hcomm.is_comm.comm a c)

theorem eq_top_of_isSimpleGroup_of_conj_mem (h : HoltTheorem1)
    {X : Type} [Group X] [Finite X] {Y : Subgroup X} [IsSimpleGroup Y] {t : X} (htY : t ∈ Y)
    (ht : orderOf t = 2) (hfix : ∀ g : X, g * t * g⁻¹ ∈ Y → g ∈ Y)
    (hsyl : ∃ S : Sylow 2 X, t ∈ (S : Subgroup X) ∧
      (S : Subgroup X) ≤ Subgroup.centralizer {t})
    (hna : ∃ a c : Y, a * c ≠ c * a)
    (halt : ∀ m : ℕ, IsEmpty (Y ≃* alternatingGroup (Fin (2 * m)))) :
    Y = ⊤ := by
  by_contra hY
  let Ω := X ⧸ Y
  let α : Ω := (QuotientGroup.mk (1 : X) : Ω)
  have ht2 : t * t = 1 := by
    have := orderOf_eq_prime_iff.mp ht
    simpa [pow_two] using this.1
  have ht_ne_one : t ≠ 1 := by
    intro h
    have h1 : orderOf t = 1 := by rw [h, orderOf_one]
    omega
  have hY_ne_bot : Y ≠ ⊥ := by
    intro h
    have ht_bot : t ∈ (⊥ : Subgroup X) := h ▸ htY
    rw [Subgroup.mem_bot] at ht_bot
    exact ht_ne_one ht_bot
  obtain ⟨hcore, hfaith, hC_t⟩ := core_faithful htY hfix hY
  let O := oddCoreOf (⊤ : Subgroup X)
  obtain ⟨hO_norm, hO_odd, hO_inf_Y⟩ := oddCore_normal_odd_inf htY ht hY
  have h_inv_t : ∀ o ∈ O, t * o * t⁻¹ = o⁻¹ :=
    involution_inverts_oddCore htY ht hC_t hO_norm hO_inf_Y
  have hO_bot : O = ⊥ :=
    oddCore_eq_bot htY ht hna hO_norm hO_odd hO_inf_Y h_inv_t
  have hstab : MulAction.stabilizer X α = Y :=
    MulAction.stabilizer_quotient Y
  have htriple : IsHoltTriple X Ω t α :=
    isHoltTriple_quotient α htY ht hfix hsyl hstab
  have ht_long : t ∈ longInv X Ω := mem_longInv_quotient α htY ht hfix hstab
  have ht_jHull : t ∈ jHull X Ω := mem_jHull_of_mem_longInv ht_long
  obtain ⟨D, hO_H⟩ := holtData_oddCore_bot h ht2 hfaith hO_bot htriple
  have hY_le_H : Y ≤ jHull X Ω := le_jHull_of_simple htY ht_ne_one ht_jHull
  have hne : ∀ i, D.L i ⊓ Y ≠ ⊥ := fun i => inf_L_ne_bot D hO_H hstab
  have hYL : ∀ i, Y ≤ D.L i := le_L D hO_H hstab hY_le_H hne
  haveI : Nontrivial Ω := QuotientGroup.nontrivial_iff.mpr hY
  obtain ⟨i₀, hι⟩ := D.exists_forall_eq_of_le_L hO_H hY_ne_bot hYL
  rcases D.factor i₀ with ⟨hA, h7⟩ | hM
  · exact false_of_alternating D hO_H hι hstab hYL hA halt
  · have hBdata : ∃ S : Sylow 2 X, t ∈ (S : Subgroup X) ∧
        (S : Subgroup X) ≤ Y ∧ Y ≤ Subgroup.normalizer (S : Set X) := by
      obtain ⟨n, i, e, hB⟩ := D.isBenderAction_L hO_H hι hM
      exact bender_le_normalizer D hB hstab hYL hsyl hC_t
    exact false_of_bender htY ht_ne_one hna hBdata

end CFSG.Holt.H78
