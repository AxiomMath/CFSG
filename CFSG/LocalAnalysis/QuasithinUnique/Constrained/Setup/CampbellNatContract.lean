module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatOutput
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAdapter

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Open CFSG.Quasithin CFSG.Quasithin.B6 CFSG.Quasithin.BlueprintB2
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Offender
  CFSG.SL2MinimalFaithful
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

section SL2Lemmas

variable {F : Type*} [Field F]

theorem center_sl2_eq_bot [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Subgroup.mem_bot]
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hr' : r ^ 2 = 1 := by simpa using hr
  have hsq : (r - 1) ^ 2 = 0 := by linear_combination hr' + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  apply Subtype.ext
  rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem normal_sl2_eq_top [CharP F 2] [Finite F] (h4 : ∃ s : Finset F, s.card = 4)
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [N.Normal] (hN : N ≠ ⊥) : N = ⊤ := by
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr h4)
  have hmap : (N.map (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))).Normal :=
    Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective _)
  have := hmap
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))) with hbot | htop
  · exfalso
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) x ∈
        N.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) :=
      ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      center_sl2_eq_bot] at h1
    exact h1
  · rw [eq_top_iff]
    intro s _
    have h1 : QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) s ∈
        N.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hns⟩ := h1
    have h2 : n⁻¹ * s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
      QuotientGroup.eq.mp hns
    rw [center_sl2_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at h2
    rw [← h2]
    exact hn

theorem not_commutative_sl2 : ¬ ∀ a b : Matrix.SpecialLinearGroup (Fin 2) F, a * b = b * a := by
  intro h
  have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 0) (h (unipotent 1) (lowerElt 1))
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h1
  simp [unipotent, lowerElt, Matrix.mul_apply, Fin.sum_univ_two] at h1

omit [Field F] in
theorem le_normalizer_commutator_left {G : Type*} [Group G] (A B : Subgroup G) :
    A ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ a ∈ A, ∀ x ∈ (⁅A, B⁆ : Subgroup G), a * x * a⁻¹ ∈ (⁅A, B⁆ : Subgroup G) := by
    intro a ha x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a', ha', b, hb, rfl⟩ := hx
      have : a * ⁅a', b⁆ * a⁻¹ = ⁅a * a', b⁆ * ⁅a, b⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem (Subgroup.commutator_mem_commutator (mul_mem ha ha') hb)
        (inv_mem (Subgroup.commutator_mem_commutator ha hb))
    | one => simp
    | mul x y _ _ ihx ihy =>
      have := mul_mem ihx ihy
      simpa [mul_assoc] using this
    | inv x _ ih =>
      have := inv_mem ih
      simpa [mul_assoc] using this
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key a ha x, fun hx => ?_⟩
  have := key a⁻¹ (inv_mem ha) _ hx
  simpa [mul_assoc] using this

theorem commutator_top_sl2_eq_top [CharP F 2] [Finite F] (h4 : ∃ s : Finset F, s.card = 4)
    (U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hU : U ≠ ⊥) :
    ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), U⁆ = ⊤ := by
  have hnormal : (⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), U⁆ :
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp (le_normalizer_commutator_left ⊤ U))
  obtain ⟨w, hwU, hw1⟩ : ∃ w ∈ U, w ≠ (1 : Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
    exact ⟨u, u.2, fun h => hu1 (Subtype.ext h)⟩
  have hnc : w ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [center_sl2_eq_bot]
    exact fun h => hw1 (Subgroup.mem_bot.mp h)
  rw [Subgroup.mem_center_iff] at hnc
  push Not at hnc
  obtain ⟨g, hg⟩ := hnc
  have hne : (⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), U⁆ :
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ≠ ⊥ := by
    intro hbot
    have hmem : ⁅g, w⁆ ∈ (⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), U⁆ :
          Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hwU
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
    apply hg
    calc g * w = (g * w * g⁻¹ * w⁻¹) * (w * g) := by group
      _ = w * g := by rw [hmem, one_mul]
  have := hnormal
  exact normal_sl2_eq_top h4 _ hne

theorem commutator_zpowers_eq [CharP F 2] [Finite F] (hcard : Nat.card F = 2)
    {t : Matrix.SpecialLinearGroup (Fin 2) F} (ht3 : orderOf t = 3)
    (U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hU : U ≠ ⊥)
    (hU2 : ∀ u ∈ U, u * u = 1) : ⁅Subgroup.zpowers t, U⁆ = Subgroup.zpowers t := by
  have hS6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 6 := by
    rw [card_specialLinearGroup_fin_two, hcard]; norm_num
  have hz3 : Nat.card (Subgroup.zpowers t) = 3 := by rw [Nat.card_zpowers, ht3]
  have hidx : (Subgroup.zpowers t).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers t)
    rw [hz3, hS6] at this
    omega
  have hnormal : (Subgroup.zpowers t).Normal := Subgroup.normal_of_index_eq_two hidx
  have hle : ⁅Subgroup.zpowers t, U⁆ ≤ Subgroup.zpowers t := Subgroup.commutator_le_left _ _
  have hne : ⁅Subgroup.zpowers t, U⁆ ≠ ⊥ := by
    intro hbot
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
    have hu1' : (u : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hcomm : (u : Matrix.SpecialLinearGroup (Fin 2) F) * t =
        t * (u : Matrix.SpecialLinearGroup (Fin 2) F) :=
      (mul_comm_of_commutator_eq_bot hbot (Subgroup.mem_zpowers t) u.2).symm
    have hu2 : orderOf (u : Matrix.SpecialLinearGroup (Fin 2) F) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hU2 u u.2) hu1'
    have hcop : Nat.Coprime (orderOf (u : Matrix.SpecialLinearGroup (Fin 2) F)) (orderOf t) := by
      rw [hu2, ht3]; norm_num
    have hord : orderOf ((u : Matrix.SpecialLinearGroup (Fin 2) F) * t) = 6 := by
      rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm hcop, hu2, ht3]
    have hcyc : IsCyclic (Matrix.SpecialLinearGroup (Fin 2) F) :=
      isCyclic_of_orderOf_eq_card _ (by rw [hord, hS6])
    exact not_commutative_sl2 (F := F) fun a b =>
      (IsCyclic.commGroup (α := Matrix.SpecialLinearGroup (Fin 2) F)).mul_comm a b
  have hdvd : Nat.card (⁅Subgroup.zpowers t, U⁆ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ∣ 3 :=
    hz3 ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exfalso
    apply hne
    exact Subgroup.eq_bot_of_card_eq _ h1
  · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hz3])).symm.symm

theorem commutator_rhoK_eq {G : Type*} [Group G] [Finite G] {X K D : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    {ρ : D →* Matrix.SpecialLinearGroup (Fin 2) F}
    {β : (⁅blockQ X, K⁆ : Subgroup G) →* Multiplicative (Fin 2 → F)}
    (h : NaturalOvergroupSetup X K) (m : NaturalOvergroupModule X K D ρ β)
    (U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hU : U ≠ ⊥)
    (hU2 : ∀ u ∈ U, u * u = 1) : ⁅rhoK K ρ, U⁆ = rhoK K ρ := by
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · rw [m.rhoK_eq_top h hn1 hcard]
    have h4 : ∃ s : Finset F, s.card = 4 := by
      have : Fintype F := Fintype.ofFinite F
      have h4' : 4 ≤ Fintype.card F := by
        rw [← Nat.card_eq_fintype_card, hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
        (by simpa using h4')
      exact ⟨t, ht⟩
    exact commutator_top_sl2_eq_top h4 U hU
  · have hn1' : n = 1 := le_antisymm hn1 hn
    subst hn1'
    have hcard2 : Nat.card F = 2 := by simpa using hcard
    obtain ⟨t, ht3, hrho⟩ := m.rhoK_eq_zpowers h hcard2
    rw [hrho]
    exact commutator_zpowers_eq hcard2 ht3 U hU hU2

theorem eq_of_map_eq_of_ker_two {A B : Type*} [Group A] [Group B] (f : A →* B) {L D : Subgroup A}
    (hno : NoPQuotient 2 L) (hDL : D ≤ L) (hDn : (D.subgroupOf L).Normal)
    (hmap : D.map f = L.map f) (hker : ∀ l ∈ L, f l = 1 → ∃ k : ℕ, l ^ 2 ^ k = 1) : D = L := by
  apply le_antisymm hDL
  have hq : IsPGroup 2 (L ⧸ D.subgroupOf L) := by
    intro x
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : f l ∈ D.map f := hmap ▸ Subgroup.mem_map_of_mem f hl
    obtain ⟨d, hd, hdl⟩ := h1
    have hq1 : f (d⁻¹ * l) = 1 := by rw [map_mul, map_inv, hdl, inv_mul_cancel]
    obtain ⟨k, hk⟩ := hker (d⁻¹ * l) (mul_mem (inv_mem (hDL hd)) hl) hq1
    refine ⟨k, ?_⟩
    have hmk : (QuotientGroup.mk ⟨l, hl⟩ : L ⧸ D.subgroupOf L) =
        QuotientGroup.mk ⟨d⁻¹ * l, mul_mem (inv_mem (hDL hd)) hl⟩ := by
      rw [QuotientGroup.eq]
      show (⟨l, hl⟩ : L)⁻¹ * ⟨d⁻¹ * l, mul_mem (inv_mem (hDL hd)) hl⟩ ∈ D.subgroupOf L
      rw [Subgroup.mem_subgroupOf]
      have : l⁻¹ * (d⁻¹ * l) = (l⁻¹ * d⁻¹ * l) := by group
      show l⁻¹ * (d⁻¹ * l) ∈ D
      rw [this]
      have := hDn.conj_mem ⟨d⁻¹, inv_mem (hDL hd)⟩ (Subgroup.mem_subgroupOf.mpr (inv_mem hd))
        ⟨l⁻¹, inv_mem hl⟩
      simpa [mul_assoc] using Subgroup.mem_subgroupOf.mp this
    rw [hmk, ← QuotientGroup.mk_pow]
    have : (⟨d⁻¹ * l, mul_mem (inv_mem (hDL hd)) hl⟩ : L) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [this]
    exact QuotientGroup.mk_one _
  have := hno _ hq
  intro x hx
  have : (⟨x, hx⟩ : L) ∈ D.subgroupOf L := ‹D.subgroupOf L = ⊤› ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

end SL2Lemmas

section Contract

variable {H : Type*} [Group H] [Finite H] {k : Type} [Field k] [Finite k] [CharP k 2]

namespace IsNatQuotSetting

variable {R M V : Subgroup H} {ρ : H →* Gamma k} {φ : V →* Multiplicative (Fin 2 → k)}

theorem actual_Campbell_natural_minimal_parabolic_chi0_block (h : IsNatQuotSetting R M V ρ φ)
    (hchar : CharTwo (⊤ : Subgroup H)) (hnc : NoCharNormal R ⊤)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card k = 2 ^ n) :
    oddOrderSubgroup (⊤ : Subgroup H) ⊔ R = ⊤ ∧
      IsChi0Block (⊤ : Subgroup H) (oddOrderSubgroup (⊤ : Subgroup H)) ∧
      ⁅oddOrderSubgroup (⊤ : Subgroup H), elemThompsonIn 2 R⁆ = oddOrderSubgroup (⊤ : Subgroup H) ∧
      (1 < n → IsLin2Type (oddOrderSubgroup (⊤ : Subgroup H)) n) ∧
      (n = 1 → IsAltType (oddOrderSubgroup (⊤ : Subgroup H)) 3 ∧
        Nonempty (↥(oddOrderSubgroup (⊤ : Subgroup H)) ≃* alternatingGroup (Fin 4))) := by
  classical
  have hVn : V.Normal := h.normal_V
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := h.normal_L
  have hVH := h.not_le_centralizer hJ
  set L : Subgroup H := oddOrderSubgroup (⊤ : Subgroup H) with hLdef
  set Gb : Subgroup H := baumannOvergroup R with hGbdef
  obtain ⟨hHLR, -⟩ := minimal_parabolic_reduced_module_Frattini_kernel_production h.sylow
    h.nonnormal h.le_M h.M_lt h.M_max h.reduced hVH
  obtain ⟨h1, h3, hρG, hVmod, -, hQK, hVE, βo, hβs, hβk, hβe⟩ :=
    h.actual_Campbell_natural_minimal_parabolic_output hchar hnc hJ
  obtain ⟨-, -, -, -, -, -, -, -, -, hKodd, -⟩ :=
    h.actual_Baumann_whole_center_natural_module hchar hnc hJ
  obtain ⟨ℓ, -, -, hJρ, -⟩ := h.Baumann_Sylow hJ
  have hmem := h.rho_mem_baumannOvergroup hJ
  have hLG : L ≤ Gb := le_sup_left
  have hQmap : blockQ Gb = (CFSG.pCore 2 ↥Gb).map Gb.subtype := blockQ_eq_map Gb
  have hKodd' : (Kodd ↥Gb).map Gb.subtype = L := hKodd
  have hUmap : (⁅blockQ Gb, L⁆ : Subgroup H) = (⁅CFSG.pCore 2 ↥Gb, Kodd ↥Gb⁆).map Gb.subtype := by
    rw [hQmap, ← hKodd', Subgroup.map_commutator]
  have hcentral : (⁅blockQ Gb, L⁆ : Subgroup H) ≤
      Subgroup.centralizer ((blockQ Gb : Subgroup H) : Set H) := by
    rw [hUmap, hQK]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rw [hQmap] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hxE := hVE hx
    have := (mem_centerTorsion_iff.mp hxE).2.1 p hp
    exact congrArg Subtype.val this
  have hsetup : NaturalOvergroupSetup Gb L :=
    { charTwo := h3
      le := hLG
      normal := inferInstance
      noPQ := hasNoTwoQuotient_oddOrderSubgroup ⊤
      two_quot := fun x _ => exists_pow_mem_oddOrderSubgroup (H := (⊤ : Subgroup H)) trivial
      central := hcentral }
  let ρ₀ : ↥Gb →* Matrix.SpecialLinearGroup (Fin 2) k := h.actualRho hJ
  let W : Subgroup ↥Gb := ⁅CFSG.pCore 2 ↥Gb, Kodd ↥Gb⁆
  let eU : ↥(⁅blockQ Gb, L⁆ : Subgroup H) ≃* ↥W :=
    (MulEquiv.subgroupCongr hUmap).trans (W.equivMapOfInjective Gb.subtype Gb.subtype_injective).symm
  have heU : ∀ u : ↥(⁅blockQ Gb, L⁆ : Subgroup H), (((eU u : ↥W) : ↥Gb) : H) = (u : H) := by
    intro u
    have h3' := (W.equivMapOfInjective Gb.subtype Gb.subtype_injective).apply_symm_apply
      (MulEquiv.subgroupCongr hUmap u)
    have h4' := congrArg (fun z : ↥(W.map Gb.subtype) => (z : H)) h3'
    rw [Subgroup.coe_equivMapOfInjective_apply] at h4'
    exact h4'
  let β' : ↥(⁅blockQ Gb, L⁆ : Subgroup H) →* Multiplicative (Fin 2 → k) := βo.comp eU.toMonoidHom
  have hmod : NaturalOvergroupModule Gb L Gb ρ₀ β' :=
    { KD := hLG
      DX := le_rfl
      ρ_surj := restrictSL_surjective ρ Gb hmem hρG
      β_surj := hβs.comp eU.surjective
      β_ker := by
        ext u
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        show βo (eU u) = 1 ↔ _
        have hkerβ : βo (eU u) = 1 ↔ (eU u) ∈ (W ⊓ Subgroup.center ↥Gb).subgroupOf W := by
          rw [← hβk]; exact MonoidHom.mem_ker.symm
        rw [hkerβ, Subgroup.mem_subgroupOf]
        constructor
        · intro hx
          refine Subgroup.mem_inf.mpr ⟨u.2, ?_⟩
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          have := Subgroup.mem_center_iff.mp hx.2 ⟨g, hg⟩
          have h5 := congrArg Subtype.val this
          rw [← heU u]
          exact h5
        · intro hx
          refine Subgroup.mem_inf.mpr ⟨(eU u).2, Subgroup.mem_center_iff.mpr fun g => ?_⟩
          apply Subtype.ext
          have := Subgroup.mem_centralizer_iff.mp hx.2 (g : H) g.2
          show (g : H) * ((eU u : ↥W) : ↥Gb) = ((eU u : ↥W) : ↥Gb) * (g : H)
          rw [heU u]
          exact this
      β_equiv := by
        intro d u u' hu'
        have := hβe d (eU u) (eU u') (Subtype.ext (by
          show (((eU u' : ↥W) : ↥Gb) : H) = (d : H) * (((eU u : ↥W) : ↥Gb) : H) * (d : H)⁻¹
          rw [heU u', heU u]; exact hu'))
        exact this }
  obtain ⟨-, -, -, -, hshort, hchi, -, -, hfKker, hLin, hAlt⟩ :=
    natural_overgroup_recognizes_actual_chi0_block hn hcard hsetup hmod
  have hsubn : (L.subgroupOf (⊤ : Subgroup H)).IsSubnormal := by
    have : (L.subgroupOf (⊤ : Subgroup H)).Normal := inferInstance
    exact this.isSubnormal
  have hchi' : IsChi0Block (⊤ : Subgroup H) L := ⟨⟨hshort, le_top, hsubn⟩, hchi.2⟩
  set J : Subgroup H := elemThompsonIn 2 R with hJdef
  have hJS : J ≤ elemBaumannIn 2 R := elemThompsonIn_le_elemBaumannIn 2 R
  have hJG : J ≤ Gb := hJS.trans le_sup_right
  set L' : Subgroup ↥Gb := L.subgroupOf Gb with hL'def
  set J' : Subgroup ↥Gb := J.subgroupOf Gb with hJ'def
  have hL'n : L'.Normal := inferInstance
  have hJ'map : J'.map ρ₀ = rootGrp ℓ := by
    apply Subgroup.map_injective (slPerm_injective (k := k))
    have e1 : (slPerm k).comp ρ₀ = ((Gamma k).subtype.comp ρ).comp Gb.subtype :=
      MonoidHom.ext fun x => h.slPerm_actualRho hJ x
    have e2 : (J'.map ρ₀).map (slPerm k) = rootPerm ℓ := by
      rw [Subgroup.map_map, e1, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hJG,
        ← Subgroup.map_map, hJρ]
      exact map_subtype_rootGamma ℓ
    rw [e2]
    rfl
  have hne : rootGrp ℓ ≠ ⊥ := by
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_rootGrp ℓ
    intro hbot
    rw [hbot] at hu
    exact hu1 (Subgroup.mem_bot.mp hu)
  have hsq : ∀ u ∈ rootGrp ℓ, u * u = 1 := fun u hu => mul_self_eq_one_of_mem_rootGrp hu
  have hcomm := commutator_rhoK_eq hn hcard hsetup hmod (rootGrp ℓ) hne hsq
  have hDL : ⁅L', J'⁆ ≤ L' := Subgroup.commutator_le_left L' J'
  have hDn : ((⁅L', J'⁆ : Subgroup ↥Gb).subgroupOf L').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mpr (le_normalizer_commutator_left L' J')
  have hmapD : (⁅L', J'⁆ : Subgroup ↥Gb).map ρ₀ = L'.map ρ₀ := by
    rw [Subgroup.map_commutator, hJ'map]
    exact hcomm
  have hno' : NoPQuotient 2 L' :=
    NoPQuotient.of_surjective (Subgroup.subgroupOfEquivOfLe hLG).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hLG).symm.surjective hsetup.noPQ
  have hker : ∀ l ∈ L', ρ₀ l = 1 → ∃ j : ℕ, l ^ 2 ^ j = 1 := by
    intro l hl hρl
    have hl' : (l : H) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hmemk : (⟨(l : H), hl'⟩ : ↥L) ∈ (ρ₀.comp (Subgroup.inclusion hLG)).ker := by
      rw [MonoidHom.mem_ker]
      exact hρl
    rw [hfKker] at hmemk
    obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hmemk⟩
    refine ⟨j, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : H)) hj
    simpa using this
  have hDeq : (⁅L', J'⁆ : Subgroup ↥Gb) = L' :=
    eq_of_map_eq_of_ker_two ρ₀ hno' hDL hDn hmapD hker
  have hthompson : ⁅L, J⁆ = L := by
    have h1 := congrArg (Subgroup.map Gb.subtype) hDeq
    rw [Subgroup.map_commutator, hL'def, hJ'def, Subgroup.map_subgroupOf_eq_of_le hLG,
      Subgroup.map_subgroupOf_eq_of_le hJG] at h1
    exact h1
  exact ⟨hHLR, hchi', hthompson, fun hn1 => (hLin hn1).2, fun hn1 => (by
    obtain ⟨-, hA4, hA⟩ := hAlt hn1
    exact ⟨hA, hA4⟩)⟩

end IsNatQuotSetting

end Contract

end CFSG.QuasithinUnique.Setup.Campbell
