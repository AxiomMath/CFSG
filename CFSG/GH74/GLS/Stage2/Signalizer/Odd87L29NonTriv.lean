module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29NonSwap
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29PGLInner

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Centre

theorem z_mem_cen {G : Type} [Group G] (z : G) : z ∈ Cen z := by
  show z ∈ centralizer ({z} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]

theorem zbar_central {G : Type} [Group G] (z : G) (y : CentralizerBar z) :
    toBar z ⟨z, z_mem_cen z⟩ * y = y * toBar z ⟨z, z_mem_cen z⟩ := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
  show toBar z ⟨z, z_mem_cen z⟩ * toBar z c = toBar z c * toBar z ⟨z, z_mem_cen z⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have := c.2
  rw [show (c : G) ∈ Cen z ↔ _ from Iff.rfl, Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

theorem eq_one_of_toBar_eq_one_of_sq {G : Type} [Group G] [Finite G] {z c : G} (hc : c ∈ Cen z)
    (hc2 : c * c = 1) (h : toBar z ⟨c, hc⟩ = 1) : c = 1 := by
  have hmem : (⟨c, hc⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).1 h
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(Cen z))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have h1 : orderOf (⟨⟨c, hc⟩, hmem⟩ : ↥(pPrimeCore 2 ↥(Cen z))) ∣
      Nat.card (pPrimeCore 2 ↥(Cen z)) := orderOf_dvd_natCard _
  have h2 : orderOf (⟨⟨c, hc⟩, hmem⟩ : ↥(pPrimeCore 2 ↥(Cen z))) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by
      apply Subtype.ext
      apply Subtype.ext
      simpa [pow_two] using hc2)
  have h3 : orderOf (⟨⟨c, hc⟩, hmem⟩ : ↥(pPrimeCore 2 ↥(Cen z))) = 1 := by
    have hodd' := Odd.of_dvd_nat hodd h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  have h4 := orderOf_eq_one_iff.mp h3
  have h5 := congrArg (fun t : ↥(pPrimeCore 2 ↥(Cen z)) => ((t : ↥(Cen z)) : G)) h4
  simpa using h5

theorem mem_zpowers_of_toBar_mem {G : Type} [Group G] [Finite G] {z u : G} (hz2 : z * z = 1)
    (hu : u ∈ Cen z) (hu2 : u * u = 1)
    (h : toBar z ⟨u, hu⟩ ∈ zpowers (toBar z ⟨z, z_mem_cen z⟩)) : u ∈ zpowers z := by
  have hzz : (toBar z ⟨z, z_mem_cen z⟩) ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← map_mul]
    have : (⟨z, z_mem_cen z⟩ * ⟨z, z_mem_cen z⟩ : ↥(Cen z)) = 1 := Subtype.ext hz2
    rw [this, map_one]
  obtain ⟨n, hn0⟩ := h
  have hn : (toBar z ⟨z, z_mem_cen z⟩) ^ n = toBar z ⟨u, hu⟩ := hn0
  rw [zpow_eq_zpow_emod n hzz] at hn
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · rw [h0, zpow_zero] at hn
    have : u = 1 := eq_one_of_toBar_eq_one_of_sq hu hu2 hn.symm
    rw [this]
    exact one_mem _
  · rw [h1, zpow_one] at hn
    have hc : u * z⁻¹ ∈ Cen z := by
      have hz : z⁻¹ ∈ Cen z := (Cen z).inv_mem (z_mem_cen z)
      exact (Cen z).mul_mem hu hz
    have huz : u * z = z * u := by
      have := hu
      rw [show u ∈ Cen z ↔ _ from Iff.rfl, Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    have hsq : u * z⁻¹ * (u * z⁻¹) = 1 := by
      have hzi : z⁻¹ = z := by
        have : z * z = 1 := hz2
        exact inv_eq_of_mul_eq_one_right this
      rw [hzi]
      calc u * z * (u * z) = u * (z * u) * z := by group
        _ = u * (u * z) * z := by rw [← huz]
        _ = (u * u) * (z * z) := by group
        _ = 1 := by rw [hu2, hz2, one_mul]
    have h1 : toBar z ⟨u * z⁻¹, hc⟩ = 1 := by
      have e : (⟨u * z⁻¹, hc⟩ : ↥(Cen z)) = ⟨u, hu⟩ * ⟨z, z_mem_cen z⟩⁻¹ := rfl
      rw [e, map_mul, map_inv, ← hn, mul_inv_cancel]
    have := eq_one_of_toBar_eq_one_of_sq hc hsq h1
    have hu' : u = z := by
      have h2 : u = u * z⁻¹ * z := by group
      rw [h2, this, one_mul]
    rw [hu']
    exact mem_zpowers z

end Centre

section PairFacts

theorem mem_inf_of_sq_one_of_centralizes {H : Type*} [Group H] {A B : Subgroup H}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hZA : Nat.card ↥(center ↥A) = 2)
    (hI : Nat.card ↥(A ⊓ B) = 2)
    (hinvB : ∀ x ∈ B, ∀ y ∈ B, orderOf x = 2 → orderOf y = 2 → x = y)
    {c : H} (hc : c ∈ A ⊔ B) (hc2 : c * c = 1) (hcen : ∀ a ∈ A, c * a = a * c) :
    c ∈ A ⊓ B := by
  obtain ⟨a, ha, b, hb, hcab⟩ := exists_mul_of_mem_sup_of_commute_aux hcomm hc
  have hac : ∀ x ∈ A, a * x = x * a := by
    intro x hx
    have h1 := hcen x hx
    rw [hcab] at h1
    have h2 := hcomm x hx b hb
    have h3 : a * x * b = x * a * b := by
      calc a * x * b = a * (x * b) := by group
        _ = a * (b * x) := by rw [h2]
        _ = a * b * x := by group
        _ = x * (a * b) := h1
        _ = x * a * b := by group
    exact mul_right_cancel h3
  have haI : a ∈ A ⊓ B := mem_inf_of_central hcomm hZA hI ha hac
  have hcB : c ∈ B := by
    rw [hcab]
    exact B.mul_mem (Subgroup.mem_inf.mp haI).2 hb
  by_cases hc1 : c = 1
  · rw [hc1]
    exact (A ⊓ B).one_mem
  · have hfin : Finite ↥(A ⊓ B) := Nat.finite_of_card_ne_zero (by rw [hI]; norm_num)
    have : Nontrivial ↥(A ⊓ B) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hI]; norm_num)
    obtain ⟨ζ, hζ⟩ := exists_ne (1 : ↥(A ⊓ B))
    have hζ1 : (ζ : H) ≠ 1 := fun h => hζ (Subtype.ext h)
    have hζo : orderOf (ζ : H) = 2 := by
      have h1 : orderOf (ζ : H) ∣ 2 := by
        rw [← hI, Subgroup.orderOf_coe]
        exact orderOf_dvd_natCard ζ
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hζ1
      · exact h
    have hco : orderOf c = 2 := by
      have h1 : c ^ 2 = 1 := by rw [pow_two]; exact hc2
      exact orderOf_eq_prime h1 hc1
    have : c = ζ := hinvB c hcB ζ (Subgroup.mem_inf.mp ζ.2).2 hco hζo
    rw [this]
    exact ζ.2

theorem le_normalizer_of_commute_aux {Y : Type*} [Group Y] {A B : Subgroup Y}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ normalizer (A : Set Y) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : b * x * b⁻¹ = x := by rw [← h x hx b hb]; group
    rw [this]; exact hx
  · intro hx
    have hc : (b * x * b⁻¹) * b⁻¹ = b⁻¹ * (b * x * b⁻¹) := h _ hx b⁻¹ (B.inv_mem hb)
    have : x = b * x * b⁻¹ := by
      calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
        _ = (b * x * b⁻¹) * b⁻¹ * b := by rw [← hc]
        _ = b * x * b⁻¹ := by group
    rw [this]; exact hx

theorem sup_le_normalizer_aux {Y : Type*} [Group Y] {A B : Subgroup Y}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ⊔ B ≤ normalizer (A : Set Y) :=
  sup_le Subgroup.le_normalizer (le_normalizer_of_commute_aux h)

variable {G : Type} [Group G] {z : G} {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem normalizes_of_mem_LBar (hp : PairShape z q₁ q₂ L₁ L₂) {c : CentralizerBar z}
    (hc : c ∈ LBar z) :
    c ∈ normalizer (L₁ : Set (CentralizerBar z)) ∧
      c ∈ normalizer (L₂ : Set (CentralizerBar z)) := by
  obtain ⟨hsup, hcomm, -⟩ := hp.prod
  rw [← hsup] at hc
  refine ⟨sup_le_normalizer_aux hcomm hc, ?_⟩
  rw [sup_comm] at hc
  exact sup_le_normalizer_aux (fun b hb a ha => (hcomm a ha b hb).symm) hc

theorem zbar_mem_inf [Finite G] (hp : PairShape z q₁ q₂ L₁ L₂) :
    toBar z ⟨z, z_mem_cen z⟩ ∈ L₁ ⊓ L₂ :=
  centralizer_pair_le_inf hp _ (fun a _ => zbar_central z a) (fun b _ => zbar_central z b)

theorem inf_eq_zpowers_zbar [Finite G] (hp : PairShape z q₁ q₂ L₁ L₂) (hz2 : orderOf z = 2) :
    L₁ ⊓ L₂ = zpowers (toBar z ⟨z, z_mem_cen z⟩) := by
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hne : toBar z ⟨z, z_mem_cen z⟩ ≠ 1 := by
    intro h
    have := eq_one_of_toBar_eq_one_of_sq (z_mem_cen z) hzz h
    rw [this, orderOf_one] at hz2
    omega
  have hsq : toBar z ⟨z, z_mem_cen z⟩ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    have : (⟨z, z_mem_cen z⟩ * ⟨z, z_mem_cen z⟩ : ↥(Cen z)) = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hord : orderOf (toBar z ⟨z, z_mem_cen z⟩) = 2 := orderOf_eq_prime hsq hne
  have hle : zpowers (toBar z ⟨z, z_mem_cen z⟩) ≤ L₁ ⊓ L₂ := (zpowers_le).mpr (zbar_mem_inf hp)
  have hI : Nat.card ↥(L₁ ⊓ L₂) = 2 := hp.prod.2.2
  have hfin : Finite ↥(L₁ ⊓ L₂) := Nat.finite_of_card_ne_zero (by rw [hI]; norm_num)
  have hc : Nat.card ↥(zpowers (toBar z ⟨z, z_mem_cen z⟩)) = 2 := by rw [Nat.card_zpowers, hord]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hI])).symm

omit [Group G] in
theorem actOnK_eq_one_imp {X : Type} [Group X] {K : Subgroup X} {s : X}
    (hs : s ∈ normalizer (K : Set X)) (h : Stage1.Main.actOnK K s hs = 1) :
    ∀ a ∈ K, s * a = a * s := by
  intro a ha
  have := congrArg (fun φ : MulAut ↥K => ((φ ⟨a, ha⟩ : ↥K) : X)) h
  simp only [MulAut.one_apply] at this
  show s * a = a * s
  calc s * a = (s * a * s⁻¹) * s := by group
    _ = a * s := by rw [show s * a * s⁻¹ = a from this]

theorem actOnK_ne_one_of_mem_LBar [Finite G] (hp : PairShape z q₁ q₂ L₁ L₂) (hz2 : orderOf z = 2)
    {u : G} (hu : u ∈ Cen z) (hu2 : u * u = 1) (hu1 : u ∉ zpowers z)
    (hLB : toBar z ⟨u, hu⟩ ∈ LBar z)
    (hn₁ : toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hn₂ : toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) :
    Stage1.Main.actOnK L₁ (toBar z ⟨u, hu⟩) hn₁ ≠ 1 ∧
      Stage1.Main.actOnK L₂ (toBar z ⟨u, hu⟩) hn₂ ≠ 1 := by
  obtain ⟨hsup, hcomm, hI⟩ := hp.prod
  have h4₁ : 4 ≤ q₁ := by have := hp.gt₁; omega
  have h4₂ : 4 ≤ q₂ := by have := hp.gt₂; omega
  obtain ⟨-, hZ₁, hinv₁⟩ := Stage2.Local.sl2_model_facts hp.odd₁ h4₁ hp.sl₁
  obtain ⟨-, hZ₂, hinv₂⟩ := Stage2.Local.sl2_model_facts hp.odd₂ h4₂ hp.sl₂
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hsq : (⟨u, hu⟩ : ↥(Cen z)) * ⟨u, hu⟩ = 1 := Subtype.ext hu2
  have hū2 : toBar z ⟨u, hu⟩ * toBar z ⟨u, hu⟩ = 1 := by rw [← map_mul, hsq, map_one]
  have hnI : toBar z ⟨u, hu⟩ ∉ L₁ ⊓ L₂ := by
    intro h
    rw [inf_eq_zpowers_zbar hp hz2] at h
    exact hu1 (mem_zpowers_of_toBar_mem hzz hu hu2 h)
  have hLB₁ : toBar z ⟨u, hu⟩ ∈ L₁ ⊔ L₂ := hsup ▸ hLB
  have hLB₂ : toBar z ⟨u, hu⟩ ∈ L₂ ⊔ L₁ := by rw [sup_comm]; exact hLB₁
  refine ⟨fun h => hnI ?_, fun h => hnI ?_⟩
  · exact mem_inf_of_sq_one_of_centralizes hcomm hZ₁ hI
      (fun x hx y hy => hinv₂ x hx y hy) hLB₁ hū2 (actOnK_eq_one_imp hn₁ h)
  · have := mem_inf_of_sq_one_of_centralizes (A := L₂) (B := L₁)
      (fun b hb a ha => (hcomm a ha b hb).symm) hZ₂ (by rwa [inf_comm])
      (fun x hx y hy => hinv₁ x hx y hy) hLB₂ hū2 (actOnK_eq_one_imp hn₂ h)
    rwa [inf_comm] at this

end PairFacts

section Psp4

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

omit [Finite G] in
theorem LC_le_cen (z : G) : LC z ≤ Cen z := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

omit [Finite G] in
theorem toBar_mem_LBar {u : G} (hu : u ∈ LC z) :
    toBar z ⟨u, LC_le_cen z hu⟩ ∈ LBar z :=
  ⟨⟨u, LC_le_cen z hu⟩, hu, rfl⟩

omit [Finite G] in
theorem not_mem_normalizer_of_swaps (hne : L₁ ≠ L₂) {s : G} (hs : s ∈ Cen z)
    (hsw : Swaps z s L₁ L₂) :
    toBar z ⟨s, hs⟩ ∉ normalizer (L₁ : Set (CentralizerBar z)) := by
  intro hn
  obtain ⟨hs', h1, -⟩ := hsw
  have h2 : conjugate L₁ (toBar z ⟨s, hs'⟩) = L₁ :=
    map_conj_eq_of_mem_normalizer ((normalizer (L₁ : Set (CentralizerBar z))).inv_mem hn)
  exact hne (h2.symm.trans h1)

theorem mem_RC_of_nonswap (hp : Stage1PSp4 G z S q L₁ L₂) {u : G} (huS : u ∈ S)
    (hu : u ∈ Cen z) (hn₁ : toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z))) :
    u ∈ RC S z := by
  have hpair := PairShape.of_pair hp.pair
  obtain ⟨s, hsS, hsw'⟩ := hp.pair.swap
  obtain ⟨hs, -, -⟩ := id hsw'
  by_contra huR
  have hsR : s ∉ RC S z := by
    intro hsR
    have hLB := toBar_mem_LBar (z := z) hsR.2
    exact not_mem_normalizer_of_swaps hp.pair.ne hs hsw'
      (normalizes_of_mem_LBar hpair hLB).1
  have hidx : ((RC S z).subgroupOf S).index = 2 := hp.index
  have huR' : (⟨u, huS⟩ : ↥S) ∉ (RC S z).subgroupOf S := fun h => huR h
  have hsR' : (⟨s, hsS⟩ : ↥S) ∉ (RC S z).subgroupOf S := fun h => hsR h
  have hprod : (⟨u, huS⟩ : ↥S)⁻¹ * ⟨s, hsS⟩ ∈ (RC S z).subgroupOf S := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    constructor
    · intro h
      exact absurd ((Subgroup.inv_mem_iff _).1 h) huR'
    · intro h
      exact absurd h hsR'
  have hprodR : u⁻¹ * s ∈ RC S z := hprod
  have hLB := toBar_mem_LBar (z := z) hprodR.2
  have hsn : toBar z ⟨s, hs⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) := by
    have e : toBar z ⟨s, hs⟩ = toBar z ⟨u, hu⟩ * toBar z ⟨u⁻¹ * s, LC_le_cen z hprodR.2⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      show s = u * (u⁻¹ * s)
      group
    rw [e]
    exact (normalizer (L₁ : Set (CentralizerBar z))).mul_mem hn₁
      (normalizes_of_mem_LBar hpair hLB).1
  exact not_mem_normalizer_of_swaps hp.pair.ne hs hsw' hsn

end Psp4

section PGLCase

variable {G : Type} [Group G] [Finite G] {z : G} {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}

omit [Finite G] in
theorem card_of_sl2_model_aux {Y : Type} [Group Y] {L : Subgroup Y} {q : ℕ}
    (h : HasSL2Model ↥L (fun r => r = q)) : Nat.card ↥L = q * (q ^ 2 - 1) := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h
  have hq' : Nat.card F = q := hq
  rw [Nat.card_congr (e.trans (specialLinearGroupEquivStatedSL 2 F).symm).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hq']

omit [Finite G] in
theorem PairShape.symm (hp : PairShape z q₁ q₂ L₁ L₂) : PairShape z q₂ q₁ L₂ L₁ where
  odd₁ := hp.odd₂
  odd₂ := hp.odd₁
  gt₁ := hp.gt₂
  gt₂ := hp.gt₁
  ne := hp.ne.symm
  prod := ⟨by rw [sup_comm]; exact hp.prod.1, fun a ha b hb => (hp.prod.2.1 b hb a ha).symm,
    by rw [inf_comm]; exact hp.prod.2.2⟩
  sl₁ := hp.sl₂
  sl₂ := hp.sl₁
  comps := by rw [hp.comps]; exact Set.pair_comm _ _
  fitting := hp.fitting

theorem false_of_centralizes_of_index_two (hp : PairShape z q₁ q₂ L₁ L₂) {R M : Subgroup G}
    (hRL : R ≤ LC z) (hMC : M ≤ Cen z) (hidx : R.relIndex M ≤ 2) {u : G}
    (huM : u ∈ M) (huR : u ∉ R) (hpgl : InducedPGL2 L₁ (barOf z M) q₁)
    (hcen : ∀ a ∈ L₁, toBar z ⟨u, hMC huM⟩ * a = a * toBar z ⟨u, hMC huM⟩) : False := by
  obtain ⟨hsup, hcomm, -⟩ := hp.prod
  have h4 : 4 ≤ q₁ := by have := hp.gt₁; omega
  obtain ⟨-, hZ, -⟩ := Stage2.Local.sl2_model_facts hp.odd₁ h4 hp.sl₁
  have hL := card_of_sl2_model_aux hp.sl₁
  have hidx2 : (R.subgroupOf M).index = 2 := by
    have h1 : (R.subgroupOf M).index ≠ 1 := by
      intro h
      apply huR
      have := (Subgroup.index_eq_one.mp h)
      have hmem : (⟨u, huM⟩ : ↥M) ∈ R.subgroupOf M := by rw [this]; exact Subgroup.mem_top _
      exact hmem
    have h0 : (R.subgroupOf M).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have h3 : (R.subgroupOf M).index ≤ 2 := hidx
    omega
  apply false_of_pgl_inner hZ hL hpgl
  rintro t ⟨c, hc, rfl⟩
  have hcM : (c : G) ∈ M := hc
  by_cases hcR : (c : G) ∈ R
  · have hLB := toBar_mem_LBar (z := z) (hRL hcR)
    rw [← hsup] at hLB
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute_aux hcomm hLB
    refine ⟨a, ha, ?_⟩
    rw [hab, inv_mul_cancel_left]
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx b hb
  · have hu' : (⟨u, huM⟩ : ↥M)⁻¹ ∉ R.subgroupOf M := fun h => huR ((Subgroup.inv_mem_iff _).1 h)
    have hcR' : (⟨c, hcM⟩ : ↥M) ∉ R.subgroupOf M := hcR
    have hprod : (⟨c, hcM⟩ : ↥M) * (⟨u, huM⟩ : ↥M)⁻¹ ∈ R.subgroupOf M := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx2]
      exact ⟨fun h => absurd h hcR', fun h => absurd h hu'⟩
    have hprodR : (c : G) * u⁻¹ ∈ R := hprod
    have hLB := toBar_mem_LBar (z := z) (hRL hprodR)
    rw [← hsup] at hLB
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute_aux hcomm hLB
    refine ⟨a, ha, ?_⟩
    have e : toBar z c = toBar z ⟨(c : G) * u⁻¹, LC_le_cen z (hRL hprodR)⟩ * toBar z ⟨u, hMC huM⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      show (c : G) = (c : G) * u⁻¹ * u
      group
    rw [e, hab]
    have h2 : a⁻¹ * (a * b * toBar z ⟨u, hMC huM⟩) = b * toBar z ⟨u, hMC huM⟩ := by group
    rw [h2]
    refine Subgroup.mul_mem _ (Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx b hb) ?_
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hcen x hx).symm

theorem actOnK_ne_one_of_index_two (hp : PairShape z q₁ q₂ L₁ L₂) {R M : Subgroup G}
    (hRL : R ≤ LC z) (hMC : M ≤ Cen z) (hidx : R.relIndex M ≤ 2) {u : G} (huM : u ∈ M)
    (huR : u ∉ R) (hpgl₁ : InducedPGL2 L₁ (barOf z M) q₁)
    (hpgl₂ : InducedPGL2 L₂ (barOf z M) q₂)
    (hn₁ : toBar z ⟨u, hMC huM⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hn₂ : toBar z ⟨u, hMC huM⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) :
    Stage1.Main.actOnK L₁ (toBar z ⟨u, hMC huM⟩) hn₁ ≠ 1 ∧
      Stage1.Main.actOnK L₂ (toBar z ⟨u, hMC huM⟩) hn₂ ≠ 1 :=
  ⟨fun h => false_of_centralizes_of_index_two hp hRL hMC hidx huM huR hpgl₁
      (actOnK_eq_one_imp hn₁ h),
   fun h => false_of_centralizes_of_index_two hp.symm hRL hMC hidx huM huR hpgl₂
      (actOnK_eq_one_imp hn₂ h)⟩

end PGLCase

section L4

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ} {ε : Bool}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

omit [Finite G] in
theorem mem_S1_of_normalizes (hp : PairShape z q q L₁ L₂) {u : G} (huS : u ∈ S) (hu : u ∈ Cen z)
    (hn₁ : toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hn₂ : toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) : u ∈ S1 S z := by
  refine Subgroup.mem_inf.mpr ⟨huS, ⟨⟨u, hu⟩, ?_, rfl⟩⟩
  simp only [SetLike.mem_coe, Subgroup.mem_iInf, Subgroup.mem_comap]
  intro K hK
  have hKmem : K ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := hK.1
  rw [hp.comps] at hKmem
  rcases hKmem with rfl | rfl
  · exact hn₁
  · exact hn₂

omit [Finite G] in
theorem S1_le_cen (S : Subgroup G) (z : G) : S1 S z ≤ Cen z := by
  rintro x ⟨hxS, ⟨c, -, rfl⟩⟩
  exact c.2

omit [Finite G] in
theorem normalizes_of_mem_S1 (hp : PairShape z q q L₁ L₂) {u : G} (hu1 : u ∈ S1 S z)
    (hu : u ∈ Cen z) :
    toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) ∧
      toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z)) := by
  obtain ⟨c, hc, hcu⟩ := (Subgroup.mem_inf.mp hu1).2
  have hcu' : c = ⟨u, hu⟩ := Subtype.ext hcu
  rw [hcu'] at hc
  simp only [SetLike.mem_coe, Subgroup.mem_iInf, Subgroup.mem_comap] at hc
  have hL₁ : L₁ ≤ LBar z := hp.prod.1 ▸ le_sup_left
  have hL₂ : L₂ ≤ LBar z := hp.prod.1 ▸ le_sup_right
  exact ⟨hc L₁ ⟨hp.isComponent₁, hL₁⟩, hc L₂ ⟨hp.isComponent₂, hL₂⟩⟩

theorem nonswap_nontriv_l4 (hp : Stage1L4 G z S ε q L₁ L₂) (hz2 : orderOf z = 2) {u : G}
    (huS : u ∈ S) (hu : u ∈ Cen z) (hu2 : u * u = 1) (hu1 : u ∉ zpowers z)
    (hn₁ : toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hn₂ : toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) :
    Stage1.Main.actOnK L₁ (toBar z ⟨u, hu⟩) hn₁ ≠ 1 ∧
      Stage1.Main.actOnK L₂ (toBar z ⟨u, hu⟩) hn₂ ≠ 1 := by
  have hpair := PairShape.of_pair hp.pair
  by_cases huR : u ∈ RC S z
  · exact actOnK_ne_one_of_mem_LBar hpair hz2 hu hu2 hu1 (toBar_mem_LBar huR.2) hn₁ hn₂
  · have huS1 : u ∈ S1 S z := mem_S1_of_normalizes hpair huS hu hn₁ hn₂
    rcases hp.fusion with ⟨-, hone⟩ | ⟨-, x, -, -⟩
    · exact absurd (hp.noDiag hone u huS1 hu2) huR
    · have hRM : RC S z ≤ S1 S z := by
        intro r hr
        have hLB := toBar_mem_LBar (z := z) hr.2
        exact mem_S1_of_normalizes hpair hr.1 (LC_le_cen z hr.2)
          (normalizes_of_mem_LBar hpair hLB).1 (normalizes_of_mem_LBar hpair hLB).2
      have hMS : S1 S z ≤ S := inf_le_left
      have hsw : ∃ s ∈ S, s ∉ S1 S z := by
        obtain ⟨s, hsS, hsw⟩ := hp.pair.swap
        refine ⟨s, hsS, fun hs1 => ?_⟩
        obtain ⟨hs, -, -⟩ := id hsw
        exact not_mem_normalizer_of_swaps hp.pair.ne hs hsw (normalizes_of_mem_S1 hpair hs1 hs).1
      have hidx : (RC S z).relIndex (S1 S z) ≤ 2 := by
        have h1 := Subgroup.relIndex_mul_relIndex (RC S z) (S1 S z) S hRM hMS
        have hne : (S1 S z).relIndex S ≠ 1 := by
          intro h
          obtain ⟨s, hsS, hs⟩ := hsw
          exact hs (Subgroup.relIndex_eq_one.mp h hsS)
        have h0 : (S1 S z).relIndex S ≠ 0 :=
          Subgroup.FiniteIndex.index_ne_zero (H := (S1 S z).subgroupOf S)
        have h2 : 2 ≤ (S1 S z).relIndex S := by omega
        have h4 := hp.index_le
        nlinarith
      exact actOnK_ne_one_of_index_two hpair (inf_le_right) (S1_le_cen S z) hidx huS1 huR
        hp.pgl.1 hp.pgl.2 hn₁ hn₂

end L4

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
