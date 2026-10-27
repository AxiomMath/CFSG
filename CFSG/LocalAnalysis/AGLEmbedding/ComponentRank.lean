module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def StmtComponentRank : Prop :=
  ∀ {X : Type} [Group X] [Finite X] {q : ℕ}, q.Prime → ∀ {ι : Type} [Finite ι]
    (L : ι → Subgroup X), (∀ i, IsComponentOf (L i) ⊤) → Function.Injective L →
    ∀ (A : Subgroup X) (y : ι → X), (∀ i, y i ∈ A) → (∀ i, y i ∈ L i) →
      (∀ i, IsPGroup q (Subgroup.zpowers (y i))) → (∀ i, ∃ l ∈ L i, y i * l ≠ l * y i) →
      Nat.card ι ≤ Open.pRank q A

@[expose] def StmtBarPRankLift : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {q : ℕ}, q.Prime → q ≠ 2 → ∀ M A : Subgroup G, A ≤ M →
    Open.pRank q (barM M A) ≤ Open.pRank q A

section Core

variable {G : Type*} [Group G] [Finite G]

theorem le_pRank_of_pow_mem {q : ℕ} (hq : q.Prime) (B C : Subgroup G)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hpow : ∀ b ∈ B, b ^ q ∈ C) {k : ℕ}
    (hk : q ^ k ≤ (C.subgroupOf B).index) : k ≤ Open.pRank q B := by
  have : Fact q.Prime := ⟨hq⟩
  let φ : B →* B :=
    { toFun := fun b => b ^ q
      map_one' := one_pow q
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_pow, Subgroup.coe_mul]
        exact (Commute.mul_pow (hcomm _ a.2 _ b.2) q)) }
  have hrange : φ.range ≤ C.subgroupOf B := by
    rintro _ ⟨b, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (by simpa [φ] using hpow b b.2)
  have hcard : Nat.card B = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hidx : Nat.card B = (C.subgroupOf B).index * Nat.card (C.subgroupOf B) :=
    (Subgroup.index_mul_card _).symm
  have hle : (C.subgroupOf B).index ≤ Nat.card φ.ker := by
    have h1 : Nat.card φ.range ≤ Nat.card (C.subgroupOf B) := Subgroup.card_le_of_le hrange
    have h2 : 0 < Nat.card (C.subgroupOf B) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card B < (C.subgroupOf B).index * Nat.card (C.subgroupOf B) := by
      rw [hcard]
      calc Nat.card φ.ker * Nat.card φ.range
          ≤ Nat.card φ.ker * Nat.card (C.subgroupOf B) := Nat.mul_le_mul_left _ h1
        _ < (C.subgroupOf B).index * Nat.card (C.subgroupOf B) :=
          Nat.mul_lt_mul_of_pos_right hlt h2
    omega
  set E : Subgroup G := φ.ker.map B.subtype with hE
  have hEel : IsElemAbelian q E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a', -, rfl⟩⟩ := a
      obtain ⟨_, ⟨b', -, rfl⟩⟩ := b
      exact hcomm _ a'.2 _ b'.2
    · rintro _ ⟨b, hb, rfl⟩
      have : φ b = 1 := hb
      simpa [φ] using congrArg Subtype.val this
  have hEcard : Nat.card E = Nat.card φ.ker :=
    Subgroup.card_map_of_injective B.subtype_injective
  have hEp : IsPGroup q E := fun g => ⟨1, Subtype.ext (by simpa using hEel.2 g g.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hEp
  have hkm : k ≤ m := by
    have : q ^ k ≤ q ^ m := by
      rw [← hm, hEcard]
      exact hk.trans hle
    exact (Nat.pow_le_pow_iff_right hq.one_lt).mp this
  exact hkm.trans (le_csSup (PreuniquenessRankFour.Helpers.pRank_bddAbove q hq B)
    ⟨E, Subgroup.map_subtype_le _, hEel, hm⟩)

end Core

section Components

variable {G : Type*} [Group G]

theorem exists_pow_not_mem_centralizer {q : ℕ} {y : G} (hy : IsPGroup q (Subgroup.zpowers y))
    {L : Subgroup G} (hyL : y ∉ Subgroup.centralizer (L : Set G)) :
    ∃ e : ℕ, y ^ q ^ e ∉ Subgroup.centralizer (L : Set G) ∧
      (y ^ q ^ e) ^ q ∈ Subgroup.centralizer (L : Set G) := by
  classical
  have hex : ∃ N : ℕ, y ^ q ^ N ∈ Subgroup.centralizer (L : Set G) := by
    obtain ⟨N, hN⟩ := hy ⟨y, Subgroup.mem_zpowers y⟩
    refine ⟨N, ?_⟩
    have : y ^ q ^ N = 1 := by simpa using congrArg Subtype.val hN
    rw [this]
    exact Subgroup.one_mem _
  set N₀ := Nat.find hex with hN₀
  have hN₀0 : N₀ ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hN₀, h0, pow_zero, pow_one] at this
    exact hyL this
  refine ⟨N₀ - 1, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hN₀0)]
  exact Nat.find_spec hex

end Components

section ComponentRank

variable {X : Type} [Group X] [Finite X]

open scoped IsMulCommutative

theorem le_pRank_of_components {q : ℕ} (hq : q.Prime) {ι : Type} [Finite ι]
    (L : ι → Subgroup X) (hL : ∀ i, IsComponentOf (L i) ⊤) (hinj : Function.Injective L)
    (A : Subgroup X) (y : ι → X) (hyA : ∀ i, y i ∈ A) (hyL : ∀ i, y i ∈ L i)
    (hyq : ∀ i, IsPGroup q (Subgroup.zpowers (y i))) (hyZ : ∀ i, ∃ l ∈ L i, y i * l ≠ l * y i) :
    Nat.card ι ≤ Open.pRank q A := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hcommL : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ z ∈ L j, x * z = z * x := by
    intro i j hij x hx z hz
    have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hL i) (hL j)
      (fun h => hij (hinj h))
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h hx
    exact (Subgroup.mem_centralizer_iff.mp hle z hz).symm
  have hnot : ∀ i, y i ∉ Subgroup.centralizer (L i : Set X) := by
    intro i hmem
    obtain ⟨l, hl, hne⟩ := hyZ i
    exact hne (Subgroup.mem_centralizer_iff.mp hmem l hl).symm
  choose e he using fun i => exists_pow_not_mem_centralizer (hyq i) (hnot i)
  set a : ι → X := fun i => y i ^ q ^ e i with ha
  have haA : ∀ i, a i ∈ A := fun i => A.pow_mem (hyA i) _
  have haL : ∀ i, a i ∈ L i := fun i => (L i).pow_mem (hyL i) _
  have hacomm : ∀ i j, a i * a j = a j * a i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · exact hcommL i j hij _ (haL i) _ (haL j)
  set B : Subgroup X := Subgroup.closure (Set.range a) with hB
  have hpair : (Set.range a).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact hacomm i j
  have : IsMulCommutative B := Subgroup.isMulCommutative_closure hpair
  let _ : CommGroup B := inferInstance
  have hcommB : ∀ x ∈ B, ∀ z ∈ B, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : B) ⟨z, hz⟩)
  have hBA : B ≤ A := (Subgroup.closure_le A).mpr (by rintro _ ⟨i, rfl⟩; exact haA i)
  set C : Subgroup X := ⨅ i, Subgroup.centralizer (L i : Set X) with hC
  have haC : ∀ i, a i ^ q ∈ C := by
    intro i
    refine Subgroup.mem_iInf.mpr fun j => ?_
    by_cases hij : i = j
    · subst hij
      exact (he i).2
    · refine Subgroup.pow_mem _ ?_ q
      exact Subgroup.mem_centralizer_iff.mpr fun z hz => (hcommL i j hij _ (haL i) z hz).symm
  have hpow : ∀ b ∈ B, b ^ q ∈ C := by
    intro b hb
    induction hb using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact haC i
    | one => simp
    | mul x z hx hz ihx ihz =>
      rw [Commute.mul_pow (hcommB x hx z hz)]
      exact C.mul_mem ihx ihz
    | inv x hx ihx =>
      rw [inv_pow]
      exact C.inv_mem ihx
  have hk : q ^ Nat.card ι ≤ (C.subgroupOf B).index := by
    let g : ι → B := fun i => ⟨a i, Subgroup.subset_closure ⟨i, rfl⟩⟩
    let f : (ι → Fin q) → B ⧸ C.subgroupOf B :=
      fun c => (QuotientGroup.mk (∏ i, g i ^ (c i : ℕ)) : B ⧸ C.subgroupOf B)
    have hf : Function.Injective f := by
      intro c c' hcc'
      have hmem := QuotientGroup.eq.mp hcc'
      set d : ι → ℤ := fun i => (c' i : ℤ) - (c i : ℤ) with hd
      have hprod : (∏ i, g i ^ (c i : ℕ))⁻¹ * ∏ i, g i ^ (c' i : ℕ) = ∏ i, g i ^ d i := by
        rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hd, zpow_sub, zpow_natCast, zpow_natCast, mul_comm]
      rw [hprod] at hmem
      funext j
      have hwC : ((∏ i, g i ^ d i : B) : X) ∈ Subgroup.centralizer (L j : Set X) :=
        (Subgroup.mem_iInf.mp (Subgroup.mem_subgroupOf.mp hmem)) j
      rw [← Finset.mul_prod_erase Finset.univ (fun i => g i ^ d i) (Finset.mem_univ j),
        Subgroup.coe_mul] at hwC
      have hrest : ((∏ i ∈ Finset.univ.erase j, g i ^ d i : B) : X) ∈
          Subgroup.centralizer (L j : Set X) := by
        refine Finset.prod_induction _ (fun b : B => (b : X) ∈ Subgroup.centralizer (L j : Set X))
          (fun b b' hb hb' => by rw [Subgroup.coe_mul]; exact Subgroup.mul_mem _ hb hb')
          (by simp) fun i hi => ?_
        rw [Subgroup.coe_zpow]
        refine Subgroup.zpow_mem _ ?_ _
        exact Subgroup.mem_centralizer_iff.mpr fun z hz =>
          (hcommL i j (Finset.ne_of_mem_erase hi) _ (haL i) z hz).symm
      have hjC : a j ^ d j ∈ Subgroup.centralizer (L j : Set X) := by
        have := (Subgroup.mul_mem_cancel_right _ hrest).mp hwC
        rwa [Subgroup.coe_zpow] at this
      have hdvd : (q : ℤ) ∣ d j := by
        by_contra hnd
        have hcop : IsCoprime (d j) (q : ℤ) := by
          rw [Int.isCoprime_iff_gcd_eq_one]
          show Nat.gcd (d j).natAbs (q : ℤ).natAbs = 1
          rw [Int.natAbs_natCast]
          exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr
            (fun h => hnd (Int.natCast_dvd.mpr h)))
        obtain ⟨u, v, huv⟩ := hcop
        have haj : a j ∈ Subgroup.centralizer (L j : Set X) := by
          have hq' : a j ^ q ∈ Subgroup.centralizer (L j : Set X) := (he j).2
          have h1 : a j = (a j ^ d j) ^ u * ((a j ^ q) ^ v) := by
            rw [← zpow_mul, ← zpow_natCast (a j) q, ← zpow_mul, ← zpow_add]
            conv_lhs => rw [← zpow_one (a j)]
            congr 1
            linarith
          rw [h1]
          exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hjC u) (Subgroup.zpow_mem _ hq' v)
        exact (he j).1 haj
      have hd0 : d j = 0 := by
        refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
        have h1 := (c j).isLt
        have h2 := (c' j).isLt
        rw [abs_lt]
        simp only [hd]
        constructor <;> omega
      have : ((c j : ℕ) : ℤ) = ((c' j : ℕ) : ℤ) := by
        have h0 := hd0
        simp only [hd] at h0
        omega
      exact Fin.ext (by exact_mod_cast this)
    have hcard : Nat.card (ι → Fin q) = q ^ Nat.card ι := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin q), Fintype.card_fin]
    rw [← hcard]
    exact Nat.card_le_card_of_injective f hf
  exact (le_pRank_of_pow_mem hq B C hcommB hpow hk).trans
    (PreuniquenessRankFour.Helpers.pRank_mono q hq hBA)

end ComponentRank

section Lift

variable {G : Type} [Group G] [Finite G]

theorem pRank_barM_le {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (M A : Subgroup G) (hAM : A ≤ M) :
    Open.pRank q (barM M A) ≤ Open.pRank q A := by
  have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  have hO : q.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  rw [barM, pRank_map_mk_eq_pRank_map_subtype hq _ hO, Subgroup.map_subgroupOf_eq_of_le hAM]

end Lift

theorem stmtComponentRank : StmtComponentRank := by
  intro X _ _ q hq ι _ L hL hinj A y hyA hyL hyq hyZ
  exact le_pRank_of_components hq L hL hinj A y hyA hyL hyq hyZ

theorem stmtBarPRankLift : StmtBarPRankLift :=
  fun hq hq2 M A hAM => pRank_barM_le hq hq2 M A hAM

end CFSG.AGLEmbedding
