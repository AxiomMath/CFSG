module

public import CFSG.GH74.Generic.BProg.B2.Prop111Normal
public import CFSG.GH74.Generic.BProg.B2.U0Gen
public import CFSG.GH74.Generic.BProg.B1.Lift0
public import CFSG.GH74.Generic.BProg.B2.Prop111Cover

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped Pointwise commutatorElement

namespace Prop111

open CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.L5U5

theorem exists_complement_zpowers {G : Type} [Group G] {A : Subgroup G}
    (hA : CFSG.IsElementaryAbelian 2 ↥A) {x : G} (hxA : x ∈ A) (hx2 : orderOf x = 2) :
    ∃ A₀ : Subgroup G, A₀ ≤ A ∧ A₀ ⊓ zpowers x = ⊥ ∧ Nat.card ↥A₀ * 2 = Nat.card ↥A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x' : ↥A := ⟨x, hxA⟩ with hx'
  have hcomm : ∀ a b : ↥A, a * b = b * a := fun a b => hA.toIsMulCommutative.is_comm.comm a b
  obtain ⟨C, hC⟩ := CFSG.IsElementaryAbelian.exists_isCompl 2 ↥A (zpowers x')
  refine ⟨C.map A.subtype, Subgroup.map_subtype_le C, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨⟨c, hc, rfl⟩, hgx⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hgx
    have hcx : c ∈ zpowers x' := ⟨j, Subtype.ext (by simpa [hx'] using hj)⟩
    have h1 : c ∈ zpowers x' ⊓ C := ⟨hcx, hc⟩
    rw [hC.inf_eq_bot, Subgroup.mem_bot] at h1
    rw [h1]
    exact Subgroup.one_mem _
  · have hdisj : Disjoint (zpowers x') C := hC.disjoint
    have hnorm : zpowers x' ≤ normalizer (C : Set ↥A) := by
      intro h _
      rw [Subgroup.mem_normalizer_iff]
      intro c
      rw [show h * c * h⁻¹ = c by rw [hcomm h c]; group]
    have hmul : ((zpowers x' : Subgroup ↥A) : Set ↥A) * (C : Set ↥A) = Set.univ := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm, hC.sup_eq_top]
      rfl
    have hcompl : Subgroup.IsComplement' (zpowers x') C :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
    have hcard := hcompl.card_mul_card
    have hz : Nat.card ↥(zpowers x') = 2 := by
      rw [Nat.card_zpowers, hx', Subgroup.orderOf_mk, hx2]
    rw [hz] at hcard
    rw [Subgroup.card_map_of_injective A.subtype_injective, mul_comm]
    exact hcard

section Main

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

omit [Finite G] in
theorem barMk_commute_iff {Cy : Subgroup G} {a b : G} (ha : a ∈ Cy) (hb : b ∈ Cy) :
    TwoThin.barMk ↥Cy ⟨a, ha⟩ * TwoThin.barMk ↥Cy ⟨b, hb⟩ =
      TwoThin.barMk ↥Cy ⟨b, hb⟩ * TwoThin.barMk ↥Cy ⟨a, ha⟩ ↔ ⁅a, b⁆ ∈ pPrimeCoreOf 2 Cy := by
  constructor
  · intro h
    have h1 : TwoThin.barMk ↥Cy ⁅(⟨a, ha⟩ : ↥Cy), ⟨b, hb⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h
    exact ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  · rintro ⟨n, hn, hnab⟩
    have hn' : ⁅(⟨a, ha⟩ : ↥Cy), ⟨b, hb⟩⁆ = n := Subtype.ext hnab.symm
    have h1 : TwoThin.barMk ↥Cy ⁅(⟨a, ha⟩ : ↥Cy), ⟨b, hb⟩⁆ = 1 := by
      rw [hn']
      exact (QuotientGroup.eq_one_iff _).2 hn
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

@[expose] def wSub (y : G) (H : Subgroup G) : Subgroup G :=
  ((centralizer ((PumpCalc.bar y H : Subgroup (TwoThin.barQ ↥(centralizer ({y} : Set G)))) :
    Set (TwoThin.barQ ↥(centralizer ({y} : Set G))))).comap
      (TwoThin.barMk ↥(centralizer ({y} : Set G)))).map (centralizer ({y} : Set G)).subtype

omit [Finite G] in
theorem wSub_le (y : G) (H : Subgroup G) : wSub y H ≤ centralizer ({y} : Set G) := by
  rintro _ ⟨c, -, rfl⟩
  exact c.2

omit [Finite G] in
theorem mem_wSub_iff {y : G} {H : Subgroup G} (hHC : H ≤ centralizer ({y} : Set G)) {w : G}
    (hw : w ∈ centralizer ({y} : Set G)) :
    w ∈ wSub y H ↔ ∀ h ∈ H, ⁅h, w⁆ ∈ pPrimeCoreOf 2 (centralizer ({y} : Set G)) := by
  constructor
  · rintro ⟨c, hc, rfl⟩ h hh
    have hc' : TwoThin.barMk ↥(centralizer ({y} : Set G)) c ∈
        centralizer ((PumpCalc.bar y H : Subgroup _) : Set _) := hc
    have := Subgroup.mem_centralizer_iff.1 hc' (TwoThin.barMk ↥(centralizer ({y} : Set G)) ⟨h, hHC hh⟩)
      ⟨⟨h, hHC hh⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
    exact (barMk_commute_iff (hHC hh) c.2).1 this
  · intro hcomm
    refine ⟨⟨w, hw⟩, ?_, rfl⟩
    show TwoThin.barMk ↥(centralizer ({y} : Set G)) ⟨w, hw⟩ ∈ centralizer ((PumpCalc.bar y H : Subgroup _) : Set _)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨m, hm, rfl⟩
    exact ((barMk_commute_iff m.2 hw).2 (hcomm m (Subgroup.mem_subgroupOf.mp hm)))

omit [Finite G] in
theorem pPrimeCoreOf_le_wSub (y : G) (H : Subgroup G) :
    pPrimeCoreOf 2 (centralizer ({y} : Set G)) ≤ wSub y H := by
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨n, ?_, rfl⟩
  show TwoThin.barMk ↥(centralizer ({y} : Set G)) n ∈ centralizer ((PumpCalc.bar y H : Subgroup _) : Set _)
  have : TwoThin.barMk ↥(centralizer ({y} : Set G)) n = 1 := (QuotientGroup.eq_one_iff _).2 hn
  rw [this]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem conj_mem_wSub {y : G} {H : Subgroup G} (hN : (PumpCalc.bar y H).Normal)
    {c : G} (hc : c ∈ centralizer ({y} : Set G)) {w : G} (hw : w ∈ wSub y H) :
    c * w * c⁻¹ ∈ wSub y H := by
  obtain ⟨d, hd, rfl⟩ := hw
  refine ⟨⟨c, hc⟩ * d * ⟨c, hc⟩⁻¹, ?_, by simp⟩
  show TwoThin.barMk ↥(centralizer ({y} : Set G)) (⟨c, hc⟩ * d * ⟨c, hc⟩⁻¹) ∈
    centralizer ((PumpCalc.bar y H : Subgroup _) : Set _)
  have hd' : TwoThin.barMk ↥(centralizer ({y} : Set G)) d ∈ centralizer ((PumpCalc.bar y H : Subgroup _) : Set _) := hd
  rw [Subgroup.mem_centralizer_iff] at hd' ⊢
  intro k hk
  rw [map_mul, map_mul, map_inv]
  set cb := TwoThin.barMk ↥(centralizer ({y} : Set G)) ⟨c, hc⟩
  have hk' : cb⁻¹ * k * cb ∈ PumpCalc.bar y H := by
    have := hN.conj_mem k hk cb⁻¹
    simpa using this
  have := hd' _ hk'
  calc k * (cb * TwoThin.barMk ↥(centralizer ({y} : Set G)) d * cb⁻¹)
      = cb * ((cb⁻¹ * k * cb) * TwoThin.barMk ↥(centralizer ({y} : Set G)) d) * cb⁻¹ := by group
    _ = cb * (TwoThin.barMk ↥(centralizer ({y} : Set G)) d * (cb⁻¹ * k * cb)) * cb⁻¹ := by rw [this]
    _ = cb * TwoThin.barMk ↥(centralizer ({y} : Set G)) d * cb⁻¹ * k := by group

theorem exists_four_group (hZ : CenterlessS345) (hs : Stage2Setup G x K A M P Q) {y : G} (hyQ : y ∈ Q)
    {Hy Λ : Subgroup G} (hH : IsPCompIn 2 (centralizer ({y} : Set G)) Hy) (hΛ : PumpCalc.IsLam x y K Λ)
    (hΛHy : Λ ≤ Hy)
    (hiso : Nonempty ((↥Hy ⧸ pPrimeCore 2 ↥Hy) ≃* (↥K ⧸ pPrimeCore 2 ↥K))) :
    ∃ E : Subgroup G, E ≤ A ⊓ K ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ 4 ≤ Nat.card ↥E ∧
      ∀ e ∈ E, (∀ h ∈ Hy, ⁅h, e⁆ ∈ pPrimeCoreOf 2 (centralizer ({y} : Set G))) → e = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cy : Subgroup G := centralizer ({y} : Set G) with hCy
  obtain ⟨e₁⟩ := hiso
  obtain ⟨e₂⟩ := PumpCalc.kBar_equiv_bar hH
  let ε : ↥(PumpCalc.bar y Hy) ≃* (↥K ⧸ pPrimeCore 2 ↥K) := e₂.symm.trans e₁
  have hEHy : A ⊓ K ≤ Hy := Prop111Cover.inf_K_le_pumpup hs hyQ hΛ hΛHy
  have hAC : A ≤ Cy := Prop111Cover.A_le_centralizer hs hyQ
  obtain ⟨-, hAel, hAcard, hcase⟩ := hs.src
  have hbar1 : ∀ e ∈ A, ∀ heC : e ∈ Cy, TwoThin.barMk ↥Cy ⟨e, heC⟩ = 1 → e = 1 := by
    intro e he heC h
    have hmem : (⟨e, heC⟩ : ↥Cy) ∈ pPrimeCore 2 ↥Cy := (QuotientGroup.eq_one_iff _).1 h
    obtain ⟨n, hn⟩ := hs.sylowP.isPGroup (⟨e, hs.A_le he⟩ : ↥P)
    have hn' : (⟨e, heC⟩ : ↥Cy) ^ (2 ^ n) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
    exact congrArg Subtype.val (Prop111Normal.eq_one_of_mem_pPrimeCore_of_two_pow hmem hn')
  have hcentral : ∀ e, ∀ he : e ∈ A ⊓ K, (∀ h ∈ Hy, ⁅h, e⁆ ∈ pPrimeCoreOf 2 Cy) →
      ∃ ze : ↥(PumpCalc.bar y Hy), (ze : TwoThin.barQ ↥Cy) = TwoThin.barMk ↥Cy ⟨e, hAC he.1⟩ ∧
        ze ∈ Subgroup.center ↥(PumpCalc.bar y Hy) := by
    intro e he hcomm
    have hmem : TwoThin.barMk ↥Cy ⟨e, hAC he.1⟩ ∈ PumpCalc.bar y Hy :=
      ⟨⟨e, hAC he.1⟩, Subgroup.mem_subgroupOf.mpr (hEHy he), rfl⟩
    refine ⟨⟨_, hmem⟩, rfl, ?_⟩
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, m, hm, rfl⟩
    apply Subtype.ext
    exact (barMk_commute_iff m.2 (hAC he.1)).2 (hcomm m (Subgroup.mem_subgroupOf.mp hm))
  rcases hcase with ⟨hAK, hS1⟩ | ⟨E, hEK, hAE, -, hEel, hE4, hshape⟩
  ·
    have hS1' : IsSL4Model ↥(PumpCalc.bar y Hy) := IsSL4Model.of_mulEquiv hS1 ε.symm
    obtain ⟨z, -, -, hcenter, -, -⟩ := hS1'.exists_center_q8q8
    have hAK' : ∀ a ∈ A, a ∈ A ⊓ K := fun a ha => ⟨ha, hAK ha⟩
    have key : ∀ a ∈ A, (∀ h ∈ Hy, ⁅h, a⁆ ∈ pPrimeCoreOf 2 Cy) → a ≠ 1 →
        ∀ b ∈ A, (∀ h ∈ Hy, ⁅h, b⁆ ∈ pPrimeCoreOf 2 Cy) → b ≠ 1 → a = b := by
      intro a ha hca ha1 b hb hcb hb1
      obtain ⟨za, hza, hzac⟩ := hcentral a (hAK' a ha) hca
      obtain ⟨zb, hzb, hzbc⟩ := hcentral b (hAK' b hb) hcb
      have hza1 : za ≠ 1 := fun h => ha1 (hbar1 a ha (hAC ha) (by rw [← hza, h]; rfl))
      have hzb1 : zb ≠ 1 := fun h => hb1 (hbar1 b hb (hAC hb) (by rw [← hzb, h]; rfl))
      have hza2 : za = z := (hcenter za).1 hzac |>.resolve_left hza1
      have hzb2 : zb = z := (hcenter zb).1 hzbc |>.resolve_left hzb1
      have hab : TwoThin.barMk ↥Cy ⟨a, hAC ha⟩ = TwoThin.barMk ↥Cy ⟨b, hAC hb⟩ := by
        rw [← hza, ← hzb, hza2, hzb2]
      have : a⁻¹ * b = 1 := by
        refine hbar1 _ (mul_mem (inv_mem ha) hb) (mul_mem (inv_mem (hAC ha)) (hAC hb)) ?_
        have h2 : (⟨a⁻¹ * b, mul_mem (inv_mem (hAC ha)) (hAC hb)⟩ : ↥Cy) = ⟨a, hAC ha⟩⁻¹ * ⟨b, hAC hb⟩ := rfl
        rw [h2, map_mul, map_inv, hab, inv_mul_cancel]
      exact inv_mul_eq_one.1 this
    by_cases hex : ∃ a₀ ∈ A, (∀ h ∈ Hy, ⁅h, a₀⁆ ∈ pPrimeCoreOf 2 Cy) ∧ a₀ ≠ 1
    · obtain ⟨a₀, ha₀, hca₀, ha₀1⟩ := hex
      have hsq : a₀ ^ 2 = 1 := by
        have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 ↥A)
          ⟨a₀, ha₀⟩
        simpa using congrArg Subtype.val this
      have ha₀2 : orderOf a₀ = 2 := orderOf_eq_prime hsq ha₀1
      obtain ⟨E₀, hE₀A, hE₀inf, hE₀card⟩ := exists_complement_zpowers hAel ha₀ ha₀2
      refine ⟨E₀, le_inf hE₀A (hE₀A.trans hAK), Th2Sig6.isElementaryAbelian_of_le hAel hE₀A,
        by omega, fun e he hce => ?_⟩
      by_contra hne
      have hea : e = a₀ := key e (hE₀A he) hce hne a₀ ha₀ hca₀ ha₀1
      have h1 : a₀ ∈ E₀ ⊓ zpowers a₀ := ⟨hea ▸ he, Subgroup.mem_zpowers a₀⟩
      rw [hE₀inf, Subgroup.mem_bot] at h1
      exact ha₀1 h1
    · push Not at hex
      exact ⟨A, le_inf le_rfl hAK, hAel, by omega, fun e he hce => hex e he hce⟩
  ·
    have hEA : E ≤ A := hAE ▸ le_sup_left
    refine ⟨E, le_inf hEA hEK, hEel, hE4.ge, fun e he hce => ?_⟩
    obtain ⟨ze, hze, hzc⟩ := hcentral e ⟨hEA he, hEK he⟩ hce
    have hcentK := hZ _ (TwoThin.isQuasisimple_hat hs.pair.1.1.1.2.2) hshape
    have hze1 : ze = 1 := by
      have h1 : ε ze = 1 := by
        refine hcentK _ fun g => ?_
        have h2 := congrArg ε (Subgroup.mem_center_iff.1 hzc (ε.symm g))
        simpa [map_mul] using h2
      exact ε.map_eq_one_iff.1 h1
    exact hbar1 e (hEA he) (hAC (hEA he)) (by rw [← hze, hze1]; rfl)

theorem normalizer_inf_le_M (hs : Stage2Setup G x K A M P Q) :
    normalizer ((A ⊓ K : Subgroup G) : Set G) ≤ M := by
  obtain ⟨-, hAel, hAcard, -⟩ := hs.src
  have hr3 : pRank 2 ↥A = 3 := pRank_eq_of_card_eq_pow one_lt_two (by simpa using hAcard)
  have hAe3 : IsE 3 ⊤ A := ⟨le_top, hAel, hr3.ge⟩
  have hbal := hs.reg.1
  have hE : IsE 2 A (A ⊓ K) := isE_inf_K hs
  have h2 : normalizer ((A ⊓ K : Subgroup G) : Set G) ≤ gammaK 2 A 2 :=
    le_iSup₂_of_le (A ⊓ K) inf_le_left (le_iSup_of_le hE.2.2 le_rfl)
  exact fun g hg => hs.le_M ((gammaK_le_normalizer_thetaHalf_one hAe3 hbal.1 hbal.2) (h2 hg))

theorem wSub_le_M (hs : Stage2Setup G x K A M P Q) {y : G} (hyQ : y ∈ Q) {Hy : Subgroup G}
    (hEH : A ⊓ K ≤ Hy)
    (hOM : pPrimeCoreOf 2 (centralizer ({y} : Set G)) ≤ M) : wSub y Hy ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cy : Subgroup G := centralizer ({y} : Set G) with hCy
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨-, hAel, -, -⟩ := hs.src
  have hEel : CFSG.IsElementaryAbelian 2 ↥(A ⊓ K) := Th2Sig6.isElementaryAbelian_of_le hAel inf_le_left
  have hAKC : A ⊓ K ≤ Cy := inf_le_left.trans (Prop111Cover.A_le_centralizer hs hyQ)
  set N : Subgroup ↥Cy := pPrimeCore 2 ↥Cy with hN
  have hNodd : Odd (Nat.card N) :=
    Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥Cy))
  have hEs : IsPGroup 2 ↥((A ⊓ K).subgroupOf Cy) := by
    have := hEel
    have : CFSG.IsElementaryAbelian 2 ↥((A ⊓ K).subgroupOf Cy) := IsElementaryAbelian.subgroupOf hAKC
    exact IsElementaryAbelian.isPGroup 2 _
  have hc' : TwoThin.barMk ↥Cy c ∈ centralizer ((PumpCalc.bar y Hy : Subgroup _) : Set _) := hc
  obtain ⟨g, hg, hgE⟩ := B1.centralizer_quotient_of_pGroup N hNodd hEs (c := QuotientGroup.mk c)
    (fun a ha => by
      have haH : (a : G) ∈ Hy := hEH (Subgroup.mem_subgroupOf.mp ha)
      exact Subgroup.mem_centralizer_iff.1 hc' (TwoThin.barMk ↥Cy a)
        ⟨a, Subgroup.mem_subgroupOf.mpr haH, rfl⟩)
  have hgM : (g : G) ∈ M := by
    refine normalizer_inf_le_M hs (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (hgE ⟨a, hAKC ha⟩ (Subgroup.mem_subgroupOf.mpr ha))
  have hcg : g⁻¹ * c ∈ N := QuotientGroup.eq.1 hg
  have hcM : ((g⁻¹ * c : ↥Cy) : G) ∈ M := hOM ⟨_, hcg, rfl⟩
  have : (c : G) = (g : G) * ((g⁻¹ * c : ↥Cy) : G) := by simp
  rw [Subgroup.coe_subtype, this]
  exact mul_mem hgM hcM

theorem pumpup_normal_data (hZ : CenterlessS345) (hs : Stage2Setup G x K A M P Q) {y : G} (hyQ : y ∈ Q)
    (hy : orderOf y = 2) :
    ∃ Hy Λ : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) Hy ∧ PumpCalc.IsLam x y K Λ ∧
      Λ ≤ K ⊓ Hy ∧ (∀ k ∈ Hy, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 Hy, k = l * o) ∧
      pPrimeCoreOf 2 Hy ≤ pPrimeCoreOf 2 (centralizer ({y} : Set G)) ∧ A ⊓ K ≤ Hy ∧
      (PumpCalc.bar y Hy).Normal := by
  obtain ⟨Hy, Λ, hH, hΛ, hΛle, hcov, hOle, hiso⟩ := Prop111Cover.pumpup_cover_data hs hyQ hy
  have hΛHy : Λ ≤ Hy := fun l hl => (hΛle hl).2
  have hEHy : A ⊓ K ≤ Hy := Prop111Cover.inf_K_le_pumpup hs hyQ hΛ hΛHy
  obtain ⟨E, hEA, hEel, hE4, hEZ⟩ := exists_four_group hZ hs hyQ hH hΛ hΛHy hiso
  exact ⟨Hy, Λ, hH, hΛ, hΛle, hcov, hOle, hEHy,
    Prop111Normal.bar_normal_of_elem hs.hyp.gen4 hy hH (hEA.trans hEHy) hEel hE4 hEZ⟩

theorem centralizer_le_M_of_mem_Q_of (hZ : CenterlessS345) (hs : Stage2Setup G x K A M P Q)
    (hKM : K ≤ M) (_hQM : Q ≤ M) (h2 : Stage2Concl2 M) {y : G} (hyQ : y ∈ Q) (hy : orderOf y = 2) :
    centralizer ({y} : Set G) ≤ M := by
  set Cy : Subgroup G := centralizer ({y} : Set G) with hCy
  have hA : InU0 M A := inU0_A hs
  have hAC : A ≤ Cy := Prop111Cover.A_le_centralizer hs hyQ
  have hOM : pPrimeCoreOf 2 Cy ≤ M := pPrimeCoreOf_le_of_inU0 hA hAC
  obtain ⟨Hy, Λ, hH, hΛ, hΛle, hcov, hOle, hEHy, hN⟩ := pumpup_normal_data hZ hs hyQ hy
  have hHyM : Hy ≤ M := fun h hh => by
    obtain ⟨l, hl, o, ho, rfl⟩ := hcov h hh
    exact mul_mem (hKM (hΛle hl).1) (hOM (hOle ho))
  have hconj := Prop111Normal.conj_mem_sup_of_bar_normal hH.1 hN
  have hWM : wSub y Hy ≤ M := wSub_le_M hs hyQ hEHy hOM
  have hxC : x ∈ Cy :=
    Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 (Prop111Cover.mem_centralizer_x_of_mem_Q hs hyQ)).symm
  have hxW : x ∈ wSub y Hy :=
    (mem_wSub_iff hH.1 hxC).2 (Prop111Cover.comm_pumpup_x hs hyQ hΛ hcov hOle)
  set Nstar : Subgroup G := Hy ⊔ wSub y Hy with hNstar
  have hNC : Nstar ≤ Cy := sup_le hH.1 (wSub_le y Hy)
  have hNM : Nstar ≤ M := sup_le hHyM hWM
  have hAsub : A ≤ (A ⊓ K) ⊔ zpowers x := by
    obtain ⟨-, -, -, hcase⟩ := hs.src
    rcases hcase with ⟨hAK, -⟩ | ⟨E, hEK, hAE, -, -, -, -⟩
    · exact fun a ha => Subgroup.mem_sup_left ⟨ha, hAK ha⟩
    · have hEA : E ≤ A := hAE ▸ le_sup_left
      calc A = E ⊔ zpowers x := hAE
        _ ≤ (A ⊓ K) ⊔ zpowers x := sup_le_sup_right (le_inf hEA hEK) _
  have hAN : A ≤ Nstar :=
    hAsub.trans (sup_le (hEHy.trans le_sup_left) (Subgroup.zpowers_le.2 (Subgroup.mem_sup_right hxW)))
  have hNorm : (Nstar.subgroupOf Cy).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hmap : Nstar.map (MulAut.conj (g : G)).toMonoidHom ≤ Nstar := by
      rw [hNstar, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨h, hh, rfl⟩
        have := hconj (g : G) g.2 h hh
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact sup_le_sup_left (pPrimeCoreOf_le_wSub y Hy) Hy this
      · rintro _ ⟨w, hw, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact Subgroup.mem_sup_right (conj_mem_wSub hN g.2 hw)
    have := hmap ⟨n, hn, rfl⟩
    simpa [MulAut.conj_apply] using this
  exact le_M_of_normal_of_inU0 h2 hA hNC hNorm hAN hNM

end Main

end Prop111

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

theorem centralizer_le_M_of_mem_Q
    (hs : Stage2Setup G x K A M P Q)
    (hKM : K ≤ M) (hQM : Q ≤ M) (h2 : Stage2Concl2 M) {y : G} (hyQ : y ∈ Q) (hy : orderOf y = 2) :
    centralizer ({y} : Set G) ≤ M :=
  Prop111.centralizer_le_M_of_mem_Q_of centerlessS345 hs hKM hQM h2 hyQ hy

theorem centralizer_x_le_M_of (hZ : CenterlessS345) (hs : Stage2Setup G x K A M P Q)
    (hKM : K ≤ M) (hQM : Q ≤ M) (h2 : Stage2Concl2 M) : centralizer ({x} : Set G) ≤ M :=
  Prop111.centralizer_le_M_of_mem_Q_of hZ hs hKM hQM h2 (x_mem_Q hs) hs.pair.1.1.1.1

end CFSG.GH74.Generic.BProg.B2
