module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269R2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TCount
public import CFSG.Fischer.Classification.PartIII.Symp.Gauss

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I269R

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.LieType.Universal.Spin
  CFSG.HardMathSupport.Curtis.Coordinator CFSG.LocalAnalysis.GLTheoremA.D4T CFSG.Open

theorem pow_apply_of_fixed {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {g : V ≃ₗ[ZMod 2] V} {v : V} (h : g v = v) (n : ℕ) : (g ^ n) v = v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, h]

theorem gauss_fixed {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {p : ℕ} {g : V ≃ₗ[ZMod 2] V} (hg : OddOrderIsometry Q p g) :
    ∃ m : ℕ, finrank (ZMod 2) (fixedSpace g) = 2 * m ∧
      (2 * ({v | Q v = 0} ∩ {v | g v = v}).ncard = 4 ^ m + 2 ^ m ∨
        2 * ({v | Q v = 0} ∩ {v | g v = v}).ncard = 4 ^ m - 2 ^ m) := by
  classical
  obtain ⟨m, hm⟩ := hg.even_finrank_fixed
  refine ⟨m, by omega, ?_⟩
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  set P : Submodule (ZMod 2) V := fixedSpace g with hP
  set Q' : QuadraticForm (ZMod 2) ↥P := Q.comp P.subtype with hQ'
  have hnd : ∀ x : ↥P, (∀ y : ↥P, QuadraticMap.polar Q' x y = 0) → x = 0 := fun x hx =>
    hg.polarBilin_fixed_nondegenerate.1 x fun w => by simpa using hx w
  have hPcard : Nat.card ↥P = 4 ^ m := by
    rw [card_submodule, show Nat.card (ZMod 2) = 2 by simp, hm, show m + m = 2 * m by omega, pow_mul]
    norm_num
  have hgauss := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic Q' hnd hPcard
  have hsplit : {x : ↥P | Q' x = 0}.ncard + {x : ↥P | Q' x = 1}.ncard = 4 ^ m := by
    have hc : {x : ↥P | Q' x = 0} = {x : ↥P | Q' x = 1}ᶜ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      have hz2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      rcases hz2 (Q' x) with h | h <;> simp [h]
    rw [hc, add_comm, Set.ncard_add_ncard_compl]
    exact hPcard
  have himg : ({v | Q v = 0} ∩ {v | g v = v}).ncard = {x : ↥P | Q' x = 0}.ncard := by
    rw [← Set.ncard_image_of_injective {x : ↥P | Q' x = 0} P.subtype_injective]
    congr 1
    ext v
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hv, hgv⟩
      exact ⟨⟨v, mem_fixedSpace.2 hgv⟩, by simpa [hQ'] using hv, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by simpa [hQ'] using hx, mem_fixedSpace.1 x.2⟩
  rw [himg]
  omega


theorem z15_arith (ma mb mc zE zY zC : ℕ)
    (hma : ma ≤ 3) (hmb : mb ≤ 3) (hmc : mc ≤ 3) (hca : mc ≤ ma) (hcb : mc ≤ mb)
    (hzE1 : 1 ≤ zE) (hzY1 : 1 ≤ zY) (hzC1 : 1 ≤ zC)
    (hY : (2 ^ (2 * mb)) % 5 = 1)
    (hC5 : (2 ^ (2 * ma)) % 5 = (2 ^ (2 * mc)) % 5)
    (hzE3 : zE % 3 = 1) (hzY5 : zY % 5 = 1) (hzC3 : zC % 3 = zY % 3) (hzC5 : zC % 5 = zE % 5)
    (gE : 2 * zE = 4 ^ ma + 2 ^ ma ∨ 2 * zE = 4 ^ ma - 2 ^ ma)
    (gY : 2 * zY = 4 ^ mb + 2 ^ mb ∨ 2 * zY = 4 ^ mb - 2 ^ mb)
    (gC : 2 * zC = 4 ^ mc + 2 ^ mc ∨ 2 * zC = 4 ^ mc - 2 ^ mc) :
    ma = 0 ∨ ma = 3 := by
  interval_cases ma <;> interval_cases mb <;> interval_cases mc <;> (try norm_num at hY hC5 gE gY gC)
  all_goals omega

theorem finrank_fixed_zero_or_six
    {e y : (Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)}
    (he : e ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 (ZMod 2)))
    (hy : y ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 (ZMod 2)))
    (hey : e * y = y * e) (he3 : e ^ 3 = 1) (hy5 : y ^ 5 = 1) (he1 : e ≠ 1) (hy1 : y ≠ 1) :
    finrank (ZMod 2) (fixedSpace e) = 0 ∨ finrank (ZMod 2) (fixedSpace e) = 6 := by
  classical
  have hK : Nat.card (ZMod 2) = 2 := by simp
  set V := Fin 4 ⊕ Fin 4 → ZMod 2 with hVdef
  set Q : QuadraticForm (ZMod 2) V := quadPlus 4 (ZMod 2) with hQdef
  haveI : Finite V := inferInstance
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    nondegenerate_polarBilin_quadPlus 4 (ZMod 2)
  have hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0 := fun v hv =>
    hQnd.1 v fun w => by simpa using hv w
  have hcast : ∀ n : ℕ, n % 2 = 1 → (n : ZMod 2) ≠ 0 := by
    intro n hn h0
    have : (n : ZMod 2) = 1 := by
      rw [← ZMod.natCast_mod, hn]; simp
    rw [this] at h0
    exact one_ne_zero h0
  have hcomm : Commute e y := hey
  have hoe : OddOrderIsometry Q 3 e := ⟨he, he3, hcast 3 (by norm_num), hreg⟩
  have hoy : OddOrderIsometry Q 5 y := ⟨hy, hy5, hcast 5 (by norm_num), hreg⟩
  have he15 : e ^ 15 = 1 := by rw [show (15 : ℕ) = 3 * 5 from rfl, pow_mul, he3, one_pow]
  have hy15 : y ^ 15 = 1 := by rw [show (15 : ℕ) = 5 * 3 from rfl, pow_mul, hy5, one_pow]
  have hoey : OddOrderIsometry Q 15 (e * y) :=
    ⟨Subgroup.mul_mem _ he hy, by rw [hcomm.mul_pow, he15, hy15, one_mul], hcast 15 (by norm_num),
      hreg⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdimV : finrank (ZMod 2) V = 8 := by
    show finrank (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) = 8
    simp
  have hVcard : Nat.card V = 2 ^ 8 := by
    show Nat.card (Fin 4 ⊕ Fin 4 → ZMod 2) = 2 ^ 8
    rw [Nat.card_fun, hK]
    simp
  have hFix : ∀ g : V ≃ₗ[ZMod 2] V, {v | g v = v} = (fixedSpace g : Set V) := fun g => by
    ext v
    exact (mem_fixedSpace (x := g)).symm
  have hncard_sub : ∀ W : Submodule (ZMod 2) V, (W : Set V).ncard = 2 ^ finrank (ZMod 2) W :=
    fun W => by
      rw [← Nat.card_coe_set_eq]
      exact (card_submodule W).trans (by rw [hK])
  have hiso : ∀ g : V ≃ₗ[ZMod 2] V, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q → ∀ v, Q (g v) = Q v :=
    fun g hg v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg v
  have hne_top : ∀ g : V ≃ₗ[ZMod 2] V, g ≠ 1 → finrank (ZMod 2) (fixedSpace g) < 8 := by
    intro g hg1
    by_contra hge
    push Not at hge
    apply hg1
    have htop : fixedSpace g = ⊤ := Submodule.eq_top_of_finrank_eq
      (le_antisymm (Submodule.finrank_le _) (by rw [hdimV]; exact hge))
    refine LinearEquiv.ext fun v => ?_
    exact mem_fixedSpace.1 (htop ▸ Submodule.mem_top)
  have he10 : e ^ 10 = e := by
    rw [show (10 : ℕ) = 3 * 3 + 1 from rfl, pow_succ, pow_mul, he3, one_pow, one_mul]
  have hy10 : y ^ 10 = 1 := by rw [show (10 : ℕ) = 5 * 2 from rfl, pow_mul, hy5, one_pow]
  have he6 : e ^ 6 = 1 := by rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, he3, one_pow]
  have hy6 : y ^ 6 = y := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, hy5, one_mul]
  have hFC : {v | (e * y) v = v} = {v | e v = v} ∩ {v | y v = v} := by
    ext v
    constructor
    · intro h
      have h1 : (e * y) ^ 10 = e := by rw [hcomm.mul_pow, he10, hy10, mul_one]
      have h2 : (e * y) ^ 6 = y := by rw [hcomm.mul_pow, he6, hy6, one_mul]
      have h3 := pow_apply_of_fixed (show (e * y) v = v from h) 10
      have h4 := pow_apply_of_fixed (show (e * y) v = v from h) 6
      rw [h1] at h3
      rw [h2] at h4
      exact ⟨h3, h4⟩
    · rintro ⟨h1, h2⟩
      show e (y v) = v
      rw [show y v = v from h2, show e v = v from h1]
  set Z : Set V := {v | Q v = 0} with hZ
  have hZcard : Z.ncard = 136 := by
    rw [← Nat.card_coe_set_eq]
    exact card_singular_quadPlus_four (K := ZMod 2) hK
  have hZinv : ∀ g : V ≃ₗ[ZMod 2] V, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q →
      ∀ v ∈ Z, g v ∈ Z := fun g hg v hv => by
    show Q (g v) = 0
    rw [hiso g hg v]
    exact hv
  have hcomm_apply : ∀ v, e (y v) = y (e v) := fun v => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hey
    exact this
  have hinvE : ∀ v ∈ {v | e v = v}, y v ∈ {v | e v = v} := by
    intro v hv
    show e (y v) = y v
    rw [hcomm_apply, show e v = v from hv]
  have hinvY : ∀ v ∈ {v | y v = v}, e v ∈ {v | y v = v} := by
    intro v hv
    show y (e v) = e v
    rw [← hcomm_apply, show y v = v from hv]
  have hZy : ∀ v ∈ Z ∩ {v | y v = v}, e v ∈ Z ∩ {v | y v = v} := fun v hv =>
    ⟨hZinv e he v hv.1, hinvY v hv.2⟩
  have hZe : ∀ v ∈ Z ∩ {v | e v = v}, y v ∈ Z ∩ {v | e v = v} := fun v hv =>
    ⟨hZinv y hy v hv.1, hinvE v hv.2⟩
  have hZC1 : (Z ∩ {v | y v = v}) ∩ {v | e v = v} = Z ∩ {v | (e * y) v = v} := by
    rw [hFC]
    ext v
    simp only [Set.mem_inter_iff]
    tauto
  have hZC2 : (Z ∩ {v | e v = v}) ∩ {v | y v = v} = Z ∩ {v | (e * y) v = v} := by
    rw [hFC]
    ext v
    simp only [Set.mem_inter_iff]
    tauto
  have hpos : ∀ T : Set V, (0 : V) ∈ T → 1 ≤ T.ncard := fun T h0 => by
    apply Nat.one_le_iff_ne_zero.2
    rw [Ne, Set.ncard_eq_zero (Set.toFinite _)]
    intro h
    rw [h] at h0
    exact h0
  have h0Z : (0 : V) ∈ Z := by show Q 0 = 0; simp
  obtain ⟨ma, hma, gE⟩ := gauss_fixed hoe
  obtain ⟨mb, hmb, gY⟩ := gauss_fixed hoy
  obtain ⟨mc, hmc, gC⟩ := gauss_fixed hoey
  rw [← hZ] at gE gY gC
  have hma : finrank (ZMod 2) (fixedSpace e) = 2 * ma := hma
  have hmb : finrank (ZMod 2) (fixedSpace y) = 2 * mb := hmb
  have hmc : finrank (ZMod 2) (fixedSpace (e * y)) = 2 * mc := hmc
  have hA1 := ncard_modEq_fixed y hy5 Set.univ (fun v _ => Set.mem_univ v)
  rw [Set.ncard_univ, Set.univ_inter, hFix y, hncard_sub, hmb, hVcard] at hA1
  have hY5 : 2 ^ (2 * mb) % 5 = 1 := by
    unfold Nat.ModEq at hA1
    norm_num at hA1
    omega
  have hA2 := ncard_modEq_fixed y hy5 {v | e v = v} hinvE
  rw [← hFC, hFix e, hFix (e * y), hncard_sub, hncard_sub, hma, hmc] at hA2
  have hC5 : 2 ^ (2 * ma) % 5 = 2 ^ (2 * mc) % 5 := hA2
  have hA3 : 136 ≡ (Z ∩ {v | e v = v}).ncard [MOD 3] := by
    have h := ncard_modEq_fixed e he3 Z (hZinv e he)
    rw [hZcard] at h
    exact h
  have hA4 : 136 ≡ (Z ∩ {v | y v = v}).ncard [MOD 5] := by
    have h := ncard_modEq_fixed y hy5 Z (hZinv y hy)
    rw [hZcard] at h
    exact h
  have hA5 : (Z ∩ {v | y v = v}).ncard ≡ (Z ∩ {v | (e * y) v = v}).ncard [MOD 3] := by
    have h := ncard_modEq_fixed e he3 (Z ∩ {v | y v = v}) hZy
    rw [hZC1] at h
    exact h
  have hA6 : (Z ∩ {v | e v = v}).ncard ≡ (Z ∩ {v | (e * y) v = v}).ncard [MOD 5] := by
    have h := ncard_modEq_fixed y hy5 (Z ∩ {v | e v = v}) hZe
    rw [hZC2] at h
    exact h
  have hdE : finrank (ZMod 2) (fixedSpace e) < 8 := hne_top e he1
  have hdY : finrank (ZMod 2) (fixedSpace y) < 8 := hne_top y hy1
  have hle1 : fixedSpace (e * y) ≤ fixedSpace e := fun v hv => by
    have : (e * y) v = v := mem_fixedSpace.1 hv
    have h2 : v ∈ {v | (e * y) v = v} := this
    rw [hFC] at h2
    exact mem_fixedSpace.2 h2.1
  have hle2 : fixedSpace (e * y) ≤ fixedSpace y := fun v hv => by
    have : (e * y) v = v := mem_fixedSpace.1 hv
    have h2 : v ∈ {v | (e * y) v = v} := this
    rw [hFC] at h2
    exact mem_fixedSpace.2 h2.2
  have hf1 := Submodule.finrank_mono hle1
  have hf2 := Submodule.finrank_mono hle2
  have hz := z15_arith ma mb mc (Z ∩ {v | e v = v}).ncard (Z ∩ {v | y v = v}).ncard
    (Z ∩ {v | (e * y) v = v}).ncard (by omega) (by omega) (by omega) (by omega)
    (by omega) (hpos _ ⟨h0Z, by simp⟩) (hpos _ ⟨h0Z, by simp⟩) (hpos _ ⟨h0Z, by simp⟩) hY5 hC5
    (by unfold Nat.ModEq at hA3; omega) (by unfold Nat.ModEq at hA4; omega)
    (by unfold Nat.ModEq at hA5; omega) (by unfold Nat.ModEq at hA6; omega) gE gY gC
  rcases hz with h | h
  · left; omega
  · right; omega


theorem no_E9_commuting_five
    (E : Subgroup ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)))
    (hEo : ∀ g ∈ E, g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 (ZMod 2)))
    (hE3 : ∀ g ∈ E, g ^ 3 = 1) (hEcard : Nat.card E = 9)
    {y : (Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)}
    (hy : y ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 (ZMod 2)))
    (hy5 : y ^ 5 = 1) (hy1 : y ≠ 1) (hEy : ∀ g ∈ E, g * y = y * g) : False := by
  classical
  have hK : Nat.card (ZMod 2) = 2 := by simp
  set V := Fin 4 ⊕ Fin 4 → ZMod 2 with hVdef
  haveI : Finite V := inferInstance
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  haveI : Fintype ↥E := Fintype.ofFinite _
  haveI : ∀ g : ↥E, Fintype (MulAction.fixedBy V g) := fun g => Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient ↥E V) := Fintype.ofFinite _
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ↥E V
  have hEc : Fintype.card ↥E = 9 := by rw [← Nat.card_eq_fintype_card]; exact hEcard
  have hVc : Fintype.card V = 256 := by
    rw [← Nat.card_eq_fintype_card]
    show Nat.card (Fin 4 ⊕ Fin 4 → ZMod 2) = 256
    rw [Nat.card_fun, hK]
    simp
  have hFix : ∀ g : V ≃ₗ[ZMod 2] V, {v | g v = v} = (fixedSpace g : Set V) := fun g => by
    ext v
    exact (mem_fixedSpace (x := g)).symm
  have hncard_sub : ∀ W : Submodule (ZMod 2) V, (W : Set V).ncard = 2 ^ finrank (ZMod 2) W :=
    fun W => by
      rw [← Nat.card_coe_set_eq]
      exact (card_submodule W).trans (by rw [hK])
  have hfc : ∀ g : ↥E, Fintype.card (MulAction.fixedBy V g) =
      2 ^ finrank (ZMod 2) (fixedSpace (g : V ≃ₗ[ZMod 2] V)) := fun g => by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← hncard_sub, ← hFix]
    rfl
  have h1 : Fintype.card (MulAction.fixedBy V (1 : ↥E)) = 256 := by
    rw [← hVc]
    refine Fintype.card_congr (Equiv.subtypeUnivEquiv fun v => ?_)
    show (1 : ↥E) • v = v
    exact one_smul _ _
  have h2 : ∀ g : ↥E, g ≠ 1 → Fintype.card (MulAction.fixedBy V g) % 9 = 1 := by
    intro g hg1
    have hg1' : (g : V ≃ₗ[ZMod 2] V) ≠ 1 := fun h => hg1 (Subtype.ext h)
    rw [hfc]
    rcases finrank_fixed_zero_or_six (hEo g g.2) hy (hEy g g.2) (hE3 g g.2) hy5 hg1' hy1 with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hsum : (∑ g : ↥E, Fintype.card (MulAction.fixedBy V g)) % 9 = 3 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ↥E)), Nat.add_mod, Finset.sum_nat_mod]
    have : ∀ g ∈ Finset.univ.erase (1 : ↥E), Fintype.card (MulAction.fixedBy V g) % 9 = 1 :=
      fun g hg => h2 g (Finset.ne_of_mem_erase hg)
    rw [Finset.sum_congr rfl this, h1]
    simp [Finset.card_erase_of_mem, hEc]
  rw [hburn, hEc] at hsum
  omega


abbrev OG : Type := ↥(CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadPlus 4 (ZMod 2)))

theorem mem_orth_of_OG (g : OG) :
    (g : (Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 (ZMod 2)) :=
  CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_orthogonalGroup _ g.2

theorem noThreeSeven_orth : NoThreeSeven OG := by
  intro s y hs3 hs1 hy7 hc
  have key := no_commuting_three_seven (K := ZMod 2) (by simp) (mem_orth_of_OG s) (mem_orth_of_OG y)
    (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hc]) (by rw [← Subgroup.coe_pow, hs3]; rfl)
    (by
      have := pow_orderOf_eq_one y
      rw [hy7] at this
      rw [← Subgroup.coe_pow, this]
      rfl)
  rcases key with h | h
  · exact hs1 (Subtype.ext h)
  · have : y = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy7
    omega

theorem noNineFive_orth : NoNineFive OG := by
  intro E hE hcard y hy5 hc
  let E' : Subgroup ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) :=
    E.map (CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadPlus 4 (ZMod 2))).subtype
  refine no_E9_commuting_five E' ?_ ?_ ?_ (y := (y : (Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2]
    (Fin 4 ⊕ Fin 4 → ZMod 2))) (mem_orth_of_OG y) ?_ ?_ ?_
  · rintro _ ⟨e, -, rfl⟩
    exact mem_orth_of_OG e
  · rintro _ ⟨e, he, rfl⟩
    show (e : (Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) ^ 3 = 1
    rw [← Subgroup.coe_pow, hE.2 e he]
    rfl
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcard]
  · have := pow_orderOf_eq_one y
    rw [hy5] at this
    rw [← Subgroup.coe_pow, this]
    rfl
  · intro h
    have : y = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy5
    omega
  · rintro _ ⟨e, he, rfl⟩
    exact congrArg Subtype.val (hc e he)

end I269R

end CFSG.LocalAnalysis.GLTheoremA

end
