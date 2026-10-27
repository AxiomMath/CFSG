module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeStd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieGamma
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement Pointwise

@[expose] def HeldUCentralStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldSetting X L →
    (∀ A : Subgroup X, A ≤ normalizer (L : Set X) → IsFourGroup A → wGroup A = ⊥) →
    ∃ U : Subgroup X, U ≤ L ∧ IsFourGroup U ∧ ∀ u ∈ U, u ≠ 1 →
      U ≤ (pCore 2 ↥(centralizer ({u} : Set X))).map (centralizer ({u} : Set X)).subtype

namespace HeOdd

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem eq_one_of_mem_odd_of_pow {Y : Subgroup X} (hY : Odd (Nat.card Y)) {x : X} (hx : x ∈ Y)
    {n : ℕ} (hn : x ^ (2 ^ n) = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : Odd (orderOf x) := hY.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hx)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases k with _ | k
  · rwa [pow_zero, orderOf_eq_one_iff] at hk
  · exfalso
    rw [hk] at h2
    exact (Nat.not_even_iff_odd.mpr h2) (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.succ_ne_zero k)))

omit [Finite X] in
theorem commute_of_le_pCore {U Y : Subgroup X} {u v y : X} (hYodd : Odd (Nat.card Y))
    (hUY : U ≤ normalizer (Y : Set X))
    (hUO : U ≤ (pCore 2 ↥(centralizer ({u} : Set X))).map (centralizer ({u} : Set X)).subtype)
    (hv : v ∈ U) (hy : y ∈ Y) (hyu : y ∈ centralizer ({u} : Set X)) : v * y = y * v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : v * y * v⁻¹ * y⁻¹ ∈ Y :=
    mul_mem ((mem_normalizer_iff.mp (hUY hv) y).mp hy) (inv_mem hy)
  obtain ⟨v', hv', hv'e⟩ := hUO hv
  have hv'e' : (v' : X) = v := hv'e
  obtain ⟨y', hy'⟩ : ∃ y' : ↥(centralizer ({u} : Set X)), (y' : X) = y := ⟨⟨y, hyu⟩, rfl⟩
  have hw : v' * (y' * v'⁻¹ * y'⁻¹) ∈ pCore 2 ↥(centralizer ({u} : Set X)) :=
    mul_mem hv' (pCore_normal.conj_mem _ (inv_mem hv') _)
  obtain ⟨n, hn⟩ := pCore_isPGroup (p := 2) (G := ↥(centralizer ({u} : Set X))) ⟨_, hw⟩
  have hn' : (v * y * v⁻¹ * y⁻¹) ^ (2 ^ n) = 1 := by
    have h := congrArg (fun z => ((z : ↥(pCore 2 ↥(centralizer ({u} : Set X)))) : X)) hn
    simp only [SubgroupClass.coe_pow, coe_mul, coe_inv, OneMemClass.coe_one] at h
    rw [show v * y * v⁻¹ * y⁻¹ = (v' : X) * ((y' : X) * (v' : X)⁻¹ * (y' : X)⁻¹) by
      rw [hv'e', hy']; group]
    exact h
  have h2 := eq_one_of_mem_odd_of_pow hYodd h1 hn'
  calc v * y = v * y * v⁻¹ * y⁻¹ * (y * v) := by group
    _ = y * v := by rw [h2, one_mul]

theorem commute_of_four {U Y : Subgroup X} (hU : IsFourGroup U) (hYodd : Odd (Nat.card Y))
    (hUY : U ≤ normalizer (Y : Set X))
    (hUO : ∀ u ∈ U, u ≠ 1 →
      U ≤ (pCore 2 ↥(centralizer ({u} : Set X))).map (centralizer ({u} : Set X)).subtype) :
    ∀ v ∈ U, ∀ y ∈ Y, v * y = y * v := by
  obtain ⟨e⟩ := hU
  have hsq : ∀ p : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), p * p = 1 := by decide
  have hEA : Open.IsElemAbelian 2 U := by
    refine ⟨⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩, fun x hx => ?_⟩
    have h := e.injective (show e (⟨x, hx⟩ * ⟨x, hx⟩) = e 1 by rw [map_mul, hsq, map_one])
    rw [pow_two]
    exact congrArg Subtype.val h
  have h4 : 4 ≤ Nat.card U := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    simp [Nat.card_eq_fintype_card]
  have hgen := RankTwoOddLie.le_iSup_inf_centralizer_of_odd hEA h4 hYodd hUY le_rfl
  have hYU : Y ≤ centralizer (U : Set X) := by
    refine hgen.trans (iSup₂_le fun u hu => iSup_le fun hu1 => ?_)
    intro y hy
    obtain ⟨hyY, hyu⟩ := mem_inf.mp hy
    exact mem_centralizer_iff.mpr fun v hv =>
      commute_of_le_pCore hYodd hUY (hUO u hu hu1) hv hyY hyu
  intro v hv y hy
  exact (mem_centralizer_iff.mp (hYU hy)) v hv

theorem orderOf_ofAdd_one_one :
    orderOf ((Multiplicative.ofAdd 1, 1) : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) =
      2 := by
  have h1 : ((Multiplicative.ofAdd 1, 1) :
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ^ 2 = 1 := by decide
  have h2 : ((Multiplicative.ofAdd 1, 1) :
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ≠ 1 := by decide
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h1 h2

theorem simple_nonab_of_held {L : Type*} [Group L]
    (e : L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) :
    IsSimpleGroup (L ⧸ pPrimeCore 2 L) ∧ ∃ a b : L ⧸ pPrimeCore 2 L, a * b ≠ b * a := by
  have hHe : IsSimpleGroup Blueprint.NativeSporadic.He := Sporadic.He.isSimpleGroup_He
  refine ⟨@MulEquiv.isSimpleGroup _ _ _ _ hHe e, ?_⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_held
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have h' := congrArg e h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'

theorem commute_of_held {L Y : Subgroup X} (hLp : ⁅L, L⁆ = L)
    (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He)
    (hLY : L ≤ normalizer (Y : Set X)) {u : X} (huL : u ∈ L) (hu : orderOf u = 2)
    (huY : ∀ y ∈ Y, u * y = y * u) : ∀ l ∈ L, ∀ y ∈ Y, l * y = y * l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥L := isPerfect_iff.mpr hLp
  obtain ⟨hQs, -⟩ := simple_nonab_of_held e
  set N : Subgroup ↥L := (centralizer (Y : Set X)).subgroupOf L with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, mem_subgroupOf, mem_centralizer_iff] at hn ⊢
    intro y hy
    have hy' : (g : X)⁻¹ * y * (g : X) ∈ Y := by
      have := (mem_normalizer_iff.mp (inv_mem (hLY g.2)) y).mp hy
      rwa [inv_inv] at this
    have hc := hn _ hy'
    simp only [coe_mul, coe_inv]
    calc y * ((g : X) * n * (g : X)⁻¹) = g * (((g : X)⁻¹ * y * g) * n) * (g : X)⁻¹ := by group
      _ = g * (n * ((g : X)⁻¹ * y * g)) * (g : X)⁻¹ := by rw [hc]
      _ = (g : X) * n * (g : X)⁻¹ * y := by group
  have huN : (⟨u, huL⟩ : ↥L) ∈ N :=
    mem_subgroupOf.mpr (mem_centralizer_iff.mpr fun y hy => (huY y hy).symm)
  have hNe : (N.map (QuotientGroup.mk' (pPrimeCore 2 ↥L))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  have htop : N.map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (pPrimeCore 2 ↥L))) with hbot | htop
    · exfalso
      have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨u, huL⟩ ∈
          N.map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) := mem_map_of_mem _ huN
      rw [hbot, mem_bot] at h1
      have h3 : (⟨u, huL⟩ : ↥L) ∈ pPrimeCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h1
      have hodd : Odd (orderOf (⟨u, huL⟩ : ↥L)) :=
        (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
          (Subgroup.orderOf_dvd_natCard _ h3)
      rw [Subgroup.orderOf_mk, hu] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    · exact htop
  have hNO : ∀ g : ↥L, ∃ n ∈ N, n⁻¹ * g ∈ pPrimeCore 2 ↥L := by
    intro g
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥L) g ∈
        N.map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) := by
      rw [htop]; exact mem_top _
    obtain ⟨n, hn, hq⟩ := h1
    refine ⟨n, hn, ?_⟩
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (pPrimeCore 2 ↥L) (n⁻¹ * g) = 1
    rw [map_mul, map_inv, hq, inv_mul_cancel]
  have hmap : (pPrimeCore 2 ↥L).map (QuotientGroup.mk' N) = ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨n, hn, ho⟩ := hNO g
    refine ⟨n⁻¹ * g, ho, ?_⟩
    have h1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, map_inv, h1, inv_one, one_mul]
  have hodd : Odd (Nat.card (↥L ⧸ N)) := by
    have h1 := card_map_dvd (pPrimeCore 2 ↥L) (QuotientGroup.mk' N)
    rw [hmap, card_top] at h1
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h1
  have hsub : Subsingleton (↥L ⧸ N) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable (↥L ⧸ N) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have hNtop : N = ⊤ := QuotientGroup.subsingleton_iff.mp hsub
  intro l hl y hy
  have hlN : (⟨l, hl⟩ : ↥L) ∈ N := by rw [hNtop]; exact mem_top _
  exact ((mem_centralizer_iff.mp (mem_subgroupOf.mp hlN)) y hy).symm

theorem pPrimeCore_eq_bot_of_central
    (hMult : TBLit.HeldTrivialMultiplier) {L : Subgroup X} (hLp : ⁅L, L⁆ = L)
    (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He)
    (hc : ∀ x ∈ (pPrimeCore 2 ↥L).map L.subtype, ∀ l ∈ L, x * l = l * x) :
    pPrimeCore 2 ↥L = ⊥ := by
  obtain ⟨hQs, a, b, hab⟩ := simple_nonab_of_held e
  have hcQ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥L ⧸ pPrimeCore 2 ↥L)) with h | h
    · exact h
    · exfalso
      have hb : b ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by rw [h]; exact mem_top b
      exact hab ((mem_center_iff.mp hb) a)
  have hOZ : pPrimeCore 2 ↥L ≤ center ↥L := fun x hx =>
    mem_center_iff.mpr fun g => Subtype.ext (hc _ ⟨x, hx, rfl⟩ _ g.2).symm
  have hZO : center ↥L ≤ pPrimeCore 2 ↥L := by
    intro z hz
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥L) z ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) g
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) g']
    rw [hcQ, mem_bot] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hZ : center ↥L = pPrimeCore 2 ↥L := le_antisymm hZO hOZ
  let e' : ↥L ⧸ center ↥L ≃* ↥L ⧸ pPrimeCore 2 ↥L := QuotientGroup.quotientMulEquivOfEq hZ
  have hq : IsQuasisimple ↥L := by
    refine ⟨isPerfect_iff.mpr hLp, @MulEquiv.isSimpleGroup _ _ _ _ hQs e', ?_⟩
    refine ⟨e'.symm a, e'.symm b, fun h => hab ?_⟩
    have h' := congrArg e' h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  rw [← hZ]
  exact hMult ↥L hq ⟨e'.trans e⟩

end HeOdd

theorem heldOddCoreStep_of_central
    (hUc : HeldUCentralStep)
    (hMult : TBLit.HeldTrivialMultiplier) (hMax : MaximalTwoComponentInputHe)
    (hS : SchreierFor Blueprint.Catalog) (hHN : HeldNotProperFixedInput)
    (h64 : HeldSylowElementarySixtyFour) : HeldOddCoreStep := by
  intro X _ _ L hset hW t ht htL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimp, hnab, hK, hU, -, ⟨a, ha2, hLa, hLc⟩, ⟨e⟩⟩ := id hset
  have hmax : GSWeakMaximalComponent L :=
    gsWeakMaximalComponent_of_held hS hHN hnab hK ha2 hLa hLc (nonempty_fusionZStar_equiv_held e)
  have haN : a ∈ normalizer (L : Set X) := mem_normalizer_of_commute fun x hx =>
    (mem_centralizer_singleton_iff.mp (hLa hx)).symm
  obtain ⟨S, hSyl, -⟩ := exists_isSylowTwoIn_mem haN ha2
  obtain ⟨E, hET, -, hEe, hE64⟩ := exists_elem_sixtyFour e h64 inf_le_right
    (hSyl.isPGroup.to_le inf_le_left) (card_inf_eq_1024 e hSyl)
  have hrank : 3 ≤ pRank 2 ↥L := three_le_pRank_of_le hEe (by omega) (hET.trans inf_le_right)
  have htop : GeneralizedFitting.subgroup X = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup X ≃* X := (MulEquiv.subgroupCongr htop).trans topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup X) := eF.isSimpleGroup
  have hnF : ∃ u v : GeneralizedFitting.subgroup X, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hnab
    exact ⟨eF.symm u, eF.symm v, fun h => huv (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hLie : ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup X) := fun h => hU (Or.inl h)
  have hT9 := hMax X hsF hnF hLie hK L hmax (by omega) (Sol78.not_psp4_of_held e)
    (nonempty_fusionZStar_equiv_held e) t ht htL
  set C := centralizer ({t} : Set X) with hC
  set M : Subgroup X := ⨆ (c : X) (_ : c ∈ C), conjugate L c with hM
  set O : Subgroup X := (pPrimeCore 2 ↥C).map C.subtype with hO
  have hLM : L ≤ M := by
    refine le_iSup₂_of_le 1 (one_mem C) (le_of_eq ?_)
    ext x
    simp only [conjugate, inv_one, map_one, mem_map, MulEquiv.coe_toMonoidHom, MulAut.one_apply,
      exists_eq_right]
  have hconjC : ∀ c ∈ C, conjugate L c ≤ C := by
    intro c hc
    rintro _ ⟨l, hl, rfl⟩
    exact mul_mem (mul_mem (inv_mem hc) (htL hl)) (inv_mem (inv_mem hc))
  have hMC : M ≤ C := iSup₂_le hconjC
  have hMOL : M ≤ O ⊔ L := by
    refine iSup₂_le fun c hc => ?_
    exact (le_iSup₂_of_le c (hconjC c hc) le_rfl).trans hT9.1
  have hCO : C ≤ normalizer (O : Set X) := le_normalizer_oddIn
  have hconjM : ∀ c ∈ C, ∀ x ∈ M, c * x * c⁻¹ ∈ M := by
    intro c hc x hx
    have hle : M ≤ M.comap (MulAut.conj c).toMonoidHom := by
      refine iSup₂_le fun c' hc' => ?_
      intro y hy
      rw [UnbalancedLayer.mem_conjugate_iff] at hy
      rw [mem_comap]
      have hz : (MulAut.conj c).toMonoidHom y ∈ conjugate L (c' * c⁻¹) := by
        rw [UnbalancedLayer.mem_conjugate_iff]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show c' * c⁻¹ * (c * y * c⁻¹) * (c' * c⁻¹)⁻¹ = c' * y * c'⁻¹ by group]
        exact hy
      exact (le_iSup₂ (f := fun c (_ : c ∈ C) => conjugate L c) (c' * c⁻¹)
        (mul_mem hc' (inv_mem hc))) hz
    have := hle hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hCM : C ≤ normalizer (M : Set X) := by
    intro c hc
    refine mem_normalizer_iff.mpr fun x => ⟨hconjM c hc x, fun h => ?_⟩
    have := hconjM c⁻¹ (inv_mem hc) _ h
    rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this
  have hCY : C ≤ normalizer (((pPrimeCore 2 ↥M).map M.subtype : Subgroup X) : Set X) := by
    intro c hc
    have := pPrimeCore_characteristic (p := 2) (G := ↥M)
    refine mem_normalizer_iff.mpr fun x =>
      ⟨fun hx => Walter.conj_mem_map_of_characteristic (hCM hc) hx, fun hx => ?_⟩
    have h := Walter.conj_mem_map_of_characteristic (hCM (inv_mem hc)) hx
    rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h
  have hYodd := odd_card_map_pPrimeCore M
  obtain ⟨U, hUL, hU4, hUO⟩ := hUc X L hset hW
  have hUY := HeOdd.commute_of_four hU4 hYodd (fun v hv => hCY (hMC (hLM (hUL hv)))) hUO
  obtain ⟨u, huU, hu⟩ : ∃ u ∈ U, orderOf u = 2 := by
    obtain ⟨eU⟩ := hU4
    refine ⟨(eU.symm (Multiplicative.ofAdd 1, 1) : X), (eU.symm _).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, HeOdd.orderOf_ofAdd_one_one]
  have hLp : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLa hLc
  have hLY := HeOdd.commute_of_held hLp e (fun l hl => hCY (hMC (hLM hl))) (hUL huU) hu
    (hUY u huU)
  have hMY : ∀ y ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, y * m = m * y := by
    have hle : M ≤ centralizer ((((pPrimeCore 2 ↥M).map M.subtype : Subgroup X)) : Set X) := by
      refine iSup₂_le fun c hc => ?_
      intro x hx
      rw [UnbalancedLayer.mem_conjugate_iff] at hx
      rw [mem_centralizer_iff]
      intro y hy
      have hy' := (mem_normalizer_iff.mp (hCY hc) y).mp hy
      have h1 := hLY _ hx _ hy'
      calc y * x = c⁻¹ * ((c * y * c⁻¹) * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * (c * y * c⁻¹)) * c := by rw [← h1]
        _ = x * y := by group
    intro y hy m hm
    exact (mem_centralizer_iff.mp (hle hm)) y hy
  have hMOY : M ⊓ O ≤ (pPrimeCore 2 ↥M).map M.subtype := by
    refine le_map_pPrimeCore inf_le_left (fun h hh d hd => mem_inf.mpr
      ⟨mul_mem (mul_mem hh (mem_inf.mp hd).1) (inv_mem hh), ?_⟩) ?_
    · exact (mem_normalizer_iff.mp (hCO (hMC hh)) d).mp (mem_inf.mp hd).2
    · have hOodd : Odd (Nat.card O) := odd_card_map_pPrimeCore C
      exact hOodd.of_dvd_nat (card_dvd_of_le inf_le_right)
  have hdec : ∀ m ∈ M, ∃ y ∈ (pPrimeCore 2 ↥M).map M.subtype, ∃ l ∈ L, m = y * l := by
    intro m hm
    have hmset : m ∈ (O : Set X) * (L : Set X) := by
      rw [← coe_mul_of_right_le_normalizer_left O L (htL.trans hCO)]
      exact hMOL hm
    obtain ⟨o, ho, l, hl, hol⟩ := hmset
    have hoM : o ∈ M := by
      have := mul_mem hm (inv_mem (hLM hl))
      rwa [← hol, mul_inv_cancel_right] at this
    exact ⟨o, hMOY (mem_inf.mpr ⟨hoM, ho⟩), l, hl, hol.symm⟩
  have hMp : M ≤ ⁅M, M⁆ := by
    refine iSup₂_le fun c hc => ?_
    have h1 : conjugate L c = ⁅conjugate L c, conjugate L c⁆ := by
      rw [conjugate, ← map_commutator, hLp]
    rw [h1]
    have h2 : conjugate L c ≤ M := le_iSup₂_of_le c hc le_rfl
    exact commutator_mono h2 h2
  have hML : M = L := by
    refine le_antisymm (hMp.trans ?_) hLM
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨o₁, ho₁, l₁, hl₁, rfl⟩ := hdec g₁ hg₁
    obtain ⟨o₂, ho₂, l₂, hl₂, rfl⟩ := hdec g₂ hg₂
    have c1 := hMY o₁ ho₁ (l₁ * o₂ * l₂ * l₁⁻¹) (mul_mem (mul_mem (mul_mem (hLM hl₁)
      (map_subtype_le _ ho₂)) (hLM hl₂)) (inv_mem (hLM hl₁)))
    have c2 := hMY o₂ ho₂ (l₂ * l₁⁻¹ * l₂⁻¹) (mul_mem (mul_mem (hLM hl₂)
      (inv_mem (hLM hl₁))) (inv_mem (hLM hl₂)))
    have e1 : ⁅o₁ * l₁, o₂ * l₂⁆ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ :=
      calc ⁅o₁ * l₁, o₂ * l₂⁆ = o₁ * (l₁ * o₂ * l₂ * l₁⁻¹) * o₁⁻¹ * (l₂⁻¹ * o₂⁻¹) := by
            rw [commutatorElement_def]; group
        _ = (l₁ * o₂ * l₂ * l₁⁻¹) * o₁ * o₁⁻¹ * (l₂⁻¹ * o₂⁻¹) := by rw [c1]
        _ = l₁ * (o₂ * (l₂ * l₁⁻¹ * l₂⁻¹)) * o₂⁻¹ := by group
        _ = l₁ * ((l₂ * l₁⁻¹ * l₂⁻¹) * o₂) * o₂⁻¹ := by rw [c2]
        _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by group
    rw [e1]
    exact mul_mem (mul_mem (mul_mem hl₁ hl₂) (inv_mem hl₁)) (inv_mem hl₂)
  have hc := hMY
  rw [hML] at hc
  rw [hML]
  exact HeOdd.pPrimeCore_eq_bot_of_central hMult hLp e hc

end CFSG.ComponentClassification.GrSLit
