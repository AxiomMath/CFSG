module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexRootCenter
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedGroup

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Inner

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.UnitaryHulls
open CFSG.ShultStronglyClosedTI.UnitaryExcluded
open CFSG.ProperTwoGeneratedCore.CosetNormalizer
open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Frame
open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Model
open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.RootCenter CFSG.SolvableHall
open scoped Pointwise

theorem exists_conj_eq_of_complement {F : Type*} [Group F] [Finite F] {N T X : Subgroup F}
    (hTN : T ≤ Subgroup.normalizer (N : Set F)) (hXB : X ≤ N ⊔ T) (hNT : N ⊓ T = ⊥)
    (hNX : N ⊓ X = ⊥) (hXT : Nat.card X = Nat.card T)
    (hcop : Nat.Coprime (Nat.card N) (Nat.card T)) (hNsolv : Group.IsSolvable N) :
    ∃ n ∈ N, X = T.map (MulAut.conj n⁻¹).toMonoidHom := by
  set B := N ⊔ T with hBdef
  have hNB : N ≤ B := le_sup_left
  have hTB : T ≤ B := le_sup_right
  have hBN : B ≤ Subgroup.normalizer (N : Set F) := sup_le Subgroup.le_normalizer hTN
  have hXN : X ≤ Subgroup.normalizer (N : Set F) := hXB.trans hBN
  have hnorm : (N.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNB).mpr hBN
  have hcardB : Nat.card B = Nat.card N * Nat.card T := by
    have := card_sup_mul_card_inf hTN
    rwa [hNT, Subgroup.card_bot, mul_one] at this
  have hNXB : N ⊔ X = B := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hNB hXB)
    have := card_sup_mul_card_inf hXN
    rw [hNX, Subgroup.card_bot, mul_one] at this
    rw [hcardB, this, hXT]
  have hcardN' : Nat.card (N.subgroupOf B) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv
  have hindex : (N.subgroupOf B).index = Nat.card T := by
    have h := Subgroup.card_mul_index (N.subgroupOf B)
    rw [hcardN', hcardB] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hsolv' : Group.IsSolvable (N.subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNB).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNB).injective
  have hmul : ∀ Y : Subgroup F, Y ≤ B → N ⊔ Y = B →
      ((N.subgroupOf B : Subgroup B) : Set B) * ((Y.subgroupOf B : Subgroup B) : Set B) =
        Set.univ := by
    intro Y hYB hNY
    have hYN : Y ≤ Subgroup.normalizer (N : Set F) := hYB.trans hBN
    rw [Set.eq_univ_iff_forall]
    intro b
    have hb : (b : F) ∈ ((N ⊔ Y : Subgroup F) : Set F) := by rw [hNY]; exact b.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N Y hYN] at hb
    obtain ⟨n, hn, y, hy, hny⟩ := hb
    exact ⟨⟨n, hNB hn⟩, hn, ⟨y, hYB hy⟩, hy, Subtype.ext hny⟩
  have hinf : ∀ Y : Subgroup F, N ⊓ Y = ⊥ → N.subgroupOf B ⊓ Y.subgroupOf B = ⊥ := by
    intro Y hNY
    rw [eq_bot_iff]
    rintro x ⟨hxN, hxY⟩
    have : (x : F) ∈ N ⊓ Y := ⟨hxN, hxY⟩
    rw [hNY] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))
  obtain ⟨n, hn, hconj⟩ := solvable_normal_hall_complement_conjugacy (N.subgroupOf B) hsolv'
    (by rw [hcardN', hindex]; exact hcop) (hmul T hTB rfl) (hmul X hXB hNXB) (hinf T hNT)
    (hinf X hNX)
  refine ⟨n, hn, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : (⟨x, hXB hx⟩ : B) ∈ X.subgroupOf B := hx
    rw [hconj] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    refine ⟨y, hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa using this
  · rintro ⟨y, hy, rfl⟩
    have hyB : (⟨y, hTB hy⟩ : B) ∈ T.subgroupOf B := hy
    have : (MulAut.conj n⁻¹).toMonoidHom ⟨y, hTB hy⟩ ∈ X.subgroupOf B := by
      rw [hconj]
      exact ⟨_, hyB, rfl⟩
    have h' := Subgroup.mem_subgroupOf.mp this
    simpa using h'

variable {G : Type} [Group G] [Finite G]

section Hull

variable {K : Type} [Field K] [Finite K] [CharP K 2] {J : HermitianForm 3 K}

theorem odd_torus_order {f : ℕ} (hf : 1 ≤ f) : Odd ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)) := by
  have hodd : Odd (2 ^ f + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right 3 (2 ^ f + 1)
  have hpos : 0 < Nat.gcd 3 (2 ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hdiv : (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1) = m :=
    Nat.div_eq_of_eq_mul_left hpos (hm.trans (mul_comm _ _))
  rw [hdiv]
  rw [hm] at hodd
  exact (Nat.odd_mul.mp hodd).2

theorem le_hull_and_mem_root_torus {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {L : Subgroup G} (θ : J.specialSubgroup ⧸ scalarCenter J ≃* L) {v : G}
    (hv : orderOf v = 2) (hLv : L ≤ Subgroup.centralizer ({v} : Set G))
    (hK : Subgroup.centralizer ({v} : Set G) ⊓ Subgroup.centralizer (L : Set G) =
      Subgroup.zpowers v)
    {W : Subgroup G} (hWv : W ≤ Subgroup.centralizer ({v} : Set G))
    (hWL : W ≤ Subgroup.normalizer (L : Set G))
    (hWQ : ∀ a ∈ W, ∀ x ∈ upperRootL J (scalarCenter J) hJ,
      a * ((θ x : L) : G) = ((θ x : L) : G) * a)
    (hWpow : ∀ a ∈ W, a ^ ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)) = 1) :
    W ≤ L ∧ ∀ a (ha : a ∈ L), a ∈ W →
      θ.symm ⟨a, ha⟩ ∈ (heisL J (scalarCenter J) hJ).range ⊔ torusL J (scalarCenter J) hJ := by
  have hkey : ∀ a ∈ W, ∃ ha : a ∈ L,
      θ.symm ⟨a, ha⟩ ∈ (heisL J (scalarCenter J) hJ).range ⊔ torusL J (scalarCenter J) hJ := by
    intro a haW
    set N := (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1) with hN
    have hNodd : Odd N := odd_torus_order (by omega)
    have hmap : L.map ((MulAut.conj a : MulAut G) : G →* G) = L := by
      apply map_eq_of_le
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hWL haW) y).mp hy
    set β : MulAut (J.specialSubgroup ⧸ scalarCenter J) :=
      (θ.trans (restrictMulAut (MulAut.conj a) L hmap)).trans θ.symm with hβ
    have hβapp : ∀ x, ((θ (β x) : L) : G) = a * ((θ x : L) : G) * a⁻¹ := by
      intro x
      rw [hβ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
        coe_restrictMulAut, MulAut.conj_apply]
    have hβpow : ∀ n : ℕ, ∀ x, ((θ ((β ^ n) x) : L) : G) = a ^ n * ((θ x : L) : G) * (a ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ n ih =>
        intro x
        rw [pow_succ, MulAut.mul_apply, ih, hβapp, pow_succ]
        group
    have haN : a ^ N = 1 := hWpow a haW
    have hβN : β ^ N = 1 := by
      ext x
      apply θ.injective
      apply Subtype.ext
      rw [hβpow, haN, one_mul, inv_one, mul_one, MulAut.one_apply]
    have hβfix : ∀ x ∈ upperRootL J (scalarCenter J) hJ, β x = x := by
      intro x hx
      apply θ.injective
      apply Subtype.ext
      rw [hβapp, hWQ a haW x hx, mul_inv_cancel_right]
    obtain ⟨z, c, hzc⟩ := exists_eq_conj_of_pow_eq_one hf hcard hfixed hJ le_rfl hβfix hNodd
      dvd_rfl hβN
    set r := heisL J (scalarCenter J) hJ z * QuotientGroup.mk' (scalarCenter J) (torusHom J hJ c)
      with hr
    have hconj : ∀ m ∈ L, a * m * a⁻¹ = ((θ r : L) : G) * m * ((θ r : L) : G)⁻¹ := by
      intro m hm
      have h1 := hβapp (θ.symm ⟨m, hm⟩)
      rw [hzc, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
      simpa using h1.symm
    have hvL : ∀ m ∈ L, v * m = m * v := fun m hm =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hLv hm)).symm
    have hk : ((θ r : L) : G)⁻¹ * a ∈ Subgroup.centralizer ({v} : Set G) ⊓
        Subgroup.centralizer (L : Set G) := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLv (θ r).2)) (hWv haW), ?_⟩
      show _ ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have := hconj m hm
      calc m * (((θ r : L) : G)⁻¹ * a)
          = ((θ r : L) : G)⁻¹ * (((θ r : L) : G) * m * ((θ r : L) : G)⁻¹) * a := by group
        _ = ((θ r : L) : G)⁻¹ * (a * m * a⁻¹) * a := by rw [this]
        _ = ((θ r : L) : G)⁻¹ * a * m := by group
    rw [hK] at hk
    rcases eq_one_or_eq_of_mem_zpowers hv hk with h1 | h1
    · have ha : a = ((θ r : L) : G) := (inv_mul_eq_one.mp h1).symm
      refine ⟨ha ▸ (θ r).2, ?_⟩
      have : (⟨a, ha ▸ (θ r).2⟩ : L) = θ r := Subtype.ext ha
      rw [this, MulEquiv.symm_apply_apply]
      exact Subgroup.mul_mem_sup ⟨z, rfl⟩ ⟨c, rfl⟩
    · exfalso
      have ha : a = ((θ r : L) : G) * v := by rw [← h1, mul_inv_cancel_left]
      have hcomm : Commute ((θ r : L) : G) v := (hvL _ (θ r).2).symm
      have hvv : v ^ 2 = 1 := by rw [← hv, pow_orderOf_eq_one]
      have hvN : v ^ N = v := by
        obtain ⟨m, hm⟩ := hNodd
        rw [hm, pow_succ, pow_mul, hvv, one_pow, one_mul]
      have hlN : ((θ r : L) : G) ^ N = v := by
        have h2 := haN
        rw [ha, hcomm.mul_pow, hvN] at h2
        have := eq_inv_of_mul_eq_one_left h2
        rwa [inv_eq_of_mul_eq_one_left (by rw [← pow_two, hvv] : v * v = 1)] at this
      have hvLmem : v ∈ L := hlN ▸ L.pow_mem (θ r).2 N
      have hcen : θ.symm ⟨v, hvLmem⟩ ∈ Subgroup.center (J.specialSubgroup ⧸ scalarCenter J) := by
        rw [Subgroup.mem_center_iff]
        intro x
        apply θ.injective
        apply Subtype.ext
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul]
        exact (hvL _ (θ x).2).symm
      rw [center_eq_bot hf hcard hfixed hJ, Subgroup.mem_bot] at hcen
      have hv1 : v = 1 := by
        have := congrArg (fun x => ((θ x : L) : G)) hcen
        simpa using this
      rw [hv1, orderOf_one] at hv
      exact absurd hv (by norm_num)
  refine ⟨fun a ha => (hkey a ha).1, fun a ha haW => ?_⟩
  obtain ⟨ha', h⟩ := hkey a haW
  exact h

omit [Finite G] in
theorem exists_cover_eq_torusL {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {L : Subgroup G} (θ : J.specialSubgroup ⧸ scalarCenter J ≃* L) {W : Subgroup G}
    (hWL : W ≤ L)
    (hWR : ∀ a (ha : a ∈ L), a ∈ W →
      θ.symm ⟨a, ha⟩ ∈ (heisL J (scalarCenter J) hJ).range ⊔ torusL J (scalarCenter J) hJ)
    (hWcard : Nat.card W = (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)) :
    ∃ θ' : J.specialSubgroup ⧸ scalarCenter J ≃* L,
      (W.subgroupOf L).map θ'.symm.toMonoidHom = torusL J (scalarCenter J) hJ := by
  set N := (heisL J (scalarCenter J) hJ).range with hNdef
  set T := torusL J (scalarCenter J) hJ with hTdef
  set X := (W.subgroupOf L).map θ.symm.toMonoidHom with hXdef
  have hTcard : Nat.card T = (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1) :=
    card_torusL_scalarCenter hf hcard hfixed hJ
  have hXcard : Nat.card X = Nat.card W := by
    rw [hXdef, Subgroup.card_map_of_injective θ.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv
  have hNcard : Nat.card N = 2 ^ (3 * f) := by
    rw [hNdef, MonoidHom.range_eq_map, Subgroup.card_map_of_injective (heisL_injective hJ le_rfl),
      Subgroup.card_top, UnitaryRootAutomorphism.card_coord J (2 ^ f) hcard hfixed, ← pow_mul,
      mul_comm]
  have hodd : Odd (Nat.card T) := by
    rw [hTcard]
    exact odd_torus_order (by omega)
  have hcop : Nat.Coprime (Nat.card N) (Nat.card T) := by
    rw [hNcard]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have hTN : T ≤ Subgroup.normalizer (N : Set (J.specialSubgroup ⧸ scalarCenter J)) := by
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, (torus_conj_heisL hJ c z).symm⟩
    · rintro ⟨z, hz⟩
      refine ⟨torusCoord c⁻¹ z, ?_⟩
      rw [← torus_conj_heisL hJ c⁻¹ z, hz]
      simp only [MonoidHom.coe_comp, Function.comp_apply, map_inv]
      group
  have hXB : X ≤ N ⊔ T := by
    rintro _ ⟨⟨a, ha⟩, haW, rfl⟩
    exact hWR a ha haW
  have hNT : N ⊓ T = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hNX : N ⊓ X = ⊥ := disjoint_iff.mp
    (Subgroup.disjoint_of_coprime_natCard (by rw [hXcard, hWcard, ← hTcard]; exact hcop))
  have hsolv : Group.IsSolvable N := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 N := IsPGroup.of_card hNcard
    have := hp.isNilpotent
    infer_instance
  obtain ⟨n, -, hn⟩ := exists_conj_eq_of_complement hTN hXB hNT hNX
    (by rw [hXcard, hWcard, hTcard]) hcop hsolv
  refine ⟨(MulAut.conj n⁻¹).trans θ, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨a, ha⟩, haW, rfl⟩
    have hmem : θ.symm ⟨a, ha⟩ ∈ X := ⟨⟨a, ha⟩, haW, rfl⟩
    rw [hn] at hmem
    obtain ⟨t, htT, ht⟩ := hmem
    have : ((MulAut.conj n⁻¹).trans θ).symm ⟨a, ha⟩ = t := by
      rw [MulEquiv.symm_trans_apply, ← ht]
      exact MulEquiv.symm_apply_apply _ _
    rw [MulEquiv.coe_toMonoidHom, this]
    exact htT
  · intro hy
    have hmem : (MulAut.conj n⁻¹).toMonoidHom y ∈ X := by
      rw [hn]
      exact ⟨y, hy, rfl⟩
    obtain ⟨⟨a, ha⟩, haW, hay⟩ := hmem
    refine ⟨⟨a, ha⟩, haW, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_trans_apply]
    rw [show θ.symm ⟨a, ha⟩ = (MulAut.conj n⁻¹) y from hay]
    exact MulEquiv.symm_apply_apply _ _

end Hull

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Inner
