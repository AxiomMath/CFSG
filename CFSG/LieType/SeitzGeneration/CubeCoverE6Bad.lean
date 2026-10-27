module

public import CFSG.LieType.SeitzGeneration.CubeCoverE6Rest
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenAsm
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenOA
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadSinger
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonomial

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open

theorem coverImage_trans {K C C' : Type*} [Group K] [Group C] [Group C']
    (e : K ⧸ Subgroup.center K ≃* C) (φ : C ≃* C') (E : Subgroup (MulAut K)) :
    coverImage (e.trans φ) E = (coverImage e E).map (MulAut.congr φ).toMonoidHom := by
  rw [coverImage, coverImage, Subgroup.map_map]
  congr 1

end CFSG.LieType.SeitzGeneration

namespace CFSG.LieType.SeitzGeneration.CubeCoverE6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.CubeCoverLayer
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts.ChevAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.GLTheoremB
  CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.SeitzGeneration.ExcWideThree
open scoped commutatorElement

theorem e6_exists_lift_of_central {k : Type} [Field k] [Finite k] (hk : 5 ≤ Nat.card k)
    {X Y : Type*} [Group X] [Group Y] (p : X →* Y) (hp : Function.Surjective p)
    (hker : p.ker ≤ Subgroup.center X) (β : e6Data_valid.minGroup k →* Y) :
    ∃ σ : e6Data_valid.minGroup k →* X, p.comp σ = β := by
  obtain ⟨s, hs⟩ := e6_exists_section_of_central (k := k) hk
    (π := CFSG.LieType.Steinberg.pullbackFst β p)
    (CFSG.LieType.Steinberg.pullbackFst_surjective hp)
    (CFSG.LieType.Steinberg.ker_pullbackFst_le_center hker)
  refine ⟨(MonoidHom.snd _ _).comp ((CFSG.LieType.Steinberg.pullback β p).subtype.comp s), ?_⟩
  ext g
  have h1 : ((s g : CFSG.LieType.Steinberg.pullback β p) :
      e6Data_valid.minGroup k × X).1 = g := hs g
  have h2 := CFSG.LieType.Steinberg.mem_pullback.1 (s g).2
  rw [h1] at h2
  show p (((s g : CFSG.LieType.Steinberg.pullback β p) :
    e6Data_valid.minGroup k × X).2) = β g
  exact h2.symm

theorem e6Isogeny_nm_elem {k : Type} [Field k] [Finite k] (l : Fin Tag.E6.rank) :
    e6Isogeny k (e6Data_valid.nm k l) = weylElement .E6 k l := by
  refine Subtype.ext ?_
  rw [show e6Data_valid.nm k l = e6Data_valid.nt k l 1 from rfl, e6Isogeny_nt_eq]
  rfl

theorem e6Isogeny_hm_elem {k : Type} [Field k] [Finite k] (l : Fin Tag.E6.rank) (s : kˣ) :
    e6Isogeny k (e6Data_valid.hm k l s) = torusElement .E6 k l s := by
  refine Subtype.ext ?_
  rw [e6Isogeny_hm_eq]
  exact (torusElt_eq_rootDiagUnit (τ := Tag.E6) (K := k) (i := l) (u := s)).symm

theorem e6Isogeny_e6NWord {k : Type} [Field k] [Finite k]
    (ω : List (Fin Tag.E6.rank)) :
    e6Isogeny k (e6NWord k ω) = weylWordElt .E6 k ω := by
  refine Subtype.ext ?_
  rw [e6Isogeny_nWord, coe_weylWordElt]
  rfl

theorem rootDiagUnit_zpow {τ : Tag} {K : Type} [Field K] (b : Fin τ.rank → Kˣ) (n : ℤ) :
    rootDiagUnit τ (b ^ n) = (rootDiagUnit τ b) ^ n := by
  exact map_zpow (rootDiagUnitHom (τ := τ) (K := K)) b n

theorem rootDiagAutHom_torusElement {k : Type} [Field k] (b : Fin Tag.E6.rank → kˣ)
    (l : Fin Tag.E6.rank) (s : kˣ) :
    rootDiagAutHom .E6 k b (torusElement .E6 k l s) = torusElement .E6 k l s := by
  change rootDiagAut .E6 k b (torusElement .E6 k l s) = torusElement .E6 k l s
  refine Subtype.ext ?_
  rw [coe_rootDiagAut]
  change rootDiagUnit .E6 b * torusElt .E6 k l s * (rootDiagUnit .E6 b)⁻¹ =
    torusElt .E6 k l s
  rw [torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul, rootDiagUnit_inv, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp [Pi.mul_apply]

theorem rootDiagAutHom_weylElement {k : Type} [Field k] (b : Fin Tag.E6.rank → kˣ)
    (l : Fin Tag.E6.rank) :
    rootDiagAutHom .E6 k b (weylElement .E6 k l) =
      torusElement .E6 k l (b l) * weylElement .E6 k l := by
  change rootDiagAut .E6 k b (weylElement .E6 k l) = _
  refine Subtype.ext ?_
  rw [coe_rootDiagAut]
  change rootDiagUnit .E6 b * weylElt .E6 k l 1 * (rootDiagUnit .E6 b)⁻¹ =
    torusElt .E6 k l (b l) * weylElt .E6 k l 1
  rw [rootDiagUnit_conj_weylElt_one]

theorem e6StarS_mulSingle_self {k : Type} [Field k] (l : Fin Tag.E6.rank) (s : kˣ) :
    e6StarS l (Pi.mulSingle l s) = Pi.mulSingle l s⁻¹ := by
  funext j
  by_cases hj : j = l
  · rw [hj]
    simp only [e6StarS, Pi.mul_apply, Pi.mulSingle_eq_same]
    rw [Finset.prod_eq_single l]
    · rw [Pi.mulSingle_eq_same, Tag.cartan_self]
      rw [show s ^ (-(2 : ℤ)) = s⁻¹ * s⁻¹ by
        rw [← zpow_neg_one s, ← zpow_add]
        norm_num]
      group
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, one_zpow]
    · intro h
      exact absurd (Finset.mem_univ l) h
  · rw [Pi.mulSingle_eq_of_ne hj]
    simp only [e6StarS, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, mul_one]

theorem e6_commutator_nm_hm {k : Type} [Field k] {s : kˣ} (hs : s ^ 3 = 1)
    (l : Fin Tag.E6.rank) :
    ⁅e6Data_valid.nm k l, e6Data_valid.hm k l s⁆ = e6Data_valid.hm k l s := by
  have h1 : e6Data_valid.nm k l * e6Data_valid.hm k l s * (e6Data_valid.nm k l)⁻¹ =
      e6Data_valid.hm k l s⁻¹ := by
    have h := nm_conj_minTorus k l (Pi.mulSingle l s)
    simpa only [minTorus_mulSingle, e6StarS_mulSingle_self] using h
  have h2 : s⁻¹ * s⁻¹ = s := by
    have hmul : s⁻¹ * s⁻¹ = s ^ (-2 : ℤ) := by
      rw [← zpow_neg_one s, ← zpow_add]
      norm_num
    rw [hmul]
    simpa using zpow_eq_zpow_of_dvd (ζ := s) hs (a := (-2 : ℤ)) (b := (1 : ℤ)) (by norm_num)
  rw [commutatorElement_def, h1, show (e6Data_valid.hm k l s)⁻¹ = e6Data_valid.hm k l s⁻¹
    from (map_inv (e6Data_valid.hHom k l) s).symm]
  change (e6Data_valid.hHom k l) s⁻¹ * (e6Data_valid.hHom k l) s⁻¹ =
    (e6Data_valid.hHom k l) s
  rw [← map_mul, h2]

theorem lift_rootDiagAut_hm_fixed {k : Type} [Field k] [Finite k]
    {b : Fin Tag.E6.rank → kˣ} {ψ : e6Data_valid.minGroup k →* e6Data_valid.minGroup k}
    (hψ : ∀ g, e6Isogeny k (ψ g) = rootDiagAutHom .E6 k b (e6Isogeny k g))
    {l : Fin Tag.E6.rank} (hb : b l = 1) {s : kˣ} (hs : s ^ 3 = 1) :
    ψ (e6Data_valid.hm k l s) = e6Data_valid.hm k l s := by
  have hz₁ : (e6Data_valid.nm k l)⁻¹ * ψ (e6Data_valid.nm k l) ∈
      Subgroup.center (e6Data_valid.minGroup k) := by
    refine e6Isogeny_ker_le_center k ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψ, e6Isogeny_nm_elem, rootDiagAutHom_weylElement,
      hb, torusElement_one_eq, one_mul]
    exact inv_mul_cancel _
  have hz₂ : (e6Data_valid.hm k l s)⁻¹ * ψ (e6Data_valid.hm k l s) ∈
      Subgroup.center (e6Data_valid.minGroup k) := by
    refine e6Isogeny_ker_le_center k ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψ, e6Isogeny_hm_elem, rootDiagAutHom_torusElement]
    exact inv_mul_cancel _
  have hψnm : ψ (e6Data_valid.nm k l) =
      e6Data_valid.nm k l * ((e6Data_valid.nm k l)⁻¹ * ψ (e6Data_valid.nm k l)) := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hψhm : ψ (e6Data_valid.hm k l s) =
      e6Data_valid.hm k l s * ((e6Data_valid.hm k l s)⁻¹ * ψ (e6Data_valid.hm k l s)) := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hcomm := map_commutatorElement ψ (e6Data_valid.nm k l) (e6Data_valid.hm k l s)
  rw [e6_commutator_nm_hm hs l] at hcomm
  have hR : ⁅ψ (e6Data_valid.nm k l), ψ (e6Data_valid.hm k l s)⁆ =
      e6Data_valid.hm k l s := by
    rw [hψnm, hψhm,
      Subgroup.mem_center_iff.1 hz₁ (e6Data_valid.nm k l),
      Subgroup.mem_center_iff.1 hz₂ (e6Data_valid.hm k l s),
      commutatorElement_mul_mul_of_mem_center hz₁ hz₂, e6_commutator_nm_hm hs l]
  rw [hR] at hcomm
  exact hcomm

theorem lift_rootDiagAut_minTorus {k : Type} [Field k] [Finite k]
    {b : Fin Tag.E6.rank → kˣ} {ψ : e6Data_valid.minGroup k →* e6Data_valid.minGroup k}
    (hψ : ∀ g, e6Isogeny k (ψ g) = rootDiagAutHom .E6 k b (e6Isogeny k g))
    {u : Fin Tag.E6.rank → kˣ} (hu : ∀ l, u l ^ 3 = 1)
    (hbu : ∀ l, b l = 1 ∨ u l = 1) :
    ψ (minTorus e6Data_valid k u) = minTorus e6Data_valid k u := by
  classical
  have key : ∀ s : Finset (Fin Tag.E6.rank),
      ψ (minTorus e6Data_valid k (∏ l ∈ s, Pi.mulSingle l (u l))) =
        minTorus e6Data_valid k (∏ l ∈ s, Pi.mulSingle l (u l)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, map_mul, map_mul, ih]
        have hsingle : ψ (minTorus e6Data_valid k (Pi.mulSingle a (u a))) =
            minTorus e6Data_valid k (Pi.mulSingle a (u a)) := by
          rw [minTorus_mulSingle]
          rcases hbu a with hb | hu1
          · exact lift_rootDiagAut_hm_fixed hψ hb (hu a)
          · rw [hu1, MinData.Valid.hm_one, map_one]
        rw [hsingle]
  have hprod : (∏ l, Pi.mulSingle l (u l)) = u := Finset.univ_prod_mulSingle u
  rw [← hprod]
  exact key Finset.univ

theorem e6BadCube_le_e6Inndiag {K : Type} [Field K] (ω c : Kˣ) :
    e6BadCube K ω c ≤ e6Inndiag K := by
  have hD : ∀ a, rootDiagAutHom .E6 K a ∈ e6Inndiag K := fun a =>
    le_sup_right (a := CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) ⟨a, rfl⟩
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (rfl | rfl | rfl)
  · exact innerAut_le_e6Inndiag K ⟨_, rfl⟩
  · exact hD _
  · exact mul_mem (innerAut_le_e6Inndiag K ⟨_, rfl⟩) (hD _)

theorem e6BadX_apply_e6BadN {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    {ω : Kˣ} (h3 : ω ^ 3 = 1) (c : Kˣ) :
    e6BadX K c (e6BadN K c) = e6BadN K c := by
  refine Subtype.ext ?_
  change (weylWordElt .E6 K e6BadWord : ModGL .E6 K) *
    (rootDiagUnit .E6 ![1, 1, c, 1, 1, 1] * (e6BadN K c : ModGL .E6 K) *
      (rootDiagUnit .E6 ![1, 1, c, 1, 1, 1])⁻¹) *
      (weylWordElt .E6 K e6BadWord : ModGL .E6 K)⁻¹ = _
  rw [show ∀ a b m : ModGL .E6 K, a * (b * m * b⁻¹) * a⁻¹ = a * b * m * (a * b)⁻¹ from
    fun a b m => by group, e6BadN_commute_X hK h3 c]
  group

theorem e6D0_ne_one {K : Type} [Field K] {ω : Kˣ} (h1 : ω ≠ 1) :
    rootDiagAutHom .E6 K (e6D0Char ω) ≠ 1 := by
  intro h
  apply h1
  simpa [e6D0Char] using
    congrFun (rootDiagAutHom_injective (h.trans (map_one (rootDiagAutHom .E6 K)).symm)) 1

theorem e6BadX_notMem_zpowers_d0 {K : Type} [Field K] [Finite K]
    {ω : Kˣ} (c : Kˣ) (hE : IsElemAbelian 3 (e6BadCube K ω c))
    (hcard : Nat.card (e6BadCube K ω c) = 3 ^ 3) :
    e6BadX K c ∉ Subgroup.zpowers (rootDiagAutHom .E6 K (e6D0Char ω)) := by
  have hh : MulAut.conj (e6LineElt ω) ∈ e6BadCube K ω c := Subgroup.subset_closure (by simp)
  have hd : rootDiagAutHom .E6 K (e6D0Char ω) ∈ e6BadCube K ω c :=
    Subgroup.subset_closure (by simp)
  have hab : Commute (MulAut.conj (e6LineElt ω)) (rootDiagAutHom .E6 K (e6D0Char ω)) := by
    have h := hE.1.is_comm.comm ⟨_, hh⟩ ⟨_, hd⟩
    exact congrArg Subtype.val h
  intro hz
  exact notMem_closure_pair_of_card hab (hE.2 _ hh) (hE.2 _ hd) hcard
    (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)) hz)

def e6M0 : Fin Tag.E6.rank → ℤ := ![0, 2, 0, 0, 1, 1]

def e6D0Exp : Fin Tag.E6.rank → ℤ := ![0, 1, 0, 0, 1, 1]

def e6BadV : Fin Tag.E6.rank → ℤ := ![2, 0, 1, 0, 2, 1]

theorem e6RootParams_e6M0 {k : Type} [Field k] {ω : kˣ} (hω3 : ω ^ 3 = 1) :
    e6RootParams (fun l => ω ^ e6M0 l) = e6D0Char ω := by
  have hdiv : ∀ j, (3 : ℤ) ∣ (∑ l, e6M0 l * Tag.E6.cartan l j) - e6D0Exp j := by
    decide +kernel
  funext j
  rw [e6D0Char_eq]
  simp only [e6RootParams]
  rw [show (∏ l, (ω ^ e6M0 l) ^ Tag.E6.cartan l j) =
      ω ^ (∑ l, e6M0 l * Tag.E6.cartan l j) from ?_]
  exact zpow_eq_zpow_of_dvd hω3 (hdiv j)
  rw [show (∏ l, (ω ^ e6M0 l) ^ Tag.E6.cartan l j) =
      ∏ l, ω ^ (e6M0 l * Tag.E6.cartan l j) from
    Finset.prod_congr rfl fun l _ => by rw [zpow_mul]]
  rw [Finset.prod_zpow_eq_zpow_sum]

theorem minTorus_t0_mul_psiX_inv {k : Type} [Field k] {ω : kˣ} (hω3 : ω ^ 3 = 1) :
    minTorus e6Data_valid k (fun l => ω ^ e6M0 l) *
      (minTorus e6Data_valid k
        (e6BadWord.foldr e6StarS (fun l => ω ^ e6M0 l)))⁻¹ =
      minTorus e6Data_valid k (fun l => ω ^ e6BadV l) := by
  have hdiv : ∀ l, (3 : ℤ) ∣ e6M0 l -
      (e6BadWord.foldr (fun j x => reflect Tag.E6 j x) e6M0) l - e6BadV l := by
    decide +kernel
  rw [foldr_e6StarS_zpow]
  rw [← map_inv, ← map_mul]
  congr 1
  funext l
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [← zpow_neg, ← zpow_add]
  refine zpow_eq_zpow_of_dvd hω3 ?_
  have h := hdiv l
  rw [show e6M0 l + -(e6BadWord.foldr (fun j x => reflect Tag.E6 j x) e6M0) l - e6BadV l =
    e6M0 l - (e6BadWord.foldr (fun j x => reflect Tag.E6 j x) e6M0) l - e6BadV l by ring]
  exact h

theorem e6RootParams_e6BadV {k : Type} [Field k] {ω : kˣ} (hω3 : ω ^ 3 = 1) :
    e6RootParams (fun l => ω ^ e6BadV l) = 1 := by
  have hdiv : ∀ j, (3 : ℤ) ∣ ∑ l, e6BadV l * Tag.E6.cartan l j := by
    decide +kernel
  funext j
  simp only [e6RootParams, Pi.one_apply]
  rw [show (∏ l, (ω ^ e6BadV l) ^ Tag.E6.cartan l j) =
      ω ^ (∑ l, e6BadV l * Tag.E6.cartan l j) from ?_]
  · rw [show (1 : kˣ) = ω ^ (0 : ℤ) from (zpow_zero ω).symm]
    exact zpow_eq_zpow_of_dvd hω3 (by simpa using hdiv j)
  rw [show (∏ l, (ω ^ e6BadV l) ^ Tag.E6.cartan l j) =
      ∏ l, ω ^ (e6BadV l * Tag.E6.cartan l j) from
    Finset.prod_congr rfl fun l _ => by rw [zpow_mul]]
  rw [Finset.prod_zpow_eq_zpow_sum]

theorem e6BadV_mem_ker {k : Type} [Field k] [Finite k] {ω : kˣ} (hω3 : ω ^ 3 = 1) :
    minTorus e6Data_valid k (fun l => ω ^ e6BadV l) ∈ (e6Isogeny k).ker := by
  rw [MonoidHom.mem_ker]
  refine Subtype.ext ?_
  rw [e6Isogeny_minTorus, e6RootParams_e6BadV hω3, rootDiagUnit_one]
  rfl

theorem e6BadV_ne_one {k : Type} [Field k] {ω : kˣ} (hω1 : ω ≠ 1) :
    minTorus e6Data_valid k (fun l => ω ^ e6BadV l) ≠ 1 := by
  intro h
  have h' : (fun l => ω ^ e6BadV l) = 1 :=
    minTorus_injective e6Data_valid k (by rw [h, map_one])
  have h2 := congrFun h' 2
  simp [e6BadV] at h2
  exact hω1 h2

theorem card_center_e6_min {k : Type} [Field k] [Finite k]
    (h3 : 3 ∣ Nat.card k - 1) :
    Nat.card (Subgroup.center (e6Data_valid.minGroup k)) = 3 := by
  obtain ⟨hcard, -⟩ := card_center_e6 k
  rw [hcard, Nat.gcd_eq_left h3]

theorem zpow_pow_three_eq_one {k : Type} [Field k] {ω : kˣ} (hω3 : ω ^ 3 = 1) (m : ℤ) :
    (ω ^ m) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul]
  rw [show (1 : kˣ) = ω ^ (0 : ℤ) from (zpow_zero ω).symm]
  refine zpow_eq_zpow_of_dvd hω3 ?_
  exact ⟨m, by push_cast; ring⟩

theorem e6M0_zpow_three {k : Type} [Field k] {ω : kˣ} (hω3 : ω ^ 3 = 1)
    (l : Fin Tag.E6.rank) : (ω ^ e6M0 l) ^ 3 = 1 := by
  have h : ∀ j, e6M0 j = 0 ∨ e6M0 j = 2 ∨ e6M0 j = 1 := by decide +kernel
  rcases h l with h | h | h
  · rw [h]
    simp
  · rw [h]
    exact zpow_pow_three_eq_one hω3 2
  · rw [h]
    simpa using hω3

theorem e6BadB_or_e6M0 {k : Type} [Field k] (c : kˣ) (ω : kˣ)
    (l : Fin Tag.E6.rank) :
    (![1, 1, c, 1, 1, 1] : Fin Tag.E6.rank → kˣ) l = 1 ∨ (fun j => ω ^ e6M0 j) l = 1 := by
  fin_cases l
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (by show ω ^ (0 : ℤ) = 1; simp)
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem minTorus_mul_comm {k : Type} [Field k] (u v : Fin Tag.E6.rank → kˣ) :
    minTorus e6Data_valid k u * minTorus e6Data_valid k v =
      minTorus e6Data_valid k v * minTorus e6Data_valid k u := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem lift_conj_minTorus {k : Type} [Field k] [Finite k]
    (u : Fin Tag.E6.rank → kˣ) (g : e6Data_valid.minGroup k) :
    e6Isogeny k ((MulAut.conj (minTorus e6Data_valid k u)) g) =
      rootDiagAutHom .E6 k (e6RootParams u) (e6Isogeny k g) := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, e6Isogeny_minTorus]
  change rootDiagUnit .E6 (e6RootParams u) * ↑(e6Isogeny k g) *
      (rootDiagUnit .E6 (e6RootParams u))⁻¹ =
    rootDiagUnit .E6 (e6RootParams u) * ↑(e6Isogeny k g) *
      (rootDiagUnit .E6 (e6RootParams u))⁻¹
  rfl

theorem e6M0_foldr_badNWord :
    ∀ l : Fin Tag.E6.rank, (3 : ℤ) ∣
      (e6BadNWord.foldr (fun j x => reflect Tag.E6 j x) e6M0) l - e6M0 l := by
  decide +kernel

theorem e6_fixed_of_conj {G K C : Type*} [Group G] [Group K] [Group C]
    (hperf : commutator G = ⊤)
    (π : K →* C) (hker : π.ker ≤ Subgroup.center K)
    (θsc : G →* C) (σ : G →* K) (hσ : ∀ g, π (σ g) = θsc g)
    (ind : MulAut K →* MulAut C)
    (hind : ∀ (f : MulAut K) (g : K), π (f g) = ind f (π g))
    (ε : MulAut K) (ψ : G →* G)
    (hψ : θsc.comp ψ = (ind ε).toMonoidHom.comp θsc)
    (g : G) : ε (σ g) = σ (ψ g) := by
  haveI : Group.IsPerfect G := ⟨hperf⟩
  have hcomp : π.comp (ε.toMonoidHom.comp σ) = π.comp (σ.comp ψ) := by
    apply MonoidHom.ext
    intro z
    calc π (ε (σ z)) = ind ε (π (σ z)) := hind ε (σ z)
      _ = ind ε (θsc z) := congrArg (ind ε) (hσ z)
      _ = θsc (ψ z) := by
        simpa [MonoidHom.comp_apply] using (DFunLike.congr_fun hψ z).symm
      _ = π (σ (ψ z)) := (hσ (ψ z)).symm
  have h := CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect
    (H := G) (E := K) (G := C)
    (π := π) (β₁ := ε.toMonoidHom.comp σ) (β₂ := σ.comp ψ) hker hcomp
  change (ε.toMonoidHom.comp σ) g = (σ.comp ψ) g
  rw [h]

theorem e6BadCube_fixed_lift
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] (hk3 : ringChar k ≠ 3)
    (h3 : 3 ∣ Nat.card k - 1) (h4 : Nat.card k ≠ 4)
    (θ : K ⧸ Subgroup.center K ≃* adjointGroup Tag.E6 k) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) {ω c : kˣ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hEc : coverImage θ E = e6BadCube k ω c) :
    ∃ (σ : e6Data_valid.minGroup k →* K)
      (ψd ψX : e6Data_valid.minGroup k →* e6Data_valid.minGroup k)
      (y : e6Data_valid.minGroup k) (b' : Fin Tag.E6.rank → kˣ),
      (∀ g, θ.toMonoidHom (QuotientGroup.mk' (Subgroup.center K) (σ g)) = e6Isogeny k g) ∧
      (∀ g, e6Isogeny k (ψd g) = rootDiagAutHom .E6 k (e6D0Char ω) (e6Isogeny k g)) ∧
      (∀ g, e6Isogeny k (ψX g) = e6BadX k c (e6Isogeny k g)) ∧
      ψd y = y ∧ ψX y = y ∧
      ((θ.toMonoidHom (QuotientGroup.mk' (Subgroup.center K) (σ y)) :
        adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
        (weylWordElt .E6 k e6BadNWord : ModGL Tag.E6 k) * rootDiagUnit .E6 b' := by
  classical

  let π : K →* adjointGroup Tag.E6 k :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  let ind : MulAut K →* MulAut (adjointGroup Tag.E6 k) :=
    (MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)
  have hind : ∀ (f : MulAut K) (g : K), π (f g) = ind f (π g) := by
    intro f g
    simp [π, ind, MulAut.congr, quotientCenterAut']
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : π.ker ≤ Subgroup.center K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = 1 := by
      apply θ.injective
      simpa [π] using hx
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hk5 : 5 ≤ Nat.card k := four_lt_card_of_three_dvd h3 h4
  have hK4 : 4 ≤ Nat.card k := (four_lt_card_of_three_dvd h3 h4).le
  haveI : Group.IsPerfect (e6Data_valid.minGroup k) := CFSG.LieType.CurtisTits.isPerfect_e6 k
  have hEab : IsElemAbelian 3 (coverImage θ E) := isElemAbelian_coverImage θ hE
  have hEd : coverImage θ E ≤ e6Inndiag k := by
    rw [hEc]
    exact e6BadCube_le_e6Inndiag ω c
  have hdE : rootDiagAutHom .E6 k (e6D0Char ω) ∈ coverImage θ E := by
    rw [hEc]
    exact Subgroup.subset_closure (by simp)
  have hXE : e6BadX k c ∈ coverImage θ E := by
    rw [hEc]
    exact Subgroup.subset_closure (by simp)
  have hmapE : E.map ind = coverImage θ E := rfl
  obtain ⟨εd, hεdE, hεd⟩ := Subgroup.mem_map.1 (hmapE ▸ hdE)
  obtain ⟨εX, hεXE, hεX⟩ := Subgroup.mem_map.1 (hmapE ▸ hXE)
  have hcard27E : Nat.card E = 27 := by rw [hcard]; norm_num

  let u0 : Fin Tag.E6.rank → kˣ := fun l => ω ^ e6M0 l
  let t0 : e6Data_valid.minGroup k := minTorus e6Data_valid k u0
  let D0 : adjointGroup Tag.E6 k := e6Isogeny k t0
  let b : Fin Tag.E6.rank → kˣ := ![1, 1, c, 1, 1, 1]
  obtain ⟨σ, hσ_comp⟩ := e6_exists_lift_of_central (k := k) hk5 (X := K)
    (Y := adjointGroup Tag.E6 k) π hπ hker (e6Isogeny k)
  have hσ : ∀ g, π (σ g) = e6Isogeny k g := fun g => DFunLike.congr_fun hσ_comp g
  obtain ⟨ψb, hψb_comp⟩ :=
    e6_exists_lift_of_central (k := k) hk5 (X := e6Data_valid.minGroup k)
      (Y := adjointGroup Tag.E6 k) (e6Isogeny k) (e6Isogeny_surjective k)
      (e6Isogeny_ker_le_center k) ((rootDiagAutHom .E6 k b).toMonoidHom.comp (e6Isogeny k))
  have hψb : ∀ g, e6Isogeny k (ψb g) = rootDiagAutHom .E6 k b (e6Isogeny k g) :=
    fun g => DFunLike.congr_fun hψb_comp g
  let ψd : e6Data_valid.minGroup k →* e6Data_valid.minGroup k := (MulAut.conj t0).toMonoidHom
  let Nw : e6Data_valid.minGroup k := e6NWord k e6BadWord
  let ψX : e6Data_valid.minGroup k →* e6Data_valid.minGroup k :=
    (MulAut.conj Nw).toMonoidHom.comp ψb
  have hψd : ∀ g, e6Isogeny k (ψd g) = rootDiagAutHom .E6 k (e6D0Char ω) (e6Isogeny k g) := by
    intro g
    have h := lift_conj_minTorus u0 g
    rw [e6RootParams_e6M0 hω3] at h
    exact h
  have hψX : ∀ g, e6Isogeny k (ψX g) = e6BadX k c (e6Isogeny k g) := by
    intro g
    change e6Isogeny k (Nw * ψb g * Nw⁻¹) =
      MulAut.conj (weylWordElt .E6 k e6BadWord) (rootDiagAutHom .E6 k b (e6Isogeny k g))
    rw [map_mul, map_mul, map_inv, e6Isogeny_e6NWord, hψb, MulAut.conj_apply]
  let x : e6Data_valid.minGroup k :=
    e6NWord k e6BadNWord * e6Data_valid.hm k 2 c * e6Data_valid.hm k 3 c
  have hx : e6Isogeny k x = e6BadN k c := by
    change e6Isogeny k (e6NWord k e6BadNWord * e6Data_valid.hm k 2 c *
      e6Data_valid.hm k 3 c) = e6BadN k c
    rw [map_mul, map_mul, e6Isogeny_e6NWord, e6Isogeny_hm_elem, e6Isogeny_hm_elem]
    rfl
  have hψd_t0 : ψd t0 = t0 := by
    change t0 * t0 * t0⁻¹ = t0
    rw [mul_assoc, mul_inv_cancel, mul_one]
  have hNcomm : e6NWord k e6BadNWord * t0 = t0 * e6NWord k e6BadNWord := by
    have h := nWord_conj_minTorus k e6BadNWord u0
    have hfold : e6BadNWord.foldr e6StarS u0 = u0 := by
      rw [foldr_e6StarS_zpow]
      funext l
      exact zpow_eq_zpow_of_dvd hω3 (e6M0_foldr_badNWord l)
    rw [hfold] at h
    calc e6NWord k e6BadNWord * t0 =
        (e6NWord k e6BadNWord * t0 * (e6NWord k e6BadNWord)⁻¹) *
          e6NWord k e6BadNWord := by group
      _ = t0 * e6NWord k e6BadNWord := by rw [h]
  have h2comm : Commute t0 (e6Data_valid.hm k 2 c) := by
    rw [← minTorus_mulSingle e6Data_valid k 2 c]
    exact minTorus_mul_comm u0 (Pi.mulSingle 2 c)
  have h3comm : Commute t0 (e6Data_valid.hm k 3 c) := by
    rw [← minTorus_mulSingle e6Data_valid k 3 c]
    exact minTorus_mul_comm u0 (Pi.mulSingle 3 c)
  have hx_fixed_d : ψd x = x := by
    have hxc : Commute t0 x := by
      rw [commute_iff_eq]
      change t0 * (e6NWord k e6BadNWord * e6Data_valid.hm k 2 c *
        e6Data_valid.hm k 3 c) =
        (e6NWord k e6BadNWord * e6Data_valid.hm k 2 c *
          e6Data_valid.hm k 3 c) * t0
      calc t0 * (e6NWord k e6BadNWord * e6Data_valid.hm k 2 c *
            e6Data_valid.hm k 3 c) =
          (t0 * e6NWord k e6BadNWord) * e6Data_valid.hm k 2 c *
            e6Data_valid.hm k 3 c := by group
        _ = (e6NWord k e6BadNWord * t0) * e6Data_valid.hm k 2 c *
            e6Data_valid.hm k 3 c := by rw [hNcomm.symm]
        _ = e6NWord k e6BadNWord * (t0 * e6Data_valid.hm k 2 c) *
            e6Data_valid.hm k 3 c := by group
        _ = e6NWord k e6BadNWord * (e6Data_valid.hm k 2 c * t0) *
            e6Data_valid.hm k 3 c := by rw [h2comm.eq]
        _ = e6NWord k e6BadNWord * e6Data_valid.hm k 2 c *
            (t0 * e6Data_valid.hm k 3 c) := by group
        _ = e6NWord k e6BadNWord * e6Data_valid.hm k 2 c *
            (e6Data_valid.hm k 3 c * t0) := by rw [h3comm.eq]
        _ = (e6NWord k e6BadNWord * e6Data_valid.hm k 2 c *
            e6Data_valid.hm k 3 c) * t0 := by group
    change t0 * x * t0⁻¹ = x
    rw [hxc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hψXx : e6Isogeny k (ψX x) = e6BadN k c := by
    rw [hψX, hx, e6BadX_apply_e6BadN hK4 hω3 c]
  let z : e6Data_valid.minGroup k := x⁻¹ * ψX x
  have hzx : ψX x = x * z := by
    change ψX x = x * (x⁻¹ * ψX x)
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hz_mem : z ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    refine e6Isogeny_ker_le_center k ?_
    rw [MonoidHom.mem_ker]
    change e6Isogeny k (x⁻¹ * ψX x) = 1
    rw [map_mul, map_inv, hx, hψXx, inv_mul_cancel]
  have hbu : ∀ l : Fin Tag.E6.rank, b l = 1 ∨ u0 l = 1 := fun l => e6BadB_or_e6M0 c ω l
  have hψb_t0 : ψb t0 = t0 :=
    lift_rootDiagAut_minTorus hψb (e6M0_zpow_three hω3) hbu
  have hψX_t0 : ψX t0 = Nw * t0 * Nw⁻¹ := by
    show (MulAut.conj Nw) (ψb t0) = Nw * t0 * Nw⁻¹
    rw [hψb_t0, MulAut.conj_apply]
  let δ : e6Data_valid.minGroup k := t0 * (ψX t0)⁻¹
  have hδ : δ = minTorus e6Data_valid k (fun l => ω ^ e6BadV l) := by
    have ht1 : Nw * t0 * Nw⁻¹ =
        minTorus e6Data_valid k (e6BadWord.foldr e6StarS u0) := by
      rw [show Nw = e6NWord k e6BadWord from rfl,
        show t0 = minTorus e6Data_valid k u0 from rfl]
      exact nWord_conj_minTorus k e6BadWord u0
    show t0 * (ψX t0)⁻¹ = minTorus e6Data_valid k (fun l => ω ^ e6BadV l)
    rw [hψX_t0, ht1]
    exact minTorus_t0_mul_psiX_inv hω3
  have hδ_mem : δ ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    rw [hδ]
    exact e6Isogeny_ker_le_center k (e6BadV_mem_ker hω3)
  have hδ_ne : δ ≠ 1 := by
    rw [hδ]
    exact e6BadV_ne_one hω1
  have hcardZ : Nat.card (Subgroup.center (e6Data_valid.minGroup k)) = 3 :=
    card_center_e6_min h3
  have hδcard : Nat.card (Subgroup.zpowers δ) = 3 := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf δ ∣ Nat.card (Subgroup.center (e6Data_valid.minGroup k)) :=
      Subgroup.orderOf_dvd_natCard _ hδ_mem
    rw [hcardZ] at hdvd
    have h1 : orderOf δ ≠ 1 := fun h => hδ_ne (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h h1
    · exact h
  have hZeq : Subgroup.zpowers δ = Subgroup.center (e6Data_valid.minGroup k) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hδ_mem) ?_
    rw [hcardZ, hδcard]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, δ ^ n = z := by
    have hz' : z ∈ Subgroup.zpowers δ := by
      rw [hZeq]
      exact hz_mem
    exact Subgroup.mem_zpowers_iff.1 hz'
  let y : e6Data_valid.minGroup k := x * t0 ^ n
  have hψd_y : ψd y = y := by
    change ψd (x * t0 ^ n) = x * t0 ^ n
    rw [map_mul, map_zpow, hx_fixed_d, hψd_t0]
  have hψX_t0_pow : ψX (t0 ^ n) = δ ^ (-n) * t0 ^ n := by
    rw [map_zpow]
    have ht : ψX t0 = δ⁻¹ * t0 := by
      have h : δ⁻¹ * t0 = ψX t0 := by
        change (t0 * (ψX t0)⁻¹)⁻¹ * t0 = ψX t0
        rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      exact h.symm
    rw [ht]
    have hcomm : Commute δ t0 := by
      rw [hδ]
      exact minTorus_mul_comm (fun l => ω ^ e6BadV l) u0
    rw [hcomm.inv_left.mul_zpow,
      show (δ⁻¹) ^ n = δ ^ (-n) from by rw [zpow_neg, inv_zpow]]
  have hψX_y : ψX y = y := by
    change ψX (x * t0 ^ n) = x * t0 ^ n
    rw [map_mul, hzx, hψX_t0_pow, ← hn]
    have h1 : δ ^ n * δ ^ (-n) = 1 := by
      rw [← zpow_add, add_neg_cancel, zpow_zero]
    calc x * δ ^ n * (δ ^ (-n) * t0 ^ n)
        = x * (δ ^ n * δ ^ (-n)) * t0 ^ n := by group
      _ = x * 1 * t0 ^ n := by rw [h1]
      _ = x * t0 ^ n := by group
  have hPy : e6Isogeny k y = e6BadN k c * D0 ^ n := by
    change e6Isogeny k (x * t0 ^ n) = e6BadN k c * D0 ^ n
    rw [map_mul, hx, map_zpow]
  have hP : π (σ y) = e6BadN k c * D0 ^ n := (hσ y).trans hPy
  let b' : Fin Tag.E6.rank → kˣ :=
    (fun j => c ^ Tag.E6.cartan 2 j) * (fun j => c ^ Tag.E6.cartan 3 j) *
      ((e6D0Char ω) ^ n)
  let D' : ModGL Tag.E6 k := rootDiagUnit .E6 b'
  have hD0mat : (D0 : ModGL .E6 k) = rootDiagUnit .E6 (e6D0Char ω) := by
    change (e6Isogeny k (minTorus e6Data_valid k u0) : ModGL .E6 k) =
      rootDiagUnit .E6 (e6D0Char ω)
    rw [e6Isogeny_minTorus, e6RootParams_e6M0 hω3]
  have hPmat : (π (σ y) : ModGL .E6 k) =
      (weylWordElt .E6 k e6BadNWord : ModGL .E6 k) * D' := by
    rw [hP]
    change (↑(e6BadN k c * D0 ^ n) : ModGL .E6 k) = _
    rw [Subgroup.coe_mul, Subgroup.coe_zpow, hD0mat, coe_e6BadN, ← coe_weylWordElt,
      ← rootDiagUnit_zpow, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit]
    show (weylWordElt .E6 k e6BadNWord : ModGL .E6 k) *
      rootDiagUnit .E6 (fun j => c ^ Tag.E6.cartan 2 j) *
      rootDiagUnit .E6 (fun j => c ^ Tag.E6.cartan 3 j) *
      rootDiagUnit .E6 ((e6D0Char ω) ^ n) =
      (weylWordElt .E6 k e6BadNWord : ModGL .E6 k) * D'
    rw [show D' = rootDiagUnit .E6 b' from rfl, rootDiagUnit_mul, rootDiagUnit_mul]
    group
  refine ⟨σ, ψd, ψX, y, b', ?_, hψd, hψX, hψd_y, hψX_y, ?_⟩
  · intro g
    exact hσ g
  · change ((π (σ y) : adjointGroup Tag.E6 k) : ModGL .E6 k) =
      (weylWordElt .E6 k e6BadNWord : ModGL .E6 k) * rootDiagUnit .E6 b'
    rw [hPmat]
theorem e6BadCube_fixed_point
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] (hk3 : ringChar k ≠ 3)
    (h3 : 3 ∣ Nat.card k - 1) (h4 : Nat.card k ≠ 4)
    (θ : K ⧸ Subgroup.center K ≃* adjointGroup Tag.E6 k) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) {ω c : kˣ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hEc : coverImage θ E = e6BadCube k ω c) :
    ∃ (σ : e6Data_valid.minGroup k →* K) (y : e6Data_valid.minGroup k)
      (b' : Fin Tag.E6.rank → kˣ),
      σ y ∈ seitzHyperGamma 3 E ∧
        ((θ.toMonoidHom (QuotientGroup.mk' (Subgroup.center K) (σ y)) :
          adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
          (weylWordElt .E6 k e6BadNWord : ModGL Tag.E6 k) * rootDiagUnit .E6 b' := by
  classical
  obtain ⟨σ, ψd, ψX, y, b', hσ, hψd, hψX, hψd_y, hψX_y, hPmat⟩ :=
    e6BadCube_fixed_lift hperf hk3 h3 h4 θ hE hcard hω3 hω1 hEc
  let π : K →* adjointGroup Tag.E6 k :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  let ind : MulAut K →* MulAut (adjointGroup Tag.E6 k) :=
    (MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)
  have hind : ∀ (f : MulAut K) (g : K), π (f g) = ind f (π g) := by
    intro f g
    simp [π, ind, MulAut.congr, quotientCenterAut']
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : π.ker ≤ Subgroup.center K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = 1 := by
      apply θ.injective
      simpa [π] using hx
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hk5 : 5 ≤ Nat.card k := four_lt_card_of_three_dvd h3 h4
  have hK4 : 4 ≤ Nat.card k := (four_lt_card_of_three_dvd h3 h4).le
  haveI : Group.IsPerfect (e6Data_valid.minGroup k) := CFSG.LieType.CurtisTits.isPerfect_e6 k
  have hEab : IsElemAbelian 3 (coverImage θ E) := isElemAbelian_coverImage θ hE
  have hEd : coverImage θ E ≤ e6Inndiag k := by
    rw [hEc]
    exact e6BadCube_le_e6Inndiag ω c
  have hdE : rootDiagAutHom .E6 k (e6D0Char ω) ∈ coverImage θ E := by
    rw [hEc]
    exact Subgroup.subset_closure (by simp)
  have hXE : e6BadX k c ∈ coverImage θ E := by
    rw [hEc]
    exact Subgroup.subset_closure (by simp)
  have hmapE : E.map ind = coverImage θ E := rfl
  obtain ⟨εd, hεdE, hεd⟩ := Subgroup.mem_map.1 (hmapE ▸ hdE)
  obtain ⟨εX, hεXE, hεX⟩ := Subgroup.mem_map.1 (hmapE ▸ hXE)
  have hcard27E : Nat.card E = 27 := by rw [hcard]; norm_num
  have hcomp_d : (e6Isogeny k).comp ψd = (ind εd).toMonoidHom.comp (e6Isogeny k) := by
    apply MonoidHom.ext
    intro g
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hεd]
    exact hψd g
  have hcomp_X : (e6Isogeny k).comp ψX = (ind εX).toMonoidHom.comp (e6Isogeny k) := by
    apply MonoidHom.ext
    intro g
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hεX]
    exact hψX g
  have hfix_d : εd (σ y) = σ y := by
    have h := e6_fixed_of_conj (G := e6Data_valid.minGroup k) (K := K)
      (C := adjointGroup Tag.E6 k) (Group.IsPerfect.commutator_eq_top) π hker
      (e6Isogeny k) σ hσ ind hind εd ψd hcomp_d y
    rwa [hψd_y] at h
  have hfix_X : εX (σ y) = σ y := by
    have h := e6_fixed_of_conj (G := e6Data_valid.minGroup k) (K := K)
      (C := adjointGroup Tag.E6 k) (Group.IsPerfect.commutator_eq_top) π hker
      (e6Isogeny k) σ hσ ind hind εX ψX hcomp_X y
    rwa [hψX_y] at h
  have hεd1 : εd ≠ 1 := by
    intro h1
    exact e6D0_ne_one hω1 (by rw [← hεd, h1, map_one])
  have hcardĒ : Nat.card (coverImage θ E) = 3 ^ 3 := by
    rw [card_coverImage hperf θ E, hcard]
  have hεX_notzp : εX ∉ Subgroup.zpowers εd := by
    intro hmem
    obtain ⟨m, hmz⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hXeq : e6BadX k c = (rootDiagAutHom .E6 k (e6D0Char ω)) ^ m := by
      calc e6BadX k c = ind εX := hεX.symm
        _ = ind (εd ^ m) := by rw [hmz]
        _ = (ind εd) ^ m := map_zpow ind εd m
        _ = (rootDiagAutHom .E6 k (e6D0Char ω)) ^ m := by rw [hεd]
    exact e6BadX_notMem_zpowers_d0 c (hEc ▸ hEab) (by rw [← hEc]; exact hcardĒ) (by
      rw [hXeq]
      exact Subgroup.mem_zpowers_iff.2 ⟨m, rfl⟩)
  have hyΓ : σ y ∈ seitzHyperGamma 3 E :=
    mem_seitzHyperGamma_of_fixed hE hcard27E hεdE hεXE hεd1 hεX_notzp hfix_d hfix_X
  refine ⟨σ, y, b', hyΓ, hPmat⟩

theorem seitzHyperGamma_eq_top_of_coverImage_eq_e6BadCube
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] (hk3 : ringChar k ≠ 3)
    (h3 : 3 ∣ Nat.card k - 1) (h4 : Nat.card k ≠ 4)
    (θ : K ⧸ Subgroup.center K ≃* adjointGroup Tag.E6 k) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) {ω c : kˣ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hEc : coverImage θ E = e6BadCube k ω c) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  let π : K →* adjointGroup Tag.E6 k :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  let ind : MulAut K →* MulAut (adjointGroup Tag.E6 k) :=
    (MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)
  have hind : ∀ (f : MulAut K) (g : K), π (f g) = ind f (π g) := by
    intro f g
    simp [π, ind, MulAut.congr, quotientCenterAut']
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : π.ker ≤ Subgroup.center K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = 1 := by
      apply θ.injective
      simpa [π] using hx
    exact (QuotientGroup.eq_one_iff x).mp h1
  haveI : Group.IsPerfect (e6Data_valid.minGroup k) := CFSG.LieType.CurtisTits.isPerfect_e6 k
  have hEab : IsElemAbelian 3 (coverImage θ E) := isElemAbelian_coverImage θ hE
  have hEd : coverImage θ E ≤ e6Inndiag k := by
    rw [hEc]
    exact e6BadCube_le_e6Inndiag ω c
  have hsig : MulAut.conj (e6LineElt ω) ∈ coverImage θ E := by
    rw [hEc]
    exact Subgroup.subset_closure (by simp)
  have hmapE : E.map ind = coverImage θ E := rfl
  obtain ⟨εh, hεhE, hεh⟩ := Subgroup.mem_map.1 (hmapE ▸ hsig)
  obtain ⟨ρ₀, hρ₀inj, hρ₀comm, hρ₀cent, hρ₀dec, hρ₀last, hρ₀map⟩ :=
    exists_line_frames_h0 hk3 h3 h4 hω3 hω1 hEab hEd hsig
  have hεh1 : εh ≠ 1 := by
    intro h1
    apply conj_e6LineElt_ne_one hω1
    rw [← hεh, h1, map_one]
  have hcard27E : Nat.card E = 27 := by rw [hcard]; norm_num
  obtain ⟨ρ, hρcomp, hρle⟩ :=
    exists_lift_layer_le_seitzHyperGamma (π := π) (E := E) (ρ₀ := ρ₀) (σ := εh)
      h3 h4 hπ hker ind hind hE hcard27E hρ₀inj hρ₀comm hεhE hεh1
      (fun i a => by rw [hεh]; exact hρ₀cent i a)
      (fun ε hεE => hρ₀dec (ind ε) (Subgroup.mem_map_of_mem ind hεE))
  let M : Subgroup (adjointGroup Tag.E6 k) := (seitzHyperGamma 3 E).map π
  have hfac : ∀ i : Fin 3, e6LineFactor k i ≤
      M.map (adjointGroup Tag.E6 k).subtype := by
    intro i y hy
    rw [← hρ₀map i] at hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨a, rfl⟩ := hw
    refine Subgroup.mem_map.2 ⟨π (ρ i a), Subgroup.mem_map_of_mem π (hρle i ⟨a, rfl⟩), ?_⟩
    exact congrArg Subtype.val (DFunLike.congr_fun (hρcomp i) a)
  have hX : rootSpan .E6 k (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) ≤
      M.map (adjointGroup Tag.E6 k).subtype := by
    change (⨆ α ∈ (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))),
      rootSubgroup .E6 k α) ≤ M.map (adjointGroup Tag.E6 k).subtype
    refine iSup_le fun α => ?_
    refine iSup_le fun hα => ?_
    obtain ⟨i, hαi⟩ := Set.mem_iUnion.1 hα
    exact (le_iSup₂_of_le α hαi le_rfl).trans (hfac i)
  obtain ⟨σ, y, b', hyΓ, hPmat⟩ :=
    e6BadCube_fixed_point hperf hk3 h3 h4 θ hE hcard hω3 hω1 hEc
  have hPmat' : (π (σ y) : ModGL .E6 k) =
      (weylWordElt .E6 k e6BadNWord : ModGL .E6 k) * rootDiagUnit .E6 b' := hPmat
  let D' : ModGL Tag.E6 k := rootDiagUnit .E6 b'
  have hconj : (rootSpan .E6 k (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)))).map
      (MulAut.conj ((weylWordElt .E6 k e6BadNWord : adjointGroup Tag.E6 k) :
        ModGL .E6 k)).toMonoidHom ≤ M.map (adjointGroup Tag.E6 k).subtype := by
    intro w hw
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.1 hw
    have hm : D'⁻¹ * y0 * D' ∈
        rootSpan .E6 k (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) := by
      show (rootDiagUnit .E6 b')⁻¹ * y0 * rootDiagUnit .E6 b' ∈ rootSpan .E6 k _
      simpa only [rootDiagUnit_inv, inv_inv] using
        rootDiagUnit_conj_mem_e6LineSpan (K := k) b'⁻¹ hy0
    let mC : adjointGroup Tag.E6 k := ⟨D'⁻¹ * y0 * D', rootSpan_le_adjointGroup k _ hm⟩
    have hmC : mC ∈ M := by
      obtain ⟨m', hm', hcoe⟩ := Subgroup.mem_map.1 (hX hm)
      have heq : m' = mC := Subtype.ext hcoe
      rwa [heq] at hm'
    have hPmem : π (σ y) ∈ M := Subgroup.mem_map_of_mem π hyΓ
    have hconjM : MulAut.conj (π (σ y)) mC ∈ M := by
      rw [MulAut.conj_apply]
      exact Subgroup.mul_mem M (Subgroup.mul_mem M hPmem hmC) (Subgroup.inv_mem M hPmem)
    refine Subgroup.mem_map.2 ⟨MulAut.conj (π (σ y)) mC, hconjM, ?_⟩
    show ((MulAut.conj (π (σ y)) mC : adjointGroup Tag.E6 k) : ModGL .E6 k) =
      (weylWordElt .E6 k e6BadNWord : ModGL .E6 k) * y0 *
        (weylWordElt .E6 k e6BadNWord : ModGL .E6 k)⁻¹
    rw [MulAut.conj_apply]
    change (π (σ y) : ModGL .E6 k) * ((mC : adjointGroup Tag.E6 k) : ModGL .E6 k) *
        ((π (σ y) : ModGL .E6 k))⁻¹ =
      (weylWordElt .E6 k e6BadNWord : ModGL .E6 k) * y0 *
        (weylWordElt .E6 k e6BadNWord : ModGL .E6 k)⁻¹
    rw [show ((mC : adjointGroup Tag.E6 k) : ModGL .E6 k) = D'⁻¹ * y0 * D' from rfl,
      hPmat']
    show (weylWordElt .E6 k e6BadNWord : ModGL .E6 k) * D' * (D'⁻¹ * y0 * D') *
      ((weylWordElt .E6 k e6BadNWord : ModGL .E6 k) * D')⁻¹ = _
    group
  have hMtop : M = ⊤ :=
    eq_top_of_e6A2_le_of_conj_le M hX e6BadNWord e6BadNWord_moves hconj
  have hmap_top : (seitzHyperGamma 3 E).map π = ⊤ := hMtop
  refine seitzHyperGamma_eq_top_of_layers hperf hπ hker (fun _ : Unit => seitzHyperGamma 3 E)
    (fun _ => le_rfl) ?_
  rw [show (⨆ _ : Unit, (seitzHyperGamma 3 E).map π) = ⊤ by
    rw [iSup_const, hmap_top]]

theorem coverE6DiagNotAll24_holds : CoverE6DiagNotAll24 := by
  intro K _ _ hperf k _ _ hk3 h3 h4 θ E hE hcard hEd hEi hn hA
  have hcardĒ : Nat.card (coverImage θ E) = 3 ^ 3 := by
    rw [card_coverImage hperf θ E, hcard]
  have hNF := e6ThreeNotAll24NF_of_parts
    (e6ThreeNotAll24NFA_of_census (e6NotAll24Census_of_OA e6Cen_OA))
    e6ThreeNotAll24NFB1_holds e6BadCube_of_monomial
  obtain ⟨ω, c, φ, hω3, hω1, hmap⟩ :=
    hNF k hk3 h3 h4 (coverImage θ E) (isElemAbelian_coverImage θ hE) hcardĒ hEd hEi hn hA
  have hEc : coverImage (θ.trans φ) E = e6BadCube k ω c := by
    rw [coverImage_trans, hmap]
  exact seitzHyperGamma_eq_top_of_coverImage_eq_e6BadCube hperf hk3 h3 h4 (θ.trans φ)
    hE hcard hω3 hω1 hEc

end CFSG.LieType.SeitzGeneration.CubeCoverE6

end
