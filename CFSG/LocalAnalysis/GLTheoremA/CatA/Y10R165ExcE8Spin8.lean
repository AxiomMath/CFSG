module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Spin7
public import CFSG.LieType.AlgebraicGroups.KernelRootDescent
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Spin3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Spin6

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE
open scoped MatrixGroups Pointwise

@[expose] def d6zRoots : Set (Fin Tag.E8.rank → ℤ) :=
  {α | IsRoot .E8 α ∧ 2 * α 4 = α 3 + α 5 ∧ 2 * α 1 = α 3}

section Pair

private theorem d6Pair_iff :
    ∀ α ∈ rootFinset .E8, ((∀ j : Fin 4, iform (e8D4LeviSimple j) α = 0) ↔
      (α 1 + α 2 - α 0 - α 4 = 0 ∧ 2 * α 3 - α 1 - α 2 - α 4 = 0 ∧
        2 * α 4 - α 3 - α 5 = 0 ∧ 2 * α 1 - α 3 = 0)) := by
  decide +kernel

end Pair

section Family

private theorem familyKernel_pair_eq_inter {L : Type} [Field L]
    (a b : Fin Tag.E8.rank → Lˣ) :
    familyKernel (![a, b] : Fin 2 → Fin Tag.E8.rank → Lˣ) =
      rootCharKernel a ∩ rootCharKernel b := by
  ext α
  simp only [familyKernel, rootCharKernel, Set.mem_setOf_eq, Set.mem_inter_iff,
    Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  tauto

theorem familyKernel_d6Pair {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Lˣ} (hζo : orderOf ζ = p) {lam : ZMod p} (hlam : lam * lam = -1)
    {b : Fin Tag.E8.rank → Lˣ} (hb : rootCharKernel b = d6zRoots) :
    familyKernel (![ExcE8Four.d6TorsionChar p ζ lam, b] : Fin 2 → Fin Tag.E8.rank → Lˣ) =
      e8D4PerpRoots := by
  rw [familyKernel_pair_eq_inter, ExcE8Four.rootCharKernel_d6TorsionChar hp hp2 hζo hlam, hb]
  ext α
  simp only [ExcE8Four.d6Roots, d6zRoots, e8D4PerpRoots, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hα, h1, h2⟩, -, h3, h4⟩
    exact ⟨hα, (d6Pair_iff α (mem_rootFinset.2 hα)).2
      ⟨by omega, by omega, by omega, by omega⟩⟩
  · rintro ⟨hα, horth⟩
    obtain ⟨hA, hB, hC, hD⟩ := (d6Pair_iff α (mem_rootFinset.2 hα)).1 horth
    exact ⟨⟨hα, by omega, by omega⟩, ⟨hα, by omega, by omega⟩⟩

theorem rootCharKernel_eq_d6zRoots_of_rootChar {L : Type} [Field L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : Lˣ} (hζo : orderOf ζ = p) {lam : ZMod p} (hlam : lam * lam = -1)
    {b : Fin Tag.E8.rank → Lˣ}
    (hb : ∀ α, rootChar b α =
      ζ ^ ((2 * α 4 - α 3 - α 5) + (2 * α 1 - α 3) * (lam.val : ℤ)))
    (hbd : ∀ α ∈ rootFinset .E8,
      (2 * α 4 - α 3 - α 5) ^ 2 + (2 * α 1 - α 3) ^ 2 ≤ 4) :
    rootCharKernel b = d6zRoots := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h5 : 5 ≤ p := by
    refine hp.five_le_of_ne_two_of_ne_three hp2 ?_
    intro h3
    have h4 : p % 4 ≠ 3 :=
      ZMod.mod_four_ne_three_of_sq_eq_neg_one (y := lam) (by rw [pow_two]; exact hlam)
    rw [h3] at h4
    exact h4 (by norm_num)
  have hz : ∀ n : ℤ, ζ ^ n = 1 ↔ ((n : ℤ) : ZMod p) = 0 := fun n => by
    rw [← orderOf_dvd_iff_zpow_eq_one, hζo, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  ext α
  show (IsRoot .E8 α ∧ rootChar b α = 1) ↔
    (IsRoot .E8 α ∧ 2 * α 4 = α 3 + α 5 ∧ 2 * α 1 = α 3)
  refine and_congr_right fun hα => ?_
  rw [hb α, hz]
  constructor
  · intro h
    have h' : ((2 * α 4 - α 3 - α 5 : ℤ) : ZMod p) +
        ((2 * α 1 - α 3 : ℤ) : ZMod p) * lam = 0 := by
      have hh := h
      push_cast at hh
      rw [ZMod.natCast_zmod_val] at hh
      push_cast
      exact hh
    have hb' := ExcE8Four.int_add_mul_eq_zero hp h5 hlam (hbd α (mem_rootFinset.2 hα)) h'
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    have hC : 2 * α 4 - α 3 - α 5 = 0 := by omega
    have hD : 2 * α 1 - α 3 = 0 := by omega
    have hE : (2 * α 4 - α 3 - α 5) + (2 * α 1 - α 3) * (lam.val : ℤ) = 0 := by
      rw [hC, hD]
      ring
    rw [hE]
    simp

end Family

section Normalizer

theorem familyCentralizer_le_normalizer_rootSpan {L : Type} [Field L] {ι : Type}
    (a : ι → Fin Tag.E8.rank → Lˣ) :
    familyCentralizer Tag.E8 L a ≤
      Subgroup.normalizer (rootSpan Tag.E8 L (familyKernel a) : Set (ModGL Tag.E8 L)) := by
  intro g hg
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul Tag.E8 L a hg
  exact mul_mem (familyGroup_le_normalizer_rootSpan (K := L) a hm)
    (canonicalRep_mem_normalizer_rootSpan_of_mem_familyStabilizer (K := L) hw)

end Normalizer

section PerpChar

private def perpCharAdd : (Fin Tag.E8.rank → ℤ) →+ (Fin 4 → ℤ) where
  toFun v j := iform (e8D4LeviSimple j) v
  map_zero' := by ext j; simp [iform]
  map_add' x y := by ext j; exact iform_add_right _ _ _

private def perpChar : Multiplicative (Fin Tag.E8.rank → ℤ) →* Multiplicative (Fin 4 → ℤ) :=
  AddMonoidHom.toMultiplicative perpCharAdd

private theorem kernelRoots_perpChar : kernelRoots perpChar = e8D4PerpRoots := by
  ext α
  simp [kernelRoots, perpChar, perpCharAdd, e8D4PerpRoots, funext_iff]

end PerpChar

private theorem coprime_two_card_sub_one (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nat.Coprime 2 (Nat.card K - 1) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 := by rw [ringChar.eq]
  have hcard2 : 2 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have heven : Nat.card K % 2 = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.even_card_of_char_two hchar
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero heven
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm; omega
    · exact h
  refine Nat.coprime_two_left.mpr ⟨m - 1, ?_⟩
  omega

section Conj

theorem conj_mem_rootSpan_perp_of_normalizer {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Field L] [Algebra K L] {c : ModGL .E8 K} (hc : c ∈ adjointGroup .E8 K)
    (hcL : baseChangeGL (algebraMap K L) c ∈
      Subgroup.normalizer (rootSpan .E8 L e8D4PerpRoots : Set (ModGL .E8 L)))
    {y : ModGL .E8 K} (hy : y ∈ rootSpan .E8 K e8D4PerpRoots) :
    c * y * c⁻¹ ∈ rootSpan .E8 K e8D4PerpRoots := by
  have hgen : ∀ β ∈ e8D4PerpRoots, ∀ t : K,
      c * pinnedX Tag.E8 K β t * c⁻¹ ∈ rootSpan Tag.E8 K e8D4PerpRoots := by
    intro β hβ t
    have hpair : pinnedX Tag.E8 K β t ∈ rootSubgroup Tag.E8 K β :=
      Subgroup.subset_closure ⟨t, rfl⟩
    have huA : c * pinnedX Tag.E8 K β t * c⁻¹ ∈ adjointGroup .E8 K :=
      mul_mem (mul_mem hc (rootSubgroup_le_adjointGroup β hpair)) (inv_mem hc)
    have hbc : baseChangeGL (algebraMap K L) (c * pinnedX Tag.E8 K β t * c⁻¹) ∈
        rootSpan Tag.E8 L e8D4PerpRoots := by
      rw [map_mul, map_mul, map_inv, baseChangeGL_pinnedX]
      exact (Subgroup.mem_normalizer_iff.1 hcL _).1
        (pinnedX_mem_rootSpan hβ (algebraMap K L t))
    have hdes : c * pinnedX Tag.E8 K β t * c⁻¹ ∈
        torusGroup Tag.E8 K ⊔ rootSpan Tag.E8 K (kernelRoots perpChar) :=
      mem_torus_sup_rootSpan_of_baseChangeGL_mem (algebraMap K L) perpChar huA
        (by simpa only [kernelRoots_perpChar] using Subgroup.mem_sup_right hbc)
    rw [kernelRoots_perpChar] at hdes
    have h2 : (c * pinnedX Tag.E8 K β t * c⁻¹) ^ 2 = 1 := by
      have hpv : pinnedX Tag.E8 K β t ^ 2 = 1 := ExcHighThree.pinnedX_pow_char 2 β t
      calc (c * pinnedX Tag.E8 K β t * c⁻¹) ^ 2
          = (c * pinnedX Tag.E8 K β t * c⁻¹) * (c * pinnedX Tag.E8 K β t * c⁻¹) := by
            rw [pow_two]
        _ = c * (pinnedX Tag.E8 K β t * pinnedX Tag.E8 K β t) * c⁻¹ := by group
        _ = c * pinnedX Tag.E8 K β t ^ 2 * c⁻¹ := by rw [pow_two]
        _ = 1 := by rw [hpv, mul_one, mul_inv_cancel]
    exact mem_rootSpan_of_mem_torus_sup_of_pow_eq_one (fun γ hγ => hγ.1)
      (coprime_two_card_sub_one K) hdes h2
  have hmap : rootSpan Tag.E8 K e8D4PerpRoots ≤
      Subgroup.comap (MulAut.conj c).toMonoidHom
        (rootSpan Tag.E8 K e8D4PerpRoots) := by
    refine iSup₂_le fun β hβ => ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨t, rfl⟩
    exact Subgroup.mem_comap.2 (hgen β hβ t)
  exact Subgroup.mem_comap.1 (hmap hy)

end Conj

section Layer

variable {K L : Type} [Field K] [Finite K] [CharP K 2] [Field L] [Algebra K L]

private theorem adjEmb_mem_normalizer_perp_of_mem_centralizers {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Lˣ} (hζo : orderOf ζ = p) {lam : ZMod p} (hlam : lam * lam = -1)
    {g : ModGL .E8 L}
    (hgM : g ∈ torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d4d4Char))
    (hgN : g ∈ Subgroup.normalizer (rootSpan .E8 L e8D4PerpRoots : Set (ModGL .E8 L)))
    {x z : adjointGroup .E8 K} {b : Fin Tag.E8.rank → Lˣ}
    (hx : adjEmb .E8 K L x =
      g * rootDiagUnit .E8 (ExcE8Four.d6TorsionChar p ζ lam) * g⁻¹)
    (hz : adjEmb .E8 K L z = g * rootDiagUnit .E8 b * g⁻¹)
    (hb : rootCharKernel b = d6zRoots)
    {c : adjointGroup .E8 K}
    (hcx : c ∈ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)))
    (hcz : c ∈ Subgroup.centralizer ({z} : Set (adjointGroup .E8 K))) :
    adjEmb .E8 K L c ∈
      Subgroup.normalizer (rootSpan .E8 L e8D4PerpRoots : Set (ModGL .E8 L)) := by
  classical
  set a : Fin Tag.E8.rank → Lˣ := ExcE8Four.d6TorsionChar p ζ lam with ha
  have hgA : g ∈ adjointGroup .E8 L :=
    (sup_le torusGroup_le_adjointGroup (rootSpan_le_adjointGroup L _)) hgM
  set y : ModGL .E8 L := g⁻¹ * adjEmb .E8 K L c * g with hy
  have hyA : y ∈ adjointGroup .E8 L :=
    mul_mem (mul_mem (inv_mem hgA) (adjEmb_mem c)) hgA
  have hcomm : ∀ (w : adjointGroup .E8 K) (d : ModGL .E8 L),
      adjEmb .E8 K L w = g * d * g⁻¹ → c * w = w * c →
      y * d = d * y := by
    intro w d hd hcw
    have hdw : g⁻¹ * adjEmb .E8 K L w * g = d := by rw [hd]; group
    have hcc : adjEmb .E8 K L c * adjEmb .E8 K L w = adjEmb .E8 K L w * adjEmb .E8 K L c := by
      rw [← map_mul, ← map_mul, hcw]
    calc y * d = g⁻¹ * (adjEmb .E8 K L c * adjEmb .E8 K L w) * g := by
          rw [hy, ← hdw]; group
      _ = g⁻¹ * (adjEmb .E8 K L w * adjEmb .E8 K L c) * g := by rw [hcc]
      _ = d * y := by rw [hy, ← hdw]; group
  have hyF : y ∈ familyCentralizer Tag.E8 L
      (![a, b] : Fin 2 → Fin Tag.E8.rank → Lˣ) := by
    rw [mem_familyCentralizer]
    refine ⟨hyA, ?_⟩
    intro i
    have key : ∀ d : ModGL .E8 L, y * d = d * y → d * y * d⁻¹ = y := by
      intro d hd
      rw [← hd]; group
    have hxa : adjEmb .E8 K L x = g * rootDiagUnit .E8 a * g⁻¹ := by rw [ha]; exact hx
    fin_cases i
    · exact key _ (hcomm x (rootDiagUnit .E8 a) hxa
        (Subgroup.mem_centralizer_singleton_iff.1 hcx))
    · exact key _ (hcomm z (rootDiagUnit .E8 b) hz
        (Subgroup.mem_centralizer_singleton_iff.1 hcz))
  have hyN : y ∈ Subgroup.normalizer
      (rootSpan .E8 L e8D4PerpRoots : Set (ModGL .E8 L)) := by
    have h := familyCentralizer_le_normalizer_rootSpan (![a, b] : Fin 2 → _) hyF
    rwa [familyKernel_d6Pair hp hp2 hζo hlam hb] at h
  have heq : adjEmb .E8 K L c = g * y * g⁻¹ := by rw [hy]; group
  rw [heq]
  exact mul_mem (mul_mem hgN hyN) (inv_mem hgN)

theorem centralizer_inf_le_normalizer_e8D4Perp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Lˣ} (hζo : orderOf ζ = p) {lam : ZMod p} (hlam : lam * lam = -1)
    {g : ModGL .E8 L}
    (hgM : g ∈ torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d4d4Char))
    (hgN : g ∈ Subgroup.normalizer (rootSpan .E8 L e8D4PerpRoots : Set (ModGL .E8 L)))
    {x z : adjointGroup .E8 K} {b : Fin Tag.E8.rank → Lˣ}
    (hx : adjEmb .E8 K L x =
      g * rootDiagUnit .E8 (ExcE8Four.d6TorsionChar p ζ lam) * g⁻¹)
    (hz : adjEmb .E8 K L z = g * rootDiagUnit .E8 b * g⁻¹)
    (hb : rootCharKernel b = d6zRoots) :
    Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) ⊓
        Subgroup.centralizer ({z} : Set (adjointGroup .E8 K)) ≤
      Subgroup.normalizer ((e8D4Perp K : Subgroup (adjointGroup .E8 K)) : Set
        (adjointGroup .E8 K)) := by
  intro c hc
  obtain ⟨hcx, hcz⟩ := Subgroup.mem_inf.1 hc
  have hconv : ∀ {d u : adjointGroup .E8 K},
      d ∈ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) →
      d ∈ Subgroup.centralizer ({z} : Set (adjointGroup .E8 K)) →
      u ∈ e8D4Perp K → d * u * d⁻¹ ∈ e8D4Perp K := by
    intro d u hdx hdz hu
    have hbase : baseChangeGL (algebraMap K L) (d : ModGL .E8 K) ∈
        Subgroup.normalizer (rootSpan .E8 L e8D4PerpRoots : Set (ModGL .E8 L)) := by
      rw [← adjEmb_apply]
      exact adjEmb_mem_normalizer_perp_of_mem_centralizers hp hp2 hζo hlam hgM hgN
        hx hz hb hdx hdz
    have hu' : (u : ModGL .E8 K) ∈ rootSpan Tag.E8 K e8D4PerpRoots := by
      rw [rootSpan_e8D4PerpRoots_eq]
      exact ⟨u, hu, rfl⟩
    have hconj := conj_mem_rootSpan_perp_of_normalizer d.2 hbase hu'
    rw [rootSpan_e8D4PerpRoots_eq] at hconj
    obtain ⟨q, hq, hqeq⟩ := hconj
    have hq' : q = d * u * d⁻¹ := Subtype.ext hqeq
    rwa [hq'] at hq
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact hconv hcx hcz
  · intro hu
    have hinv := hconv (Subgroup.inv_mem _ hcx) (Subgroup.inv_mem _ hcz) hu
    have heq : c⁻¹ * (c * u * c⁻¹) * (c⁻¹)⁻¹ = u := by group
    rwa [heq] at hinv

theorem e8D4Perp_normal_in_inf_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Lˣ} (hζo : orderOf ζ = p) {lam : ZMod p} (hlam : lam * lam = -1)
    {g : ModGL .E8 L}
    (hgM : g ∈ torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d4d4Char))
    (hgN : g ∈ Subgroup.normalizer (rootSpan .E8 L e8D4PerpRoots : Set (ModGL .E8 L)))
    {x z : adjointGroup .E8 K} {b : Fin Tag.E8.rank → Lˣ}
    (hx : adjEmb .E8 K L x =
      g * rootDiagUnit .E8 (ExcE8Four.d6TorsionChar p ζ lam) * g⁻¹)
    (hz : adjEmb .E8 K L z = g * rootDiagUnit .E8 b * g⁻¹)
    (hb : rootCharKernel b = d6zRoots)
    {J : Subgroup (adjointGroup .E8 K)}
    (hJ : J ≤ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)))
    (hQJ : e8D4Perp K ≤ J) (hzL : z ∈ e8D4Levi K) :
    ((e8D4Perp K).subgroupOf
      (J ⊓ Subgroup.centralizer ({z} : Set (adjointGroup .E8 K)))).Normal := by
  have hQz : e8D4Perp K ≤ Subgroup.centralizer ({z} : Set (adjointGroup .E8 K)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (e8D4Perp_le_centralizer_e8D4Levi K hy) z hzL).symm
  have hQle : e8D4Perp K ≤
      J ⊓ Subgroup.centralizer ({z} : Set (adjointGroup .E8 K)) := le_inf hQJ hQz
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQle]
  intro w hw
  exact centralizer_inf_le_normalizer_e8D4Perp hp hp2 hζo hlam hgM hgN hx hz hb
    ⟨hJ hw.1, hw.2⟩

end Layer

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin
