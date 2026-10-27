module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.FusionControl
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups Pointwise

private theorem map_eq_one_of_isPerfect_of_isSolvable {A B : Type*} [Group A] [Group B]
    [Group.IsPerfect A] [Group.IsSolvable B] (f : A →* B) (a : A) : f a = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  exact congrArg Subtype.val (Subsingleton.elim (⟨f a, a, rfl⟩ : f.range) 1)

theorem isCatalogGroup_psl_two_galoisField_two {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    IsCatalogGroup PSL(2, GaloisField p 2) := by
  let q : TauCeti.PrimePower := ⟨p, 2, Fact.out, by norm_num⟩
  have h25 : 25 ≤ p ^ 2 := by nlinarith
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [TauCeti.PrimePower.card_def, q]
    omega
  exact ⟨.lie ⟨_, hv⟩, ⟨(CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).symm⟩⟩

variable {G : Type} [Group G] [Finite G]

section Setup

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen5_centralizer_le_normalizer (x : G) :
    centralizer ({x} : Set G) ≤ normalizer ((gen5L x : Subgroup G) : Set G) :=
  le_normalizer_rankThreeLayer _

theorem gen5_sylow_isMulCommutative (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    (Q : Sylow p G) : IsMulCommutative (Q : Subgroup G) := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  have hPab := (gen5_P_abelian hG hl).2
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  have hmem : ∀ y : G, y ∈ ((g • P : Sylow p G) : Subgroup G) ↔
      g⁻¹ * y * g ∈ (P : Subgroup G) := fun y => by
    change y ∈ MulAut.conj g • (P : Subgroup G) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h := hPab.is_comm.comm ⟨_, (hmem a).mp a.2⟩ ⟨_, (hmem b).mp b.2⟩
  have h2 : g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * b * g * (g⁻¹ * a * g) := congrArg Subtype.val h
  have h3 : g * (g⁻¹ * a * g * (g⁻¹ * b * g)) * g⁻¹ =
      g * (g⁻¹ * b * g * (g⁻¹ * a * g)) * g⁻¹ := by rw [h2]
  simpa [mul_assoc] using h3

theorem gen5_pgroup (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    {Q : Subgroup G} (hQ : IsPGroup p Q) :
    IsMulCommutative Q ∧ CFSG.Open.pRank p Q ≤ 3 := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  have hSab := gen5_sylow_isMulCommutative hG hl S
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · have h := hSab.is_comm.comm ⟨a, hQS a.2⟩ ⟨b, hQS b.2⟩
    have h2 := congrArg Subtype.val h
    exact h2
  · exact (pRank_mono p (gen5_prime hl).one_lt le_top).trans
      (pRank_top_le_three hG.setting hl.sigma hl.core)

theorem gen5_Z (hG : Gen5Global G) (hl : Gen5Local G p P M x) :
    x ∈ centralizer ((gen5L x : Subgroup G) : Set G) ∧
      ¬ 2 ∣ Nat.card (centralizer ((gen5L x : Subgroup G) : Set G)) ∧
      ∀ A : Subgroup G, IsPGroup p A → A ≤ centralizer ((gen5L x : Subgroup G) : Set G) →
        IsCyclic A := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨e⟩ := gen5_psl hG hl
  refine ⟨mem_centralizer_iff.mpr fun l hl' =>
    mem_centralizer_singleton_iff.mp (rankThreeLayer_le _ hl'), ?_, fun A hA hAL => ?_⟩
  · exact not_two_dvd_card_centralizer_layer hG.setting hG.d1 hG.d2 hG.u0 hG.layer hl.sigma
      hl.core hl.fail hl.larger hl.generic
  · exact isCyclic_of_isPGroup_of_le_centralizer_layer hG.setting hl.sigma hl.core hl.generic
      le_rfl e hA hAL

theorem gen5_Z_le (hG : Gen5Global G) (hl : Gen5Local G p P M x) :
    centralizer ((gen5L x : Subgroup G) : Set G) ≤ M := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨e⟩ := gen5_psl hG hl
  exact centralizer_layer_le hG.setting hG.u0 hl.sigma hl.core hl.generic le_rfl e

theorem gen5_P_decomp (hG : Gen5Global G) (hl : Gen5Local G p P M x) :
    (P : Subgroup G) = gen5U (P : Subgroup G) x ⊔ ((P : Subgroup G) ⊓
      centralizer ((gen5L x : Subgroup G) : Set G)) ∧
    gen5U (P : Subgroup G) x ⊓ centralizer ((gen5L x : Subgroup G) : Set G) = ⊥ ∧
    IsCyclic ↥((P : Subgroup G) ⊓ centralizer ((gen5L x : Subgroup G) : Set G)) ∧
    ∀ y ∈ (P : Subgroup G) ⊓ centralizer ((gen5L x : Subgroup G) : Set G),
      y ≠ 1 → y ^ p = 1 → zpowers y = zpowers x := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨e⟩ := gen5_psl hG hl
  have hK : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hU := gen5_sylow hG hl
  obtain ⟨hPx, hPab⟩ := gen5_P_abelian hG hl
  obtain ⟨hxZ, -, hZcyc⟩ := gen5_Z hG hl
  have hcyc : IsCyclic ↥((P : Subgroup G) ⊓ centralizer ((gen5L x : Subgroup G) : Set G)) :=
    hZcyc _ P.isPGroup'.to_inf_left inf_le_right
  refine ⟨le_antisymm ?_ (sup_le inf_le_left inf_le_left), ?_, hcyc, ?_⟩
  · intro g hg
    have hgU : ∀ u ∈ gen5U (P : Subgroup G) x, g * u = u * g := fun u hu => by
      have h := hPab.is_comm.comm ⟨g, hg⟩ ⟨u, hu.1⟩
      have h2 := congrArg Subtype.val h
      exact h2
    obtain ⟨u₀, hu₀U, hu₀⟩ := exists_conj_eq_of_centralizes_isSylowOf_psl hK e hU
      (gen5_centralizer_le_normalizer x (hPx hg)) hgU
    have hz : u₀⁻¹ * g ∈ centralizer ((gen5L x : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro l hl'
      have h2 := hu₀ l hl'
      calc l * (u₀⁻¹ * g) = u₀⁻¹ * (u₀ * l * u₀⁻¹) * g := by group
        _ = u₀⁻¹ * (g * l * g⁻¹) * g := by rw [h2]
        _ = u₀⁻¹ * g * l := by group
    have hz' : u₀⁻¹ * g ∈ (P : Subgroup G) ⊓ centralizer ((gen5L x : Subgroup G) : Set G) :=
      ⟨(P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hu₀U.1) hg, hz⟩
    have h := mul_mem_sup hu₀U hz'
    rwa [mul_inv_cancel_left] at h
  · refine eq_bot_iff.mpr fun y hy => (mem_bot).mpr ?_
    exact eq_one_of_commute_of_mulEquiv_psl_two e hy.1.2 fun h hh =>
      mem_centralizer_iff.mp hy.2 h hh
  · intro y hy hy1 hyp
    obtain ⟨hxP, ⟨-, hx1, hxp, -, -⟩, -, -⟩ := hl.generic
    have hxA : x ∈ (P : Subgroup G) ⊓ centralizer ((gen5L x : Subgroup G) : Set G) :=
      ⟨hxP, hxZ⟩
    have heq : zpowers (⟨y, hy⟩ : ↥((P : Subgroup G) ⊓
        centralizer ((gen5L x : Subgroup G) : Set G))) = zpowers ⟨x, hxA⟩ := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
        Subgroup.orderOf_mk, Subgroup.orderOf_mk, orderOf_eq_prime hyp hy1,
        orderOf_eq_prime hxp hx1]
    have h := congrArg (Subgroup.map ((P : Subgroup G) ⊓
      centralizer ((gen5L x : Subgroup G) : Set G)).subtype) heq
    rwa [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h

theorem gen5_weakly_closed_P (hG : Gen5Global G) (hl : Gen5Local G p P M x) {h : G}
    (hh : h * x * h⁻¹ ∈ (P : Subgroup G)) : zpowers (h * x * h⁻¹) = zpowers x := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨hU, -, hPab⟩ := generic_central_abelian hG.setting hG.d1 hG.u0 hG.layer hl.sigma
    hl.core hl.fail hl.larger hl.generic
  obtain ⟨hxP, hxL, -, -⟩ := hl.generic
  have hg : (zpowers x).map (MulAut.conj h⁻¹⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rw [inv_inv, MonoidHom.map_zpowers, zpowers_le]
    exact hh
  obtain ⟨c, hcM, hc⟩ := exists_mem_conj_eq_of_map_le hG.setting hG.u0 hl.sigma hl.core
    (zpowers_le.mpr hxP) hg
  have hy : h * x * h⁻¹ = MulAut.conj c⁻¹ x := by
    have h1 := hc x (mem_zpowers x)
    rw [inv_inv] at h1
    rw [MulAut.conj_apply, inv_inv, h1]
  obtain ⟨-, hy1, hyp, -, hyM⟩ := hxL.conj (M.inv_mem hcM)
  rw [← hy] at hy1 hyp hyM
  have hyx : h * x * h⁻¹ ∈ zpowers x := by
    by_contra hyx
    exact hyM (centralizer_le_of_not_mem_zpowers hG.setting hl.sigma hl.core hU hPab hh hy1
      hyp hyx)
  have hXc : Nat.card (zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxL.2.2.1 hxL.2.1]
  exact (eq_zpowers_of_card_eq_prime hXc hyx hy1).symm

theorem gen5_weakly_closed (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    (Q : Sylow p G) (hxQ : x ∈ (Q : Subgroup G)) (g : G)
    (hg : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G)) :
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  have hsylG : ∀ S : Sylow p G, IsSylowOf p (S : Subgroup G) ⊤ := fun S =>
    isSylowOf_iff.2 ⟨le_top, S.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact S.not_dvd_index⟩
  have hQC : (Q : Subgroup G) ≤ centralizer ({x} : Set G) := fun q hq => by
    rw [mem_centralizer_singleton_iff]
    have h := (gen5_sylow_isMulCommutative hG hl Q).is_comm.comm ⟨q, hq⟩ ⟨x, hxQ⟩
    have h2 := congrArg Subtype.val h
    exact h2
  obtain ⟨k, hkC, hk⟩ := ((hsylG P).of_le (gen5_P_abelian hG hl).1 le_top).exists_mem_conj
    ((hsylG Q).of_le hQC le_top)
  have hyQ : g * x * g⁻¹ ∈ (Q : Subgroup G) := by
    have h := hg (mem_map_of_mem (MulAut.conj g).toMonoidHom (mem_zpowers x))
    simpa using h
  have hP : (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ ∈ (P : Subgroup G) := by
    have h := (hk _).mp hyQ
    have he : (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k := by group
    rw [he]
    exact h
  have h1 := gen5_weakly_closed_P hG hl hP
  have hkx : k * x * k⁻¹ = x := by
    rw [mem_centralizer_singleton_iff] at hkC
    rw [hkC, mul_inv_cancel_right]
  have key : ∀ y : G, zpowers (k * y * k⁻¹) = (zpowers y).map (MulAut.conj k).toMonoidHom :=
    fun y => by
      rw [MonoidHom.map_zpowers]
      rfl
  calc (zpowers x).map (MulAut.conj g).toMonoidHom
      = zpowers (k * ((k⁻¹ * g) * x * (k⁻¹ * g)⁻¹) * k⁻¹) := by
        rw [MonoidHom.map_zpowers]
        congr 1
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    _ = (zpowers ((k⁻¹ * g) * x * (k⁻¹ * g)⁻¹)).map (MulAut.conj k).toMonoidHom := key _
    _ = (zpowers x).map (MulAut.conj k).toMonoidHom := by rw [h1]
    _ = zpowers (k * x * k⁻¹) := (key x).symm
    _ = zpowers x := by rw [hkx]

theorem gen5_perfect_le (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    (Sch : KFactCatalogSchreier) {J : Subgroup G} (hJ : J ≤ centralizer ({x} : Set G))
    (hJp : ⁅J, J⁆ = J) : J ≤ gen5L x := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨e⟩ := gen5_psl hG hl
  have hK4 : 4 ≤ Nat.card (GaloisField p 2) := by
    rw [GaloisField.card p 2 (by norm_num)]
    nlinarith [gen5_five_le hG hl]
  have : IsSimpleGroup PSL(2, GaloisField p 2) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK4
  have hLs : IsSimpleGroup (gen5L x) := e.isSimpleGroup
  have hZL : ∀ l : gen5L x, (∀ m : gen5L x, m * l = l * m) → l = 1 := fun l hl' =>
    Subtype.ext (eq_one_of_commute_of_mulEquiv_psl_two e l.2 fun h hh =>
      congrArg Subtype.val (hl' ⟨h, hh⟩))
  have hnab : ∃ a b : gen5L x, a * b ≠ b * a := by
    by_contra h
    push Not at h
    obtain ⟨l, hl1⟩ := exists_ne (1 : gen5L x)
    exact hl1 (hZL l fun m => h m l)
  have hcat : IsCatalogGroup (gen5L x) := by
    obtain ⟨i, ⟨f⟩⟩ := isCatalogGroup_psl_two_galoisField_two (gen5_five_le hG hl)
    exact ⟨i, ⟨e.trans f⟩⟩
  have : Group.IsSolvable (Outer (gen5L x)) := Sch _ hLs hnab hcat
  have hinj : Function.Injective (MulAut.conj : gen5L x →* MulAut (gen5L x)) := by
    rw [injective_iff_map_eq_one]
    intro l hl'
    refine hZL l fun m => ?_
    have h := congrArg (fun φ : MulAut (gen5L x) => φ m) hl'
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hJN : J ≤ normalizer ((gen5L x : Subgroup G) : Set G) :=
    hJ.trans (gen5_centralizer_le_normalizer x)
  let ρ : J →* MulAut (gen5L x) := (gen5L x).normalizerMonoidHom.comp (Subgroup.inclusion hJN)
  have : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJp
  have hρ0 : ∀ j : J, ρ j ∈ inner (gen5L x) := fun j =>
    (QuotientGroup.eq_one_iff _).mp
      (map_eq_one_of_isPerfect_of_isSolvable ((QuotientGroup.mk' (inner (gen5L x))).comp ρ) j)
  have hρ : ∀ j : J, ρ j ∈ (MulAut.conj : gen5L x →* MulAut (gen5L x)).range := hρ0
  let ℓ : J →* gen5L x := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (ρ.codRestrict _ hρ)
  have hℓ : ∀ j : J, ∀ m ∈ gen5L x,
      (ℓ j : G) * m * (ℓ j : G)⁻¹ = (j : G) * m * (j : G)⁻¹ := by
    intro j m hm
    have h : MulAut.conj (ℓ j) = ρ j := by
      have h0 := congrArg Subtype.val ((MonoidHom.ofInjective hinj).apply_symm_apply
        (ρ.codRestrict _ hρ j))
      rw [MonoidHom.ofInjective_apply] at h0
      exact h0
    have h2 := congrArg (fun φ : MulAut (gen5L x) => ((φ ⟨m, hm⟩ : gen5L x) : G)) h
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [h2]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hμ : ∀ j : J, (ℓ j : G)⁻¹ * j ∈ centralizer ((gen5L x : Subgroup G) : Set G) := by
    intro j
    rw [mem_centralizer_iff]
    intro m hm
    have h2 := hℓ j m hm
    calc m * ((ℓ j : G)⁻¹ * j) = (ℓ j : G)⁻¹ * ((ℓ j : G) * m * (ℓ j : G)⁻¹) * j := by group
      _ = (ℓ j : G)⁻¹ * ((j : G) * m * (j : G)⁻¹) * j := by rw [h2]
      _ = (ℓ j : G)⁻¹ * j * m := by group
  let μ : J →* centralizer ((gen5L x : Subgroup G) : Set G) :=
    MonoidHom.mk' (fun j => ⟨(ℓ j : G)⁻¹ * j, hμ j⟩) fun a b => by
      apply Subtype.ext
      have hc : (ℓ b : G)⁻¹ * ((ℓ a : G)⁻¹ * a) = (ℓ a : G)⁻¹ * a * (ℓ b : G)⁻¹ :=
        mem_centralizer_iff.mp (hμ a) _ (inv_mem (ℓ b).2)
      simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
      calc (ℓ b : G)⁻¹ * (ℓ a : G)⁻¹ * (a * b) = (ℓ b : G)⁻¹ * ((ℓ a : G)⁻¹ * a) * b := by
            group
        _ = (ℓ a : G)⁻¹ * a * (ℓ b : G)⁻¹ * b := by rw [hc]
        _ = (ℓ a : G)⁻¹ * a * ((ℓ b : G)⁻¹ * b) := by group
  have : Group.IsSolvable (centralizer ((gen5L x : Subgroup G) : Set G)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (gen5_Z hG hl).2.1))
  intro j hj
  have h1 := congrArg Subtype.val (map_eq_one_of_isPerfect_of_isSolvable μ ⟨j, hj⟩)
  have h2 : (ℓ ⟨j, hj⟩ : G)⁻¹ * j = 1 := h1
  rw [inv_mul_eq_one] at h2
  exact h2 ▸ (ℓ ⟨j, hj⟩).2

end Setup

end CFSG.LocalAnalysis.RankThreeTheoremC
