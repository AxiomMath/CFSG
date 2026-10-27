module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inner
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Lemma47

theorem lieModel_of_equiv_psl {Y : Type} [Group Y] {F : Type} [Field F] [Fintype F] {p k : ℕ}
    (hp : p.Prime) (hk : 1 ≤ k) (hF : Fintype.card F = p ^ k) (h4 : 4 ≤ p ^ k)
    (e : Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    Blueprint.LieModel Y .PSL 2 p k := by
  refine Or.inl ⟨by decide, ⟨hp, hk, le_rfl, ?_, ?_⟩, F, inferInstance,
    inferInstance, by rw [Nat.card_eq_fintype_card, hF],
    ⟨e.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F)⟩⟩
  all_goals
    intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

theorem sl2_facts {Y : Type} [Group Y] [Finite Y] {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 1 ≤ k) (h5 : 5 ≤ p ^ k) (hY : IsSLTwoOver (p ^ k) Y) :
    IsQuasisimple Y ∧ Nat.card ↥(center Y) = 2 ∧
      Blueprint.LieModel (Y ⧸ center Y) .PSL 2 p k ∧ pPrimeCore 2 Y = ⊥ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hY
  have hFn : Nat.card F = p ^ k := by rw [Nat.card_eq_fintype_card, hF]
  have hq : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    RankThree.CALinearPlane.isQuasisimple_SL_of_two_le le_rfl (by omega)
  have hYq : IsQuasisimple Y := LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  have hodd : Odd (p ^ k) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hZSL : Nat.card ↥(center (Matrix.SpecialLinearGroup (Fin 2) F)) = 2 := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
      (0 : Fin 2)).toEquiv, Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, Fintype.card_fin,
      hFn]
    obtain ⟨m, hm⟩ := hodd
    rw [hm, Nat.add_sub_cancel]
    exact Nat.gcd_eq_right (dvd_mul_right 2 m)
  have hZmap := OuterAutomorphisms.center_map_equiv e
  have hZY : Nat.card ↥(center Y) = 2 := by
    rw [← hZSL, ← hZmap, Subgroup.card_map_of_injective e.injective]
  refine ⟨hYq, hZY, ?_, ?_⟩
  · have eq : Y ⧸ center Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      QuotientGroup.congr (center Y) (center (Matrix.SpecialLinearGroup (Fin 2) F)) e hZmap
    exact lieModel_of_equiv_psl hp hk hF (by omega) eq
  · have hZ2 : IsPGroup 2 ↥(center Y) := IsPGroup.of_card (n := 1) (by rw [hZY, pow_one])
    exact pPrimeCore_eq_bot_of_surjective_of_isQuasisimple hYq hZ2 (MonoidHom.id Y)
      Function.surjective_id

theorem centralizer_closure_pair {G : Type*} [Group G] (β z : G) :
    centralizer ((closure {β, z} : Subgroup G) : Set G) = centralizer {β} ⊓ centralizer {z} := by
  rw [centralizer_closure]
  ext x
  simp only [mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq, mem_inf]

theorem fourGroup_closure_pair {G : Type*} [Group G] [Finite G] {β z : G} (hβ : orderOf β = 2)
    (hz : orderOf z = 2) (hne : z ≠ β) (hc : β * z = z * β) :
    (∀ a ∈ (closure {β, z} : Subgroup G), a * a = 1) ∧
      Nat.card (closure {β, z} : Subgroup G) = 4 := by
  have hcl : (closure {β, z} : Subgroup G) = zpowers β ⊔ zpowers z := by
    rw [show ({β, z} : Set G) = {β} ∪ {z} from rfl, Subgroup.closure_union,
      ← zpowers_eq_closure, ← zpowers_eq_closure]
  have hc' : ∀ a ∈ zpowers β, a * z = z * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (show Commute β z from hc) n).eq
  have hzβ : z ∉ zpowers β := by
    intro h1
    rcases eq_one_or_eq_of_mem_zpowers_two hβ h1 with h1 | h1
    · rw [h1, orderOf_one] at hz; exact absurd hz (by norm_num)
    · exact hne h1
  have hβE : GrSLit.IsElemTwo (zpowers β) := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · rcases eq_one_or_eq_of_mem_zpowers_two hβ ha with rfl | rfl
      · exact mul_one 1
      · rw [← sq, ← hβ, pow_orderOf_eq_one]
  rw [hcl]
  refine ⟨(isElemTwo_sup_zpowers hβE hc' (by rw [← sq, ← hz, pow_orderOf_eq_one])).2, ?_⟩
  rw [card_sup_zpowers hc' hz hzβ, Nat.card_zpowers, hβ]

theorem exists_lift_two_component {X : Type} [Group X] [Finite X] {β z : X}
    (hzβ : z ∈ centralizer ({β} : Set X)) (hz : orderOf z = 2) {Y : Subgroup (MBar β)}
    (hYle : Y ≤ centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)})
    (hY : IsPComponent 2 (Y.subgroupOf (centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)})))
    (hzY : (QuotientGroup.mk ⟨z, hzβ⟩ : MBar β) ∈ Y) :
    ∃ J : Subgroup X, J ≤ centralizer {β} ⊓ centralizer {z} ∧
      IsPComponent 2 (J.subgroupOf (centralizer {β} ⊓ centralizer {z})) ∧ z ∈ J ∧
      (J.subgroupOf (centralizer {β})).map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer
        ({β} : Set X)))) = Y ∧
      ∃ g : ↥J →* ↥Y, Function.Surjective g ∧ ¬ 2 ∣ Nat.card g.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := centralizer ({β} : Set X)
  let z' : ↥M := ⟨z, hzβ⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let C := centralizer ({z'} : Set ↥M)
  have hz'2 : z' * z' = 1 := Subtype.ext (by
    change z * z = 1
    rw [← sq, ← hz, pow_orderOf_eq_one])
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥M)) := by
    have h2 := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥M)
    rw [QuotientGroup.ker_mk'] at h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have hCmap : C.map π = centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} :=
    map_centralizer_eq hodd hz'2
  let φ : ↥C →* ↥(centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} : Set (MBar β))) :=
    (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hCmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map C.subtype ≤ pPrimeCore 2 ↥M := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π (x : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 ↥M) := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hc))
  obtain ⟨-, hlift, -⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection φ hφs hφk
  obtain ⟨hĴ, hĴmap⟩ := hlift _ hY
  have hCX : C.map M.subtype = centralizer {β} ⊓ centralizer {z} := by
    rw [map_subtype_centralizer hzβ, inf_comm]
  let eC : ↥C ≃* ↥(centralizer ({β} : Set X) ⊓ centralizer {z}) :=
    (C.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hCX)
  generalize hĴdef : closure {x : ↥C | x ∈ (Y.subgroupOf (centralizer
    {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)})).comap φ ∧ ∃ k : ℕ, orderOf x = 2 ^ k} = Ĵ at hĴ hĴmap
  have hzĴ : (⟨z', mem_centralizer_singleton_iff.mpr rfl⟩ : ↥C) ∈ Ĵ := by
    rw [← hĴdef]
    refine subset_closure ⟨?_, 1, ?_⟩
    · exact hzY
    · rw [pow_one, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact hz
  have hJle : (Ĵ.map C.subtype).map M.subtype ≤ centralizer {β} ⊓ centralizer {z} := by
    rw [← hCX]
    exact map_mono (map_subtype_le Ĵ)
  have hJeq : ((Ĵ.map C.subtype).map M.subtype).subgroupOf (centralizer {β} ⊓ centralizer {z}) =
      Ĵ.map eC.toMonoidHom := by
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hyx⟩
      exact ⟨y, hy, Subtype.ext hyx⟩
    · rintro ⟨y, hy, hyx⟩
      have h1 : ((eC y : ↥(centralizer ({β} : Set X) ⊓ centralizer {z})) : X) = x :=
        congrArg Subtype.val hyx
      exact ⟨(y : ↥M), ⟨y, hy, rfl⟩, h1⟩
  refine ⟨(Ĵ.map C.subtype).map M.subtype, hJle,
    by rw [hJeq]; exact isPComponent_map_mulEquiv eC hĴ, ⟨_, ⟨_, hzĴ, rfl⟩, rfl⟩, ?_, ?_⟩
  ·
    have h1 : ((Ĵ.map C.subtype).map M.subtype).subgroupOf M = Ĵ.map C.subtype :=
      comap_map_eq_self_of_injective M.subtype_injective _
    have hcomp : π.comp C.subtype = (centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} :
        Set (MBar β))).subtype.comp φ := rfl
    rw [h1, map_map, hcomp, ← map_map, hĴmap, subgroupOf_map_subtype, inf_eq_left.mpr hYle]
  ·
    let eJ : ↥Ĵ ≃* ↥((Ĵ.map C.subtype).map M.subtype) :=
      ((Ĵ.equivMapOfInjective C.subtype C.subtype_injective).trans
        ((Ĵ.map C.subtype).equivMapOfInjective M.subtype M.subtype_injective))
    have hφĴ : ∀ x : ↥Ĵ, ((φ x : ↥(centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} :
        Set (MBar β)))) : MBar β) ∈ Y := by
      intro x
      have : φ x ∈ Ĵ.map φ := mem_map_of_mem φ x.2
      rw [hĴmap] at this
      exact this
    let g₀ : ↥Ĵ →* ↥Y := ((centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} :
      Set (MBar β))).subtype.comp (φ.comp Ĵ.subtype)).codRestrict Y hφĴ
    have hg₀ : Function.Surjective g₀ := by
      rintro ⟨y, hy⟩
      have hy' : (⟨y, hYle hy⟩ : ↥(centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} :
          Set (MBar β)))) ∈ Ĵ.map φ := by
        rw [hĴmap]; exact hy
      obtain ⟨x, hx, hxy⟩ := hy'
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      show ((φ x : ↥(centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} : Set (MBar β)))) :
        MBar β) = y
      rw [hxy]
    have hg₀k : ¬ 2 ∣ Nat.card g₀.ker := by
      have hle : g₀.ker.map Ĵ.subtype ≤ φ.ker := by
        rintro _ ⟨x, hx, rfl⟩
        have hx' : g₀ x = 1 := hx
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        have h2 := congrArg Subtype.val hx'
        exact h2
      have hc : Nat.card g₀.ker ∣ Nat.card φ.ker := by
        rw [← Subgroup.card_map_of_injective Ĵ.subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      exact fun h2 => hφk (h2.trans hc)
    refine ⟨g₀.comp eJ.symm.toMonoidHom, hg₀.comp eJ.symm.surjective, ?_⟩
    have hk : Nat.card (g₀.comp eJ.symm.toMonoidHom).ker = Nat.card g₀.ker := by
      rw [← MonoidHom.comap_ker]
      exact Nat.card_congr ((Subgroup.equivMapOfInjective _ _ eJ.symm.injective).trans
        (MulEquiv.subgroupCongr (by
          rw [Subgroup.map_comap_eq_self_of_surjective eJ.symm.surjective]))).toEquiv
    rw [hk]
    exact hg₀k

end Lemma47

end CFSG.ComponentClassification.HarrisLit
