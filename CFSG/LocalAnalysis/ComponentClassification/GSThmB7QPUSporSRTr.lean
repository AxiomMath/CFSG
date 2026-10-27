module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1Comp
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.ComponentClassification.GSThmB.QPUSpor

open CFSG Subgroup

theorem not_isPGroup_two_of_simple {T : Type*} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hna : ∃ a b : T, a * b ≠ b * a) : ¬ IsPGroup 2 T := by
  intro hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := hs.toNontrivial
  have hc := hP.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center T) with h | h
  · rw [h] at hc
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hc rfl
  · obtain ⟨a, b, hab⟩ := hna
    have hb : b ∈ center T := h ▸ mem_top b
    exact hab (mem_center_iff.1 hb a)

theorem le_pPrimeCore_of_isSubnormal {G : Type*} [Group G] [Finite G] {X : Subgroup G}
    (hX : X.IsSubnormal) (hodd : Nat.Coprime 2 (Nat.card X)) : X ≤ pPrimeCore 2 G := by
  have h1 := Walter.map_pPrimeCore_le_of_isSubnormal hX
  have htop : pPrimeCore 2 ↥X = ⊤ := by
    rw [eq_top_iff]
    exact le_sSup ⟨normal_top, by rw [card_top]; exact hodd⟩
  rw [htop, ← MonoidHom.range_eq_map, range_subtype] at h1
  exact h1

theorem map_centralizer_normal {M S : Type*} [Group M] [Group S] (φ : M →* S)
    (hφ : Function.Surjective φ) (hcen : φ.ker ≤ center M) (t : M) :
    (((centralizer ({t} : Set M)).map φ).subgroupOf
      (centralizer ({φ t} : Set S))).Normal := by
  constructor
  rintro ⟨_, hc⟩ ⟨c, hcC, rfl⟩ ⟨u, hu⟩
  obtain ⟨s, rfl⟩ := hφ u
  rw [mem_subgroupOf]
  refine ⟨s * c * s⁻¹, ?_, by simp⟩
  have hz : t⁻¹ * (s⁻¹ * t * s) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv]
    have hu' : φ s * φ t = φ t * φ s := (mem_centralizer_singleton_iff.1 hu)
    calc (φ t)⁻¹ * ((φ s)⁻¹ * φ t * φ s) = (φ t)⁻¹ * ((φ s)⁻¹ * (φ t * φ s)) := by group
      _ = (φ t)⁻¹ * ((φ s)⁻¹ * (φ s * φ t)) := by rw [hu']
      _ = 1 := by group
  have hzc := mem_center_iff.1 (hcen hz)
  have hct : c * t = t * c := mem_centralizer_singleton_iff.1 hcC
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  have h1 : c * (s⁻¹ * t * s) = (s⁻¹ * t * s) * c := by
    set z := t⁻¹ * (s⁻¹ * t * s) with hz'
    have e : s⁻¹ * t * s = t * z := by rw [hz']; group
    rw [e, ← mul_assoc, hct, mul_assoc, hzc c, ← mul_assoc]
  calc s * c * s⁻¹ * t = s * (c * (s⁻¹ * t * s)) * s⁻¹ := by group
    _ = s * ((s⁻¹ * t * s) * c) * s⁻¹ := by rw [h1]
    _ = t * (s * c * s⁻¹) := by group

theorem exists_subnormal_of_cover {M S T : Type*} [Group M] [Group S] [Group T] [Finite M]
    (φ : M →* S) (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker)
    (hcen : φ.ker ≤ center M) {t : M} {J : Subgroup M} (hJC : J ≤ centralizer ({t} : Set M))
    (hJs : (J.subgroupOf (centralizer ({t} : Set M))).IsSubnormal)
    (eT : ↥J ⧸ pPrimeCore 2 ↥J ≃* T) (hTs : IsSimpleGroup T) (hTna : ∃ a b : T, a * b ≠ b * a)
    (hO : pPrimeCore 2 ↥(centralizer ({φ t} : Set S)) = ⊥) :
    ∃ K : Subgroup S, K ≤ centralizer ({φ t} : Set S) ∧
      (K.subgroupOf (centralizer ({φ t} : Set S))).IsSubnormal ∧ Nonempty (↥K ≃* T) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite S := Finite.of_surjective φ hφ
  set C := centralizer ({t} : Set M) with hC
  set C' := centralizer ({φ t} : Set S) with hC'
  set A := C.map φ with hA
  have hAC' : A ≤ C' := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c * t = t * c := mem_centralizer_singleton_iff.1 hc
    exact mem_centralizer_singleton_iff.2 (by rw [← map_mul, hc', map_mul])
  have hAn := map_centralizer_normal φ hφ hcen t
  have hOC : pPrimeCore 2 ↥C = ⊥ := by
    set P := ((pPrimeCore 2 ↥C).map C.subtype).map φ with hP
    have hPA : P ≤ A := map_mono (map_subtype_le _)
    have hPn : (P.subgroupOf A).Normal := by
      constructor
      intro n hn g
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨_, ⟨y, hyO, rfl⟩, hyx⟩ := hn
      obtain ⟨g, hgA⟩ := g
      obtain ⟨c, hcC, rfl⟩ := hgA
      refine ⟨_, ⟨⟨c, hcC⟩ * y * ⟨c, hcC⟩⁻¹,
        (inferInstance : (pPrimeCore 2 ↥C).Normal).conj_mem _ hyO _, rfl⟩, ?_⟩
      simp only [coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [← hyx]
      rfl
    have hPsn : (P.subgroupOf C').IsSubnormal :=
      HarrisLit.L33.SR.E1.isSubnormal_subgroupOf_trans hPA hAC' hPn.isSubnormal hAn
    have hPodd : Nat.Coprime 2 (Nat.card (P.subgroupOf C')) := by
      have h1 : Nat.card (P.subgroupOf C') = Nat.card P :=
        Nat.card_congr (subgroupOfEquivOfLe (hPA.trans hAC')).toEquiv
      have h2 : Nat.card P ∣ Nat.card (pPrimeCore 2 ↥C) :=
        (Subgroup.card_map_dvd _ _).trans (Subgroup.card_map_dvd _ _)
      rw [h1]
      exact Nat.Coprime.coprime_dvd_right h2 (pPrimeCore_coprime_card (p := 2) (G := ↥C))
    have h1 := le_pPrimeCore_of_isSubnormal hPsn hPodd
    rw [hO, le_bot_iff] at h1
    have hP1 : ∀ y ∈ P, y = 1 := fun y hy => by
      have hy' : (⟨y, hPA.trans hAC' hy⟩ : C') ∈ P.subgroupOf C' := hy
      rw [h1, Subgroup.mem_bot] at hy'
      exact congrArg Subtype.val hy'
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxker : (x : M) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact hP1 _ ⟨x, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hker) ⟨x, hxker⟩
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at hk
    have hdvd : orderOf x ∣ Nat.card (pPrimeCore 2 ↥C) := by
      have h2 := orderOf_dvd_natCard (⟨x, hx⟩ : pPrimeCore 2 ↥C)
      rwa [Subgroup.orderOf_mk] at h2
    have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥C)
    have h3 : orderOf x = 1 := by
      rw [hk] at hdvd ⊢
      rcases k with _ | k
      · rfl
      · exact absurd ((dvd_pow_self 2 (by omega)).trans hdvd)
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop)
    exact orderOf_eq_one_iff.mp h3
  have hOJ : pPrimeCore 2 ↥J = ⊥ := by
    have h1 := Walter.map_pPrimeCore_le_of_isSubnormal hJs
    rw [hOC, le_bot_iff, map_eq_bot_iff_of_injective _ (subtype_injective _)] at h1
    have e := subgroupOfEquivOfLe hJC
    rw [← pPrimeCore_map_iso 2 e, h1, Subgroup.map_bot]
  let eJ : ↥J ≃* T :=
    ((QuotientGroup.quotientMulEquivOfEq hOJ).trans QuotientGroup.quotientBot).symm.trans eT
  have hJk : ∀ x ∈ J, φ x = 1 → x = 1 := by
    intro x hxJ hx1
    set N := φ.ker.subgroupOf J with hN
    have hNn : N.Normal := by
      constructor
      intro n hn g
      rw [hN, mem_subgroupOf] at hn ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        (mem_center_iff.1 (hcen hn) (g : M)), mul_inv_cancel_right]
      exact hn
    have hNt : (N.map eJ.toMonoidHom).Normal := hNn.map _ eJ.surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map eJ.toMonoidHom) with h | h
    · have hxN : (⟨x, hxJ⟩ : J) ∈ N := by
        rw [hN, mem_subgroupOf]
        exact hx1
      have h2 : eJ ⟨x, hxJ⟩ ∈ N.map eJ.toMonoidHom := mem_map_of_mem _ hxN
      rw [h, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h2
      exact congrArg Subtype.val h2
    · exfalso
      have : Finite T := Finite.of_equiv _ eJ.toEquiv
      apply not_isPGroup_two_of_simple hTs hTna
      have hNP : IsPGroup 2 N := by
        intro n
        obtain ⟨k, hk⟩ := hker ⟨(n : J), n.2⟩
        refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg Subtype.val hk
        simpa using this
      have hTP : IsPGroup 2 (N.map eJ.toMonoidHom) := hNP.map _
      rw [h] at hTP
      exact hTP.of_equiv Subgroup.topEquiv
  refine ⟨J.map φ, (map_mono hJC).trans hAC', ?_, ?_⟩
  ·
    have hKA : J.map φ ≤ A := map_mono hJC
    have hsn : ((J.map φ).subgroupOf A).IsSubnormal := by
      have h1 := hJs.map (f := φ.subgroupMap C) (φ.subgroupMap_surjective C)
      convert h1 using 1
      ext ⟨a, ha⟩
      simp only [mem_subgroupOf, mem_map]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j, hJC hj⟩, hj, rfl⟩
      · rintro ⟨⟨c, hc⟩, hcJ, hca⟩
        exact ⟨c, hcJ, congrArg Subtype.val hca⟩
    exact HarrisLit.L33.SR.E1.isSubnormal_subgroupOf_trans hKA hAC' hsn hAn
  ·
    have hinj : Function.Injective (φ.comp J.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      rw [Subgroup.mem_bot]
      exact Subtype.ext (hJk x x.2 hx)
    have hrange : (φ.comp J.subtype).range = J.map φ := by
      rw [MonoidHom.range_comp, range_subtype]
    exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans eJ⟩

end CFSG.ComponentClassification.GSThmB.QPUSpor
