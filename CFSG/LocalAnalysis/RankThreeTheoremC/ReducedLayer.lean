module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSL
import CFSG.LocalAnalysis.RankThreeTheoremC.GaschutzTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem isPConstrained_of_hasPrimeConstraint {p : ℕ} [Fact p.Prime] {H : Type*} [Group H]
    [Finite H] (h : HasPrimeConstraint (G := H) p) : CFSG.ABGLocalTools.IsPConstrained p H := by
  rw [CFSG.ABGLocalTools.isPConstrained_iff_pConstrainedGroup]
  intro Q hQ hsup
  obtain ⟨N, hN, hNp, hNc⟩ := h
  let π : H →* H ⧸ CFSG.pPrimeCore p H := QuotientGroup.mk' (CFSG.pPrimeCore p H)
  have hNle : N ≤ CFSG.pCore p (H ⧸ CFSG.pPrimeCore p H) := le_sSup ⟨hN, hNp⟩
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hQmap : Q.map π = CFSG.pCore p (H ⧸ CFSG.pPrimeCore p H) := by
    have h1 := congrArg (Subgroup.map π) hsup
    rw [Subgroup.map_sup] at h1
    have h2 : (CFSG.pPrimeCore p H).map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff x).2 hx
    rw [h2, bot_sup_eq] at h1
    rw [h1]
    exact Subgroup.map_comap_eq_self_of_surjective hsurj _
  intro x hx
  have hxc : π x ∈ centralizer ((CFSG.pCore p (H ⧸ CFSG.pPrimeCore p H) : Subgroup _) : Set _) := by
    rw [← hQmap, mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have := mem_centralizer_iff.1 hx y hy
    change π y * π x = π x * π y
    rw [← map_mul, ← map_mul, this]
  exact hNle (hNc (centralizer_le (by exact hNle) hxc))

theorem inf_comap_ne_bot_of_dvd_card {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
    (O : Subgroup Y) [O.Normal] (T : Sylow p Y) {Nb : Subgroup (Y ⧸ O)} [Nb.Normal]
    (hdvd : p ∣ Nat.card Nb) :
    (T : Subgroup Y) ⊓ Nb.comap (QuotientGroup.mk' O) ≠ ⊥ := by
  have hp : p.Prime := Fact.out
  obtain ⟨R₁, hR₁⟩ := CFSG.Glauberman.sylow_inf_normal
    (T.mapSurjective (QuotientGroup.mk'_surjective O)) (N := Nb)
  have hcard : Nat.card (R₁ : Subgroup Nb) = p ^ (Nat.card Nb).factorization p :=
    R₁.card_eq_multiplicity
  have hfac : 1 ≤ (Nat.card Nb).factorization p :=
    (hp.dvd_iff_one_le_factorization Nat.card_pos.ne').1 hdvd
  have hne : (R₁ : Subgroup Nb) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have h1 : 1 < p ^ (Nat.card Nb).factorization p := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  rw [hR₁] at hb
  obtain ⟨hbT, hbN⟩ := mem_inf.1 (mem_subgroupOf.1 hb)
  rw [Sylow.coe_mapSurjective] at hbT
  obtain ⟨t, ht, htb⟩ := hbT
  intro hbot
  have htmem : t ∈ (T : Subgroup Y) ⊓ Nb.comap (QuotientGroup.mk' O) :=
    ⟨ht, mem_comap.2 (by rw [htb]; exact hbN)⟩
  rw [hbot, mem_bot] at htmem
  apply hb1
  apply Subtype.ext
  apply Subtype.ext
  change (b : Y ⧸ O) = 1
  rw [← htb, htmem, map_one]

theorem commute_of_mem_layer {X : Type*} [Group X] [Finite X] {c : X} (hc : (zpowers c).Normal)
    {e : X} (he : e ∈ rankThreeLayer (⊤ : Subgroup X)) : c * e = e * c := by
  have hsub : IsSubnormal (zpowers c) ⊤ :=
    IsSubnormal.step le_top (Subgroup.normal_subgroupOf) (IsSubnormal.refl _)
  have hcomm := CFSG.ComponentClassification.Layer.commutes_with_solvable_subnormal
    (zpowers c) hsub
  exact mem_centralizer_iff.1 ((commutator_eq_bot_iff_le_centralizer.1 hcomm) he) c
    (mem_zpowers c)

theorem exists_eq_mul_of_mem_sup_of_commute {X : Type*} [Group X] {A B : Subgroup X}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {c : X} (hc : c ∈ A ⊔ B) :
    ∃ u ∈ A, ∃ v ∈ B, c = u * v := by
  let S : Subgroup X :=
    { carrier := {x | ∃ u ∈ A, ∃ v ∈ B, x = u * v}
      mul_mem' := by
        rintro _ _ ⟨u, hu, v, hv, rfl⟩ ⟨u', hu', v', hv', rfl⟩
        refine ⟨u * u', A.mul_mem hu hu', v * v', B.mul_mem hv hv', ?_⟩
        calc u * v * (u' * v') = u * (v * u') * v' := by group
          _ = u * (u' * v) * v' := by rw [← h u' hu' v hv]
          _ = u * u' * (v * v') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨u, hu, v, hv, rfl⟩
        refine ⟨u⁻¹, A.inv_mem hu, v⁻¹, B.inv_mem hv, ?_⟩
        calc (u * v)⁻¹ = v⁻¹ * u⁻¹ := by group
          _ = u⁻¹ * v⁻¹ := (h u⁻¹ (A.inv_mem hu) v⁻¹ (B.inv_mem hv)).symm }
  have hle : A ⊔ B ≤ S := sup_le (fun x hx => ⟨x, hx, 1, B.one_mem, by simp⟩)
    (fun y hy => ⟨1, A.one_mem, y, hy, by simp⟩)
  exact hle hc

theorem eq_one_of_mem_iSup_components {X : Type*} [Group X] [Finite X] (S : Finset (Subgroup X))
    (hS : ∀ K ∈ S, IsComponentOf K ⊤) (hZ : ∀ K ∈ S, center K = ⊥) :
    ∀ c ∈ (⨆ K ∈ S, K : Subgroup X), (∀ K ∈ S, ∀ x ∈ K, c * x = x * c) → c = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro c hc _
    simpa using hc
  | insert a S ha ih =>
    intro c hc hcomm
    rw [Finset.iSup_insert] at hc
    have hB : (⨆ K ∈ S, K : Subgroup X) ≤ centralizer (a : Set X) := by
      refine iSup₂_le fun K hK => ?_
      have hne : a ≠ K := fun h => ha (h ▸ hK)
      have := CFSG.ComponentClassification.LocalComponents.commute_of_ne a K
        (hS a (Finset.mem_insert_self a S)) (hS K (Finset.mem_insert_of_mem hK)) hne
      exact le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 this)
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_eq_mul_of_mem_sup_of_commute
      (fun x hx y hy => mem_centralizer_iff.1 (hB hy) x hx) hc
    have hu1 : u = 1 := by
      have hcen : (⟨u, hu⟩ : a) ∈ center a := by
        rw [mem_center_iff]
        intro g
        apply Subtype.ext
        have h1 := hcomm a (Finset.mem_insert_self a S) g g.2
        have h2 : v * g = g * v := (mem_centralizer_iff.1 (hB hv) g g.2).symm
        change (g : X) * u = u * g
        have h3 : (g : X) * u * v = u * g * v := by
          calc (g : X) * u * v = g * (u * v) := by group
            _ = u * v * g := h1.symm
            _ = u * (v * g) := by group
            _ = u * (g * v) := by rw [h2]
            _ = u * g * v := by group
        exact mul_right_cancel h3
      rw [hZ a (Finset.mem_insert_self a S), mem_bot] at hcen
      exact congrArg Subtype.val hcen
    subst hu1
    rw [one_mul] at hcomm ⊢
    exact ih (fun K hK => hS K (Finset.mem_insert_of_mem hK))
      (fun K hK => hZ K (Finset.mem_insert_of_mem hK)) v hv
      (fun K hK x hx => by simpa using hcomm K (Finset.mem_insert_of_mem hK) x hx)

theorem exists_component_center_ne_bot_of_mem_layer {X : Type*} [Group X] [Finite X] {c : X}
    (hc : c ∈ rankThreeLayer (⊤ : Subgroup X)) (hc1 : c ≠ 1)
    (hcc : ∀ e ∈ rankThreeLayer (⊤ : Subgroup X), c * e = e * c) :
    ∃ K : Subgroup X, IsComponentOf K ⊤ ∧ center K ≠ ⊥ := by
  classical
  by_contra hno
  push Not at hno
  have hfin : {K : Subgroup X | IsComponentOf K ⊤}.Finite := Set.toFinite _
  have hlayer : rankThreeLayer (⊤ : Subgroup X) = ⨆ K ∈ hfin.toFinset, K :=
    le_antisymm (sSup_le fun K hK => le_iSup₂_of_le K (hfin.mem_toFinset.2 hK) le_rfl)
      (iSup₂_le fun K hK => le_sSup (hfin.mem_toFinset.1 hK))
  rw [hlayer] at hc
  exact hc1 (eq_one_of_mem_iSup_components hfin.toFinset (fun K hK => hfin.mem_toFinset.1 hK)
    (fun K hK => hno K (hfin.mem_toFinset.1 hK)) c hc fun K hK x hx =>
      hcc x (le_sSup (hfin.mem_toFinset.1 hK) hx))

theorem two_le_pRank_inf_layer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type} [Group X]
    [Finite X] (T : Sylow p X) {c : X} (hc : c ∈ rankThreeLayer (⊤ : Subgroup X))
    (hcn : (zpowers c).Normal) (hc1 : c ≠ 1) (hcp : c ^ p = 1) :
    2 ≤ CFSG.Open.pRank p ((T : Subgroup X) ⊓ rankThreeLayer (⊤ : Subgroup X)) := by
  have hp : p.Prime := Fact.out
  have hEn : (rankThreeLayer (⊤ : Subgroup X)).Normal :=
    CFSG.ComponentClassification.Layer.normal X
  have hEp : Group.IsPerfect (rankThreeLayer (⊤ : Subgroup X)) :=
    CFSG.ComponentClassification.Layer.perfect X
  obtain ⟨R, hR⟩ := CFSG.Glauberman.sylow_inf_normal T (N := rankThreeLayer (⊤ : Subgroup X))
  have hcen : (⟨c, hc⟩ : rankThreeLayer (⊤ : Subgroup X)) ∈
      center (rankThreeLayer (⊤ : Subgroup X)) := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (commute_of_mem_layer hcn g.2).symm
  have hnc : ¬ IsCyclic (R : Subgroup (rankThreeLayer (⊤ : Subgroup X))) :=
    not_isCyclic_sylow_of_isPerfect hEp R hcen (fun h => hc1 (congrArg Subtype.val h))
      (Subtype.ext hcp)
  have hnc' : ¬ IsCyclic ((T : Subgroup X) ⊓ rankThreeLayer (⊤ : Subgroup X) : Subgroup X) := by
    intro h
    apply hnc
    rw [hR]
    exact isCyclic_of_surjective (subgroupOfEquivOfLe inf_le_right).symm.toMonoidHom
      (subgroupOfEquivOfLe inf_le_right).symm.surjective
  exact two_le_pRank_of_not_isCyclic hp hp2 (T.isPGroup'.to_inf_left) hnc'

theorem pCore_quotient_eq_map_inf_Op_p'p {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] [Finite H]
    (T : Sylow p H) :
    CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) =
      ((T : Subgroup H) ⊓ CFSG.Op_p'p p H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  apply le_antisymm
  · intro c hc
    have hcT : c ∈ ((T.mapSurjective (QuotientGroup.mk'_surjective
        (primeComplementCore (G := H) p))) : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
      have := CFSG.pCore_normal (p := p) (G := H ⧸ primeComplementCore (G := H) p)
      exact IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := p)
        (G := H ⧸ primeComplementCore (G := H) p)) _ hc
    rw [Sylow.coe_mapSurjective] at hcT
    obtain ⟨t, ht, rfl⟩ := hcT
    exact ⟨t, ⟨ht, hc⟩, rfl⟩
  · rintro _ ⟨t, ⟨-, ht⟩, rfl⟩
    exact ht

theorem isCyclic_pCore_quotient {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] {H : Subgroup G}
    [Finite H] (T : Sylow p H)
    (h : IsCyclic (((T : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype)) :
    IsCyclic (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p)) := by
  rw [pCore_quotient_eq_map_inf_Op_p'p T]
  have h1 : IsCyclic ((T : Subgroup H) ⊓ CFSG.Op_p'p p H : Subgroup H) :=
    isCyclic_of_surjective
      (((T : Subgroup H) ⊓ CFSG.Op_p'p p H).equivMapOfInjective H.subtype
        H.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  exact isCyclic_of_surjective
    ((QuotientGroup.mk' (primeComplementCore (G := H) p)).subgroupMap _)
    (MonoidHom.subgroupMap_surjective _ _)

section Transport

variable {p : ℕ} {Y : Type*} [Group Y] [Finite Y]

theorem le_normalizer_of_map_le_normalizer_map (hp : p.Prime) (O : Subgroup Y) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {T D : Subgroup Y} (hT : IsPGroup p T) (hDT : D ≤ T)
    (h : T.map (QuotientGroup.mk' O) ≤
      normalizer ((D.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O))) :
    T ≤ normalizer (D : Set Y) := by
  intro g hg
  have hle : D.map (MulAut.conj g).toMonoidHom ≤ D := by
    rintro _ ⟨d, hd, rfl⟩
    have h1 : QuotientGroup.mk' O (g * d * g⁻¹) ∈ D.map (QuotientGroup.mk' O) := by
      have := (mem_normalizer_iff.1 (h (mem_map_of_mem _ hg)) (QuotientGroup.mk' O d)).1
        (mem_map_of_mem _ hd)
      simpa using this
    obtain ⟨d', hd', hd'eq⟩ := h1
    have := CFSG.AGLEmbedding.eq_of_mk_eq_of_isPGroup hp O hO hT (hDT hd')
      (T.mul_mem (T.mul_mem hg (hDT hd)) (T.inv_mem hg)) hd'eq
    change g * d * g⁻¹ ∈ D
    rw [← this]
    exact hd'
  exact mem_normalizer_iff_map_conj_eq.2
    (Subgroup.eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj g).injective).ge)

theorem pRank_map_sup_inf_centralizer_le_pRank (hp : p.Prime) (O : Subgroup Y) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {T D : Subgroup Y} (hT : IsPGroup p T) (hDT : D ≤ T) :
    CFSG.Open.pRank p (D.map (QuotientGroup.mk' O) ⊔ (T.map (QuotientGroup.mk' O) ⊓
      centralizer ((D.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)))) ≤
      CFSG.Open.pRank p (D ⊔ (T ⊓ centralizer (D : Set Y))) := by
  have hle : D.map (QuotientGroup.mk' O) ⊔ (T.map (QuotientGroup.mk' O) ⊓
      centralizer ((D.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O))) ≤
      (D ⊔ (T ⊓ centralizer (D : Set Y))).map (QuotientGroup.mk' O) := by
    rw [Subgroup.map_sup]
    exact sup_le_sup_left (CFSG.AGLEmbedding.map_inf_centralizer_map_le hp O hO hT hDT) _
  refine (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hle).trans ?_
  rw [CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal p hp O
    (hp.coprime_iff_not_dvd.mp hO)]

end Transport

end CFSG.LocalAnalysis.RankThreeTheoremC
