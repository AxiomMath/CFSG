module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenInputs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Semisimple
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Centralizers

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem rightConjugate_normalizer_eq_iff (hyp : Hyp61 G D r Abar) (g : G) :
    rightConjugate (Subgroup.normalizer (D : Set G)) g = Subgroup.normalizer (D : Set G) ↔
      g ∈ Subgroup.normalizer (D : Set G) := by
  constructor
  · intro heq
    apply enters_normalizer_of_preimage_le D r Abar hyp.hii ⟨0, by have := hyp.hr; omega⟩ g
    change aschbacherThm5Preimage D _ ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g
    rw [heq]
    exact (preimage_le D _).trans Subgroup.le_normalizer
  · intro hg
    exact (rightConjugate_eq_self_iff _ g).mpr (Subgroup.le_normalizer hg)

structure Hyp71 (D : Subgroup G) (t g : G) : Prop where
  mem : t ∈ Subgroup.normalizer (D : Set G)
  orderOf_eq : orderOf t = 2
  centralizer_le : Subgroup.centralizer ({t} : Set G) ≤
    rightConjugate (Subgroup.normalizer (D : Set G)) g
  ne : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G)

theorem Hyp71.not_mem (hyp : Hyp61 G D r Abar) {t g : G} (h : Hyp71 D t g) :
    g ∉ Subgroup.normalizer (D : Set G) :=
  fun hg => h.ne ((rightConjugate_normalizer_eq_iff hyp g).mpr hg)

omit [Finite G] in
theorem Hyp71.mem_conjugate {t g : G} (h : Hyp71 D t g) :
    t ∈ rightConjugate (Subgroup.normalizer (D : Set G)) g :=
  h.centralizer_le (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

omit [Finite G] in
theorem isFourGroup_map {G' : Type*} [Group G'] {U : Subgroup G}
    (hU : AschbacherKnownGroup.IsFourGroup U) (f : G →* G') (hf : Function.Injective f) :
    AschbacherKnownGroup.IsFourGroup (U.map f) :=
  ⟨CFSG.SectionRank.isElemAbelian_map hU.1 f, by rw [Subgroup.card_map_of_injective hf]; exact hU.2⟩

theorem no_four_group (hin : SectionSevenBase) (hC : Counterexample G D r Abar) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {U : Subgroup G}
    (hUH : U ≤ Subgroup.normalizer (D : Set G)) (hU : AschbacherKnownGroup.IsFourGroup U)
    (hcent : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g) : False :=
  hin.theorem_6_4 hC g (fun heq => hg ((rightConjugate_normalizer_eq_iff hC.hyp g).mp heq))
    U hUH hU hcent

theorem no_four_group_conjugate (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {g : G} (hg : g ∉ Subgroup.normalizer (D : Set G)) {U : Subgroup G}
    (hUH : U ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g)
    (hU : AschbacherKnownGroup.IsFourGroup U)
    (hcent : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (D : Set G)) : False := by
  set H := Subgroup.normalizer (D : Set G)
  have hg' : g⁻¹ ∉ H := fun hmem => hg (by simpa using H.inv_mem hmem)
  apply no_four_group hin hC hg' (U := U.map (MulAut.conj g).toMonoidHom)
  · rintro _ ⟨u, hu, rfl⟩
    exact (mem_rightConjugate_iff H g u).mp (hUH hu)
  · exact isFourGroup_map hU _ (MulAut.conj g).injective
  · rintro _ ⟨u, hu, rfl⟩ hne x hx
    have hu1 : u ≠ 1 := by
      rintro rfl
      exact hne (map_one _)
    rw [mem_rightConjugate_iff, inv_inv]
    apply hcent u hu hu1
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    change x * (g * u * g⁻¹) = (g * u * g⁻¹) * x at hx
    calc g⁻¹ * x * g * u = g⁻¹ * (x * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * x) * g := by rw [hx]
      _ = u * (g⁻¹ * x * g) := by group

theorem two_le (hC : Counterexample G D r Abar) : 2 ≤ r := by
  have h1 := hC.hyp.hr
  by_contra h
  exact hC.fails (Or.inl (by omega))

theorem centralizer_le_of_centralizes (hC : Counterexample G D r Abar) (i : Fin r) {u : G}
    (htwo : ∃ k : ℕ, u ^ (2 ^ k) = 1) (hu : u ≠ 1)
    (hcent : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar i)) u) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (D : Set G) := by
  refine centralizer_le_normalizer_of_control D r Abar hC.hyp.hi i u htwo ?_ hcent
  rw [hC.center, Subgroup.mem_bot]
  exact hu

theorem exists_ne (hC : Counterexample G D r Abar) (i : Fin r) : ∃ j : Fin r, j ≠ i := by
  have h2 := two_le hC
  by_cases hi : i.val = 0
  · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
  · exact ⟨⟨0, by omega⟩, fun h => hi (by simp [Fin.ext_iff] at h; omega)⟩

theorem centralizer_le_of_mem_factor (hC : Counterexample G D r Abar) {i : Fin r} {u : G}
    (hui : u ∈ aschbacherThm5Preimage D (Abar i)) (htwo : ∃ k : ℕ, u ^ (2 ^ k) = 1)
    (hu : u ≠ 1) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (D : Set G) := by
  obtain ⟨j, hj⟩ := exists_ne hC i
  exact centralizer_le_of_centralizes hC j htwo hu
    (cross_factor_centralizes D Abar hC.hyp.hcomm j i hj u hui)

omit [Finite G] in
theorem two_power_of_orderOf {u : G} (hu : orderOf u = 2) : ∃ k : ℕ, u ^ (2 ^ k) = 1 :=
  ⟨1, by rw [pow_one, ← hu]; exact pow_orderOf_eq_one u⟩

omit [Finite G] in
theorem two_power_of_sq {u : G} (hu : u ^ 2 = 1) : ∃ k : ℕ, u ^ (2 ^ k) = 1 :=
  ⟨1, by rw [pow_one]; exact hu⟩

@[expose] def factorCentralizer (D : Subgroup G) (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    Subgroup G :=
  ((Subgroup.centralizer (Ā : Set (D ⧸ aschbacherThm5OddCore D))).comap
    (QuotientGroup.mk' (aschbacherThm5OddCore D))).map D.subtype

omit [Finite G] in
theorem mem_factorCentralizer_iff (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)) (y : G) :
    y ∈ factorCentralizer D Ā ↔ y ∈ D ∧
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D Ā) y := by
  rw [factorCentralizer, Subgroup.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d.2, (centralizes_iff_quotient_commutes D Ā d).mpr fun a ha => ?_⟩
    exact ((Subgroup.mem_centralizer_iff.mp hd) a ha).symm
  · rintro ⟨hy, hcent⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((centralizes_iff_quotient_commutes D Ā ⟨y, hy⟩).mp hcent a ha).symm

omit [Finite G] in
theorem factorCentralizer_le_D (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    factorCentralizer D Ā ≤ D :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem factor_le_factorCentralizer
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x) {i j : Fin r}
    (hij : i ≠ j) :
    aschbacherThm5Preimage D (Abar j) ≤ factorCentralizer D (Abar i) := fun y hy =>
  (mem_factorCentralizer_iff (Abar i) y).mpr
    ⟨preimage_le D _ hy, cross_factor_centralizes D Abar hcomm i j hij y hy⟩

theorem factor_even (hyp : Hyp61 G D r Abar) (i : Fin r) :
    Even (Nat.card (aschbacherThm5Preimage D (Abar i))) := by
  have : Group.IsPerfect (Abar i) := semisimple_perfect _ (hyp.hsemisimple i)
  have : Nontrivial (Abar i) := semisimple_nontrivial _ (hyp.hsemisimple i)
  have heven : Even (Nat.card (Abar i)) := by
    by_contra hodd
    exact Group.IsPerfect.not_isSolvable (Abar i)
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd))
  have hdvd : Nat.card (Abar i) ∣ Nat.card (aschbacherThm5Preimage D (Abar i)) := by
    have h1 := Subgroup.card_map_dvd ((Abar i).comap (QuotientGroup.mk' (aschbacherThm5OddCore D)))
      (QuotientGroup.mk' (aschbacherThm5OddCore D))
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at h1
    rw [aschbacherThm5Preimage, Subgroup.card_map_of_injective D.subtype_injective]
    exact h1
  exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp heven).trans hdvd)

theorem pRank_le_one_of_conjugate (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {g : G} (hg : g ∉ Subgroup.normalizer (D : Set G)) {X : Subgroup G}
    (hXg : X ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g)
    (hgood : ∀ x ∈ X, x ≠ 1 → (∃ k : ℕ, x ^ (2 ^ k) = 1) →
      Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (D : Set G)) :
    pRank 2 X ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨E, hEX, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := 2) (H := X) (k := 2) (by omega)
  refine no_four_group_conjugate hin hC hg (hEX.trans hXg) ⟨hE, by rw [hcard]; norm_num⟩ ?_
  intro u hu hne
  exact hgood u (hEX hu) hne (two_power_of_sq (hE.2 u hu))

theorem lemma_7_2_left (hin : SectionSevenBase) (hC : Counterexample G D r Abar) {t g : G}
    (h : Hyp71 D t g) (i : Fin r) :
    pRank 2 (factorCentralizer D (Abar i) ⊓ Subgroup.centralizer ({t} : Set G)) ≤ 1 :=
  pRank_le_one_of_conjugate hin hC (h.not_mem hC.hyp) (inf_le_right.trans h.centralizer_le)
    fun x hx hne htwo => centralizer_le_of_centralizes hC i htwo hne
      ((mem_factorCentralizer_iff (Abar i) x).mp hx.1).2

omit [Finite G] in
theorem card_fixedPoints_eq {X : Subgroup G} {t : G}
    (htX : t ∈ Subgroup.normalizer (X : Set G)) :
    Nat.card (MulAction.fixedPoints ((Subgroup.zpowers t).subgroupOf
        (Subgroup.normalizer (X : Set G))) X) =
      Nat.card (X ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
  apply Nat.card_congr
  refine
    { toFun := fun x => ⟨x.1, x.1.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · have hfix := x.2 ⟨⟨t, htX⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers t)⟩
    have hval := congrArg Subtype.val hfix
    change (t * x.1 * t⁻¹ : G) = x.1 at hval
    calc (x.1 : G) * t = t * x.1 * t⁻¹ * t := by rw [hval]
      _ = t * x.1 := by group
  · rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hs)
    apply Subtype.ext
    change (s : G) * y.1 * (s : G)⁻¹ = y.1
    have hc : Commute t (y.1 : G) :=
      (Subgroup.mem_centralizer_singleton_iff.mp y.2.2).symm
    rw [← hk, ((hc.zpow_left k).eq), mul_inv_cancel_right]

theorem exists_involution_commute {X : Subgroup G} {t : G}
    (htwo : IsPGroup 2 (Subgroup.zpowers t)) (htX : t ∈ Subgroup.normalizer (X : Set G))
    (heven : Even (Nat.card X)) :
    ∃ x ∈ X, orderOf x = 2 ∧ x * t = t * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := (Subgroup.zpowers t).subgroupOf (Subgroup.normalizer (X : Set G))
  have hT : IsPGroup 2 T := htwo.comap_subtype
  have hmod := hT.card_modEq_card_fixedPoints X
  rw [card_fixedPoints_eq htX] at hmod
  have hC : 2 ∣ Nat.card (X ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :=
    (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans
      (Nat.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp heven))))
  have : Fintype (X ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := (X ⊓ Subgroup.centralizer
    ({t} : Set G) : Subgroup G)) 2 (by rwa [← Nat.card_eq_fintype_card])
  refine ⟨x.1, x.2.1, by rw [← hx, Subgroup.orderOf_coe], ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp x.2.2

theorem lemma_7_2_right (hC : Counterexample G D r Abar) {t : G} (ht : orderOf t = 2)
    (i : Fin r)
    (hti : t ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) :
    ∃ x ∈ aschbacherThm5Preimage D (Abar i), orderOf x = 2 ∧ x * t = t * x := by
  refine exists_involution_commute ?_ hti ?_
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  · exact factor_even hC.hyp i

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5
