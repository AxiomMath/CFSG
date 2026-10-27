module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

private theorem card_map_mk'_mul_card_of_le {C : Type*} [Group C] (Z D : Subgroup C) [Z.Normal]
    (hZD : Z ≤ D) : Nat.card (D.map (QuotientGroup.mk' Z)) * Nat.card Z = Nat.card D := by
  have h1 := Subgroup.relIndex_ker D (QuotientGroup.mk' Z)
  rw [QuotientGroup.ker_mk'] at h1
  have h2 := Subgroup.relIndex_mul_card (H := Z) (K := D)
  rwa [inf_eq_left.2 hZD, h1] at h2

private theorem comap_map_mk'_of_le {C : Type*} [Group C] (Z D : Subgroup C) [Z.Normal]
    (hZD : Z ≤ D) : (D.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) = D := by
  rw [QuotientGroup.comap_map_mk', sup_eq_right.2 hZD]

private theorem normalizer_map_mk'_of_le {C : Type*} [Group C] (Z D : Subgroup C) [Z.Normal]
    (hZD : Z ≤ D) :
    Subgroup.normalizer ((D.map (QuotientGroup.mk' Z) : Subgroup (C ⧸ Z)) : Set (C ⧸ Z)) =
      (Subgroup.normalizer (D : Set C)).map (QuotientGroup.mk' Z) := by
  have h1 : (Subgroup.normalizer ((D.map (QuotientGroup.mk' Z) : Subgroup (C ⧸ Z)) :
      Set (C ⧸ Z))).comap (QuotientGroup.mk' Z) = Subgroup.normalizer (D : Set C) := by
    rw [Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range _ D),
      comap_map_mk'_of_le Z D hZD]
  rw [← h1, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)]

private theorem nonempty_mulEquiv_normalizer_quotient {A K Q : Type*} [Group A] [Group K]
    [Group Q] (B : Subgroup A) [B.Normal] (E : Subgroup K) (f : A →* K)
    (hfN : ∀ a, f a ∈ Subgroup.normalizer (E : Set K))
    (hsurj : ∀ n ∈ Subgroup.normalizer (E : Set K), ∃ a, f a = n)
    (hker : ∀ a, f a ∈ E ↔ a ∈ B) (e : A ⧸ B ≃* Q) :
    Nonempty (↥(Subgroup.normalizer (E : Set K)) ⧸
      E.subgroupOf (Subgroup.normalizer (E : Set K)) ≃* Q) := by
  let ψ : A →* ↥(Subgroup.normalizer (E : Set K)) ⧸
      E.subgroupOf (Subgroup.normalizer (E : Set K)) :=
    (QuotientGroup.mk' (E.subgroupOf (Subgroup.normalizer (E : Set K)))).comp
      (f.codRestrict _ hfN)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨n, hn⟩, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, rfl⟩ := hsurj n hn
    exact ⟨a, rfl⟩
  have hker' : ψ.ker = B := by
    ext a
    rw [MonoidHom.mem_ker]
    change ((⟨f a, hfN a⟩ : ↥(Subgroup.normalizer (E : Set K))) :
      ↥(Subgroup.normalizer (E : Set K)) ⧸ E.subgroupOf (Subgroup.normalizer (E : Set K))) = 1 ↔
        a ∈ B
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hker a
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker')).trans e⟩

private theorem exists_quotient_image {G Q : Type*} [Group G] [Group Q] (C E L : Subgroup G)
    (Z : Subgroup ↥C) [Z.Normal] (hEC : E ≤ C) (hLC : L ≤ C)
    (hL : L = Subgroup.normalizer (E : Set G)) (hZE : ∀ z ∈ Z, (z : G) ∈ E)
    (hsq : ∀ y ∈ E.subgroupOf C, y * y ∈ Z) (hnot : ∃ h ∈ C, ∃ x ∈ E, h * x * h⁻¹ ∉ E)
    [(E.subgroupOf L).Normal] (e : ↥L ⧸ E.subgroupOf L ≃* Q) :
    ∃ E' : Subgroup (↥C ⧸ Z), (∀ x ∈ E', x * x = 1) ∧ Nat.card E' * Nat.card Z = Nat.card E ∧
      Nat.card (Subgroup.normalizer (E' : Set (↥C ⧸ Z))) * Nat.card Z = Nat.card L ∧
      ¬ E'.Normal ∧
      Nonempty (↥(Subgroup.normalizer (E' : Set (↥C ⧸ Z))) ⧸
        E'.subgroupOf (Subgroup.normalizer (E' : Set (↥C ⧸ Z))) ≃* Q) := by
  have hZEC : Z ≤ E.subgroupOf C := fun z hz => Subgroup.mem_subgroupOf.2 (hZE z hz)
  have hEL : E ≤ L := by
    rw [hL]
    exact Subgroup.le_normalizer
  have hZLC : Z ≤ L.subgroupOf C := fun z hz => Subgroup.mem_subgroupOf.2 (hEL (hZE z hz))
  have hNEC : Subgroup.normalizer ((E.subgroupOf C : Subgroup ↥C) : Set ↥C) =
      L.subgroupOf C := by
    rw [← Subgroup.subgroupOf_normalizer_eq hEC, ← hL]
  have hNL := normalizer_map_mk'_of_le Z (E.subgroupOf C) hZEC
  rw [hNEC] at hNL
  refine ⟨(E.subgroupOf C).map (QuotientGroup.mk' Z), ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff (y * y)).2 (hsq y hy)
  · rw [card_map_mk'_mul_card_of_le Z _ hZEC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv
  · rw [hNL, card_map_mk'_mul_card_of_le Z _ hZLC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLC).toEquiv
  · intro hn
    have hEn : (E.subgroupOf C).Normal := by
      have h := hn.comap (QuotientGroup.mk' Z)
      rwa [comap_map_mk'_of_le Z _ hZEC] at h
    obtain ⟨h, hhC, x, hxE, hx⟩ := hnot
    exact hx (Subgroup.mem_subgroupOf.1
      (hEn.conj_mem ⟨x, hEC hxE⟩ (Subgroup.mem_subgroupOf.2 hxE) ⟨h, hhC⟩))
  · refine nonempty_mulEquiv_normalizer_quotient (E.subgroupOf L)
      ((E.subgroupOf C).map (QuotientGroup.mk' Z))
      ((QuotientGroup.mk' Z).comp (Subgroup.inclusion hLC)) ?_ ?_ ?_ e
    · intro a
      rw [hNL]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 a.2)
    · intro n hn
      rw [hNL] at hn
      obtain ⟨g, hg, rfl⟩ := hn
      exact ⟨⟨(g : G), Subgroup.mem_subgroupOf.1 hg⟩, rfl⟩
    · intro a
      have h1 : (QuotientGroup.mk' Z) (Subgroup.inclusion hLC a) ∈
          (E.subgroupOf C).map (QuotientGroup.mk' Z) ↔
          Subgroup.inclusion hLC a ∈ E.subgroupOf C := by
        rw [← Subgroup.mem_comap, comap_map_mk'_of_le Z _ hZEC]
      exact h1

theorem card_center_centralizer_eq_two {G : Type*} [Group G] (c : G) (hc2 : c * c = 1)
    (hc1 : c ≠ 1)
    (hZ : ∀ z ∈ Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)),
      (z : G) = 1 ∨ (z : G) = c) :
    Nat.card (Subgroup.center ↥(Subgroup.centralizer ({c} : Set G))) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]
  let c' : ↥(Subgroup.centralizer ({c} : Set G)) := ⟨c, hcC⟩
  have hc'Z : c' ∈ Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 g.2 c (Set.mem_singleton c)).symm
  have hZeq : Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)) = Subgroup.zpowers c' := by
    refine le_antisymm (fun z hz => ?_) (Subgroup.zpowers_le.2 hc'Z)
    rcases hZ z hz with h | h
    · have hz1 : z = 1 := Subtype.ext h
      rw [hz1]
      exact Subgroup.one_mem _
    · have hzc : z = c' := Subtype.ext h
      rw [hzc]
      exact Subgroup.mem_zpowers c'
  have hord : orderOf c' = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      exact Subtype.ext hc2
    · intro h
      exact hc1 (congrArg Subtype.val h)
  rw [hZeq, Nat.card_zpowers, hord]

theorem exists_E_quotient {G : Type} [Group G] [Finite G] (c : G) (E L : Subgroup G)
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hcE : c ∈ E)
    (hEsq : ∀ y ∈ E, y * y = 1 ∨ y * y = c)
    (hZ : ∀ z ∈ Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)), (z : G) = 1 ∨ (z : G) = c)
    (hL : L = Subgroup.normalizer (E : Set G)) (hLC : ∀ ℓ ∈ L, ℓ * c = c * ℓ)
    (hEcard : Nat.card E = 2 ^ 7) (hLcard : Nat.card L = 2 ^ 7 * 168)
    (hnot : ∃ h : G, h * c = c * h ∧ ∃ x ∈ E, h * x * h⁻¹ ∉ E)
    [(E.subgroupOf L).Normal]
    (hgl : Nonempty (↥L ⧸ E.subgroupOf L ≃* GL (Fin 3) (ZMod 2))) :
    ∃ E' : Subgroup (↥(Subgroup.centralizer ({c} : Set G)) ⧸
        Subgroup.center ↥(Subgroup.centralizer ({c} : Set G))),
      (∀ x ∈ E', x * x = 1) ∧ Nat.card E' = 2 ^ 6 ∧
      Nat.card (Subgroup.normalizer (SetLike.coe E')) = 2 ^ 6 * 168 ∧ ¬ E'.Normal ∧
      Nonempty (↥(Subgroup.normalizer (E' : Set _)) ⧸
        E'.subgroupOf (Subgroup.normalizer (E' : Set _)) ≃* GL (Fin 3) (ZMod 2)) := by
  obtain ⟨e⟩ := hgl
  have hmemC : ∀ g : G, g ∈ Subgroup.centralizer ({c} : Set G) ↔ c * g = g * c := fun g =>
    ⟨fun h => Subgroup.mem_centralizer_iff.1 h c (Set.mem_singleton c),
      fun h => Subgroup.mem_centralizer_iff.2 fun x hx => by
        rw [Set.mem_singleton_iff.1 hx]
        exact h⟩
  have hLle : L ≤ Subgroup.centralizer ({c} : Set G) := fun ℓ hℓ => (hmemC ℓ).2 (hLC ℓ hℓ).symm
  have hEL : E ≤ L := by
    rw [hL]
    exact Subgroup.le_normalizer
  have hEle : E ≤ Subgroup.centralizer ({c} : Set G) := hEL.trans hLle
  have hZE : ∀ z ∈ Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)), (z : G) ∈ E := by
    intro z hz
    rcases hZ z hz with h | h
    · rw [h]
      exact E.one_mem
    · rw [h]
      exact hcE
  have hsq : ∀ y ∈ E.subgroupOf (Subgroup.centralizer ({c} : Set G)),
      y * y ∈ Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)) := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hyE : (y : G) ∈ E := Subgroup.mem_subgroupOf.1 hy
    have hgc : c * (g : G) = (g : G) * c := (hmemC g).1 g.2
    show (g : G) * ((y : G) * (y : G)) = ((y : G) * (y : G)) * (g : G)
    rcases hEsq y hyE with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]
      exact hgc.symm
  obtain ⟨h, hhc, x, hx, hxn⟩ := hnot
  have hnot' : ∃ h ∈ Subgroup.centralizer ({c} : Set G), ∃ x ∈ E, h * x * h⁻¹ ∉ E :=
    ⟨h, (hmemC h).2 hhc.symm, x, hx, hxn⟩
  have hZ2 := card_center_centralizer_eq_two c hc2 hc1 hZ
  obtain ⟨E', hsq', hcardE, hcardN, hnorm, hiso⟩ := exists_quotient_image
    (Subgroup.centralizer ({c} : Set G)) E L (Subgroup.center _) hEle hLle hL hZE hsq hnot' e
  refine ⟨E', hsq', ?_, ?_, hnorm, hiso⟩
  · rw [hZ2, hEcard] at hcardE
    omega
  · rw [hZ2, hLcard] at hcardN
    omega

end CFSG.EvenSporadicStandard.M12Std.Yosh
