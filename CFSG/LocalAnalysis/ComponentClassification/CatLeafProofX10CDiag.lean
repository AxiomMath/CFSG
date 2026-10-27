module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitOddQuotient
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aFStar

public section

namespace CFSG.ComponentClassification.CatLeafProof.X10C

open CFSG Subgroup CFSG.LocalCores

section Diagonal

variable {G : Type*} [Group G] [Finite G]

theorem layer_le_normalizer {W : Subgroup G} (hW : IsComponent W) :
    layer G ≤ normalizer (W : Set G) :=
  CFSG.LocalCores.layer_le_normalizer hW

theorem exists_component_centralizer_of_conj_ne {g : G} (hg : g * g = 1) {W : Subgroup G}
    (hW : IsComponent W) (hne : W.map (MulAut.conj g).toMonoidHom ≠ W) :
    ∃ D : Subgroup ↥(centralizer ({g} : Set G)), IsComponent D := by
  set W' := W.map (MulAut.conj g).toMonoidHom with hW'def
  have hW' : IsComponent W' := isComponent_map_mulEquiv (MulAut.conj g) hW
  have hcomm : ⁅W, W'⁆ = ⊥ := (distinct_components_commute hW hW').resolve_left fun h => hne h.symm
  have hc : ∀ x ∈ W, ∀ y ∈ W', x * y = y * x := fun x hx y hy =>
    mem_centralizer_iff.mp ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hcomm)) hy) x hx
  have hgW : ∀ x ∈ W, g * x * g⁻¹ ∈ W' := fun x hx => ⟨x, hx, rfl⟩
  have hginv : g⁻¹ = g := by rw [eq_comm, ← mul_eq_one_iff_eq_inv]; exact hg
  let δ : W →* G :=
    { toFun := fun x => (x : G) * (g * x * g⁻¹)
      map_one' := by simp
      map_mul' := fun x y => by
        have h1 := hc y y.2 (g * x * g⁻¹) (hgW x x.2)
        simp only [Subgroup.coe_mul]
        calc (x : G) * y * (g * (x * y) * g⁻¹)
            = x * (y * (g * x * g⁻¹)) * (g * y * g⁻¹) := by group
          _ = x * ((g * x * g⁻¹) * y) * (g * y * g⁻¹) := by rw [h1]
          _ = x * (g * x * g⁻¹) * (y * (g * y * g⁻¹)) := by group }
  have hδ : ∀ x : W, δ x = (x : G) * (g * x * g⁻¹) := fun x => rfl
  have hδC : ∀ x : W, δ x ∈ centralizer ({g} : Set G) := fun x => by
    rw [mem_centralizer_singleton_iff, hδ]
    have h1 := hc x x.2 (g * x * g⁻¹) (hgW x x.2)
    rw [hginv] at h1 ⊢
    calc (x : G) * (g * x * g) * g = x * (g * x * g) * g := rfl
      _ = (g * x * g) * x * g := by rw [h1]
      _ = g * ((x : G) * (g * x * g)) := by
          calc (g * x * g) * (x : G) * g = g * x * (g * x * g) := by group
            _ = g * ((x : G) * (g * x * g)) := by group
  let δ' : W →* centralizer ({g} : Set G) := δ.codRestrict _ hδC
  refine ⟨δ'.range, ?_, ?_⟩
  ·
    refine LieType.CurtisTits.isQuasisimple_of_surjective hW.1 δ'.rangeRestrict_surjective ?_
    by_contra hall
    push Not at hall
    have hWW' : ∀ x ∈ W, x ∈ W' := fun x hx => by
      have h1 : (x : G) * (g * x * g⁻¹) = 1 :=
        congrArg (fun y : δ'.range => ((y : centralizer ({g} : Set G)) : G)) (hall ⟨x, hx⟩)
      have h2 : (x : G) = g * x⁻¹ * g⁻¹ :=
        calc (x : G) = (g * x * g⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
          _ = g * x⁻¹ * g⁻¹ := by group
      rw [h2]
      exact hgW _ (inv_mem hx)
    obtain ⟨-, -, a, b, hab⟩ := hW.1
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hc a a.2 b (hWW' b b.2))
  ·
    set E : Subgroup (centralizer ({g} : Set G)) := (layer G).subgroupOf _ with hEdef
    have hWl : W ≤ layer G := le_sSup hW
    have hW'l : W' ≤ layer G := le_sSup hW'
    have hDE : δ'.range ≤ E := by
      rintro _ ⟨x, rfl⟩
      exact mul_mem (hWl x.2) (hW'l (hgW x x.2))
    have hEn : E.Normal := by
      have : (layer G).Characteristic := layer_characteristic
      exact normal_subgroupOf
    refine IsSubnormal.step _ E hDE hEn.isSubnormal ⟨fun n hn c => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨x, hx⟩ := hn
    set c' : G := ((c : centralizer ({g} : Set G)) : G) with hc'def
    have hn' : ((n : centralizer ({g} : Set G)) : G) = (x : G) * (g * x * g⁻¹) := by
      rw [← hx]
      rfl
    have hcl : c' ∈ layer G := c.2
    have hcg : c' * g = g * c' := mem_centralizer_singleton_iff.mp
      (c : centralizer ({g} : Set G)).2
    have hcW : c' * x * c'⁻¹ ∈ W :=
      (mem_normalizer_iff.mp (layer_le_normalizer hW hcl) x).mp x.2
    refine ⟨⟨_, hcW⟩, Subtype.ext ?_⟩
    change (c' * x * c'⁻¹) * (g * (c' * x * c'⁻¹) * g⁻¹) =
      c' * ((n : centralizer ({g} : Set G)) : G) * c'⁻¹
    rw [hn']
    have hcgi : g⁻¹ * c'⁻¹ = c'⁻¹ * g⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hcg]
    calc c' * x * c'⁻¹ * (g * (c' * x * c'⁻¹) * g⁻¹)
        = c' * x * c'⁻¹ * ((g * c') * x * (c'⁻¹ * g⁻¹)) := by group
      _ = c' * x * c'⁻¹ * ((c' * g) * x * (g⁻¹ * c'⁻¹)) := by rw [hcg, hcgi]
      _ = c' * ((x : G) * (g * x * g⁻¹)) * c'⁻¹ := by group

end Diagonal

section Transfer

open CFSG.LocalAnalysis.ComponentInitial (isPComponent_map_of_isPComponent
  not_le_of_isComponent_of_isSolvable isPComponent_of_isComponent_of_not_le ne_bot_of_isComponent)

variable {G : Type*} [Group G] [Finite G]

theorem conj_eq_of_pLayer_centralizer_eq_bot {a : G} (ha : orderOf a = 2)
    (hL : pLayer ↥(centralizer ({a} : Set G)) 2 = ⊥) {W : Subgroup G} (hW : IsPComponent 2 W) :
    W.map (MulAut.conj a).toMonoidHom = W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  set N := pPrimeCore 2 G with hNdef
  have hNodd : ¬ 2 ∣ Nat.card N := fun h =>
    Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    exact hNodd
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hker
  have hWa : IsPComponent 2 (W.map (MulAut.conj a).toMonoidHom) :=
    isPComponent_map_of_isPComponent 2 (MulAut.conj a) hW
  have hWbar : IsComponent (W.map (QuotientGroup.mk' N)) :=
    GSThmB.B5a.isComponent_of_isPComponent (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
      (hbij.mapsTo hW)
  have hmap : (W.map (MulAut.conj a).toMonoidHom).map (QuotientGroup.mk' N) =
      (W.map (QuotientGroup.mk' N)).map (MulAut.conj (QuotientGroup.mk' N a)).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
  have hne' : (W.map (QuotientGroup.mk' N)).map
      (MulAut.conj (QuotientGroup.mk' N a)).toMonoidHom ≠ W.map (QuotientGroup.mk' N) := by
    rw [← hmap]
    intro h
    exact hne (hbij.injOn hWa hW h)
  have ha2 : a ^ 2 = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have hga : QuotientGroup.mk' N a * QuotientGroup.mk' N a = 1 := by
    rw [← map_mul, ← pow_two, ha2, map_one]
  obtain ⟨D, hD⟩ := exists_component_centralizer_of_conj_ne hga hWbar hne'
  have hNodd' : Odd (Nat.card N) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hNodd)
  have hC := AschbacherToolkit.centralizer_quotient_odd N hNodd' a ha
  let ρ : centralizer ({a} : Set G) →* centralizer ({QuotientGroup.mk' N a} : Set (G ⧸ N)) :=
    ((QuotientGroup.mk' N).comp (centralizer ({a} : Set G)).subtype).codRestrict _ fun c => by
      rw [hC]
      exact mem_map_of_mem _ c.2
  have hρs : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    rw [hC] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, hc⟩, rfl⟩
  have hρk : ¬ 2 ∣ Nat.card ρ.ker := by
    intro h2
    let f : ρ.ker →* N :=
      ((centralizer ({a} : Set G)).subtype.comp ρ.ker.subtype).codRestrict N fun x => by
        have hx := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
        change QuotientGroup.mk' N ((x : centralizer ({a} : Set G)) : G) = 1 at hx
        exact (QuotientGroup.eq_one_iff _).mp hx
    have hf : Function.Injective f := fun x y hxy => by
      have h1 : ((x : centralizer ({a} : Set G)) : G) = ((y : centralizer ({a} : Set G)) : G) :=
        congrArg (fun w : N => (w : G)) hxy
      exact Subtype.ext (Subtype.ext h1)
    exact hNodd (h2.trans (Subgroup.card_dvd_of_injective f hf))
  obtain ⟨-, hlift, -⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection ρ hρs hρk
  have hDp : IsPComponent 2 D := isPComponent_of_isComponent_of_not_le 2 hD
    (not_le_of_isComponent_of_isSolvable hD (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (by
      rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      exact fun h => Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h
        (pPrimeCore_coprime_card (p := 2)))))
  obtain ⟨hMp, hMD⟩ := hlift D hDp
  have hM : Subgroup.closure {x : centralizer ({a} : Set G) | x ∈ D.comap ρ ∧
      ∃ k : ℕ, orderOf x = 2 ^ k} ≤ pLayer ↥(centralizer ({a} : Set G)) 2 := le_sSup hMp
  rw [hL, le_bot_iff] at hM
  rw [hM, Subgroup.map_bot] at hMD
  exact ne_bot_of_isComponent hD hMD.symm

end Transfer

end CFSG.ComponentClassification.CatLeafProof.X10C
