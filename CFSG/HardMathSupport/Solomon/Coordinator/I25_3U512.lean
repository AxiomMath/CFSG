module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3NoSU
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3U38
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FieldThreeCyclic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

theorem i253_mem_zpowers_of_cyclic {M : Type*} [Group M] [Finite M] {E : Subgroup M}
    [IsCyclic ↥E] {α ε : M} (hα : α ∈ E) (hε : ε ∈ E) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hε3 : ε ^ 3 = 1) : ε ∈ Subgroup.zpowers α := by
  classical
  haveI := Fintype.ofFinite ↥E
  let a : ↥E := ⟨α, hα⟩
  let e : ↥E := ⟨ε, hε⟩
  have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hα3)
  have he3 : e ^ 3 = 1 := Subtype.ext (by simpa using hε3)
  have ha1 : a ≠ 1 := fun h => hα1 (congrArg Subtype.val h)
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥E) (n := 3) (by norm_num)
  by_contra hne
  have he1 : e ≠ 1 := fun h => hne (by
    have : ε = 1 := congrArg Subtype.val h
    rw [this]; exact Subgroup.one_mem _)
  have hea : e ≠ a := fun h => hne (by
    have : ε = α := congrArg Subtype.val h
    rw [this]; exact Subgroup.mem_zpowers _)
  have ha2 : a ^ 2 ≠ 1 := fun h => ha1 (by
    calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
      _ = 1 := by rw [ha3, h]; simp)
  have hae2 : a ≠ a ^ 2 := fun h => ha1 (by
    calc a = a ^ 2 * a⁻¹ := by group
      _ = a * a⁻¹ := by rw [← h]
      _ = 1 := by simp)
  have he2 : e ≠ a ^ 2 := fun h => hne (by
    have : ε = α ^ 2 := congrArg Subtype.val h
    rw [this]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2)
  have hsub : ({1, a, a ^ 2, e} : Finset ↥E) ⊆ Finset.univ.filter (fun x : ↥E => x ^ 3 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact ha3
    · calc (a ^ 2) ^ 3 = (a ^ 3) ^ 2 := by group
        _ = 1 := by rw [ha3]; simp
    · exact he3
  have hcard : ({1, a, a ^ 2, e} : Finset ↥E).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using he2.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hae2, hea.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha1.symm, ha2.symm, he1.symm⟩
  have := Finset.card_le_card hsub
  omega

theorem i253_pow_three_of_mem_sup {G : Type*} [Group G] {A : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hAC : ∀ a ∈ A, a * x = x * a) {g : G}
    (hg : g ∈ A ⊔ Subgroup.zpowers x) : g ^ 3 = 1 := by
  have hnorm : A ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro a ha
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((Commute.zpow_right (show Commute a x from hAC a ha) k).eq).symm
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  rw [← SetLike.mem_coe, hmul] at hg
  obtain ⟨v, hv, u, hu, rfl⟩ := hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  have hcomm : Commute v (x ^ k) := (Commute.zpow_right (show Commute v x from hAC v hv) k)
  rw [hcomm.mul_pow, hA3 v hv, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hx3, one_zpow]

theorem i253_barAut_one_of_restrict {G : Type*} [Group G] [Finite G] {L C J₀ : Subgroup G}
    (hJL : J₀ ≤ L) (hJC : J₀ ≤ C) (e : barOf 3 (barX 3 C J₀) ≃* ↥(barX 3 L J₀))
    (he1 : ∀ (j : G) (hj : j ∈ J₀),
      ((e (QuotientGroup.mk
          (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨j, hJC hj⟩,
            ⟨⟨j, hJC hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩⟩ : ↥(barX 3 C J₀))) :
        ↥(barX 3 L J₀)) : barOf 3 L) = QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨j, hJL hj⟩)
    {a : G} (haC : a ∈ C) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (haJ : a ∈ Subgroup.normalizer (J₀ : Set G))
    (hres : ∀ y : ↥(barX 3 L J₀), ((barAut 3 L ⟨a, haL⟩ y : barOf 3 L)) = y)
    (h : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨a, haC⟩ ∈
      Subgroup.normalizer ((barX 3 C J₀ : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C)) : Set _)) :
    barAut 3 (barX 3 C J₀) ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨a, haC⟩, h⟩ = 1 := by
  ext w
  obtain ⟨w0, rfl⟩ := QuotientGroup.mk_surjective w
  rw [MulAut.one_apply, barAut_mk]
  obtain ⟨⟨j, hjC⟩, hj, hjw⟩ := w0.2
  have hj' : j ∈ J₀ := Subgroup.mem_subgroupOf.1 hj
  have hj'' : a * j * a⁻¹ ∈ J₀ := (Subgroup.mem_normalizer_iff.1 haJ j).1 hj'
  have hw0 : w0 = ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨j, hjC⟩,
      ⟨⟨j, hjC⟩, Subgroup.mem_subgroupOf.2 hj', rfl⟩⟩ := Subtype.ext hjw.symm
  have key1 : (QuotientGroup.mk ((barX 3 C J₀).normalizerMonoidHom
      ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨a, haC⟩, h⟩ w0) : barOf 3 (barX 3 C J₀)) =
      QuotientGroup.mk (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨a * j * a⁻¹, hJC hj''⟩,
        ⟨⟨a * j * a⁻¹, hJC hj''⟩, Subgroup.mem_subgroupOf.2 hj'', rfl⟩⟩ :
          ↥(barX 3 C J₀)) := by
    congr 1
    apply Subtype.ext
    rw [hw0]
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨a, haC⟩ *
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨j, hjC⟩ *
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨a, haC⟩)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have key2 : (QuotientGroup.mk w0 : barOf 3 (barX 3 C J₀)) =
      QuotientGroup.mk (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨j, hJC hj'⟩,
        ⟨⟨j, hJC hj'⟩, Subgroup.mem_subgroupOf.2 hj', rfl⟩⟩ : ↥(barX 3 C J₀)) := by
    congr 1
  rw [key1, key2]
  apply e.injective
  apply Subtype.ext
  rw [he1 (a * j * a⁻¹) hj'', he1 j hj']
  have h1 := hres (e (QuotientGroup.mk (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨j, hJC hj'⟩,
        ⟨⟨j, hJC hj'⟩, Subgroup.mem_subgroupOf.2 hj', rfl⟩⟩ : ↥(barX 3 C J₀))))
  rw [he1 j hj'] at h1
  have h1' : barAut 3 L ⟨a, haL⟩ (QuotientGroup.mk (⟨j, hJL hj'⟩ : ↥L)) =
      QuotientGroup.mk (⟨j, hJL hj'⟩ : ↥L) := h1
  rw [barAut_mk] at h1'
  have h2 : (L.normalizerMonoidHom ⟨a, haL⟩ ⟨j, hJL hj'⟩ : ↥L) = ⟨a * j * a⁻¹, hJL hj''⟩ :=
    Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _)
  rw [h2] at h1'
  exact h1'

theorem i253_su38Trivial_512 {G : Type} [Group G] [Finite G]
    {L A J₀ : Subgroup G} {x : G}
    (hLq : CFSG.Open.IsQuasisimple (barOf 3 L))
    (hty : IsExtremalType (barOf 3 L) ∨ IsSLThreeEps (barOf 3 L))
    (hz : ∃ z ∈ Subgroup.center (barOf 3 L), z ≠ 1)
    (hx3 : x ^ 3 = 1) (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hAC : A ≤ Cen x)
    (hfld : ∀ g ∈ A ⊔ Subgroup.zpowers x, InducesFieldAut 3 L g)
    (hJL : J₀ ≤ L) (hJC : J₀ ≤ Cen x)
    (hfixJ : fixedSub (barAut 3 L ⟨x, hxN⟩) = barX 3 L J₀)
    (hJN : ∀ a ∈ A, a ∈ Subgroup.normalizer (J₀ : Set G))
    (e : barOf 3 (barX 3 (Cen x) J₀) ≃* ↥(barX 3 L J₀))
    (he1 : ∀ (j : G) (hj : j ∈ J₀),
      ((e (QuotientGroup.mk
          (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨j, hJC hj⟩,
            ⟨⟨j, hJC hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩⟩ : ↥(barX 3 (Cen x) J₀))) :
        ↥(barX 3 L J₀)) : barOf 3 L) = QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨j, hJL hj⟩) :
    SU38Trivial (barX 3 (Cen x) A) (barX 3 (Cen x) J₀) := by
  intro hsu ã hã h
  obtain ⟨⟨a, haC⟩, ha, rfl⟩ := hã
  have haA : a ∈ A := Subgroup.mem_subgroupOf.1 ha
  have hAcomm : ∀ a ∈ A, a * x = x * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.1 (hAC ha)
  have hxmem : x ∈ A ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have haS : a ∈ A ⊔ Subgroup.zpowers x := Subgroup.mem_sup_left haA
  obtain ⟨haL, -⟩ := hfld a haS
  have hα3 : (barAut 3 L ⟨x, hxN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  set E : Subgroup (MulAut (barOf 3 L)) :=
    ((A ⊔ Subgroup.zpowers x).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L)
    with hE
  have hαE : barAut 3 L ⟨x, hxN⟩ ∈ E := ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.2 hxmem, rfl⟩
  have hEf : ∀ ε ∈ E, IsFieldAutThree ε := by
    rintro ε ⟨γ, hγ, rfl⟩
    exact (hfld γ.1 (Subgroup.mem_subgroupOf.1 hγ)).2
  have hE3 : ∀ ε ∈ E, ε ^ 3 = 1 := by
    rintro ε ⟨γ, hγ, rfl⟩
    rw [← map_pow]
    have : γ ^ 3 = 1 := Subtype.ext (by
      simpa using i253_pow_three_of_mem_sup hx3 hA3 hAcomm (Subgroup.mem_subgroupOf.1 hγ))
    rw [this, map_one]
  haveI : IsCyclic ↥E := isCyclic_fieldAutThree_of_exponent_three hLq E hEf hE3
  by_cases hα1 : barAut 3 L ⟨x, hxN⟩ = 1
  · exfalso
    apply i253_not_isSU38 hty
    have h1 : IsSU38 ↥(barX 3 L J₀) := isSU38_congr e hsu
    rw [← hfixJ, hα1] at h1
    have htop : fixedSub (1 : MulAut (barOf 3 L)) = ⊤ := by
      ext y
      simp only [Subgroup.mem_top, iff_true]
      rfl
    rw [htop] at h1
    exact isSU38_congr Subgroup.topEquiv h1
  · have hεE : barAut 3 L ⟨a, haL⟩ ∈ E := ⟨⟨a, haL⟩, Subgroup.mem_subgroupOf.2 haS, rfl⟩
    have hmem : barAut 3 L ⟨a, haL⟩ ∈ Subgroup.zpowers (barAut 3 L ⟨x, hxN⟩) :=
      i253_mem_zpowers_of_cyclic hαE hεE hα3 hα1 (hE3 _ hεE)
    have hres : ∀ y : ↥(barX 3 L J₀), ((barAut 3 L ⟨a, haL⟩ y : barOf 3 L)) = y := by
      intro y
      have hy : (y : barOf 3 L) ∈ fixedSub (barAut 3 L ⟨x, hxN⟩) := by rw [hfixJ]; exact y.2
      have hfix : (barAut 3 L ⟨x, hxN⟩) • (y : barOf 3 L) = y := hy
      have hst := Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hfix) hmem
      exact MulAction.mem_stabilizer_iff.1 hst
    exact i253_barAut_one_of_restrict hJL hJC e he1 haC haL (hJN a haA) hres h

end CFSG.HardMathSupport.Solomon.Coordinator
