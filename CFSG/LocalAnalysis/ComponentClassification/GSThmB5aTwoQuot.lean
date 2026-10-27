module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFix

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace TwoQuot

section General

variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']

omit [Finite G] [Finite G'] in
theorem ker_subgroupMap_le_center (f : G →* G') {L : Subgroup G}
    (hL : L ≤ centralizer (f.ker : Set G)) : (f.subgroupMap L).ker ≤ center ↥L := by
  intro l hl
  rw [mem_center_iff]
  intro m
  have hl' : (l : G) ∈ f.ker := by
    rw [MonoidHom.mem_ker] at hl ⊢
    exact congrArg Subtype.val hl
  exact Subtype.ext (mem_centralizer_iff.mp (hL m.2) l hl').symm

theorem isPComponent_map_of_le_centralizer (f : G →* G') {L Y : Subgroup G} (hLY : L ≤ Y)
    (hLc : L ≤ centralizer (f.ker : Set G)) (hL : IsPComponent 2 (L.subgroupOf Y)) :
    IsPComponent 2 ((L.map f).subgroupOf (Y.map f)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L Y hLY] at hL
  obtain ⟨hsub, hres, hq⟩ := hL
  have hLL : IsPComponent 2 (L.subgroupOf L) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L L le_rfl).mpr
      ⟨by rw [subgroupOf_self]; exact IsSubnormal.top, hres, hq⟩
  have h2 := CatalogueBCentralQuotient.pComponent_map 2 (f.subgroupMap L)
    (f.subgroupMap_surjective L) (ker_subgroupMap_le_center f hLc) _ hLL
  rw [OddQuot.map_subgroupOf_subgroupMap f le_rfl] at h2
  obtain ⟨-, hres', hq'⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ le_rfl).mp h2
  rw [CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ (map_mono hLY)]
  refine ⟨?_, hres', hq'⟩
  have h1 := hsub.map (f.subgroupMap_surjective Y)
  rwa [OddQuot.map_subgroupOf_subgroupMap f hLY] at h1

theorem map_oddCoreIn_le (f : G →* G') (L : Subgroup G) :
    (oddCoreIn L).map f ≤ oddCoreIn (L.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CatalogueBCentralQuotient.primeCore_map_le 2 (f.subgroupMap L)
    (f.subgroupMap_surjective L)
  unfold oddCoreIn
  rw [map_map, ← OddQuot.subtype_comp_subgroupMap, ← map_map]
  exact map_mono h

theorem map_oddCoreIn_of_le_centralizer (f : G →* G') {L : Subgroup G}
    (hLc : L ≤ centralizer (f.ker : Set G)) : (oddCoreIn L).map f = oddCoreIn (L.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CatalogueBCentralQuotient.primeCore_map 2 (f.subgroupMap L)
    (f.subgroupMap_surjective L) (ker_subgroupMap_le_center f hLc)
  unfold oddCoreIn
  rw [← h, map_map, map_map, OddQuot.subtype_comp_subgroupMap]

theorem map_layerIn_of_le_centralizer (f : G →* G') {L : Subgroup G}
    (hLc : L ≤ centralizer (f.ker : Set G)) : (layerIn L).map f = layerIn (L.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hmaps, -, hsurj⟩ := CatalogueBCentralQuotient.pComponent_bijOn 2 (f.subgroupMap L)
    (f.subgroupMap_surjective L) (ker_subgroupMap_le_center f hLc)
  have h : (pLayer ↥L 2).map (f.subgroupMap L) = pLayer ↥(L.map f) 2 := by
    apply le_antisymm
    · exact map_le_iff_le_comap.mpr (sSup_le fun K hK => map_le_iff_le_comap.mp
        (le_sSup (hmaps hK)))
    · refine sSup_le fun M hM => ?_
      obtain ⟨K, hK, rfl⟩ := hsurj hM
      exact map_mono (le_sSup hK)
  unfold layerIn
  rw [← h, map_map, map_map, OddQuot.subtype_comp_subgroupMap]

omit [Finite G] [Finite G'] in
theorem map_mem_coreActionKernel [Finite G] [Finite G'] (f : G →* G') {L : Subgroup G} {g : G}
    (hg : g ∈ coreActionKernel L) : f g ∈ coreActionKernel (L.map f) := by
  obtain ⟨hgN, hgL⟩ := mem_coreActionKernel.mp hg
  refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
  · rw [mem_normalizer_iff] at hgN ⊢
    intro y
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨g * l * g⁻¹, (hgN l).mp hl, by simp⟩
    · rintro ⟨l, hl, hly⟩
      refine ⟨g⁻¹ * l * g, (hgN _).mpr (by rwa [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]), ?_⟩
      rw [map_mul, map_mul, map_inv, hly]
      group
  · obtain ⟨l, hl, rfl⟩ := mem_map.mp hj
    have h1 := hgL l hl
    have h2 := map_oddCoreIn_le f L (mem_map_of_mem f h1)
    have h3 : (f l)⁻¹ * (f g)⁻¹ * f l * f g ∈ oddCoreIn (L.map f) := by
      simpa only [map_mul, map_inv] using h2
    exact h3

omit [Finite G] [Finite G'] in
theorem eq_one_of_isPerfect' {M Q : Type*} [Group M] [Group Q] [Group.IsPerfect M] (c : M →* Q)
    (hc : ∀ u v : M, c u * c v = c v * c u) (u : M) : c u = 1 := by
  have hle : commutator M ≤ c.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc g₁ g₂
  rw [Group.IsPerfect.commutator_eq_top] at hle
  exact hle (mem_top u)

omit [Finite G] [Finite G'] in
theorem commutator_mem_of_isPerfect {V N : Subgroup G} [Group.IsPerfect V] (hNV : N ≤ V)
    (hN : (N.subgroupOf V).Normal) {w : G} (hwV : w ∈ normalizer (V : Set G))
    (hA : ∀ v ∈ V, ∃ o ∈ N, ∃ z ∈ centralizer (V : Set G), v⁻¹ * w⁻¹ * v * w = o * z) :
    ∀ v ∈ V, v⁻¹ * w⁻¹ * v * w ∈ N := by
  have hwV' : ∀ v ∈ V, v⁻¹ * w⁻¹ * v * w ∈ V := by
    intro v hv
    have h1 := (mem_normalizer_iff.mp (inv_mem hwV) v).mp hv
    rw [inv_inv] at h1
    rw [show v⁻¹ * w⁻¹ * v * w = v⁻¹ * (w⁻¹ * v * w) by group]
    exact mul_mem (inv_mem hv) h1
  have hNc : ∀ (v : G), v ∈ V → ∀ o ∈ N, v⁻¹ * o * v ∈ N := by
    intro v hv o ho
    have h1 := hN.conj_mem ⟨o, hNV ho⟩ ho ⟨v, hv⟩⁻¹
    rw [mem_subgroupOf] at h1
    simpa only [coe_mul, coe_inv, inv_inv] using h1
  let δ : ↥V → ↥V := fun v => ⟨(v : G)⁻¹ * w⁻¹ * v * w, hwV' v v.2⟩
  have hcen : ∀ u v : ↥V, ((δ u : ↥V) : ↥V ⧸ N.subgroupOf V) * (v : ↥V ⧸ N.subgroupOf V) =
      (v : ↥V ⧸ N.subgroupOf V) * (δ u : ↥V ⧸ N.subgroupOf V) := by
    intro u v
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    obtain ⟨o, ho, z, hz, hoz⟩ := hA u u.2
    have hov : o⁻¹ * (v : G) * o ∈ V := mul_mem (mul_mem (inv_mem (hNV ho)) v.2) (hNV ho)
    have hzv : z⁻¹ * (o⁻¹ * (v : G) * o) * z = o⁻¹ * (v : G) * o := by
      rw [mul_assoc, mem_centralizer_iff.mp hz _ hov]
      group
    have h2 : (((δ u * v)⁻¹ * (v * δ u) : ↥V) : G) = (v : G)⁻¹ * o⁻¹ * v * o := by
      have h3 : ((δ u : ↥V) : G) = o * z := hoz
      simp only [coe_mul, coe_inv, h3]
      calc (o * z * (v : G))⁻¹ * ((v : G) * (o * z))
          = (v : G)⁻¹ * (z⁻¹ * (o⁻¹ * (v : G) * o) * z) := by group
        _ = (v : G)⁻¹ * o⁻¹ * v * o := by rw [hzv]; group
    rw [h2]
    exact mul_mem (hNc v v.2 o⁻¹ (inv_mem ho)) ho
  let c : ↥V →* ↥V ⧸ N.subgroupOf V :=
    { toFun := fun v => ((δ v : ↥V) : ↥V ⧸ N.subgroupOf V)
      map_one' := by
        have h1 : δ 1 = 1 := Subtype.ext (by simp [δ])
        simp only [h1, QuotientGroup.mk_one]
      map_mul' := by
        intro u v
        have h1 : δ (u * v) = v⁻¹ * δ u * v * δ v :=
          Subtype.ext (by simp only [δ, coe_mul, coe_inv]; group)
        simp only [h1, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [mul_assoc ((v : ↥V ⧸ N.subgroupOf V)⁻¹), hcen u v, ← mul_assoc, inv_mul_cancel,
          one_mul] }
  intro v hv
  have h1 := eq_one_of_isPerfect' c (fun u u' => hcen u (δ u')) ⟨v, hv⟩
  have h2 : ((δ ⟨v, hv⟩ : ↥V) : ↥V ⧸ N.subgroupOf V) = 1 := h1
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h2
  exact h2

omit [Finite G'] in
theorem mem_coreActionKernel_of_map [Finite G'] (f : G →* G') {L : Subgroup G}
    [Group.IsPerfect L] (hLc : L ≤ centralizer (f.ker : Set G)) {g : G}
    (hgN : g ∈ normalizer (L : Set G)) (hg : f g ∈ coreActionKernel (L.map f)) :
    g ∈ coreActionKernel L := by
  refine mem_coreActionKernel.mpr ⟨hgN, ?_⟩
  have hOL : oddCoreIn L ≤ L := map_subtype_le _
  have hN : ((oddCoreIn L).subgroupOf L).Normal := by
    rw [show (oddCoreIn L).subgroupOf L = pPrimeCore 2 L from
      comap_map_eq_self_of_injective L.subtype_injective _]
    infer_instance
  refine commutator_mem_of_isPerfect hOL hN hgN fun j hj => ?_
  have hjg : j⁻¹ * g⁻¹ * j * g ∈ L := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hgN) j).mp hj
    rw [inv_inv] at h1
    rw [show j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * j * g) by group]
    exact mul_mem (inv_mem hj) h1
  have h1 := (mem_coreActionKernel.mp hg).2 (f j) (mem_map_of_mem f hj)
  have h2 : f (j⁻¹ * g⁻¹ * j * g) ∈ (oddCoreIn L).map f := by
    rw [map_oddCoreIn_of_le_centralizer f hLc]
    have h1' : (f j)⁻¹ * (f g)⁻¹ * f j * f g ∈ oddCoreIn (L.map f) := h1
    simpa only [map_mul, map_inv] using h1'
  obtain ⟨o, ho, hoe⟩ := mem_map.mp h2
  refine ⟨o, ho, o⁻¹ * (j⁻¹ * g⁻¹ * j * g), ?_, by group⟩
  have hk : o⁻¹ * (j⁻¹ * g⁻¹ * j * g) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hoe, inv_mul_cancel]
  exact mem_centralizer_iff.mpr fun l hl => (mem_centralizer_iff.mp (hLc hl) _ hk).symm

omit [Finite G] [Finite G'] in
theorem map_inf_comap (f : G →* G') (L : Subgroup G) (M : Subgroup G') :
    (L ⊓ M.comap f).map f = L.map f ⊓ M := by
  apply le_antisymm
  · exact le_inf (map_mono inf_le_left) (map_le_iff_le_comap.mpr inf_le_right)
  · rintro y ⟨⟨l, hl, rfl⟩, hy⟩
    exact ⟨l, mem_inf.mpr ⟨hl, hy⟩, rfl⟩

theorem layerIn_eq_of_isPGroup {C C' : Subgroup G} (hCC' : C ≤ C')
    (hN : (C.subgroupOf C').Normal) (h2 : IsPGroup 2 (↥C' ⧸ C.subgroupOf C')) :
    layerIn C' = layerIn C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have : Group.IsNilpotent (↥C' ⧸ C.subgroupOf C') := h2.isNilpotent
    unfold layerIn
    refine map_le_iff_le_comap.mpr (sSup_le fun K hK => ?_)
    obtain ⟨hKN, hKc⟩ := CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient
      2 (C.subgroupOf C') K hK
    rw [← map_le_iff_le_comap]
    have hKC : K.map C'.subtype ≤ C := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := mem_map.mp hx
      exact hKN hk
    have h1 : IsPComponent 2 ((K.map C'.subtype).subgroupOf C) := by
      have h3 := (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
        (L := K.map C'.subtype) hCC' 2 Nat.prime_two).mp
      rw [show (K.map C'.subtype).subgroupOf C' = K from
        comap_map_eq_self_of_injective C'.subtype_injective K] at h3
      exact h3 hKc
    have h4 := map_mono (f := C.subtype)
      (show (K.map C'.subtype).subgroupOf C ≤ pLayer ↥C 2 from le_sSup h1)
    rwa [map_subgroupOf_eq_of_le hKC] at h4
  · have h1 := LBalance.pLayer_relative_normal_mono 2 C C' hCC'
    rwa [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h1

theorem map_fixedLayer_of_ker_le (f : G →* G') {L E : Subgroup G}
    (hLc : L ≤ centralizer (f.ker : Set G)) (hkE : f.ker ≤ E) (hk2 : IsPGroup 2 f.ker) :
    (GSLit.fixedLayer L E).map f = GSLit.fixedLayer (L.map f) (E.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := L ⊓ centralizer (E : Set G) with hC
  set C' := L ⊓ (centralizer ((E.map f : Subgroup G') : Set G')).comap f with hC'
  have hk : ∀ l ∈ C', ∀ e ∈ E, e⁻¹ * l * e * l⁻¹ ∈ f.ker := by
    intro l hl e he
    have h1 := mem_centralizer_iff.mp (mem_inf.mp hl).2 (f e) (mem_map_of_mem f he)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_assoc ((f e)⁻¹), ← h1]
    group
  have hconj : ∀ l ∈ C', ∀ e ∈ E, l * e * l⁻¹ ∈ E := by
    intro l hl e he
    rw [show l * e * l⁻¹ = e * (e⁻¹ * l * e * l⁻¹) by group]
    exact mul_mem he (hkE (hk l hl e he))
  have hCC' : C ≤ C' := by
    refine inf_le_inf_left _ fun l hl => ?_
    rw [mem_comap, mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hl e he]
  have hN : (C.subgroupOf C').Normal := by
    refine ⟨fun c hc l => ?_⟩
    rw [mem_subgroupOf] at hc ⊢
    obtain ⟨hcL, hcE⟩ := mem_inf.mp hc
    refine mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem (mul_mem (mem_inf.mp l.2).1 hcL) (inv_mem (mem_inf.mp l.2).1)
    · rw [mem_centralizer_iff]
      intro e he
      have hle : (l : G)⁻¹ * e * (l : G) ∈ E := by
        have h1 := hconj (l : G)⁻¹ (inv_mem l.2) e he
        rwa [inv_inv] at h1
      have h2 := mem_centralizer_iff.mp hcE _ hle
      simp only [coe_mul, coe_inv]
      calc e * ((l : G) * c * (l : G)⁻¹)
          = (l : G) * (((l : G)⁻¹ * e * (l : G)) * c) * (l : G)⁻¹ := by group
        _ = (l : G) * (c * ((l : G)⁻¹ * e * (l : G))) * (l : G)⁻¹ := by rw [h2]
        _ = (l : G) * c * (l : G)⁻¹ * e := by group
  have h2 : IsPGroup 2 (↥C' ⧸ C.subgroupOf C') := by
    obtain ⟨m, hm⟩ := hk2.exists_card_eq
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, coe_pow]
    refine mem_inf.mpr ⟨pow_mem (mem_inf.mp l.2).1 _, mem_centralizer_iff.mpr fun e he => ?_⟩
    have hfix : ∀ k ∈ f.ker, (l : G) * k * (l : G)⁻¹ = k := by
      intro k hk'
      rw [← mem_centralizer_iff.mp (hLc (mem_inf.mp l.2).1) k hk', mul_inv_cancel_right]
    set κ := e⁻¹ * (l : G) * e * (l : G)⁻¹ with hκ
    have hκk : κ ∈ f.ker := hk l l.2 e he
    have hpow : ∀ n : ℕ, (l : G) ^ n * e * ((l : G) ^ n)⁻¹ = e * κ ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', show (l : G) * (l : G) ^ n * e * ((l : G) * (l : G) ^ n)⁻¹ =
          (l : G) * ((l : G) ^ n * e * ((l : G) ^ n)⁻¹) * (l : G)⁻¹ by group, ih,
          show (l : G) * (e * κ ^ n) * (l : G)⁻¹ =
            ((l : G) * e * (l : G)⁻¹) * ((l : G) * κ ^ n * (l : G)⁻¹) by group,
          hfix _ (pow_mem hκk n), show (l : G) * e * (l : G)⁻¹ = e * κ by rw [hκ]; group,
          pow_succ']
        group
    have hκn : κ ^ (2 ^ m) = 1 := by
      have h3 := pow_card_eq_one' (G := f.ker) (x := ⟨κ, hκk⟩)
      rw [hm] at h3
      exact congrArg Subtype.val h3
    have h4 := hpow (2 ^ m)
    rw [hκn, mul_one] at h4
    calc e * (l : G) ^ 2 ^ m = (l : G) ^ 2 ^ m * e * ((l : G) ^ 2 ^ m)⁻¹ * (l : G) ^ 2 ^ m := by
          rw [h4]
      _ = (l : G) ^ 2 ^ m * e := by group
  have h3 : (L.map f) ⊓ centralizer ((E.map f : Subgroup G') : Set G') = C'.map f :=
    (map_inf_comap f L _).symm
  show (layerIn C).map f = layerIn ((L.map f) ⊓ centralizer ((E.map f : Subgroup G') : Set G'))
  rw [h3, ← map_layerIn_of_le_centralizer f (inf_le_left.trans hLc),
    layerIn_eq_of_isPGroup hCC' hN h2]

omit [Finite G] [Finite G'] in
theorem eq_of_map_eq_of_le_centralizer (f : G →* G') [Group.IsSolvable f.ker] {L₁ L₂ : Subgroup G}
    [Group.IsPerfect L₁] [Group.IsPerfect L₂] (h1 : L₁ ≤ centralizer (f.ker : Set G))
    (h2 : L₂ ≤ centralizer (f.ker : Set G)) (heq : L₁.map f = L₂.map f) : L₁ = L₂ := by
  have key : ∀ {M₁ M₂ : Subgroup G} [Group.IsPerfect M₁],
      M₂ ≤ centralizer (f.ker : Set G) → M₁.map f = M₂.map f → M₁ ≤ M₂ := by
    intro M₁ M₂ _ hM₂ hmap
    set U := M₂ ⊔ f.ker with hU
    have hM₁U : M₁ ≤ U := by
      intro m hm
      have h3 : f m ∈ M₂.map f := hmap ▸ mem_map_of_mem f hm
      obtain ⟨m₂, hm₂, he⟩ := mem_map.mp h3
      rw [show m = m₂ * (m₂⁻¹ * m) by group]
      refine mul_mem (mem_sup_left hm₂) (mem_sup_right ?_)
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    have hM₂U : M₂ ≤ U := le_sup_left
    have hUN : U ≤ normalizer (M₂ : Set G) := by
      refine sup_le le_normalizer fun k hk => centralizer_le_normalizer _ ?_
      exact mem_centralizer_iff.mpr fun m hm => (mem_centralizer_iff.mp (hM₂ hm) k hk).symm
    have : (M₂.subgroupOf U).Normal := (normal_subgroupOf_iff_le_normalizer hM₂U).mpr hUN
    let φ : ↥f.ker →* ↥U ⧸ M₂.subgroupOf U :=
      (QuotientGroup.mk' (M₂.subgroupOf U)).comp (inclusion le_sup_right)
    have hφ : Function.Surjective φ := by
      intro q
      obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have hu' : u ∈ (↑(M₂ ⊔ f.ker) : Set G) := hu
      rw [mul_normal] at hu'
      obtain ⟨m, hm, k, hk, rfl⟩ := hu'
      refine ⟨⟨k, hk⟩, ?_⟩
      show (QuotientGroup.mk (inclusion le_sup_right ⟨k, hk⟩) : ↥U ⧸ M₂.subgroupOf U) =
        QuotientGroup.mk ⟨m * k, hu⟩
      rw [QuotientGroup.eq, mem_subgroupOf]
      simp only [coe_mul, coe_inv, coe_inclusion]
      rw [show k⁻¹ * (m * k) = k⁻¹ * m * k by group]
      have h4 := (mem_normalizer_iff.mp (hUN (mem_sup_right (inv_mem hk))) m).mp hm
      rwa [inv_inv] at h4
    have : Group.IsSolvable (↥U ⧸ M₂.subgroupOf U) := Group.isSolvable_of_surjective hφ
    have : Group.IsPerfect (M₁.subgroupOf U) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hM₁U).symm.toMonoidHom)
        (subgroupOfEquivOfLe hM₁U).symm.surjective
    have h5 := CatalogueBLinearTwo.perfect_le_normal_of_solvable_quotient (M₂.subgroupOf U)
      (M₁.subgroupOf U)
    intro m hm
    exact h5 (show (⟨m, hM₁U hm⟩ : ↥U) ∈ M₁.subgroupOf U from hm)
  exact le_antisymm (key h2 heq) (key h1 heq.symm)

end General

section Star

variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']

omit [Finite G] [Finite G'] in
theorem map_mem_center (f : G →* G') (hf : Function.Surjective f) {z : G} (hz : z ∈ center G) :
    f z ∈ center G' := by
  rw [mem_center_iff]
  intro w
  obtain ⟨w', rfl⟩ := hf w
  rw [← map_mul, ← map_mul, mem_center_iff.mp hz w']

omit [Finite G] [Finite G'] in
theorem mem_center_of_commutator_mem_center {Q : Type*} [Group Q] (hq : IsQuasisimple Q) {x : Q}
    (hx : ∀ m : Q, ⁅x, m⁆ ∈ center Q) : x ∈ center Q := by
  obtain ⟨-, hs, a, b, hab⟩ := hq
  have hcen : QuotientGroup.mk' (center Q) x ∈ center (Q ⧸ center Q) := by
    rw [mem_center_iff]
    intro z
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have h1 := (QuotientGroup.eq_one_iff _).mpr (hx m)
    rw [← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Q ⧸ center Q)) with hbot | htop
  · rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
    exact hcen
  · exfalso
    apply hab
    have h2 : a ∈ center (Q ⧸ center Q) := htop ▸ mem_top a
    exact (mem_center_iff.mp h2 b).symm

theorem comap_fusionZStar_of_central (f : G →* G') (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center G) (hq : IsQuasisimple (G ⧸ pPrimeCore 2 G)) :
    (Open.fusionZStar G').comap f = Open.fusionZStar G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := CatalogueBCentralQuotient.primeCore_map 2 f hf hcentral
  ext x
  rw [mem_comap, OddQuot.mem_fusionZStar_iff, OddQuot.mem_fusionZStar_iff]
  constructor
  · intro h m
    have h1 : ∀ m' : G, ⁅QuotientGroup.mk' (pPrimeCore 2 G) x,
        QuotientGroup.mk' (pPrimeCore 2 G) m'⁆ ∈ center (G ⧸ pPrimeCore 2 G) := by
      intro m'
      have h2 := h (f m')
      rw [← map_commutatorElement, ← hO] at h2
      obtain ⟨o, ho, hoe⟩ := mem_map.mp h2
      have hk : o⁻¹ * ⁅x, m'⁆ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hoe, inv_mul_cancel]
      have h3 : QuotientGroup.mk' (pPrimeCore 2 G) ⁅x, m'⁆ =
          QuotientGroup.mk' (pPrimeCore 2 G) (o⁻¹ * ⁅x, m'⁆) := by
        have ho1 : QuotientGroup.mk' (pPrimeCore 2 G) o = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact ho
        rw [map_mul, map_inv, ho1, inv_one, one_mul]
      rw [← map_commutatorElement, h3]
      exact map_mem_center _ (QuotientGroup.mk'_surjective _) (hcentral hk)
    have h4 := mem_center_of_commutator_mem_center hq
      (x := QuotientGroup.mk' (pPrimeCore 2 G) x) (fun z => by
        obtain ⟨m', rfl⟩ := QuotientGroup.mk'_surjective _ z
        exact h1 m')
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.mp h4 (QuotientGroup.mk' (pPrimeCore 2 G) m)).symm
  · intro h y'
    obtain ⟨m, rfl⟩ := hf y'
    rw [← map_commutatorElement, ← hO]
    exact mem_map_of_mem f (h m)

theorem nonempty_fusionZStar_equiv_of_central (f : G →* G') (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center G) (hq : IsQuasisimple (G ⧸ pPrimeCore 2 G)) :
    Nonempty (G ⧸ Open.fusionZStar G ≃* G' ⧸ Open.fusionZStar G') := by
  set φ := (QuotientGroup.mk' (Open.fusionZStar G')).comp f with hφ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hφk : Open.fusionZStar G = φ.ker := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      comap_fusionZStar_of_central f hf hcentral hq]
  exact ⟨QuotientGroup.liftEquiv _ hφs hφk⟩

omit [Finite G'] in
theorem injective_of_central (f : G →* G') (hcentral : f.ker ≤ center G)
    (hk2 : IsPGroup 2 f.ker) (hZ : center (G ⧸ pPrimeCore 2 G) = ⊥) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  have h1 := map_mem_center (QuotientGroup.mk' (pPrimeCore 2 G)) (QuotientGroup.mk'_surjective _)
    (hcentral hk)
  rw [hZ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact mem_bot.mpr (B5a.eq_one_of_isPGroup_of_odd hk2
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hk h1)

omit [Finite G] [Finite G'] in
theorem nonempty_fusionZStar_equiv_of_pPrimeCore_equiv {X₁ X₂ : Type*} [Group X₁] [Group X₂]
    (e : X₁ ⧸ pPrimeCore 2 X₁ ≃* X₂ ⧸ pPrimeCore 2 X₂) :
    Nonempty (X₁ ⧸ Open.fusionZStar X₁ ≃* X₂ ⧸ Open.fusionZStar X₂) := by
  set Q₂ := X₂ ⧸ pPrimeCore 2 X₂
  let ψ₂ : X₂ →* Q₂ ⧸ center Q₂ :=
    (QuotientGroup.mk' (center Q₂)).comp (QuotientGroup.mk' (pPrimeCore 2 X₂))
  let ψ₁ : X₁ →* Q₂ ⧸ center Q₂ :=
    (QuotientGroup.mk' (center Q₂)).comp (e.toMonoidHom.comp (QuotientGroup.mk' _))
  have hs₂ : Function.Surjective ψ₂ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hs₁ : Function.Surjective ψ₁ :=
    (QuotientGroup.mk'_surjective _).comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hk₂ : Open.fusionZStar X₂ = ψ₂.ker := by
    ext x
    rw [OddQuot.mem_fusionZStar_iff, MonoidHom.mem_ker]
    change _ ↔ QuotientGroup.mk' (center Q₂) (QuotientGroup.mk' (pPrimeCore 2 X₂) x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_center_iff]
    constructor
    · intro h z
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ z
      have h1 := (QuotientGroup.eq_one_iff _).mpr (h m)
      rw [← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    · intro h m
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact (h _).symm
  have hk₁ : Open.fusionZStar X₁ = ψ₁.ker := by
    ext x
    rw [OddQuot.mem_fusionZStar_iff, MonoidHom.mem_ker]
    change _ ↔ QuotientGroup.mk' (center Q₂) (e (QuotientGroup.mk' (pPrimeCore 2 X₁) x)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_center_iff]
    constructor
    · intro h z
      obtain ⟨m, rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) z
      have h1 := (QuotientGroup.eq_one_iff _).mpr (h m)
      rw [← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm] at h1
      have h2 := congrArg e h1
      simp only [map_mul] at h2
      exact h2.symm
    · intro h m
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      apply e.injective
      simp only [map_mul]
      exact (h _).symm
  exact ⟨(QuotientGroup.liftEquiv _ hs₁ hk₁).trans (QuotientGroup.liftEquiv _ hs₂ hk₂).symm⟩

theorem nonempty_fusionZStar_equiv_map (f : G →* G') {L : Subgroup G}
    (hLc : L ≤ centralizer (f.ker : Set G)) (hq : IsQuasisimple (L ⧸ pPrimeCore 2 L)) :
    Nonempty (L ⧸ Open.fusionZStar L ≃* L.map f ⧸ Open.fusionZStar (L.map f)) :=
  nonempty_fusionZStar_equiv_of_central (f.subgroupMap L) (f.subgroupMap_surjective L)
    (ker_subgroupMap_le_center f hLc) hq

omit [Finite G'] in
theorem nonempty_pPrimeCore_equiv_map (f : G →* G') {L : Subgroup G}
    (hLc : L ≤ centralizer (f.ker : Set G)) (hk2 : IsPGroup 2 f.ker)
    (hZ : center (L ⧸ pPrimeCore 2 L) = ⊥) :
    Nonempty (L ⧸ pPrimeCore 2 L ≃* L.map f ⧸ pPrimeCore 2 (L.map f)) := by
  have hk2' : IsPGroup 2 (f.subgroupMap L).ker := by
    intro k
    have hk : ((k : ↥L) : G) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val ((MonoidHom.mem_ker).mp k.2)
    obtain ⟨n, hn⟩ := hk2 ⟨_, hk⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hinj := injective_of_central (f.subgroupMap L) (ker_subgroupMap_le_center f hLc) hk2' hZ
  exact ⟨UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
    (MulEquiv.ofBijective _ ⟨hinj, f.subgroupMap_surjective L⟩)⟩

end Star

end TwoQuot

end CFSG.ComponentClassification.GSThmB
