module

public import CFSG.CGT.A8S.TopData
public import CFSG.CGT.A8S.TopPerm
public import CFSG.CGT.A8S.TopSylow

public section

namespace CFSG.CGT.A8S

open Equiv Equiv.Perm CFSG.CGT.Timmesfeld75 CFSG.Holt.General Perm8

variable {G : Type} [Group G]

theorem exists_translA_of_mem {T X : Subgroup G} (φ : ↥X ≃* alternatingGroup (Fin 8))
    (hφ : ∀ x : ↥X, (x : G) ∈ T ↔
      ∃ c : Fin 8, ((φ x : alternatingGroup (Fin 8)) : Perm (Fin 8)) = transl c)
    {t : G} (ht : t ∈ T) (ht1 : t ≠ 1) (htX : t ∈ X) :
    ∃ c : Fin 8, c ≠ 0 ∧ φ ⟨t, htX⟩ = translA c := by
  obtain ⟨c, hc⟩ := (hφ ⟨t, htX⟩).1 ht
  refine ⟨c, fun hc0 => ht1 ?_, Subtype.ext hc⟩
  have h1 : φ ⟨t, htX⟩ = 1 := Subtype.ext (by rw [hc, hc0, transl_zero]; rfl)
  exact congrArg Subtype.val (φ.injective (h1.trans (map_one φ).symm))

theorem card_centralizer_eq_of_mulEquiv {T X : Subgroup G} (hT : IsWC T)
    (hX : Subgroup.normalizer (T : Set G) ≤ X) (φ : ↥X ≃* alternatingGroup (Fin 8))
    (hφ : ∀ x : ↥X, (x : G) ∈ T ↔
      ∃ c : Fin 8, ((φ x : alternatingGroup (Fin 8)) : Perm (Fin 8)) = transl c)
    {z : G} (hz : z ∈ T) (hz1 : z ≠ 1) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) = 192 := by
  have hzX : z ∈ X := hX (Subgroup.le_normalizer hz)
  have hCX : Subgroup.centralizer ({z} : Set G) ≤ X :=
    (hT.centralizer_le_normalizer hz hz1).trans hX
  obtain ⟨c, hc0, hc⟩ := exists_translA_of_mem φ hφ hz hz1 hzX
  have h1 := card_centralizer_subtype X ⟨z, hzX⟩
  rw [inf_eq_right.2 hCX] at h1
  rw [← h1, card_centralizer_mulEquiv φ, hc]
  exact card_centralizer_eq_of_forall_ne (translA_sq c) (transl_apply_ne hc0)

theorem ninetySix_le_card_inf_centralizer {X : Subgroup G} (φ : ↥X ≃* alternatingGroup (Fin 8))
    {y : G} (hyX : y ∈ X) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) :
    96 ≤ Nat.card ↥(X ⊓ Subgroup.centralizer ({y} : Set G)) := by
  have e2 : (⟨y, hyX⟩ : ↥X) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hy2)
  have e1 : (⟨y, hyX⟩ : ↥X) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  rw [← card_centralizer_subtype X ⟨y, hyX⟩, card_centralizer_mulEquiv φ]
  exact ninetySix_le_card_centralizer (by rw [← map_pow, e2, map_one])
    (fun h => e1 (φ.injective (h.trans (map_one φ).symm)))

theorem exists_sq_eq_of_mem {T X : Subgroup G} (hX : Subgroup.normalizer (T : Set G) ≤ X)
    (φ : ↥X ≃* alternatingGroup (Fin 8))
    (hφ : ∀ x : ↥X, (x : G) ∈ T ↔
      ∃ c : Fin 8, ((φ x : alternatingGroup (Fin 8)) : Perm (Fin 8)) = transl c)
    {z t : G} (hz : z ∈ T) (hz1 : z ≠ 1) (ht : t ∈ T) :
    ∃ s ∈ Subgroup.centralizer ({z} : Set G), s ^ 2 = t := by
  by_cases ht1 : t = 1
  · exact ⟨1, Subgroup.one_mem _, by rw [ht1, one_pow]⟩
  have hzX : z ∈ X := hX (Subgroup.le_normalizer hz)
  have htX : t ∈ X := hX (Subgroup.le_normalizer ht)
  obtain ⟨c, hc0, hc⟩ := exists_translA_of_mem φ hφ hz hz1 hzX
  obtain ⟨c', hc'0, hc'⟩ := exists_translA_of_mem φ hφ ht ht1 htX
  obtain ⟨σ, hσc, hσ2⟩ := exists_sq_eq_translA hc0 hc'0
  refine ⟨(φ.symm σ : G), Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
  · have h : φ.symm σ * ⟨z, hzX⟩ = ⟨z, hzX⟩ * φ.symm σ :=
      φ.injective (by rw [map_mul, map_mul, φ.apply_symm_apply, hc, hσc])
    exact congrArg Subtype.val h
  · have h : φ.symm σ ^ 2 = ⟨t, htX⟩ :=
      φ.injective (by rw [map_pow, φ.apply_symm_apply, hσ2, hc'])
    rw [← Subgroup.coe_pow, h]

theorem le_of_card_le_two_mul {T X : Subgroup G} [Finite G] (hT : IsWC T)
    (hX : Subgroup.normalizer (T : Set G) ≤ X) (φ : ↥X ≃* alternatingGroup (Fin 8))
    (hφ : ∀ x : ↥X, (x : G) ∈ T ↔
      ∃ c : Fin 8, ((φ x : alternatingGroup (Fin 8)) : Perm (Fin 8)) = transl c)
    {z : G} (hz : z ∈ T) (hz1 : z ≠ 1) {U : Subgroup G}
    (hU : U ≤ Subgroup.centralizer ({z} : Set G))
    (hcard : Nat.card (Subgroup.centralizer ({z} : Set G)) ≤ 2 * Nat.card U) : T ≤ U := by
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  have hidx := Subgroup.card_mul_index (U.subgroupOf C)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv] at hidx
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hi0 : (U.subgroupOf C).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : (U.subgroupOf C).index ≤ 2 := by
    by_contra hlt
    have h3 : Nat.card U * 3 ≤ Nat.card U * (U.subgroupOf C).index :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  intro t ht
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_mul_comm hT.1 ht hz)
  obtain h1 | h2 : (U.subgroupOf C).index = 1 ∨ (U.subgroupOf C).index = 2 := by omega
  · have hmem : (⟨t, htC⟩ : C) ∈ U.subgroupOf C := Subgroup.index_eq_one.1 h1 ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem
  · obtain ⟨s, hsC, hs⟩ := exists_sq_eq_of_mem hX φ hφ hz hz1 ht
    have hmem := Subgroup.sq_mem_of_index_two h2 ⟨s, hsC⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at hmem
    rwa [hs] at hmem

theorem mem_of_conjSubgroup_le {T X : Subgroup G} (hT : IsWC T) (hT8 : Nat.card T = 8)
    (hX : Subgroup.normalizer (T : Set G) ≤ X) (φ : ↥X ≃* alternatingGroup (Fin 8))
    (hφ : ∀ x : ↥X, (x : G) ∈ T ↔
      ∃ c : Fin 8, ((φ x : alternatingGroup (Fin 8)) : Perm (Fin 8)) = transl c)
    {g : G} (hg : conjSubgroup g⁻¹ T ≤ X) : g ∈ X := by
  have hmemT' : ∀ u : G, u ∈ conjSubgroup g⁻¹ T ↔ g * u * g⁻¹ ∈ T := fun u => by
    rw [mem_conjSubgroup, inv_inv]
  set E : Subgroup (alternatingGroup (Fin 8)) :=
    ((conjSubgroup g⁻¹ T).subgroupOf X).map φ.toMonoidHom with hE
  have hE8 : Nat.card E = 8 := by
    rw [hE, Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hg).toEquiv, conjSubgroup,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hT8]
  have hu2 : ∀ u : ↥X, (u : G) ∈ conjSubgroup g⁻¹ T → u ^ 2 = 1 := by
    intro u hu
    have h2 : (g * u * g⁻¹) ^ 2 = 1 := hT.1.2 _ ((hmemT' u).1 hu)
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have h3 : g * (u : G) ^ 2 * g⁻¹ = 1 := by rw [← h2, sq, sq]; group
    have h4 : (u : G) ^ 2 = g⁻¹ * (g * (u : G) ^ 2 * g⁻¹) * g := by group
    rw [h4, h3]
    group
  have hE2 : ∀ e ∈ E, e ^ 2 = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hu2 u (Subgroup.mem_subgroupOf.1 hu), map_one]
  obtain ⟨_, ⟨u, hu, rfl⟩, hfree⟩ := exists_forall_ne_of_card_eq_eight hE8 hE2
  have huT : g * u * g⁻¹ ∈ T := (hmemT' u).1 (Subgroup.mem_subgroupOf.1 hu)
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := T)).1 (fun h => by
    rw [h, Subgroup.card_bot] at hT8
    omega)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzX : z ∈ X := hX (Subgroup.le_normalizer hz)
  obtain ⟨c, hc0, hc⟩ := exists_translA_of_mem φ hφ hz hz1' hzX
  have he2 : φ u ^ 2 = 1 := by rw [← map_pow, hu2 u (Subgroup.mem_subgroupOf.1 hu), map_one]
  obtain ⟨π, hπ⟩ := exists_conj_eq_of_forall_ne he2 hfree (translA_sq c) (transl_apply_ne hc0)
  set x : ↥X := φ.symm π with hxdef
  have hxu : x * ⟨z, hzX⟩ * x⁻¹ = u := φ.injective (by
    rw [map_mul, map_mul, map_inv, hxdef, φ.apply_symm_apply, hc]
    exact hπ)
  have hxu' : (x : G) * z * (x : G)⁻¹ = u := congrArg Subtype.val hxu
  have hu1 : (u : G) ≠ 1 := by
    intro h1
    have h1' : u = 1 := Subtype.ext h1
    apply hfree 0
    rw [h1', map_one]
    rfl
  have hne : T ⊓ conjSubgroup (g * x) T ≠ ⊥ := by
    rw [Ne, Subgroup.eq_bot_iff_forall]
    intro hbot
    apply hu1
    have h1 : g * u * g⁻¹ ∈ conjSubgroup (g * x) T := by
      rw [mem_conjSubgroup]
      have h2 : (g * x)⁻¹ * (g * u * g⁻¹) * (g * x) = z := by
        rw [← hxu']
        group
      rw [h2]
      exact hz
    have h3 := hbot _ ⟨huT, h1⟩
    calc (u : G) = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  have hgx : g * x ∈ X := hX (mem_normalizer_of_conjSubgroup_eq (hT.conj_eq_of_inf_ne_bot hne))
  have h := X.mul_mem hgx (X.inv_mem x.2)
  rwa [mul_inv_cancel_right] at h

theorem mem_of_conj_mem_of_mulEquiv_a8 [Finite G] {T X : Subgroup G} (hT : IsWC T)
    (hT8 : Nat.card T = 8) (hX : Subgroup.normalizer (T : Set G) ≤ X)
    (φ : ↥X ≃* alternatingGroup (Fin 8))
    (hφ : ∀ x : ↥X, (x : G) ∈ T ↔
      ∃ c : Fin 8, ((φ x : alternatingGroup (Fin 8)) : Perm (Fin 8)) = transl c)
    {z : G} (hz : z ∈ T) (hz1 : z ≠ 1) {g : G} (hg : g⁻¹ * z * g ∈ X) : g ∈ X := by
  have hz2 : z ^ 2 = 1 := hT.1.2 z hz
  have hy2 : (g⁻¹ * z * g) ^ 2 = 1 := by
    rw [show (g⁻¹ * z * g) ^ 2 = g⁻¹ * z ^ 2 * g by rw [sq, sq]; group, hz2]
    group
  have hy1 : g⁻¹ * z * g ≠ 1 := fun h => hz1 (by
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  set U := conjSubgroup g (X ⊓ Subgroup.centralizer ({g⁻¹ * z * g} : Set G)) with hUdef
  have hUC : U ≤ Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    rw [hUdef, mem_conjSubgroup] at hu
    have h := Subgroup.mem_centralizer_singleton_iff.1 hu.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * z = g * (g⁻¹ * u * g * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
      _ = z * u := by group
  have hUcard : Nat.card U =
      Nat.card ↥(X ⊓ Subgroup.centralizer ({g⁻¹ * z * g} : Set G)) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have h96 := ninetySix_le_card_inf_centralizer φ hg hy2 hy1
  have h192 := card_centralizer_eq_of_mulEquiv hT hX φ hφ hz hz1
  have hTU : T ≤ U := le_of_card_le_two_mul hT hX φ hφ hz hz1 hUC (by omega)
  refine mem_of_conjSubgroup_le hT hT8 hX φ hφ fun x hx => ?_
  rw [mem_conjSubgroup, inv_inv] at hx
  have h := hTU hx
  rw [hUdef, mem_conjSubgroup] at h
  have h' := h.1
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h'

theorem eq_top_or_nonempty_mulEquiv_alt9 [Finite G] [IsSimpleGroup G]
    (hHoltA9 : HoltA9Statement) {T H : Subgroup G} (h : A8Hyp T H) {X : Subgroup G}
    (hX : Subgroup.normalizer (T : Set G) ≤ X) (φ : ↥X ≃* alternatingGroup (Fin 8))
    (hφ : ∀ x : ↥X, (x : G) ∈ T ↔
      ∃ c : Fin 8, ((φ x : alternatingGroup (Fin 8)) : Perm (Fin 8)) = transl c) :
    X = ⊤ ∨ Nonempty (G ≃* alternatingGroup (Fin 9)) := by
  by_cases hXtop : X = ⊤
  · exact Or.inl hXtop
  right
  have hT8 : Nat.card T = 8 := CFSG.CGT.T75P.A8Cfg.card_T ⟨h.le, h.wc, h.nat, h.compl, h.odd⟩
  obtain ⟨S, hTS, hcard, z, hzT, hz1, hZ⟩ := exists_sylow_of_a8Hyp h
  have hSz : ∀ s ∈ (S : Subgroup G), s * z = z * s := fun s hs =>
    ((hZ z (hTS hzT)).mpr (Or.inr rfl) s hs).symm
  have hz2 : z ^ 2 = 1 := h.wc.1.2 z hzT
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
  have hzX : z ∈ X := hX (Subgroup.le_normalizer hzT)
  have hTrip : IsHoltTriple G (G ⧸ X) z ((1 : G) : G ⧸ X) := by
    refine ⟨inferInstance, orderOf_eq_prime hz2 hz1, fun ω => ?_,
      ⟨S, hTS hzT, fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hSz s hs)⟩⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, QuotientGroup.eq, mul_one,
      show (z * g)⁻¹ * g = g⁻¹ * z * g by rw [mul_inv_rev, hzinv], Subgroup.inv_mem_iff]
    exact ⟨fun hg => mem_of_conj_mem_of_mulEquiv_a8 h.wc hT8 hX φ hφ hzT hz1 hg,
      fun hg => X.mul_mem (X.mul_mem (X.inv_mem hg) hzX) hg⟩
  exact (hHoltA9 G X hXtop S z hcard hZ hTrip).2

end CFSG.CGT.A8S
