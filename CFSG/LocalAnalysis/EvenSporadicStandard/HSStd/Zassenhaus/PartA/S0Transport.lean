module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

structure S0D (M : Type) [Group M] (E : Subgroup M) (z : M) where
  y : M
  u : M
  K₀ : Subgroup M
  Abar : Subgroup M
  eK₀ : ↥K₀ ≃* Equiv.Perm (Fin 5)
  eAbar : ↥Abar ≃* MulAut (alternatingGroup (Fin 6))
  y_mem : y ∈ normalizer (E : Set M)
  y_ord : orderOf y = 3
  zy : y * z = z * y
  card_Ey : Nat.card ↥(E ⊓ Cen y) = 4
  K₀_le : K₀ ≤ Cen y
  K₀_y : Cen y = zpowers y ⊔ K₀
  K₀_disj : Disjoint (zpowers y) K₀
  u_mem : u ∈ K₀
  u_swap : (eK₀ ⟨u, u_mem⟩).IsSwap
  card_Lu : Nat.card ↥(Cen u) = 2880
  Abar_le : Abar ≤ Cen u
  Abar_comp : Cen u = zpowers u ⊔ Abar
  Abar_disj : Disjoint (zpowers u) Abar
  y_J : y ∈ derivedIn Abar
  C_L_J : centralizer ((derivedIn Abar : Subgroup M) : Set M) = zpowers u
  tab_inner : ∀ x (hx : x ∈ Abar), x * x = 1 → x ≠ 1 → eAbar ⟨x, hx⟩ ∈ innR →
    Nat.card ↥(Cen x) = 7680 ∧ Nat.card ↥(Cen (u * x)) = 2880
  tab_S6 : ∀ x (hx : x ∈ Abar), x * x = 1 → x ≠ 1 → eAbar ⟨x, hx⟩ ∉ innR →
    (∃ a : alternatingGroup (Fin 6), orderOf a = 3 ∧ eAbar ⟨x, hx⟩ a = a) →
    (Nat.card ↥(Cen x) = 7680 ∧ Nat.card ↥(Cen (u * x)) = 2880) ∨
      (Nat.card ↥(Cen x) = 2880 ∧ Nat.card ↥(Cen (u * x)) = 7680)
  tab_PGL : ∀ x (hx : x ∈ Abar), x * x = 1 → x ≠ 1 → eAbar ⟨x, hx⟩ ∉ innR →
    (∀ a : alternatingGroup (Fin 6), orderOf a = 3 → eAbar ⟨x, hx⟩ a ≠ a) →
    Nat.card ↥(Cen x) = 2880 ∧ Nat.card ↥(Cen (u * x)) = 2880

section Dictionary

variable {M G : Type*} [Group M] [Group G]

theorem s0_map_cent {φ : M →* G} (hφ : Function.Injective φ) (y : M) :
    (Cen y).map φ = φ.range ⊓ Cen (φ y) := by
  ext z
  simp only [mem_map, mem_inf, MonoidHom.mem_range, mem_Cen]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul, ha]
  · rintro ⟨⟨a, rfl⟩, h⟩
    refine ⟨a, ?_, rfl⟩
    apply hφ
    rw [map_mul, map_mul]
    exact h

theorem s0_map_cent_set {φ : M →* G} (hφ : Function.Injective φ) (D : Subgroup M) :
    (centralizer (D : Set M)).map φ =
      φ.range ⊓ centralizer ((D.map φ : Subgroup G) : Set G) := by
  ext z
  simp only [mem_map, mem_inf, MonoidHom.mem_range, mem_centralizer_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, rfl⟩, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul, ha d hd]
  · rintro ⟨⟨a, rfl⟩, h⟩
    refine ⟨a, fun d hd => ?_, rfl⟩
    apply hφ
    rw [map_mul, map_mul]
    exact h _ ⟨d, hd, rfl⟩

theorem derivedIn_eq_commutator (A : Subgroup G) : derivedIn A = ⁅A, A⁆ := by
  unfold derivedIn
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem s0_map_derived {φ : M →* G} (A : Subgroup M) :
    (derivedIn A).map φ = derivedIn (A.map φ) := by
  rw [derivedIn_eq_commutator, derivedIn_eq_commutator, Subgroup.map_commutator]

theorem s0_map_disjoint {φ : M →* G} (hφ : Function.Injective φ) {A B : Subgroup M}
    (h : Disjoint A B) : Disjoint (A.map φ) (B.map φ) := by
  rw [disjoint_iff] at h ⊢
  rw [← Subgroup.map_inf_eq A B φ hφ, h, Subgroup.map_bot]

theorem s0_map_disjoint' {φ : M →* G} (hφ : Function.Injective φ) {A B : Subgroup M}
    (h : Disjoint (A.map φ) (B.map φ)) : Disjoint A B := by
  rw [disjoint_iff] at h ⊢
  rw [← Subgroup.map_inf_eq A B φ hφ] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ hφ).1 h

theorem s0_map_E_cent {φ : M →* G} (hφ : Function.Injective φ) (E : Subgroup M) (y : M) :
    E.map φ ⊓ Cen (φ y) = (E ⊓ Cen y).map φ := by
  ext z
  simp only [mem_inf, mem_map, mem_Cen]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, h⟩
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    apply hφ
    rw [map_mul, map_mul]
    exact h
  · rintro ⟨a, ⟨ha, h⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, by rw [← map_mul, ← map_mul, h]⟩

theorem s0_card_cent_map {φ : M →* G} (hφ : Function.Injective φ) (a : M) :
    Nat.card ↥(φ.range ⊓ Cen (φ a)) = Nat.card ↥(Cen a) := by
  rw [← s0_map_cent hφ]
  exact Subgroup.card_map_of_injective hφ

end Dictionary

section Forward

variable {M G : Type} [Group M] [Group G] [Finite G] {E : Subgroup M} {z : M}

noncomputable def S0D.toPA0 (d : S0D M E z) {φ : M →* G} (hφ : Function.Injective φ) (t : G) :
    PA0 φ.range t (E.map φ) (φ z) where
  y := φ d.y
  u := φ d.u
  K₀ := d.K₀.map φ
  Abar := d.Abar.map φ
  eK₀ := (Subgroup.equivMapOfInjective d.K₀ φ hφ).symm.trans d.eK₀
  eAbar := (Subgroup.equivMapOfInjective d.Abar φ hφ).symm.trans d.eAbar
  y_mem := by
    refine Subgroup.mem_inf.2 ⟨?_, ⟨d.y, rfl⟩⟩
    rw [mem_normalizer_iff]
    intro x
    have hn := mem_normalizer_iff.1 d.y_mem
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨d.y * a * d.y⁻¹, (hn a).1 ha, by simp⟩
    · rintro ⟨b, hb, hbx⟩
      have hx : x = φ (d.y⁻¹ * b * d.y) := by
        simp only [map_mul, map_inv]
        rw [hbx]
        group
      refine ⟨d.y⁻¹ * b * d.y, (hn _).2 ?_, hx.symm⟩
      simpa [mul_assoc] using hb
  y_ord := (orderOf_injective φ hφ d.y).trans d.y_ord
  zy := by rw [← map_mul, ← map_mul, d.zy]
  card_Ey := by
    rw [s0_map_E_cent hφ, Subgroup.card_map_of_injective hφ]
    exact d.card_Ey
  K₀_le := by
    rw [← s0_map_cent hφ]
    exact Subgroup.map_mono d.K₀_le
  K₀_y := by
    rw [← s0_map_cent hφ, d.K₀_y, Subgroup.map_sup, MonoidHom.map_zpowers]
  K₀_disj := by
    rw [← MonoidHom.map_zpowers]
    exact s0_map_disjoint hφ d.K₀_disj
  u_mem := Subgroup.mem_map_of_mem φ d.u_mem
  u_swap := by
    have h : (Subgroup.equivMapOfInjective d.K₀ φ hφ).symm
        ⟨φ d.u, Subgroup.mem_map_of_mem φ d.u_mem⟩ = ⟨d.u, d.u_mem⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simpa [MulEquiv.trans_apply, h] using d.u_swap
  card_Lu := by
    rw [s0_card_cent_map hφ]
    exact d.card_Lu
  Abar_le := by
    rw [← s0_map_cent hφ]
    exact Subgroup.map_mono d.Abar_le
  Abar_comp := by
    rw [← s0_map_cent hφ, d.Abar_comp, Subgroup.map_sup, MonoidHom.map_zpowers]
  Abar_disj := by
    rw [← MonoidHom.map_zpowers]
    exact s0_map_disjoint hφ d.Abar_disj
  y_J := by
    rw [← s0_map_derived]
    exact Subgroup.mem_map_of_mem φ d.y_J
  C_L_J := by
    rw [← s0_map_derived, ← s0_map_cent_set hφ, d.C_L_J, MonoidHom.map_zpowers]
  tab_inner := by
    rintro _ ⟨a, ha, rfl⟩ hx2 hx1 hinn
    have hE : ((Subgroup.equivMapOfInjective d.Abar φ hφ).symm.trans d.eAbar)
        ⟨φ a, Subgroup.mem_map_of_mem φ ha⟩ = d.eAbar ⟨a, ha⟩ := by
      show d.eAbar ((Subgroup.equivMapOfInjective d.Abar φ hφ).symm _) = _
      congr 1
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hE] at hinn
    have ha2 : a * a = 1 := hφ (by rw [map_mul, hx2, map_one])
    have ha1 : a ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have := d.tab_inner a ha ha2 ha1 hinn
    rw [← map_mul, s0_card_cent_map hφ, s0_card_cent_map hφ]
    exact this
  tab_S6 := by
    rintro _ ⟨a, ha, rfl⟩ hx2 hx1 hnot hfix
    have hE : ((Subgroup.equivMapOfInjective d.Abar φ hφ).symm.trans d.eAbar)
        ⟨φ a, Subgroup.mem_map_of_mem φ ha⟩ = d.eAbar ⟨a, ha⟩ := by
      show d.eAbar ((Subgroup.equivMapOfInjective d.Abar φ hφ).symm _) = _
      congr 1
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hE] at hnot hfix
    have ha2 : a * a = 1 := hφ (by rw [map_mul, hx2, map_one])
    have ha1 : a ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have := d.tab_S6 a ha ha2 ha1 hnot hfix
    rw [← map_mul, s0_card_cent_map hφ, s0_card_cent_map hφ]
    exact this
  tab_PGL := by
    rintro _ ⟨a, ha, rfl⟩ hx2 hx1 hnot hfix
    have hE : ((Subgroup.equivMapOfInjective d.Abar φ hφ).symm.trans d.eAbar)
        ⟨φ a, Subgroup.mem_map_of_mem φ ha⟩ = d.eAbar ⟨a, ha⟩ := by
      show d.eAbar ((Subgroup.equivMapOfInjective d.Abar φ hφ).symm _) = _
      congr 1
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hE] at hnot hfix
    have ha2 : a * a = 1 := hφ (by rw [map_mul, hx2, map_one])
    have ha1 : a ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have := d.tab_PGL a ha ha2 ha1 hnot hfix
    rw [← map_mul, s0_card_cent_map hφ, s0_card_cent_map hφ]
    exact this

end Forward

section Restriction

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E : Subgroup G} {z : G}

omit [Finite G] in
theorem card_cent_L (x : ↥L) :
    Nat.card ↥(Cen x) = Nat.card ↥(L ⊓ Cen (x : G)) := by
  have := s0_card_cent_map L.subtype_injective x
  rw [Subgroup.range_subtype] at this
  exact this.symm

omit [Finite G] in
theorem map_cent_L (y : ↥L) : (Cen y).map L.subtype = L ⊓ Cen (y : G) := by
  rw [s0_map_cent L.subtype_injective, Subgroup.range_subtype]
  rfl

noncomputable def S0D.ofPA0 (a : PA0 L t E z) (hEL : E ≤ L) (hzL : z ∈ L) :
    S0D ↥L (E.subgroupOf L) ⟨z, hzL⟩ :=
  have hφ : Function.Injective L.subtype := L.subtype_injective
  have hy : a.y ∈ L := (Subgroup.mem_inf.1 a.y_mem).2
  have hu : a.u ∈ L := (a.Abar_le.trans (inf_le_left : _ ≤ L)) |> fun _ =>
    (Subgroup.mem_inf.1 (a.K₀_le a.u_mem)).1
  have hKL : a.K₀ ≤ L := a.K₀_le.trans inf_le_left
  have hAL : a.Abar ≤ L := a.Abar_le.trans inf_le_left
  have mapK : (a.K₀.subgroupOf L).map L.subtype = a.K₀ := Subgroup.map_subgroupOf_eq_of_le hKL
  have mapA : (a.Abar.subgroupOf L).map L.subtype = a.Abar := Subgroup.map_subgroupOf_eq_of_le hAL
  have mapE : (E.subgroupOf L).map L.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEL
  have hKcent : a.K₀.subgroupOf L ≤ Cen (⟨a.y, hy⟩ : ↥L) := by
    rw [← Subgroup.map_le_map_iff_of_injective hφ, mapK, map_cent_L]
    exact a.K₀_le
  have hAcent : a.Abar.subgroupOf L ≤ Cen (⟨a.u, hu⟩ : ↥L) := by
    rw [← Subgroup.map_le_map_iff_of_injective hφ, mapA, map_cent_L]
    exact a.Abar_le
  have mapDer : (derivedIn (a.Abar.subgroupOf L)).map L.subtype = derivedIn a.Abar := by
    rw [s0_map_derived, mapA]
  { y := ⟨a.y, hy⟩
    u := ⟨a.u, hu⟩
    K₀ := a.K₀.subgroupOf L
    Abar := a.Abar.subgroupOf L
    eK₀ := (Subgroup.subgroupOfEquivOfLe hKL).trans a.eK₀
    eAbar := (Subgroup.subgroupOfEquivOfLe hAL).trans a.eAbar
    y_mem := by
      rw [mem_normalizer_iff]
      intro x
      have hn := mem_normalizer_iff.1 (Subgroup.mem_inf.1 a.y_mem).1 (x : G)
      simpa [Subgroup.mem_subgroupOf] using hn
    y_ord := by
      rw [Subgroup.orderOf_mk]
      exact a.y_ord
    zy := Subtype.ext a.zy
    card_Ey := by
      rw [← Subgroup.card_map_of_injective hφ, Subgroup.map_inf_eq _ _ _ hφ, mapE, map_cent_L]
      have h : E ⊓ (L ⊓ Cen a.y) = E ⊓ Cen a.y := by rw [← inf_assoc, inf_of_le_left hEL]
      show Nat.card ↥(E ⊓ (L ⊓ Cen a.y)) = 4
      rw [h]
      exact a.card_Ey
    K₀_le := hKcent
    K₀_y := by
      apply Subgroup.map_injective hφ
      rw [map_cent_L, Subgroup.map_sup, MonoidHom.map_zpowers, mapK]
      exact a.K₀_y
    K₀_disj := by
      refine s0_map_disjoint' hφ ?_
      rw [MonoidHom.map_zpowers, mapK]
      exact a.K₀_disj
    u_mem := a.u_mem
    u_swap := a.u_swap
    card_Lu := by
      rw [card_cent_L]
      exact a.card_Lu
    Abar_le := hAcent
    Abar_comp := by
      apply Subgroup.map_injective hφ
      rw [map_cent_L, Subgroup.map_sup, MonoidHom.map_zpowers, mapA]
      exact a.Abar_comp
    Abar_disj := by
      refine s0_map_disjoint' hφ ?_
      rw [MonoidHom.map_zpowers, mapA]
      exact a.Abar_disj
    y_J := by
      refine (Subgroup.mem_map_iff_mem hφ).1 ?_
      rw [mapDer]
      exact a.y_J
    C_L_J := by
      apply Subgroup.map_injective hφ
      rw [s0_map_cent_set hφ, mapDer, Subgroup.range_subtype, MonoidHom.map_zpowers]
      exact a.C_L_J
    tab_inner := fun x hx hx2 hx1 hinn => by
      have := a.tab_inner (x : G) hx (congrArg Subtype.val hx2)
        (fun h => hx1 (Subtype.ext h)) hinn
      rw [card_cent_L x, card_cent_L ((⟨a.u, hu⟩ : ↥L) * x)]
      exact this
    tab_S6 := fun x hx hx2 hx1 hnot hfix => by
      have := a.tab_S6 (x : G) hx (congrArg Subtype.val hx2)
        (fun h => hx1 (Subtype.ext h)) hnot hfix
      rw [card_cent_L x, card_cent_L ((⟨a.u, hu⟩ : ↥L) * x)]
      exact this
    tab_PGL := fun x hx hx2 hx1 hnot hfix => by
      have := a.tab_PGL (x : G) hx (congrArg Subtype.val hx2)
        (fun h => hx1 (Subtype.ext h)) hnot hfix
      rw [card_cent_L x, card_cent_L ((⟨a.u, hu⟩ : ↥L) * x)]
      exact this }

end Restriction

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
