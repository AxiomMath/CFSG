module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Sec44

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

theorem sec46_conj_elemAbelian {S : Type} [Group S] {A : Subgroup S} (hA : IsElemAbelian 2 A)
    (g : S) : IsElemAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := by
  have hc : ∀ x ∈ A.map (MulAut.conj g).toMonoidHom, ∀ y ∈ A.map (MulAut.conj g).toMonoidHom,
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
    show g * u * g⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (g * u * g⁻¹)
    calc g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
      _ = g * (v * u) * g⁻¹ := by rw [sec44_comm hA hu hv]
      _ = g * v * g⁻¹ * (g * u * g⁻¹) := by group
  refine ⟨⟨⟨fun x y => Subtype.ext (hc x.1 x.2 y.1 y.2)⟩⟩, ?_⟩
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  show (g * u * g⁻¹) ^ 2 = 1
  have h2 : (g * u * g⁻¹) ^ 2 = g * u ^ 2 * g⁻¹ := by
    simp only [pow_two]
    group
  rw [h2, hA.2 u hu]
  group

theorem sec46_conj_card {S : Type} [Group S] (A : Subgroup S) (g : S) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulEquiv.injective _)

theorem sec46_conj_mem {S : Type} [Group S] {E : Subgroup S} [E.Normal] {a g : S}
    (hc : (g : S ⧸ E) * (a : S ⧸ E) = (a : S ⧸ E) * (g : S ⧸ E)) :
    a⁻¹ * (g * a * g⁻¹) ∈ E := by
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hc, mul_inv_cancel_right, inv_mul_cancel]

theorem sec46_card_comap {S : Type} [Group S] [Finite S] (E : Subgroup S) [E.Normal]
    (C : Subgroup (S ⧸ E)) :
    Nat.card (C.comap (QuotientGroup.mk' E)) = Nat.card E * Nat.card C := by
  have h1 : (C.comap (QuotientGroup.mk' E)).index = C.index :=
    Subgroup.index_comap_of_surjective C (QuotientGroup.mk'_surjective E)
  have hpos : 0 < C.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have key : Nat.card (C.comap (QuotientGroup.mk' E)) * C.index =
      (Nat.card E * Nat.card C) * C.index := by
    calc Nat.card (C.comap (QuotientGroup.mk' E)) * C.index
        = Nat.card (C.comap (QuotientGroup.mk' E)) * (C.comap (QuotientGroup.mk' E)).index := by
          rw [h1]
      _ = Nat.card S := Subgroup.card_mul_index (C.comap (QuotientGroup.mk' E))
      _ = Nat.card E * E.index := (Subgroup.card_mul_index E).symm
      _ = Nat.card E * Nat.card (S ⧸ E) := by rw [Subgroup.index_eq_card]
      _ = Nat.card E * (Nat.card C * C.index) := by rw [← Subgroup.card_mul_index C]
      _ = (Nat.card E * Nat.card C) * C.index := by ring
  exact Nat.eq_of_mul_eq_mul_right hpos key

theorem sec46_normalizes {S : Type} [Group S] [Finite S] {A E : Subgroup S} [E.Normal]
    (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8) (hE : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hAE4 : Nat.card (A ⊓ E : Subgroup S) = 4) (hCA : Subgroup.centralizer (A : Set S) ≤ A)
    {a : S} (haA : a ∈ A) (haE : a ∉ E) {g : S} (hg : a⁻¹ * (g * a * g⁻¹) ∈ E) :
    g ∈ Subgroup.normalizer (A : Set S) := by
  have hZA : (A ⊓ E).relIndex A = 2 := sec44_relIndex_two inf_le_left (by omega)
  have hdecA : ∀ x ∈ A, x ∈ A ⊓ E ∨ ∃ z ∈ A ⊓ E, x = a * z := by
    intro x hx
    by_cases hxZ : x ∈ A ⊓ E
    · exact Or.inl hxZ
    · exact Or.inr ⟨a⁻¹ * x, sec44_inv_mul_mem hZA haA
        (fun h => haE (Subgroup.mem_inf.mp h).2) hx hxZ, (mul_inv_cancel_left a x).symm⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup S, B = A.map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hBmem : ∀ x : S, x ∈ B ↔ ∃ y ∈ A, g * y * g⁻¹ = x := by
    intro x
    rw [hBdef]
    exact Subgroup.mem_map
  have hB8 : Nat.card B = 8 := by
    rw [hBdef, sec46_conj_card, hA8]
  have hBel : IsElemAbelian 2 B := by
    rw [hBdef]
    exact sec46_conj_elemAbelian hA g
  have hBle : B ≤ A ⊔ E := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hBmem _).mp hx
    rcases hdecA y hy with hyZ | ⟨z, hz, rfl⟩
    · exact Subgroup.mem_sup_right
        (Subgroup.Normal.conj_mem ‹E.Normal› y (Subgroup.mem_inf.mp hyZ).2 g)
    · have hzE : g * z * g⁻¹ ∈ E :=
        Subgroup.Normal.conj_mem ‹E.Normal› z (Subgroup.mem_inf.mp hz).2 g
      have hx' : g * (a * z) * g⁻¹ = a * ((a⁻¹ * (g * a * g⁻¹)) * (g * z * g⁻¹)) := by
        group
      rw [hx']
      exact mul_mem (Subgroup.mem_sup_left haA) (Subgroup.mem_sup_right (mul_mem hg hzE))
  rcases (sub_E8_of_AE hA hA8 hE hE8 ‹E.Normal› hAE4 hCA).2.2 B hBle hBel hB8 with hBA | hBE
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hgB : g * h * g⁻¹ ∈ B := (hBmem _).mpr ⟨h, hh, rfl⟩
      rw [hBA] at hgB
      exact hgB
    · intro hh
      have hgB : g * h * g⁻¹ ∈ B := by
        rw [hBA]
        exact hh
      obtain ⟨y, hy, hyh⟩ := (hBmem _).mp hgB
      have hyh' : y = h := by
        calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
          _ = g⁻¹ * (g * h * g⁻¹) * g := by rw [hyh]
          _ = h := by group
      rw [← hyh']
      exact hy
  ·
    exfalso
    have hAE : A ≤ E := by
      intro x hx
      have hxB : g * x * g⁻¹ ∈ B := (hBmem _).mpr ⟨x, hx, rfl⟩
      rw [hBE] at hxB
      have h3 := Subgroup.Normal.conj_mem ‹E.Normal› _ hxB g⁻¹
      have h4 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [h4] at h3
    rw [inf_eq_left.mpr hAE, hA8] at hAE4
    omega

theorem card_centralizer_quot_le_four {S : Type} [Group S] [Finite S] {A E : Subgroup S} [E.Normal]
    (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8) (hE : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hAE4 : Nat.card (A ⊓ E : Subgroup S) = 4) (hCA : Subgroup.centralizer (A : Set S) ≤ A)
    (hN : Nat.card (Subgroup.normalizer (A : Set S)) ≤ 32) {a : S} (haA : a ∈ A) (haE : a ∉ E) :
    Nat.card (Subgroup.centralizer ({(a : S ⧸ E)} : Set (S ⧸ E))) ≤ 4 := by
  have hDN : (Subgroup.centralizer ({(a : S ⧸ E)} : Set (S ⧸ E))).comap (QuotientGroup.mk' E) ≤
      Subgroup.normalizer (A : Set S) := by
    intro g hg
    apply sec46_normalizes hA hA8 hE hE8 hAE4 hCA haA haE
    apply sec46_conj_mem
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hg)
  have h1 := Subgroup.card_le_of_le hDN
  rw [sec46_card_comap E, hE8] at h1
  omega

end CFSG.EvenSporadicStandard.Fin76b
