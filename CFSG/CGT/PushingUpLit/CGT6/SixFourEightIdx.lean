module

public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.Open CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G]

variable [Finite G]

theorem card_index_transfer {U V A : Subgroup G} {t : G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V)
    (ht : t ∈ A) (hsup : U ⊔ (V ⊓ Subgroup.centralizer (A : Set G)) = V) :
    Nat.card V * Nat.card ↥(U ⊓ Subgroup.centralizer ({t} : Set G)) =
      Nat.card U * Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) := by
  set C : Subgroup G := V ⊓ Subgroup.centralizer (A : Set G) with hC
  have hCt : C ≤ Subgroup.centralizer ({t} : Set G) := fun c hc =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]
      exact Subgroup.mem_centralizer_iff.mp hc.2 t ht
  have hcomm1 : ∀ x ∈ U, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm' hV (hUV hx) hy.1
  have e1 := card_sup_mul_card_inf' hcomm1
  rw [hsup] at e1
  have hcomm2 : ∀ x ∈ U ⊓ Subgroup.centralizer ({t} : Set G), ∀ y ∈ C, x * y = y * x :=
    fun x hx y hy => hcomm1 x hx.1 y hy
  have e2 := card_sup_mul_card_inf' hcomm2
  have hsup2 : (U ⊓ Subgroup.centralizer ({t} : Set G)) ⊔ C =
      V ⊓ Subgroup.centralizer ({t} : Set G) := by
    apply le_antisymm
    · exact sup_le (inf_le_inf_right _ hUV) (le_inf (inf_le_left : C ≤ V) hCt)
    · intro v hv
      have hvV : v ∈ U ⊔ C := by rw [hsup]; exact hv.1
      obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_of_mem_sup' hcomm1 hvV
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hu, ?_⟩) (Subgroup.mem_sup_right hc)
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rw [Set.mem_singleton_iff.mp hy]
      have h1 : t * (u * c) = (u * c) * t := Subgroup.mem_centralizer_iff.mp hv.2 t (Set.mem_singleton t)
      have h2 : t * c = c * t := Subgroup.mem_centralizer_iff.mp (hCt hc) t (Set.mem_singleton t)
      apply mul_right_cancel (b := c)
      calc t * u * c = t * (u * c) := by group
        _ = (u * c) * t := h1
        _ = u * (c * t) := by group
        _ = u * (t * c) := by rw [h2]
        _ = u * t * c := by group
  have hinf2 : (U ⊓ Subgroup.centralizer ({t} : Set G)) ⊓ C = U ⊓ C := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨⟨a, _⟩, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨⟨a, hCt c⟩, c⟩⟩
  rw [hsup2, hinf2] at e2
  have hCpos : 0 < Nat.card C := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hCpos
  calc Nat.card V * Nat.card ↥(U ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card C
      = Nat.card V * (Nat.card ↥(U ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card C) := by ring
    _ = Nat.card V * (Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card ↥(U ⊓ C)) := by
        rw [← e2]
    _ = Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) * (Nat.card V * Nat.card ↥(U ⊓ C)) := by
        ring
    _ = Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) * (Nat.card U * Nat.card C) := by
        rw [e1]
    _ = Nat.card U * Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card C := by ring


omit [Finite G] in
theorem card_inf_centralizer_conj {V : Subgroup G} [V.Normal] (g t : G) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G)) =
      Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) := by
  have hmap : (V ⊓ Subgroup.centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom =
      V ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyV, hyt⟩, rfl⟩
      refine ⟨(inferInstance : V.Normal).conj_mem y hyV g, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      rw [Set.mem_singleton_iff.mp hz]
      have h1 := Subgroup.mem_centralizer_iff.mp hyt t (Set.mem_singleton t)
      show g * t * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * t * g⁻¹)
      calc g * t * g⁻¹ * (g * y * g⁻¹) = g * (t * y) * g⁻¹ := by group
        _ = g * (y * t) * g⁻¹ := by rw [h1]
        _ = g * y * g⁻¹ * (g * t * g⁻¹) := by group
    · rintro ⟨hxV, hxu⟩
      refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, ?_⟩
      · have := (inferInstance : V.Normal).conj_mem x hxV g⁻¹
        simpa using this
      · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
        rw [Set.mem_singleton_iff.mp hz]
        have h1 := Subgroup.mem_centralizer_iff.mp hxu (g * t * g⁻¹) (Set.mem_singleton _)
        calc t * (g⁻¹ * x * g) = g⁻¹ * ((g * t * g⁻¹) * x) * g := by group
          _ = g⁻¹ * (x * (g * t * g⁻¹)) * g := by rw [h1]
          _ = g⁻¹ * x * g * t := by group
      · show g * (g⁻¹ * x * g) * g⁻¹ = x
        group
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem card_le_two_mul_of_index {U V : Subgroup G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V)
    {u : G} (h : Nat.card V = 2 * Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G))) :
    Nat.card U ≤ 2 * Nat.card ↥(U ⊓ Subgroup.centralizer ({u} : Set G)) := by
  set CVu : Subgroup G := V ⊓ Subgroup.centralizer ({u} : Set G) with hCVu
  have hcomm : ∀ x ∈ U, ∀ y ∈ CVu, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm' hV (hUV hx) hy.1
  have e := card_sup_mul_card_inf' hcomm
  have hUC : U ⊓ CVu = U ⊓ Subgroup.centralizer ({u} : Set G) := by
    ext x
    simp only [Subgroup.mem_inf, hCVu]
    exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, hUV a, c⟩⟩
  rw [hUC] at e
  have hle : Nat.card ↥(U ⊔ CVu) ≤ Nat.card V :=
    Subgroup.card_le_of_le (sup_le hUV inf_le_left)
  have hpos : 0 < Nat.card CVu := Nat.card_pos
  have h1 : Nat.card U * Nat.card CVu ≤ Nat.card V * Nat.card ↥(U ⊓ Subgroup.centralizer ({u} : Set G)) := by
    rw [← e]
    exact Nat.mul_le_mul_right _ hle
  rw [h] at h1
  have h2 : Nat.card U * Nat.card CVu ≤ (2 * Nat.card ↥(U ⊓ Subgroup.centralizer ({u} : Set G))) * Nat.card CVu := by
    calc _ ≤ 2 * Nat.card CVu * Nat.card ↥(U ⊓ Subgroup.centralizer ({u} : Set G)) := h1
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h2 hpos


end CFSG.CGT.PushingUpLit.CGT6
