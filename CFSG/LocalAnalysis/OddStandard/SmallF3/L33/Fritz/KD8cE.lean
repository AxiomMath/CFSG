module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cIota
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46T

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c
open CFSG.ComponentClassification.HSFLit.KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

structure Conf (S : KDBase A C) (T₁ : Subgroup X) where
  h4 : S.Sec4 T₁
  D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y)
  D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)
  hq₁ : D₁.q0 = .extraspecial
  hq₂ : D₂.q0 = .extraspecial

namespace Conf

variable (K : Conf S T₁)

abbrev P : CPair S T₁ := pair₁ S K.h4 K.D₁ K.D₂ K.hq₁ K.hq₂

noncomputable abbrev ι : MC →* X := K.P.ι

theorem ι_injective : Function.Injective K.ι := K.P.ι_injective

theorem range_ι : K.ι.range = K.D₁.S₁ := K.P.range_ι

theorem ι_z : K.ι MC.z = S.z := K.P.ι_z
theorem ι_y : K.ι MC.y = S.y := K.P.ι_y
theorem ι_t : K.ι MC.t = t := K.P.ι_t
theorem ι_k : K.ι MC.k = S.k := K.P.ι_k
theorem ι_u : K.ι MC.u = t * (S.x * S.y) := (K.P.ι_u).trans (u₁_eq S K.h4 K.D₁ K.D₂ K.hq₁ K.hq₂)

theorem ι_tu : K.ι (MC.t * MC.u) = S.x * S.y := by
  rw [map_mul, K.ι_t, K.ι_u, ← mul_assoc, tt (A := A), one_mul]

@[expose] noncomputable def R1 : Subgroup X := R1h.map K.ι

@[expose] noncomputable def Zx : Subgroup X := Zh.map K.ι

@[expose] noncomputable def Ex (i : Fin 8) : Subgroup X := (Eh i).map K.ι

theorem mem_Ex {i : Fin 8} {g : X} : g ∈ K.Ex i ↔ ∃ x, inE i x = true ∧ K.ι x = g :=
  Subgroup.mem_map

theorem ι_mem_Ex {i : Fin 8} {x : MC} (hx : inE i x = true) : K.ι x ∈ K.Ex i :=
  K.mem_Ex.mpr ⟨x, hx, rfl⟩

theorem mem_R1 {g : X} : g ∈ K.R1 ↔ ∃ x, inR1 x = true ∧ K.ι x = g := Subgroup.mem_map

theorem ι_mem_R1 {x : MC} (hx : inR1 x = true) : K.ι x ∈ K.R1 := K.mem_R1.mpr ⟨x, hx, rfl⟩

theorem card_Ex (i : Fin 8) : Nat.card (K.Ex i) = 16 := by
  rw [Ex, card_map_of_injective K.ι_injective, card_Eh]

theorem card_R1 : Nat.card K.R1 = 128 := by
  rw [R1, card_map_of_injective K.ι_injective, card_R1h]

theorem card_Zx : Nat.card K.Zx = 4 := by
  rw [Zx, card_map_of_injective K.ι_injective, card_Zh]

theorem Ex_le_R1 (i : Fin 8) : K.Ex i ≤ K.R1 := map_mono (Eh_le_R1h i)

theorem Zx_le_Ex (i : Fin 8) : K.Zx ≤ K.Ex i := map_mono (Zh_le_Eh i)

theorem R1_le_S1 : K.R1 ≤ K.D₁.S₁ := by
  rw [← K.range_ι]; exact map_le_range _ _

theorem card_inf_Ex (i j : Fin 8) : Nat.card (K.Ex i ⊓ K.Ex j : Subgroup X) = interCard i j := by
  rw [Ex, Ex, ← Subgroup.map_inf_eq (Eh i) (Eh j) K.ι K.ι_injective,
    card_map_of_injective K.ι_injective, card_inf]

theorem eq_Ex_of {H : Subgroup X} (hH : H ≤ K.R1) (hab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hsq : ∀ a ∈ H, a * a = 1) (hcard : Nat.card H = 16) : ∃ i : Fin 8, H = K.Ex i := by
  have hHr : H ≤ K.ι.range := hH.trans (map_le_range _ _)
  set H' := H.comap K.ι with hH'
  have hmap : H'.map K.ι = H := map_comap_eq_self hHr
  obtain ⟨i, hi⟩ := eq_Eh_of (H := H')
    (fun x hx => by
      obtain ⟨y, hy, hxy⟩ := hH (mem_comap.mp hx)
      rw [← K.ι_injective hxy]; exact hy)
    (fun a ha b hb => K.ι_injective (by rw [map_mul, map_mul]; exact hab _ ha _ hb))
    (fun a ha => K.ι_injective (by rw [map_mul, map_one]; exact hsq _ ha))
    (by rw [← card_map_of_injective K.ι_injective, hmap, hcard])
  exact ⟨i, by rw [← hmap, hi]; rfl⟩

theorem E₁_eq : S.E S.y = K.Ex 0 := by
  refine eq_of_le_of_card_ge ?_ (by rw [K.card_Ex, KD46.card_E₁ S])
  refine (closure_le _).mpr (Set.insert_subset_iff.mpr ⟨?_, Set.insert_subset_iff.mpr ⟨?_,
    Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩⟩⟩)
  · rw [← K.ι_z]; exact K.ι_mem_Ex (by decide +kernel)
  · rw [← K.ι_y]; exact K.ι_mem_Ex (by decide +kernel)
  · have h := K.ι_mem_Ex (i := 0) (x := MC.t) (by decide +kernel)
    rwa [K.ι_t] at h
  · rw [← K.ι_k]; exact K.ι_mem_Ex (by decide +kernel)

theorem E₂_eq : S.E (S.x * S.y) = K.Ex 1 := by
  refine eq_of_le_of_card_ge ?_ (by rw [K.card_Ex, KD46.card_E₂ S])
  refine (closure_le _).mpr (Set.insert_subset_iff.mpr ⟨?_, Set.insert_subset_iff.mpr ⟨?_,
    Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩⟩⟩)
  · rw [← K.ι_z]; exact K.ι_mem_Ex (by decide +kernel)
  · rw [← K.ι_tu]; exact K.ι_mem_Ex (by decide +kernel)
  · have h := K.ι_mem_Ex (i := 1) (x := MC.t) (by decide +kernel)
    rwa [K.ι_t] at h
  · rw [← K.ι_k]; exact K.ι_mem_Ex (by decide +kernel)

theorem conj_Ex_of_le {n : X} {i j : Fin 8}
    (h : ∀ e ∈ K.Ex i, n * e * n⁻¹ ∈ K.Ex j) :
    (K.Ex i).map (MulAut.conj n).toMonoidHom = K.Ex j := by
  refine eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj n).injective,
    K.card_Ex, K.card_Ex])
  rintro _ ⟨e, he, rfl⟩
  exact h e he

theorem R1_conj_Ex {g : X} (hg : g ∈ K.R1) {i : Fin 8} {e : X} (he : e ∈ K.Ex i) :
    g * e * g⁻¹ ∈ K.Ex i := by
  obtain ⟨a, ha, rfl⟩ := K.mem_R1.mp hg
  obtain ⟨b, hb, rfl⟩ := K.mem_Ex.mp he
  rw [← map_inv, ← map_mul, ← map_mul]
  exact K.ι_mem_Ex (mem_Eh.mp (R1h_conj_Eh (mem_R1h.mpr ha) (mem_Eh.mpr hb)))

theorem w₂_conj_Ex {i : Fin 8} {e : X} (he : e ∈ K.Ex i) :
    K.ι MC.w₂ * e * (K.ι MC.w₂)⁻¹ ∈ K.Ex (sig21 i) := by
  obtain ⟨b, hb, rfl⟩ := K.mem_Ex.mp he
  rw [← map_inv, ← map_mul, ← map_mul]
  exact K.ι_mem_Ex (w₂_conj_Eh i b hb)

theorem mem_S1_cases {g : X} (hg : g ∈ K.D₁.S₁) : g ∈ K.R1 ∨ (K.ι MC.w₂)⁻¹ * g ∈ K.R1 := by
  rw [← K.range_ι] at hg
  obtain ⟨x, rfl⟩ := hg
  by_cases hx : inR1 x = true
  · exact Or.inl (K.ι_mem_R1 hx)
  · right
    rw [← map_inv, ← map_mul]
    refine K.ι_mem_R1 ?_
    have key : ∀ x : MC, inR1 x = false → inR1 (MC.w₂⁻¹ * x) = true := by decide +kernel
    exact key x (by simpa using hx)

end Conf

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
