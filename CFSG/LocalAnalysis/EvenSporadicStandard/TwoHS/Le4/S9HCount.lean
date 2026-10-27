module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Coord

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

namespace ECoord

variable {G : Type*} [Group G]

theorem natCard_E (C : ECoord G) : Nat.card C.E = 256 := by
  rw [Nat.card_congr C.φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
  simp [Fintype.card_pi, ZMod.card]

theorem card_inf_centralizer_mul_ncard_image [Finite G] (C : ECoord G) (T : Subgroup G)
    (hT : ∀ x ∈ T, x ∈ normalizer (C.E : Set G)) :
    Nat.card ↥(T ⊓ centralizer (C.E : Set G)) * (C.mat '' (T : Set G)).ncard = Nat.card T := by
  let f : T →* M4 :=
    { toFun := fun x => C.mat (x : G)
      map_one' := C.mat_one
      map_mul' := fun x y => C.mat_mul (hT x x.2) (hT y y.2) }
  let φ : T →* M4ˣ := f.toHomUnits
  have hφ : ∀ x : T, ((φ x : M4ˣ) : M4) = C.mat (x : G) := fun x => rfl
  have hker : φ.ker = (T ⊓ centralizer (C.E : Set G)).subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, Units.ext_iff, hφ, Units.val_one, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, mem_centralizer_iff]
    exact (C.mat_eq_one_iff (hT x x.2)).trans
      ⟨fun h => ⟨x.2, fun e he => (h e he).symm⟩, fun h e he => (h.2 e he).symm⟩
  have himg : Units.val '' (φ.range : Set M4ˣ) = C.mat '' (T : Set G) := by
    ext A
    constructor
    · rintro ⟨u, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, x.2, (hφ x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hrange : Nat.card φ.range = (C.mat '' (T : Set G)).ncard := by
    rw [← himg, Set.ncard_image_of_injective _ Units.val_injective, ← Nat.card_coe_set_eq]
    rfl
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  exact h

theorem count_normalizer [Finite G] (C : ECoord G) {t : G}
    (htE : t ∈ C.E) (Q : List M4) (hQ : Q.Nodup)
    (hreal : ∀ A ∈ Q, ∃ x : G, x * t = t * x ∧ x ∈ normalizer (C.E : Set G) ∧ C.mat x = A)
    (hbound : Nat.card ↥(centralizer ({t} : Set G) ⊓ normalizer (C.E : Set G)) ≤ 256 * Q.length) :
    (∀ x : G, x * t = t * x → x ∈ normalizer (C.E : Set G) → C.mat x ∈ Q) ∧
    (∀ x : G, x * t = t * x → (∀ e ∈ C.E, x * e = e * x) → x ∈ C.E) := by
  set 𝒩 : Subgroup G := centralizer ({t} : Set G) ⊓ normalizer (C.E : Set G) with h𝒩
  have hmemN : ∀ x : G, x ∈ 𝒩 ↔ x * t = t * x ∧ x ∈ normalizer (C.E : Set G) := fun x => by
    rw [h𝒩, Subgroup.mem_inf, mem_centralizer_singleton_iff]
  have hEN : C.E ≤ 𝒩 := fun e he => (hmemN e).2 ⟨C.comm he htE, Subgroup.le_normalizer he⟩
  set K : Subgroup G := 𝒩 ⊓ centralizer (C.E : Set G)
  have hEK : C.E ≤ K := fun e he => ⟨hEN he, mem_centralizer_iff.2 fun h hh => C.comm hh he⟩
  have hkcard : 256 ≤ Nat.card K := by
    rw [← C.natCard_E]
    exact Subgroup.card_le_of_le hEK
  have hfac := C.card_inf_centralizer_mul_ncard_image 𝒩 fun x hx => ((hmemN x).1 hx).2
  set R : Set M4 := C.mat '' (𝒩 : Set G)
  set S : Set M4 := ((Q.toFinset : Finset M4) : Set M4) with hS
  have hSR : S ⊆ R := by
    intro A hA
    obtain ⟨x, hxt, hxN, hxA⟩ := hreal A (List.mem_toFinset.1 hA)
    exact ⟨x, (hmemN x).2 ⟨hxt, hxN⟩, hxA⟩
  have hSc : S.ncard = Q.length := by
    rw [hS, Set.ncard_coe_finset, List.toFinset_card_of_nodup hQ]
  have hRfin : R.Finite := (Set.toFinite _).image _
  have hqr : Q.length ≤ R.ncard := hSc ▸ Set.ncard_le_ncard hSR hRfin
  have hRpos : 0 < R.ncard := by
    rw [Set.ncard_pos hRfin]
    exact ⟨C.mat 1, 1, 𝒩.one_mem, rfl⟩
  have h256 : 256 * R.ncard ≤ 256 * Q.length :=
    calc 256 * R.ncard ≤ Nat.card K * R.ncard := Nat.mul_le_mul_right _ hkcard
      _ = Nat.card 𝒩 := hfac
      _ ≤ 256 * Q.length := hbound
  have hReq : R.ncard = Q.length :=
    le_antisymm (Nat.le_of_mul_le_mul_left h256 (by norm_num)) hqr
  have hKle : Nat.card K ≤ 256 := by
    have : Nat.card K * R.ncard ≤ 256 * R.ncard := by
      rw [hfac, hReq]
      exact hbound
    exact Nat.le_of_mul_le_mul_right this hRpos
  have hRS : S = R := Set.eq_of_subset_of_ncard_le hSR (by omega) hRfin
  have hEK' : C.E = K := Subgroup.eq_of_le_of_card_ge hEK (by rw [C.natCard_E]; exact hKle)
  refine ⟨fun x hxt hxN => ?_, fun x hxt hxE => ?_⟩
  · have hxR : C.mat x ∈ R := ⟨x, (hmemN x).2 ⟨hxt, hxN⟩, rfl⟩
    rw [← hRS] at hxR
    exact List.mem_toFinset.1 hxR
  · have hxc : x ∈ centralizer (C.E : Set G) := mem_centralizer_iff.2 fun e he => (hxE e he).symm
    have hxN : x ∈ normalizer (C.E : Set G) := centralizer_le_normalizer _ hxc
    have hxK : x ∈ K := ⟨(hmemN x).2 ⟨hxt, hxN⟩, hxc⟩
    rw [← hEK'] at hxK
    exact hxK

end ECoord

end CFSG.EvenSporadicStandard.TwoHS
