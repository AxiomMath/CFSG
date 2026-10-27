module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47Quot
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47K

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.split47 (h : Sec4FSetup t L S z A B φ)
    (hK : ∃ K : Subgroup G, K ≤ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) ∧
      K.relIndex (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) = 2 ∧ t ∉ K) :
    ∃ M₀ : Subgroup G, M₀ ≤ normalizer (A : Set G) ∧
      M₀.relIndex (normalizer (A : Set G)) = 2 ∧ t ∉ M₀ := by
  obtain ⟨K, -, hidx, htK⟩ := hK
  have htM : t ∈ normalizer (A : Set G) := Subgroup.le_normalizer h.t_mem_A
  have htC : t ∈ centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => h.A_comm ha h.t_mem_A
  let H : Subgroup ↥(normalizer (A : Set G)) :=
    (B ⊔ oddCoreIn (centralizer (A : Set G))).subgroupOf (normalizer (A : Set G))
  haveI hHn : H.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa [mul_assoc] using h.conj_mem_BO g.2 hx⟩
  let t' : ↥(normalizer (A : Set G)) := ⟨t, htM⟩
  have hsq : ∀ y : ↥(normalizer (A : Set G)), (y : G) ∈ K → h.actHom y * h.actHom y = 1 →
      y * y ∈ H := by
    intro y hyK hy1
    rw [Subgroup.mem_subgroupOf]
    have hyy : h.actHom (y * y) = 1 := by rw [map_mul, hy1]
    have hC : ((y * y : ↥(normalizer (A : Set G))) : G) ∈ centralizer (A : Set G) :=
      (h.actHom_eq_one_iff (y * y)).mp hyy
    exact h.inf_cent_le_of_index_two hidx htK ⟨K.mul_mem hyK hyK, hC⟩
  obtain ⟨M₀', hidx', ht'⟩ := sec4S47_exists_index_two h.actHom H
    (fun x hx => by
      rw [MonoidHom.mem_ker, h.actHom_eq_one_iff]
      exact h.BO_le_cent ((Subgroup.mem_subgroupOf).mp hx))
    (t := t') (fun ht => h.t_not_mem_BO ((Subgroup.mem_subgroupOf).mp ht))
    ((h.actHom_eq_one_iff t').mpr htC) (Subtype.ext h.t_sq)
    (fun x hx => by
      rcases h.cent_cases ((h.actHom_eq_one_iff x).mp hx) with hc | hc
      · exact Or.inl ((Subgroup.mem_subgroupOf).mpr hc)
      · exact Or.inr ((Subgroup.mem_subgroupOf).mpr hc))
    (fun x => (Subgroup.mem_subgroupOf).mpr
      (Subgroup.mem_sup_left (by simpa using h.conj_t_mem_B x.2)))
    h.alt_le_range
    (fun x hx hx2 => by
      have hxX : (x : G) ∈ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) :=
        ⟨(h.actHom_none_iff x).mp hx, x.2⟩
      rcases h.mem_or_mul_mem_of_index_two hidx htK hxX with hxK | hxK
      · exact ⟨x, rfl, hsq x hxK hx2⟩
      · have ht1 : h.actHom t' = 1 := (h.actHom_eq_one_iff t').mpr htC
        refine ⟨x * t', by rw [map_mul, ht1, mul_one], hsq (x * t') hxK ?_⟩
        rw [map_mul, ht1, mul_one, hx2])
  refine ⟨M₀'.map (normalizer (A : Set G)).subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (normalizer (A : Set G)).subtype_injective]
    exact hidx'
  · rintro ⟨y, hy, hyt⟩
    apply ht'
    have hyt' : y = t' := Subtype.ext hyt
    rwa [← hyt']

theorem asc82Split47_of (I : Sec4FInputs) (hP5 : Asc82Split47Cent) : Asc82Split47 := by
  intro G _ _ t L S z hctx hnot A hA
  obtain ⟨A₀, B, φ, hD⟩ := I.hAD G t L S z hctx
  obtain rfl : A = A₀ := hD.unique A hA
  exact (sec4FSetup_of_data I hctx hnot hD).split47 (hP5 G t L S z hctx hnot A hA)

end CFSG.OddStandard.SmallF3.Omega
