module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_centralizer_singleton (t g : G) :
    (centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * t * g⁻¹} : Set G) := by
  ext x
  rw [Subgroup.mem_map, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := mem_centralizer_singleton_iff.mp hy
    show g * y * g⁻¹ * (g * t * g⁻¹) = g * t * g⁻¹ * (g * y * g⁻¹)
    calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
      _ = g * (t * y) * g⁻¹ := by rw [hy']
      _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx]
      _ = t * (g⁻¹ * x * g) := by group
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem exists_mem_normalizer_conj {t t' g : G} (hg : g * t * g⁻¹ = t') {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hQM : Q ≤ centralizer ({t} : Set G))
    (hodd : ¬ 2 ∣ Q.relIndex (centralizer ({t} : Set G))) (hQt' : Q ≤ centralizer ({t'} : Set G)) :
    ∃ n ∈ normalizer (Q : Set G), n * t * n⁻¹ = t' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : G →* G := (MulAut.conj g).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj g).injective
  set M' : Subgroup G := centralizer ({t'} : Set G) with hM'
  have hMeq : (centralizer ({t} : Set G)).map f = M' := by
    rw [hM', ← hg]; exact map_conj_centralizer_singleton t g
  set Q'' : Subgroup G := Q.map f with hQ''
  have hQ''M : Q'' ≤ M' := by
    rw [← hMeq]; exact Subgroup.map_mono hQM
  have hQ''2 : IsPGroup 2 Q'' := hQ.of_equiv (Subgroup.equivMapOfInjective Q f hfinj)
  have hcard : Nat.card Q'' = Nat.card Q := Subgroup.card_map_of_injective hfinj
  have hrel'' : Q''.relIndex M' = Q.relIndex (centralizer ({t} : Set G)) := by
    rw [← hMeq]; exact Subgroup.relIndex_map_map_of_injective _ _ hfinj
  have hrel : Q.relIndex M' = Q''.relIndex M' := by
    have h1 := Subgroup.relIndex_mul_card (H := Q) (K := M')
    have h2 := Subgroup.relIndex_mul_card (H := Q'') (K := M')
    rw [inf_eq_left.2 hQt'] at h1
    rw [inf_eq_left.2 hQ''M, hcard] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  have hS1p : IsPGroup 2 (Q.subgroupOf M') :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQt').symm
  have hS2p : IsPGroup 2 (Q''.subgroupOf M') :=
    hQ''2.of_equiv (Subgroup.subgroupOfEquivOfLe hQ''M).symm
  have hS1i : ¬ 2 ∣ (Q.subgroupOf M').index := by
    show ¬ 2 ∣ Q.relIndex M'
    rw [hrel, hrel'']; exact hodd
  have hS2i : ¬ 2 ∣ (Q''.subgroupOf M').index := by
    show ¬ 2 ∣ Q''.relIndex M'
    rw [hrel'']; exact hodd
  let S1 : Sylow 2 M' := hS1p.toSylow hS1i
  let S2 : Sylow 2 M' := hS2p.toSylow hS2i
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M' S2 S1
  have hmem' : ∀ w ∈ Q'', (c : G) * w * (c : G)⁻¹ ∈ Q := by
    intro w hw
    have hw2 : (⟨w, hQ''M hw⟩ : M') ∈ S2 := (IsPGroup.mem_toSylow hS2p hS2i).mpr hw
    have h1 : (MulAut.conj c) ⟨w, hQ''M hw⟩ ∈ ((c • S2 : Sylow 2 M') : Subgroup M') := by
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hw2
    rw [hc] at h1
    have h2 := (IsPGroup.mem_toSylow hS1p hS1i).mp h1
    exact h2
  have hcc : (c : G) * t' * (c : G)⁻¹ = t' := by
    have := mem_centralizer_singleton_iff.mp c.2
    calc (c : G) * t' * (c : G)⁻¹ = t' * (c : G) * (c : G)⁻¹ := by rw [this]
      _ = t' := by group
  refine ⟨(c : G) * g, ?_, ?_⟩
  · have hle : Q.map (MulAut.conj ((c : G) * g)).toMonoidHom ≤ Q := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : g * y * g⁻¹ ∈ Q'' := ⟨y, hy, by simp [hf, MulAut.conj_apply]⟩
      have := hmem' _ h1
      simpa [MulAut.conj_apply, mul_assoc] using this
    have heq : Q.map (MulAut.conj ((c : G) * g)).toMonoidHom = Q :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective (MulAut.conj ((c : G) * g)).injective])
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hle ⟨y, hy, rfl⟩
    · intro hy
      rw [← heq] at hy
      obtain ⟨q, hq, hqy⟩ := hy
      have : q = y := (MulAut.conj ((c : G) * g)).injective hqy
      rw [← this]
      exact hq
  · calc (c : G) * g * t * ((c : G) * g)⁻¹ = (c : G) * (g * t * g⁻¹) * (c : G)⁻¹ := by group
      _ = t' := by rw [hg, hcc]

end CFSG.EvenSporadicStandard.HSStd
