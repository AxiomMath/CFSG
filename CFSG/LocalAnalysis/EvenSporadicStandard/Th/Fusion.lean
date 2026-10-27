module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Basic

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}

theorem ThCyc.mul_comm_of_mem (H : ThCyc G L R t) : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := by
  intro r hr r' hr'
  have := H.cyclic.isMulCommutative.is_comm.comm (⟨r, hr⟩ : R) ⟨r', hr'⟩
  exact congrArg Subtype.val this

theorem ThCyc.commutator_centralizer_le (H : ThCyc G L R t) :
    ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ ≤ L := by
  rw [H.centralizer_eq]
  exact commutator_sup_le_left H.le_centralizer H.mul_comm_of_mem

theorem ThCyc.not_conj_mem (H : ThCyc G L R t) (g : G) : g⁻¹ * t * g ∉ L := by
  intro hu
  have ht1 : t ≠ 1 := by
    intro h1
    have := H.order_two
    rw [h1, orderOf_one] at this
    omega
  set u := g⁻¹ * t * g with hu_def
  have hu2 : orderOf u = 2 := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective t
    simpa [hu_def] using this.trans H.order_two
  have hu2' : orderOf (⟨u, hu⟩ : L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hperf := H.data.perfectCentralizer _ hu2'
  set Mu : Subgroup G := (centralizer ({⟨u, hu⟩} : Set L)).map L.subtype with hMu
  have hMuperf : ⁅Mu, Mu⁆ = Mu := by
    rw [hMu, ← Subgroup.map_commutator, hperf]
  have hMuu : u ∈ Mu := ⟨⟨u, hu⟩, mem_centralizer_singleton_iff.2 rfl, rfl⟩
  have hMuc : ∀ x ∈ Mu, x * u = u * x := by
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy)
  set M' : Subgroup G := Mu.map (MulAut.conj g).toMonoidHom with hM'
  have hM'perf : ⁅M', M'⁆ = M' := by
    rw [hM', ← Subgroup.map_commutator, hMuperf]
  have htM' : t ∈ M' := ⟨u, hMuu, by simp [hu_def, MulAut.conj_apply]; group⟩
  have hM'le : M' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := hMuc x hx
    show g * x * g⁻¹ * t = t * (g * x * g⁻¹)
    calc g * x * g⁻¹ * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * (x * u) * g⁻¹ := by rw [hu_def]
      _ = g * (u * x) * g⁻¹ := by rw [this]
      _ = t * (g * x * g⁻¹) := by rw [hu_def]; group
  have hcomm := Subgroup.commutator_mono hM'le hM'le
  have htL : t ∈ L := by
    have h1 : t ∈ ⁅M', M'⁆ := by rw [hM'perf]; exact htM'
    exact H.commutator_centralizer_le (hcomm h1)
  have : t ∈ L ⊓ R := ⟨htL, H.mem⟩
  rw [disjoint_iff.1 H.disjoint, mem_bot] at this
  exact ht1 this

structure IsThSylow (L SL : Subgroup G) : Prop where
  le : SL ≤ L
  pgroup : IsPGroup 2 SL
  maximal : ∀ Y : Subgroup G, Y ≤ L → IsPGroup 2 Y → SL ≤ Y → Y ≤ SL
  center : ∀ x ∈ SL, (∀ y ∈ SL, x * y = y * x) → x ^ 2 = 1

theorem ThCyc.exists_sylow (H : ThCyc G L R t) : ∃ SL : Subgroup G, IsThSylow L SL := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS', hidx, hZ⟩ := H.data.sylowCenter
  refine ⟨S'.map L.subtype, Subgroup.map_subtype_le _, hS'.map _, ?_, ?_⟩
  · intro Y hYL hY hle
    have hker : IsPGroup 2 L.subtype.ker := by
      rw [Subgroup.ker_subtype]
      exact IsPGroup.of_card (n := 0) (by simp)
    have hY' : IsPGroup 2 (Y.comap L.subtype) := IsPGroup.comap_of_ker_isPGroup hY _ hker
    have hle' : S' ≤ Y.comap L.subtype := fun x hx => hle ⟨x, hx, rfl⟩
    have heq := (hS'.toSylow hidx).is_maximal' hY' hle'
    intro y hy
    have hy' : (⟨y, hYL hy⟩ : L) ∈ Y.comap L.subtype := hy
    rw [heq] at hy'
    exact ⟨_, hy', rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ hcomm
    have h2 := hZ x hx (fun y hy => Subtype.ext (hcomm y ⟨y, hy, rfl⟩))
    simpa using congrArg L.subtype h2

end CFSG.EvenSporadicStandard.ThStd
