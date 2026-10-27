module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR3A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]

structure Z4JLift (N : Subgroup X) [N.Normal] (P : Subgroup X) (Vh : Subgroup (X ⧸ N)) : Prop where
  odd : Odd (Nat.card N)
  isPGroup : IsPGroup 2 P
  map_eq : P.map (z4iπ N) = Vh

namespace Z4JLift

variable {P : Subgroup X} {Vh : Subgroup (X ⧸ N)} (h : Z4JLift N P Vh)
include h

theorem inj {a b : X} (ha : a ∈ P) (hb : b ∈ P) (hab : z4iπ N a = z4iπ N b) : a = b :=
  z4iπ_injOn N h.odd h.isPGroup ha hb hab

theorem card_eq : Nat.card P = Nat.card Vh := by
  rw [← h.map_eq]
  exact (z4i_card_map N h.odd h.isPGroup).symm

theorem exists_lift {u : X ⧸ N} (hu : u ∈ Vh) : ∃ x ∈ P, z4iπ N x = u := by
  rw [← h.map_eq] at hu
  obtain ⟨x, hx, hxu⟩ := hu
  exact ⟨x, hx, hxu⟩

theorem mul_self_eq_one {a : X} (ha : a ∈ P) (h2 : z4iπ N a * z4iπ N a = 1) : a * a = 1 := by
  refine h.inj (P.mul_mem ha ha) P.one_mem ?_
  rw [map_mul, h2, map_one]

theorem comm {a b : X} (ha : a ∈ P) (hb : b ∈ P)
    (hab : z4iπ N a * z4iπ N b = z4iπ N b * z4iπ N a) : a * b = b * a := by
  refine h.inj (P.mul_mem ha hb) (P.mul_mem hb ha) ?_
  rw [map_mul, map_mul, hab]

theorem map_cent {β : X} (hβ : β ∈ P) :
    (P ⊓ centralizer ({β} : Set X)).map (z4iπ N) = Vh ⊓ centralizer ({z4iπ N β} : Set (X ⧸ N)) := by
  apply le_antisymm
  · rintro u hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨hxP, hxc⟩ := hx
    have hxc' : β * x = x * β := by simpa [Subgroup.mem_centralizer_iff] using hxc
    refine ⟨?_, ?_⟩
    · rw [← h.map_eq]
      exact ⟨x, hxP, rfl⟩
    · have hxc'' : z4iπ N β * z4iπ N x = z4iπ N x * z4iπ N β := by
        rw [← map_mul, ← map_mul, hxc']
      simpa [Subgroup.mem_centralizer_iff] using hxc''
  · rintro u ⟨huVh, huc⟩
    obtain ⟨x, hxP, hxu⟩ := h.exists_lift huVh
    have huc' : z4iπ N β * u = u * z4iπ N β := by
      simpa [Subgroup.mem_centralizer_iff] using huc
    have huc'' : z4iπ N β * z4iπ N x = z4iπ N x * z4iπ N β := by
      rw [← hxu] at huc'
      exact huc'
    refine ⟨x, ⟨hxP, ?_⟩, hxu⟩
    have hxc' : β * x = x * β := (h.comm hxP hβ huc''.symm).symm
    simpa [Subgroup.mem_centralizer_iff] using hxc'

theorem card_cent {β : X} (hβ : β ∈ P) :
    Nat.card ↥(P ⊓ centralizer ({β} : Set X)) =
      Nat.card ↥(Vh ⊓ centralizer ({z4iπ N β} : Set (X ⧸ N))) := by
  have h2 : IsPGroup 2 ((P ⊓ centralizer ({β} : Set X)) : Subgroup X) :=
    h.isPGroup.to_le inf_le_left
  rw [← h.map_cent hβ]
  exact (z4i_card_map N h.odd h2).symm

theorem map_sub {F : Subgroup (X ⧸ N)} (hF : F ≤ Vh) : (P ⊓ F.comap (z4iπ N)).map (z4iπ N) = F := by
  apply le_antisymm
  · rintro u ⟨x, hx, rfl⟩
    exact Subgroup.mem_comap.1 hx.2
  · intro u hu
    obtain ⟨x, hxP, hxu⟩ := h.exists_lift (hF hu)
    rw [← hxu] at hu ⊢
    exact ⟨x, ⟨hxP, Subgroup.mem_comap.2 hu⟩, rfl⟩

theorem card_sub {F : Subgroup (X ⧸ N)} (hF : F ≤ Vh) :
    Nat.card ↥(P ⊓ F.comap (z4iπ N)) = Nat.card F := by
  have h2 : IsPGroup 2 ((P ⊓ F.comap (z4iπ N)) : Subgroup X) := h.isPGroup.to_le inf_le_left
  conv_rhs => rw [← h.map_sub hF]
  exact (z4i_card_map N h.odd h2).symm

theorem centralizes_iff {U : Subgroup X} (hUP : U ≤ P) {x : X} (hx : x ∈ P) :
    (∀ v ∈ U, x * v = v * x) ↔ ∀ w ∈ U.map (z4iπ N), z4iπ N x * w = w * z4iπ N x := by
  constructor
  · intro H w hw
    obtain ⟨v, hvU, rfl⟩ := Subgroup.mem_map.1 hw
    rw [← map_mul, ← map_mul, H v hvU]
  · intro H v hvU
    exact h.comm hx (hUP hvU) (H (z4iπ N v) (Subgroup.mem_map_of_mem (z4iπ N) hvU))

end Z4JLift

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
