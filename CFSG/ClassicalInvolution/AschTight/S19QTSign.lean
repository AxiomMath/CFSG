module

public import CFSG.ClassicalInvolution.AschTight.S1916CSR
public import CFSG.ClassicalInvolution.AschTight.S1916Coh2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def signSub (O : Subgroup G) (ζ : G) : Subgroup G where
  carrier := {b | b ∈ Subgroup.normalizer (O : Set G) ∧ ζ⁻¹ * (b * ζ * b⁻¹) ∈ O}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro b₁ b₂ ⟨hb₁N, hb₁⟩ ⟨hb₂N, hb₂⟩
    refine ⟨Subgroup.mul_mem _ hb₁N hb₂N, ?_⟩
    have h2 : b₁ * (ζ⁻¹ * (b₂ * ζ * b₂⁻¹)) * b₁⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp hb₁N _).mp hb₂
    have e : ζ⁻¹ * (b₁ * b₂ * ζ * (b₁ * b₂)⁻¹) =
        (ζ⁻¹ * (b₁ * ζ * b₁⁻¹)) * (b₁ * (ζ⁻¹ * (b₂ * ζ * b₂⁻¹)) * b₁⁻¹) := by group
    rw [e]
    exact O.mul_mem hb₁ h2
  inv_mem' := by
    rintro b ⟨hbN, hb⟩
    refine ⟨Subgroup.inv_mem _ hbN, ?_⟩
    have h2 : b⁻¹ * (ζ⁻¹ * (b * ζ * b⁻¹)) * b⁻¹⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) _).mp hb
    have e : ζ⁻¹ * (b⁻¹ * ζ * b⁻¹⁻¹) = (b⁻¹ * (ζ⁻¹ * (b * ζ * b⁻¹)) * b⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact O.inv_mem h2

theorem not_mem_signSub_of_inv {O : Subgroup G} {ζ g : G} (hζO : ζ * ζ ∉ O)
    (hg : g * ζ * g⁻¹ = ζ⁻¹) : g ∉ signSub O ζ := by
  rintro ⟨-, h⟩
  rw [hg] at h
  apply hζO
  have e : (ζ⁻¹ * ζ⁻¹)⁻¹ = ζ * ζ := by rw [mul_inv_rev, inv_inv]
  rw [← e]
  exact O.inv_mem h

theorem mem_signSub_of_comm {O : Subgroup G} {ζ g : G}
    (hgN : g ∈ Subgroup.normalizer (O : Set G)) (hg : g * ζ = ζ * g) : g ∈ signSub O ζ := by
  refine ⟨hgN, ?_⟩
  have e : ζ⁻¹ * (g * ζ * g⁻¹) = 1 := by rw [hg]; group
  rw [e]
  exact O.one_mem

section Sign

variable {O C : Subgroup G} {ζ : G}
  (hP : ∀ g ∈ C, g ∈ Subgroup.normalizer (O : Set G) ∧
    (ζ⁻¹ * (g * ζ * g⁻¹) ∈ O ∨ ζ * (g * ζ * g⁻¹) ∈ O))
include hP

theorem mem_of_not_mem_signSub {g : G} (hg : g ∈ C) (hgH : g ∉ signSub O ζ) :
    ζ * (g * ζ * g⁻¹) ∈ O := by
  obtain ⟨hgN, h | h⟩ := hP g hg
  · exact absurd ⟨hgN, h⟩ hgH
  · exact h

theorem inv_mul_mem_signSub {a b : G} (ha : a ∈ C) (hb : b ∈ C) (haH : a ∉ signSub O ζ)
    (hbH : b ∉ signSub O ζ) : a⁻¹ * b ∈ signSub O ζ := by
  have haN := (hP a ha).1
  have h1 := mem_of_not_mem_signSub hP ha haH
  have h2 := mem_of_not_mem_signSub hP hb hbH
  refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ haN) (hP b hb).1, ?_⟩
  have h3 : a⁻¹ * ((ζ * (a * ζ * a⁻¹))⁻¹ * (ζ * (b * ζ * b⁻¹))) * a⁻¹⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp (O.mul_mem (O.inv_mem h1) h2)
  have e : ζ⁻¹ * (a⁻¹ * b * ζ * (a⁻¹ * b)⁻¹) =
      a⁻¹ * ((ζ * (a * ζ * a⁻¹))⁻¹ * (ζ * (b * ζ * b⁻¹))) * a⁻¹⁻¹ := by group
  rw [e]
  exact h3

theorem conj_mem_signSub {g x : G} (hg : g ∈ C) (hx : x ∈ C) (hxH : x ∈ signSub O ζ) :
    g * x * g⁻¹ ∈ signSub O ζ := by
  by_cases hgH : g ∈ signSub O ζ
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgH hxH) (Subgroup.inv_mem _ hgH)
  · have hgx : (g * x)⁻¹ ∉ signSub O ζ := fun h => hgH (by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h) (Subgroup.inv_mem _ hxH)
      rwa [inv_inv, mul_inv_cancel_right] at this)
    have hg' : g⁻¹ ∉ signSub O ζ := fun h => hgH (by simpa using Subgroup.inv_mem _ h)
    have h := inv_mul_mem_signSub hP (C.inv_mem (C.mul_mem hg hx)) (C.inv_mem hg) hgx hg'
    have e : (g * x)⁻¹⁻¹ * g⁻¹ = g * x * g⁻¹ := by group
    rwa [e] at h

theorem conj_not_mem_signSub {g x : G} (hg : g ∈ C) (hx : x ∈ C) (hxH : x ∉ signSub O ζ) :
    g * x * g⁻¹ ∉ signSub O ζ := by
  intro h
  apply hxH
  have := conj_mem_signSub hP (C.inv_mem hg) (C.mul_mem (C.mul_mem hg hx) (C.inv_mem hg)) h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

end Sign

variable [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem exists_mul_self_eq_z (hd : Sec19DataT p f K z S W L t V) :
    ∃ ζ ∈ W ⊓ sec19Y K z, ζ * ζ = z := by
  have ef := S1911.etaYForm p f G K z S W L t V hd
  refine exists_mul_self_eq_of_isCyclic (S1916.isUniqueInvolution_W_inf hd) le_rfl ef.cyclic
    (S.isPGroup'.to_le (inf_le_left.trans hd.hWS)) ?_
  rw [ef.card]
  exact ef.four

theorem sign_mem_or (hd : Sec19DataT p f K z S W L t V)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) {ζ : G} (hζ : ζ ∈ W ⊓ sec19Y K z)
    (hζ2 : ζ * ζ = z) {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    g ∈ Subgroup.normalizer (oddCoreOf (sec19Y K z) : Set G) ∧
      (ζ⁻¹ * (g * ζ * g⁻¹) ∈ oddCoreOf (sec19Y K z) ∨
        ζ * (g * ζ * g⁻¹) ∈ oddCoreOf (sec19Y K z)) := by
  have hd0 := hd.toSec19Data
  have hNY := S1916.sd_centralizer_le_normalizer_Y hd0
  have hNO : ∀ x ∈ Subgroup.centralizer ({z} : Set G),
      x ∈ Subgroup.normalizer (oddCoreOf (sec19Y K z) : Set G) := fun x hx =>
    AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer (hNY hx)
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := hd.hWS.trans hd0.hSz
  refine ⟨hNO g hg, ?_⟩
  have hzZ := S1916.isUniqueInvolution_W_inf hd
  have hcomm := S1911.comm_of_mem hd0
  have hZ2 : IsPGroup 2 ↥(W ⊓ sec19Y K z) := S.isPGroup'.to_le (inf_le_left.trans hd.hWS)
  have hbot := S1916.inf_oddCoreOf_eq_bot hZ2 (sec19Y K z)
  have hOY : oddCoreOf (sec19Y K z) ≤ sec19Y K z := Subgroup.map_subtype_le _
  have hyY : g * ζ * g⁻¹ ∈ sec19Y K z := (Subgroup.mem_normalizer_iff.mp (hNY hg) ζ).mp hζ.2
  have hyOW : g * ζ * g⁻¹ ∈ oddCoreOf (sec19Y K z) ⊔ W := by
    rw [← h1]
    exact Subgroup.mem_sup_right hyY
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left (oddCoreOf (sec19Y K z)) W
    (fun x hx => hNO x (hWC hx))
  have hyOW' : g * ζ * g⁻¹ ∈ ((oddCoreOf (sec19Y K z) : Set G) * (W : Set G)) := by
    rw [← hset]
    exact hyOW
  obtain ⟨o, ho, w, hw, how⟩ := Set.mem_mul.mp hyOW'
  have hwY : w ∈ sec19Y K z := by
    have e : w = o⁻¹ * (g * ζ * g⁻¹) := by rw [← how]; group
    rw [e]
    exact (sec19Y K z).mul_mem ((sec19Y K z).inv_mem (hOY ho)) hyY
  have hwZ : w ∈ W ⊓ sec19Y K z := ⟨hw, hwY⟩
  have hsq : (o * w) * (o * w) = z := by
    have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [how]
    calc g * ζ * g⁻¹ * (g * ζ * g⁻¹) = g * (ζ * ζ) * g⁻¹ := by group
      _ = z := by rw [hζ2, hgz, mul_inv_cancel_right]
  have hwo : w * o * w⁻¹ ∈ oddCoreOf (sec19Y K z) :=
    (Subgroup.mem_normalizer_iff.mp (hNO w (hWC hw)) o).mp ho
  have hww : w * w = z := by
    have e2 : w * w * z⁻¹ = (o * (w * o * w⁻¹))⁻¹ := by rw [← hsq]; group
    have hO : w * w * z⁻¹ ∈ oddCoreOf (sec19Y K z) := by
      rw [e2]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ ho hwo)
    have hmem : w * w * z⁻¹ ∈ W ⊓ sec19Y K z ⊓ oddCoreOf (sec19Y K z) :=
      ⟨(W ⊓ sec19Y K z).mul_mem ((W ⊓ sec19Y K z).mul_mem hwZ hwZ)
        ((W ⊓ sec19Y K z).inv_mem hzZ.mem), hO⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    calc w * w = w * w * z⁻¹ * z := by group
      _ = z := by rw [hmem, one_mul]
  have hζN : ζ ∈ Subgroup.normalizer (oddCoreOf (sec19Y K z) : Set G) := hNO ζ (hWC hζ.1)
  rcases S1916.eq_or_eq_inv_of_mul_self_eq hzZ (fun x hx y hy => hcomm x hx.1 y hy.1) hwZ hζ hww
    hζ2 with h | h
  · left
    rw [← how, h]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hζN) o).mp ho
    have e : ζ⁻¹ * (o * ζ) = ζ⁻¹ * o * ζ⁻¹⁻¹ := by group
    rw [e]
    exact this
  · right
    rw [← how, h]
    have := (Subgroup.mem_normalizer_iff.mp hζN o).mp ho
    have e : ζ * (o * ζ⁻¹) = ζ * o * ζ⁻¹ := by group
    rw [e]
    exact this

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q
