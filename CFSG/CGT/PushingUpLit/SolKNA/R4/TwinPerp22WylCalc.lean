module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylFrame
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Free
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Alpha
public import CFSG.ClassicalInvolution.Asc77.WP3S28BIndep

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

namespace Perp22Wyl

section Group

variable {G : Type*} [Group G]

theorem swap_relations {z t' r s : G} (hzt : z * t' = t' * z) (hz2 : z * z = 1) (ht2 : t' * t' = 1)
    (h1 : r * z * r⁻¹ = z) (h2 : r * t' * r⁻¹ = z * t') (h3 : s * z * s⁻¹ = t' * z)
    (h4 : s * t' * s⁻¹ = t') :
    (r * s * r⁻¹) * z * (r * s * r⁻¹)⁻¹ = t' ∧ (r * s * r⁻¹) * t' * (r * s * r⁻¹)⁻¹ = z ∧
      (r * (r * s * r⁻¹)) * z * (r * (r * s * r⁻¹))⁻¹ = z * t' ∧
      (r * (r * s * r⁻¹)) * t' * (r * (r * s * r⁻¹))⁻¹ = z := by
  have e1 : r⁻¹ * z * r = z := by
    calc r⁻¹ * z * r = r⁻¹ * (r * z * r⁻¹) * r := by rw [h1]
      _ = z := by group
  have e2 : r⁻¹ * t' * r = z * t' := by
    have h5 : z * (r⁻¹ * t' * r) = t' := by
      calc z * (r⁻¹ * t' * r) = (r⁻¹ * z * r) * (r⁻¹ * t' * r) := by rw [e1]
        _ = r⁻¹ * (z * t') * r := by group
        _ = r⁻¹ * (r * t' * r⁻¹) * r := by rw [h2]
        _ = t' := by group
    calc r⁻¹ * t' * r = (z * z) * (r⁻¹ * t' * r) := by rw [hz2, one_mul]
      _ = z * (z * (r⁻¹ * t' * r)) := by rw [mul_assoc]
      _ = z * t' := by rw [h5]
  have hy1 : (r * s * r⁻¹) * z * (r * s * r⁻¹)⁻¹ = t' := by
    calc (r * s * r⁻¹) * z * (r * s * r⁻¹)⁻¹
        = r * (s * (r⁻¹ * z * r) * s⁻¹) * r⁻¹ := by group
      _ = r * (t' * z) * r⁻¹ := by rw [e1, h3]
      _ = (r * t' * r⁻¹) * (r * z * r⁻¹) := by group
      _ = (z * t') * z := by rw [h2, h1]
      _ = t' * (z * z) := by rw [hzt]; group
      _ = t' := by rw [hz2, mul_one]
  have hy2 : (r * s * r⁻¹) * t' * (r * s * r⁻¹)⁻¹ = z := by
    calc (r * s * r⁻¹) * t' * (r * s * r⁻¹)⁻¹
        = r * (s * (r⁻¹ * t' * r) * s⁻¹) * r⁻¹ := by group
      _ = r * ((s * z * s⁻¹) * (s * t' * s⁻¹)) * r⁻¹ := by rw [e2]; group
      _ = r * ((t' * z) * t') * r⁻¹ := by rw [h3, h4]
      _ = r * z * r⁻¹ := by
          congr 2
          calc t' * z * t' = z * (t' * t') := by rw [← hzt, mul_assoc]
            _ = z := by rw [ht2, mul_one]
      _ = z := h1
  refine ⟨hy1, hy2, ?_, ?_⟩
  · calc (r * (r * s * r⁻¹)) * z * (r * (r * s * r⁻¹))⁻¹
        = r * ((r * s * r⁻¹) * z * (r * s * r⁻¹)⁻¹) * r⁻¹ := by group
      _ = z * t' := by rw [hy1, h2]
  · calc (r * (r * s * r⁻¹)) * t' * (r * (r * s * r⁻¹))⁻¹
        = r * ((r * s * r⁻¹) * t' * (r * s * r⁻¹)⁻¹) * r⁻¹ := by group
      _ = z := by rw [hy2, h1]

end Group



section Group2

variable {Y : Type} [Group Y]

theorem mem_normalizer_closure_pair {a b g : Y}
    (ha : g * a * g⁻¹ ∈ Subgroup.closure ({a, b} : Set Y))
    (hb : g * b * g⁻¹ ∈ Subgroup.closure ({a, b} : Set Y)) [Finite Y] :
    g ∈ Subgroup.normalizer (Subgroup.closure ({a, b} : Set Y) : Set Y) := by
  set B := Subgroup.closure ({a, b} : Set Y) with hB
  have hle : B ≤ B.comap (MulAut.conj g).toMonoidHom := by
    rw [hB, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact ha
    · rw [Set.mem_singleton_iff.mp hx]; exact hb
  have hle' : conjSub g B ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hle hx
  have hcard : Nat.card B ≤ Nat.card (conjSub g B) := by
    unfold conjSub
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact mem_normalizer_iff_conjSub_eq.mpr (Subgroup.eq_of_le_of_card_ge hle' hcard)

theorem centralizer_le_of_conj {H : Subgroup Y} {z w g : Y} (hCz : Subgroup.centralizer ({z} : Set Y) ≤ H)
    (hg : g ∈ H) (hgz : g * z * g⁻¹ = w) : Subgroup.centralizer ({w} : Set Y) ≤ H := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer ({z} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hgz] at hx
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hx]
      _ = z * (g⁻¹ * x * g) := by group
  have h2 := H.mul_mem (H.mul_mem hg (hCz hx')) (H.inv_mem hg)
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [e] at h2

end Group2

section Conj

variable {Y : Type} [Group Y] [Finite Y]

theorem conj_of_mem {J : Subgroup Y} {w x : Y} (hw : IsUniqueInvolution J w) (hx : x ∈ J) :
    x * w * x⁻¹ = w := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp (isUniqueInvolution_le_centralizer hw hx)
  calc x * w * x⁻¹ = (w * x) * x⁻¹ := by rw [h]
    _ = w := by group

end Conj

namespace WylFrame

section Basic

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W : Subgroup Y} {z : Y}
  (F : WylFrame Ω W z) (c : Q3CL.Thompson.Ctx Ω W)

include c

theorem hnot₁ (i : Fin 4) : F.σ.K ∉ omegaNbr Ω (F.ρ i).K := fun h => by
  obtain ⟨j, hj⟩ := F.hclos F.σ i (Or.inr h)
  exact F.hfar j hj

theorem hnot₂ (i : Fin 4) : (F.ρ i).K ∉ omegaNbr Ω F.σ.K := fun h => by
  have hcomm := c.comm_of_omega F.σ (F.ρ i) h
  exact F.hnot₁ c i (c.omega_of_comm (F.ρ i) F.σ (F.hfar i).symm hcomm.symm)

theorem conj_t' (k : Fin 4) : (F.ρ k).r * F.t' * (F.ρ k).r⁻¹ = z * F.t' :=
  c.conj_involution (F.ρ k) F.σ (F.hfar k).symm (F.hnot₁ c k) (F.hz k) F.ht'

theorem conj_z (k : Fin 4) : F.σ.r * z * F.σ.r⁻¹ = F.t' * z :=
  c.conj_involution F.σ (F.ρ k) (F.hfar k) (F.hnot₂ c k) F.ht' (F.hz k)

end Basic

section Elements

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W : Subgroup Y} {z : Y}
  (F : WylFrame Ω W z) (c : Q3CL.Thompson.Ctx Ω W)

include F

theorem a_mem_K (i : Fin 4) : F.a i ∈ (F.ρ i).K := (F.ρ i).hRK.1 (F.ha i).1.1

theorem a_mem_W (i : Fin 4) : F.a i ∈ W := (F.ha i).1.2

theorem a_sq (i : Fin 4) : F.a i * F.a i = z :=
  T7A.sq_eq_of_orderOf_four (F.hz i) (F.a_mem_K i) (F.ha i).2

theorem z_sq : z * z = 1 := (F.hz 0).sq

theorem z_ne_one : z ≠ 1 := (F.hz 0).ne_one

theorem t'_sq : F.t' * F.t' = 1 := F.ht'.sq

theorem t'_ne_one : F.t' ≠ 1 := F.ht'.ne_one

theorem t'_ne_z : F.t' ≠ z := fun h => by
  have h' : IsUniqueInvolution F.σ.K z := by
    have := F.ht'
    rwa [h] at this
  obtain ⟨i, hi⟩ := F.hcover F.σ.K F.σ.hK h'
  exact F.hfar i hi

include c

theorem z_mem_W : z ∈ W := c.mem_W_of_isUniqueInvolution (F.ρ 0) (F.hz 0)

theorem t'_mem_W : F.t' ∈ W := c.mem_W_of_isUniqueInvolution F.σ F.ht'

theorem zt' (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : z * F.t' = F.t' * z :=
  hc z (F.z_mem_W c) F.t' (F.t'_mem_W c)

theorem swap_k (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (k : Fin 4) :
    ((F.ρ k).r * F.σ.r * (F.ρ k).r⁻¹) * z * ((F.ρ k).r * F.σ.r * (F.ρ k).r⁻¹)⁻¹ = F.t' ∧
    ((F.ρ k).r * F.σ.r * (F.ρ k).r⁻¹) * F.t' * ((F.ρ k).r * F.σ.r * (F.ρ k).r⁻¹)⁻¹ = z ∧
    ((F.ρ k).r * ((F.ρ k).r * F.σ.r * (F.ρ k).r⁻¹)) * z *
      ((F.ρ k).r * ((F.ρ k).r * F.σ.r * (F.ρ k).r⁻¹))⁻¹ = z * F.t' ∧
    ((F.ρ k).r * ((F.ρ k).r * F.σ.r * (F.ρ k).r⁻¹)) * F.t' *
      ((F.ρ k).r * ((F.ρ k).r * F.σ.r * (F.ρ k).r⁻¹))⁻¹ = z :=
  swap_relations (F.zt' c hc) F.z_sq F.t'_sq
    (conj_of_mem (F.hz k) ((F.ρ k).hRK.1 (F.ρ k).hr)) (F.conj_t' c k) (F.conj_z c k)
    (conj_of_mem F.ht' (F.σ.hRK.1 F.σ.hr))

end Elements

section E

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W : Subgroup Y} {z : Y}
  (F : WylFrame Ω W z) (c : Q3CL.Thompson.Ctx Ω W)
  (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)

@[expose] def E : Subgroup Y := Subgroup.closure ({z, F.t'} : Set Y)

include F c hc

theorem E_sq : ∀ x ∈ F.E, x * x = 1 :=
  Perp24.closure_pair_sq F.z_sq F.t'_sq (F.zt' c hc)

theorem E_isPGroup : IsPGroup 2 F.E := Perp24.isPGroup_two_of_sq (F.E_sq c hc)

theorem E_card : Nat.card F.E = 4 :=
  S28B.card_closure_pair_eq_four F.z_sq F.t'_sq (F.zt' c hc) F.z_ne_one F.t'_ne_one F.t'_ne_z

theorem E_cases : ∀ x ∈ F.E, x = 1 ∨ x = z ∨ x = F.t' ∨ x = z * F.t' :=
  Perp24.closure_pair_cases F.z_sq F.t'_sq (F.zt' c hc)

omit c hc

theorem z_mem_E : z ∈ F.E := Subgroup.subset_closure (Set.mem_insert _ _)

theorem t'_mem_E : F.t' ∈ F.E := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem zt'_mem_E : z * F.t' ∈ F.E := F.E.mul_mem F.z_mem_E F.t'_mem_E

theorem mem_normalizer_E {g : Y} (hz : g * z * g⁻¹ ∈ F.E) (ht : g * F.t' * g⁻¹ ∈ F.E) :
    g ∈ Subgroup.normalizer (F.E : Set Y) :=
  mem_normalizer_closure_pair hz ht

include c

theorem y_mem_normE (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (k : Fin 4) :
    (F.ρ k).r * F.σ.r * (F.ρ k).r⁻¹ ∈ Subgroup.normalizer (F.E : Set Y) := by
  obtain ⟨h1, h2, -, -⟩ := F.swap_k c hc k
  exact F.mem_normalizer_E (by rw [h1]; exact F.t'_mem_E) (by rw [h2]; exact F.z_mem_E)

theorem g_mem_normE (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (k : Fin 4) :
    (F.ρ k).r * ((F.ρ k).r * F.σ.r * (F.ρ k).r⁻¹) ∈ Subgroup.normalizer (F.E : Set Y) := by
  obtain ⟨-, -, h3, h4⟩ := F.swap_k c hc k
  exact F.mem_normalizer_E (by rw [h3]; exact F.zt'_mem_E) (by rw [h4]; exact F.z_mem_E)

end E

end WylFrame

end Perp22Wyl

end CFSG.CGT.PushingUpLit.SolKNA.R4