module

public import CFSG.CGT.Stroth77.Section223Layer
public import CFSG.CGT.Stroth77.Section223Sylow
public import CFSG.GroupTheory.OddInversion

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace S223

variable {G : Type} [Group G]

@[expose] def commX (D V : Subgroup G) : Subgroup G where
  carrier := {k | k ∈ Subgroup.centralizer (D : Set G) ∧ ∀ v ∈ V, k⁻¹ * (v⁻¹ * k * v) ∈ D}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun v hv => ?_⟩
    have hc := (Subgroup.mem_centralizer_iff.mp hb) _ (ha' v hv)
    have e : (a * b)⁻¹ * (v⁻¹ * (a * b) * v) =
        (b⁻¹ * ((a⁻¹ * (v⁻¹ * a * v)) * b)) * (b⁻¹ * (v⁻¹ * b * v)) := by group
    rw [e, hc, inv_mul_cancel_left]
    exact mul_mem (ha' v hv) (hb' v hv)
  one_mem' := ⟨one_mem _, fun v _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun v hv => ?_⟩
    have hc := (Subgroup.mem_centralizer_iff.mp ha) _ (inv_mem (ha' v hv))
    have e : a⁻¹⁻¹ * (v⁻¹ * a⁻¹ * v) = a * (a⁻¹ * (v⁻¹ * a * v))⁻¹ * a⁻¹ := by group
    rw [e, ← hc, mul_inv_cancel_right]
    exact inv_mem (ha' v hv)

theorem comm_mul_commX {D V : Subgroup G} {a b v : G} (hb : b ∈ commX D V) (hv : v ∈ V)
    (ha : a ∈ commX D V) :
    (a * b)⁻¹ * (v⁻¹ * (a * b) * v) = (a⁻¹ * (v⁻¹ * a * v)) * (b⁻¹ * (v⁻¹ * b * v)) := by
  have hc := (Subgroup.mem_centralizer_iff.mp hb.1) _ (ha.2 v hv)
  calc (a * b)⁻¹ * (v⁻¹ * (a * b) * v) =
      (b⁻¹ * (a⁻¹ * (v⁻¹ * a * v) * b)) * (b⁻¹ * (v⁻¹ * b * v)) := by group
    _ = (a⁻¹ * (v⁻¹ * a * v)) * (b⁻¹ * (v⁻¹ * b * v)) := by
      rw [hc, inv_mul_cancel_left]

theorem comm_pow_commX {D V : Subgroup G} {a v : G} (ha : a ∈ commX D V) (hv : v ∈ V) (n : ℕ) :
    (a ^ n)⁻¹ * (v⁻¹ * a ^ n * v) = (a⁻¹ * (v⁻¹ * a * v)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, comm_mul_commX ha hv (pow_mem ha n), ih, pow_succ]

theorem le_commX {D V : Subgroup G} (hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hV : V ≤ Subgroup.normalizer (D : Set G)) : D ≤ commX D V := fun d hd =>
  ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx d hd, fun _ hv =>
    mul_mem (inv_mem hd) ((Subgroup.mem_normalizer_iff''.mp (hV hv) d).mp hd)⟩

theorem mem_normalizer_commX [Finite G] {D V : Subgroup G} {g : G}
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (hgV : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer (commX D V : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (D : Set G) →
      g ∈ Subgroup.normalizer (V : Set G) → ∀ k ∈ commX D V, g * k * g⁻¹ ∈ commX D V := by
    intro g hgD hgV k hk
    refine ⟨?_, fun v hv => ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hd' : g⁻¹ * d * g ∈ D := (Subgroup.mem_normalizer_iff''.mp hgD d).mp hd
      have hc := (Subgroup.mem_centralizer_iff.mp hk.1) _ hd'
      calc d * (g * k * g⁻¹) = g * ((g⁻¹ * d * g) * k) * g⁻¹ := by group
        _ = g * (k * (g⁻¹ * d * g)) * g⁻¹ := by rw [hc]
        _ = g * k * g⁻¹ * d := by group
    · have hv' : g⁻¹ * v * g ∈ V := (Subgroup.mem_normalizer_iff''.mp hgV v).mp hv
      have h1 := hk.2 _ hv'
      have h2 : g * (k⁻¹ * ((g⁻¹ * v * g)⁻¹ * k * (g⁻¹ * v * g))) * g⁻¹ ∈ D := by
        have := (Subgroup.mem_normalizer_iff''.mp (inv_mem hgD) _).mp h1
        simpa using this
      convert h2 using 1
      group
  exact mem_normalizer_of_conj_mem (key hgD hgV)

theorem mem_centralizer_closure {S : Set G} {c : G} (h : ∀ s ∈ S, s * c = c * s) :
    c ∈ Subgroup.centralizer (Subgroup.closure S : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy =>
    calc x * y * c = x * (y * c) := by group
      _ = x * (c * y) := by rw [hy]
      _ = (x * c) * y := by group
      _ = (c * x) * y := by rw [hx]
      _ = c * (x * y) := by group
  | inv x _ hx =>
    calc x⁻¹ * c = x⁻¹ * (c * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * c) * x⁻¹ := by rw [hx]
      _ = c * x⁻¹ := by group

end S223

namespace StrothFrame

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

@[expose] def V : Subgroup G := Subgroup.closure {F.dA.uv, F.dA.t}

theorem V_le_E : F.V ≤ F.E := by
  rw [StrothFrame.V, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact F.uv_mem_E
  · exact F.t_mem_E

theorem mem_normalizer_V {g : G} (huv : g * F.dA.uv * g⁻¹ ∈ F.V)
    (ht : g * F.dA.t * g⁻¹ ∈ F.V) : g ∈ Subgroup.normalizer (F.V : Set G) := by
  refine S223.mem_normalizer_of_conj_mem fun x hx => ?_
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact huv
    · exact ht
  | one => simp
  | mul x y _ _ hx hy =>
    have := mul_mem hx hy
    convert this using 1
    group
  | inv x _ hx =>
    have := inv_mem hx
    convert this using 1
    group

theorem uv_mem_V : F.dA.uv ∈ F.V := Subgroup.subset_closure (by simp)

theorem t_mem_V : F.dA.t ∈ F.V := Subgroup.subset_closure (by simp)

theorem ρ_mem_normalizer_V : F.dA.ρ ∈ Subgroup.normalizer (F.V : Set G) := by
  have e : F.dA.uv * F.dA.t * F.dA.ρ = F.dA.ρ * F.dA.uv := by
    calc F.dA.uv * F.dA.t * F.dA.ρ = F.dA.uv * (F.dA.t * F.dA.ρ) := by group
      _ = F.dA.uv * (F.dA.ρ * F.dA.uv * F.dA.t) := by rw [F.dA.t_rho]
      _ = (F.dA.uv * F.dA.ρ) * F.dA.uv * F.dA.t := by group
      _ = (F.dA.ρ * F.dA.t) * F.dA.uv * F.dA.t := by rw [F.dA.uv_rho]
      _ = F.dA.ρ * (F.dA.t * F.dA.uv) * F.dA.t := by group
      _ = F.dA.ρ * (F.dA.uv * F.dA.t) * F.dA.t := by rw [F.dA.uv_comm_t]
      _ = F.dA.ρ * F.dA.uv * (F.dA.t * F.dA.t) := by group
      _ = F.dA.ρ * F.dA.uv := by rw [F.dA.t_sq, mul_one]
  have h1 : F.dA.ρ * F.dA.uv * F.dA.ρ⁻¹ = F.dA.uv * F.dA.t := by
    calc F.dA.ρ * F.dA.uv * F.dA.ρ⁻¹ = (F.dA.uv * F.dA.t * F.dA.ρ) * F.dA.ρ⁻¹ := by rw [e]
      _ = F.dA.uv * F.dA.t := by group
  have h2 : F.dA.ρ * F.dA.t * F.dA.ρ⁻¹ = F.dA.uv := by
    calc F.dA.ρ * F.dA.t * F.dA.ρ⁻¹ = (F.dA.uv * F.dA.ρ) * F.dA.ρ⁻¹ := by rw [F.dA.uv_rho]
      _ = F.dA.uv := by group
  refine F.mem_normalizer_V ?_ ?_
  · rw [h1]; exact mul_mem F.uv_mem_V F.t_mem_V
  · rw [h2]; exact F.uv_mem_V

theorem u_mem_normalizer_V : F.dA.u ∈ Subgroup.normalizer (F.V : Set G) := by
  have hu : F.dA.u⁻¹ = F.dA.u := inv_eq_of_mul_eq_one_right F.dA.u_sq
  have h1 : F.dA.u * F.dA.uv * F.dA.u⁻¹ = F.dA.uv := by
    rw [← F.dA.uv_comm_u, mul_inv_cancel_right]
  have h2 : F.dA.u * F.dA.t * F.dA.u⁻¹ = F.dA.uv * F.dA.t := by
    calc F.dA.u * F.dA.t * F.dA.u⁻¹ = F.dA.u * (F.dA.t * F.dA.u) := by rw [hu]; group
      _ = F.dA.u * (F.dA.u * F.dA.uv * F.dA.t) := by rw [F.dA.t_u]
      _ = (F.dA.u * F.dA.u) * F.dA.uv * F.dA.t := by group
      _ = F.dA.uv * F.dA.t := by rw [F.dA.u_sq, one_mul]
  refine F.mem_normalizer_V ?_ ?_
  · rw [h1]; exact F.uv_mem_V
  · rw [h2]; exact mul_mem F.uv_mem_V F.t_mem_V

theorem u_ne_one : F.dA.u ≠ 1 := by
  intro h1
  have h2 : conjBy F.dA.u_mem F.dA.a = F.dA.a := by
    apply Subtype.ext
    simp [conjBy, h1]
  have h3 := F.dA.conj_apply F.dA.u_mem F.dA.u_conj Torus.a
  rw [show Additive.toMul (F.dA.e.symm Torus.a) = F.dA.a from rfl, h2] at h3
  have h4 : F.dA.e (Additive.ofMul F.dA.a) = Torus.a := by simp [StrothWeakTypeData.a]
  rw [h4] at h3
  exact (show (Type100.action 1).φu Torus.a ≠ (Torus.a : Torus (Type100.k 1)) by decide) h3.symm

theorem orderOf_u : orderOf F.dA.u = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact F.dA.u_sq) F.u_ne_one

theorem rho_cube_mem_centralizer_E : F.dA.ρ ^ 3 ∈ Subgroup.centralizer (F.E : Set G) := by
  have hA := F.dA.rho_cube_mem
  have h1 : F.dA.ρ⁻¹ * F.dA.uv * F.dA.ρ = F.dA.t := by rw [mul_assoc, F.dA.uv_rho]; group
  have h2 : F.dA.ρ⁻¹ * F.dA.t * F.dA.ρ = F.dA.uv * F.dA.t := by rw [mul_assoc, F.dA.t_rho]; group
  have h3 : F.dA.ρ⁻¹ * (F.dA.uv * F.dA.t) * F.dA.ρ = F.dA.uv := by
    calc F.dA.ρ⁻¹ * (F.dA.uv * F.dA.t) * F.dA.ρ =
        (F.dA.ρ⁻¹ * F.dA.uv * F.dA.ρ) * (F.dA.ρ⁻¹ * F.dA.t * F.dA.ρ) := by group
      _ = F.dA.t * (F.dA.uv * F.dA.t) := by rw [h1, h2]
      _ = (F.dA.t * F.dA.uv) * F.dA.t := by group
      _ = (F.dA.uv * F.dA.t) * F.dA.t := by rw [F.dA.uv_comm_t]
      _ = F.dA.uv * (F.dA.t * F.dA.t) := by group
      _ = F.dA.uv := by rw [F.dA.t_sq, mul_one]
  have huv : (F.dA.ρ * F.dA.ρ * F.dA.ρ)⁻¹ * F.dA.uv * (F.dA.ρ * F.dA.ρ * F.dA.ρ) = F.dA.uv := by
    calc (F.dA.ρ * F.dA.ρ * F.dA.ρ)⁻¹ * F.dA.uv * (F.dA.ρ * F.dA.ρ * F.dA.ρ) =
        F.dA.ρ⁻¹ * (F.dA.ρ⁻¹ * (F.dA.ρ⁻¹ * F.dA.uv * F.dA.ρ) * F.dA.ρ) * F.dA.ρ := by group
      _ = F.dA.uv := by rw [h1, h2, h3]
  have ht : (F.dA.ρ * F.dA.ρ * F.dA.ρ)⁻¹ * F.dA.t * (F.dA.ρ * F.dA.ρ * F.dA.ρ) = F.dA.t := by
    calc (F.dA.ρ * F.dA.ρ * F.dA.ρ)⁻¹ * F.dA.t * (F.dA.ρ * F.dA.ρ * F.dA.ρ) =
        F.dA.ρ⁻¹ * (F.dA.ρ⁻¹ * (F.dA.ρ⁻¹ * F.dA.t * F.dA.ρ) * F.dA.ρ) * F.dA.ρ := by group
      _ = F.dA.t := by rw [h2, h3, h1]
  have hρ3 : F.dA.ρ ^ 3 = F.dA.ρ * F.dA.ρ * F.dA.ρ := by rw [pow_three, mul_assoc]
  rw [F.E_eq]
  refine S223.mem_centralizer_closure fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ((Subgroup.mem_centralizer_iff.mp hA) _ (pow_mem F.dA.a.2 2))
  · exact ((Subgroup.mem_centralizer_iff.mp hA) _ (pow_mem F.dA.b.2 2))
  · rw [hρ3]
    calc F.dA.uv * (F.dA.ρ * F.dA.ρ * F.dA.ρ) = (F.dA.ρ * F.dA.ρ * F.dA.ρ) *
        ((F.dA.ρ * F.dA.ρ * F.dA.ρ)⁻¹ * F.dA.uv * (F.dA.ρ * F.dA.ρ * F.dA.ρ)) := by group
      _ = (F.dA.ρ * F.dA.ρ * F.dA.ρ) * F.dA.uv := by rw [huv]
  · rw [hρ3]
    calc F.dA.t * (F.dA.ρ * F.dA.ρ * F.dA.ρ) = (F.dA.ρ * F.dA.ρ * F.dA.ρ) *
        ((F.dA.ρ * F.dA.ρ * F.dA.ρ)⁻¹ * F.dA.t * (F.dA.ρ * F.dA.ρ * F.dA.ρ)) := by group
      _ = (F.dA.ρ * F.dA.ρ * F.dA.ρ) * F.dA.t := by rw [ht]

end StrothFrame

namespace StrothFrame.IsTyped

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem comm (_h : F.IsTyped D dD) : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := comm_of_torus dD.e

theorem uv_mem_normalizer (h : F.IsTyped D dD) : F.dA.uv ∈ Subgroup.normalizer (D : Set G) :=
  h.uv_eq ▸ dD.uv_mem

theorem t_mem_normalizer (h : F.IsTyped D dD) : F.dA.t ∈ Subgroup.normalizer (D : Set G) :=
  h.t_eq ▸ dD.t_mem

theorem u_mem_normalizer (h : F.IsTyped D dD) : F.dA.u ∈ Subgroup.normalizer (D : Set G) :=
  h.u_eq ▸ dD.u_mem

theorem ρ_mem_normalizer (h : F.IsTyped D dD) : F.dA.ρ ∈ Subgroup.normalizer (D : Set G) :=
  h.ρ_eq ▸ dD.ρ_mem

theorem V_le_normalizer (h : F.IsTyped D dD) : F.V ≤ Subgroup.normalizer (D : Set G) := by
  rw [StrothFrame.V, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact h.uv_mem_normalizer
  · exact h.t_mem_normalizer

theorem mem_centralizer_E (h : F.IsTyped D dD) {c : G}
    (hcD : c ∈ Subgroup.centralizer (D : Set G)) (huv : F.dA.uv * c = c * F.dA.uv)
    (ht : F.dA.t * c = c * F.dA.t) : c ∈ Subgroup.centralizer (F.E : Set G) := by
  rw [F.E_eq]
  refine S223.mem_centralizer_closure fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact (Subgroup.mem_centralizer_iff.mp hcD) _ (h.A_le (pow_mem F.dA.a.2 2))
  · exact (Subgroup.mem_centralizer_iff.mp hcD) _ (h.A_le (pow_mem F.dA.b.2 2))
  · exact huv
  · exact ht

theorem _root_.CFSG.CGT.Stroth77.S223.mem_normalizer_centralizer {G : Type} [Group G] [Finite G]
    {D : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) := by
  refine S223.mem_normalizer_of_conj_mem fun c hc => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : g⁻¹ * d * g ∈ D := (Subgroup.mem_normalizer_iff''.mp hg d).mp hd
  have h1 := (Subgroup.mem_centralizer_iff.mp hc) _ hd'
  calc d * (g * c * g⁻¹) = g * ((g⁻¹ * d * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * d * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * d := by group

section OddPart

variable {K : Subgroup G} (hKC : K ≤ Subgroup.centralizer (F.E : Set G))
  (hKiff : ∀ c : G, c ∈ K ↔ c ∈ Subgroup.centralizer (F.E : Set G) ∧ Odd (orderOf c))
  (hdec : ∀ c ∈ Subgroup.centralizer (F.E : Set G), ∃ e ∈ F.E, ∃ k ∈ K, c = e * k)

include hKC in
theorem odd_le_commX (_h : F.IsTyped D dD) :
    K ⊓ Subgroup.centralizer (D : Set G) ≤ S223.commX D F.V := fun o ho =>
  ⟨ho.2, fun v hv => by
    have hc := (Subgroup.mem_centralizer_iff.mp (hKC ho.1)) v (F.V_le_E hv)
    rw [show v⁻¹ * o * v = o by rw [mul_assoc, ← hc]; group, inv_mul_cancel]
    exact one_mem _⟩

include hKiff in
theorem commX_le_normalizer_odd (h : F.IsTyped D dD) :
    S223.commX D F.V ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  intro x hx
  refine S223.mem_normalizer_of_conj_mem fun o ho => ?_
  have hoX : o ∈ S223.commX D F.V :=
    ⟨ho.2, fun v hv => by
      have hc := (Subgroup.mem_centralizer_iff.mp ((hKiff o).1 ho.1).1) v (F.V_le_E hv)
      rw [show v⁻¹ * o * v = o by rw [mul_assoc, ← hc]; group, inv_mul_cancel]
      exact one_mem _⟩
  have hcD : x * o * x⁻¹ ∈ Subgroup.centralizer (D : Set G) :=
    mul_mem (mul_mem hx.1 ho.2) (inv_mem hx.1)
  have hcommV : ∀ v ∈ F.V, v * (x * o * x⁻¹) = (x * o * x⁻¹) * v := by
    intro v hv
    have hxi : x⁻¹ ∈ S223.commX D F.V := inv_mem hx
    have h1 := S223.comm_mul_commX (mul_mem hoX hxi) hv hx
    have h2 := S223.comm_mul_commX hxi hv hoX
    have h3 := S223.comm_mul_commX hxi hv hx
    have hov : o⁻¹ * (v⁻¹ * o * v) = 1 := by
      have hc := (Subgroup.mem_centralizer_iff.mp ((hKiff o).1 ho.1).1) v (F.V_le_E hv)
      rw [show v⁻¹ * o * v = o by rw [mul_assoc, ← hc]; group, inv_mul_cancel]
    rw [mul_inv_cancel, show (1 : G)⁻¹ * (v⁻¹ * 1 * v) = 1 by group] at h3
    have hy : (x * o * x⁻¹)⁻¹ * (v⁻¹ * (x * o * x⁻¹) * v) = 1 := by
      rw [show x * o * x⁻¹ = x * (o * x⁻¹) by group, h1, h2, hov, one_mul]
      exact h3.symm
    calc v * (x * o * x⁻¹) = v * ((x * o * x⁻¹) *
        ((x * o * x⁻¹)⁻¹ * (v⁻¹ * (x * o * x⁻¹) * v))) := by rw [hy, mul_one]
      _ = (x * o * x⁻¹) * v := by group
  refine ⟨(hKiff _).2 ⟨h.mem_centralizer_E hcD ?_ ?_, ?_⟩, hcD⟩
  · exact hcommV _ F.uv_mem_V
  · exact hcommV _ F.t_mem_V
  · rw [show x * o * x⁻¹ = MulAut.conj x o by rfl, MulEquiv.orderOf_eq]
    exact ((hKiff o).1 ho.1).2

include hKC hKiff hdec in
theorem pow_mem_odd_of_mem_commX (h : F.IsTyped D dD) {x : G} (hx : x ∈ S223.commX D F.V) :
    ∃ n : ℕ, x ^ (2 ^ n) ∈ K ⊓ Subgroup.centralizer (D : Set G) := by
  set N := Nat.card D with hN
  obtain ⟨r, hr⟩ : ∃ r, N = 2 ^ r := ⟨τ.k 0 + τ.k 1 + τ.k 2, dD.card⟩
  refine ⟨r + 1, ?_⟩
  set y := x ^ N with hy
  have hyD : y ∈ Subgroup.centralizer (D : Set G) := pow_mem hx.1 N
  have hyv : ∀ v ∈ F.V, v * y = y * v := by
    intro v hv
    have h1 := S223.comm_pow_commX hx hv N
    have h2 : (x⁻¹ * (v⁻¹ * x * v)) ^ N = 1 := by
      have := pow_card_eq_one' (G := D) (x := ⟨_, hx.2 v hv⟩)
      exact congrArg Subtype.val this
    rw [h2] at h1
    calc v * y = v * (y * (y⁻¹ * (v⁻¹ * y * v))) := by rw [hy, h1, mul_one]
      _ = y * v := by group
  have hyE : y ∈ Subgroup.centralizer (F.E : Set G) :=
    h.mem_centralizer_E hyD (hyv _ F.uv_mem_V) (hyv _ F.t_mem_V)
  obtain ⟨e, he, k, hk, hyek⟩ := hdec y hyE
  have hek : e * k = k * e := (Subgroup.mem_centralizer_iff.mp (hKC hk)) e he
  have he2 : e * e = 1 := F.E_sq he
  have hkodd : Odd (orderOf k) := ((hKiff k).1 hk).2
  have hey : e = y ^ (orderOf k) := by
    rw [hyek, (Commute.mul_pow hek (orderOf k)), pow_orderOf_eq_one, mul_one]
    obtain ⟨m, hm⟩ := hkodd
    rw [hm, pow_succ, pow_mul, pow_two, he2, one_pow, one_mul]
  have heD : e ∈ Subgroup.centralizer (D : Set G) := hey ▸ pow_mem hyD _
  have hkD : k ∈ Subgroup.centralizer (D : Set G) := by
    have : k = e⁻¹ * y := by rw [hyek]; group
    rw [this]
    exact mul_mem (inv_mem heD) hyD
  have hy2 : y * y = k * k := by
    rw [hyek]
    calc e * k * (e * k) = (e * e) * (k * k) := by
          rw [mul_assoc, ← mul_assoc k e k, ← hek]; group
      _ = k * k := by rw [he2, one_mul]
  have hxpow : x ^ (2 ^ (r + 1)) = y * y := by
    rw [hy, pow_succ, pow_mul, ← hr, pow_two]
  rw [hxpow, hy2]
  exact ⟨mul_mem hk hk, mul_mem hkD hkD⟩

include hKiff in
theorem ρ_mem_normalizer_odd (h : F.IsTyped D dD) :
    F.dA.ρ ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  have hρE : F.dA.ρ ∈ Subgroup.normalizer (F.E : Set G) := F.L_le F.dA.ρ_mem_L
  refine S223.mem_normalizer_of_conj_mem fun c hc => ?_
  have hcE := ((hKiff c).1 hc.1)
  refine ⟨(hKiff _).2 ⟨?_, ?_⟩, ?_⟩
  · exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (S223.mem_normalizer_centralizer hρE)) ▸ ⟨c, hcE.1, rfl⟩
  · rw [show F.dA.ρ * c * F.dA.ρ⁻¹ = MulAut.conj F.dA.ρ c by rfl, MulEquiv.orderOf_eq]
    exact hcE.2
  · exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (S223.mem_normalizer_centralizer h.ρ_mem_normalizer)) ▸ ⟨c, hc.2, rfl⟩

include hKiff in
theorem u_mem_normalizer_odd (h : F.IsTyped D dD) :
    F.dA.u ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  have huE : F.dA.u ∈ Subgroup.normalizer (F.E : Set G) := F.L_le F.dA.u_mem_L
  refine S223.mem_normalizer_of_conj_mem fun c hc => ?_
  have hcE := ((hKiff c).1 hc.1)
  refine ⟨(hKiff _).2 ⟨?_, ?_⟩, ?_⟩
  · exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (S223.mem_normalizer_centralizer huE)) ▸ ⟨c, hcE.1, rfl⟩
  · rw [show F.dA.u * c * F.dA.u⁻¹ = MulAut.conj F.dA.u c by rfl, MulEquiv.orderOf_eq]
    exact hcE.2
  · exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (S223.mem_normalizer_centralizer h.u_mem_normalizer)) ▸ ⟨c, hc.2, rfl⟩

include hKiff in
theorem mem_sup_rho (h : F.IsTyped D dD) {y : G}
    (hy : y ∈ (K ⊓ Subgroup.centralizer (D : Set G)) ⊔ Subgroup.zpowers F.dA.ρ) :
    ∃ c ∈ K ⊓ Subgroup.centralizer (D : Set G), ∃ j : ℤ, y = c * F.dA.ρ ^ j := by
  have hle : Subgroup.zpowers F.dA.ρ ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact h.ρ_mem_normalizer_odd hKiff
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hy
  obtain ⟨c, hc, z, hz, rfl⟩ := hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ⟨c, hc, j, rfl⟩

theorem zpow_rho_mem_of_two {O : Subgroup G} {j : ℤ} (h2 : F.dA.ρ ^ (2 * j) ∈ O) :
    F.dA.ρ ^ j ∈ O := by
  obtain ⟨m, hm⟩ := F.dA.rho_odd
  have hr : F.dA.ρ ^ ((2 * m + 1 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hm, pow_orderOf_eq_one]
  have e : F.dA.ρ ^ j = (F.dA.ρ ^ (2 * j)) ^ ((m : ℤ) + 1) := by
    rw [← zpow_mul, show 2 * j * ((m : ℤ) + 1) = j + ((2 * m + 1 : ℕ) : ℤ) * j by push_cast; ring,
      zpow_add, zpow_mul, hr, one_zpow, mul_one]
  rw [e]
  exact zpow_mem h2 _

include hKiff in
theorem odd_card_sup_rho (h : F.IsTyped D dD) :
    Odd (Nat.card ((K ⊓ Subgroup.centralizer (D : Set G)) ⊔ Subgroup.zpowers F.dA.ρ :
      Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  have h2 : 2 ∣ Nat.card ((K ⊓ Subgroup.centralizer (D : Set G)) ⊔ Subgroup.zpowers F.dA.ρ :
      Subgroup G) := by
    rw [← even_iff_two_dvd]
    exact Nat.not_odd_iff_even.mp hev
  obtain ⟨⟨y, hy⟩, hord⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hord' : orderOf y = 2 := by rw [← hord]; exact Subgroup.orderOf_coe ⟨y, hy⟩
  have hy2 : y * y = 1 := by rw [← pow_two, ← hord', pow_orderOf_eq_one]
  obtain ⟨c, hc, j, rfl⟩ := h.mem_sup_rho hKiff hy
  have hρO := h.ρ_mem_normalizer_odd hKiff
  have hw : F.dA.ρ ^ j * c * (F.dA.ρ ^ j)⁻¹ ∈ K ⊓ Subgroup.centralizer (D : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (zpow_mem hρO j) c).mp hc
  have e : (F.dA.ρ ^ j * c * (F.dA.ρ ^ j)⁻¹)⁻¹ * c⁻¹ = F.dA.ρ ^ (2 * j) := by
    calc (F.dA.ρ ^ j * c * (F.dA.ρ ^ j)⁻¹)⁻¹ * c⁻¹ =
        (F.dA.ρ ^ j * c * (F.dA.ρ ^ j)⁻¹)⁻¹ * c⁻¹ * (c * F.dA.ρ ^ j * (c * F.dA.ρ ^ j)) := by
          rw [hy2, mul_one]
      _ = F.dA.ρ ^ j * F.dA.ρ ^ j := by group
      _ = F.dA.ρ ^ (2 * j) := by rw [two_mul, zpow_add]
  have hρj := zpow_rho_mem_of_two (F := F) (e ▸ mul_mem (inv_mem hw) (inv_mem hc))
  have hyO := mul_mem hc hρj
  have hodd := ((hKiff _).1 hyO.1).2
  rw [hord'] at hodd
  exact absurd hodd (by decide)

end OddPart

theorem isPGroup (_h : F.IsTyped D dD) : IsPGroup 2 D := IsPGroup.of_card dD.card

theorem _root_.CFSG.CGT.Stroth77.StrothFrame.isPGroup_V (F : StrothFrame G) : IsPGroup 2 F.V :=
  (isPGroup_of_isE F.E_isE).to_le F.V_le_E

theorem exists_mem_commX_not_mem (h : F.IsTyped D dD)
    (hns : ¬ IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D) :
    ∃ d ∈ S223.commX D F.V, d ∉ D ∧ d * d ∈ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := h.comm
  have hDC : D ≤ Subgroup.centralizer (D : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
  obtain ⟨R, hR, huvR, htR⟩ := S223.exists_isSylowIn_mem_normalizer₂
    (X := Subgroup.centralizer (D : Set G))
    (S223.mem_normalizer_centralizer h.uv_mem_normalizer) F.dA.uv_sq
    (S223.mem_normalizer_centralizer h.t_mem_normalizer) F.dA.t_sq F.dA.uv_comm_t
  have hRD : R ≤ Subgroup.normalizer (D : Set G) :=
    hR.1.trans (Subgroup.centralizer_le_normalizer _)
  have hDR : D ≤ R := by
    have hsup : IsPGroup 2 (R ⊔ D : Subgroup G) := hR.2.1.to_sup_of_normal_right' h.isPGroup hRD
    exact le_sup_right.trans (S223.le_of_isSylowIn hR le_sup_left (sup_le hR.1 hDC) hsup)
  have hDR' : D < R := lt_of_le_of_ne hDR fun hEq => hns (hEq ▸ hR)
  have hVR : F.V ≤ Subgroup.normalizer (R : Set G) := by
    rw [StrothFrame.V, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact huvR
    · exact htR
  have hP : IsPGroup 2 (R ⊔ F.V : Subgroup G) := hR.2.1.to_sup_of_normal_left' F.isPGroup_V hVR
  obtain ⟨d, hdR, hdD, hd2, hdc⟩ := S223.exists_mem_sq_comm_mem hP hDR' le_sup_left
    (sup_le hRD h.V_le_normalizer) (sup_le Subgroup.le_normalizer hVR)
  refine ⟨d, ⟨hR.1 hdR, fun v hv => ?_⟩, hdD, hd2⟩
  have := hdc v (Subgroup.mem_sup_right hv)
  simpa [mul_assoc] using this

theorem exists_rho_change (h : F.IsTyped D dD)
    (hns : ¬ IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D) :
    ∃ (o : G) (Q : Subgroup G),
      o ∈ Subgroup.centralizer (F.E : Set G) ∧ o ∈ Subgroup.centralizer (D : Set G) ∧
      Odd (orderOf o) ∧ Odd (orderOf (F.dA.ρ * o)) ∧
      F.dA.u * (F.dA.ρ * o) * F.dA.u * (F.dA.ρ * o) = 1 ∧
      IsPGroup 2 Q ∧ D < Q ∧ Q ≤ S223.commX D F.V ∧
      F.dA.u ∈ Subgroup.normalizer (Q : Set G) ∧
      F.dA.ρ * o ∈ Subgroup.normalizer (Q : Set G) ∧
      (F.dA.ρ * o) ^ 3 ∈ Subgroup.centralizer (Q : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := h.comm
  obtain ⟨K, hKC, hKodd, hKiff, hdec, -⟩ := exists_odd_complement_centralizer F.E_isE F.E_syl
  set O := K ⊓ Subgroup.centralizer (D : Set G) with hOdef
  set X := S223.commX D F.V with hXdef
  have hDX : D ≤ X := S223.le_commX hcomm h.V_le_normalizer
  have hOX : O ≤ X := h.odd_le_commX hKC
  have hXO : X ≤ Subgroup.normalizer (O : Set G) := h.commX_le_normalizer_odd hKiff
  have hOodd : Odd (Nat.card O) := hKodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hpow : ∀ x ∈ X, ∃ n : ℕ, x ^ (2 ^ n) ∈ O := fun x hx =>
    h.pow_mem_odd_of_mem_commX hKC hKiff hdec hx
  have hρX : F.dA.ρ ∈ Subgroup.normalizer (X : Set G) :=
    S223.mem_normalizer_commX h.ρ_mem_normalizer F.ρ_mem_normalizer_V
  have huX : F.dA.u ∈ Subgroup.normalizer (X : Set G) :=
    S223.mem_normalizer_commX h.u_mem_normalizer F.u_mem_normalizer_V
  have hρO := h.ρ_mem_normalizer_odd hKiff
  have huO := h.u_mem_normalizer_odd hKiff
  have huinv : F.dA.u⁻¹ = F.dA.u := inv_eq_of_mul_eq_one_right F.dA.u_sq
  obtain ⟨Q, hQ, huQ⟩ := S223.exists_isSylowIn_mem_normalizer huX F.dA.u_sq
  obtain ⟨d, hdX, hdD, hd2⟩ := h.exists_mem_commX_not_mem hns
  have hdN : d ∈ Subgroup.normalizer (D : Set G) := (Subgroup.centralizer_le_normalizer _) hdX.1
  have hDd : D ⊔ Subgroup.zpowers d ≤ X := sup_le hDX ((Subgroup.zpowers_le).mpr hdX)
  have hDdcard := S223.card_sup_zpowers_two hdN hd2 hdD
  have hDdp : IsPGroup 2 (D ⊔ Subgroup.zpowers d : Subgroup G) := by
    refine IsPGroup.of_card (n := τ.k 0 + τ.k 1 + τ.k 2 + 1) ?_
    rw [hDdcard, dD.card, pow_succ, mul_comm]
  have hcardQ : 2 * Nat.card D ≤ Nat.card Q := by
    rw [← hDdcard]
    exact S223.card_le_of_isSylowIn hQ hDd hDdp
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) :=
    hQ.1.trans fun x hx => (Subgroup.centralizer_le_normalizer _) hx.1
  have hDQ : D ≤ Q := by
    have hsup : IsPGroup 2 (Q ⊔ D : Subgroup G) := hQ.2.1.to_sup_of_normal_right' h.isPGroup hQD
    exact le_sup_right.trans (S223.le_of_isSylowIn hQ le_sup_left (sup_le hQ.1 hDX) hsup)
  have hDQ' : D < Q := by
    refine lt_of_le_of_ne hDQ fun hEq => ?_
    rw [← hEq] at hcardQ
    have hpos : 0 < Nat.card D := Nat.card_pos
    omega
  have hQρ := S223.isSylowIn_map_conj hQ (inv_mem hρX)
  obtain ⟨x, hxX, hxQ⟩ := S223.exists_conj_of_isSylowIn hQ hQρ
  obtain ⟨q, hq, o', ho', rfl⟩ := S223.exists_mul_eq_of_isSylowIn hQ hOX hXO hOodd hpow x hxX
  set o'' := q * o' * q⁻¹ with ho''def
  have ho'' : o'' ∈ O := (Subgroup.mem_normalizer_iff.mp (hXO (hQ.1 hq)) o').mp ho'
  have hρ₁Q : F.dA.ρ * o'' ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro z
    have h1 := hxQ (F.dA.ρ⁻¹ * z * F.dA.ρ)
    rw [S223.mem_map_conj, inv_inv,
      show F.dA.ρ * (F.dA.ρ⁻¹ * z * F.dA.ρ) * F.dA.ρ⁻¹ = z by group] at h1
    rw [h1]
    have e : (q * o')⁻¹ * (F.dA.ρ⁻¹ * z * F.dA.ρ) * (q * o') =
        q⁻¹ * ((F.dA.ρ * o'')⁻¹ * z * (F.dA.ρ * o'')) * q := by
      rw [ho''def]; group
    rw [e]
    constructor
    · intro hz
      have := mul_mem (mul_mem hq hz) (inv_mem hq)
      rwa [show q * (q⁻¹ * ((F.dA.ρ * o'')⁻¹ * z * (F.dA.ρ * o'')) * q) * q⁻¹ =
        (F.dA.ρ * o'')⁻¹ * z * (F.dA.ρ * o'') by group] at this
    · intro hz
      exact mul_mem (mul_mem (inv_mem hq) hz) hq
  set Y := O ⊔ Subgroup.zpowers F.dA.ρ with hYdef
  have hYodd : Odd (Nat.card Y) := h.odd_card_sup_rho hKiff
  set K₁ := Y ⊓ Subgroup.normalizer (Q : Set G) with hK₁def
  have hK₁odd : Odd (Nat.card K₁) := hYodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have huρ : F.dA.u * F.dA.ρ * F.dA.u⁻¹ = F.dA.ρ⁻¹ := by
    have e := F.dA.u_rho
    rw [huinv]
    calc F.dA.u * F.dA.ρ * F.dA.u = F.dA.u * F.dA.ρ * F.dA.u * (F.dA.ρ * F.dA.ρ⁻¹) := by group
      _ = (F.dA.u * F.dA.ρ * F.dA.u * F.dA.ρ) * F.dA.ρ⁻¹ := by group
      _ = F.dA.ρ⁻¹ := by rw [e, one_mul]
  have huY : F.dA.u ∈ Subgroup.normalizer (Y : Set G) := by
    refine S223.mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨c, hc, j, rfl⟩ := h.mem_sup_rho hKiff hy
    have e : F.dA.u * (c * F.dA.ρ ^ j) * F.dA.u⁻¹ =
        (F.dA.u * c * F.dA.u⁻¹) * (F.dA.u * F.dA.ρ * F.dA.u⁻¹) ^ j := by
      rw [conj_zpow]; group
    rw [e, huρ]
    exact mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp huO c).mp hc))
      (Subgroup.mem_sup_right ((Subgroup.zpowers F.dA.ρ).zpow_mem
        ((Subgroup.zpowers F.dA.ρ).inv_mem (Subgroup.mem_zpowers _)) j))
  have huK₁ : F.dA.u ∈ Subgroup.normalizer (K₁ : Set G) :=
    S223.mem_normalizer_of_conj_mem fun y hy =>
      ⟨(Subgroup.mem_normalizer_iff.mp huY y).mp hy.1,
        (Subgroup.normalizer (Q : Set G)).mul_mem
          ((Subgroup.normalizer (Q : Set G)).mul_mem huQ hy.2)
          ((Subgroup.normalizer (Q : Set G)).inv_mem huQ)⟩
  have hρ₁K₁ : F.dA.ρ * o'' ∈ K₁ :=
    ⟨Y.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers F.dA.ρ))
      (Subgroup.mem_sup_left ho''), hρ₁Q⟩
  obtain ⟨⟨c, i⟩, ⟨hc, hi⟩, hci⟩ :=
    (CFSG.OddInversion.odd_involution_product_decomposition hK₁odd F.orderOf_u huK₁).1.surjOn
      hρ₁K₁
  dsimp only at hc hi hci
  have hcO : c ∈ O := by
    obtain ⟨c', hc', j, hcj⟩ := h.mem_sup_rho hKiff hc.1.1
    have hcu : c * F.dA.u = F.dA.u * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have e1 : F.dA.u * c * F.dA.u⁻¹ = c := by rw [← hcu]; group
    have e2 : F.dA.u * c * F.dA.u⁻¹ = (F.dA.u * c' * F.dA.u⁻¹) * F.dA.ρ ^ (-j) := by
      rw [hcj, zpow_neg, ← inv_zpow, ← huρ, conj_zpow]; group
    have e3 : c'⁻¹ * (F.dA.u * c' * F.dA.u⁻¹) = F.dA.ρ ^ (2 * j) := by
      have h3 := e2.symm.trans (e1.trans hcj)
      have h4 : F.dA.u * c' * F.dA.u⁻¹ = c' * F.dA.ρ ^ j * F.dA.ρ ^ j := by
        calc F.dA.u * c' * F.dA.u⁻¹ =
            (F.dA.u * c' * F.dA.u⁻¹) * F.dA.ρ ^ (-j) * F.dA.ρ ^ j := by
              rw [mul_assoc _ (F.dA.ρ ^ (-j)), ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
          _ = c' * F.dA.ρ ^ j * F.dA.ρ ^ j := by rw [h3]
      rw [h4, two_mul, zpow_add]
      group
    have hρj := zpow_rho_mem_of_two (F := F) (O := O)
      (e3 ▸ mul_mem (inv_mem hc') ((Subgroup.mem_normalizer_iff.mp huO c').mp hc'))
    rw [hcj]
    exact mul_mem hc' hρj
  have hi' : i = c⁻¹ * (F.dA.ρ * o'') := by rw [← hci]; group
  have ho : F.dA.ρ⁻¹ * i ∈ O := by
    rw [hi']
    have h1 : F.dA.ρ⁻¹ * c⁻¹ * F.dA.ρ⁻¹⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hρO) c⁻¹).mp (inv_mem hcO)
    rw [inv_inv] at h1
    have := mul_mem h1 ho''
    convert this using 1
    group
  refine ⟨F.dA.ρ⁻¹ * i, Q, hKC ho.1, ho.2, ((hKiff _).1 ho.1).2, ?_, ?_, hQ.2.1, hDQ', hQ.1,
    huQ, ?_, ?_⟩
  · rw [mul_inv_cancel_left]
    exact hK₁odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard K₁ hi.1)
  · rw [mul_inv_cancel_left]
    have hinv := hi.2
    rw [huinv] at hinv
    rw [hinv]
    group
  · rw [mul_inv_cancel_left]
    exact hi.1.2
  · rw [mul_inv_cancel_left]
    set w := i ^ 3 with hw
    have hρ3D : F.dA.ρ ^ 3 ∈ Subgroup.centralizer (D : Set G) := h.ρ_eq ▸ dD.rho_cube_mem
    have hρ3E := F.rho_cube_mem_centralizer_E
    obtain ⟨o₀, ho₀⟩ : ∃ o₀, o₀ = F.dA.ρ⁻¹ * i := ⟨_, rfl⟩
    have hio : i = F.dA.ρ * o₀ := by rw [ho₀, mul_inv_cancel_left]
    rw [← ho₀] at ho
    have hwsplit : w = F.dA.ρ ^ 3 * ((F.dA.ρ⁻¹ * F.dA.ρ⁻¹ * o₀ * F.dA.ρ * F.dA.ρ) *
        (F.dA.ρ⁻¹ * o₀ * F.dA.ρ) * o₀) := by
      rw [hw, hio, pow_three]; group
    have hO1 : F.dA.ρ⁻¹ * o₀ * F.dA.ρ ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hρO) o₀).mp ho
      rwa [inv_inv] at this
    have hO2 : F.dA.ρ⁻¹ * F.dA.ρ⁻¹ * o₀ * F.dA.ρ * F.dA.ρ ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hρO) _).mp hO1
      rw [inv_inv] at this
      convert this using 1
      group
    have hprod := mul_mem (mul_mem hO2 hO1) ho
    have hwD : w ∈ Subgroup.centralizer (D : Set G) := by
      rw [hwsplit]; exact mul_mem hρ3D hprod.2
    have hwE : w ∈ Subgroup.centralizer (F.E : Set G) := by
      rw [hwsplit]; exact mul_mem hρ3E (hKC hprod.1)
    have hwodd : Odd (orderOf w) :=
      (hK₁odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard K₁ hi.1)).of_dvd_nat
        (orderOf_pow_dvd 3)
    have hwO : w ∈ O := ⟨(hKiff w).2 ⟨hwE, hwodd⟩, hwD⟩
    have hwQ : w ∈ Subgroup.normalizer (Q : Set G) := pow_mem hi.1.2 3
    rw [Subgroup.mem_centralizer_iff]
    intro q' hq'
    set z := q'⁻¹ * (w⁻¹ * q' * w) with hz
    have hzQ : z ∈ Q :=
      mul_mem (inv_mem hq') ((Subgroup.mem_normalizer_iff''.mp hwQ q').mp hq')
    have hzO : z ∈ O := by
      have h1 : q'⁻¹ * w⁻¹ * q'⁻¹⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (inv_mem (hXO (hQ.1 hq'))) w⁻¹).mp (inv_mem hwO)
      rw [inv_inv] at h1
      have := mul_mem h1 hwO
      convert this using 1
      rw [hz]; group
    have hz1 : z = 1 := by
      obtain ⟨k, hk⟩ := hQ.2.1 ⟨z, hzQ⟩
      have hk' : z ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      have hzodd : Odd (orderOf z) := hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hzO)
      have hdvd : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have hcop : Nat.Coprime (orderOf z) (2 ^ k) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_comm).mp (Nat.coprime_two_left.mpr hzodd))
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
    calc q' * w = w * (w⁻¹ * q' * w) := by group
      _ = w * (q' * z) := by rw [hz]; group
      _ = w * q' := by rw [hz1, mul_one]

end StrothFrame.IsTyped

end CFSG.CGT.Stroth77
