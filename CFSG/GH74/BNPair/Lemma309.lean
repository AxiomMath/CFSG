module

public import CFSG.GH74.BNPair.RootCalc
public import CFSG.GH74.BNPair.Assembly

public section

namespace CFSG.GH74.BNPair

universe u

open scoped Pointwise

@[expose] def stType (first : Bool) (i : ℕ) : Bool :=
  if Even i then first else !first

theorem stType_succ (first : Bool) (i : ℕ) : stType first (i + 1) = !stType first i := by
  by_cases h : Even i <;> simp [stType, h, Nat.even_add_one]

@[expose] def jIdx (n : ℕ) (first : Bool) (i : ℕ) : ℤ :=
  if stType first i then (n : ℤ) - i else (i : ℤ) + 1

@[expose] def chainElt {X : Type*} [Group X] (mm : Bool → X) (first : Bool) : ℕ → X
  | 0 => 1
  | i + 1 => mm (stType first i) * chainElt mm first i

namespace RankTwoSystem

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

@[expose] def lifts (m₁ m₂ : D.N) : Bool → X :=
  fun s => if s then (m₁ : X) else (m₂ : X)

theorem inv_lift₁ (m₁ : D.N) (hm₁ : (m₁ : D.Weyl) = D.w₁) :
    ((m₁⁻¹ : D.N) : D.Weyl) = D.w₁ := by
  rw [QuotientGroup.mk_inv, hm₁]
  exact inv_eq_of_mul_eq_one_right D.w₁_mul_self

theorem inv_lift₂ (m₂ : D.N) (hm₂ : (m₂ : D.Weyl) = D.w₂) :
    ((m₂⁻¹ : D.N) : D.Weyl) = D.w₂ := by
  rw [QuotientGroup.mk_inv, hm₂]
  exact inv_eq_of_mul_eq_one_right D.w₂_mul_self

variable (m₁ m₂ : D.N) (hm₁ : (m₁ : D.Weyl) = D.w₁) (hm₂ : (m₂ : D.Weyl) = D.w₂) (first : Bool)
include hm₁ hm₂

theorem chain_fwd : ∀ i : ℕ, i + 1 ≤ n → ∀ g ∈ D.root (jIdx n first 0),
    chainElt (D.lifts m₁ m₂) first i * g * (chainElt (D.lifts m₁ m₂) first i)⁻¹ ∈
      D.root (jIdx n first i)
  | 0, _, g, hg => by simpa [chainElt] using hg
  | i + 1, hi, g, hg => by
    have ih := chain_fwd i (by omega) g hg
    have hn := D.three_le
    have e : chainElt (D.lifts m₁ m₂) first (i + 1) * g *
        (chainElt (D.lifts m₁ m₂) first (i + 1))⁻¹ =
        D.lifts m₁ m₂ (stType first i) *
          (chainElt (D.lifts m₁ m₂) first i * g * (chainElt (D.lifts m₁ m₂) first i)⁻¹) *
          (D.lifts m₁ m₂ (stType first i))⁻¹ := by
      simp only [chainElt]
      group
    rw [e]
    cases hs : stType first i with
    | true =>
      have hj : jIdx n first i = (n : ℤ) - i := by simp [jIdx, hs]
      rw [hj] at ih
      have h1 := D.conj_mem_root₁ m₁ hm₁ (k := (n : ℤ) - i) (by omega) (by omega) ih
      have hj' : jIdx n first (i + 1) = (n : ℤ) + 2 - ((n : ℤ) - i) := by
        simp only [jIdx, stType_succ, hs]
        push_cast
        simp
        ring
      rw [hj']
      simpa [lifts] using h1
    | false =>
      have hj : jIdx n first i = (i : ℤ) + 1 := by simp [jIdx, hs]
      rw [hj] at ih
      have h1 := D.conj_mem_root₂ m₂ hm₂ (k := (i : ℤ) + 1) (by omega) (by omega) ih
      have hj' : jIdx n first (i + 1) = (n : ℤ) - ((i : ℤ) + 1) := by
        simp only [jIdx, stType_succ, hs]
        push_cast
        simp
      rw [hj']
      simpa [lifts] using h1

theorem chain_bwd : ∀ i : ℕ, i + 1 ≤ n → ∀ h ∈ D.root (jIdx n first i),
    (chainElt (D.lifts m₁ m₂) first i)⁻¹ * h * chainElt (D.lifts m₁ m₂) first i ∈
      D.root (jIdx n first 0)
  | 0, _, h, hh => by simpa [chainElt] using hh
  | i + 1, hi, h, hh => by
    have hn := D.three_le
    have e : (chainElt (D.lifts m₁ m₂) first (i + 1))⁻¹ * h *
        chainElt (D.lifts m₁ m₂) first (i + 1) =
        (chainElt (D.lifts m₁ m₂) first i)⁻¹ *
          ((D.lifts m₁ m₂ (stType first i))⁻¹ * h * D.lifts m₁ m₂ (stType first i)) *
          chainElt (D.lifts m₁ m₂) first i := by
      simp only [chainElt]
      group
    rw [e]
    refine chain_bwd i (by omega) _ ?_
    cases hs : stType first i with
    | true =>
      have hj' : jIdx n first (i + 1) = (i : ℤ) + 2 := by
        simp only [jIdx, stType_succ, hs]
        push_cast
        simp
        ring
      rw [hj'] at hh
      have h1 := D.conj_mem_root₁ (m₁⁻¹) (D.inv_lift₁ m₁ hm₁) (k := (i : ℤ) + 2)
        (by omega) (by omega) hh
      have hj : jIdx n first i = (n : ℤ) + 2 - ((i : ℤ) + 2) := by
        simp only [jIdx, hs]
        simp
      rw [hj]
      simpa [lifts] using h1
    | false =>
      have hj' : jIdx n first (i + 1) = (n : ℤ) - ((i : ℤ) + 1) := by
        simp only [jIdx, stType_succ, hs]
        push_cast
        simp
      rw [hj'] at hh
      have h1 := D.conj_mem_root₂ (m₂⁻¹) (D.inv_lift₂ m₂ hm₂) (k := (n : ℤ) - ((i : ℤ) + 1))
        (by omega) (by omega) hh
      have hj : jIdx n first i = (n : ℤ) - ((n : ℤ) - ((i : ℤ) + 1)) := by
        simp only [jIdx, hs]
        simp
      rw [hj]
      simpa [lifts] using h1

theorem chain_core {i : ℕ} (hi : i + 2 ≤ n) {g z : X} (hg : g ∈ D.root (jIdx n first 0))
    (hz : z * (chainElt (D.lifts m₁ m₂) first i)⁻¹ ∈
      pgen D.B D.N D.w₁ D.w₂ (stType first i)) : z * g * z⁻¹ ∈ D.B := by
  have hn := D.three_le
  have hx := D.chain_fwd m₁ m₂ hm₁ hm₂ first i (by omega) g hg
  have hp := (mem_parabolic_single_iff D.rank2.tits (D.rank2.gen_mem (stType first i))).1 hz
  have e : z * (chainElt (D.lifts m₁ m₂) first i)⁻¹ *
      (chainElt (D.lifts m₁ m₂) first i * g * (chainElt (D.lifts m₁ m₂) first i)⁻¹) *
      (z * (chainElt (D.lifts m₁ m₂) first i)⁻¹)⁻¹ = z * g * z⁻¹ := by group
  rw [← e]
  cases hs : stType first i with
  | true =>
    rw [hs] at hp
    have hj : jIdx n first i = (n : ℤ) - i := by simp [jIdx, hs]
    rw [hj] at hx
    exact D.root_core_w₁ m₁ hm₁ (by omega) (by omega) hp hx
  | false =>
    rw [hs] at hp
    have hj : jIdx n first i = (i : ℤ) + 1 := by simp [jIdx, hs]
    rw [hj] at hx
    exact D.root_core_w₂ m₂ hm₂ (by omega) (by omega) hp hx

theorem chain_fix {i : ℕ} (hi : i + 2 ≤ n) {g : X} (hg : g ∈ D.root (jIdx n first 0))
    {w : D.Vertex}
    (hw : D.graph.Adj (vtx D.B D.N D.w₁ D.w₂ (stType first i)
      (chainElt (D.lifts m₁ m₂) first i)) w) : D.action g w = w := by
  obtain ⟨z, hzv, hzw⟩ := hw.2
  have e1 := D.rank2.eq_vtx_not_of_adj hw hzw
  rw [D.rank2.vtype_vtx] at e1
  have hgi : g⁻¹ ∈ D.root (jIdx n first 0) := (D.root _).inv_mem hg
  have hB : z * g⁻¹ * z⁻¹ ∈ D.B :=
    D.chain_core m₁ m₂ hm₁ hm₂ first hi hgi (mem_vtx.1 hzv)
  have h2 : D.action g w = vtx D.B D.N D.w₁ D.w₂ (!stType first i) (z * g⁻¹) := by
    rw [e1]
    exact rankTwoAction_vtx g _ z
  rw [h2, e1]
  exact vtx_eq_vtx (D.rank2.B_le_pgen _ hB)

end RankTwoSystem

section PathOfFun

variable {V : Type*} {G : SimpleGraph V}

theorem isGLSPath_map_range (f : ℕ → V) :
    ∀ k : ℕ, (∀ i, i < k → G.Adj (f i) (f (i + 1))) → (∀ i, i + 2 ≤ k → f i ≠ f (i + 2)) →
      IsGLSPath G ((List.range (k + 1)).map f)
  | 0, _, _ => by simpa using IsGLSPath.singleton (G := G) (f 0)
  | k + 1, hadj, hnb => by
    have ih := isGLSPath_map_range f k (fun i hi => hadj i (by omega))
      (fun i hi => hnb i (by omega))
    have e : (List.range (k + 1 + 1)).map f = (List.range k).map f ++ [f k, f (k + 1)] := by
      simp [List.range_succ]
    rw [e, isGLSPath_concat]
    refine ⟨by simpa [List.range_succ] using ih, hadj k (by omega), ?_⟩
    intro w hw hwx
    cases k with
    | zero => simp at hw
    | succ k =>
      have : ((List.range (k + 1)).map f).getLast? = some (f k) := by
        simp [List.range_succ]
      rw [this] at hw
      have hw' : f k = w := Option.some.inj hw
      exact hnb k (by omega) (by rw [hw', hwx])

theorem mem_interior_map_range (f : ℕ → V) (k : ℕ) {v : V}
    (hv : v ∈ interiorVertices ((List.range (k + 2)).map f)) : ∃ i, i + 1 ≤ k ∧ v = f (i + 1) := by
  unfold interiorVertices at hv
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hv
  have ht' : t < k := by simpa using ht
  refine ⟨t, by omega, ?_⟩
  simp [List.getElem_dropLast, List.getElem_tail]

end PathOfFun

namespace RankTwoSystem

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)
variable (m₁ m₂ : D.N) (hm₁ : (m₁ : D.Weyl) = D.w₁) (hm₂ : (m₂ : D.Weyl) = D.w₂) (first : Bool)

@[expose] def liftsN : Bool → D.N := fun s => if s then m₁ else m₂

theorem lifts_eq (s : Bool) : D.lifts m₁ m₂ s = ((D.liftsN m₁ m₂ s : D.N) : X) := by
  cases s <;> rfl

include hm₁ hm₂ in
theorem liftsN_mk (s : Bool) : ((D.liftsN m₁ m₂ s : D.N) : D.Weyl) = gen D.w₁ D.w₂ s := by
  cases s
  · exact hm₂
  · exact hm₁

include hm₁ hm₂ in
theorem lifts_mem_dc (s : Bool) : D.lifts m₁ m₂ s ∈ dc D.B D.N (gen D.w₁ D.w₂ s) := by
  rw [lifts_eq, ← D.liftsN_mk m₁ m₂ hm₁ hm₂ s]
  exact coe_mem_dc _

include hm₁ hm₂ in
theorem lifts_mul_mem_dc (s' s : Bool) :
    D.lifts m₁ m₂ s' * D.lifts m₁ m₂ s ∈
      dc D.B D.N (gen D.w₁ D.w₂ s' * gen D.w₁ D.w₂ s) := by
  have := coe_mem_dc (B := D.B) (N := D.N) (D.liftsN m₁ m₂ s' * D.liftsN m₁ m₂ s)
  rw [QuotientGroup.mk_mul, D.liftsN_mk m₁ m₂ hm₁ hm₂, D.liftsN_mk m₁ m₂ hm₁ hm₂] at this
  simpa [lifts_eq] using this

@[expose] def vv (k : ℕ) : D.Vertex :=
  if k = 0 then vtx D.B D.N D.w₁ D.w₂ (!first) 1
  else vtx D.B D.N D.w₁ D.w₂ (stType first (k - 1)) (chainElt (D.lifts m₁ m₂) first (k - 1))

theorem vv_zero : D.vv m₁ m₂ first 0 = vtx D.B D.N D.w₁ D.w₂ (!first) 1 := by simp [vv]

theorem vv_succ (i : ℕ) : D.vv m₁ m₂ first (i + 1) =
    vtx D.B D.N D.w₁ D.w₂ (stType first i) (chainElt (D.lifts m₁ m₂) first i) := by simp [vv]

theorem vtype_vv_succ (i : ℕ) :
    vtype D.B D.N D.w₁ D.w₂ (D.vv m₁ m₂ first (i + 1)) = stType first i := by
  rw [vv_succ, D.rank2.vtype_vtx]

theorem vtype_vv_zero :
    vtype D.B D.N D.w₁ D.w₂ (D.vv m₁ m₂ first 0) = !first := by
  rw [vv_zero, D.rank2.vtype_vtx]

include hm₁ hm₂ in
theorem chamber_mem_vv (i : ℕ) : chainElt (D.lifts m₁ m₂) first i ∈ (D.vv m₁ m₂ first i : Set X) := by
  cases i with
  | zero =>
    rw [vv_zero]
    simpa [chainElt] using (mem_self_vtx : (1 : X) ∈ (vtx D.B D.N D.w₁ D.w₂ (!first) 1 : Set X))
  | succ i =>
    rw [vv_succ]
    refine mem_vtx.2 ?_
    have : chainElt (D.lifts m₁ m₂) first (i + 1) * (chainElt (D.lifts m₁ m₂) first i)⁻¹ =
        D.lifts m₁ m₂ (stType first i) := by simp [chainElt]
    rw [this]
    exact (mem_parabolic_single_iff D.rank2.tits (D.rank2.gen_mem _)).2
      (Or.inr (D.lifts_mem_dc m₁ m₂ hm₁ hm₂ _))

theorem chamber_mem_vv_succ (i : ℕ) :
    chainElt (D.lifts m₁ m₂) first i ∈ (D.vv m₁ m₂ first (i + 1) : Set X) := by
  rw [vv_succ]
  exact mem_self_vtx

include hm₁ hm₂ in
theorem vv_adj (i : ℕ) : D.graph.Adj (D.vv m₁ m₂ first i) (D.vv m₁ m₂ first (i + 1)) := by
  refine ⟨?_, chainElt (D.lifts m₁ m₂) first i,
    Set.mem_inter (D.chamber_mem_vv m₁ m₂ hm₁ hm₂ first i) (D.chamber_mem_vv_succ m₁ m₂ first i)⟩
  intro h
  have h1 := congrArg (vtype D.B D.N D.w₁ D.w₂) h
  cases i with
  | zero =>
    rw [vtype_vv_zero, vtype_vv_succ] at h1
    revert h1
    cases first <;> simp [stType]
  | succ i =>
    rw [vtype_vv_succ, vtype_vv_succ, stType_succ] at h1
    revert h1
    cases stType first i <;> simp

include hm₁ hm₂ in
theorem lifts_prod_not_mem (s : Bool) :
    D.lifts m₁ m₂ (!s) * D.lifts m₁ m₂ s ∉ pgen D.B D.N D.w₁ D.w₂ s := by
  intro h
  have hd := D.lifts_mul_mem_dc m₁ m₂ hm₁ hm₂ (!s) s
  rcases (mem_parabolic_single_iff D.rank2.tits (D.rank2.gen_mem s)).1 h with hB | hd'
  · have := D.rank2.tits.dc_injective (dc_eq_of_mem hd (mem_dc_one.2 hB))
    have h2 : gen D.w₁ D.w₂ (!s) = gen D.w₁ D.w₂ s := by
      have e1 := D.rank2.tits.mul_self_gen (D.rank2.gen_mem s)
      calc gen D.w₁ D.w₂ (!s) = gen D.w₁ D.w₂ (!s) * (gen D.w₁ D.w₂ s * gen D.w₁ D.w₂ s) := by
            rw [e1, mul_one]
        _ = (gen D.w₁ D.w₂ (!s) * gen D.w₁ D.w₂ s) * gen D.w₁ D.w₂ s := by rw [mul_assoc]
        _ = gen D.w₁ D.w₂ s := by rw [this, one_mul]
    exact D.rank2.gen_ne s h2.symm
  · have := D.rank2.tits.dc_injective (dc_eq_of_mem hd hd')
    have h2 : gen D.w₁ D.w₂ (!s) = 1 := by
      have := mul_right_cancel (a := gen D.w₁ D.w₂ (!s)) (b := gen D.w₁ D.w₂ s)
        (c := 1) (by rw [one_mul]; exact this)
      exact this
    exact D.rank2.tits.gen_ne_one (D.rank2.gen_mem _) h2

include hm₁ hm₂ in
theorem vv_ne (i : ℕ) : D.vv m₁ m₂ first i ≠ D.vv m₁ m₂ first (i + 2) := by
  intro h
  cases i with
  | zero =>
    have hc : chainElt (D.lifts m₁ m₂) first 1 ∈ (D.vv m₁ m₂ first 2 : Set X) :=
      D.chamber_mem_vv_succ m₁ m₂ first 1
    rw [← h, vv_zero] at hc
    have hpg := mem_vtx.1 hc
    have e : chainElt (D.lifts m₁ m₂) first 1 * (1 : X)⁻¹ = D.lifts m₁ m₂ first := by
      simp [chainElt, stType]
    rw [e] at hpg
    have hd := D.lifts_mem_dc m₁ m₂ hm₁ hm₂ first
    rcases (mem_parabolic_single_iff D.rank2.tits (D.rank2.gen_mem (!first))).1 hpg with hB | hd'
    · exact D.rank2.not_mem_B_of_mem_dc (D.rank2.gen_mem first) hd hB
    · exact D.rank2.gen_ne first (D.rank2.tits.dc_injective (dc_eq_of_mem hd hd'))
  | succ i =>
    have hc : chainElt (D.lifts m₁ m₂) first (i + 2) ∈ (D.vv m₁ m₂ first (i + 1 + 2) : Set X) :=
      D.chamber_mem_vv_succ m₁ m₂ first (i + 2)
    rw [← h, vv_succ] at hc
    have hpg := mem_vtx.1 hc
    have e : chainElt (D.lifts m₁ m₂) first (i + 2) * (chainElt (D.lifts m₁ m₂) first i)⁻¹ =
        D.lifts m₁ m₂ (!stType first i) * D.lifts m₁ m₂ (stType first i) := by
      simp only [chainElt, stType_succ]
      group
    rw [e] at hpg
    exact D.lifts_prod_not_mem m₁ m₂ hm₁ hm₂ (stType first i) hpg

@[expose] def basePath : List D.Vertex :=
  (List.range (n + 1)).map (D.vv m₁ m₂ first)

include hm₁ hm₂ in
theorem basePath_isGLSPath : IsGLSPath D.graph (D.basePath m₁ m₂ first) :=
  isGLSPath_map_range _ n (fun i _ => D.vv_adj m₁ m₂ hm₁ hm₂ first i)
    (fun i _ => D.vv_ne m₁ m₂ hm₁ hm₂ first i)

theorem basePath_length : (D.basePath m₁ m₂ first).length = n + 1 := by
  simp [basePath]

theorem basePath_head : (D.basePath m₁ m₂ first).head? = some (D.vv m₁ m₂ first 0) := by
  simp [basePath, List.range_succ_eq_map]

include hm₁ hm₂ in
theorem basePath_fix {g : X} (hg : g ∈ D.root (jIdx n first 0)) :
    ∀ v ∈ interiorVertices (D.basePath m₁ m₂ first), ∀ w, D.graph.Adj v w → D.action g w = w := by
  intro v hv w hw
  have hn := D.three_le
  have hv' : v ∈ interiorVertices ((List.range ((n - 1) + 2)).map (D.vv m₁ m₂ first)) := by
    rw [show (n - 1) + 2 = n + 1 by omega]
    exact hv
  obtain ⟨i, hi, rfl⟩ := mem_interior_map_range _ _ hv'
  rw [vv_succ] at hw
  exact D.chain_fix m₁ m₂ hm₁ hm₂ first (by omega) hg hw

theorem conj_cartan_mem (m : D.N) {h : X} (hh : h ∈ D.B ⊓ D.N) :
    (m : X) * h * (m : X)⁻¹ ∈ D.B ⊓ D.N := by
  have hh' : (⟨h, hh.2⟩ : D.N) ∈ cartan D.B D.N := by
    rw [cartan, Subgroup.mem_subgroupOf]
    exact hh
  have := (inferInstance : (cartan D.B D.N).Normal).conj_mem _ hh' m
  rw [cartan, Subgroup.mem_subgroupOf] at this
  simpa using this

include hm₁ in
theorem dc_panel_w₁ {p : X} (hp : p ∈ dc D.B D.N D.w₁) :
    ∃ b ∈ D.B, ∃ x ∈ D.root 1, p = b * (m₁ : X) * x := by
  have hn := D.three_le
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_dc_of_lift hm₁).1 hp
  obtain ⟨V, hVc, -, hVn, -⟩ := D.roots.subgroup 2 (n : ℤ) (by norm_num) (by omega) le_rfl
  have hb₂' : b₂ ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb₂
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hb₂'
  have hu' : u ∈ chainProd D.root (intList 1 n) := D.roots.carrier_eq ▸ hu
  rw [intList_cons (by omega : (1 : ℤ) ≤ n), show (1 : ℤ) + 1 = 2 by norm_num,
    chainProd_cons] at hu'
  obtain ⟨x₁, hx₁, v₀, hv₀, rfl⟩ := Set.mem_mul.1 hu'
  have hv₀V : v₀ ∈ V := by
    rw [← SetLike.mem_coe, hVc]
    exact hv₀
  have hv' : x₁ * v₀ * x₁⁻¹ ∈ V := hVn (by norm_num) x₁ (by simpa using hx₁) v₀ hv₀V
  have hc1 : (m₁ : X) * h * (m₁ : X)⁻¹ ∈ D.B := (D.conj_cartan_mem m₁ hh).1
  have hc2 : (m₁ : X) * (x₁ * v₀ * x₁⁻¹) * (m₁ : X)⁻¹ ∈ D.B := by
    refine chainProd_conj_mem D.root D.B (m₁ : X) (intList 2 n) (fun k hk y' hy' => ?_) _
      (by rw [← hVc]; exact hv')
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    exact D.root_le_B (by omega) (by omega) (D.conj_mem_root₁ m₁ hm₁ hk1 hk2 hy')
  refine ⟨b₁ * ((m₁ : X) * h * (m₁ : X)⁻¹) * ((m₁ : X) * (x₁ * v₀ * x₁⁻¹) * (m₁ : X)⁻¹),
    D.B.mul_mem (D.B.mul_mem hb₁ hc1) hc2, x₁, by simpa using hx₁, ?_⟩
  group

include hm₂ in
theorem dc_panel_w₂ {p : X} (hp : p ∈ dc D.B D.N D.w₂) :
    ∃ b ∈ D.B, ∃ x ∈ D.root n, p = b * (m₂ : X) * x := by
  have hn := D.three_le
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_dc_of_lift hm₂).1 hp
  obtain ⟨V, hVc, -, -, hVn⟩ := D.roots.subgroup 1 ((n : ℤ) - 1) le_rfl (by omega) (by omega)
  have hb₂' : b₂ ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb₂
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hb₂'
  have hu' : u ∈ chainProd D.root (intList 1 n) := D.roots.carrier_eq ▸ hu
  rw [intList_snoc (by omega : (1 : ℤ) ≤ n), chainProd_append, chainProd_singleton] at hu'
  obtain ⟨v₀, hv₀, xn, hxn, rfl⟩ := Set.mem_mul.1 hu'
  have hv₀V : v₀ ∈ V := by
    rw [← SetLike.mem_coe, hVc]
    exact hv₀
  have hc1 : (m₂ : X) * h * (m₂ : X)⁻¹ ∈ D.B := (D.conj_cartan_mem m₂ hh).1
  have hc2 : (m₂ : X) * v₀ * (m₂ : X)⁻¹ ∈ D.B := by
    refine chainProd_conj_mem D.root D.B (m₂ : X) (intList 1 ((n : ℤ) - 1))
      (fun k hk y' hy' => ?_) _ hv₀
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    exact D.root_le_B (by omega) (by omega) (D.conj_mem_root₂ m₂ hm₂ hk1 hk2 hy')
  refine ⟨b₁ * ((m₂ : X) * h * (m₂ : X)⁻¹) * ((m₂ : X) * v₀ * (m₂ : X)⁻¹),
    D.B.mul_mem (D.B.mul_mem hb₁ hc1) hc2, xn, by simpa using hxn, ?_⟩
  group

include hm₁ hm₂ in
theorem last_panel_trans {z z' : X}
    (hz : z * (chainElt (D.lifts m₁ m₂) first (n - 1))⁻¹ ∈
      dc D.B D.N (gen D.w₁ D.w₂ (stType first (n - 1))))
    (hz' : z' * (chainElt (D.lifts m₁ m₂) first (n - 1))⁻¹ ∈
      dc D.B D.N (gen D.w₁ D.w₂ (stType first (n - 1)))) :
    ∃ g ∈ D.root (jIdx n first 0), z * g⁻¹ * z'⁻¹ ∈ D.B := by
  have hn := D.three_le
  have hroot : ∀ h ∈ D.root (jIdx n first (n - 1)),
      (chainElt (D.lifts m₁ m₂) first (n - 1))⁻¹ * h * chainElt (D.lifts m₁ m₂) first (n - 1) ∈
        D.root (jIdx n first 0) :=
    fun h hh => D.chain_bwd m₁ m₂ hm₁ hm₂ first (n - 1) (by omega) h hh
  generalize hc : chainElt (D.lifts m₁ m₂) first (n - 1) = c at hz hz' hroot
  cases hτ : stType first (n - 1) with
  | true =>
    rw [hτ] at hz hz'
    obtain ⟨b, hb, x, hx, hpx⟩ := D.dc_panel_w₁ m₁ hm₁ hz
    obtain ⟨b', hb', x', hx', hpx'⟩ := D.dc_panel_w₁ m₁ hm₁ hz'
    have hj : jIdx n first (n - 1) = 1 := by
      simp only [jIdx, hτ, ite_true]
      omega
    have hh' : x'⁻¹ * x ∈ D.root (jIdx n first (n - 1)) := by
      rw [hj]
      exact (D.root 1).mul_mem ((D.root 1).inv_mem hx') hx
    refine ⟨c⁻¹ * (x'⁻¹ * x) * c, hroot _ hh', ?_⟩
    have hz1 : z = b * (m₁ : X) * x * c := by
      calc z = z * c⁻¹ * c := by group
        _ = b * (m₁ : X) * x * c := by rw [hpx]
    have hz1' : z' = b' * (m₁ : X) * x' * c := by
      calc z' = z' * c⁻¹ * c := by group
        _ = b' * (m₁ : X) * x' * c := by rw [hpx']
    have e : z * (c⁻¹ * (x'⁻¹ * x) * c)⁻¹ * z'⁻¹ = b * b'⁻¹ := by
      rw [hz1, hz1']
      group
    rw [e]
    exact D.B.mul_mem hb (D.B.inv_mem hb')
  | false =>
    rw [hτ] at hz hz'
    obtain ⟨b, hb, x, hx, hpx⟩ := D.dc_panel_w₂ m₂ hm₂ hz
    obtain ⟨b', hb', x', hx', hpx'⟩ := D.dc_panel_w₂ m₂ hm₂ hz'
    have hj : jIdx n first (n - 1) = n := by
      simp only [jIdx, hτ]
      simp
      omega
    have hh' : x'⁻¹ * x ∈ D.root (jIdx n first (n - 1)) := by
      rw [hj]
      exact (D.root n).mul_mem ((D.root n).inv_mem hx') hx
    refine ⟨c⁻¹ * (x'⁻¹ * x) * c, hroot _ hh', ?_⟩
    have hz1 : z = b * (m₂ : X) * x * c := by
      calc z = z * c⁻¹ * c := by group
        _ = b * (m₂ : X) * x * c := by rw [hpx]
    have hz1' : z' = b' * (m₂ : X) * x' * c := by
      calc z' = z' * c⁻¹ * c := by group
        _ = b' * (m₂ : X) * x' * c := by rw [hpx']
    have e : z * (c⁻¹ * (x'⁻¹ * x) * c)⁻¹ * z'⁻¹ = b * b'⁻¹ := by
      rw [hz1, hz1']
      group
    rw [e]
    exact D.B.mul_mem hb (D.B.inv_mem hb')

omit hm₁ hm₂ in
theorem ext_facts {y : D.Vertex}
    (hl : IsGLSPath D.graph (D.basePath m₁ m₂ first ++ [y])) :
    D.graph.Adj (D.vv m₁ m₂ first n) y ∧ D.vv m₁ m₂ first (n - 1) ≠ y := by
  have hn := D.three_le
  have hhead : (D.basePath m₁ m₂ first ++ [y]).head? = some (D.vv m₁ m₂ first 0) := by
    rw [List.head?_append, basePath_head]
    rfl
  have hlast : (D.basePath m₁ m₂ first ++ [y]).getLast? = some y := by simp
  obtain ⟨f, k, hk, hf0, hfk, hadj, hnb, hfl⟩ := hl.exists_fun hhead hlast
  have hk' : k = n + 1 := by
    simp only [List.length_append, basePath_length, List.length_singleton] at hk
    omega
  have hfv : ∀ i, i ≤ n → f i = D.vv m₁ m₂ first i := by
    intro i hi
    have h1 := hfl i (by omega)
    have hi' : i < n + 1 := by omega
    have h2 : (D.basePath m₁ m₂ first ++ [y])[i]? = some (D.vv m₁ m₂ first i) := by
      rw [List.getElem?_append_left (by simp [basePath_length]; omega)]
      simp [basePath, hi']
    rw [h1] at h2
    exact Option.some.inj h2
  subst hk'
  refine ⟨?_, ?_⟩
  · have := hadj n (by omega)
    rwa [hfv n le_rfl, hfk] at this
  · have := hnb (n - 1) (by omega)
    rw [hfv (n - 1) (by omega), show n - 1 + 2 = n + 1 by omega, hfk] at this
    exact this

include hm₁ hm₂ in
theorem last_chamber_not_B {y : D.Vertex} (hne : D.vv m₁ m₂ first (n - 1) ≠ y)
    {z : X} (hzy : z ∈ (y : Set X)) (hadj : D.graph.Adj (D.vv m₁ m₂ first n) y) :
    z * (chainElt (D.lifts m₁ m₂) first (n - 1))⁻¹ ∉ D.B := by
  have hn := D.three_le
  intro hB
  have hnn : n - 1 + 1 = n := by omega
  have hvv : D.vv m₁ m₂ first n = vtx D.B D.N D.w₁ D.w₂ (stType first (n - 1))
      (chainElt (D.lifts m₁ m₂) first (n - 1)) := by
    have := D.vv_succ m₁ m₂ first (n - 1)
    rwa [hnn] at this
  have e1 := D.rank2.eq_vtx_not_of_adj hadj hzy
  rw [hvv, D.rank2.vtype_vtx] at e1
  have e2 : y = vtx D.B D.N D.w₁ D.w₂ (!stType first (n - 1)) (chainElt (D.lifts m₁ m₂) first (n - 1)) := by
    rw [e1]
    exact vtx_eq_vtx (D.rank2.B_le_pgen _ hB)
  have hmem := D.chamber_mem_vv m₁ m₂ hm₁ hm₂ first (n - 1)
  have e3 := D.rank2.eq_vtx_of_mem hmem
  have hn2 : n - 2 + 1 = n - 1 := by omega
  have hty : vtype D.B D.N D.w₁ D.w₂ (D.vv m₁ m₂ first (n - 1)) = !stType first (n - 1) := by
    have h1 := D.vtype_vv_succ m₁ m₂ first (n - 2)
    rw [hn2] at h1
    rw [h1]
    have h2 := stType_succ first (n - 2)
    rw [hn2] at h2
    rw [h2]
    simp
  rw [hty] at e3
  exact hne (e3.trans e2.symm)

include hm₁ hm₂ in
theorem basePath_trans : ∀ l l' : List D.Vertex, IsGLSPath D.graph l → IsGLSPath D.graph l' →
    l.length = n + 2 → l'.length = n + 2 → D.basePath m₁ m₂ first <+: l →
      D.basePath m₁ m₂ first <+: l' →
        ∃ x ∈ D.root (jIdx n first 0), l.map (D.action x) = l' := by
  intro l l' hl hl' hlen hlen' hpre hpre'
  have hn := D.three_le
  obtain ⟨t, rfl⟩ := hpre
  obtain ⟨t', rfl⟩ := hpre'
  have ht : t.length = 1 := by
    simp only [List.length_append, basePath_length] at hlen
    omega
  have ht' : t'.length = 1 := by
    simp only [List.length_append, basePath_length] at hlen'
    omega
  obtain ⟨y, rfl⟩ := List.length_eq_one_iff.1 ht
  obtain ⟨y', rfl⟩ := List.length_eq_one_iff.1 ht'
  obtain ⟨hAdj, hne⟩ := D.ext_facts m₁ m₂ first hl
  obtain ⟨hAdj', hne'⟩ := D.ext_facts m₁ m₂ first hl'
  obtain ⟨z, hzv, hzy⟩ := hAdj.2
  obtain ⟨z', hzv', hzy'⟩ := hAdj'.2
  have hnn : n - 1 + 1 = n := by omega
  have hvv : D.vv m₁ m₂ first n = vtx D.B D.N D.w₁ D.w₂ (stType first (n - 1))
      (chainElt (D.lifts m₁ m₂) first (n - 1)) := by
    have := D.vv_succ m₁ m₂ first (n - 1)
    rwa [hnn] at this
  have hzB := D.last_chamber_not_B m₁ m₂ hm₁ hm₂ first hne hzy hAdj
  have hzB' := D.last_chamber_not_B m₁ m₂ hm₁ hm₂ first hne' hzy' hAdj'
  have hzp : z * (chainElt (D.lifts m₁ m₂) first (n - 1))⁻¹ ∈
      pgen D.B D.N D.w₁ D.w₂ (stType first (n - 1)) := by
    have := hzv
    rw [hvv] at this
    exact mem_vtx.1 this
  have hzp' : z' * (chainElt (D.lifts m₁ m₂) first (n - 1))⁻¹ ∈
      pgen D.B D.N D.w₁ D.w₂ (stType first (n - 1)) := by
    have := hzv'
    rw [hvv] at this
    exact mem_vtx.1 this
  have hz1 := ((mem_parabolic_single_iff D.rank2.tits
    (D.rank2.gen_mem (stType first (n - 1)))).1 hzp).resolve_left hzB
  have hz1' := ((mem_parabolic_single_iff D.rank2.tits
    (D.rank2.gen_mem (stType first (n - 1)))).1 hzp').resolve_left hzB'
  obtain ⟨g, hg, hgB⟩ := D.last_panel_trans m₁ m₂ hm₁ hm₂ first hz1 hz1'
  refine ⟨g, hg, ?_⟩
  have hmem : D.action g ∈ pathFixer D.graph (D.basePath m₁ m₂ first) :=
    mem_pathFixer_iff.2 ⟨D.action_mem_graphAut g, D.basePath_fix m₁ m₂ hm₁ hm₂ first hg⟩
  have hfix := pathFixer_fixes (D.basePath_isGLSPath m₁ m₂ hm₁ hm₂ first) hn
    (D.basePath_length m₁ m₂ first) hmem
  have e1 := D.rank2.eq_vtx_not_of_adj hAdj hzy
  rw [hvv, D.rank2.vtype_vtx] at e1
  have e1' := D.rank2.eq_vtx_not_of_adj hAdj' hzy'
  rw [hvv, D.rank2.vtype_vtx] at e1'
  have hy : D.action g y = y' := by
    have h2 : D.action g y = vtx D.B D.N D.w₁ D.w₂ (!stType first (n - 1)) (z * g⁻¹) := by
      rw [e1]
      exact rankTwoAction_vtx g _ z
    rw [h2, e1']
    exact vtx_eq_vtx (D.rank2.B_le_pgen _ hgB)
  have hmapπ : (D.basePath m₁ m₂ first).map (D.action g) = D.basePath m₁ m₂ first := by
    conv_rhs => rw [← List.map_id (D.basePath m₁ m₂ first)]
    exact List.map_congr_left hfix
  rw [List.map_append, hmapπ]
  simp [hy]

end RankTwoSystem

theorem lemma30_9 : Lemma30_9.{u} := by
  intro X _ n D
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective D.w₁
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective D.w₂
  have hn := D.three_le
  have h2 : jIdx n true 0 = (n : ℤ) := by simp [jIdx, stType]
  have h1 : jIdx n false 0 = 1 := by simp [jIdx, stType]
  refine ⟨D.basePath m₁ m₂ false, D.basePath m₁ m₂ true,
    D.basePath_isGLSPath m₁ m₂ hm₁ hm₂ false, D.basePath_isGLSPath m₁ m₂ hm₁ hm₂ true,
    D.basePath_length m₁ m₂ false, D.basePath_length m₁ m₂ true,
    ⟨_, D.basePath_head m₁ m₂ false, (D.isTypeOne_iff _).2 (by rw [D.vtype_vv_zero]; rfl)⟩,
    ⟨_, D.basePath_head m₁ m₂ true, (D.isTypeTwo_iff _).2 (by rw [D.vtype_vv_zero]; rfl)⟩,
    ?_, ?_, ?_, ?_⟩
  · intro x hx v hv w hw
    exact D.basePath_fix m₁ m₂ hm₁ hm₂ true (by rw [h2]; exact hx) v hv w hw
  · intro l l' hl hl' hlen hlen' hp hp'
    have := D.basePath_trans m₁ m₂ hm₁ hm₂ true l l' hl hl' hlen hlen' hp hp'
    rwa [h2] at this
  · intro x hx v hv w hw
    exact D.basePath_fix m₁ m₂ hm₁ hm₂ false (by rw [h1]; exact hx) v hv w hw
  · intro l l' hl hl' hlen hlen' hp hp'
    have := D.basePath_trans m₁ m₂ hm₁ hm₂ false l l' hl hl' hlen hlen' hp hp'
    rwa [h1] at this

theorem theorem30_4_of_coordIso (hc : CoordIso.{u}) : Theorem30_4.{u} :=
  theorem30_4_of_lemma30_9_of_coordIso lemma30_9 hc

end CFSG.GH74.BNPair
