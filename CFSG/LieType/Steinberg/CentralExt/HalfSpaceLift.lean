module

public import CFSG.LieType.Steinberg.CentralExt.RootLift
public import CFSG.LieType.Steinberg.PartBHalfSpace
public import CFSG.LieType.Steinberg.RankTwo.ReparamRelations
public import CFSG.LieType.Steinberg.RankTwo.Statement
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Steinberg.CentralExt.RankOne
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.HalfSpaceLift

open CFSG.LieType.Steinberg CFSG.LieType.Universal

section Generic

variable {ι k G : Type*} [Field k] [Group G]

theorem mem_chevRoot_iff {xh : (ι → ℤ) → k → G} {γ : ι → ℤ}
    (hadd : ∀ c d, xh γ (c + d) = xh γ c * xh γ d) {g : G} :
    g ∈ chevRoot xh γ ↔ ∃ c, xh γ c = g := by
  have h0 : xh γ 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hneg : ∀ c, xh γ (-c) = (xh γ c)⁻¹ := fun c =>
    eq_inv_of_mul_eq_one_left (by rw [← hadd, neg_add_cancel, h0])
  refine ⟨fun hg => ?_, fun ⟨c, hc⟩ => hc ▸ xh_mem_chevRoot γ c⟩
  induction hg using Subgroup.closure_induction with
  | mem _ h => exact h
  | one => exact ⟨0, h0⟩
  | mul _ _ _ _ h1 h2 =>
    obtain ⟨c, rfl⟩ := h1
    obtain ⟨d, rfl⟩ := h2
    exact ⟨c + d, hadd c d⟩
  | inv _ _ h =>
    obtain ⟨c, rfl⟩ := h
    exact ⟨-c, hneg c⟩

omit [Field k] in
theorem iSup_list_induction {xh : (ι → ℤ) → k → G} {L : List (ι → ℤ)} {P : G → Prop}
    (hgen : ∀ v ∈ L, ∀ c, P (xh v c)) (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hinv : ∀ a, P a → P a⁻¹) {g : G} (hg : g ∈ ⨆ v ∈ L, chevRoot xh v) : P g := by
  have he : (⨆ v ∈ L, chevRoot xh v) = Subgroup.closure (⋃ v ∈ L, Set.range (xh v)) := by
    simp only [chevRoot, Subgroup.closure_iUnion]
  rw [he] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_iUnion, Set.mem_range] at hg
    obtain ⟨v, hv, c, rfl⟩ := hg
    exact hgen v hv c
  | one => exact h1
  | mul _ _ _ _ ha hb => exact hmul _ _ ha hb
  | inv _ _ ha => exact hinv _ ha

theorem iSup_cons_le' {A : (ι → ℤ) → Subgroup G} {h : (ι → ℤ) → ℤ} {a : ι → ℤ}
    {L : List (ι → ℤ)} {m : ℤ} (ha : h a ≤ m) :
    ⨆ c ∈ a :: L, ⨆ (_ : m < h c), A c ≤ ⨆ c ∈ L, ⨆ (_ : m < h c), A c := by
  rw [iSup_mem_cons]
  exact sup_le (iSup_le fun hlt => absurd hlt (not_lt.2 ha)) le_rfl

theorem prodInjectiveFor_tail {A : (ι → ℤ) → Subgroup G} {a : ι → ℤ} {L : List (ι → ℤ)}
    (haL : a ∉ L) (h : ProdInjectiveFor A (a :: L)) : ProdInjectiveFor A L := by
  classical
  intro F F' hF hF' hFF' v hv
  have hupd : ∀ (F : (ι → ℤ) → G), ∀ w ∈ L, Function.update F a 1 w = F w := fun F w hw =>
    Function.update_of_ne (by rintro rfl; exact haL hw) _ _
  have e := h (Function.update F a 1) (Function.update F' a 1)
    (fun w hw => by
      rcases List.mem_cons.1 hw with rfl | hw
      · simp
      · rw [hupd F w hw]
        exact hF w hw)
    (fun w hw => by
      rcases List.mem_cons.1 hw with rfl | hw
      · simp
      · rw [hupd F' w hw]
        exact hF' w hw)
    (by
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Function.update_self,
        Function.update_self, List.map_congr_left (hupd F), List.map_congr_left (hupd F'), hFF'])
    v (List.mem_cons_of_mem a hv)
  rwa [hupd F v hv, hupd F' v hv] at e

end Generic

section Step

variable {ι k E K : Type*} [Field k] [Group E] [Group K] {π : E →* K}
  (hcen : π.ker ≤ Subgroup.center E) {x : (ι → ℤ) → k → K} {X : (ι → ℤ) → k → E}
  {τ : Type*} {tor : τ → E} {χ : τ → (ι → ℤ) → k}
include hcen

theorem injOn_cons {a : ι → ℤ} {L : List (ι → ℤ)} (haL : a ∉ L)
    (hXadd : ∀ v ∈ a :: L, ∀ c d, X v (c + d) = X v c * X v d)
    (hxadd : ∀ v ∈ a :: L, ∀ c d, x v (c + d) = x v c * x v d)
    (hXker : ∀ c, x a c = 1 → X a c = 1) (hπX : ∀ v ∈ a :: L, ∀ c, π (X v c) = x v c)
    (hKc : ∀ b ∈ L, ∀ s t, ⁅x a s, x b t⁆ ∈ ⨆ c ∈ L, chevRoot x c)
    (hcoll : ∀ u ∈ ⨆ v ∈ L, chevRoot x v,
      ∃ F : (ι → ℤ) → K, (∀ v ∈ L, F v ∈ chevRoot x v) ∧ u = (L.map F).prod)
    (hprod : ProdInjectiveFor (chevRoot x) (a :: L))
    (hT : ∀ j, ∀ v ∈ a :: L, ∀ c, tor j * X v c * (tor j)⁻¹ = X v (χ j v * c))
    (hsep : ∀ b ∈ L, (∃ j, χ j a = 1 ∧ χ j b ≠ 1) ∨
      ∀ t c, X a t * X b c * (X a t)⁻¹ ∈ ⨆ v ∈ L, chevRoot X v)
    (IH : Set.InjOn π ((⨆ v ∈ L, chevRoot X v : Subgroup E) : Set E)) :
    Set.InjOn π ((⨆ v ∈ a :: L, chevRoot X v : Subgroup E) : Set E) := by
  classical
  have ha : a ∈ a :: L := List.mem_cons_self
  have hL : ∀ v ∈ L, v ∈ a :: L := fun v hv => List.mem_cons_of_mem a hv
  set Ũ : Subgroup E := ⨆ v ∈ L, chevRoot X v with hŨ
  set U : Subgroup K := ⨆ v ∈ L, chevRoot x v with hU
  have hXmem : ∀ v ∈ L, ∀ c, X v c ∈ Ũ := fun v hv c =>
    (le_iSup₂ (f := fun v (_ : v ∈ L) => chevRoot X v) v hv) (xh_mem_chevRoot v c)
  have hxmem : ∀ v ∈ L, ∀ c, x v c ∈ U := fun v hv c =>
    (le_iSup₂ (f := fun v (_ : v ∈ L) => chevRoot x v) v hv) (xh_mem_chevRoot v c)
  have hmap : Ũ.map π = U := by
    rw [hŨ, hU, Subgroup.map_iSup]
    refine iSup_congr fun v => ?_
    rw [Subgroup.map_iSup]
    refine iSup_congr fun hv => ?_
    rw [chevRoot, chevRoot, MonoidHom.map_closure, ← Set.range_comp,
      show (⇑π ∘ X v) = x v from funext fun c => hπX v (hL v hv) c]
  have hπŨ : ∀ g ∈ Ũ, π g ∈ U := fun g hg => hmap ▸ Subgroup.mem_map_of_mem π hg
  have hsurj : ∀ u ∈ U, ∃ g ∈ Ũ, π g = u := fun u hu => by
    rw [← hmap] at hu
    obtain ⟨g, hg, rfl⟩ := hu
    exact ⟨g, hg, rfl⟩
  let σ : K → E := fun u => if hu : u ∈ U then (hsurj u hu).choose else 1
  have hσmem : ∀ u ∈ U, σ u ∈ Ũ := fun u hu => by
    simp only [σ, hu, ↓reduceDIte]
    exact (hsurj u hu).choose_spec.1
  have hσπ : ∀ u ∈ U, π (σ u) = u := fun u hu => by
    simp only [σ, hu, ↓reduceDIte]
    exact (hsurj u hu).choose_spec.2
  have hσ_of : ∀ g ∈ Ũ, σ (π g) = g := fun g hg =>
    IH (hσmem _ (hπŨ g hg)) hg (hσπ _ (hπŨ g hg))
  have hσmul : ∀ u ∈ U, ∀ u' ∈ U, σ (u * u') = σ u * σ u' := fun u hu u' hu' => by
    refine IH (hσmem _ (U.mul_mem hu hu')) (Ũ.mul_mem (hσmem u hu) (hσmem u' hu')) ?_
    rw [map_mul, hσπ _ (U.mul_mem hu hu'), hσπ u hu, hσπ u' hu']
  have hnormK : ∀ t, ∀ u ∈ U, x a t * u * (x a t)⁻¹ ∈ U := fun t u hu => by
    refine iSup_list_induction (P := fun u => x a t * u * (x a t)⁻¹ ∈ U) (fun v hv c => ?_) ?_
      (fun u u' hu hu' => ?_) (fun u hu => ?_) hu
    · rw [conj_eq_commutatorElement_mul]
      exact U.mul_mem (hKc v hv t c) (hxmem v hv c)
    · simp
    · have e : x a t * (u * u') * (x a t)⁻¹ =
          (x a t * u * (x a t)⁻¹) * (x a t * u' * (x a t)⁻¹) := by group
      rw [e]
      exact U.mul_mem hu hu'
    · have e : x a t * u⁻¹ * (x a t)⁻¹ = (x a t * u * (x a t)⁻¹)⁻¹ := by group
      rw [e]
      exact U.inv_mem hu
  have hTŨ : ∀ j, ∀ g ∈ Ũ, tor j * g * (tor j)⁻¹ ∈ Ũ := fun j g hg => by
    set h := tor j
    refine iSup_list_induction (P := fun g => h * g * h⁻¹ ∈ Ũ) (fun v hv c => ?_) ?_
      (fun g g' hg hg' => ?_) (fun g hg => ?_) hg
    · rw [hT j v (hL v hv) c]
      exact hXmem v hv _
    · simp
    · have e : h * (g * g') * h⁻¹ = (h * g * h⁻¹) * (h * g' * h⁻¹) := by group
      rw [e]
      exact Ũ.mul_mem hg hg'
    · have e : h * g⁻¹ * h⁻¹ = (h * g * h⁻¹)⁻¹ := by group
      rw [e]
      exact Ũ.inv_mem hg
  have hσT : ∀ j, ∀ u ∈ U, σ (π (tor j) * u * (π (tor j))⁻¹) = tor j * σ u * (tor j)⁻¹ :=
      fun j u hu => by
    have hu' : π (tor j) * u * (π (tor j))⁻¹ ∈ U := by
      rw [← hσπ u hu, ← map_inv, ← map_mul, ← map_mul]
      exact hπŨ _ (hTŨ j _ (hσmem u hu))
    refine IH (hσmem _ hu') (hTŨ j _ (hσmem u hu)) ?_
    rw [hσπ _ hu', map_mul, map_mul, map_inv, hσπ u hu]
  have hconj : ∀ t, ∀ g ∈ Ũ, X a t * g * (X a t)⁻¹ = σ (x a t * π g * (x a t)⁻¹) := by
    intro t
    let D : E → E := fun g => X a t * g * (X a t)⁻¹ * (σ (x a t * π g * (x a t)⁻¹))⁻¹
    have hDker : ∀ g ∈ Ũ, D g ∈ π.ker := fun g hg => by
      rw [MonoidHom.mem_ker]
      simp only [D, map_mul, map_inv, hπX a ha t,
        hσπ _ (hnormK t _ (hπŨ g hg)), mul_inv_cancel]
    have hDc : ∀ g ∈ Ũ, ∀ e, e * D g = D g * e := fun g hg e =>
      (Subgroup.mem_center_iff.1 (hcen (hDker g hg))) e
    have hD1 : D 1 = 1 := by
      have hσ1 : σ 1 = 1 := by
        have := hσ_of 1 Ũ.one_mem
        rwa [map_one] at this
      simp only [D, mul_one, mul_inv_cancel, map_one, hσ1, inv_one]
    have hDmul : ∀ g ∈ Ũ, ∀ g' ∈ Ũ, D (g * g') = D g * D g' := fun g hg g' hg' => by
      have hu := hnormK t _ (hπŨ g hg)
      have hu' := hnormK t _ (hπŨ g' hg')
      have e1 : x a t * π (g * g') * (x a t)⁻¹ =
          (x a t * π g * (x a t)⁻¹) * (x a t * π g' * (x a t)⁻¹) := by
        rw [map_mul]
        group
      have e2 : D (g * g') = (X a t * g * (X a t)⁻¹) * D g' *
          (σ (x a t * π g * (x a t)⁻¹))⁻¹ := by
        simp only [D]
        rw [e1, hσmul _ hu _ hu']
        group
      rw [e2, mul_assoc (X a t * g * (X a t)⁻¹), ← hDc g' hg', ← mul_assoc]
    have hDT : ∀ j, χ j a = 1 → ∀ g ∈ Ũ, D (tor j * g * (tor j)⁻¹) = D g := fun j hha g hg => by
      have hσh := hσT j
      set h := tor j with hhdef
      have hXa : h * X a t * h⁻¹ = X a t := by rw [hhdef, hT j a ha t, hha, one_mul]
      have hxa : π h * x a t * (π h)⁻¹ = x a t := by
        rw [← hπX a ha t, ← map_inv, ← map_mul, ← map_mul, hXa]
      have hu := hnormK t _ (hπŨ g hg)
      have e1 : X a t * (h * g * h⁻¹) * (X a t)⁻¹ = h * (X a t * g * (X a t)⁻¹) * h⁻¹ :=
        calc X a t * (h * g * h⁻¹) * (X a t)⁻¹ =
            (h * X a t * h⁻¹) * (h * g * h⁻¹) * (h * X a t * h⁻¹)⁻¹ := by rw [hXa]
          _ = h * (X a t * g * (X a t)⁻¹) * h⁻¹ := by group
      have e2 : x a t * π (h * g * h⁻¹) * (x a t)⁻¹ =
          π h * (x a t * π g * (x a t)⁻¹) * (π h)⁻¹ :=
        calc x a t * π (h * g * h⁻¹) * (x a t)⁻¹ =
            (π h * x a t * (π h)⁻¹) * (π h * π g * (π h)⁻¹) * (π h * x a t * (π h)⁻¹)⁻¹ := by
              rw [hxa, map_mul, map_mul, map_inv]
          _ = π h * (x a t * π g * (x a t)⁻¹) * (π h)⁻¹ := by group
      have e3 : D (h * g * h⁻¹) = h * D g * h⁻¹ := by
        simp only [D]
        rw [e1, e2, hσh _ hu]
        group
      rw [e3, hDc g hg h, mul_inv_cancel_right]
    have hDgen : ∀ v ∈ L, ∀ c, D (X v c) = 1 := fun v hv => by
      rcases hsep v hv with ⟨j, hha, hhv⟩ | hconjv
      · refine RootLift.eq_one_of_add_of_smul (ρ := fun c => D (X v c)) (fun c c' => ?_) hhv
          (fun c => ?_)
        · rw [hXadd v (hL v hv), hDmul _ (hXmem v hv c) _ (hXmem v hv c')]
        · rw [← hT j v (hL v hv) c, hDT j hha _ (hXmem v hv c)]
      · intro c
        have hmem := hconjv t c
        have hπc : x a t * π (X v c) * (x a t)⁻¹ = π (X a t * X v c * (X a t)⁻¹) := by
          rw [map_mul, map_mul, map_inv, hπX a ha t]
        simp only [D]
        rw [hπc, hσ_of _ hmem, mul_inv_cancel]
    have hDU : ∀ g ∈ Ũ, D g = 1 := fun g hg => by
      have := iSup_list_induction (P := fun g => g ∈ Ũ ∧ D g = 1)
        (fun v hv c => ⟨hXmem v hv c, hDgen v hv c⟩) ⟨Ũ.one_mem, hD1⟩
        (fun g g' ⟨hg, h1⟩ ⟨hg', h2⟩ => ⟨Ũ.mul_mem hg hg', by rw [hDmul g hg g' hg', h1, h2,
          mul_one]⟩)
        (fun g ⟨hg, h1⟩ => ⟨Ũ.inv_mem hg, by
          have := hDmul g⁻¹ (Ũ.inv_mem hg) g hg
          rw [inv_mul_cancel, hD1, h1, mul_one] at this
          exact this.symm⟩) hg
      exact this.2
    intro g hg
    have := hDU g hg
    simp only [D] at this
    exact mul_inv_eq_one.1 this
  have hnorm : chevRoot X a ≤ Subgroup.normalizer (Ũ : Set E) := by
    refine le_normalizer_of_map_conj_le fun y hy => ?_
    obtain ⟨t, rfl⟩ := (mem_chevRoot_iff (hXadd a ha)).1 hy
    rw [Subgroup.map_le_iff_le_comap]
    intro g hg
    rw [Subgroup.mem_comap]
    change X a t * g * (X a t)⁻¹ ∈ Ũ
    rw [hconj t g hg]
    exact hσmem _ (hnormK t _ (hπŨ g hg))
  refine injOn_of_eq_one fun g hg h1 => ?_
  rw [iSup_mem_cons, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm,
    Set.mem_mul] at hg
  obtain ⟨y, hy, u, hu, rfl⟩ := hg
  obtain ⟨t, rfl⟩ := (mem_chevRoot_iff (hXadd a ha)).1 hy
  rw [map_mul, hπX a ha t] at h1
  obtain ⟨F, hF, hFu⟩ := hcoll _ (hπŨ u hu)
  have hupd : ∀ v ∈ L, Function.update F a (x a t) v = F v := fun v hv =>
    Function.update_of_ne (by rintro rfl; exact haL hv) _ _
  have hP := hprod (Function.update F a (x a t)) (fun _ => 1)
    (fun v hv => by
      rcases List.mem_cons.1 hv with rfl | hv
      · rw [Function.update_self]
        exact xh_mem_chevRoot v t
      · rw [hupd v hv]
        exact hF v hv)
    (fun _ _ => Subgroup.one_mem _)
    (by
      rw [List.map_cons, List.prod_cons, Function.update_self, List.map_congr_left hupd, ← hFu,
        h1]
      simp)
  have hx1 : x a t = 1 := by simpa using hP a ha
  rw [hx1, one_mul] at h1
  rw [hXker t hx1, one_mul]
  exact IH hu Ũ.one_mem (h1.trans (map_one π).symm)

end Step

section List

variable {ι k E K : Type*} [Field k] [Group E] [Group K] {π : E →* K}
  (hcen : π.ker ≤ Subgroup.center E) {x : (ι → ℤ) → k → K} {X : (ι → ℤ) → k → E}
  {τ : Type*} {tor : τ → E} {χ : τ → (ι → ℤ) → k}
include hcen

theorem injOn_list' (f : (ι → ℤ) → ℤ) :
    ∀ {L : List (ι → ℤ)}, L.Nodup → L.Pairwise (fun a b => f a ≤ f b) →
      (∀ v ∈ L, ∀ c d, X v (c + d) = X v c * X v d) →
      (∀ v ∈ L, ∀ c d, x v (c + d) = x v c * x v d) →
      (∀ v ∈ L, ∀ c, x v c = 1 → X v c = 1) →
      (∀ v ∈ L, ∀ c, π (X v c) = x v c) →
      (∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ y ∈ chevRoot x a, ∀ z ∈ chevRoot x b,
        ⁅y, z⁆ ∈ ⨆ c ∈ L, ⨆ (_ : min (f a) (f b) < f c), chevRoot x c) →
      ProdInjectiveFor (chevRoot x) L →
      (∀ j, ∀ v ∈ L, ∀ c, tor j * X v c * (tor j)⁻¹ = X v (χ j v * c)) →
      (∀ a ∈ L, ∀ b ∈ L, a ≠ b → (∃ j, χ j a = 1 ∧ χ j b ≠ 1) ∨
        ∀ t c, X a t * X b c * (X a t)⁻¹ ∈ ⨆ v ∈ L, ⨆ (_ : f a < f v ∨ v = b), chevRoot X v) →
      Set.InjOn π ((⨆ v ∈ L, chevRoot X v : Subgroup E) : Set E)
  | [], _, _, _, _, _, _, _, _, _, _ => by
    simp only [List.not_mem_nil, iSup_false, iSup_bot, Subgroup.coe_bot]
    exact Set.injOn_singleton _ _
  | a :: L, hnd, hs, hXadd, hxadd, hXker, hπX, hc, hprod, hT, hsep => by
    obtain ⟨haL, hnd⟩ := List.nodup_cons.1 hnd
    obtain ⟨hah, hs⟩ := List.pairwise_cons.1 hs
    have hL : ∀ v ∈ L, v ∈ a :: L := fun v hv => List.mem_cons_of_mem a hv
    have hc' : ∀ b ∈ L, ∀ c ∈ L, b ≠ c → ∀ y ∈ chevRoot x b, ∀ z ∈ chevRoot x c,
        ⁅y, z⁆ ∈ ⨆ d ∈ L, ⨆ (_ : min (f b) (f c) < f d), chevRoot x d :=
      fun b hb c hc'' hbc y hy z hz =>
        iSup_cons_le' (le_min (hah b hb) (hah c hc''))
          (hc b (hL b hb) c (hL c hc'') hbc y hy z hz)
    have hdrop : ∀ a' ∈ L, ∀ b' ∈ L, ⨆ v ∈ a :: L, ⨆ (_ : f a' < f v ∨ v = b'), chevRoot X v ≤
        ⨆ v ∈ L, ⨆ (_ : f a' < f v ∨ v = b'), chevRoot X v := fun a' ha' b' hb' => by
      rw [iSup_mem_cons]
      refine sup_le (iSup_le fun h => ?_) le_rfl
      rcases h with h | rfl
      · exact absurd h (not_lt.2 (hah a' ha'))
      · exact absurd hb' haL
    have IH := injOn_list' f hnd hs (fun v hv => hXadd v (hL v hv))
      (fun v hv => hxadd v (hL v hv)) (fun v hv => hXker v (hL v hv))
      (fun v hv => hπX v (hL v hv)) hc' (prodInjectiveFor_tail haL hprod)
      (fun j v hv => hT j v (hL v hv))
      (fun a' ha' b hb hab => (hsep a' (hL a' ha') b (hL b hb) hab).imp id
        fun h t c => hdrop a' ha' b hb (h t c))
    refine injOn_cons hcen haL hXadd hxadd (hXker a List.mem_cons_self) hπX
      (fun b hb s t => ?_) (fun u hu => exists_prod_eq_of_commutator_mem (chevRoot x) f hnd hs hc'
        u hu) hprod hT
      (fun b hb => (hsep a List.mem_cons_self b (hL b hb) (by rintro rfl; exact haL hb)).imp id
        fun h t c => by
          have hle : ⨆ v ∈ a :: L, ⨆ (_ : f a < f v ∨ v = b), chevRoot X v ≤
              ⨆ v ∈ L, chevRoot X v := by
            refine iSup₂_le fun v hv => iSup_le fun h' => ?_
            rcases List.mem_cons.1 hv with rfl | hv'
            · rcases h' with h' | rfl
              · exact absurd h' (lt_irrefl _)
              · exact absurd hb haL
            · exact le_iSup₂ (f := fun v (_ : v ∈ L) => chevRoot X v) v hv'
          exact hle (h t c)) IH
    have hab : a ≠ b := by rintro rfl; exact haL hb
    have h := hc a List.mem_cons_self b (hL b hb) hab _ (xh_mem_chevRoot a s) _
      (xh_mem_chevRoot b t)
    have hle : ⨆ c ∈ a :: L, ⨆ (_ : min (f a) (f b) < f c), chevRoot x c ≤
        ⨆ c ∈ L, chevRoot x c :=
      (iSup_cons_le' (le_of_eq (min_eq_left (hah b hb)).symm)).trans
        (iSup₂_mono fun d _ => iSup_le fun _ => le_rfl)
    exact hle h

theorem injOn_list (f : (ι → ℤ) → ℤ) {L : List (ι → ℤ)} (hnd : L.Nodup)
    (hs : L.Pairwise (fun a b => f a ≤ f b))
    (hXadd : ∀ v ∈ L, ∀ c d, X v (c + d) = X v c * X v d)
    (hxadd : ∀ v ∈ L, ∀ c d, x v (c + d) = x v c * x v d)
    (hXker : ∀ v ∈ L, ∀ c, x v c = 1 → X v c = 1) (hπX : ∀ v ∈ L, ∀ c, π (X v c) = x v c)
    (hc : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ y ∈ chevRoot x a, ∀ z ∈ chevRoot x b,
      ⁅y, z⁆ ∈ ⨆ c ∈ L, ⨆ (_ : min (f a) (f b) < f c), chevRoot x c)
    (hprod : ProdInjectiveFor (chevRoot x) L)
    (hT : ∀ j, ∀ v ∈ L, ∀ c, tor j * X v c * (tor j)⁻¹ = X v (χ j v * c))
    (hsep : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∃ j, χ j a = 1 ∧ χ j b ≠ 1) :
    Set.InjOn π ((⨆ v ∈ L, chevRoot X v : Subgroup E) : Set E) :=
  injOn_list' hcen f hnd hs hXadd hxadd hXker hπX hc hprod hT
    fun a ha b hb hab => Or.inl (hsep a ha b hb hab)

end List

section Chevalley

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*} [Field k]
  {x : (Fin D.rank → ℤ) → k → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
  {E : Type*} [Group E] {π : E →* K} (hcen : π.ker ≤ Subgroup.center E)
  {X : (Fin D.rank → ℤ) → k → E} {τ : Type*} {tor : τ → E}
  {χ : τ → (Fin D.rank → ℤ) → k}
include hcen

omit hcen in
theorem chevRoot_eq_rootGroup (hE : ChevalleyExtras D k x C O) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : chevRoot x γ = D.rootGroup γ := by
  ext g
  rw [mem_chevRoot_iff (hE.param γ hγ).2.1, (hE.param γ hγ).1 g]

theorem injOn_posSet_lift' (hD : D.divisible = ∅) (hE : ChevalleyExtras D k x C O)
    (hXadd : ∀ γ ∈ D.roots, ∀ c d, X γ (c + d) = X γ c * X γ d)
    (hπX : ∀ γ ∈ D.roots, ∀ c, π (X γ c) = x γ c)
    (hT : ∀ j, ∀ γ ∈ D.roots, ∀ c, tor j * X γ c * (tor j)⁻¹ = X γ (χ j γ * c))
    (hsep : ∀ γ ∈ D.roots, ∀ δ ∈ D.roots, LinIndepPair γ δ → (∃ j, χ j γ = 1 ∧ χ j δ ≠ 1) ∨
      ∀ t c, X γ t * X δ c * (X γ t)⁻¹ ∈ ⨆ (ε : Fin D.rank → ℤ)
        (_ : ε ∈ D.roots ∧ (ε = δ ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • γ + p.2 • δ)),
          chevRoot X ε)
    (f : (Fin D.rank → ℤ) →+ ℤ) :
    Set.InjOn π ((chevSub X (posSet D.roots f) : Subgroup E) : Set E) := by
  obtain ⟨L, hnd, hmem, hs⟩ := exists_sorted_list (S := posSet D.roots f)
    ((RootSystem.ofCartan D.isFiniteType D.divisible).finite_roots.subset fun _ h => h.1) f
  have hsub : chevSub X (posSet D.roots f) = ⨆ v ∈ L, chevRoot X v := by
    simp only [chevSub, ← hmem]
  rw [hsub]
  have hroot : ∀ v ∈ L, v ∈ D.roots := fun v hv => ((hmem v).1 hv).1
  have hR : ChevRels O C x := ⟨fun γ hγ => (hE.param γ hγ).2.1, hE.comm⟩
  have hXker : ∀ v ∈ L, ∀ c, x v c = 1 → X v c = 1 := fun v hv c h => by
    have hx0 : x v 0 = 1 := by
      have h' := (hE.param v (hroot v hv)).2.1 0 0
      rw [add_zero] at h'
      exact left_eq_mul.1 h'
    have hX0 : X v 0 = 1 := by
      have h' := hXadd v (hroot v hv) 0 0
      rw [add_zero] at h'
      exact left_eq_mul.1 h'
    rw [(hE.param v (hroot v hv)).2.2 (h.trans hx0.symm), hX0]
  refine injOn_list' hcen f hnd hs (fun v hv => hXadd v (hroot v hv))
    (fun v hv => (hE.param v (hroot v hv)).2.1) hXker
    (fun v hv => hπX v (hroot v hv)) ?_ ?_ (fun j v hv => hT j v (hroot v hv)) ?_
  · intro a ha b hb _ y hy z hz
    obtain ⟨ha1, ha2⟩ := (hmem a).1 ha
    obtain ⟨hb1, hb2⟩ := (hmem b).1 hb
    obtain ⟨c, rfl⟩ := (hR.mem_chevRoot_iff ha1).1 hy
    obtain ⟨d, rfl⟩ := (hR.mem_chevRoot_iff hb1).1 hz
    have hab : a + b ≠ 0 := fun h => by
      have := congrArg f h
      rw [map_add, map_zero] at this
      linarith
    refine hR.commutator_mem ha1 hb1 hab c d fun p hp e => ?_
    have hf : min (f a) (f b) < f (p.1 • a + p.2 • b) := by
      rw [map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
      have h1 : (1 : ℤ) ≤ p.1 := by exact_mod_cast hp.1
      have h2 : (1 : ℤ) ≤ p.2 := by exact_mod_cast hp.2.1
      have := min_le_left (f a) (f b)
      nlinarith
    have hL : p.1 • a + p.2 • b ∈ L := (hmem _).2 ⟨hp.2.2, (min_lt_iff.1 hf).elim
      (fun h => ha2.trans h) (fun h => hb2.trans h)⟩
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hL
      (Subgroup.mem_iSup_of_mem hf (xh_mem_chevRoot _ e)))
  · intro F F' hF hF' hFF' v hv
    exact hE.prodInjective f L hnd (fun v hv => (hmem v).1 hv) hs F F'
      (fun v hv => chevRoot_eq_rootGroup hE (hroot v hv) ▸ hF v hv)
      (fun v hv => chevRoot_eq_rootGroup hE (hroot v hv) ▸ hF' v hv) hFF' v hv
  · intro a ha b hb hab
    have hli : LinIndepPair a b := by
      by_contra hli
      rcases eq_or_eq_neg_of_not_linIndepPair D.isFiniteType hD (hroot a ha) (hroot b hb) hli with
        h | h
      · exact hab h.symm
      · have h1 := ((hmem a).1 ha).2
        have h2 := ((hmem b).1 hb).2
        rw [h, map_neg] at h2
        linarith
    refine (hsep a (hroot a ha) b (hroot b hb) hli).imp id fun h t c => ?_
    refine (show (⨆ (ε : Fin D.rank → ℤ) (_ : ε ∈ D.roots ∧ (ε = b ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧
        0 < p.2 ∧ ε = p.1 • a + p.2 • b)), chevRoot X ε) ≤
        ⨆ v ∈ L, ⨆ (_ : f a < f v ∨ v = b), chevRoot X v from
      iSup₂_le fun ε hε => ?_) (h t c)
    obtain ⟨hεr, rfl | ⟨p, hp1, hp2, rfl⟩⟩ := hε
    · exact le_iSup₂_of_le (f := fun v (_ : v ∈ L) => ⨆ (_ : f a < f v ∨ v = ε), chevRoot X v) ε hb
        (le_iSup_of_le (Or.inr rfl) le_rfl)
    · have ha2 := ((hmem a).1 ha).2
      have hb2 := ((hmem b).1 hb).2
      have hf : f a < f (p.1 • a + p.2 • b) := by
        rw [map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
        have h1 : (1 : ℤ) ≤ p.1 := by exact_mod_cast hp1
        have h2 : (1 : ℤ) ≤ p.2 := by exact_mod_cast hp2
        nlinarith
      have hL : p.1 • a + p.2 • b ∈ L := (hmem _).2 ⟨hεr, ha2.trans hf⟩
      exact le_iSup₂_of_le (f := fun v (_ : v ∈ L) => ⨆ (_ : f a < f v ∨ v = b), chevRoot X v)
        _ hL (le_iSup_of_le (Or.inl hf) le_rfl)

theorem injOn_posSet_lift (hD : D.divisible = ∅) (hE : ChevalleyExtras D k x C O)
    (hXadd : ∀ γ ∈ D.roots, ∀ c d, X γ (c + d) = X γ c * X γ d)
    (hπX : ∀ γ ∈ D.roots, ∀ c, π (X γ c) = x γ c)
    (hT : ∀ j, ∀ γ ∈ D.roots, ∀ c, tor j * X γ c * (tor j)⁻¹ = X γ (χ j γ * c))
    (hsep : ∀ γ ∈ D.roots, ∀ δ ∈ D.roots, LinIndepPair γ δ → ∃ j, χ j γ = 1 ∧ χ j δ ≠ 1)
    (f : (Fin D.rank → ℤ) →+ ℤ) :
    Set.InjOn π ((chevSub X (posSet D.roots f) : Subgroup E) : Set E) :=
  injOn_posSet_lift' hcen hD hE hXadd hπX hT
    (fun γ hγ δ hδ hli => Or.inl (hsep γ hγ δ hδ hli)) f

theorem commutatorFormula_lift' (hD : D.divisible = ∅) (hE : ChevalleyExtras D k x C O)
    (hXadd : ∀ γ ∈ D.roots, ∀ c d, X γ (c + d) = X γ c * X γ d)
    (hπX : ∀ γ ∈ D.roots, ∀ c, π (X γ c) = x γ c)
    (hT : ∀ j, ∀ γ ∈ D.roots, ∀ c, tor j * X γ c * (tor j)⁻¹ = X γ (χ j γ * c))
    (hsep : ∀ γ ∈ D.roots, ∀ δ ∈ D.roots, LinIndepPair γ δ → (∃ j, χ j γ = 1 ∧ χ j δ ≠ 1) ∨
      ∀ t c, X γ t * X δ c * (X γ t)⁻¹ ∈ ⨆ (ε : Fin D.rank → ℤ)
        (_ : ε ∈ D.roots ∧ (ε = δ ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • γ + p.2 • δ)),
          chevRoot X ε) :
    CommutatorFormula X O C := by
  intro α hα β hβ hαβ c d
  obtain ⟨f, hfα, hfβ⟩ := exists_addHom_pos_of_not_isNegMultiple D.isFiniteType hD hα hβ
    (not_isNegMultiple_of_add_ne_zero D.isFiniteType hD hα hβ hαβ)
  have hinj := injOn_posSet_lift' hcen hD hE hXadd hπX hT hsep f
  have hpos : ∀ p ∈ O.list α β, p.1 • α + p.2 • β ∈ posSet D.roots f := fun p hp => by
    obtain ⟨hp1, hp2, hr⟩ := (O.mem_iff α hα β hβ hαβ p).1 hp
    exact mem_posSet.2 ⟨hr, pos_apply_nsmul_add_nsmul hfα hfβ (by omega)⟩
  have hXα := xh_mem_chevSub (xh := X) (S := posSet D.roots f) (mem_posSet.2 ⟨hα, hfα⟩) c
  have hXβ := xh_mem_chevSub (xh := X) (S := posSet D.roots f) (mem_posSet.2 ⟨hβ, hfβ⟩) d
  refine hinj ?_ ?_ ?_
  · change ⁅X α c, X β d⁆ ∈ chevSub X (posSet D.roots f)
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hXα hXβ)
      (Subgroup.inv_mem _ hXα)) (Subgroup.inv_mem _ hXβ)
  · exact Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
      exact xh_mem_chevSub (hpos p hp) _
  · rw [map_commutatorElement, hπX α hα, hπX β hβ, hE.comm α hα β hβ hαβ c d, map_list_prod,
      List.map_map]
    refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
    exact (hπX _ (hpos p hp).1 _).symm

theorem commutatorFormula_lift (hD : D.divisible = ∅) (hE : ChevalleyExtras D k x C O)
    (hXadd : ∀ γ ∈ D.roots, ∀ c d, X γ (c + d) = X γ c * X γ d)
    (hπX : ∀ γ ∈ D.roots, ∀ c, π (X γ c) = x γ c)
    (hT : ∀ j, ∀ γ ∈ D.roots, ∀ c, tor j * X γ c * (tor j)⁻¹ = X γ (χ j γ * c))
    (hsep : ∀ γ ∈ D.roots, ∀ δ ∈ D.roots, LinIndepPair γ δ → ∃ j, χ j γ = 1 ∧ χ j δ ≠ 1) :
    CommutatorFormula X O C :=
  commutatorFormula_lift' hcen hD hE hXadd hπX hT
    fun γ hγ δ hδ hli => Or.inl (hsep γ hγ δ hδ hli)

theorem exists_section_of_lift' (hD : D.divisible = ∅) (hE : ChevalleyExtras D k x C O)
    (hB : PresentationB (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) x)
    (hXadd : ∀ γ ∈ D.roots, ∀ c d, X γ (c + d) = X γ c * X γ d)
    (hπX : ∀ γ ∈ D.roots, ∀ c, π (X γ c) = x γ c)
    (hT : ∀ j, ∀ γ ∈ D.roots, ∀ c, tor j * X γ c * (tor j)⁻¹ = X γ (χ j γ * c))
    (hsep : ∀ γ ∈ D.roots, ∀ δ ∈ D.roots, LinIndepPair γ δ → (∃ j, χ j γ = 1 ∧ χ j δ ≠ 1) ∨
      ∀ t c, X γ t * X δ c * (X γ t)⁻¹ ∈ ⨆ (ε : Fin D.rank → ℤ)
        (_ : ε ∈ D.roots ∧ (ε = δ ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • γ + p.2 • δ)),
          chevRoot X ε) :
    ∃ σ : K →* E, ∀ g, π (σ g) = g := by
  obtain ⟨σ, hσ, -⟩ := RankTwo.existsUnique_hom_of_presentationB hB O hE.comm
    (⟨hXadd, commutatorFormula_lift' hcen hD hE hXadd hπX hT hsep⟩ : ChevRels O C X)
  refine ⟨σ, fun g => ?_⟩
  have hid : π.comp σ = MonoidHom.id K := by
    refine MonoidHom.eq_of_eqOn_dense (RankTwo.closure_range_eq_top_of_presentationB hB O) ?_
    intro g hg
    obtain ⟨γ, hγ, c, rfl⟩ : ∃ γ, γ ∈ D.roots ∧ ∃ c, x γ c = g := by
      simpa using hg
    rw [MonoidHom.comp_apply, hσ γ hγ c, MonoidHom.id_apply, hπX γ hγ c]
  exact DFunLike.congr_fun hid g

theorem exists_section_of_lift (hD : D.divisible = ∅) (hE : ChevalleyExtras D k x C O)
    (hB : PresentationB (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) x)
    (hXadd : ∀ γ ∈ D.roots, ∀ c d, X γ (c + d) = X γ c * X γ d)
    (hπX : ∀ γ ∈ D.roots, ∀ c, π (X γ c) = x γ c)
    (hT : ∀ j, ∀ γ ∈ D.roots, ∀ c, tor j * X γ c * (tor j)⁻¹ = X γ (χ j γ * c))
    (hsep : ∀ γ ∈ D.roots, ∀ δ ∈ D.roots, LinIndepPair γ δ → ∃ j, χ j γ = 1 ∧ χ j δ ≠ 1) :
    ∃ σ : K →* E, ∀ g, π (σ g) = g :=
  exists_section_of_lift' hcen hD hE hB hXadd hπX hT
    fun γ hγ δ hδ hli => Or.inl (hsep γ hγ δ hδ hli)

end Chevalley

end CFSG.LieType.Steinberg.CentralExt.HalfSpaceLift
