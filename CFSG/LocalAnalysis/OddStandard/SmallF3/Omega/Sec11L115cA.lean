module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11c_oTwoRes_mono {X Y : Subgroup G} (h : X ≤ Y) : oTwoRes X ≤ oTwoRes Y :=
  Subgroup.closure_mono (fun _ hx => ⟨h hx.1, hx.2⟩)

theorem sec11c_mem_oTwoRes {X : Subgroup G} {x : G} (hx : x ∈ X) (ho : Odd (orderOf x)) :
    x ∈ oTwoRes X :=
  Subgroup.subset_closure ⟨hx, ho⟩

theorem sec11c_oTwoRes_le (X : Subgroup G) : oTwoRes X ≤ X :=
  (Subgroup.closure_le X).2 (fun _ hx => hx.1)

theorem sec11c_orderOf_conj (r x : G) : orderOf (r * x * r⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj r).toMonoidHom (MulAut.conj r).injective x
  simpa using h

theorem sec11c_conj_mem_oTwoRes {X : Subgroup G} {r : G} (hr : ∀ x ∈ X, r * x * r⁻¹ ∈ X)
    {y : G} (hy : y ∈ oTwoRes X) : r * y * r⁻¹ ∈ oTwoRes X := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    refine sec11c_mem_oTwoRes (hr x hx.1) ?_
    rw [sec11c_orderOf_conj]
    exact hx.2
  | one => simp
  | mul x y _ _ hx hy =>
    have h : r * (x * y) * r⁻¹ = (r * x * r⁻¹) * (r * y * r⁻¹) := by group
    rw [h]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have h : r * x⁻¹ * r⁻¹ = (r * x * r⁻¹)⁻¹ := by group
    rw [h]
    exact Subgroup.inv_mem _ hx

theorem sec11c_cent_pair (t z : G) :
    centralizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) =
      centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
  have h : (zpowers t ⊔ zpowers z : Subgroup G) = Subgroup.closure ({t, z} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    rfl
  rw [h, Subgroup.centralizer_closure]
  ext g
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem sec11c_fixed_coset [Finite G] {d : G} (hd : IsPGroup 2 (zpowers d)) {N : Subgroup G}
    (hN : Odd (Nat.card N)) (hdN : ∀ m ∈ N, d * m * d⁻¹ ∈ N) {v : G}
    (hv : v⁻¹ * (d * v * d⁻¹) ∈ N) : ∃ c : G, v⁻¹ * c ∈ N ∧ d * c = c * d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : ¬ 2 ∣ Nat.card N := fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  have hstep : ∀ y : G, v⁻¹ * y ∈ N → v⁻¹ * (d * y * d⁻¹) ∈ N := by
    intro y hy
    have e : v⁻¹ * (d * y * d⁻¹) = (v⁻¹ * (d * v * d⁻¹)) * (d * (v⁻¹ * y) * d⁻¹) := by group
    rw [e]
    exact N.mul_mem hv (hdN _ hy)
  have hpow : ∀ k : ℕ, ∀ y : G, v⁻¹ * y ∈ N → v⁻¹ * (d ^ k * y * (d ^ k)⁻¹) ∈ N := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have := hstep _ (ih y hy)
      have e : d * (d ^ k * y * (d ^ k)⁻¹) * d⁻¹ = d ^ (k + 1) * y * (d ^ (k + 1))⁻¹ := by
        rw [pow_succ']
        group
      rwa [e] at this
  let α : ↥(zpowers d) →* MulAut G := MulAut.conj.comp (zpowers d).subtype
  have hα : ∀ (a : ↥(zpowers d)) (y : G), α a y = (a : G) * y * (a : G)⁻¹ := fun a y => rfl
  have hinv : ∀ a : ↥(zpowers d), ∀ y : G, v⁻¹ * y ∈ N → v⁻¹ * α a y ∈ N := by
    intro a y hy
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp
      ((mem_powers_iff_mem_zpowers (x := d) (y := (a : G))).mpr a.2)
    rw [hα, ← hk]
    exact hpow k y hy
  obtain ⟨c, hc, hfix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 hd α N hcop v).2 hinv
  refine ⟨c, hc, ?_⟩
  have h' : d * c * d⁻¹ = c := (hα ⟨d, mem_zpowers d⟩ c).symm.trans (hfix ⟨d, mem_zpowers d⟩)
  calc d * c = d * c * d⁻¹ * d := by group
    _ = c * d := by rw [h']

end CFSG.OddStandard.SmallF3.Omega
