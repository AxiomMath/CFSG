module

public import CFSG.Holt.H78.Lemma16
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Holt.H78

open Subgroup

namespace L17


variable {G : Type*} [Group G]

def conjRestrict (T : Subgroup G) {g : G} (hg : g ∈ normalizer (T : Set G)) : MulAut T where
  toFun x := ⟨g * x * g⁻¹, (mem_normalizer_iff.1 hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by simpa using (mem_normalizer_iff.1 (inv_mem hg) x).1 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjRestrict_pow_apply (T : Subgroup G) {g : G} (hg : g ∈ normalizer (T : Set G))
    (j : ℕ) (x : T) : (((conjRestrict T hg ^ j) x : T) : G) = g ^ j * x * (g ^ j)⁻¹ := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply]
    change g * (((conjRestrict T hg ^ j) x : T) : G) * g⁻¹ = _
    rw [ih, pow_succ']; group

theorem commutator_mem_of_sup_eq_top {S D : Subgroup G} (hSc : S ≤ center G) (hSD : S ⊔ D = ⊤)
    (a b : G) : a * b * a⁻¹ * b⁻¹ ∈ D := by
  have : S.Normal := normal_of_le_center hSc
  obtain ⟨s₁, hs₁, y₁, hy₁, rfl⟩ := mem_sup_of_normal_left.1 (hSD ▸ mem_top a : a ∈ S ⊔ D)
  obtain ⟨s₂, hs₂, y₂, hy₂, rfl⟩ := mem_sup_of_normal_left.1 (hSD ▸ mem_top b : b ∈ S ⊔ D)
  have c₁ := mem_center_iff.1 (hSc hs₁)
  have c₂ := mem_center_iff.1 (hSc hs₂)
  have k₁ : ∀ X : G, s₁ * X * s₁⁻¹ = X := fun X => by rw [← c₁ X, mul_inv_cancel_right]
  have k₂ : ∀ X : G, s₂ * X * s₂⁻¹ = X := fun X => by rw [← c₂ X, mul_inv_cancel_right]
  have e : s₁ * y₁ * (s₂ * y₂) * (s₁ * y₁)⁻¹ * (s₂ * y₂)⁻¹ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by
    calc s₁ * y₁ * (s₂ * y₂) * (s₁ * y₁)⁻¹ * (s₂ * y₂)⁻¹
        = s₁ * (y₁ * (s₂ * y₂) * y₁⁻¹) * s₁⁻¹ * (s₂ * y₂)⁻¹ := by group
      _ = y₁ * s₂ * y₂ * y₁⁻¹ * y₂⁻¹ * s₂⁻¹ := by rw [k₁]; group
      _ = s₂ * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * s₂⁻¹ := by rw [c₂ y₁]; group
      _ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := k₂ _
  rw [e]
  exact mul_mem (mul_mem (mul_mem hy₁ hy₂) (inv_mem hy₁)) (inv_mem hy₂)

theorem exists_eq_commutator_of_fixedPointFree [Finite G] {U : Subgroup G} {d : G}
    (hdU : d ∈ normalizer (U : Set G)) (hd : ∀ u ∈ U, d * u * d⁻¹ = u → u = 1) {u : G}
    (hu : u ∈ U) : ∃ w ∈ U, u = w⁻¹ * d * w * d⁻¹ := by
  let f : U → U := fun w => ⟨(w : G)⁻¹ * (d * w * d⁻¹),
    mul_mem (inv_mem w.2) ((mem_normalizer_iff.1 hdU w).1 w.2)⟩
  have hf : Function.Injective f := by
    intro w w' hww'
    have h1 : (w : G)⁻¹ * (d * w * d⁻¹) = (w' : G)⁻¹ * (d * w' * d⁻¹) := congrArg Subtype.val hww'
    have hy : (w' : G) * (w : G)⁻¹ ∈ U := mul_mem w'.2 (inv_mem w.2)
    have h2 : d * ((w' : G) * (w : G)⁻¹) * d⁻¹ = (w' : G) * (w : G)⁻¹ := by
      have : d * w' * d⁻¹ = (w' : G) * ((w : G)⁻¹ * (d * w * d⁻¹)) := by
        rw [h1]; group
      calc d * ((w' : G) * (w : G)⁻¹) * d⁻¹ = (d * w' * d⁻¹) * (d * w * d⁻¹)⁻¹ := by group
        _ = (w' : G) * (w : G)⁻¹ := by rw [this]; group
    have h3 := hd _ hy h2
    exact Subtype.ext (mul_inv_eq_one.1 h3).symm
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hf) ⟨u, hu⟩
  refine ⟨w, w.2, ?_⟩
  have := congrArg Subtype.val hw
  change (w : G)⁻¹ * (d * w * d⁻¹) = u at this
  rw [← this]; group

end L17

open L16 L17

variable {G : Type*} [Group G]

theorem lemma_1_7 [Finite G] {S U : Subgroup G} (T : Sylow 2 G) (hSc : S ≤ center G)
    (hS2 : IsPGroup 2 S) (hUT : U ≤ T) (hUS : U ⊓ S = ⊥)
    (hTU : ∀ x ∈ (T : Subgroup G), ∀ u ∈ U, x * u * x⁻¹ ∈ U) {N k : ℕ} (hN : 3 ≤ N)
    (hk : k = 2 ^ N - 1 ∨ (3 * k = 2 ^ N - 1 ∧ 6 ≤ N))
    (hsq : ∀ x ∈ (T : Subgroup G), x ^ 2 ∈ U ⊔ S) (hidx : (U ⊔ S).relIndex T = 2 ^ N)
    {g : G} (hgT : g ∈ normalizer (T : Set G)) (hgU : g ∈ normalizer (U : Set G))
    (hgk : ∀ j : ℕ, g ^ j ∈ S ↔ k ∣ j)
    (hsemi : ∀ (j : ℕ), ∀ x ∈ (T : Subgroup G),
      x⁻¹ * (g ^ j * x * (g ^ j)⁻¹) ∈ U ⊔ S → x ∈ U ⊔ S ∨ g ^ j ∈ S)
    {d : G} (hdU : d ∈ normalizer (U : Set G)) (hd : ∀ u ∈ U, d * u * d⁻¹ = u → u = 1) :
    ∃ Gs : Subgroup G, Gs.Normal ∧ Gs ⊓ S = ⊥ ∧ Gs ⊔ S = ⊤ ∧ U ≤ Gs := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSn : S.Normal := normal_of_le_center hSc
  have hSc' : ∀ s ∈ S, ∀ y : G, y * s = s * y := fun s hs => mem_center_iff.1 (hSc hs)
  have hST : S ≤ T := hS2.le_sylow_of_normal T
  have hWn : ∀ x ∈ (T : Subgroup G), ∀ w ∈ U ⊔ S, x * w * x⁻¹ ∈ U ⊔ S := fun x hx w hw =>
    conj_mem_sup_of (fun u hu => hTU x hx u hu) (fun s hs => hSn.conj_mem s hs x) hw
  have hφpow := conjRestrict_pow_apply (T : Subgroup G) hgT
  have hφ1 : ∀ j : ℕ, g ^ j ∈ S → conjRestrict (T : Subgroup G) hgT ^ j = 1 := by
    intro j hj
    ext x
    rw [hφpow, MulAut.one_apply, ← hSc' _ hj, mul_inv_cancel_right]
  have hord : orderOf (conjRestrict (T : Subgroup G) hgT) = k := by
    have h1 := hφ1 k ((hgk k).2 dvd_rfl)
    have h2 : ∀ j, conjRestrict (T : Subgroup G) hgT ^ j = 1 → k ∣ j := by
      intro j hj
      obtain ⟨x, hxT, hxW⟩ : ∃ x ∈ (T : Subgroup G), x ∉ U ⊔ S := by
        by_contra hc
        push Not at hc
        have h8 : 8 ≤ 2 ^ N := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
        have := Subgroup.relIndex_eq_one.2 hc
        omega
      have hx := hφpow j ⟨x, hxT⟩
      rw [hj, MulAut.one_apply] at hx
      rcases hsemi j x hxT (by rw [← hx, inv_mul_cancel]; exact one_mem _) with h | h
      · exact absurd h hxW
      · exact (hgk j).1 h
    exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one h1) (h2 _ (pow_orderOf_eq_one _))
  have hT'n : ((U ⊔ S).subgroupOf T).Normal := ⟨fun n hn x => by
    rw [mem_subgroupOf] at hn ⊢; exact hWn x x.2 n hn⟩
  have hR'n : (U.subgroupOf T).Normal := ⟨fun n hn x => by
    rw [mem_subgroupOf] at hn ⊢; exact hTU x x.2 n hn⟩
  obtain ⟨V', ⟨-, -, hRV', hTV', hTV'top⟩, -⟩ := lemma_1_6_rel T.isPGroup'
    (conjRestrict (T : Subgroup G) hgT) (T := (U ⊔ S).subgroupOf T) (R := U.subgroupOf T)
    (N := N)
    (fun x hx => mem_subgroupOf.2 (mem_sup_left (mem_subgroupOf.1 hx)))
    (fun r hr => mem_subgroupOf.2 ((mem_normalizer_iff.1 hgU r).1 (mem_subgroupOf.1 hr)))
    (fun t ht => by
      rw [mem_subgroupOf] at ht ⊢
      obtain ⟨u, hu, s, hs, he⟩ := mem_sup_of_normal_right.1 ht
      have c := hSc' s hs
      have e : ((t⁻¹ * conjRestrict (T : Subgroup G) hgT t : T) : G) =
          u⁻¹ * (g * u * g⁻¹) := by
        change (t : G)⁻¹ * (g * t * g⁻¹) = _
        rw [← he]
        calc (u * s)⁻¹ * (g * (u * s) * g⁻¹) = s⁻¹ * ((u⁻¹ * (g * u * (s * g⁻¹)))) := by group
          _ = s⁻¹ * ((u⁻¹ * (g * u * g⁻¹)) * s) := by rw [← c g⁻¹]; group
          _ = u⁻¹ * (g * u * g⁻¹) := by rw [c, inv_mul_cancel_left]
      rw [e]
      exact mul_mem (inv_mem hu) ((mem_normalizer_iff.1 hgU u).1 hu))
    (fun x => mem_subgroupOf.2 (by simpa using hsq x x.2)) hidx hN
    (fun j x hx => by
      rw [mem_subgroupOf] at hx ⊢
      have hx' : (x : G)⁻¹ * (g ^ j * x * (g ^ j)⁻¹) ∈ U ⊔ S := by
        simpa [hφpow] using hx
      exact (hsemi j x x.2 hx').imp id (hφ1 j))
    (hord ▸ hk)
  have hUV : U ≤ V'.map (T : Subgroup G).subtype := fun u hu =>
    ⟨⟨u, hUT hu⟩, hRV' (mem_subgroupOf.2 hu), rfl⟩
  have hSV : S ⊓ V'.map (T : Subgroup G).subtype = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hxS, v, hv, rfl⟩
    have hvW : v ∈ (U ⊔ S).subgroupOf T := mem_subgroupOf.2 (mem_sup_right hxS)
    have hvU : (v : G) ∈ U := by
      have : v ∈ U.subgroupOf T := hTV' ▸ (⟨hvW, hv⟩ : v ∈ (U ⊔ S).subgroupOf T ⊓ V')
      exact mem_subgroupOf.1 this
    exact hUS ▸ (⟨hvU, hxS⟩ : (v : G) ∈ U ⊓ S)
  have hSVsup : S ⊔ V'.map (T : Subgroup G).subtype = T := by
    refine le_antisymm (sup_le hST (map_subtype_le V')) (fun x hx => ?_)
    have hx' : (⟨x, hx⟩ : T) ∈ (U ⊔ S).subgroupOf T ⊔ V' := hTV'top ▸ mem_top _
    obtain ⟨w, hw, v, hv, he⟩ := mem_sup_of_normal_left.1 hx'
    obtain ⟨u, hu, s, hs, hus⟩ := mem_sup_of_normal_right.1 (mem_subgroupOf.1 hw)
    have hxe : x = s * (u * v) := by
      have h1 : (x : G) = (w : G) * v := (congrArg Subtype.val he).symm
      rw [h1, ← hus, hSc' s hs u, mul_assoc]
    rw [hxe]
    exact mul_mem (mem_sup_left hs) (mem_sup_right (mul_mem (hUV hu) ⟨v, hv, rfl⟩))
  have hcomm : IsMulCommutative S := ⟨⟨fun a b => Subtype.ext (mem_center_iff.1 (hSc b.2) a)⟩⟩
  have hcop : Nat.Coprime (T : Subgroup G).index (Nat.card S) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hS2
    rw [hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_comm.1
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 T.not_dvd_index))
  obtain ⟨D, -, hSD, hSDtop⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting S T _ hcop hSV hSVsup
  have hDn : D.Normal := ⟨fun n hn x => by
    obtain ⟨s, hs, y, hy, rfl⟩ := mem_sup_of_normal_left.1 (hSDtop ▸ mem_top x : x ∈ S ⊔ D)
    have e : s * y * n * (s * y)⁻¹ = y * n * y⁻¹ := by
      calc s * y * n * (s * y)⁻¹ = s * (y * n * y⁻¹) * s⁻¹ := by group
        _ = y * n * y⁻¹ := by rw [← hSc' s hs, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (mul_mem hy hn) (inv_mem hy)⟩
  refine ⟨D, hDn, by rw [inf_comm]; exact hSD, by rw [sup_comm]; exact hSDtop, fun u hu => ?_⟩
  obtain ⟨w, -, rfl⟩ := exists_eq_commutator_of_fixedPointFree hdU hd hu
  simpa using commutator_mem_of_sup_eq_top hSc hSDtop w⁻¹ d

theorem lemma_1_7_of_surjective [Finite G] {Q : Type*} [Group Q] (π : G →* Q)
    (hπ : Function.Surjective π) (hSc : π.ker ≤ center G) (hS2 : IsPGroup 2 π.ker)
    (T : Sylow 2 G) {U : Subgroup G} (hUT : U ≤ T) (hUS : U ⊓ π.ker = ⊥)
    (hU : normalizer (T : Set G) ≤ normalizer (U : Set G)) {N k : ℕ} (hN : 3 ≤ N)
    (hk : k = 2 ^ N - 1 ∨ (3 * k = 2 ^ N - 1 ∧ 6 ≤ N))
    (hsq : ∀ x ∈ (T : Subgroup G).map π, x ^ 2 ∈ U.map π)
    (hidx : (U.map π).relIndex ((T : Subgroup G).map π) = 2 ^ N)
    {gbar : Q} (hgT : gbar ∈ normalizer (((T : Subgroup G).map π : Subgroup Q) : Set Q))
    (hgk : orderOf gbar = k)
    (hsemi : ∀ (j : ℕ), ∀ x ∈ (T : Subgroup G).map π,
      x⁻¹ * (gbar ^ j * x * (gbar ^ j)⁻¹) ∈ U.map π → x ∈ U.map π ∨ gbar ^ j = 1)
    {dbar : Q} (hdT : dbar ∈ normalizer (((T : Subgroup G).map π : Subgroup Q) : Set Q))
    (hd : ∀ z ∈ U.map π, dbar * z * dbar⁻¹ = z → z = 1) :
    ∃ Gs : Subgroup G, Gs.Normal ∧ Gs ⊓ π.ker = ⊥ ∧ Gs ⊔ π.ker = ⊤ ∧ U ≤ Gs := by
  have hkerT : π.ker ≤ T := hS2.le_sylow_of_normal T
  have hcomapT : ((T : Subgroup G).map π).comap π = T := by
    rw [comap_map_eq, sup_eq_left.2 hkerT]
  have key : ∀ y : G, π y ∈ normalizer (((T : Subgroup G).map π : Subgroup Q) : Set Q) →
      ∀ t ∈ (T : Subgroup G), y * t * y⁻¹ ∈ (T : Subgroup G) := by
    intro y hy t ht
    rw [← hcomapT, mem_comap, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 hy _).1 ⟨t, ht, rfl⟩
  have hNT : ∀ y : G, π y ∈ normalizer (((T : Subgroup G).map π : Subgroup Q) : Set Q) →
      y ∈ normalizer ((T : Subgroup G) : Set G) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro t
    refine ⟨key y hy t, fun ht => ?_⟩
    have hy' : π y⁻¹ ∈ normalizer (((T : Subgroup G).map π : Subgroup Q) : Set Q) := by
      rw [map_inv]; exact inv_mem hy
    have := key y⁻¹ hy' _ ht
    simpa [mul_assoc] using this
  obtain ⟨g, rfl⟩ := hπ gbar
  obtain ⟨d, rfl⟩ := hπ dbar
  have hgT' := hNT g hgT
  have hdT' := hNT d hdT
  refine lemma_1_7 T hSc hS2 hUT hUS
    (fun x hx u hu => (mem_normalizer_iff.1 (hU (le_normalizer hx)) u).1 hu) hN hk
    (fun x hx => by
      rw [← comap_map_eq, mem_comap, map_pow]
      exact hsq _ ⟨x, hx, rfl⟩)
    (by rw [← comap_map_eq, relIndex_comap]; exact hidx) hgT' (hU hgT')
    (fun j => by rw [MonoidHom.mem_ker, map_pow, ← hgk, orderOf_dvd_iff_pow_eq_one])
    (fun j x hx hmem => ?_) (hU hdT') (fun u hu hdu => ?_)
  · rw [← comap_map_eq, mem_comap] at hmem
    simp only [map_mul, map_inv, map_pow] at hmem
    rcases hsemi j (π x) ⟨x, hx, rfl⟩ hmem with h | h
    · left
      rw [← comap_map_eq, mem_comap]
      exact h
    · right
      rw [MonoidHom.mem_ker, map_pow]
      exact h
  · have h1 : π u = 1 := hd (π u) ⟨u, hu, rfl⟩ (by rw [← map_inv, ← map_mul, ← map_mul, hdu])
    have : u ∈ U ⊓ π.ker := Subgroup.mem_inf.2 ⟨hu, h1⟩
    rw [hUS] at this
    exact this

end CFSG.Holt.H78
