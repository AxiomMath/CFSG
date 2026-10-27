module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LySylow
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyAux
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyOutConj
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyThreeCycle
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Cover
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyOutPerm
public import CFSG.Sporadic.Recognition.LyonsLocalBasic

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Subgroup Equiv Equiv.Perm CFSG CFSG.Blueprint CFSG.Sporadic.Recognition.LyonsSims
  CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem isConj_x₁_of_normalizes_sylow
    {Y : Type} [Group Y] [Finite Y] (hY : Nonempty (Y ≃* NativeSporadic.Ly)) {t : Y}
    {ρ : ↥(centralizer ({t} : Set Y)) →* Perm (Fin 11)}
    {x₁ x₂ x₃ : ↥(centralizer ({t} : Set Y))} (D : LyData Y t ρ) (S : LyStd ρ x₁ x₂ x₃)
    {x : Y} (hx3 : orderOf x = 3) {A : Subgroup Y} (hA : Nat.card ↥A = 2 ^ 8)
    (hAn : A ≤ normalizer (zpowers x : Set Y)) : IsConj x (x₁ : Y) := by
  classical
  obtain ⟨τ, hτA, hτ2, hτc, -, hτcomm⟩ := exists_central_involution_sylow_ly hY hA
  obtain ⟨g, hg⟩ := isConj_iff.1 (D.one_class τ t hτ2 D.order_t)
  set A' : Subgroup Y := A.map (MulAut.conj g).toMonoidHom with hA'def
  set x' : Y := g * x * g⁻¹ with hx'def
  have hA'card : Nat.card ↥A' = 2 ^ 8 := by rw [hA'def, card_map_conj, hA]
  have hA'n : A' ≤ normalizer (zpowers x' : Set Y) := map_conj_le_normalizer_zpowers g hAn
  have hτcen : A ≤ centralizer ({τ} : Set Y) := fun a ha => by
    rw [mem_centralizer_singleton_iff]; exact hτc a ha
  have hA'K : A' ≤ centralizer ({t} : Set Y) := by
    have := map_conj_le_centralizer g hτcen
    rwa [hg] at this
  have hx'3 : orderOf x' = 3 := by
    rw [hx'def, show g * x * g⁻¹ = MulAut.conj g x from rfl, MulEquiv.orderOf_eq]; exact hx3
  have ht_comm : t ∈ ⁅A', A'⁆ := by
    rw [hA'def, map_conj_commutator]
    exact ⟨τ, hτcomm, by rw [← hg]; rfl⟩
  have hxt : x' ∈ centralizer ({t} : Set Y) := by
    have := (commutator_le_centralizer_of_le_normalizer_zpowers hx'3 hA'n) ht_comm
    rw [mem_centralizer_singleton_iff] at this ⊢
    exact this.symm
  let K : Subgroup Y := centralizer ({t} : Set Y)
  let xK : ↥K := ⟨x', hxt⟩
  have hxK3 : xK ^ 3 = 1 := by
    apply Subtype.ext
    have : x' ^ 3 = 1 := by rw [← hx'3]; exact pow_orderOf_eq_one x'
    simpa [xK] using this
  have hxK1 : xK ≠ 1 := by
    intro h
    have : x' = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hx'3
    exact absurd hx'3 (by norm_num)
  have hA'Kcard : Nat.card ↥(A'.subgroupOf K) = 2 ^ 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'K).toEquiv, hA'card]
  have hker : ρ.ker = zpowers (⟨t, self_mem_centralizer_singleton t⟩ : ↥K) := D.cover.ker_eq
  have hker2 : Nat.card ρ.ker = 2 := by
    rw [hker, Nat.card_zpowers, Subgroup.orderOf_mk, D.order_t]
  have hrange : ρ.range ≤ alternatingGroup (Fin 11) := D.cover.range_eq.le
  have hT := card_map_eq_two_pow_seven ρ hrange hker2 hA'Kcard
  have hTA : (A'.subgroupOf K).map ρ ≤ alternatingGroup (Fin 11) :=
    (Subgroup.map_le_range ρ _).trans hrange
  have hV3 : IsPGroup 3 ↥((zpowers xK).map ρ) := by
    have : IsPGroup 3 ↥(zpowers xK) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime hxK3 hxK1, pow_one])
    exact this.map ρ
  have hVA : (zpowers xK).map ρ ≤ alternatingGroup (Fin 11) :=
    (Subgroup.map_le_range ρ _).trans hrange
  have hrho1 : ρ xK ≠ 1 := by
    intro h
    rcases (D.cover.mem_ker_iff).1 h with h1 | h1
    · exact hxK1 h1
    · have : x' = t := congrArg Subtype.val h1
      rw [this, D.order_t] at hx'3
      exact absurd hx'3 (by norm_num)
  have hV1 : (zpowers xK).map ρ ≠ ⊥ := by
    intro h
    apply hrho1
    have : ρ xK ∈ (zpowers xK).map ρ := Subgroup.mem_map_of_mem _ (mem_zpowers xK)
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  have key : ∀ s ∈ A'.subgroupOf K, ∀ k : ℤ, ∃ m : ℤ, s * xK ^ k * s⁻¹ = xK ^ m := by
    intro s hs k
    have hs' : (s : Y) ∈ normalizer (zpowers x' : Set Y) := hA'n (Subgroup.mem_subgroupOf.1 hs)
    have h1 : (s : Y) * x' * (s : Y)⁻¹ ∈ zpowers x' :=
      (mem_normalizer_iff.1 hs' x').1 (mem_zpowers x')
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h1
    refine ⟨j * k, ?_⟩
    apply Subtype.ext
    have e1 : (s : Y) * x' ^ k * (s : Y)⁻¹ = ((s : Y) * x' * (s : Y)⁻¹) ^ k :=
      (conj_zpow (a := (s : Y)) (b := x') (i := k)).symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    show (s : Y) * x' ^ k * (s : Y)⁻¹ = x' ^ (j * k)
    rw [e1, ← hj, ← zpow_mul]
  have hfwd : ∀ s ∈ A'.subgroupOf K, ∀ v ∈ (zpowers xK).map ρ,
      ρ s * v * (ρ s)⁻¹ ∈ (zpowers xK).map ρ := by
    intro s hs v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
    obtain ⟨m, hm⟩ := key s hs k
    refine ⟨xK ^ m, mem_zpowers_iff.2 ⟨m, rfl⟩, ?_⟩
    rw [← hm, map_mul, map_mul, map_inv]
  have hn : (A'.subgroupOf K).map ρ ≤
      normalizer (((zpowers xK).map ρ : Subgroup (Perm (Fin 11))) : Set (Perm (Fin 11))) := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hy
    refine mem_normalizer_iff.2 fun v => ⟨hfwd s hs v, fun hv => ?_⟩
    have := hfwd s⁻¹ ((A'.subgroupOf K).inv_mem hs) _ hv
    simpa [map_inv, mul_assoc] using this
  have hcyc := cycleType_eq_three_of_normalized hTA hT hV3 hVA hV1 hn (ρ xK)
    (Subgroup.mem_map_of_mem _ (mem_zpowers xK)) hrho1
  have hconj : IsConj xK x₁ := by
    refine D.cover.isConj_of_cycleType_eq hxK3 S.pow₁ ?_
    rw [hcyc, S.rho₁]
    exact (LyOut.x1p_cycleType rfl).symm
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hc' : (c : Y) * x' * (c : Y)⁻¹ = (x₁ : Y) := by
    have := congrArg Subtype.val hc
    simpa [xK] using this
  exact (isConj_iff.2 ⟨g, rfl⟩ : IsConj x x').trans (isConj_iff.2 ⟨(c : Y), hc'⟩)

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
