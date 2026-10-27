module

public import CFSG.Holt.H78.Sec4CCLMatch
import CFSG.Holt.H78.Sec4Prop43W
import CFSG.Holt.H78.KernelSplit
import CFSG.Holt.H78.Lemma27Real
import CFSG.Holt.H78.Sec4Lemma48
public import CFSG.Holt.H78.Sec4FinalA

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section Coset

variable {K : Type*} [Group K]

theorem exists_mem_centralizer_conj_of_odd {O : Subgroup K} [O.Normal] (hO : Odd (Nat.card O))
    {Z : Subgroup K} (hZ : IsPGroup 2 Z) {u : K} (hu : u * u = 1)
    (hZu : ∀ z ∈ Z, z * u * z⁻¹ * u ∈ O) :
    ∃ x : K, x * x = 1 ∧ x ∈ Subgroup.centralizer (Z : Set K) ∧ ∃ p ∈ O, p * u * p⁻¹ = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  set T := {g : K // g * u ∈ O}
  have hmem : ∀ z ∈ Z, ∀ g : K, g * u ∈ O → z * g * z⁻¹ * u ∈ O := by
    intro z hz g hg
    have h1 := ‹O.Normal›.conj_mem _ hg z
    have h2 := hZu z hz
    have e : z * g * z⁻¹ * u = z * (g * u) * z⁻¹ * (z * u * z⁻¹ * u) := by
      calc z * g * z⁻¹ * u = z * g * (u * u) * z⁻¹ * u := by rw [hu, mul_one]
        _ = _ := by group
    rw [e]
    exact O.mul_mem h1 h2
  let _ : MulAction Z T :=
    { smul := fun z g => ⟨(z : K) * g * (z : K)⁻¹, hmem z z.2 g g.2⟩
      one_smul := fun g => Subtype.ext (by
        change ((1 : Z) : K) * g * ((1 : Z) : K)⁻¹ = g
        simp)
      mul_smul := fun z z' g => Subtype.ext (by
        change (z * z' : K) * g * (z * z' : K)⁻¹ = z * (z' * g * (z' : K)⁻¹) * (z : K)⁻¹
        group) }
  have hcard : Nat.card T = Nat.card O := by
    refine Nat.card_congr ⟨fun g => ⟨g * u, g.2⟩, fun o => ⟨o * u, ?_⟩, fun g => ?_, fun o => ?_⟩
    · rw [mul_assoc, hu, mul_one]; exact o.2
    · exact Subtype.ext (by simp [mul_assoc, hu])
    · exact Subtype.ext (by simp [mul_assoc, hu])
  obtain ⟨g₀, hg₀⟩ := hZ.nonempty_fixed_point_of_prime_not_dvd_card T (by
    rw [hcard]
    exact Nat.odd_iff.mp hO |> fun h h' => by omega)
  have hg₀Z : (g₀ : K) ∈ Subgroup.centralizer (Z : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h := congrArg Subtype.val (hg₀ ⟨z, hz⟩)
    change z * (g₀ : K) * z⁻¹ = g₀ at h
    calc z * (g₀ : K) = z * g₀ * z⁻¹ * z := by group
      _ = g₀ * z := by rw [h]
  set o := (g₀ : K) * u with ho
  have hoO : o ∈ O := g₀.2
  have hg : (g₀ : K) = o * u := by rw [ho, mul_assoc, hu, mul_one]
  have hsq : (g₀ : K) * g₀ ∈ O := by
    have h1 := ‹O.Normal›.conj_mem _ hoO u
    rw [hg, show o * u * (o * u) = o * (u * o * u⁻¹) by rw [hui]; group]
    exact O.mul_mem hoO h1
  set m := orderOf ((g₀ : K) * g₀)
  have hm : Odd m := Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O hsq)
  obtain ⟨k, hk⟩ := hm
  set x := (g₀ : K) ^ m with hx
  have hxx : x * x = 1 := by
    rw [hx, ← pow_add, ← two_mul, pow_mul, sq, pow_orderOf_eq_one]
  have hxZ : x ∈ Subgroup.centralizer (Z : Set K) := pow_mem hg₀Z m
  have hxu : x * u ∈ O := by
    have e : x * u = o * (u * ((g₀ : K) * g₀) ^ k * u⁻¹) := by
      rw [hx, hk, pow_succ', pow_mul, ← sq, hui, hg]
      group
    rw [e]
    exact O.mul_mem hoO (‹O.Normal›.conj_mem _ (pow_mem hsq k) u)
  have hxo : Odd (orderOf (x * u)) := Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O hxu)
  obtain ⟨p, hp, hpu⟩ := exists_conj_eq_mul_of_odd_orderOf hxo hu
    (by rw [mul_assoc x u u, hu, mul_one]; exact hxx)
  refine ⟨x, hxx, hxZ, p, ?_, ?_⟩
  · exact (Subgroup.zpowers_le.mpr hxu) hp
  · rw [hpu, mul_assoc, hu, mul_one]

end Coset

section Lifts

variable {K : Type} [Group K] [Finite K] {X : Type} [MulAction K X] [Finite X] [FaithfulSMul K X]

namespace HoltData

variable (D : HoltData K X) {i₀ : D.ι} (hι : ∀ j, j = i₀)

include hι in
theorem mul_mem_jOddCore_of_extRho_eq (hK : IsStarGroup K X) {e e' : K}
    (he : e ∈ longInv K X) (he' : e' ∈ longInv K X) (h : D.extRho hι e = D.extRho hι e') :
    e * e' ∈ jOddCore K X := by
  have hS := D.mul_mem_socPre hK he he'
  set h' : jHull K X := ⟨e * e', mul_mem (mem_jHull_of_mem_longInv he)
    (mem_jHull_of_mem_longInv he')⟩
  have hker : (h' : K) ∈ jOrbitKernel K X := by
    rw [D.mem_jOrbitKernel_iff_rho]
    intro i
    rw [hι i, ← D.extRho_eq_rho hι]
    change D.extRho hι (e * e') = 1
    rw [map_mul, h, ← map_mul, mul_self_eq_one_of_mem_longInv he', map_one]
  rw [← D.socPre_inf_jOrbitKernel]
  exact ⟨hS, hker⟩

omit [Finite K] [Finite X] [FaithfulSMul K X] in
include hι in
theorem extRho_eq_one_of_mem_jOddCore {o : K} (ho : o ∈ jOddCore K X) : D.extRho hι o = 1 := by
  rw [show o = ((⟨o, jOddCore_le_jHull ho⟩ : jHull K X) : K) from rfl, D.extRho_eq_rho hι]
  exact D.rho_eq_one_of_mem_jOddCore ho i₀

include hι in
theorem exists_mem_centralizer_extRho_eq (hK : IsStarGroup K X) {Z : Subgroup K}
    (hZ : IsPGroup 2 Z) {u : K} (hu : u ∈ longInv K X)
    (hZu : ∀ z ∈ Z, D.extRho hι z * D.extRho hι u = D.extRho hι u * D.extRho hι z) :
    ∃ x ∈ longInv K X, x ∈ Subgroup.centralizer (Z : Set K) ∧ D.extRho hι x = D.extRho hι u := by
  have huu := mul_self_eq_one_of_mem_longInv hu
  obtain ⟨x, -, hxZ, p, hp, rfl⟩ := exists_mem_centralizer_conj_of_odd odd_card_jOddCore hZ huu
    fun z hz => D.mul_mem_jOddCore_of_extRho_eq hι hK (conj_mem_longInv hu z) hu (by
      rw [map_mul, map_mul, map_inv, hZu z hz, mul_inv_cancel_right])
  refine ⟨p * u * p⁻¹, conj_mem_longInv hu p, hxZ, ?_⟩
  rw [map_mul, map_mul, map_inv, D.extRho_eq_one_of_mem_jOddCore hι hp, one_mul, inv_one,
    mul_one]

include hι in
theorem exists_commute_lifts (hK : IsStarGroup K X) {Z : Subgroup K} (hZ : IsPGroup 2 Z)
    {u₁ u₂ : K} (hu₁ : u₁ ∈ longInv K X) (hu₂ : u₂ ∈ longInv K X)
    (h12 : D.extRho hι u₁ * D.extRho hι u₂ = D.extRho hι u₂ * D.extRho hι u₁)
    (hZ₁ : ∀ z ∈ Z, D.extRho hι z * D.extRho hι u₁ = D.extRho hι u₁ * D.extRho hι z)
    (hZ₂ : ∀ z ∈ Z, D.extRho hι z * D.extRho hι u₂ = D.extRho hι u₂ * D.extRho hι z)
    {γ₀ : X} (hγ₀ : γ₀ ∈ fixSet X Z)
    (hγ₂ : D.extRho hι u₂ (D.coord γ₀ i₀) = D.coord γ₀ i₀) :
    ∃ x₁ x₂ : K, x₁ ∈ longInvAt K X γ₀ ∧ x₂ ∈ longInvAt K X γ₀ ∧ x₁ * x₂ = x₂ * x₁ ∧
      x₁ ∈ Subgroup.centralizer (Z : Set K) ∧ x₂ ∈ Subgroup.centralizer (Z : Set K) ∧
      D.extRho hι x₁ = D.extRho hι u₁ ∧ D.extRho hι x₂ = D.extRho hι u₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := jOddCore K X
  obtain ⟨y₁, hy₁, hy₁Z, hy₁ρ⟩ := D.exists_mem_centralizer_extRho_eq hι hK hZ hu₁ hZ₁
  obtain ⟨y₂, hy₂, hy₂Z, hy₂ρ⟩ := D.exists_mem_centralizer_extRho_eq hι hK hZ hu₂ hZ₂
  have hy₁y₁ := mul_self_eq_one_of_mem_longInv hy₁
  have hy₂y₂ := mul_self_eq_one_of_mem_longInv hy₂
  have hu₂u₂ := mul_self_eq_one_of_mem_longInv hu₂
  have hsq : (y₁ * y₂) ^ 2 ∈ O ⊓ Subgroup.centralizer (Z : Set K) := by
    have hconj : y₂ * y₁ * y₂ ∈ longInv K X := by
      have h := conj_mem_longInv hy₁ y₂
      rwa [inv_eq_self_of_mem_longInv hy₂] at h
    refine ⟨?_, pow_mem (mul_mem hy₁Z hy₂Z) 2⟩
    have h := D.mul_mem_jOddCore_of_extRho_eq hι hK hy₁ hconj (by
      rw [map_mul, map_mul, hy₁ρ, hy₂ρ, ← h12, mul_assoc, ← map_mul, hu₂u₂, map_one, mul_one])
    rwa [sq, show y₁ * y₂ * (y₁ * y₂) = y₁ * (y₂ * y₁ * y₂) by group]
  have hOZ : Odd (Nat.card ↥(O ⊓ Subgroup.centralizer (Z : Set K))) :=
    Odd.of_dvd_nat odd_card_jOddCore (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨p, hp, hpc⟩ := exists_mem_conj_commute_of_odd hOZ hy₁y₁ hy₂y₂ hsq
  set y₁' := p * y₁ * p⁻¹
  have hy₁' : y₁' ∈ longInv K X := conj_mem_longInv hy₁ p
  have hy₁'Z : y₁' ∈ Subgroup.centralizer (Z : Set K) :=
    mul_mem (mul_mem hp.2 hy₁Z) (inv_mem hp.2)
  have hy₁'ρ : D.extRho hι y₁' = D.extRho hι u₁ := by
    rw [map_mul, map_mul, map_inv, D.extRho_eq_one_of_mem_jOddCore hι hp.1, one_mul, inv_one,
      mul_one, hy₁ρ]
  obtain ⟨δ, hδ, hδu⟩ := hy₂.2
  have hδ₁ : y₁' • δ = δ := by
    refine hδu _ ?_
    show y₂ • y₁' • δ = y₁' • δ
    rw [← mul_smul, ← hpc.eq, mul_smul, hδ]
  have hδZ : δ ∈ fixSet X Z := fun z hz => hδu _ (by
    show y₂ • z • δ = z • δ
    rw [← mul_smul, ← (Subgroup.mem_centralizer_iff.mp hy₂Z z hz), mul_smul, hδ])
  have hδγ : D.coord δ = D.coord γ₀ := by
    funext j
    rw [hι j]
    have h1 : D.extRho hι u₂ (D.coord δ i₀) = D.coord δ i₀ := by
      rw [← hy₂ρ, D.extRho_coord, hδ]
    obtain ⟨-, c, -, hcu⟩ := D.rho_mem_longInv hu₂ i₀
    rw [← D.extRho_eq_rho hι] at hcu
    exact (hcu _ h1).trans (hcu _ hγ₂).symm
  obtain ⟨⟨g, hg⟩, hgδ⟩ := (D.coord_eq_iff δ γ₀).mp hδγ
  have hOodd : Odd (Nat.card O) := odd_card_jOddCore
  have hON : O.Normal := jOddCore_normal
  obtain ⟨m, hm, hmδ⟩ := exists_mem_centralizer_smul_eq (p := 2)
    (fun h => by rw [Nat.odd_iff] at hOodd; omega) hZ
    (fun x _ => Subgroup.mem_normalizer_iff.mpr fun n =>
      ⟨fun hn => hON.conj_mem n hn x, fun hn => by
        simpa [mul_assoc] using hON.conj_mem _ hn x⁻¹⟩)
    hδZ hγ₀ hg hgδ
  have hmρ : D.extRho hι m = 1 := D.extRho_eq_one_of_mem_jOddCore hι hm.1
  refine ⟨m * y₁' * m⁻¹, m * y₂ * m⁻¹, ⟨conj_mem_longInv hy₁' m, ?_⟩,
    ⟨conj_mem_longInv hy₂ m, ?_⟩, ?_, mul_mem (mul_mem hm.2 hy₁'Z) (inv_mem hm.2),
    mul_mem (mul_mem hm.2 hy₂Z) (inv_mem hm.2), ?_, ?_⟩
  · rw [← hmδ, mul_smul, mul_smul, inv_smul_smul, hδ₁]
  · rw [← hmδ, mul_smul, mul_smul, inv_smul_smul, hδ]
  · rw [show m * y₁' * m⁻¹ * (m * y₂ * m⁻¹) = m * (y₁' * y₂) * m⁻¹ by group, hpc.eq]
    group
  · rw [map_mul, map_mul, map_inv, hmρ, one_mul, inv_one, mul_one, hy₁'ρ]
  · rw [map_mul, map_mul, map_inv, hmρ, one_mul, inv_one, mul_one, hy₂ρ]

end HoltData

end Lifts

section Separation

variable {G : Type} [Group G] {Ω : Type} [Fintype Ω] [MulAction G Ω]

theorem notMem_orbit_jOddCore_of_separation {V X : Subgroup G}
    (hXV : X ≤ Subgroup.centralizer (V : Set G)) (hX : IsPGroup 2 X) {δ₀ δ₁ : fixSet Ω V}
    (hδ₀ : (δ₀ : Ω) ∈ fixSet Ω X) (hδ₁ : (δ₁ : Ω) ∈ fixSet Ω X) {e₁ e₂ : G}
    (he₁ : e₁ ∈ longInvAt G Ω δ₀)
    (he₂ : e₂ ∈ longInvAt G Ω δ₀) (he₁V : e₁ ∈ Subgroup.centralizer (V : Set G))
    (he₂V : e₂ ∈ Subgroup.centralizer (V : Set G)) (he₁X : e₁ ∈ Subgroup.centralizer (X : Set G))
    (he₂X : e₂ ∈ Subgroup.centralizer (X : Set G))
    (hcomm : ∀ ω ∈ fixSet Ω X, ω ∈ fixSet Ω V → e₁ • e₂ • ω = e₂ • e₁ • ω)
    (hmove : e₁ • e₂ • (δ₁ : Ω) ≠ δ₁) :
    δ₁ ∉ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) δ₀ := by
  classical
  intro hmem
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Subgroup.centralizer (V : Set G) →* centralizerImage Ω V :=
    (MulAction.toPermHom (Subgroup.centralizer (V : Set G)) (fixSet Ω V)).rangeRestrict
  set O := jOddCore (centralizerImage Ω V) (fixSet Ω V)
  have hON : O.Normal := jOddCore_normal
  set Xh : Subgroup (centralizerImage Ω V) :=
    (X.subgroupOf (Subgroup.centralizer (V : Set G))).map f
  have hXh : IsPGroup 2 Xh :=
    (hX.comap_of_injective _ (Subgroup.centralizer (V : Set G)).subtype_injective).map f
  have hXfix : ∀ ω : fixSet Ω V, (ω : Ω) ∈ fixSet Ω X → ω ∈ fixSet (fixSet Ω V) Xh := by
    rintro ω hω _ ⟨x, hx, rfl⟩
    exact Subtype.ext (hω x hx)
  obtain ⟨⟨g, hg⟩, hgδ⟩ := hmem
  obtain ⟨m, hm, hmδ⟩ := exists_mem_centralizer_smul_eq (p := 2) (N := O) (S := Xh)
    (fun h => by
      have hO : Odd (Nat.card O) := odd_card_jOddCore
      rw [Nat.odd_iff] at hO
      omega)
    hXh (fun x _ => Subgroup.mem_normalizer_iff.mpr fun n =>
      ⟨fun hn => hON.conj_mem n hn x, fun hn => by simpa [mul_assoc] using hON.conj_mem _ hn x⁻¹⟩)
    (hXfix δ₀ hδ₀) (hXfix δ₁ hδ₁) hg hgδ
  set N' := O ⊓ Subgroup.centralizer (Xh : Set (centralizerImage Ω V)) with hN'
  have hcX : ∀ {c : G} (hc : c ∈ Subgroup.centralizer (V : Set G)),
      c ∈ Subgroup.centralizer (X : Set G) →
        centralizerImageElt (Ω := Ω) hc ∈ Subgroup.centralizer (Xh : Set _) := by
    intro c hc hcX
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    refine Subtype.ext (Equiv.ext fun ω => Subtype.ext ?_)
    change (x : G) • c • (ω : Ω) = c • (x : G) • (ω : Ω)
    rw [← mul_smul, ← mul_smul, Subgroup.mem_centralizer_iff.mp hcX x hx]
  have hnorm : ∀ g ∈ Subgroup.centralizer (Xh : Set (centralizerImage Ω V)),
      g ∈ Subgroup.normalizer (N' : Set (centralizerImage Ω V)) := by
    intro g hg
    have hg' : g⁻¹ ∈ Subgroup.centralizer (Xh : Set (centralizerImage Ω V)) :=
      (Subgroup.centralizer _).inv_mem hg
    have h1 : ∀ k ∈ Subgroup.centralizer (Xh : Set (centralizerImage Ω V)), ∀ n ∈ N',
        k * n * k⁻¹ ∈ N' := fun k hk n hn =>
      ⟨hON.conj_mem n hn.1 k, (Subgroup.centralizer _).mul_mem
        ((Subgroup.centralizer _).mul_mem hk hn.2) ((Subgroup.centralizer _).inv_mem hk)⟩
    refine Subgroup.mem_normalizer_iff.mpr fun n => ⟨h1 g hg n, fun hn => ?_⟩
    simpa [mul_assoc] using h1 _ hg' _ hn
  set 𝔛 := Subgroup.normalizer (N' : Set (centralizerImage Ω V))
  have hNodd : Odd (Nat.card (N'.subgroupOf 𝔛)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv]
    exact Odd.of_dvd_nat odd_card_jOddCore (Subgroup.card_dvd_of_le inf_le_left)
  have : (N'.subgroupOf 𝔛).Normal := Subgroup.normal_in_normalizer
  set x : 𝔛 := ⟨_, hnorm _ (hcX he₁V he₁X)⟩
  set y : 𝔛 := ⟨_, hnorm _ (hcX he₂V he₂X)⟩
  have hxω : ∀ ω : fixSet Ω V, ((x • ω : fixSet Ω V) : Ω) = e₁ • (ω : Ω) := fun _ => rfl
  have hyω : ∀ ω : fixSet Ω V, ((y • ω : fixSet Ω V) : Ω) = e₂ • (ω : Ω) := fun _ => rfl
  have horbX : ∀ δ ∈ orbit (N'.subgroupOf 𝔛) δ₀, (δ : Ω) ∈ fixSet Ω X := by
    rintro _ ⟨n, rfl⟩ z hz
    have hn : ((n : 𝔛) : centralizerImage Ω V) ∈ N' := n.2
    have hzc := Subgroup.mem_centralizer_iff.mp hn.2 (f ⟨z, hXV hz⟩) ⟨⟨z, hXV hz⟩, hz, rfl⟩
    have h1 := congrArg (fun π : centralizerImage Ω V => ((π : Equiv.Perm (fixSet Ω V)) δ₀ : Ω))
      hzc
    have h2 : ((f ⟨z, hXV hz⟩ : centralizerImage Ω V) : Equiv.Perm (fixSet Ω V)) δ₀ = δ₀ :=
      Subtype.ext (hδ₀ z hz)
    calc z • ((n • δ₀ : fixSet Ω V) : Ω)
        = (((f ⟨z, hXV hz⟩ * ((n : 𝔛) : centralizerImage Ω V) : centralizerImage Ω V) :
            Equiv.Perm (fixSet Ω V)) δ₀ : Ω) := rfl
      _ = ((((n : 𝔛) : centralizerImage Ω V) * f ⟨z, hXV hz⟩ : centralizerImage Ω V) :
            Equiv.Perm (fixSet Ω V)) δ₀ := h1
      _ = ((n • δ₀ : fixSet Ω V) : Ω) := by
        change ((((n : 𝔛) : centralizerImage Ω V) : Equiv.Perm (fixSet Ω V))
          (((f ⟨z, hXV hz⟩ : centralizerImage Ω V) : Equiv.Perm (fixSet Ω V)) δ₀) : Ω) = _
        rw [h2]
        rfl
  set B := orbit (N'.subgroupOf 𝔛) δ₀ with hBdef
  have he₁e₁ := mul_self_eq_one_of_mem_longInv he₁.1
  have he₂e₂ := mul_self_eq_one_of_mem_longInv he₂.1
  have hx2 : ∀ δ ∈ B, x • x • δ = δ := fun δ _ => Subtype.ext (by
    rw [hxω, hxω, ← mul_smul, he₁e₁, one_smul])
  have hy2 : ∀ δ ∈ B, y • y • δ = δ := fun δ _ => Subtype.ext (by
    rw [hyω, hyω, ← mul_smul, he₂e₂, one_smul])
  have hxy : ∀ δ ∈ B, x • y • δ = y • x • δ := fun δ hδ => Subtype.ext (by
    rw [hxω, hyω, hyω, hxω]
    exact hcomm _ (horbX δ hδ) δ.2)
  have key := ncard_fixed_orbit_mul hNodd (Subtype.ext he₁.2 : x • δ₀ = δ₀)
    (Subtype.ext he₂.2 : y • δ₀ = δ₀) hx2 hy2 hxy
  rw [← hBdef] at key
  have hfix : ∀ {e : G}, e ∈ longInvAt G Ω δ₀ → ∀ z : 𝔛,
      (∀ ω : fixSet Ω V, ((z • ω : fixSet Ω V) : Ω) = e • (ω : Ω)) →
        {δ | δ ∈ B ∧ z • δ = δ} = {δ₀} := by
    intro e he z hz
    ext δ
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      apply Subtype.ext
      obtain ⟨-, ω, -, hωu⟩ := he.1
      have h1 : e • (δ : Ω) = δ := by rw [← hz]; exact congrArg Subtype.val h
      exact (hωu _ h1).trans (hωu _ he.2).symm
    · intro h
      rw [h]
      exact ⟨mem_orbit_self _, Subtype.ext ((hz δ₀).trans he.2)⟩
  have hboth : {δ | δ ∈ B ∧ x • δ = δ ∧ y • δ = δ} = {δ₀} := by
    refine Set.Subset.antisymm (fun δ h => ?_) ?_
    · have h1 : δ ∈ {δ | δ ∈ B ∧ x • δ = δ} := ⟨h.1, h.2.1⟩
      rwa [hfix he₁ x hxω] at h1
    · rintro _ rfl
      exact ⟨mem_orbit_self _, Subtype.ext he₁.2, Subtype.ext he₂.2⟩
  rw [hfix he₁ x hxω, hfix he₂ y hyω, hboth, Set.ncard_singleton] at key
  simp only [one_pow, one_mul, mul_one] at key
  have hB : {δ | δ ∈ B ∧ x • y • δ = δ} = B :=
    Set.eq_of_subset_of_ncard_le (fun δ h => h.1) key.ge (Set.toFinite _)
  have hδ₁B : δ₁ ∈ B := ⟨⟨⟨m, Subgroup.le_normalizer hm⟩, hm⟩, hmδ⟩
  rw [← hB] at hδ₁B
  exact hmove (by
    have h := congrArg Subtype.val hδ₁B.2
    rwa [hxω, hyω] at h)

end Separation

namespace Box3

open Equiv

variable {ι : Type*} [DecidableEq ι] {Λ : ι → Type*} {Z : Type*}
  [∀ i, Fintype (Λ i)] [∀ i, DecidableEq (Λ i)]

theorem apply_update_eq_of_apply_eq_of_ne (hodd : ∀ i, Odd (Fintype.card (Λ i)))
    (h3 : ∀ i, 3 ≤ Fintype.card (Λ i)) {f : (∀ i, Λ i) → Z}
    (hf : ∀ y : ∀ i, Perm (Λ i), (∀ i, y i ∈ longInv (Perm (Λ i)) (Λ i)) →
      ∀ x x', f x = f x' → f (fun i => y i (x i)) = f (fun i => y i (x' i)))
    {x x' : ∀ i, Λ i} (hxx' : f x = f x') {i : ι} (h5 : 5 ≤ Fintype.card (Λ i))
    (hi : x i ≠ x' i) {μ : Λ i} (hμ : μ ≠ x i) : f (Function.update x' i μ) = f x' := by
  obtain ⟨y, hy, y', hy', hyy'⟩ :=
    CCL.exists_mem_longInvAt_perm_apply_apply_eq (hodd i) h5 (Ne.symm hi) hμ
  obtain ⟨z, hz⟩ := CCL.exists_forall_mem_longInvAt hodd h3 x
  have hJ : ∀ w : Perm (Λ i), w ∈ longInv (Perm (Λ i)) (Λ i) →
      ∀ k, Function.update z i w k ∈ longInv (Perm (Λ k)) (Λ k) := by
    intro w hw k
    by_cases hk : k = i
    · subst hk
      rwa [Function.update_self]
    · rw [Function.update_of_ne hk]
      exact (hz k).1
  have h2 := hf _ (hJ y hy.1) _ _ (hf _ (hJ y' hy'.1) x x' hxx')
  have e1 : (fun k => Function.update z i y k (Function.update z i y' k (x k))) = x := by
    funext k
    by_cases hk : k = i
    · subst hk
      have h1 : y' (x k) = x k := hy'.2
      have h2 : y (x k) = x k := hy.2
      rw [Function.update_self, Function.update_self, h1, h2]
    · rw [Function.update_of_ne hk, Function.update_of_ne hk,
        CCL.apply_apply_of_mem_longInv (hz k).1]
  have e2 : (fun k => Function.update z i y k (Function.update z i y' k (x' k))) =
      Function.update x' i μ := by
    funext k
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self, Function.update_self, Function.update_self, hyy']
    · rw [Function.update_of_ne hk, Function.update_of_ne hk, Function.update_of_ne hk,
        CCL.apply_apply_of_mem_longInv (hz k).1]
  rw [e1, e2] at h2
  rw [← h2, hxx']

theorem apply_update_eq_of_apply_eq (hodd : ∀ i, Odd (Fintype.card (Λ i)))
    (h3 : ∀ i, 3 ≤ Fintype.card (Λ i)) {f : (∀ i, Λ i) → Z}
    (hf : ∀ y : ∀ i, Perm (Λ i), (∀ i, y i ∈ longInv (Perm (Λ i)) (Λ i)) →
      ∀ x x', f x = f x' → f (fun i => y i (x i)) = f (fun i => y i (x' i)))
    {x x' : ∀ i, Λ i} (hxx' : f x = f x') {i : ι} (h5 : 5 ≤ Fintype.card (Λ i))
    (hi : x i ≠ x' i) (μ : Λ i) : f (Function.update x' i μ) = f x' := by
  obtain ⟨μ₀, hμ₀x, hμ₀x'⟩ := CCL.exists_ne_ne_of_three_le (h3 i) (x i) (x' i)
  have h1 := apply_update_eq_of_apply_eq_of_ne hodd h3 hf hxx' h5 hi hμ₀x
  by_cases hμ : μ = x i
  · subst hμ
    have h2 : Function.update x' i μ₀ i ≠ x' i := by rw [Function.update_self]; exact hμ₀x'
    have h3' : x i ≠ Function.update x' i μ₀ i := by rw [Function.update_self]; exact hμ₀x.symm
    exact apply_update_eq_of_apply_eq_of_ne hodd h3 hf h1 h5 h2 h3'
  · exact apply_update_eq_of_apply_eq_of_ne hodd h3 hf hxx' h5 hi hμ

theorem eq_of_mem_coordSupport (hodd : ∀ i, Odd (Fintype.card (Λ i)))
    (h3 : ∀ i, 3 ≤ Fintype.card (Λ i)) {f : (∀ i, Λ i) → Z}
    (hf : ∀ y : ∀ i, Perm (Λ i), (∀ i, y i ∈ longInv (Perm (Λ i)) (Λ i)) →
      ∀ x x', f x = f x' → f (fun i => y i (x i)) = f (fun i => y i (x' i)))
    {j : ι} (h5 : 5 ≤ Fintype.card (Λ j)) (hj : j ∈ CCL.coordSupport f) {x x' : ∀ i, Λ i}
    (hxx' : f x = f x') : x j = x' j := by
  by_contra hne
  obtain ⟨z, μ, hzμ⟩ := hj
  apply hzμ
  choose Y hY hYz using fun k => CCL.exists_mem_longInv_perm_apply_eq_of_odd (hodd k) (h3 k)
    (x' k) (z k)
  have h := hf Y hY _ x' (apply_update_eq_of_apply_eq hodd h3 hf hxx' h5 hne (Y j μ))
  have e1 : (fun k => Y k (Function.update x' j (Y j μ) k)) = Function.update z j μ := by
    funext k
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self, Function.update_self, CCL.apply_apply_of_mem_longInv (hY k)]
    · rw [Function.update_of_ne hk, Function.update_of_ne hk, hYz k]
  rwa [e1, show (fun k => Y k (x' k)) = z from funext hYz] at h

end Box3

section CCLBox3

variable (G : Type*) [Group G] {Ω : Type*} [MulAction G Ω] {ι' : Type*}
  (Λc : ι' → Type*) [∀ i, Fintype (Λc i)]

structure CCLBox3 (ε : (∀ i, Λc i) → Ω) (α β : Ω) : Prop where
  injective : Function.Injective ε
  range_eq : Set.range ε = holtDelta G Ω α β
  three_le : ∀ i, 3 ≤ Fintype.card (Λc i)
  smul_eq : ∀ c ∈ longInvSwap G Ω α β, ∃ y : ∀ i, Equiv.Perm (Λc i),
    (∀ i, y i ∈ longInv (Equiv.Perm (Λc i)) (Λc i)) ∧ ∀ x, c • ε x = ε fun i => y i (x i)
  exists_smul_eq : ∀ y : ∀ i, Equiv.Perm (Λc i),
    (∀ i, y i ∈ longInv (Equiv.Perm (Λc i)) (Λc i)) →
      ∃ c ∈ longInvSwap G Ω α β, ∀ x, c • ε x = ε fun i => y i (x i)

namespace CCLBox3

variable {G Λc} {ε : (∀ i, Λc i) → Ω} {α β : Ω}

theorem mem_holtDelta (hbox : CCLBox3 G Λc ε α β) (x : ∀ i, Λc i) :
    ε x ∈ holtDelta G Ω α β :=
  hbox.range_eq ▸ ⟨x, rfl⟩

theorem nonempty (hbox : CCLBox3 G Λc ε α β) : Nonempty (∀ i, Λc i) :=
  ⟨fun i => Classical.choice (Fintype.card_pos_iff.mp (by have := hbox.three_le i; omega))⟩

theorem odd_card [∀ i, DecidableEq (Λc i)] (hbox : CCLBox3 G Λc ε α β) (i : ι') :
    Odd (Fintype.card (Λc i)) := by
  obtain ⟨x⟩ := hbox.nonempty
  obtain ⟨c, hc, -⟩ := hbox.mem_holtDelta x
  obtain ⟨y, hy, -⟩ := hbox.smul_eq c hc
  exact odd_card_of_mem_longInv_perm (hy i)

theorem eq_of_mem_orbit [Finite G] [DecidableEq ι'] [∀ i, DecidableEq (Λc i)]
    (hG : IsStarGroup G Ω) (hbox : CCLBox3 G Λc ε α β) {x x' : ∀ i, Λc i}
    (h : ε x' ∈ orbit (jOddCore G Ω) (ε x)) {i : ι'} (h5 : 5 ≤ Fintype.card (Λc i)) :
    x i = x' i := by
  by_contra hi
  have hodd := hbox.odd_card
  obtain ⟨y, hy, y', hy', hww, hw⟩ :=
    CCL.exists_mem_longInvAt_perm_mul_mul_self_eq_one (hodd i) h5 (Ne.symm hi)
  obtain ⟨z, hz⟩ := CCL.exists_forall_mem_longInvAt hodd hbox.three_le x
  have hJ := fun w (hw : w ∈ longInvAt (Equiv.Perm (Λc i)) (Λc i) (x i)) =>
    CCL.update_mem_longInvAt hz hw
  obtain ⟨c, hc, hcε⟩ := hbox.exists_smul_eq _ fun k => (hJ y hy k).1
  obtain ⟨c', hc', hc'ε⟩ := hbox.exists_smul_eq _ fun k => (hJ y' hy' k).1
  have hcx : c • ε x = ε x := by
    rw [hcε, CCL.apply_eq_self_of_forall_mem_longInvAt (hJ y hy)]
  have hc'x : c' • ε x = ε x := by
    rw [hc'ε, CCL.apply_eq_self_of_forall_mem_longInvAt (hJ y' hy')]
  obtain ⟨m, hm, hmB⟩ := exists_odd_pow_smul_eq_of_mem_longInvAt hG ⟨hc'.1, hc'x⟩ ⟨hc.1, hcx⟩
  have h1 := hmB _ h
  rw [CCL.pow_smul_eq_of_forall_smul_eq (CCL.mul_smul_eq_of_forall_smul_eq hcε hc'ε)] at h1
  have h2 := congrFun (hbox.injective h1) i
  simp only [Function.update_self] at h2
  obtain ⟨r, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, hww, one_pow, one_mul] at h2
  exact hw h2

theorem of_equiv {e : holtDelta G Ω α β ≃ ∀ i, Λc i} (h3 : ∀ i, 3 ≤ Fintype.card (Λc i))
    (hcoord : ∀ c ∈ longInvSwap G Ω α β, ∃ y : ∀ i, Equiv.Perm (Λc i),
      (∀ i, y i ∈ longInv (Equiv.Perm (Λc i)) (Λc i)) ∧ ∀ δ δ' : holtDelta G Ω α β,
        (δ' : Ω) = c • (δ : Ω) → e δ' = fun i => y i (e δ i))
    (hreal : ∀ y : ∀ i, Equiv.Perm (Λc i), (∀ i, y i ∈ longInv (Equiv.Perm (Λc i)) (Λc i)) →
      ∃ c ∈ longInvSwap G Ω α β, ∀ δ : holtDelta G Ω α β, ∀ δ' : holtDelta G Ω α β,
        (δ' : Ω) = c • (δ : Ω) → e δ' = fun i => y i (e δ i)) :
    CCLBox3 G Λc (fun x => (e.symm x : Ω)) α β := by
  have key : ∀ c ∈ longInvSwap G Ω α β, ∀ y : ∀ i, Equiv.Perm (Λc i),
      (∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = c • (δ : Ω) → e δ' = fun i => y i (e δ i)) →
        ∀ x, c • (e.symm x : Ω) = (e.symm fun i => y i (x i) : Ω) := by
    intro c hc y hy x
    have hmem : c • (e.symm x : Ω) ∈ holtDelta G Ω α β := by
      have h := mem_stabilizer_iff.mp (mem_stabilizer_holtDelta_of_mem_longInvSwap hc)
      have h1 : c • (e.symm x : Ω) ∈ c • holtDelta G Ω α β :=
        Set.smul_mem_smul_set (e.symm x).2
      rwa [h] at h1
    have h1 := hy (e.symm x) ⟨_, hmem⟩ rfl
    rw [e.apply_symm_apply] at h1
    exact congrArg Subtype.val (e.eq_symm_apply.mpr h1)
  refine ⟨fun x x' h => e.symm.injective (Subtype.ext h), ?_, h3, fun c hc => ?_,
    fun y hy => ?_⟩
  · ext ω
    refine ⟨?_, fun hω => ⟨e ⟨ω, hω⟩, by simp⟩⟩
    rintro ⟨x, rfl⟩
    exact (e.symm x).2
  · obtain ⟨y, hy, hyc⟩ := hcoord c hc
    exact ⟨y, hy, key c hc y hyc⟩
  · obtain ⟨c, hc, hcy⟩ := hreal y hy
    exact ⟨c, hc, key c hc y hcy⟩

end CCLBox3

end CCLBox3

namespace HoltData

section Match3

variable {K : Type*} [Group K] [Finite K] {X : Type*} [MulAction K X] (D : HoltData K X)
  {ι' : Type*} [DecidableEq ι'] {Λc : ι' → Type*} [∀ i, Fintype (Λc i)]
  [∀ i, DecidableEq (Λc i)] {ε : (∀ i, Λc i) → X} {α β : X}

omit [Finite K] in
theorem eq_of_coord_box_eq (hbox : CCLBox3 K Λc ε α β) (j : D.ι) {i : ι'}
    (h5 : 5 ≤ Fintype.card (Λc i)) (hi : i ∈ D.boxSupport ε j) {x x' : ∀ i, Λc i}
    (h : D.coord (ε x) j = D.coord (ε x') j) : x i = x' i := by
  refine Box3.eq_of_mem_coordSupport (f := fun x => D.coord (ε x) j) hbox.odd_card
    hbox.three_le ?_ h5 hi h
  intro y hy z z' hzz
  obtain ⟨c, hc, hcε⟩ := hbox.exists_smul_eq y hy
  have hcε' : ∀ x, ((⟨c, mem_jHull_of_mem_longInv hc.1⟩ : jHull K X) : K) • ε x =
      ε fun i => y i (x i) := hcε
  change D.coord (ε fun i => y i (z i)) j = D.coord (ε fun i => y i (z' i)) j
  rw [D.coord_box_smul hcε', D.coord_box_smul hcε']
  exact congrArg _ hzz

omit [∀ i, DecidableEq (Λc i)] in
theorem coord_ne_of_mem_boxSupport (hbox : CCLBox3 K Λc ε α β) {j : D.ι} {i : ι'}
    (hi : i ∈ D.boxSupport ε j) : D.coord α j ≠ D.coord β j := by
  intro hab
  obtain ⟨x, μ, hne⟩ := hi
  have h1 : ∀ x, D.coord (ε x) j = D.coord α j := fun x => by
    have h := D.coord_mem_holtDelta (hbox.mem_holtDelta x) j
    rw [← hab, D.holtDelta_range_rho_self] at h
    exact h
  exact hne ((h1 _).trans (h1 x).symm)

omit [DecidableEq ι'] [∀ i, DecidableEq (Λc i)] in
theorem coord_box_ne_right (hbox : CCLBox3 K Λc ε α β) {j : D.ι}
    (hab : D.coord α j ≠ D.coord β j) (x : ∀ i, Λc i) : D.coord (ε x) j ≠ D.coord β j := by
  intro h
  obtain ⟨w, ⟨-, hwJ, hwa⟩, hwc⟩ := mem_holtDelta_subgroup_perm_iff.mp
    (D.coord_mem_holtDelta (hbox.mem_holtDelta x) j)
  rw [h] at hwc
  have h1 := CCL.apply_apply_of_mem_longInv hwJ (D.coord α j)
  rw [hwa, hwc] at h1
  exact hab h1.symm

theorem notMem_boxSupport_of_isNaturalSE
    (hbox : CCLBox3 K Λc ε α β) {j : D.ι}
    (hSE : IsNaturalSE (D.M j)) (hab : D.coord α j ≠ D.coord β j) {i : ι'}
    (h5 : 5 ≤ Fintype.card (Λc i)) : i ∉ D.boxSupport ε j := by
  intro hi
  obtain ⟨x⟩ := hbox.nonempty
  have hodd := hbox.odd_card
  obtain ⟨μ, hμ, -⟩ := CCL.exists_ne_ne_of_three_le (hbox.three_le i) (x i) (x i)
  obtain ⟨y, hy, y', hy', -, hw⟩ :=
    CCL.exists_mem_longInvAt_perm_mul_mul_self_eq_one (hodd i) h5 hμ
  obtain ⟨z, hz⟩ := CCL.exists_forall_mem_longInvAt hodd hbox.three_le x
  obtain ⟨c, hc, hcε⟩ := hbox.exists_smul_eq _ fun k => (CCL.update_mem_longInvAt hz hy k).1
  obtain ⟨c', hc', hc'ε⟩ := hbox.exists_smul_eq _ fun k => (CCL.update_mem_longInvAt hz hy' k).1
  set u : jHull K X := ⟨c, mem_jHull_of_mem_longInv hc.1⟩
  set u' : jHull K X := ⟨c', mem_jHull_of_mem_longInv hc'.1⟩
  have huε : ∀ x, (u : K) • ε x = ε fun k => Function.update z i y k (x k) := hcε
  have hu'ε : ∀ x, (u' : K) • ε x = ε fun k => Function.update z i y' k (x k) := hc'ε
  have hP : D.ρ j u (D.coord (ε x) j) = D.coord (ε x) j := by
    rw [← D.coord_box_smul huε, CCL.apply_eq_self_of_forall_mem_longInvAt
      (CCL.update_mem_longInvAt hz hy)]
  have hP' : D.ρ j u' (D.coord (ε x) j) = D.coord (ε x) j := by
    rw [← D.coord_box_smul hu'ε, CCL.apply_eq_self_of_forall_mem_longInvAt
      (CCL.update_mem_longInvAt hz hy')]
  have hs := D.rho_mem_swapSet (u := u) hc j
  have hs' := D.rho_mem_swapSet (u := u') hc' j
  have hrange := D.range_rho_of_not_isOuterFactor hSE.not_isOuterFactor
  have haP : D.coord α j ≠ D.coord (ε x) j := by
    intro h
    have h1 := hs.2.2
    rw [h, hP, ← h] at h1
    exact hab h1
  have heq : D.ρ j u = D.ρ j u' := hSE.eq_of_mem_longInvAt_of_apply_eq (hrange ▸ hs.1)
    (hrange ▸ hs'.1) ⟨hs.2.1, hP⟩ ⟨hs'.2.1, hP'⟩ haP (by rw [hs.2.2, hs'.2.2])
  have key : ∀ q : Λc i, y q = y' q := by
    intro q
    have h1 : D.coord (ε fun k => Function.update z i y k (Function.update x i q k)) j =
        D.coord (ε fun k => Function.update z i y' k (Function.update x i q k)) j := by
      rw [D.coord_box_smul huε, D.coord_box_smul hu'ε, heq]
    have h2 := D.eq_of_coord_box_eq hbox j h5 hi h1
    simpa using h2
  apply hw
  rw [Equiv.Perm.mul_apply, key (y' μ), CCL.apply_apply_of_mem_longInv hy'.1]

omit [DecidableEq ι'] [∀ i, DecidableEq (Λc i)] in
theorem exists_box3_of_forall_mem_swapSet
    (hbox : CCLBox3 K Λc ε α β) (w : ∀ l, Equiv.Perm (D.Ψc l))
    (hw : ∀ l, w l ∈ swapSet (D.ρ l).range (D.coord α l) (D.coord β l)) :
    ∃ Y : ∀ i, Equiv.Perm (Λc i), (∀ i, Y i ∈ longInv (Equiv.Perm (Λc i)) (Λc i)) ∧
      ∀ x l, D.coord (ε fun i => Y i (x i)) l = w l (D.coord (ε x) l) := by
  obtain ⟨u, hu, hρ⟩ := D.exists_mem_longInvSwap_rho_eq w (fun l => (hw l).1)
    (fun l => (hw l).2.1) fun l => (hw l).2.2
  obtain ⟨Y, hY, hYε⟩ := hbox.smul_eq u hu
  exact ⟨Y, hY, fun x l => by rw [D.coord_box_smul hYε, hρ]⟩

theorem eq_of_mem_boxSupport_of_alternatingGroup
    (hbox : CCLBox3 K Λc ε α β) {j : D.ι} (hA : D.M j = alternatingGroup (D.Ψc j))
    (hab : D.coord α j ≠ D.coord β j) {i i' : ι'} (h5 : 5 ≤ Fintype.card (Λc i))
    (hi : i ∈ D.boxSupport ε j) (hi' : i' ∈ D.boxSupport ε j) : i' = i := by
  by_contra hne
  obtain ⟨x, ν, hxν⟩ := hi'
  obtain ⟨μ, hμ, -⟩ := CCL.exists_ne_ne_of_three_le (hbox.three_le i) (x i) (x i)
  have hchar := fun z z' (h : D.coord (ε z) j = D.coord (ε z') j) =>
    D.eq_of_coord_box_eq hbox j h5 hi h
  have hX : ∀ z, D.coord (ε z) j ≠ D.coord α j ∧ D.coord (ε z) j ≠ D.coord β j := by
    intro z
    have h := D.coord_mem_holtDelta (hbox.mem_holtDelta z) j
    rw [D.holtDelta_range_rho_eq_compl hA hab] at h
    simpa [not_or] using h
  have hRP : D.coord (ε x) j ≠ D.coord (ε (Function.update x i' ν)) j := fun h => hxν h.symm
  have hRQ : D.coord (ε x) j ≠ D.coord (ε (Function.update x i μ)) j := fun h => by
    have h1 := hchar _ _ h
    rw [Function.update_self] at h1
    exact hμ h1.symm
  have hPQ : D.coord (ε (Function.update x i' ν)) j ≠
      D.coord (ε (Function.update x i μ)) j := fun h => by
    have h1 := hchar _ _ h
    rw [Function.update_of_ne (Ne.symm hne), Function.update_self] at h1
    exact hμ h1.symm
  obtain ⟨w, hw, hwa, hwP⟩ := exists_mem_longInvAt_perm_apply_eq_apply_eq (D.odd_card_Ψc j)
    hab (hX x).1.symm (hX _).1.symm (hX _).1.symm (hX x).2.symm (hX _).2.symm (hX _).2.symm
    hRP hRQ hPQ
  have hAle : alternatingGroup (D.Ψc j) ≤ (D.ρ j).range := by
    rw [← hA]
    exact Subgroup.map_le_range _ _
  have hwN : w ∈ (D.ρ j).range := longInv_perm_subset_of_alternatingGroup_le hAle
    ⟨D.tHull, rfl⟩ (D.rho_mem_longInv D.t_mem j) hw.1
  obtain ⟨t, ht, -⟩ := hbox.mem_holtDelta x
  have hws : ∀ l, Function.update (fun l => D.ρ l ⟨t, mem_jHull_of_mem_longInv ht.1⟩) j w l ∈
      swapSet (D.ρ l).range (D.coord α l) (D.coord β l) := by
    intro l
    by_cases hl : l = j
    · subst hl
      rw [Function.update_self]
      exact ⟨hwN, hw.1, hwa⟩
    · rw [Function.update_of_ne hl]
      exact D.rho_mem_swapSet ht l
  obtain ⟨Y, -, hY⟩ := D.exists_box3_of_forall_mem_swapSet hbox _ hws
  have h1 : D.coord (ε fun k => Y k (x k)) j = D.coord (ε x) j := by
    rw [hY, Function.update_self]
    exact hw.2
  have h2 : D.coord (ε fun k => Y k (Function.update x i' ν k)) j =
      D.coord (ε (Function.update x i μ)) j := by
    rw [hY, Function.update_self, hwP]
  have h3 := hchar _ _ h1
  have h4 := hchar _ _ h2
  simp only [Function.update_of_ne (Ne.symm hne), Function.update_self] at h3 h4
  exact hμ (h4.symm.trans h3)

theorem exists_mem_boxSupport_of_five_le (hK : IsStarGroup K X) (hbox : CCLBox3 K Λc ε α β)
    {i : ι'} (h5 : 5 ≤ Fintype.card (Λc i)) : ∃ j, i ∈ D.boxSupport ε j := by
  by_contra h
  obtain ⟨x⟩ := hbox.nonempty
  obtain ⟨μ, hμ, -⟩ := CCL.exists_ne_ne_of_three_le (hbox.three_le i) (x i) (x i)
  have hc : D.coord (ε x) = D.coord (ε (Function.update x i μ)) := funext fun j =>
    (CCL.apply_update_eq_of_notMem_coordSupport (not_exists.mp h j) x μ).symm
  have h1 := hbox.eq_of_mem_orbit hK ((D.coord_eq_iff _ _).mp hc) h5
  rw [Function.update_self] at h1
  exact hμ h1.symm

theorem eq_of_mem_boxSupport_of_five_le
    (hbox : CCLBox3 K Λc ε α β) {j : D.ι} {i i' : ι'} (h5 : 5 ≤ Fintype.card (Λc i))
    (hi : i ∈ D.boxSupport ε j) (hi' : i' ∈ D.boxSupport ε j) : i' = i := by
  have hab := D.coord_ne_of_mem_boxSupport hbox hi
  rcases D.factor j with ⟨hA, -⟩ | hSE
  · exact D.eq_of_mem_boxSupport_of_alternatingGroup hbox hA hab h5 hi hi'
  · exact absurd hi (D.notMem_boxSupport_of_isNaturalSE hbox hSE hab h5)

end Match3

end HoltData

end CFSG.Holt.H78
