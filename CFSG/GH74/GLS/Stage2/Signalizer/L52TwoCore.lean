module

public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoMain
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoOdd
public import CFSG.GH74.GLS.Stage2.Local.P27.S45L4Cls
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Bg
open scoped commutatorElement

variable {G : Type} [Group G]

theorem UData.mem_U4 {z t : G} (hu : UData z t) {x : G} (hx : x ∈ U4 z t) :
    x = 1 ∨ x = z ∨ x = t ∨ x = z * t :=
  P27.S45.mem_sup_two_invol hu.z_sq hu.t_sq hu.comm hx

theorem UData.sq_U4 {z t : G} (hu : UData z t) : ∀ x ∈ U4 z t, x * x = 1 := by
  intro x hx
  rcases hu.mem_U4 hx with rfl | rfl | rfl | rfl
  · simp
  · exact hu.z_sq
  · exact hu.t_sq
  · calc z * t * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [hu.comm]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [hu.z_sq, hu.t_sq, one_mul]

theorem UData.comm_U4 {z t : G} (hu : UData z t) : ∀ a ∈ U4 z t, ∀ b ∈ U4 z t, a * b = b * a := by
  intro a ha b hb
  have hc : Commute z t := hu.comm
  rcases hu.mem_U4 ha with rfl | rfl | rfl | rfl <;> rcases hu.mem_U4 hb with rfl | rfl | rfl | rfl
  all_goals first
    | simp
    | exact hu.comm
    | exact hu.comm.symm
    | exact ((Commute.refl _).mul_right hc).eq
    | exact ((Commute.refl _).mul_right hc).eq.symm
    | exact (hc.symm.mul_right (Commute.refl _)).eq
    | exact (hc.symm.mul_right (Commute.refl _)).eq.symm

theorem UData.isPGroup_U4 {z t : G} (hu : UData z t) : IsPGroup 2 ↥(U4 z t) := by
  intro g
  exact ⟨1, by
    have := hu.sq_U4 g.1 g.2
    apply Subtype.ext
    simpa [pow_two] using this⟩


omit [Group G] in
theorem exists_ne_one_mem_center_of_normal {M : Type*} [Group M] {T X : Subgroup M} (hT : IsPGroup 2 ↥T)
    (hXT : X ≤ T) (hXn : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) (hX : X ≠ ⊥) [Finite M] :
    ∃ x ∈ X, x ≠ 1 ∧ ∀ t ∈ T, t * x = x * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  let X' : Subgroup ↥T := X.subgroupOf T
  have hX'n : X'.Normal := ⟨fun x hx t => by
    show ((t * x * t⁻¹ : ↥T) : M) ∈ X
    have : ((t * x * t⁻¹ : ↥T) : M) = (t : M) * (x : M) * (t : M)⁻¹ := rfl
    rw [this]
    exact hXn t t.2 x hx⟩
  have hX'ne : X' ≠ ⊥ := by
    intro h
    apply hX
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hXT hx⟩ : ↥T) ∈ X' := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hX'ne
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hzX : ((z : ↥T) : M) ∈ X := (Subgroup.mem_inf.1 z.2).1
  have hzc := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 z.2).2
  refine ⟨((z : ↥T) : M), hzX, fun h => hz1 (Subtype.ext (Subtype.ext h)), fun t ht => ?_⟩
  exact congrArg Subtype.val (hzc ⟨t, ht⟩)


section Core

variable [Finite G]

theorem dbar_core {z t : G} (hu : UData z t) {H P I₁ : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hzH : z ∈ H) (htH : t ∈ H) (hPp : IsPGroup p ↥P)
    (hUP : ∀ u ∈ U4 z t, u ∈ normalizer (P : Set G)) (hI : GoodI1 H (U4 z t) I₁)
    (hcent : ∀ W : Subgroup (HBar H), IsPGroup 2 ↥W →
      W ≤ centralizer ((barIn H I₁ : Subgroup (HBar H)) : Set (HBar H)) →
      barIn H (U4 z t) ≤ W →
      W ⊓ centralizer ((barIn H (U4 z t) : Subgroup (HBar H)) : Set (HBar H)) ≤ barIn H (U4 z t))
    (hcd : ∀ W : Subgroup (HBar H), IsPGroup 2 ↥W → barIn H (U4 z t) ≤ W →
      W ⊓ centralizer ((barIn H (U4 z t) : Subgroup (HBar H)) : Set (HBar H)) ≤ barIn H (U4 z t) →
      IsCyclic ↥W ∨ IsDihedral ↥W) :
    DBar H P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hUH : U4 z t ≤ H := sup_le ((zpowers_le).2 hzH) ((zpowers_le).2 htH)
  let π : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H)
  have hU2 : IsPGroup 2 ↥(U4 z t) := hu.isPGroup_U4
  have hUb2 : IsPGroup 2 ↥(barIn H (U4 z t)) := (hU2.comap_subtype).map π
  have hDn : (pCore 2 (HBar H)).Normal := CFSG.pCore_normal
  have hD2 : IsPGroup 2 ↥(pCore 2 (HBar H)) := CFSG.pCore_isPGroup
  have hO : pPrimeCore 2 (HBar H) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hFD : fittingSubgroup (HBar H) = pCore 2 (HBar H) := Fitting_eq_pcore (HBar H) 2 hO
  have hDC : pCore 2 (HBar H) ≤ centralizer ((barIn H I₁ : Subgroup (HBar H)) : Set (HBar H)) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    have hdF : d ∈ fittingSubgroup (HBar H) := by rw [hFD]; exact hd
    have h1 : ⁅d, i⁆ ∈ ⁅fittingSubgroup (HBar H), layer (HBar H)⁆ :=
      Subgroup.commutator_mem_commutator hdF (hI.layer hi)
    rw [LocalCores.fitting_layer_commute, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hUC : barIn H (U4 z t) ≤ centralizer ((barIn H I₁ : Subgroup (HBar H)) : Set (HBar H)) := by
    rintro _ ⟨u', hu', rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨i', hi', rfl⟩
    have h1 := hI.comm (i' : G) hi' (u' : G) hu'
    show π i' * π u' = π u' * π i'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h1.symm
  set C' : Subgroup (HBar H) := centralizer ((barIn H I₁ : Subgroup (HBar H)) : Set (HBar H)) with hC'
  have hVC : pCore 2 (HBar H) ⊔ barIn H (U4 z t) ≤ C' := sup_le hDC hUC
  have hV2 : IsPGroup 2 ↥(pCore 2 (HBar H) ⊔ barIn H (U4 z t)) :=
    IsPGroup.to_sup_of_normal_left' hD2 hUb2 (Subgroup.le_normalizer_of_normal)
  have hV2' : IsPGroup 2 ↥((pCore 2 (HBar H) ⊔ barIn H (U4 z t)).subgroupOf C') := hV2.comap_subtype
  obtain ⟨Q, hQ⟩ := hV2'.exists_le_sylow
  set W : Subgroup (HBar H) := (Q : Subgroup ↥C').map C'.subtype with hW
  have hW2 : IsPGroup 2 ↥W := Q.isPGroup'.map C'.subtype
  have hWC : W ≤ C' := Subgroup.map_subtype_le _
  have hVW : pCore 2 (HBar H) ⊔ barIn H (U4 z t) ≤ W := by
    intro x hx
    exact ⟨⟨x, hVC hx⟩, hQ hx, rfl⟩
  have hDW : pCore 2 (HBar H) ≤ W := le_sup_left.trans hVW
  have hUW : barIn H (U4 z t) ≤ W := le_sup_right.trans hVW
  have hcW := hcent W hW2 hWC hUW
  have hWcd := hcd W hW2 hUW hcW
  intro D hD g hg
  have hgP : (g : G) ∈ P := hg
  obtain ⟨n, hn⟩ := (hPp.comap_subtype) ⟨g, hg⟩
  have hn' : g ^ (p ^ n) = 1 := by
    have h2 := congrArg (fun y : ↥(P.subgroupOf H) => (y : ↥H)) hn
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  have hgm : (π g) ^ (p ^ n) = 1 := by rw [← map_pow, hn', map_one]
  have hfix : IsKleinFour ↥(pCore 2 (HBar H)) →
      ∃ u ∈ pCore 2 (HBar H), u ≠ 1 ∧ π g * u * (π g)⁻¹ = u := by
    intro hK
    have hne : pCore 2 (HBar H) ≠ ⊥ := by
      intro h
      have h4 := hK.card_four
      rw [h, Subgroup.card_bot] at h4
      omega
    obtain ⟨u, hu, hu1, huW⟩ := exists_ne_one_mem_center_of_normal hW2 hDW
      (fun t' _ x hx => hDn.conj_mem x hx t') hne
    have huUb : u ∈ barIn H (U4 z t) := by
      apply hcW
      exact Subgroup.mem_inf.2 ⟨hDW hu, Subgroup.mem_centralizer_iff.2 (fun y hy => huW y (hUW hy))⟩
    obtain ⟨τ, hτ, rfl⟩ := huUb
    refine ⟨π τ, hu, hu1, ?_⟩
    have hτU : (τ : G) ∈ U4 z t := hτ
    set c : ↥H := τ * g * τ⁻¹ * g⁻¹ with hc
    have hcP : c ∈ P.subgroupOf H := by
      show (τ : G) * (g : G) * (τ : G)⁻¹ * (g : G)⁻¹ ∈ P
      exact P.mul_mem ((Subgroup.mem_normalizer_iff.1 (hUP τ hτU) g).1 hgP) (P.inv_mem hgP)
    have hcD : π c ∈ pCore 2 (HBar H) := by
      have h1 : π g * (π τ)⁻¹ * (π g)⁻¹ ∈ pCore 2 (HBar H) :=
        hDn.conj_mem _ ((pCore 2 (HBar H)).inv_mem hu) (π g)
      have : π c = π τ * (π g * (π τ)⁻¹ * (π g)⁻¹) := by
        simp only [hc, map_mul, map_inv]; group
      rw [this]
      exact (pCore 2 (HBar H)).mul_mem hu h1
    have hPb : IsPGroup p ↥((P.subgroupOf H).map π) := (hPp.comap_subtype).map π
    have hcPb : π c ∈ (P.subgroupOf H).map π := ⟨c, hcP, rfl⟩
    have hc1 : π c = 1 := by
      obtain ⟨n', hn1⟩ := hPb ⟨π c, hcPb⟩
      obtain ⟨m', hm1⟩ := hD2 ⟨π c, hcD⟩
      have hn1' : (π c) ^ (p ^ n') = 1 := by simpa using congrArg Subtype.val hn1
      have hm1' : (π c) ^ (2 ^ m') = 1 := by simpa using congrArg Subtype.val hm1
      have hcop : Nat.Coprime (p ^ n') (2 ^ m') :=
        Nat.Coprime.pow n' m' ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      have := (pow_gcd_eq_one (a := π c)).mpr ⟨hn1', hm1'⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    have h2 : π τ * π g * (π τ)⁻¹ * (π g)⁻¹ = 1 := by
      have := hc1
      simpa only [hc, map_mul, map_inv] using this
    have h3 : π τ * π g = π g * π τ := by
      calc π τ * π g = (π τ * π g * (π τ)⁻¹ * (π g)⁻¹) * (π g * π τ) := by group
        _ = π g * π τ := by rw [h2, one_mul]
    rw [← h3]
    group
  have hall := odd_centralizes hW2 hWcd hDW hpodd.pow hgm hfix
  exact (mul_inv_eq_iff_eq_mul.1 (hall D hD)).symm

end Core

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
