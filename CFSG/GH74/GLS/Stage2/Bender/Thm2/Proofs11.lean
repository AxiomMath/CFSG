module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Conj
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Elem

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Elem

variable {G : Type} [Group G]

theorem inverts_of_fpf [Finite G] {t : G} (ht : t * t = 1) {A : Subgroup G}
    (hn : t ∈ normalizer (A : Set G)) (hfix : ∀ x ∈ A, t * x * t⁻¹ = x → x = 1) :
    ∀ x ∈ A, t * x * t⁻¹ = x⁻¹ := by
  let c : ↥A → ↥A := fun x => ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp hn x).mp x.2⟩
  let f : ↥A → ↥A := fun x => x⁻¹ * c x
  have hinj : Function.Injective f := by
    intro x y hxy
    have h : (x : G)⁻¹ * (t * x * t⁻¹) = (y : G)⁻¹ * (t * y * t⁻¹) := congrArg Subtype.val hxy
    have hY : t * (y : G) * t⁻¹ = (y : G) * ((x : G)⁻¹ * (t * x * t⁻¹)) := by
      rw [h]
      group
    have hfixed : t * ((y : G) * (x : G)⁻¹) * t⁻¹ = (y : G) * (x : G)⁻¹ := by
      calc t * ((y : G) * (x : G)⁻¹) * t⁻¹ = (t * y * t⁻¹) * (t * x * t⁻¹)⁻¹ := by group
        _ = (y : G) * ((x : G)⁻¹ * (t * x * t⁻¹)) * (t * x * t⁻¹)⁻¹ := by rw [hY]
        _ = (y : G) * (x : G)⁻¹ := by group
    have h1 := hfix _ (mul_mem y.2 (inv_mem x.2)) hfixed
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  intro a ha
  obtain ⟨x, hx⟩ := hsurj ⟨a, ha⟩
  have hxa : (x : G)⁻¹ * (t * x * t⁻¹) = a := congrArg Subtype.val hx
  have hconj := conj_conj_of_mul_self ht (x : G)
  rw [← hxa]
  calc t * ((x : G)⁻¹ * (t * x * t⁻¹)) * t⁻¹ = (t * x * t⁻¹)⁻¹ * (t * (t * x * t⁻¹) * t⁻¹) := by group
    _ = (t * x * t⁻¹)⁻¹ * x := by rw [hconj]
    _ = ((x : G)⁻¹ * (t * x * t⁻¹))⁻¹ := by group

theorem eq_one_of_mul_self_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup G} (hA : IsPGroup p ↥A)
    {a : G} (ha : a ∈ A) (h : a * a = 1) : a = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hA ⟨a, ha⟩
  rw [Subgroup.orderOf_mk] at hn
  have hd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have hcop : Nat.Coprime p (orderOf a) :=
    Nat.Coprime.coprime_dvd_right hd ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact eq_one_of_coprime_pow hp hn hcop

theorem eq_one_of_inverts_fixed {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup G} (hA : IsPGroup p ↥A)
    {t x : G} (hx : x ∈ A) (hinv : t * x * t⁻¹ = x⁻¹) (hfix : t * x * t⁻¹ = x) : x = 1 :=
  eq_one_of_mul_self_eq_one hp hp2 hA hx (mul_eq_one_iff_eq_inv.mpr (hfix.symm.trans hinv))

theorem le_Op_of_normal {p : ℕ} {L X : Subgroup G} (hXL : X ≤ L) (hn : L ≤ normalizer (X : Set G))
    (hX : IsPGroup p ↥X) : X ≤ Op p L := by
  have hnorm : (X.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXL).mpr hn
  have hpg : IsPGroup p ↥(X.subgroupOf L) :=
    hX.of_injective (Subgroup.subgroupOfEquivOfLe hXL).toMonoidHom (Subgroup.subgroupOfEquivOfLe hXL).injective
  have h1 : X.subgroupOf L ≤ pCore p ↥L := le_sSup ⟨hnorm, hpg⟩
  have h2 : (X.subgroupOf L).map L.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXL
  rw [← h2]
  exact Subgroup.map_mono h1

theorem mem_commutator_of_inverts {z a : G} (h : z * a * z⁻¹ = a⁻¹) (hodd : Odd (orderOf a))
    {A : Subgroup G} (haA : a ∈ A) : a ∈ ⁅A, zpowers z⁆ := by
  have hcomm : ⁅a, z⁆ = a * a := by
    have h1 : z * a⁻¹ * z⁻¹ = a := by
      calc z * a⁻¹ * z⁻¹ = (z * a * z⁻¹)⁻¹ := by group
        _ = a := by rw [h, inv_inv]
    calc ⁅a, z⁆ = a * (z * a⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
      _ = a * a := by rw [h1]
  have h1 : a * a ∈ ⁅A, zpowers z⁆ := by
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator haA (mem_zpowers z)
  obtain ⟨m, hm⟩ := hodd
  have hpow : a ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one a
  have hbm : a = (a * a) ^ (m + 1) := by
    calc a = a ^ (2 * m + 1) * a := by rw [hpow, one_mul]
      _ = (a * a) ^ (m + 1) := by rw [← pow_succ, ← pow_two, ← pow_mul]; ring_nf
  have h2 := Subgroup.pow_mem _ h1 (m + 1)
  rwa [← hbm] at h2

end Elem

section Inverted

variable {G : Type} [Group G]

theorem commutator_inverted_centralizes {P₁ : Subgroup G} {t c : G} (ht : t * t = 1)
    (hinv : ∀ x ∈ P₁, t * x * t⁻¹ = x⁻¹) (hc' : c⁻¹ ∈ normalizer (P₁ : Set G)) :
    ⁅c, t⁆ ∈ centralizer (P₁ : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hw : c⁻¹ * x * c ∈ P₁ := by
    have := (Subgroup.mem_normalizer_iff.mp hc' x).mp hx
    simpa using this
  have h1 : t * (c⁻¹ * x * c) * t⁻¹ = (c⁻¹ * x * c)⁻¹ := hinv _ hw
  have hinv' : t⁻¹ * x * t = x⁻¹ := by
    have := hinv x hx
    rw [htt] at this ⊢
    exact this
  have key : ⁅c, t⁆ * x * ⁅c, t⁆⁻¹ = x := by
    have e1 : ⁅c, t⁆ * x * ⁅c, t⁆⁻¹ = c * (t * (c⁻¹ * (t⁻¹ * x * t) * c) * t⁻¹) * c⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1, hinv']
    have e2 : c⁻¹ * x⁻¹ * c = (c⁻¹ * x * c)⁻¹ := by group
    rw [e2, show t * (c⁻¹ * x * c)⁻¹ * t⁻¹ = (t * (c⁻¹ * x * c) * t⁻¹)⁻¹ by group, h1, inv_inv]
    group
  exact (mul_inv_eq_iff_eq_mul.mp key).symm

theorem commutator_le_centralizer_of_inverts [Finite G] {z t : G} {P₁ : Subgroup G} (ht : t * t = 1)
    (hzc : ∀ x ∈ P₁, z * x * z⁻¹ = x) (hinv : ∀ x ∈ P₁, t * x * t⁻¹ = x⁻¹) (hzt : z * t = t * z)
    (hCn : ∀ c ∈ Cen z, c ∈ normalizer (P₁ : Set G)) :
    ⁅Cen z, zpowers z ⊔ zpowers t⁆ ≤ centralizer (P₁ : Set G) := by
  have hzN : z ∈ normalizer (P₁ : Set G) := mem_normalizer_of_forall fun x hx => by rw [hzc x hx]; exact hx
  have htN : t ∈ normalizer (P₁ : Set G) := mem_normalizer_of_forall fun x hx => by
    rw [hinv x hx]
    exact inv_mem hx
  have hzCS : z ∈ centralizerSection (Cen z) (centralizer (P₁ : Set G)) := by
    refine ⟨Subgroup.le_normalizer (mem_Cen_self z), normalizer_le_normalizer_centralizer P₁ hzN, ?_⟩
    intro c hc
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have : ⁅c, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcz
    rw [this]
    exact one_mem _
  have htCen : t ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have htCS : t ∈ centralizerSection (Cen z) (centralizer (P₁ : Set G)) := by
    refine ⟨Subgroup.le_normalizer htCen, normalizer_le_normalizer_centralizer P₁ htN, ?_⟩
    intro c hc
    exact commutator_inverted_centralizes ht hinv (hCn c⁻¹ (inv_mem hc))
  have hU : zpowers z ⊔ zpowers t ≤ centralizerSection (Cen z) (centralizer (P₁ : Set G)) :=
    sup_le (Subgroup.zpowers_le.mpr hzCS) (Subgroup.zpowers_le.mpr htCS)
  rw [Subgroup.commutator_le]
  intro c hc u hu
  exact (hU hu).2.2 c hc

end Inverted

section Cen9

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem Ctx9.mem_Op_of_cen (h : Ctx9 G z k S M p) {x : G} (hxM : x ∈ M)
    (hx : x ∈ centralizer ((Op p M : Subgroup G) : Set G)) : x ∈ Op p M := by
  have hD : generalizedFitting ↥M = pCore p ↥M := (Fs_eq_Op_iff M p).mp h.fstar
  have hx' : (⟨x, hxM⟩ : ↥M) ∈ centralizer ((generalizedFitting ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hD] at hy
    have hmem : (y : G) ∈ Op p M := ⟨y, hy, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx _ hmem)
  have h1 := centralizer_generalizedFitting_le_fitting'' ↥M hx'
  have h2 : fittingSubgroup ↥M ≤ generalizedFitting ↥M := le_sup_left
  have h3 := h2 h1
  rw [hD] at h3
  exact ⟨_, h3, rfl⟩

theorem Ctx9.eq_one_of_cen (h : Ctx9 G z k S M p) {x : G} (hxM : x ∈ M) (hx2 : x * x = 1)
    (hx : x ∈ centralizer ((Op p M : Subgroup G) : Set G)) : x = 1 :=
  eq_one_of_mul_self_eq_one h.prime h.odd (op_isPGroup M) (h.mem_Op_of_cen hxM hx) hx2

end Cen9

end CFSG.GH74.GLS.Stage2.Bender.Thm2
