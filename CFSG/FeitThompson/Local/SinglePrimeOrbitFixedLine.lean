module

public import CFSG.FeitThompson.Local.PrimeCentralizerTransitiveHyperplanes
import CFSG.FeitThompson.Local.PrimeCentralizerAbelianCommutatorConjugates
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise
open scoped commutatorElement

universe u

variable {G : Type u} [Group G] {p q : ℕ}

section MulAutNorm

variable {A : Type*} [CommGroup A]

def mulAutNorm (φ : MulAut A) (n : ℕ) : A →* A where
  toFun x := ∏ i ∈ Finset.range n, (φ ^ i) x
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, Finset.prod_mul_distrib]

theorem mulAutNorm_apply (φ : MulAut A) (n : ℕ) (x : A) :
    mulAutNorm φ n x = ∏ i ∈ Finset.range n, (φ ^ i) x := (rfl)

@[simp] theorem mulAutNorm_zero (φ : MulAut A) (x : A) : mulAutNorm φ 0 x = 1 := by
  simp [mulAutNorm_apply]

theorem mulAutNorm_one (φ : MulAut A) (x : A) : mulAutNorm φ 1 x = x := by
  simp [mulAutNorm_apply]

theorem mulAutNorm_succ_apply (φ : MulAut A) (m : ℕ) (x : A) :
    mulAutNorm φ (m + 1) x = (∏ i ∈ Finset.range m, (φ ^ (i + 1)) x) * x := by
  rw [mulAutNorm_apply, Finset.prod_range_succ' (fun i => (φ ^ i) x) m]
  simp

theorem apply_mulAutNorm (φ : MulAut A) {n : ℕ} (hn : φ ^ n = 1) (x : A) :
    φ (mulAutNorm φ n x) = mulAutNorm φ n x := by
  obtain _ | m := n
  · simp
  · rw [mulAutNorm_apply, map_prod]
    have hstep : ∀ i : ℕ, φ ((φ ^ i) x) = (φ ^ (i + 1)) x := fun i => by rw [pow_succ']; rfl
    rw [Finset.prod_congr rfl fun i _ => hstep i, Finset.prod_range_succ,
      Finset.prod_range_succ' (fun i => (φ ^ i) x) m, hn]
    simp

end MulAutNorm

section ConjOrbit

def conjOrbit (S W : Subgroup G) : Set (Subgroup G) :=
  {W' | ∃ g ∈ S, ConjAct.toConjAct g • W = W'}

theorem mem_conjOrbit {S W W' : Subgroup G} :
    W' ∈ conjOrbit S W ↔ ∃ g ∈ S, ConjAct.toConjAct g • W = W' := Iff.rfl

theorem self_mem_conjOrbit (S W : Subgroup G) : W ∈ conjOrbit S W := ⟨1, one_mem _, by simp⟩

theorem conjOrbit_nonempty (S W : Subgroup G) : (conjOrbit S W).Nonempty :=
  ⟨W, self_mem_conjOrbit S W⟩

theorem mem_conjOrbit_comm {S W W' : Subgroup G} (h : W' ∈ conjOrbit S W) :
    W ∈ conjOrbit S W' := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g⁻¹, inv_mem hg, by rw [map_inv, inv_smul_smul]⟩

theorem smul_mem_conjOrbit {S W : Subgroup G} {g : G} (hg : g ∈ S) :
    ConjAct.toConjAct g • W ∈ conjOrbit S W := ⟨g, hg, rfl⟩

theorem conjOrbit_eq_of_mem {S W W' : Subgroup G} (h : W' ∈ conjOrbit S W) :
    conjOrbit S W' = conjOrbit S W := by
  obtain ⟨g, hg, rfl⟩ := h
  ext W''
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g, mul_mem hh hg, by rw [map_mul, mul_smul]⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g⁻¹, mul_mem hh (inv_mem hg), by rw [map_mul, map_inv, mul_smul, inv_smul_smul]⟩

theorem conjOrbit_eq_orbit (S W : Subgroup G) :
    conjOrbit S W
      = MulAction.orbit ↥(S.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom) W := by
  ext W'
  constructor
  · rintro ⟨g, hg, rfl⟩; exact ⟨⟨ConjAct.toConjAct g, ⟨g, hg, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨g, hg, rfl⟩ := ha
    exact ⟨g, hg, rfl⟩

theorem ncard_conjOrbit_dvd [Finite G] (S W : Subgroup G) :
    (conjOrbit S W).ncard ∣ Nat.card ↥S := by
  set S' := S.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom with hS'
  have hcard : Nat.card ↥S' = Nat.card ↥S :=
    (Nat.card_congr (S.equivMapOfInjective _ (ConjAct.toConjAct (G := G)).injective).toEquiv).symm
  rw [conjOrbit_eq_orbit, ← hcard, ← MulAction.index_stabilizer ↥S' W]
  exact Subgroup.index_dvd_card _

theorem ncard_conjOrbit_eq_one_iff {S W : Subgroup G} :
    (conjOrbit S W).ncard = 1 ↔ ∀ g ∈ S, ConjAct.toConjAct g • W = W := by
  classical
  constructor
  · intro h g hg
    obtain ⟨W', hW'⟩ := Set.ncard_eq_one.1 h
    have h1 : W = W' := by
      have hm := self_mem_conjOrbit S W; rwa [hW', Set.mem_singleton_iff] at hm
    have h2 : ConjAct.toConjAct g • W = W' := by
      have hm : ConjAct.toConjAct g • W ∈ conjOrbit S W := ⟨g, hg, rfl⟩
      rwa [hW', Set.mem_singleton_iff] at hm
    rw [h2, ← h1]
  · intro h
    refine Set.ncard_eq_one.2 ⟨W, Set.eq_singleton_iff_unique_mem.2
      ⟨self_mem_conjOrbit S W, ?_⟩⟩
    rintro W' ⟨g, hg, rfl⟩
    exact h g hg

theorem disjoint_conjOrbit_of_ne {S W₁ W₂ : Subgroup G} (h : conjOrbit S W₁ ≠ conjOrbit S W₂) :
    Disjoint (conjOrbit S W₁) (conjOrbit S W₂) := by
  rw [Set.disjoint_left]
  intro W' h₁ h₂
  exact h ((conjOrbit_eq_of_mem h₁).symm.trans (conjOrbit_eq_of_mem h₂))

theorem conjAct_smul_eq_self_of_mem_zpowers {a b : G} {W : Subgroup G}
    (h : ConjAct.toConjAct a • W = W) (hb : b ∈ Subgroup.zpowers a) :
    ConjAct.toConjAct b • W = W :=
  Subgroup.conjAct_pointwise_smul_iff.2
    (Subgroup.zpowers_le.2 (Subgroup.conjAct_pointwise_smul_iff.1 h) hb)

end ConjOrbit

section Aux

theorem conj_mem_conjAct_smul {W : Subgroup G} {g x : G} (hx : x ∈ W) :
    g * x * g⁻¹ ∈ ConjAct.toConjAct g • W := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct]
  simpa [mul_assoc] using hx

theorem eq_of_le_of_natCard_eq [Finite G] {A B : Subgroup G} (h : B ≤ A)
    (hcard : Nat.card ↥A = Nat.card ↥B) : B = A := by
  have h2 := Subgroup.card_mul_index (B.subgroupOf A)
  rw [Nat.card_congr (subgroupOfEquivOfLe h).toEquiv, hcard] at h2
  have h3 : (B.subgroupOf A).index = 1 :=
    Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥B)) (by rw [h2, mul_one])
  exact le_antisymm h (Subgroup.relIndex_eq_one.1 h3)

theorem sup_zpowers_eq_of_relIndex_eq [Finite G] {K L : Subgroup G} (hq : q.Prime)
    (hLK : L ≤ K) (hidx : L.relIndex K = q) {x : G} (hxK : x ∈ K) (hxL : x ∉ L) :
    L ⊔ Subgroup.zpowers x = K := by
  have hidx' : (L.subgroupOf K).index = q := hidx
  have hxL' : (⟨x, hxK⟩ : ↥K) ∉ L.subgroupOf K := fun h => hxL (Subgroup.mem_subgroupOf.1 h)
  have hmap := congrArg (fun S : Subgroup ↥K => S.map K.subtype)
    (sup_zpowers_eq_top_of_index_eq (K := ↥K) hq hidx' hxL')
  simp only [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype] at hmap
  rw [inf_eq_left.2 hLK] at hmap
  have h1 : (Subgroup.zpowers (⟨x, hxK⟩ : ↥K)).map K.subtype = Subgroup.zpowers x := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_zpowers_iff, coe_subtype]
    exact ⟨by rintro ⟨z, ⟨n, rfl⟩, rfl⟩; exact ⟨n, by push_cast; rfl⟩,
      by rintro ⟨n, rfl⟩; exact ⟨(⟨x, hxK⟩ : ↥K) ^ n, ⟨n, rfl⟩, by push_cast; rfl⟩⟩
  have h2 : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← Subgroup.top_subgroupOf (H := K), Subgroup.subgroupOf_map_subtype, top_inf_eq]
  rw [h1, h2] at hmap
  exact hmap

theorem inf_centralizer_le_of_relIndex_eq [Finite G] {V K L W : Subgroup G} (hq : q.Prime)
    (hVK : V ⊓ centralizer (K : Set G) = ⊥) (hLK : L ≤ K) (hidx : L.relIndex K = q)
    (hWL : W = V ⊓ centralizer (L : Set G)) (hWne : W ≠ ⊥) :
    K ⊓ centralizer (W : Set G) ≤ L := by
  rintro x ⟨hxK, hxW⟩
  by_contra hxL
  refine hWne (le_bot_iff.1 ?_)
  rw [← hVK]
  intro v hv
  have hvV : v ∈ V := (hWL ▸ hv).1
  have hvL : v ∈ centralizer (L : Set G) := (hWL ▸ hv).2
  set S : Subgroup G := K ⊓ centralizer ({v} : Set G) with hS
  have hLS : L ≤ S := fun y hy =>
    ⟨hLK hy, mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hvL y hy)⟩
  have hxS : x ∈ S :=
    ⟨hxK, mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxW v hv).symm⟩
  have hKS : K ≤ S := by
    rw [← sup_zpowers_eq_of_relIndex_eq hq hLK hidx hxK hxL]
    exact sup_le hLS (Subgroup.zpowers_le.2 hxS)
  exact ⟨hvV, mem_centralizer_iff.2 fun k hk => mem_centralizer_singleton_iff.1 (hKS hk).2⟩

theorem commutator_le_left_of_le_normalizer {K R : Subgroup G}
    (hR : R ≤ normalizer (K : Set G)) : ⁅K, R⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro k hk g hg
  rw [commutatorElement_def, show k * g * k⁻¹ * g⁻¹ = k * (g * k⁻¹ * g⁻¹) from by group]
  exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.1 (hR hg) k⁻¹).1 (K.inv_mem hk))

theorem conjAct_smul_ne_self_of_ncard_conjOrbit_ne_one [Finite G] {R W : Subgroup G} {c : G}
    (hcR : Subgroup.zpowers c = R) (hR : (Nat.card ↥R).Prime)
    (hn : (conjOrbit R W).ncard ≠ 1) {i : ℕ} (hi0 : i ≠ 0) (hir : i < Nat.card ↥R) :
    ConjAct.toConjAct (c ^ i) • W ≠ W := by
  intro h
  have hcmem : c ∈ R := hcR ▸ Subgroup.mem_zpowers c
  have horder : orderOf c = Nat.card ↥R := by rw [← Nat.card_zpowers, hcR]
  have hzp : Subgroup.zpowers (c ^ i) = R :=
    zpowers_eq_of_prime_natCard hR (R.pow_mem hcmem i)
      (pow_ne_one_of_lt_orderOf hi0 (horder ▸ hir))
  exact hn (ncard_conjOrbit_eq_one_iff.2 fun g hg =>
    conjAct_smul_eq_self_of_mem_zpowers h (hzp ▸ hg))

end Aux

def fixedHyperplaneFixedSubgroups (q : ℕ) (V K R : Subgroup G) : Set (Subgroup G) :=
  {W | W ∈ hyperplaneFixedSubgroups q V K ∧ ∀ g ∈ R, ConjAct.toConjAct g • W = W}

theorem mem_fixedHyperplaneFixedSubgroups {V K R W : Subgroup G} :
    W ∈ fixedHyperplaneFixedSubgroups q V K R ↔ W ∈ hyperplaneFixedSubgroups q V K ∧
      ∀ g ∈ R, ConjAct.toConjAct g • W = W := Iff.rfl

theorem fixedHyperplaneFixedSubgroups_subset (q : ℕ) (V K R : Subgroup G) :
    fixedHyperplaneFixedSubgroups q V K R ⊆ hyperplaneFixedSubgroups q V K := fun _ h => h.1

namespace IsTransitiveHyperplaneSetup

variable [Finite G] {d : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsTransitiveHyperplaneSetup p q d H R R0 V K U N P)

include hc

theorem prime_natCard_R0 : (Nat.card ↥R0).Prime := hc.reduced.admissible.prime_card

theorem natCard_R : Nat.card ↥R = Nat.card ↥R0 := by rw [hc.reduced.R_eq]

theorem conjOrbit_subset {W : Subgroup G} (hW : W ∈ hyperplaneFixedSubgroups q V K) :
    conjOrbit R W ⊆ hyperplaneFixedSubgroups q V K := by
  rintro W' ⟨g, hg, rfl⟩
  exact hc.smul_mem_hyperplaneFixedSubgroups (Subgroup.mem_sup_right hg) hW

theorem commutator_K_R_le : (⁅K, R⁆ : Subgroup G) ≤ K :=
  commutator_le_left_of_le_normalizer hc.reduced.R_le_normalizer_K

theorem K_le_normalizer_of_mem {W : Subgroup G} (hW : W ∈ hyperplaneFixedSubgroups q V K) :
    K ≤ normalizer (W : Set G) := fun k hk =>
  Subgroup.conjAct_pointwise_smul_iff.1 (hc.smul_eq_self_of_mem_K hk hW)

theorem inf_iSup_sdiff_conjOrbit_eq_bot {W : Subgroup G}
    (hW : W ∈ hyperplaneFixedSubgroups q V K) :
    W ⊓ (⨆ W' ∈ (conjOrbit R W \ {W} : Set (Subgroup G)), W') = ⊥ := by
  have h := hc.hyperplaneDecomposition.2 {W} (conjOrbit R W \ {W})
    (Set.singleton_subset_iff.2 hW)
    (Set.sdiff_subset.trans (hc.conjOrbit_subset hW)) Set.disjoint_sdiff_right
  rwa [show (⨆ W' ∈ ({W} : Set (Subgroup G)), W') = W from by simp] at h

theorem exists_zpowers_eq_R : ∃ c : G, Subgroup.zpowers c = R := by
  have hRprime : (Nat.card ↥R).Prime := hc.natCard_R ▸ hc.prime_natCard_R0
  have hRne : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hRprime
    exact Nat.not_prime_one hRprime
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRne
  exact ⟨(a : G), zpowers_eq_of_prime_natCard hRprime a.2 fun h => ha (Subtype.ext h)⟩

theorem exists_le_inf_centralizer_of_ncard_conjOrbit_ne_one {W : Subgroup G}
    (hW : W ∈ hyperplaneFixedSubgroups q V K) (hn : (conjOrbit R W).ncard ≠ 1) :
    ∃ C : Subgroup G, C ≤ V ⊓ centralizer (R : Set G) ∧
      C ≤ (⨆ W' ∈ conjOrbit R W, W') ∧ Nat.card ↥C = Nat.card ↥W := by
  classical
  have hVn := hc.normal_V
  have hVcomm : IsMulCommutative ↥V := hc.isMulCommutative_V
  let _instCG : CommGroup ↥V := IsMulCommutative.instCommGroup
  obtain ⟨c, hcR⟩ := hc.exists_zpowers_eq_R
  have hRprime : (Nat.card ↥R).Prime := hc.natCard_R ▸ hc.prime_natCard_R0
  have hcmem : c ∈ R := hcR ▸ Subgroup.mem_zpowers c
  have hcr : c ^ Nat.card ↥R = 1 := by
    have horder : orderOf c = Nat.card ↥R := by rw [← Nat.card_zpowers, hcR]
    rw [← horder]; exact pow_orderOf_eq_one c
  set φ : MulAut ↥V := MulAut.conjNormal c with hφ
  have hφpow : ∀ i : ℕ, φ ^ i = MulAut.conjNormal (c ^ i) := fun i => by rw [hφ, ← map_pow]
  have hφr : φ ^ Nat.card ↥R = 1 := by rw [hφpow, hcr, map_one]
  have hcoe : ∀ (i : ℕ) (y : ↥V), (((φ ^ i) y : ↥V) : G) = c ^ i * (y : G) * (c ^ i)⁻¹ := by
    intro i y
    rw [hφpow]
    exact MulAut.conjNormal_apply _ _
  have hWV : W ≤ V := le_of_mem_hyperplaneFixedSubgroups hW
  set r := Nat.card ↥R with hr
  set f : ↥W →* G := V.subtype.comp ((mulAutNorm φ r).comp (Subgroup.inclusion hWV)) with hf
  have hfval : ∀ x : ↥W, f x = ((mulAutNorm φ r (Subgroup.inclusion hWV x) : ↥V) : G) :=
    fun _ => rfl
  have hfV : ∀ x : ↥W, f x ∈ V := fun x => (mulAutNorm φ r (Subgroup.inclusion hWV x)).2
  have hfC : ∀ x : ↥W, f x ∈ centralizer (R : Set G) := by
    intro x
    have h2 : c * f x * c⁻¹ = f x := by
      have h4 : (((φ (mulAutNorm φ r (Subgroup.inclusion hWV x))) : ↥V) : G)
          = ((mulAutNorm φ r (Subgroup.inclusion hWV x) : ↥V) : G) := by
        rw [apply_mulAutNorm φ hφr]
      rwa [hφ, MulAut.conjNormal_apply] at h4
    have hcomm : Commute c (f x) := mul_inv_eq_iff_eq_mul.1 h2
    refine mem_centralizer_iff.2 fun h hh => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hcR ▸ hh : h ∈ Subgroup.zpowers c)
    exact (hcomm.zpow_left n).eq
  have hforb : ∀ i : ℕ, ConjAct.toConjAct (c ^ i) • W ∈ conjOrbit R W :=
    fun i => smul_mem_conjOrbit (R.pow_mem hcmem i)
  have hfjoin : ∀ x : ↥W, f x ∈ (⨆ W' ∈ conjOrbit R W, W') := by
    intro x
    refine Subgroup.mem_subgroupOf.1 (?_ : mulAutNorm φ r (Subgroup.inclusion hWV x)
      ∈ (⨆ W' ∈ conjOrbit R W, W').subgroupOf V)
    rw [mulAutNorm_apply]
    refine Subgroup.prod_mem _ fun i _ => ?_
    rw [Subgroup.mem_subgroupOf, hcoe]
    exact le_iSup₂ (f := fun W' (_ : W' ∈ conjOrbit R W) => W') _ (hforb i)
      (conj_mem_conjAct_smul (show (x : G) ∈ W from x.2))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨m, hm⟩ : ∃ m, r = m + 1 := ⟨r - 1, by have := hRprime.two_le; omega⟩
    set T : Set (Subgroup G) := conjOrbit R W \ {W} with hT
    have hTmem : ∀ i, i ≠ 0 → i < r → ConjAct.toConjAct (c ^ i) • W ∈ T := fun i hi0 hir =>
      ⟨hforb i, by
        simpa using conjAct_smul_ne_self_of_ncard_conjOrbit_ne_one hcR hRprime hn hi0 (hr ▸ hir)⟩
    set z : ↥V := ∏ i ∈ Finset.range m, (φ ^ (i + 1)) (Subgroup.inclusion hWV x) with hzdef
    have hz : (z : G) ∈ (⨆ W' ∈ T, W') := by
      refine Subgroup.mem_subgroupOf.1 (Subgroup.prod_mem ((⨆ W' ∈ T, W').subgroupOf V)
        fun i hi => ?_)
      rw [Subgroup.mem_subgroupOf, hcoe]
      have hi2 : i + 1 < r := by have := Finset.mem_range.1 hi; omega
      exact le_iSup₂ (f := fun W' (_ : W' ∈ T) => W') _ (hTmem (i + 1) (Nat.succ_ne_zero i) hi2)
        (conj_mem_conjAct_smul (show (x : G) ∈ W from x.2))
    have hx1 : mulAutNorm φ r (Subgroup.inclusion hWV x) = 1 :=
      Subtype.ext (by rw [← hfval x]; exact hx)
    have hsplit : mulAutNorm φ r (Subgroup.inclusion hWV x) = z * Subgroup.inclusion hWV x := by
      rw [hm]; exact mulAutNorm_succ_apply φ m _
    have hxz : Subgroup.inclusion hWV x = z⁻¹ := by
      rw [hsplit] at hx1
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hx1)
    have hxG : (x : G) = ((z : ↥V) : G)⁻¹ := by
      have := congrArg (fun y : ↥V => (y : G)) hxz
      simpa using this
    have hxT : (x : G) ∈ (⨆ W' ∈ T, W') := by rw [hxG]; exact inv_mem hz
    have hbot := hc.inf_iSup_sdiff_conjOrbit_eq_bot (R := R) hW
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨x.2, hxT⟩
    exact Subtype.ext (by simpa using hxbot)
  exact ⟨f.range, fun _ ⟨x, hx⟩ => hx ▸ ⟨hfV x, hfC x⟩, fun _ ⟨x, hx⟩ => hx ▸ hfjoin x,
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm⟩

theorem natCard_eq_and_le_iSup_conjOrbit {W : Subgroup G}
    (hW : W ∈ hyperplaneFixedSubgroups q V K) (hn : (conjOrbit R W).ncard ≠ 1) :
    Nat.card ↥W = p ∧ V ⊓ centralizer (R : Set G) ≤ (⨆ W' ∈ conjOrbit R W, W') := by
  obtain ⟨C, hCle, hCjoin, hCcard⟩ :=
    hc.exists_le_inf_centralizer_of_ncard_conjOrbit_ne_one hW hn
  have hne : Nat.card ↥W ≠ 1 := fun h =>
    ne_bot_of_mem_hyperplaneFixedSubgroups hW (Subgroup.card_eq_one.1 h)
  have hWp : Nat.card ↥W = p := by
    rcases hc.prime_p.eq_one_or_self_of_dvd _
      (hCcard ▸ hc.card_inf_centralizer_R ▸ Subgroup.card_dvd_of_le hCle) with h | h
    · exact absurd h hne
    · exact h
  have hCeq : C = V ⊓ centralizer (R : Set G) :=
    eq_of_le_of_natCard_eq hCle (by rw [hc.card_inf_centralizer_R, hCcard, hWp])
  exact ⟨hWp, hCeq ▸ hCjoin⟩

theorem exists_ncard_conjOrbit_ne_one :
    ∃ W ∈ hyperplaneFixedSubgroups q V K, (conjOrbit R W).ncard ≠ 1 := by
  obtain ⟨W, hW, g, hg, hne⟩ := hc.exists_not_fixed
  exact ⟨W, hW, fun h => hne (ncard_conjOrbit_eq_one_iff.1 h g hg)⟩

private theorem linearCore_aux :
    (∀ W ∈ hyperplaneFixedSubgroups q V K, Nat.card ↥W = p) ∧
      (∀ W₁ ∈ hyperplaneFixedSubgroups q V K, ∀ W₂ ∈ hyperplaneFixedSubgroups q V K,
        (conjOrbit R W₁).ncard ≠ 1 → (conjOrbit R W₂).ncard ≠ 1 →
          conjOrbit R W₁ = conjOrbit R W₂) := by
  refine ⟨fun W hW => ?_, fun W₁ h₁ W₂ h₂ hn₁ hn₂ => ?_⟩
  ·
    obtain ⟨W₀, hW₀, hn₀⟩ := hc.exists_ncard_conjOrbit_ne_one (R := R)
    obtain ⟨a, -, hae⟩ := hc.exists_smul_eq hW₀ hW
    rw [← hae, natCard_conjAct_smul]
    exact (hc.natCard_eq_and_le_iSup_conjOrbit hW₀ hn₀).1
  ·
    by_contra hne
    have hinf := hc.hyperplaneDecomposition.2 (conjOrbit R W₁) (conjOrbit R W₂)
      (hc.conjOrbit_subset h₁) (hc.conjOrbit_subset h₂) (disjoint_conjOrbit_of_ne hne)
    have hbot : V ⊓ centralizer (R : Set G) = ⊥ :=
      le_bot_iff.1 (hinf ▸ le_inf (hc.natCard_eq_and_le_iSup_conjOrbit h₁ hn₁).2
        (hc.natCard_eq_and_le_iSup_conjOrbit h₂ hn₂).2)
    have hcard := hc.card_inf_centralizer_R
    rw [hbot, Subgroup.card_bot] at hcard
    exact hc.prime_p.one_lt.ne hcard

theorem linearCore :
    (∀ W ∈ hyperplaneFixedSubgroups q V K, Nat.card ↥W = p) ∧
      (∀ W₁ ∈ hyperplaneFixedSubgroups q V K, ∀ W₂ ∈ hyperplaneFixedSubgroups q V K,
        (conjOrbit R W₁).ncard ≠ 1 → (conjOrbit R W₂).ncard ≠ 1 →
          conjOrbit R W₁ = conjOrbit R W₂) :=
  hc.linearCore_aux

theorem natCard_eq_of_mem_hyperplaneFixedSubgroups {W : Subgroup G}
    (hW : W ∈ hyperplaneFixedSubgroups q V K) : Nat.card ↥W = p :=
  hc.linearCore.1 W hW

theorem conjOrbit_eq_of_ncard_ne_one {W₁ W₂ : Subgroup G}
    (h₁ : W₁ ∈ hyperplaneFixedSubgroups q V K) (h₂ : W₂ ∈ hyperplaneFixedSubgroups q V K)
    (hn₁ : (conjOrbit R W₁).ncard ≠ 1) (hn₂ : (conjOrbit R W₂).ncard ≠ 1) :
    conjOrbit R W₁ = conjOrbit R W₂ :=
  hc.linearCore.2 W₁ h₁ W₂ h₂ hn₁ hn₂

theorem isCyclic_of_mem_hyperplaneFixedSubgroups {W : Subgroup G}
    (hW : W ∈ hyperplaneFixedSubgroups q V K) : IsCyclic ↥W :=
  haveI := Fact.mk hc.prime_p
  isCyclic_of_prime_card (hc.natCard_eq_of_mem_hyperplaneFixedSubgroups hW)

theorem commutator_eq_of_mem_fixedHyperplaneFixedSubgroups {W L : Subgroup G}
    (hW : W ∈ fixedHyperplaneFixedSubgroups q V K R) (hLK : L ≤ K) (hidx : L.relIndex K = q)
    (hWL : W = V ⊓ centralizer (L : Set G)) : L = ⁅K, R⁆ := by
  haveI : IsCyclic ↥W := hc.isCyclic_of_mem_hyperplaneFixedSubgroups hW.1
  have hKW : K ≤ normalizer (W : Set G) := hc.K_le_normalizer_of_mem hW.1
  have hRW : R ≤ normalizer (W : Set G) := fun g hg =>
    Subgroup.conjAct_pointwise_smul_iff.1 (hW.2 g hg)
  have hCK : K ⊓ centralizer (W : Set G) ≤ L :=
    inf_centralizer_le_of_relIndex_eq hc.prime_q hc.reduced.inf_V_centralizer_K hLK hidx hWL
      (ne_bot_of_mem_hyperplaneFixedSubgroups hW.1)
  have hKRle : (⁅K, R⁆ : Subgroup G) ≤ L := by
    refine le_trans ?_ hCK
    rw [Subgroup.commutator_le]
    intro k hk g hg
    exact ⟨hc.commutator_K_R_le (Subgroup.commutator_mem_commutator hk hg),
      commutatorElement_mem_centralizer_of_isCyclic (hKW hk) (hRW hg)⟩
  have h1 := natCard_mul_relIndex hLK
  have h2 := natCard_mul_relIndex hc.commutator_K_R_le
  rw [hidx] at h1
  rw [hc.relIndex_commutator] at h2
  exact (eq_of_le_of_natCard_eq hKRle
    (Nat.eq_of_mul_eq_mul_right hc.prime_q.pos (h1.trans h2.symm))).symm

theorem eq_of_mem_fixedHyperplaneFixedSubgroups {W₁ W₂ : Subgroup G}
    (h₁ : W₁ ∈ fixedHyperplaneFixedSubgroups q V K R)
    (h₂ : W₂ ∈ fixedHyperplaneFixedSubgroups q V K R) : W₁ = W₂ := by
  obtain ⟨-, L₁, hL₁K, hL₁idx, hW₁⟩ := mem_hyperplaneFixedSubgroups.1 h₁.1
  obtain ⟨-, L₂, hL₂K, hL₂idx, hW₂⟩ := mem_hyperplaneFixedSubgroups.1 h₂.1
  have e₁ := hc.commutator_eq_of_mem_fixedHyperplaneFixedSubgroups h₁ hL₁K hL₁idx hW₁
  have e₂ := hc.commutator_eq_of_mem_fixedHyperplaneFixedSubgroups h₂ hL₂K hL₂idx hW₂
  rw [hW₁, hW₂, e₁, e₂]

theorem ncard_conjOrbit_eq_one_or_eq (W : Subgroup G) :
    (conjOrbit R W).ncard = 1 ∨ (conjOrbit R W).ncard = Nat.card ↥R0 :=
  hc.prime_natCard_R0.eq_one_or_self_of_dvd _ (hc.natCard_R ▸ ncard_conjOrbit_dvd R W)

theorem exists_ncard_conjOrbit_eq : ∃ W ∈ hyperplaneFixedSubgroups q V K,
    (conjOrbit R W).ncard = Nat.card ↥R0 := by
  obtain ⟨W, hW, g, hg, hne⟩ := hc.exists_not_fixed
  refine ⟨W, hW, ?_⟩
  rcases hc.ncard_conjOrbit_eq_one_or_eq (R := R) W with h | h
  · exact absurd (ncard_conjOrbit_eq_one_iff.1 h g hg) hne
  · exact h

theorem notMem_fixedHyperplaneFixedSubgroups_of_ncard_eq {W : Subgroup G}
    (h : (conjOrbit R W).ncard = Nat.card ↥R0) :
    W ∉ fixedHyperplaneFixedSubgroups q V K R := fun hmem =>
  hc.prime_natCard_R0.one_lt.ne ((ncard_conjOrbit_eq_one_iff.2 hmem.2) ▸ h)

theorem hyperplaneFixedSubgroups_eq_union {W : Subgroup G}
    (hW : W ∈ hyperplaneFixedSubgroups q V K) (hn : (conjOrbit R W).ncard = Nat.card ↥R0) :
    hyperplaneFixedSubgroups q V K
      = conjOrbit R W ∪ fixedHyperplaneFixedSubgroups q V K R := by
  have hne : (conjOrbit R W).ncard ≠ 1 := by
    rw [hn]; exact fun h => hc.prime_natCard_R0.one_lt.ne h.symm
  refine Set.Subset.antisymm (fun W' hW' => ?_) ?_
  · rcases hc.ncard_conjOrbit_eq_one_or_eq (R := R) W' with h | h
    · exact Or.inr ⟨hW', ncard_conjOrbit_eq_one_iff.1 h⟩
    · refine Or.inl ?_
      have hne' : (conjOrbit R W').ncard ≠ 1 := by
        rw [h]; exact fun hh => hc.prime_natCard_R0.one_lt.ne hh.symm
      rw [← hc.conjOrbit_eq_of_ncard_ne_one hW' hW hne' hne]
      exact self_mem_conjOrbit R W'
  · exact Set.union_subset (hc.conjOrbit_subset hW)
      (fixedHyperplaneFixedSubgroups_subset q V K R)

theorem disjoint_conjOrbit_fixed {W : Subgroup G}
    (hn : (conjOrbit R W).ncard = Nat.card ↥R0) :
    Disjoint (conjOrbit R W) (fixedHyperplaneFixedSubgroups q V K R) := by
  rw [Set.disjoint_left]
  intro W' hW' hfix
  refine hc.notMem_fixedHyperplaneFixedSubgroups_of_ncard_eq (W := W') ?_ hfix
  rw [conjOrbit_eq_of_mem hW', hn]

theorem ncard_fixedHyperplaneFixedSubgroups_le :
    (fixedHyperplaneFixedSubgroups q V K R).ncard ≤ 1 :=
  (Set.ncard_le_one (Set.toFinite _)).2 fun _ h₁ _ h₂ =>
    hc.eq_of_mem_fixedHyperplaneFixedSubgroups h₁ h₂

theorem ncard_eq_or :
    (hyperplaneFixedSubgroups q V K).ncard = Nat.card ↥R0 ∨
      (hyperplaneFixedSubgroups q V K).ncard = Nat.card ↥R0 + 1 := by
  obtain ⟨W, hW, hn⟩ := hc.exists_ncard_conjOrbit_eq
  have hsplit : (hyperplaneFixedSubgroups q V K).ncard
      = (conjOrbit R W).ncard + (fixedHyperplaneFixedSubgroups q V K R).ncard := by
    rw [hc.hyperplaneFixedSubgroups_eq_union hW hn]
    exact Set.ncard_union_eq (hc.disjoint_conjOrbit_fixed hn) (Set.toFinite _) (Set.toFinite _)
  have hle := hc.ncard_fixedHyperplaneFixedSubgroups_le (q := q) (V := V) (K := K)
  rw [hn] at hsplit
  interval_cases h : (fixedHyperplaneFixedSubgroups q V K R).ncard
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end IsTransitiveHyperplaneSetup

theorem singlePrimeOrbit [Finite G] {d : ℕ} {H R R0 V K U N P : Subgroup G}
    (hc : IsTransitiveHyperplaneSetup p q d H R R0 V K U N P) :
    (∀ W ∈ hyperplaneFixedSubgroups q V K, Nat.card ↥W = p) ∧
      (∀ W ∈ hyperplaneFixedSubgroups q V K,
        (conjOrbit R W).ncard = 1 ∨ (conjOrbit R W).ncard = Nat.card ↥R0) ∧
      (∃ W ∈ hyperplaneFixedSubgroups q V K, (conjOrbit R W).ncard = Nat.card ↥R0) ∧
      (∀ W₁ ∈ hyperplaneFixedSubgroups q V K, ∀ W₂ ∈ hyperplaneFixedSubgroups q V K,
        (conjOrbit R W₁).ncard = Nat.card ↥R0 → (conjOrbit R W₂).ncard = Nat.card ↥R0 →
          conjOrbit R W₁ = conjOrbit R W₂) ∧
      ((hyperplaneFixedSubgroups q V K).ncard = Nat.card ↥R0 ∨
        (hyperplaneFixedSubgroups q V K).ncard = Nat.card ↥R0 + 1) := by
  refine ⟨fun _ hW => hc.natCard_eq_of_mem_hyperplaneFixedSubgroups hW,
    fun W _ => hc.ncard_conjOrbit_eq_one_or_eq W, hc.exists_ncard_conjOrbit_eq,
    fun W₁ h₁ W₂ h₂ hn₁ hn₂ => ?_, hc.ncard_eq_or⟩
  have hone : ∀ m : ℕ, m = Nat.card ↥R0 → m ≠ 1 := fun m hm hm1 =>
    hc.prime_natCard_R0.one_lt.ne (hm1 ▸ hm)
  exact hc.conjOrbit_eq_of_ncard_ne_one h₁ h₂ (hone _ hn₁) (hone _ hn₂)

end

end CFSG.FeitThompson

