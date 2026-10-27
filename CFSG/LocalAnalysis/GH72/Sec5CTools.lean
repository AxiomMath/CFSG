module

public import CFSG.LocalAnalysis.GH72.MaxInvariant
public import CFSG.LocalAnalysis.GH72.Sec5Tools
public import CFSG.LocalAnalysis.GH72.Sec6
public import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

section Conj

variable {G : Type} [Group G]

theorem mem_normalizer_of_map_conj_le [Finite G] {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ normalizer (H : Set G) := by
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    eq_of_le_of_card_ge h (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      simpa using hyx
    exact this ▸ hy

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp hg

theorem mem_normalizer_map_conj {R : Subgroup G} {x z : G} (hz : z ∈ normalizer (R : Set G))
    (hxz : z * x = x * z) : z ∈ normalizer ((R.map (MulAut.conj x).toMonoidHom : Subgroup G) :
      Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have e : ∀ a b : G, (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := fun a b => by
    ext y
    simp [mul_assoc]
  change (R.map (MulAut.conj x).toMonoidHom).map (MulAut.conj z).toMonoidHom = _
  rw [map_map, e, hxz, ← e, ← map_map, map_conj_eq_of_mem_normalizer hz]

end Conj

section KleinFour

variable {G : Type} [Group G] [Finite G]

theorem inf_eq_bot_of_isKleinFour {B K : Subgroup G} (hB : IsKleinFour B) (hK : Odd (Nat.card K)) :
    B ⊓ K = ⊥ :=
  eq_bot_of_le_of_isKleinFour hB inf_le_left (hK.of_dvd_nat (card_dvd_of_le inf_le_right))

omit [Finite G] in
theorem exists_ne_one_of_isKleinFour {B : Subgroup G} (hB : IsKleinFour B) :
    ∃ b ∈ B, b ≠ 1 := by
  refine (Subgroup.bot_or_exists_ne_one B).resolve_left fun hB1 => ?_
  have h4 := hB.card_four
  rw [hB1, card_bot] at h4
  exact absurd h4 (by norm_num)

end KleinFour

section Commutator

variable {G : Type} [Group G]

theorem commutatorElement_mul_of_commute {t q x : G} (hqx : q * x = x * q) :
    ⁅t * q, x⁆ = ⁅t, x⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have e : q * x * q⁻¹ = x := by rw [hqx, mul_inv_cancel_right]
  calc t * q * x * (t * q)⁻¹ * x⁻¹ = t * (q * x * q⁻¹) * t⁻¹ * x⁻¹ := by group
    _ = t * x * t⁻¹ * x⁻¹ := by rw [e]

theorem le_normalizer_commutator {H K L : Subgroup G} (hH : L ≤ normalizer (H : Set G))
    (hK : L ≤ normalizer (K : Set G)) : L ≤ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅H, K⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom = _
  rw [map_commutator, map_conj_eq_of_mem_normalizer (hH hg), map_conj_eq_of_mem_normalizer (hK hg)]

end Commutator

section Covering

variable {G : Type} [Group G]

theorem Covers.mono {H H' M₀ OM : Subgroup G} (h : Covers H M₀ OM) (hle : H ⊓ M₀ ≤ H') :
    Covers H' M₀ OM :=
  h.trans (sup_le_sup_right (le_inf hle inf_le_right) _)

theorem Covers.exists_mul {H M₀ OM : Subgroup G} (h : Covers H M₀ OM)
    (hOM : M₀ ≤ normalizer (OM : Set G)) {m : G} (hm : m ∈ M₀) :
    ∃ x ∈ H ⊓ M₀, ∃ o ∈ OM, x * o = m := by
  have hm' : m ∈ ((H ⊓ M₀ ⊔ OM : Subgroup G) : Set G) := h hm
  rw [coe_mul_of_left_le_normalizer_right _ _ (inf_le_right.trans hOM)] at hm'
  obtain ⟨x, hx, o, ho, rfl⟩ := hm'
  exact ⟨x, hx, o, ho, rfl⟩

theorem covers_of_forall {H M₀ OM : Subgroup G}
    (h : ∀ m ∈ M₀, ∃ x ∈ H ⊓ M₀, ∃ o ∈ OM, x * o = m) : Covers H M₀ OM := by
  intro m hm
  obtain ⟨x, hx, o, ho, rfl⟩ := h m hm
  exact mul_mem (mem_sup_left hx) (mem_sup_right ho)

theorem map_eq_top_of_covers {L : Type*} [Group L] {H M₀ OM : Subgroup G} (f : M₀ →* L)
    (hf : Function.Surjective f) (hker : f.ker = OM.subgroupOf M₀) (hcov : Covers H M₀ OM)
    (hOMn : M₀ ≤ normalizer (OM : Set G)) : (H.subgroupOf M₀).map f = ⊤ := by
  rw [eq_top_iff]
  rintro l -
  obtain ⟨⟨m, hm⟩, rfl⟩ := hf l
  obtain ⟨x, hx, o, ho, rfl⟩ := hcov.exists_mul hOMn hm
  have hxM : x ∈ M₀ := hx.2
  have hoM : o ∈ M₀ := by
    have h := M₀.mul_mem (M₀.inv_mem hxM) hm
    simpa using h
  refine ⟨⟨x, hx.2⟩, hx.1, ?_⟩
  have hok : (⟨o, hoM⟩ : M₀) ∈ f.ker := by rw [hker]; exact ho
  have e : (⟨x * o, hm⟩ : M₀) = ⟨x, hx.2⟩ * ⟨o, hoM⟩ := rfl
  rw [e, map_mul, (MonoidHom.mem_ker).mp hok, mul_one]

theorem covers_of_map_eq_top {L : Type*} [Group L] {D M₀ OM : Subgroup G} (f : M₀ →* L)
    (hker : f.ker = OM.subgroupOf M₀) (hD : (D.subgroupOf M₀).map f = ⊤) : Covers D M₀ OM := by
  apply covers_of_forall
  intro m hm
  obtain ⟨d, hd, hdm⟩ : f ⟨m, hm⟩ ∈ (D.subgroupOf M₀).map f := hD ▸ mem_top _
  have hk : d⁻¹ * ⟨m, hm⟩ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdm, inv_mul_cancel]
  rw [hker] at hk
  refine ⟨d, ⟨hd, d.2⟩, ((d⁻¹ * ⟨m, hm⟩ : M₀) : G), mem_subgroupOf.mp hk, ?_⟩
  simp

theorem le_commutator_sup_of_covers {L : Type*} [Group L] {H M₀ OM : Subgroup G}
    (f : M₀ →* L) (hf : Function.Surjective f) (hker : f.ker = OM.subgroupOf M₀)
    (hL : commutator L = ⊤) (hcov : Covers H M₀ OM) (hOMn : M₀ ≤ normalizer (OM : Set G)) :
    M₀ ≤ ⁅H ⊓ M₀, H ⊓ M₀⁆ ⊔ OM := by
  set B : Subgroup M₀ := (H ⊓ M₀).subgroupOf M₀ with hBdef
  have hB : B.map f = ⊤ := by
    rw [hBdef, inf_subgroupOf_right]
    exact map_eq_top_of_covers f hf hker hcov hOMn
  have hBB : (⁅B, B⁆ : Subgroup M₀).map f = ⊤ := by
    rw [map_commutator, hB, ← commutator_def, hL]
  have hcov' : Covers (⁅H ⊓ M₀, H ⊓ M₀⁆ : Subgroup G) M₀ OM := by
    refine covers_of_map_eq_top f hker (eq_top_iff.mpr ((eq_top_iff.mp hBB).trans ?_))
    apply map_mono
    intro c hc
    have hmap : (⁅B, B⁆ : Subgroup M₀).map M₀.subtype = ⁅H ⊓ M₀, H ⊓ M₀⁆ := by
      rw [map_commutator, hBdef, subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
    show (c : G) ∈ ⁅H ⊓ M₀, H ⊓ M₀⁆
    rw [← hmap]
    exact ⟨c, hc, rfl⟩
  exact hcov'.trans (sup_le_sup_right inf_le_left _)

theorem covers_of_isSimpleGroup {L : Type*} [Group L] [IsSimpleGroup L]
    {K D N₀ ON : Subgroup G} (f : N₀ →* L) (hf : Function.Surjective f)
    (hker : f.ker = ON.subgroupOf N₀) (hcov : Covers K N₀ ON)
    (hONn : N₀ ≤ normalizer (ON : Set G)) (hKD : K ⊓ N₀ ≤ normalizer (D : Set G)) {x : G}
    (hx : x ∈ D ⊓ K ⊓ N₀) (hxO : x ∉ ON) : Covers D N₀ ON := by
  set E : Subgroup N₀ := (D ⊓ K).subgroupOf N₀ with hEdef
  have hK : (K.subgroupOf N₀).map f = ⊤ := map_eq_top_of_covers f hf hker hcov hONn
  have hEn : (E.map f).Normal := by
    constructor
    rintro _ ⟨e, he, rfl⟩ l
    obtain ⟨k, hk, rfl⟩ : l ∈ (K.subgroupOf N₀).map f := hK ▸ mem_top _
    refine ⟨k * e * k⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hkN : (k : G) ∈ normalizer (D : Set G) := hKD ⟨hk, k.2⟩
    refine ⟨?_, ?_⟩
    · show (k : G) * e * (k : G)⁻¹ ∈ D
      exact (mem_normalizer_iff.mp hkN e).mp he.1
    · show (k : G) * e * (k : G)⁻¹ ∈ K
      exact mul_mem (mul_mem hk he.2) (inv_mem hk)
  have hEtop : E.map f = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (E.map f) with h | h
    · exfalso
      apply hxO
      have hxE : (⟨x, hx.2⟩ : N₀) ∈ E := ⟨hx.1.1, hx.1.2⟩
      have h1 : f ⟨x, hx.2⟩ = 1 := by
        have := mem_map_of_mem f hxE
        rw [h] at this
        exact (mem_bot).mp this
      have h2 : (⟨x, hx.2⟩ : N₀) ∈ f.ker := h1
      rw [hker] at h2
      exact h2
    · exact h
  apply covers_of_map_eq_top f hker
  rw [eq_top_iff, ← hEtop]
  exact map_mono (fun y hy => hy.1)

theorem covers_of_card_eq {L : Type*} [Group L] [Finite L] {X D N₀ ON : Subgroup G}
    (f : N₀ →* L) (hker : f.ker = ON.subgroupOf N₀) (hXD : X ≤ D ⊓ N₀) (hXO : X ⊓ ON = ⊥)
    (hcard : Nat.card X = Nat.card L) : Covers D N₀ ON := by
  set X' : Subgroup N₀ := X.subgroupOf N₀ with hX'def
  set φ : X' →* L := f.comp X'.subtype with hφdef
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨⟨y, hyN⟩, hyX⟩ hy
    have hy' : (⟨y, hyN⟩ : N₀) ∈ f.ker := hy
    rw [hker] at hy'
    have : y ∈ X ⊓ ON := ⟨hyX, hy'⟩
    rw [hXO, mem_bot] at this
    exact (mem_bot).mpr (Subtype.ext (Subtype.ext this))
  have hcardX' : Nat.card X' = Nat.card X :=
    Nat.card_congr (subgroupOfEquivOfLe (hXD.trans inf_le_right)).toEquiv
  have hφrange : φ.range = X'.map f := by
    rw [hφdef, MonoidHom.range_comp, range_subtype]
  have hrange : (X'.map f) = ⊤ := by
    have h1 : Nat.card (X'.map f) = Nat.card L := by
      rw [← hφrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcardX', hcard]
    exact Subgroup.eq_top_of_card_eq _ h1
  apply covers_of_map_eq_top f hker
  rw [eq_top_iff, ← hrange]
  exact map_mono (fun y hy => (hXD hy).1)

end Covering

section OddCore

variable {G : Type} [Group G]

variable [Finite G]

theorem le_O_sup_inf_normalizer_of_isSylowOf {p : ℕ} (hp : p.Prime) {H Q : Subgroup G}
    (hQ : IsSylowOf p Q (O H)) : H ≤ O H ⊔ (H ⊓ normalizer (Q : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  intro h hh
  have hQO : Q ≤ O H := hQ.le
  have hconjO : Q.map (MulAut.conj h).toMonoidHom ≤ O H := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp (le_normalizer_O H hh) x).mp (hQO hx)
  obtain ⟨c, hcO, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hQ hconjO (hQ.isPGroup.map _)
  have hch : c * h ∈ normalizer (Q : Set G) := by
    apply mem_normalizer_of_forall_conj_mem
    intro x hx
    have hmem := hc ⟨h * x * h⁻¹, ⟨x, hx, rfl⟩, rfl⟩
    have e : (MulAut.conj c).toMonoidHom (h * x * h⁻¹) = c * h * x * (c * h)⁻¹ := by
      simp [mul_assoc]
    rwa [e] at hmem
  have hcH : c ∈ H := O_le H hcO
  have e : h = c⁻¹ * (c * h) := by group
  rw [e]
  exact mul_mem (mem_sup_left (inv_mem hcO)) (mem_sup_right ⟨mul_mem hcH hh, hch⟩)

end OddCore

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem coprime_card_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P X : Subgroup G}
    (hP : IsPGroup p P) (hX : IsPGroup 2 X) : Nat.Coprime (Nat.card X) (Nat.card P) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hX.exists_card_eq
  obtain ⟨b, hb⟩ := hP.exists_card_eq
  rw [ha, hb]
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))

theorem le_commutator_sup_inf_centralizer_of_coprime_pGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P X : Subgroup G} (hP : IsPGroup p P) (hX : IsPGroup 2 X)
    (hXP : X ≤ normalizer (P : Set G)) : P ≤ ⁅P, X⁆ ⊔ P ⊓ centralizer (X : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hP.isNilpotent
  exact CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite hXP
    (coprime_card_of_isPGroup hp hp2 hP hX) inferInstance

theorem covers_normalizer_of_isSylowOf {r : ℕ} (hr : r.Prime) {Z K R B M₀ OM : Subgroup G}
    (hZ : IsPGroup 2 Z) (hZK : Z ≤ normalizer (K : Set G)) (hK : Odd (Nat.card K))
    (hR : IsSylowOf r R K) (hZR : Z ≤ normalizer (R : Set G)) (hB : Covers B M₀ OM)
    (hBK : B ⊓ M₀ ≤ normalizer (K : Set G)) (hBZ : B ⊓ M₀ ≤ centralizer (Z : Set G))
    (hKZ : K ⊓ centralizer (Z : Set G) ≤ OM) (hOM : OM ≤ M₀)
    (hOMn : M₀ ≤ normalizer (OM : Set G)) : Covers (normalizer (R : Set G)) M₀ OM := by
  have : Fact r.Prime := ⟨hr⟩
  apply covers_of_forall
  intro m hm
  obtain ⟨x, hx, o, ho, rfl⟩ := hB.exists_mul hOMn hm
  have hRx : IsSylowOf r (R.map (MulAut.conj x).toMonoidHom) K := by
    have h := isSylowOf_map_hom hR (MulAut.conj x).toMonoidHom
    rwa [map_conj_eq_of_mem_normalizer (hBK hx)] at h
  have hZRx : Z ≤ normalizer ((R.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) :=
    fun z hz => mem_normalizer_map_conj (hZR hz) (mem_centralizer_iff.mp (hBZ hx) z hz)
  obtain ⟨c, ⟨hcK, hcZ⟩, hc⟩ :=
    CFSG.ABGTheoremB.exists_conj_eq_of_isSylowOf_normalized_of_odd hr hZ hZK hK hRx hR hZRx hZR
  have hcO : c ∈ OM := hKZ ⟨hcK, hcZ⟩
  have hcx : c * x ∈ normalizer (R : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    have e : (MulAut.conj (c * x)).toMonoidHom =
        (MulAut.conj c).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
      ext y
      simp [mul_assoc]
    change R.map (MulAut.conj (c * x)).toMonoidHom = R
    rw [e, ← map_map, hc]
  refine ⟨c * x, ⟨hcx, mul_mem (hOM hcO) hx.2⟩, x⁻¹ * c⁻¹ * x * o, ?_, by group⟩
  refine mul_mem ?_ ho
  have h1 := (mem_normalizer_iff.mp (hOMn (inv_mem hx.2)) c⁻¹).mp (inv_mem hcO)
  simpa using h1

theorem inf_centralizer_ne_bot_of_isCyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E F : Subgroup G} (hE : IsPGroup p E) (hEc : IsCyclic E) (hF : CFSG.Open.IsElemAbelian p F)
    (hF3 : Nat.card F = p ^ 3) (hFE : F ≤ normalizer (E : Set G)) :
    F ⊓ centralizer (E : Set G) ≠ ⊥ := by
  intro hbot
  have : Fact p.Prime := ⟨hp⟩
  have := hEc
  set φ : F →* MulAut E := E.normalizerMonoidHom.comp (inclusion hFE) with hφdef
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hxF⟩ hx
    have hx' : inclusion hFE ⟨x, hxF⟩ ∈ E.normalizerMonoidHom.ker := hx
    rw [normalizerMonoidHom_ker] at hx'
    have : x ∈ F ⊓ centralizer (E : Set G) := ⟨hxF, hx'⟩
    rw [hbot, mem_bot] at this
    exact (mem_bot).mpr (Subtype.ext this)
  obtain ⟨n, hn⟩ := hE.exists_card_eq
  have : IsCyclic (ZMod (Nat.card E))ˣ := by
    rw [hn]
    exact ZMod.isCyclic_units_of_prime_pow p hp hp2 n
  have : IsCyclic (MulAut E) :=
    isCyclic_of_injective (IsCyclic.mulAutMulEquiv E).toMonoidHom
      (IsCyclic.mulAutMulEquiv E).injective
  have : IsCyclic F := isCyclic_of_injective φ hφ
  have hexp : Monoid.exponent F ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hF.2 g g.2)
  rw [IsCyclic.exponent_eq_card, hF3] at hexp
  have h1 : p ^ 3 ≤ p := Nat.le_of_dvd hp.pos hexp
  have h2 := hp.two_le
  have h3 : p ^ 3 = p * p * p := by ring
  nlinarith

end Coprime

end CFSG.GH72
