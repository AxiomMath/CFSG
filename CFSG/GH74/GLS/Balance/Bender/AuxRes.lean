module

public import CFSG.GH74.GLS.Balance.Bender.Aux1
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GH74.GLS.Balance.Bender.Ambient
public import CFSG.GH74.GLS.Balance.PStarComp

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
theorem oResOf_conj_mem {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) {x : G}
    (hx : x ∈ oResOf p X) : g * x * g⁻¹ ∈ oResOf p X := by
  have key : oResOf p X ≤ (oResOf p X).comap (MulAut.conj g).toMonoidHom := by
    refine oResOf_le_of fun y hy hyo => ?_
    show g * y * g⁻¹ ∈ oResOf p X
    refine mem_oResOf ?_ ?_
    · have := (mem_normalizer_iff.mp hg y).mp hy
      exact this
    · have : orderOf (g * y * g⁻¹) = orderOf y := by
        have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
        simpa using this
      rw [this]; exact hyo
  exact key hx

omit [Finite G] [Fact p.Prime] in
theorem normalizer_le_normalizer_oResOf (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer ((oResOf p X : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact oResOf_conj_mem hg hx
  · intro hx
    have hg' : g⁻¹ ∈ normalizer (X : Set G) := (normalizer (X : Set G)).inv_mem hg
    have := oResOf_conj_mem hg' hx
    simpa [mul_assoc] using this

theorem le_sup_oResOf_of_le_sup {A B X : Subgroup G} (hAX : A ≤ X) (hAn : (A.subgroupOf X).Normal)
    (hBX : B ≤ X) (hXAB : X ≤ A ⊔ B) (hres : oResOf p X = X) : X ≤ A ⊔ oResOf p B := by
  have hXn : X ≤ normalizer (A : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hAX
  rw [← hres]
  refine oResOf_le_of fun x hx hxo => ?_
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (mem_sup_of_le_normalizer (N := A) (V₁ := B) (hBX.trans hXn)).1 (hXAB hx)
  set f : ↥B →* ↥X ⧸ A.subgroupOf X :=
    (QuotientGroup.mk' (A.subgroupOf X)).comp (Subgroup.inclusion hBX) with hf
  have hfb : f ⟨b, hb⟩ = QuotientGroup.mk' (A.subgroupOf X) ⟨x, hx⟩ := by
    show (QuotientGroup.mk' (A.subgroupOf X)) ⟨b, hBX hb⟩ = _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    show (b⁻¹ * x : G) ∈ A
    have hb' : b⁻¹ ∈ normalizer (A : Set G) := hXn (X.inv_mem (hBX hb))
    have h1 := (mem_normalizer_iff.mp hb' a).mp ha
    have : b⁻¹ * x = b⁻¹ * a * b⁻¹⁻¹ := by rw [← hab]; group
    rw [this]; exact h1
  have hcop : Nat.Coprime (orderOf (QuotientGroup.mk' (A.subgroupOf X) ⟨x, hx⟩)) p :=
    Nat.Coprime.coprime_dvd_left (orderOf_map_dvd _ _) (by simpa [Subgroup.orderOf_mk] using hxo)
  obtain ⟨b', hb'f, hb'c⟩ := BenderExt.exists_coprime_lift (Fact.out : p.Prime) f hcop hfb
  have hb'B : (b' : G) ∈ oResOf p B := mem_oResOf b'.2 (by simpa using hb'c)
  have h1 : (⟨(b' : G), hBX b'.2⟩ : ↥X)⁻¹ * ⟨x, hx⟩ ∈ A.subgroupOf X := by
    have h3 : (QuotientGroup.mk' (A.subgroupOf X)) ⟨(b' : G), hBX b'.2⟩ =
        QuotientGroup.mk' (A.subgroupOf X) ⟨x, hx⟩ := hb'f
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h3
    exact h3
  have h2 : (b' : G)⁻¹ * x ∈ A := h1
  have key : (b' : G) * ((b' : G)⁻¹ * x) ∈ oResOf p B ⊔ A := Subgroup.mul_mem_sup hb'B h2
  rw [mul_inv_cancel_left] at key
  rwa [sup_comm] at key

theorem coprime_card_oResOf_of_central_sylow {N T : Subgroup G} (hT : IsSylowIn p T N)
    (hc : ∀ t ∈ T, ∀ n ∈ N, t * n = n * t) : Nat.Coprime p (Nat.card (oResOf p N)) := by
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowIn p hT
  have hnorm : Subgroup.normalizer (S : Set ↥N) ≤ Subgroup.centralizer (S : Set ↥N) := by
    intro n _
    rw [mem_centralizer_iff]
    intro s hs
    have hsT : (s : G) ∈ T := by rw [← hS]; exact ⟨s, hs, rfl⟩
    exact Subtype.ext (hc _ hsT _ n.2)
  obtain ⟨K, hKn, hKp, hKidx, -⟩ := CFSG.GroupTheory.burnside_normal_complement S hnorm
  have hpq : IsPGroup p (↥N ⧸ K) := by
    obtain ⟨n, hn⟩ := S.2.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [← Subgroup.index_eq_card, hKidx, hn]
  have hle : oResOf p N ≤ K.map N.subtype := by
    refine oResOf_le_of fun x hx hxo => ?_
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    have h1 : Nat.Coprime (orderOf (QuotientGroup.mk' K ⟨x, hx⟩)) p :=
      Nat.Coprime.coprime_dvd_left (orderOf_map_dvd _ _) (by simpa [Subgroup.orderOf_mk] using hxo)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hpq) (QuotientGroup.mk' K ⟨x, hx⟩)
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk] at h1
      have : p ∣ p ^ k := dvd_pow_self p hk0
      have h2 : p ∣ Nat.gcd (p ^ k) p := Nat.dvd_gcd this dvd_rfl
      rw [h1] at h2
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h2)
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact (QuotientGroup.eq_one_iff _).1 hk
  have hdvd : Nat.card (oResOf p N) ∣ Nat.card K := by
    have h1 := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective N.subtype_injective] at h1
  refine (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 fun h => hKp (h.trans hdvd)

omit [Finite G] [Fact p.Prime] in
theorem commutator_le_of_le_normalizer {X P : Subgroup G} (hP : P ≤ normalizer (X : Set G)) :
    ⁅X, P⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx q hq
  have h1 : q * x⁻¹ * q⁻¹ ∈ X := (mem_normalizer_iff.mp (hP hq) x⁻¹).mp (X.inv_mem hx)
  have : ⁅x, q⁆ = x * (q * x⁻¹ * q⁻¹) := by rw [commutatorElement_def]; group
  rw [this]; exact X.mul_mem hx h1

omit [Finite G] [Fact p.Prime] in
theorem le_normalizer_commutator {X P : Subgroup G} (hP : P ≤ normalizer (X : Set G)) :
    X ≤ normalizer ((⁅X, P⁆ : Subgroup G) : Set G) ∧ P ≤ normalizer ((⁅X, P⁆ : Subgroup G) : Set G) := by
  have hX : ∀ y ∈ X, ∀ h ∈ ⁅X, P⁆, y * h * y⁻¹ ∈ ⁅X, P⁆ := by
    intro y hy h hh
    have key : ⁅X, P⁆ ≤ (⁅X, P⁆).comap (MulAut.conj y).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro x hx q hq
      show y * ⁅x, q⁆ * y⁻¹ ∈ ⁅X, P⁆
      have : y * ⁅x, q⁆ * y⁻¹ = ⁅y * x, q⁆ * ⁅y, q⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact ⁅X, P⁆.mul_mem (Subgroup.commutator_mem_commutator (X.mul_mem hy hx) hq)
        (⁅X, P⁆.inv_mem (Subgroup.commutator_mem_commutator hy hq))
    exact key hh
  have hP' : ∀ y ∈ P, ∀ h ∈ ⁅X, P⁆, y * h * y⁻¹ ∈ ⁅X, P⁆ := by
    intro y hy h hh
    have key : ⁅X, P⁆ ≤ (⁅X, P⁆).comap (MulAut.conj y).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro x hx q hq
      show y * ⁅x, q⁆ * y⁻¹ ∈ ⁅X, P⁆
      have : y * ⁅x, q⁆ * y⁻¹ = ⁅y * x * y⁻¹, y * q * y⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact Subgroup.commutator_mem_commutator ((mem_normalizer_iff.mp (hP hy) x).mp hx)
        (P.mul_mem (P.mul_mem hy hq) (P.inv_mem hy))
    exact key hh
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [mem_normalizer_iff]
    intro h
    exact ⟨fun hh => hX y hy h hh, fun hh => by
      have := hX y⁻¹ (X.inv_mem hy) _ hh
      simpa [mul_assoc] using this⟩
  · rw [mem_normalizer_iff]
    intro h
    exact ⟨fun hh => hP' y hy h hh, fun hh => by
      have := hP' y⁻¹ (P.inv_mem hy) _ hh
      simpa [mul_assoc] using this⟩

omit [Finite G] [Fact p.Prime] in
theorem centralizer_sup_eq {T P : Subgroup G} :
    centralizer ((T ⊔ P : Subgroup G) : Set G) = centralizer (T : Set G) ⊓ centralizer (P : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le fun x hx => (le_sup_left : T ≤ T ⊔ P) hx)
      (Subgroup.centralizer_le fun x hx => (le_sup_right : P ≤ T ⊔ P) hx)
  · intro x hx
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, mem_centralizer_iff]
    rintro h (hh | hh)
    · exact mem_centralizer_iff.mp hx.1 h hh
    · exact mem_centralizer_iff.mp hx.2 h hh

omit [Finite G] [Fact p.Prime] in
theorem normal_inf_subgroupOf {X X₂ N : Subgroup G} (hNX : N ≤ X) (hNn : (N.subgroupOf X).Normal)
    (hX₂X : X₂ ≤ X) : ((N ⊓ X₂).subgroupOf X₂).Normal := by
  refine ⟨fun m hm g => ?_⟩
  have hm' : (m : G) ∈ N ⊓ X₂ := hm
  have h1 := hNn.conj_mem ⟨(m : G), hNX hm'.1⟩ hm'.1 ⟨(g : G), hX₂X g.2⟩
  have h2 : (g : G) * (m : G) * (g : G)⁻¹ ∈ N := h1
  have h3 : (g : G) * (m : G) * (g : G)⁻¹ ∈ X₂ :=
    X₂.mul_mem (X₂.mul_mem g.2 m.2) (X₂.inv_mem g.2)
  exact ⟨h2, h3⟩

omit [Finite G] in
theorem isPStar_quot_of_le_sup {X X₂ N : Subgroup G} (hNX : N ≤ X) (hNn : (N.subgroupOf X).Normal)
    (hX₂X : X₂ ≤ X) (hXN : X ≤ N ⊔ X₂) [((N ⊓ X₂).subgroupOf X₂).Normal]
    (h : IsPStar p (↥X ⧸ N.subgroupOf X)) : IsPStar p (↥X₂ ⧸ (N ⊓ X₂).subgroupOf X₂) := by
  have hXn : X ≤ normalizer (N : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hNX
  set φ : ↥X₂ →* ↥X ⧸ N.subgroupOf X :=
    (QuotientGroup.mk' (N.subgroupOf X)).comp (Subgroup.inclusion hX₂X) with hφ
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn, z, hz, hnz⟩ :=
      (mem_sup_of_le_normalizer (N := N) (V₁ := X₂) (hX₂X.trans hXn)).1 (hXN y.2)
    refine ⟨⟨z, hz⟩, ?_⟩
    show (QuotientGroup.mk' (N.subgroupOf X)) ⟨z, hX₂X hz⟩ = (QuotientGroup.mk' (N.subgroupOf X)) y
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    show ((⟨z, hX₂X hz⟩ : ↥X)⁻¹ * y : ↥X).1 ∈ N
    show z⁻¹ * (y : G) ∈ N
    have : z⁻¹ * (y : G) = z⁻¹ * n * z⁻¹⁻¹ := by rw [← hnz]; group
    rw [this]
    have hz' : z⁻¹ ∈ normalizer (N : Set G) := hXn (X.inv_mem (hX₂X hz))
    exact (mem_normalizer_iff.mp hz' n).mp hn
  have hker : φ.ker = (N ⊓ X₂).subgroupOf X₂ := by
    ext z
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' (N.subgroupOf X)) ⟨(z : G), hX₂X z.2⟩ = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hz; exact ⟨hz, z.2⟩
    · intro hz; exact hz.1
  let e : (↥X₂ ⧸ (N ⊓ X₂).subgroupOf X₂) ≃* (↥X ⧸ N.subgroupOf X) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
  exact IsPStar.of_mulEquiv e.symm h

end CFSG.GH74.GLS.Balance
