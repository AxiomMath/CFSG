module

public import CFSG.CGT.PushingUpLit.C2L.GomiMax

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2KSW
open CFSG.RankThree.PartOne (omegaOneCenterIn)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_omegaOneCenterIn_iff {Q : Subgroup G} {x : G} :
    x ∈ omegaOneCenterIn Q ↔ x ∈ Q ∧ (∀ y ∈ Q, y * x = x * y) ∧ x * x = 1 := by
  unfold omegaOneCenterIn CFSG.RankThree.PartOne.omegaOne
  have hcen : ∀ z : G, z ∈ (Subgroup.center ↥Q).map Q.subtype ↔
      z ∈ Q ∧ ∀ y ∈ Q, y * z = z * y := by
    intro z
    rw [map_center_subtype, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  constructor
  · intro hx
    refine Subgroup.closure_induction
      (p := fun z _ => z ∈ Q ∧ (∀ y ∈ Q, y * z = z * y) ∧ z * z = 1) ?_ ?_ ?_ ?_ hx
    · rintro z ⟨hz, hz2⟩
      obtain ⟨h1, h2⟩ := (hcen z).1 hz
      exact ⟨h1, h2, by simpa [pow_two] using hz2⟩
    · exact ⟨Q.one_mem, fun y _ => by simp, by simp⟩
    · rintro z w - - ⟨hzQ, hzc, hz2⟩ ⟨hwQ, hwc, hw2⟩
      refine ⟨Q.mul_mem hzQ hwQ, fun y hy => ?_, ?_⟩
      · calc y * (z * w) = (y * z) * w := by group
          _ = (z * y) * w := by rw [hzc y hy]
          _ = z * (y * w) := by group
          _ = z * (w * y) := by rw [hwc y hy]
          _ = z * w * y := by group
      · have hzw : w * z = z * w := hzc w hwQ
        calc z * w * (z * w) = z * (w * z) * w := by group
          _ = z * (z * w) * w := by rw [hzw]
          _ = (z * z) * (w * w) := by group
          _ = 1 := by rw [hz2, hw2]; group
    · rintro z - ⟨hzQ, hzc, hz2⟩
      refine ⟨Q.inv_mem hzQ, fun y hy => ?_, ?_⟩
      · have := hzc y hy
        calc y * z⁻¹ = z⁻¹ * (z * y) * z⁻¹ := by group
          _ = z⁻¹ * (y * z) * z⁻¹ := by rw [this]
          _ = z⁻¹ * y := by group
      · calc z⁻¹ * z⁻¹ = (z * z)⁻¹ := by group
          _ = 1 := by rw [hz2]; group
  · rintro ⟨hxQ, hxc, hx2⟩
    exact Subgroup.subset_closure ⟨(hcen x).2 ⟨hxQ, hxc⟩, by simpa [pow_two] using hx2⟩

theorem omegaOneCenterIn_le (Q : Subgroup G) : omegaOneCenterIn Q ≤ Q :=
  fun _ h => (mem_omegaOneCenterIn_iff.1 h).1

theorem normalizer_le_normalizer_omegaOneCenterIn (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (omegaOneCenterIn Q : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (Q : Set G), ∀ x ∈ omegaOneCenterIn Q,
      g * x * g⁻¹ ∈ omegaOneCenterIn Q := by
    intro g hg x hx
    obtain ⟨hxQ, hxc, hx2⟩ := mem_omegaOneCenterIn_iff.1 hx
    refine mem_omegaOneCenterIn_iff.2 ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hxQ,
      fun y hy => ?_, ?_⟩
    · have hy' : g⁻¹ * y * g ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) y).1 hy
        simpa using this
      have h1 := hxc _ hy'
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
        _ = g * x * g⁻¹ * y := by group
    · calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2]; group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem omegaOneCenterIn_ne_bot [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) :
    omegaOneCenterIn Q ≠ ⊥ := by
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
  have hc : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  have hcp : IsPGroup 2 (Subgroup.center Q) := hQ.to_subgroup _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hcp
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
    exact not_subsingleton (Subgroup.center Q) hn.1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  have hx2 : orderOf (x : Q) = 2 := by rw [Subgroup.orderOf_coe, hx]
  have hxsq : (x : Q) ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one _
  have hmem : ((x : Q) : G) ∈ omegaOneCenterIn Q :=
    mem_omegaOneCenterIn_iff.2 ⟨(x : Q).2, fun k hk =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨k, hk⟩), by
        simpa [pow_two] using congrArg Subtype.val hxsq⟩
  intro h
  rw [h, Subgroup.mem_bot] at hmem
  have hx1 : (x : Q) = 1 := Subtype.ext hmem
  rw [hx1, orderOf_one] at hx2
  omega

theorem isPGroup_zpowers_of_mul_self {x : G} (hx : x * x = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  rintro ⟨y, hy⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨1, Subtype.ext ?_⟩
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]

theorem normalizer_zpowers_eq_centralizer {x : G} (hx : x * x = 1) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  ext g
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((h x).1 (Subgroup.mem_zpowers x))
    have hgx : g * x * g⁻¹ = x := by
      obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
      · have h1 : x ^ (2 * m) = 1 := by rw [zpow_mul, hx2, one_zpow]
        rw [h1] at hk
        have h2 : x = 1 := by
          have : g * x * g⁻¹ = 1 := hk.symm
          simpa using this
        rw [h2]; group
      · have h1 : x ^ (2 * m + 1) = x := by rw [zpow_add_one, zpow_mul, hx2, one_zpow, one_mul]
        rw [h1] at hk
        exact hk.symm
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    calc x * g = (g * x * g⁻¹) * g := by rw [hgx]
      _ = g * x := by group
  · intro h y
    have hc : Commute g x := (h x (Set.mem_singleton x)).symm
    have h1 : ∀ k : ℤ, g * x ^ k = x ^ k * g := fun k => (hc.zpow_right k).eq
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have : g * x ^ k * g⁻¹ = x ^ k := by rw [h1 k]; group
      rw [this]
      exact hy
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hy' : y = x ^ k := by
        calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
          _ = g⁻¹ * x ^ k * g := by rw [← hk]
          _ = g⁻¹ * (x ^ k * g) := by group
          _ = g⁻¹ * (g * x ^ k) := by rw [h1 k]
          _ = x ^ k := by group
      rw [hy']
      exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩

theorem isTwoLocal_centralizer_of_mul_self {x : G} (hx1 : x ≠ 1) (hx : x * x = 1) :
    CFSG.Assembly.IsTwoLocal (Subgroup.centralizer ({x} : Set G)) :=
  ⟨Subgroup.zpowers x, by rwa [Ne, Subgroup.zpowers_eq_bot], isPGroup_zpowers_of_mul_self hx,
    (normalizer_zpowers_eq_centralizer hx).symm⟩

structure GomiAmbient (G : Type) [Group G] : Prop where
  charTwo : CFSG.Assembly.IsCharTwoType G
  classTwo : ∀ N : Subgroup G, CFSG.Assembly.IsTwoLocal N → ¬ TwoClosed N →
    ∀ S : Subgroup G, IsSylowOf 2 S N → ClassLETwo S
  zElem : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ClassLETwo S →
    ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set G), z * z = 1

structure Side (P P' D : Subgroup G) : Prop where
  sylow : IsSylowOf 2 P ⊤
  sylow' : IsSylowOf 2 P' ⊤
  ne : P ≠ P'
  max : GomiD P D
  max' : GomiD P' D

namespace Side

variable {P P' D : Subgroup G}

theorem symm (h : Side P P' D) : Side P' P D := ⟨h.sylow', h.sylow, h.ne.symm, h.max', h.max⟩

theorem hH (h : Side P P' D) : GomiH D := h.max.1.1

theorem le (h : Side P P' D) : D ≤ P := h.max.1.2

theorem le' (h : Side P P' D) : D ≤ P' := h.max'.1.2

theorem isTwoLocal (h : Side P P' D) :
    CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (D : Set G)) := h.hH.isTwoLocal

end Side

structure Hyp42Side (P D Q' P' : Subgroup G) : Prop where
  sylow : IsSylowOf 2 P ⊤
  max : GomiD P D
  other : IsOtherSylow P D Q'
  sylow' : IsSylowOf 2 P' ⊤
  le' : Q' ≤ P'

structure Hyp42 (P D₁ D₂ Q₁ Q₂ P₁ P₂ : Subgroup G) : Prop where
  sylow : IsSylowOf 2 P ⊤
  pair : GomiE P D₁ D₂
  other₁ : IsOtherSylow P D₁ Q₁
  other₂ : IsOtherSylow P D₂ Q₂
  sylow₁ : IsSylowOf 2 P₁ ⊤
  le₁ : Q₁ ≤ P₁
  sylow₂ : IsSylowOf 2 P₂ ⊤
  le₂ : Q₂ ≤ P₂

theorem GomiE.symm {P D₁ D₂ : Subgroup G} (h : GomiE P D₁ D₂) : GomiE P D₂ D₁ := by
  obtain ⟨h1, h2, hne, hN, hc⟩ := h
  refine ⟨h2, h1, hne.symm, hN.symm, ?_⟩
  rcases hc with ⟨a, b⟩ | ⟨u, hu, h1u, h2u⟩
  · exact Or.inl ⟨b, a⟩
  · exact Or.inr ⟨u, hu, h2u, h1u⟩

namespace Hyp42

variable {P D₁ D₂ Q₁ Q₂ P₁ P₂ : Subgroup G}

theorem side₁ (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂) : Hyp42Side P D₁ Q₁ P₁ :=
  ⟨h.sylow, h.pair.1, h.other₁, h.sylow₁, h.le₁⟩

theorem side₂ (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂) : Hyp42Side P D₂ Q₂ P₂ :=
  ⟨h.sylow, h.pair.2.1, h.other₂, h.sylow₂, h.le₂⟩

theorem swap (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂) : Hyp42 P D₂ D₁ Q₂ Q₁ P₂ P₁ :=
  ⟨h.sylow, h.pair.symm, h.other₂, h.other₁, h.sylow₂, h.le₂, h.sylow₁, h.le₁⟩

end Hyp42

section Ambient

variable [Finite G]

omit [Finite G] in
theorem GomiAmbient.classLETwo_of_le (hA : GomiAmbient G) {N A : Subgroup G}
    (hN : CFSG.Assembly.IsTwoLocal N) (hNc : ¬ TwoClosed N) (hAN : A ≤ N) (hA2 : IsPGroup 2 A) :
    ClassLETwo A := by
  obtain ⟨S, hS, hAS⟩ := exists_isSylowOf_ge hAN hA2
  exact CFSG.CGT.PushingUpLit.C2L.classLETwo_of_le (hA.classTwo N hN hNc S hS) hAS

theorem GomiD.isSylowOf_inf_of_lt {P D K : Subgroup G} (hP : IsSylowOf 2 P ⊤) (h : GomiD P D)
    (hK : D < P ⊓ K) : IsSylowOf 2 (P ⊓ K) K :=
  isSylowOf_inf_of_forall hP fun P₁ hP₁ hne hle =>
    h.not_lt_inf hP P₁ hP₁ hne (lt_of_lt_of_le hK (le_inf inf_le_left hle))

namespace Side

variable {P P' D : Subgroup G}

theorem inf_eq (h : Side P P' D) : P ⊓ P' = D := by
  refine le_antisymm ?_ (le_inf h.le h.le')
  by_contra hn
  exact h.max.not_lt_inf h.sylow P' h.sylow' h.ne.symm (lt_of_le_not_ge (le_inf h.le h.le') hn)

theorem lt_normalizer (h : Side P P' D) : D < P ⊓ Subgroup.normalizer (D : Set G) :=
  lt_inf_normalizer_of_lt h.sylow.isPGroup (h.max.lt h.sylow)

theorem le_inf_normalizer (h : Side P P' D) : D ≤ P ⊓ Subgroup.normalizer (D : Set G) :=
  h.lt_normalizer.le

theorem isSylowOf_inf_normalizer (h : Side P P' D) :
    IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G)) (Subgroup.normalizer (D : Set G)) :=
  h.max.isSylowOf_inf_normalizer h.sylow

theorem inf_normalizer_ne (h : Side P P' D) :
    P ⊓ Subgroup.normalizer (D : Set G) ≠ P' ⊓ Subgroup.normalizer (D : Set G) := by
  intro heq
  have h1 : P ⊓ Subgroup.normalizer (D : Set G) ≤ D :=
    (le_inf inf_le_left (heq.le.trans inf_le_left)).trans h.inf_eq.le
  exact h.lt_normalizer.not_ge h1

omit [Finite G] in
theorem centralizer_le (hA : GomiAmbient G) (h : Side P P' D) :
    Subgroup.centralizer (D : Set G) ≤ D := GomiH.centralizer_le hA.charTwo h.hH

omit [Finite G] in
theorem omega_le (hA : GomiAmbient G) (h : Side P P' D) {R : Subgroup G} (hR : D ≤ R) :
    omegaOneCenterIn R ≤ D := by
  intro x hx
  obtain ⟨hxR, hxc, -⟩ := mem_omegaOneCenterIn_iff.1 hx
  exact GomiH.center_le hA.charTwo h.hH hR ⟨hxR, Subgroup.mem_centralizer_iff.2 hxc⟩

theorem inf_le_normalizer (hA : GomiAmbient G) (h : Side P P' D) {K : Subgroup G}
    (hK : CFSG.Assembly.IsTwoLocal K) (h1 : D < P ⊓ K) (h2 : D < P' ⊓ K) :
    IsSylowOf 2 (P ⊓ K) K ∧ IsSylowOf 2 (P' ⊓ K) K ∧
      P ⊓ K ≤ P ⊓ Subgroup.normalizer (D : Set G) ∧
      P' ⊓ K ≤ P' ⊓ Subgroup.normalizer (D : Set G) := by
  have hs1 := h.max.isSylowOf_inf_of_lt h.sylow h1
  have hs2 := h.max'.isSylowOf_inf_of_lt h.sylow' h2
  have hne : P ⊓ K ≠ P' ⊓ K := by
    intro heq
    have : P ⊓ K ≤ D := (le_inf inf_le_left (heq.le.trans inf_le_left)).trans h.inf_eq.le
    exact h1.not_ge this
  have hnc : ¬ TwoClosed K := fun hc => hne (twoClosed_iff_forall_eq.1 hc _ _ hs1 hs2)
  have hc1 := hA.classLETwo_of_le hK hnc hs1.le hs1.isPGroup
  have hc2 := hA.classLETwo_of_le hK hnc hs2.le hs2.isPGroup
  refine ⟨hs1, hs2, le_inf inf_le_left ?_, le_inf inf_le_left ?_⟩
  · exact GomiH.le_normalizer_of_classLETwo hA.charTwo h.hH hc1 h1.le
  · exact GomiH.le_normalizer_of_classLETwo hA.charTwo h.hH hc2 h2.le

end Side

namespace Hyp42Side

variable {P D Q' P' : Subgroup G}

theorem eq_inf (h : Hyp42Side P D Q' P') : Q' = P' ⊓ Subgroup.normalizer (D : Set G) :=
  (h.other.1.eq_of_le (le_inf h.le' h.other.1.le) inf_le_right
    (h.sylow'.isPGroup.to_inf_left : IsPGroup 2 ↥(P' ⊓ Subgroup.normalizer (D : Set G) :
      Subgroup G))).symm

theorem side (h : Hyp42Side P D Q' P') : Side P P' D := by
  have hQ := h.max.isSylowOf_inf_normalizer h.sylow
  have hDQ := lt_inf_normalizer_of_lt h.sylow.isPGroup (h.max.lt h.sylow)
  obtain ⟨n, hn, hQ'n⟩ := exists_eq_map_conj_of_isSylowOf hQ h.other.1
  have hDn : D.map (MulAut.conj n).toMonoidHom = D := Subgroup.mem_normalizer_iff_map_conj_eq.1 hn
  have hPn : IsSylowOf 2 (P.map (MulAut.conj n).toMonoidHom) ⊤ :=
    isSylowOf_top_map_conj h.sylow n
  have hDPn : GomiD (P.map (MulAut.conj n).toMonoidHom) D := by
    have := h.max.map_conj n
    rwa [hDn] at this
  have hQ'Pn : Q' ≤ P.map (MulAut.conj n).toMonoidHom := by
    rw [hQ'n]
    exact Subgroup.map_mono inf_le_left
  have hDQ' : D < Q' := by
    rw [hQ'n]
    have := (Subgroup.map_lt_map_iff_of_injective (f := (MulAut.conj n).toMonoidHom)
      (MulAut.conj n).injective).2 hDQ
    rwa [hDn] at this
  have hP'eq : P' = P.map (MulAut.conj n).toMonoidHom := by
    by_contra hne
    exact hDPn.not_lt_inf hPn P' h.sylow' hne (lt_of_lt_of_le hDQ' (le_inf hQ'Pn h.le'))
  refine ⟨h.sylow, h.sylow', ?_, h.max, by rw [hP'eq]; exact hDPn⟩
  intro hPP'
  apply h.other.2
  have hle : Q' ≤ P ⊓ Subgroup.normalizer (D : Set G) := le_inf (hPP' ▸ h.le') h.other.1.le
  exact (h.other.1.eq_of_le hle inf_le_right
    (h.sylow.isPGroup.to_inf_left : IsPGroup 2 ↥(P ⊓ Subgroup.normalizer (D : Set G) :
      Subgroup G))).symm

end Hyp42Side

end Ambient

end CFSG.CGT.PushingUpLit.C2L

