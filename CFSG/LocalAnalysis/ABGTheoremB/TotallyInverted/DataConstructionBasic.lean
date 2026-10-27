module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Data
public import CFSG.LocalAnalysis.ABGTheoremB.IV1

public section

namespace CFSG.ABGTheoremB.TotallyInverted.DataConstruction

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_conjSub_iff {g y : G} {X : Subgroup G} : y ∈ conjSub g X ↔ g⁻¹ * y * g ∈ X := by
  rw [conjSub, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_conjSub {g x : G} {X : Subgroup G} (hx : x ∈ X) :
    g * x * g⁻¹ ∈ conjSub g X := by
  rw [mem_conjSub_iff, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  exact hx

theorem coe_conjSub (g : G) (X : Subgroup G) :
    (conjSub g X : Set G) = MulAut.conj g '' (X : Set G) :=
  Subgroup.coe_map _ X

theorem conjSub_one (X : Subgroup G) : conjSub 1 X = X := by
  ext y
  simp [mem_conjSub_iff]

theorem conjSub_conjSub (g h : G) (X : Subgroup G) :
    conjSub g (conjSub h X) = conjSub (g * h) X := by
  ext y
  simp only [mem_conjSub_iff]
  rw [show h⁻¹ * (g⁻¹ * y * g) * h = (g * h)⁻¹ * y * (g * h) by group]

theorem conjSub_inv_conjSub (g : G) (X : Subgroup G) : conjSub g⁻¹ (conjSub g X) = X := by
  rw [conjSub_conjSub, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv (g : G) (X : Subgroup G) : conjSub g (conjSub g⁻¹ X) = X := by
  rw [conjSub_conjSub, mul_inv_cancel, conjSub_one]

theorem conjSub_pow_succ (g : G) (n : ℕ) (X : Subgroup G) :
    conjSub (g ^ (n + 1)) X = conjSub g (conjSub (g ^ n) X) := by
  rw [conjSub_conjSub, pow_succ']

theorem conjSub_mono {g : G} {X Y : Subgroup G} (h : X ≤ Y) : conjSub g X ≤ conjSub g Y :=
  Subgroup.map_mono h

theorem conjSub_le_conjSub_iff {g : G} {X Y : Subgroup G} :
    conjSub g X ≤ conjSub g Y ↔ X ≤ Y :=
  ⟨fun h => by simpa [conjSub_inv_conjSub] using conjSub_mono (g := g⁻¹) h, conjSub_mono⟩

theorem le_conjSub_iff {g : G} {X Y : Subgroup G} : X ≤ conjSub g Y ↔ conjSub g⁻¹ X ≤ Y := by
  rw [← conjSub_le_conjSub_iff (g := g⁻¹), conjSub_inv_conjSub]

theorem conjSub_injective (g : G) : Function.Injective (conjSub g) := fun X Y h => by
  rw [← conjSub_inv_conjSub g X, h, conjSub_inv_conjSub]

theorem conjSub_inf (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊓ Y) = conjSub g X ⊓ conjSub g Y :=
  Subgroup.map_inf_eq X Y _ (MulAut.conj g).injective

theorem conjSub_sup (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊔ Y) = conjSub g X ⊔ conjSub g Y :=
  Subgroup.map_sup X Y _

theorem conjSub_bot (g : G) : conjSub g (⊥ : Subgroup G) = ⊥ :=
  Subgroup.map_bot _

theorem conjSub_eq_bot_iff {g : G} {X : Subgroup G} : conjSub g X = ⊥ ↔ X = ⊥ :=
  ⟨fun h => conjSub_injective g (h.trans (conjSub_bot g).symm), fun h => h ▸ conjSub_bot g⟩

theorem card_conjSub (g : G) (X : Subgroup G) : Nat.card (conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isPGroup_conjSub {p : ℕ} {X : Subgroup G} (hX : IsPGroup p X) (g : G) :
    IsPGroup p (conjSub g X) :=
  hX.map _

theorem conjSub_eq_self_iff {g : G} {X : Subgroup G} :
    conjSub g X = X ↔ g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rfl

theorem conjSub_eq_self_of_mem {g : G} {X : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : conjSub g X = X :=
  conjSub_eq_self_iff.mpr hg

theorem mem_conjSub_of_mem_normalizer {g y : G} {X : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hy : y ∈ X) : y ∈ conjSub g X := by
  rwa [conjSub_eq_self_of_mem hg]

theorem normalizer_conjSub (g : G) (X : Subgroup G) :
    Subgroup.normalizer (conjSub g X : Set G) = conjSub g (Subgroup.normalizer (X : Set G)) := by
  ext n
  rw [mem_conjSub_iff, ← conjSub_eq_self_iff, ← conjSub_eq_self_iff]
  have e : conjSub (g⁻¹ * n * g) X = conjSub g⁻¹ (conjSub n (conjSub g X)) := by
    rw [conjSub_conjSub, conjSub_conjSub, mul_assoc]
  rw [e]
  constructor
  · intro h
    rw [h, conjSub_inv_conjSub]
  · intro h
    calc conjSub n (conjSub g X) = conjSub g (conjSub g⁻¹ (conjSub n (conjSub g X))) :=
          (conjSub_conjSub_inv g _).symm
      _ = conjSub g X := by rw [h]

theorem le_normalizer_conjSub {g : G} {C X : Subgroup G}
    (h : C ≤ Subgroup.normalizer (X : Set G)) :
    conjSub g C ≤ Subgroup.normalizer (conjSub g X : Set G) := by
  rw [normalizer_conjSub]
  exact conjSub_mono h

theorem le_normalizer_conjSub_of_eq {g : G} {C X : Subgroup G} (hC : conjSub g C = C)
    (h : C ≤ Subgroup.normalizer (X : Set G)) :
    C ≤ Subgroup.normalizer (conjSub g X : Set G) := by
  rw [← hC]
  exact le_normalizer_conjSub h

theorem conjSub_centralizer_singleton (g t : G) :
    conjSub g (Subgroup.centralizer ({t} : Set G)) =
      Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
  ext y
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * (g * t * g⁻¹) = g * (g⁻¹ * y * g * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * t * g⁻¹ * y := by group
  · intro h
    calc g⁻¹ * y * g * t = g⁻¹ * (y * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * y) * g := by rw [h]
      _ = t * (g⁻¹ * y * g) := by group

theorem conjSub_centralizer (g : G) (H : Subgroup G) :
    conjSub g (Subgroup.centralizer (H : Set G)) =
      Subgroup.centralizer (conjSub g H : Set G) := by
  ext y
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have hk' : g⁻¹ * k * g ∈ H := mem_conjSub_iff.mp hk
    have := h _ hk'
    calc k * y = g * (g⁻¹ * k * g * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * (g⁻¹ * k * g)) * g⁻¹ := by rw [this]
      _ = y * k := by group
  · intro h k hk
    have := h _ (conj_mem_conjSub (g := g) hk)
    calc k * (g⁻¹ * y * g) = g⁻¹ * (g * k * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * k * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * y * g * k := by group

theorem mem_normalizer_of_conjSub_le [Finite G] {g : G} {X : Subgroup G}
    (h : conjSub g X ≤ X) : g ∈ Subgroup.normalizer (X : Set G) :=
  conjSub_eq_self_iff.mp (Subgroup.eq_of_le_of_card_ge h (card_conjSub g X).ge)

theorem mem_normalizer_of_conj_mem [Finite G] {g : G} {X : Subgroup G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  apply mem_normalizer_of_conjSub_le
  intro y hy
  have := h _ (mem_conjSub_iff.mp hy)
  rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this

theorem le_normalizer_sup {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  (le_inf hA hB).trans (normalizer_inf_normalizer_le_normalizer_sup A B)

theorem le_normalizer_inf {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  (le_inf hA hB).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem sup_mul_comm_of_le {R V C : Subgroup G} (hRC : R ≤ C)
    (hCV : C ≤ Subgroup.normalizer (V : Set G)) :
    ((R ⊔ V : Subgroup G) : Set G) * (C : Set G) =
      (C : Set G) * ((R ⊔ V : Subgroup G) : Set G) := by
  have h1 : ((R ⊔ V : Subgroup G) : Set G) * (C : Set G) = ((C ⊔ V : Subgroup G) : Set G) := by
    apply le_antisymm
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact (C ⊔ V).mul_mem (sup_le_sup_right hRC V ha) (Subgroup.mem_sup_left hb)
    · rw [sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left V C hCV]
      exact Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr le_sup_right)
  have h2 : (C : Set G) * ((R ⊔ V : Subgroup G) : Set G) = ((C ⊔ V : Subgroup G) : Set G) := by
    apply le_antisymm
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact (C ⊔ V).mul_mem (Subgroup.mem_sup_left ha) (sup_le_sup_right hRC V hb)
    · rw [Subgroup.coe_mul_of_left_le_normalizer_right C V hCV]
      exact Set.mul_subset_mul_left (SetLike.coe_subset_coe.mpr le_sup_right)
  rw [h1, h2]

theorem isPGroup_pCoreIn (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreIn p H) :=
  IsPGroup.map CFSG.pCore_isPGroup H.subtype

theorem le_normalizer_pCoreIn (p : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pCoreIn p H : Set G) :=
  le_normalizer_map_subtype H (CFSG.pCore p H)

theorem le_pCoreIn {p : ℕ} {X H : Subgroup G} (hXH : X ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (X : Set G)) (hX : IsPGroup p X) : X ≤ pCoreIn p H := by
  have hnormal : (X.subgroupOf H).Normal := by
    constructor
    intro a ha h
    exact (Subgroup.mem_normalizer_iff.mp (hnorm h.property) a).mp ha
  have hle : X.subgroupOf H ≤ CFSG.pCore p H :=
    le_sSup ⟨hnormal, hX.comap_subtype⟩
  intro x hx
  exact ⟨⟨x, hXH hx⟩, hle hx, rfl⟩

theorem conjSub_pCoreIn (p : ℕ) (g : G) (H : Subgroup G) :
    conjSub g (pCoreIn p H) = pCoreIn p (conjSub g H) := by
  have key : ∀ (g : G) (H : Subgroup G), conjSub g (pCoreIn p H) ≤ pCoreIn p (conjSub g H) :=
    fun g H => le_pCoreIn (conjSub_mono (pCoreIn_le p H))
      (le_normalizer_conjSub (le_normalizer_pCoreIn p H)) (isPGroup_conjSub
        (isPGroup_pCoreIn p H) g)
  refine le_antisymm (key g H) ?_
  have h := key g⁻¹ (conjSub g H)
  rw [conjSub_inv_conjSub] at h
  rw [le_conjSub_iff]
  exact h

theorem conjSub_oddCoreIn [Finite G] (g : G) (H : Subgroup G) :
    conjSub g (oddCoreIn H) = oddCoreIn (conjSub g H) := by
  have key : ∀ (g : G) (H : Subgroup G), conjSub g (oddCoreIn H) ≤ oddCoreIn (conjSub g H) :=
    fun g H => le_oddCoreIn (conjSub_mono (oddCoreIn_le H))
      (le_normalizer_conjSub (le_normalizer_oddCoreIn H))
      (by rw [card_conjSub]; exact odd_card_oddCoreIn H)
  refine le_antisymm (key g H) ?_
  have h := key g⁻¹ (conjSub g H)
  rw [conjSub_inv_conjSub] at h
  rw [le_conjSub_iff]
  exact h

theorem normalizer_le_normalizer_oddCoreIn [Finite G] (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (oddCoreIn H : Set G) := by
  intro g hg
  rw [← conjSub_eq_self_iff, conjSub_oddCoreIn, conjSub_eq_self_of_mem hg]

theorem normalizer_le_normalizer_pCoreIn (p : ℕ) (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (pCoreIn p H : Set G) := by
  intro g hg
  rw [← conjSub_eq_self_iff, conjSub_pCoreIn, conjSub_eq_self_of_mem hg]

theorem odd_card_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hX : IsPGroup p X) : Odd (Nat.card X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk]
  exact (hp.eq_two_or_odd'.resolve_left hp2).pow

theorem eq_bot_of_isPGroup_of_le [Finite G] {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (hX : IsPGroup p X) (hXK : X ≤ K) (hK : ¬ p ∣ Nat.card K) : X = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  apply Subgroup.eq_bot_of_card_eq
  rcases k with _ | k
  · simpa using hk
  · exact absurd ((Dvd.intro_left _ (pow_succ p k).symm).trans
      (hk ▸ Subgroup.card_dvd_of_le hXK)) hK

theorem inf_eq_bot_of_isPGroup [Finite G] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {X Y : Subgroup G} (hX : IsPGroup p X) (hY : IsPGroup q Y) : X ⊓ Y = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  refine eq_bot_of_isPGroup_of_le hp (hX.to_le inf_le_left) inf_le_right ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY
  rw [hk]
  intro hdvd
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))

theorem isSylowOf_bot [Finite G] {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hK : ¬ p ∣ Nat.card K) : IsSylowOf p ⊥ K := by
  refine isSylowOf_of_card bot_le ?_
  rw [Subgroup.card_bot, Nat.factorization_eq_zero_of_not_dvd hK, pow_zero]

theorem isSylowOf_self [Finite G] {p : ℕ} [Fact p.Prime] {X : Subgroup G}
    (hX : IsPGroup p X) : IsSylowOf p X X :=
  isSylowOf_iff.mpr ⟨le_rfl, hX, by
    rw [Subgroup.relIndex_self]; exact (Fact.out : p.Prime).not_dvd_one⟩

theorem isSylowOf_conjSub [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (h : IsSylowOf p P K) (g : G) : IsSylowOf p (conjSub g P) (conjSub g K) :=
  isSylowOf_of_card (conjSub_mono h.le) (by rw [card_conjSub, card_conjSub, h.card_eq])

theorem exists_le_conjSub_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {P K X : Subgroup G}
    (hP : IsSylowOf p P K) (hXK : X ≤ K) (hX : IsPGroup p X) :
    ∃ c ∈ K, X ≤ conjSub c P := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', hQ'⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hx' : (⟨x, hXK hx⟩ : K) ∈ ((c • Q : Sylow p K) : Subgroup K) := hQ' hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
  rw [mem_conjSub_iff]
  refine ⟨_, hx', ?_⟩
  simp [MulAut.inv_apply]

theorem isSylowOf_sup [Finite G] {p : ℕ} [Fact p.Prime] {A B R Z : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hR : IsSylowOf p R A) (hZ : IsSylowOf p Z B)
    (hRZ : R ≤ Subgroup.normalizer (Z : Set G)) (hinf : R ⊓ Z = ⊥) :
    IsSylowOf p (R ⊔ Z) (A ⊔ B) := by
  have hp : p.Prime := Fact.out
  have hle : R ⊔ Z ≤ A ⊔ B := sup_le_sup hR.le hZ.le
  refine isSylowOf_iff.mpr ⟨hle, hR.isPGroup.to_sup_of_normal_right' hZ.isPGroup hRZ, ?_⟩
  have h1 := card_sup_mul_card_inf_of_le_normalizer hAB
  have h2 := card_sup_mul_card_inf_of_le_normalizer hRZ
  rw [sup_comm B, inf_comm B] at h1
  rw [sup_comm Z, inf_comm Z, hinf, Subgroup.card_bot, mul_one] at h2
  have hA := Subgroup.relIndex_mul_card R A
  have hB := Subgroup.relIndex_mul_card Z B
  have hK := Subgroup.relIndex_mul_card (R ⊔ Z) (A ⊔ B)
  rw [inf_eq_left.mpr hR.le] at hA
  rw [inf_eq_left.mpr hZ.le] at hB
  rw [inf_eq_left.mpr hle] at hK
  have hpos : 0 < Nat.card (R ⊔ Z : Subgroup G) := Nat.card_pos
  have key : (R ⊔ Z).relIndex (A ⊔ B) * Nat.card (A ⊓ B : Subgroup G) =
      R.relIndex A * Z.relIndex B := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (R ⊔ Z).relIndex (A ⊔ B) * Nat.card (A ⊓ B : Subgroup G) * Nat.card (R ⊔ Z : Subgroup G)
        = Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) := by rw [← hK]; ring
      _ = R.relIndex A * Nat.card R * (Z.relIndex B * Nat.card Z) := by
          rw [h1, ← hA, ← hB]; ring
      _ = R.relIndex A * Z.relIndex B * Nat.card (R ⊔ Z : Subgroup G) := by rw [h2]; ring
  intro hdvd
  have : p ∣ R.relIndex A * Z.relIndex B := key ▸ hdvd.mul_right _
  rcases hp.dvd_mul.mp this with h | h
  · exact (isSylowOf_iff.mp hR).2.2 h
  · exact (isSylowOf_iff.mp hZ).2.2 h

theorem le_sup_of_isSylowOf_sup [Finite G] {p : ℕ} [Fact p.Prime] {R Z K U : Subgroup G}
    (hRZ : IsSylowOf p (R ⊔ Z) K) (hZ : IsPGroup p Z) (hUK : U ≤ K) (hU : IsPGroup p U)
    (hRU : R ≤ U) (hUZ : U ≤ Subgroup.normalizer (Z : Set G)) : U ≤ R ⊔ Z := by
  have hZK : Z ≤ K := le_sup_right.trans hRZ.le
  have h := hRZ.eq_of_le (sup_le_sup_right hRU Z) (sup_le hUK hZK)
    (hU.to_sup_of_normal_right' hZ hUZ)
  exact h ▸ le_sup_left

theorem le_of_isSylowOf_of_le_normalizer [Finite G] {p : ℕ} [Fact p.Prime] {Z K U : Subgroup G}
    (hZ : IsSylowOf p Z K) (hUK : U ≤ K) (hU : IsPGroup p U)
    (hUZ : U ≤ Subgroup.normalizer (Z : Set G)) : U ≤ Z := by
  have h := hZ.eq_of_le le_sup_right (sup_le hUK hZ.le) (hU.to_sup_of_normal_right' hZ.isPGroup hUZ)
  exact le_sup_left.trans h.le

theorem sup_inf_eq_of_le {A B K : Subgroup G} (hBK : B ≤ K)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) : (A ⊔ B) ⊓ K = (A ⊓ K) ⊔ B := by
  refine le_antisymm ?_ (sup_le (inf_le_inf_right K le_sup_left) (le_inf le_sup_right hBK))
  rintro y ⟨hy, hyK⟩
  have hy' : y ∈ ((A ⊔ B : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAB] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  have haK : a ∈ K := by
    have := K.mul_mem hyK (K.inv_mem (hBK hb))
    rwa [mul_inv_cancel_right] at this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ha, haK⟩) (Subgroup.mem_sup_right hb)

theorem le_centralizer_of_inf_eq_bot {X Y : Subgroup G}
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hYX : Y ≤ Subgroup.normalizer (X : Set G))
    (h : X ⊓ Y = ⊥) : X ≤ Subgroup.centralizer (Y : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ Y :=
    Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXY hx) y).mp hy) (Y.inv_mem hy)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ X := by
    have := X.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hYX hy) x⁻¹).mp (X.inv_mem hx))
    rwa [show x * (y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ by group] at this
  have h3 : x * y * x⁻¹ * y⁻¹ = 1 := by
    have : x * y * x⁻¹ * y⁻¹ ∈ X ⊓ Y := ⟨h2, h1⟩
    rwa [h, Subgroup.mem_bot] at this
  calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
    _ = x * y := by rw [h3, inv_one, one_mul]

theorem mul_comm_of_conj_eq_inv {t : G} {B : Subgroup G} (h : ∀ y ∈ B, t * y * t⁻¹ = y⁻¹)
    {u v : G} (hu : u ∈ B) (hv : v ∈ B) : u * v = v * u := by
  have h1 := h (u * v) (B.mul_mem hu hv)
  rw [show t * (u * v) * t⁻¹ = t * u * t⁻¹ * (t * v * t⁻¹) by group, h u hu, h v hv,
    mul_inv_rev] at h1
  calc u * v = (v⁻¹ * u⁻¹)⁻¹ := by group
    _ = (u⁻¹ * v⁻¹)⁻¹ := by rw [h1]
    _ = v * u := by group

theorem setOf_maximals_ge_eq_pair {𝓢 : Set (Subgroup G)} {R A B : Subgroup G} (hA : A ∈ 𝓢)
    (hB : B ∈ 𝓢) (hRA : R ≤ A) (hRB : R ≤ B) (hcov : ∀ U ∈ 𝓢, R ≤ U → U ≤ A ∨ U ≤ B)
    (hAB : A ≤ B → A = B) (hBA : B ≤ A → B = A) :
    {U | U ∈ maximals 𝓢 ∧ R ≤ U} = {A, B} := by
  have hmaxA : A ∈ maximals 𝓢 := by
    refine ⟨hA, fun U hU hAU => ?_⟩
    rcases hcov U hU (hRA.trans hAU) with h | h
    · exact le_antisymm h hAU
    · have hAB' := hAB (hAU.trans h)
      exact le_antisymm (hAB' ▸ h) hAU
  have hmaxB : B ∈ maximals 𝓢 := by
    refine ⟨hB, fun U hU hBU => ?_⟩
    rcases hcov U hU (hRB.trans hBU) with h | h
    · have hBA' := hBA (hBU.trans h)
      exact le_antisymm (hBA' ▸ h) hBU
    · exact le_antisymm h hBU
  ext U
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hU, hmax⟩, hRU⟩
    rcases hcov U hU hRU with h | h
    · exact Or.inl (hmax A hA h).symm
    · exact Or.inr (hmax B hB h).symm
  · rintro (rfl | rfl)
    · exact ⟨hmaxA, hRA⟩
    · exact ⟨hmaxB, hRB⟩

theorem maximals_eq_pair {𝓢 : Set (Subgroup G)} {A B : Subgroup G} (hA : A ∈ 𝓢) (hB : B ∈ 𝓢)
    (hcov : ∀ U ∈ 𝓢, U ≤ A ∨ U ≤ B) (hAB : A ≤ B → A = B) (hBA : B ≤ A → B = A) :
    maximals 𝓢 = {A, B} := by
  have h := setOf_maximals_ge_eq_pair (R := ⊥) hA hB bot_le bot_le
    (fun U hU _ => hcov U hU) hAB hBA
  simpa using h

theorem conjSub_mem_signalizers_iff {g : G} {H X R : Subgroup G} {p : ℕ} :
    conjSub g R ∈ signalizers (conjSub g H) (conjSub g X) p ↔ R ∈ signalizers H X p := by
  simp only [signalizers, Set.mem_ofPred_eq]
  rw [conjSub_le_conjSub_iff, normalizer_conjSub, conjSub_le_conjSub_iff, ← conjSub_inf,
    conjSub_eq_bot_iff]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  refine ⟨fun h => ?_, fun h => isPGroup_conjSub h g⟩
  have := isPGroup_conjSub h g⁻¹
  rwa [conjSub_inv_conjSub] at this

theorem conjSub_mul_conjSub (g : G) (X Y : Subgroup G) :
    (conjSub g X : Set G) * (conjSub g Y : Set G) = MulAut.conj g '' ((X : Set G) * Y) := by
  rw [coe_conjSub, coe_conjSub, Set.image_mul]

theorem conjSub_mem_signalizersPerm_iff {g : G} {H X Y R : Subgroup G} {p : ℕ} :
    conjSub g R ∈ signalizersPerm (conjSub g H) (conjSub g X) (conjSub g Y) p ↔
      R ∈ signalizersPerm H X Y p := by
  simp only [signalizersPerm, Set.mem_ofPred_eq]
  rw [conjSub_mem_signalizers_iff, conjSub_mul_conjSub, conjSub_mul_conjSub,
    (Set.image_injective.mpr (MulAut.conj g).injective).eq_iff]

theorem signalizers_conjSub (g : G) (H X : Subgroup G) (p : ℕ) :
    signalizers (conjSub g H) (conjSub g X) p = conjSub g '' signalizers H X p := by
  ext U
  constructor
  · intro hU
    refine ⟨conjSub g⁻¹ U, ?_, conjSub_conjSub_inv g U⟩
    rw [← conjSub_mem_signalizers_iff (g := g), conjSub_conjSub_inv]
    exact hU
  · rintro ⟨V, hV, rfl⟩
    exact conjSub_mem_signalizers_iff.mpr hV

theorem signalizersPerm_conjSub (g : G) (H X Y : Subgroup G) (p : ℕ) :
    signalizersPerm (conjSub g H) (conjSub g X) (conjSub g Y) p =
      conjSub g '' signalizersPerm H X Y p := by
  ext U
  constructor
  · intro hU
    refine ⟨conjSub g⁻¹ U, ?_, conjSub_conjSub_inv g U⟩
    rw [← conjSub_mem_signalizersPerm_iff (g := g), conjSub_conjSub_inv]
    exact hU
  · rintro ⟨V, hV, rfl⟩
    exact conjSub_mem_signalizersPerm_iff.mpr hV

theorem maximals_image_conjSub (g : G) (𝓢 : Set (Subgroup G)) :
    maximals (conjSub g '' 𝓢) = conjSub g '' maximals 𝓢 := by
  ext U
  constructor
  · rintro ⟨⟨V, hV, rfl⟩, hmax⟩
    refine ⟨V, ⟨hV, fun W hW hVW => ?_⟩, rfl⟩
    exact conjSub_injective g (hmax _ ⟨W, hW, rfl⟩ (conjSub_mono hVW))
  · rintro ⟨V, ⟨hV, hmax⟩, rfl⟩
    refine ⟨⟨V, hV, rfl⟩, ?_⟩
    rintro _ ⟨W, hW, rfl⟩ hVW
    rw [hmax W hW (conjSub_le_conjSub_iff.mp hVW)]

theorem setOf_image_conjSub_ge (g : G) (𝓢 : Set (Subgroup G)) (R : Subgroup G) :
    {U | U ∈ conjSub g '' 𝓢 ∧ conjSub g R ≤ U} = conjSub g '' {U | U ∈ 𝓢 ∧ R ≤ U} := by
  ext U
  constructor
  · rintro ⟨⟨V, hV, rfl⟩, hRV⟩
    exact ⟨V, ⟨hV, conjSub_le_conjSub_iff.mp hRV⟩, rfl⟩
  · rintro ⟨V, ⟨hV, hRV⟩, rfl⟩
    exact ⟨⟨V, hV, rfl⟩, conjSub_mono hRV⟩

end CFSG.ABGTheoremB.TotallyInverted.DataConstruction
