module

public import CFSG.LocalAnalysis.EvenBN.Common.AffinePlane
public import CFSG.LocalAnalysis.SteinbergCDAffineSharplyTwoTransitive
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDBasic

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaD

variable {G : Type*} [Group G]

theorem mem_map_conj_iff {P : Subgroup G} {h z : G} :
    z ∈ P.map (MulAut.conj h).toMonoidHom ↔ h⁻¹ * z * h ∈ P := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa [mul_assoc] using hp
  · intro hz
    exact ⟨h⁻¹ * z * h, hz, by simp [mul_assoc]⟩

theorem conj_mem_oTwo_of_mem_normalizer {X : Subgroup G} {h g : G}
    (hh : h ∈ normalizer (X : Set G)) (hg : g ∈ oTwo X) : h * g * h⁻¹ ∈ oTwo X := by
  have hX : ∀ x, x ∈ X ↔ h * x * h⁻¹ ∈ X := mem_normalizer_iff.mp hh
  have hle : oTwo X ≤ (oTwo X).comap (MulAut.conj h).toMonoidHom := by
    refine sSup_le fun P hP y hy => ?_
    obtain ⟨hPX, hXP, hP2⟩ := hP
    change h * y * h⁻¹ ∈ oTwo X
    refine le_oTwo (P := P.map (MulAut.conj h).toMonoidHom) ?_ ?_ (hP2.map _) ⟨y, hy, rfl⟩
    · intro z hz
      rw [mem_map_conj_iff] at hz
      have := (hX _).mp (hPX hz)
      simpa [mul_assoc] using this
    · intro x hx
      rw [mem_normalizer_iff]
      intro z
      rw [mem_map_conj_iff, mem_map_conj_iff]
      have hx' : h⁻¹ * x * h ∈ X := (hX (h⁻¹ * x * h)).mpr (by simpa [mul_assoc] using hx)
      have key := mem_normalizer_iff.mp (hXP hx') (h⁻¹ * z * h)
      have e : (h⁻¹ * x * h) * (h⁻¹ * z * h) * (h⁻¹ * x * h)⁻¹ = h⁻¹ * (x * z * x⁻¹) * h := by
        group
      rw [key, e]
  exact hle hg

theorem exists_conj_mem_sylow [Finite G] {Q : Subgroup G} (S : Sylow 2 Q) {x : G} (hx : x ∈ Q)
    {a : ℕ} (hxa : x ^ 2 ^ a = 1) : ∃ g ∈ Q, g * x * g⁻¹ ∈ (S : Subgroup Q).map Q.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x' : Q := ⟨x, hx⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers x') := by
    rintro ⟨y, m, rfl⟩
    refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    change ((x' ^ m) ^ 2 ^ a : Q).1 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have : x' ^ 2 ^ a = 1 := Subtype.ext (by simpa using hxa)
    rw [this, one_zpow]
    rfl
  obtain ⟨S', hS'⟩ := h2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q S' S
  have hmem : x' ∈ (S' : Subgroup Q) := hS' (Subgroup.mem_zpowers x')
  have hg' : g * x' * g⁻¹ ∈ (S : Subgroup Q) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    refine Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr ?_
    simp only [MulAut.smul_def, MulAut.conj_inv_apply]
    convert hmem using 1
    group
  exact ⟨g, g.2, ⟨_, hg', rfl⟩⟩

theorem eq_of_sylow_le {Q : Subgroup G} (S : Sylow 2 Q) {R : Subgroup G} (hRQ : R ≤ Q)
    (hR : IsPGroup 2 R) (hSR : (S : Subgroup Q).map Q.subtype ≤ R) :
    R = (S : Subgroup Q).map Q.subtype := by
  have hR' : IsPGroup 2 (R.subgroupOf Q) := hR.of_equiv (subgroupOfEquivOfLe hRQ).symm
  have hSR' : (S : Subgroup Q) ≤ R.subgroupOf Q := fun s hs =>
    mem_subgroupOf.mpr (hSR ⟨s, hs, rfl⟩)
  have := S.is_maximal' hR' hSR'
  rw [← this, map_subgroupOf_eq_of_le hRQ]

theorem le_sylow_of_le_normalizer [Finite G] {Q B : Subgroup G} (S : Sylow 2 Q) (hBQ : B ≤ Q)
    (hQB : Q ≤ normalizer (B : Set G)) (hB : IsPGroup 2 B) :
    B ≤ (S : Subgroup Q).map Q.subtype := by
  have hn : (B.subgroupOf Q).Normal := (normal_subgroupOf_iff_le_normalizer hBQ).mpr hQB
  have hB' : IsPGroup 2 (B.subgroupOf Q) := hB.of_equiv (subgroupOfEquivOfLe hBQ).symm
  have hle := hB'.le_sylow_of_normal S
  intro b hb
  exact ⟨⟨b, hBQ hb⟩, hle (mem_subgroupOf.mpr hb), rfl⟩

@[expose] def centralizerMod (N K₀ B : Subgroup G) (hK : ∀ g ∈ N, ∀ y ∈ K₀, g * y * g⁻¹ ∈ K₀)
    (hB : ∀ g ∈ N, ∀ b ∈ B, g * b * g⁻¹ ∈ B) : Subgroup G where
  carrier := {g | g ∈ N ∧ ∀ y ∈ K₀, g * y * g⁻¹ * y⁻¹ ∈ B}
  mul_mem' := by
    rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
    refine ⟨mul_mem hgN hhN, fun y hy => ?_⟩
    have e : g * h * y * (g * h)⁻¹ * y⁻¹ =
        g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹) := by group
    rw [e]
    exact mul_mem (hB g hgN _ (hh y hy)) (hg y hy)
  one_mem' := ⟨one_mem N, fun y _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem B⟩
  inv_mem' := by
    rintro g ⟨hgN, hg⟩
    refine ⟨inv_mem hgN, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ K₀ := by simpa using hK g⁻¹ (inv_mem hgN) y hy
    have h1 := inv_mem (hg _ hy')
    have e : (g * (g⁻¹ * y * g) * g⁻¹ * (g⁻¹ * y * g)⁻¹)⁻¹ = g⁻¹ * y * g⁻¹⁻¹ * y⁻¹ := by group
    rwa [e] at h1

theorem mem_centralizerMod {N K₀ B : Subgroup G} {hK : ∀ g ∈ N, ∀ y ∈ K₀, g * y * g⁻¹ ∈ K₀}
    {hB : ∀ g ∈ N, ∀ b ∈ B, g * b * g⁻¹ ∈ B} {g : G} :
    g ∈ centralizerMod N K₀ B hK hB ↔ g ∈ N ∧ ∀ y ∈ K₀, g * y * g⁻¹ * y⁻¹ ∈ B :=
  Iff.rfl

theorem conj_mem_centralizerMod {N K₀ B : Subgroup G} {hK : ∀ g ∈ N, ∀ y ∈ K₀, g * y * g⁻¹ ∈ K₀}
    {hB : ∀ g ∈ N, ∀ b ∈ B, g * b * g⁻¹ ∈ B} {h z : G} (hh : h ∈ N)
    (hz : z ∈ centralizerMod N K₀ B hK hB) : h * z * h⁻¹ ∈ centralizerMod N K₀ B hK hB := by
  obtain ⟨hzN, hz⟩ := hz
  refine ⟨mul_mem (mul_mem hh hzN) (inv_mem hh), fun y hy => ?_⟩
  have hy' : h⁻¹ * y * h ∈ K₀ := by simpa using hK h⁻¹ (inv_mem hh) y hy
  have h1 := hB h hh _ (hz _ hy')
  have e : h * (z * (h⁻¹ * y * h) * z⁻¹ * (h⁻¹ * y * h)⁻¹) * h⁻¹ =
      h * z * h⁻¹ * y * (h * z * h⁻¹)⁻¹ * y⁻¹ := by group
  rwa [e] at h1

theorem exists_mem_ne_ne [Finite G] {Y : Subgroup G} (hY : 2 < Nat.card Y) (a b : G) :
    ∃ z ∈ Y, z ≠ a ∧ z ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : (Y : Set G) ⊆ {a, b} := fun z hz => by
    by_cases hza : z = a
    · exact Or.inl hza
    · exact Or.inr (hcon z hz hza)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at hle
  have h2 : ({a, b} : Set G).ncard ≤ 2 := by
    refine (Set.ncard_insert_le a {b}).trans ?_
    rw [Set.ncard_singleton]
  omega

theorem pCore_map_eq_oTwo [Finite G] (H : Subgroup G) :
    (CFSG.pCore 2 H).map H.subtype = oTwo H := by
  apply le_antisymm
  · refine le_oTwo (map_subtype_le _) (fun g hg => ?_) (CFSG.pCore_isPGroup.map _)
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, CFSG.pCore_normal.conj_mem y hy _, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨⟨g, hg⟩⁻¹ * y * ⟨g, hg⟩⁻¹⁻¹, CFSG.pCore_normal.conj_mem y hy _, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hyx ⊢
      rw [hyx]
      group
  · have hn : ((oTwo H).subgroupOf H).Normal :=
      (normal_subgroupOf_iff_le_normalizer (oTwo_le H)).mpr (le_normalizer_oTwo H)
    have h2 : IsPGroup 2 ((oTwo H).subgroupOf H) :=
      (isPGroup_oTwo H).of_equiv (subgroupOfEquivOfLe (oTwo_le H)).symm
    have hle : (oTwo H).subgroupOf H ≤ CFSG.pCore 2 H := le_sSup ⟨hn, h2⟩
    intro x hx
    exact ⟨⟨x, oTwo_le H hx⟩, hle (mem_subgroupOf.mpr hx), rfl⟩

structure CosetData (H Y : Subgroup G) (t : G) : Prop where
  mul_self : t * t = 1
  le_centralizer : Y ≤ centralizer ({t} : Set G)
  isElementaryAbelian : IsElementaryAbelian 2 Y
  le_normalizer : H ≤ normalizer (Y : Set G)
  crossed_mem : ∀ h ∈ H, h⁻¹ * t * h * t ∈ Y

namespace CosetData

variable {H Y : Subgroup G} {t : G}

theorem of_le_normalizer (ht : t * t = 1) (hYt : Y ≤ centralizer ({t} : Set G))
    (hY : IsElementaryAbelian 2 Y) (hHY : H ≤ normalizer (Y : Set G))
    (hHE : H ≤ normalizer ((Y ⊔ zpowers t : Subgroup G) : Set G)) : CosetData H Y t := by
  refine ⟨ht, hYt, hY, hHY, fun h hh => ?_⟩
  have hw := CFSG.LocalAnalysis.EvenBN.LinearThree.Plane.conj_mem_coset ht hYt
    (hHY (inv_mem hh)) (hHE (inv_mem hh))
  rw [inv_inv] at hw
  set w := t⁻¹ * (h⁻¹ * t * h) with hwdef
  have htw : t * w = w * t := (mem_centralizer_singleton_iff.mp (hYt hw)).symm
  have e : h⁻¹ * t * h * t = w := by
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    calc h⁻¹ * t * h * t = t * (t⁻¹ * (h⁻¹ * t * h)) * t := by group
      _ = t * w * t := by rw [hwdef]
      _ = w * (t * t) := by rw [htw, mul_assoc]
      _ = w := by rw [ht, mul_one]
  rw [e]
  exact hw

variable (h : CosetData H Y t)
include h

theorem inv_eq : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.mul_self

theorem comm_of_mem {y : G} (hy : y ∈ Y) : t * y = y * t :=
  (mem_centralizer_singleton_iff.mp (h.le_centralizer hy)).symm

theorem mul_comm_of_mem {x y : G} (hx : x ∈ Y) (hy : y ∈ Y) : x * y = y * x := by
  have := h.isElementaryAbelian
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Y) ⟨y, hy⟩)

theorem mul_self_of_mem {y : G} (hy : y ∈ Y) : y * y = 1 := by
  have := h.isElementaryAbelian
  rw [← sq]
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian y hy

theorem conj_eq_mul {g : G} (hg : g ∈ H) : g⁻¹ * t * g = t * (g⁻¹ * t * g * t) := by
  have hc := h.comm_of_mem (h.crossed_mem g hg)
  calc g⁻¹ * t * g = g⁻¹ * t * g * t * t := by rw [mul_assoc _ t t, h.mul_self, mul_one]
    _ = t * (g⁻¹ * t * g * t) := by rw [← hc]

theorem crossed_eq_iff {v y : G} (hy : y ∈ Y) : v⁻¹ * t * v * t = y ↔ v⁻¹ * t * v = t * y := by
  constructor
  · intro e
    calc v⁻¹ * t * v = v⁻¹ * t * v * t * t := by rw [mul_assoc _ t t, h.mul_self, mul_one]
      _ = y * t := by rw [e]
      _ = t * y := (h.comm_of_mem hy).symm
  · intro e
    rw [e, mul_assoc, ← h.comm_of_mem hy, ← mul_assoc, h.mul_self, one_mul]

theorem conj_mem_inf_centralizer {g v : G} (hg : g ∈ H) (hv : v ∈ H ⊓ centralizer (Y : Set G)) :
    g * v * g⁻¹ ∈ H ⊓ centralizer (Y : Set G) := by
  refine ⟨mul_mem (mul_mem hg hv.1) (H.inv_mem hg), mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ Y := by
    have := (mem_normalizer_iff.mp (h.le_normalizer (H.inv_mem hg)) y).mp hy
    rwa [inv_inv] at this
  have hc := mem_centralizer_iff.mp hv.2 _ hy'
  calc y * (g * v * g⁻¹) = g * ((g⁻¹ * y * g) * v) * g⁻¹ := by group
    _ = g * (v * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
    _ = g * v * g⁻¹ * y := by group

theorem conj_mem_kernel {g k : G} (hg : g ∈ H)
    (hk : k ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G)) :
    g * k * g⁻¹ ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G) := by
  refine ⟨h.conj_mem_inf_centralizer hg hk.1, mem_centralizer_singleton_iff.mpr ?_⟩
  have hkt : k * t = t * k := mem_centralizer_singleton_iff.mp hk.2
  obtain ⟨c, hcY, hce⟩ : ∃ c ∈ Y, g⁻¹ * t * g = t * c :=
    ⟨_, h.crossed_mem g hg, h.conj_eq_mul hg⟩
  have hkc : k * c = c * k := (mem_centralizer_iff.mp hk.1.2 _ hcY).symm
  have hk' : k * (g⁻¹ * t * g) = (g⁻¹ * t * g) * k := by
    rw [hce, ← mul_assoc, hkt, mul_assoc, hkc, ← mul_assoc]
  calc g * k * g⁻¹ * t = g * (k * (g⁻¹ * t * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * t * g) * k) * g⁻¹ := by rw [hk']
    _ = t * (g * k * g⁻¹) := by group

theorem pow_odd {y : G} (hy : y ∈ Y) {m : ℕ} (hm : Odd m) : y ^ m = y := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, h.mul_self_of_mem hy, one_pow, one_mul]

theorem crossed_mem_of_mem {x : G} (hx : x ∈ H ⊓ centralizer (Y : Set G)) :
    x⁻¹ * t * x * t ∈ Y :=
  h.crossed_mem x hx.1

theorem crossed_mul_of_mem {x z : G} (hx : x ∈ H ⊓ centralizer (Y : Set G))
    (hz : z ∈ H ⊓ centralizer (Y : Set G)) :
    (x * z)⁻¹ * t * (x * z) * t = (x⁻¹ * t * x * t) * (z⁻¹ * t * z * t) :=
  crossed_mul h.mul_self (mem_centralizer_iff.mp hz.2 _ (h.crossed_mem_of_mem hx))

theorem crossed_inv_of_mem {x : G} (hx : x ∈ H ⊓ centralizer (Y : Set G)) :
    x⁻¹⁻¹ * t * x⁻¹ * t = (x⁻¹ * t * x * t)⁻¹ :=
  crossed_inv h.mul_self (mem_centralizer_iff.mp hx.2 _ (h.crossed_mem_of_mem hx))

theorem crossed_pow_of_mem {x : G} (hx : x ∈ H ⊓ centralizer (Y : Set G)) (m : ℕ) :
    (x ^ m)⁻¹ * t * x ^ m * t = (x⁻¹ * t * x * t) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, inv_one, one_mul, mul_one, h.mul_self]
  | succ m ih => rw [pow_succ, h.crossed_mul_of_mem (pow_mem hx m) hx, ih, pow_succ]

theorem crossed_conj_of_mem {g x : G} (hg : g ∈ H ⊓ centralizer (Y : Set G))
    (hx : x ∈ H ⊓ centralizer (Y : Set G)) :
    (g * x * g⁻¹)⁻¹ * t * (g * x * g⁻¹) * t = x⁻¹ * t * x * t := by
  rw [h.crossed_mul_of_mem (mul_mem hg hx) (inv_mem hg), h.crossed_mul_of_mem hg hx,
    h.crossed_inv_of_mem hg, h.mul_comm_of_mem (h.crossed_mem_of_mem hg)
      (h.crossed_mem_of_mem hx), mul_assoc, mul_inv_cancel, mul_one]

end CosetData

theorem mul_inv_mem_centralizer_of_conj_eq {p q t : G} (e : p⁻¹ * t * p = q⁻¹ * t * q) :
    q * p⁻¹ ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  calc q * p⁻¹ * t = q * (p⁻¹ * t * p) * p⁻¹ := by group
    _ = q * (q⁻¹ * t * q) * p⁻¹ := by rw [e]
    _ = t * (q * p⁻¹) := by group

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ g' : G, g' ∈ normalizer (A : Set G) → g' ∈ normalizer (B : Set G) →
      A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g').toMonoidHom := fun g' hA' hB' =>
    sup_le (fun a ha => mem_sup_left ((mem_normalizer_iff.mp hA' a).mp ha))
      (fun b hb => mem_sup_right ((mem_normalizer_iff.mp hB' b).mp hb))
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hA hB hx, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hA) (inv_mem hB) hx
  simpa [mul_assoc] using this

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_inf, mem_inf, mem_normalizer_iff.mp hA x, mem_normalizer_iff.mp hB x]

namespace CosetData

variable {H Y : Subgroup G} {t : G} (h : CosetData H Y t)
include h

theorem two_core [Finite G] {B : Subgroup G} (hB2 : IsPGroup 2 B)
    (hBK : B ≤ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G))
    (hBn : H ≤ normalizer (B : Set G))
    (hBmax : ∀ R : Subgroup G, R ≤ H ⊓ centralizer ({t} : Set G) →
      H ⊓ centralizer ({t} : Set G) ≤ normalizer (R : Set G) → IsPGroup 2 R → R ≤ B)
    (hQtr : ∀ y ∈ Y, ∃ q ∈ H ⊓ centralizer (Y : Set G),
      (∀ k ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G), q * k * q⁻¹ * k⁻¹ ∈ B) ∧
        q⁻¹ * t * q = t * y) :
    oTwo H ≤ centralizer (Y : Set G) ∧
      (∀ d ∈ oTwo H, ∀ k ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G),
        d * k * d⁻¹ * k⁻¹ ∈ B) ∧
      oTwo H ⊓ centralizer ({t} : Set G) = B ∧
      (∀ y ∈ Y, ∃ d ∈ oTwo H, d⁻¹ * t * d = t * y) ∧
      ∀ g ∈ H, ∃ c ∈ H ⊓ centralizer ({t} : Set G), ∃ d ∈ oTwo H, g = c * d := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := H ⊓ centralizer (Y : Set G) with hV
  set K₀ := V ⊓ centralizer ({t} : Set G) with hK₀
  have hBn' : ∀ g ∈ H, ∀ b ∈ B, g * b * g⁻¹ ∈ B := fun g hg b hb =>
    (mem_normalizer_iff.mp (hBn hg) b).mp hb
  have hK : ∀ g ∈ H, ∀ k ∈ K₀, g * k * g⁻¹ ∈ K₀ := fun g hg k hk => h.conj_mem_kernel hg hk
  set E := centralizerMod H K₀ B hK hBn' with hE
  set Q := V ⊓ E with hQ
  have hQH : Q ≤ H := fun q hq => hq.1.1
  have hQn : ∀ g ∈ H, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    ⟨h.conj_mem_inf_centralizer hg hq.1, conj_mem_centralizerMod hg hq.2⟩
  have hHQ : H ≤ normalizer (Q : Set G) := fun g hg => by
    rw [mem_normalizer_iff]
    intro q
    refine ⟨hQn g hg q, fun hq => ?_⟩
    have := hQn g⁻¹ (H.inv_mem hg) _ hq
    simpa [mul_assoc] using this
  have hcQ : ∀ y ∈ Y, ∃ q ∈ Q, q⁻¹ * t * q = t * y := by
    intro y hy
    obtain ⟨q, hq, hqK, hqt⟩ := hQtr y hy
    exact ⟨q, ⟨hq, hq.1, hqK⟩, hqt⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 Q) := inferInstance
  set P : Subgroup G := (S : Subgroup Q).map Q.subtype with hP
  have hPQ : P ≤ Q := map_subtype_le _
  have hP2 : IsPGroup 2 P := S.isPGroup'.map _
  have hBQ : B ≤ Q := by
    intro b hb
    refine ⟨(hBK hb).1, (hBK hb).1.1, fun k hk => ?_⟩
    have e : b * k * b⁻¹ * k⁻¹ = b * (k * b⁻¹ * k⁻¹) := by group
    rw [e]
    exact mul_mem hb (hBn' k hk.1.1 _ (inv_mem hb))
  have hBP : B ≤ P := le_sylow_of_le_normalizer S hBQ (hQH.trans hBn) hB2
  have hcP : ∀ y ∈ Y, ∃ p ∈ P, p⁻¹ * t * p = t * y := by
    intro y hy
    obtain ⟨q, hq, hqt⟩ := hcQ y hy
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos q).ne'
    have hxa : (q ^ m) ^ 2 ^ a = 1 := by
      rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
    obtain ⟨g, hg, hgx⟩ := exists_conj_mem_sylow S (pow_mem hq m) hxa
    refine ⟨g * q ^ m * g⁻¹, hgx, ?_⟩
    rw [← h.crossed_eq_iff hy, h.crossed_conj_of_mem hg.1 (pow_mem hq.1 m),
      h.crossed_pow_of_mem hq.1 m, (h.crossed_eq_iff hy).mpr hqt, h.pow_odd hy hm]
  have hPn : ∀ q ∈ Q, ∀ x ∈ P, q * x * q⁻¹ ∈ P := by
    intro q hq x hx
    obtain ⟨p, hp, hpt⟩ := hcP _ (h.crossed_mem q hq.1.1)
    rw [← h.conj_eq_mul hq.1.1] at hpt
    have hzt := mul_inv_mem_centralizer_of_conj_eq hpt
    have hzQ : q * p⁻¹ ∈ Q := mul_mem hq (inv_mem (hPQ hp))
    have hzK : q * p⁻¹ ∈ K₀ := ⟨hzQ.1, hzt⟩
    have hw : p * x * p⁻¹ ∈ P := mul_mem (mul_mem hp hx) (inv_mem hp)
    have hzw : ∀ w ∈ P, (q * p⁻¹) * w * (q * p⁻¹)⁻¹ ∈ P := by
      intro w hwP
      have hw' : w⁻¹ ∈ E := (hPQ (inv_mem hwP)).2
      have hb := hw'.2 _ hzK
      rw [inv_inv] at hb
      have e : (q * p⁻¹) * w * (q * p⁻¹)⁻¹ = w * (w⁻¹ * (q * p⁻¹) * w * (q * p⁻¹)⁻¹) := by
        group
      rw [e]
      exact mul_mem hwP (hBP hb)
    have e : q * x * q⁻¹ = (q * p⁻¹) * (p * x * p⁻¹) * (q * p⁻¹)⁻¹ := by group
    rw [e]
    exact hzw _ hw
  have hQP : Q ≤ normalizer (P : Set G) := fun q hq => by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hPn q hq x, fun hx => ?_⟩
    have := hPn q⁻¹ (inv_mem hq) _ hx
    simpa [mul_assoc] using this
  have hoQ : oTwo Q = P := eq_of_sylow_le S (oTwo_le Q) (isPGroup_oTwo Q) (le_oTwo hPQ hQP hP2)
  have hHP : H ≤ normalizer (P : Set G) := fun g hg => by
    rw [← hoQ]
    rw [mem_normalizer_iff]
    intro x
    refine ⟨conj_mem_oTwo_of_mem_normalizer (hHQ hg), fun hx => ?_⟩
    have := conj_mem_oTwo_of_mem_normalizer (hHQ (H.inv_mem hg)) hx
    simpa [mul_assoc] using this
  have hPH : P ≤ H := hPQ.trans hQH
  have hfac : ∀ g ∈ H, ∃ c ∈ H ⊓ centralizer ({t} : Set G), ∃ d ∈ P, g = c * d := by
    intro g hg
    obtain ⟨p, hp, hpt⟩ := hcP _ (h.crossed_mem g hg)
    rw [← h.conj_eq_mul hg] at hpt
    exact ⟨g * p⁻¹, ⟨mul_mem hg (H.inv_mem (hPH hp)), mul_inv_mem_centralizer_of_conj_eq hpt⟩,
      p, hp, by group⟩
  have hPt : P ⊓ centralizer ({t} : Set G) = B := by
    apply le_antisymm
    · refine hBmax _ (inf_le_inf_right _ hPH) (fun c hc => ?_) (hP2.to_le inf_le_left)
      exact mem_normalizer_inf (hHP hc.1) (Subgroup.le_normalizer hc.2)
    · exact le_inf hBP fun b hb => (hBK hb).2
  have hoH : oTwo H = P := by
    apply le_antisymm
    · intro r hr
      have hR2 : IsPGroup 2 ↥(oTwo H ⊔ P) :=
        IsPGroup.to_sup_of_normal_right' (isPGroup_oTwo H) hP2 ((oTwo_le H).trans hHP)
      obtain ⟨c, hc, d, hd, rfl⟩ := hfac r (oTwo_le H hr)
      have hcR : c ∈ oTwo H ⊔ P := by
        have e : c = (c * d) * d⁻¹ := by group
        rw [e]
        exact mul_mem (mem_sup_left hr) (mem_sup_right (inv_mem hd))
      have hcB : c ∈ B := by
        refine hBmax ((oTwo H ⊔ P) ⊓ centralizer ({t} : Set G))
          (inf_le_inf_right _ (sup_le (oTwo_le H) hPH)) (fun c' hc' => ?_)
          (hR2.to_le inf_le_left) ⟨hcR, hc.2⟩
        exact mem_normalizer_inf (mem_normalizer_sup (le_normalizer_oTwo H hc'.1) (hHP hc'.1))
          (Subgroup.le_normalizer hc'.2)
      exact mul_mem (hBP hcB) hd
    · exact le_oTwo hPH hHP hP2
  rw [hoH]
  exact ⟨fun x hx => (hPQ hx).1.2, fun d hd k hk => (hPQ hd).2.2 k hk, hPt, hcP, hfac⟩

theorem exists_mulEquiv_quotient {D B : Subgroup G} (hDH : D ≤ H)
    (hDY : D ≤ centralizer (Y : Set G)) (hDB : D ⊓ centralizer ({t} : Set G) = B)
    (htrD : ∀ y ∈ Y, ∃ d ∈ D, d⁻¹ * t * d = t * y) [(B.subgroupOf D).Normal] :
    ∃ φ : D ⧸ B.subgroupOf D ≃* Y,
      (∀ d : D, (φ (QuotientGroup.mk d) : G) = (d : G)⁻¹ * t * d * t) ∧
      ∀ c ∈ H ⊓ centralizer ({t} : Set G), ∀ (d : D) (hd : c * d * c⁻¹ ∈ D),
        (φ (QuotientGroup.mk ⟨c * d * c⁻¹, hd⟩) : G) = c * φ (QuotientGroup.mk d) * c⁻¹ := by
  let f := crossedHom h.mul_self Y D hDY fun d hd => h.crossed_mem d (hDH hd)
  have hker : f.ker = B.subgroupOf D := by
    ext d
    rw [mem_ker_crossedHom, mem_subgroupOf, ← hDB, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun e => ⟨d.2, e⟩, fun e => e.2⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨d, hd, hdt⟩ := htrD y hy
    exact ⟨⟨d, hd⟩, Subtype.ext ((h.crossed_eq_iff hy).mpr hdt)⟩
  let φ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  refine ⟨φ, fun d => rfl, fun c hc d hd => ?_⟩
  show (c * d * c⁻¹)⁻¹ * t * (c * d * c⁻¹) * t = c * ((d : G)⁻¹ * t * d * t) * c⁻¹
  exact crossed_conj (mem_centralizer_singleton_iff.mp hc.2)

theorem normal_subgroupOf {D B : Subgroup G} (hDH : D ≤ H) (hDY : D ≤ centralizer (Y : Set G))
    (hDB : D ⊓ centralizer ({t} : Set G) = B) : (B.subgroupOf D).Normal := by
  let f := crossedHom h.mul_self Y D hDY fun d hd => h.crossed_mem d (hDH hd)
  have hker : f.ker = B.subgroupOf D := by
    ext d
    rw [mem_ker_crossedHom, mem_subgroupOf, ← hDB, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun e => ⟨d.2, e⟩, fun e => e.2⟩
  rw [← hker]
  infer_instance

theorem transitive_of_le {B : Subgroup G}
    (hKB : H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G) ≤ B)
    (htr : ∀ y ∈ Y, ∃ v ∈ H ⊓ centralizer (Y : Set G), v⁻¹ * t * v = t * y) :
    ∀ y ∈ Y, ∃ q ∈ H ⊓ centralizer (Y : Set G),
      (∀ k ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G), q * k * q⁻¹ * k⁻¹ ∈ B) ∧
        q⁻¹ * t * q = t * y := by
  intro y hy
  obtain ⟨v, hv, hvt⟩ := htr y hy
  exact ⟨v, hv, fun k hk => hKB (mul_mem (h.conj_mem_kernel hv.1 hk) (inv_mem hk)), hvt⟩

theorem transitive_of_transitive [Finite G] {A B : Subgroup G} (hBn : H ≤ normalizer (B : Set G))
    (hAH : A ≤ H ⊓ centralizer ({t} : Set G))
    (hAK : ∀ a ∈ A, ∀ k ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G),
      a * k * a⁻¹ * k⁻¹ ∈ B)
    (hAtr : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ 1 → y' ≠ 1 → ∃ a ∈ A, a * y * a⁻¹ = y')
    (hY : 2 < Nat.card Y)
    (htr : ∀ y ∈ Y, ∃ v ∈ H ⊓ centralizer (Y : Set G), v⁻¹ * t * v = t * y) :
    ∀ y ∈ Y, ∃ q ∈ H ⊓ centralizer (Y : Set G),
      (∀ k ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G), q * k * q⁻¹ * k⁻¹ ∈ B) ∧
        q⁻¹ * t * q = t * y := by
  set V := H ⊓ centralizer (Y : Set G) with hV
  set K₀ := V ⊓ centralizer ({t} : Set G) with hK₀
  have hBn' : ∀ g ∈ H, ∀ b ∈ B, g * b * g⁻¹ ∈ B := fun g hg b hb =>
    (mem_normalizer_iff.mp (hBn hg) b).mp hb
  have hK : ∀ g ∈ H, ∀ k ∈ K₀, g * k * g⁻¹ ∈ K₀ := fun g hg k hk => h.conj_mem_kernel hg hk
  set Q := V ⊓ centralizerMod H K₀ B hK hBn' with hQ
  have hcomm : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ Q := by
    intro a ha v hv
    have haH := (hAH ha).1
    have hw : a * v * a⁻¹ * v⁻¹ ∈ V :=
      mul_mem (h.conj_mem_inf_centralizer haH hv) (inv_mem hv)
    refine ⟨hw, hw.1, fun k hk => ?_⟩
    set k₁ := v⁻¹ * k * v with hk₁
    have hk₁K : k₁ ∈ K₀ := by
      have := hK v⁻¹ (H.inv_mem hv.1) k hk
      rwa [inv_inv] at this
    have hb₁ := hAK a⁻¹ (inv_mem ha) k₁ hk₁K
    have hb₃ := hAK a ha k hk
    have e : a * v * a⁻¹ * v⁻¹ * k * (a * v * a⁻¹ * v⁻¹)⁻¹ * k⁻¹ =
        a * (v * (a⁻¹ * k₁ * a⁻¹⁻¹ * k₁⁻¹) * v⁻¹) * a⁻¹ * (a * k * a⁻¹ * k⁻¹) := by
      rw [hk₁]
      group
    rw [e]
    exact mul_mem (hBn' a haH _ (hBn' v hv.1 _ hb₁)) hb₃
  have hcr : ∀ a ∈ A, ∀ v ∈ V, (a * v * a⁻¹ * v⁻¹)⁻¹ * t * (a * v * a⁻¹ * v⁻¹) * t =
      a * (v⁻¹ * t * v * t) * a⁻¹ * (v⁻¹ * t * v * t) := by
    intro a ha v hv
    have haH := (hAH ha).1
    rw [h.crossed_mul_of_mem (h.conj_mem_inf_centralizer haH hv) (inv_mem hv),
      crossed_conj (mem_centralizer_singleton_iff.mp (hAH ha).2), h.crossed_inv_of_mem hv,
      inv_eq_of_mul_eq_one_right (h.mul_self_of_mem (h.crossed_mem_of_mem hv))]
  obtain ⟨y₀, hy₀, hy₀1, -⟩ := exists_mem_ne_ne hY 1 1
  obtain ⟨v₀, hv₀, hv₀t⟩ := htr y₀ hy₀
  have hv₀c : v₀⁻¹ * t * v₀ * t = y₀ := (h.crossed_eq_iff hy₀).mpr hv₀t
  have hcQ' : ∀ y' ∈ Y, y' ≠ 1 → y' ≠ y₀ → ∃ q ∈ Q, q⁻¹ * t * q * t = y' * y₀ := by
    intro y' hy' hy'1 _
    obtain ⟨a, ha, hay⟩ := hAtr y₀ hy₀ y' hy' hy₀1 hy'1
    refine ⟨_, hcomm a ha v₀ hv₀, ?_⟩
    rw [hcr a ha v₀ hv₀, hv₀c, hay]
  have hcQ : ∀ y ∈ Y, ∃ q ∈ Q, q⁻¹ * t * q * t = y := by
    intro y hy
    by_cases hy1 : y = 1
    · exact ⟨1, one_mem _, by rw [hy1, inv_one, one_mul, mul_one, h.mul_self]⟩
    by_cases hyy : y = y₀
    · obtain ⟨z, hz, hz1, hzy⟩ := exists_mem_ne_ne hY 1 y₀
      have hzy₀ : z * y₀ ∈ Y := mul_mem hz hy₀
      have hzy₀1 : z * y₀ ≠ 1 := fun e => hzy (by
        have := congrArg (· * y₀) e
        simpa [mul_assoc, h.mul_self_of_mem hy₀] using this)
      have hzy₀y : z * y₀ ≠ y₀ := fun e => hz1 (by simpa using e)
      obtain ⟨q₁, hq₁, hq₁c⟩ := hcQ' z hz hz1 hzy
      obtain ⟨q₂, hq₂, hq₂c⟩ := hcQ' (z * y₀) hzy₀ hzy₀1 hzy₀y
      refine ⟨q₁ * q₂, mul_mem hq₁ hq₂, ?_⟩
      rw [h.crossed_mul_of_mem hq₁.1 hq₂.1, hq₁c, hq₂c, hyy]
      calc z * y₀ * (z * y₀ * y₀) = z * y₀ * z * (y₀ * y₀) := by group
        _ = y₀ * (z * z) := by
          rw [h.mul_self_of_mem hy₀, mul_one, h.mul_comm_of_mem hz hy₀, mul_assoc]
        _ = y₀ := by rw [h.mul_self_of_mem hz, mul_one]
    · obtain ⟨q, hq, hqc⟩ := hcQ' (y * y₀) (mul_mem hy hy₀) (fun e => hyy (by
          have := congrArg (· * y₀) e
          simpa [mul_assoc, h.mul_self_of_mem hy₀] using this))
        (fun e => hy1 (by simpa using e))
      refine ⟨q, hq, ?_⟩
      rw [hqc, mul_assoc, h.mul_self_of_mem hy₀, mul_one]
  intro y hy
  obtain ⟨q, hq, hqc⟩ := hcQ y hy
  exact ⟨q, hq.1, hq.2.2, (h.crossed_eq_iff hy).mp hqc⟩

end CosetData

section CosetPerm

variable {V : Type*} [AddCommGroup V] {H Y : Subgroup G} {t : G}

@[expose] def cosetPoint (ι : Multiplicative V ≃* Y) (t : G) (v : V) : G :=
  t * (ι (Multiplicative.ofAdd v) : G)

theorem eq_of_coe_ι_eq (ι : Multiplicative V ≃* Y) {v w : V}
    (e : (ι (Multiplicative.ofAdd v) : G) = ι (Multiplicative.ofAdd w)) : v = w := by
  have := ι.injective (Subtype.ext e)
  simpa using this

theorem cosetPoint_injective (ι : Multiplicative V ≃* Y) (t : G) :
    Function.Injective (cosetPoint ι t) := fun _ _ e => eq_of_coe_ι_eq ι (mul_left_cancel e)

theorem cosetPoint_zero (ι : Multiplicative V ≃* Y) (t : G) : cosetPoint ι t 0 = t := by
  simp [cosetPoint]

theorem cosetPoint_add (ι : Multiplicative V ≃* Y) (t : G) (v w : V) :
    cosetPoint ι t (v + w) = cosetPoint ι t v * (ι (Multiplicative.ofAdd w) : G) := by
  simp [cosetPoint, ofAdd_add, mul_assoc]

theorem cosetPoint_coord (ι : Multiplicative V ≃* Y) (t : G) {g : G} (hg : t⁻¹ * g ∈ Y) :
    cosetPoint ι t (Multiplicative.toAdd (ι.symm ⟨t⁻¹ * g, hg⟩)) = g := by
  simp [cosetPoint]

theorem coe_ι_coord (ι : Multiplicative V ≃* Y) {y : G} (hy : y ∈ Y) :
    (ι (Multiplicative.ofAdd (Multiplicative.toAdd (ι.symm ⟨y, hy⟩))) : G) = y := by
  simp

namespace CosetData

variable (h : CosetData H Y t)
include h

theorem inv_mul_conj_mem {g : G} (hg : g ∈ H) : t⁻¹ * (g * t * g⁻¹) ∈ Y := by
  have hc := h.crossed_mem g⁻¹ (H.inv_mem hg)
  rw [inv_inv] at hc
  have e : t⁻¹ * (g * t * g⁻¹) = t⁻¹ * (g * t * g⁻¹ * t) * t⁻¹ := by group
  rw [e, h.inv_eq, h.comm_of_mem hc, mul_assoc, h.mul_self, mul_one]
  exact hc

theorem conj_cosetPoint_mem (ι : Multiplicative V ≃* Y) {g : G} (hg : g ∈ H) (v : V) :
    t⁻¹ * (g * cosetPoint ι t v * g⁻¹) ∈ Y := by
  have e : t⁻¹ * (g * cosetPoint ι t v * g⁻¹) =
      (t⁻¹ * (g * t * g⁻¹)) * (g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹) := by
    simp only [cosetPoint]
    group
  rw [e]
  exact mul_mem (h.inv_mul_conj_mem hg)
    ((mem_normalizer_iff.mp (h.le_normalizer hg) _).mp (ι _).2)

@[expose] noncomputable def cosetCoord (ι : Multiplicative V ≃* Y) (g : H) (v : V) : V :=
  Multiplicative.toAdd (ι.symm ⟨_, h.conj_cosetPoint_mem ι g.2 v⟩)

theorem cosetPoint_cosetCoord (ι : Multiplicative V ≃* Y) (g : H) (v : V) :
    cosetPoint ι t (h.cosetCoord ι g v) = g * cosetPoint ι t v * (g : G)⁻¹ :=
  cosetPoint_coord ι t _

@[expose] noncomputable def cosetPerm (ι : Multiplicative V ≃* Y) : H →* Equiv.Perm V where
  toFun g :=
    { toFun := h.cosetCoord ι g
      invFun := h.cosetCoord ι g⁻¹
      left_inv := fun v => cosetPoint_injective ι t (by
        rw [h.cosetPoint_cosetCoord, h.cosetPoint_cosetCoord, Subgroup.coe_inv]
        group)
      right_inv := fun v => cosetPoint_injective ι t (by
        rw [h.cosetPoint_cosetCoord, h.cosetPoint_cosetCoord, Subgroup.coe_inv]
        group) }
  map_one' := Equiv.ext fun v => cosetPoint_injective ι t (by
    rw [Equiv.Perm.one_apply, Equiv.coe_fn_mk, h.cosetPoint_cosetCoord]
    simp)
  map_mul' g g' := Equiv.ext fun v => cosetPoint_injective ι t (by
    simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [h.cosetPoint_cosetCoord, h.cosetPoint_cosetCoord, h.cosetPoint_cosetCoord,
      Subgroup.coe_mul]
    group)

theorem cosetPoint_cosetPerm (ι : Multiplicative V ≃* Y) (g : H) (v : V) :
    cosetPoint ι t (h.cosetPerm ι g v) = g * cosetPoint ι t v * (g : G)⁻¹ :=
  h.cosetPoint_cosetCoord ι g v

theorem cosetPerm_zero_eq_zero_iff (ι : Multiplicative V ≃* Y) (g : H) :
    h.cosetPerm ι g 0 = 0 ↔ (g : G) ∈ centralizer ({t} : Set G) := by
  rw [← (cosetPoint_injective ι t).eq_iff, h.cosetPoint_cosetPerm, cosetPoint_zero,
    mem_centralizer_singleton_iff]
  constructor
  · intro e
    calc (g : G) * t = ((g : G) * t * (g : G)⁻¹) * g := by group
      _ = t * g := by rw [e]
  · intro e
    rw [e, mul_inv_cancel_right]

@[expose] noncomputable def linCoord (ι : Multiplicative V ≃* Y) (g : H) (v : V) : V :=
  Multiplicative.toAdd (ι.symm ⟨_, (mem_normalizer_iff.mp (h.le_normalizer g.2) _).mp
    (ι (Multiplicative.ofAdd v)).2⟩)

theorem coe_ι_linCoord (ι : Multiplicative V ≃* Y) (g : H) (v : V) :
    (ι (Multiplicative.ofAdd (h.linCoord ι g v)) : G) =
      g * (ι (Multiplicative.ofAdd v) : G) * (g : G)⁻¹ := by
  simp [linCoord]

theorem cosetPerm_apply (ι : Multiplicative V ≃* Y) (g : H) (v : V) :
    h.cosetPerm ι g v = h.cosetPerm ι g 0 + h.linCoord ι g v := by
  apply cosetPoint_injective ι t
  rw [cosetPoint_add, h.cosetPoint_cosetPerm, h.cosetPoint_cosetPerm, cosetPoint_zero,
    h.coe_ι_linCoord]
  simp only [cosetPoint]
  group

theorem linCoord_add (ι : Multiplicative V ≃* Y) (g : H) (v w : V) :
    h.linCoord ι g (v + w) = h.linCoord ι g v + h.linCoord ι g w := by
  apply eq_of_coe_ι_eq ι
  rw [h.coe_ι_linCoord, ofAdd_add, map_mul, Subgroup.coe_mul, ofAdd_add, map_mul,
    Subgroup.coe_mul, h.coe_ι_linCoord, h.coe_ι_linCoord]
  group

theorem linCoord_inv_linCoord (ι : Multiplicative V ≃* Y) (g : H) (v : V) :
    h.linCoord ι g⁻¹ (h.linCoord ι g v) = v := by
  apply eq_of_coe_ι_eq ι
  rw [h.coe_ι_linCoord, h.coe_ι_linCoord, Subgroup.coe_inv]
  group

theorem linCoord_linCoord_inv (ι : Multiplicative V ≃* Y) (g : H) (v : V) :
    h.linCoord ι g (h.linCoord ι g⁻¹ v) = v := by
  apply eq_of_coe_ι_eq ι
  rw [h.coe_ι_linCoord, h.coe_ι_linCoord, Subgroup.coe_inv]
  group

theorem mem_centralizer_of_translation (ι : Multiplicative V ≃* Y) (g : H) {b : V}
    (hb : ∀ v, h.cosetPerm ι g v = v + b) :
    (g : G) ∈ centralizer (Y : Set G) ∧ (g : G) * t * (g : G)⁻¹ = cosetPoint ι t b := by
  have h0 : h.cosetPerm ι g 0 = b := by rw [hb, zero_add]
  have hlin : ∀ v, h.linCoord ι g v = v := by
    intro v
    have := h.cosetPerm_apply ι g v
    rw [hb, h0, add_comm b] at this
    exact (add_right_cancel this).symm
  refine ⟨mem_centralizer_iff.mpr fun y hy => ?_, ?_⟩
  · have e := h.coe_ι_linCoord ι g (Multiplicative.toAdd (ι.symm ⟨y, hy⟩))
    rw [hlin, coe_ι_coord] at e
    calc y * g = (g * y * (g : G)⁻¹) * g := by rw [← e]
      _ = g * y := by group
  · have := h.cosetPoint_cosetPerm ι g 0
    rw [h0, cosetPoint_zero] at this
    exact this.symm

end CosetData

end CosetPerm

section Frobenius

open CFSG.LocalAnalysis.SteinbergCD (affPerm scalarPerm translPerm
  affine_scalar_sharply_two_transitive_normal_translations)

variable {H Y : Subgroup G} {t : G} {K : Type*} [Field K]

omit [Group G] in
theorem exists_ne_zero_ne_one [Finite K] (hK : 2 < Nat.card K) : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun a _ => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (hcon a ha)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ] at hle
  have h2 : ({0, 1} : Set K).ncard ≤ 2 := by
    refine (Set.ncard_insert_le 0 {1}).trans ?_
    rw [Set.ncard_singleton]
  omega

namespace CosetData

variable (h : CosetData H Y t)
include h

theorem cosetPerm_mem_affPerm (ι : Multiplicative K ≃* Y) (g : H) :
    h.cosetPerm ι g ∈ affPerm K := by
  let σ : K ≃+ K :=
    { toFun := h.linCoord ι g
      invFun := h.linCoord ι g⁻¹
      left_inv := h.linCoord_inv_linCoord ι g
      right_inv := h.linCoord_linCoord_inv ι g
      map_add' := h.linCoord_add ι g }
  exact ⟨σ, h.cosetPerm ι g 0, fun x => by rw [h.cosetPerm_apply ι g x, add_comm]; rfl⟩

theorem cosetPerm_of_scalar (ι : Multiplicative K ≃* Y) {g : H}
    (hgt : (g : G) ∈ centralizer ({t} : Set G)) {a : K}
    (hga : ∀ x : K, (g : G) * (ι (Multiplicative.ofAdd x) : G) * (g : G)⁻¹ =
      ι (Multiplicative.ofAdd (a * x))) (x : K) :
    h.cosetPerm ι g x = a * x := by
  rw [h.cosetPerm_apply ι g x, (h.cosetPerm_zero_eq_zero_iff ι g).mpr hgt, zero_add]
  apply eq_of_coe_ι_eq ι
  rw [h.coe_ι_linCoord, hga]

theorem exists_conj_eq_mul_of_frobenius [Finite K] [CharP K 2] (hK2 : 2 < Nat.card K)
    (ι : Multiplicative K ≃* Y) (htr : ∀ y ∈ Y, ∃ g ∈ H, g⁻¹ * t * g = t * y)
    {E : Subgroup G} (hEH : E ≤ H) (hEn : H ≤ normalizer (E : Set G))
    (hsc : ∀ e ∈ E ⊓ centralizer ({t} : Set G), ∃ a : K, a ≠ 0 ∧ ∀ x : K,
      e * (ι (Multiplicative.ofAdd x) : G) * e⁻¹ = ι (Multiplicative.ofAdd (a * x)))
    (hsc' : ∀ a : K, a ≠ 0 → ∃ e ∈ E ⊓ centralizer ({t} : Set G), ∀ x : K,
      e * (ι (Multiplicative.ofAdd x) : G) * e⁻¹ = ι (Multiplicative.ofAdd (a * x))) :
    ∀ y ∈ Y, ∃ e ∈ E ⊓ centralizer (Y : Set G), e⁻¹ * t * e = t * y := by
  classical
  set ρ := h.cosetPerm ι with hρ
  set H' : Subgroup (Equiv.Perm K) := ρ.range with hH'
  set F : Subgroup (Equiv.Perm K) := (E.subgroupOf H).map ρ with hF
  have hscal : ∀ a : K, a ≠ 0 → ∃ e : H, (e : G) ∈ E ∧ ∀ x, ρ e x = a * x := by
    intro a ha
    obtain ⟨e, he, hex⟩ := hsc' a ha
    exact ⟨⟨e, hEH he.1⟩, he.1, h.cosetPerm_of_scalar ι he.2 hex⟩
  have hHaff : H' ≤ affPerm K := by
    rintro _ ⟨g, rfl⟩
    exact h.cosetPerm_mem_affPerm ι g
  have hSH : scalarPerm K ≤ H' := by
    rintro s ⟨a, ha, hs⟩
    obtain ⟨e, -, he⟩ := hscal a ha
    exact ⟨e, Equiv.ext fun x => (he x).trans (hs x).symm⟩
  have hFH : F ≤ H' := map_le_range _ _
  have hFn : (F.subgroupOf H').Normal := by
    refine ⟨fun f hf h' => ?_⟩
    rw [mem_subgroupOf] at hf ⊢
    obtain ⟨z, hz, hzf⟩ := hf
    obtain ⟨g, hg⟩ := h'.2
    refine ⟨g * z * g⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf] at hz ⊢
      exact (mem_normalizer_iff.mp (hEn g.2) _).mp hz
    · rw [map_mul, map_mul, map_inv, hg, hzf]
      rfl
  have hF0 : ∀ f : Equiv.Perm K, f ∈ F ∧ f 0 = 0 ↔ f ∈ scalarPerm K := by
    intro f
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, h0⟩
      have hzt := (h.cosetPerm_zero_eq_zero_iff ι z).mp h0
      obtain ⟨a, ha, hza⟩ := hsc z ⟨mem_subgroupOf.mp hz, hzt⟩
      exact ⟨a, ha, h.cosetPerm_of_scalar ι hzt hza⟩
    · rintro ⟨a, ha, hf⟩
      obtain ⟨e, heE, he⟩ := hscal a ha
      have e' : ρ e = f := Equiv.ext fun x => (he x).trans (hf x).symm
      exact ⟨⟨e, mem_subgroupOf.mpr heE, e'⟩, by rw [hf, mul_zero]⟩
  have hfrom0 : ∀ y : K, ∃ f ∈ F, f 0 = y := by
    obtain ⟨m, hm, hmt⟩ := htr _ (ι (Multiplicative.ofAdd (1 : K))).2
    set g : H := ⟨m⁻¹, H.inv_mem hm⟩ with hgdef
    have hg0 : ρ g 0 = 1 := by
      apply cosetPoint_injective ι t
      rw [hρ, h.cosetPoint_cosetPerm, cosetPoint_zero, hgdef]
      simp only [inv_inv]
      rw [hmt]
      rfl
    have hw : ρ g⁻¹ 0 ≠ 0 := by
      intro h0
      have : ρ g (ρ g⁻¹ 0) = 0 := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [h0, hg0] at this
      exact one_ne_zero this
    obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_ne_one hK2
    obtain ⟨z, hzE, hz⟩ := hscal a ha0
    have hfF : ρ (g * z * g⁻¹) ∈ F :=
      ⟨g * z * g⁻¹, mem_subgroupOf.mpr ((mem_normalizer_iff.mp (hEn g.2) _).mp hzE), rfl⟩
    have hf0 : ρ (g * z * g⁻¹) 0 ≠ 0 := by
      obtain ⟨σ, b, hσ⟩ := h.cosetPerm_mem_affPerm ι g
      have h1 : ρ (g * z * g⁻¹) 0 = ρ g (a * ρ g⁻¹ 0) := by
        rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hz]
      have h2 : ρ g (ρ g⁻¹ 0) = 0 := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [h1, hσ]
      rw [hσ] at h2
      intro h3
      have h4 : σ (a * ρ g⁻¹ 0 - ρ g⁻¹ 0) = 0 := by
        rw [map_sub]
        linear_combination h3 - h2
      have h5 : a * ρ g⁻¹ 0 - ρ g⁻¹ 0 = 0 := σ.injective (h4.trans (map_zero σ).symm)
      have h6 : (a - 1) * ρ g⁻¹ 0 = 0 := by linear_combination h5
      rcases mul_eq_zero.mp h6 with h7 | h7
      · exact ha1 (sub_eq_zero.mp h7)
      · exact hw h7
    intro y
    by_cases hy : y = 0
    · exact ⟨1, one_mem F, by rw [hy]; rfl⟩
    · obtain ⟨z', hz'E, hz'⟩ := hscal (y / ρ (g * z * g⁻¹) 0) (div_ne_zero hy hf0)
      refine ⟨ρ z' * ρ (g * z * g⁻¹), mul_mem ⟨z', mem_subgroupOf.mpr hz'E, rfl⟩ hfF, ?_⟩
      rw [Equiv.Perm.mul_apply, hz', div_mul_cancel₀ y hf0]
  have htrans : ∀ x y : K, ∃ f ∈ F, f x = y := by
    intro x y
    obtain ⟨f₁, hf₁, h₁⟩ := hfrom0 x
    obtain ⟨f₂, hf₂, h₂⟩ := hfrom0 y
    refine ⟨f₂ * f₁⁻¹, mul_mem hf₂ (inv_mem hf₁), ?_⟩
    rw [Equiv.Perm.mul_apply, ← h₁, show f₁⁻¹ (f₁ 0) = 0 from Equiv.Perm.inv_eq_iff_eq.mpr rfl,
      h₂]
  obtain ⟨-, -, hTF, -⟩ :=
    affine_scalar_sharply_two_transitive_normal_translations K H' F hHaff hSH hFH hFn htrans hF0
  intro y hy
  set b := Multiplicative.toAdd (ι.symm ⟨y, hy⟩) with hb
  obtain ⟨⟨e, heH⟩, he, hρe⟩ := hTF (⟨b, fun _ => rfl⟩ : Equiv.addRight b ∈ translPerm K)
  have heE : e ∈ E := mem_subgroupOf.mp he
  obtain ⟨hec, het⟩ := h.mem_centralizer_of_translation ι ⟨e, heH⟩ (b := b) fun v => by
    rw [← hρ, hρe]
    rfl
  refine ⟨e⁻¹, ⟨E.inv_mem heE, (centralizer (Y : Set G)).inv_mem hec⟩, ?_⟩
  rw [inv_inv, het, cosetPoint, hb, coe_ι_coord]

end CosetData

end Frobenius

section Combined

open Matrix
open scoped MatrixGroups

variable {H Y : Subgroup G} {t : G}

namespace CosetData

variable (h : CosetData H Y t)
include h

theorem exists_conj_eq_mul_of_sl {k : Type*} [Field k] [Fintype k] [CharP k 2]
    (ι : Multiplicative (Fin 2 → k) ≃* Y) (htr : ∀ y ∈ Y, ∃ g ∈ H, g⁻¹ * t * g = t * y)
    {A : Subgroup G} (hA : A ≤ H ⊓ centralizer ({t} : Set G))
    (hnat : ∀ g ∈ A, ∃ M : SL(2, k), ∀ v : Fin 2 → k,
      g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v)))
    (hsurj : ∀ M : SL(2, k), ∃ g ∈ A, ∀ v : Fin 2 → k,
      g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v)))
    (hAn : ∀ x ∈ H ⊓ centralizer ({t} : Set G), ∀ g ∈ A, ∃ g' ∈ A, ∀ w ∈ Y,
      x * g * x⁻¹ * w * (x * g * x⁻¹)⁻¹ = g' * w * g'⁻¹) :
    ∀ y ∈ Y, ∃ v ∈ H ⊓ centralizer (Y : Set G), v⁻¹ * t * v = t * y := by
  have htr' : ∀ w ∈ Y, ∃ x ∈ H, x * t * x⁻¹ = t * w := by
    intro w hw
    obtain ⟨g, hg, hgt⟩ := htr w hw
    exact ⟨g⁻¹, H.inv_mem hg, by rw [inv_inv, hgt]⟩
  intro y hy
  obtain ⟨x, hx, hxc, hxt⟩ := exists_conj_eq_mul_of_sl_transitive ι h.le_normalizer
    (fun x hx => h.inv_mul_conj_mem hx) htr' hA hnat hsurj hAn y hy
  exact ⟨x⁻¹, ⟨H.inv_mem hx, (centralizer (Y : Set G)).inv_mem hxc⟩, by rw [inv_inv, hxt]⟩

theorem sl_two_core [Finite G] {k : Type*} [Field k] [Fintype k] [CharP k 2]
    (ι : Multiplicative (Fin 2 → k) ≃* Y) (htr : ∀ y ∈ Y, ∃ g ∈ H, g⁻¹ * t * g = t * y)
    {A : Subgroup G} (hA : A ≤ H ⊓ centralizer ({t} : Set G))
    (hnat : ∀ g ∈ A, ∃ M : SL(2, k), ∀ v : Fin 2 → k,
      g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v)))
    (hsurj : ∀ M : SL(2, k), ∃ g ∈ A, ∀ v : Fin 2 → k,
      g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v)))
    (hAn : ∀ x ∈ H ⊓ centralizer ({t} : Set G), ∀ g ∈ A, ∃ g' ∈ A, ∀ w ∈ Y,
      x * g * x⁻¹ * w * (x * g * x⁻¹)⁻¹ = g' * w * g'⁻¹)
    {B : Subgroup G} (hB2 : IsPGroup 2 B)
    (hBK : B ≤ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G))
    (hBn : H ≤ normalizer (B : Set G))
    (hBmax : ∀ R : Subgroup G, R ≤ H ⊓ centralizer ({t} : Set G) →
      H ⊓ centralizer ({t} : Set G) ≤ normalizer (R : Set G) → IsPGroup 2 R → R ≤ B)
    (hAK : ∀ a ∈ A, ∀ k ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G),
      a * k * a⁻¹ * k⁻¹ ∈ B) :
    oTwo H ≤ centralizer (Y : Set G) ∧ oTwo H ⊓ centralizer ({t} : Set G) = B ∧
      (∀ y ∈ Y, ∃ d ∈ oTwo H, d⁻¹ * t * d = t * y) ∧
      ∀ g ∈ H, ∃ c ∈ H ⊓ centralizer ({t} : Set G), ∃ d ∈ oTwo H, g = c * d := by
  have htrV := h.exists_conj_eq_mul_of_sl ι htr hA hnat hsurj hAn
  have hAtr : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ 1 → y' ≠ 1 → ∃ a ∈ A, a * y * a⁻¹ = y' := by
    intro y hy y' hy' hy1 hy'1
    set v := Multiplicative.toAdd (ι.symm ⟨y, hy⟩) with hv
    set v' := Multiplicative.toAdd (ι.symm ⟨y', hy'⟩) with hv'
    have hv0 : v ≠ 0 := fun e => hy1 (by rw [← coe_ι_coord ι hy, ← hv, e]; simp)
    have hv'0 : v' ≠ 0 := fun e => hy'1 (by rw [← coe_ι_coord ι hy', ← hv', e]; simp)
    obtain ⟨M, hM⟩ := CFSG.LocalAnalysis.EvenBN.LinearThree.Plane.exists_sl_smul hv0 hv'0
    obtain ⟨g, hg, hgM⟩ := hsurj M
    refine ⟨g, hg, ?_⟩
    have := hgM v
    rw [hv, coe_ι_coord, show ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v) = v' from hM] at this
    rw [this, hv', coe_ι_coord]
  have hY : 2 < Nat.card Y := by
    have e : Nat.card Y = Nat.card k ^ 2 := by
      rw [← Nat.card_congr ι.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    have hk : 2 ≤ Nat.card k := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    rw [e]
    nlinarith
  exact h.two_core hB2 hBK hBn hBmax
    (h.transitive_of_transitive hBn hA hAK hAtr hY htrV) |>.elim fun h1 h2 => ⟨h1, h2.2⟩

theorem frobenius_two_core [Finite G] {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK2 : 2 < Nat.card K) (ι : Multiplicative K ≃* Y)
    (htr : ∀ y ∈ Y, ∃ g ∈ H, g⁻¹ * t * g = t * y)
    {B : Subgroup G} (hB2 : IsPGroup 2 B)
    (hBK : B ≤ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G))
    (hBn : H ≤ normalizer (B : Set G))
    (hBmax : ∀ R : Subgroup G, R ≤ H ⊓ centralizer ({t} : Set G) →
      H ⊓ centralizer ({t} : Set G) ≤ normalizer (R : Set G) → IsPGroup 2 R → R ≤ B)
    (hsc : ∀ e ∈ H ⊓ centralizer ({t} : Set G),
      (∀ k ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G), e * k * e⁻¹ * k⁻¹ ∈ B) →
        ∃ a : K, a ≠ 0 ∧ ∀ x : K,
          e * (ι (Multiplicative.ofAdd x) : G) * e⁻¹ = ι (Multiplicative.ofAdd (a * x)))
    (hsc' : ∀ a : K, a ≠ 0 → ∃ e ∈ H ⊓ centralizer ({t} : Set G),
      (∀ k ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G), e * k * e⁻¹ * k⁻¹ ∈ B) ∧
        ∀ x : K, e * (ι (Multiplicative.ofAdd x) : G) * e⁻¹ = ι (Multiplicative.ofAdd (a * x))) :
    oTwo H ≤ centralizer (Y : Set G) ∧ oTwo H ⊓ centralizer ({t} : Set G) = B ∧
      (∀ y ∈ Y, ∃ d ∈ oTwo H, d⁻¹ * t * d = t * y) ∧
      ∀ g ∈ H, ∃ c ∈ H ⊓ centralizer ({t} : Set G), ∃ d ∈ oTwo H, g = c * d := by
  have hBn' : ∀ g ∈ H, ∀ b ∈ B, g * b * g⁻¹ ∈ B := fun g hg b hb =>
    (mem_normalizer_iff.mp (hBn hg) b).mp hb
  have hK : ∀ g ∈ H, ∀ k ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G),
      g * k * g⁻¹ ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G) :=
    fun g hg k hk => h.conj_mem_kernel hg hk
  set E := centralizerMod H (H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G)) B hK hBn'
    with hE
  have hEH : E ≤ H := fun e he => he.1
  have hEn : H ≤ normalizer (E : Set G) := fun g hg => by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨conj_mem_centralizerMod hg, fun hx => ?_⟩
    have := conj_mem_centralizerMod (H.inv_mem hg) hx
    simpa [mul_assoc] using this
  have htrE := h.exists_conj_eq_mul_of_frobenius hK2 ι htr hEH hEn
    (fun e he => hsc e ⟨he.1.1, he.2⟩ he.1.2)
    (fun a ha => by
      obtain ⟨e, he, heK, hex⟩ := hsc' a ha
      exact ⟨e, ⟨⟨he.1, heK⟩, he.2⟩, hex⟩)
  have hQtr : ∀ y ∈ Y, ∃ q ∈ H ⊓ centralizer (Y : Set G),
      (∀ k ∈ H ⊓ centralizer (Y : Set G) ⊓ centralizer ({t} : Set G), q * k * q⁻¹ * k⁻¹ ∈ B) ∧
        q⁻¹ * t * q = t * y := by
    intro y hy
    obtain ⟨e, he, het⟩ := htrE y hy
    exact ⟨e, ⟨he.1.1, he.2⟩, he.1.2, het⟩
  exact h.two_core hB2 hBK hBn hBmax hQtr |>.elim fun h1 h2 => ⟨h1, h2.2⟩

end CosetData

end Combined

end CFSG.LocalAnalysis.EvenBN.Common
