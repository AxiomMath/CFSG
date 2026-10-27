module

import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionCentre
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankFourTheoremC.Refined
public import CFSG.LocalAnalysis.RankThreeTheoremC.FullCoreReduction
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionOrder

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.RankThree.PartOne.Planes Subgroup

variable {G : Type} [Group G] [Finite G]

structure ExtraspecialFrame (p : ℕ) (P D Z : Subgroup G) (x y : G) : Prop where
  prime : p.Prime
  card_D : Nat.card D = p ^ 3
  card_Z : Nat.card Z = p
  Z_le : Z ≤ D
  D_le : D ≤ P
  Z_comm : ∀ z ∈ Z, ∀ d ∈ D, d * z = z * d
  mem_of_comm : ∀ d ∈ D, (∀ e ∈ D, e * d = d * e) → d ∈ Z
  Z_comm_P : ∀ z ∈ Z, ∀ g ∈ P, g * z = z * g
  comm_mem : ∀ d ∈ D, ∀ e ∈ D, d * e * d⁻¹ * e⁻¹ ∈ Z
  x_mem : x ∈ D
  y_mem : y ∈ D
  comm_x : ∀ g ∈ P, g * x * g⁻¹ * x⁻¹ ∈ Z
  comm_y : ∀ g ∈ P, g * y * g⁻¹ * y⁻¹ ∈ Z ⊔ zpowers x
  gen : Z ⊔ zpowers x ⊔ zpowers y = D
  card_U : Nat.card ↥(Z ⊔ zpowers x) = p ^ 2

section Frame

variable {p : ℕ} {P D Z : Subgroup G} {x y : G}

omit [Finite G] in
theorem ExtraspecialFrame.conj_Z (F : ExtraspecialFrame p P D Z x y) {z g : G} (hz : z ∈ Z)
    (hg : g ∈ P) : g * z * g⁻¹ = z := by
  rw [mul_inv_eq_iff_eq_mul]
  exact F.Z_comm_P z hz g hg

omit [Finite G] in
theorem ExtraspecialFrame.U_le (F : ExtraspecialFrame p P D Z x y) : Z ⊔ zpowers x ≤ D :=
  sup_le F.Z_le (zpowers_le.mpr F.x_mem)

theorem normalizer_sup_zpowers_of_comm {Z P : Subgroup G} {x : G}
    (hZ : ∀ z ∈ Z, ∀ g ∈ P, g * z * g⁻¹ = z) (hx : ∀ g ∈ P, g * x * g⁻¹ * x⁻¹ ∈ Z) :
    P ≤ normalizer ((Z ⊔ zpowers x : Subgroup G) : Set G) := by
  intro g hg
  have hle : (Z ⊔ zpowers x).map (MulAut.conj g).toMonoidHom ≤ Z ⊔ zpowers x := by
    rw [map_le_iff_le_comap]
    refine sup_le (fun z hz => mem_sup_left ?_) ?_
    · change g * z * g⁻¹ ∈ Z
      rw [hZ z hz g hg]; exact hz
    · rw [zpowers_le]
      change g * x * g⁻¹ ∈ Z ⊔ zpowers x
      have h1 : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
      rw [h1]
      exact mul_mem (mem_sup_left (hx g hg)) (mem_sup_right (mem_zpowers x))
  exact mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj g).injective).ge)

omit [Finite G] in
theorem ExtraspecialFrame.centralizes (F : ExtraspecialFrame p P D Z x y) {c : G}
    (hcZ : ∀ z ∈ Z, c * z = z * c) (hcx : c * x = x * c) (hcy : c * y = y * c) :
    ∀ d ∈ D, c * d = d * c := by
  have hle : D ≤ centralizer ({c} : Set G) := by
    rw [← F.gen]
    refine sup_le (sup_le (fun z hz => mem_centralizer_iff.2 fun h hh => ?_) ?_) ?_
    · rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact hcZ z hz
    · rw [zpowers_le]
      exact mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hcx
    · rw [zpowers_le]
      exact mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hcy
  intro d hd
  exact mem_centralizer_iff.1 (hle hd) c rfl

theorem ExtraspecialFrame.exists_commutators (F : ExtraspecialFrame p P D Z x y) :
    ∀ a ∈ Z, ∀ b ∈ Z, ∃ d ∈ D, d * x * d⁻¹ * x⁻¹ = a ∧ d * y * d⁻¹ * y⁻¹ = b := by
  classical
  have hp := F.prime
  have hmulaux : ∀ a ∈ D, ∀ b ∈ D, ∀ e ∈ D,
      a * b * e * (a * b)⁻¹ * e⁻¹ = (a * e * a⁻¹ * e⁻¹) * (b * e * b⁻¹ * e⁻¹) := by
    intro a ha b hb e he
    have hbz := F.comm_mem b hb e he
    have hcom : a * (b * e * b⁻¹ * e⁻¹) = (b * e * b⁻¹ * e⁻¹) * a := F.Z_comm _ hbz a ha
    have haD : a * e * a⁻¹ * e⁻¹ ∈ D :=
      mul_mem (mul_mem (mul_mem ha he) (inv_mem ha)) (inv_mem he)
    have hcom2 : (a * e * a⁻¹ * e⁻¹) * (b * e * b⁻¹ * e⁻¹) =
        (b * e * b⁻¹ * e⁻¹) * (a * e * a⁻¹ * e⁻¹) := F.Z_comm _ hbz _ haD
    calc a * b * e * (a * b)⁻¹ * e⁻¹ = a * (b * e * b⁻¹ * e⁻¹) * e * a⁻¹ * e⁻¹ := by group
      _ = (b * e * b⁻¹ * e⁻¹) * a * e * a⁻¹ * e⁻¹ := by rw [hcom]
      _ = (b * e * b⁻¹ * e⁻¹) * (a * e * a⁻¹ * e⁻¹) := by group
      _ = (a * e * a⁻¹ * e⁻¹) * (b * e * b⁻¹ * e⁻¹) := hcom2.symm
  let ν : D →* Z × Z :=
    { toFun := fun d => (⟨(d : G) * x * (d : G)⁻¹ * x⁻¹, F.comm_mem d d.2 x F.x_mem⟩,
        ⟨(d : G) * y * (d : G)⁻¹ * y⁻¹, F.comm_mem d d.2 y F.y_mem⟩)
      map_one' := Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
      map_mul' := fun d d' => Prod.ext
        (Subtype.ext (hmulaux d d.2 d' d'.2 x F.x_mem))
        (Subtype.ext (hmulaux d d.2 d' d'.2 y F.y_mem)) }
  have hνker : ∀ d : D, ν d = 1 → (d : G) ∈ Z := by
    intro d hd
    have h1 : (d : G) * x * (d : G)⁻¹ * x⁻¹ = 1 := congrArg Subtype.val (congrArg Prod.fst hd)
    have h2 : (d : G) * y * (d : G)⁻¹ * y⁻¹ = 1 := congrArg Subtype.val (congrArg Prod.snd hd)
    have hdx : (d : G) * x = x * d := by
      have := mul_inv_eq_one.1 h1
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have hdy : (d : G) * y = y * d := by
      have := mul_inv_eq_one.1 h2
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have hall := F.centralizes (fun z hz => F.Z_comm z hz d d.2) hdx hdy
    exact F.mem_of_comm d d.2 fun e he => (hall e he).symm
  have hνsurj : Function.Surjective ν := by
    have hker : Nat.card ν.ker ≤ p := by
      calc Nat.card ν.ker = Nat.card (ν.ker.map D.subtype) :=
            (card_map_of_injective D.subtype_injective).symm
        _ ≤ Nat.card Z := Subgroup.card_le_of_le (by
            rintro _ ⟨d, hd, rfl⟩
            exact hνker d (MonoidHom.mem_ker.1 hd))
        _ = p := F.card_Z
    have h1 := Subgroup.card_ker_mul_card_range ν
    have h2 : Nat.card ν.range ≤ p ^ 2 := by
      calc Nat.card ν.range ≤ Nat.card (Z × Z) := Subgroup.card_le_card_group _
        _ = p ^ 2 := by rw [Nat.card_prod, F.card_Z, pow_two]
    have h3 : p ^ 2 ≤ Nat.card ν.range := by
      have hpp : 0 < p := hp.pos
      rw [F.card_D] at h1
      have : p ^ 2 * p ≤ p * Nat.card ν.range := by
        calc p ^ 2 * p = p ^ 3 := by ring
          _ = Nat.card ν.ker * Nat.card ν.range := h1.symm
          _ ≤ p * Nat.card ν.range := Nat.mul_le_mul_right _ hker
      nlinarith
    have hrange : ν.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by
      rw [Nat.card_prod, F.card_Z, ← pow_two]; omega)
    exact MonoidHom.range_eq_top.1 hrange
  intro a ha b hb
  obtain ⟨d, hd⟩ := hνsurj (⟨a, ha⟩, ⟨b, hb⟩)
  exact ⟨d, d.2, congrArg Subtype.val (congrArg Prod.fst hd),
    congrArg Subtype.val (congrArg Prod.snd hd)⟩

omit [Finite G] in
theorem ExtraspecialFrame.U_comm (F : ExtraspecialFrame p P D Z x y) :
    ∀ b ∈ Z ⊔ zpowers x, ∀ a ∈ Z ⊔ zpowers x, b * a = a * b := by
  intro b hb a ha
  have hbx : b * x = x * b := by
    have hle : Z ⊔ zpowers x ≤ centralizer ({x} : Set G) := by
      refine sup_le (fun z hz => mem_centralizer_iff.2 fun h hh => ?_) ?_
      · rw [Set.mem_singleton_iff] at hh
        rw [hh]; exact F.Z_comm z hz x F.x_mem
      · rw [zpowers_le]
        exact mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff] at hh; rw [hh]
    exact (mem_centralizer_iff.1 (hle hb) x rfl).symm
  have hle : Z ⊔ zpowers x ≤ centralizer ({b} : Set G) := by
    refine sup_le (fun z hz => mem_centralizer_iff.2 fun h hh => ?_) ?_
    · rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact F.Z_comm z hz b (F.U_le hb)
    · rw [zpowers_le]
      exact mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hbx
  exact mem_centralizer_iff.1 (hle ha) b rfl

omit [Finite G] in
theorem ExtraspecialFrame.comm_mem_U (F : ExtraspecialFrame p P D Z x y) :
    ∀ g ∈ P, ∀ u ∈ Z ⊔ zpowers x, g * u * g⁻¹ * u⁻¹ ∈ Z := by
  intro g hg
  let T : Subgroup G :=
    { carrier := {u | u ∈ D ∧ g * u * g⁻¹ * u⁻¹ ∈ Z}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨mul_mem ha.1 hb.1, ?_⟩
        have hcen : a * (g * b * g⁻¹ * b⁻¹) = (g * b * g⁻¹ * b⁻¹) * a :=
          F.Z_comm _ hb.2 a ha.1
        have : g * (a * b) * g⁻¹ * (a * b)⁻¹ =
            (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹) := by
          calc g * (a * b) * g⁻¹ * (a * b)⁻¹
              = (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹) * a⁻¹) := by group
            _ = (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹) := by rw [hcen]; group
        rw [this]
        exact mul_mem ha.2 hb.2
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := fun {a} ha => by
        refine ⟨inv_mem ha.1, ?_⟩
        have hc' : (g * a * g⁻¹ * a⁻¹)⁻¹ ∈ Z := inv_mem ha.2
        have h2 := F.Z_comm _ hc' a⁻¹ (inv_mem ha.1)
        have : g * a⁻¹ * g⁻¹ * a⁻¹⁻¹ = a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [this]
        have h3 : a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a = (g * a * g⁻¹ * a⁻¹)⁻¹ := by
          calc a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a
              = (g * a * g⁻¹ * a⁻¹)⁻¹ * a⁻¹ * a := by rw [h2]
            _ = (g * a * g⁻¹ * a⁻¹)⁻¹ := by group
        rw [h3]; exact hc' }
  have hZT : Z ≤ T := fun z hz => ⟨F.Z_le hz, by
    rw [F.conj_Z hz hg, mul_inv_cancel]; exact one_mem _⟩
  have hxT : zpowers x ≤ T := zpowers_le.2 ⟨F.x_mem, F.comm_x g hg⟩
  exact fun u hu => (sup_le hZT hxT hu).2

theorem ExtraspecialFrame.commutator_mul_mem (F : ExtraspecialFrame p P D Z x y) {g h : G}
    (hg : g ∈ P) (hh : h ∈ P) : (g * h * y * (g * h)⁻¹ * y⁻¹)⁻¹ *
      ((g * y * g⁻¹ * y⁻¹) * (h * y * h⁻¹ * y⁻¹)) ∈ Z := by
  have hPU : P ≤ normalizer ((Z ⊔ zpowers x : Subgroup G) : Set G) :=
    normalizer_sup_zpowers_of_comm (fun z hz g hg => F.conj_Z hz hg) F.comm_x
  have hvU : g * y * g⁻¹ * y⁻¹ ∈ Z ⊔ zpowers x := F.comm_y g hg
  have huU : h * y * h⁻¹ * y⁻¹ ∈ Z ⊔ zpowers x := F.comm_y h hh
  have hwU : g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ ∈ Z ⊔ zpowers x :=
    (mem_normalizer_iff.1 (hPU hg) _).1 huU
  have hc : g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ * (h * y * h⁻¹ * y⁻¹)⁻¹ ∈ Z :=
    F.comm_mem_U g hg _ huU
  have hvw := F.U_comm _ (inv_mem hvU) _ (inv_mem hwU)
  have hgh : g * h * y * (g * h)⁻¹ * y⁻¹ =
      (g * (h * y * h⁻¹ * y⁻¹) * g⁻¹) * (g * y * g⁻¹ * y⁻¹) := by group
  have hw : g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ =
      (g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ * (h * y * h⁻¹ * y⁻¹)⁻¹) * (h * y * h⁻¹ * y⁻¹) := by group
  rw [hgh]
  set v := g * y * g⁻¹ * y⁻¹ with hv
  set u := h * y * h⁻¹ * y⁻¹ with hu
  set w := g * u * g⁻¹ with hwdef
  set c := g * u * g⁻¹ * u⁻¹ with hcdef
  have huD : u ∈ D := F.U_le huU
  have hc' := F.Z_comm _ (inv_mem hc) u⁻¹ (inv_mem huD)
  have hfin : (w * v)⁻¹ * (v * u) = c⁻¹ := by
    calc (w * v)⁻¹ * (v * u) = (v⁻¹ * w⁻¹) * (v * u) := by group
      _ = (w⁻¹ * v⁻¹) * (v * u) := by rw [hvw]
      _ = w⁻¹ * u := by group
      _ = u⁻¹ * c⁻¹ * u := by rw [hw]; group
      _ = c⁻¹ * u⁻¹ * u := by rw [hc']
      _ = c⁻¹ := by group
  rw [hfin]
  exact inv_mem hc

theorem ExtraspecialFrame.mem_sup_of_comm_mem (F : ExtraspecialFrame p P D Z x y) {e : G}
    (heP : e ∈ P) (hey : e * y * e⁻¹ * y⁻¹ ∈ Z) :
    e ∈ D ⊔ (P ⊓ centralizer (D : Set G)) := by
  obtain ⟨d, hdD, hd1, hd2⟩ := F.exists_commutators _ (F.comm_x e heP) _ hey
  have hd1' := mul_right_cancel hd1
  have hd2' := mul_right_cancel hd2
  have hcP : d⁻¹ * e ∈ P := mul_mem (inv_mem (F.D_le hdD)) heP
  have hcx : (d⁻¹ * e) * x = x * (d⁻¹ * e) := by
    calc (d⁻¹ * e) * x = d⁻¹ * (e * x * e⁻¹) * e := by group
      _ = d⁻¹ * (d * x * d⁻¹) * e := by rw [hd1']
      _ = x * (d⁻¹ * e) := by group
  have hcy : (d⁻¹ * e) * y = y * (d⁻¹ * e) := by
    calc (d⁻¹ * e) * y = d⁻¹ * (e * y * e⁻¹) * e := by group
      _ = d⁻¹ * (d * y * d⁻¹) * e := by rw [hd2']
      _ = y * (d⁻¹ * e) := by group
  have hcall := F.centralizes (fun z hz => F.Z_comm_P z hz _ hcP) hcx hcy
  have hcC : d⁻¹ * e ∈ centralizer (D : Set G) :=
    mem_centralizer_iff.2 fun h hh => (hcall h hh).symm
  have : e = d * (d⁻¹ * e) := by group
  rw [this]
  exact mul_mem (mem_sup_left hdD) (mem_sup_right ⟨hcP, hcC⟩)

end Frame

theorem ExtraspecialFrame.card_le_of_elemAbelian {p : ℕ} {P D Z : Subgroup G} {x y : G}
    (F : ExtraspecialFrame p P D Z x y)
    (hrank : Open.pRank p (D ⊔ (P ⊓ centralizer (D : Set G)) : Subgroup G) ≤ 2)
    {E : Subgroup G} (hEP : E ≤ P) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  classical
  have hp := F.prime
  have hfact : Fact p.Prime := ⟨hp⟩
  set U : Subgroup G := Z ⊔ zpowers x with hU
  have hDcen : D ≤ centralizer (Z : Set G) := fun d hd =>
    mem_centralizer_iff.2 fun z hz => (F.Z_comm z hz d hd).symm
  have hDN : D ≤ normalizer (Z : Set G) := hDcen.trans (centralizer_le_normalizer _)
  have hZ'N : (Z.subgroupOf U).Normal :=
    (normal_subgroupOf_iff_le_normalizer (le_sup_left : Z ≤ U)).2 (F.U_le.trans hDN)
  let γ : E →* U ⧸ Z.subgroupOf U :=
    { toFun := fun e => QuotientGroup.mk ⟨(e : G) * y * (e : G)⁻¹ * y⁻¹, F.comm_y e (hEP e.2)⟩
      map_one' := by
        have : (⟨((1 : E) : G) * y * ((1 : E) : G)⁻¹ * y⁻¹, F.comm_y 1 (hEP E.one_mem)⟩ : U) =
            1 := Subtype.ext (by simp)
        rw [this]
        exact QuotientGroup.mk_one _
      map_mul' := fun e e' => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact F.commutator_mul_mem (hEP e.2) (hEP e'.2) }
  have hE0 : Nat.card γ.ker ≤ p ^ 2 := by
    set E0 : Subgroup G := γ.ker.map E.subtype with hE0def
    have hE0E : E0 ≤ E := map_subtype_le _
    have hE0K : E0 ≤ D ⊔ ((P : Subgroup G) ⊓ centralizer (D : Set G)) := by
      rintro _ ⟨e, he, rfl⟩
      exact F.mem_sup_of_comm_mem (hEP e.2)
        (mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 he))
    have hE0e : IsElemAbelian p E0 := isElemAbelian_mono hE hE0E
    obtain ⟨k, hk⟩ := (elementary_isPGroup p E0 hE0e).exists_card_eq
    have hkle : k ≤ Open.pRank p (D ⊔ ((P : Subgroup G) ⊓ centralizer (D : Set G))) := by
      unfold Open.pRank
      exact le_csSup (pRank_set_bddAbove p hp.one_lt _) ⟨E0, hE0K, hE0e, hk⟩
    calc Nat.card γ.ker = Nat.card E0 := (card_map_of_injective E.subtype_injective).symm
      _ = p ^ k := hk
      _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (hkle.trans hrank)
  have hq : Nat.card (U ⧸ Z.subgroupOf U) = p := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf U)
    rw [F.card_U, Nat.card_congr (subgroupOfEquivOfLe (le_sup_left : Z ≤ U)).toEquiv,
      F.card_Z] at h1
    have hpp : 0 < p := hp.pos
    have : p * p = Nat.card (U ⧸ Z.subgroupOf U) * p := by rw [← h1, pow_two]
    exact (Nat.eq_of_mul_eq_mul_right hpp this).symm
  have hr : Nat.card γ.range ≤ p := hq ▸ Subgroup.card_le_card_group _
  calc Nat.card E = Nat.card γ.ker * Nat.card γ.range := (Subgroup.card_ker_mul_card_range γ).symm
    _ ≤ p ^ 2 * p := Nat.mul_le_mul hE0 hr
    _ = p ^ 3 := by ring

theorem exists_extraspecialFrame {p : ℕ} (hp : p.Prime) {P D Z : Subgroup G} (hP : IsPGroup p P)
    (hDP : D ≤ P) (hPD : P ≤ normalizer (D : Set G)) (hDc : Nat.card D = p ^ 3)
    (hpow : ∀ x ∈ D, x ^ p = 1) (hZD : Z ≤ D) (hZc : Nat.card Z = p)
    (hZcomm : ∀ z ∈ Z, ∀ d ∈ D, d * z = z * d)
    (hZmem : ∀ d ∈ D, (∀ e ∈ D, e * d = d * e) → d ∈ Z)
    (hZP : ∀ z ∈ Z, ∀ g ∈ P, g * z = z * g)
    (hcZ : ∀ d ∈ D, ∀ e ∈ D, d * e * d⁻¹ * e⁻¹ ∈ Z) (hZne : Z ≠ D) :
    ∃ x y : G, ExtraspecialFrame p P D Z x y := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  have hZcen : ∀ z ∈ Z, ∀ g ∈ P, g * z * g⁻¹ = z := fun z hz g hg => by
    rw [mul_inv_eq_iff_eq_mul]
    exact hZP z hz g hg
  have hPZ : (P : Subgroup G) ≤ normalizer (Z : Set G) := fun g hg =>
    mem_normalizer_iff.2 fun z => ⟨fun hz => by rw [hZcen z hz g hg]; exact hz,
      fun hz => by
        have h1 := hZcen _ hz g⁻¹ (inv_mem hg)
        have h2 : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
        rwa [h2] at h1 ▸ hz⟩
  obtain ⟨x, hxD, hxZ, hx⟩ := exists_mem_not_mem_commutator_mem hP hDP hZD hZne hPD hPZ
  have hxp : x ^ p = 1 := hpow x hxD
  have hZx : ∀ z ∈ Z, z * x = x * z := fun z hz => (hZcomm z hz x hxD).symm
  have hUc : Nat.card ↥(Z ⊔ zpowers x) = p ^ 2 := by
    rw [card_sup_zpowers hp Z hxp hxZ hZx, hZc, pow_two]
  have hUD : Z ⊔ zpowers x ≤ D := sup_le hZD (zpowers_le.mpr hxD)
  have hUne : Z ⊔ zpowers x ≠ D := by
    intro h
    rw [h, hDc] at hUc
    have := Nat.pow_right_injective hp.two_le hUc
    omega
  have hPU : (P : Subgroup G) ≤ normalizer ((Z ⊔ zpowers x : Subgroup G) : Set G) :=
    normalizer_sup_zpowers_of_comm hZcen hx
  obtain ⟨y, hyD, hyU, hy⟩ := exists_mem_not_mem_commutator_mem hP hDP hUD hUne hPD hPU
  have hDeq : Z ⊔ zpowers x ⊔ zpowers y = D := by
    have hWD : Z ⊔ zpowers x ⊔ zpowers y ≤ D := sup_le hUD (zpowers_le.mpr hyD)
    have hUW : Z ⊔ zpowers x < Z ⊔ zpowers x ⊔ zpowers y :=
      lt_of_le_of_ne le_sup_left fun h => hyU (h ▸ mem_sup_right (mem_zpowers y))
    have hlt : p ^ 2 < Nat.card ↥(Z ⊔ zpowers x ⊔ zpowers y) :=
      hUc ▸ Subgroup.card_lt_of_lt hUW
    have hdvd : Nat.card ↥(Z ⊔ zpowers x ⊔ zpowers y) ∣ p ^ 3 :=
      hDc ▸ Subgroup.card_dvd_of_le hWD
    obtain ⟨i, hi, hiW⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hi3 : i = 3 := by
      rw [hiW] at hlt
      have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
      omega
    exact Subgroup.eq_of_le_of_card_ge hWD (by rw [hDc, hiW, hi3])
  exact ⟨x, y, ⟨hp, hDc, hZc, hZD, hDP, hZcomm, hZmem, hZP, hcZ, hxD, hyD, hx, hy, hDeq, hUc⟩⟩

theorem card_le_of_elemAbelian_normalizing {p : ℕ} (hp : p.Prime) {P D E : Subgroup G}
    (hP : IsPGroup p P) (hDP : D ≤ P) (hPD : P ≤ normalizer (D : Set G))
    (hD : ¬ IsMulCommutative D) (hDc : Nat.card D = p ^ 3)
    (hpow : ∀ x ∈ D, x ^ p = 1)
    (hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ centralizer (D : Set G))
    (hZc : Nat.card ((center D).map D.subtype) = p)
    (hZP : (center D).map D.subtype ≤ centralizer (P : Set G))
    (hrank : Open.pRank p (D ⊔ (P ⊓ centralizer (D : Set G)) : Subgroup G) ≤ 2)
    (hEP : E ≤ P) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  set Z : Subgroup G := (center D).map D.subtype with hZ
  have hZD : Z ≤ D := map_subtype_le _
  have hZcomm : ∀ z ∈ Z, ∀ d ∈ D, d * z = z * d := fun z hz d hd =>
    mul_comm_of_mem_center_map hz hd
  have hZne : Z ≠ D := by
    intro h
    apply hD
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hb : (b : G) ∈ Z := h.symm ▸ b.2
    exact hZcomm _ hb a a.2
  have hcZ : ∀ d ∈ D, ∀ e ∈ D, d * e * d⁻¹ * e⁻¹ ∈ Z := by
    intro d hd e he
    have hc := hcomm d hd e he
    have hcD : d * e * d⁻¹ * e⁻¹ ∈ D := mul_mem (mul_mem (mul_mem hd he) (inv_mem hd)) (inv_mem he)
    exact ⟨⟨_, hcD⟩, mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_iff.mp hc g g.2),
      rfl⟩
  have hZmem : ∀ d ∈ D, (∀ e ∈ D, e * d = d * e) → d ∈ Z := fun d hd h =>
    ⟨⟨d, hd⟩, mem_center_iff.2 fun g => Subtype.ext (h g g.2), rfl⟩
  obtain ⟨x, y, F⟩ := exists_extraspecialFrame hp hP hDP hPD hDc hpow hZD hZc hZcomm hZmem
    (fun z hz g hg => mem_centralizer_iff.1 (hZP hz) g hg) hcZ hZne
  exact F.card_le_of_elemAbelian hrank hEP hE

theorem not_le_normalizer_of_four_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hP4 : 4 ≤ Open.pRank p (P : Subgroup G)) : ¬ (P : Subgroup G) ≤ normalizer (D : Set G) := by
  intro hPD
  have hfact : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEP, hE, hEc⟩ := pRank_attained p (P : Subgroup G) (by omega)
  have hDP : D ≤ P := hext.obstruction.2.1
  by_cases hDab : IsMulCommutative D
  ·
    have hiso := hext.isIsolatedPlane_of_isMulCommutative hp hDab
    have hdvd : p ^ 3 ∣ Nat.card E := hEc ▸ pow_dvd_pow p (by omega)
    obtain ⟨E', hE'c, -, hE'E⟩ :=
      Sylow.exists_subgroup_card_pow_prime_le_le hp (H := ⊥) (L := E) (by simp) hdvd bot_le
    exact not_elemAbelian_cube_le_normalizer_of_isIsolatedPlane hp P.isPGroup' hiso
      (le_inf (hE'E.trans hEP) ((hE'E.trans hEP).trans hPD))
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E').2
        (isElemAbelian_mono hE hE'E)) hE'c
  ·
    have hcard := card_le_of_elemAbelian_normalizing hp P.isPGroup' hDP hPD hDab
      (hext.card_eq_of_not_isMulCommutative hp hp2 hDab)
      (hext.pow_eq_one_and_commutator_mem hp hp2).1 (hext.pow_eq_one_and_commutator_mem hp hp2).2
      (hext.card_center_eq hp hp2 hDab) (hext.center_le_centralizer hp hp2 hDab)
      hext.product_rank_eq.le hEP hE
    rw [hEc] at hcard
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
    omega

end CFSG.LocalAnalysis.RankFourTheoremC
