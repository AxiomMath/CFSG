module

import CFSG.Quasithin.Background.GoldschmidtB69DeepLt
import CFSG.Quasithin.Background.FFC13E
import CFSG.Fischer.NoF25.Steiner
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

private theorem isInv_sup_of_isInv {V : Type} [CommGroup V]
    {L A : Subgroup (MulAut V)} {T : Subgroup V}
    (hL : XMod.IsInv ↥L T) (hA : XMod.IsInv ↥A T) : XMod.IsInv ↥(L ⊔ A) T := by
  have hls : L ≤ stabSub T := B1.le_stabSub_of_invariant (fun a ha w hw => hL ⟨a, ha⟩ w hw)
  have has : A ≤ stabSub T := B1.le_stabSub_of_invariant (fun a ha w hw => hA ⟨a, ha⟩ w hw)
  intro x y hy
  exact ((mem_stabSub.mp ((sup_le hls has) x.2)) y).2 hy

private theorem isInv_map_of_normalizer {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {Γ : Subgroup V} (hΓ : XMod.IsInv ↥L Γ) {a : MulAut V}
    (ha : a ∈ Subgroup.normalizer (L : Set (MulAut V))) :
    XMod.IsInv ↥L (Γ.map a.toMonoidHom) := by
  intro l x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have hmem : a⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut V)) := Subgroup.inv_mem _ ha
  have hconj : a⁻¹ * l.1 * a ∈ L :=
    (Subgroup.mem_normalizer_iff''.mp ha l.1).mp l.2
  let k : ↥L := ⟨a⁻¹ * l.1 * a, hconj⟩
  refine Subgroup.mem_map.mpr ⟨(k : MulAut V) g, ?_, ?_⟩
  · exact hΓ k g hg
  · change a ((a⁻¹ * l.1 * a) g) = l.1 (a g)
    simp [MulAut.mul_apply]

private theorem autSec_eq_bot_of_commOf_le {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {I Z : Subgroup V} (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hc : XMod.commOf ↥L I ≤ Z) : autSec L I Z = ⊥ := by
  rw [← B5.range_secHom L hLI hLZ]
  refine le_antisymm ?_ bot_le
  rintro φ ⟨l, rfl⟩
  rw [Subgroup.mem_bot, ← MonoidHom.mem_ker]
  refine (B5.mem_ker_secHom L hLI hLZ l).2 ⟨hLI l.2, fun i hi => ?_⟩
  exact hc (Subgroup.subset_closure ⟨l, i, hi, rfl⟩)

private theorem mul_inv_mem_of_mk_eq_mk {V : Type} [CommGroup V] {I Z : Subgroup V}
    {a b : ↥I} (h : (QuotientGroup.mk a : Sec I Z) = QuotientGroup.mk b) :
    (a : V) * (b : V)⁻¹ ∈ Z := by
  have h1 : QuotientGroup.mk' (Z.subgroupOf I) (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, h, mul_inv_cancel]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa using h1

private theorem mem_zpowers_iff_eq_one_or {G : Type*} [Group G] [Finite G] [DecidableEq G]
    {w : G} (hw : w ^ 2 = 1) (hw1 : w ≠ 1) (x : G) :
    x ∈ Subgroup.zpowers w ↔ x = 1 ∨ x = w := by
  have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw
  have horder : orderOf w = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  rw [mem_zpowers_iff_mem_range_orderOf, horder]
  simp only [Finset.mem_range, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    interval_cases n
    · exact Or.inl (pow_zero w)
    · exact Or.inr (pow_one w)
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by simp⟩
    · exact ⟨1, by norm_num, by simp⟩

private def IsMinInv {V : Type} [CommGroup V] (L : Subgroup (MulAut V)) (Γ : Subgroup V) : Prop :=
  Γ ≠ ⊥ ∧ XMod.IsInv ↥L Γ ∧ ∀ Δ : Subgroup V, Δ ≠ ⊥ → XMod.IsInv ↥L Δ → Δ ≤ Γ → Δ = Γ

private theorem IsMinInv.inf_eq_bot_of_ne {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {Γ Δ : Subgroup V} (hΓ : IsMinInv L Γ) (hΔ : IsMinInv L Δ) (hne : Γ ≠ Δ) :
    Γ ⊓ Δ = ⊥ := by
  by_contra h
  have hinf : Γ ⊓ Δ = Γ :=
    hΓ.2.2 (Γ ⊓ Δ) h (hΓ.2.1.inf hΔ.2.1) inf_le_left
  have hle : Γ ≤ Δ := by rw [← hinf]; exact inf_le_right
  exact hne (hΔ.2.2 Γ hΓ.1 hΓ.2.1 hle)

private theorem IsMinInv.map {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {Γ : Subgroup V} (hΓ : IsMinInv L Γ) {a : MulAut V}
    (ha : a ∈ Subgroup.normalizer (L : Set (MulAut V))) :
    IsMinInv L (Γ.map a.toMonoidHom) := by
  refine ⟨?_, isInv_map_of_normalizer hΓ.2.1 ha, ?_⟩
  · intro hbot
    apply hΓ.1
    refine le_antisymm ?_ bot_le
    intro g hg
    have hmem : a g ∈ Γ.map a.toMonoidHom := Subgroup.mem_map_of_mem _ hg
    rw [hbot, Subgroup.mem_bot] at hmem
    have hg1 : g = 1 := a.injective (by simpa using hmem)
    simp [hg1]
  · intro Δ hΔne hΔinv hΔle
    have hkey : Δ.map a.symm.toMonoidHom = Γ := by
      apply hΓ.2.2
      · intro h
        apply hΔne
        have := congrArg (fun T : Subgroup V => T.map a.toMonoidHom) h
        rw [Subgroup.map_map] at this
        have hcomp : a.toMonoidHom.comp a.symm.toMonoidHom = MonoidHom.id V := by ext; simp
        rw [hcomp, Subgroup.map_id, Subgroup.map_bot] at this
        exact this
      · exact isInv_map_of_normalizer hΔinv (Subgroup.inv_mem _ ha)
      · intro d hd
        obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hd
        obtain ⟨h, hh, hgh⟩ := Subgroup.mem_map.mp (hΔle hg)
        rw [← hgh]
        simpa using hh
    have : Δ = Γ.map a.toMonoidHom := by
      have := congrArg (fun T : Subgroup V => T.map a.toMonoidHom) hkey
      rw [Subgroup.map_map] at this
      have hcomp : a.toMonoidHom.comp a.symm.toMonoidHom = MonoidHom.id V := by ext; simp
      rw [hcomp, Subgroup.map_id] at this
      exact this
    exact this

private theorem exists_isMinInv_aux {V : Type} [CommGroup V] [Finite V]
    (L : Subgroup (MulAut V)) (n : ℕ) :
    ∀ J : Subgroup V, Nat.card J = n → J ≠ ⊥ → XMod.IsInv ↥L J →
      ∃ Γ : Subgroup V, IsMinInv L Γ ∧ Γ ≤ J := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J hcard hJne hJinv
    by_cases hmin : ∀ Δ : Subgroup V, Δ ≠ ⊥ → XMod.IsInv ↥L Δ → Δ ≤ J → Δ = J
    · exact ⟨J, ⟨hJne, hJinv, hmin⟩, le_rfl⟩
    · push Not at hmin
      obtain ⟨Δ, hΔne, hΔinv, hΔle, hΔneJ⟩ := hmin
      have hlt : Nat.card Δ < Nat.card J := by
        have hle : Nat.card Δ ≤ Nat.card J := Subgroup.card_le_of_le hΔle
        have hne : Nat.card Δ ≠ Nat.card J := by
          intro hc
          exact hΔneJ (Subgroup.eq_of_le_of_card_ge hΔle (le_of_eq hc.symm))
        omega
      rw [hcard] at hlt
      obtain ⟨Γ, hΓ, hΓΔ⟩ := ih (Nat.card Δ) hlt Δ rfl hΔne hΔinv
      exact ⟨Γ, hΓ, hΓΔ.trans hΔle⟩

private theorem exists_isMinInv {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {J : Subgroup V} (hJ : J ≠ ⊥) (hJinv : XMod.IsInv ↥L J) :
    ∃ Γ : Subgroup V, IsMinInv L Γ ∧ Γ ≤ J :=
  exists_isMinInv_aux L (Nat.card J) J rfl hJ hJinv

private theorem exists_min_card_isMinInv {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} (h : ∃ Γ : Subgroup V, IsMinInv L Γ) :
    ∃ X : Subgroup V, IsMinInv L X ∧ ∀ Γ : Subgroup V, IsMinInv L Γ → Nat.card X ≤ Nat.card Γ := by
  let : Nonempty {Γ : Subgroup V // IsMinInv L Γ} := ⟨⟨h.choose, h.choose_spec⟩⟩
  obtain ⟨⟨X, hX⟩, hmin⟩ :=
    Finite.exists_min (fun Γ : {Γ : Subgroup V // IsMinInv L Γ} => Nat.card Γ.1)
  exact ⟨X, hX, fun Γ hΓ => hmin ⟨Γ, hΓ⟩⟩

private theorem iSup_translates_eq_top {V : Type} [CommGroup V] [Finite V]
    {L A : Subgroup (MulAut V)} (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) (⊥ : Subgroup V) ⊤)
    {Γ : Subgroup V} (hΓ : IsMinInv L Γ) :
    (⨆ a : ↥A, Γ.map (a : MulAut V).toMonoidHom) = ⊤ := by
  let T : Subgroup V := ⨆ a : ↥A, Γ.map (a : MulAut V).toMonoidHom
  have hL : XMod.IsInv ↥L T := by
    intro l x hx
    refine Subgroup.iSup_induction (S := fun a : ↥A => Γ.map (a : MulAut V).toMonoidHom)
      (C := fun z => l • z ∈ T) hx ?_ ?_ ?_
    · intro a y hy
      exact Subgroup.mem_iSup_of_mem a (isInv_map_of_normalizer hΓ.2.1 (hAL a.2) l y hy)
    · rw [Subgroup.smul_def, MulAut.smul_def, map_one]; exact T.one_mem
    · intro p q hp hq
      rw [Subgroup.smul_def, MulAut.smul_def, map_mul]; exact T.mul_mem hp hq
  have hA : XMod.IsInv ↥A T := by
    intro b x hx
    refine Subgroup.iSup_induction (S := fun a : ↥A => Γ.map (a : MulAut V).toMonoidHom)
      (C := fun z => b • z ∈ T) hx ?_ ?_ ?_
    · intro a y hy
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_iSup_of_mem (⟨b * a, A.mul_mem b.2 a.2⟩ : ↥A) ?_
      refine Subgroup.mem_map.mpr ⟨g, hg, ?_⟩
      change (b : MulAut V) ((a : MulAut V) g) = (b : MulAut V) ((a : MulAut V) g)
      rfl
    · rw [Subgroup.smul_def, MulAut.smul_def, map_one]; exact T.one_mem
    · intro p q hp hq
      rw [Subgroup.smul_def, MulAut.smul_def, map_mul]; exact T.mul_mem hp hq
  have hTinv : XMod.IsInv ↥(L ⊔ A) T := isInv_sup_of_isInv hL hA
  have hTne : T ≠ ⊥ := by
    intro hbot
    have hle : Γ.map ((1 : MulAut V).toMonoidHom) ≤ T :=
      le_iSup (fun a : ↥A => Γ.map (a : MulAut V).toMonoidHom) ⟨1, A.one_mem⟩
    rw [hbot] at hle
    have hΓbot : Γ ≤ ⊥ := fun g hg => by
      have := hle (Subgroup.mem_map_of_mem (1 : MulAut V).toMonoidHom hg)
      simpa using this
    exact hΓ.1 (le_antisymm hΓbot bot_le)
  rcases hirr.2 T hTinv bot_le le_top with h | h
  · exact absurd h hTne
  · exact h

private theorem map_eq_self_fixes_top {V : Type} [CommGroup V] [Finite V]
    {L A : Subgroup (MulAut V)} (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hAe : IsElemAbelian2 A) (hquad : IsQuadratic A)
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) (⊥ : Subgroup V) ⊤)
    {Γ : Subgroup V} (hΓ : IsMinInv L Γ) {a c : MulAut V} (ha : a ∈ A) (hc : c ∈ A)
    (hfix : Γ.map a.toMonoidHom = Γ) (hne : Γ.map c.toMonoidHom ≠ Γ) : a = 1 := by
  have hfixΓ : ∀ x ∈ Γ, a x = x := by
    intro x hx
    have hyc : a x * x⁻¹ ∈ commV A := Subgroup.subset_closure ⟨a, ha, x, rfl⟩
    have hyfix : a x * x⁻¹ ∈ fixV A := hquad hyc
    have haxΓ : a x ∈ Γ := by
      have : a x ∈ Γ.map a.toMonoidHom := Subgroup.mem_map_of_mem _ hx
      rwa [hfix] at this
    have hyΓ : a x * x⁻¹ ∈ Γ := Γ.mul_mem haxΓ (Γ.inv_mem hx)
    have hycΓ : a x * x⁻¹ ∈ Γ.map c.toMonoidHom := by
      have hcy : c (a x * x⁻¹) = a x * x⁻¹ := hyfix c hc
      rw [← hcy, map_mul, map_inv]
      exact (Γ.map c.toMonoidHom).mul_mem
        (Subgroup.mem_map_of_mem _ haxΓ)
        ((Γ.map c.toMonoidHom).inv_mem (Subgroup.mem_map_of_mem _ hx))
    have hinf := IsMinInv.inf_eq_bot_of_ne hΓ (IsMinInv.map (a := c) hΓ (hAL hc)) (Ne.symm hne)
    have hybot : a x * x⁻¹ ∈ (⊥ : Subgroup V) := by
      rw [← hinf]; exact ⟨hyΓ, hycΓ⟩
    exact mul_inv_eq_one.mp (by simpa using hybot)
  have hfixAll : ∀ d ∈ A, ∀ x ∈ Γ, a (d x) = d x := by
    intro d hd x hx
    rw [← MulAut.mul_apply, hAe.1 a ha d hd, MulAut.mul_apply, hfixΓ x hx]
  have hT := iSup_translates_eq_top hAL hirr hΓ
  ext z
  rw [MulAut.one_apply]
  have hzT : z ∈ ⨆ d : ↥A, Γ.map (d : MulAut V).toMonoidHom := by rw [hT]; trivial
  refine Subgroup.iSup_induction (S := fun d : ↥A => Γ.map (d : MulAut V).toMonoidHom)
    (C := fun z => a z = z) hzT ?_ ?_ ?_
  · intro d y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact hfixAll d d.2 x hx
  · rw [map_one]
  · intro p q hp hq
    rw [map_mul, hp, hq]

private theorem map_eq_self_imp_eq_one {V : Type} [CommGroup V] [Finite V]
    {L A : Subgroup (MulAut V)} (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hAe : IsElemAbelian2 A) (hquad : IsQuadratic A)
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) (⊥ : Subgroup V) ⊤)
    {Γ : Subgroup V} (hΓ : IsMinInv L Γ) (hΓtop : Γ ≠ ⊤) {a : MulAut V} (ha : a ∈ A) :
    Γ.map a.toMonoidHom = Γ → a = 1 := by
  intro hfix
  by_contra ha1
  by_cases hall : ∀ c ∈ A, Γ.map c.toMonoidHom = Γ
  · have hΓinv : XMod.IsInv ↥A Γ := by
      intro c w hw
      have : (c : MulAut V) w ∈ Γ.map (c : MulAut V).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hw
      rw [hall c c.2] at this
      exact this
    have hsupinv : XMod.IsInv ↥(L ⊔ A) Γ := isInv_sup_of_isInv hΓ.2.1 hΓinv
    rcases hirr.2 Γ hsupinv bot_le le_top with h | h
    · exact hΓ.1 h
    · exact hΓtop h
  · push Not at hall
    obtain ⟨c, hcA, hcne⟩ := hall
    exact ha1 (map_eq_self_fixes_top hAL hAe hquad hirr hΓ ha hcA hfix hcne)

private noncomputable def graph {V : Type} [CommGroup V] {X X' : Subgroup V}
    (φ : ↥X →* ↥X') : Subgroup V :=
  (X.subtype * (X'.subtype.comp φ)).range

private theorem mem_graph {V : Type} [CommGroup V] {X X' : Subgroup V}
    {φ : ↥X →* ↥X'} {v : V} :
    v ∈ graph φ ↔ ∃ x : ↥X, (x : V) * (φ x : V) = v := by
  rw [graph, MonoidHom.mem_range]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, by simpa [MonoidHom.mul_apply] using hx⟩,
    fun ⟨x, hx⟩ => ⟨x, by simpa [MonoidHom.mul_apply] using hx⟩⟩

private theorem eq_of_mul_eq_mul_of_inf_eq_bot {V : Type} [CommGroup V]
    {X X' : Subgroup V} (hdisj : X ⊓ X' = ⊥) {x x' y y' : V}
    (hx : x ∈ X) (hx' : x' ∈ X') (hy : y ∈ X) (hy' : y' ∈ X')
    (h : x * x' = y * y') : x = y ∧ x' = y' := by
  have heq : y⁻¹ * x = y' * x'⁻¹ := by
    calc y⁻¹ * x = y⁻¹ * (x * x') * x'⁻¹ := by group
      _ = y⁻¹ * (y * y') * x'⁻¹ := by rw [h]
      _ = y' * x'⁻¹ := by group
  have h1 : y⁻¹ * x ∈ X ⊓ X' := by
    refine ⟨X.mul_mem (X.inv_mem hy) hx, ?_⟩
    rw [heq]
    exact X'.mul_mem hy' (X'.inv_mem hx')
  have hx1 : y⁻¹ * x = 1 := by
    have := h1
    rw [hdisj] at this
    simpa using this
  have hx'1 : y' * x'⁻¹ = 1 := by
    have := h1
    rw [hdisj, heq] at this
    simpa using this
  exact ⟨mul_inv_eq_one.mp (by simpa [mul_comm] using hx1),
    (mul_inv_eq_one.mp (by simpa [mul_comm] using hx'1)).symm⟩

private theorem exists_unique_coord {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') (d : ↥Y) :
    ∃! p : ↥X × ↥X', (p.1 : V) * (p.2 : V) = (d : V) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.mp (hYH d.2)
  refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy, ?_⟩
  rintro ⟨x', y'⟩ hx'y'
  obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul_of_inf_eq_bot hdisj hx hy x'.2 y'.2
    (hxy.trans hx'y'.symm)
  exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)

private noncomputable def coord {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') (d : ↥Y) : ↥X :=
  (Classical.choose (exists_unique_coord hdisj hYH d)).1

private noncomputable def coordY {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') (d : ↥Y) : ↥X' :=
  (Classical.choose (exists_unique_coord hdisj hYH d)).2

private theorem coord_spec {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') (d : ↥Y) :
    (coord hdisj hYH d : V) * (coordY hdisj hYH d : V) = (d : V) :=
  (Classical.choose_spec (exists_unique_coord hdisj hYH d)).1

private theorem coord_eq_of_mul {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') {d : ↥Y} {x : ↥X} {y : ↥X'}
    (h : (x : V) * (y : V) = (d : V)) : coord hdisj hYH d = x :=
  (congrArg Prod.fst ((Classical.choose_spec (exists_unique_coord hdisj hYH d)).2 (x, y) h)).symm

private theorem coordY_eq_of_mul {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') {d : ↥Y} {x : ↥X} {y : ↥X'}
    (h : (x : V) * (y : V) = (d : V)) : coordY hdisj hYH d = y :=
  (congrArg Prod.snd ((Classical.choose_spec (exists_unique_coord hdisj hYH d)).2 (x, y) h)).symm

private theorem coord_one {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') :
    coord hdisj hYH (1 : ↥Y) = 1 := by
  apply coord_eq_of_mul hdisj hYH (x := 1) (y := 1)
  simp

private theorem coord_mul {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') (d₁ d₂ : ↥Y) :
    coord hdisj hYH (d₁ * d₂) = coord hdisj hYH d₁ * coord hdisj hYH d₂ := by
  apply coord_eq_of_mul hdisj hYH (x := coord hdisj hYH d₁ * coord hdisj hYH d₂)
    (y := coordY hdisj hYH d₁ * coordY hdisj hYH d₂)
  simp only [Subgroup.coe_mul]
  rw [← coord_spec hdisj hYH d₁, ← coord_spec hdisj hYH d₂]
  ac_rfl

private theorem coordY_one {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') :
    coordY hdisj hYH (1 : ↥Y) = 1 := by
  apply coordY_eq_of_mul hdisj hYH (x := 1) (y := 1)
  simp

private theorem coordY_mul {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') (d₁ d₂ : ↥Y) :
    coordY hdisj hYH (d₁ * d₂) = coordY hdisj hYH d₁ * coordY hdisj hYH d₂ := by
  apply coordY_eq_of_mul hdisj hYH (x := coord hdisj hYH d₁ * coord hdisj hYH d₂)
    (y := coordY hdisj hYH d₁ * coordY hdisj hYH d₂)
  simp only [Subgroup.coe_mul]
  rw [← coord_spec hdisj hYH d₁, ← coord_spec hdisj hYH d₂]
  ac_rfl

private noncomputable def coordHom {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') : ↥Y →* ↥X where
  toFun := coord hdisj hYH
  map_one' := coord_one hdisj hYH
  map_mul' := coord_mul hdisj hYH

private noncomputable def coordYHom {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') : ↥Y →* ↥X' where
  toFun := coordY hdisj hYH
  map_one' := coordY_one hdisj hYH
  map_mul' := coordY_mul hdisj hYH

private theorem coord_injective {V : Type} [CommGroup V] {X X' Y : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X') (hYdisj : Y ⊓ X' = ⊥) :
    Function.Injective (coordHom hdisj hYH) := by
  intro d₁ d₂ h
  have hx : (coord hdisj hYH d₁ : V) = (coord hdisj hYH d₂ : V) := congrArg Subtype.val h
  have hmem : (coordY hdisj hYH d₁ : V) * (coordY hdisj hYH d₂ : V)⁻¹ ∈ Y ⊓ X' := by
    constructor
    · have e : (d₁ : V) * (d₂ : V)⁻¹ =
          (coordY hdisj hYH d₁ : V) * (coordY hdisj hYH d₂ : V)⁻¹ := by
        rw [← coord_spec hdisj hYH d₁, ← coord_spec hdisj hYH d₂, hx, mul_inv_rev]
        simp only [mul_assoc, mul_comm, mul_left_comm]
        exact mul_inv_cancel_left _ _
      rw [← e]
      exact Y.mul_mem d₁.2 (Y.inv_mem d₂.2)
    · exact X'.mul_mem (coordY hdisj hYH d₁).2 (X'.inv_mem (coordY hdisj hYH d₂).2)
  have hy : (coordY hdisj hYH d₁ : V) = (coordY hdisj hYH d₂ : V) := by
    have := hmem
    rw [hYdisj] at this
    exact mul_inv_eq_one.mp (by simpa using this)
  apply Subtype.ext
  calc (d₁ : V) = (coord hdisj hYH d₁ : V) * (coordY hdisj hYH d₁ : V) :=
        (coord_spec hdisj hYH d₁).symm
    _ = (coord hdisj hYH d₂ : V) * (coordY hdisj hYH d₂ : V) := by rw [hx, hy]
    _ = (d₂ : V) := coord_spec hdisj hYH d₂

private def eqvHoms {V : Type} [CommGroup V] (L : Subgroup (MulAut V)) {X X' : Subgroup V}
    (hX : XMod.IsInv ↥L X) (hX' : XMod.IsInv ↥L X') : Subgroup (↥X →* ↥X') where
  carrier := {φ | ∀ (l : ↥L) (x : ↥X),
    φ ⟨(l : MulAut V) x, hX l x x.2⟩ = ⟨(l : MulAut V) (φ x), hX' l (φ x) (φ x).2⟩}
  one_mem' := by
    intro l x
    apply Subtype.ext
    simp
  mul_mem' := by
    intro φ ψ hφ hψ l x
    simp [MonoidHom.mul_apply, hφ l x, hψ l x, map_mul]
  inv_mem' := by
    intro φ hφ l x
    apply Subtype.ext
    simp [MonoidHom.inv_apply, hφ l x, map_inv]

private theorem eqvHoms_sq_one {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} {X X' : Subgroup V}
    (hX : XMod.IsInv ↥L X) (hX' : XMod.IsInv ↥L X')
    (φ : ↥(eqvHoms L hX hX')) : φ ^ 2 = 1 := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two, MonoidHom.mul_apply]
  exact Subtype.ext (by simpa [pow_two] using hV ((φ : ↥X →* ↥X') x : V))

private theorem eqvHoms_isPGroup {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} {X X' : Subgroup V}
    (hX : XMod.IsInv ↥L X) (hX' : XMod.IsInv ↥L X') :
    IsPGroup 2 ↥(eqvHoms L hX hX') := by
  rw [IsPGroup.iff_orderOf]
  intro φ
  have hφ2 : φ ^ 2 = 1 := eqvHoms_sq_one hV hX hX' φ
  have hdvd : orderOf φ ∣ 2 := orderOf_dvd_of_pow_eq_one hφ2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

private noncomputable def graphMap {V : Type} [CommGroup V] {X X' : Subgroup V}
    (φ : ↥X →* ↥X') : ↥X →* ↥(graph φ) :=
  MonoidHom.codRestrict (X.subtype * (X'.subtype.comp φ)) (graph φ)
    (fun x => (mem_graph).2 ⟨x, rfl⟩)

private theorem graphMap_apply {V : Type} [CommGroup V] {X X' : Subgroup V}
    (φ : ↥X →* ↥X') (x : ↥X) :
    ((graphMap φ x : ↥(graph φ)) : V) = (x : V) * (φ x : V) := rfl

private theorem graphMap_injective {V : Type} [CommGroup V] {X X' : Subgroup V}
    {φ : ↥X →* ↥X'} (hdisj : X ⊓ X' = ⊥) : Function.Injective (graphMap φ) := by
  intro x₁ x₂ h
  have hv : (x₁ : V) * (φ x₁ : V) = (x₂ : V) * (φ x₂ : V) := by
    have := congrArg (fun y : ↥(graph φ) => (y : V)) h
    simpa [graphMap_apply] using this
  exact Subtype.ext (eq_of_mul_eq_mul_of_inf_eq_bot hdisj x₁.2 (φ x₁).2 x₂.2 (φ x₂).2 hv).1

private theorem graphMap_surjective {V : Type} [CommGroup V] {X X' : Subgroup V}
    (φ : ↥X →* ↥X') : Function.Surjective (graphMap φ) := by
  intro y
  obtain ⟨x, hx⟩ := (mem_graph).1 y.2
  exact ⟨x, Subtype.ext (by simpa [graphMap_apply] using hx)⟩

private theorem map_map_self {V : Type} [CommGroup V] {a : MulAut V} (ha2 : a * a = 1)
    (Y : Subgroup V) : (Y.map a.toMonoidHom).map a.toMonoidHom = Y := by
  rw [Subgroup.map_map]
  have hcomp : a.toMonoidHom.comp a.toMonoidHom = MonoidHom.id V := by
    ext x
    show a (a x) = x
    rw [← MulAut.mul_apply, ha2, MulAut.one_apply]
  rw [hcomp, Subgroup.map_id]

private theorem graph_inf_eq_bot {V : Type} [CommGroup V] {X X' : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (φ : ↥X →* ↥X') : graph φ ⊓ X' = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hy, hy'⟩
  obtain ⟨x, hx⟩ := (mem_graph).1 hy
  have hxX' : (x : V) ∈ X' := by
    have : (x : V) = y * ((φ x : ↥X') : V)⁻¹ := by
      rw [← hx]; group
    rw [this]
    exact X'.mul_mem hy' (X'.inv_mem (φ x).2)
  have hx1 : (x : V) = 1 := by
    have : (x : V) ∈ X ⊓ X' := ⟨x.2, hxX'⟩
    rw [hdisj] at this
    simpa using this
  have hxsub : x = 1 := Subtype.ext hx1
  rw [Subgroup.mem_bot, ← hx, hxsub, map_one]
  simp

private theorem card_graph {V : Type} [CommGroup V] {X X' : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (φ : ↥X →* ↥X') : Nat.card (graph φ) = Nat.card X := by
  have hbi : Function.Bijective (graphMap φ) :=
    ⟨graphMap_injective hdisj, graphMap_surjective φ⟩
  exact (Nat.card_congr (MulEquiv.ofBijective (graphMap φ) hbi).toEquiv).symm

private theorem eqvHoms_of_isInv_graph {V : Type} [CommGroup V]
    {L : Subgroup (MulAut V)} {X X' : Subgroup V}
    (hX : XMod.IsInv ↥L X) (hX' : XMod.IsInv ↥L X') (hdisj : X ⊓ X' = ⊥)
    {φ : ↥X →* ↥X'} (hgraph : XMod.IsInv ↥L (graph φ)) :
    φ ∈ eqvHoms L hX hX' := by
  intro l x
  apply Subtype.ext
  have hmem : (l : MulAut V) ((x : V) * (φ x : V)) ∈ graph φ :=
    hgraph l ((x : V) * (φ x : V)) ((mem_graph).2 ⟨x, rfl⟩)
  obtain ⟨x', hx'⟩ := (mem_graph).1 hmem
  have hprod : ((x' : V) * (φ x' : V)) =
      ((l : MulAut V) x) * ((l : MulAut V) (φ x)) := by
    rw [hx', map_mul]
  have hx'l : x' = ⟨(l : MulAut V) x, hX l x x.2⟩ :=
    Subtype.ext (eq_of_mul_eq_mul_of_inf_eq_bot hdisj x'.2
      (φ x').2 (hX l x x.2) (hX' l (φ x) (φ x).2) hprod).1
  have hphi : φ x' = ⟨(l : MulAut V) (φ x), hX' l (φ x) (φ x).2⟩ :=
    Subtype.ext (eq_of_mul_eq_mul_of_inf_eq_bot hdisj x'.2
      (φ x').2 (hX l x x.2) (hX' l (φ x) (φ x).2) hprod).2
  rw [hx'l] at hphi
  exact congrArg Subtype.val hphi

private theorem graph_ne_X {V : Type} [CommGroup V] {X X' : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) {φ : ↥X →* ↥X'} (hφ : φ ≠ 1) : graph φ ≠ X := by
  intro h
  apply hφ
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  by_contra hxne
  have hxmem : (x : V) * (φ x : V) ∈ graph φ := (mem_graph).2 ⟨x, rfl⟩
  rw [h] at hxmem
  have hphiX : (φ x : V) ∈ X := by
    have : (φ x : V) = (x : V)⁻¹ * ((x : V) * (φ x : V)) := by group
    rw [this]
    exact X.mul_mem (X.inv_mem x.2) hxmem
  have hphi1 : (φ x : V) = 1 := by
    have : (φ x : V) ∈ X ⊓ X' := ⟨hphiX, (φ x).2⟩
    rw [hdisj] at this
    simpa using this
  exact hxne (by simpa using hphi1)
private theorem isMinInv_graph_minimal {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {X X' : Subgroup V} (hX : IsMinInv L X) (hX' : IsMinInv L X')
    (_hdisj : X ⊓ X' = ⊥) {φ : ↥X →* ↥X'}
    (hφ : φ ∈ eqvHoms L hX.2.1 hX'.2.1) :
    ∀ U : Subgroup V, U ≠ ⊥ → XMod.IsInv ↥L U → U ≤ graph φ → U = graph φ := by
      intro U hUne hUinv hUle
      let g : ↥X →* V := X.subtype * (X'.subtype.comp φ)
      let U₀ : Subgroup ↥X := U.comap g
      have hUeq : U = U₀.map g := (Subgroup.map_comap_eq_self hUle).symm
      have hU₀ne : U₀.map X.subtype ≠ ⊥ := by
        intro h
        apply hUne
        have hbot : U₀ = ⊥ := by
          have hker : U₀ ≤ (X.subtype : ↥X →* V).ker := by
            rw [← Subgroup.map_eq_bot_iff]
            exact h
          rw [Subgroup.ker_subtype] at hker
          exact le_antisymm hker bot_le
        rw [hUeq, hbot, Subgroup.map_bot]
      have hU₀inv : XMod.IsInv ↥L (U₀.map X.subtype) := by
        intro l y hy
        obtain ⟨x, hxU, rfl⟩ := Subgroup.mem_map.mp hy
        have hxU' : g x ∈ U := hxU
        have hge : g ⟨(l : MulAut V) x, hX.2.1 l x x.2⟩ = (l : MulAut V) (g x) := by
          change ((l : MulAut V) x) *
            ((φ ⟨(l : MulAut V) x, hX.2.1 l x x.2⟩ : ↥X') : V) =
              (l : MulAut V) ((x : V) * (φ x : V))
          rw [congrArg Subtype.val (hφ l x)]
          simp [map_mul]
        refine Subgroup.mem_map.mpr ⟨⟨(l : MulAut V) x, hX.2.1 l x x.2⟩, ?_, rfl⟩
        have hge' : g ⟨(l : MulAut V) x, hX.2.1 l x x.2⟩ = l • (g x) := by
          simpa [Subgroup.smul_def, MulAut.smul_def] using hge
        have := hUinv l (g x) hxU'
        rwa [← hge'] at this
      have hU₀eq : U₀.map X.subtype = X := hX.2.2 _ hU₀ne hU₀inv (Subgroup.map_subtype_le _)
      have hU₀top : U₀ = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : (x : V) ∈ U₀.map X.subtype := by rw [hU₀eq]; exact x.2
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        have : y = x := Subtype.ext hyx
        rwa [this] at hy
      rw [hUeq, hU₀top, Subgroup.map_top]
      rfl

private theorem isMinInv_graph {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {X X' : Subgroup V} (hX : IsMinInv L X) (hX' : IsMinInv L X')
    (hdisj : X ⊓ X' = ⊥) {φ : ↥X →* ↥X'}
    (hφ : φ ∈ eqvHoms L hX.2.1 hX'.2.1) : IsMinInv L (graph φ) := by
  have hmapinv : XMod.IsInv ↥L (graph φ) := by
    intro l y hy
    obtain ⟨x, rfl⟩ := (mem_graph).1 hy
    refine (mem_graph).2 ⟨⟨(l : MulAut V) x, hX.2.1 l x x.2⟩, ?_⟩
    simp [hφ l x, Subgroup.smul_def, MulAut.smul_def]
  refine ⟨?_, hmapinv, ?_⟩
  · intro hbot
    apply hX.1
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxmem : x * (φ ⟨x, hx⟩ : V) ∈ graph φ := (mem_graph).2 ⟨⟨x, hx⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hxmem
    have hx' : x ∈ X' := by
      have hxinv : x = ((φ ⟨x, hx⟩ : ↥X') : V)⁻¹ :=
        mul_eq_one_iff_eq_inv.mp hxmem
      rw [hxinv]
      exact X'.inv_mem (φ ⟨x, hx⟩).2
    have hx1 : x = 1 := by
      have hmem : x ∈ X ⊓ X' := ⟨hx, hx'⟩
      rw [hdisj] at hmem
      simpa using hmem
    simp [hx1]
  · exact isMinInv_graph_minimal hX hX' hdisj hφ

private theorem exists_graph_of_le_sup {V : Type} [CommGroup V] [Finite V]
    {X X' Y : Subgroup V} (hdisj : X ⊓ X' = ⊥) (hYH : Y ≤ X ⊔ X')
    (hYdisj : Y ⊓ X' = ⊥) (hcard : Nat.card Y = Nat.card X) :
    ∃ φ : ↥X →* ↥X', graph φ = Y := by
  have hbi : Function.Bijective (coordHom hdisj hYH) :=
    (Nat.bijective_iff_injective_and_card (coordHom hdisj hYH)).2
      ⟨coord_injective hdisj hYH hYdisj, hcard⟩
  let e : ↥Y ≃* ↥X := MulEquiv.ofBijective (coordHom hdisj hYH) hbi
  let φ : ↥X →* ↥X' := (coordYHom hdisj hYH).comp e.symm.toMonoidHom
  refine ⟨φ, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨x, rfl⟩ := (mem_graph).1 hv
    have hcoord : coord hdisj hYH (e.symm x) = x := by
      have := e.apply_symm_apply x
      exact this
    have hgraph : (x : V) * ((φ x : ↥X') : V) = ((e.symm x : ↥Y) : V) := by
      show (x : V) * (coordY hdisj hYH (e.symm x) : V) = ((e.symm x : ↥Y) : V)
      have := coord_spec hdisj hYH (e.symm x)
      rw [hcoord] at this
      exact this
    rw [hgraph]
    exact (e.symm x).2
  · intro hv
    refine (mem_graph).2 ⟨coord hdisj hYH ⟨v, hv⟩, ?_⟩
    have hd : e ⟨v, hv⟩ = coord hdisj hYH ⟨v, hv⟩ := rfl
    have hes : e.symm (coord hdisj hYH ⟨v, hv⟩) = ⟨v, hv⟩ := by
      rw [← hd, e.symm_apply_apply]
    have hphi : φ (coord hdisj hYH ⟨v, hv⟩) = coordY hdisj hYH ⟨v, hv⟩ := by
      show coordY hdisj hYH (e.symm (coord hdisj hYH ⟨v, hv⟩)) = _
      rw [hes]
    rw [hphi]
    simpa using coord_spec hdisj hYH ⟨v, hv⟩

private theorem graph_one {V : Type} [CommGroup V] {X X' : Subgroup V} :
    graph (1 : ↥X →* ↥X') = X := by
  ext v
  rw [mem_graph]
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro hv
    exact ⟨⟨v, hv⟩, by simp⟩

private theorem graph_ne_X' {V : Type} [CommGroup V] {X X' : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) (hX' : X' ≠ ⊥) (φ : ↥X →* ↥X') : graph φ ≠ X' := by
  intro h
  have := graph_inf_eq_bot hdisj φ
  rw [h, inf_idem] at this
  exact hX' this

private theorem graph_map_twist_inf_eq_bot {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {X X' : Subgroup V} (hX : IsMinInv L X)
    (hX' : IsMinInv L X') (hdisj : X ⊓ X' = ⊥) {a : MulAut V} (ha2 : a * a = 1)
    (haX : X.map a.toMonoidHom = X') {φ : ↥(eqvHoms L hX.2.1 hX'.2.1)}
    (hφ : (φ : ↥X →* ↥X') ≠ 1) :
    (graph (φ : ↥X →* ↥X')).map a.toMonoidHom ⊓ X' = ⊥ := by
  have haX' : X'.map a.toMonoidHom = X := by
    rw [← haX, map_map_self ha2]
  rw [eq_bot_iff]
  rintro y ⟨hy, hy'⟩
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  have hzX : z ∈ X := by
    have haz' : a (a z) ∈ X'.map a.toMonoidHom := Subgroup.mem_map_of_mem _ hy'
    rw [haX'] at haz'
    have hzz : a (a z) = z := by
      rw [← MulAut.mul_apply, ha2, MulAut.one_apply]
    rwa [hzz] at haz'
  have hzbot : z ∈ graph (φ : ↥X →* ↥X') ⊓ X := ⟨hz, hzX⟩
  have hinfX : graph (φ : ↥X →* ↥X') ⊓ X = ⊥ :=
    (isMinInv_graph hX hX' hdisj φ.2).inf_eq_bot_of_ne hX (graph_ne_X hdisj hφ)
  rw [hinfX] at hzbot
  have hz1 : z = 1 := by simpa using hzbot
  rw [hz1, map_one]
  simp

private theorem exists_graphTwist {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {X X' : Subgroup V} (hX : IsMinInv L X) (hX' : IsMinInv L X')
    (hdisj : X ⊓ X' = ⊥) {a : MulAut V}
    (haN : a ∈ Subgroup.normalizer (L : Set (MulAut V))) (ha2 : a * a = 1)
    (haX : X.map a.toMonoidHom = X') {φ : ↥(eqvHoms L hX.2.1 hX'.2.1)}
    (hφ : (φ : ↥X →* ↥X') ≠ 1) :
    ∃ θ : ↥(eqvHoms L hX.2.1 hX'.2.1), (θ : ↥X →* ↥X') ≠ 1 ∧
      graph (θ : ↥X →* ↥X') = (graph (φ : ↥X →* ↥X')).map a.toMonoidHom := by
  have hYH : graph (φ : ↥X →* ↥X') ≤ X ⊔ X' := by
    intro y hy
    obtain ⟨x, rfl⟩ := (mem_graph).1 hy
    exact Subgroup.mem_sup.mpr ⟨x, x.2, (φ : ↥X →* ↥X') x, ((φ : ↥X →* ↥X') x).2, rfl⟩
  have hYdisj : graph (φ : ↥X →* ↥X') ⊓ X' = ⊥ := graph_inf_eq_bot hdisj _
  have hYcard : Nat.card (graph (φ : ↥X →* ↥X')) = Nat.card X := card_graph hdisj _
  have haX' : X'.map a.toMonoidHom = X := by
    rw [← haX, map_map_self ha2]
  have hH : (X ⊔ X').map a.toMonoidHom = X ⊔ X' := by
    rw [Subgroup.map_sup, haX, haX', sup_comm]
  have hY'inv : XMod.IsInv ↥L ((graph (φ : ↥X →* ↥X')).map a.toMonoidHom) :=
    isInv_map_of_normalizer (isMinInv_graph hX hX' hdisj φ.2).2.1 haN
  have hY'H : (graph (φ : ↥X →* ↥X')).map a.toMonoidHom ≤ X ⊔ X' := by
    rw [← hH]
    exact Subgroup.map_mono hYH
  have hY'disj : (graph (φ : ↥X →* ↥X')).map a.toMonoidHom ⊓ X' = ⊥ :=
    graph_map_twist_inf_eq_bot hX hX' hdisj ha2 haX hφ
  have hY'card : Nat.card ((graph (φ : ↥X →* ↥X')).map a.toMonoidHom) = Nat.card X := by
    rw [Subgroup.card_map_of_injective a.injective, hYcard]
  obtain ⟨θ, hθgraph⟩ := exists_graph_of_le_sup hdisj hY'H hY'disj hY'card
  have hθE : θ ∈ eqvHoms L hX.2.1 hX'.2.1 :=
    eqvHoms_of_isInv_graph hX.2.1 hX'.2.1 hdisj (by rw [hθgraph]; exact hY'inv)
  have hθne : θ ≠ 1 := by
    intro hθ1
    have hY'X : (graph (φ : ↥X →* ↥X')).map a.toMonoidHom = X := by
      rw [← hθgraph, hθ1, graph_one]
    have hYX' : graph (φ : ↥X →* ↥X') = X' := by
      have := congrArg (fun T : Subgroup V => T.map a.toMonoidHom) hY'X
      rw [map_map_self ha2, haX] at this
      exact this
    exact graph_ne_X' hdisj hX'.1 (φ : ↥X →* ↥X') hYX'
  exact ⟨⟨θ, hθE⟩, hθne, hθgraph⟩

private theorem graph_injective {V : Type} [CommGroup V] {X X' : Subgroup V}
    (hdisj : X ⊓ X' = ⊥) :
    Function.Injective (fun φ : ↥X →* ↥X' => graph φ) := by
  intro φ ψ h
  apply MonoidHom.ext
  intro x
  have hxmem : (x : V) * (φ x : V) ∈ graph φ := (mem_graph).2 ⟨x, rfl⟩
  have hxmem' : (x : V) * (φ x : V) ∈ graph ψ := by
    simpa [h] using hxmem
  obtain ⟨x', hx'⟩ := (mem_graph).1 hxmem'
  obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul_of_inf_eq_bot hdisj x'.2 (ψ x').2 x.2 (φ x).2 hx'
  have h1s : x' = ⟨x, x.2⟩ := Subtype.ext h1
  rw [h1s] at h2
  exact Subtype.ext h2.symm

private theorem odd_card_ne_one {α : Type*} [Group α] [Finite α]
    (hpow : ∃ k : ℕ, Nat.card α = 2 ^ k) (hnt : Nontrivial α) :
    Odd (Nat.card {φ : α // φ ≠ 1}) := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let : Fintype {φ : α // φ ≠ 1} := Fintype.ofFinite _
  have h1 : 1 < Nat.card α := Finite.one_lt_card
  obtain ⟨k, hk⟩ := hpow
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero] at hk
      omega
    · exact hkpos
  have heven : Even (Nat.card α) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hk, pow_succ]
    exact ⟨2 ^ j, by ring⟩
  have hcard : Nat.card {φ : α // φ ≠ 1} = Nat.card α - 1 := by
    have := Set.card_ne_eq (1 : α)
    simp [Nat.card_eq_fintype_card]
  rw [hcard]
  obtain ⟨m, hm⟩ := heven
  have hm1 : 1 ≤ m := by
    rw [hm] at h1
    omega
  exact ⟨m - 1, by omega⟩

private theorem exists_involutive_twist {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {X X' : Subgroup V} (hX : IsMinInv L X) (hX' : IsMinInv L X')
    (hdisj : X ⊓ X' = ⊥) {a : MulAut V}
    (haN : a ∈ Subgroup.normalizer (L : Set (MulAut V))) (ha2 : a * a = 1)
    (haX : X.map a.toMonoidHom = X') :
    ∃ T : {φ : ↥(eqvHoms L hX.2.1 hX'.2.1) // φ ≠ 1} →
        {φ : ↥(eqvHoms L hX.2.1 hX'.2.1) // φ ≠ 1},
      Function.Involutive T ∧
      ∀ φ, graph ((T φ).1 : ↥X →* ↥X') =
        (graph (φ.1 : ↥X →* ↥X')).map a.toMonoidHom := by
  let T : {φ : ↥(eqvHoms L hX.2.1 hX'.2.1) // φ ≠ 1} →
      {φ : ↥(eqvHoms L hX.2.1 hX'.2.1) // φ ≠ 1} := fun φ => by
    let h := Classical.choose (exists_graphTwist hX hX' hdisj haN ha2 haX
      (by intro hh; exact φ.2 (Subtype.ext hh)))
    have hspec := Classical.choose_spec (exists_graphTwist hX hX' hdisj haN ha2 haX
      (by intro hh; exact φ.2 (Subtype.ext hh)))
    exact ⟨h, fun hh => hspec.1 (by
      show (h : ↥X →* ↥X') = 1
      simpa using congrArg Subtype.val hh)⟩
  have hTgraph : ∀ φ, graph ((T φ).1 : ↥X →* ↥X') =
      (graph (φ.1 : ↥X →* ↥X')).map a.toMonoidHom := fun φ =>
    (Classical.choose_spec (exists_graphTwist hX hX' hdisj haN ha2 haX
      (by intro hh; exact φ.2 (Subtype.ext hh)))).2
  have hT2 : Function.Involutive T := by
    intro φ
    apply Subtype.ext
    apply Subtype.ext
    apply graph_injective hdisj
    calc graph ((T (T φ)).1 : ↥X →* ↥X')
        = (graph ((T φ).1 : ↥X →* ↥X')).map a.toMonoidHom := hTgraph (T φ)
      _ = ((graph (φ.1 : ↥X →* ↥X')).map a.toMonoidHom).map a.toMonoidHom := by
            rw [hTgraph φ]
      _ = graph (φ.1 : ↥X →* ↥X') := map_map_self ha2 _
  exact ⟨T, hT2, hTgraph⟩

private theorem exists_fixed_of_nontrivial {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} {X X' : Subgroup V}
    (hX : IsMinInv L X) (hX' : IsMinInv L X') (hdisj : X ⊓ X' = ⊥) {a : MulAut V}
    (haN : a ∈ Subgroup.normalizer (L : Set (MulAut V))) (ha2 : a * a = 1)
    (haX : X.map a.toMonoidHom = X')
    (hE : ∃ φ : ↥(eqvHoms L hX.2.1 hX'.2.1), φ ≠ 1) :
    ∃ φ : ↥(eqvHoms L hX.2.1 hX'.2.1), φ ≠ 1 ∧
      (graph (φ : ↥X →* ↥X')).map a.toMonoidHom = graph (φ : ↥X →* ↥X') := by
  classical
  let E := eqvHoms L hX.2.1 hX'.2.1
  let Ene := {φ : ↥E // φ ≠ 1}
  let : Finite (↥X →* ↥X') :=
    Finite.of_injective (fun f : ↥X →* ↥X' => (f : ↥X → ↥X')) DFunLike.coe_injective
  let : Finite ↥E :=
    Finite.of_injective (fun φ : ↥E => (φ : ↥X →* ↥X')) Subtype.coe_injective
  let : Fintype ↥E := Fintype.ofFinite ↥E
  let : Fintype Ene := Fintype.ofFinite Ene
  have hEcard : ∃ k : ℕ, Nat.card ↥E = 2 ^ k :=
    IsPGroup.iff_card.mp (eqvHoms_isPGroup hV hX.2.1 hX'.2.1)
  have hnt : Nontrivial ↥E := by
    obtain ⟨φ, hφ⟩ := hE
    refine ⟨⟨φ, 1, ?_⟩⟩
    intro h
    exact hφ (by simpa using congrArg Subtype.val h)
  have hEneOdd : Odd (Nat.card Ene) := by
    simpa [Ene] using odd_card_ne_one hEcard hnt
  obtain ⟨T, hT2, hTgraph⟩ := exists_involutive_twist hX hX' hdisj haN ha2 haX
  let Tperm : Equiv.Perm Ene :=
    { toFun := T, invFun := T, left_inv := hT2, right_inv := hT2 }
  have hTperm2 : Tperm * Tperm = 1 := by
    apply Equiv.ext
    intro φ
    change T (T φ) = φ
    exact hT2 φ
  by_contra hno
  have hfree : ∀ φ ∈ (Finset.univ : Finset Ene), Tperm φ ≠ φ := by
    intro φ _ hfix
    apply hno
    refine ⟨φ.1, φ.2, ?_⟩
    have hg := hTgraph φ
    rw [show T φ = φ from hfix] at hg
    exact hg.symm
  have heven := CFSG.Fischer.even_card_of_involution Tperm hTperm2 Finset.univ
    (by intro x _; exact Finset.mem_univ (Tperm x)) hfree
  have heven' : Even (Nat.card Ene) := by simpa using heven
  exact (Nat.not_even_iff_odd.mpr hEneOdd) heven'
private theorem isMinInv_le_sup_eq {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} {X X' : Subgroup V}
    (hX : IsMinInv L X) (hX' : IsMinInv L X')
    (hXmin : ∀ Γ : Subgroup V, IsMinInv L Γ → Nat.card X ≤ Nat.card Γ)
    (hdisj : X ⊓ X' = ⊥) {a : MulAut V}
    (haN : a ∈ Subgroup.normalizer (L : Set (MulAut V))) (ha2 : a * a = 1)
    (haX : X.map a.toMonoidHom = X')
    (hno : ∀ Γ : Subgroup V, IsMinInv L Γ → Γ.map a.toMonoidHom ≠ Γ) :
    ∀ Δ : Subgroup V, IsMinInv L Δ → Δ ≤ X ⊔ X' → Δ = X ∨ Δ = X' := by
  intro Δ hΔ hΔH
  by_contra hne
  push Not at hne
  obtain ⟨hneX, hneX'⟩ := hne
  have hΔX' : Δ ⊓ X' = ⊥ := hΔ.inf_eq_bot_of_ne hX' hneX'
  have hinj : Function.Injective (coordHom hdisj hΔH) := coord_injective hdisj hΔH hΔX'
  have hle : Nat.card Δ ≤ Nat.card X := Nat.card_le_card_of_injective _ hinj
  have hge : Nat.card X ≤ Nat.card Δ := hXmin Δ hΔ
  have hcard : Nat.card Δ = Nat.card X := le_antisymm hle hge
  obtain ⟨φ, hφgraph⟩ := exists_graph_of_le_sup hdisj hΔH hΔX' hcard
  have hφne : φ ≠ 1 := by
    intro h
    apply hneX
    rw [← hφgraph, h, graph_one]
  have hφE : φ ∈ eqvHoms L hX.2.1 hX'.2.1 :=
    eqvHoms_of_isInv_graph hX.2.1 hX'.2.1 hdisj (by rw [hφgraph]; exact hΔ.2.1)
  have hE : ∃ ψ : ↥(eqvHoms L hX.2.1 hX'.2.1), ψ ≠ 1 :=
    ⟨⟨φ, hφE⟩, fun h => hφne (congrArg Subtype.val h)⟩
  obtain ⟨ψ, hψne, hψfix⟩ := exists_fixed_of_nontrivial hV hX hX' hdisj haN ha2 haX hE
  exact hno (graph (ψ : ↥X →* ↥X')) (isMinInv_graph hX hX' hdisj ψ.2) hψfix
private theorem card_sup_mul_card_inf {V : Type} [CommGroup V] [Finite V] (X Y : Subgroup V) :
    Nat.card ↥(X ⊔ Y) * Nat.card ↥(X ⊓ Y) = Nat.card X * Nat.card Y := by
  let π : V →* V ⧸ Y := QuotientGroup.mk' Y
  have h1 := B1More.card_map_mul_card_inf_ker X π
  have h2 := B1More.card_map_mul_card_inf_ker (X ⊔ Y) π
  have hker : π.ker = Y := QuotientGroup.ker_mk' Y
  have hsupinf : (X ⊔ Y) ⊓ Y = Y := inf_eq_right.2 le_sup_right
  have hmap : (X ⊔ Y).map π = X.map π := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp hw
      refine ⟨x, hx, ?_⟩
      rw [map_mul]
      have hy1 : π y = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact hy
      rw [hy1, mul_one]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_sup_left hx, rfl⟩
  rw [hker, hsupinf] at h2
  rw [hker] at h1
  rw [hmap] at h2
  rw [← h2, ← h1]
  ac_rfl

private theorem card_sup_of_inf_eq_bot {V : Type} [CommGroup V] [Finite V]
    (X Y : Subgroup V) (h : X ⊓ Y = ⊥) :
    Nat.card ↥(X ⊔ Y) = Nat.card X * Nat.card Y := by
  have := card_sup_mul_card_inf X Y
  rw [h] at this
  simpa using this
private theorem IsMinInv.ne_top_of_ne {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {X Γ : Subgroup V} (hX : IsMinInv L X) (hXtop : X ≠ ⊤) (hΓ : IsMinInv L Γ) :
    Γ ≠ ⊤ := by
  intro h
  apply hXtop
  have hle : X ≤ Γ := by rw [h]; exact le_top
  exact (hΓ.2.2 X hX.1 hX.2.1 hle).trans h

private theorem sup_map_eq {V : Type} [CommGroup V] (X X' : Subgroup V) {a b : MulAut V}
    (hab : b * a = a * b) (hXa : X.map a.toMonoidHom = X') :
    (X ⊔ X').map b.toMonoidHom = X.map b.toMonoidHom ⊔ (X.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_sup, ← hXa, Subgroup.map_map, Subgroup.map_map]
  rw [show b.toMonoidHom.comp a.toMonoidHom = a.toMonoidHom.comp b.toMonoidHom by
    ext x; simpa [MulAut.mul_apply] using congrArg (fun f : MulAut V => f x) hab]

private theorem inf_map_eq_bot_false {V : Type} [CommGroup V]
    {L A : Subgroup (MulAut V)} (_hA : IsElemAbelian2 A) (hquad : IsQuadratic A)
    {X X' : Subgroup V} (hX : IsMinInv L X) (hdisj : X ⊓ X' = ⊥)
    {a b : MulAut V} (ha : a ∈ A) (hb : b ∈ A) (haX : X.map a.toMonoidHom = X')
    (_ha1 : a ≠ 1) (hHdisj : (X ⊔ X') ⊓ ((X ⊔ X').map b.toMonoidHom) = ⊥) : False := by
  have hxex : ∃ x ∈ X, x ≠ 1 := by
    by_contra h
    push Not at h
    apply hX.1
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot, h x hx]
  obtain ⟨x, hxX, hx1⟩ := hxex
  let y : V := a x * x⁻¹
  have hyc : y ∈ commV A := Subgroup.subset_closure ⟨a, ha, x, rfl⟩
  have hyfix : y ∈ fixV A := hquad hyc
  have hyb : b y = y := hyfix b hb
  have haxX' : a x ∈ X' := by
    rw [← haX]
    exact Subgroup.mem_map_of_mem _ hxX
  have hyH : y ∈ X ⊔ X' :=
    Subgroup.mem_sup.mpr ⟨x⁻¹, X.inv_mem hxX, a x, haxX', by rw [mul_comm]⟩
  have hyHmap : y ∈ (X ⊔ X').map b.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨y, hyH, hyb⟩
  have hybot : y ∈ (⊥ : Subgroup V) := by
    rw [← hHdisj]
    exact ⟨hyH, hyHmap⟩
  have hy1 : y = 1 := by simpa using hybot
  have hax : a x = x := mul_inv_eq_one.mp (by simpa [y] using hy1)
  have hxX' : x ∈ X' := by
    rw [← hax]
    exact haxX'
  have hxbot : x ∈ X ⊓ X' := ⟨hxX, hxX'⟩
  rw [hdisj] at hxbot
  exact hx1 (by simpa using hxbot)
private theorem b_eq_a_of_map_mul_eq {V : Type} [CommGroup V] [Finite V]
    {L A : Subgroup (MulAut V)} (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hA : IsElemAbelian2 A) (hquad : IsQuadratic A)
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) (⊥ : Subgroup V) ⊤)
    {X : Subgroup V} (hX : IsMinInv L X) (hXtop : X ≠ ⊤) {a b : MulAut V}
    (ha : a ∈ A) (hb : b ∈ A) (h : X.map (a * b).toMonoidHom = X) : b = a := by
  have ha2 : a * a = 1 := by simpa [pow_two] using hA.2 a ha
  have hab1 : a * b = 1 :=
    map_eq_self_imp_eq_one hAL hA hquad hirr hX hXtop (A.mul_mem ha hb) h
  calc b = (a * a) * b := by rw [ha2, one_mul]
    _ = a * (a * b) := by group
    _ = a := by rw [hab1, mul_one]

private theorem b_eq_a_of_map_eq_map {V : Type} [CommGroup V] [Finite V]
    {L A : Subgroup (MulAut V)} (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hA : IsElemAbelian2 A) (hquad : IsQuadratic A)
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) (⊥ : Subgroup V) ⊤)
    {X : Subgroup V} (hX : IsMinInv L X) (hXtop : X ≠ ⊤) {a b : MulAut V}
    (ha : a ∈ A) (hb : b ∈ A) (h : X.map a.toMonoidHom = X.map b.toMonoidHom) :
    b = a := by
  apply b_eq_a_of_map_mul_eq hAL hA hquad hirr hX hXtop ha hb
  have ha2 : a * a = 1 := by simpa [pow_two] using hA.2 a ha
  have h2 := congrArg (fun T : Subgroup V => T.map a.toMonoidHom) h
  rw [map_map_self ha2, Subgroup.map_map] at h2
  rw [show a.toMonoidHom.comp b.toMonoidHom = (a * b).toMonoidHom by
    ext x; rfl] at h2
  exact h2.symm

private theorem b_eq_one_of_map_a_eq_map_mul {V : Type} [CommGroup V] [Finite V]
    {L A : Subgroup (MulAut V)} (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hA : IsElemAbelian2 A) (hquad : IsQuadratic A)
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) (⊥ : Subgroup V) ⊤)
    {X : Subgroup V} (hX : IsMinInv L X) (hXtop : X ≠ ⊤) {a b : MulAut V}
    (ha : a ∈ A) (hb : b ∈ A) (h : X.map a.toMonoidHom = X.map (a * b).toMonoidHom) :
    b = 1 := by
  apply map_eq_self_imp_eq_one hAL hA hquad hirr hX hXtop hb
  have ha2 : a * a = 1 := by simpa [pow_two] using hA.2 a ha
  have h2 := congrArg (fun T : Subgroup V => T.map a.toMonoidHom) h
  rw [map_map_self ha2, Subgroup.map_map] at h2
  rw [show a.toMonoidHom.comp (a * b).toMonoidHom = b.toMonoidHom by
    ext x
    show a (a (b x)) = b x
    rw [← MulAut.mul_apply, ha2, MulAut.one_apply]] at h2
  exact h2.symm

private theorem b_eq_one_or_eq_a_of_cases {V : Type} [CommGroup V] [Finite V]
    {L A : Subgroup (MulAut V)} (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hA : IsElemAbelian2 A) (hquad : IsQuadratic A)
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) (⊥ : Subgroup V) ⊤)
    {X : Subgroup V} (hX : IsMinInv L X) (hXtop : X ≠ ⊤) {a b : MulAut V}
    (ha : a ∈ A) (hb : b ∈ A) {Δ : Subgroup V}
    (hXcase : Δ = X ∨ Δ = X.map a.toMonoidHom)
    (hXbcase : Δ = X.map b.toMonoidHom ∨ Δ = (X.map b.toMonoidHom).map a.toMonoidHom) :
    b = 1 ∨ b = a := by
  rcases hXcase with hΔX | hΔX'
  · rcases hXbcase with hΔXb | hΔXb'
    · left
      apply map_eq_self_imp_eq_one hAL hA hquad hirr hX hXtop hb
      rw [← hΔXb, hΔX]
    · right
      apply b_eq_a_of_map_mul_eq hAL hA hquad hirr hX hXtop ha hb
      have h1 : (X.map b.toMonoidHom).map a.toMonoidHom = X.map (a * b).toMonoidHom := by
        rw [Subgroup.map_map]
        rfl
      rw [← h1, ← hΔXb', hΔX]
  · rcases hXbcase with hΔXb | hΔXb'
    · right
      apply b_eq_a_of_map_eq_map hAL hA hquad hirr hX hXtop ha hb
      rw [← hΔX', hΔXb]
    · left
      apply b_eq_one_of_map_a_eq_map_mul hAL hA hquad hirr hX hXtop ha hb
      have h1 : (X.map b.toMonoidHom).map a.toMonoidHom = X.map (a * b).toMonoidHom := by
        rw [Subgroup.map_map]
        rfl
      rw [← h1, ← hΔX', hΔXb']

private theorem b_eq_one_or_eq_a_of_inf_ne_bot {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {L A : Subgroup (MulAut V)}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hA : IsElemAbelian2 A) (hquad : IsQuadratic A)
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) (⊥ : Subgroup V) ⊤)
    {X : Subgroup V} (hX : IsMinInv L X)
    (hXmin : ∀ Γ : Subgroup V, IsMinInv L Γ → Nat.card X ≤ Nat.card Γ)
    (hXtop : X ≠ ⊤) {a b : MulAut V} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A)
    (hHne : (X ⊔ X.map a.toMonoidHom) ⊓ ((X ⊔ X.map a.toMonoidHom).map b.toMonoidHom) ≠ ⊥) :
    b = 1 ∨ b = a := by
  have haN : a ∈ Subgroup.normalizer (L : Set (MulAut V)) := hAL ha
  have hbN : b ∈ Subgroup.normalizer (L : Set (MulAut V)) := hAL hb
  have hX' : IsMinInv L (X.map a.toMonoidHom) := IsMinInv.map (a := a) hX haN
  have hXane : X.map a.toMonoidHom ≠ X := fun h =>
    ha1 (map_eq_self_imp_eq_one hAL hA hquad hirr hX hXtop ha h)
  have hdisj : X ⊓ X.map a.toMonoidHom = ⊥ :=
    hX.inf_eq_bot_of_ne hX' (Ne.symm hXane)
  have hno : ∀ Γ : Subgroup V, IsMinInv L Γ → Γ.map a.toMonoidHom ≠ Γ := fun Γ hΓ hfix =>
    ha1 (map_eq_self_imp_eq_one hAL hA hquad hirr hΓ
      (hX.ne_top_of_ne hXtop hΓ) ha hfix)
  let H : Subgroup V := X ⊔ X.map a.toMonoidHom
  let Xb : Subgroup V := X.map b.toMonoidHom
  have hXb : IsMinInv L Xb := IsMinInv.map (a := b) hX hbN
  have hXbmin : ∀ Γ : Subgroup V, IsMinInv L Γ → Nat.card Xb ≤ Nat.card Γ := fun Γ hΓ => by
    rw [show Nat.card Xb = Nat.card X from Subgroup.card_map_of_injective b.injective]
    exact hXmin Γ hΓ
  have hab : b * a = a * b := hA.1 b hb a ha
  have hHb : H.map b.toMonoidHom = Xb ⊔ Xb.map a.toMonoidHom := by
    exact sup_map_eq X (X.map a.toMonoidHom) hab rfl
  have hXbne : Xb ≠ Xb.map a.toMonoidHom := fun h => ha1 (map_eq_self_imp_eq_one hAL hA
    hquad hirr hXb (hX.ne_top_of_ne hXtop hXb) ha h.symm)
  have hXbdisj : Xb ⊓ Xb.map a.toMonoidHom = ⊥ :=
    hXb.inf_eq_bot_of_ne (IsMinInv.map (a := a) hXb haN) hXbne
  have hHinv : XMod.IsInv ↥L H := hX.2.1.sup hX'.2.1
  have hHbinv : XMod.IsInv ↥L (H.map b.toMonoidHom) := isInv_map_of_normalizer hHinv hbN
  obtain ⟨Δ, hΔ, hΔle⟩ := exists_isMinInv hHne (hHinv.inf hHbinv)
  have hΔH : Δ ≤ H := le_trans hΔle inf_le_left
  have hΔHb : Δ ≤ H.map b.toMonoidHom := le_trans hΔle inf_le_right
  rw [hHb] at hΔHb
  let bcase := b_eq_one_or_eq_a_of_cases (Δ := Δ) hAL hA hquad hirr hX hXtop ha hb
  rcases isMinInv_le_sup_eq hV hX hX' hXmin hdisj haN (hA.2 a ha) rfl hno Δ hΔ hΔH with
    hΔX | hΔX'
  · rcases isMinInv_le_sup_eq hV hXb (IsMinInv.map (a := a) hXb haN) hXbmin hXbdisj haN
      (by simpa [pow_two] using hA.2 a ha) rfl hno Δ hΔ hΔHb with hΔXb | hΔXb'
    · exact bcase (Or.inl hΔX) (Or.inl (by simpa [Xb] using hΔXb))
    · exact bcase (Or.inl hΔX) (Or.inr (by simpa [Xb] using hΔXb'))
  · rcases isMinInv_le_sup_eq hV hXb (IsMinInv.map (a := a) hXb haN) hXbmin hXbdisj haN
      (by simpa [pow_two] using hA.2 a ha) rfl hno Δ hΔ hΔHb with hΔXb | hΔXb'
    · exact bcase (Or.inr hΔX') (Or.inl (by simpa [Xb] using hΔXb))
    · exact bcase (Or.inr hΔX') (Or.inr (by simpa [Xb] using hΔXb'))
private theorem A_eq_pair {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {L A : Subgroup (MulAut V)}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hA : IsElemAbelian2 A) (hquad : IsQuadratic A)
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) (⊥ : Subgroup V) ⊤)
    {X : Subgroup V} (hX : IsMinInv L X)
    (hXmin : ∀ Γ : Subgroup V, IsMinInv L Γ → Nat.card X ≤ Nat.card Γ)
    (hXtop : X ≠ ⊤) {a : MulAut V} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ∀ b : MulAut V, b ∈ A → b = 1 ∨ b = a := by
  have haN : a ∈ Subgroup.normalizer (L : Set (MulAut V)) := hAL ha
  have hX' : IsMinInv L (X.map a.toMonoidHom) := IsMinInv.map (a := a) hX haN
  have hXane : X.map a.toMonoidHom ≠ X := fun h =>
    ha1 (map_eq_self_imp_eq_one hAL hA hquad hirr hX hXtop ha h)
  have hdisj : X ⊓ X.map a.toMonoidHom = ⊥ := hX.inf_eq_bot_of_ne hX' (Ne.symm hXane)
  intro b hb
  by_cases hHdisj : (X ⊔ X.map a.toMonoidHom) ⊓
      ((X ⊔ X.map a.toMonoidHom).map b.toMonoidHom) = ⊥
  · exact absurd (inf_map_eq_bot_false hA hquad hX hdisj ha hb rfl ha1 hHdisj) (not_false)
  · exact b_eq_one_or_eq_a_of_inf_ne_bot hV hAL hA hquad hirr hX hXmin hXtop ha ha1 hb hHdisj

private theorem sup_map_eq_top {V : Type} [CommGroup V] [Finite V]
    {L A : Subgroup (MulAut V)} (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (_hA : IsElemAbelian2 A)
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) (⊥ : Subgroup V) ⊤)
    {X : Subgroup V} (hX : IsMinInv L X) {a : MulAut V} (ha : a ∈ A)
    (ha2 : a * a = 1) (hAeq : ∀ b : MulAut V, b ∈ A → b = 1 ∨ b = a) :
    X ⊔ X.map a.toMonoidHom = ⊤ := by
  have haN : a ∈ Subgroup.normalizer (L : Set (MulAut V)) := hAL ha
  have hX' : IsMinInv L (X.map a.toMonoidHom) := IsMinInv.map (a := a) hX haN
  let H : Subgroup V := X ⊔ X.map a.toMonoidHom
  have hHinvL : XMod.IsInv ↥L H := hX.2.1.sup hX'.2.1
  have hHmapa : H.map a.toMonoidHom = H := by
    change H.map a.toMonoidHom = X ⊔ X.map a.toMonoidHom
    rw [sup_map_eq X (X.map a.toMonoidHom) (by rw [ha2]) rfl, map_map_self ha2, sup_comm]
  have hHinvA : XMod.IsInv ↥A H := by
    intro b y hy
    rcases hAeq b b.2 with hb1 | hba
    · change (b : MulAut V) y ∈ H
      rw [hb1]
      simpa using hy
    · change (b : MulAut V) y ∈ H
      rw [hba]
      have hy' : a y ∈ H.map a.toMonoidHom := Subgroup.mem_map_of_mem _ hy
      rwa [hHmapa] at hy'
  have hHinv : XMod.IsInv ↥(L ⊔ A) H := isInv_sup_of_isInv hHinvL hHinvA
  have hHne : H ≠ ⊥ := by
    intro h
    exact hX.1 (le_antisymm (fun x hx => by
      have hxH : x ∈ H := Subgroup.mem_sup_left hx
      rw [h] at hxH
      exact hxH) bot_le)
  rcases hirr.2 H hHinv bot_le le_top with h | h
  · exact absurd h hHne
  · exact h
private theorem card_X_eq_two {V : Type} [CommGroup V] [Finite V]
    {L A : Subgroup (MulAut V)} (_hA : IsElemAbelian2 A)
    {X X' : Subgroup V} (hX : IsMinInv L X) (hdisj : X ⊓ X' = ⊥)
    (hHtop : X ⊔ X' = ⊤) {a : MulAut V} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hX'a : X' = X.map a.toMonoidHom)
    (hAeq : ∀ b : MulAut V, b ∈ A → b = 1 ∨ b = a)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card ↥(fixV A)) : Nat.card X = 2 := by
  have hAcard : Nat.card A = 2 := by
    rw [Nat.card_eq_two_iff' (1 : ↥A)]
    refine ⟨⟨a, ha⟩, ?_, ?_⟩
    · intro h
      exact ha1 (congrArg Subtype.val h)
    · intro y hy
      apply Subtype.ext
      rcases hAeq y y.2 with h | h
      · exact absurd (Subtype.ext h) hy
      · exact h
  have hcardV : Nat.card V = Nat.card X * Nat.card X := by
    have h := card_sup_of_inf_eq_bot X X' hdisj
    rw [hHtop, hX'a, Subgroup.card_map_of_injective a.injective] at h
    simpa using h
  have hCdisj : fixV A ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxC, hxX⟩
    have hax : a x = x := hxC a ha
    have hax' : a x ∈ X.map a.toMonoidHom := Subgroup.mem_map_of_mem _ hxX
    have hxX' : x ∈ X.map a.toMonoidHom := by rwa [hax] at hax'
    have hxbot : x ∈ X ⊓ X.map a.toMonoidHom := ⟨hxX, hxX'⟩
    rw [← hX'a, hdisj] at hxbot
    simpa using hxbot
  have hC_le : Nat.card ↥(fixV A) * Nat.card X ≤ Nat.card V := by
    have h := card_sup_of_inf_eq_bot (fixV A) X hCdisj
    rw [← h]
    exact Nat.card_le_card_of_injective (fun x : ↥((fixV A) ⊔ X) => (x : V))
      Subtype.val_injective
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hC_le_X : Nat.card ↥(fixV A) ≤ Nat.card X := by
    have h := hC_le
    rw [hcardV] at h
    exact Nat.le_of_mul_le_mul_right h hXpos
  have hX_le_two : Nat.card X ≤ 2 := by
    have h := hoff
    rw [hcardV, hAcard] at h
    have h2 : 2 * Nat.card ↥(fixV A) ≤ 2 * Nat.card X :=
      Nat.mul_le_mul_left 2 hC_le_X
    exact Nat.le_of_mul_le_mul_right (le_trans h h2) hXpos
  have hXne : Nat.card X ≠ 1 := by
    intro h
    exact hX.1 (Subgroup.eq_bot_of_card_eq X h)
  omega
private theorem card_two_point_data {V : Type} [CommGroup V] [Finite V]
    {L A : Subgroup (MulAut V)} (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    {X X' : Subgroup V} (hX : IsMinInv L X) (_hdisj : X ⊓ X' = ⊥)
    {a : MulAut V} (ha : a ∈ A) (_ha1 : a ≠ 1) (haX : X.map a.toMonoidHom = X')
    (hcardX : Nat.card X = 2) :
    ∃ x : ↥X, (x : V) ≠ 1 ∧
      (∀ l ∈ L, ∀ z ∈ X, (l : MulAut V) z = z) ∧
      (∀ l ∈ L, ∀ y ∈ X', (l : MulAut V) y = y) ∧
      (∀ l ∈ L, (l : MulAut V) (x : V) * (l : MulAut V) (a (x : V)) =
        (x : V) * a (x : V)) := by
  obtain ⟨x, hxne, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥X)).mp hcardX
  have hxneV : (x : V) ≠ 1 := fun h => hxne (Subtype.ext h)
  have hLfixX : ∀ l ∈ L, (l : MulAut V) (x : V) = (x : V) := by
    intro l hl
    have hlx : (⟨(l : MulAut V) (x : V), hX.2.1 ⟨l, hl⟩ x x.2⟩ : ↥X) ≠ 1 := by
      intro h
      apply hxneV
      have := congrArg Subtype.val h
      exact (l : MulAut V).injective (by simpa [map_one] using this)
    have := huniq ⟨(l : MulAut V) (x : V), hX.2.1 ⟨l, hl⟩ x x.2⟩ hlx
    exact congrArg Subtype.val this
  have hLfixXall : ∀ l ∈ L, ∀ z ∈ X, (l : MulAut V) z = z := by
    intro l hl z hz
    by_cases hz1 : z = 1
    · rw [hz1]; simp
    · have hzsub : (⟨z, hz⟩ : ↥X) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
      have := huniq ⟨z, hz⟩ hzsub
      have hzx : z = (x : V) := congrArg Subtype.val this
      rw [hzx]
      exact hLfixX l hl
  have hLfixX' : ∀ l ∈ L, ∀ y ∈ X', (l : MulAut V) y = y := by
    intro l hl y hy
    rw [← haX] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have hconj : a⁻¹ * (l : MulAut V) * a ∈ L :=
      (Subgroup.mem_normalizer_iff''.mp (hAL ha) l).mp hl
    calc (l : MulAut V) (a z) = a ((a⁻¹ * (l : MulAut V) * a) z) := by
          simp [MulAut.mul_apply]
      _ = a z := by rw [hLfixXall _ hconj z hz]
  have hLfixw : ∀ l ∈ L, (l : MulAut V) (x : V) * (l : MulAut V) (a (x : V)) =
      (x : V) * a (x : V) := by
    intro l hl
    rw [hLfixX l hl]
    have haxX' : a (x : V) ∈ X' := by
      rw [← haX]
      exact Subgroup.mem_map_of_mem _ x.2
    rw [hLfixX' l hl (a (x : V)) haxX']
  exact ⟨x, hxneV, hLfixXall, hLfixX', hLfixw⟩

private theorem word_data_of_card_two {V : Type} [CommGroup V]
    (hV : ∀ v : V, v ^ 2 = 1) {X X' : Subgroup V} (hdisj : X ⊓ X' = ⊥)
    {a : MulAut V} (haX : X.map a.toMonoidHom = X') {x : ↥X} (hxneV : (x : V) ≠ 1) :
    ∃ w : V, w = (x : V) * a (x : V) ∧ w ^ 2 = 1 ∧ w ≠ 1 ∧ orderOf w = 2 := by
  let w : V := x * a (x : V)
  have hw2 : w ^ 2 = 1 := hV w
  have hwne : w ≠ 1 := by
    intro hw1
    have hax : a (x : V) = (x : V) := by
      have hw1' : a (x : V) * (x : V) = 1 := by simpa [w, mul_comm] using hw1
      have h2 : a (x : V) = (x : V)⁻¹ := mul_eq_one_iff_eq_inv.mp hw1'
      have hinv : (x : V)⁻¹ = (x : V) := by
        rw [inv_eq_iff_mul_eq_one]
        simpa [pow_two] using hV (x : V)
      rwa [hinv] at h2
    have haxX' : a (x : V) ∈ X' := by
      rw [← haX]
      exact Subgroup.mem_map_of_mem _ x.2
    have hxX' : (x : V) ∈ X' := by simpa [hax] using haxX'
    have hxbot : (x : V) ∈ X ⊓ X' := ⟨x.2, hxX'⟩
    rw [hdisj] at hxbot
    exact hxneV (by simpa using hxbot)
  have horder : orderOf w = 2 := by
    have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hw2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hwne
    · exact h
  exact ⟨w, rfl, hw2, hwne, horder⟩

private theorem D_min_of_card_two {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {X X' : Subgroup V} (_hX : IsMinInv L X)
    {a : MulAut V} (haX : X.map a.toMonoidHom = X') {x : ↥X}
    (hLfixw : ∀ l ∈ L, (l : MulAut V) (x : V) * (l : MulAut V) (a (x : V)) =
      (x : V) * a (x : V)) {w : V} (hwdef : w = (x : V) * a (x : V))
    (_hw2 : w ^ 2 = 1) (_hwne : w ≠ 1)
    (horder : orderOf w = 2) :
    ∃ D : Subgroup V, D = Subgroup.zpowers w ∧ IsMinInv L D ∧ D ≤ X ⊔ X' := by
  let D : Subgroup V := Subgroup.zpowers w
  have hDcard : Nat.card D = 2 := by
    change Nat.card (Subgroup.zpowers w) = 2
    rw [Nat.card_zpowers, horder]
  have hDinv : XMod.IsInv ↥L D := by
    intro l y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hlw : (l : MulAut V) w = w := by
      simpa [hwdef, map_mul] using hLfixw l.1 l.2
    change (l : MulAut V) (w ^ n) ∈ D
    have hlpow : (l : MulAut V) (w ^ n) = w ^ n := by
      simp [hlw]
    rw [hlpow]
    exact Subgroup.zpow_mem_zpowers w n
  have hDmin : IsMinInv L D := by
    refine ⟨?_, hDinv, ?_⟩
    · intro h
      have : Nat.card D = 1 := by rw [h]; simp
      omega
    · intro U hUne hUinv hUle
      obtain ⟨u, hu, hu1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hUne)
      have hnt : Nontrivial ↥U :=
        ⟨⟨⟨u, hu⟩, ⟨1, U.one_mem⟩, fun h => hu1 (by simpa using congrArg Subtype.val h)⟩⟩
      have h1 : 1 < Nat.card U := Finite.one_lt_card
      have h2 : Nat.card U ≤ Nat.card D := Subgroup.card_le_of_le hUle
      exact Subgroup.eq_of_le_of_card_ge hUle (by omega)
  have hwH : w ∈ X ⊔ X' := by
    have haxX' : a (x : V) ∈ X' := by
      rw [← haX]
      exact Subgroup.mem_map_of_mem _ x.2
    exact Subgroup.mem_sup.mpr ⟨x, x.2, a (x : V), haxX', hwdef.symm⟩
  exact ⟨D, rfl, hDmin, Subgroup.zpowers_le.mpr hwH⟩

private theorem D_ne_X_of_card_two {V : Type} [CommGroup V]
    {X X' : Subgroup V} (hdisj : X ⊓ X' = ⊥) {a : MulAut V}
    (haX : X.map a.toMonoidHom = X') {x : ↥X} (hxneV : (x : V) ≠ 1)
    {D : Subgroup V} {w : V} (hwD : w ∈ D) (hwdef : w = (x : V) * a (x : V)) : D ≠ X := by
  intro h
  have hwX : w ∈ X := by rw [← h]; exact hwD
  have haxX : a (x : V) ∈ X := by
    have : a (x : V) = (x : V)⁻¹ * w := by rw [hwdef]; group
    rw [this]
    exact X.mul_mem (X.inv_mem x.2) hwX
  have haxX' : a (x : V) ∈ X' := by
    rw [← haX]
    exact Subgroup.mem_map_of_mem _ x.2
  have hbot : a (x : V) ∈ X ⊓ X' := ⟨haxX, haxX'⟩
  rw [hdisj] at hbot
  have h1 : a (x : V) = 1 := by simpa using hbot
  exact hxneV (a.injective (by rw [h1, map_one]))

private theorem D_ne_X'_of_card_two {V : Type} [CommGroup V]
    {X X' : Subgroup V} (hdisj : X ⊓ X' = ⊥) {a : MulAut V}
    (haX : X.map a.toMonoidHom = X') {x : ↥X} (hxneV : (x : V) ≠ 1)
    {D : Subgroup V} {w : V} (hwD : w ∈ D) (hwdef : w = (x : V) * a (x : V)) : D ≠ X' := by
  intro h
  have hwX' : w ∈ X' := by rw [← h]; exact hwD
  have haxX' : a (x : V) ∈ X' := by
    rw [← haX]
    exact Subgroup.mem_map_of_mem _ x.2
  have hxX' : (x : V) ∈ X' := by
    have : (x : V) = w * (a (x : V))⁻¹ := by rw [hwdef]; group
    rw [this]
    exact X'.mul_mem hwX' (X'.inv_mem haxX')
  have hbot : (x : V) ∈ X ⊓ X' := ⟨x.2, hxX'⟩
  rw [hdisj] at hbot
  exact hxneV (by simpa using hbot)

private theorem false_of_card_X_two {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {L A : Subgroup (MulAut V)}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (_hirr : XMod.IsIrrSec ↥(L ⊔ A) (⊥ : Subgroup V) ⊤)
    {X X' : Subgroup V} (hX : IsMinInv L X) (hX' : IsMinInv L X')
    (hdisj : X ⊓ X' = ⊥) {a : MulAut V} (ha : a ∈ A) (ha1 : a ≠ 1)
    (ha2 : a * a = 1) (haX : X.map a.toMonoidHom = X')
    (hXmin : ∀ Γ : Subgroup V, IsMinInv L Γ → Nat.card X ≤ Nat.card Γ)
    (hno : ∀ Γ : Subgroup V, IsMinInv L Γ → Γ.map a.toMonoidHom ≠ Γ)
    (_hHtop : X ⊔ X' = ⊤) (hcardX : Nat.card X = 2) : False := by
  obtain ⟨x, hxneV, hLfixXall, hLfixX', hLfixw⟩ :=
    card_two_point_data hAL hX hdisj ha ha1 haX hcardX
  obtain ⟨w, hwdef, hw2, hwne, horder⟩ := word_data_of_card_two hV hdisj haX hxneV
  obtain ⟨D, hDdef, hDmin, hDH⟩ := D_min_of_card_two hX haX hLfixw hwdef hw2 hwne horder
  have hwD : w ∈ D := by rw [hDdef]; exact Subgroup.mem_zpowers w
  have hDneX : D ≠ X := D_ne_X_of_card_two hdisj haX hxneV hwD hwdef
  have hDneX' : D ≠ X' := D_ne_X'_of_card_two hdisj haX hxneV hwD hwdef
  rcases isMinInv_le_sup_eq hV hX hX' hXmin hdisj (hAL ha) ha2 haX hno D hDmin hDH with h | h
  · exact hDneX h
  · exact hDneX' h

private theorem exists_minInv_of_not_irr {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} (hlt : (⊥ : Subgroup V) < ⊤)
    (hnot : ¬ XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) :
    ∃ X : Subgroup V, IsMinInv L X ∧ X ≠ ⊤ ∧
      ∀ Γ : Subgroup V, IsMinInv L Γ → Nat.card X ≤ Nat.card Γ := by
  have hnotmin : ¬ ∀ J : Subgroup V, XMod.IsInv ↥L J → J = ⊥ ∨ J = ⊤ := by
    intro hall
    exact hnot ⟨hlt, fun J hJ _ _ => hall J hJ⟩
  push Not at hnotmin
  obtain ⟨J, hJinv, hJnebot, hJnetop⟩ := hnotmin
  obtain ⟨X, hX, hXJ⟩ := exists_isMinInv hJnebot hJinv
  have hXtop : X ≠ ⊤ := by
    intro h
    exact hJnetop (le_antisymm le_top (h ▸ hXJ))
  obtain ⟨Y, hY, hYmin⟩ := exists_min_card_isMinInv (L := L) ⟨X, hX⟩
  exact ⟨Y, hY, hX.ne_top_of_ne hXtop hY, hYmin⟩

private theorem isIrrSec_of_isIrrSec_sup_abstract {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {L A : Subgroup (MulAut V)}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hA : IsElemAbelian2 A) (hquad : IsQuadratic A)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card ↥(fixV A))
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) (⊥ : Subgroup V) ⊤) :
    XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤ := by
  classical
  by_contra hcon
  obtain ⟨X, hX, hXtop, hXmin⟩ := exists_minInv_of_not_irr (L := L) hirr.1 hcon
  by_cases hAbot : A = ⊥
  · apply hcon
    have hL : L ⊔ A = L := by rw [hAbot, sup_bot_eq]
    rw [hL] at hirr
    exact hirr
  · obtain ⟨a, ha, ha1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hAbot)
    have ha1' : a ≠ 1 := fun h => ha1 (by simp [h])
    have ha2 : a * a = 1 := by simpa [pow_two] using hA.2 a ha
    have hXa : IsMinInv L (X.map a.toMonoidHom) := IsMinInv.map (a := a) hX (hAL ha)
    have hXane : X.map a.toMonoidHom ≠ X := by
      intro h
      exact ha1 (map_eq_self_imp_eq_one hAL hA hquad hirr hX hXtop ha h)
    have hdisj : X ⊓ X.map a.toMonoidHom = ⊥ :=
      hX.inf_eq_bot_of_ne hXa (Ne.symm hXane)
    have hno : ∀ Γ : Subgroup V, IsMinInv L Γ → Γ.map a.toMonoidHom ≠ Γ := by
      intro Γ hΓ hfix
      exact ha1' (map_eq_self_imp_eq_one hAL hA hquad hirr hΓ
        (hX.ne_top_of_ne hXtop hΓ) ha hfix)
    have hAeq := A_eq_pair hV hAL hA hquad hirr hX hXmin hXtop ha ha1'
    have hHtop := sup_map_eq_top hAL hA hirr hX ha ha2 hAeq
    have hcard := card_X_eq_two hA hX hdisj hHtop ha ha1' rfl hAeq hoff
    exact false_of_card_X_two hV hAL hirr hX hXa hdisj ha ha1' ha2 rfl hXmin hno hHtop hcard

private theorem I_le_of_map_subgroupOf_eq_top {V : Type} [CommGroup V]
    {I Z J : Subgroup V} (hZJ : Z ≤ J) (_hJI : J ≤ I)
    (htop : (J.subgroupOf I).map (QuotientGroup.mk' (Z.subgroupOf I)) = ⊤) : I ≤ J := by
  intro i hi
  have hmem : QuotientGroup.mk' (Z.subgroupOf I) ⟨i, hi⟩ ∈
      (J.subgroupOf I).map (QuotientGroup.mk' (Z.subgroupOf I)) := by
    rw [htop]
    trivial
  obtain ⟨j, hjJ, hji⟩ := Subgroup.mem_map.mp hmem
  have hz : (j : V)⁻¹ * i ∈ Z := by
    have hz' : QuotientGroup.mk' (Z.subgroupOf I) ((j : ↥I)⁻¹ * ⟨i, hi⟩) = 1 := by
      rw [map_mul, map_inv, hji]
      simp
    have hz'' : QuotientGroup.mk' (Z.subgroupOf I) ((j : ↥I)⁻¹ * ⟨i, hi⟩) = 1 := by
      rw [map_mul, map_inv]
      exact hz'
    change (QuotientGroup.mk ((j : ↥I)⁻¹ * ⟨i, hi⟩) : Sec I Z) = 1 at hz''
    have := (QuotientGroup.eq_one_iff ((j : ↥I)⁻¹ * ⟨i, hi⟩)).mp hz''
    exact Subgroup.mem_subgroupOf.mp this
  have hji' : (j : V)⁻¹ * i ∈ J := hZJ hz
  have : i = (j : V) * ((j : V)⁻¹ * i) := by group
  rw [this]
  exact J.mul_mem (Subgroup.mem_subgroupOf.mp hjJ) hji'

private theorem isIrrSec_of_isIrrSec_autSec {V : Type} [CommGroup V]
    {L : Subgroup (MulAut V)} {I Z : Subgroup V} (hZI : Z ≤ I)
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (h : XMod.IsIrrSec ↥(autSec L I Z) (⊥ : Subgroup (Sec I Z)) ⊤) :
    XMod.IsIrrSec ↥L Z I := by
  have hlt : Z < I := by
    refine lt_of_le_of_ne hZI ?_
    intro hZI'
    apply h.1.ne
    apply le_antisymm le_top
    intro v
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf I) v
    have : (w : ↥I) ∈ Z.subgroupOf I := by
      rw [Subgroup.mem_subgroupOf, hZI']
      exact w.2
    simpa using (QuotientGroup.eq_one_iff w).mpr this
  refine ⟨hlt, fun J hJinv hZJ hJI => ?_⟩
  let π : ↥I →* Sec I Z := QuotientGroup.mk' (Z.subgroupOf I)
  let J' : Subgroup (Sec I Z) := (J.subgroupOf I).map π
  have hJ'inv : XMod.IsInv ↥(autSec L I Z) J' := by
    intro φ j' hj'
    obtain ⟨j, hjJ, rfl⟩ := Subgroup.mem_map.mp hj'
    have hmemrange : (φ : MulAut (Sec I Z)) ∈ (B5.secHom L hLI hLZ).range := by
      rw [B5.range_secHom L hLI hLZ]
      exact φ.2
    obtain ⟨l, hl⟩ := hmemrange
    refine Subgroup.mem_map.mpr ⟨⟨(l : MulAut V) (j : V), (hLI l.2 (j:V)).2 j.2⟩, ?_, ?_⟩
    · exact hJinv l (j : V) hjJ
    · symm
      change (φ : MulAut (Sec I Z)) (QuotientGroup.mk j) =
        QuotientGroup.mk ⟨(l : MulAut V) (j : V), (hLI l.2 (j:V)).2 j.2⟩
      rw [← hl]
      exact B5.secHom_mk L hLI hLZ l j
  rcases h.2 J' hJ'inv bot_le le_top with hbot | htop
  · left
    refine le_antisymm ?_ hZJ
    intro j hj
    have hzero : π ⟨j, hJI hj⟩ ∈ (⊥ : Subgroup (Sec I Z)) := by
      rw [← hbot]
      exact Subgroup.mem_map.mpr ⟨⟨j, hJI hj⟩, hj, rfl⟩
    have hzero1 : π ⟨j, hJI hj⟩ = 1 := by simpa using hzero
    have : (⟨j, hJI hj⟩ : ↥I) ∈ Z.subgroupOf I :=
      (QuotientGroup.eq_one_iff (⟨j, hJI hj⟩ : ↥I)).mp hzero1
    exact Subgroup.mem_subgroupOf.mp this
  · right
    refine le_antisymm hJI ?_
    exact I_le_of_map_subgroupOf_eq_top hZJ hJI htop

theorem isIrrSec_of_isIrrSec_sup [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L A : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hA : IsElemAbelian2 (autSec A I Z)) (hquad : IsQuadratic (autSec A I Z))
    (hoff : Nat.card (Sec I Z) ≤ Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)))
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) Z I) : XMod.IsIrrSec ↥L Z I := by
  classical
  have hVsec : ∀ v : Sec I Z, v ^ 2 = 1 := by
    intro v
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf I) v
    rw [← map_pow]
    rw [show (w : ↥I) ^ 2 = 1 from Subtype.ext (by simpa using hW (w : W)), map_one]
  have hLI' : L ⊔ A ≤ stabSub I := sup_le hLI hAI
  have hLZ' : L ⊔ A ≤ stabSub Z := sup_le hLZ hAZ
  have hirrA : XMod.IsIrrSec ↥(autSec (L ⊔ A) I Z) (⊥ : Subgroup (Sec I Z)) ⊤ :=
    B5.isIrrSec_autSec hirr.1
      (fun J hJ hZJ hJI => hirr.2 J (fun a w hw => by
        rw [Subgroup.smul_def, MulAut.smul_def]
        exact hJ a a.2 w hw) hZJ hJI) hLI' hLZ'
  have hsup : autSec (L ⊔ A) I Z = autSec L I Z ⊔ autSec A I Z :=
    B69.autSec_sup_eq hLI' hLZ'
  have hirrAbs : XMod.IsIrrSec ↥(autSec L I Z ⊔ autSec A I Z)
      (⊥ : Subgroup (Sec I Z)) ⊤ := by
    rw [← hsup]
    exact hirrA
  have hALabs : autSec A I Z ≤
      Subgroup.normalizer (autSec L I Z : Set (MulAut (Sec I Z))) := by
    have hN : autSec (L ⊔ A) I Z ≤
        Subgroup.normalizer (autSec L I Z : Set (MulAut (Sec I Z))) := by
      intro ψ hψ
      rw [Subgroup.mem_normalizer_iff]
      intro φ
      constructor
      · intro hφ
        exact B69.autSec_sup_conj hAL hLI' hLZ' hψ hφ
      · intro hφ
        have hψinv : ((ψ : MulAut (Sec I Z))⁻¹) ∈ autSec (L ⊔ A) I Z :=
          (autSec (L ⊔ A) I Z).inv_mem hψ
        have := B69.autSec_sup_conj hAL hLI' hLZ' hψinv hφ
        simpa [mul_assoc] using this
    rw [hsup] at hN
    exact le_trans le_sup_right hN
  have hAabs : IsElemAbelian2 (autSec A I Z) := hA
  have hqabs : IsQuadratic (autSec A I Z) := hquad
  have hLabs : XMod.IsIrrSec ↥(autSec L I Z) (⊥ : Subgroup (Sec I Z)) ⊤ :=
    isIrrSec_of_isIrrSec_sup_abstract hVsec hALabs hAabs hqabs hoff hirrAbs
  exact isIrrSec_of_isIrrSec_autSec hirr.1.le hLI hLZ hLabs

private theorem isPGroup_of_sq_one {G : Type*} [Group G] [Finite G]
    (h : ∀ g : G, g ^ 2 = 1) : IsPGroup 2 G := by
  rw [IsPGroup.iff_orderOf]
  intro g
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (h g)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact ⟨0, by rw [h1, pow_zero]⟩
  · exact ⟨1, by rw [h1, pow_one]⟩

private theorem sec_sq_one [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (I Z : Subgroup W) :
    ∀ v : Sec I Z, v ^ 2 = 1 := by
  intro v
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf I) v
  rw [← map_pow]
  rw [show (w : ↥I) ^ 2 = 1 from Subtype.ext (by simpa using hW (w : W)), map_one]

private theorem sec_isPGroup [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (I Z : Subgroup W) :
    IsPGroup 2 (Sec I Z) :=
  isPGroup_of_sq_one (sec_sq_one hW I Z)

private theorem autSec_sq_one {A : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hA : IsElemAbelian2 (autSec A I Z)) : ∀ φ : ↥(autSec A I Z), φ ^ 2 = 1 := by
  intro φ
  apply Subtype.ext
  exact hA.2 φ φ.2

private theorem autSec_isPGroup [Finite W] {A : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hA : IsElemAbelian2 (autSec A I Z)) : IsPGroup 2 ↥(autSec A I Z) :=
  isPGroup_of_sq_one (autSec_sq_one hA)

private theorem card_dvd_two_of_isPGroup {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (hnt : Nontrivial G) : 2 ∣ Nat.card G := by
  rcases hG.card_eq_or_dvd with h | h
  · exfalso
    have h1 : 1 < Nat.card G := Finite.one_lt_card
    omega
  · exact h

private theorem exists_fixed_sec [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L A : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hA : IsElemAbelian2 (autSec A I Z)) (hirr : XMod.IsIrrSec ↥(L ⊔ A) Z I) :
    ∃ w : Sec I Z, w ∈ MulAction.fixedPoints ↥(autSec A I Z) (Sec I Z) ∧ w ≠ 1 := by
  obtain ⟨w0, hw0I, hw0Z⟩ := IsConcreteLE.exists_of_lt hirr.1
  have hne : (QuotientGroup.mk (⟨w0, hw0I⟩ : ↥I) : Sec I Z) ≠ 1 := by
    intro h
    apply hw0Z
    rw [QuotientGroup.eq_one_iff] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hnt : Nontrivial (Sec I Z) := ⟨⟨_, 1, hne⟩⟩
  have htwo : 2 ∣ Nat.card (Sec I Z) :=
    card_dvd_two_of_isPGroup (sec_isPGroup hW I Z) hnt
  obtain ⟨w, hwfix, hwne⟩ :=
    IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (autSec_isPGroup hA) (α := Sec I Z) htwo (a := (1 : Sec I Z))
        (by
          rw [MulAction.mem_fixedPoints]
          intro x
          change (x : MulAut (Sec I Z)) (1 : Sec I Z) = 1
          exact map_one _)
  exact ⟨w, hwfix, fun h => hwne h.symm⟩

private theorem lift_fixed_sec {I Z : Subgroup W} {w : Sec I Z} (hwne : w ≠ 1) :
    ∃ w1 : ↥I, QuotientGroup.mk' (Z.subgroupOf I) w1 = w ∧ (w1 : W) ∉ Z := by
  obtain ⟨w1, hw1eq⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf I) w
  refine ⟨w1, hw1eq, ?_⟩
  intro hz
  apply hwne
  rw [← hw1eq]
  change (QuotientGroup.mk w1 : Sec I Z) = 1
  exact (QuotientGroup.eq_one_iff w1).2 (Subgroup.mem_subgroupOf.mpr hz)

private theorem J_L_inv {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hLZ : L ≤ stabSub Z) (hc : XMod.commOf ↥L I ≤ Z) {w1 : ↥I} (_hw1Z : (w1 : W) ∉ Z) :
    XMod.IsInv ↥L (Z ⊔ Subgroup.zpowers (w1 : W)) := by
  let J : Subgroup W := Z ⊔ Subgroup.zpowers (w1 : W)
  change XMod.IsInv ↥L J
  intro l x hx
  obtain ⟨z, hz, c, hczp, rfl⟩ := Subgroup.mem_sup.mp hx
  rw [Subgroup.smul_def, MulAut.smul_def, map_mul]
  have hmem : (l : MulAut W) (w1 : W) * (w1 : W)⁻¹ ∈ Z := by
    have := hc (Subgroup.subset_closure ⟨l, w1, w1.2, rfl⟩)
    simpa [Subgroup.smul_def, MulAut.smul_def] using this
  have hmul : (l : MulAut W) (w1 : W) ∈ J := by
    have h1 : (l : MulAut W) (w1 : W) =
        ((l : MulAut W) (w1 : W) * (w1 : W)⁻¹) * (w1 : W) := by group
    rw [h1]
    exact Subgroup.mul_mem (H := J) (Subgroup.mem_sup_left hmem)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  refine Subgroup.mul_mem (H := J) (Subgroup.mem_sup_left (((mem_stabSub.mp (hLZ l.2)) z).2 hz)) ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hczp
  rw [map_zpow]
  exact Subgroup.zpow_mem (K := J) hmul n

private theorem J_A_inv [Finite W] {A : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z) {w1 : ↥I} {w : Sec I Z}
    (hw1eq : QuotientGroup.mk' (Z.subgroupOf I) w1 = w)
    (hwfix : w ∈ MulAction.fixedPoints ↥(autSec A I Z) (Sec I Z)) :
    XMod.IsInv ↥A (Z ⊔ Subgroup.zpowers (w1 : W)) := by
  let J : Subgroup W := Z ⊔ Subgroup.zpowers (w1 : W)
  change XMod.IsInv ↥A J
  intro a x hx
  obtain ⟨z, hz, c, hczp, rfl⟩ := Subgroup.mem_sup.mp hx
  rw [Subgroup.smul_def, MulAut.smul_def, map_mul]
  have hfixa : B5.secHom A hAI hAZ a w = w := by
    have hφ : B5.secHom A hAI hAZ a ∈ autSec A I Z := by
      rw [← B5.range_secHom A hAI hAZ]
      exact ⟨a, rfl⟩
    have := MulAction.mem_fixedPoints.mp hwfix ⟨B5.secHom A hAI hAZ a, hφ⟩
    simpa [Subgroup.smul_def, MulAut.smul_def] using this
  have hsec0 : B5.secHom A hAI hAZ a (QuotientGroup.mk' (Z.subgroupOf I) w1) =
      QuotientGroup.mk' (Z.subgroupOf I) w1 := by
    rw [hw1eq]
    exact hfixa
  have hsec : (QuotientGroup.mk (⟨(a : MulAut W) (w1 : W),
        ((mem_stabSub.mp (hAI a.2)) (w1 : W)).2 w1.2⟩ : ↥I) : Sec I Z) =
      QuotientGroup.mk w1 := by
    simpa [B5.secHom_mk, QuotientGroup.mk'_apply] using hsec0
  have hmem : (a : MulAut W) (w1 : W) * (w1 : W)⁻¹ ∈ Z :=
    mul_inv_mem_of_mk_eq_mk (a := ⟨(a : MulAut W) (w1 : W),
      ((mem_stabSub.mp (hAI a.2)) (w1 : W)).2 w1.2⟩) (b := w1) hsec
  have hmul : (a : MulAut W) (w1 : W) ∈ J := by
    have h1 : (a : MulAut W) (w1 : W) =
        ((a : MulAut W) (w1 : W) * (w1 : W)⁻¹) * (w1 : W) := by group
    rw [h1]
    exact Subgroup.mul_mem (H := J) (Subgroup.mem_sup_left hmem)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  refine Subgroup.mul_mem (H := J) (Subgroup.mem_sup_left (((mem_stabSub.mp (hAZ a.2)) z).2 hz)) ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hczp
  rw [map_zpow]
  exact Subgroup.zpow_mem (K := J) hmul n

private theorem J_eq_sec [Finite W] {L A : Subgroup (MulAut W)} {I Z : Subgroup W}
    {w1 : ↥I} (hZJ : Z ≤ Z ⊔ Subgroup.zpowers (w1 : W))
    (hJI : Z ⊔ Subgroup.zpowers (w1 : W) ≤ I)
    (hJinv : XMod.IsInv ↥(L ⊔ A) (Z ⊔ Subgroup.zpowers (w1 : W)))
    (hw1Z : (w1 : W) ∉ Z) (hirr : XMod.IsIrrSec ↥(L ⊔ A) Z I) :
    Z ⊔ Subgroup.zpowers (w1 : W) = I := by
  rcases hirr.2 _ hJinv hZJ hJI with h | h
  · exfalso
    apply hw1Z
    have hw1J : (w1 : W) ∈ Z ⊔ Subgroup.zpowers (w1 : W) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rw [h] at hw1J
    exact hw1J
  · exact h

private theorem sec_dichotomy_of_J [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {I Z : Subgroup W}
    {w1 : ↥I} (hw1Z : (w1 : W) ∉ Z) (hJIeq : Z ⊔ Subgroup.zpowers (w1 : W) = I) :
    ∀ J' : Subgroup W, Z ≤ J' → J' ≤ I → J' = Z ∨ J' = I := by
  classical
  intro J' hZJ' hJ'I
  by_cases hJ'Z : J' = Z
  · exact Or.inl hJ'Z
  · right
    have hlt : Z < J' := lt_of_le_of_ne hZJ' (Ne.symm hJ'Z)
    obtain ⟨j, hjJ', hjZ⟩ := IsConcreteLE.exists_of_lt hlt
    have hjI : j ∈ I := hJ'I hjJ'
    have hjJ : j ∈ Z ⊔ Subgroup.zpowers (w1 : W) := by rw [hJIeq]; exact hjI
    obtain ⟨z, hz, c, hc, hjc⟩ := Subgroup.mem_sup.mp hjJ
    have hcJ' : c ∈ J' := by
      have : c = z⁻¹ * j := by rw [← hjc]; group
      rw [this]
      exact J'.mul_mem (J'.inv_mem (hZJ' hz)) hjJ'
    have hcZ : c ∉ Z := by
      intro hcz
      apply hjZ
      have : j = z * c := hjc.symm
      rw [this]
      exact Z.mul_mem hz hcz
    have hcw : c = (w1 : W) := by
      have hw1ne1 : (w1 : W) ≠ 1 := fun h => hw1Z (h ▸ Z.one_mem)
      rcases (mem_zpowers_iff_eq_one_or (hW (w1 : W)) hw1ne1 c).mp hc with hc1 | hcw
      · exact absurd (hc1 ▸ Z.one_mem) hcZ
      · exact hcw
    have hw1J' : (w1 : W) ∈ J' := hcw ▸ hcJ'
    have hIJ' : I ≤ J' := by
      have hle : Z ⊔ Subgroup.zpowers (w1 : W) ≤ J' :=
        sup_le hZJ' (Subgroup.zpowers_le.mpr hw1J')
      rwa [hJIeq] at hle
    exact le_antisymm hJ'I hIJ'
theorem isIrrSec_of_isIrrSec_sup_of_commOf_le [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L A : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hA : IsElemAbelian2 (autSec A I Z)) (hc : XMod.commOf ↥L I ≤ Z)
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) Z I) : XMod.IsIrrSec ↥L Z I := by
  have hZI : Z ≤ I := hirr.1.le
  have hLI' : L ⊔ A ≤ stabSub I := sup_le hLI hAI
  have hLZ' : L ⊔ A ≤ stabSub Z := sup_le hLZ hAZ
  have haut : autSec (L ⊔ A) I Z = autSec A I Z := by
    rw [B69.autSec_sup_eq hLI' hLZ', autSec_eq_bot_of_commOf_le hLI hLZ hc]
    simp
  have hirrA : XMod.IsIrrSec ↥(autSec A I Z) (⊥ : Subgroup (Sec I Z)) ⊤ := by
    rw [← haut]
    exact B5.isIrrSec_autSec hirr.1
      (fun J hJ hZJ hJI => hirr.2 J (fun a w hw => by
        rw [Subgroup.smul_def, MulAut.smul_def]
        exact hJ a a.2 w hw) hZJ hJI) hLI' hLZ'
  obtain ⟨w, hwfix, hwne⟩ := exists_fixed_sec hW hA hirr
  obtain ⟨w1, hw1eq, hw1Z⟩ := lift_fixed_sec hwne
  let J : Subgroup W := Z ⊔ Subgroup.zpowers (w1 : W)
  have hZJ : Z ≤ J := le_sup_left
  have hJI : J ≤ I := sup_le hZI (Subgroup.zpowers_le.mpr w1.2)
  have hLJ : XMod.IsInv ↥L J := J_L_inv hLZ hc hw1Z
  have hAJ : XMod.IsInv ↥A J := J_A_inv hAI hAZ hw1eq hwfix
  have hJinv : XMod.IsInv ↥(L ⊔ A) J := isInv_sup_of_isInv hLJ hAJ
  have hJIeq : J = I := J_eq_sec hZJ hJI hJinv hw1Z hirr
  refine ⟨hirr.1, fun J' _ hZJ' hJ'I => ?_⟩
  exact sec_dichotomy_of_J hW hw1Z hJIeq J' hZJ' hJ'I

end CFSG.GroupTheory
