module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.Lift
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTransport
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Triple
import CFSG.Quasithin.Background.F918V5GComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I113

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem closureIn_eq_bClosure (K B : Subgroup G) : closureIn K B = bClosure B K := by
  refine le_antisymm (iSup₂_le fun a ha => ?_) (iSup₂_le fun b hb => ?_)
  · have h : K.map (MulAut.conj a).toMonoidHom = GLBConj a⁻¹ K := by
      show K.map (MulAut.conj a).toMonoidHom = K.map (MulAut.conj a⁻¹⁻¹).toMonoidHom
      rw [inv_inv]
    rw [h]
    exact le_iSup₂_of_le (f := fun (b : G) (_ : b ∈ B) => GLBConj b K) a⁻¹ (B.inv_mem ha) le_rfl
  · exact le_iSup₂_of_le (f := fun (a : G) (_ : a ∈ B) => K.map (MulAut.conj a).toMonoidHom) b⁻¹
      (B.inv_mem hb) le_rfl

private theorem mk'_eq_one_iff {Y : Type*} [Group Y] (N : Subgroup Y) [N.Normal] (y : Y) :
    QuotientGroup.mk' N y = 1 ↔ y ∈ N := QuotientGroup.eq_one_iff y

private theorem exists_lift_abstract {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {D M : Subgroup Y} (hD : IsPGroup 3 D)
    (hDM : D ≤ Subgroup.normalizer (M : Set Y)) (E : Subgroup (Y ⧸ N))
    (hEM : E ≤ M.map (QuotientGroup.mk' N)) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hcent : ∀ z ∈ D.map (QuotientGroup.mk' N), ∀ e ∈ E, z * e = e * z) :
    ∃ W : Subgroup Y, W ≤ M ∧ IsPGroup 3 W ∧ D ≤ Subgroup.normalizer (W : Set Y) ∧
      W.map (QuotientGroup.mk' N) = E := by
  have hOE : N ≤ E.comap (QuotientGroup.mk' N) := fun n hn => by
    rw [Subgroup.mem_comap, (mk'_eq_one_iff N n).2 hn]
    exact E.one_mem
  have hEN : E.comap (QuotientGroup.mk' N) ≤ Subgroup.normalizer (N : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hEp : ∀ e ∈ E.comap (QuotientGroup.mk' N), ∃ k : ℕ, e ^ (3 ^ k) ∈ N := fun e he => by
    refine ⟨1, ?_⟩
    rw [pow_one, ← mk'_eq_one_iff N, map_pow]
    exact hE3 _ he
  have hDE : D ≤ Subgroup.normalizer (E.comap (QuotientGroup.mk' N) : Set Y) := fun d hd =>
    Subgroup.mem_normalizer_fintype fun h hh => by
      rw [SetLike.mem_coe, Subgroup.mem_comap] at hh ⊢
      rw [map_mul, map_mul, map_inv]
      have := hcent _ ⟨d, hd, rfl⟩ _ hh
      rw [this, mul_inv_cancel_right]
      exact hh
  have hNO : M ≤ Subgroup.normalizer (N : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hENO : E.comap (QuotientGroup.mk' N) ≤ M ⊔ N := fun y hy => by
    obtain ⟨m, hm, hmy⟩ := hEM hy
    have hn : m⁻¹ * y ∈ N := by
      rw [← mk'_eq_one_iff N, map_mul, map_inv, hmy, inv_mul_cancel]
    have := Subgroup.mul_mem_sup hm hn
    rwa [mul_inv_cancel_left] at this
  obtain ⟨W, hWle, hWp, hDW, hWsup⟩ := exists_pGroup_lift Nat.prime_three hN hOE hEN hEp hD hDE
    hDM hNO hENO
  refine ⟨W, hWle.trans inf_le_left, hWp, hDW, ?_⟩
  have := congrArg (Subgroup.map (QuotientGroup.mk' N)) hWsup
  rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)] at this

theorem exists_two_abstract {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {A : Subgroup Y} (hA : IsPGroup 3 A) (T : Subgroup (Y ⧸ N))
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hAT : A.map (QuotientGroup.mk' N) ≤ Subgroup.normalizer (T : Set (Y ⧸ N))) :
    ∃ S : Subgroup Y, S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set Y) := by
  have hNT : N ≤ T.comap (QuotientGroup.mk' N) := fun n hn => by
    rw [Subgroup.mem_comap, (mk'_eq_one_iff N n).2 hn]
    exact T.one_mem
  have hOT : N < T.comap (QuotientGroup.mk' N) := by
    refine lt_of_le_of_ne hNT fun h => hT ?_
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N t
    have hy : y ∈ T.comap (QuotientGroup.mk' N) := ht
    rw [← h] at hy
    rw [Subgroup.mem_bot]
    exact (mk'_eq_one_iff N y).2 hy
  have hTN : T.comap (QuotientGroup.mk' N) ≤ Subgroup.normalizer (N : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hT2' : ∀ t ∈ T.comap (QuotientGroup.mk' N), ∃ k : ℕ, t ^ (2 ^ k) ∈ N := fun t ht => by
    obtain ⟨k, hk⟩ := hT2 (⟨QuotientGroup.mk' N t, ht⟩ : T)
    refine ⟨k, ?_⟩
    rw [← mk'_eq_one_iff N, map_pow]
    exact congrArg Subtype.val hk
  have hAT' : A ≤ Subgroup.normalizer (T.comap (QuotientGroup.mk' N) : Set Y) := fun a ha =>
    Subgroup.mem_normalizer_fintype fun h hh => by
      rw [SetLike.mem_coe, Subgroup.mem_comap] at hh ⊢
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hAT ⟨a, ha, rfl⟩) _).1 hh
  obtain ⟨S, -, hS, hS2, hAS⟩ := exists_two_subgroup_lift Nat.prime_three (by norm_num) hN hOT hTN
    hT2' hA hAT'
  exact ⟨S, hS, hS2, hAS⟩

private theorem comap_subtype_map_subtype {X : Subgroup G} (S₀ : Subgroup ↥X) :
    (S₀.map X.subtype).subgroupOf X = S₀ :=
  Subgroup.comap_map_eq_self_of_injective X.subtype_injective S₀

theorem le_normalizer_map_subtype {X A : Subgroup G} (hAX : A ≤ X) {S₀ : Subgroup ↥X}
    (h : A.subgroupOf X ≤ Subgroup.normalizer (S₀ : Set ↥X)) :
    A ≤ Subgroup.normalizer ((S₀.map X.subtype : Subgroup G) : Set G) := by
  have h2 := Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le S₀)
  rw [comap_subtype_map_subtype] at h2
  intro a ha
  have h3 : (⟨a, hAX ha⟩ : ↥X) ∈
      (Subgroup.normalizer ((S₀.map X.subtype : Subgroup G) : Set G)).subgroupOf X := by
    rw [h2]
    exact h ha
  exact h3

theorem not_dvd_card_glaPPrimeCore (X : Subgroup G) :
    ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card

theorem exists_W {X D N : Subgroup G} (hDX : D ≤ X) (hNX : N ≤ X) (hD : IsPGroup 3 D)
    (hDN : D ≤ Subgroup.normalizer (N : Set G)) (E : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X))
    (hEN : E ≤ barX 3 X N) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hcent : ∀ z ∈ barX 3 X D, ∀ e ∈ E, z * e = e * z) :
    ∃ W : Subgroup G, W ≤ X ∧ W ≤ N ∧ IsPGroup 3 W ∧ D ≤ Subgroup.normalizer (W : Set G) ∧
      barX 3 X W = E := by
  have hNc := not_dvd_card_glaPPrimeCore X
  have hDM : D.subgroupOf X ≤ Subgroup.normalizer ((N.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hNX]
    exact fun x hx => hDN hx
  obtain ⟨W₀, hW₀N, hW₀p, hDW₀, hW₀E⟩ := exists_lift_abstract (GLAPPrimeCore 3 ↥X) hNc
    (hD.comap_of_injective X.subtype X.subtype_injective) hDM E hEN hE3 hcent
  have hWX : W₀.map X.subtype ≤ X := Subgroup.map_subtype_le W₀
  refine ⟨W₀.map X.subtype, hWX, ?_, hW₀p.map _, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hW₀N hw
  · have h2 := Subgroup.subgroupOf_normalizer_eq hWX
    rw [comap_subtype_map_subtype] at h2
    intro d hd
    have h3 : (⟨d, hDX hd⟩ : ↥X) ∈
        (Subgroup.normalizer ((W₀.map X.subtype : Subgroup G) : Set G)).subgroupOf X := by
      rw [h2]
      exact hDW₀ (show (⟨d, hDX hd⟩ : ↥X) ∈ D.subgroupOf X from hd)
    exact h3
  · show ((W₀.map X.subtype).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) = E
    rw [comap_subtype_map_subtype]
    exact hW₀E

theorem barX_sup {X P R : Subgroup G} (hP : P ≤ X) (hR : R ≤ X) :
    barX 3 X (P ⊔ R) = barX 3 X P ⊔ barX 3 X R := by
  unfold barX
  rw [Subgroup.subgroupOf_sup hP hR, Subgroup.map_sup]

theorem eq_of_mk'_eq {X W : Subgroup G} (hW : IsPGroup 3 W) (hWX : W ≤ X) {x y : ↥X}
    (hx : (x : G) ∈ W) (hy : (y : G) ∈ W)
    (h : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x = QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) y) :
    x = y := by
  have := injective_barX_comp Nat.prime_three hW hWX
    (a₁ := (⟨x, hx⟩ : ↥(W.subgroupOf X))) (a₂ := ⟨y, hy⟩) h
  exact congrArg Subtype.val this

private theorem mk'_eq_one_of_mem_O {X : Subgroup G} {x : ↥X}
    (h : (x : G) ∈ GLAPPrimeCoreOf 3 X) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x = 1 := by
  have h' : (x : G) ∈ (GLAPPrimeCore 3 ↥X).map X.subtype := h
  obtain ⟨y, hy, hyx⟩ := h'
  have : y = x := Subtype.ext hyx
  subst this
  exact (mk'_eq_one_iff _ y).2 hy

private theorem mem_O_of_mk'_eq_one {X : Subgroup G} {x : ↥X}
    (h : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x = 1) : (x : G) ∈ GLAPPrimeCoreOf 3 X :=
  ⟨x, (mk'_eq_one_iff _ x).1 h, rfl⟩

private theorem comm_of_centMod {X K : Subgroup G} (hK : GLAPComponent 3 X K) {x : ↥X}
    (hx : (x : G) ∈ centModSubgroup 3 K) :
    ∀ m ∈ barX 3 X K, QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x * m =
      m * QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x := by
  rintro _ ⟨l, hl, rfl⟩
  have h1 : ⁅(l : G), (x : G)⁆ ∈ GLAPPrimeCoreOf 3 K := hx.2 (l : G) hl
  have h2 : ⁅(l : G), (x : G)⁆ ∈ GLAPPrimeCoreOf 3 X := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hK.2.1] at h1
    exact h1.2
  have h3 := mk'_eq_one_of_mem_O (x := ⁅l, x⁆) h2
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h3
  exact h3.symm

theorem mem_centMod_of_comm {X K : Subgroup G} (hK : GLAPComponent 3 X K) {x : ↥X}
    (h : ∀ m ∈ barX 3 X K, QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x * m =
      m * QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x) :
    (x : G) ∈ centModSubgroup 3 K := by
  have hnorm : (x : G) ∈ Subgroup.normalizer (K : Set G) := by
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x ∈
        Subgroup.normalizer ((barX 3 X K : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := t113_mem_normalizer_of_commute h
    have h2 : x ∈ (Subgroup.normalizer ((barX 3 X K : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X))).comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) := h1
    rw [i112f_comap_normalizer_barX hK] at h2
    exact h2
  refine ⟨hnorm, fun l hl => ?_⟩
  have hlX : l ∈ X := hK.1 hl
  have hk : ⁅l, (x : G)⁆ ∈ K := by
    have h1 : (x : G) * l⁻¹ * (x : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 hnorm _).1 (K.inv_mem hl)
    have := K.mul_mem hl h1
    simpa [commutatorElement_def, mul_assoc] using this
  have hO : ⁅l, (x : G)⁆ ∈ GLAPPrimeCoreOf 3 X := by
    have h3 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⁅(⟨l, hlX⟩ : ↥X), x⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (h _ ⟨⟨l, hlX⟩, hl, rfl⟩).symm
    exact mem_O_of_mk'_eq_one h3
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hK.2.1]
  exact ⟨hk, hO⟩

theorem bClosure_le_X {X B K : Subgroup G} (hBX : B ≤ X) (hKX : K ≤ X) :
    bClosure B K ≤ X := by
  refine iSup₂_le fun g hg y hy => ?_
  have h1 : g * y * g⁻¹ ∈ X := hKX (mem_gLBConj.1 hy)
  have := X.mul_mem (X.mul_mem (X.inv_mem (hBX hg)) h1) (hBX hg)
  simpa [mul_assoc] using this

theorem le_normalizer_bClosure' (B K : Subgroup G) :
    B ≤ Subgroup.normalizer (bClosure B K : Set G) := by
  have key : ∀ h ∈ B, ∀ y ∈ bClosure B K, h * y * h⁻¹ ∈ bClosure B K := by
    intro h hh y hy
    have : bClosure B K ≤ GLBConj h (bClosure B K) := by
      refine iSup₂_le fun g hg z hz => ?_
      rw [mem_gLBConj]
      have hz' : g * z * g⁻¹ ∈ K := mem_gLBConj.1 hz
      refine (le_iSup₂_of_le (f := fun (b : G) (_ : b ∈ B) => GLBConj b K) (g * h⁻¹)
        (B.mul_mem hg (B.inv_mem hh)) le_rfl : GLBConj (g * h⁻¹) K ≤ bClosure B K) ?_
      rw [mem_gLBConj]
      have : g * h⁻¹ * (h * z * h⁻¹) * (g * h⁻¹)⁻¹ = g * z * g⁻¹ := by group
      rw [this]
      exact hz'
    exact mem_gLBConj.1 (this hy)
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key h hh y, fun hy => ?_⟩
  have := key h⁻¹ (B.inv_mem hh) _ hy
  simpa [mul_assoc] using this

private theorem comm_barX_bClosure {X B K : Subgroup G} (hB : IsElemAbelian 3 B) (hBX : B ≤ X)
    (hKX : K ≤ X) {z : ↥X ⧸ GLAPPrimeCore 3 ↥X} (hzB : z ∈ barX 3 X B)
    (hz : ∀ m ∈ barX 3 X K, z * m = m * z) :
    ∀ m ∈ barX 3 X (bClosure B K), z * m = m * z := by
  rw [i112f_barX_bClosure hBX hKX]
  have hle : i112J (barX 3 X B) (barX 3 X K) ≤
      Subgroup.centralizer ({z} : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    refine iSup₂_le fun g hg y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcg : Commute z g := isElemAbelian_commute (isElemAbelian_barX hB) hzB hg
    have hcy : Commute z (g * y * g⁻¹) := hz _ (mem_gLBConj.1 hy)
    have h1 : Commute z (g⁻¹ * (g * y * g⁻¹) * g) := (hcg.inv_right.mul_right hcy).mul_right hcg
    have h2 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [h2] at h1
    exact h1.eq.symm
  intro m hm
  have := hle hm
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

private theorem mem_normalizer_conj {X B K : Subgroup G} (hBX : B ≤ X)
    (hK : GLAPComponent 3 X K) {x : ↥X}
    (hx : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x ∈ barX 3 X (bClosure B K)) {b : G}
    (hb : b ∈ B) : (x : G) ∈ Subgroup.normalizer (GLBConj b K : Set G) := by
  have hbX : b ∈ X := hBX hb
  have hXb : GLBConj b X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hbX)
  have hL : GLAPComponent 3 X (GLBConj b K) := by
    have := glaPComponent_gLBConj hK b
    rwa [hXb] at this
  have hL2 : IsComponentOf (barX 3 X (GLBConj b K)) ⊤ := hL.2.2.1
  have hkey := i112f_comap_normalizer_barX hL
  have hle : barX 3 X (bClosure B K) ≤
      Subgroup.normalizer ((barX 3 X (GLBConj b K) : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    rw [i112f_barX_bClosure hBX hK.1]
    refine iSup₂_le fun g hg => ?_
    obtain ⟨y, hy, rfl⟩ := hg
    have h1 : GLBConj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) y) (barX 3 X K) =
        barX 3 X (GLBConj (y : G) K) := (i113g_barX_gLBConj_eq 3 y.2 K).symm
    rw [h1]
    have hLy : GLAPComponent 3 X (GLBConj (y : G) K) := by
      have := glaPComponent_gLBConj hK (y : G)
      rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer y.2)] at this
    have hLy2 : IsComponentOf (barX 3 X (GLBConj (y : G) K)) ⊤ := hLy.2.2.1
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hLy2 hL2 with h | h
    · rw [h]
      exact Subgroup.le_normalizer
    · intro m hm
      exact t113_mem_normalizer_of_commute (fun j hj => h m hm j hj)
  have hmem : x ∈ (Subgroup.normalizer ((barX 3 X (GLBConj b K) :
      Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))).comap
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) := hle hx
  rw [hkey] at hmem
  exact hmem

private theorem mem_zpowers_of_pow_three {Q : Type*} [Group Q] {a u v : Q} (ha : a ^ 3 = 1)
    {i j : ℤ} (hu : a ^ i = u) (hv : a ^ j = v) (hu1 : u ≠ 1) : v ∈ Subgroup.zpowers u := by
  have ha' : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha
  have hi : a ^ i = a ^ (i % 3) := zpow_eq_zpow_emod i ha'
  have hmod : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hamem : a ∈ Subgroup.zpowers u := by
    rcases hmod with h | h | h
    · exfalso
      apply hu1
      rw [← hu, hi, h, zpow_zero]
    · have : a = u := by rw [← hu, hi, h, zpow_one]
      rw [this]
      exact Subgroup.mem_zpowers u
    · have h2 : u = a ^ (2 : ℤ) := by rw [← hu, hi, h]
      have h3 : a = u ^ (2 : ℤ) := by
        rw [h2, ← zpow_mul]
        have : a ^ ((2 : ℤ) * 2) = a ^ (4 : ℤ) := by norm_num
        rw [this]
        have h4 : a ^ (4 : ℤ) = a ^ (1 : ℤ) := by
          rw [zpow_eq_zpow_emod 4 ha']
          norm_num
        rw [h4, zpow_one]
      rw [h3]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) _
  rw [← hv]
  exact Subgroup.zpow_mem _ hamem _

theorem i113_lift {X B K : Subgroup G} (hB : GLAIsBmax 3 B) (hBX : B ≤ X)
    (hK : GLAPComponent 3 X K) (E : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X))
    (hEK : E ≤ barX 3 X (bClosure B K)) (hEel : IsElemAbelian 3 E)
    (hEnc : ∃ u ∈ E, ∃ v ∈ E, (∀ m ∈ barX 3 X K, u * m = m * u) ∧
      (∀ m ∈ barX 3 X K, v * m = m * v) ∧ u ≠ 1 ∧ v ∉ Subgroup.zpowers u)
    (hEbot : barX 3 X (B ⊓ centModSubgroup 3 K) ⊓ E = ⊥)
    (hEcard : Nat.card B ≤ Nat.card (barX 3 X (B ⊓ centModSubgroup 3 K)) * Nat.card E)
    (hE2 : 2 ∣ Nat.card (GLAPPrimeCoreOf 3 X) ∨
      ∃ T : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), T ≠ ⊥ ∧ IsPGroup 2 T ∧
        barX 3 X (B ⊓ centModSubgroup 3 K) ≤ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ∧
        E ≤ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) :
    ∃ A : Subgroup G, GLAIsBmax 3 A ∧ B ⊓ centModSubgroup 3 K ≤ A ∧
      (∀ b ∈ B, A ≤ Subgroup.normalizer (GLBConj b K : Set G)) ∧
      (∀ a ∈ A, ∃ u ∈ A ⊓ B, ∃ v ∈ A ⊓ closureIn K B, a = u * v) ∧
      ¬ IsCyclic (A ⊓ closureIn K B ⊓ centModSubgroup 3 K : Subgroup G) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set B₀ : Subgroup G := B ⊓ centModSubgroup 3 K with hB₀
  have hKX : K ≤ X := hK.1
  have hBp : IsPGroup 3 B := GLAIsBmax.isPGroup hB
  have hB₀B : B₀ ≤ B := inf_le_left
  have hB₀X : B₀ ≤ X := hB₀B.trans hBX
  have hB₀p : IsPGroup 3 B₀ := hBp.to_le hB₀B
  have hB₀el : IsElemAbelian 3 B₀ := isElemAbelian_mono hB.1 hB₀B
  have hKtX : bClosure B K ≤ X := bClosure_le_X hBX hKX
  have hcentK : ∀ z ∈ barX 3 X B₀, ∀ m ∈ barX 3 X (bClosure B K), z * m = m * z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxB₀ : (x : G) ∈ B₀ := hx
    have hzB : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x ∈ barX 3 X B := ⟨x, hxB₀.1, rfl⟩
    exact comm_barX_bClosure hB.1 hBX hKX hzB (comm_of_centMod hK hxB₀.2)
  have hcent : ∀ z ∈ barX 3 X B₀, ∀ e ∈ E, z * e = e * z := fun z hz e he =>
    hcentK z hz e (hEK he)
  obtain ⟨W, hWX, hWK, hWp, hB₀W, hWE⟩ := exists_W hB₀X hKtX hB₀p
    (hB₀B.trans (le_normalizer_bClosure' B K)) E hEK (fun e he => hEel.2 e he) hcent
  have hWmem : ∀ x : ↥X, (x : G) ∈ W → QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x ∈ E :=
    fun x hx => by
      rw [← hWE]
      exact ⟨x, hx, rfl⟩
  have hWsurj : ∀ e ∈ E, ∃ x : ↥X, (x : G) ∈ W ∧ QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x = e :=
    fun e he => by
      rw [← hWE] at he
      exact he
  have hcomm : ∀ b ∈ B₀, ∀ w ∈ W, b * w = w * b := by
    intro b hb w hw
    have hbX := hB₀X hb
    have hwX := hWX hw
    have hcW : b * w * b⁻¹ * w⁻¹ ∈ W := by
      have h1 : b * w * b⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 (hB₀W hb) w).1 hw
      exact W.mul_mem h1 (W.inv_mem hw)
    have h2 : (⁅(⟨b, hbX⟩ : ↥X), (⟨w, hwX⟩ : ↥X)⁆ : ↥X) = 1 := by
      refine eq_of_mk'_eq hWp hWX (x := ⁅(⟨b, hbX⟩ : ↥X), (⟨w, hwX⟩ : ↥X)⁆) (y := 1) hcW
        W.one_mem ?_
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2, map_one]
      exact hcent _ ⟨⟨b, hbX⟩, hb, rfl⟩ _ (hWmem ⟨w, hwX⟩ hw)
    exact commutatorElement_eq_one_iff_mul_comm.1 (congrArg Subtype.val h2)
  have hWel : IsElemAbelian 3 W := by
    refine isElemAbelian_of_forall (fun a ha b hb => ?_) (fun a ha => ?_)
    · have haX := hWX ha
      have hbX := hWX hb
      have h1 := isElemAbelian_commute hEel (hWmem ⟨a, haX⟩ ha) (hWmem ⟨b, hbX⟩ hb)
      have h2 := eq_of_mk'_eq hWp hWX (x := ⟨a, haX⟩ * ⟨b, hbX⟩) (y := ⟨b, hbX⟩ * ⟨a, haX⟩)
        (W.mul_mem ha hb) (W.mul_mem hb ha) (by rw [map_mul, map_mul]; exact h1)
      exact congrArg Subtype.val h2
    · have haX := hWX ha
      have h2 := eq_of_mk'_eq hWp hWX (x := (⟨a, haX⟩ : ↥X) ^ 3) (y := 1) (W.pow_mem ha 3)
        W.one_mem (by rw [map_pow, map_one]; exact hEel.2 _ (hWmem ⟨a, haX⟩ ha))
      exact congrArg Subtype.val h2
  have hB₀W' : B₀ ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hgX : g ∈ X := hB₀X hg.1
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨g, hgX⟩ ∈ barX 3 X B₀ ⊓ E :=
      ⟨⟨⟨g, hgX⟩, hg.1, rfl⟩, hWmem ⟨g, hgX⟩ hg.2⟩
    rw [hEbot, Subgroup.mem_bot] at h1
    have h2 := eq_of_mk'_eq hBp hBX (x := ⟨g, hgX⟩) (y := 1) (hB₀B hg.1) B.one_mem
      (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  obtain ⟨hAel, hAcard⟩ := t113_sup_elemAbelian hB₀el hWel hcomm hB₀W'
  set A : Subgroup G := B₀ ⊔ W with hA
  have hAX : A ≤ X := sup_le hB₀X hWX
  have hAp : IsPGroup 3 A := isPGroup_of_isElemAbelian hAel
  have hWcard : Nat.card W = Nat.card E := by
    rw [← i113g_card_barX hp3 hWp hWX, hWE]
  have hB₀card : Nat.card B₀ = Nat.card (barX 3 X B₀) := (i113g_card_barX hp3 hB₀p hB₀X).symm
  have hBA : Nat.card B ≤ Nat.card A := by
    rw [hAcard, hB₀card, hWcard]
    exact hEcard
  obtain ⟨S, hS1, hS2, hAS⟩ : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧
      A ≤ Subgroup.normalizer (S : Set G) := by
    rcases hE2 with hev | ⟨T, hT, hT2, hB₀T, hET⟩
    · obtain ⟨S, -, hS1, hS2, hAS⟩ := exists_two_subgroup_of_even hp3
        (not_dvd_card_glaPPrimeCoreOf hp3 X) hev hAp
        (hAX.trans (le_normalizer_glaPPrimeCoreOf 3 X))
      exact ⟨S, hS1, hS2, hAS⟩
    · have hAT : (A.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) ≤
          Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
        show barX 3 X A ≤ _
        rw [hA, barX_sup hB₀X hWX, hWE]
        exact sup_le hB₀T hET
      obtain ⟨S₀, hS₀1, hS₀2, hAS₀⟩ := exists_two_abstract (GLAPPrimeCore 3 ↥X)
        (not_dvd_card_glaPPrimeCore X) (hAp.comap_of_injective X.subtype X.subtype_injective) T hT
        hT2 hAT
      refine ⟨S₀.map X.subtype, ?_, hS₀2.map _, le_normalizer_map_subtype hAX hAS₀⟩
      rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]
  have hAB : GLAIsBmax 3 A :=
    ⟨hAel, le_antisymm (card_le_pow_glaTwoLocalRank hp3 hAel hS1 hS2 hAS)
      (by rw [← hB.2.1]; exact hBA), S, hS1, hS2, hAS⟩
  refine ⟨A, hAB, le_sup_left, ?_, ?_, ?_⟩
  ·
    intro b hb
    refine sup_le ?_ ?_
    · intro b' hb'
      have hb'K : b' ∈ Subgroup.normalizer (K : Set G) := hb'.2.1
      rw [mem_normalizer_iff_gLBConj_eq] at hb'K ⊢
      have hcomm' : b * b' = b' * b := isElemAbelian_commute hB.1 hb hb'.1
      calc GLBConj b' (GLBConj b K) = GLBConj (b * b') K := gLBConj_gLBConj b' b K
        _ = GLBConj (b' * b) K := by rw [hcomm']
        _ = GLBConj b (GLBConj b' K) := (gLBConj_gLBConj b b' K).symm
        _ = GLBConj b K := by rw [hb'K]
    · intro w hw
      exact mem_normalizer_conj hBX hK (x := ⟨w, hWX hw⟩) (hEK (hWmem ⟨w, hWX hw⟩ hw)) hb
  ·
    intro a ha
    obtain ⟨u, hu, v, hv, rfl⟩ := t113_mem_sup hcomm ha
    refine ⟨u, ⟨Subgroup.mem_sup_left hu, hB₀B hu⟩, v, ⟨Subgroup.mem_sup_right hv, ?_⟩, rfl⟩
    rw [closureIn_eq_bClosure]
    exact hWK hv
  ·
    obtain ⟨u, hu, v, hv, huK, hvK, hu1, hvu⟩ := hEnc
    obtain ⟨u', hu'W, rfl⟩ := hWsurj u hu
    obtain ⟨v', hv'W, rfl⟩ := hWsurj v hv
    have hmemH : ∀ x : ↥X, (x : G) ∈ W →
        (∀ m ∈ barX 3 X K, QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x * m =
          m * QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x) →
        (x : G) ∈ (A ⊓ closureIn K B ⊓ centModSubgroup 3 K : Subgroup G) := fun x hx hcm =>
      ⟨⟨Subgroup.mem_sup_right hx, by rw [closureIn_eq_bClosure]; exact hWK hx⟩,
        mem_centMod_of_comm hK hcm⟩
    have hu'H := hmemH u' hu'W huK
    have hv'H := hmemH v' hv'W hvK
    intro hcyc
    obtain ⟨g, hg⟩ := @IsCyclic.exists_generator _ _ hcyc
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨u', hu'H⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨v', hv'H⟩)
    have hgA : (g : G) ∈ A := g.2.1.1
    have hgX : (g : G) ∈ X := hAX hgA
    have hγ3 : (⟨g, hgX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (hAel.2 _ hgA)
    have hγi : (⟨g, hgX⟩ : ↥X) ^ i = u' := by
      apply Subtype.ext
      have := congrArg Subtype.val hi
      simpa using this
    have hγj : (⟨g, hgX⟩ : ↥X) ^ j = v' := by
      apply Subtype.ext
      have := congrArg Subtype.val hj
      simpa using this
    exact hvu (mem_zpowers_of_pow_three
      (a := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨g, hgX⟩)
      (by rw [← map_pow, hγ3, map_one]) (i := i) (j := j) (by rw [← map_zpow, hγi])
      (by rw [← map_zpow, hγj]) hu1)

end CFSG.LocalAnalysis.GLTheoremA.I113
