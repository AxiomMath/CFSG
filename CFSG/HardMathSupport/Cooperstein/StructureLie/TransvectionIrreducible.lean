module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.Nodes
import CFSG.HardMathSupport.Cooperstein.Coordinator.Star

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

namespace TransvIrr

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_commutator_le_of_rotate {A B C N : Subgroup G}
    (hA : A ≤ normalizer (N : Set G)) (hB : B ≤ normalizer (N : Set G))
    (hC : C ≤ normalizer (N : Set G))
    (h1 : ⁅⁅A, B⁆, C⁆ ≤ N) (h2 : ⁅⁅B, C⁆, A⁆ ≤ N) : ⁅⁅C, A⁆, B⁆ ≤ N := by
  set Y := normalizer (N : Set G) with hY
  have hN : (N.subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer (le_normalizer)).mpr le_rfl
  let q := QuotientGroup.mk' (N.subgroupOf Y)
  have hcomm : ∀ {P R : Subgroup G}, P ≤ Y → R ≤ Y →
      ⁅P, R⁆.subgroupOf Y = ⁅P.subgroupOf Y, R.subgroupOf Y⁆ := by
    intro P R hP hR
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hP hR), Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hP, Subgroup.map_subgroupOf_eq_of_le hR]
  have hAB : ⁅A, B⁆ ≤ Y := Subgroup.commutator_le_of_le hA hB
  have hBC : ⁅B, C⁆ ≤ Y := Subgroup.commutator_le_of_le hB hC
  have hCA : ⁅C, A⁆ ≤ Y := Subgroup.commutator_le_of_le hC hA
  have e1 : ⁅⁅A.subgroupOf Y, B.subgroupOf Y⁆, C.subgroupOf Y⁆ ≤ N.subgroupOf Y := by
    rw [← hcomm hA hB, ← hcomm hAB hC]
    exact (Subgroup.comap_mono h1)
  have e2 : ⁅⁅B.subgroupOf Y, C.subgroupOf Y⁆, A.subgroupOf Y⁆ ≤ N.subgroupOf Y := by
    rw [← hcomm hB hC, ← hcomm hBC hA]
    exact (Subgroup.comap_mono h2)
  have f1 : ⁅⁅(A.subgroupOf Y).map q, (B.subgroupOf Y).map q⁆, (C.subgroupOf Y).map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    simpa [q] using e1
  have f2 : ⁅⁅(B.subgroupOf Y).map q, (C.subgroupOf Y).map q⁆, (A.subgroupOf Y).map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    simpa [q] using e2
  have f3 := Subgroup.commutator_commutator_eq_bot_of_rotate f1 f2
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff] at f3
  have f4 : ⁅⁅C, A⁆, B⁆.subgroupOf Y ≤ N.subgroupOf Y := by
    rw [hcomm hCA hB, hcomm hC hA]
    simpa [q] using f3
  intro x hx
  have := f4 (show (⟨x, Subgroup.commutator_le_of_le hCA hB hx⟩ : Y) ∈ ⁅⁅C, A⁆, B⁆.subgroupOf Y from hx)
  exact this

theorem conj_mem_of_le_normalizer {K X : Subgroup G} (hK : K ≤ normalizer (X : Set G)) {g x : G}
    (hg : g ∈ K) (hx : x ∈ X) : g * x * g⁻¹ ∈ X :=
  (mem_normalizer_iff.mp (hK hg) x).mp hx

theorem le_normalizer_of_conj_mem {K X : Subgroup G}
    (h : ∀ g ∈ K, ∀ x ∈ X, g * x * g⁻¹ ∈ X) : K ≤ normalizer (X : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h g hg x, fun hx => ?_⟩
  have := h g⁻¹ (K.inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem mem_normalizer_commutator {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  have := Subgroup.map_commutator A B (MulAut.conj g).toMonoidHom
  show ⁅A, B⁆.map (MulAut.conj g).toMonoidHom = ⁅A, B⁆
  rw [this]
  have hA' : A.map (MulAut.conj g).toMonoidHom = A := hA
  have hB' : B.map (MulAut.conj g).toMonoidHom = B := hB
  rw [hA', hB']

def commKer (M W₁ W₂ : Subgroup G) (hW₂ : M ≤ normalizer (W₂ : Set G)) : Subgroup G where
  carrier := {g | g ∈ M ∧ ∀ w ∈ W₁, ⁅w, g⁆ ∈ W₂}
  one_mem' := ⟨M.one_mem, fun w _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨M.mul_mem ha hb, fun w hw => ?_⟩
    have e : ⁅w, a * b⁆ = ⁅w, a⁆ * (a * ⁅w, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact W₂.mul_mem (ha' w hw) (conj_mem_of_le_normalizer hW₂ ha (hb' w hw))
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨M.inv_mem ha, fun w hw => ?_⟩
    have e : ⁅w, a⁻¹⁆ = a⁻¹ * ⁅w, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact conj_mem_of_le_normalizer hW₂ (M.inv_mem ha) (W₂.inv_mem (ha' w hw))

theorem C0_le_commKer {M V W₁ W₂ : Subgroup G} {hW₂ : M ≤ normalizer (W₂ : Set G)}
    (h1 : W₁ ≤ V) : M ⊓ centralizer (V : Set G) ≤ commKer M W₁ W₂ hW₂ := by
  rintro c ⟨hcM, hcV⟩
  refine ⟨hcM, fun w hw => ?_⟩
  have h2 : w * c = c * w := mem_centralizer_iff.mp hcV w (h1 hw)
  have : ⁅w, c⁆ = 1 := by rw [commutatorElement_eq_one_iff_mul_comm]; exact h2
  rw [this]; exact W₂.one_mem

structure Setting (M L V : Subgroup G) (s : G) : Prop where
  normV : M ≤ normalizer (V : Set G)
  comm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v
  normL : M ≤ normalizer (L : Set G)
  le : L ≤ M
  mem : s ∈ M
  card : Nat.card ↥⁅V, zpowers s⁆ = 2
  gen : M ≤ L ⊔ zpowers s ⊔ (M ⊓ centralizer (V : Set G))
  notCent : ¬ L ≤ centralizer (V : Set G)
  perf : L ≤ ⁅L, L⁆ ⊔ (M ⊓ centralizer (V : Set G))
  normal : ∀ T : Subgroup G, T ≤ M → M ≤ normalizer (T : Set G) →
    M ⊓ centralizer (V : Set G) ≤ T → s ∈ T → L ≤ T

namespace Setting

variable {M L V : Subgroup G} {s : G} (h : Setting M L V s)
include h

theorem conjV {g v : G} (hg : g ∈ M) (hv : v ∈ V) : g * v * g⁻¹ ∈ V :=
  conj_mem_of_le_normalizer h.normV hg hv

theorem commV_mem {g v : G} (hg : g ∈ M) (hv : v ∈ V) : ⁅v, g⁆ ∈ V := by
  have e : ⁅v, g⁆ = v * (g * v * g⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact V.mul_mem hv (V.inv_mem (h.conjV hg hv))

theorem comm_le_V {A K : Subgroup G} (hA : A ≤ V) (hK : K ≤ M) : ⁅A, K⁆ ≤ V :=
  commutator_le.mpr fun _ ha _ hk => h.commV_mem (hK hk) (hA ha)

theorem normU : M ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun _ hg =>
  mem_normalizer_commutator (h.normV hg) (h.normL hg)

theorem normCentL : M ≤ normalizer ((centralizer (L : Set G) : Subgroup G) : Set G) := by
  apply le_normalizer_of_conj_mem
  intro g hg x hx
  rw [mem_centralizer_iff] at hx ⊢
  intro l hl
  have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ L := conj_mem_of_le_normalizer h.normL (M.inv_mem hg) hl
  have := hx _ hl'
  calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g⁻¹⁻¹) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * l * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
    _ = g * x * g⁻¹ * l := by group

theorem normCl : M ≤ normalizer ((⁅V, L⁆ ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
  fun _ hg => inf_normalizer_le_normalizer_inf ⟨h.normU hg, h.normCentL hg⟩

theorem le_normalizer_of {X : Subgroup G} (hX : X ≤ V) (hL : L ≤ normalizer (X : Set G))
    (hs : s ∈ normalizer (X : Set G)) : M ≤ normalizer (X : Set G) := by
  refine h.gen.trans (sup_le (sup_le hL ?_) ?_)
  · rw [zpowers_le]; exact hs
  · refine le_normalizer_of_conj_mem fun c hc x hx => ?_
    have hxc : x * c = c * x := mem_centralizer_iff.mp hc.2 x (hX hx)
    have e : c * x * c⁻¹ = x := by
      calc c * x * c⁻¹ = (x * c) * c⁻¹ := by rw [hxc]
        _ = x := by group
    rw [e]; exact hx


theorem comm_of_mem_s {W₁ W₂ : Subgroup G} (h1 : W₁ ≤ V) (hn1 : M ≤ normalizer (W₁ : Set G))
    (hn2 : M ≤ normalizer (W₂ : Set G)) (hs : ∀ w ∈ W₁, ⁅w, s⁆ ∈ W₂) :
    ∀ g ∈ M, ∀ w ∈ W₁, ⁅w, g⁆ ∈ W₂ := by
  set T := commKer M W₁ W₂ hn2 with hT
  have hTM : T ≤ M := fun g hg => hg.1
  have hTn : M ≤ normalizer (T : Set G) := by
    apply le_normalizer_of_conj_mem
    rintro m hm g ⟨hg, hg'⟩
    refine ⟨?_, fun w hw => ?_⟩
    · exact M.mul_mem (M.mul_mem hm hg) (M.inv_mem hm)
    · have e : ⁅w, m * g * m⁻¹⁆ = m * ⁅m⁻¹ * w * m⁻¹⁻¹, g⁆ * m⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      have := hg' (m⁻¹ * w * m⁻¹⁻¹) (conj_mem_of_le_normalizer hn1 (M.inv_mem hm) hw)
      exact conj_mem_of_le_normalizer hn2 hm this
  have hC : M ⊓ centralizer (V : Set G) ≤ T := C0_le_commKer h1
  have hsT : s ∈ T := ⟨h.mem, hs⟩
  have hL := h.normal T hTM hTn hC hsT
  have hM : M ≤ T := h.gen.trans (sup_le (sup_le hL (zpowers_le.mpr hsT)) hC)
  exact fun g hg w hw => (hM hg).2 w hw

theorem mem_Z {v : G} (hv : v ∈ V) : ⁅v, s⁆ ∈ (⁅V, zpowers s⁆ : Subgroup G) :=
  commutator_mem_commutator hv (mem_zpowers s)

theorem s_mem_normalizer_Z : s ∈ normalizer ((⁅V, zpowers s⁆ : Subgroup G) : Set G) :=
  mem_normalizer_commutator (h.normV h.mem) (le_normalizer (mem_zpowers s))

theorem Z_eq_of_ne_one {a b : G} (ha : a ∈ (⁅V, zpowers s⁆ : Subgroup G))
    (hb : b ∈ (⁅V, zpowers s⁆ : Subgroup G)) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have h2 := (Nat.card_eq_two_iff' (1 : ↥(⁅V, zpowers s⁆ : Subgroup G))).mp h.card
  obtain ⟨y, -, hy⟩ := h2
  have e1 : (⟨a, ha⟩ : ↥(⁅V, zpowers s⁆ : Subgroup G)) = y := hy _ (fun e => ha1 (congrArg Subtype.val e))
  have e2 : (⟨b, hb⟩ : ↥(⁅V, zpowers s⁆ : Subgroup G)) = y := hy _ (fun e => hb1 (congrArg Subtype.val e))
  exact congrArg Subtype.val (e1.trans e2.symm)

theorem s_fix_Z {z : G} (hz : z ∈ (⁅V, zpowers s⁆ : Subgroup G)) : s * z * s⁻¹ = z := by
  by_cases hz1 : z = 1
  · simp [hz1]
  · refine (h.Z_eq_of_ne_one (conj_mem_of_le_normalizer (le_refl _) ?_ hz) hz ?_ hz1).symm.symm
    · exact h.s_mem_normalizer_Z
    · intro e; apply hz1
      have : s * z * s⁻¹ = 1 := e
      simpa using this
  

theorem s_sq {v : G} (hv : v ∈ V) : s * (s * v * s⁻¹) * s⁻¹ = v := by
  have hz := h.mem_Z (s := s) hv
  set z := ⁅v, s⁆ with hzdef
  have hz2 : z * z = 1 := by
    have := pow_card_eq_one' (G := ↥(⁅V, zpowers s⁆ : Subgroup G)) (x := ⟨z, hz⟩)
    rw [h.card] at this
    have := congrArg Subtype.val this
    simpa [pow_two] using this
  have hw : s * v * s⁻¹ = z⁻¹ * v := by rw [hzdef]; simp only [commutatorElement_def]; group
  calc s * (s * v * s⁻¹) * s⁻¹ = s * (z⁻¹ * v) * s⁻¹ := by rw [hw]
    _ = (s * z * s⁻¹)⁻¹ * (s * v * s⁻¹) := by group
    _ = z⁻¹ * (z⁻¹ * v) := by rw [h.s_fix_Z hz, hw]
    _ = (z * z)⁻¹ * v := by group
    _ = v := by rw [hz2]; group

theorem comm_s_mem {X : Subgroup G} (hX : s ∈ normalizer (X : Set G)) {x : G} (hx : x ∈ X) :
    ⁅x, s⁆ ∈ X := by
  have e : ⁅x, s⁆ = x * (s * x * s⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact X.mul_mem hx (X.inv_mem (conj_mem_of_le_normalizer (K := normalizer (X : Set G)) le_rfl hX hx))

theorem U_le_V : (⁅V, L⁆ : Subgroup G) ≤ V := h.comm_le_V le_rfl h.le

theorem comm_comm_ge : (⁅V, L⁆ : Subgroup G) ≤ ⁅⁅V, L⁆, L⁆ := by
  have hNV : (⁅⁅V, L⁆, L⁆ : Subgroup G) ≤ V := h.comm_le_V h.U_le_V h.le
  have hnN : M ≤ normalizer ((⁅⁅V, L⁆, L⁆ : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_commutator (h.normU hg) (h.normL hg)
  have hLN : L ≤ normalizer ((⁅⁅V, L⁆, L⁆ : Subgroup G) : Set G) := fun g hg => hnN (h.le hg)
  have hVN : V ≤ normalizer ((⁅⁅V, L⁆, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_of_conj_mem fun v hv x hx => by
      have : v * x * v⁻¹ = x := by
        calc v * x * v⁻¹ = (x * v) * v⁻¹ := by rw [h.comm v hv x (hNV hx)]
          _ = x := by group
      rw [this]; exact hx
  have h3 := commutator_commutator_le_of_rotate (A := L) (B := V) (C := L) hLN hVN hLN
    (by rw [commutator_comm L V]) le_rfl
  have hLT : L ≤ commKer M V ⁅⁅V, L⁆, L⁆ hnN := by
    refine h.perf.trans (sup_le ?_ (C0_le_commKer le_rfl))
    intro a ha
    refine ⟨Subgroup.commutator_le_of_le h.le h.le ha, fun w hw => ?_⟩
    apply h3
    have := commutator_mem_commutator hw ha
    rwa [commutator_comm V] at this
  exact commutator_le.mpr fun v hv l hl => (hLT hl).2 v hv

theorem Cl_lt : (⁅V, L⁆ ⊓ centralizer (L : Set G) : Subgroup G) < ⁅V, L⁆ := by
  refine lt_of_le_of_ne inf_le_left fun e => ?_
  have hU : (⁅V, L⁆ : Subgroup G) ≤ centralizer (L : Set G) := by
    rw [← e]; exact inf_le_right
  have h0 : (⁅⁅V, L⁆, L⁆ : Subgroup G) = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hU
  have h1 : (⁅V, L⁆ : Subgroup G) = ⊥ := le_bot_iff.mp (h0 ▸ h.comm_comm_ge)
  exact h.notCent (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h1))

theorem Z_le_or (X : Subgroup G) :
    (⁅V, zpowers s⁆ : Subgroup G) ≤ X ∨ (⁅V, zpowers s⁆ : Subgroup G) ⊓ X = ⊥ := by
  set Z : Subgroup G := ⁅V, zpowers s⁆ with hZ
  have : Fact (Nat.card ↥Z).Prime := ⟨by rw [h.card]; exact Nat.prime_two⟩
  rcases (X.subgroupOf Z).eq_bot_or_eq_top_of_prime_card with hb | ht
  · right
    refine eq_bot_iff.mpr fun x hx => ?_
    have : (⟨x, hx.1⟩ : ↥Z) ∈ X.subgroupOf Z := hx.2
    rw [hb] at this
    simpa using congrArg Subtype.val (Subgroup.mem_bot.mp this)
  · left
    intro z hz
    have : (⟨z, hz⟩ : ↥Z) ∈ X.subgroupOf Z := by rw [ht]; trivial
    exact this

theorem dichotomy {X : Subgroup G} (hXU : X ≤ ⁅V, L⁆) (hX : M ≤ normalizer (X : Set G)) :
    (⁅V, L⁆ : Subgroup G) ≤ X ∨ X ≤ centralizer (M : Set G) := by
  rcases h.Z_le_or X with hZ | hZ
  · left
    have key := h.comm_of_mem_s h.U_le_V h.normU hX (fun w hw => hZ (h.mem_Z (h.U_le_V hw)))
    have : (⁅⁅V, L⁆, L⁆ : Subgroup G) ≤ X :=
      commutator_le.mpr fun u hu l hl => key l (h.le hl) u hu
    exact h.comm_comm_ge.trans this
  · right
    have hbot : M ≤ normalizer (((⊥ : Subgroup G)) : Set G) :=
      le_normalizer_of_conj_mem fun g _ x hx => by
        rw [Subgroup.mem_bot.mp hx]; simp
    have key := h.comm_of_mem_s (hXU.trans h.U_le_V) hX hbot (fun x hx => by
      rw [← hZ]
      exact ⟨h.mem_Z ((hXU.trans h.U_le_V) hx), h.comm_s_mem (hX h.mem) hx⟩)
    intro x hx
    rw [mem_centralizer_iff]
    intro g hg
    have := key g hg x hx
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm


theorem s_inv_conj {v : G} (hv : v ∈ V) : s⁻¹ * v * s = s * v * s⁻¹ := by
  have := h.s_sq hv
  calc s⁻¹ * v * s = s⁻¹ * (s * (s * v * s⁻¹) * s⁻¹) * s := by rw [this]
    _ = s * v * s⁻¹ := by group

theorem s_mem_normalizer {X : Subgroup G} (hX : X ≤ V) (hf : ∀ x ∈ X, s * x * s⁻¹ ∈ X) :
    s ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hf x, fun hx => ?_⟩
  have e : s * (s * x * s⁻¹) * s⁻¹ = x := by
    have := h.s_inv_conj (hX hx)
    calc s * (s * x * s⁻¹) * s⁻¹ = s⁻¹ * (s * x * s⁻¹) * s := by rw [this]
      _ = x := by group
  rw [← e]
  exact hf _ hx

theorem comm_s_mul {a b : G} (ha : a ∈ V) (hb : b ∈ V) (hs : s ∈ M) :
    ⁅a * b, s⁆ = ⁅a, s⁆ * ⁅b, s⁆ := by
  have e : ⁅a * b, s⁆ = a * ⁅b, s⁆ * a⁻¹ * ⁅a, s⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have hc := h.comm a ha _ (h.commV_mem hs hb)
  have hcm := h.comm _ (h.commV_mem hs ha) _ (h.commV_mem hs hb)
  rw [hc]
  calc ⁅b, s⁆ * a * a⁻¹ * ⁅a, s⁆ = ⁅b, s⁆ * ⁅a, s⁆ := by group
    _ = ⁅a, s⁆ * ⁅b, s⁆ := hcm.symm

theorem comm_mul_l {a b l : G} : ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ * ⁅a, l⁆ := by
  simp only [commutatorElement_def]; group

theorem irred {W : Subgroup G} (hCW : (⁅V, L⁆ ⊓ centralizer (L : Set G) : Subgroup G) ≤ W)
    (hWU : W ≤ ⁅V, L⁆) (hLW : L ≤ normalizer (W : Set G)) :
    W = ⁅V, L⁆ ⊓ centralizer (L : Set G) ∨ W = ⁅V, L⁆ := by
  set U : Subgroup G := ⁅V, L⁆ with hUdef
  set Cl : Subgroup G := U ⊓ centralizer (L : Set G) with hCl
  have hWV : W ≤ V := hWU.trans h.U_le_V
  have hClM : Cl ≤ centralizer (M : Set G) := by
    rcases h.dichotomy (X := Cl) inf_le_left h.normCl with h1 | h1
    · exact absurd (le_antisymm inf_le_left h1) (ne_of_lt h.Cl_lt)
    · exact h1
  have hClfix : ∀ c ∈ Cl, s * c * s⁻¹ = c := by
    intro c hc
    have := mem_centralizer_iff.mp (hClM hc) s h.mem
    calc s * c * s⁻¹ = (c * s) * s⁻¹ := by rw [this]
      _ = c := by group
  set W' : Subgroup G := W.map (MulAut.conj s).toMonoidHom with hW'
  have memW' : ∀ y, y ∈ W' ↔ ∃ x ∈ W, s * x * s⁻¹ = y := by
    intro y; simp [hW', Subgroup.mem_map]
  have hW'U : W' ≤ U := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (memW' y).mp hy
    exact conj_mem_of_le_normalizer h.normU h.mem (hWU hx)
  have hW'V : W' ≤ V := hW'U.trans h.U_le_V
  have hLW' : L ≤ normalizer (W' : Set G) := by
    apply le_normalizer_of_conj_mem
    intro l hl y hy
    obtain ⟨x, hx, rfl⟩ := (memW' y).mp hy
    have hl' : s⁻¹ * l * s⁻¹⁻¹ ∈ L := conj_mem_of_le_normalizer h.normL (M.inv_mem h.mem) hl
    refine (memW' _).mpr ⟨(s⁻¹ * l * s⁻¹⁻¹) * x * (s⁻¹ * l * s⁻¹⁻¹)⁻¹,
      conj_mem_of_le_normalizer hLW hl' hx, ?_⟩
    group
  have hCW' : Cl ≤ W' := fun c hc => (memW' c).mpr ⟨c, hCW hc, hClfix c hc⟩
  have hsW : ∀ x ∈ W', s * x * s⁻¹ ∈ W := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (memW' y).mp hy
    rw [h.s_sq (hWV hx)]; exact hx
  have hsW' : ∀ x ∈ W, s * x * s⁻¹ ∈ W' := fun x hx => (memW' _).mpr ⟨x, hx, rfl⟩
  have hQU : W ⊔ W' ≤ U := sup_le hWU hW'U
  have hPU : W ⊓ W' ≤ U := inf_le_left.trans hWU
  have hQn : M ≤ normalizer ((W ⊔ W' : Subgroup G) : Set G) := by
    refine h.le_normalizer_of (hQU.trans h.U_le_V)
      (fun l hl => inf_normalizer_le_normalizer_sup _ _ ⟨hLW hl, hLW' hl⟩) ?_
    refine h.s_mem_normalizer (hQU.trans h.U_le_V) fun x hx => ?_
    have : W ⊔ W' ≤ (W ⊔ W').comap (MulAut.conj s).toMonoidHom :=
      sup_le (fun w hw => Subgroup.mem_sup_right (hsW' w hw)) (fun w hw => Subgroup.mem_sup_left (hsW w hw))
    exact this hx
  have hPn : M ≤ normalizer ((W ⊓ W' : Subgroup G) : Set G) := by
    refine h.le_normalizer_of (hPU.trans h.U_le_V)
      (fun l hl => inf_normalizer_le_normalizer_inf ⟨hLW hl, hLW' hl⟩) ?_
    exact h.s_mem_normalizer (hPU.trans h.U_le_V) fun x hx => ⟨hsW x hx.2, hsW' x hx.1⟩
  have hcLM : centralizer (M : Set G) ≤ centralizer (L : Set G) :=
    Subgroup.centralizer_le (s := (L : Set G)) (t := (M : Set G)) h.le
  rcases h.dichotomy hQU hQn with hQ | hQ
  swap
  · left
    refine le_antisymm (fun x hx => ⟨hWU hx, ?_⟩) hCW
    exact hcLM (hQ (Subgroup.mem_sup_left hx))
  · rcases h.dichotomy hPU hPn with hP | hP
    · right
      exact le_antisymm hWU (hP.trans inf_le_left)
    · exfalso
      have hker : ∀ x ∈ W, ⁅x, s⁆ = 1 → x ∈ Cl := by
        intro x hx hx1
        rw [commutatorElement_eq_one_iff_mul_comm] at hx1
        have hxW' : x ∈ W' := (memW' x).mpr ⟨x, hx, by
          calc s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [hx1]
            _ = x := by group⟩
        exact ⟨hWU hx, hcLM (hP ⟨hx, hxW'⟩)⟩
      have hWcomm : ∀ x ∈ W, ∀ l ∈ L, ⁅x, l⁆ ∈ Cl := by
        intro x hx l hl
        have hx'W : l * x * l⁻¹ ∈ W := conj_mem_of_le_normalizer hLW hl hx
        have hyW : ⁅x, l⁆ ∈ W := by
          have : ⁅x, l⁆ = x * (l * x * l⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
          rw [this]; exact W.mul_mem hx (W.inv_mem hx'W)
        have hyx : ⁅x, l⁆ * (l * x * l⁻¹) = x := by simp only [commutatorElement_def]; group
        have hxx' : ⁅x, s⁆ = ⁅l * x * l⁻¹, s⁆ := by
          by_cases ha : ⁅x, s⁆ = 1
          · have hxCl := hker x hx ha
            have hc := mem_centralizer_iff.mp hxCl.2 l hl
            have : l * x * l⁻¹ = x := by
              calc l * x * l⁻¹ = (x * l) * l⁻¹ := by rw [hc]
                _ = x := by group
            rw [this]
          · by_cases hb : ⁅l * x * l⁻¹, s⁆ = 1
            · have hxCl' := hker _ hx'W hb
              have hc := mem_centralizer_iff.mp hxCl'.2 l⁻¹ (L.inv_mem hl)
              have : x = l * x * l⁻¹ := by
                calc x = l⁻¹ * (l * x * l⁻¹) * l := by group
                  _ = ((l * x * l⁻¹) * l⁻¹) * l := by rw [hc]
                  _ = l * x * l⁻¹ := by group
              rw [← this]
            · exact h.Z_eq_of_ne_one (h.mem_Z (hWV hx)) (h.mem_Z (hWV hx'W)) ha hb
        have hmul := h.comm_s_mul (hWV hyW) (hWV hx'W) h.mem
        rw [hyx, hxx'] at hmul
        have h1 : ⁅⁅x, l⁆, s⁆ = 1 := by simpa using hmul.symm
        exact hker _ hyW h1
      have hW'comm : ∀ x ∈ W', ∀ l ∈ L, ⁅x, l⁆ ∈ Cl := by
        intro x hx l hl
        obtain ⟨w, hw, rfl⟩ := (memW' x).mp hx
        have hl' : s⁻¹ * l * s⁻¹⁻¹ ∈ L := conj_mem_of_le_normalizer h.normL (M.inv_mem h.mem) hl
        have hc := hWcomm w hw _ hl'
        have e : ⁅s * w * s⁻¹, l⁆ = s * ⁅w, s⁻¹ * l * s⁻¹⁻¹⁆ * s⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e, hClfix _ hc]; exact hc
      have hQcomm : ∀ q ∈ W ⊔ W', ∀ l ∈ L, ⁅q, l⁆ ∈ Cl := by
        intro q hq l hl
        have hle : W ≤ normalizer (W' : Set G) := le_normalizer_of_conj_mem fun w hw x hx => by
          have : w * x * w⁻¹ = x := by
            calc w * x * w⁻¹ = (x * w) * w⁻¹ := by rw [h.comm w (hWV hw) x (hW'V hx)]
              _ = x := by group
          rw [this]; exact hx
        have hco := Subgroup.coe_mul_of_left_le_normalizer_right W W' hle
        have hq' : q ∈ ((W ⊔ W' : Subgroup G) : Set G) := hq
        rw [hco] at hq'
        obtain ⟨w, hw, w', hw', rfl⟩ := hq'
        rw [h.comm_mul_l]
        have h1 := hWcomm w hw l hl
        have h2 := hW'comm w' hw' l hl
        have hVc : ⁅w', l⁆ ∈ V := h.U_le_V h2.1
        have : w * ⁅w', l⁆ * w⁻¹ = ⁅w', l⁆ := by
          calc w * ⁅w', l⁆ * w⁻¹ = (⁅w', l⁆ * w) * w⁻¹ := by rw [h.comm w (hWV hw) _ hVc]
            _ = ⁅w', l⁆ := by group
        rw [this]; exact Cl.mul_mem h2 h1
      have hUQ' : ⁅U, L⁆ ≤ Cl := commutator_le.mpr fun u hu l hl => hQcomm u (hQ hu) l hl
      exact absurd (h.comm_comm_ge.trans hUQ') (not_le_of_gt h.Cl_lt)

end Setting


section Bridge

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock blockV)
open CFSG.QuasithinUnique
open CFSG.Open (pCoreOf)
open CFSG.Quasithin (autOn)
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (sup_le_normalizer_blockV le_normalizer_of_isWeakSBlock not_le_centralizer_blockV
    isQuasisimple_autOn quasithinGenFitting_autOn_sup)

theorem le_of_mem_normal {Ω : Type*} [Group Ω] {H K N : Subgroup Ω} {t : Ω}
    (hKH : K ≤ H) (hNH : N ≤ H)
    (hKn : ∀ x ∈ H, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hNn : ∀ x ∈ H, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hq : CFSG.IsQuasisimple ↥K) (hcent : H ⊓ centralizer (K : Set Ω) ≤ K)
    (htN : t ∈ N) (htK : t ∉ K) : K ≤ N := by
  have hKK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  have hcomm : _root_.commutator ↥K = ⊤ := hq.1.commutator_eq_top
  let N' : Subgroup ↥K := N.subgroupOf K
  have hN' : N'.Normal := ⟨fun n hn k => by
    show ((k * n * k⁻¹ : ↥K) : Ω) ∈ N
    exact hNn k (hKH k.2) n hn⟩
  rcases CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.normal_le_center_or_eq_top
    hcomm hq.2.1 N' hN' with hc | htop
  · exfalso
    have hNK : ⁅N, K⁆ ≤ N ⊓ K := commutator_le.mpr fun n hn k hk => by
      refine ⟨?_, ?_⟩
      · have e : ⁅n, k⁆ = n * (k * n⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem hn (hNn k (hKH hk) n⁻¹ (N.inv_mem hn))
      · have e : ⁅n, k⁆ = (n * k * n⁻¹) * k⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact K.mul_mem (hKn n (hNH hn) k hk) (K.inv_mem hk)
    have hWbot : ⁅⁅N, K⁆, K⁆ = ⊥ := by
      refine eq_bot_iff.mpr (commutator_le.mpr fun x hx k hk => ?_)
      have hx' := hNK hx
      have hxc := hc (show (⟨x, hx'.2⟩ : ↥K) ∈ N' from hx'.1)
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨k, hk⟩)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact this.symm
    have hNc : N ≤ centralizer (K : Set Ω) :=
      CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.le_centralizer_of_commutator_commutator_eq_bot
        hKK hWbot
    exact htK (hcent ⟨hNH htN, hNc htN⟩)
  · intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ N' := by rw [htop]; trivial
    exact this

theorem setting_of {G : Type} [Group G] [Finite G] {X S L : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) {s : G}
    (hsS : s ∈ S) (hgen : S ≤ zpowers s ⊔ (L ⊔ S) ⊓ centralizer (blockV S L : Set G))
    (hsn : s ∉ L ⊔ (L ⊔ S) ⊓ centralizer (blockV S L : Set G))
    (hZ : Nat.card ↥⁅blockV S L, zpowers s⁆ = 2) :
    Setting (L ⊔ S) L (blockV S L) s := by
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hMV := sup_le_normalizer_blockV S L
  have hsM : s ∈ L ⊔ S := Subgroup.mem_sup_right hsS
  have hq := isQuasisimple_autOn hA hL hSL
  have hFit := quasithinGenFitting_autOn_sup hA hL hSL
  have hnotCent := not_le_centralizer_blockV hA hL hSL
  have hcomm : ∀ v ∈ blockV S L, ∀ w ∈ blockV S L, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val
      ((CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))).1.is_comm.comm
        ⟨v, hv⟩ ⟨w, hw⟩)
  set V := blockV S L with hV
  set M := L ⊔ S with hM
  let ρ := Setup.rho V M hMV
  have hρ1 : ∀ a b : M, ρ a = ρ b → (a : G)⁻¹ * b ∈ M ⊓ centralizer (V : Set G) := by
    intro a b hab
    have : ρ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    exact ⟨(a⁻¹ * b).2, (Setup.rho_eq_one_iff hMV _).mp this⟩
  have hK : autOn L V = (L.subgroupOf M).map ρ := by
    ext x
    rw [Setup.mem_autOn_iff_rho hMV le_sup_left, Subgroup.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  have hperfK : ⁅autOn L V, autOn L V⁆ = autOn L V := Subgroup.isPerfect_iff.mp hq.1
  refine ⟨hMV, hcomm, sup_le Subgroup.le_normalizer hSL, le_sup_left, hsM, hZ, ?_,
    hnotCent, ?_, ?_⟩
  · exact sup_le (le_sup_left.trans le_sup_left)
      (hgen.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  · intro l hl
    have hmem : ρ ⟨l, Subgroup.mem_sup_left hl⟩ ∈ autOn L V :=
      (Setup.mem_autOn_iff_rho hMV le_sup_left).mpr ⟨⟨l, Subgroup.mem_sup_left hl⟩, hl, rfl⟩
    rw [← hperfK, hK, ← Subgroup.map_commutator] at hmem
    obtain ⟨a, ha, hρa⟩ := hmem
    have hsub : ⁅L.subgroupOf M, L.subgroupOf M⁆ ≤ (⁅L, L⁆ : Subgroup G).subgroupOf M :=
      commutator_le.mpr fun p hp q hq' => by
        show ((⁅p, q⁆ : M) : G) ∈ ⁅L, L⁆
        have : ((⁅p, q⁆ : M) : G) = ⁅(p : G), (q : G)⁆ := rfl
        rw [this]
        exact commutator_mem_commutator hp hq'
    have haL : (a : G) ∈ ⁅L, L⁆ := hsub ha
    have h2 := hρ1 a _ hρa
    have e : l = (a : G) * ((a : G)⁻¹ * l) := by group
    rw [e]
    exact Subgroup.mul_mem_sup haL h2
  · intro T hTM hMT hCT hsT
    have hcent : autOn M V ⊓ centralizer (autOn L V : Set (MulAut V)) ≤ autOn L V := by
      have := CFSG.Quasithin.centralizer_quasithinGenFitting_le (autOn M V)
      rwa [hFit] at this
    have htN : ρ ⟨s, hsM⟩ ∈ autOn T V :=
      (Setup.mem_autOn_iff_rho hMV hTM).mpr ⟨⟨s, hsM⟩, hsT, rfl⟩
    have htK : ρ ⟨s, hsM⟩ ∉ autOn L V := by
      intro hk
      obtain ⟨p, hpL, hρ⟩ := (Setup.mem_autOn_iff_rho hMV le_sup_left).mp hk
      have h2 := hρ1 p _ hρ
      apply hsn
      have e : s = (p : G) * ((p : G)⁻¹ * s) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hpL h2
    have hle := le_of_mem_normal (H := autOn M V) (K := autOn L V) (N := autOn T V)
      (CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le le_sup_left) (CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le hTM)
      (CFSG.Quasithin.InternalSec.autOn_normal_of (sup_le Subgroup.le_normalizer hSL))
      (CFSG.Quasithin.InternalSec.autOn_normal_of hMT) hq hcent htN htK
    intro l hl
    have hmem := hle ((Setup.mem_autOn_iff_rho hMV le_sup_left).mpr ⟨⟨l, Subgroup.mem_sup_left hl⟩, hl, rfl⟩)
    obtain ⟨p, hpT, hρ⟩ := (Setup.mem_autOn_iff_rho hMV hTM).mp hmem
    have h2 := hρ1 p _ hρ
    have e : l = (p : G) * ((p : G)⁻¹ * l) := by group
    rw [e]
    exact T.mul_mem hpT (hCT h2)

end Bridge

end TransvIrr

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock blockV HasIrreducibleCommutatorQuotient)

theorem hasIrreducibleCommutatorQuotient_of_transvectionData
    {G : Type} [Group G] [Finite G] {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) (ht : TransvectionData S L) :
    HasIrreducibleCommutatorQuotient L (blockV S L) := by
  obtain ⟨s, hsS, hgen, hsn, hZ⟩ := ht
  have hset := TransvIrr.setting_of hX hA hL hsS hgen hsn hZ
  exact ⟨hset.Cl_lt, fun W h1 h2 h3 => hset.irred h1 h2 h3⟩

end CFSG.HardMathSupport.Cooperstein.StructureLie
