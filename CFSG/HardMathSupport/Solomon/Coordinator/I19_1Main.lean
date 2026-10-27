module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Aut
public import CFSG.HardMathSupport.Timmesfeld.Proving.MapGLAPPrimeCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Balance

open scoped commutatorElement

theorem h1Stmt_zero : H1Stmt.{0} := by
  intro X Z _ _ _ φ hφ p hp Q hQ
  exact CFSG.HardMathSupport.Timmesfeld.Proving.map_glaPPrimeCoreOf_centralizer_le φ hφ hp hQ

section General

variable {G : Type} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem conj_mem_centralizer_singleton {g b x : G} (hg : g * b = b * g)
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have hgi : g⁻¹ * b = b * g⁻¹ := (Commute.inv_left (show Commute g b from hg)).eq
  calc (g * x * g⁻¹) * b = g * x * (g⁻¹ * b) := by group
    _ = g * x * (b * g⁻¹) := by rw [hgi]
    _ = g * (x * b) * g⁻¹ := by group
    _ = g * (b * x) * g⁻¹ := by rw [hx]
    _ = (g * b) * x * g⁻¹ := by group
    _ = (b * g) * x * g⁻¹ := by rw [hg]
    _ = b * (g * x * g⁻¹) := by group

omit [Finite G] in
theorem mem_normalizer_inf {A C : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hC : g ∈ Subgroup.normalizer (C : Set G)) : g ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  show x ∈ A ⊓ C ↔ g * x * g⁻¹ ∈ A ⊓ C
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.1 hA x,
    Subgroup.mem_normalizer_iff.1 hC x]

theorem le_normalizer_delta_inf {B D : Subgroup G} (hB : IsElemAbelian p B) (hDB : D ≤ B) {b : G}
    (hb : ∀ g ∈ B, g * b = b * g) :
    B ≤ Subgroup.normalizer ((GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) :
      Set G) := fun g hg =>
  mem_normalizer_inf (le_normalizer_gLADelta hB hDB hg)
    (Subgroup.mem_normalizer_fintype fun x (hx : x ∈ Subgroup.centralizer ({b} : Set G)) =>
      conj_mem_centralizer_singleton (hb g hg) hx)

theorem mem_normalizer_commutator {T B : Subgroup G} {g : G} (hgB : g ∈ B)
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) :
    g ∈ Subgroup.normalizer ((⁅T, B⁆ : Subgroup G) : Set G) := by
  have key : (⁅T, B⁆ : Subgroup G) ≤ (⁅T, B⁆ : Subgroup G).comap (MulAut.conj g).toMonoidHom := by
    refine Subgroup.commutator_le.2 fun t ht β hβ => ?_
    show g * ⁅t, β⁆ * g⁻¹ ∈ (⁅T, B⁆ : Subgroup G)
    have e : g * ⁅t, β⁆ * g⁻¹ = ⁅g * t * g⁻¹, g * β * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 hgT t).1 ht)
      (B.mul_mem (B.mul_mem hgB hβ) (B.inv_mem hgB))
  exact Subgroup.mem_normalizer_fintype fun n (hn : n ∈ (⁅T, B⁆ : Subgroup G)) => key hn

omit [Finite G] in
theorem elemAbelian_commute {B : Subgroup G} (hB : IsElemAbelian p B) {a b : G} (ha : a ∈ B)
    (hb : b ∈ B) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hB ha hb

omit [Finite G] in
theorem ne_bot_of_card {D : Subgroup G} {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (hcard : Nat.card D = p ^ k) : D ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card D = 1 := by rw [hbot]; exact Subgroup.card_bot
  have : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
  omega

omit [Finite G] in
theorem autBar_mono {B D L : Subgroup G} (hDB : D ≤ B) : autBar p D L ≤ autBar p B L := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, (Subgroup.mem_subgroupOf).2 (inf_le_inf_right _ hDB ((Subgroup.mem_subgroupOf).1 hx)), rfl⟩

theorem delta_normalizes_and_not_balanced (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) {D : Subgroup G}
    (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ k) {b : G}
    (hb : b ∈ Subgroup.centralizer (D : Set G)) :
    (∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
      GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
      ¬ ⁅L, GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤
          GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) →
        D ≤ Subgroup.normalizer (L : Set G) ∧ ¬ IsCompLocallyBalanced p k D L := by
  have hDb : ∀ g ∈ D, g * b = b * g := fun g hg => (Subgroup.mem_centralizer_iff.1 hb g hg)
  have hDX : D ≤ Subgroup.centralizer ({b} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (hDb g hg)
  have h : InDelta p (Subgroup.centralizer ({b} : Set G)) D
      (GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)) :=
    InDelta.of_le_gLADelta hp hDX hD (ne_bot_of_card hp hk hcard) inf_le_right inf_le_left
  have hDS := le_normalizer_delta_inf hD le_rfl hDb
  refine ⟨fun L hL => (h.main h1Stmt_zero hp hL).1, fun L hL hn => ?_⟩
  obtain ⟨hDN, -, -, -, hnb⟩ := h.conclusions h1Stmt_zero hp hL hcard hDS hn
  exact ⟨hDN, hnb⟩

theorem delta_conclusions (hp : p.Prime) {D : Subgroup G} (hD : IsElemAbelian p D) (hD1 : D ≠ ⊥)
    {b : G} (hb : b ∈ Subgroup.centralizer (D : Set G)) :
    (∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
      GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
      ¬ ⁅L, GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤
          GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) →
        kerB p D L = ⊥ ∧ D ≤ Subgroup.normalizer (L : Set G) ∧
          ((((GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf
                (Subgroup.normalizer (L : Set G))).map (barAut p L)) ≤
            localDeltaIn p
              ((((GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)) ⊔ L).subgroupOf
                (Subgroup.normalizer (L : Set G))).map (barAut p L))
              ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L))) := by
  have hDX : D ≤ Subgroup.centralizer ({b} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hb g hg)
  have h : InDelta p (Subgroup.centralizer ({b} : Set G)) D
      (GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)) :=
    InDelta.of_le_gLADelta hp hDX hD hD1 inf_le_right inf_le_left
  refine ⟨fun L hL => (h.main h1Stmt_zero hp hL).1, fun L hL hn => ?_⟩
  obtain ⟨-, hDN, hker, -, hle⟩ := h.conclusions_nocard h1Stmt_zero hp hL hn
  exact ⟨hker, hDN, hle⟩

theorem commutator_le_of_isCompLocallyBalanced (hp : p.Prime) {B : Subgroup G}
    (hB : IsElemAbelian p B) {k : ℕ} (hk : 1 ≤ k) {D : Subgroup G} (hD : IsEkIn p k B D) {b : G}
    (hbB : b ∈ B) {L : Subgroup G} (hL : GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L)
    (hbal : IsCompLocallyBalanced p k B L) :
    ⁅L, GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ GLAPPrimeCoreOf p L := by
  have hBb : ∀ g ∈ B, g * b = b * g := fun g hg => elemAbelian_commute hB hg hbB
  have hDX : D ≤ Subgroup.centralizer ({b} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (hBb g (hD.1 hg))
  have h : InDelta p (Subgroup.centralizer ({b} : Set G)) D
      (GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)) :=
    InDelta.of_le_gLADelta hp hDX hD.2.1 (ne_bot_of_card hp hk hD.2.2) inf_le_right inf_le_left
  have hDS := le_normalizer_delta_inf hB hD.1 hBb
  obtain ⟨hSN, -⟩ := h.main h1Stmt_zero hp hL
  have hcore : ⁅L, GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) := by
    by_contra hn
    obtain ⟨-, -, -, -, hnb⟩ := h.conclusions h1Stmt_zero hp hL hD.2.2 (fun g hg => hDS (hD.1 hg)) hn
    exact hnb (isLocallyBalanced_mono p k (autBar_mono hD.1) hbal)
  refine Subgroup.commutator_le.2 fun x hx s hs => ?_
  have hxs : x * s * x⁻¹ * s⁻¹ ∈ L := by
    have h1 : s * x⁻¹ * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hSN hs) x⁻¹).1 (L.inv_mem hx)
    have := L.mul_mem hx h1
    simpa [mul_assoc] using this
  have h2 : x * s * x⁻¹ * s⁻¹ ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) := by
    rw [← commutatorElement_def]
    exact hcore (Subgroup.commutator_mem_commutator hx hs)
  rw [commutatorElement_def]
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL.2.1]
  exact ⟨hxs, h2⟩

theorem delta2At_conclusions (hp : p.Prime) {B : Subgroup G} (hB : IsElemAbelian p B) {k : ℕ}
    (hk : 1 ≤ k) {D : Subgroup G} (hD : IsEkIn p k B D) {b : G} (hbB : b ∈ B)
    (hweak : ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
      IsCompWeaklyLocallyBalanced p k B L) :
    (⁅oPrimePOf p (Subgroup.centralizer ({b} : Set G)), delta2At p B D b⁆ ≤
        GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) ∧
      ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
        delta2At p B D b ≤ Subgroup.normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
      ¬ ⁅L, delta2At p B D b⁆ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) →
        ¬ IsCompLocallyBalanced p k B L ∧ kerB p D L = ⊥ ∧
          ¬ B ≤ Subgroup.normalizer (L : Set G) ∧ D ≤ Subgroup.normalizer (L : Set G) ∧
          (((delta2At p B D b).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≠ ⊥ ∧
            ((delta2At p B D b).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≤
              localDeltaIn p
                (((delta2At p B D b ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map
                  (barAut p L))
                ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L))) := by
  have hBb : ∀ g ∈ B, g * b = b * g := fun g hg => elemAbelian_commute hB hg hbB
  have hBX : B ≤ Subgroup.centralizer ({b} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (hBb g hg)
  have hD1 := ne_bot_of_card hp hk hD.2.2
  have hDX : D ≤ Subgroup.centralizer ({b} : Set G) := hD.1.trans hBX
  have hTX : GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    inf_le_right
  have hWX : delta2At p B D b ≤ Subgroup.centralizer ({b} : Set G) :=
    commutator_le_of_le' hTX hBX
  have hIW : InDelta p (Subgroup.centralizer ({b} : Set G)) D (delta2At p B D b) :=
    InDelta.of_le_gLADelta hp hDX hD.2.1 hD1 hWX (delta2At_le_gLADelta hB hD.1 b)
  have hIT : InDelta p (Subgroup.centralizer ({b} : Set G)) D
      (GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)) :=
    InDelta.of_le_gLADelta hp hDX hD.2.1 hD1 hTX inf_le_left
  have hBT := le_normalizer_delta_inf hB hD.1 hBb
  have hDW : D ≤ Subgroup.normalizer ((delta2At p B D b : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_commutator (hD.1 hg) (hBT (hD.1 hg))
  refine ⟨⟨hIW.commutator_oPrimePOf_le h1Stmt_zero hp, fun L hL =>
    (hIW.main h1Stmt_zero hp hL).1⟩, fun L hL hn => ?_⟩
  obtain ⟨hDN, hker, hne, hle, hnb⟩ := hIW.conclusions h1Stmt_zero hp hL hD.2.2 hDW hn
  refine ⟨fun hbal => hnb (isLocallyBalanced_mono p k (autBar_mono hD.1) hbal), hker, ?_, hDN,
    hne, hle⟩
  intro hBN
  have hTN := (hIT.main h1Stmt_zero hp hL).1
  have hleT := hIT.map_le_localDeltaIn h1Stmt_zero hp hL.1 hTN hDN
  have hA : autBar p B L = (B.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) := by
    unfold autBar
    rw [inf_eq_left.2 hBN]
  have hE : IsEkIn p k (autBar p B L)
      ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L)) := by
    refine ⟨?_, isElemAbelian_map (isElemAbelian_subgroupOf hD.2.1) _,
      (card_map_barAut hDN hker).trans hD.2.2⟩
    rw [hA]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, (Subgroup.mem_subgroupOf).2 (hD.1 ((Subgroup.mem_subgroupOf).1 hx)), rfl⟩
  have hnorm := map_subgroupOf_le_normalizer_map (p := p) (S := GLADelta p D ⊓
    Subgroup.centralizer ({b} : Set G)) hBT hBN
  have hcomm := hweak L hL _ hE _ innerAut_le_map (hA ▸ hnorm)
  apply hn
  have hWK : delta2At p B D b ≤ centralizerQuot L (GLAPPrimeCoreOf p L) := by
    refine Subgroup.commutator_le.2 fun t ht β hβ => ?_
    have htN := hTN ht
    have hβN := hBN hβ
    have hcN : ⁅t, β⁆ ∈ Subgroup.normalizer (L : Set G) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem htN hβN) (inv_mem htN)) (inv_mem hβN)
    refine (mem_centralizerQuot_iff_barAut_eq_one p ⟨⁅t, β⁆, hcN⟩).2 ?_
    have e : (⟨⁅t, β⁆, hcN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⁅(⟨t, htN⟩ : ↥(Subgroup.normalizer (L : Set G))), ⟨β, hβN⟩⁆ := rfl
    rw [e, map_commutatorElement]
    have hmem := Subgroup.commutator_mem_commutator
      (hleT ⟨⟨t, htN⟩, (Subgroup.mem_subgroupOf).2 ht, rfl⟩)
      (show barAut p L ⟨β, hβN⟩ ∈ autBar p B L from
        ⟨⟨β, hβN⟩, (Subgroup.mem_subgroupOf).2 ⟨hβ, hβN⟩, rfl⟩)
    rw [hcomm] at hmem
    exact hmem
  refine Subgroup.commutator_le.2 fun x hx w hw => ?_
  obtain ⟨-, -, hc⟩ := hWK hw
  exact glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1 (hc x hx)

end General

end CFSG.HardMathSupport.Solomon.Coordinator
