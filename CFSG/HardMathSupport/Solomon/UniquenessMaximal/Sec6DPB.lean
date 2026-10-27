module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DPB1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DK0
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DP4

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure RData (X B K : Subgroup G) (y : G) (R : Subgroup G) : Prop where
  R_le : R ≤ bClosure B K
  R_p : IsPGroup 3 ↥R
  R_card : Nat.card R = 3 ^ (Nat.card ↥(bClosure B K)).factorization 3
  R_inv : B ≤ Subgroup.normalizer (R : Set G)
  c1 : Nat.card ↥(R ⊓ K) = 3 ^ (Nat.card K).factorization 3
  heis : IsThreeOnePlusTwo (R ⊓ K)
  hc1 : barCenterX 3 X (R ⊓ K) = barCenterX 3 X K
  triple : Triple y⁻¹ (R ⊓ K)
  Rdef : Triple.R y⁻¹ (R ⊓ K) = R
  Wdef : Triple.W y⁻¹ (R ⊓ K) = Zc R
  W_card : Nat.card (Triple.W y⁻¹ (R ⊓ K)) ≤ 9
  W_bar : ∀ w ∈ Zc R, ∀ k ∈ bClosure B K, k * w * k⁻¹ * w⁻¹ ∈ GLAPPrimeCoreOf 3 X

section PhaseB

variable {X B K : Subgroup G} {y : G}

theorem exists_rData (hB : IsElemAbelian 3 B) (hBX : B ≤ X) (hK : GLAPComponent 3 X K)
    (hy : y ∈ B) (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3)
    (hZ : Nat.card ↥(barCenterX 3 X (bClosure B K)) ≤ 9)
    (hR4 : ∀ R : Subgroup G, R ≤ K → IsPGroup 3 ↥R →
      (∀ S : Subgroup G, S ≤ K → IsPGroup 3 ↥S → R ≤ S → S = R) →
        IsThreeOnePlusTwo R ∧ barCenterX 3 X R = barCenterX 3 X K) :
    ∃ R : Subgroup G, RData X B K y R := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 ↥B := isPGroup_of_isElemAbelian hB
  obtain ⟨R, hRle, hRp, hRc, hRB⟩ := exists_invariant_sylow (p := 3) hBp
    (le_normalizer_bClosure B K)
  obtain ⟨c1, c2, c3, cm12, cm13, cm23, hdec⟩ :=
    phase1_sylow hB hBX hK hy hyN h3 hRle hRp hRc hRB
  obtain ⟨hne1, hne2, hne3, -⟩ := three_conjugates hB hy hyN h3
  obtain ⟨hK2, hK3⟩ := phase1_comps hK hBX hy
  have hyR : y ∈ Subgroup.normalizer (R : Set G) := hRB hy
  have hcj2 : cj y⁻¹ (R ⊓ K) = R ⊓ GLBConj y K := cj_inv_inf hyR
  have hcj3 : cj y⁻¹ (R ⊓ GLBConj y K) = R ⊓ GLBConj y (GLBConj y K) := cj_inv_inf hyR
  have hmax : ∀ S : Subgroup G, S ≤ K → IsPGroup 3 ↥S → R ⊓ K ≤ S → S = R ⊓ K := by
    intro S hSK hSp hRS
    exact (eq_of_le_sylow hRS hSK hSp c1).symm
  obtain ⟨hheis, hc1⟩ := hR4 (R ⊓ K) inf_le_right (hRp.to_inf_left) hmax
  have hy3 : y ^ 3 = 1 := hB.2 y hy
  have htriple : Triple y⁻¹ (R ⊓ K) :=
    ⟨hheis, by rw [inv_pow, hy3, inv_one], by
      intro r hr s hs
      rw [hcj2] at hs
      exact cm12 r hr s hs⟩
  have hRdef : Triple.R y⁻¹ (R ⊓ K) = R := by
    unfold Triple.R
    rw [hcj2, hcj3]
    exact hdec.symm
  have hWdef : Triple.W y⁻¹ (R ⊓ K) = Zc R := by
    have := htriple.Zc_R
    rw [hRdef] at this
    exact this.symm
  have hW₀ : Triple.W y⁻¹ (R ⊓ K) =
      Zc (R ⊓ K) ⊔ Zc (R ⊓ GLBConj y K) ⊔ Zc (R ⊓ GLBConj y (GLBConj y K)) := by
    unfold Triple.W
    rw [hcj2, hcj3]
  have hyX : y ∈ X := hBX hy
  have hRy : GLBConj y R = R := gLBConj_eq_of_mem_normalizer hyR
  have hinf2 : R ⊓ GLBConj y K = GLBConj y (R ⊓ K) := by
    rw [gLBConj_inf, hRy]
  have hinf3 : R ⊓ GLBConj y (GLBConj y K) = GLBConj y (R ⊓ GLBConj y K) := by
    rw [gLBConj_inf, hRy]
  have hc2 : barCenterX 3 X (R ⊓ GLBConj y K) = barCenterX 3 X (GLBConj y K) := by
    rw [hinf2, barCenterX_gLBConj 3 hyX (R ⊓ K), hc1]
    exact (barCenterX_gLBConj 3 hyX K).symm
  have hc3 : barCenterX 3 X (R ⊓ GLBConj y (GLBConj y K)) =
      barCenterX 3 X (GLBConj y (GLBConj y K)) := by
    rw [hinf3, barCenterX_gLBConj 3 hyX (R ⊓ GLBConj y K), hc2]
    exact (barCenterX_gLBConj 3 hyX (GLBConj y K)).symm
  have hW9 := card_W_le hB hBX hK hy hyN h3 hRle hRp hc1 hc2 hc3 hZ
  have hbar := barX_W_le_center hB hBX hK hy hyN h3 hRle hRp hc1 hc2 hc3
  refine ⟨R, ⟨hRle, hRp, hRc, hRB, c1, hheis, hc1, htriple, hRdef, hWdef, ?_, ?_⟩⟩
  · rw [hW₀]; exact hW9
  · intro w hw k hk
    have hwW : w ∈ Triple.W y⁻¹ (R ⊓ K) := by rw [hWdef]; exact hw
    rw [hW₀] at hwW
    have hz1 : Zc (R ⊓ K) ≤ X := (Zc_le _).trans (inf_le_right.trans hK.1)
    have hz2 : Zc (R ⊓ GLBConj y K) ≤ X := (Zc_le _).trans (inf_le_right.trans hK2.1)
    have hz3 : Zc (R ⊓ GLBConj y (GLBConj y K)) ≤ X := (Zc_le _).trans (inf_le_right.trans hK3.1)
    have hwX : w ∈ X := sup_le (sup_le hz1 hz2) hz3 hwW
    have hkX : k ∈ X := by
      have : bClosure B K ≤ X := by
        rw [bClosure_eq_three hB hy hyN h3]
        exact sup_le (sup_le hK.1 hK2.1) hK3.1
      exact this hk
    have hwb : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨w, hwX⟩ ∈ barCenterX 3 X (bClosure B K) :=
      hbar (mem_barX_iff.2 ⟨⟨w, hwX⟩, hwW, rfl⟩)
    have hkb : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨k, hkX⟩ ∈ barX 3 X (bClosure B K) :=
      mem_barX_iff.2 ⟨⟨k, hkX⟩, hk, rfl⟩
    have hcomm := ((mem_barCenterX_iff).1 hwb).2 _ hkb
    have hone : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨k, hkX⟩ * ⟨w, hwX⟩ * ⟨k, hkX⟩⁻¹ *
        ⟨w, hwX⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact commutatorElement_eq_one_iff_mul_comm.2 hcomm.symm
    have := (mem_coreOf_iff (p := 3) (X := X)
      (⟨k, hkX⟩ * ⟨w, hwX⟩ * ⟨k, hkX⟩⁻¹ * ⟨w, hwX⟩⁻¹)).2 ((QuotientGroup.eq_one_iff _).1 (by exact hone))
    exact this

omit [Finite G] in
theorem card_zpowers_sup {x y : G} (hxy : x * y = y * x) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : Subgroup.zpowers x ≠ Subgroup.zpowers y) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
  have cx : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have cy : Nat.card ↥(Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
  have hI := inf_eq_bot_of_card_three cx cy hne
  have hN : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    exact (zpowers_le_cent_zpowers hxy.symm).trans (Subgroup.centralizer_le_normalizer _)
  have h := card_sup_mul_card_inf hN
  rw [hI, Subgroup.card_bot, cx, cy] at h
  omega

structure K0Data (B K : Subgroup G) (x y : G) (K₀ : Subgroup G) : Prop where
  comp : GLAPComponent 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G)) K₀
  le : K₀ ≤ bClosure B K ⊓ Subgroup.centralizer ({y} : Set G)
  B_inv : B ≤ Subgroup.normalizer (K₀ : Set G)
  E9 : ∃ E : Subgroup G, E ≤ K₀ ∧ IsElemAbelian 3 E ∧ Nat.card E = 9
  cq : B ⊓ LocalBalance.centralizerQuot K₀ (GLAPPrimeCoreOf 3 K₀) = Subgroup.zpowers x ⊔ Subgroup.zpowers y
  ne : B ⊓ K₀ ≠ ⊥
  inf_cq : (B ⊓ K₀) ⊓ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = ⊥

omit [Finite G] in
theorem gLBConj_centralizer_of_comm {b y : G} (hby : b * y = y * b) :
    GLBConj b (Subgroup.centralizer ({y} : Set G)) = Subgroup.centralizer ({y} : Set G) := by
  ext z
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : b * z * b⁻¹ * y = y * (b * z * b⁻¹) := h
    have e : b * (z * y) * b⁻¹ = b * (y * z) * b⁻¹ := by
      calc b * (z * y) * b⁻¹ = b * z * b⁻¹ * (b * y * b⁻¹) := by group
        _ = b * z * b⁻¹ * y := by rw [hby]; group
        _ = y * (b * z * b⁻¹) := h1
        _ = b * y * b⁻¹ * (b * z * b⁻¹) := by rw [hby]; group
        _ = b * (y * z) * b⁻¹ := by group
    simpa using e
  · intro h
    have e : b * z * b⁻¹ * y = y * (b * z * b⁻¹) := by
      calc b * z * b⁻¹ * y = b * (z * (b⁻¹ * y * b)) * b⁻¹ := by group
        _ = b * (z * y) * b⁻¹ := by
          have : b⁻¹ * y * b = y := by
            calc b⁻¹ * y * b = b⁻¹ * (y * b) := by group
              _ = b⁻¹ * (b * y) := by rw [← hby]
              _ = y := by group
          rw [this]
        _ = b * (y * z) * b⁻¹ := by rw [h]
        _ = y * (b * z * b⁻¹) := by
          calc b * (y * z) * b⁻¹ = (b * y * b⁻¹) * (b * z * b⁻¹) := by group
            _ = y * (b * z * b⁻¹) := by rw [hby]; group
    exact e

theorem mem_normalizer_of_le_centralizer {x : G} {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({x} : Set G)) : x ∈ Subgroup.normalizer (K : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  have h := Subgroup.mem_centralizer_singleton_iff.1 (hK hn)
  have : x * n * x⁻¹ = n := by
    calc x * n * x⁻¹ = n * x * x⁻¹ := by rw [← h]
      _ = n := by group
  rw [this]; exact hn

omit [Finite G] in
theorem layer_gLBConj (p : ℕ) (g : G) (X : Subgroup G) :
    GLAPLayer p (GLBConj g X) = GLBConj g (GLAPLayer p X) := by
  refine gLBConj_eq_of_forall_ge (F := GLAPLayer p) (fun g X => ?_) g X
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (glaPComponent_gLBConj hL g)

theorem bClosure_le_of_comp (hB : IsElemAbelian 3 B) (hBX : B ≤ X) (hK : GLAPComponent 3 X K)
    (hy : y ∈ B) (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3) : bClosure B K ≤ X := by
  obtain ⟨hK2, hK3⟩ := phase1_comps hK hBX hy
  rw [bClosure_eq_three hB hy hyN h3]
  exact sup_le (sup_le hK.1 hK2.1) hK3.1

theorem exists_k0Data {x : G} (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 81)
    (hSC : IsSCp 3 ⊤ B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hK : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K)
    (hy : y ∈ B) (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3) {R : Subgroup G}
    (hR : RData (Subgroup.centralizer ({x} : Set G)) B K y R)
    (hiso : Nonempty (↥(GLAPLayer 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G))) ⧸
        GLAPPrimeCore 3 ↥(GLAPLayer 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G))) ≃*
        (↥(barX 3 (Subgroup.centralizer ({x} : Set G)) K) ⧸
          Subgroup.center ↥(barX 3 (Subgroup.centralizer ({x} : Set G)) K))))
    (hcomp0 : GLAPComponent 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G))
      (GLAPLayer 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G)))) :
    K0Data B K x y (GLAPLayer 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G))) := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 ↥B := isPGroup_of_isElemAbelian hB
  set X := Subgroup.centralizer ({x} : Set G) with hX
  set K₀ := GLAPLayer 3 (bClosure B K ⊓ Subgroup.centralizer ({y} : Set G)) with hK₀
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => elemAbelian_comm hB ha hb
  have hBX : B ≤ X := fun b hb => by
    rw [hX, Subgroup.mem_centralizer_singleton_iff]; exact hcomm b hb x hxB
  have hle : K₀ ≤ bClosure B K ⊓ Subgroup.centralizer ({y} : Set G) :=
    sSup_le fun L hL => hL.1
  have hK₀B : B ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro b hb
    rw [mem_normalizer_iff_gLBConj_eq, hK₀, ← layer_gLBConj, gLBConj_inf, bClosure_conj_eq hb,
      gLBConj_centralizer_of_comm (hcomm b hb y hy)]
  obtain ⟨S₀, hS₀K, hS₀p, hS₀c, hS₀B⟩ := exists_invariant_sylow (p := 3) hBp hK₀B
  obtain ⟨φ⟩ := hiso
  obtain ⟨hS9, hSel⟩ := k0_sylow_facts hK hR.heis inf_le_right hR.c1 hR.hc1 φ hS₀K hS₀p hS₀c
  obtain ⟨hcard, hne, hinf⟩ := card_centralizerQuot_le hB hBc hSC hK₀B hS₀B hS₀K hSel hS₀c
    (by rw [hS9]; norm_num) (fun g hg hc => k0_centreless hK φ hg hc)
  have hKX := bClosure_le_of_comp hB hBX hK hy hyN h3
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_le_centralizer hK.1
  have hxy : x * y = y * x := hcomm x hxB y hy
  have hx3 := hB.2 x hxB
  have hy3 := hB.2 y hy
  have hy1 : y ≠ 1 := fun h => hyN (h ▸ Subgroup.one_mem _)
  have hne' : Subgroup.zpowers x ≠ Subgroup.zpowers y := by
    intro h
    apply hyN
    have : y ∈ Subgroup.zpowers x := h ▸ Subgroup.mem_zpowers y
    exact (Subgroup.zpowers_le.2 hxN) this
  have h9 := card_zpowers_sup hxy hx3 hy3 hx1 hy1 hne'
  have hmemcq : ∀ g ∈ B, (∀ k ∈ K₀, k * g * k⁻¹ * g⁻¹ = 1) →
      g ∈ B ⊓ LocalBalance.centralizerQuot K₀ (GLAPPrimeCoreOf 3 K₀) := fun g hg hcg =>
    ⟨hg, hK₀B hg, normalizer_core 3 (hK₀B hg), fun k hk => by
      rw [hcg k hk]; exact Subgroup.one_mem _⟩
  have hxcq := hmemcq x hxB (fun k hk => by
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hKX (hle hk).1)
    calc k * x * k⁻¹ * x⁻¹ = x * k * k⁻¹ * x⁻¹ := by rw [h]
      _ = 1 := by group)
  have hycq := hmemcq y hy (fun k hk => by
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hle hk).2
    calc k * y * k⁻¹ * y⁻¹ = y * k * k⁻¹ * y⁻¹ := by rw [h]
      _ = 1 := by group)
  have hsup : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤
      B ⊓ LocalBalance.centralizerQuot K₀ (GLAPPrimeCoreOf 3 K₀) :=
    sup_le (Subgroup.zpowers_le.2 hxcq) (Subgroup.zpowers_le.2 hycq)
  have hcqeq : B ⊓ LocalBalance.centralizerQuot K₀ (GLAPPrimeCoreOf 3 K₀) =
      Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    (Subgroup.eq_of_le_of_card_ge hsup (by rw [h9]; exact hcard)).symm
  refine ⟨hcomp0, hle, hK₀B, ⟨S₀, hS₀K, hSel, hS9⟩, hcqeq, hne, ?_⟩
  rw [hcqeq] at hinf
  exact hinf

theorem bClosure_le_normalizer (hB : IsElemAbelian 3 B) (hBX : B ≤ X) (hK : GLAPComponent 3 X K)
    (hy : y ∈ B) (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3) :
    bClosure B K ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨hne1, hne2, hne3, -⟩ := three_conjugates hB hy hyN h3
  obtain ⟨hK2, hK3⟩ := phase1_comps hK hBX hy
  rw [bClosure_eq_three hB hy hyN h3]
  exact sup_le (sup_le Subgroup.le_normalizer (le_normalizer_of_ne hK2 hK hne1.symm))
    (le_normalizer_of_ne hK3 hK hne2.symm)

theorem x_mem_W {x : G} (hB : IsElemAbelian 3 B) (hSC : IsSCp 3 ⊤ B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hK : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K)
    (hy : y ∈ B) (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3) {R K₀ : Subgroup G}
    (hR : RData (Subgroup.centralizer ({x} : Set G)) B K y R) (hk : K0Data B K x y K₀) :
    x ∈ Zc R ∧ ∀ z ∈ Zc R, y * z = z * y → z ∈ Subgroup.zpowers x := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 ↥B := isPGroup_of_isElemAbelian hB
  set X := Subgroup.centralizer ({x} : Set G) with hX
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => elemAbelian_comm hB ha hb
  have hBX : B ≤ X := fun b hb => by
    rw [hX, Subgroup.mem_centralizer_singleton_iff]; exact hcomm b hb x hxB
  have hWp : IsPGroup 3 ↥(Zc R) := by
    have := hR.triple.isPGroup_W
    rwa [hR.Wdef] at this
  have hWne : Zc R ≠ ⊥ := by
    intro h0
    have hle : Zc (R ⊓ K) ≤ Zc R := by
      rw [← hR.Wdef]; exact Triple.Zc_le_W₁
    rw [h0, le_bot_iff] at hle
    have := hR.heis.card_Zc
    rw [hle, Subgroup.card_bot] at this
    omega
  have hBnW : B ≤ Subgroup.normalizer (Zc R : Set G) := fun b hb => normalizer_Zc (hR.R_inv hb)
  obtain ⟨w, hwW, hw1, hwc⟩ := exists_fixed_ne_one (p := 3) hBp hBnW hWne hWp
  have hwR : w ∈ Triple.R y⁻¹ (R ⊓ K) := by rw [hR.Rdef]; exact Zc_le _ hwW
  have hw3 : w ^ 3 = 1 := hR.triple.exp3_R hwR
  have hwB : w ∈ B := by
    have hcentr : B ≤ Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact (Commute.zpow_left ((show Commute b w from hwc b hb).symm) m).eq
    have hE : IsElemAbelian 3 (B ⊔ Subgroup.zpowers w) :=
      isElemAbelian_sup_of_commute hB (isElemAbelian_zpowers hw3) hcentr
    have hEB : B ⊔ Subgroup.zpowers w = B := hSC.2.2 _ le_top hE le_sup_left
    rw [← hEB]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hwcq : w ∈ B ⊓ LocalBalance.centralizerQuot K₀ (GLAPPrimeCoreOf 3 K₀) := by
    refine ⟨hwB, hk.B_inv hwB, normalizer_core 3 (hk.B_inv hwB), fun k hk' => ?_⟩
    have hcK₀ : k * w * k⁻¹ * w⁻¹ ∈ K₀ := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (hk.B_inv hwB) k⁻¹).1 (K₀.inv_mem hk')
      have := K₀.mul_mem hk' h1
      simpa [mul_assoc] using this
    have hcO : k * w * k⁻¹ * w⁻¹ ∈ GLAPPrimeCoreOf 3 X := hR.W_bar w hwW k (hk.le hk').1
    have hK₀X : K₀ ≤ X := (hk.le.trans inf_le_left).trans
      (bClosure_le_of_comp hB hBX hK hy hyN h3)
    exact inf_core_le 3 hK₀X ⟨hcK₀, hcO⟩
  have hwxy : w ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [← hk.cq]; exact hwcq
  have hwN : w ∈ Subgroup.normalizer (K : Set G) := by
    have hwK : w ∈ bClosure B K := hR.R_le (by rw [← hR.Rdef]; exact hwR)
    exact bClosure_le_normalizer hB hBX hK hy hyN h3 hwK
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_le_centralizer hK.1
  have hxy : x * y = y * x := hcomm x hxB y hy
  have hx3 := hB.2 x hxB
  have hy3 := hB.2 y hy
  have hy1 : y ≠ 1 := fun h => hyN (h ▸ Subgroup.one_mem _)
  have hne' : Subgroup.zpowers x ≠ Subgroup.zpowers y := by
    intro h
    apply hyN
    have : y ∈ Subgroup.zpowers x := h ▸ Subgroup.mem_zpowers y
    exact (Subgroup.zpowers_le.2 hxN) this
  have h9 := card_zpowers_sup hxy hx3 hy3 hx1 hy1 hne'
  have cx : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  set N' := Subgroup.normalizer (K : Set G) ⊓ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) with hN'
  have hxN' : Subgroup.zpowers x ≤ N' :=
    le_inf (Subgroup.zpowers_le.2 hxN) le_sup_left
  have hN'y : N' ≠ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    intro h
    apply hyN
    have : y ∈ N' := by rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    exact this.1
  have hdvd : Nat.card N' ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : N' ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers y)
    rw [h9] at this; norm_num; exact this
  obtain ⟨i, hi, hiN⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hcard3 : Nat.card N' = 3 := by
    have h1 : 3 ≤ Nat.card N' := by
      have := Subgroup.card_le_of_le hxN'
      omega
    have h2 : Nat.card N' ≠ 9 := by
      intro h9'
      apply hN'y
      exact (Subgroup.eq_of_le_of_card_ge (inf_le_right : N' ≤ _) (by rw [h9, h9'])).symm ▸ rfl
    interval_cases i <;> simp_all
  have hxeq : Subgroup.zpowers x = N' := Subgroup.eq_of_le_of_card_ge hxN' (by rw [cx, hcard3])
  have hwx : w ∈ Subgroup.zpowers x := by rw [hxeq]; exact ⟨hwN, hwxy⟩
  have cw : Nat.card ↥(Subgroup.zpowers w) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1]
  have hzw : Subgroup.zpowers w = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hwx) (by rw [cx, cw])
  have hxW : x ∈ Zc R := by
    have : x ∈ Subgroup.zpowers w := by rw [hzw]; exact Subgroup.mem_zpowers x
    exact (Subgroup.zpowers_le.2 hwW) this
  refine ⟨hxW, fun z hz hyz => ?_⟩
  set C := Triple.W y⁻¹ (R ⊓ K) ⊓ Subgroup.centralizer ({y⁻¹} : Set G) with hC
  have hCle := hR.triple.card_fix_W_le hR.W_card
  have hxC : Subgroup.zpowers x ≤ C := by
    exact Subgroup.zpowers_le.2 ⟨by rw [hR.Wdef]; exact hxW,
      Subgroup.mem_centralizer_singleton_iff.2 (Commute.inv_right (show Commute x y from hxy)).eq⟩
  have hCeq : Subgroup.zpowers x = C := Subgroup.eq_of_le_of_card_ge hxC (by rw [cx]; exact hCle)
  have hzC : z ∈ C := by
    exact ⟨by rw [hR.Wdef]; exact hz,
      Subgroup.mem_centralizer_singleton_iff.2 (Commute.inv_right (show Commute z y from hyz.symm)).eq⟩
  rw [hCeq]; exact hzC

end PhaseB

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
