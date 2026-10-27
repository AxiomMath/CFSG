module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldChart2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBFix
public import Certificates.Certificate6136
public import CFSG.LocalAnalysis.OddStandard.ChengHeldChart4
public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartRep

public section

namespace CFSG.OddStandard.ChengHeld

@[expose] def GAct {G : Type*} [Group G] (α : ℕ) (t pi tau mu lam ze xi g : G) : Prop :=
  if α = 0 then
    cj t g = t ∧ cj pi g = tau * pi * t ^ 3 ∧ cj tau g = pi * t ∧ cj mu g = lam * mu * t ^ 2 ∧
      cj lam g = mu * t ^ 2 ∧ cj ze g = xi * ze ∧ cj xi g = ze
  else if α = 1 then
    cj t g = t ∧ cj pi g = tau * pi * t ∧ cj tau g = pi * t ∧ cj mu g = lam * mu ∧
      cj lam g = mu * t ^ 2 ∧ cj ze g = xi * ze * t ^ 2 ∧ cj xi g = ze
  else
    cj t g = t ∧ cj pi g = tau * pi * t ∧ cj tau g = pi * t ∧ cj mu g = lam * mu ∧
      cj lam g = mu ∧ cj ze g = xi * ze ∧ cj xi g = ze

end CFSG.OddStandard.ChengHeld

namespace CFSG.OddStandard.ChengHeld.M1b

open Subgroup CFSG.Open CFSG.OddStandard.ChengHeldData
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real

section Struct

variable {E : Type*} [Group E]

attribute [local simp] evalE evalE_pw vt vpi vtau vmu vlam vze vxi Tm.prod

theorem gAct_of_rels (α : ℕ) (σ : ℕ → E) (y : E)
    (h : ∀ e ∈ gRels α, cj (σ e.1) y = evalE σ e.2) :
    GAct α (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) y := by
  have key : ∀ i τ, (i, τ) ∈ gRels α → cj (σ i) y = evalE σ τ := fun i τ hm => h _ hm
  unfold GAct
  split_ifs with h0 h1
  · subst h0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using key 0 vt (by simp [gRels])
    · simpa [mul_assoc] using key 1 (Tm.prod [vtau, vpi, Tm.pw vt 3]) (by simp [gRels])
    · simpa using key 2 (Tm.prod [vpi, vt]) (by simp [gRels])
    · simpa [mul_assoc] using key 3 (Tm.prod [vlam, vmu, Tm.pw vt 2]) (by simp [gRels])
    · simpa using key 4 (Tm.prod [vmu, Tm.pw vt 2]) (by simp [gRels])
    · simpa using key 5 (Tm.prod [vxi, vze]) (by simp [gRels])
    · simpa using key 6 vze (by simp [gRels])
  · subst h1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using key 0 vt (by simp [gRels])
    · simpa [mul_assoc] using key 1 (Tm.prod [vtau, vpi, vt]) (by simp [gRels])
    · simpa using key 2 (Tm.prod [vpi, vt]) (by simp [gRels])
    · simpa using key 3 (Tm.prod [vlam, vmu]) (by simp [gRels])
    · simpa using key 4 (Tm.prod [vmu, Tm.pw vt 2]) (by simp [gRels])
    · simpa [mul_assoc] using key 5 (Tm.prod [vxi, vze, Tm.pw vt 2]) (by simp [gRels])
    · simpa using key 6 vze (by simp [gRels])
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using key 0 vt (by simp [gRels, h0, h1])
    · simpa [mul_assoc] using key 1 (Tm.prod [vtau, vpi, vt]) (by simp [gRels, h0, h1])
    · simpa using key 2 (Tm.prod [vpi, vt]) (by simp [gRels, h0, h1])
    · simpa using key 3 (Tm.prod [vlam, vmu]) (by simp [gRels, h0, h1])
    · simpa using key 4 vmu (by simp [gRels, h0, h1])
    · simpa using key 5 (Tm.prod [vxi, vze]) (by simp [gRels, h0, h1])
    · simpa using key 6 vze (by simp [gRels, h0, h1])

end Struct

theorem gAct_parts (h : gActOK = true) :
    (∀ α ≤ 1, actOK (eqKM (kapOf α)) (frM α) 31 (gRels α) = true) ∧
      actOK eqN2 (frM 2) 31 (gRels 2) = true := by
  simp only [gActOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  exact ⟨fun α hα => h1 α (by interval_cases α <;> simp), h2⟩

section TwoElt

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem eq_of_jq_eq_of_pow (h : Hyp G A) {u p : G} (hu : u ∈ A) (hp : p ∈ A) {k : ℕ}
    (hu2 : u ^ 2 ^ k = 1) (hp2 : p ^ 2 ^ k = 1) (e : jq A ⟨u, hu⟩ = jq A ⟨p, hp⟩) : u = p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : ↥A := ⟨u, hu⟩ with hU
  set V : ↥A := ⟨p, hp⟩ with hV
  have ho : U⁻¹ * V ∈ CFSG.pPrimeCore 2 ↥A := QuotientGroup.eq.1 e
  have hc : Commute U (U⁻¹ * V) := mem_center_iff.1 (h.pPrimeCore_le_center ho) U
  have hU2 : U ^ 2 ^ k = 1 := Subtype.ext (by simpa [hU] using hu2)
  have hV2 : V ^ 2 ^ k = 1 := Subtype.ext (by simpa [hV] using hp2)
  have h1 : (U⁻¹ * V) ^ 2 ^ k = 1 := by
    have h2 := hc.mul_pow (2 ^ k)
    rw [mul_inv_cancel_left, hV2, hU2, one_mul] at h2
    exact h2.symm
  have h3 : orderOf (⟨U⁻¹ * V, ho⟩ : CFSG.pPrimeCore 2 ↥A) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h1))
  have h4 := orderOf_dvd_natCard (⟨U⁻¹ * V, ho⟩ : CFSG.pPrimeCore 2 ↥A)
  have h5 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k CFSG.pPrimeCore_coprime_card) h3 h4
  have h6 : U⁻¹ * V = 1 := congrArg Subtype.val (orderOf_eq_one_iff.1 h5)
  exact congrArg Subtype.val (inv_mul_eq_one.1 h6)

theorem cj_eq_of_jq {d : Datum A} (h : Hyp G A) {g : G} (hg : g ∈ A) {s p : G} (hs : s ∈ d.S)
    (hp : p ∈ d.S)
    (e : (jq A ⟨g, hg⟩)⁻¹ * jq A ⟨s, d.S_le_A hs⟩ * jq A ⟨g, hg⟩ = jq A ⟨p, d.S_le_A hp⟩) :
    cj s g = p := by
  obtain ⟨k₁, hk₁⟩ := S_isPGroup d ⟨s, hs⟩
  obtain ⟨k₂, hk₂⟩ := S_isPGroup d ⟨p, hp⟩
  have hs1 : s ^ 2 ^ k₁ = 1 := by simpa using congrArg Subtype.val hk₁
  have hp1 : p ^ 2 ^ k₂ = 1 := by simpa using congrArg Subtype.val hk₂
  have hgs : g⁻¹ * s * g ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hg) (d.S_le_A hs)) hg
  have hpow : ∀ n : ℕ, (g⁻¹ * s * g) ^ n = g⁻¹ * s ^ n * g := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, pow_succ]; group
  refine eq_of_jq_eq_of_pow (u := g⁻¹ * s * g) h hgs (d.S_le_A hp) (k := k₁ + k₂) ?_ ?_ ?_
  · rw [hpow, pow_add, pow_mul, hs1, one_pow, mul_one, inv_mul_cancel]
  · rw [pow_add, mul_comm, pow_mul, hp1, one_pow]
  · rw [← e, ← map_inv, ← map_mul, ← map_mul]
    rfl

end TwoElt

section GElt

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {d : Datum A}

theorem repPerm_thirtyOne_mem_S : repPerm 31 ∈ S := repPerm_mem_S (by norm_num) (by decide)

theorem exists_g (P : Pos d) : ∃ g : G, ∃ hg : g ∈ A, P.q (jq A ⟨g, hg⟩) = (repPerm 31)⁻¹ := by
  obtain ⟨e, he⟩ := P.isQ.qsurj _ (S.inv_mem repPerm_thirtyOne_mem_S)
  obtain ⟨⟨g, hg⟩, rfl⟩ := jq_surjective A e
  exact ⟨g, hg, he⟩

theorem betaHat_g (P : Pos d) {g : G} (hg : g ∈ A) (hq : P.q (jq A ⟨g, hg⟩) = (repPerm 31)⁻¹) :
    ∀ w, betaHat A (le_normalizer hg) (P.l (cv w)) = P.l (cv (substWord (aut 31) w)) := by
  have hβ : ∀ x, P.q (betaHat A (le_normalizer hg) x) =
      (wordPerm (tg 0) * repPerm 31) * P.q x * (wordPerm (tg 0) * repPerm 31)⁻¹ := by
    intro x
    rw [betaHat_of_mem hg, map_mul, map_mul, map_inv, hq, wordPerm_tg_zero', one_mul, inv_inv]
  intro w
  have := betaRep_of_decomp P.isQ (by norm_num) (by norm_num) hβ w
  rwa [nf_zero, inv_one, one_mul, mul_one] at this

theorem conj_mem_S_of_g (h : Hyp G A) (P : Pos d) {g : G} (hg : g ∈ A)
    (hq : P.q (jq A ⟨g, hg⟩) = (repPerm 31)⁻¹) : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S := by
  intro s hs
  have hT : P.q ((jq A ⟨g, hg⟩)⁻¹ * jq A ⟨s, d.S_le_A hs⟩ * jq A ⟨g, hg⟩) ∈ T0 := by
    rw [map_mul, map_mul, map_inv, hq, inv_inv]
    exact (repPerm_conj_T0 (by norm_num) _).2 ((P.hT _).2 ⟨s, hs, d.S_le_A hs, rfl⟩)
  obtain ⟨p, hpS, hpA, hpe⟩ := (P.hT _).1 hT
  have hsp : cj s g = p := cj_eq_of_jq h hg hs hpS hpe.symm
  rw [show g⁻¹ * s * g = cj s g from rfl, hsp]
  exact hpS

variable {P : Pos d} {α : ℕ} (F : FrameData P α)

theorem g_table (h : Hyp G A) {g : G} (hg : g ∈ A)
    (hβ : ∀ w, betaHat A (le_normalizer hg) (P.l (cv w)) = P.l (cv (substWord (aut 31) w)))
    {eqf : MElt → MElt → Bool}
    (hf : ∀ x y : MElt, x.1 < 64 → y.1 < 64 → (eqf x y = true ↔ nfM P.l x = nfM P.l y))
    (hr : actOK eqf (frM α) 31 (gRels α) = true) :
    ∀ e ∈ gRels α, cj ((F.p e.1 : ↥d.S) : G) g = evalE (fun i => ((F.p i : ↥d.S) : G)) e.2 := by
  intro e he
  have h1 := act_of_actOK P.isQ hf (frM_lt α) (by norm_num) hβ hr e he
  rw [betaHat_of_mem hg, ← F.hp e.1, ← jS_evalE F e.2, jS_apply, jS_apply] at h1
  have h2 := evalE_map d.S.subtype F.p e.2
  simp only [Subgroup.coe_subtype] at h2
  rw [← h2]
  exact cj_eq_of_jq h hg (F.p e.1).2 (evalE F.p e.2).2 h1

end GElt

end CFSG.OddStandard.ChengHeld.M1b

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.Open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.M1b
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

theorem Datum.exists_chart4_g {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (d : Datum A) (h : Hyp G A)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) (hC : chCoverOK = true) :
    ∃ α : ℕ, α ≤ 1 ∧ ∃ c : Chart4 d α, ∃ g : G, g ∈ A ∧ (∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) ∧
      GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g := by
  have hCp := chCoverParts hC
  obtain ⟨-, hcyc⟩ := d.center_two_part h
  obtain ⟨P, α, hα, hstd⟩ := exists_pos_std4 d h hCp hc hcyc
  obtain ⟨F⟩ := exists_frameData P α
  have hkle := ker_le_zpowers4 P.isQ hα hstd
  have hfr : Frame4 α (F.p 0 : G) (F.p 1 : G) (F.p 2 : G) (F.p 3 : G) (F.p 4 : G) (F.p 5 : G)
      (F.p 6 : G) :=
    frame4_of_rels α (fun i => ((F.p i : ↥d.S) : G)) (fun e he => G_rel F
      (eval_eq_of_relsOK P.isQ (fun _ _ hx hy => eqKM_iff P.isQ hstd hx hy) (frM_lt α)
        (relsOK_of_frame4 hCp.frame4 hα) e he))
  have hord : orderOf ((F.p 0 : ↥d.S) : G) = 4 := (orderOf_t F h hkle).trans hc
  have hq_eq : d.q = ((F.p 0 : ↥d.S) : G) ^ 2 := by
    refine eq_of_orderOf_two_of_isCyclic hcyc ⟨⟨(d.q_mem_X h).1, d.q_mem⟩, d.q_cent⟩
      (pow_mem (t_mem_Z2 F h) 2) d.q_ord ?_
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hord]; norm_num), hord]
  obtain ⟨g, hg, hq⟩ := exists_g P
  have htab := g_table F h hg (betaHat_g P hg hq) (fun _ _ hx hy => eqKM_iff P.isQ hstd hx hy)
    ((gAct_parts hCp.gAct).1 α hα)
  refine ⟨α, hα, {
    t := (F.p 0 : G), pi := (F.p 1 : G), tau := (F.p 2 : G), mu := (F.p 3 : G),
    lam := (F.p 4 : G), ze := (F.p 5 : G), xi := (F.p 6 : G), frame := hfr, q_eq := hq_eq,
    t_mem := ⟨⟨d.S_le_X (F.p 0).2, (t_mem_Z2 F h).2⟩, (F.p 0).2⟩,
    mem := ⟨(F.p 1).2, (F.p 2).2, (F.p 3).2, (F.p 4).2, (F.p 5).2, (F.p 6).2⟩,
    gen := closure_frame F hCp hkle,
    rep := repOf d P,
    rep_mem := fun k y hk => ?_,
    cover := fun y hy hyQS => repOf_cover d h P hy hyQS }, g, hg, conj_mem_S_of_g h P hg hq,
    gAct_of_rels α (fun i => ((F.p i : ↥d.S) : G)) g htab⟩
  obtain ⟨hyX, hyQS⟩ := repOf_mem d h P hk
  obtain ⟨hy, hp⟩ := repOf_spec d P hk
  refine ⟨hyX, hyQS, ?_⟩
  cases k
  · exact act_field_of_rels α hα (fun i => ((F.p i : ↥d.S) : G)) y
      (act_G F hCp hα hstd (k := 0) (by norm_num) hp)
  · exact act_graph_of_rels α hα (fun i => ((F.p i : ↥d.S) : G)) y
      (act_G F hCp hα hstd (k := 1) (by norm_num) hp)
  · exact act_unitary_of_rels α hα (fun i => ((F.p i : ↥d.S) : G)) y
      (act_G F hCp hα hstd (k := 2) (by norm_num) hp)

theorem Datum.exists_chart2_g {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (d : Datum A) (h : Hyp G A)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 2) (hC : chCoverOK = true) :
    ∃ c : Chart2 d, ∃ g : G, g ∈ A ∧ (∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) ∧
      GAct 2 d.q c.pi c.tau c.mu c.lam c.ze c.xi g := by
  have hCp := chCoverParts hC
  obtain ⟨-, hcyc⟩ := d.center_two_part h
  obtain ⟨P, hstd⟩ := exists_pos_std2 d h hCp hc
  obtain ⟨F⟩ := exists_frameData P 2
  have hkle := ker_le_zpowers2 P.isQ hstd
  have hord : orderOf ((F.p 0 : ↥d.S) : G) = 2 := (orderOf_t F h hkle).trans hc
  have hq : ((F.p 0 : ↥d.S) : G) = d.q :=
    eq_of_orderOf_two_of_isCyclic hcyc (t_mem_Z2 F h)
      ⟨⟨(d.q_mem_X h).1, d.q_mem⟩, d.q_cent⟩ hord d.q_ord
  have hfr : Frame2 (F.p 0 : G) (F.p 1 : G) (F.p 2 : G) (F.p 3 : G) (F.p 4 : G) (F.p 5 : G)
      (F.p 6 : G) :=
    frame2_of_rels (fun i => ((F.p i : ↥d.S) : G)) (fun e he => G_rel F
      (eval_eq_of_relsOK P.isQ (fun _ _ hx hy => eqN2_iff P.isQ hstd hx hy) (frM_lt 2)
        hCp.frame2 e he))
  have hgen := closure_frame F hCp hkle
  obtain ⟨g, hg, hgq⟩ := exists_g P
  have htab := g_table F h hg (betaHat_g P hg hgq) (fun _ _ hx hy => eqN2_iff P.isQ hstd hx hy)
    (gAct_parts hCp.gAct).2
  have hgact : GAct 2 (F.p 0 : G) (F.p 1 : G) (F.p 2 : G) (F.p 3 : G) (F.p 4 : G) (F.p 5 : G)
      (F.p 6 : G) g :=
    gAct_of_rels 2 (fun i => ((F.p i : ↥d.S) : G)) g htab
  rw [hq] at hfr hgen hgact
  refine ⟨{
    pi := (F.p 1 : G), tau := (F.p 2 : G), mu := (F.p 3 : G), lam := (F.p 4 : G),
    ze := (F.p 5 : G), xi := (F.p 6 : G), frame := hfr,
    mem := ⟨(F.p 1).2, (F.p 2).2, (F.p 3).2, (F.p 4).2, (F.p 5).2, (F.p 6).2, hq ▸ (F.p 0).2⟩,
    gen := hgen, rep := repOf d P, rep_mem := fun k y hk => ?_,
    cover := fun y hy hyQS => repOf_cover d h P hy hyQS }, g, hg, conj_mem_S_of_g h P hg hgq,
    hgact⟩
  obtain ⟨hyX, hyQS⟩ := repOf_mem d h P hk
  obtain ⟨hy, hp⟩ := repOf_spec d P hk
  refine ⟨hyX, hyQS, ?_⟩
  cases k
  · have := act2_field_of_rels (fun i => ((F.p i : ↥d.S) : G)) y
      (act2_G F hCp hstd (k := 0) (by norm_num) hp)
    rwa [hq] at this
  · have := act2_graph_of_rels (fun i => ((F.p i : ↥d.S) : G)) y
      (act2_G F hCp hstd (k := 1) (by norm_num) hp)
    rwa [hq] at this
  · have := act2_unitary_of_rels (fun i => ((F.p i : ↥d.S) : G)) y
      (act2_G F hCp hstd (k := 2) (by norm_num) hp)
    rwa [hq] at this


section Charts


theorem Datum.exists_chart4_g_cert {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A)
    (h : Hyp G A) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) :
    ∃ α : ℕ, α ≤ 1 ∧ ∃ c : Chart4 d α, ∃ g : G, g ∈ A ∧ (∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) ∧
      GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g :=
  d.exists_chart4_g h hc Certificates.certificate6136

theorem Datum.exists_chart2_g_cert {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A)
    (h : Hyp G A) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 2) :
    ∃ c : Chart2 d, ∃ g : G, g ∈ A ∧ (∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) ∧
      GAct 2 d.q c.pi c.tau c.mu c.lam c.ze c.xi g :=
  d.exists_chart2_g h hc Certificates.certificate6136

end Charts

end CFSG.OddStandard.ChengHeld
