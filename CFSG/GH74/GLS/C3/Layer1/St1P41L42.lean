module

public import CFSG.GH74.GLS.C3.Layer1.St1Iv251C

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpL42

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open CFSG.GH74.GLS.Stage1.Thm3.Sec4
open CFSG.GH74.GLS.C3.Layer1.PumpCalc (conj_mem_cSec)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cmap_inf (c : G) (A B : Subgroup G) : cmap c (A ⊓ B) = cmap c A ⊓ cmap c B :=
  Subgroup.map_inf A B _ (MulAut.conj c).injective

omit [Finite G] in
theorem cmap_centralizerSection (c : G) (K M : Subgroup G) :
    cmap c (centralizerSection K M) = centralizerSection (cmap c K) (cmap c M) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply] using cmap_mem_centralizerSection hh c
  · intro hg
    have h1 := cmap_mem_centralizerSection hg c⁻¹
    rw [cmap_inv_cancel, cmap_inv_cancel] at h1
    refine ⟨c⁻¹ * g * c, ?_, by simp [MulAut.conj_apply]; group⟩
    simpa using h1

omit [Finite G] in
theorem cmap_CxK {x : G} {K : Subgroup G} (c : G) :
    cmap c (CxK x K) = CxK (c * x * c⁻¹) (cmap c K) := by
  unfold CxK
  have h1 : centralizer ({c * x * c⁻¹} : Set G) = cmap c (centralizer ({x} : Set G)) :=
    (Stage1.Thm2.Recip.map_centralizer_singleton_conj x c).symm
  rw [cmap_inf, cmap_centralizerSection, pPrimeCoreOf_cmap, h1]

theorem isSylowOf_cmap {p : ℕ} [Fact p.Prime] {P X : Subgroup G} (h : IsSylowOf p P X) (c : G) :
    IsSylowOf p (cmap c P) (cmap c X) := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hle, hP.of_equiv ((MulAut.conj c).subgroupMap P), ?_⟩
  rwa [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]

theorem exists_conj_mem_sylow {p : ℕ} [Fact p.Prime] {D Q : Subgroup G} (hQ : IsSylowOf p Q D)
    {a : G} (haD : a ∈ D) (ha : ∃ n : ℕ, a ^ (p ^ n) = 1) : ∃ d ∈ D, d * a * d⁻¹ ∈ Q := by
  obtain ⟨S₁, hS₁⟩ : ∃ S : Sylow p ↥D, Subgroup.zpowers (⟨a, haD⟩ : ↥D) ≤ S := by
    refine IsPGroup.exists_le_sylow ?_
    obtain ⟨n, hn⟩ := ha
    rw [IsPGroup.iff_card]
    have hord : orderOf (⟨a, haD⟩ : ↥D) ∣ p ^ n :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hn))
    obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hord
    exact ⟨k, by rw [Nat.card_zpowers, hk']⟩
  obtain ⟨Q', hQ'⟩ := hQ.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥D) S₁ Q'
  refine ⟨g, g.2, ?_⟩
  have h1 : (⟨a, haD⟩ : ↥D) ∈ (S₁ : Subgroup ↥D) := hS₁ (Subgroup.mem_zpowers _)
  have h2 : g * ⟨a, haD⟩ * g⁻¹ ∈ (g • S₁ : Sylow p ↥D) := by
    rw [Sylow.smul_def]; exact ⟨_, h1, rfl⟩
  rw [hg] at h2
  have h3 : g * ⟨a, haD⟩ * g⁻¹ ∈ (Q' : Subgroup ↥D) := h2
  rw [hQ'] at h3
  simpa using Subgroup.mem_subgroupOf.mp h3

theorem exists_conj_sylow {p : ℕ} [Fact p.Prime] {D Q Q' : Subgroup G} (hQ : IsSylowOf p Q D)
    (hQ' : IsSylowOf p Q' D) : ∃ d ∈ D, cmap d Q' = Q := by
  obtain ⟨S, hS⟩ := hQ.exists_sylow_eq_subgroupOf
  obtain ⟨S', hS'⟩ := hQ'.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥D) S' S
  have key : ∀ (A B : Sylow p ↥D) (h : ↥D), h • A = B →
      ∀ a ∈ (A : Subgroup ↥D), h * a * h⁻¹ ∈ (B : Subgroup ↥D) := by
    intro A B h hAB a ha
    rw [← hAB]
    rw [Sylow.smul_def]
    exact ⟨a, ha, rfl⟩
  refine ⟨g, g.2, le_antisymm ?_ ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : (⟨q, hQ'.le hq⟩ : ↥D) ∈ (S' : Subgroup ↥D) := by
      rw [hS']; exact Subgroup.mem_subgroupOf.mpr hq
    have := key S' S g hg _ hq'
    rw [hS] at this
    simpa [MulAut.conj_apply] using Subgroup.mem_subgroupOf.mp this
  · intro q hq
    have hq' : (⟨q, hQ.le hq⟩ : ↥D) ∈ (S : Subgroup ↥D) := by
      rw [hS]; exact Subgroup.mem_subgroupOf.mpr hq
    have hg' : g⁻¹ • S = S' := by rw [← hg, inv_smul_smul]
    have := key S S' g⁻¹ hg' _ hq'
    rw [hS'] at this
    have h2 := Subgroup.mem_subgroupOf.mp this
    refine ⟨(g⁻¹ * ⟨q, hQ.le hq⟩ * g⁻¹⁻¹ : ↥D), h2, ?_⟩
    simp [MulAut.conj_apply]
    group

omit [Finite G] in
theorem orderOf_conj' (d x : G) : orderOf (d * x * d⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj d).toMonoidHom (MulAut.conj d).injective x
  simpa [MulAut.conj_apply] using this

omit [Finite G] in
theorem cmap_eq_of_mem_normalizer {d : G} {K : Subgroup G} (hd : d ∈ normalizer (K : Set G)) :
    cmap d K = K := by
  ext g
  rw [mem_cmap]
  have := Subgroup.mem_normalizer_iff.mp hd (d⁻¹ * g * d)
  rw [show d * (d⁻¹ * g * d) * d⁻¹ = g by group] at this
  exact this

omit [Finite G] in
theorem trivial_of_cmap {x : G} {K K' : Subgroup G} {d : G} (hdD : d ∈ CxK x K)
    (h : x ∈ normalizer (cmap d K' : Set G) ∧ Nonempty (kBar (cmap d K') ≃* kBar K)) :
    x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K) := by
  obtain ⟨hn, ⟨e⟩⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro g
    have hcomm : d * x = x * d := Subgroup.mem_centralizer_singleton_iff.mp hdD.1
    have hx' : d⁻¹ * x * d = x := by
      calc d⁻¹ * x * d = d⁻¹ * (x * d) := by group
        _ = d⁻¹ * (d * x) := by rw [hcomm]
        _ = x := by group
    have h1 := hn (d * g * d⁻¹)
    rw [mem_cmap, mem_cmap] at h1
    have e1 : d⁻¹ * (d * g * d⁻¹) * d = g := by group
    have e2 : d⁻¹ * (x * (d * g * d⁻¹) * x⁻¹) * d = x * g * x⁻¹ := by
      calc d⁻¹ * (x * (d * g * d⁻¹) * x⁻¹) * d
          = (d⁻¹ * x * d) * g * (d⁻¹ * x * d)⁻¹ := by group
        _ = x * g * x⁻¹ := by rw [hx']
    rw [e1, e2] at h1
    exact h1
  · obtain ⟨e'⟩ := nonempty_quot_cmap d K'
    exact ⟨e'.symm.trans e⟩

theorem exists_nontrivial_in_sylow {x : G} {K Q : Subgroup G} (hQ : IsSylowOf 2 Q (CxK x K))
    {x' : G} {K' : Subgroup G} (hlt : PumpUpLT 2 x K x' K')
    (hnt : ¬ (x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K))) :
    ∃ u ∈ Q, orderOf u = 2 ∧ ∃ K'' : Subgroup G, PumpUpLT 2 x K u K'' ∧
      ¬ (x ∈ normalizer (K'' : Set G) ∧ Nonempty (kBar K'' ≃* kBar K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx'D : x' ∈ CxK x K := Subgroup.mem_inf.mpr ⟨hlt.2.2.1, hlt.2.2.2.1⟩
  have hx'2 : orderOf x' = 2 := hlt.2.1.1
  obtain ⟨d, hdD, hdx⟩ := exists_conj_mem_sylow hQ hx'D
    ⟨1, by rw [pow_one, ← hx'2]; exact pow_orderOf_eq_one x'⟩
  have hdx_c : d * x * d⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hdD.1
    calc d * x * d⁻¹ = x * d * d⁻¹ := by rw [this]
      _ = x := by group
  have hdK : cmap d K = K := cmap_eq_of_mem_normalizer hdD.2.1
  have hlt' : PumpUpLT 2 x K (d * x' * d⁻¹) (cmap d K') := by
    have := pumpUpLT_cmap hlt d
    rwa [hdx_c, hdK] at this
  exact ⟨d * x' * d⁻¹, hdx, by rw [orderOf_conj']; exact hx'2, cmap d K', hlt',
    fun h => hnt (trivial_of_cmap hdD h)⟩

omit [Finite G] in
theorem mem_normalizer_CxK {x : G} {K : Subgroup G} {g : G} (hg : g ∈ NxK x K) :
    g ∈ normalizer (CxK x K : Set G) := by
  have hNxK : ∀ g ∈ NxK x K, ∀ d ∈ CxK x K, g * d * g⁻¹ ∈ CxK x K := fun g hg d hd =>
    Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg.1 hd.1) (inv_mem hg.1), conj_mem_cSec hg.2 hd.2⟩
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨hNxK g hg d, fun hd => ?_⟩
  have h1 := hNxK g⁻¹ (inv_mem hg) _ hd
  simpa [mul_assoc] using h1

theorem exists_yinv_sylow {x y : G} {K : Subgroup G} (hy2 : orderOf y = 2) (hyN : y ∈ NxK x K) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q (CxK x K) ∧ y ∈ normalizer (Q : Set G) := by
  have hV2 : IsPGroup 2 ↥(Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hy2, pow_one]
  obtain ⟨Q, hQ, -, hyQ⟩ := Iv251.exists_invariant_sylow (C := CxK x K) (Q := ⊥)
    (V := Subgroup.zpowers y) bot_le (IsPGroup.of_card (n := 0) (by simp)) hV2
    (Subgroup.zpowers_le.mpr (mem_normalizer_CxK hyN))
    (Subgroup.zpowers_le.mpr (by rw [Subgroup.normalizer_eq_top]; trivial))
  exact ⟨Q, hQ, hyQ (Subgroup.mem_zpowers y)⟩

theorem lemma42
    (hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)))
    {x y : G} {K : Subgroup G} (hP : IsILo 2 x K)
    (hy2 : orderOf y = 2) (hyN : y ∈ NxK x K)
    (hsyl : ∀ Q : Subgroup G, IsSylowOf 2 Q (CxK x K) → ∀ t ∈ Q, orderOf t = 2 →
      (∀ q ∈ Q, t * q = q * t) → t * y = y * t → ∀ K' : Subgroup G, PumpUpLT 2 x K t K' →
        IsSylowOf 2 Q (CxK t K'))
    (hnt : ¬ IsTwoTerminal x K) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q (CxK x K) ∧ y ∈ normalizer (Q : Set G) ∧
      ∃ u ∈ Q, orderOf u = 2 ∧ ∃ K' : Subgroup G, PumpUpLT 2 x K u K' ∧
        ¬ (x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 ↥(Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hy2, pow_one]
  obtain ⟨Q, hQ, hyQ'⟩ := exists_yinv_sylow hy2 hyN
  by_contra hne
  have htr : ∀ u ∈ Q, orderOf u = 2 → ∀ K' : Subgroup G, PumpUpLT 2 x K u K' →
      x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K) := by
    intro u hu hu2 K' hlt
    by_contra hnt'
    exact hne ⟨Q, hQ, hyQ', u, hu, hu2, K', hlt, hnt'⟩
  refine hnt ⟨hP, ?_, ?_⟩
  ·
    intro x' K' hlt
    by_contra hnt'
    obtain ⟨u, hu, hu2, K'', hlt'', hnt''⟩ := exists_nontrivial_in_sylow hQ hlt hnt'
    exact hnt'' (htr u hu hu2 K'' hlt'')
  ·
    intro Q' hQ' x' K' hlt hx'Q' hx'c
    obtain ⟨d, hdD, hdQ⟩ := exists_conj_sylow hQ hQ'
    have hdx_c : d * x * d⁻¹ = x := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hdD.1
      calc d * x * d⁻¹ = x * d * d⁻¹ := by rw [this]
        _ = x := by group
    have hdK : cmap d K = K := cmap_eq_of_mem_normalizer hdD.2.1
    have hlt' : PumpUpLT 2 x K (d * x' * d⁻¹) (cmap d K') := by
      have := pumpUpLT_cmap hlt d
      rwa [hdx_c, hdK] at this
    have hx'2 : orderOf x' = 2 := hlt.2.1.1
    have hx''o : orderOf (d * x' * d⁻¹) = 2 := by rw [orderOf_conj']; exact hx'2
    have hx''Q : d * x' * d⁻¹ ∈ Q := by
      rw [← hdQ]; exact ⟨x', hx'Q', by simp [MulAut.conj_apply]⟩
    have hx''c : ∀ q ∈ Q, (d * x' * d⁻¹) * q = q * (d * x' * d⁻¹) := by
      intro q hq
      rw [← hdQ] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      have := hx'c q' hq'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc d * x' * d⁻¹ * (d * q' * d⁻¹) = d * (x' * q') * d⁻¹ := by group
        _ = d * (q' * x') * d⁻¹ := by rw [this]
        _ = d * q' * d⁻¹ * (d * x' * d⁻¹) := by group
    have h5 := Iv251.iv2_5_1 hP hQ hV2 (Subgroup.zpowers_le.mpr hyN)
      (Subgroup.zpowers_le.mpr hyQ')
      (fun z _ hz2 _ _ => hR z hz2)
      (fun z hz hz2 hzc hzV K'' hlt'' =>
        ⟨htr z hz hz2 K'' hlt'', hsyl Q hQ z hz hz2 hzc (hzV y (Subgroup.mem_zpowers y)) K'' hlt''⟩)
      (d * x' * d⁻¹) hx''Q hx''o hx''c (cmap d K') hlt' (htr _ hx''Q hx''o _ hlt')
    rw [← cmap_CxK d] at h5
    have h6 := isSylowOf_cmap h5 d⁻¹
    rwa [cmap_inv_cancel, ← hdQ, cmap_inv_cancel] at h6

theorem exists_noncommuting_pumpup_of_terminallyUnbalancing
    (hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)))
    {x y : G} {K : Subgroup G} (hP : IsILo 2 x K)
    (hterm : IsTerminallyUnbalancing x y K) (hnt : ¬ IsTwoTerminal x K) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q (CxK x K) ∧ y ∈ normalizer (Q : Set G) ∧
      ∃ u ∈ Q, orderOf u = 2 ∧ ∃ H : Subgroup G, PumpUpLT 2 x K u H ∧
        ¬ (x ∈ normalizer (H : Set G) ∧ Nonempty (kBar H ≃* kBar K)) ∧
        u * y ≠ y * u := by
  have hy2 : orderOf y = 2 := hterm.unbalancing.2.1
  have hyN : y ∈ NxK x K :=
    Subgroup.mem_inf.mpr ⟨hterm.unbalancing.2.2.1, hterm.unbalancing.2.2.2.1⟩
  obtain ⟨Q, hQ, hyQ, u, hu, hu2, H, hlt, hntriv⟩ :=
    lemma42 hR hP hy2 hyN hterm.sylow hnt
  refine ⟨Q, hQ, hyQ, u, hu, hu2, H, hlt, hntriv, ?_⟩
  intro hcomm
  exact hntriv (hterm.trivialPumpups u hu2 (hQ.le hu) hcomm H hlt)

end CFSG.GH74.GLS.C3.Layer1.PumpL42
