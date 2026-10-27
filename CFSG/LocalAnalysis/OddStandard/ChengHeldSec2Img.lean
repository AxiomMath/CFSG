module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Fuse
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2GL

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

namespace Sec2Aux

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj {V : Subgroup G} {g : G} (h1 : ∀ v ∈ V, g * v * g⁻¹ ∈ V)
    (h2 : ∀ v ∈ V, g⁻¹ * v * g ∈ V) : g ∈ normalizer (V : Set G) := by
  refine mem_normalizer_iff.2 fun v => ?_
  constructor
  · intro hv; exact h1 v hv
  · intro hv
    have := h2 _ hv
    simpa [mul_assoc] using this

theorem mem_normalizer_of_conj_le [Finite G] {V : Subgroup G} {g : G}
    (h2 : ∀ v ∈ V, g⁻¹ * v * g ∈ V) : g ∈ normalizer (V : Set G) := by
  refine mem_normalizer_of_conj (fun v hv => ?_) h2
  let f : V → V := fun w => ⟨g⁻¹ * w * g, h2 w w.2⟩
  have hinj : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [f] at this
    exact Subtype.ext (mul_left_cancel (mul_right_cancel this))
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj ⟨v, hv⟩
  have := congrArg Subtype.val hw
  simp only [f] at this
  have hwv : (w : G) = g * v * g⁻¹ := by
    rw [← this]; group
  rw [← hwv]; exact w.2

theorem normalizerMonoidHom_coe {V : Subgroup G} (n : normalizer (V : Set G)) (v : V) :
    ((V.normalizerMonoidHom n v : V) : G) = (n : G) * v * (n : G)⁻¹ := rfl

end Sec2Aux

section Chart

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.t_sq_ne_one (c : Chart4 d α) : c.t ^ 2 ≠ 1 := fun h1 => by
  have := orderOf_dvd_of_pow_eq_one h1
  rw [c.orderOf_t] at this
  omega

theorem Chart4.pi_ne_one (c : Chart4 d α) : c.pi ≠ 1 := fun h1 => by
  have hpe : cj c.pi c.mu = c.t ^ 2 * c.pi := c.frame.pi_mu
  rw [h1] at hpe
  apply c.t_sq_ne_one
  have : cj (1 : G) c.mu = 1 := by unfold cj; group
  rw [this] at hpe
  simpa using hpe.symm

theorem Chart4.pi_ne_q (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) : c.pi ≠ d.q := fun h1 => by
  have hpe : cj c.pi c.mu = c.t ^ 2 * c.pi := c.frame.pi_mu
  have hcomm : c.mu * c.t = c.t * c.mu := c.t_comm hα h hP hQ c.mu c.mem.2.2.1
  have h3 : c.mu⁻¹ * c.t * c.mu = c.t := by
    calc c.mu⁻¹ * c.t * c.mu = c.mu⁻¹ * (c.t * c.mu) := by group
      _ = c.mu⁻¹ * (c.mu * c.t) := by rw [hcomm]
      _ = c.t := by group
  have hcq : cj c.pi c.mu = c.pi := by
    rw [h1, c.q_eq]
    unfold cj
    calc c.mu⁻¹ * c.t ^ 2 * c.mu = (c.mu⁻¹ * c.t * c.mu) * (c.mu⁻¹ * c.t * c.mu) := by
          rw [pow_two]; simp [mul_assoc]
      _ = c.t * c.t := by rw [h3]
      _ = c.t ^ 2 := (pow_two _).symm
  rw [hcq] at hpe
  apply c.t_sq_ne_one
  have h2 : c.t ^ 2 * c.pi = 1 * c.pi := by rw [← hpe]; simp
  exact mul_right_cancel h2

theorem Datum.cj_q_of_mem_X (d : Datum A) (h : Hyp G A) {x : G} (hx : x ∈ d.X) :
    x⁻¹ * d.q * x = d.q := by
  have h1 : d.q * x = x * d.q :=
    mem_centralizer_iff.1 ((d.q_mem_X h).2 hx) d.q (Set.mem_singleton _)
  calc x⁻¹ * d.q * x = x⁻¹ * (d.q * x) := by group
    _ = x⁻¹ * (x * d.q) := by rw [h1]
    _ = d.q := by group

theorem Chart4.closure_famG_eq (c : Chart4 d α) :
    (closure ({c.famG 0 ^ 2, c.famG 1, c.famG 0 * c.famG 2} : Set G)) = c.V := by
  simp [Chart4.famG, Chart4.V, c.q_eq]

theorem Chart4.famG_mem_S (c : Chart4 d α) (j : Fin 7) : c.famG j ∈ d.S := by
  rw [← c.subtype_fam]; exact (c.fam j).2

theorem Chart4.cj_t_of_GAct (c : Chart4 d α) {g : G}
    (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g) : cj c.t g = c.t := by
  unfold GAct at hact
  split_ifs at hact <;> exact hact.1

theorem Chart4.S_le_normalizer_V (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) : d.S ≤ normalizer (c.V : Set G) :=
  fun s hs => Sec2Aux.mem_normalizer_of_conj
    (fun w hw => by simpa [cj] using c.cj_V_mem hα h hP hQ s⁻¹ (d.S.inv_mem hs) w hw)
    (fun w hw => c.cj_V_mem hα h hP hQ s hs w hw)

theorem Chart4.exists_conj_pi_of_mem_V (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    {v : G} (hv : v ∈ c.V) (hv1 : v ≠ 1) (hvq : v ≠ d.q) :
    ∃ e ∈ normalizer (c.V : Set G), e⁻¹ * d.q * e = d.q ∧ e⁻¹ * c.pi * e = v := by
  have hGF := c.gFactsG hα h hP hQ hg hact
  have hVeq := c.closure_famG_eq
  have hqt : d.q = c.famG 0 ^ 2 := by simp [Chart4.famG, c.q_eq]
  have hgN : g ∈ normalizer (c.V : Set G) := by
    refine Sec2Aux.mem_normalizer_of_conj_le fun w hw => ?_
    have := hGF.V_stable hα w (by rw [hVeq]; exact hw)
    rwa [hVeq] at this
  have hgq : g⁻¹ * d.q * g = d.q := by
    have h1 : cj c.t g = c.t := c.cj_t_of_GAct hact
    unfold cj at h1
    rw [c.q_eq, pow_two]
    calc g⁻¹ * (c.t * c.t) * g = (g⁻¹ * c.t * g) * (g⁻¹ * c.t * g) := by simp [mul_assoc]
      _ = c.t * c.t := by rw [h1]
  have hSN := c.S_le_normalizer_V hα h hP hQ
  have hSq : ∀ s ∈ d.S, s⁻¹ * d.q * s = d.q := fun s hs => d.cj_q_of_mem_X h (d.S_le_X hs)
  let P : Set G :=
    {y | ∃ e ∈ normalizer (c.V : Set G), e⁻¹ * d.q * e = d.q ∧ y = e⁻¹ * c.pi * e}
  have hstep : ∀ e' ∈ normalizer (c.V : Set G), e'⁻¹ * d.q * e' = d.q → ∀ y ∈ P,
      e'⁻¹ * y * e' ∈ P := by
    rintro e' he' he'q y ⟨e, he, heq, rfl⟩
    refine ⟨e * e', mul_mem he he', ?_, ?_⟩
    · calc (e * e')⁻¹ * d.q * (e * e') = e'⁻¹ * (e⁻¹ * d.q * e) * e' := by group
        _ = d.q := by rw [heq, he'q]
    · group
  have hπP : c.pi ∈ P := ⟨1, one_mem _, by simp, by simp⟩
  have hO := hGF.orbit4 hα
  rw [hVeq] at hO
  have hsub := hO.2.2 P hπP (by
    intro F hF y hy
    simp only [gMapsG, List.mem_cons, List.mem_map, List.mem_range] at hF
    rcases hF with rfl | ⟨j, hj, rfl⟩
    · exact hstep g hgN hgq y hy
    · exact hstep _ (hSN (c.famG_mem_S _)) (hSq _ (c.famG_mem_S _)) y hy)
  have hvO : v ∈ ((c.V : Set G) \ {1, c.famG 0 ^ 2}) := by
    refine ⟨hv, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hv1, by rw [← hqt]; exact hvq⟩
  obtain ⟨e, he, heq, hy⟩ := hsub hvO
  exact ⟨e, he, heq, hy.symm⟩

theorem Chart4.dvd_card_range (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) {g : G} (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S)
    (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hn : ∃ n ∈ normalizer (c.V : Set G), cj d.q n = c.pi) :
    84 ∣ Nat.card c.V.normalizerMonoidHom.range := by
  have hS := c.sFacts hα h hP hQ
  have hVcard : Nat.card c.V = 8 := hS.card_V
  have hqV : d.q ∈ c.V := subset_closure (by simp)
  have hpV : c.pi ∈ c.V := subset_closure (by simp)
  set ρ := c.V.normalizerMonoidHom with hρ
  have hq1 : (⟨d.q, hqV⟩ : ↥c.V) ≠ 1 := fun h1 => by
    have h2 : d.q = 1 := congrArg Subtype.val h1
    have hord := d.q_ord
    rw [h2, orderOf_one] at hord
    omega
  have hp1 : (⟨c.pi, hpV⟩ : ↥c.V) ≠ 1 := fun h1 => c.pi_ne_one (congrArg Subtype.val h1)
  have hpq : (⟨c.pi, hpV⟩ : ↥c.V) ≠ ⟨d.q, hqV⟩ := fun h1 =>
    c.pi_ne_q hα h hP hQ (congrArg Subtype.val h1)
  have hπ : ∃ φ ∈ ρ.range, φ ⟨d.q, hqV⟩ = ⟨c.pi, hpV⟩ := by
    obtain ⟨n, hn, hnq⟩ := hn
    refine ⟨ρ ⟨n⁻¹, (normalizer (c.V : Set G)).inv_mem hn⟩, ⟨_, rfl⟩, Subtype.ext ?_⟩
    rw [Sec2Aux.normalizerMonoidHom_coe]
    simpa [cj] using hnq
  have horb : ∀ v : ↥c.V, v ≠ 1 → v ≠ ⟨d.q, hqV⟩ →
      ∃ φ ∈ ρ.range, φ ⟨d.q, hqV⟩ = ⟨d.q, hqV⟩ ∧ φ ⟨c.pi, hpV⟩ = v := by
    intro v hv1 hvq
    obtain ⟨e, he, heq, hy⟩ := c.exists_conj_pi_of_mem_V hα h hP hQ hg hact v.2
      (fun h1 => hv1 (Subtype.ext h1)) (fun h1 => hvq (Subtype.ext h1))
    refine ⟨ρ ⟨e⁻¹, (normalizer (c.V : Set G)).inv_mem he⟩, ⟨_, rfl⟩, Subtype.ext ?_,
      Subtype.ext ?_⟩
    · rw [Sec2Aux.normalizerMonoidHom_coe]; simpa using heq
    · rw [Sec2Aux.normalizerMonoidHom_coe]; simpa using hy
  obtain ⟨h7, h6⟩ := dvd_card_of_orbits hVcard ρ.range _ _ hq1 hp1 hpq hπ horb
  have hSN := c.S_le_normalizer_V hα h hP hQ
  have h4 : 4 ∣ Nat.card ρ.range := by
    let ρS : ↥d.S →* MulAut ↥c.V := ρ.comp (Subgroup.inclusion hSN)
    have hker : ρS.ker = c.W.subgroupOf d.S := by
      ext s
      simp only [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro hs1
        refine ⟨s.2, mem_centralizer_iff.2 fun v hv => ?_⟩
        have h2 := congrArg (fun φ : MulAut ↥c.V => ((φ ⟨v, hv⟩ : ↥c.V) : G)) hs1
        have h3 : ((ρS s ⟨v, hv⟩ : ↥c.V) : G) = (s : G) * v * (s : G)⁻¹ :=
          Sec2Aux.normalizerMonoidHom_coe (Subgroup.inclusion hSN s) ⟨v, hv⟩
        have this : (s : G) * v * (s : G)⁻¹ = v := by
          rw [← h3]; simpa using h2
        calc v * (s : G) = ((s : G) * v * (s : G)⁻¹) * s := by rw [this]
          _ = s * v := by group
      · rintro ⟨-, hc⟩
        refine MulEquiv.ext fun v => Subtype.ext ?_
        have h3 : ((ρS s v : ↥c.V) : G) = (s : G) * v * (s : G)⁻¹ :=
          Sec2Aux.normalizerMonoidHom_coe (Subgroup.inclusion hSN s) v
        rw [h3, MulAut.one_apply]
        have := mem_centralizer_iff.1 hc v v.2
        calc (s : G) * v * (s : G)⁻¹ = (v * s) * (s : G)⁻¹ := by rw [← this]
          _ = v := by group
    have hkerc : Nat.card ρS.ker = 64 := by
      rw [hker, ← hS.card_W]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hmul := Subgroup.card_ker_mul_card_range ρS
    rw [hkerc, hS.card_S] at hmul
    have h4' : Nat.card ρS.range = 4 := by omega
    have hle : ρS.range ≤ ρ.range := by
      rintro φ ⟨s, rfl⟩
      exact ⟨Subgroup.inclusion hSN s, rfl⟩
    exact h4' ▸ Subgroup.card_dvd_of_le hle
  have h21 : 21 ∣ Nat.card ρ.range :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 7)
      (dvd_trans (by norm_num : 3 ∣ 6) h6) h7
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 21) h4 h21


theorem Chart4.surjective_normalizerMonoidHom (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) {g : G} (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S)
    (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hn : ∃ n ∈ normalizer (c.V : Set G), cj d.q n = c.pi) :
    Function.Surjective c.V.normalizerMonoidHom := by
  have hS := c.sFacts hα h hP hQ
  have hV2 : ∀ v : ↥c.V, v * v = 1 := fun v => Subtype.ext (hS.V_sq v v.2)
  exact MonoidHom.range_eq_top.mp
    (eq_top_of_dvd_84 hS.card_V hV2 _ (c.dvd_card_range hα h hP hQ hg hact hn))

theorem Chart4.surjective_normalizerMonoidHom_of_isConj
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) (hS2 : chSec2OK = true)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hfus : IsConj d.q c.pi) : Function.Surjective c.V.normalizerMonoidHom :=
  c.surjective_normalizerMonoidHom hα h hP hQ hg hact (c.fuse_in_normalizer' hα h hP hQ hS2 hc hfus)

theorem Chart4.card_X_eq_eight_mul
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hn : ∃ n ∈ normalizer (c.V : Set G), cj d.q n = c.pi) :
    Nat.card d.X = 8 * Nat.card ↥(d.X ⊓ centralizer (c.V : Set G)) := by
  have hS := c.sFacts hα h hP hQ
  have hV2 : ∀ v : ↥c.V, v * v = 1 := fun v => Subtype.ext (hS.V_sq v v.2)
  have h84 := c.dvd_card_range hα h hP hQ hg hact hn
  set N : Subgroup G := normalizer (c.V : Set G) with hN
  set ρ := c.V.normalizerMonoidHom with hρ
  have hXN : d.X ≤ N := fun x hx =>
    mem_normalizer_iff.2 fun v => (c.X_normalizes hα h hP hQ hS2 hc hx).2 v
  have hXsyl : CFSG.ABGLocalTools.IsSylowOf 2 d.X N := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, hpg, hdvd⟩ :=
      CFSG.ABGLocalTools.isSylowOf_iff.1 (c.X_sylow_G_of_facts hα h hP hQ)
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hXN, hpg, fun hd => hdvd ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex d.X N ⊤ hXN le_top]
    exact dvd_mul_of_dvd_left hd _
  obtain ⟨Q, hQeq⟩ := hXsyl.exists_sylow_eq_subgroupOf
  have hQ8 : Nat.card ((Q : Subgroup N).map ρ) = 8 :=
    card_map_sylow_eq_eight hS.card_V hV2 ρ (dvd_trans (by norm_num) h84)
      (dvd_trans (by norm_num) h84) Q
  let f : ↥d.X →* MulAut ↥c.V := ρ.comp (Subgroup.inclusion hXN)
  have hrange : f.range = (Q : Subgroup N).map ρ := by
    rw [hQeq]
    ext φ
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hXN x, mem_subgroupOf.2 x.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, mem_subgroupOf.1 hn⟩, rfl⟩
  have hker : f.ker = (centralizer (c.V : Set G)).subgroupOf d.X := by
    ext x
    have h1 : x ∈ f.ker ↔ Subgroup.inclusion hXN x ∈ ρ.ker := Iff.rfl
    rw [h1, hρ, Subgroup.normalizerMonoidHom_ker, mem_subgroupOf, mem_subgroupOf]
    rfl
  have hkercard : Nat.card f.ker = Nat.card ↥(d.X ⊓ centralizer (c.V : Set G)) := by
    rw [hker]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hkercard, hrange, hQ8] at hmul
  rw [← hmul, mul_comm]

theorem Chart4.card_X_eq_eight_mul_of_isConj
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) (hS2 : chSec2OK = true)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hfus : IsConj d.q c.pi) :
    Nat.card d.X = 8 * Nat.card ↥(d.X ⊓ centralizer (c.V : Set G)) :=
  c.card_X_eq_eight_mul hα h hP hQ hS2 hc hg hact (c.fuse_in_normalizer' hα h hP hQ hS2 hc hfus)

end Chart

end CFSG.OddStandard.ChengHeld
