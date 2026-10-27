module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitOneJAux

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddInversion
open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

theorem lit_inv_mod {F U : Subgroup Γ} {t : Γ} (hF : Odd (Nat.card F)) (ht : orderOf t = 2)
    (htF : t ∈ normalizer (F : Set Γ)) (hfix : ∀ c ∈ F, t * c * t⁻¹ = c → c ∈ U) {x : Γ}
    (hxF : x ∈ F) (hxU : x ∈ normalizer (U : Set Γ)) : (t * x * t⁻¹) * x ∈ U := by
  obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ := (fixed_mul_inverted_bijOn hF ht htF).surjOn hxF
  dsimp only at hcj hc hj
  obtain ⟨hcF, hcC⟩ := Subgroup.mem_inf.mp hc
  have hct : t * c * t⁻¹ = c := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp hcC).symm]
    group
  have hcU : c ∈ U := hfix c hcF hct
  have hjx : t * j * t⁻¹ = j⁻¹ := hj.2
  have hjn : j⁻¹ ∈ normalizer (U : Set Γ) := by
    have hcn : c ∈ normalizer (U : Set Γ) := Subgroup.le_normalizer hcU
    have : j = c⁻¹ * x := by rw [← hcj]; group
    rw [this, mul_inv_rev, inv_inv]
    exact (normalizer (U : Set Γ)).mul_mem ((normalizer (U : Set Γ)).inv_mem hxU) hcn
  have hconj : j⁻¹ * c * j⁻¹⁻¹ ∈ U := conj_mem_of_mem_normalizer hjn hcU
  have e : (t * x * t⁻¹) * x = c * (j⁻¹ * c * j⁻¹⁻¹) := by
    rw [← hcj]
    calc (t * (c * j) * t⁻¹) * (c * j) = (t * c * t⁻¹) * (t * j * t⁻¹) * (c * j) := by group
      _ = c * (j⁻¹ * c * j⁻¹⁻¹) := by rw [hct, hjx]; group
  rw [e]
  exact U.mul_mem hcU hconj

theorem lit_gen_trivial {X U : Subgroup Γ} {t a : Γ} (hXU : X ≤ normalizer (U : Set Γ))
    (hinv : ∀ x ∈ X, (t * x * t⁻¹) * x ∈ U) (hinv' : ∀ x ∈ X, (t⁻¹ * x * t) * x ∈ U)
    (hXa : ∀ x ∈ X, a⁻¹ * x * a ∈ X) (hUa : ∀ u ∈ U, a * u * a⁻¹ ∈ U)
    (hUa' : ∀ u ∈ U, a⁻¹ * u * a ∈ U) (hUt : ∀ u ∈ U, t * u * t⁻¹ ∈ U) :
    ∀ x ∈ X, x⁻¹ * (⁅a, t⁆ * x * ⁅a, t⁆⁻¹) ∈ U := by
  intro x hx
  have hyX : a⁻¹ * x * a ∈ X := hXa x hx
  have h1 : (t⁻¹ * x * t) * x ∈ U := hinv' x hx
  have h3 : (t * (a⁻¹ * x * a) * t⁻¹) * (a⁻¹ * x * a) ∈ U := hinv _ hyX
  have h2 : a⁻¹ * ((t⁻¹ * x * t) * x) * a ∈ U := hUa' _ h1
  have h4 : a * (t * (a⁻¹ * ((t⁻¹ * x * t) * x) * a) * t⁻¹) * a⁻¹ ∈ U := hUa _ (hUt _ h2)
  have h5 : a * ((t * (a⁻¹ * x * a) * t⁻¹) * (a⁻¹ * x * a)) * a⁻¹ ∈ U := hUa _ h3
  have h6 : x⁻¹ * (a * (t * (a⁻¹ * ((t⁻¹ * x * t) * x) * a) * t⁻¹) * a⁻¹) * x⁻¹⁻¹ ∈ U :=
    conj_mem_of_mem_normalizer (hXU (X.inv_mem hx)) h4
  have e : x⁻¹ * (⁅a, t⁆ * x * ⁅a, t⁆⁻¹) =
      (x⁻¹ * (a * (t * (a⁻¹ * ((t⁻¹ * x * t) * x) * a) * t⁻¹) * a⁻¹) * x⁻¹⁻¹) *
        (a * ((t * (a⁻¹ * x * a) * t⁻¹) * (a⁻¹ * x * a)) * a⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact U.mul_mem h6 (U.inv_mem h5)

theorem lit_comm_lift [Finite Γ] {N : Subgroup Γ} (hN : Odd (Nat.card N)) {t : Γ}
    (ht : orderOf t = 2) (htN : t ∈ normalizer (N : Set Γ)) {A B : Subgroup Γ}
    (hAN : A ≤ normalizer (N : Set Γ)) (hAB : A ≤ normalizer (B : Set Γ))
    (htB : t ∈ normalizer (B : Set Γ))
    (hC : ∀ x ∈ N, t * x * t⁻¹ = x → ∀ b ∈ B, x * b = b * x) :
    ∀ g ∈ ⁅A, zpowers t⁆, g ∈ normalizer (N : Set Γ) ∧ g ∈ normalizer (B : Set Γ) ∧
      ∀ x ∈ litX N B, x⁻¹ * (g * x * g⁻¹) ∈ litU N B := by
  intro g hg
  have hFodd : Odd (Nat.card (CFSG.fittingSubgroupOf N)) :=
    Odd.of_dvd_nat hN (Subgroup.card_dvd_of_le (litFit_le N))
  have hfix : ∀ c ∈ CFSG.fittingSubgroupOf N, t * c * t⁻¹ = c → c ∈ litU N B := by
    intro c hc hct
    exact ⟨hc, mem_centralizer_iff.mpr fun b hb => (hC c (litFit_le N hc) hct b hb).symm⟩
  have hinv : ∀ x ∈ litX N B, (t * x * t⁻¹) * x ∈ litU N B := fun x hx =>
    lit_inv_mod hFodd ht (litFit_normalizer htN) hfix hx.1 hx.2
  have hti : t⁻¹ = t := CFSG.OddInversion.inv_eq_self_of_orderOf_eq_two ht
  have hinv' : ∀ x ∈ litX N B, (t⁻¹ * x * t) * x ∈ litU N B := by
    intro x hx
    rw [hti]
    have := hinv x hx
    rwa [hti] at this
  rw [Subgroup.commutator_def] at hg
  refine Subgroup.closure_induction
    (p := fun g _ => g ∈ normalizer (N : Set Γ) ∧ g ∈ normalizer (B : Set Γ) ∧
      ∀ x ∈ litX N B, x⁻¹ * (g * x * g⁻¹) ∈ litU N B) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨a, ha, s, hs, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hk : t ^ k = 1 ∨ t ^ k = t := by
      have hmod := zpow_mod_orderOf t k
      rw [ht] at hmod
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        rw [← hmod]
        simp [h]
      · right
        rw [← hmod]
        simp [h]
    rcases hk with hk | hk
    · rw [hk, commutatorElement_one_right]
      exact ⟨one_mem _, one_mem _, fun x hx => by simpa using (litU N B).one_mem⟩
    · rw [hk]
      have haN := hAN ha
      have haB := hAB ha
      refine ⟨?_, ?_, ?_⟩
      · rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem haN htN) (inv_mem haN)) (inv_mem htN)
      · rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem haB htB) (inv_mem haB)) (inv_mem htB)
      · refine lit_gen_trivial (fun x hx => hx.2) hinv hinv' ?_ ?_ ?_ ?_
        · intro x hx
          have := litX_conj ((normalizer (N : Set Γ)).inv_mem haN)
            ((normalizer (B : Set Γ)).inv_mem haB) hx
          simpa using this
        · exact fun u hu => litU_conj haN haB hu
        · intro u hu
          have := litU_conj ((normalizer (N : Set Γ)).inv_mem haN)
            ((normalizer (B : Set Γ)).inv_mem haB) hu
          simpa using this
        · exact fun u hu => litU_conj htN htB hu
  · exact ⟨one_mem _, one_mem _, fun x hx => by simpa using (litU N B).one_mem⟩
  · rintro g h _ _ ⟨hgN, hgB, hg⟩ ⟨hhN, hhB, hh⟩
    refine ⟨mul_mem hgN hhN, mul_mem hgB hhB, fun x hx => ?_⟩
    have hy : h * x * h⁻¹ ∈ litX N B := litX_conj hhN hhB hx
    have := (litU N B).mul_mem (hh x hx) (hg _ hy)
    have e : x⁻¹ * (h * x * h⁻¹) * ((h * x * h⁻¹)⁻¹ * (g * (h * x * h⁻¹) * g⁻¹)) =
        x⁻¹ * (g * h * x * (g * h)⁻¹) := by group
    rwa [e] at this
  · rintro g _ ⟨hgN, hgB, hg⟩
    refine ⟨inv_mem hgN, inv_mem hgB, fun x hx => ?_⟩
    have hy : g⁻¹ * x * g⁻¹⁻¹ ∈ litX N B := litX_conj (inv_mem hgN) (inv_mem hgB) hx
    have := (litU N B).inv_mem (hg _ hy)
    have e : ((g⁻¹ * x * g⁻¹⁻¹)⁻¹ * (g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹))⁻¹ =
        x⁻¹ * (g⁻¹ * x * g⁻¹⁻¹) := by group
    rwa [e] at this

theorem lit_normalizer_cond {F U : Subgroup Γ} (hF : Group.IsNilpotent ↥F) (hUF : U ≤ F)
    (h : ∀ x ∈ F, x ∈ normalizer (U : Set Γ) → x ∈ U) : F ≤ U := by
  by_contra hFU
  have hne : U.subgroupOf F ≠ ⊤ := fun h' => hFU (Subgroup.subgroupOf_eq_top.mp h')
  have hlt : U.subgroupOf F < normalizer (U.subgroupOf F : Set ↥F) :=
    normalizerCondition_of_isNilpotent _ (lt_top_iff_ne_top.mpr hne)
  obtain ⟨y, hy, hyU⟩ := SetLike.exists_of_lt hlt
  have hfwd : ∀ (z : ↥F), z ∈ normalizer (U.subgroupOf F : Set ↥F) → ∀ u ∈ U,
      (z : Γ) * u * (z : Γ)⁻¹ ∈ U := by
    intro z hz u hu
    have := (hz ⟨u, hUF hu⟩).mp hu
    exact this
  have hmem : (y : Γ) ∈ normalizer (U : Set Γ) := by
    intro u
    refine ⟨hfwd y hy u, fun hu => ?_⟩
    have := hfwd y⁻¹ ((normalizer (U.subgroupOf F : Set ↥F)).inv_mem hy) _ hu
    have e : ((y⁻¹ : ↥F) : Γ) * ((y : Γ) * u * (y : Γ)⁻¹) * ((y⁻¹ : ↥F) : Γ)⁻¹ = u := by
      simp only [Subgroup.coe_inv, inv_inv]
      group
    rwa [e] at this
  exact hyU (h y y.2 hmem)

theorem lit_oneJ [Finite Γ] {N : Subgroup Γ} (hN : Odd (Nat.card N)) {t : Γ}
    (ht : orderOf t = 2) (htN : t ∈ normalizer (N : Set Γ)) {A B : Subgroup Γ}
    (hAN : A ≤ normalizer (N : Set Γ)) (hBA : B ≤ ⁅A, zpowers t⁆)
    (hAB : A ≤ normalizer (B : Set Γ)) (htB : t ∈ normalizer (B : Set Γ))
    (hB2 : B ≤ Subgroup.closure {x | x ∈ B ∧ ∃ k : ℕ, x ^ 2 ^ k = 1})
    (hC : ∀ x ∈ N, t * x * t⁻¹ = x → ∀ b ∈ B, x * b = b * x) :
    ∀ x ∈ N, ∀ b ∈ B, x * b = b * x := by
  have hlift := lit_comm_lift hN ht htN hAN hAB htB hC
  have hX : ∀ b ∈ B, ∀ x ∈ litX N B, x * b = b * x := by
    refine lit_closure_two hB2 ?_
    rintro b hb ⟨k, hk⟩ x hx
    have hu : x⁻¹ * (b * x * b⁻¹) ∈ litU N B := (hlift b (hBA hb)).2.2 x hx
    have hbu' : b * (x⁻¹ * (b * x * b⁻¹)) = (x⁻¹ * (b * x * b⁻¹)) * b :=
      mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 b hb
    have hbu : b * (x⁻¹ * (b * x * b⁻¹)) * b⁻¹ = x⁻¹ * (b * x * b⁻¹) := by
      rw [hbu']
      group
    have hxb : b * x * b⁻¹ = x * (x⁻¹ * (b * x * b⁻¹)) := by group
    have hu1 := lit_two_power_fix hN hk (litFit_le N (Subgroup.mem_inf.mp hu).1) hbu hxb
    have h1 : b * x * b⁻¹ = x := by rw [hxb, hu1, mul_one]
    calc x * b = (b * x * b⁻¹) * b := by rw [h1]
      _ = b * x := by group
  have hFU : CFSG.fittingSubgroupOf N ≤ litU N B := by
    refine lit_normalizer_cond (litFit_nilpotent N) inf_le_left fun x hxF hxn => ?_
    exact ⟨hxF, mem_centralizer_iff.mpr fun b hb => (hX b hb x ⟨hxF, hxn⟩).symm⟩
  have hFB : ∀ f ∈ CFSG.fittingSubgroupOf N, ∀ b ∈ B, f * b = b * f := fun f hf b hb =>
    (mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hFU hf)).2 b hb).symm
  suffices h : ∀ b ∈ B, ∀ x ∈ (N : Set Γ), x * b = b * x from fun x hx b hb => h b hb x hx
  refine lit_closure_two hB2 ?_
  rintro b hb ⟨k, hk⟩ x hx
  have hbN : b ∈ normalizer (N : Set Γ) := (hlift b (hBA hb)).1
  have hn' : x⁻¹ * (b * x * b⁻¹) ∈ N :=
    N.mul_mem (N.inv_mem hx) (conj_mem_of_mem_normalizer hbN hx)
  have hcent : ∀ f ∈ CFSG.fittingSubgroupOf N,
      (x⁻¹ * (b * x * b⁻¹)) * f = f * (x⁻¹ * (b * x * b⁻¹)) := by
    intro f hf
    have hf' : x * f * x⁻¹ ∈ CFSG.fittingSubgroupOf N :=
      litFit_conj (Subgroup.le_normalizer hx) hf
    have hbf : f * b⁻¹ = b⁻¹ * f := hFB f hf b⁻¹ (B.inv_mem hb)
    have hbf' : (x * f * x⁻¹) * b = b * (x * f * x⁻¹) := hFB _ hf' b hb
    calc (x⁻¹ * (b * x * b⁻¹)) * f = x⁻¹ * b * x * (b⁻¹ * f) := by group
      _ = x⁻¹ * b * x * (f * b⁻¹) := by rw [hbf]
      _ = x⁻¹ * (b * (x * f * x⁻¹)) * x * b⁻¹ := by group
      _ = x⁻¹ * ((x * f * x⁻¹) * b) * x * b⁻¹ := by rw [hbf']
      _ = f * (x⁻¹ * (b * x * b⁻¹)) := by group
  have hnF : x⁻¹ * (b * x * b⁻¹) ∈ CFSG.fittingSubgroupOf N := litFit_cent hN hn' hcent
  have hbn : b * (x⁻¹ * (b * x * b⁻¹)) * b⁻¹ = x⁻¹ * (b * x * b⁻¹) := by
    rw [← hFB _ hnF b hb]
    group
  have hxb : b * x * b⁻¹ = x * (x⁻¹ * (b * x * b⁻¹)) := by group
  have hu1 := lit_two_power_fix hN hk hn' hbn hxb
  have h1 : b * x * b⁻¹ = x := by rw [hxb, hu1, mul_one]
  calc x * b = (b * x * b⁻¹) * b := by rw [h1]
    _ = b * x := by group

theorem lit_le_normalizer_commutator (H K : Subgroup Γ) :
    H ≤ normalizer ((⁅H, K⁆ : Subgroup Γ) : Set Γ) := by
  have fwd : ∀ a ∈ H, ∀ g ∈ ⁅H, K⁆, a * g * a⁻¹ ∈ ⁅H, K⁆ := by
    intro a ha g hg
    rw [Subgroup.commutator_def] at hg
    refine Subgroup.closure_induction
      (p := fun g _ => a * g * a⁻¹ ∈ ⁅H, K⁆) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨h, hh, k, hk, rfl⟩
      have e : a * ⁅h, k⁆ * a⁻¹ = ⁅a * h, k⁆ * ⁅a, k⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (Subgroup.commutator_mem_commutator (mul_mem ha hh) hk)
        (inv_mem (Subgroup.commutator_mem_commutator ha hk))
    · simp
    · intro x y _ _ hx hy
      have e : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      rw [e]
      exact mul_mem hx hy
    · intro x _ hx
      have e : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hx
  intro a ha g
  refine ⟨fwd a ha g, fun h => ?_⟩
  have := fwd a⁻¹ (inv_mem ha) _ h
  have e : a⁻¹ * (a * g * a⁻¹) * a⁻¹⁻¹ = g := by group
  rwa [e] at this

theorem lit_normalizer_commutator_zpowers (A : Subgroup Γ) (t : Γ) :
    A ≤ normalizer ((⁅A, zpowers t⁆ : Subgroup Γ) : Set Γ) ∧
      t ∈ normalizer ((⁅A, zpowers t⁆ : Subgroup Γ) : Set Γ) := by
  refine ⟨lit_le_normalizer_commutator A _, ?_⟩
  have h := lit_le_normalizer_commutator (zpowers t) A
  rw [Subgroup.commutator_comm] at h
  exact h (Subgroup.mem_zpowers t)

theorem lit_oneJ_comm [Finite Γ] {N : Subgroup Γ} (hN : Odd (Nat.card N)) {t : Γ}
    (ht : orderOf t = 2) (htN : t ∈ normalizer (N : Set Γ)) {A : Subgroup Γ}
    (hAN : A ≤ normalizer (N : Set Γ)) (h2 : ∀ b ∈ ⁅A, zpowers t⁆, ∃ k : ℕ, b ^ 2 ^ k = 1)
    (hC : ∀ x ∈ N, t * x * t⁻¹ = x → ∀ b ∈ ⁅A, zpowers t⁆, x * b = b * x) :
    ∀ x ∈ N, ∀ b ∈ ⁅A, zpowers t⁆, x * b = b * x :=
  lit_oneJ hN ht htN hAN le_rfl (lit_normalizer_commutator_zpowers A t).1
    (lit_normalizer_commutator_zpowers A t).2
    (fun b hb => Subgroup.subset_closure ⟨hb, h2 b hb⟩) hC

end CFSG.OddStandard.HigherRank.YamadaG23
