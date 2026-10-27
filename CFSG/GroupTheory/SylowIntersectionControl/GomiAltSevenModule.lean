module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
public import CFSG.Quasithin.Background.Module
import CFSG.GroupTheory.AltSevenFixedPointFree
import CFSG.GroupTheory.AltSevenCommuting
import CFSG.Quasithin.Background.FixVLattice

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (fixV commV)

private lemma orderOf_eq_three_of_isGomiThreeCycle_g7m {G : Type} [Group G] {K : Subgroup G}
    {x : G} (h : IsGomiThreeCycle 7 K x) : orderOf x = 3 := by
  obtain ⟨hx, φ, h3⟩ := h
  have h1 : orderOf (φ ⟨x, hx⟩ : alternatingGroup (Fin 7)) = 3 :=
    (Subgroup.orderOf_coe (φ ⟨x, hx⟩)).symm.trans (Equiv.Perm.IsThreeCycle.orderOf h3)
  calc orderOf x = orderOf (⟨x, hx⟩ : ↥K) := (Subgroup.orderOf_mk x hx).symm
    _ = orderOf (φ ⟨x, hx⟩) := (φ.orderOf_eq ⟨x, hx⟩).symm
    _ = 3 := h1

private lemma commV_mono_g7m {W : Type} [CommGroup W] {A B : Subgroup (MulAut W)}
    (h : A ≤ B) : commV A ≤ commV B := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, hx, v, rfl⟩
  exact ⟨x, h hx, v, rfl⟩

private lemma mem_fixV_zpowers_g7m {W : Type} [CommGroup W] {g : MulAut W} {u : W}
    (h : g u = u) : u ∈ fixV (Subgroup.zpowers g) := by
  have hinv : g⁻¹ u = u := by
    have hg : g (g⁻¹ u) = g u := by rw [MulAut.apply_inv_self, h]
    exact g.injective hg
  intro z hz
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact zpow_induction_right (g := g) (P := fun a : MulAut W => a u = u) (by rfl)
    (fun a ha => by rw [MulAut.mul_apply, h, ha])
    (fun a ha => by rw [MulAut.mul_apply, hinv, ha]) m

private lemma zpowers_zpow_eq_of_orderOf_eq_three_g7m {G : Type*} [Group G] [Finite G] {g : G}
    (h3 : orderOf g = 3) {j : ℤ} (hj : g ^ j ≠ 1) :
    Subgroup.zpowers (g ^ j) = Subgroup.zpowers g := by
  have hle : Subgroup.zpowers (g ^ j) ≤ Subgroup.zpowers g :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hdvd : orderOf (g ^ j) ∣ orderOf g :=
    orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩)
  rw [h3] at hdvd
  have hcard : Nat.card (Subgroup.zpowers (g ^ j)) = 3 := by
    rw [Nat.card_zpowers]
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · rw [orderOf_eq_one_iff] at h1
      exact absurd h1 hj
    · exact h1
  rw [hcard, Nat.card_zpowers, h3]

private theorem commute_mem_closure_g7m {W : Type} [CommGroup W]
    {𝓚 : Set (Subgroup (MulAut W))} (x : Subgroup (MulAut W) → MulAut W)
    (hx : ∀ K ∈ 𝓚, IsGomiThreeCycle 7 K (x K))
    (hcomm : ∀ K ∈ 𝓚, ∀ K' ∈ 𝓚, K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k) :
    ∀ a ∈ Subgroup.closure (x '' 𝓚), ∀ b ∈ Subgroup.closure (x '' 𝓚), a * b = b * a := by
  have hp : (x '' 𝓚).Pairwise Commute := by
    rintro _ ⟨K, hK, rfl⟩ _ ⟨K', hK', rfl⟩ hne
    exact hcomm K hK K' hK' (fun h => hne (by rw [h]))
      (x K) ((hx K hK).choose) (x K') ((hx K' hK').choose)
  have hcompl : ∀ a b : ↥(Subgroup.closure (x '' 𝓚)), a * b = b * a :=
    isMulCommutative_iff.mp (Subgroup.isMulCommutative_closure hp)
  intro a ha b hb
  exact congrArg Subtype.val (hcompl ⟨a, ha⟩ ⟨b, hb⟩)

private theorem pow_three_eq_one_of_mem_closure_g7m {W : Type} [CommGroup W]
    {𝓚 : Set (Subgroup (MulAut W))} (x : Subgroup (MulAut W) → MulAut W)
    (hx : ∀ K ∈ 𝓚, IsGomiThreeCycle 7 K (x K))
    (hcomm : ∀ K ∈ 𝓚, ∀ K' ∈ 𝓚, K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k) :
    ∀ d ∈ Subgroup.closure (x '' 𝓚), d ^ 3 = 1 := by
  intro d hd
  induction hd using Subgroup.closure_induction with
  | mem s hs =>
      obtain ⟨K, hK, rfl⟩ := hs
      rw [← orderOf_eq_three_of_isGomiThreeCycle_g7m (hx K hK)]
      exact pow_orderOf_eq_one _
  | one => simp
  | mul a b ha hb iha ihb =>
      have hc : Commute a b := commute_mem_closure_g7m x hx hcomm a ha b hb
      simp only [hc.mul_pow 3, iha, ihb, one_mul]
  | inv a ha iha => simp only [inv_pow, iha, inv_one]

private theorem commV_closure_le_iSup_g7m {W : Type} [CommGroup W]
    {𝓚 : Set (Subgroup (MulAut W))} (x : Subgroup (MulAut W) → MulAut W)
    (hx : ∀ K ∈ 𝓚, IsGomiThreeCycle 7 K (x K)) :
    commV (Subgroup.closure (x '' 𝓚)) ≤ ⨆ K ∈ 𝓚, commV K := by
  refine CFSG.Quasithin.FixVLat.commV_closure_le ?_
  rintro _ ⟨K, hK, rfl⟩ v
  exact Subgroup.mem_iSup_of_mem K (Subgroup.mem_iSup_of_mem hK
    (Subgroup.subset_closure ⟨x K, (hx K hK).choose, v, rfl⟩))

private lemma zpow_act_of_inv_g7m {W : Type} [CommGroup W] {a g : MulAut W} (hc : Commute a g)
    {j : ℤ} {u : W} (h : a u = (g ^ j) u) : a⁻¹ u = (g ^ (-j)) u := by
  have h2 : a ((g ^ (-j)) u) = u := by
    calc a ((g ^ (-j)) u) = ((g ^ (-j)) * a) u :=
          congrArg (fun e : MulAut W => e u) (hc.zpow_right (-j))
      _ = (g ^ (-j)) (a u) := rfl
      _ = (g ^ (-j)) ((g ^ j) u) := by rw [h]
      _ = ((g ^ (-j)) * (g ^ j)) u := rfl
      _ = (g ^ (-j + j)) u := by rw [zpow_add]
      _ = (g ^ (0 : ℤ)) u := by rw [neg_add_cancel]
      _ = u := by rw [zpow_zero]; rfl
  exact a.injective (by rw [MulAut.apply_inv_self, h2])

private theorem exists_zpow_act_commV_g7m {W : Type} [CommGroup W]
    (hW : ∀ w : W, w ^ 2 = 1) {𝓚 : Set (Subgroup (MulAut W))}
    (x : Subgroup (MulAut W) → MulAut W) (hx : ∀ K ∈ 𝓚, IsGomiThreeCycle 7 K (x K))
    (hcard : ∀ K ∈ 𝓚, Nat.card (commV K) = 16)
    (hcomm : ∀ K ∈ 𝓚, ∀ K' ∈ 𝓚, K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k)
    (d : MulAut W) (hd : d ∈ Subgroup.closure (x '' 𝓚)) :
    ∀ K ∈ 𝓚, ∃ j : ℤ, ∀ w ∈ commV K, d w = ((x K) ^ j) w := by
  induction hd using Subgroup.closure_induction with
  | mem s hs =>
      intro K hK
      obtain ⟨K', hK', rfl⟩ := hs
      by_cases hKK : K' = K
      · subst hKK
        exact ⟨1, fun w _ => by simp⟩
      · refine ⟨0, fun w hw => ?_⟩
        have hle : commV K ≤ fixV K' :=
          commV_le_fixV_of_commute hW ⟨(hx K hK).choose_spec.choose⟩
            ⟨(hx K' hK').choose_spec.choose⟩ (hcard K hK)
            (hcomm K hK K' hK' (Ne.symm hKK))
        simpa using hle hw (x K') ((hx K' hK').choose)
  | one => intro K hK; exact ⟨0, fun w _ => by simp⟩
  | mul a b ha hb iha ihb =>
      intro K hK
      obtain ⟨j₁, hj₁⟩ := iha K hK
      obtain ⟨j₂, hj₂⟩ := ihb K hK
      refine ⟨j₁ + j₂, fun w hw => ?_⟩
      have hcab : Commute a (x K) :=
        commute_mem_closure_g7m x hx hcomm a ha (x K) (Subgroup.subset_closure ⟨K, hK, rfl⟩)
      calc (a * b) w = a (b w) := rfl
        _ = a (((x K) ^ j₂) w) := by rw [hj₂ w hw]
        _ = (((x K) ^ j₂) * a) w := congrArg (fun e : MulAut W => e w) (hcab.zpow_right j₂)
        _ = ((x K) ^ j₂) (a w) := rfl
        _ = ((x K) ^ j₂) (((x K) ^ j₁) w) := by rw [hj₁ w hw]
        _ = (((x K) ^ j₂) * ((x K) ^ j₁)) w := rfl
        _ = ((x K) ^ (j₂ + j₁)) w := by rw [zpow_add]
        _ = ((x K) ^ (j₁ + j₂)) w := by rw [add_comm]
  | inv a ha iha =>
      intro K hK
      obtain ⟨j, hj⟩ := iha K hK
      exact ⟨-j, fun w hw => zpow_act_of_inv_g7m
        (commute_mem_closure_g7m x hx hcomm a ha (x K) (Subgroup.subset_closure ⟨K, hK, rfl⟩))
        (hj w hw)⟩

private theorem fixV_zpowers_inf_commV_eq_bot_of_act_zpow_g7m {W : Type} [CommGroup W] [Finite W]
    {K : Subgroup (MulAut W)} (φ : ↥K ≃* alternatingGroup (Fin 7))
    (hK : Nat.card (commV K) = 16) {d z : MulAut W} {j : ℤ} (hz : z ∈ K)
    (hz3 : ((φ ⟨z, hz⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).IsThreeCycle)
    (hact : ∀ w ∈ commV K, d w = ((z ^ j)) w) (hne : z ^ j ≠ 1) :
    fixV (Subgroup.zpowers d) ⊓ commV K = ⊥ := by
  have hzp : Subgroup.zpowers (z ^ j) = Subgroup.zpowers z :=
    zpowers_zpow_eq_of_orderOf_eq_three_g7m
      (orderOf_eq_three_of_isGomiThreeCycle_g7m ⟨hz, φ, hz3⟩) hne
  refine le_antisymm ?_ bot_le
  intro u hu
  obtain ⟨hufix, huK⟩ := Subgroup.mem_inf.mp hu
  have hzufix : ((z ^ j)) u = u := by
    rw [← hact u huK]
    exact hufix d (Subgroup.mem_zpowers d)
  have hux : u ∈ fixV (Subgroup.zpowers z) := by
    rw [← hzp]
    exact mem_fixV_zpowers_g7m hzufix
  have hmem : u ∈ fixV (Subgroup.zpowers z) ⊓ commV K := Subgroup.mem_inf.mpr ⟨hux, huK⟩
  rwa [fixV_zpowers_inf_commV_eq_bot φ hK hz hz3] at hmem

private theorem card_commV_zpowers_ge_of_act_nontrivial_g7m {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {𝓚 : Set (Subgroup (MulAut W))}
    (x : Subgroup (MulAut W) → MulAut W) (hx : ∀ K ∈ 𝓚, IsGomiThreeCycle 7 K (x K))
    (hcard : ∀ K ∈ 𝓚, Nat.card (commV K) = 16)
    (hcomm : ∀ K ∈ 𝓚, ∀ K' ∈ 𝓚, K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k)
    {d : MulAut W} (hd : d ∈ Subgroup.closure (x '' 𝓚))
    (hA : ∃ K ∈ 𝓚, ∃ w ∈ commV K, d w ≠ w) :
    16 ≤ Nat.card (commV (Subgroup.zpowers d)) := by
  obtain ⟨K, hK, w₀, hw₀, hdw₀⟩ := hA
  obtain ⟨j, hj⟩ := exists_zpow_act_commV_g7m hW x hx hcard hcomm d hd K hK
  obtain ⟨hxmem, φ, h3⟩ := hx K hK
  have hzjne : (x K) ^ j ≠ 1 := by
    intro h0
    exact hdw₀ (by rw [hj w₀ hw₀, h0]; rfl)
  have hfixK : fixV (Subgroup.zpowers d) ⊓ commV K = ⊥ :=
    fixV_zpowers_inf_commV_eq_bot_of_act_zpow_g7m φ (hcard K hK) hxmem h3 hj hzjne
  let Φ : commV K → commV (Subgroup.zpowers d) := fun w =>
    ⟨w.1⁻¹ * d w.1,
      Subgroup.subset_closure ⟨d, Subgroup.mem_zpowers d, w.1, mul_comm (d w.1) w.1⁻¹⟩⟩
  have hΦinj : Function.Injective Φ := by
    intro w₁ w₂ h
    have hval : w₁.1⁻¹ * d w₁.1 = w₂.1⁻¹ * d w₂.1 := congrArg Subtype.val h
    have hd_eq : d (w₁.1 * w₂.1⁻¹) = w₁.1 * w₂.1⁻¹ := by
      have h' : d w₁.1 = w₁.1 * w₂.1⁻¹ * d w₂.1 := by
        calc d w₁.1 = w₁.1 * (w₁.1⁻¹ * d w₁.1) := by group
          _ = w₁.1 * (w₂.1⁻¹ * d w₂.1) := by rw [hval]
          _ = w₁.1 * w₂.1⁻¹ * d w₂.1 := by group
      rw [map_mul, map_inv, h']
      group
    have hfix : w₁.1 * w₂.1⁻¹ ∈ fixV (Subgroup.zpowers d) := mem_fixV_zpowers_g7m hd_eq
    have hmemK : w₁.1 * w₂.1⁻¹ ∈ commV K := mul_mem w₁.2 (inv_mem w₂.2)
    have hbot : w₁.1 * w₂.1⁻¹ ∈ (⊥ : Subgroup W) := by
      rw [← hfixK]
      exact Subgroup.mem_inf.mpr ⟨hfix, hmemK⟩
    have hw : w₁.1 = w₂.1 := by
      have h1 := congrArg (fun z => z * w₂.1) (Subgroup.mem_bot.mp hbot)
      simpa [mul_assoc] using h1
    exact Subtype.ext hw
  have hle := Nat.card_le_card_of_injective Φ hΦinj
  rw [hcard K hK] at hle
  exact hle

private theorem eq_one_of_forall_commV_le_fixV_g7m {W : Type} [CommGroup W]
    (hW : ∀ w : W, w ^ 2 = 1) {𝓚 : Set (Subgroup (MulAut W))}
    (x : Subgroup (MulAut W) → MulAut W) (hx : ∀ K ∈ 𝓚, IsGomiThreeCycle 7 K (x K))
    {d : MulAut W} (hd : d ∈ Subgroup.closure (x '' 𝓚)) (h3d : d ^ 3 = 1)
    (hfix : ∀ K ∈ 𝓚, commV K ≤ fixV (Subgroup.zpowers d)) : d = 1 := by
  set M : Subgroup W := ⨆ K ∈ 𝓚, commV K with hM
  have hHM : commV (Subgroup.closure (x '' 𝓚)) ≤ ⨆ K ∈ 𝓚, commV K :=
    commV_closure_le_iSup_g7m x hx
  have hdM : commV (Subgroup.zpowers d) ≤ M := by
    rw [hM]
    exact (commV_mono_g7m (Subgroup.zpowers_le.mpr hd)).trans hHM
  have hMfix : M ≤ fixV (Subgroup.zpowers d) := by
    rw [hM]
    exact iSup_le fun K => iSup_le fun hK => hfix K hK
  ext w
  let c : W := w⁻¹ * d w
  have hcM : c ∈ M :=
    hdM (Subgroup.subset_closure ⟨d, Subgroup.mem_zpowers d, w, mul_comm (d w) w⁻¹⟩)
  have hc : d c = c := (hMfix hcM) d (Subgroup.mem_zpowers d)
  have hdw : d w = w * c := by
    show d w = w * (w⁻¹ * d w)
    group
  have hpow : ∀ n : ℕ, (d ^ n) w = w * c ^ n := by
    intro n
    induction n with
    | zero => simp [MulAut.one_apply]
    | succ n ih =>
        have hdc : d (c ^ n) = c ^ n := by rw [map_pow, hc]
        calc (d ^ (n + 1)) w = (d * d ^ n) w := by rw [pow_succ']
          _ = d ((d ^ n) w) := rfl
          _ = d (w * c ^ n) := by rw [ih]
          _ = d w * d (c ^ n) := by rw [map_mul]
          _ = d w * c ^ n := by rw [hdc]
          _ = w * c * c ^ n := by rw [hdw]
          _ = w * (c * c ^ n) := by rw [mul_assoc]
          _ = w * c ^ (n + 1) := by rw [pow_succ']
  have h3w : w = w * c ^ 3 := by
    have h := hpow 3
    rwa [h3d, MulAut.one_apply] at h
  have hc3 : c ^ 3 = 1 := by
    have h : w * c ^ 3 = w * 1 := by rw [mul_one, ← h3w]
    exact mul_left_cancel h
  have hc1 : c = 1 := by
    have h2 : c ^ 2 = 1 := hW c
    have h3' : c ^ 3 = c := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul]
    rw [h3'] at hc3
    exact hc3
  show d w = (1 : MulAut W) w
  rw [MulAut.one_apply, hdw, hc1, mul_one]

theorem le_card_commV_zpowers_of_mem_closure {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {𝓚 : Set (Subgroup (MulAut W))}
    (x : Subgroup (MulAut W) → MulAut W) (hx : ∀ K ∈ 𝓚, IsGomiThreeCycle 7 K (x K))
    (hcard : ∀ K ∈ 𝓚, Nat.card (commV K) = 16)
    (hcomm : ∀ K ∈ 𝓚, ∀ K' ∈ 𝓚, K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k)
    {d : MulAut W} (hd : d ∈ Subgroup.closure (x '' 𝓚)) (hd1 : d ≠ 1) :
    16 ≤ Nat.card (commV (Subgroup.zpowers d)) := by
  by_cases hA : ∃ K ∈ 𝓚, ∃ w ∈ commV K, d w ≠ w
  · exact card_commV_zpowers_ge_of_act_nontrivial_g7m hW x hx hcard hcomm hd hA
  · have hfix : ∀ K ∈ 𝓚, commV K ≤ fixV (Subgroup.zpowers d) := by
      intro K hK w hw
      have hdw : d w = w := by
        by_contra hne
        exact hA ⟨K, hK, w, hw, hne⟩
      exact mem_fixV_zpowers_g7m hdw
    have h3d : d ^ 3 = 1 := pow_three_eq_one_of_mem_closure_g7m x hx hcomm d hd
    exact absurd (eq_one_of_forall_commV_le_fixV_g7m hW x hx hd h3d hfix) hd1

end CFSG.GroupTheory
