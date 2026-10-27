module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Klein
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.CTMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

section A2

theorem mf_closure_three (a b c : GL32) :
    Subgroup.closure {a, b, c} = zpowers a ⊔ zpowers b ⊔ zpowers c := by
  rw [Set.insert_eq, Set.insert_eq, Subgroup.closure_union, Subgroup.closure_union,
    ← zpowers_eq_closure, ← zpowers_eq_closure, ← zpowers_eq_closure, sup_assoc]

theorem mf_zpowers_conj (g s : GL32) :
    zpowers (g * s * g⁻¹) = (zpowers s).map (MulAut.conj g).toMonoidHom := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem card_le_eight {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M]
    (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0) {s : GL32} (hs : s ^ 2 = 1) (hs1 : s ≠ 1)
    (h : Nat.card M ≤ 2 * Nat.card (fixSub M (zpowers s))) : Nat.card M ≤ 8 := by
  obtain ⟨g₁, g₂, hgen⟩ := involutions_generate hs hs1
  have hc : ∀ g : GL32,
      Nat.card (fixSub M (zpowers (g * s * g⁻¹))) = Nat.card (fixSub M (zpowers s)) := by
    intro g
    rw [mf_zpowers_conj, card_fixSub_conj]
  have hbot : fixSub M (zpowers s) ⊓ fixSub M (zpowers (g₁ * s * g₁⁻¹)) ⊓
      fixSub M (zpowers (g₂ * s * g₂⁻¹)) = ⊥ := by
    rw [← fixSub_sup, ← fixSub_sup, ← mf_closure_three, hgen]
    refine le_antisymm ?_ bot_le
    intro m hm
    rw [AddSubgroup.mem_bot]
    exact hM0 m (fun g => hm g (Subgroup.mem_top g))
  have hn : 0 < Nat.card M := Nat.card_pos
  have h1 := card_inf_ge (fixSub M (zpowers s)) (fixSub M (zpowers (g₁ * s * g₁⁻¹)))
  have h2 := card_inf_ge (fixSub M (zpowers s) ⊓ fixSub M (zpowers (g₁ * s * g₁⁻¹)))
    (fixSub M (zpowers (g₂ * s * g₂⁻¹)))
  rw [hbot, AddSubgroup.card_bot] at h2
  rw [hc g₁] at h1
  rw [hc g₂] at h2
  generalize Nat.card (fixSub M (zpowers s)) = c at h h1 h2
  generalize Nat.card M = n at h hn h1 h2 ⊢
  generalize Nat.card (fixSub M (zpowers s) ⊓ fixSub M (zpowers (g₁ * s * g₁⁻¹)) :
    AddSubgroup M) = e at h1 h2
  have hc3 : c ^ 3 ≤ n ^ 2 := by
    calc c ^ 3 = c * (c * c) := by ring
      _ ≤ c * (n * e) := Nat.mul_le_mul_left _ h1
      _ = n * (e * c) := by ring
      _ ≤ n * (n * 1) := Nat.mul_le_mul_left _ h2
      _ = n ^ 2 := by ring
  have h3 : n * n ^ 2 ≤ 8 * n ^ 2 := by
    calc n * n ^ 2 = n ^ 3 := by ring
      _ ≤ (2 * c) ^ 3 := Nat.pow_le_pow_left h 3
      _ = 8 * c ^ 3 := by ring
      _ ≤ 8 * n ^ 2 := Nat.mul_le_mul_left _ hc3
  exact Nat.le_of_mul_le_mul_right h3 (by positivity)

theorem offender_to_Sbar {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M]
    (h2 : ∀ m : M, m + m = 0) (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0)
    (hne : ∃ m : M, m ≠ 0) {S A₀ : Subgroup GL32} (hS : Nat.card S = 4)
    (hS2 : ∀ g ∈ S, g ^ 2 = 1) (hAS : A₀ ≤ S) (hA₀ : A₀ ≠ ⊥)
    (hoff : Nat.card M ≤ Nat.card A₀ * Nat.card (fixSub M A₀)) :
    Nat.card M ≤ 4 * Nat.card (fixSub M S) := by
  have hdvd : Nat.card A₀ ∣ 4 := hS ▸ Subgroup.card_dvd_of_le hAS
  have hA1 : Nat.card A₀ ≠ 1 := fun h => hA₀ (Subgroup.card_eq_one.1 h)
  have hApos : 0 < Nat.card A₀ := Nat.card_pos
  have hAle : Nat.card A₀ ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : Nat.card A₀ = 2 ∨ Nat.card A₀ = 4 := by
    generalize Nat.card A₀ = k at hdvd hA1 hApos hAle
    interval_cases k <;> omega
  rcases hcases with hA2 | hA4
  ·
    obtain ⟨⟨s, hsA⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA₀
    have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
    have hsq : s ^ 2 = 1 := hS2 s (hAS hsA)
    have hord : orderOf s = 2 := by
      have hdv : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      rcases (Nat.dvd_prime Nat.prime_two).1 hdv with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hs1'
      · exact h
    have hzA : zpowers s ≤ A₀ := (Subgroup.zpowers_le).2 hsA
    have hzeq : zpowers s = A₀ := by
      refine Subgroup.eq_of_le_of_card_ge hzA ?_
      rw [Nat.card_zpowers, hord, hA2]
    rw [← hzeq] at hoff
    rw [Nat.card_zpowers, hord] at hoff
    have h8 : Nat.card M ≤ 8 := card_le_eight hM0 hsq hs1' hoff
    have hS2g : IsPGroup 2 S := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact IsPGroup.of_card (n := 2) (by rw [hS]; norm_num)
    have hd2 := two_dvd_card_fixSub (M := M) h2 hne hS2g
    have hpos : 0 < Nat.card (fixSub M S) := Nat.card_pos
    have hge : 2 ≤ Nat.card (fixSub M S) := Nat.le_of_dvd hpos hd2
    omega
  ·
    have hAeq : A₀ = S := Subgroup.eq_of_le_of_card_ge hAS (by rw [hS, hA4])
    subst hAeq
    rw [hA4] at hoff
    exact hoff

theorem mf_τ_τ (g : GL32) : L32Insp.τ (L32Insp.τ g) = g := by
  have h := congrArg (fun f : MulAut GL32 => f g) L32Insp.τ_mul_τ
  simpa using h

theorem mf_mem_map_τ (H : Subgroup GL32) (x : GL32) :
    x ∈ H.map L32Insp.τ.toMonoidHom ↔ L32Insp.τ x ∈ H := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show L32Insp.τ (L32Insp.τ y) ∈ H
    rw [mf_τ_τ]
    exact hy
  · intro hx
    exact ⟨L32Insp.τ x, hx, mf_τ_τ x⟩

theorem mf_normalizer_τ {p : V3} {d : GL32}
    (hdS : d ∈ normalizer (((Spt p).map L32Insp.τ.toMonoidHom : Subgroup GL32) : Set GL32)) :
    L32Insp.τ d ∈ normalizer (Spt p : Set GL32) := by
  rw [Subgroup.mem_normalizer_iff] at hdS ⊢
  intro h
  have h1 := hdS (L32Insp.τ h)
  rw [mf_mem_map_τ, mf_mem_map_τ, mf_τ_τ, map_mul, map_mul, map_inv, mf_τ_τ] at h1
  exact h1

section Twist

@[instance_reducible] def mf_twAct (M : Type) [AddCommGroup M] [DistribMulAction GL32 M] :
    DistribMulAction GL32 M :=
  DistribMulAction.compHom M L32Insp.τ.toMonoidHom

variable {M : Type} [AddCommGroup M] [DistribMulAction GL32 M]

theorem mf_mem_fixSub_tw (H : Subgroup GL32) (m : M) :
    m ∈ @fixSub M _ (mf_twAct M) H ↔ m ∈ fixSub M (H.map L32Insp.τ.toMonoidHom) := by
  rw [@mem_fixSub M _ (mf_twAct M), mem_fixSub]
  constructor
  · intro h g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    exact h y hy
  · intro h g hg
    exact h _ (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)

theorem mf_fixSub_tw (H : Subgroup GL32) :
    @fixSub M _ (mf_twAct M) H = fixSub M (H.map L32Insp.τ.toMonoidHom) :=
  AddSubgroup.ext fun m => mf_mem_fixSub_tw H m

theorem mf_commSub_tw (H : Subgroup GL32) :
    @commSub M _ (mf_twAct M) H = commSub M (H.map L32Insp.τ.toMonoidHom) := by
  unfold commSub
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, m, rfl⟩
    exact ⟨L32Insp.τ g, ⟨g, hg, rfl⟩, m, rfl⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, m, rfl⟩
    exact ⟨g, hg, m, rfl⟩

theorem mf_commSub_tw_zpowers (d : GL32) :
    @commSub M _ (mf_twAct M) (zpowers (L32Insp.τ d)) = commSub M (zpowers d) := by
  rw [mf_commSub_tw, MonoidHom.map_zpowers]
  have h : L32Insp.τ.toMonoidHom (L32Insp.τ d) = d := mf_τ_τ d
  rw [h]

theorem mf_fixSub_tw_sup (p : V3) (d : GL32) :
    @fixSub M _ (mf_twAct M) (Spt p ⊔ zpowers (L32Insp.τ d)) =
      fixSub M ((Spt p).map L32Insp.τ.toMonoidHom ⊔ zpowers d) := by
  rw [mf_fixSub_tw, Subgroup.map_sup, MonoidHom.map_zpowers]
  have h : L32Insp.τ.toMonoidHom (L32Insp.τ d) = d := mf_τ_τ d
  rw [h]

end Twist

theorem ct_final {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M]
    (h2 : ∀ m : M, m + m = 0) (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0)
    (hne : ∃ m : M, m ≠ 0) {p : V3} (hp : p ≠ 0) {S : Subgroup GL32}
    (hSp : S = Spt p ∨ S = (Spt p).map L32Insp.τ.toMonoidHom) {d : GL32} (hd : orderOf d = 3)
    (hdS : d ∈ normalizer (S : Set GL32)) (hoff : Nat.card M ≤ 4 * Nat.card (fixSub M S)) :
    Nat.card (commSub M (zpowers d)) ≤ 16 ∧ Nat.card (fixSub M (S ⊔ zpowers d)) ≤ 2 ∧
      ((∃ m ∈ fixSub M S, d • m ≠ m) → fixSub M (S ⊔ zpowers d) = ⊥) := by
  rcases hSp with rfl | rfl
  · have hdp : act d p = p := by
      have hmem : d ∈ Pstab p := by
        rw [← normalizer_Spt hp]
        exact hdS
      exact hmem
    have hyp : CTHyp M p d := ⟨h2, hM0, hne, hp, hoff, hd, hdp⟩
    exact ct_main hyp
  · have hdp : act (L32Insp.τ d) p = p := by
      have hmem : L32Insp.τ d ∈ Pstab p := by
        rw [← normalizer_Spt hp]
        exact mf_normalizer_τ hdS
      exact hmem
    have hyp : @CTHyp M _ _ (mf_twAct M) p (L32Insp.τ d) := by
      refine @CTHyp.mk M _ _ (mf_twAct M) p (L32Insp.τ d) h2 ?_ hne hp ?_ ?_ hdp
      · intro m hm
        refine hM0 m (fun g => ?_)
        have h1 : L32Insp.τ (L32Insp.τ g) • m = m := hm (L32Insp.τ g)
        rwa [mf_τ_τ] at h1
      · rw [mf_fixSub_tw]
        exact hoff
      · exact (MulEquiv.orderOf_eq L32Insp.τ d).trans hd
    obtain ⟨c1, c2, c3⟩ := @ct_main M _ _ (mf_twAct M) p (L32Insp.τ d) hyp
    refine ⟨?_, ?_, ?_⟩
    · rwa [mf_commSub_tw_zpowers] at c1
    · rwa [mf_fixSub_tw_sup] at c2
    · rintro ⟨m, hm, hdm⟩
      rw [← mf_fixSub_tw_sup]
      apply c3
      refine ⟨m, ?_, ?_⟩
      · rw [mf_fixSub_tw]
        exact hm
      · intro h
        apply hdm
        have h' : L32Insp.τ (L32Insp.τ d) • m = m := h
        rwa [mf_τ_τ] at h'

end A2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
