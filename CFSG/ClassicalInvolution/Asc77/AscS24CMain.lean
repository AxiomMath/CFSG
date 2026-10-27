module

public import CFSG.ClassicalInvolution.Asc77.AscS24CCase
public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24

theorem commutator_eq_top_of_simple {G : Type} [Group G] [IsSimpleGroup G]
    (hnc : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with
    h | h
  · obtain ⟨a, b, hab⟩ := hnc
    exact (hab ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) a b)).elim
  · exact h

section Ctx

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}


variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : S24B.Ctx8 p f Ω K K' W S R R' z u)

include C in
theorem exists_caseI {c : G} (hcS : c ∈ (S : Subgroup G)) (hc2 : c * c = 1)
    (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) (hcr : c * C.D.F.ρ.r = C.D.F.ρ.r * c)
    (hin : InnerOn c R') :
    ∃ e ∈ (S : Subgroup G), e ∉ sZero Ω W S ∧ e * e = 1 ∧
      (∀ x ∈ (S : Subgroup G), x ∉ sZero Ω W S → e⁻¹ * x ∈ sZero Ω W S) ∧
      (∀ v ∈ R, v * e = e * v) ∧ (∀ v ∈ R', v * e = e * v) := by
  obtain ⟨q, hq, hqv⟩ := hin
  have hst := C.hs.stand
  have hrS : C.D.F.ρ.r ∈ (S : Subgroup G) := C.hd.hR.2.2 C.r_mem_R
  have hqS : q ∈ (S : Subgroup G) := C.hd.hR'.2.2 hq
  have hqrP : q * C.D.F.ρ.r ∈ sZero Ω W S :=
    inf_le_sZero ⟨S.mul_mem hqS hrS, (MGrp Ω W).mul_mem
      (Thompson.le_MGrp_of_mem_D C.D.F.ρ'.hR (by rw [C.hR']; exact hq))
      (Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR C.D.F.ρ.hr)⟩
  have hcR : ∀ v ∈ R, c * v * c⁻¹ = C.D.F.ρ.r * v * C.D.F.ρ.r⁻¹ := by
    refine conj_eq_of_gens (Subgroup.zpowers_le.mpr C.x₁_mem_R) C.card_R C.r_mem_R
      C.r_not_mem_zpowers ?_ ?_
    · rw [hinv _ C.D.x₁_mem, C.D.r₁]
    · rw [hcr, mul_inv_cancel_right]
      group
  have hqR : ∀ v ∈ R, q * v = v * q := fun v hv => (C.commutes_R_R' v hv q hq).symm
  have hrR' : ∀ v ∈ R', C.D.F.ρ.r * v = v * C.D.F.ρ.r := fun v hv =>
    C.commutes_R_R' _ C.r_mem_R v hv
  have hcq : c * q = q * c := by
    have e := hqv q hq
    calc c * q = c * q * c⁻¹ * c := by group
      _ = q * c := by rw [e]; group
  have hqr : q * C.D.F.ρ.r = C.D.F.ρ.r * q := (hrR' q hq).symm
  have hqU : q ∉ Subgroup.zpowers C.D.x₂ := by
    intro h
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    have e := hqv _ C.x₂_mem_R'
    rw [hinv _ C.D.x₂_mem, (Commute.zpow_self C.D.x₂ i).eq, mul_inv_cancel_right] at e
    have e3 : C.D.x₂ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← e]
      exact inv_mul_cancel _
    have := orderOf_dvd_of_pow_eq_one e3
    rw [C.orderOf_x₂] at this
    omega
  have hqq : q * q = z := by
    have hquat := hst.hyp.isQuatSub_of_mem_RSet hst.odd C.hd.hR'.1
    have hzR' : z ∈ R' := T7C.mem_of_isSylow2In hst.odd hst.hyp C.hs.hK'.1 (hR'syl C) C.hzK'
    exact AscL62.sq_eq_of_not_mem hquat (AscL62.isUniqueInvolution_of_le C.hzK' C.hd.hR'.2.1 hzR')
      (Subgroup.zpowers_le.mpr C.x₂_mem_R') inferInstance C.card_R' hq hqU
  have hcqr : c * (q * C.D.F.ρ.r) = (q * C.D.F.ρ.r) * c := by
    rw [← mul_assoc, hcq, mul_assoc, hcr, ← mul_assoc]
  have hqr2 : (q * C.D.F.ρ.r) * (q * C.D.F.ρ.r) = 1 := by
    calc (q * C.D.F.ρ.r) * (q * C.D.F.ρ.r) = q * (C.D.F.ρ.r * q) * C.D.F.ρ.r := by group
      _ = q * (q * C.D.F.ρ.r) * C.D.F.ρ.r := by rw [hqr]
      _ = (q * q) * (C.D.F.ρ.r * C.D.F.ρ.r) := by group
      _ = 1 := by rw [hqq, C.r_mul_self, C.hzK.sq]
  have hcqr' : c * (q * C.D.F.ρ.r)⁻¹ = (q * C.D.F.ρ.r)⁻¹ * c := by
    calc c * (q * C.D.F.ρ.r)⁻¹ = (q * C.D.F.ρ.r)⁻¹ * ((q * C.D.F.ρ.r) * c) *
          (q * C.D.F.ρ.r)⁻¹ := by group
      _ = (q * C.D.F.ρ.r)⁻¹ * (c * (q * C.D.F.ρ.r)) * (q * C.D.F.ρ.r)⁻¹ := by rw [hcqr]
      _ = (q * C.D.F.ρ.r)⁻¹ * c := by group
  refine ⟨c * (q * C.D.F.ρ.r)⁻¹, S.mul_mem hcS (S.inv_mem (S.mul_mem hqS hrS)), ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h2 := Subgroup.mul_mem _ h hqrP
    rw [inv_mul_cancel_right] at h2
    exact not_mem_sZero C hinv h2
  · calc c * (q * C.D.F.ρ.r)⁻¹ * (c * (q * C.D.F.ρ.r)⁻¹)
        = c * ((q * C.D.F.ρ.r)⁻¹ * c) * (q * C.D.F.ρ.r)⁻¹ := by group
      _ = c * (c * (q * C.D.F.ρ.r)⁻¹) * (q * C.D.F.ρ.r)⁻¹ := by rw [hcqr']
      _ = (c * c) * ((q * C.D.F.ρ.r) * (q * C.D.F.ρ.r))⁻¹ := by group
      _ = 1 := by rw [hc2, hqr2]; group
  · intro x hx hxN
    have h := (mem_or_inv_mul_mem_sZero C hcS hinv hx).resolve_left hxN
    have e : (c * (q * C.D.F.ρ.r)⁻¹)⁻¹ * x = (q * C.D.F.ρ.r) * (c⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ hqrP h
  · intro v hv
    have hv' : C.D.F.ρ.r⁻¹ * v * C.D.F.ρ.r ∈ R :=
      R.mul_mem (R.mul_mem (R.inv_mem C.r_mem_R) hv) C.r_mem_R
    have hqv' : q⁻¹ * v * q = v := by
      calc q⁻¹ * v * q = q⁻¹ * (v * q) := by group
        _ = q⁻¹ * (q * v) := by rw [hqR v hv]
        _ = v := by group
    have key : c * (q * C.D.F.ρ.r)⁻¹ * v * (c * (q * C.D.F.ρ.r)⁻¹)⁻¹ = v := by
      calc c * (q * C.D.F.ρ.r)⁻¹ * v * (c * (q * C.D.F.ρ.r)⁻¹)⁻¹
          = c * (C.D.F.ρ.r⁻¹ * (q⁻¹ * v * q) * C.D.F.ρ.r) * c⁻¹ := by group
        _ = c * (C.D.F.ρ.r⁻¹ * v * C.D.F.ρ.r) * c⁻¹ := by rw [hqv']
        _ = C.D.F.ρ.r * (C.D.F.ρ.r⁻¹ * v * C.D.F.ρ.r) * C.D.F.ρ.r⁻¹ := hcR _ hv'
        _ = v := by group
    calc v * (c * (q * C.D.F.ρ.r)⁻¹)
        = c * (q * C.D.F.ρ.r)⁻¹ * v * (c * (q * C.D.F.ρ.r)⁻¹)⁻¹ * (c * (q * C.D.F.ρ.r)⁻¹) := by
          rw [key]
      _ = c * (q * C.D.F.ρ.r)⁻¹ * v := by group
  · intro v hv
    have hv' : q⁻¹ * v * q ∈ R' := R'.mul_mem (R'.mul_mem (R'.inv_mem hq) hv) hq
    have key : c * (q * C.D.F.ρ.r)⁻¹ * v * (c * (q * C.D.F.ρ.r)⁻¹)⁻¹ = v := by
      calc c * (q * C.D.F.ρ.r)⁻¹ * v * (c * (q * C.D.F.ρ.r)⁻¹)⁻¹
          = c * (C.D.F.ρ.r⁻¹ * (q⁻¹ * v * q) * C.D.F.ρ.r) * c⁻¹ := by group
        _ = c * ((q⁻¹ * v * q) * C.D.F.ρ.r⁻¹ * C.D.F.ρ.r) * c⁻¹ := by
            rw [show C.D.F.ρ.r⁻¹ * (q⁻¹ * v * q) = (q⁻¹ * v * q) * C.D.F.ρ.r⁻¹ by
              calc C.D.F.ρ.r⁻¹ * (q⁻¹ * v * q)
                  = C.D.F.ρ.r⁻¹ * ((q⁻¹ * v * q) * C.D.F.ρ.r) * C.D.F.ρ.r⁻¹ := by group
                _ = C.D.F.ρ.r⁻¹ * (C.D.F.ρ.r * (q⁻¹ * v * q)) * C.D.F.ρ.r⁻¹ := by
                    rw [hrR' _ hv']
                _ = (q⁻¹ * v * q) * C.D.F.ρ.r⁻¹ := by group]
        _ = c * (q⁻¹ * v * q) * c⁻¹ := by group
        _ = q * (q⁻¹ * v * q) * q⁻¹ := hqv _ hv'
        _ = v := by group
    calc v * (c * (q * C.D.F.ρ.r)⁻¹)
        = c * (q * C.D.F.ρ.r)⁻¹ * v * (c * (q * C.D.F.ρ.r)⁻¹)⁻¹ * (c * (q * C.D.F.ρ.r)⁻¹) := by
          rw [key]
      _ = c * (q * C.D.F.ρ.r)⁻¹ * v := by group

end Ctx

variable (p f : ℕ) [Fact p.Prime]


theorem noGraph_of (h3 : S24B.H3 p f) : S24B.NoGraph p f := by
  intro G _ _ _ Ω K K' W S R R' z u hs hd h8 y hyS hyT
  by_contra hyW
  obtain ⟨C⟩ := S24B.Ctx8.nonempty hs hd h8
  have hinv : ∀ w ∈ W, y * w * y⁻¹ = w⁻¹ := by
    rcases acts_pm C hyS hyT with h | h
    · exfalso
      apply hyW
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      calc w * y = y * w * y⁻¹ * y := by rw [h w hw]
        _ = y * w := by group
    · exact h
  obtain ⟨k, hk⟩ := exists_centralizes_r C hyS hyT hinv
  have hx₃W : C.D.x₃ ^ k ∈ W := W.zpow_mem C.D.x₃_mem k
  have hc₀S : y * C.D.x₃ ^ k ∈ (S : Subgroup G) := S.mul_mem hyS (C.hd.hWS hx₃W)
  have hc₀T : S24B.TrivMu Ω W (y * C.D.x₃ ^ k) :=
    trivMu_mul (C.le_normalizer_W hyS) hyT (trivMu_of_mem_W hx₃W)
  have hc₀inv : ∀ w ∈ W, (y * C.D.x₃ ^ k) * w * (y * C.D.x₃ ^ k)⁻¹ = w⁻¹ := by
    intro w hw
    have e : C.D.x₃ ^ k * w * (C.D.x₃ ^ k)⁻¹ = w :=
      conj_eq_of_mem_centralizer (Subgroup.mem_centralizer_iff.mpr fun v hv =>
        Thompson.commutes_of_mem_WSet C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW v hv _ hx₃W) hw
    calc (y * C.D.x₃ ^ k) * w * (y * C.D.x₃ ^ k)⁻¹
        = y * (C.D.x₃ ^ k * w * (C.D.x₃ ^ k)⁻¹) * y⁻¹ := by group
      _ = w⁻¹ := by rw [e, hinv w hw]
  generalize y * C.D.x₃ ^ k = c₀ at hk hc₀S hc₀T hc₀inv
  have hc₀2 : c₀ * c₀ = 1 := graph_sq C h3 hc₀S hc₀T hc₀inv
  have hc₀N : c₀ ∉ sZero Ω W S := not_mem_sZero C hc₀inv
  have hc₀N' := C.le_normalizer_W hc₀S
  have hc₀K : conjSub c₀ K = K := by
    have h := C.fix_of_trivMu hc₀N' hc₀T C.D.F.ρ
    rwa [C.hK] at h
  have hc₀K' : conjSub c₀ K' = K' := C.conjSub_K'_of_K hc₀K
  suffices H : ∃ e ∈ (S : Subgroup G), e ∉ sZero Ω W S ∧ e * e = 1 ∧
      (∀ x ∈ (S : Subgroup G), x ∉ sZero Ω W S → e⁻¹ * x ∈ sZero Ω W S) ∧
      ∀ g : G, (∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer {e},
        g⁻¹ * y * g ∈ (S : Subgroup G)) → g⁻¹ * e * g ∉ sZero Ω W S by
    obtain ⟨e, heS, heN, he2, hidx, hfus⟩ := H
    have hne := CFSG.RankThree.PartTwo.Sec8.commutator_ne_top_of_extremal S
      (commutator_mem_sZero C hc₀S hc₀inv) heS heN (by rw [pow_two]; exact he2)
      (fun g hg => hidx _ (hg e ⟨heS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
        (hfus g hg))
    apply hne
    refine commutator_eq_top_of_simple ⟨C.D.F.ρ.r, C.D.x₁, fun h => ?_⟩
    have e1 : C.D.x₁⁻¹ = C.D.x₁ := by rw [← C.D.r₁, h]; group
    have e3 : C.D.x₁ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← e1]
      exact inv_mul_cancel _
    have := orderOf_dvd_of_pow_eq_one e3
    rw [C.orderOf_x₁] at this
    omega
  have hcaseI : ∀ {c : G}, c ∈ (S : Subgroup G) → c * c = 1 → (∀ w ∈ W, c * w * c⁻¹ = w⁻¹) →
      c * C.D.F.ρ.r = C.D.F.ρ.r * c → InnerOn c R' → ∃ e ∈ (S : Subgroup G),
        e ∉ sZero Ω W S ∧ e * e = 1 ∧
        (∀ x ∈ (S : Subgroup G), x ∉ sZero Ω W S → e⁻¹ * x ∈ sZero Ω W S) ∧
        ∀ g : G, (∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer {e},
          g⁻¹ * y * g ∈ (S : Subgroup G)) → g⁻¹ * e * g ∉ sZero Ω W S := by
    intro c hcS hc2 hcinv hcr hin
    obtain ⟨e, heS, heN, he2, hidx, heR, heR'⟩ := exists_caseI C hcS hc2 hcinv hcr hin
    exact ⟨e, heS, heN, he2, hidx, fun g hg => hfus_I C h3 heN he2 heR heR' g hg⟩
  by_cases hI : InnerOn c₀ R'
  · exact hcaseI hc₀S hc₀2 hc₀inv hk hI
  by_cases hA : ∀ a ∈ C.A, InnerOn a R'
  · exact ⟨c₀, hc₀S, hc₀N, hc₀2,
      fun x hx hxN => (mem_or_inv_mul_mem_sZero C hc₀S hc₀inv hx).resolve_left hxN,
      fun g hg => hfus_II C hc₀S hc₀2 hk hc₀K hI hA g hg⟩
  push Not at hA
  obtain ⟨a, ha, haout⟩ := hA
  obtain ⟨haS, haW, haR, haK', -⟩ := (C.mem_A).mp ha
  have haK'' : conjSub a K' = K' := mem_normalizer_iff_conjSub_eq.mp haK'
  have hax₂ : a * C.D.x₂ * a⁻¹ = C.D.x₂ := conj_eq_of_mem_centralizer haW C.D.x₂_mem
  obtain ⟨κ, hκ⟩ := exists_conj_s (Subgroup.zpowers_le.mpr C.x₂_mem_R') C.card_R' C.t_mem_R'
    C.t_not_mem_zpowers (conj_mem_R' C haS haK'') (Or.inl hax₂)
  obtain ⟨κ₀, hκ₀⟩ := exists_conj_s (Subgroup.zpowers_le.mpr C.x₂_mem_R') C.card_R' C.t_mem_R'
    C.t_not_mem_zpowers (conj_mem_R' C hc₀S hc₀K') (Or.inr (hc₀inv _ C.D.x₂_mem))
  have hκo : ¬ Even κ := fun h => haout ((innerOn_R'_iff C haS haK'' hκ).mpr h)
  have hκ₀o : ¬ Even κ₀ := fun h => hI ((innerOn_R'_iff C hc₀S hc₀K' hκ₀).mpr h)
  obtain ⟨κ₁, hκ₁e, hκ₁⟩ := conj_s_mul (Or.inr (hc₀inv _ C.D.x₂_mem)) hκ₀ hκ
  have hc₁S : c₀ * a ∈ (S : Subgroup G) := S.mul_mem hc₀S haS
  have hc₁K' : conjSub (c₀ * a) K' = K' := by rw [conjSub_mul, haK'', hc₀K']
  have hc₁in : InnerOn (c₀ * a) R' :=
    (innerOn_R'_iff C hc₁S hc₁K' hκ₁).mpr (hκ₁e.mpr (iff_of_false hκ₀o hκo))
  have hc₁T : S24B.TrivMu Ω W (c₀ * a) := trivMu_mul hc₀N' hc₀T (trivMu_of_mem_A C ha)
  have hc₁inv : ∀ w ∈ W, (c₀ * a) * w * (c₀ * a)⁻¹ = w⁻¹ := by
    intro w hw
    calc (c₀ * a) * w * (c₀ * a)⁻¹ = c₀ * (a * w * a⁻¹) * c₀⁻¹ := by group
      _ = w⁻¹ := by rw [conj_eq_of_mem_centralizer haW hw, hc₀inv w hw]
  have hc₁2 : (c₀ * a) * (c₀ * a) = 1 := graph_sq C h3 hc₁S hc₁T hc₁inv
  have hc₁r : (c₀ * a) * C.D.F.ρ.r = C.D.F.ρ.r * (c₀ * a) := by
    have har : a * C.D.F.ρ.r = C.D.F.ρ.r * a :=
      (Subgroup.mem_centralizer_iff.mp haR _ C.r_mem_R).symm
    rw [mul_assoc, har, ← mul_assoc, hk, mul_assoc]
  exact hcaseI hc₁S hc₁2 hc₁inv hc₁r hc₁in

end S24

end CFSG.ClassicalInvolution.Asc77
