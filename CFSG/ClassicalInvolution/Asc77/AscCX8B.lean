module

public import CFSG.ClassicalInvolution.Asc77.AscCX6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_centralizer_of_trivialOnQuot {Y : Subgroup G} {e z t h₀ : G}
    (he2 : IsPGroup 2 (Subgroup.zpowers e)) (heY : e ∈ trivialOnQuot Y)
    (hez : e * z = z * e) (het : e * t = t * e) (hh₀ : h₀ ∈ Y) (hzt : h₀ * z * h₀⁻¹ = t) :
    ∃ h ∈ Subgroup.centralizer ({e} : Set G), h * z * h⁻¹ = t := by
  set N : Subgroup G := oddCoreIn Y ⊓ Subgroup.centralizer ({z} : Set G) with hN
  have hNodd : Odd (Nat.card N) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn Y) (Subgroup.card_dvd_of_le inf_le_left)
  have hEY : Subgroup.zpowers e ≤ trivialOnQuot Y := Subgroup.zpowers_le.mpr heY
  have hEz : Subgroup.zpowers e ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hez)
  have hEt : Subgroup.zpowers e ≤ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr het)
  have hAN : ∀ a ∈ Subgroup.zpowers e, ∀ n ∈ N, a * n * a⁻¹ ∈ N := by
    intro a ha n hn
    refine ⟨conj_mem_oddCoreIn_of_mem_normalizer (hEY ha).1 hn.1, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hEz ha) hn.2) (Subgroup.inv_mem _ (hEz ha))
  have hx : ∀ a ∈ Subgroup.zpowers e, h₀⁻¹ * (a * h₀ * a⁻¹) ∈ N := by
    intro a ha
    refine ⟨?_, ?_⟩
    · have h1 := (oddCoreIn Y).inv_mem ((hEY ha).2 h₀⁻¹ (Y.inv_mem hh₀))
      have e1 : h₀⁻¹ * (a * h₀ * a⁻¹) = ⁅a, h₀⁻¹⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact h1
    · have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp (hEz ha)
      have hat : a * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp (hEt ha)
      have hconj : (a * h₀ * a⁻¹) * z * (a * h₀ * a⁻¹)⁻¹ = t := by
        calc (a * h₀ * a⁻¹) * z * (a * h₀ * a⁻¹)⁻¹ = a * h₀ * (a⁻¹ * z * a) * h₀⁻¹ * a⁻¹ := by
              group
          _ = a * h₀ * z * h₀⁻¹ * a⁻¹ := by
              rw [show a⁻¹ * z * a = z by rw [mul_assoc, ← haz]; group]
          _ = a * t * a⁻¹ := by rw [← hzt]; group
          _ = t := by rw [hat]; group
      show h₀⁻¹ * (a * h₀ * a⁻¹) ∈ Subgroup.centralizer ({z} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : (h₀⁻¹ * (a * h₀ * a⁻¹)) * z * (h₀⁻¹ * (a * h₀ * a⁻¹))⁻¹ = z := by
        calc (h₀⁻¹ * (a * h₀ * a⁻¹)) * z * (h₀⁻¹ * (a * h₀ * a⁻¹))⁻¹ =
            h₀⁻¹ * ((a * h₀ * a⁻¹) * z * (a * h₀ * a⁻¹)⁻¹) * h₀ := by group
          _ = h₀⁻¹ * t * h₀ := by rw [hconj]
          _ = z := by rw [← hzt]; group
      calc (h₀⁻¹ * (a * h₀ * a⁻¹)) * z =
          (h₀⁻¹ * (a * h₀ * a⁻¹)) * z * (h₀⁻¹ * (a * h₀ * a⁻¹))⁻¹ *
            (h₀⁻¹ * (a * h₀ * a⁻¹)) := by group
        _ = z * (h₀⁻¹ * (a * h₀ * a⁻¹)) := by rw [h2]
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mem_coset_of_isPGroup he2 hNodd hAN hx
  refine ⟨h₀ * n, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hfix e (Subgroup.mem_zpowers e)
    calc h₀ * n * e = e * (h₀ * n) * e⁻¹ * e := by rw [h1]
      _ = e * (h₀ * n) := by group
  · have hnz : n * z = z * n := Subgroup.mem_centralizer_singleton_iff.mp hn.2
    calc h₀ * n * z * (h₀ * n)⁻¹ = h₀ * (n * z) * n⁻¹ * h₀⁻¹ := by group
      _ = h₀ * (z * n) * n⁻¹ * h₀⁻¹ := by rw [hnz]
      _ = h₀ * z * h₀⁻¹ := by group
      _ = t := hzt

end Lift

section Trivial

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem mem_trivialOnQuot_of_good (h6 : Layer6Twin p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {b e : G} (hbA : b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbbad : z ∉ zStarOf (Subgroup.centralizer ({b} : Set G)))
    (heA : e ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (heb : e ∈ Subgroup.centralizer ({b} : Set G))
    (hgood : z ∈ zStarOf (Subgroup.centralizer ({e * z} : Set G))) :
    e ∈ trivialOnQuot (exactLayer Ω b) := by
  classical
  have hzA : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    T7T.z_mem_centralizer_of_hyp hyp
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hΩ : HypOmegaMod p f Ω := hyp.std.setting.stand.hyp
  set E := Subgroup.zpowers e ⊔ Subgroup.zpowers z with hE
  have heE : e ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers e)
  have hzE : z ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hEA : E ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr heA) (Subgroup.zpowers_le.mpr hzA)
  have hE2 : IsPGroup 2 E := S.isPGroup'.to_le (hEA.trans inf_le_left)
  have hEb : E ≤ Subgroup.centralizer ({b} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr heb) (Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr (hzS b hbA.1).symm))
  obtain ⟨hzY, hK₂, hK₂', hcen, hO, hO', hT2, hT3⟩ :=
    twinFacts_of_bad h6 hyp hbA hb2 hb1 hbbad
  have hEY : ∀ x ∈ E, conjSub x (exactLayer Ω b) = exactLayer Ω b := fun x hx =>
    conjSub_exactLayer hΩ.conjInvariant (hEb hx)
  set lam := layerHom (exactLayer Ω b) E hEY with hlam
  have hb2' : IsPGroup 2 (Subgroup.zpowers b) := isPGroup_zpowers_of_sq_eq_one hb2
  have hfixK : ∀ x : E, ∀ y ∈ T7H.exactImg Ω b K, lam x y = y := fun x y hy =>
    layerAut_fix_exactImg hΩ hb2' hK₂ hO (hEb x.2) (mem_trivialOnQuot_of_mem_A hyp (hEA x.2)).1
      y hy
  have hfixK' : ∀ x : E, ∀ y ∈ T7H.exactImg Ω b K', lam x y = y := fun x y hy =>
    layerAut_fix_exactImg hΩ hb2' hK₂' hO' (hEb x.2) (mem_trivialOnQuot_of_mem_A hyp (hEA x.2)).2
      y hy
  have hP2 : IsPGroup 2 lam.range := by
    rw [MonoidHom.range_eq_map]
    exact (hE2.to_subgroup ⊤).map lam
  obtain ⟨hexpP, -⟩ := hT2 lam.range hP2 fun β hβ => by
    obtain ⟨x, rfl⟩ := hβ
    exact ⟨hfixK x, hfixK' x⟩
  let z₀ : E := ⟨z, hzE⟩
  let e₀ : E := ⟨e, heE⟩
  have hlamz : lam z₀ = MulAut.conj (T7H.toBar Ω b z hzY) := by
    ext y
    refine QuotientGroup.induction_on y fun y => ?_
    rw [hlam, layerHom_apply, C25Y.layerAut_mk, MulAut.conj_apply]
    unfold T7H.toBar
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1
  set F := Subgroup.zpowers (e * z) with hF
  have hezE : e * z ∈ E := E.mul_mem heE hzE
  have hFE : F ≤ E := Subgroup.zpowers_le.mpr hezE
  have hF2 : IsPGroup 2 F := hE2.to_le hFE
  have hFb : F ≤ Subgroup.centralizer ({b} : Set G) := hFE.trans hEb
  have hzF : z ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hzS g ((hEA (hFE hg)).1)
  have hgoodF : z ∈ zStarOf (Subgroup.centralizer (F : Set G)) := by
    rw [hF, centralizer_zpowers_eq_singleton']
    exact hgood
  have hlamF : ∀ g (hg : g ∈ F), ∃ k : ℤ,
      C25Y.layerAut (exactLayer Ω b) (conjSub_exactLayer hΩ.conjInvariant (hFb hg)) =
        (lam (e₀ * z₀)) ^ k := by
    intro g hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, ?_⟩
    have h1 : (⟨g, hFE hg⟩ : E) = (e₀ * z₀) ^ k := by
      apply Subtype.ext
      simp only [Subgroup.coe_zpow, Subgroup.coe_mul]
      exact hk.symm
    rw [← map_zpow, ← h1]
    rfl
  by_cases hβ1 : lam e₀ = 1
  · have htriv : ∀ g (hg : g ∈ Subgroup.zpowers e), ∀ y, C25Y.layerAut (exactLayer Ω b)
        (conjSub_exactLayer hΩ.conjInvariant
          ((Subgroup.zpowers_le.mpr heb) hg)) y = y := by
      intro g hg y
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      have h1 : (⟨g, Subgroup.mem_sup_left hg⟩ : E) = e₀ ^ k := by
        apply Subtype.ext
        simp only [Subgroup.coe_zpow]
        exact hk.symm
      have h2 : lam ⟨g, Subgroup.mem_sup_left hg⟩ = 1 := by rw [h1, map_zpow, hβ1, one_zpow]
      have := congrArg (fun φ => φ y) h2
      simpa [hlam, layerHom_apply] using this
    exact le_trivialOnQuot_of_layerAut_trivial hΩ (Subgroup.zpowers_le.mpr heb) htriv
      (Subgroup.mem_zpowers e)
  · exfalso
    have hez2 : lam (e₀ * z₀) * lam (e₀ * z₀) = 1 := hexpP _ ⟨_, rfl⟩
    by_cases hβz : lam e₀ = lam z₀
    ·
      have hez1 : lam (e₀ * z₀) = 1 := by
        rw [map_mul, hβz]
        exact hexpP _ ⟨_, rfl⟩
      refine not_mem_zStarOf_of_layerAut_trivial hΩ hF2 hFb hzF hzY hz2 hz1 hcen ?_ hgoodF
      intro g hg y
      obtain ⟨k, hk⟩ := hlamF g hg
      rw [hk, hez1, one_zpow, MulAut.one_apply]
    ·
      have hne1 : lam (e₀ * z₀) ≠ 1 := by
        intro h
        apply hβz
        rw [map_mul] at h
        calc lam e₀ = lam e₀ * lam z₀ * (lam z₀)⁻¹ := by group
          _ = (lam z₀)⁻¹ := by rw [h, one_mul]
          _ = lam z₀ := by
            rw [inv_eq_of_mul_eq_one_right (hexpP _ ⟨_, rfl⟩)]
      have hnez : lam (e₀ * z₀) ≠ MulAut.conj (T7H.toBar Ω b z hzY) := by
        rw [← hlamz]
        intro h
        apply hβ1
        rw [map_mul] at h
        calc lam e₀ = lam e₀ * lam z₀ * (lam z₀)⁻¹ := by group
          _ = 1 := by rw [h, mul_inv_cancel]
      obtain ⟨xb, hxbfix, hxbz, hxbc⟩ := hT3 (lam (e₀ * z₀)) (hfixK _) (hfixK' _) hez2 hne1
        hnez
      refine not_mem_zStarOf_of_layerAut_fix hΩ hF2 hFb hzY hz2 (x := xb) ?_ hxbz hxbc hgoodF
      intro g hg
      obtain ⟨k, hk⟩ := hlamF g hg
      rw [hk]
      have hstab : lam (e₀ * z₀) ∈
          MulAction.stabilizer (MulAut (↥(exactLayer Ω b) ⧸
            classicalInvolutionOddCore ↥(exactLayer Ω b))) xb := hxbfix
      exact (MulAction.stabilizer _ xb).zpow_mem hstab k

end Trivial

end CFSG.ClassicalInvolution.Asc77.CX
