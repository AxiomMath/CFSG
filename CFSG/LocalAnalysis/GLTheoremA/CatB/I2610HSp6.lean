module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HL2
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFixInf
import CFSG.Timmesfeld.LieEmbed.SpF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6

theorem card_pSimple_sp6_of_pow_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    [IsSimpleGroup (StatedProj (StatedSp 3 K))]
    {α : MulAut (StatedProj (StatedSp 3 K))} (hα : α ^ 3 = 1)
    {J : Subgroup (StatedProj (StatedSp 3 K))} (hJ : GLAPComponent 3 (fixSubgroup α) J) :
    Nat.card (PSimple 3 J) = 360 ∨ Nat.card (PSimple 3 J) = 1451520 := by
  have hcardT : Nat.card (StatedProj (StatedSp 3 K)) = 1451520 := by
    rw [Nat.card_congr (CFSG.Monster.Existence.Compat.statedProjEquivOfBot
        (StatedSp 3 K)
        (CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK (Fin 3 ⊕ Fin 3))).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
    decide
  have hnc : ∃ a b : StatedProj (StatedSp 3 K), a * b ≠ b * a :=
    exists_noncomm_of_simple_not_prime (by rw [hcardT]; norm_num)
  obtain ⟨t, rfl⟩ := inner_of_card_two hK α
  have ht3 : t ^ 3 = 1 := by
    have h1 : MulAut.conj (t ^ 3) = 1 := by rw [map_pow, hα]
    have h2 : t ^ 3 ∈ Subgroup.center (StatedProj (StatedSp 3 K)) :=
      mem_center_of_conj_eq_one h1
    rw [center_eq_bot_of_simple hnc, Subgroup.mem_bot] at h2
    exact h2
  by_cases ht1 : t = 1
  · subst ht1
    rw [fixSubgroup_conj_one] at hJ
    obtain ⟨f⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv Nat.prime_three hnc hJ
    exact Or.inr (by rw [Nat.card_congr f.toEquiv, hcardT])
  · have hord : orderOf t = 3 := orderOf_eq_prime ht3 ht1
    have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
    obtain ⟨x, ⟨hxt, hxo⟩, -⟩ :=
      (CFSG.RankThree.Classical.symplectic_cross_prime_primary_centralizer_blocks
        (r := 3) Nat.prime_two le_rfl hK' Nat.prime_three (by norm_num) (by norm_num)
        (by norm_num) t hord).1
    have hblocks := (CFSG.RankThree.Classical.symplectic_cross_prime_primary_centralizer_blocks
        (r := 3) Nat.prime_two le_rfl hK' Nat.prime_three (by norm_num) (by norm_num)
        (by norm_num) t hord).2 x hxt hxo
    subst hxt
    have hx3 : x ^ 3 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hxo] at this
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact ht1 (map_one _)
    obtain ⟨e⟩ := components_A6 hK hx3 hx1 hblocks hJ
    exact Or.inl (by rw [Nat.card_congr e.toEquiv, card_alternating_six])

theorem not_catalogIs_isL2prime_of_card_eq_360 {X : Type} [Group X] (h : Nat.card X = 360) :
    ¬ catalogIs X isL2prime := by
  intro hc
  rcases card_of_catalogIs_isL2prime hc with h60 | ⟨r, hrprime, hr7, hr⟩
  · omega
  · have hr2 : r ≠ 2 := by omega
    have hodd : Odd r := hrprime.odd_of_ne_two hr2
    have h2 : 2 ∣ r ^ 2 - 1 :=
      (show 2 ∣ 8 by norm_num).trans (Nat.eight_dvd_sq_sub_one_of_odd hodd)
    have h2' : 2 ∣ r * (r ^ 2 - 1) := dvd_mul_of_dvd_right h2 r
    have hdiv : r * (r ^ 2 - 1) / 2 = 360 := by omega
    have heq : r * (r ^ 2 - 1) = 720 := by
      have hm := Nat.div_mul_cancel h2'
      omega
    have hdvd : r ∣ 720 := ⟨r ^ 2 - 1, by rw [← heq]⟩
    have h' : r ∣ 2 ^ 4 * 3 ^ 2 * 5 := by norm_num; exact hdvd
    rcases hrprime.dvd_mul.mp h' with h1 | h5
    · rcases hrprime.dvd_mul.mp h1 with h2 | h3
      · have hr2' : r = 2 :=
          (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_two).1 (hrprime.dvd_of_dvd_pow h2)
        omega
      · have hr3 : r = 3 :=
          (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_three).1 (hrprime.dvd_of_dvd_pow h3)
        omega
    · have hr5 : r = 5 := (Nat.prime_dvd_prime_iff_eq hrprime (by norm_num)).1 h5
      omega

theorem not_catalogIs_isL2prime_of_card_eq_1451520 {X : Type} [Group X]
    (h : Nat.card X = 1451520) : ¬ catalogIs X isL2prime := by
  intro hc
  rcases card_of_catalogIs_isL2prime hc with h60 | ⟨r, hrprime, hr7, hr⟩
  · omega
  · have hr2 : r ≠ 2 := by omega
    have hodd : Odd r := hrprime.odd_of_ne_two hr2
    have h2 : 2 ∣ r ^ 2 - 1 :=
      (show 2 ∣ 8 by norm_num).trans (Nat.eight_dvd_sq_sub_one_of_odd hodd)
    have h2' : 2 ∣ r * (r ^ 2 - 1) := dvd_mul_of_dvd_right h2 r
    have hdiv : r * (r ^ 2 - 1) / 2 = 1451520 := by omega
    have heq : r * (r ^ 2 - 1) = 2903040 := by
      have hm := Nat.div_mul_cancel h2'
      omega
    have hdvd : r ∣ 2903040 := ⟨r ^ 2 - 1, by rw [← heq]⟩
    have h' : r ∣ 2 ^ 10 * 3 ^ 4 * 5 * 7 := by norm_num; exact hdvd
    rcases hrprime.dvd_mul.mp h' with h1 | h7
    · rcases hrprime.dvd_mul.mp h1 with h2 | h5
      · rcases hrprime.dvd_mul.mp h2 with h2 | h3
        · have hr2' : r = 2 :=
            (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_two).1 (hrprime.dvd_of_dvd_pow h2)
          omega
        · have hr3 : r = 3 :=
            (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_three).1 (hrprime.dvd_of_dvd_pow h3)
          omega
      · have hr5 : r = 5 := (Nat.prime_dvd_prime_iff_eq hrprime (by norm_num)).1 h5
        omega
    · have hr7' : r = 7 := (Nat.prime_dvd_prime_iff_eq hrprime (by norm_num)).1 h7
      rw [hr7'] at heq
      norm_num at heq

theorem not_catalogIs_isL2prime_of_quot_sp6 {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (e : L ⧸ Subgroup.center L ≃* StatedSp 3 F ⧸ Subgroup.center (StatedSp 3 F))
    {β : MulAut L} (hβ : β ^ 3 = 1) {J : Subgroup L} (hJ : GLAPComponent 3 (fixSubgroup β) J) :
    ¬ catalogIs (PSimple 3 J) isL2prime := by
  classical
  intro hcat
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    charP_of_card_eq_prime (p := 2) (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have hcenter : Subgroup.center (StatedSp 3 F) = ⊥ :=
    CFSG.Timmesfeld.LieEmbed.center_statedSp_eq_bot (K := F)
  have hscal : StatedScalars (Fin 3 ⊕ Fin 3) F = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hF (Fin 3 ⊕ Fin 3)
  let ψ : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp 3 F) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientBot.trans
        (CFSG.Monster.Existence.Compat.statedProjEquivOfBot (StatedSp 3 F) hscal).symm))
  haveI hLsimple : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2
  haveI hPsimple : IsSimpleGroup (StatedProj (StatedSp 3 F)) := ψ.symm.isSimpleGroup
  let π : L →* StatedProj (StatedSp 3 F) :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπsurj : Function.Surjective π :=
    ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker ≤ Subgroup.center L := by
    rw [show π.ker = (QuotientGroup.mk' (Subgroup.center L)).ker from
      MonoidHom.ker_comp_of_injective _ _ ψ.injective, QuotientGroup.ker_mk']
  let βbar : MulAut (L ⧸ Subgroup.center L) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L β
  have hβbar_apply : ∀ k : L, βbar (QuotientGroup.mk k) = QuotientGroup.mk (β k) := fun k =>
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk β k
  have hβbar3 : βbar ^ 3 = 1 := by
    change (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L β) ^ 3 = 1
    rw [← map_pow, hβ, map_one]
  let α : MulAut (StatedProj (StatedSp 3 F)) := MulAut.congr ψ βbar
  have hα3 : α ^ 3 = 1 := by
    change (MulAut.congr ψ βbar) ^ 3 = 1
    rw [← map_pow, hβbar3, map_one]
  have hαβ : ∀ k : L, π (β k) = α (π k) := by
    intro k
    show ψ (QuotientGroup.mk (β k)) = MulAut.congr ψ βbar (ψ (QuotientGroup.mk k))
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      hβbar_apply]
  have hJmap : GLAPComponent 3 (fixSubgroup α) (J.map π) := by
    have hJ' : GLAPComponent 3 (⨅ _ : Unit, fixSubgroup β) J := by
      simpa only [iInf_const] using hJ
    have h := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_iInf_fixSubgroup
      (ι := Unit) π hπker (fun _ : Unit => β) (fun _ : Unit => α) (fun _ k => hαβ k)
      hπsurj Nat.prime_three hJ'
    simpa only [iInf_const] using h
  obtain ⟨eJ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_map Nat.prime_three π hJ hJmap
  have hcard : Nat.card (PSimple 3 J) = Nat.card (PSimple 3 (J.map π)) :=
    Nat.card_congr eJ.toEquiv
  rcases card_pSimple_sp6_of_pow_three hF hα3 hJmap with h360 | h1451
  · exact not_catalogIs_isL2prime_of_card_eq_360 (hcard.trans h360) hcat
  · exact not_catalogIs_isL2prime_of_card_eq_1451520 (hcard.trans h1451) hcat

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

end
