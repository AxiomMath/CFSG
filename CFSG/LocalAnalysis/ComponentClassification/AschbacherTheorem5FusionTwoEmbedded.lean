module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5FusionTwoAction
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingSolvable
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5FusionTwoBasic

public section

open CFSG.Open CFSG.ABGLocalTools CFSG.BenderSuzuki CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace FusionTwo

@[expose] noncomputable def quotAut {X : Type*} [Group X] (O : Subgroup X)
    [hO : O.Characteristic] : MulAut X →* MulAut (X ⧸ O) where
  toFun α := QuotientGroup.congr O O α (Subgroup.characteristic_iff_map_eq.mp hO α)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' α β := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

theorem quotAut_mk {X : Type*} [Group X] (O : Subgroup X) [O.Characteristic] (α : MulAut X)
    (x : X) : quotAut O α (x : X ⧸ O) = (α x : X ⧸ O) :=
  rfl

theorem exists_derivedSeries_succ_eq (Y : Type*) [Group Y] [Finite Y] :
    ∃ n, derivedSeries Y (n + 1) = derivedSeries Y n := by
  by_contra h
  push Not at h
  have hlt : ∀ n, Nat.card (derivedSeries Y (n + 1)) < Nat.card (derivedSeries Y n) := fun n =>
    Subgroup.card_lt_of_lt (lt_of_le_of_ne (derivedSeries_antitone Y (Nat.le_succ n)) (h n))
  have hbound : ∀ n, Nat.card (derivedSeries Y n) + n ≤ Nat.card Y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hlt n
      omega
  have h1 := hbound (Nat.card Y + 1)
  have h2 : 0 < Nat.card (derivedSeries Y (Nat.card Y + 1)) := Nat.card_pos
  omega

theorem two_le_twoRank_of_four {X : Type*} [Group X] [Finite X] (h : TwoRankAtLeastTwo X) :
    2 ≤ twoRank X := by
  obtain ⟨E, hcard, hsq⟩ := h
  have hE : IsElemAbelian 2 E := by
    refine ⟨isMulCommutative_of_forall_sq_one hsq, ?_⟩
    intro e he
    exact congrArg Subtype.val (hsq ⟨e, he⟩)
  exact CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary X E hE 2 (by
    rw [hcard]
    norm_num)

theorem mem_of_conj_mem_of_involution {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : fusionStronglyEmbedded M) {w y : X} (hw : orderOf w = 2) (hwM : w ∈ M)
    (hy : y * w * y⁻¹ ∈ M) : y ∈ M := by
  by_contra hyM
  have hodd := hM.2.2 y hyM
  have hmem : w ∈ M ⊓ M.map (MulAut.conj y⁻¹).toMonoidHom := by
    refine Subgroup.mem_inf.mpr ⟨hwM, ?_⟩
    rw [Subgroup.mem_map_equiv]
    simpa [MulAut.conj_symm_apply] using hy
  have hdvd := orderOf_dvd_natCard
    (⟨w, hmem⟩ : (M ⊓ M.map (MulAut.conj y⁻¹).toMonoidHom : Subgroup X))
  rw [Subgroup.orderOf_mk, hw] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem false_of_rank_le_one {Hs : Subgroup G}
    (hodd : ∀ K : Subgroup G, K.Normal → Odd (Nat.card K) → K ≤ Hs) {N : Subgroup G}
    [hNn : N.Normal] (hM : fusionStronglyEmbedded (Hs.subgroupOf N))
    (hrank : ¬ TwoRankAtLeastTwo N) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Hs.subgroupOf N) 2
    (even_iff_two_dvd.mp hM.2.1)
  set w' : N := (w : N) with hw'
  have hw2 : orderOf w' = 2 := by rw [hw', Subgroup.orderOf_coe, hw]
  have hiso : ∀ g : N, (g * w' * g⁻¹) * w' = w' * (g * w' * g⁻¹) → g * w' * g⁻¹ = w' := by
    intro g hcomm
    by_contra hne
    apply hrank
    have hg2 : orderOf (g * w' * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hw2]
    obtain ⟨hE, hcard, -⟩ :=
      CFSG.ProperTwoGeneratedCore.commuting_distinct_involutions_four_group hw2 hg2 hcomm.symm hne
    exact ⟨_, hcard, fun x => Subtype.ext (hE.2 x x.2)⟩
  apply hM.1
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨c, hc, k, hk, rfl⟩ := zStar_factor hw2 hiso x
  apply Subgroup.mul_mem
  · apply mem_of_conj_mem_of_involution hM hw2 w.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact w.2
  · have hk' := oddCore_le_pPrimeCore N hk
    have hle := hodd ((CFSG.pPrimeCore 2 N).map N.subtype) inferInstance (by
      rw [Subgroup.card_map_of_injective N.subtype_injective]
      exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := N)))
    exact hle ⟨k, hk', rfl⟩

theorem false_of_bender (hC : Counterexample G D r Abar)
    (S : Sylow 2 G) (hSH : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    {N : Subgroup G} [hNn : N.Normal]
    (hM : fusionStronglyEmbedded ((Subgroup.normalizer (D : Set G)).subgroupOf N))
    (hrank : TwoRankAtLeastTwo N) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hC.hyp
  obtain ⟨i₀, -⟩ : ∃ i : Fin r, True := ⟨⟨0, by have := hyp.hr; omega⟩, trivial⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := (Subgroup.normalizer (D : Set G)).subgroupOf N) 2 (even_iff_two_dvd.mp hM.2.1)
  set w' : N := (w : N) with hw'
  have hw2 : orderOf w' = 2 := by rw [hw', Subgroup.orderOf_coe, hw]
  have hMsolv := strongly_embedded_solvable N _ hM (two_le_twoRank_of_four hrank)
  have hHN : Group.IsSolvable (Subgroup.normalizer (D : Set G) ⊓ N : Subgroup G) := by
    let f : (Subgroup.normalizer (D : Set G)).subgroupOf N →*
        (Subgroup.normalizer (D : Set G) ⊓ N : Subgroup G) :=
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.mpr ⟨x.2, x.1.2⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_surjective (f := f) ?_
    intro y
    obtain ⟨hyH, hyN⟩ := Subgroup.mem_inf.mp y.2
    exact ⟨⟨⟨y, hyN⟩, hyH⟩, rfl⟩
  rcases theorem_SE _ hM.to_native with hlow | hB
  · exact hlow (twoRankAtLeastTwo_involutionCore_iff.mpr hrank)
  obtain ⟨hBender, hOle, -⟩ := hB
  set K : Subgroup N := involutionCore N with hKdef
  have hOc : (twoPrimeCore K).Characteristic := by
    simpa [twoPrimeCore] using (CFSG.pPrimeCore_characteristic (p := 2) (G := K))
  let Φ : G →* MulAut (K ⧸ twoPrimeCore K) :=
    (quotAut (twoPrimeCore K)).comp ((MulAut.characteristic K).comp MulAut.conjNormal)
  have hΦ : ∀ (g : G) (k : K), Φ g (k : K ⧸ twoPrimeCore K) =
      ((MulAut.characteristic K (MulAut.conjNormal g) k : K) : K ⧸ twoPrimeCore K) :=
    fun _ _ => rfl
  have hΦval : ∀ (g : G) (k : K),
      (((MulAut.characteristic K (MulAut.conjNormal g) k : K) : N) : G) =
        g * ((k : N) : G) * g⁻¹ := fun _ _ => rfl
  have hwK : w' ∈ K := by
    apply Subgroup.subset_closure
    refine ⟨fun h => ?_, by rw [← hw2, pow_orderOf_eq_one]⟩
    rw [h, orderOf_one] at hw2
    omega
  set KG : Subgroup G := K.map N.subtype with hKG
  set R : Subgroup G := (S : Subgroup G) ⊓ KG with hR
  have hRH : R ≤ Subgroup.normalizer (D : Set G) := inf_le_left.trans hSH
  have hRN : R ≤ N := inf_le_right.trans (Subgroup.map_subtype_le K)
  have hR2 : IsPGroup 2 R := S.isPGroup'.to_inf_left
  have hSyl : IsSylowOf 2 (S : Subgroup G) ⊤ := isSylowOf_iff.mpr
    ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  have hRK : IsSylowOf 2 R KG := hSyl.inf_of_le_normalizer le_top (by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance])
  have hRmap : (R.subgroupOf N).map N.subtype = R := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRN]
  have hRK' : IsSylowOf 2 (R.subgroupOf N) K := by
    rw [← isSylowOf_map_subtype_iff N, hRmap]
    exact hRK
  obtain ⟨Q, hQ⟩ := hRK'.exists_sylow_eq_subgroupOf
  have hQR : ∀ q ∈ (Q : Subgroup K), (((q : K) : N) : G) ∈ R := by
    intro q hq
    rw [hQ] at hq
    exact hq
  set T := Q.mapSurjective (QuotientGroup.mk'_surjective (twoPrimeCore K)) with hT
  have htriv : ∀ x ∈ R, ∀ d ∈ D, d⁻¹ * (x * d * x⁻¹) ∈ aschbacherThm5Core D :=
    fun x hx d hd => conj_mem_core_of_solvable hyp hHN (hRH hx) (hRN hx) hd
  set C₀ : Subgroup G := Subgroup.centralizer (R : Set G) ⊓ D with hC₀
  have hcover : ∀ d ∈ D, ∃ c ∈ C₀, c⁻¹ * d ∈ aschbacherThm5Core D := by
    intro d hd
    obtain ⟨c, hcD, hcR, hco⟩ := exists_centralizer_cover hR2 hRH htriv hd
    refine ⟨c, Subgroup.mem_inf.mpr ⟨?_, hcD⟩, hco⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hcR x hx
    calc x * c = (x * c * x⁻¹) * x := by group
      _ = c * x := by rw [h]
  obtain ⟨n, hn⟩ := exists_derivedSeries_succ_eq C₀
  set P : Subgroup C₀ := derivedSeries C₀ n with hP
  have hPperf : Group.IsPerfect P := by
    rw [Subgroup.isPerfect_iff, hP, ← derivedSeries_succ, hn]
  have hglaub : P.map (Φ.comp C₀.subtype) = ⊥ := by
    apply CFSG.ComponentClassification.AschbacherToolkit.glaubermanBenderPerfect
      (K ⧸ twoPrimeCore K) hBender T
    · exact Group.IsPerfect.map _
    · intro α hα s hs
      obtain ⟨c, -, rfl⟩ := hα
      rw [hT, Sylow.coe_mapSurjective] at hs
      obtain ⟨q, hq, rfl⟩ := hs
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply, hΦ]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      rw [hΦval]
      have hcR := (Subgroup.mem_inf.mp c.2).1
      have hqc := Subgroup.mem_centralizer_iff.mp hcR _ (hQR q hq)
      calc (c : G) * ((q : N) : G) * (c : G)⁻¹ = ((q : N) : G) * c * (c : G)⁻¹ := by
            rw [← hqc]
        _ = ((q : N) : G) := by group
  have hPker : ∀ p ∈ P, Φ ((p : C₀) : G) = 1 := by
    intro p hp
    have : (Φ.comp C₀.subtype) p ∈ P.map (Φ.comp C₀.subtype) := Subgroup.mem_map_of_mem _ hp
    rw [hglaub, Subgroup.mem_bot] at this
    exact this
  have hperfD : Group.IsPerfect (D ⧸ aschbacherThm5OddCore D) :=
    quotient_perfect_of_semisimple_factors Abar hyp.hsemisimple hyp.hgen
  set ψ : C₀ →* D ⧸ aschbacherThm5OddCore D :=
    (QuotientGroup.mk' (aschbacherThm5OddCore D)).comp
      (Subgroup.inclusion (inf_le_right : C₀ ≤ D)) with hψ
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) q
    obtain ⟨c, hc, hco⟩ := hcover d d.2
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply]
    apply QuotientGroup.eq.mpr
    obtain ⟨o, ho, hoe⟩ := hco
    have : (Subgroup.inclusion (inf_le_right : C₀ ≤ D) ⟨c, hc⟩)⁻¹ * d = o := by
      apply Subtype.ext
      change c⁻¹ * (d : G) = o
      exact hoe.symm
    rw [this]
    exact ho
  have hPcover : ∀ a ∈ D, ∃ p ∈ P, ((p : C₀) : G)⁻¹ * a ∈ aschbacherThm5Core D := by
    intro a ha
    have hmap := map_derivedSeries_eq hψs n
    rw [Group.IsPerfect.derivedSeries_eq_top (D ⧸ aschbacherThm5OddCore D) n] at hmap
    have hmem : QuotientGroup.mk' (aschbacherThm5OddCore D) ⟨a, ha⟩ ∈ P.map ψ := by
      rw [hP, hmap]
      exact Subgroup.mem_top _
    obtain ⟨p, hp, hpa⟩ := hmem
    refine ⟨p, hp, ?_⟩
    rw [hψ, MonoidHom.comp_apply] at hpa
    have h := QuotientGroup.eq.mp hpa
    exact ⟨_, h, rfl⟩
  have hKH : ∀ k : K, ((k : N) : G) ∈ Subgroup.normalizer (D : Set G) := by
    intro k
    set g : G := ((k : N) : G) with hg
    suffices hg' : g⁻¹ ∈ Subgroup.normalizer (D : Set G) by
      simpa using (Subgroup.normalizer (D : Set G)).inv_mem hg'
    refine hyp.hii i₀ g⁻¹ (P.map C₀.subtype) ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      rw [inv_inv, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
      have hfix := congrArg (fun α : MulAut (K ⧸ twoPrimeCore K) => α (k : K ⧸ twoPrimeCore K))
        (hPker p hp)
      simp only [MulAut.one_apply] at hfix
      rw [hΦ] at hfix
      have ho := QuotientGroup.eq.mp hfix
      have hoH := (hOle ⟨_, ho, rfl⟩).1
      have hoH' : (((MulAut.characteristic K (MulAut.conjNormal ((p : C₀) : G)) k)⁻¹ * k :
          K) : N) ∈ (Subgroup.normalizer (D : Set G)).subgroupOf N := hoH
      rw [Subgroup.mem_subgroupOf] at hoH'
      have hval : ((((MulAut.characteristic K (MulAut.conjNormal ((p : C₀) : G)) k)⁻¹ * k :
          K) : N) : G) = ((p : C₀) : G) * g⁻¹ * ((p : C₀) : G)⁻¹ * g := by
        change (((MulAut.characteristic K (MulAut.conjNormal ((p : C₀) : G)) k : K) : N) :
          G)⁻¹ * g = _
        rw [hΦval, ← hg]
        group
      rw [hval] at hoH'
      have hpH : ((p : C₀) : G) ∈ Subgroup.normalizer (D : Set G) :=
        Subgroup.le_normalizer (Subgroup.mem_inf.mp (p : C₀).2).2
      have h1 : g⁻¹ * ((p : C₀) : G)⁻¹ * g ∈ Subgroup.normalizer (D : Set G) := by
        have := Subgroup.mul_mem _ ((Subgroup.normalizer (D : Set G)).inv_mem hpH) hoH'
        convert this using 1
        group
      have := (Subgroup.normalizer (D : Set G)).inv_mem h1
      convert this using 1
      simp only [Subgroup.coe_subtype]
      group
    · intro a haA
      obtain ⟨p, hp, hpa⟩ := hPcover a (preimage_le D _ haA)
      exact ⟨_, ⟨p, hp, rfl⟩, _, hpa, by simp only [Subgroup.coe_subtype]; group⟩
  apply hM.1
  apply eq_top_iff.mpr
  intro y _
  apply mem_of_conj_mem_of_involution hM hw2 w.2
  have hyK : y * w' * y⁻¹ ∈ K := (involutionCore_normal (X := N)).conj_mem _ hwK y
  exact hKH ⟨_, hyK⟩

theorem no_normal_strongly_embedded (hC : Counterexample G D r Abar)
    (hodd : ∀ K : Subgroup G, K.Normal → Odd (Nat.card K) →
      K ≤ Subgroup.normalizer (D : Set G))
    (S : Sylow 2 G) (hSH : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    {N : Subgroup G} [N.Normal]
    (hM : fusionStronglyEmbedded ((Subgroup.normalizer (D : Set G)).subgroupOf N)) : False := by
  by_cases hrank : TwoRankAtLeastTwo N
  · exact false_of_bender hC S hSH hM hrank
  · exact false_of_rank_le_one hodd hM hrank

end FusionTwo

end CFSG.ComponentClassification.AschbacherTheorem5
