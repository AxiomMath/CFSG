module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerGL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClLin
public import CFSG.LocalAnalysis.GLTheoremA.CatB.RankFineU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeLinFive
import CFSG.Quasithin.H13.A5LNat
import CFSG.Quasithin.Vol2.Ch12Sec2Lem25N


public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open

namespace Lin

open CFSG.LocalAnalysis.GLTheoremA.I1431C2
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem exists_oneBlock_maxrank {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    (hV : 1 ≤ Module.finrank (ZMod 2) V / 2)
    (hge : 3 ^ (Module.finrank (ZMod 2) V / 2) ≤ Nat.card E) :
    ∃ e ∈ E, e ^ 3 = 1 ∧ Module.finrank (ZMod 2) (comSp e) = 2 := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  have hge' : 3 ^ (Module.finrank (ZMod 2) V / 2) ≤ Fintype.card E := by
    rwa [Nat.card_eq_fintype_card] at hge
  obtain ⟨k, X, ρf, hXprop, hind, hsup, hρf, hPcard, hpe⟩ := exists_struct E hE hge'
  have hPpos : 0 < Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} := by
    rw [hPcard]; omega
  obtain ⟨p⟩ := Fintype.card_pos_iff.1 hPpos
  obtain ⟨e, heE, hexp⟩ := hpe p
  have hplane : ∀ i, Module.finrank (ZMod 2) (X i) = 2 →
      (∀ x ∈ X i, ρf i x = x → x = 0) ∧
        (∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x) := by
    intro i hi
    rcases (hρf i).2 with ⟨h1, -⟩ | ⟨-, hfix, -, hpow⟩
    · omega
    · exact ⟨hfix, hpow⟩
  have hline : ∀ i, Module.finrank (ZMod 2) (X i) ≠ 2 → ∀ g ∈ E, ∀ x ∈ X i, g x = x := by
    intro i hi
    rcases (hρf i).2 with ⟨-, h⟩ | ⟨h2, -⟩
    · exact h
    · exact absurd h2 hi
  have hA : ∀ x ∈ X p.1, e x = ρf p.1 x := by
    intro x hx
    have h := expo_spec ((hplane p.1 p.2).2 e heE) x hx
    rw [h, hexp p]
    simp
  have hB : ∀ j, j ≠ p.1 → ∀ x ∈ X j, e x = x := by
    intro j hj x hx
    by_cases hjp : Module.finrank (ZMod 2) (X j) = 2
    · have h := expo_spec ((hplane j hjp).2 e heE) x hx
      have hne : (⟨j, hjp⟩ : {i // Module.finrank (ZMod 2) (X i) = 2}) ≠ p := fun h' =>
        hj (congrArg Subtype.val h')
      rw [h, hexp ⟨j, hjp⟩, if_neg hne]
      simp
    · exact hline j hjp e heE x hx
  have hinv : ∀ x ∈ X p.1, ρf p.1 x ∈ X p.1 := fun x hx =>
    (hXprop p.1).1 (ρf p.1) (hρf p.1).1 x hx
  have hcom : comSp e = X p.1 := by
    apply le_antisymm
    · rintro a ha
      obtain ⟨v, rfl⟩ := mem_comSp.1 ha
      refine Planes.sub_mem_of_pieces hsup e (X p.1) (fun j x hx => ?_) v
      by_cases hj : j = p.1
      · subst hj
        rw [hA x hx]
        exact (X p.1).sub_mem (hinv x hx) hx
      · rw [hB j hj x hx, sub_self]
        exact (X p.1).zero_mem
    · intro a ha
      obtain ⟨y, hy, hya⟩ := Planes.surj_of_plane p.2 hinv (hplane p.1 p.2).1 a ha
      exact mem_comSp.2 ⟨y, by rw [hA y hy]; exact hya⟩
  exact ⟨e, heE, hE.2 e heE, by rw [hcom]; exact p.2⟩

theorem cent_Nsub_le_zpowers_c {e : V ≃ₗ[ZMod 2] V} (h3 : e ^ 3 = 1)
    (hfr : Module.finrank (ZMod 2) (comSp e) = 2)
    (hc3 : 3 ≤ Module.finrank (ZMod 2) (fixSp e))
    {g : V ≃ₗ[ZMod 2] V} (hgC : g ∈ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)))
    (hgN : ∀ h ∈ Nsub h3, g * h = h * g) : g ∈ Subgroup.zpowers e := by
  have hg : g * e = e * g := Subgroup.mem_centralizer_singleton_iff.1 hgC
  obtain ⟨k, hk⟩ := exists_pow_of_cent h3 hfr hg
  have hek : e ^ k * e = e * e ^ k := (Commute.refl e).pow_left k |>.eq
  have hekC : (e ^ k)⁻¹ ∈ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)) := by
    apply (Subgroup.centralizer _).inv_mem
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hek
  have hekC' : (e ^ k)⁻¹ * e = e * (e ^ k)⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.1 hekC
  have hg'N : g * (e ^ k)⁻¹ ∈ Nsub h3 := by
    rw [mem_Nsub]
    refine ⟨fun a ha => ?_, fun w hw => ?_⟩
    · have hb : (e ^ k)⁻¹ a ∈ comSp e := cent_com hekC' ha
      simp only [LinearEquiv.mul_apply]
      rw [hk _ hb, ← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    · simp only [LinearEquiv.mul_apply]
      exact cent_fix hg (cent_fix hekC' hw)
  have hcomm : ∀ h ∈ Nsub h3, (g * (e ^ k)⁻¹) * h = h * (g * (e ^ k)⁻¹) := by
    intro h hh
    have hhC := Nsub_le_cent h3 hh
    have h1 : h * e = e * h := Subgroup.mem_centralizer_singleton_iff.1 hhC
    have h2 : Commute h ((e ^ k)⁻¹) := (Commute.pow_right h1 k).inv_right
    rw [mul_assoc, h2.symm.eq, ← mul_assoc, hgN h hh, mul_assoc]
  have hcen : (⟨g * (e ^ k)⁻¹, hg'N⟩ : Nsub h3) ∈ Subgroup.center (Nsub h3) := by
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (hcomm h h.2).symm
  rw [Nsub_center_c hc3 h3 rfl, Subgroup.mem_bot] at hcen
  have h1 : g * (e ^ k)⁻¹ = 1 := congrArg Subtype.val hcen
  have : g = e ^ k := mul_inv_eq_one.1 h1
  rw [this]
  exact Subgroup.npow_mem_zpowers e k

theorem not_smallOrd_Nsub {e : V ≃ₗ[ZMod 2] V} (h3 : e ^ 3 = 1)
    (hfr : Module.finrank (ZMod 2) (comSp e) = 2) {c : ℕ}
    (hc : Module.finrank (ZMod 2) (fixSp e) = c) (hc4 : 4 ≤ c) (hc7 : c ≤ 7) :
    ¬ HStdExcl.SmallOrd (Nsub h3) := by
  intro hso
  have hc3 : 3 ≤ c := by omega
  have hcenter := Nsub_center_c hc3 h3 hc
  have hcardN : Nat.card (Nsub h3) = Nat.card (GL (Fin c) (ZMod 2)) := by
    rw [Nat.card_congr (NsubEquivC h3 hc).toEquiv]
    rw [← Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) (Fin c → ZMod 2)).toEquiv]
    exact (Nat.card_congr
      (Matrix.GeneralLinearGroup.toLin (n := Fin c) (R := ZMod 2)).toEquiv).symm
  have hcardq : Nat.card (↥(Nsub h3) ⧸ Subgroup.center ↥(Nsub h3)) =
      Nat.card (GL (Fin c) (ZMod 2)) := by
    rw [hcenter, Nat.card_congr (QuotientGroup.quotientBot).toEquiv, hcardN]
  rcases hso with h | h <;> rw [hcardq] at h
  · interval_cases c
    · rw [CFSG.Quasithin.H13.A5.card_GL4] at h; norm_num at h
    · rw [CFSG.Quasithin.H13.A5.card_GL5] at h; norm_num at h
    · rw [CFSG.Quasithin.H13.Lem25.card_GL_six] at h; norm_num at h
    · rw [CFSG.Quasithin.H13.Lem25.card_GL_seven] at h; norm_num at h
  · interval_cases c
    · rw [CFSG.Quasithin.H13.A5.card_GL4] at h; norm_num at h
    · rw [CFSG.Quasithin.H13.A5.card_GL5] at h; norm_num at h
    · rw [CFSG.Quasithin.H13.Lem25.card_GL_six] at h; norm_num at h
    · rw [CFSG.Quasithin.H13.Lem25.card_GL_seven] at h; norm_num at h

theorem false_of_smallModel_maxrank {m : ℕ} (hV : Module.finrank (ZMod 2) V = m)
    (hm : 6 ≤ m) (hm9 : m ≤ 9) {Bb : Subgroup (V ≃ₗ[ZMod 2] V)}
    (h : SmallModel (V ≃ₗ[ZMod 2] V) Bb) (hge : 3 ^ (m / 2) ≤ Nat.card Bb) : False := by
  obtain ⟨helem, hcardge, hcardle, htl, hmax, hstd, hsmall⟩ := h
  have hdim : Module.finrank (ZMod 2) V / 2 = m / 2 := by rw [hV]
  obtain ⟨y, hyB, hy3, hyfr⟩ := exists_oneBlock_maxrank helem (by omega) (by rwa [hdim])
  have hy1 : y ≠ 1 := by
    intro h1
    have hbot : comSp y = ⊥ := by
      rw [h1]
      simp [comSp, ds]
    have h0 : Module.finrank (ZMod 2) (comSp y) = 0 := by
      rw [hbot]
      simp
    omega
  have hc_fix : Module.finrank (ZMod 2) (fixSp y) = m - 2 := by
    have h := finrank_fixSp hy3
    rw [hyfr, hV] at h
    omega
  have hNq : CFSG.Open.IsQuasisimple (Nsub hy3) :=
    Nsub_isQuasisimple_c (c := m - 2) (by omega) hy3 hc_fix
  have hNq' : CFSG.IsQuasisimple ↥(Nsub hy3) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥(Nsub hy3)).2.2.1.mpr hNq
  have hlayer := CFSG.LocalAnalysis.GLTheoremA.S172B.Cent.glaLayer_eq_of_commutator_le
    (Nsub_le_cent hy3) (comm_le_Nsub hy3 hyfr) hNq'
  have hcent : Bb ⊓ Subgroup.centralizer (Nsub hy3 : Set (V ≃ₗ[ZMod 2] V)) =
      Subgroup.zpowers y := by
    refine le_antisymm ?_ ?_
    · rintro b hb
      have hbB : b ∈ Bb := hb.1
      have hbN : b ∈ Subgroup.centralizer (Nsub hy3 : Set (V ≃ₗ[ZMod 2] V)) := hb.2
      have hbC : b ∈ Subgroup.centralizer ({y} : Set (V ≃ₗ[ZMod 2] V)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm := helem.1.is_comm.comm (⟨b, hbB⟩ : Bb) (⟨y, hyB⟩ : Bb)
        exact congrArg Subtype.val hcomm
      have hbN' : ∀ h ∈ Nsub hy3, b * h = h * b := by
        intro h hh
        exact (Subgroup.mem_centralizer_iff.1 hbN h hh).symm
      exact cent_Nsub_le_zpowers_c hy3 hyfr (by omega) hbC hbN'
    · intro z hz
      have hyN : y ∈ Subgroup.centralizer (Nsub hy3 : Set (V ≃ₗ[ZMod 2] V)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact Subgroup.mem_centralizer_singleton_iff.1 (Nsub_le_cent hy3 hh)
      exact ⟨Subgroup.zpowers_le.2 hyB hz, Subgroup.zpowers_le.2 hyN hz⟩
  have hstdAt : StdAt Bb y := by
    refine ⟨?_, ?_⟩
    · rw [hlayer.1]
      exact hlayer.2
    · rw [hlayer.1]
      exact hcent
  have hso := hsmall y hyB hy1 hstdAt
  rw [hlayer.1] at hso
  exact not_smallOrd_Nsub hy3 hyfr (c := m - 2) hc_fix (by omega) (by omega) hso

theorem noSmallModel_dim_five (hV : Module.finrank (ZMod 2) V = 5) :
    NoSmallModel (V ≃ₗ[ZMod 2] V) := by
  rintro Bb ⟨helem, hcardge, hcardle, htl, hmax, hstd, hsmall⟩
  have h := card_le_three_pow Bb helem
  rw [hV] at h
  norm_num at h
  omega

theorem noSmallModel_dim_six_seven (hV : Module.finrank (ZMod 2) V = 6 ∨
    Module.finrank (ZMod 2) V = 7) : NoSmallModel (V ≃ₗ[ZMod 2] V) := by
  rintro Bb h
  rcases hV with hV | hV
  · exact false_of_smallModel_maxrank (m := 6) hV (by norm_num) (by norm_num) h
      (by simpa using h.card_ge)
  · exact false_of_smallModel_maxrank (m := 7) hV (by norm_num) (by norm_num) h
      (by simpa using h.card_ge)


noncomputable def pslEquivLinearEquiv (m : ℕ) :
    Matrix.ProjectiveSpecialLinearGroup (Fin m) (ZMod 2) ≃* VecAut m :=
  (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m
    (ZMod 2)).trans
    ((@CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two m (ZMod 2)
      (inferInstance) (inferInstance) (by norm_num)).trans (linEquivSL m))

theorem local81_linearEquiv {m : ℕ} (hm : 8 ≤ m) : Local81 (VecAut m) :=
  Local81.congr (pslEquivLinearEquiv m)
    (CFSG.LocalAnalysis.GLTheoremA.I1431C2.lin_local81_psl (K := ZMod 2) hm)

theorem noSmallModel_fin_eight : NoSmallModel (VecAut 8) := by
  rintro Bb h
  obtain ⟨U, hU2, hUne, E, hEU, hEe, hEcard⟩ :=
    local81_linearEquiv (m := 8) (by norm_num)
  have hble := h.max E hEe ⟨U, hU2, hUne, hEU⟩
  rw [hEcard] at hble
  exact false_of_smallModel_maxrank (m := 8) (by simp [Module.finrank_fin_fun])
    (by norm_num) (by norm_num) h (by simpa using hble)

theorem noSmallModel_fin_nine : NoSmallModel (VecAut 9) := by
  rintro Bb h
  obtain ⟨U, hU2, hUne, E, hEU, hEe, hEcard⟩ :=
    local81_linearEquiv (m := 9) (by norm_num)
  have hble := h.max E hEe ⟨U, hU2, hUne, hEU⟩
  rw [hEcard] at hble
  exact false_of_smallModel_maxrank (m := 9) (by simp [Module.finrank_fin_fun])
    (by norm_num) (by norm_num) h (by simpa using hble)

theorem noSmallModel_fin_ge_ten {m : ℕ} (hm : 10 ≤ m) : NoSmallModel (VecAut m) := by
  rintro Bb h
  obtain ⟨U, hU2, hUne, E, hEU, hEe, hEcard⟩ := localPow5_fin hm
  have hble := h.max E hEe ⟨U, hU2, hUne, hEU⟩
  rw [hEcard] at hble
  norm_num at hble
  have hle := h.card_le
  omega

theorem noSmallModel_fin {m : ℕ} (hm : 5 ≤ m) : NoSmallModel (VecAut m) := by
  rcases Nat.lt_or_ge m 6 with h5 | h6
  · have hm5 : m = 5 := by omega
    subst hm5
    exact noSmallModel_dim_five (V := Fin 5 → ZMod 2)
      (by simp [Module.finrank_fin_fun])
  rcases Nat.lt_or_ge m 8 with h7 | h8
  · have h : m = 6 ∨ m = 7 := by omega
    rcases h with rfl | rfl
    · exact noSmallModel_dim_six_seven (V := Fin 6 → ZMod 2)
        (Or.inl (by simp [Module.finrank_fin_fun]))
    · exact noSmallModel_dim_six_seven (V := Fin 7 → ZMod 2)
        (Or.inr (by simp [Module.finrank_fin_fun]))
  rcases Nat.lt_or_ge m 10 with h9 | h10
  · have h : m = 8 ∨ m = 9 := by omega
    rcases h with rfl | rfl
    · exact noSmallModel_fin_eight
    · exact noSmallModel_fin_nine
  · exact noSmallModel_fin_ge_ten h10

theorem noSmallModel_of_rankFine {G : Type} [Group G] {B : ℕ}
    (h : CFSG.LocalAnalysis.GLTheoremA.CatB.RankFine G B) (hB : B < 27) :
    NoSmallModel G := by
  rintro Bb ⟨helem, hge, -, htl, -, -, -⟩
  obtain ⟨P, hP2, hPne, hnorm⟩ := htl
  have hle := h Bb P helem hP2 hPne hnorm
  omega

theorem rankFine_statedSU_card_four {K : Type} [Field K] (hK : Nat.card K = 4) :
    CFSG.LocalAnalysis.GLTheoremA.CatB.RankFine
      (StatedProj (StatedSU 4 2 K)) 9 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype CFSG.LocalAnalysis.GLTheoremA.CatB.K4 := Fintype.ofFinite _
  have hcard : Fintype.card CFSG.LocalAnalysis.GLTheoremA.CatB.K4 = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.LocalAnalysis.GLTheoremA.CatB.K4_card, hK]
  let e : CFSG.LocalAnalysis.GLTheoremA.CatB.K4 ≃+* K :=
    FiniteField.ringEquivOfCardEq hcard
  exact CFSG.LocalAnalysis.GLTheoremA.CatB.RankFine.of_mulEquiv
    (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv e 4 2).symm
    CFSG.LocalAnalysis.GLTheoremA.CatB.rankFine_u4

end Lin

theorem famLin_holds : FamLin := by
  intro n q hv hq h4
  obtain ⟨hp2, hexp⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I1431C2.cl_primePower_card_two hq
  have hcl : StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩).Group
      .PSL (n + 1) q.p q.exponent :=
    (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA n q hv).2.resolve_right
      (fun h0 => by omega)
  have hcl' : StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩).Group
      .PSL (n + 1) 2 1 := by
    simpa [hp2, hexp] using hcl
  obtain ⟨-, K, hfK, hfinK, hcardK, ⟨e⟩⟩ := hcl'
  haveI := hfK
  haveI := hfinK
  have hK2 : Nat.card K = 2 := by simpa using hcardK
  let e2 := (@CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two (n + 1) K
    hfK hfinK hK2).trans (linEquivSL (n + 1))
  exact noSmallModel_of_mulEquiv (e.trans e2)
    (Lin.noSmallModel_fin (m := n + 1) (by omega))

theorem famU4_holds : FamU4 := by
  intro q hv hq
  obtain ⟨hp2, hexp⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I1431C2.cl_primePower_card_two hq
  have hmod : StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group
      .PSU 4 2 1 := by
    simpa [hp2, hexp] using
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _)
  obtain ⟨-, K, hfK, hfinK, hcardK, ⟨e⟩⟩ := hmod
  haveI := hfK
  haveI := hfinK
  have hcard4 : Nat.card K = 4 := by simpa using hcardK
  exact noSmallModel_of_mulEquiv e
    (Lin.noSmallModel_of_rankFine (@Lin.rankFine_statedSU_card_four K hfK hcard4)
      (by norm_num))

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
