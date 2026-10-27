module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcRedG
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC

open CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.Y10GField

section E6


theorem e6_fieldKind_false {S : Type} [Group S] [Finite S] {p : ℕ} {α : MulAut S} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (hα : α ^ p = 1)
    (hfld : FieldKind S (⟨.E6, 0, 2⟩ : GLALabel) α) : False := by
  unfold FieldKind CFSG.Assembly.LargeEvenMarking at hfld
  obtain ⟨-, lab', hlam', hraw⟩ := hfld
  obtain ⟨_, _, _, _, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ0
  subst hlab
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  dsimp only at hraw
  obtain ⟨K, hKF, hKfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hnaR, θ, -, ⟨i, hi, f, hf, hind⟩, hout⟩ := hQ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  have hn : 1 ≤ (⟨.E6, 0, 2⟩ : GLALabel).n := by norm_num
  have hconj := RecipeExcLang.ggRawFieldConj_chev
    (τ := CFSG.Blueprint.Chevalley.TwistTag.E6.tag) (ℓ := 2) (f := 2) (p := p) hn hK hp
    CFSG.StandardType.RecipeExcLang.innerFieldTrivial_E6
  let eS : S ≃* S ⧸ Subgroup.center S :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  let e : S ≃* _ := eS.trans θ
  have hkey : ∀ s : S, (i * f) (e s) = e (α s) := fun s => hind s (α s) rfl
  have hαe : MulAut.congr e α = i * f := by
    ext r
    have h := hkey (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hpow : (i * f) ^ p = 1 := by rw [← hαe, ← map_pow, hα, map_one]
  have hnot : i * f ∉ _ := fun h => hout ⟨i * f, h, hind⟩
  obtain ⟨f', hf', u', hu', hord', hdec⟩ :=
    hconj hsR hnaR i hi f (Subgroup.subset_closure hf) hnot hpow
  have hpn : p ∣ 2 :=
    dvd_of_chevField_order (n := 2) (by norm_num) hK hp (LargeEvenChevH (LargeEvenCartanE 6) K false)
      (fun σ h hh => chevH_stable (LargeEvenCartanE 6) K false σ h hh) hf' hord'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpn)

end E6

end CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10GField

section FromInnDiagExc


theorem i14NegPieceDOne_of_innDiagExc (hInn : InnDiagExc) : I14NegPieceDOne := by
  intro S _ _ p α J labK labJ hp hp2 hcen hlabK hlabJ hα hJ hKE hJE
  subst hKE hJE
  have hFam : FamExc (⟨.E6, 0, 2⟩ : GLALabel) := Or.inl rfl
  rcases Y10GClsExc.clsExc_holds S p α _ hFam hp hp2 hcen hlabK hα with hin | hfld
  · have h2 := hInn S p α J _ _ hFam hp hp2 hcen hin hα hlabJ hJ
    rw [canonLabel_e6_two, canonLabel_twD5 ⟨rfl, rfl⟩] at h2
    exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)
  · exact Y10GNegBC.e6_fieldKind_false hp hp2 hcen hα hfld

theorem i14NegPieceD_of_innDiagExc (hInn : InnDiagExc) : I14NegPieceD :=
  i14NegPieceD_of_one (i14NegPieceDOne_of_innDiagExc hInn)

end FromInnDiagExc

end CFSG.LocalAnalysis.GLTheoremA.Y10F
