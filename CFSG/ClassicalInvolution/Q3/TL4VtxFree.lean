module

public import CFSG.ClassicalInvolution.Q3.TL4VtxFamC
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs
public import CFSG.ClassicalInvolution.Q3.TL4VtxAutF

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace Vtx

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {n : ℕ}

theorem alphaOf_eq_bot_of_twinFree (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n)
    {K J : Subgroup Q} (hK : K ∈ Φ) (hJ : J ∈ omegaNbr Φ K) {a b : Q}
    (ha : IsUniqueInvolution K a) (hb : IsUniqueInvolution J b) {L : Subgroup Q}
    (hL : IsComponent L) (hma : ∃ y ∈ L, a * y ≠ y * a) (hmb : ∃ y ∈ L, b * y ≠ y * b)
    (hmab : ∃ y ∈ L, a * b * y ≠ y * (a * b)) (htf : TwinFreeAt Φ K a L)
    (haN : a ∈ Subgroup.normalizer (L : Set Q)) (hbN : b ∈ Subgroup.normalizer (L : Set Q)) :
    alphaOf (Subgroup.closure ({toInducedAutOn L ⟨a, haN⟩, toInducedAutOn L ⟨b, hbN⟩} :
      Set ↥(inducedAutOn L))) = ⊥ := by
  have hcl := h.hyp.conjInvariant
  have hXN := orbGrp_le_normalizer h4 h hO hn hK ha hL hma
  have hΦ' := typeRFam_imgFam h4 h hO hn hK ha hL hma htf
  have hJΦ : J ∈ Φ := hJ.1
  obtain ⟨ya, hya, hnea⟩ := hma
  obtain ⟨yb, hyb, hneb⟩ := hmb
  obtain ⟨x, hx, hxJ⟩ := exists_conj_of_moves h4 h hO hn hL hK hJΦ ⟨a, ha.mem, ya, hya, hnea⟩
    ⟨b, hb.mem, yb, hyb, hneb⟩
  have hJX : J ≤ orbGrp Φ K := hxJ ▸ conjSub_le_orbGrp K ⟨x, orbGrp_le hcl hK hx⟩
  have hK' : inducedImage L K ∈ imgFam Φ K L hXN :=
    (mem_imgFam_iff hcl hK hXN).mpr ⟨1, Subgroup.one_mem _, by rw [conjSub_one]⟩
  have hJ' : inducedImage L J ∈ imgFam Φ K L hXN :=
    (mem_imgFam_iff hcl hK hXN).mpr ⟨x, hx, by rw [hxJ]⟩
  have hinv : ∀ {M : Subgroup ↥(inducedAutOn L)}, M ∈ imgFam Φ K L hXN →
      ∀ w ∈ M, w * w = 1 → w ≠ 1 → IsUniqueInvolution M w := by
    intro M hM w hw hw2 hw1
    obtain ⟨w', hw'⟩ := Sec6Gen.exists_uniqueInvolution hΦ'.hyp hM
    rcases hw'.unique w hw hw2 with h1 | h1
    · exact absurd h1 hw1
    · rwa [h1]
  have hsq : ∀ {u : Q} (hu : u * u = 1) (huN : u ∈ Subgroup.normalizer (L : Set Q)),
      toInducedAutOn L ⟨u, huN⟩ * toInducedAutOn L ⟨u, huN⟩ = 1 := by
    intro u hu huN
    rw [← map_mul]
    have e : (⟨u, huN⟩ * ⟨u, huN⟩ : ↥(Subgroup.normalizer (L : Set Q))) = 1 := Subtype.ext hu
    rw [e, map_one]
  have hσa : IsUniqueInvolution (inducedImage L K) (toInducedAutOn L ⟨a, haN⟩) :=
    hinv hK' _ (Lemma52Proof.toInducedAutOn_mem_inducedImage L K ha.mem haN) (hsq ha.sq haN)
      (Lemma52Proof.toInducedAutOn_ne_one_of_moved L haN hya hnea)
  have hσb : IsUniqueInvolution (inducedImage L J) (toInducedAutOn L ⟨b, hbN⟩) :=
    hinv hJ' _ (Lemma52Proof.toInducedAutOn_mem_inducedImage L J hb.mem hbN) (hsq hb.sq hbN)
      (Lemma52Proof.toInducedAutOn_ne_one_of_moved L hbN hyb hneb)
  have hne : inducedImage L K ≠ inducedImage L J := by
    intro e
    rw [e] at hσa
    have hab := hσa.eq hσb
    obtain ⟨y, hy, hne'⟩ := hmab
    apply hne'
    have h1 : toInducedAutOn L (⟨a, haN⟩ * ⟨b, hbN⟩) = 1 := by
      rw [map_mul, hab, hsq hb.sq hbN]
    exact Lemma52Proof.commute_of_toInducedAutOn_eq_one L
      (Subgroup.mul_mem _ haN hbN) h1 y hy
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := hJ
  have hRS : IsSylow2In R J := Sec6Gen.isSylow2In_of_mem_RSet_of_le h.hyp hJΦ hR hRJ
  have hinjJ : ∀ y ∈ J.subgroupOf (orbGrp Φ K), psiL L (orbGrp Φ K) hXN y = 1 → y = 1 := by
    intro y hy hy1
    have h1 := ker_psiL_inf_conj h4 h hO hn hK ha hL ⟨ya, hya, hnea⟩ ⟨x, hx⟩
    rw [conjSub_subgroupOf] at h1
    have hmem : y ∈ (psiL L (orbGrp Φ K) hXN).ker ⊓ (conjSub x K).subgroupOf (orbGrp Φ K) :=
      ⟨hy1, by rwa [hxJ]⟩
    rwa [h1, Subgroup.mem_bot] at hmem
  have hRsyl : IsSylow2In (inducedImage L R) (inducedImage L J) := by
    rw [← map_psiL hXN (hRJ.trans hJX), ← map_psiL hXN hJX]
    exact isSylow2In_map_of_injOn _ hinjJ (hRS.subgroupOf hJX)
  have hnbr : inducedImage L J ∈ omegaNbr (imgFam Φ K L hXN) (inducedImage L K) := by
    refine ⟨hJ', hne.symm, inducedImage L R, mem_RSet_of_isSylow2In hJ' hRsyl,
      Subgroup.map_mono fun r hr => Subgroup.mem_subgroupOf.mpr
        (hRJ (Subgroup.mem_subgroupOf.mp hr)), ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    rw [mem_normalizer_iff_conjSub_eq, conjSub_inducedImage]
    congr 1
    exact mem_normalizer_iff_conjSub_eq.mp (hRN (Subgroup.mem_subgroupOf.mp hr))
  exact h5 _ (lt_of_le_of_lt (natCard_inducedAutOn_le L) hn) _ hΦ'
    (oddCore_inducedAutOn_eq_bot hL) (isSimpleGroup_fstar_inducedAutOn hL)
    (nonabelian_fstar_inducedAutOn hL) (imgFam_transitive hXN) _ hK' _ hnbr _ _ hσa hσb

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
