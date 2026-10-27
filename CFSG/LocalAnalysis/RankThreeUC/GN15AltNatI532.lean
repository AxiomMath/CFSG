module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltNatMain
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBaum

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThree.PartTwo
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
open CFSG.HardMathSupport.Cooperstein.Coordinator (GF2EightFive)
open Equiv
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem exists_i532_of_gf2EightFive (hGF : GF2EightFive) (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) {n : ℕ} (hn9 : 9 ≤ n) (hodd : Odd n)
    (e : ↥L ≃* alternatingGroup (Fin n)) :
    ∃ (gE : ↥L ≃* alternatingGroup (Fin n))
      (π : ↥⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (altHeart n)),
      Function.Surjective π ∧
      (∀ u, π u = 1 ↔
        ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), (k : X) * u * (k : X)⁻¹ = u) ∧
      ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L)
        (u u' : ↥⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆),
        (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
          Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
          Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm
            (gE ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin n)) x) : altHeart n) := by
  classical
  obtain ⟨g, W, π, hg, hWV, hZW, hWK, hπk, hπi, hVW⟩ :=
    exists_naturalOnLayer_of_gf2EightFive hGF hX hL hJ hn9 hodd e
  have hgi : Function.Injective g := (Finite.injective_iff_surjective_of_equiv e.toEquiv).2 hg
  let gE : ↥L ≃* alternatingGroup (Fin n) := MulEquiv.ofBijective g ⟨hgi, hg⟩
  have hΦs : Function.Surjective (liftToAlt L g) := liftToAlt_surjective L hg
  have hΦk := liftToAlt_eq_one_iff L hgi
  have hVC : ∀ c ∈ gnC T, ∀ v ∈ gnV T, c * v * c⁻¹ = v := fun c hc v hv => by
    have h1 : v * c = c * v := Subgroup.mem_centralizer_iff.1 hc v hv
    rw [← h1, mul_inv_cancel_right]
  have hVab := isElemAbelian_gnV T hX
  have hSW : AltBaumSetup W (L.comap (QuotientGroup.mk' (gnC T))) (liftToAlt L g) :=
    { comm := fun v hv w hw =>
        congrArg Subtype.val (hVab.1.is_comm.comm ⟨v, hWV hv⟩ ⟨w, hWV hw⟩)
      sq := fun v hv => by have := hVab.2 v (hWV hv); simpa [pow_two] using this
      norm := hWK
      surj := hΦs
      ker := fun k hk v hv => hVC _ ((hΦk k).1 hk) v (hWV hv) }
  have hi2 : ∀ (l : ↥(L.comap (QuotientGroup.mk' (gnC T))))
      (u u' : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆),
      (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
        Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd (π u') = (QuotientAddGroup.mk
          (evenWeightPerm (liftToAlt L g l : Perm (Fin n)) x) : altHeart n) :=
    fun l u u' h x hx => hπi (l : X) l.2 u u' h x hx
  have hne : ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ ≠ ⊥ := by
    intro hbot
    rw [← hVW] at hbot
    have h1 : gnV T ≤ Subgroup.centralizer ((L.comap (QuotientGroup.mk' (gnC T)) : Subgroup X) :
        Set X) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    have h2 : L.comap (QuotientGroup.mk' (gnC T)) ≤ gnC T := Subgroup.le_centralizer_iff.1 h1
    have hL1 : ∀ l : ↥L, l = 1 := by
      intro l
      obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (l : X ⧸ gnC T)
      have hkK : k ∈ L.comap (QuotientGroup.mk' (gnC T)) := by
        show QuotientGroup.mk' (gnC T) k ∈ L
        rw [show QuotientGroup.mk' (gnC T) k = (l : X ⧸ gnC T) from hk]; exact l.2
      apply Subtype.ext
      rw [← hk]
      exact (QuotientGroup.eq_one_iff k).2 (h2 hkK)
    have : Nontrivial (alternatingGroup (Fin n)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
    obtain ⟨σ, hσ⟩ := exists_ne (1 : alternatingGroup (Fin n))
    exact hσ (by simpa using congrArg e (hL1 (e.symm σ)))
  have hπs : Function.Surjective π := surjective_of_ne_bot (by omega) hSW hπk hi2 hne
  obtain ⟨π'', hπ'', hπ''k⟩ := exists_altBaumSection_of_setup_ker hn9 hodd hSW hπs hπk hi2
  let π' : ↥⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (altHeart n) :=
    π.comp (Subgroup.inclusion hVW.le)
  refine ⟨gE, π', ?_, fun u => ?_, fun l hl u u' h x hx => ?_⟩
  · intro v
    obtain ⟨u, hu⟩ := hπs v
    exact ⟨⟨u.1, hVW.ge u.2⟩, hu⟩
  · constructor
    · intro h
      exact hπk (Subgroup.inclusion hVW.le u) h
    · intro hfix
      have h1 : π'' (Subgroup.inclusion hVW.le u) = 1 := (hπ''.ker_iff _).2 hfix
      exact (hπ''k _).1 h1
  · exact hπi l hl (Subgroup.inclusion hVW.le u) (Subgroup.inclusion hVW.le u') h x hx

theorem gnBaumNormalizes_of_gf2EightFive (hGF : GF2EightFive) : GNBaumNormalizes := by
  intro X _ _ T hX L hL hJ n hn9 hodd he
  obtain ⟨e⟩ := he
  obtain ⟨gE, π, hπs, hπk, hπi⟩ := exists_i532_of_gf2EightFive hGF hX hL hJ hn9 hodd e
  exact baum_le_normalizer_alt hX hL hn9 hodd gE π hπs hπk hπi

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
