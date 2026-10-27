module

public import CFSG.ClassicalInvolution.Q3.TL4OddKey
public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs
public import CFSG.ClassicalInvolution.Q3.TL4SepDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.Assembly.Dichotomy (involutionOddCore)

section Conj

variable {Y : Type} [Group Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem tightClsR_conj {r : ℕ} (hc : TightClsR r Y R S t) (g : Y)
    {S' : Sylow 2 ↥(conjSub g R)} (e : (S' : Subgroup ↥(conjSub g R)) ≃* (S : Subgroup R)) :
    TightClsR r Y (conjSub g R) S' (g * t * g⁻¹) := by
  obtain ⟨⟨eq⟩, hgen, hO⟩ := hc
  refine ⟨⟨e.trans eq⟩, ?_, hO⟩
  have key : (⨆ h : Y, conjSub h (conjSub g (tightCore R))) =
      ⨆ h : Y, conjSub h (tightCore R) := by
    apply le_antisymm
    · refine iSup_le fun h => ?_
      rw [← conjSub_mul]
      exact le_iSup (fun h : Y => conjSub h (tightCore R)) (h * g)
    · refine iSup_le fun h => ?_
      have e1 : conjSub h (tightCore R) = conjSub (h * g⁻¹) (conjSub g (tightCore R)) := by
        rw [conjSub_mul, conjSub_inv_conjSub]
      rw [e1]
      exact le_iSup (fun h : Y => conjSub h (conjSub g (tightCore R))) (h * g⁻¹)
  show (⨆ h : Y, conjSub h (tightCore (conjSub g R))) = ⊤
  rw [← conjSub_tightCore R g, key]
  exact hgen

variable [Finite Y]

omit [Finite Y] in
theorem conj_mem_oddCent (g : Y) {x : Y}
    (hx : x ∈ oddCoreImg (Subgroup.centralizer ({t} : Set Y))) :
    g * x * g⁻¹ ∈ oddCoreImg (Subgroup.centralizer ({g * t * g⁻¹} : Set Y)) := by
  have h := CFSG.Assembly.Dichotomy.involutionOddCore_map (MulAut.conj g) t
  have hmem : (MulAut.conj g) x ∈ (involutionOddCore t).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [h, MulAut.conj_apply] at hmem
  rw [MulAut.conj_apply] at hmem
  exact hmem

omit [Finite Y] in
theorem card_oddCent_conj (g : Y) :
    Nat.card (oddCoreImg (Subgroup.centralizer ({g * t * g⁻¹} : Set Y))) =
      Nat.card (oddCoreImg (Subgroup.centralizer ({t} : Set Y))) := by
  have h := CFSG.Assembly.Dichotomy.involutionOddCore_map (MulAut.conj g) t
  rw [MulAut.conj_apply] at h
  change Nat.card (involutionOddCore (g * t * g⁻¹)) = Nat.card (involutionOddCore t)
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem mem_secH (hd : TightDatum R S t) {u : Y} (htu : t ∈ Subgroup.centralizer ({u} : Set Y)) :
    (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u := by
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    exact hd.order ▸ pow_orderOf_eq_one t
  apply le_subnormalClosure
  apply Subgroup.subset_closure
  refine ⟨Subgroup.mem_subgroupOf.mpr hd.mem_right, ?_⟩
  exact Balance.isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext ht2)

end Conj

section Cit3

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem tightLargeHypR_conj {r n : ℕ} (h : TightLargeHypR r n Y R S t) (g : Y) :
    ∃ SJ : Sylow 2 ↥(conjSub g R), TightLargeHypR r n Y (conjSub g R) SJ (g * t * g⁻¹) := by
  obtain ⟨SJ, hdJ, ⟨eJ⟩⟩ := h.datum.conj g
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  refine ⟨SJ, ⟨h.below, h.tbelow, h.card, hdJ, tightClsR_conj h.cls g eJ,
    not_tightInO2_conj h.notInO2 g, h.fstar, h.large, ?_, h.center⟩⟩
  have := h.edge
  unfold TightEdgeless at this ⊢
  rwa [hfam]

theorem tightSepAlpha_of_alphaLeafR {r n : ℕ} (hα : TightAlphaLeafR r n)
    (hL : TightLargeHypR r n Y R S t)
    (hc : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))) : TightSepAlpha R t :=
  hα Y R S t hL hc

theorem oddCent_le_of_maxSec {r n : ℕ} (hα : TightAlphaLeafR r n) (hsec : TightMaxSecR r n)
    (hL : TightLargeHypR r n Y R S t)
    (hc : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)))
    (hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R))) {J : Subgroup Y}
    (hJ : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J) {u : Y}
    (hu : IsUniqueInvolution J u) :
    oddCoreImg (Subgroup.centralizer ({t} : Set Y)) ≤
      oddCoreImg (Subgroup.centralizer ({u} : Set Y)) := by
  have hd := hL.datum
  have hJn := hJ.1.2
  have hαJ := hα Y R S t hL hc J hJn u hu
  obtain ⟨-, -, -, htu, -⟩ := hd.edge_involution hJn hu
  have ht := mem_secH hd htu
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    exact hd.order ▸ pow_orderOf_eq_one t
  exact oddCent_le_oddCent_of_sec htu ht2 (ne_one_of_datum hd)
    (oddCent_le_centralizer_of_alpha hd hαJ) ht (hsec Y R S t hL hc hsp J hJ u hu htu ht)

theorem orbitGraph_of_alpha {r n : ℕ} (hα : TightAlphaLeafR r n) (hL : TightLargeHypR r n Y R S t)
    (hc : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)))
    (hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R))) :
    OrbitGraph (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) := by
  have hΩ := hL.datum.hypOmegaGen
  refine ⟨fun {K J} h => ⟨h.2.1, Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ h.1 h.2.1 h.2⟩,
    fun K h => h.2.2.1 rfl,
    fun {K J} g h => ⟨hΩ.conjInvariant g K h.1, Asc77.omegaNbr_conj hΩ.conjInvariant h.2 g⟩,
    fun {K J} h j hj => ?_, fun hKJ hKJ' h => hsp hKJ hKJ' h⟩
  obtain ⟨g, hgK'⟩ := h.1
  have hgK : conjSub g (tightCore R) = K := hgK'
  obtain ⟨a, haJ'⟩ := h.2.1
  have haJ : conjSub a (tightCore R) = J := haJ'
  obtain ⟨SJ, hLg⟩ := tightLargeHypR_conj hL g
  have hcore : tightCore (conjSub g R) = K := by rw [← conjSub_tightCore, hgK]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hcg : Disconnected.DConnected (CoreAssembly.conjClass (tightCore (conjSub g R))) := by
    rw [hfam]
    exact hc
  have hJ' : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub g R)))
      (tightCore (conjSub g R)) := by
    rw [hfam, hcore]
    exact h.2
  have huJ : IsUniqueInvolution J (a * t * a⁻¹) := haJ ▸ hL.datum.isUniqueInvolution_core.conj a
  have hαJ := hα Y (conjSub g R) SJ (g * t * g⁻¹) hLg hcg J hJ' (a * t * a⁻¹) huJ
  have hJN := edge_le_normalizer_of_alpha hLg.datum hJ' huJ hαJ
  rw [hcore] at hJN
  exact conjSub_eq_of_mem_normalizer (hJN hj)

theorem tightOddCent_of_conj_eq {r n : ℕ} (hL : TightLargeHypR r n Y R S t)
    (h : ∀ g : Y, oddCoreImg (Subgroup.centralizer ({g * t * g⁻¹} : Set Y)) =
      oddCoreImg (Subgroup.centralizer ({t} : Set Y))) : TightOddCent t := by
  have hnorm : (oddCoreImg (Subgroup.centralizer ({t} : Set Y))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [← h g]
    exact conj_mem_oddCent g hx
  have hle : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) ≤ classicalInvolutionOddCore Y :=
    le_sSup ⟨hnorm, odd_natCard_oddCoreImg _⟩
  have hO : classicalInvolutionOddCore Y = ⊥ := hL.cls.2.2
  rw [hO] at hle
  exact le_bot_iff.mp hle

theorem graphFam_of_alpha {r n : ℕ} (hα : TightAlphaLeafR r n) (hL : TightLargeHypR r n Y R S t)
    (hc : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)))
    (hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R))) :
    GraphFam (CoreAssembly.conjClass (tightCore R))
      (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) := by
  have hΩ := hL.datum.hypOmegaGen
  have hgen : (⨆ J ∈ CoreAssembly.conjClass (tightCore R), J) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hL.cls.2.1
  refine ⟨orbitGraph_of_alpha hα hL hc hsp, fun h => h.1,
    fun K hK g => hΩ.conjInvariant g K hK, ?_, ?_⟩
  · intro L hL' M hM
    obtain ⟨a, rfl⟩ := hL'
    obtain ⟨b, rfl⟩ := hM
    refine ⟨b * a⁻¹, by rw [hgen]; exact Subgroup.mem_top _, ?_⟩
    rw [conjSub_mul, conjSub_inv_conjSub]
  · intro L hL' M hM
    have key : ∀ b, Relation.ReflTransGen (fun M N : Subgroup Y =>
        N ∈ CoreAssembly.conjClass (tightCore R) ∧
          Disconnected.dAdj (CoreAssembly.conjClass (tightCore R)) M N) L b →
        b ∈ CoreAssembly.conjClass (tightCore R) ∧
          Relation.ReflTransGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L b := by
      intro b hb
      induction hb with
      | refl => exact ⟨hL', Relation.ReflTransGen.refl⟩
      | tail _ hbc ih =>
        rename_i b c
        obtain ⟨hbΩ, hpath⟩ := ih
        obtain ⟨hcΩ, hadj⟩ := hbc
        refine ⟨hcΩ, hpath.tail ⟨hbΩ, ?_⟩⟩
        rcases hadj with h | h
        · exact h
        · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hcΩ hbΩ h
    exact (key M (hc L hL' M hM)).2

theorem tightOddLeafR_of_maxSec {r n : ℕ} (hα : TightAlphaLeafR r n)
    (hconn : TightConnLeafR' r n) (hsep : TightSepLeafRα r n) (hsec : TightMaxSecR r n) :
    TightOddLeafR r n := by
  intro Y _ _ R S t hL
  have hd := hL.datum
  have huniq := hd.isUniqueInvolution_core
  have hc := hconn Y R S t hL
  have hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R)) :=
    hsep Y R S t hL (tightSepAlpha_of_alphaLeafR hα hL hc)
  have hF := graphFam_of_alpha hα hL hc hsp
  have hstep : ∀ M N : Subgroup Y,
      MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) M N → ∀ zM zN : Y,
      IsUniqueInvolution M zM → IsUniqueInvolution N zN →
      oddCoreImg (Subgroup.centralizer ({zN} : Set Y)) =
        oddCoreImg (Subgroup.centralizer ({zM} : Set Y)) := by
    intro M N hMN zM zN hzM hzN
    obtain ⟨g, hgM'⟩ := hMN.1.1
    have hgM : conjSub g (tightCore R) = M := hgM'
    obtain ⟨a, haN'⟩ := hMN.1.2.1
    have haN : conjSub a (tightCore R) = N := haN'
    obtain ⟨SJ, hLg⟩ := tightLargeHypR_conj hL g
    have hcore : tightCore (conjSub g R) = M := by rw [← conjSub_tightCore, hgM]
    have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
        CoreAssembly.conjClass (tightCore R) := by
      rw [← conjSub_tightCore, conjClass_conjSub]
    have hzM' : g * t * g⁻¹ = zM := by
      have h1 := huniq.conj g
      rw [hgM] at h1
      exact h1.eq hzM
    have hzN' : a * t * a⁻¹ = zN := by
      have h1 := huniq.conj a
      rw [haN] at h1
      exact h1.eq hzN
    have hcg : Disconnected.DConnected (CoreAssembly.conjClass (tightCore (conjSub g R))) := by
      rw [hfam]
      exact hc
    have hspg : TC.SepHyp (CoreAssembly.conjClass (tightCore (conjSub g R))) := by
      rw [hfam]
      exact hsp
    have hMN' : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore (conjSub g R))))
        (tightCore (conjSub g R)) N := by
      rw [hfam, hcore]
      exact hMN
    have hle := oddCent_le_of_maxSec hα hsec hLg hcg hspg hMN' hzN
    rw [hzM'] at hle
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [← hzN', ← hzM', card_oddCent_conj, card_oddCent_conj]
  have hall : ∀ L : Subgroup Y,
      Relation.ReflTransGen (MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))))
        (tightCore R) L → ∀ z : Y, IsUniqueInvolution L z →
      oddCoreImg (Subgroup.centralizer ({z} : Set Y)) =
        oddCoreImg (Subgroup.centralizer ({t} : Set Y)) := by
    intro L hpath
    induction hpath with
    | refl => intro z hz; rw [huniq.eq hz]
    | @tail M N _ hMN ih =>
      intro z hz
      obtain ⟨g, hgM'⟩ := hMN.1.1
      have hgM : conjSub g (tightCore R) = M := hgM'
      have hzM : IsUniqueInvolution M (g * t * g⁻¹) := hgM ▸ huniq.conj g
      rw [hstep M N hMN _ z hzM hz, ih _ hzM]
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  refine tightOddCent_of_conj_eq hL fun g => ?_
  have hgK : conjSub g (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨g, rfl⟩
  exact hall _ (reach_maxAdj hF hK _ hgK) (g * t * g⁻¹) (huniq.conj g)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
