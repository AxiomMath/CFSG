module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrLeaves
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrLie
public import CFSG.ClassicalInvolution.Q3.TL4SecIdFam
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

namespace AlphaFr

section Orbit

variable {Q : Type} [Group Q] {Φ : Set (Subgroup Q)}

theorem map_conjSub_subgroupOf_orbGrp (hcl : ConjInvariant Φ) {K : Subgroup Q} (hK : K ∈ Φ)
    (k : ↥(Vtx.orbGrp Φ K)) :
    (conjSub k (K.subgroupOf (Vtx.orbGrp Φ K))).map (Vtx.orbGrp Φ K).subtype =
      conjSub (k : Q) K := by
  rw [conjSub_subgroupOf]
  exact Subgroup.map_subgroupOf_eq_of_le
    (Vtx.conjSub_le_orbGrp K ⟨k, Vtx.orbGrp_le hcl hK k.2⟩)

theorem dConnected_conjClass_of_orbGrp [Finite Q] {r n : ℕ} (h4 : Thm4RBelow r n)
    (h : TypeRFam r Φ) (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n)
    (hgen : omegaGen Φ = ⊤) {K : Subgroup Q} (hK : K ∈ Φ)
    (hc : DConnected (CoreAssembly.conjClass (K.subgroupOf (Vtx.orbGrp Φ K)))) :
    DConnected (CoreAssembly.conjClass K) := by
  have hcl := h.hyp.conjInvariant
  have hconj : ∀ P ∈ CoreAssembly.conjClass K, ∃ k : ↥(Vtx.orbGrp Φ K), conjSub (k : Q) K = P := by
    rintro P ⟨g, rfl⟩
    have hg : g ∈ omegaGen Φ := by
      rw [hgen]
      exact Subgroup.mem_top g
    obtain ⟨k, hk, e⟩ :=
      Vtx.exists_orbGrp_conj hcl hK (Vtx.commute_conj_of_not_conj h4 h hO hn hK) hg
    exact ⟨⟨k, hk⟩, e.symm⟩
  have hmem : ∀ M' ∈ CoreAssembly.conjClass (K.subgroupOf (Vtx.orbGrp Φ K)),
      M'.map (Vtx.orbGrp Φ K).subtype ∈ CoreAssembly.conjClass K := by
    rintro _ ⟨k, rfl⟩
    exact ⟨(k : Q), (map_conjSub_subgroupOf_orbGrp hcl hK k).symm⟩
  have hedge : ∀ M' ∈ CoreAssembly.conjClass (K.subgroupOf (Vtx.orbGrp Φ K)),
      ∀ N' ∈ omegaNbr (CoreAssembly.conjClass (K.subgroupOf (Vtx.orbGrp Φ K))) M',
        N'.map (Vtx.orbGrp Φ K).subtype ∈
          omegaNbr (CoreAssembly.conjClass K) (M'.map (Vtx.orbGrp Φ K).subtype) := by
    intro M' _ N' hN'
    obtain ⟨hN'c, hne, T', hT', hTN', hTM'⟩ := hN'
    obtain ⟨L', hL', hTL'⟩ := exists_isSylow2In_of_mem_RSet hT'
    refine ⟨hmem N' hN'c,
      fun e => hne (Subgroup.map_injective (Vtx.orbGrp Φ K).subtype_injective e),
      T'.map (Vtx.orbGrp Φ K).subtype,
      mem_RSet_of_isSylow2In (hmem L' hL') (isSylow2In_map_subtype_iff.mpr hTL'),
      Subgroup.map_mono hTN', ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    refine (mem_normalizer_subgroupOf_iff (Subgroup.map_subtype_le M')).mpr ?_
    rw [subgroupOf_map_subtype']
    exact hTM' ht
  intro P hP P₂ hP₂
  obtain ⟨k, rfl⟩ := hconj P hP
  obtain ⟨k₂, rfl⟩ := hconj P₂ hP₂
  have key : ∀ N', Relation.ReflTransGen
      (fun M N => N ∈ CoreAssembly.conjClass (K.subgroupOf (Vtx.orbGrp Φ K)) ∧
        dAdj (CoreAssembly.conjClass (K.subgroupOf (Vtx.orbGrp Φ K))) M N)
      (conjSub k (K.subgroupOf (Vtx.orbGrp Φ K))) N' →
      N' ∈ CoreAssembly.conjClass (K.subgroupOf (Vtx.orbGrp Φ K)) ∧
        Relation.ReflTransGen
          (fun M N => N ∈ CoreAssembly.conjClass K ∧ dAdj (CoreAssembly.conjClass K) M N)
          (conjSub (k : Q) K) (N'.map (Vtx.orbGrp Φ K).subtype) := by
    intro N' hN'
    induction hN' with
    | refl =>
      refine ⟨⟨k, rfl⟩, ?_⟩
      rw [map_conjSub_subgroupOf_orbGrp hcl hK k]
    | @tail b c _ hbc ih =>
      obtain ⟨hb, ihp⟩ := ih
      obtain ⟨hcm, hadj⟩ := hbc
      refine ⟨hcm, ihp.tail ⟨hmem c hcm, ?_⟩⟩
      rcases hadj with h1 | h2
      · exact Or.inl (hedge b hb c h1)
      · exact Or.inr (hedge c hcm b h2)
  have h₂ := (key _ (hc _ ⟨k, rfl⟩ _ ⟨k₂, rfl⟩)).2
  rwa [map_conjSub_subgroupOf_orbGrp hcl hK k₂] at h₂

end Orbit

end AlphaFr

section Cit3

theorem tightSecLinkGenR_three_of_plus {n : ℕ} (hA : CIT3Below n) (hP : TightBelowRPlus 3 n)
    (h4 : Thm4RBelow 3 n) (hE2 : SecIdE2LinkGen) (hE4 : SecIdE4LinkCent) :
    TightSecLinkGenR 3 n := by
  intro X _ _ hn Φ h hO hgen _ A hA' B hB hBc hdisc u v hu hv
  have hcl := h.hyp.conjInvariant
  obtain ⟨S', hd, hc, hout⟩ :=
    secIdent3_of (secIdentDatum3_of hP hA) h4 X hn Φ h hO A hA' u hu
  have hAX : A ≤ Vtx.orbGrp Φ A := Vtx.le_orbGrp A
  obtain ⟨g, hgB⟩ := hBc
  have hgB' : conjSub g A = B := hgB
  have hg : g ∈ omegaGen Φ := by
    rw [hgen]
    exact Subgroup.mem_top g
  obtain ⟨k, hk, e⟩ :=
    Vtx.exists_orbGrp_conj hcl hA' (Vtx.commute_conj_of_not_conj h4 h hO hn hA') hg
  have hBX : B ≤ Vtx.orbGrp Φ A := by
    rw [← hgB']
    exact Vtx.conjSub_le_orbGrp A ⟨g, hg⟩
  have hAtc := tightCore_subgroupOf_orbGrp h hA'
  have hBc' : B.subgroupOf (Vtx.orbGrp Φ A) ∈
      CoreAssembly.conjClass (A.subgroupOf (Vtx.orbGrp Φ A)) := by
    refine ⟨⟨k, hk⟩, ?_⟩
    show conjSub (⟨k, hk⟩ : ↥(Vtx.orbGrp Φ A)) (A.subgroupOf (Vtx.orbGrp Φ A)) =
      B.subgroupOf (Vtx.orbGrp Φ A)
    rw [conjSub_subgroupOf, ← e, hgB']
  obtain ⟨hBΦ, hne, T, hT, hTB, hTN⟩ := id hB
  have hTsyl : IsSylow2In T B := Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hBΦ hT hTB
  have hnbr : B.subgroupOf (Vtx.orbGrp Φ A) ∈
      omegaNbr (CoreAssembly.conjClass (tightCore (A.subgroupOf (Vtx.orbGrp Φ A))))
        (tightCore (A.subgroupOf (Vtx.orbGrp Φ A))) := by
    rw [hAtc]
    exact ⟨hBc', subgroupOf_ne_of_ne hAX hBX hne, T.subgroupOf (Vtx.orbGrp Φ A),
      mem_RSet_of_isSylow2In hBc' (hTsyl.subgroupOf hBX),
      fun x hx => Subgroup.mem_subgroupOf.mpr (hTB (Subgroup.mem_subgroupOf.mp hx)),
      fun x hx => (mem_normalizer_subgroupOf_iff hAX).mp (hTN (Subgroup.mem_subgroupOf.mp hx))⟩
  have hv' := isUniqueInvolution_subgroupOf hv hBX
  have hnA : Nat.card ↥(Vtx.orbGrp Φ A) < n :=
    lt_of_le_of_lt (Subgroup.card_le_card_group _) hn
  have hdiscA : ¬ DConnected
      (CoreAssembly.conjClass (tightCore (A.subgroupOf (Vtx.orbGrp Φ A)))) := by
    rw [hAtc]
    exact fun hc' => hdisc (AlphaFr.dConnected_conjClass_of_orbGrp h4 h hO hn hgen hA' hc')
  have hgenA : Subgroup.centralizer
        ({(⟨u, Vtx.le_orbGrp A hu.mem⟩ : ↥(Vtx.orbGrp Φ A))} : Set ↥(Vtx.orbGrp Φ A)) ⊔
      Subgroup.centralizer
        ({(⟨v, hBX hv.mem⟩ : ↥(Vtx.orbGrp Φ A))} : Set ↥(Vtx.orbGrp Φ A)) ⊔
      Subgroup.centralizer
        ({(⟨u, Vtx.le_orbGrp A hu.mem⟩ : ↥(Vtx.orbGrp Φ A)) * ⟨v, hBX hv.mem⟩} :
          Set ↥(Vtx.orbGrp Φ A)) = ⊤ := by
    by_cases hE2' : TightInO2 (⟨u, Vtx.le_orbGrp A hu.mem⟩ : ↥(Vtx.orbGrp Φ A))
    · exact hE2 n hA hP _ hnA _ S' _ hd hc hE2' hdiscA _ hnbr _ hv'
    rcases hout with h2 | ⟨he, -⟩ | ⟨he, -⟩ | hE4' | hl
    · exact absurd h2 hE2'
    · exact absurd he (not_tightEdgeless_orbGrp h4 h hO hn hA' hB hg hgB')
    · exact absurd he (not_tightEdgeless_orbGrp h4 h hO hn hA' hB hg hgB')
    · have hz := hE4 _ _ S' _ hd hc hE2' hE4'.1 hE4'.2 _ hnbr _ hv'
      refine eq_top_iff.mpr fun w _ => Subgroup.mem_sup_right ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hz w)
    · exact SecIdLie3.linkGen hd hc hl hnbr hv'
  have hXA : Vtx.orbGrp Φ A ≤ Subgroup.centralizer ({u} : Set X) ⊔
      Subgroup.centralizer ({v} : Set X) ⊔ Subgroup.centralizer ({u * v} : Set X) := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥(Vtx.orbGrp Φ A)) ∈ (⊤ : Subgroup ↥(Vtx.orbGrp Φ A)) :=
      Subgroup.mem_top _
    rw [← hgenA] at hx'
    refine (sup_le (sup_le ?_ ?_) ?_ : _ ≤ (Subgroup.centralizer ({u} : Set X) ⊔
      Subgroup.centralizer ({v} : Set X) ⊔ Subgroup.centralizer ({u * v} : Set X)).comap
        (Vtx.orbGrp Φ A).subtype) hx'
    · intro y hy
      have hy' := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
      exact Subgroup.mem_sup_left
        (Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hy'))
    · intro y hy
      have hy' := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
      exact Subgroup.mem_sup_left
        (Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.mpr hy'))
    · intro y hy
      have hy' := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
      exact Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.mpr hy')
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun L hL => ?_
  by_cases hcL : ∃ g' ∈ omegaGen Φ, conjSub g' A = L
  · obtain ⟨g', hg', rfl⟩ := hcL
    exact (Vtx.conjSub_le_orbGrp A ⟨g', hg'⟩).trans hXA
  · have hcomm := Vtx.commutes_of_not_conj h4 h hO hn hA' hL hcL
    intro b hb
    refine Subgroup.mem_sup_left (Subgroup.mem_sup_left ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm u hu.mem b hb).symm

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
