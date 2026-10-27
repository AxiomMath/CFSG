module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinHyps
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinD2Leaves
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinD2Leaves2

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section WIn

variable {G : Type} [Group G] [Finite G]

theorem false_of_WIn_eq_R {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hPne : P.Nonempty)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) {w : G}
    (hXw : pSpan P ≤ Subgroup.centralizer ({w} : Set G))
    (hXn : ((pSpan P).subgroupOf (Subgroup.centralizer ({w} : Set G))).Normal)
    (hthin : ∀ L ∈ P, ¬ UAt Ω w L) {W : Subgroup G} (hW : WIn P (pSpan P) = {W}) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := pSpan P with hX
  have hc' : ConjInvariant (restrictFamily P X) :=
    conjInvariant_restrictFamily fun L hL x hx => hinv L hL x hx
  have hWmem : W ∈ WIn P X := by rw [hW]; rfl
  obtain ⟨W', hW'mem, rfl⟩ := hWmem
  have hW'uniq : ∀ W'' ∈ WSet (restrictFamily P X), W'' = W' := by
    intro W'' h
    have h1 : W''.map X.subtype ∈ WIn P X := ⟨W'', h, rfl⟩
    rw [hW] at h1
    exact Subgroup.map_injective X.subtype_injective h1
  have hnorm' : ∀ g : X, conjSub g W' = W' := fun g => hW'uniq _ (WSet.conj hc' hW'mem g)
  obtain ⟨η, ⟨S, hη, -⟩, hW'eq⟩ := hW'mem
  have hWS : W' ≤ (S : Subgroup X) := by
    rw [hW'eq]
    exact iSup₂_le fun U hU => (hη.1 hU).2
  have hW2 : IsPGroup 2 ↥(W'.map X.subtype) := (S.isPGroup'.to_le hWS).map _
  have hWX : W'.map X.subtype ≤ X := Subgroup.map_subtype_le _
  have hnorm : ∀ x ∈ X, ∀ q ∈ W'.map X.subtype, x * q * x⁻¹ ∈ W'.map X.subtype := by
    rintro x hx _ ⟨q, hq, rfl⟩
    have h1 : (⟨x, hx⟩ : X) * q * (⟨x, hx⟩ : X)⁻¹ ∈ conjSub (⟨x, hx⟩ : X) W' :=
      conj_mem_conjSub hq
    rw [hnorm'] at h1
    exact ⟨_, h1, rfl⟩
  obtain ⟨L, hL⟩ := hPne
  have hL'2 : IsPGroup 2 ↥(L.subgroupOf X) := (h2 L (hPΩ hL)).comap_subtype
  obtain ⟨S'', hS''⟩ := hL'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S'' S
  have hgS : conjSub g (L.subgroupOf X) ≤ (S : Subgroup X) := by
    rw [← hg, Sec7.coe_smul_sylow]
    exact conjSub_mono hS''
  rw [conjSub_subgroupOf] at hgS
  set L₁ := conjSub (g : G) L with hL₁
  have hL₁P : L₁ ∈ P := hinv L hL g g.2
  have hL₁X : L₁ ≤ X := le_pSpan hL₁P
  have hL₁2 : IsPGroup 2 ↥(L₁.subgroupOf X) := (h2 L₁ (hPΩ hL₁P)).comap_subtype
  have hq₁ : IsQuatSub L₁ :=
    Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isPGroup (hPΩ hL₁P) (h2 L₁ (hPΩ hL₁P)))
  obtain ⟨C, hCL₁, hCc, hCcard⟩ := hq₁.exists_cyclic_index_two
  have hCX : C ≤ X := hCL₁.trans hL₁X
  have hU1 : C.subgroupOf X ∈ USet (restrictFamily P X) := by
    refine mem_USet_of_natCard (R := L₁.subgroupOf X) (J := L₁.subgroupOf X)
      ⟨L₁, hL₁P, hL₁X, rfl⟩ ⟨le_rfl, hL₁2, fun Q hQ _ hRQ => le_antisymm hQ hRQ⟩
      (Subgroup.subgroupOf_mono X hCL₁) ?_ ?_
    · exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hCX).symm.surjective
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁X).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv]
      exact hCcard
  have hU1S : C.subgroupOf X ≤ (S : Subgroup X) :=
    (Subgroup.subgroupOf_mono X hCL₁).trans hgS
  have hηpos : η.ncard ≠ 0 := by
    have h1 := hη.2.2 {C.subgroupOf X} (by
      intro U hU
      rw [Set.mem_singleton_iff.mp hU]
      exact ⟨hU1, hU1S⟩) (by
      intro U hU U' hU' hne
      exact absurd ((Set.mem_singleton_iff.mp hU).trans (Set.mem_singleton_iff.mp hU').symm) hne)
    rw [Set.ncard_singleton] at h1
    omega
  obtain ⟨U₀, hU₀⟩ := Set.nonempty_of_ncard_ne_zero hηpos
  obtain ⟨hU₀U, -⟩ := hη.1 hU₀
  obtain ⟨R₀, hR₀, hU₀R₀, hU₀c, hidx⟩ := hU₀U
  obtain ⟨J₀', hJ₀', hR₀J₀, -, hmax⟩ := mem_RSet_iff.mp hR₀
  obtain ⟨J₀, hJ₀, hJ₀X, rfl⟩ := hJ₀'
  have hJ₀'2 : IsPGroup 2 ↥(J₀.subgroupOf X) := (h2 J₀ (hPΩ hJ₀)).comap_subtype
  have hR₀eq : J₀.subgroupOf X = R₀ := hmax _ le_rfl hJ₀'2 hR₀J₀
  have hU₀W : U₀ ≤ W' := by
    rw [hW'eq]
    exact le_biSup (fun U => U) hU₀
  have hRmap : R₀.map X.subtype = J₀ := by
    rw [← hR₀eq]
    exact Subgroup.map_subgroupOf_eq_of_le hJ₀X
  have hUle : U₀.map X.subtype ≤ J₀ := hRmap ▸ Subgroup.map_mono hU₀R₀
  have hUW : U₀.map X.subtype ≤ W'.map X.subtype := Subgroup.map_mono hU₀W
  have hWQ : W'.map X.subtype ≤ pCoreOf 2 X := by
    have hQnorm : ((W'.map X.subtype).subgroupOf X).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hWX]
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => hnorm x hx y hy, fun hy => ?_⟩
      have := hnorm x⁻¹ (X.inv_mem hx) _ hy
      simpa [mul_assoc] using this
    exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ X hWX hQnorm hW2
  refine hthin J₀ hJ₀ ⟨U₀.map X.subtype,
    ⟨J₀, mem_RSet_of_isPGroup (hPΩ hJ₀) (h2 J₀ (hPΩ hJ₀)), hUle, ?_, ?_⟩, hUle, pCoreOf 2 X,
    TwinThin.isNormalTwoIn_pCore hXw hXn, hUW.trans hWQ⟩
  · haveI := hU₀c
    exact isCyclic_of_surjective _
      (Subgroup.equivMapOfInjective U₀ X.subtype X.subtype_injective).surjective
  · rw [← hRmap]
    rw [Subgroup.relIndex_map_map_of_injective _ _ X.subtype_injective]
    exact hidx

end WIn

section E8

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem false_of_e8Struct_pSpan' {r : ℕ} (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω)
    (hinO2 : ∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q)
    {E : Subgroup G} (hE : E8Struct (pSpan P) E) {K : Subgroup G} (hK : K ∈ P) : False := by
  obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 K (hPΩ hK)
  have hzE : z ∈ E := by
    obtain ⟨Q, hQX, hQn, hQ2, hzQ⟩ := hinO2 K hK z hz
    exact hE.core Q hQX hQn hQ2 hzQ
  have h := card_eq_eight_of_e8Struct hΩ h2 hE (hPΩ hK) (le_pSpan hK) hz hzE
  rw [h8 K (hPΩ hK)] at h
  have h3 : r = 3 := Nat.pow_right_injective (le_refl 2) (show 2 ^ r = 2 ^ 3 by omega)
  omega

end E8

section Setting

variable {G : Type} [Group G] [Finite G]

structure ThinSettingR (r : ℕ) (K₀ K K' : Subgroup G) (z : G) (π : Set (Subgroup G)) (g : G) :
    Prop where
  hs : TwinGraphStd K₀
  hK : K ∈ CoreAssembly.conjClass K₀
  hK' : K' ∈ twinSet (CoreAssembly.conjClass K₀) K
  hne : K' ≠ K
  card : ∀ J ∈ CoreAssembly.conjClass K₀, Nat.card J = 2 ^ r
  hA : AEmpty (CoreAssembly.conjClass K₀) K
  hz : IsUniqueInvolution K z
  hπ : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K
  hH1 : NoCentralInv π
  hg : conjSub g K ∈ π
  hO : classicalInvolutionOddCore ↥(conjSub g (piGen π)) = ⊥
  thin : ∀ M N : Subgroup G, MaxAdj (nbrAdj (CoreAssembly.conjClass K₀)) M N →
    ThinAt (CoreAssembly.conjClass K₀) M N

variable {r : ℕ} {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)} {g : G}

namespace ThinSettingR

variable (S : ThinSettingR r K₀ K K' z π g)
include S

theorem hos : OrbitStd (CoreAssembly.conjClass K₀) := S.hs.orbitStd

theorem hKX : K ≤ conjSub g (piGen π) := S.hos.le_conj_piGen S.hπ S.hg

theorem fam_gen :
    pSpan (TwinThin.fam K (conjSub g (piGen π))) = conjSub g (piGen π) :=
  TwinThin.pSpan_fam (TwinSecXg.sec_gen S.hos S.hπ S.hg)

theorem aEmpty : ∀ J ∈ CoreAssembly.conjClass K₀, AEmpty (CoreAssembly.conjClass K₀) J :=
  Asc77.T3.aEmpty_forall_of_transitive' S.hs.hyp.conjInvariant
    (TwinSecXg.conj_trans_of_mem_conjClass S.hK) S.hA

theorem le_cent : conjSub g (piGen π) ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) :=
  (S.hos.conj_piGen_le_centralizer S.hK S.hπ S.hH1 S.hz g).1

theorem normal_cent :
    ((conjSub g (piGen π)).subgroupOf (Subgroup.centralizer ({g * z * g⁻¹} : Set G))).Normal :=
  S.hos.conj_piGen_normal S.hK S.hπ S.hH1 S.hz g

theorem mem_fam_self : K ∈ TwinThin.fam K (conjSub g (piGen π)) := by
  have := TwinThin.mem_fam (K := K) (X' := conjSub g (piGen π)) (Subgroup.one_mem _)
  rwa [conjSub_one] at this

theorem twin_mem_fam : K' ∈ TwinThin.fam K (conjSub g (piGen π)) := by
  obtain ⟨a, ha, hKa⟩ := TwinSecXg.twin_conj S.hos S.hK S.hπ S.hH1 S.hg S.hK'
  rw [← hKa]
  exact TwinThin.mem_fam ha

theorem maxAdj_fam {L : Subgroup G} (hL : L ∈ TwinThin.fam K (conjSub g (piGen π))) :
    MaxAdj (nbrAdj (CoreAssembly.conjClass K₀)) (conjSub g K) L := by
  obtain ⟨x, rfl⟩ := hL
  have hπ' : conjSub g '' π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) (conjSub g K) :=
    isMaxOrb_conj S.hos.graph S.hπ g
  refine TwinThin.maxAdj_of_mem_maxOrb S.hos.graph hπ' ?_
  have hKmem : K ∈ conjSub g '' π := S.hos.mem_conj_image_of_mem S.hπ S.hg
  have hx : (x : G) ∈ piGen (conjSub g '' π) := by
    rw [piGen_conj]
    exact x.2
  exact stable_of_maxOrb S.hos.graph hπ' (x : G) hx K hKmem

theorem exists_normalTwo {L : Subgroup G} (hL : L ∈ TwinThin.fam K (conjSub g (piGen π))) {u : G}
    (hu : IsUniqueInvolution L u) :
    ∃ Q : Subgroup G, Q ≤ conjSub g (piGen π) ∧
      (∀ x ∈ conjSub g (piGen π), ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 ↥Q ∧ u ∈ Q := by
  have hth := S.thin _ _ (S.maxAdj_fam hL)
  obtain ⟨Q, ⟨hQC, hQ2, hQn⟩, huQ⟩ := hth.1 (g * z * g⁻¹) u (S.hz.conj g) hu
  have hLX : L ≤ conjSub g (piGen π) := by
    obtain ⟨x, rfl⟩ := hL
    have := conjSub_mono (n := (x : G)) S.hKX
    rwa [conjSub_eq_self_of_mem x.2] at this
  refine ⟨Q ⊓ conjSub g (piGen π), inf_le_right, fun x hx q hq => ?_, hQ2.to_le inf_le_left,
    Subgroup.mem_inf.mpr ⟨huQ, hLX hu.mem⟩⟩
  exact Subgroup.mem_inf.mpr ⟨hQn x (S.le_cent hx) q (Subgroup.mem_inf.mp hq).1,
    (conjSub g (piGen π)).mul_mem ((conjSub g (piGen π)).mul_mem hx (Subgroup.mem_inf.mp hq).2)
      ((conjSub g (piGen π)).inv_mem hx)⟩

theorem false_of_four_le (hr : 4 ≤ r) : False := by
  have hΩ := S.hs.hyp
  have h2 := S.hs.two
  have hPΩ : TwinThin.fam K (conjSub g (piGen π)) ⊆ CoreAssembly.conjClass K₀ :=
    TwinThin.fam_subset S.hos.graph S.hK
  have hP : pSpan (TwinThin.fam K (conjSub g (piGen π))) = conjSub g (piGen π) := S.fam_gen
  have htrans : ∀ L ∈ TwinThin.fam K (conjSub g (piGen π)),
      ∀ L' ∈ TwinThin.fam K (conjSub g (piGen π)),
      ∃ x ∈ pSpan (TwinThin.fam K (conjSub g (piGen π))), conjSub x L = L' := by
    rw [hP]; exact TwinThin.fam_trans
  have hinv : ∀ L ∈ TwinThin.fam K (conjSub g (piGen π)),
      ∀ x ∈ pSpan (TwinThin.fam K (conjSub g (piGen π))),
      conjSub x L ∈ TwinThin.fam K (conjSub g (piGen π)) := by
    rw [hP]; exact TwinThin.fam_inv
  have hodd : classicalInvolutionOddCore ↥(pSpan (TwinThin.fam K (conjSub g (piGen π)))) = ⊥ := by
    rw [hP]; exact S.hO
  have hE2 : ∀ L ∈ TwinThin.fam K (conjSub g (piGen π)), ∀ u : G, IsUniqueInvolution L u →
      ∃ Q : Subgroup G, Q ≤ pSpan (TwinThin.fam K (conjSub g (piGen π))) ∧
        (∀ x ∈ pSpan (TwinThin.fam K (conjSub g (piGen π))), ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧
          IsPGroup 2 Q ∧ u ∈ Q := by
    rw [hP]; exact fun L hL u hu => S.exists_normalTwo hL hu
  rcases thmDGen_at hΩ h2 S.card S.aEmpty hPΩ (thmDAbs_of_four_le hr _) htrans hinv hodd hE2 with
    hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | h64 | ⟨m, hm, hAE⟩ | h29
  · exact S.hne (hsing _ S.twin_mem_fam _ S.mem_fam_self)
  · refine false_of_WIn_eq_R hΩ h2 hPΩ ⟨K, S.mem_fam_self⟩ hinv (w := g * z * g⁻¹) ?_ ?_ ?_ hW
    · rw [hP]; exact S.le_cent
    · rw [hP]; exact S.normal_cent
    · exact fun L hL => (S.thin _ _ (S.maxAdj_fam hL)).2 (g * z * g⁻¹) (S.hz.conj g)
  · exact false_of_e8Struct_pSpan' hr hΩ h2 S.card hPΩ hE2 hE S.mem_fam_self
  · obtain ⟨I⟩ := h64
    exact false_of_aeIdentOn_of_four_le hr hΩ h2 S.card hPΩ (by norm_num) I S.mem_fam_self
  · obtain ⟨I⟩ := hAE
    exact false_of_aeIdent_of_four_le hr hΩ h2 S.card hPΩ hm I S.mem_fam_self
  · obtain ⟨I⟩ := h29
    exact false_of_aeIdentOn_of_four_le hr hΩ h2 S.card hPΩ (by norm_num) I S.mem_fam_self

end ThinSettingR

end Setting

end CFSG.CGT.PushingUpLit.SolKNA.R4
