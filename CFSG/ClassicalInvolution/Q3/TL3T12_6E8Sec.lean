module

public import CFSG.ClassicalInvolution.Q3.TL3T12_6Dual
public import CFSG.ClassicalInvolution.Q3.TL3T12_6E8Three

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω P : Set (Subgroup G)} {E : Subgroup G}

theorem E8Struct.toTop {X : Subgroup G} (hE : E8Struct X E) :
    E8Struct (⊤ : Subgroup ↥X) (E.subgroupOf X) where
  le := le_top
  normal := fun x _ e he => Subgroup.mem_subgroupOf.mpr
    (hE.normal x x.2 e (Subgroup.mem_subgroupOf.mp he))
  card := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE.le).toEquiv]
    exact hE.card
  sq := fun e he => Subtype.ext (hE.sq e (Subgroup.mem_subgroupOf.mp he))
  cent := fun x _ hc => Subgroup.mem_subgroupOf.mpr (hE.cent x x.2 fun e he =>
    congrArg Subtype.val (hc ⟨e, hE.le he⟩ (Subgroup.mem_subgroupOf.mpr he)))
  core := by
    intro Q _ hQn hQ2 q hq
    have hQX : Q.map X.subtype ≤ X := Subgroup.map_subtype_le _
    have hle := hE.core (Q.map X.subtype) hQX (by
        rintro x hx _ ⟨q', hq', rfl⟩
        exact ⟨⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹, hQn ⟨x, hx⟩ (Subgroup.mem_top _) q' hq', rfl⟩)
      (hQ2.map X.subtype)
    exact Subgroup.mem_subgroupOf.mpr (hle ⟨q, hq, rfl⟩)
  index := by
    have h1 := Subgroup.relIndex_subgroupOf (H := E) (K := X) (L := X) le_rfl
    rw [Subgroup.subgroupOf_self] at h1
    exact h1.trans hE.index

theorem SecHyp.thmDHyp (hP : SecHyp r Ω P) : ThmDHyp r (restrictFamily P (pSpan P)) := by
  have hLX : ∀ L ∈ P, L ≤ pSpan P := fun L hL => le_pSpan hL
  have hΩ' : HypOmegaGen (restrictFamily P (pSpan P)) := by
    refine TL4.hypOmegaGen_restrict_of (pSpan P) hLX (fun n hn L hL => hP.inv L hL n hn)
      (fun K hK => hP.hyp.omega1 K (hP.sub hK)) (fun K hK => ?_)
      (fun K hK J hJ => hP.hyp.omega3 K (hP.sub hK) J (hP.sub hJ))
      (fun K hK J hJ hne => hP.hyp.omega4 K (hP.sub hK) J (hP.sub hJ) hne)
      (fun K hK J hJ hne => hP.hyp.omega5 K (hP.sub hK) J (hP.sub hJ) hne)
    refine le_antisymm (Subgroup.closure_le _ |>.mpr fun x hx => hx.1) fun x hx => ?_
    exact Subgroup.subset_closure ⟨hx, (hP.two K (hP.sub hK)).to_le (Subgroup.zpowers_le.mpr hx)⟩
  refine ⟨hΩ', ?_, ?_, ?_, pSpan_restrictFamily_eq_top P, ?_, hP.odd, ?_⟩
  · rintro _ ⟨J, hJ, -, rfl⟩
    exact (hP.two J (hP.sub hJ)).comap_subtype
  · rintro _ ⟨J, hJ, hJX, rfl⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJX).toEquiv]
    exact hP.card J (hP.sub hJ)
  · rintro _ ⟨J, hJ, hJX, rfl⟩
    exact aEmpty_restrictFamily hP.hyp hP.two hP.sub hJX (hP.aEmpty J (hP.sub hJ))
  · rintro _ ⟨L, hL, -, rfl⟩ _ ⟨L', hL', -, rfl⟩
    obtain ⟨x, hx, hxL⟩ := hP.trans L hL L' hL'
    exact ⟨⟨x, hx⟩, by rw [conjSub_subgroupOf, hxL]⟩
  · rintro _ ⟨L, hL, hLX', rfl⟩ u hu
    obtain ⟨Q, -, hQn, hQ2, huQ⟩ :=
      hP.e2 L hL (u : G) (isUniqueInvolution_of_subgroupOf hu hLX')
    refine ⟨Q.subgroupOf (pSpan P), ⟨fun q hq g => ?_⟩, hQ2.comap_subtype,
      Subgroup.mem_subgroupOf.mpr huQ⟩
    exact Subgroup.mem_subgroupOf.mpr (hQn g g.2 q (Subgroup.mem_subgroupOf.mp hq))

namespace SecHyp

variable (hP : SecHyp 3 Ω P) (hE : E8Struct (pSpan P) E)
include hP hE

theorem e8_inv_mem {L : Subgroup G} (hL : L ∈ P) {u : G} (hu : IsUniqueInvolution L u) :
    u ∈ E := by
  obtain ⟨Q, hQX, hQn, hQ2, huQ⟩ := hP.e2 L hL u hu
  exact hE.core Q hQX hQn hQ2 huQ

theorem e8_conj_mem_or {L : Subgroup G} (hL : L ∈ P) {u : G} (hu : IsUniqueInvolution L u)
    {k : G} (hk : k ∈ L) {e : G} (he : e ∈ E) :
    k * e * k⁻¹ = e ∨ k * e * k⁻¹ = u * e := by
  have hLX : L ≤ pSpan P := le_pSpan hL
  have h := conj_mem_or_e8 hP.thmDHyp hE.toTop (K := L.subgroupOf (pSpan P))
    ⟨L, hL, hLX, rfl⟩ (isUniqueInvolution_subgroupOf hu hLX) (k := ⟨k, hLX hk⟩)
    (Subgroup.mem_subgroupOf.mpr hk) (e := ⟨e, hE.le he⟩) (Subgroup.mem_subgroupOf.mpr he)
  rcases h with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem e8_eq_of_comm {L : Subgroup G} (hL : L ∈ P) {u : G} (hu : IsUniqueInvolution L u)
    {e : G} (he : e ∈ E) (hc : ∀ k ∈ L, k * e = e * k) : e = 1 ∨ e = u := by
  have hLX : L ≤ pSpan P := le_pSpan hL
  have h := eq_of_comm_e8 hP.thmDHyp hE.toTop (K := L.subgroupOf (pSpan P))
    ⟨L, hL, hLX, rfl⟩ (isUniqueInvolution_subgroupOf hu hLX) (e := ⟨e, hE.le he⟩)
    (Subgroup.mem_subgroupOf.mpr he) fun k hk =>
      Subtype.ext (hc k (Subgroup.mem_subgroupOf.mp hk))
  rcases h with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem e8_exists_conj {L : Subgroup G} (hL : L ∈ P) {u : G} (hu : IsUniqueInvolution L u)
    {e : G} (he : e ∈ E) (he1 : e ≠ 1) : ∃ x ∈ pSpan P, x * u * x⁻¹ = e := by
  have hLX : L ≤ pSpan P := le_pSpan hL
  obtain ⟨g, hg⟩ := exists_conj_e8 hP.thmDHyp hE.toTop (K := L.subgroupOf (pSpan P))
    ⟨L, hL, hLX, rfl⟩ (isUniqueInvolution_subgroupOf hu hLX) (e := ⟨e, hE.le he⟩)
    (Subgroup.mem_subgroupOf.mpr he) (fun h => he1 (congrArg Subtype.val h))
  exact ⟨g, g.2, congrArg Subtype.val hg⟩

theorem e8_noCentralInv : NoCentralInv P := by
  intro L hL u hu hc
  have hE8 : (2 : ℕ) < Nat.card E := by rw [hE.card]; norm_num
  obtain ⟨e, heE, he1, heu⟩ : ∃ e ∈ E, e ≠ 1 ∧ e ≠ u := by
    by_contra hcon
    push Not at hcon
    have := natCard_subgroup_le_two_of_subset (A := E) (a := 1) (b := u) fun x hx => by
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x hx h1)
    omega
  obtain ⟨x, hx, hxu⟩ := hP.e8_exists_conj hE hL hu heE he1
  apply heu
  rw [← hxu, hc x hx]
  group

theorem e8_le_closure_threeElts {K : Subgroup G} (hK : K ∈ P) {z : G}
    (hz : IsUniqueInvolution K z) :
    E ≤ Subgroup.closure {w : G | w ∈ pSpan P ∧ w * z = z * w ∧ ∃ a : ℕ, w ^ 3 ^ a = 1} := by
  have hKX : K ≤ pSpan P := le_pSpan hK
  have hD := hP.thmDHyp
  have hE' := hE.toTop
  have hK' : K.subgroupOf (pSpan P) ∈ restrictFamily P (pSpan P) := ⟨K, hK, hKX, rfl⟩
  have hz' := isUniqueInvolution_subgroupOf hz hKX
  have hzE : (⟨z, hKX hz.mem⟩ : ↥(pSpan P)) ∈ E.subgroupOf (pSpan P) := inv_mem_e8 hD hE' hK' hz'
  obtain ⟨y, hyz, hy3, -, -⟩ := exists_three_e8 hD hE' hK' hz'
  have hmain := e8_top_le_closure hE' hzE (fun h => hz.ne_one (congrArg Subtype.val h))
    (card_centralizer_e8 hD hE' hK' hz') hyz hy3
  intro e he
  have h1 := hmain (Subgroup.mem_subgroupOf.mpr he : (⟨e, hE.le he⟩ : ↥(pSpan P)) ∈ _)
  have hle : Subgroup.closure {w : ↥(pSpan P) | w * ⟨z, hKX hz.mem⟩ = ⟨z, hKX hz.mem⟩ * w ∧
      ∃ a : ℕ, w ^ 3 ^ a = 1} ≤ (Subgroup.closure {w : G | w ∈ pSpan P ∧ w * z = z * w ∧
        ∃ a : ℕ, w ^ 3 ^ a = 1}).comap (pSpan P).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro w ⟨hwz, a, hwa⟩
    refine Subgroup.subset_closure ⟨w.2, congrArg Subtype.val hwz, a, ?_⟩
    simpa using congrArg Subtype.val hwa
  exact hle h1

end SecHyp

end CFSG.ClassicalInvolution.Q3.TC.Thin
