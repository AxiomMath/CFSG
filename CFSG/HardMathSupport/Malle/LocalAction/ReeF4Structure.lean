module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4PlaneCentralizer
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4OuterSigma
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4LocalCore
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4InSituNormalizer
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4SocleFacts
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Assembly
public import CFSG.HardMathSupport.Malle.Proving.ReeF4NormalizerPlane
public import CFSG.HardMathSupport.Malle.Proving.ReeF4CoreFields
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Reduction

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Malle.OvergroupTransport

theorem pRank_mono_of_le' {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 1 < p)
    {H H' : Subgroup G} (h : H ≤ H') : CFSG.Open.pRank p H ≤ CFSG.Open.pRank p H' := by
  unfold CFSG.Open.pRank
  have hne : {k | ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ k}.Nonempty :=
    ⟨0, ⊥, bot_le, ⟨inferInstance, fun x hx => by rw [Subgroup.mem_bot] at hx; subst hx; simp⟩,
      by simp⟩
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ H' ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E, -, -, hk⟩
    have h1 : k < p ^ k := Nat.lt_pow_self hp
    have h2 : Nat.card E ≤ Nat.card G := Nat.card_le_card_of_injective _ Subtype.val_injective
    omega
  exact csSup_le_csSup hbdd hne (fun k ⟨E, hE, he, hc⟩ => ⟨E, hE.trans h, he, hc⟩)

theorem reeF4_core_of_certs
    {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsReeFFourFiveIndex d) (e : Nonempty (K ≃* CatGroup d))
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) (T : Sylow 5 Y)
    (h3 : 3 ≤ CFSG.Open.pRank 5 (T : Subgroup Y)) :
    centerOf (T : Subgroup Y) ≤ K ∧ CFSG.Open.IsElemAbelian 5 (centerOf (T : Subgroup Y)) ∧
      Nat.card (centerOf (T : Subgroup Y)) = 5 ^ 2 ∧
      Subgroup.centralizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y) =
        (T : Subgroup Y) ∧
      ∃ i j h t : Y, CFSG.Quasithin.B45Tor.IsGL23Data (centerOf (T : Subgroup Y)) i j h t := by
  have hrankY : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Y) :=
    h3.trans (pRank_mono_of_le' (by norm_num) le_top)
  have hσ := exists_outer_sigma K d hd e hC hrankY
  exact reeF4_local_core K d hd e hC hσ
    (fun F _ _ _ hF P E hEP hE hEc => centralizer_plane_eq_sylow hF P E hEP hE hEc) T

theorem reeF4NormalizerStructure_of_certs :
    ReeF4NormalizerStructure := by
  intro Y _ _ K d hd hKn hiso hC T h3
  obtain ⟨hZK, hZe, hZc, hCZ, i, j, h, t, hGL⟩ := reeF4_core_of_certs K d hd hiso hC T h3
  have hNZT : Subgroup.normalizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer ((T : Subgroup Y) : Set Y) :=
    normalizer_le_normalizer_of_centralizer_eq hCZ
  have hNTZ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y) :=
    CFSG.HardMathSupport.Malle.Proving.le_normalizer_centreOfSub_of_le le_rfl
  have hEq : Subgroup.normalizer ((T : Subgroup Y) : Set Y) =
      Subgroup.normalizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y) :=
    le_antisymm hNTZ hNZT
  have hTC : (T : Subgroup Y) ≤ Subgroup.centralizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y) :=
    hCZ.ge
  have hTN : (T : Subgroup Y) ≤
      Subgroup.normalizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y) :=
    hTC.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨k, hk⟩ := CFSG.HardMathSupport.Malle.Proving.natCard_sylow_eq_pow T
  have hsolv := CFSG.HardMathSupport.Malle.Proving.isSolvable_normalizer_plane hZe hZc hk
    T.not_dvd_index hTN hTC (inf_le_right.trans hCZ.le)
  rw [hEq]
  exact ⟨reeF4InSitu_normalizer_of_solvable T hZe hZc hCZ hGL.toIsQ8Data hsolv, hZK⟩

theorem mem_normalizer_of_map_conj_eq {Y : Type*} [Group Y] {Z : Subgroup Y} {g : Y}
    (h : Z.map (MulAut.conj g).toMonoidHom = Z) : g ∈ Subgroup.normalizer (Z : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    have : z = x := by
      have h1 : g * z * g⁻¹ = g * x * g⁻¹ := by simpa [MulAut.conj_apply] using hzx
      simpa using h1
    rw [← this]
    exact hz

theorem reeF4SocleSylowNormal_of_certs :
    ReeF4SocleSylowNormal := by
  intro Y _ _ K d hd hKn hiso hC T h3
  obtain ⟨hZK, hZe, hZc, hCZ, -⟩ := reeF4_core_of_certs K d hd hiso hC T h3
  have hshape := sylowShape_five_of_catGroup (K := ↥K) hd (by
    obtain ⟨e⟩ := hiso; exact ⟨e⟩)
  obtain ⟨e⟩ := sylow_inf_homocyclic K hshape T
  have hZP : centerOf (T : Subgroup Y) ≤ (T : Subgroup Y) ⊓ K :=
    le_inf inf_le_left hZK
  intro g hg
  have hgZ : g ∈ Subgroup.normalizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y) := by
    apply mem_normalizer_of_map_conj_eq
    set Z := centerOf (T : Subgroup Y)
    have hmap : Z.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup Y) ⊓ K := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      have := (Subgroup.mem_normalizer_iff.mp hg z).mp (hZP hz)
      simpa [MulAut.conj_apply] using this
    refine eq_of_exponent_five_of_homocyclic e hmap hZP ?_ ?_ ?_ ?_
    · rintro x hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      have := hZe.2 z hz
      simp [MulAut.conj_apply, conj_pow, this]
    · intro x hx; exact hZe.2 x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hZc
    · exact hZc
  exact (normalizer_le_normalizer_of_centralizer_eq hCZ) hgZ

end CFSG.HardMathSupport.Malle.LocalAction
