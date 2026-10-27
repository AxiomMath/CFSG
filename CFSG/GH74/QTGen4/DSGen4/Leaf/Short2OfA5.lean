module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv10

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private theorem isPerfect_alt5 : Group.IsPerfect (alternatingGroup (Fin 5)) :=
  Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))

private theorem isPerfect_of_quotient {H : Type} [Group H] (N : Subgroup H) [N.Normal]
    (hN : N ≤ commutator H) [Group.IsPerfect (H ⧸ N)] : Group.IsPerfect H := by
  rw [Group.isPerfect_def, eq_top_iff]
  intro x _
  have hq : commutator (H ⧸ N) = ⊤ := Group.isPerfect_def.mp inferInstance
  have hmap : (commutator H).map (QuotientGroup.mk' N) = commutator (H ⧸ N) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have hx : QuotientGroup.mk' N x ∈ (commutator H).map (QuotientGroup.mk' N) := by
    rw [hmap, hq]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hyN : y⁻¹ * x ∈ N := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
    exact hyx
  simpa using (commutator H).mul_mem hy (hN hyN)

private theorem eq_top_of_perfect {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (N : Subgroup H) [N.Normal] (hN : IsPGroup 2 (H ⧸ N)) : N = ⊤ := by
  by_contra hne
  haveI : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  have : Group.IsNilpotent (H ⧸ N) := hN.isNilpotent
  exact Group.IsPerfect.not_isNilpotent (H ⧸ N) this

private theorem isQuasisimple_of_mulEquiv_alt5 {H : Type} [Group H]
    (e : H ≃* alternatingGroup (Fin 5)) : CFSG.IsQuasisimple H := by
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) := isPerfect_alt5
  haveI : IsSimpleGroup H := e.isSimpleGroup
  haveI : Group.IsPerfect H :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hc : Subgroup.center H = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center H) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) (Group.IsPerfect.not_isMulCommutative H)
  have hsimp : IsSimpleGroup (H ⧸ Subgroup.center H) :=
    MulEquiv.isSimpleGroup ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)
  haveI := hsimp
  have hnc : ∃ a b : H ⧸ Subgroup.center H, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative (H ⧸ Subgroup.center H) ⟨⟨fun a b => hcon a b⟩⟩
  unfold CFSG.IsQuasisimple
  exact ⟨inferInstance, hsimp, hnc⟩

theorem leafShort2OfA5 [DSLeaf LeafFaithfulA5] : LeafShort2OfA5 := by
  intro G _ _ L hq hc he hn
  obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) := isPerfect_alt5
  haveI : Group.IsPerfect (oTwoQuot ↥L) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : IsSimpleGroup (oTwoQuot ↥L) := e.isSimpleGroup
  have hc' : L ⊓ Subgroup.centralizer (blockQ L : Set G) ≤ blockQ L := hc
  have hLQn : L ≤ Subgroup.normalizer (blockQ L : Set G) :=
    CFSG.QuasithinUnique.C1.le_normalizer_blockQ L
  have hcomm : ∀ a ∈ blockQ L, ∀ b ∈ blockQ L, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (he.1.is_comm.comm (⟨a, ha⟩ : ↥(blockQ L)) ⟨b, hb⟩)
  obtain ⟨x, hxQ⟩ : ∃ x : ↥L, (x : G) ∉ blockQ L := by
    obtain ⟨y, hy⟩ := exists_ne (1 : oTwoQuot ↥L)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨x, fun h => hy ?_⟩
    have h' : (x : G) ∈ (pCore 2 ↥L).map L.subtype := h
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp h'
    have hkx' : k = x := Subtype.ext hkx
    rw [← hkx', QuotientGroup.eq_one_iff]
    exact hk
  have hnt : ∃ l ∈ L, ∃ e' ∈ blockQ L, ⁅l, e'⁆ ∉ (⊥ : Subgroup G) := by
    refine ⟨(x : G), x.2, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hxQ
    refine hc' (Subgroup.mem_inf.mpr ⟨x.2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := hcon h hh
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hsec : IsElemSec (⊥ : Subgroup G) (blockQ L) :=
    ⟨bot_le, Subgroup.commutator_le.mpr fun a ha b hb =>
      Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hcomm a ha b hb)),
      fun a ha => Subgroup.mem_bot.mpr (he.2 a ha)⟩
  have hPK : L ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp
  have hcard : (⊥ : Subgroup G).relIndex (blockQ L) ≤ 16 := by
    rw [Subgroup.relIndex_bot_left]
    exact le_of_eq hn
  have hcore : ∀ q ∈ pCoreOf 2 L, ∀ e' ∈ blockQ L, ⁅q, e'⁆ ∈ (⊥ : Subgroup G) := fun q hq' e' he' =>
    Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hcomm q hq' e' he'))
  have hA : A5Chief L L (blockQ L) ⊥ :=
    faithful_a5 le_rfl Subgroup.le_normalizer (CFSG.QuasithinUnique.C1.blockQ_le L) hLQn hPK hsec hcard
      hq hcore hnt
  have hsubU : blockU L ≤ blockQ L := by
    show ⁅blockQ L, L⁆ ≤ blockQ L
    refine Subgroup.commutator_le.mpr fun a ha l hl => ?_
    have h1 : l * a⁻¹ * l⁻¹ ∈ blockQ L :=
      (Subgroup.mem_normalizer_iff.mp (hLQn hl) a⁻¹).mp (inv_mem ha)
    have e1 : ⁅a, l⁆ = a * (l * a⁻¹ * l⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [e1]
    exact mul_mem ha h1
  have hU : blockU L = blockQ L := by
    rcases hA.irred (blockU L) bot_le hsubU (CFSG.QuasithinUnique.C1.le_normalizer_blockU L) with h | h
    · exfalso
      obtain ⟨l, hl, e', he', hne⟩ := hnt
      apply hne
      have h1 : ⁅e', l⁆ ∈ blockU L := Subgroup.commutator_mem_commutator he' hl
      rw [h, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot, ← commutatorElement_inv e' l, h1, inv_one]
    · exact h
  have hlt : blockZ L < blockU L := by
    refine lt_of_le_of_ne (fun g hg => (Subgroup.mem_inf.mp hg).1) ?_
    intro heq
    obtain ⟨l, hl, e', he', hne⟩ := hnt
    apply hne
    have he'U : e' ∈ blockU L := by
      rw [hU]
      exact he'
    have hcent : e' ∈ blockZ L := by
      rw [heq]
      exact he'U
    exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcent).2 l hl))
  have h5b : ∀ W : Subgroup G, blockZ L ≤ W → W ≤ blockU L → L ≤ Subgroup.normalizer (W : Set G) →
      W = blockZ L ∨ W = blockU L := by
    intro W hZW hWU hWN
    rcases hA.irred W bot_le (hWU.trans hU.le) hWN with h | h
    · left
      have hZbot : blockZ L = ⊥ := le_bot_iff.mp (hZW.trans h.le)
      exact h.trans hZbot.symm
    · right
      exact h.trans hU.symm
  have h3a : blockU L ≤ blockQ L ⊓ Subgroup.centralizer (blockQ L : Set G) := by
    rw [hU]
    exact le_inf le_rfl fun x hx => Subgroup.mem_centralizer_iff.mpr fun h hh => hcomm h hh x hx
  have h3b : ∀ x ∈ blockU L, x ^ 2 = 1 := fun x hx => he.2 x (by rw [hU] at hx; exact hx)
  have hK : pCore 2 ↥L ≤ commutator ↥L := by
    intro k hk
    have hkQ : (k : G) ∈ blockQ L := Subgroup.mem_map_of_mem L.subtype hk
    have hkU : (k : G) ∈ blockU L := by
      rw [hU]
      exact hkQ
    have hkU' : (k : G) ∈ ⁅blockQ L, L⁆ := hkU
    have h1 : (k : G) ∈ ⁅L, L⁆ :=
      Subgroup.commutator_mono (CFSG.QuasithinUnique.C1.blockQ_le L) le_rfl hkU'
    rw [← Subgroup.map_subtype_commutator L] at h1
    obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp h1
    have hyk' : y = k := Subtype.ext hyk
    rw [← hyk']
    exact hy
  haveI : Group.IsPerfect ↥L := isPerfect_of_quotient (pCore 2 ↥L) hK
  exact ⟨fun N _ hN => eq_top_of_perfect N hN, hc, ⟨h3a, h3b⟩,
    Or.inl (isQuasisimple_of_mulEquiv_alt5 e), ⟨hlt, h5b⟩⟩

end CFSG.GH74.QTGen4.DSGen4
