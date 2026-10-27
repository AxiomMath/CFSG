module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264X1ExcF4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnModel
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HF4Model
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint.Chevalley

namespace X1F4

theorem isElemAbelian_of_le {G : Type*} [Group G] {p : ℕ} {E F : Subgroup G}
    (hE : IsElemAbelian p E) (hFE : F ≤ E) : IsElemAbelian p F := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE.2 x (hFE hx)⟩
  apply Subtype.ext
  have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, hFE a.2⟩ ⟨b, hFE b.2⟩)
  exact h

theorem isElemAbelian_comap {G H : Type*} [Group G] [Group H] {p : ℕ} {f : G →* H}
    (hf : Function.Injective f) {U : Subgroup H} (hU : IsElemAbelian p U) :
    IsElemAbelian p (U.comap f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hf
    have h := congrArg Subtype.val (hU.1.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩)
    simpa [map_mul] using h
  · apply hf
    rw [map_pow, map_one]
    exact hU.2 _ hx

theorem congr_conj_conj {G : Type*} [Group G] (c g : G) :
    MulAut.congr (MulAut.conj c) (MulAut.conj g) = MulAut.conj (MulAut.conj c g) := by
  ext x
  simp [MulAut.congr_apply, mul_assoc]

theorem concl_of_equiv {S T : Type} [Group S] [Finite S] [Group T] [Finite T] (e : S ≃* T)
    (h : ∀ A' : Subgroup (MulAut T), IsElemAbelian 3 A' →
      CFSG.Open.pRank 3 (⊤ : Subgroup T) ≤ CFSG.Open.pRank 3 A' →
        ∃ F' ≤ A', IsElemAbelian 3 F' ∧ 9 ≤ Nat.card F' ∧ IsGood 3 F')
    (A : Subgroup (MulAut S)) (hA : IsElemAbelian 3 A)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ CFSG.Open.pRank 3 A) :
    ∃ F ≤ A, IsElemAbelian 3 F ∧ min 2 (CFSG.Open.pRank 3 A - 1) ≤ CFSG.Open.pRank 3 F ∧
      IsGood 3 F := by
  have hΦ : Function.Injective (MulAut.congr e) := (MulAut.congr e).injective
  have hΦ' : Function.Injective (MulAut.congr e).symm := (MulAut.congr e).symm.injective
  have hA' : IsElemAbelian 3 (A.map (MulAut.congr e).toMonoidHom) :=
    RowXUn.isElemAbelian_map_of_injective hΦ hA
  have hrk' : CFSG.Open.pRank 3 (⊤ : Subgroup T) ≤
      CFSG.Open.pRank 3 (A.map (MulAut.congr e).toMonoidHom) := by
    rw [RowXUn.pRank_map_of_injective Nat.prime_three hΦ hA,
      ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact hrk
  obtain ⟨F', hF'A', hF'el, hF'card, hF'good⟩ := h _ hA' hrk'
  have hFel : IsElemAbelian 3 (F'.map (MulAut.congr e).symm.toMonoidHom) :=
    RowXUn.isElemAbelian_map_of_injective hΦ' hF'el
  have hFcard : 3 ^ 2 ≤ Nat.card (F'.map (MulAut.congr e).symm.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective hΦ']
    norm_num
    exact hF'card
  have hFrank : 2 ≤ CFSG.Open.pRank 3 (F'.map (MulAut.congr e).symm.toMonoidHom) := by
    have h1 := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hFel
    rw [h1] at hFcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hFcard
  have hmm : (F'.map (MulAut.congr e).symm.toMonoidHom).map (MulAut.congr e).toMonoidHom =
      F' := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      show (MulAut.congr e) ((MulAut.congr e).symm z) ∈ F'
      rw [MulEquiv.apply_symm_apply]
      exact hz
    · intro hx
      exact ⟨(MulAut.congr e).symm x, ⟨x, hx, rfl⟩, MulEquiv.apply_symm_apply _ _⟩
  refine ⟨F'.map (MulAut.congr e).symm.toMonoidHom, ?_, hFel,
    (min_le_left _ _).trans hFrank, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hF'A' hy
    show (MulAut.congr e).symm ((MulAut.congr e) a) ∈ A
    rw [MulEquiv.symm_apply_apply]
    exact ha
  · refine (RowXUn.isGood_iff_map_mulEquiv e _).2 ?_
    rw [hmm]
    exact hF'good

theorem isElemAbelian_top_frame :
    IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 3))) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩, fun x _ => ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  have h3 : ∀ y : ZMod 3, 3 • y = 0 := by decide
  simp [h3]

end X1F4

open CFSG.StandardType.TableBF4TwoTB (tE tE_injective)

section Frame


@[expose] def X1F4FrameConj : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ E : Subgroup (adjointGroup .F4 K), IsElemAbelian 3 E → Nat.card E = 3 ^ 4 →
      ∃ c : adjointGroup .F4 K, E = (tE K).range.map (MulAut.conj c).toMonoidHom

@[expose] def X1F4FrameGood : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∃ F : Subgroup (adjointGroup .F4 K), F ≤ (tE K).range ∧ 9 ≤ Nat.card F ∧
      IsGood 3 (F.map (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)))

namespace X1F4

variable {K : Type} [Field K] [CharP K 2]

theorem isElemAbelian_range_tE : IsElemAbelian 3 (tE K).range := by
  rw [MonoidHom.range_eq_map]
  exact CFSG.SectionRank.isElemAbelian_map isElemAbelian_top_frame (tE K)

theorem card_range_tE : Nat.card (tE K).range = 3 ^ 4 := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective tE_injective, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp [Nat.card_zmod]

end X1F4

end Frame

section Reduction


namespace X1F4

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem conj_injective :
    Function.Injective (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hz : g ∈ Subgroup.center (adjointGroup .F4 K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg (fun f : MulAut (adjointGroup .F4 K) => f x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot] at hz
  exact Subgroup.mem_bot.1 hz

theorem model (hK : Nat.card K = 2) (hC : X1F4FrameConj) (hG : X1F4FrameGood)
    (A' : Subgroup (MulAut (adjointGroup .F4 K))) (hA' : IsElemAbelian 3 A')
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup .F4 K)) ≤ CFSG.Open.pRank 3 A') :
    ∃ F' ≤ A', IsElemAbelian 3 F' ∧ 9 ≤ Nat.card F' ∧ IsGood 3 F' := by
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup .F4 K)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top isElemAbelian_range_tE card_range_tE
  have hcardA' : 3 ^ 4 ≤ Nat.card A' := by
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hA']
    exact Nat.pow_le_pow_right (by norm_num) (h4.trans hrk)
  have hle : A' ≤ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
    intro α hα
    obtain ⟨x, hx⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.CatB.I2610.exists_eq_conj_of_pow_three_F4 hK (hA'.2 α hα)
    exact ⟨x, hx.symm⟩
  set Ahat : Subgroup (adjointGroup .F4 K) := A'.comap MulAut.conj
  have hmap : Ahat.map MulAut.conj = A' := Subgroup.map_comap_eq_self hle
  have hAhatel : IsElemAbelian 3 Ahat := isElemAbelian_comap conj_injective hA'
  have hAhatcard : Nat.card A' = Nat.card Ahat := by
    have := Subgroup.card_map_of_injective (K := Ahat) conj_injective
    rwa [hmap] at this
  have hAhat81 : Nat.card Ahat = 3 ^ 4 :=
    le_antisymm (CFSG.StandardType.TableBF4Two.card_le_adjointF4 hK hAhatel)
      (hAhatcard ▸ hcardA')
  obtain ⟨c, hc⟩ := hC K hK Ahat hAhatel hAhat81
  obtain ⟨F, hFT, hF9, hFgood⟩ := hG K hK
  have hFle : (F.map (MulAut.conj c).toMonoidHom).map
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) ≤ A' := by
    rw [← hmap]
    refine Subgroup.map_mono ?_
    rw [hc]
    exact Subgroup.map_mono hFT
  have hFeq : (F.map
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K))).map
        (MulAut.congr (MulAut.conj c)).toMonoidHom =
      (F.map (MulAut.conj c).toMonoidHom).map
        (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) := by
    have hhom : (MulAut.congr (MulAut.conj c)).toMonoidHom.comp
        (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) =
        (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).comp
          (MulAut.conj c).toMonoidHom :=
      MonoidHom.ext fun g => congr_conj_conj c g
    rw [Subgroup.map_map, Subgroup.map_map, hhom]
  refine ⟨(F.map (MulAut.conj c).toMonoidHom).map MulAut.conj, hFle,
    isElemAbelian_of_le hA' hFle, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective conj_injective,
      Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hF9
  · rw [← hFeq]
    exact (RowXUn.isGood_iff_map_mulEquiv (MulAut.conj c) _).1 hFgood

end X1F4

theorem kd264X1ExcF4_of_frame (hC : X1F4FrameConj) (hG : X1F4FrameGood) : KD264X1ExcF4 := by
  intro d q hd _
  intro _ _ _ hov _ _
  have hq : q.card = 2 := by simpa [ov2Idx, fieldSize, hd] using hov
  have hcat : CFSG.Yardstones.Md0ec50421ce4.catalogIs (TauCeti.CFSGIndex.lie d).Group
      CFSG.LocalAnalysis.GLTheoremA.S9.isF4two :=
    ⟨.lie d, by
      simp only [CFSG.LocalAnalysis.GLTheoremA.S9.isF4two, CFSG.Yardstones.Md0ec50421ce4.onLie, hd]
      exact hq, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.I2610.exists_adjointGroup_of_catalogIs_isF4two hcat
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (le_refl 1) (by rw [pow_one]; exact hK)
  intro A hA hrk
  exact X1F4.concl_of_equiv e (fun A' hA' hrk' => X1F4.model hK hC hG A' hA' hrk') A hA hrk

end Reduction

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
