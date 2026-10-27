module

import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35CentralSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Inner
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma102
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Split

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)

variable {X : Type} [Group X] [Finite X]

section Aut

variable {K S : Subgroup X}

theorem normalizerMonoidHom_of_mem {k : X} (hk : k ∈ K)
    (hkN : k ∈ Subgroup.normalizer (K : Set X)) :
    K.normalizerMonoidHom ⟨k, hkN⟩ = MulAut.conj ⟨k, hk⟩ :=
  MulEquiv.ext fun z => Subtype.ext (by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
    rfl)

theorem isPGroup_autIm (hS : IsPGroup 2 S) : IsPGroup 2 (autIm S K) :=
  (hS.comap_subtype (K := Subgroup.normalizer (K : Set X))).map _

theorem mem_normalizer_autIm {g : X} (hgK : g ∈ Subgroup.normalizer (K : Set X))
    (hgS : g ∈ Subgroup.normalizer (S : Set X)) :
    K.normalizerMonoidHom ⟨g, hgK⟩ ∈
      Subgroup.normalizer ((autIm S K : Subgroup (MulAut ↥K)) : Set (MulAut ↥K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro f
  constructor
  · rintro ⟨x, hxS, rfl⟩
    refine ⟨⟨g, hgK⟩ * x * ⟨g, hgK⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp hgS x).mp (Subgroup.mem_subgroupOf.mp hxS)
  · rintro ⟨y, hyS, hy⟩
    refine ⟨⟨g, hgK⟩⁻¹ * y * ⟨g, hgK⟩, ?_, ?_⟩
    · have hgS' : g⁻¹ ∈ Subgroup.normalizer (S : Set X) := inv_mem hgS
      have h := (Subgroup.mem_normalizer_iff.mp hgS' y).mp (Subgroup.mem_subgroupOf.mp hyS)
      simpa [Subgroup.mem_subgroupOf] using h
    · rw [map_mul, map_mul, map_inv, hy]
      group

theorem le_centralizer_of_autIm_eq_bot (hSN : S ≤ Subgroup.normalizer (K : Set X))
    (h : autIm S K = ⊥) : S ≤ Subgroup.centralizer (K : Set X) := by
  intro s hs
  have hmem : K.normalizerMonoidHom ⟨s, hSN hs⟩ ∈ autIm S K :=
    ⟨⟨s, hSN hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  rw [h, Subgroup.mem_bot, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

end Aut

namespace K37Setting

variable {K E S : Subgroup X}

theorem le_normalizer_K (h : K37Setting X K E S) : E ≤ Subgroup.normalizer (K : Set X) := by
  haveI := h.normal
  rw [Subgroup.normalizer_eq_top]
  exact le_top

theorem S_le_normalizer_K (h : K37Setting X K E S) : S ≤ Subgroup.normalizer (K : Set X) := by
  haveI := h.normal
  rw [Subgroup.normalizer_eq_top]
  exact le_top

theorem centralizer_le (h : K37Setting X K E S) {e : X} (he : e ∈ E) (he1 : e ≠ 1) :
    Subgroup.centralizer {e} ≤ rankThreeGamma 1 3 E :=
  CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35.centralizer_le_gamma h.elem he he1

theorem exists_ne_one (h : K37Setting X K E S) : ∃ e ∈ E, e ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
  have h9 := h.card
  rw [hbot, Subgroup.card_bot] at h9
  omega

theorem le_gamma (h : K37Setting X K E S) : E ≤ rankThreeGamma 1 3 E := by
  obtain ⟨e, he, he1⟩ := h.exists_ne_one
  refine le_trans ?_ (h.centralizer_le he he1)
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (h.elem.1.is_comm.comm (⟨x, hx⟩ : ↥E) ⟨e, he⟩)

theorem le_normalizer_S (h : K37Setting X K E S) : E ≤ Subgroup.normalizer (S : Set X) :=
  h.le_gamma.trans h.le_normalizer

theorem inf_centralizer_eq_bot (h : K37Setting X K E S) :
    E ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
  by_contra hne
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have he1' : e ≠ 1 := fun h1 => he1 (Subtype.ext h1)
  apply h.not_le
  refine le_trans ?_ (h.centralizer_le he.1 he1')
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp he.2 k hk

theorem card_autIm (h : K37Setting X K E S) : Nat.card (autIm E K) = 3 ^ 2 := by
  rw [CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.card_autIm h.le_normalizer_K
    h.inf_centralizer_eq_bot, h.card]
  norm_num

theorem isElemAbelian_autIm (h : K37Setting X K E S) : IsElemAbelian 3 (autIm E K) :=
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.isElemAbelian_autIm h.elem K

theorem seitzHyperGamma_ne_top (h : K37Setting X K E S) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 (autIm E K) ≠ ⊤ := fun htop =>
  h.not_le ((CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.le_centGenI_of_autIm
    h.le_normalizer_K h.inf_centralizer_eq_bot htop).trans
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central.centGenI_le_rankThreeGamma h.elem
        h.card K))

theorem isPGroup_center (h : K37Setting X K E S) : IsPGroup 3 (Subgroup.center ↥K) :=
  CFSG.LocalAnalysis.GLTheoremA.S10.lemma102_isPGroup_of_central Nat.prime_three h.core _ le_rfl

theorem conj_mem_normalizer_autIm (h : K37Setting X K E S) {k : X} (hk : k ∈ K)
    (hkΓ : k ∈ rankThreeGamma 1 3 E) :
    MulAut.conj (⟨k, hk⟩ : ↥K) ∈
      Subgroup.normalizer ((autIm S K : Subgroup (MulAut ↥K)) : Set (MulAut ↥K)) := by
  have hkN : k ∈ Subgroup.normalizer (K : Set X) := by
    haveI := h.normal
    rw [Subgroup.normalizer_eq_top]
    trivial
  rw [← normalizerMonoidHom_of_mem hk hkN]
  exact mem_normalizer_autIm hkN (h.le_normalizer hkΓ)

theorem mem_gamma_of_inner (h : K37Setting X K E S) {e k : X} (he : e ∈ E) (he1 : e ≠ 1)
    (hek : ∀ y ∈ K, e * y * e⁻¹ = k * y * k⁻¹) {y : X} (hy : y ∈ K) (hyk : y * k = k * y) :
    y ∈ rankThreeGamma 1 3 E := by
  refine h.centralizer_le he he1 (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  have h1 := hek y hy
  rw [← hyk, mul_inv_cancel_right] at h1
  calc y * e = e * y * e⁻¹ * e := by rw [h1]
    _ = e * y := by group

theorem exists_comm_not_mem (h : K37Setting X K E S)
    (hSC : ¬ S ≤ Subgroup.centralizer (K : Set X)) :
    ∃ e ∈ E, e ≠ 1 ∧ ∃ s ∈ S, s * e = e * s ∧ s ∉ Subgroup.centralizer (K : Set X) := by
  have hpow : ∀ m : ↥E, m ^ 3 = 1 := fun m => Subtype.ext (by
    rw [Subgroup.coe_pow, h.elem.2 m m.2, Subgroup.coe_one])
  have hcard : Nat.card E = 3 ^ 2 := by rw [h.card]; norm_num
  have h3 : ¬ 3 ∣ Nat.card S := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := h.two.exists_card_eq
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three E S hpow hcard h3 h.le_normalizer_S
  by_contra hcon
  push Not at hcon
  apply hSC
  rw [hgen]
  refine iSup_le fun m => iSup_le fun hm => ?_
  intro s hs
  have hm1 : (m : X) ≠ 1 := fun h1 => hm (Subtype.ext h1)
  exact hcon m m.2 hm1 s hs.1 (Subgroup.mem_centralizer_singleton_iff.mp hs.2)

end K37Setting

end CFSG.LocalAnalysis.RankThreeUC.S15.K37
