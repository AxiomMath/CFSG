module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalInSitu
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalNoE27
public import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalTransport

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.PreuniquenessRankFour.Helpers
open scoped commutatorElement

section Action

variable {Y : Type} [Group Y] {X : Type} [Group X]

@[expose] noncomputable def actHom (Kn : Subgroup Y) [Kn.Normal] (e : Kn ≃* X) :
    Y →* MulAut X :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem actHom_apply (Kn : Subgroup Y) [Kn.Normal] (e : Kn ≃* X) (y : Y) (x : X) :
    ((e.symm (actHom Kn e y x) : Kn) : Y) = y * (e.symm x : Y) * y⁻¹ := by
  have h : e.symm (actHom Kn e y x) = MulAut.conjNormal y (e.symm x) := by
    show e.symm (e (MulAut.conjNormal y (e.symm x))) = _
    exact e.symm_apply_apply _
  rw [h, MulAut.conjNormal_apply]

theorem actHom_injective (Kn : Subgroup Y) [Kn.Normal] (e : Kn ≃* X)
    (hC : Subgroup.centralizer (Kn : Set Y) = ⊥) : Function.Injective (actHom Kn e) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have : y ∈ Subgroup.centralizer (Kn : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h := actHom_apply Kn e y (e ⟨k, hk⟩)
    simp only [hy, MulAut.one_apply, MulEquiv.symm_apply_apply] at h
    have h' : y * k * y⁻¹ = k := h.symm
    calc k * y = (y * k * y⁻¹) * y := by rw [h']
      _ = y * k := by group
  rw [hC] at this
  exact this

theorem actHom_inner (Kn : Subgroup Y) [Kn.Normal] (e : Kn ≃* X) (g : X) :
    actHom Kn e (e.symm g : Y) = MulAut.conj g := by
  ext x
  apply e.symm.injective
  apply Subtype.ext
  rw [actHom_apply]
  simp [MulAut.conj_apply]

end Action

section Reduction


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem kfact_main (hK : Nat.card K = 8) (hSU : SUStruct M)
    {Y : Type} [Group Y] [Finite Y] (Kn : Subgroup Y) [Kn.Normal]
    (e : Kn ≃* adjointGroup .G2 K) (hC : Subgroup.centralizer (Kn : Set Y) = ⊥)
    (T : Sylow 3 Y) (Y₀ : Subgroup Y) (h3 : 3 ≤ Open.pRank 3 (T : Subgroup Y))
    (hweak : GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀) (hne : Y₀ ≠ ⊤) :
    ∃ (zb : Y) (V₀ : Subgroup Y), G28InSitu (T : Subgroup Y) Y₀ zb V₀ := by
  set c := actHom Kn e with hcdef
  have hinj : Function.Injective c := actHom_injective Kn e hC
  let cI : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K) := MulAut.conj
  have hcI : Function.Injective cI := conj_injective_X
  have hInn : cI.range ≤ c.range := by
    rintro _ ⟨g, rfl⟩
    exact ⟨(e.symm g : Y), actHom_inner Kn e g⟩
  have hcases : c.range = cI.range ∨ c.range = ⊤ := by
    have h1 : Nat.card cI.range = Nat.card (adjointGroup .G2 K) :=
      Nat.card_range_of_injective hcI
    have h2 : Nat.card cI.range ∣ Nat.card c.range := Subgroup.card_dvd_of_le hInn
    have h3' : Nat.card c.range ∣ Nat.card (MulAut (adjointGroup .G2 K)) :=
      Subgroup.card_subgroup_dvd_card _
    rw [card_aut hK] at h3'
    obtain ⟨m, hm⟩ := h2
    rw [h1] at hm
    have hpos : 0 < Nat.card (adjointGroup .G2 K) := Nat.card_pos
    rw [hm, mul_comm 3] at h3'
    have hm3 : m ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hpos h3'
    have hm' : m = 1 ∨ m = 3 := (Nat.dvd_prime Nat.prime_three).mp hm3
    rcases hm' with rfl | rfl
    · left
      refine (Subgroup.eq_of_le_of_card_ge hInn ?_).symm
      rw [h1, hm, mul_one]
    · right
      apply Subgroup.eq_top_of_card_eq
      rw [hm, card_aut hK, mul_comm]
  rcases hcases with hr | hr
  ·
    exfalso
    obtain ⟨E, hET, hEe, hE27⟩ := exists_elemAbelian_27 h3
    have hEc : E.map c ≤ cI.range := hr ▸ Subgroup.map_le_range c E
    have hmap : ((E.map c).comap cI).map cI = E.map c := Subgroup.map_comap_eq_self hEc
    have hcard : Nat.card ((E.map c).comap cI) = 27 := by
      rw [← Subgroup.card_map_of_injective hcI, hmap, Subgroup.card_map_of_injective hinj, hE27]
    exact no_elemAbelian_27_X M hK
      (isElemAbelian_comap_injective cI hcI
        (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 c E hEe)) hcard
  ·
    have hsurj : Function.Surjective c := MonoidHom.range_eq_top.mp hr
    let Ψ₀ : Y ≃* MulAut (adjointGroup .G2 K) := MulEquiv.ofBijective c ⟨hinj, hsurj⟩
    have hs : Function.Surjective Ψ₀.toMonoidHom := fun x => Ψ₀.surjective x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut (adjointGroup .G2 K))
      (Sylow.mapSurjective hs T) (T0Sylow M hK)
    let Ψ : Y ≃* MulAut (adjointGroup .G2 K) := Ψ₀.trans (MulAut.conj g)
    have hT : (T : Subgroup Y).map Ψ.toMonoidHom = T0 M hK := by
      have h1 := congrArg (fun P : Sylow 3 (MulAut (adjointGroup .G2 K)) =>
        (P : Subgroup (MulAut (adjointGroup .G2 K)))) hg
      simp only [Sylow.coe_subgroup_smul, coe_T0Sylow, Sylow.coe_mapSurjective] at h1
      rw [← h1]
      show Subgroup.map Ψ.toMonoidHom (T : Subgroup Y) =
        Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.map Ψ₀.toMonoidHom (T : Subgroup Y))
      rw [Subgroup.map_map]
      rfl
    have hmapsymm : ∀ A : Subgroup (MulAut (adjointGroup .G2 K)),
        (A.map Ψ.symm.toMonoidHom).map Ψ.toMonoidHom = A := fun A => by
      rw [Subgroup.map_map]
      ext x
      simp
    have hmap : ∀ A : Subgroup Y, (A.map Ψ.toMonoidHom).map Ψ.symm.toMonoidHom = A := fun A => by
      rw [Subgroup.map_map]
      ext x
      simp
    have hcore : GLBWeakCore 3 (T0 M hK) ≤ Y₀.map Ψ.toMonoidHom := by
      have h1 := map_glbWeakCore_le Nat.prime_three Ψ.symm.toMonoidHom Ψ.symm.injective
        (T0 M hK)
      rw [show (T0 M hK).map Ψ.symm.toMonoidHom = (T : Subgroup Y) by rw [← hT, hmap]] at h1
      have h2 := Subgroup.map_mono (f := Ψ.toMonoidHom) (h1.trans hweak)
      rwa [hmapsymm] at h2
    have hne' : Y₀.map Ψ.toMonoidHom ≠ ⊤ := by
      intro h
      apply hne
      have := congrArg (Subgroup.map Ψ.symm.toMonoidHom) h
      rwa [hmap, Subgroup.map_top_of_surjective _ Ψ.symm.surjective] at this
    have key := g28InSitu_aut M hK hSU hcore hne'
    refine ⟨Ψ.symm (zb M), (V0 M).map Ψ.symm.toMonoidHom, G28InSitu.of_mulEquiv Ψ ?_⟩
    have hz : Ψ.toMonoidHom (Ψ.symm (zb M)) = zb M := Ψ.apply_symm_apply _
    rw [hT, hmapsymm, hz]
    exact key

end Reduction

end CFSG.AGLEmbedding.KFactProofs.G28
