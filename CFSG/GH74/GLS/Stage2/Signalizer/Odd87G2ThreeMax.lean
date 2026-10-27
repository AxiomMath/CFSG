module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeRep
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Cls
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import Certificates.Certificate5182
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvCent
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ResG2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert CFSG.LieType.AlgebraicGroups
  Certificates.G2ThreeMax CFSG.GH74.GLS.IVK.Proofs2

section Transport

theorem isCoatom_map_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {H : Subgroup A}
    (h : IsCoatom H) : IsCoatom (H.map e.toMonoidHom) := by
  refine ⟨?_, fun K hK => ?_⟩
  · intro htop
    apply h.1
    have : H = (H.map e.toMonoidHom).comap e.toMonoidHom :=
      (Subgroup.comap_map_eq_self_of_injective e.injective H).symm
    rw [this, htop]
    exact Subgroup.comap_top _
  · have hle : H ≤ K.comap e.toMonoidHom := by
      rw [← Subgroup.map_le_iff_le_comap]
      exact hK.le
    have hlt : H < K.comap e.toMonoidHom := by
      refine lt_of_le_of_ne hle fun heq => ?_
      have : K = H.map e.toMonoidHom := by
        rw [heq, Subgroup.map_comap_eq_self_of_surjective e.surjective]
      exact hK.ne this.symm
    have htop := h.2 _ hlt
    have : K = (K.comap e.toMonoidHom).map e.toMonoidHom :=
      (Subgroup.map_comap_eq_self_of_surjective e.surjective K).symm
    rw [this, htop]
    exact Subgroup.map_top_of_surjective _ e.surjective

theorem isCoatom_of_map_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {H : Subgroup A}
    (h : IsCoatom (H.map e.toMonoidHom)) : IsCoatom H := by
  have h' := isCoatom_map_equiv e.symm h
  have : (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
    ext x
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  rwa [this] at h'

theorem fixSub_congr {Y Y' : Type} [Group Y] [Group Y'] (Ψ : Y ≃* Y') (α : MulAut Y) :
    fixSub (MulAut.congr Ψ α) = (fixSub α).map Ψ.toMonoidHom := by
  ext y'
  rw [Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨Ψ.symm y', ?_, by simp⟩
    rw [mem_fixSub] at h ⊢
    have h1 : Ψ (α (Ψ.symm y')) = y' := h
    have h2 : α (Ψ.symm y') = Ψ.symm y' := by
      apply Ψ.injective
      rw [h1]
      simp
    exact h2
  · rintro ⟨y, hy, rfl⟩
    rw [mem_fixSub] at hy ⊢
    show Ψ (α (Ψ.symm (Ψ y))) = Ψ y
    simp [hy]

end Transport

section Words

theorem ρG_wordElem (w : List ℕ)
    (hw : ∀ k ∈ w, k < 8) :
    ((ρG (wordElem gensG w) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
      M (wordArr w) := by
  induction w with
  | nil =>
    rw [wordArr_nil, M_idArr]
    simp [wordElem]
  | cons k w ih =>
    have hk : k < 8 := hw k (by simp)
    have hwe : wordElem gensG (k :: w) = gensG k * wordElem gensG w := by simp [wordElem]
    rw [hwe, map_mul, Units.val_mul, hρ_gens k hk, ih (fun x hx => hw x (by simp [hx])),
      wordArr_cons, M_mmul]

end Words

theorem innerInput_base_lt : ∀ k ∈ Certificates.G2ThreeMax.innerInput.base, k < 8 := by
  intro k hk
  simp only [Certificates.G2ThreeMax.innerInput] at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  omega

section Core


theorem g3_z_coatom :
    IsCoatom (centralizer ({wordElem gensG Certificates.G2ThreeMax.innerInput.base} : Set G3)) := by
  have hψ : ∀ k < 8, (MonoidHom.id G3) (gensG k) =
      gensG Certificates.G2ThreeMax.innerInput.sigma[k]! := by
    intro k hk
    interval_cases k <;> rfl
  have hcoatom := Certificates.certificate5182.1 ρG (MonoidHom.id G3) gensG closure_gensG
    hρ_gens hinv_gens Certificates.G2ThreeMax.innerInput List.mem_cons_self hψ
  have hz := ρG_wordElem Certificates.G2ThreeMax.innerInput.base innerInput_base_lt
  rw [← hz, stabilizer_id_eq_centralizer ρG ρG_injective] at hcoatom
  exact hcoatom

theorem g3_z_sq :
    wordElem gensG Certificates.G2ThreeMax.innerInput.base *
      wordElem gensG Certificates.G2ThreeMax.innerInput.base = 1 := by
  have hsq := Certificates.certificate5182.2
  apply ρG_injective
  apply Units.ext
  rw [map_mul, Units.val_mul, ρG_wordElem _ innerInput_base_lt, hsq, map_one, Units.val_one]

theorem g3_z_ne_one :
    wordElem gensG Certificates.G2ThreeMax.innerInput.base ≠ 1 := by
  intro h
  apply g3_z_coatom.1
  rw [h]
  refine eq_top_iff.2 fun x _ => ?_
  simp [Subgroup.mem_centralizer_singleton_iff]

end Core

section Exceptional


theorem finiteReeAut_xElement [CharP (ZMod 3) ReeTag.G2.prime] (i : Fin Tag.G2.rank) (c : ZMod 3) :
    (ReeTag.G2.finiteReeAut (ZMod 3) 0 : MulAut G3) (xElement i c) =
      xElement (ReeTag.G2.perm i) (c ^ ReeTag.G2.exponent i) := by
  have h : ReeTag.G2.finiteReeAut (ZMod 3) 0 = ReeTag.G2.finiteExceptionalAut (ZMod 3) := by
    simp [ReeTag.finiteReeAut]
  rw [h]
  exact ReeTag.finiteExceptionalAut_xElement (t := ReeTag.G2) (K := ZMod 3) i c

theorem finiteReeAut_yElement [CharP (ZMod 3) ReeTag.G2.prime] (i : Fin Tag.G2.rank) (c : ZMod 3) :
    (ReeTag.G2.finiteReeAut (ZMod 3) 0 : MulAut G3) (yElement i c) =
      yElement (ReeTag.G2.perm i) (c ^ ReeTag.G2.exponent i) := by
  have h : ReeTag.G2.finiteReeAut (ZMod 3) 0 = ReeTag.G2.finiteExceptionalAut (ZMod 3) := by
    simp [ReeTag.finiteReeAut]
  rw [h]
  exact ReeTag.finiteExceptionalAut_yElement (t := ReeTag.G2) (K := ZMod 3) i c

theorem pow_exponent (i : Fin Tag.G2.rank) (c : ZMod 3) : c ^ ReeTag.G2.exponent i = c := by
  rcases fin_rank_cases i with rfl | rfl <;> revert c <;> decide

theorem finiteReeAut_gens [CharP (ZMod 3) ReeTag.G2.prime] : ∀ k < 8,
    (ReeTag.G2.finiteReeAut (ZMod 3) 0 : MulAut G3).toMonoidHom (gensG k) =
      gensG Certificates.G2ThreeMax.outerInput.sigma[k]! := by
  intro k hk
  interval_cases k
  · exact (finiteReeAut_xElement i0 _).trans (by rw [pow_exponent]; rfl)
  · exact (finiteReeAut_xElement i0 _).trans (by rw [pow_exponent]; rfl)
  · exact (finiteReeAut_xElement i1 _).trans (by rw [pow_exponent]; rfl)
  · exact (finiteReeAut_xElement i1 _).trans (by rw [pow_exponent]; rfl)
  · exact (finiteReeAut_yElement i0 _).trans (by rw [pow_exponent]; rfl)
  · exact (finiteReeAut_yElement i0 _).trans (by rw [pow_exponent]; rfl)
  · exact (finiteReeAut_yElement i1 _).trans (by rw [pow_exponent]; rfl)
  · exact (finiteReeAut_yElement i1 _).trans (by rw [pow_exponent]; rfl)

theorem g3_outer_coatom [CharP (ZMod 3) ReeTag.G2.prime] :
    IsCoatom (fixSub (ReeTag.G2.finiteReeAut (ZMod 3) 0 : MulAut G3)) := by
  have hcoatom := Certificates.certificate5182.1 ρG
    (ReeTag.G2.finiteReeAut (ZMod 3) 0 : MulAut G3).toMonoidHom gensG closure_gensG hρ_gens
    hinv_gens Certificates.G2ThreeMax.outerInput (List.mem_cons_of_mem _ List.mem_cons_self)
    finiteReeAut_gens
  have hx : (⟨M (wordArr Certificates.G2ThreeMax.outerInput.base)⟩ :
      TwPt ρG (ReeTag.G2.finiteReeAut (ZMod 3) 0 : MulAut G3).toMonoidHom) = ⟨1⟩ := by
    apply TwPt.ext
    show M (wordArr Certificates.G2ThreeMax.outerInput.base) = 1
    have hb : Certificates.G2ThreeMax.outerInput.base = [] := rfl
    rw [hb, wordArr_nil, M_idArr]
  have hstab := stabilizer_one_eq_eqLocus ρG ρG_injective
    (ReeTag.G2.finiteReeAut (ZMod 3) 0 : MulAut G3).toMonoidHom
  rw [hx, hstab] at hcoatom
  exact hcoatom

end Exceptional

section Certs


theorem g3_inner_coatom (g : G3) (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    IsCoatom (centralizer ({g} : Set G3)) := by
  have hzo : orderOf (wordElem gensG Certificates.G2ThreeMax.innerInput.base) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact g3_z_sq) g3_z_ne_one
  have hgo : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  have hchar : ringChar (ZMod 3) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    norm_num
  obtain ⟨c, hc⟩ := isConj_iff.1
    (CFSG.LieType.HighestRoot.g2_involutions_isConj hchar _ g hzo hgo)
  have hmap := CFSG.GH74.GLS.IVK.GHInv.map_centralizer_singleton' (MulAut.conj c)
    (wordElem gensG Certificates.G2ThreeMax.innerInput.base)
  have hcg : (MulAut.conj c) (wordElem gensG Certificates.G2ThreeMax.innerInput.base) = g := by
    rw [MulAut.conj_apply]
    exact hc
  rw [hcg] at hmap
  rw [← hmap]
  exact isCoatom_map_equiv (MulAut.conj c) g3_z_coatom

theorem g3_fixSub_coatom (α : MulAut G3) (hα2 : α * α = 1)
    (hα1 : α ≠ 1) : IsCoatom (fixSub α) := by
  have : CharP (ZMod 3) ReeTag.G2.prime := ZMod.charP 3
  have hZ : Subgroup.center G3 = ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  by_cases hin : α ∈ (MulAut.conj : G3 →* MulAut G3).range
  · obtain ⟨g, rfl⟩ := hin
    have hgg : g * g = 1 := by
      have hmem : g * g ∈ Subgroup.center G3 := by
        rw [Subgroup.mem_center_iff]
        intro y
        have h1 := congrArg (fun σ : MulAut G3 => σ y) hα2
        simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h1
        calc y * (g * g) = (g * (g * y * g⁻¹) * g⁻¹) * (g * g) := by rw [h1]
          _ = (g * g) * y := by group
      rw [hZ] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hg1 : g ≠ 1 := fun h1 => hα1 (by rw [h1, map_one])
    rw [fixSub_conj]
    exact g3_inner_coatom g hgg hg1
  · have hα'2 : α ^ 2 = 1 := by rw [sq]; exact hα2
    have hK : Nat.card (ZMod 3) = 3 ^ 1 := by simp
    rcases CFSG.LieType.AlgebraicGroups.G2_three_involution_inner_quadratic_or_exceptional
        (K := ZMod 3) (f := 1) le_rfl hK hα'2 with
      ⟨g, a, hαg⟩ | ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, hαeq⟩
    · exact absurd (ivk93res_inner_of_diag hαg) hin
    · exfalso
      have h3 : 3 ≤ 3 ^ e := Nat.le_self_pow (by omega) 3
      have h9 : 3 * 3 ≤ 3 ^ e * 3 ^ e := Nat.mul_le_mul h3 h3
      have hc : Nat.card (ZMod 3) = 3 := by simp
      rw [hKe, sq] at hc
      omega
    · have hb : b = 0 := by omega
      subst hb
      have hα'' : (MulAut.conj g * ReeTag.G2.finiteReeAut (ZMod 3) 0) ^ 2 = 1 := by
        rw [← hαeq]; exact hα'2
      obtain ⟨⟨ψ, hψ⟩, -, -⟩ := CFSG.LieType.Ree.G2_exceptional_coset_involution_fixed_p_components
        0 (ZMod 3) (by simp) g hα''
      rw [← hαeq] at hψ
      obtain ⟨hfix, -⟩ := CFSG.LieType.Chevalley.fixed_centralizer_of_conj_eq hψ
      refine isCoatom_of_map_equiv ψ ?_
      have hfix' : (fixSub α).map ψ.toMonoidHom =
          fixSub (ReeTag.G2.finiteReeAut (ZMod 3) 0 : MulAut G3) := hfix
      rw [hfix']
      exact g3_outer_coatom

theorem g2ThreeMax_of_cert : G2ThreeMax := by
  intro Y _ _ hm α hα2 hα1
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hm
  have hF3 : Nat.card F = 3 := by simpa using hcard
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card]
    exact hF3
  let r : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hFc
  let Ψ : Y ≃* G3 := e.trans (CFSG.TauCetiBridge.adjointGroupCongr r)
  have hα'2 : MulAut.congr Ψ α * MulAut.congr Ψ α = 1 := by rw [← map_mul, hα2, map_one]
  have hα'1 : MulAut.congr Ψ α ≠ 1 := fun h =>
    hα1 ((MulAut.congr Ψ).injective (by rw [h, map_one]))
  have key := g3_fixSub_coatom (MulAut.congr Ψ α) hα'2 hα'1
  rw [fixSub_congr] at key
  exact isCoatom_of_map_equiv Ψ key

end Certs

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
