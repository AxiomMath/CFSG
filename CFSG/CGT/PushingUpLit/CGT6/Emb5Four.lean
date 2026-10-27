module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Basic
public import CFSG.CGT.PushingUpLit.CGT6.Emb5Odd
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem commV_map_conj (Y : Subgroup (MulAut V)) (g : MulAut V) :
    commV (Y.map (MulAut.conj g).toMonoidHom) = (commV Y).map g.toMonoidHom :=
  CFSG.Quasithin.commV_map_conj_eq Y g

theorem card_mulAut_dvd_of_card_le_sixteen {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W ≤ 16) : Nat.card (MulAut W) ∣ 20160 := by
  have hW2 : IsPGroup 2 W := fun w => ⟨1, by simpa using hW w⟩
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hn4 : n ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm a b) (fun a => hW a) hn
  have hGL : Nat.card (MulAut W) = Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :=
    Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toEquiv
  rw [hGL, Matrix.card_GL_field]
  interval_cases n <;> simp [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]

variable [Finite V]

theorem card_commV_sup_conj_le {Y : Subgroup (MulAut V)} (hU4 : Nat.card ↥(commV Y) = 4)
    (g : MulAut V) : Nat.card ↥(commV (Y ⊔ Y.map (MulAut.conj g).toMonoidHom)) ≤ 16 := by
  set Y' : Subgroup (MulAut V) := Y.map (MulAut.conj g).toMonoidHom with hY'
  have hU'4 : Nat.card ↥(commV Y') = 4 := by
    rw [hY', commV_map_conj, Subgroup.card_map_of_injective (MulEquiv.injective g)]
    exact hU4
  have h1 : Nat.card ↥(commV (Y ⊔ Y')) ≤ Nat.card ↥(commV Y ⊔ commV Y') :=
    Subgroup.card_le_of_le (commV_sup_le Y Y')
  have h2 := card_sup_le_mul (commV Y) (commV Y')
  rw [hU4, hU'4] at h2
  omega

theorem card_sup_conj_dvd (hV : ∀ v : V, v ^ 2 = 1) {Y X : Subgroup (MulAut V)} (hYX : Y ≤ X)
    (hodd : Odd (Nat.card ↥X)) (hU4 : Nat.card ↥(commV Y) = 4) {g : MulAut V} (hgX : g ∈ X) :
    Nat.card ↥(Y ⊔ Y.map (MulAut.conj g).toMonoidHom) ∣ 315 := by
  set Y' : Subgroup (MulAut V) := Y.map (MulAut.conj g).toMonoidHom with hY'
  set H : Subgroup (MulAut V) := Y ⊔ Y' with hH
  have hY'X : Y' ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    show g * y * g⁻¹ ∈ X
    exact X.mul_mem (X.mul_mem hgX (hYX hy)) (X.inv_mem hgX)
  have hHX : H ≤ X := sup_le hYX hY'X
  have hHodd : ∀ x ∈ H, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard X (hHX hx))
  have hU16 : Nat.card ↥(commV H) ≤ 16 := card_commV_sup_conj_le hU4 g
  have hinj := injective_resHom hV hHodd
  have hWelem : ∀ w : ↥(commV H), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have hdvdAut : Nat.card (MulAut ↥(commV H)) ∣ 20160 :=
    card_mulAut_dvd_of_card_le_sixteen hWelem hU16
  have hHdvd : Nat.card ↥H ∣ Nat.card (MulAut ↥(commV H)) := by
    have h1 : Nat.card ↥H = Nat.card ↥(resHom H).range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [h1]
    exact Subgroup.card_subgroup_dvd_card _
  have hd : Nat.card ↥H ∣ 64 * 315 := by
    have := hHdvd.trans hdvdAut
    simpa using this
  have hHoddCard : Odd (Nat.card ↥H) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hHX)
  have hcop : Nat.Coprime (Nat.card ↥H) 64 := by
    have h2 : Nat.Coprime (Nat.card ↥H) 2 := Nat.coprime_two_right.mpr hHoddCard
    simpa using Nat.Coprime.pow_right 6 h2
  exact hcop.dvd_of_dvd_mul_left hd

theorem exists_normal_seven_of_odd (hV : ∀ v : V, v ^ 2 = 1) {Y X : Subgroup (MulAut V)}
    (hYX : Y ≤ X) (hodd : Odd (Nat.card ↥X)) (hY3 : Nat.card ↥Y = 3)
    (hU4 : Nat.card ↥(commV Y) = 4)
    (hgen : ∀ N : Subgroup (MulAut V), N ≤ X → Y ≤ N →
      X ≤ Subgroup.normalizer (N : Set (MulAut V)) → N = X) :
    ∃ R : Subgroup (MulAut V), R ≤ X ∧ X ≤ Subgroup.normalizer (R : Set (MulAut V)) ∧
      IsPGroup 7 ↥R ∧ Y ⊔ R = X := by
  classical
  set Yt : Subgroup ↥X := Y.subgroupOf X with hYt0
  have hYt : Yt.map X.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYX
  have hdata : SevenData ↥X Yt := by
    refine ⟨?_, ?_, ?_⟩
    · have := Subgroup.card_map_of_injective X.subtype_injective (K := Yt)
      rw [hYt, hY3] at this
      exact this.symm
    · intro N' hN' hYN'
      have hNX : N'.map X.subtype ≤ X := Subgroup.map_subtype_le N'
      have hYN : Y ≤ N'.map X.subtype := by
        rw [← hYt]
        exact Subgroup.map_mono hYN'
      have hnorm : X ≤ Subgroup.normalizer ((N'.map X.subtype : Subgroup (MulAut V)) : Set (MulAut V)) := by
        intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro a
        constructor
        · rintro ⟨a', ha', rfl⟩
          exact ⟨⟨x, hx⟩ * a' * ⟨x, hx⟩⁻¹, hN'.conj_mem a' ha' ⟨x, hx⟩, by simp⟩
        · rintro ⟨b, hb, hba⟩
          refine ⟨⟨x, hx⟩⁻¹ * b * ⟨x, hx⟩, hN'.conj_mem b hb ⟨x, hx⟩⁻¹ |> fun h => ?_, ?_⟩
          · simpa using h
          · simpa [mul_assoc] using congrArg (fun z => x⁻¹ * z * x) hba
      have hNeq := hgen _ hNX hYN hnorm
      rw [eq_top_iff]
      intro x _
      have hx : (x : MulAut V) ∈ N'.map X.subtype := by rw [hNeq]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
    · intro g
      have himg : (Yt ⊔ Yt.map (MulAut.conj g).toMonoidHom).map X.subtype =
          Y ⊔ Y.map (MulAut.conj (g : MulAut V)).toMonoidHom := by
        have hcomp : X.subtype.comp (MulAut.conj g).toMonoidHom =
            (MulAut.conj (g : MulAut V)).toMonoidHom.comp X.subtype := by
          ext x
          simp [MulAut.conj_apply]
        rw [Subgroup.map_sup, Subgroup.map_map, hcomp, ← Subgroup.map_map, hYt]
      have hcard : Nat.card ↥(Yt ⊔ Yt.map (MulAut.conj g).toMonoidHom) =
          Nat.card ↥(Y ⊔ Y.map (MulAut.conj (g : MulAut V)).toMonoidHom) := by
        rw [← himg, Subgroup.card_map_of_injective X.subtype_injective]
      rw [hcard]
      exact card_sup_conj_dvd hV hYX hodd hU4 g.2
  obtain ⟨Rt, hRtn, hRt7, hRt⟩ := exists_normal_sevenGroup_sup_eq_top hodd hdata
  refine ⟨Rt.map X.subtype, Subgroup.map_subtype_le Rt, ?_, hRt7.map _, ?_⟩
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · rintro ⟨a', ha', rfl⟩
      exact ⟨⟨x, hx⟩ * a' * ⟨x, hx⟩⁻¹, hRtn.conj_mem a' ha' ⟨x, hx⟩, by simp⟩
    · rintro ⟨b, hb, hba⟩
      have h1 : (⟨x, hx⟩ : ↥X)⁻¹ * b * ⟨x, hx⟩ ∈ Rt := by
        simpa using hRtn.conj_mem b hb ⟨x, hx⟩⁻¹
      exact ⟨_, h1, by simpa [mul_assoc] using congrArg (fun z => x⁻¹ * z * x) hba⟩
  · have := congrArg (Subgroup.map X.subtype) hRt
    rw [Subgroup.map_sup, hYt, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    exact this

end CFSG.CGT.PushingUpLit.CGT6
