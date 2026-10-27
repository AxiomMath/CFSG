module

public import CFSG.GH74.GLS.IVK.Lifted.YConf

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4

section Action

variable {Gs : Type} [Group Gs]

@[expose] def normAct (A : Subgroup Gs) : ↥(normalizer (A : Set Gs)) →* MulAut ↥A where
  toFun x := TwoThin.conjAut x.2
  map_one' := by
    ext a
    simp [TwoThin.conjAut]
  map_mul' x y := by
    ext a
    simp [TwoThin.conjAut, mul_assoc]

end Action

section CenterSL

variable {F : Type} [Field F]

theorem cen_unique_of_equiv {Q : Type} [Group Q] (e : Q ≃* SpecialLinearGroup (Fin 2) F) {x y : Q}
    (hx : x ∈ center Q) (hy : y ∈ center Q) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have hcen : ∀ z : Q, z ∈ center Q → e z ∈ center (SpecialLinearGroup (Fin 2) F) := by
    intro z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have := hz (e.symm g)
    have h2 := congrArg e this
    simpa using h2
  have := sl2_center_unique (hcen x hx) (hcen y hy)
    (fun h => hx1 (e.injective (by rw [h, map_one]))) (fun h => hy1 (e.injective (by rw [h, map_one])))
  exact e.injective this

end CenterSL

section Main

variable {Gs : Type} [Group Gs]

theorem model_outer [Finite Gs] {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) {E₁ : Subgroup Gs} (e : ↥E₁ ≃* SpecialLinearGroup (Fin 2) F) {z w : Gs}
    (hz₁ : z ∈ E₁) (hzc : ∀ a ∈ E₁, a * z = z * a) (hz1 : z ≠ 1)
    (hwN : w ∈ normalizer (E₁ : Set Gs)) (hww : w * w = 1)
    (hn : ((zpowers z).subgroupOf (E₁ ⊔ zpowers w)).Normal)
    (hPGL : IsPGL2 (↥(E₁ ⊔ zpowers w) ⧸ (zpowers z).subgroupOf (E₁ ⊔ zpowers w))
      (fun r => r = Nat.card F))
    (P : Sylow 2 ↥E₁) (hP : ∀ x ∈ (P : Subgroup ↥E₁), TwoThin.conjAut hwN x ∈ (P : Subgroup ↥E₁)) :
    TwoThin.conjAut hwN ∉ innOf ↥E₁ ∧
      (gammaOf hodd h3 (MulAut.congr e (TwoThin.conjAut hwN))).right = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : L2Field F := ⟨hodd, h3⟩
  have hfinE : Finite ↥E₁ := Finite.of_equiv _ e.symm.toEquiv
  set X : Subgroup Gs := E₁ ⊔ zpowers w with hX
  set Z₀ : Subgroup ↥X := (zpowers z).subgroupOf X with hZ₀
  have hE₁X : E₁ ≤ X := le_sup_left
  have hwX : w ∈ X := mem_sup_right (mem_zpowers w)
  have hzE : zpowers z ≤ E₁ := zpowers_le.2 hz₁
  have hXN : X ≤ normalizer (E₁ : Set Gs) := sup_le le_normalizer (zpowers_le.2 hwN)
  let Φ : ↥X →* MulAut ↥E₁ := (normAct E₁).comp (Subgroup.inclusion hXN)
  have hΦ : ∀ (x : ↥X) (a : ↥E₁), (((Φ x) a : ↥E₁) : Gs) = (x : Gs) * (a : Gs) * (x : Gs)⁻¹ :=
    fun x a => rfl
  have hwx : (TwoThin.conjAut hwN : MulAut ↥E₁) = Φ ⟨w, hwX⟩ := rfl
  have hXcases : ∀ x : ↥X, (∃ a : ↥E₁, (x : Gs) = a) ∨ ∃ a : ↥E₁, (x : Gs) = a * w := by
    intro x
    rcases mem_sup_zpowers_cases hww (fun n hn => (Subgroup.mem_normalizer_iff.1 hwN n).1 hn) x.2 with
      h | ⟨n, hn, hx⟩
    · exact Or.inl ⟨⟨x, h⟩, rfl⟩
    · exact Or.inr ⟨⟨n, hn⟩, hx⟩
  have hzcen : (⟨z, hz₁⟩ : ↥E₁) ∈ center ↥E₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2)
  have hz1' : (⟨z, hz₁⟩ : ↥E₁) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hcard_center : Nat.card ↥(center ↥E₁) = 2 := by
    rw [Nat.card_eq_two_iff' (1 : ↥(center ↥E₁))]
    refine ⟨⟨⟨z, hz₁⟩, hzcen⟩, ?_, ?_⟩
    · intro h
      exact hz1' (congrArg Subtype.val h)
    · intro y hy
      apply Subtype.ext
      exact cen_unique_of_equiv e y.2 hzcen (fun h => hy (Subtype.ext h)) hz1'
  obtain ⟨F₀, hF₀f, hF₀fin, hF₀card, ⟨eD⟩⟩ := hPGL
  have hF₀ : Nat.card F₀ = Nat.card F := hF₀card
  have hcardE : Nat.card ↥E₁ = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, sl2_card_formula]
  have hcardD : Nat.card (↥X ⧸ Z₀) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr eD.toEquiv, pgl2_card_formula, hF₀]
  have hinnCard : 2 * Nat.card ↥(innOf ↥E₁) = Nat.card ↥E₁ := by
    have h1 := Subgroup.card_ker_mul_card_range (MulAut.conj : ↥E₁ →* MulAut ↥E₁)
    have h2 : (MulAut.conj : ↥E₁ →* MulAut ↥E₁).ker = center ↥E₁ := by
      ext y
      rw [MonoidHom.mem_ker]
      exact ⟨mem_center_of_conj_eq_one, conj_eq_one_of_mem_center⟩
    rw [h2, hcard_center] at h1
    exact h1
  have hker_Z : Z₀ ≤ Φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxz : (x : Gs) ∈ zpowers z := hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxz
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [hΦ]
    have hc : (a : Gs) * (x : Gs) = (x : Gs) * (a : Gs) := by
      rw [← hk]
      exact (Commute.zpow_right (show Commute (a : Gs) z from hzc a a.2) k).eq
    show (x : Gs) * (a : Gs) * (x : Gs)⁻¹ = (a : Gs)
    rw [← hc]
    group
  let Φb : ↥X ⧸ Z₀ →* MulAut ↥E₁ := QuotientGroup.lift Z₀ Φ hker_Z
  have hΦb : ∀ x : ↥X, Φb (QuotientGroup.mk x) = Φ x := fun x => rfl
  have hrange : Φb.range = Φ.range := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      induction u using QuotientGroup.induction_on with | H x => ?_
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨QuotientGroup.mk x, rfl⟩
  have hInn_le : innOf ↥E₁ ≤ Φ.range := by
    rintro _ ⟨a, rfl⟩
    refine ⟨⟨(a : Gs), hE₁X a.2⟩, ?_⟩
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [hΦ]
    rfl
  have hα_out : TwoThin.conjAut hwN ∉ innOf ↥E₁ := by
    intro hin
    have hR : Φ.range = innOf ↥E₁ := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        rcases hXcases x with ⟨a, hxa⟩ | ⟨a, hxa⟩
        · have : x = ⟨(a : Gs), hE₁X a.2⟩ := Subtype.ext hxa
          rw [this]
          have : Φ ⟨(a : Gs), hE₁X a.2⟩ = MulAut.conj a := by
            apply MulEquiv.ext
            intro b
            apply Subtype.ext
            rw [hΦ]
            rfl
          rw [this]
          exact ⟨a, rfl⟩
        · have : x = ⟨(a : Gs), hE₁X a.2⟩ * ⟨w, hwX⟩ := Subtype.ext hxa
          rw [this, map_mul]
          have h1 : Φ ⟨(a : Gs), hE₁X a.2⟩ = MulAut.conj a := by
            apply MulEquiv.ext
            intro b
            apply Subtype.ext
            rw [hΦ]
            rfl
          rw [h1, ← hwx]
          exact mul_mem ⟨a, rfl⟩ hin
      · exact hInn_le
    have hk := Subgroup.card_ker_mul_card_range Φb
    rw [hcardD, hrange, hR] at hk
    have hinnpos : 0 < Nat.card ↥(innOf ↥E₁) := Nat.card_pos
    have hk2 : Nat.card Φb.ker = 2 := by
      have : Nat.card Φb.ker * Nat.card ↥(innOf ↥E₁) = 2 * Nat.card ↥(innOf ↥E₁) := by
        rw [hk, ← hcardE, ← hinnCard]
      exact Nat.eq_of_mul_eq_mul_right hinnpos this
    obtain ⟨u, hu1, huc⟩ := exists_central_of_normal_card_two Φb.ker hk2
    have hψu : eD u ∈ Subgroup.center (PGL2 F₀) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨v, rfl⟩ := eD.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact (Subgroup.mem_center_iff.1 huc v)
    rw [pgl2_center_eq_bot F₀, Subgroup.mem_bot] at hψu
    exact hu1 (eD.injective (hψu.trans (map_one eD).symm))
  refine ⟨hα_out, ?_⟩
  set α : MulAut ↥E₁ := TwoThin.conjAut hwN with hαdef
  have hα2 : α * α = 1 := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    show w * (w * (a : Gs) * w⁻¹) * w⁻¹ = (a : Gs)
    calc w * (w * (a : Gs) * w⁻¹) * w⁻¹ = (w * w) * (a : Gs) * (w * w)⁻¹ := by group
      _ = a := by rw [hww]; group
  have hαR : α ∈ Φ.range := ⟨⟨w, hwX⟩, rfl⟩
  have hconj_Φ : ∀ a : ↥E₁, Φ ⟨(a : Gs), hE₁X a.2⟩ = MulAut.conj a := by
    intro a
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [hΦ]
    rfl
  have hRcases : ∀ r ∈ Φ.range, r ∈ innOf ↥E₁ ∨ ∃ i ∈ innOf ↥E₁, r = i * α := by
    rintro _ ⟨x, rfl⟩
    rcases hXcases x with ⟨a, hxa⟩ | ⟨a, hxa⟩
    · left
      have : x = ⟨(a : Gs), hE₁X a.2⟩ := Subtype.ext hxa
      rw [this, hconj_Φ]
      exact ⟨a, rfl⟩
    · right
      have : x = ⟨(a : Gs), hE₁X a.2⟩ * ⟨w, hwX⟩ := Subtype.ext hxa
      rw [this, map_mul, hconj_Φ]
      exact ⟨MulAut.conj a, ⟨a, rfl⟩, rfl⟩
  have hidxR : ((innOf ↥E₁).subgroupOf Φ.range).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨α, hαR⟩, fun b => ?_⟩
    have h1 : (b * ⟨α, hαR⟩ ∈ (innOf ↥E₁).subgroupOf Φ.range) ↔ ((b : MulAut ↥E₁) * α ∈ innOf ↥E₁) :=
      Iff.rfl
    have h2 : (b ∈ (innOf ↥E₁).subgroupOf Φ.range) ↔ ((b : MulAut ↥E₁) ∈ innOf ↥E₁) := Iff.rfl
    rw [h1, h2]
    rcases hRcases b b.2 with hb | ⟨i, hi, hbi⟩
    · have : (b : MulAut ↥E₁) * α ∉ innOf ↥E₁ := fun h => hα_out (by
        have := mul_mem (inv_mem hb) h
        simpa using this)
      simp [hb, this]
    · have hb' : (b : MulAut ↥E₁) ∉ innOf ↥E₁ := fun h => hα_out (by
        have h3' := mul_mem (inv_mem hi) (hbi ▸ h)
        simpa using h3')
      have : (b : MulAut ↥E₁) * α ∈ innOf ↥E₁ := by
        rw [hbi]
        have : i * α * α = i := by rw [mul_assoc, hα2, mul_one]
        rw [this]
        exact hi
      simp [hb', this]
  have hcardR : Nat.card ↥Φ.range = Nat.card ↥E₁ := by
    have h1 := Subgroup.card_mul_index ((innOf ↥E₁).subgroupOf Φ.range)
    rw [hidxR] at h1
    have h2 : Nat.card ↥((innOf ↥E₁).subgroupOf Φ.range) = Nat.card ↥(innOf ↥E₁) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hInn_le).toEquiv
    rw [h2] at h1
    omega
  have hker1 : Φb.ker = ⊥ := by
    have hk := Subgroup.card_ker_mul_card_range Φb
    rw [hcardD, hrange, hcardR, hcardE] at hk
    have hpos : 0 < Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [← hcardE]
      exact Nat.card_pos
    have : Nat.card Φb.ker = 1 := by
      have h' : Nat.card Φb.ker * (Nat.card F * (Nat.card F ^ 2 - 1)) =
          1 * (Nat.card F * (Nat.card F ^ 2 - 1)) := by rw [hk, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hpos h'
    exact Subgroup.eq_bot_of_card_eq _ this
  have hinjb : Function.Injective Φb := (MonoidHom.ker_eq_bot_iff Φb).1 hker1
  have hbij : Function.Bijective Φb.rangeRestrict :=
    ⟨fun a b h => hinjb (by
        have := congrArg Subtype.val h
        exact this), Φb.rangeRestrict_surjective⟩
  let e₁ : ↥X ⧸ Z₀ ≃* ↥Φb.range := MulEquiv.ofBijective Φb.rangeRestrict hbij
  let hRiso : ↥X ⧸ Z₀ ≃* ↥Φ.range := e₁.trans (MulEquiv.subgroupCongr hrange)
  let eR : PGL2 F₀ ≃* ↥Φ.range := eD.symm.trans hRiso
  have : Finite (PGL2 F₀) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 2) F₀ →* PGL2 F₀)
      Matrix.ProjGenLinGroup.mk_surjective
  have hodd₀ : IsOddPrimePower (Nat.card F₀) :=
    isOddPrimePower_of_L2Field (F := F₀) ⟨by rw [hF₀]; exact hodd, by rw [hF₀]; exact h3⟩
  have hdihR : HasDihedralSylowTwo ↥Φ.range :=
    hasDihedralSylowTwo_of_equiv eR (pgl2_odd_hasDihedralSylowTwo_model F₀ hodd₀)
  let Pmap : Subgroup (MulAut ↥E₁) := (P : Subgroup ↥E₁).map (MulAut.conj : ↥E₁ →* MulAut ↥E₁)
  have hPmapNorm : ∀ a ∈ Pmap, α * a * α⁻¹ ∈ Pmap := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨α p, hP p hp, ?_⟩
    exact (mulAut_conj_conj α p).symm
  have hT2 : IsPGroup 2 ↥(Pmap ⊔ zpowers α) :=
    isPGroup_sup_zpowers_of_involution (P.isPGroup'.map _) hα2 hPmapNorm
  have hTR : Pmap ⊔ zpowers α ≤ Φ.range :=
    sup_le ((Subgroup.map_le_range _ _).trans hInn_le) (zpowers_le.2 hαR)
  obtain ⟨Mm, hM, hTM⟩ := M.exists_syl2In_ge hT2 hTR
  have hdihM : ∃ n, IsDihedralTwoGroup ↥Mm n := by
    obtain ⟨m, hm, ⟨d⟩⟩ := hdihR (M.toSylow hM)
    refine ⟨m + 1, isDihedralTwoGroup_of_equiv hm ?_⟩
    exact (Subgroup.subgroupOfEquivOfLe hM.1).symm.trans
      ((MulEquiv.subgroupCongr (M.coe_toSylow hM).symm).trans d)
  exact sl_dihedral_field hodd h3 e Mm hM.2.1 P (le_sup_left.trans hTM) hdihM α
    (hTM (mem_sup_right (mem_zpowers α)))

end Main

end CFSG.GH74.GLS.IVK.Lifted
