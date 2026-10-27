module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs
import CFSG.CharacterTheory.Wreathed.BaseFrattini
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8

private theorem coprime_card_inf_ker_mulEquiv {K K' : Type} [Group K] [Group K'] (p : ℕ)
    (φ : K ≃* K') (J : Subgroup K) : Nat.Coprime p (Nat.card ↥(J ⊓ φ.toMonoidHom.ker)) := by
  rw [(MonoidHom.ker_eq_bot_iff _).2 φ.injective, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right p

private theorem card_map_mulEquiv {K K' : Type} [Group K] [Group K'] (φ : K ≃* K')
    (H : Subgroup K) : Nat.card (H.map φ.toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective

private theorem map_centralizer_mulEquiv {K K' : Type} [Group K] [Group K'] (φ : K ≃* K')
    (s : Set K) :
    (Subgroup.centralizer s).map φ.toMonoidHom = Subgroup.centralizer (φ.toMonoidHom '' s) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image s φ.toMonoidHom)
    fun y hy => Subgroup.mem_map.2 ⟨φ.symm y, Subgroup.mem_centralizer_iff.2
      fun x hx => φ.injective ?_, φ.apply_symm_apply y⟩
  simpa using Subgroup.mem_centralizer_iff.1 hy (φ x) ⟨x, hx, rfl⟩

private theorem map_centralizer_singleton_mulEquiv {K K' : Type} [Group K] [Group K']
    (φ : K ≃* K') (d : K) :
    (Subgroup.centralizer ({d} : Set K)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ d} : Set K') := by
  rw [map_centralizer_mulEquiv, Set.image_singleton]
  rfl

private theorem map_centralizer_subgroup_mulEquiv {K K' : Type} [Group K] [Group K']
    (φ : K ≃* K') (H : Subgroup K) :
    (Subgroup.centralizer (H : Set K)).map φ.toMonoidHom =
      Subgroup.centralizer ((H.map φ.toMonoidHom : Subgroup K') : Set K') := by
  rw [map_centralizer_mulEquiv, Subgroup.coe_map]

private theorem centerOf_map_mulEquiv {K K' : Type} [Group K] [Group K'] (φ : K ≃* K')
    (H : Subgroup K) : centerOf (H.map φ.toMonoidHom) = (centerOf H).map φ.toMonoidHom := by
  set e : ↥H ≃* ↥(H.map φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective H φ.toMonoidHom φ.injective
  have hZ : (Subgroup.center ↥H).map e.toMonoidHom = Subgroup.center ↥(H.map φ.toMonoidHom) :=
    Subgroup.map_center_eq e
  unfold centerOf
  rw [← hZ, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem glaPLayer_map_mulEquiv {K K' : Type} [Group K] [Group K'] [Finite K] {p : ℕ}
    (hp : p.Prime) (φ : K ≃* K') (X : Subgroup K) :
    (GLAPLayer p X).map φ.toMonoidHom = GLAPLayer p (X.map φ.toMonoidHom) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    unfold GLAPLayer
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (GLTheoremB.glaPComponent_map hp φ.toMonoidHom
      (coprime_card_inf_ker_mulEquiv p φ X) hJ)
  · unfold GLAPLayer
    refine sSup_le fun J' hJ' => ?_
    obtain ⟨J, hJ, rfl⟩ := GLTheoremB.exists_glaPComponent_map_eq hp φ.toMonoidHom
      (coprime_card_inf_ker_mulEquiv p φ X) hJ'
    exact Subgroup.map_mono (le_sSup hJ)

private theorem nonempty_pQuot_map_mulEquiv {K K' : Type} [Group K] [Group K'] [Finite K]
    {p : ℕ} (hp : p.Prime) (φ : K ≃* K') (J : Subgroup K) :
    Nonempty (PQuot p J ≃* PQuot p (J.map φ.toMonoidHom)) :=
  ⟨GLTheoremB.lcEquiv hp φ.toMonoidHom J (coprime_card_inf_ker_mulEquiv p φ J)⟩

private theorem isTypeWithCenter_of_pQuot_mulEquiv {K K' : Type} [Group K] [Group K']
    [Finite K] [Finite K'] {p : ℕ} {X : Subgroup K} {Y : Subgroup K'}
    (e : PQuot p X ≃* PQuot p Y) {Q : TauCeti.CFSGIndex → Prop} {z : ℕ}
    (h : IsTypeWithCenter p X Q z) : IsTypeWithCenter p Y Q z := by
  obtain ⟨⟨i, hi, ⟨f⟩⟩, hz⟩ := h
  exact ⟨⟨i, hi, ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm.trans f⟩⟩,
    (Nat.card_congr (Subgroup.centerCongr e).symm.toEquiv).trans hz⟩

private theorem isTypeWithCenter_map_mulEquiv {K K' : Type} [Group K] [Group K'] [Finite K]
    [Finite K'] {p : ℕ} (hp : p.Prime) (φ : K ≃* K') {J : Subgroup K}
    {Q : TauCeti.CFSGIndex → Prop} {z : ℕ} (h : IsTypeWithCenter p J Q z) :
    IsTypeWithCenter p (J.map φ.toMonoidHom) Q z := by
  obtain ⟨e⟩ := nonempty_pQuot_map_mulEquiv hp φ J
  exact isTypeWithCenter_of_pQuot_mulEquiv e h

private theorem catalogIs_pSimple_map_mulEquiv {K K' : Type} [Group K] [Group K'] [Finite K]
    {p : ℕ} (hp : p.Prime) (φ : K ≃* K') {J : Subgroup K} {Q : TauCeti.CFSGIndex → Prop}
    (h : catalogIs (PSimple p J) Q) : catalogIs (PSimple p (J.map φ.toMonoidHom)) Q := by
  obtain ⟨e⟩ := nonempty_pQuot_map_mulEquiv hp φ J
  exact (catalogIs_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))).1 h

private theorem rowK_map_mulEquiv {K K' : Type} [Group K] [Group K'] [Finite K] [Finite K']
    {p : ℕ} (hp : p.Prime) (φ : K ≃* K') {row : Row} {J : Subgroup K} (h : RowK row p J) :
    RowK row p (J.map φ.toMonoidHom) := by
  obtain ⟨e⟩ := nonempty_pQuot_map_mulEquiv hp φ J
  have hbot (hJ : J = ⊥) : J.map φ.toMonoidHom = ⊥ := by rw [hJ, Subgroup.map_bot]
  cases row with
  | ly => exact hbot h
  | co2 => exact isTypeWithCenter_of_pQuot_mulEquiv e h
  | co1 => exact isTypeWithCenter_of_pQuot_mulEquiv e h
  | fi24 => exact hbot h
  | fi24h => exact hbot h
  | suz => exact hbot h
  | suzh => exact hbot h
  | th => exact hbot h
  | m3 => exact isTypeWithCenter_of_pQuot_mulEquiv e h
  | m5 =>
    obtain ⟨f⟩ := h
    exact ⟨e.symm.trans f⟩

private theorem isExtraSpec2_map_mulEquiv {K K' : Type} [Group K] [Group K'] (φ : K ≃* K')
    {R : Subgroup K} (h : IsExtraSpec2 R) : IsExtraSpec2 (R.map φ.toMonoidHom) := by
  set e : ↥R ≃* ↥(R.map φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective R φ.toMonoidHom φ.injective
  obtain ⟨h2, hcomm, hfrat, hcard⟩ := h
  have hC : (commutator ↥R).map e.toMonoidHom = commutator ↥(R.map φ.toMonoidHom) := by
    rw [_root_.map_commutator_eq, (MonoidHom.range_eq_top (f := e.toMonoidHom)).2 e.surjective,
      _root_.commutator_def]
  have hF : (frattini ↥R).map e.toMonoidHom = frattini ↥(R.map φ.toMonoidHom) :=
    CFSG.Wreathed.frattini_map_mulEquiv e
  have hZ : (Subgroup.center ↥R).map e.toMonoidHom = Subgroup.center ↥(R.map φ.toMonoidHom) :=
    Subgroup.map_center_eq e
  refine ⟨h2.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hC, ← hF, hcomm]
  · rw [← hF, ← hZ, hfrat]
  · rw [← hcard]
    exact Nat.card_congr (Subgroup.centerCongr e).symm.toEquiv

private theorem rowIOf_map_mulEquiv {K K' : Type} [Group K] [Group K'] [Finite K] {p : ℕ}
    (hp : p.Prime) (φ : K ≃* K') (d : K) :
    rowIOf p (φ d) = (rowIOf p d).map φ.toMonoidHom := by
  unfold rowIOf
  rw [glaPLayer_map_mulEquiv hp, map_centralizer_singleton_mulEquiv]

private theorem rowKOf_map_mulEquiv {K K' : Type} [Group K] [Group K'] [Finite K] {p : ℕ}
    (hp : p.Prime) (φ : K ≃* K') (d : K) (R : Subgroup K) :
    rowKOf p (φ d) (R.map φ.toMonoidHom) = (rowKOf p d R).map φ.toMonoidHom := by
  unfold rowKOf
  rw [rowIOf_map_mulEquiv hp, ← Subgroup.map_equiv_normalizer_eq,
    ← Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective, glaPLayer_map_mulEquiv hp]

private theorem rowR0Of_map_mulEquiv {K K' : Type} [Group K] [Group K'] (φ : K ≃* K') (d : K)
    (R : Subgroup K) : rowR0Of (φ d) (R.map φ.toMonoidHom) = (rowR0Of d R).map φ.toMonoidHom := by
  unfold rowR0Of
  rw [Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective, map_centralizer_singleton_mulEquiv]

theorem I301ARowCfg.map {K K' : Type} [Group K] [Group K'] [Finite K] [Finite K'] {row : Row}
    {R B₁ : Subgroup K} {d : K} (h : I301ARowCfg row R B₁ d) (φ : K ≃* K') :
    I301ARowCfg row (R.map φ.toMonoidHom) (B₁.map φ.toMonoidHom) (φ d) := by
  have hp : row.prime.Prime := by cases row <;> norm_num [Row.prime]
  exact
    { hR := ⟨isExtraSpec2_map_mulEquiv φ h.hR.1, (card_map_mulEquiv φ R).trans h.hR.2⟩
      hB := ⟨h.hB.1.map φ.toMonoidHom, (card_map_mulEquiv φ B₁).trans h.hB.2⟩
      hBN := (Subgroup.map_mono h.hBN).trans_eq (Subgroup.map_equiv_normalizer_eq R φ)
      hd := ⟨Subgroup.mem_map_of_mem φ.toMonoidHom h.hd.1, φ.map_ne_one_iff.2 h.hd.2⟩
      hI := by
        rw [rowIOf_map_mulEquiv hp]
        exact isTypeWithCenter_map_mulEquiv hp φ h.hI
      hK := by
        rw [rowKOf_map_mulEquiv hp]
        exact rowK_map_mulEquiv hp φ h.hK
      hR0 := by
        rw [rowR0Of_map_mulEquiv, card_map_mulEquiv]
        exact h.hR0
      hR0t := by
        rw [rowR0Of_map_mulEquiv, card_map_mulEquiv]
        exact h.hR0t.imp (isExtraSpec2_map_mulEquiv φ) id
      hK6 := h.hK6.imp id fun h6 => by
        rw [rowKOf_map_mulEquiv hp, rowR0Of_map_mulEquiv, centerOf_map_mulEquiv,
          ← map_centralizer_singleton_mulEquiv, ← map_centralizer_subgroup_mulEquiv,
          ← Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective, ← glaPLayer_map_mulEquiv hp, h6]
      hNL := fun h5 => by
        obtain ⟨J₀, hJ₀, hcat⟩ := h.hNL h5
        refine ⟨J₀.map φ.toMonoidHom, ?_, catalogIs_pSimple_map_mulEquiv Nat.prime_five φ hcat⟩
        rw [← Subgroup.map_equiv_normalizer_eq]
        exact GLTheoremB.glaPComponent_map Nat.prime_five φ.toMonoidHom
          (coprime_card_inf_ker_mulEquiv 5 φ _) hJ₀
      hMax := by
        intro A _ _ ι hι hn hc R' hR' hN hle
        have hrange : (ι.comp φ.toMonoidHom).range = ι.range := by
          rw [MonoidHom.range_comp, (MonoidHom.range_eq_top (f := φ.toMonoidHom)).2 φ.surjective,
            ← MonoidHom.range_eq_map]
        have hmap (H : Subgroup K) :
            H.map (ι.comp φ.toMonoidHom) = (H.map φ.toMonoidHom).map ι :=
          (Subgroup.map_map _ _ _).symm
        rw [← hrange] at hn hc
        rw [h.hMax A (ι.comp φ.toMonoidHom) (hι.comp φ.injective) hn hc R' hR'
          (by rw [hmap, Subgroup.map_sup, ← rowKOf_map_mulEquiv hp]; exact hN)
          (by rw [hmap]; exact hle), hmap] }

theorem i301ARow_of_model {row : Row} (K₀ : Type) [Group K₀] [Finite K₀]
    (hK₀ : Nonempty (K₀ ≃* (TauCeti.CFSGIndex.sporadic row.name).Group))
    {R B₁ : Subgroup K₀} {d : K₀} (h : I301ARowCfg row R B₁ d) : I301ARow row := by
  intro _ K _ _ hK
  obtain ⟨i, hi, ⟨e⟩⟩ := hK
  obtain rfl : i = .sporadic row.name := hi
  obtain ⟨e₀⟩ := hK₀
  exact ⟨_, _, _, h.map (e₀.trans e.symm)⟩

end CFSG.LocalAnalysis.GLTheoremA.H301
