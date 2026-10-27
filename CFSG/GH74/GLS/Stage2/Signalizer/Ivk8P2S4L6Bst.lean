module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Star
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L4Aux
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
open scoped commutatorElement

section YLevel

variable {Y : Type} [Group Y] [Finite Y]

theorem conj_apply_aut' {Z : Type} [Group Z] (α : MulAut Z) (y : Z) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext z
  simp [MulAut.conj_apply]

omit [Finite Y] in
theorem conj_injective_of_simple (hs : IsSimpleGroup Y) (hns : ¬ Group.IsSolvable Y) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  have hc : Subgroup.center Y = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · exact h
    · exfalso
      apply hns
      have : ∀ a b : Y, a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
      exact (IsSimpleGroup.comm_iff_isSolvable.mp this)
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have hyc : y ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut Y => φ g) hy
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * y = (y * g * y⁻¹) * y := by rw [this]
      _ = y * g := by group
  rw [hc] at hyc
  exact hyc

theorem eq_map_conj_of_normalized (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y}
    (hE : ∃ E : Subgroup Y, E ≤ fixSub α ∧ IsElementaryAbelian 3 ↥E ∧ Nat.card ↥E = 9 ∧
      ∀ c ∈ fixSub α, c ∈ normalizer (E : Set Y))
    (h9 : ∀ P : Subgroup (MulAut Y), IsPGroup 3 ↥P → (∀ e ∈ P, e * α = α * e) →
      (∀ c ∈ fixSub α, MulAut.conj c ∈ normalizer (P : Set (MulAut Y))) → Nat.card ↥P ≤ 9)
    {P : Subgroup (MulAut Y)} (hP : IsPGroup 3 ↥P) (hcomm : ∀ e ∈ P, e * α = α * e)
    (hnorm : ∀ c ∈ fixSub α, MulAut.conj c ∈ normalizer (P : Set (MulAut Y)))
    (hcard : Nat.card ↥P = 9) :
    ∃ E : Subgroup Y, E ≤ fixSub α ∧ IsElementaryAbelian 3 ↥E ∧ Nat.card ↥E = 9 ∧
      (∀ c ∈ fixSub α, c ∈ normalizer (E : Set Y)) ∧
      P = E.map (MulAut.conj : Y →* MulAut Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEle, hEel, hEcard, hEnorm⟩ := hE
  refine ⟨E, hEle, hEel, hEcard, hEnorm, ?_⟩
  set B : Subgroup (MulAut Y) := E.map (MulAut.conj : Y →* MulAut Y) with hB
  have hBp : IsPGroup 3 ↥B := (IsElementaryAbelian.isPGroup 3 ↥E).map _
  have hBcard : Nat.card ↥B = 9 := by
    rw [hB, Subgroup.card_map_of_injective hinj]
    exact hEcard
  have hBnorm : B ≤ normalizer (P : Set (MulAut Y)) := by
    rintro _ ⟨e, he, rfl⟩
    exact hnorm e (hEle he)
  have hsup : IsPGroup 3 ↥(B ⊔ P) := hBp.to_sup_of_normal_right' hP hBnorm
  have hBcomm : B ≤ Subgroup.centralizer {α} := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 : h * MulAut.conj e * h⁻¹ = MulAut.conj (h e) := conj_apply_aut' h e
    have h2 : h e = e := (mem_fixSub).mp (hEle he)
    rw [h2] at h1
    calc h * MulAut.conj e = (h * MulAut.conj e * h⁻¹) * h := by group
      _ = MulAut.conj e * h := by rw [h1]
  have hPcomm : P ≤ Subgroup.centralizer {α} := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hcomm e he).symm
  have hsupcomm : ∀ e ∈ B ⊔ P, e * α = α * e := by
    intro e he
    have := (sup_le hBcomm hPcomm) he
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this α (Set.mem_singleton α)).symm
  have hBnormAll : ∀ c ∈ fixSub α, MulAut.conj c ∈ normalizer (B : Set (MulAut Y)) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hE' : E.map (MulAut.conj c).toMonoidHom = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEnorm c hc)
    calc B.map (MulAut.conj (MulAut.conj c : MulAut Y)).toMonoidHom
        = E.map ((MulAut.conj (MulAut.conj c : MulAut Y)).toMonoidHom.comp
            (MulAut.conj : Y →* MulAut Y)) := by rw [hB, Subgroup.map_map]
      _ = E.map ((MulAut.conj : Y →* MulAut Y).comp (MulAut.conj c).toMonoidHom) := by
          congr 1
          ext e
          simp [MulAut.conj_apply]
      _ = (E.map (MulAut.conj c).toMonoidHom).map (MulAut.conj : Y →* MulAut Y) := by
          rw [Subgroup.map_map]
      _ = B := by rw [hE']
  have hsupnorm : ∀ c ∈ fixSub α,
      MulAut.conj c ∈ normalizer ((B ⊔ P : Subgroup (MulAut Y)) : Set _) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBnormAll c hc),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnorm c hc)]
  have hle9 : Nat.card ↥(B ⊔ P) ≤ 9 := h9 _ hsup hsupcomm hsupnorm
  have hBeq : B = B ⊔ P :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hBcard]; exact hle9)
  have hPB : P ≤ B := by
    rw [hBeq]
    exact le_sup_right
  exact Subgroup.eq_of_le_of_card_ge hPB (by rw [hBcard, hcard])

end YLevel

section JLevel

variable {G : Type} [Group G]

theorem bst_noncyclic [Finite G] (hstar : KStarL34) (hkb : KB813) (hno3 : KNoOrder3L34)
    {J O : Subgroup G} (hq : IsQuasisimple ↥J) (hLie : LieModel (↥J ⧸ center ↥J) .PSL 3 2 2)
    (hZ : Odd (Nat.card (center ↥J))) {z : G} (hzN : z ∈ normalizer (J : Set G))
    (hz2 : z * z = 1) (hJz : ⁅J, zpowers z⁆ = J) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hOp : IsPGroup p ↥O) (hOz : ∀ x ∈ O, z * x = x * z)
    (hOnorm : ∀ y ∈ J, y * z = z * y → y ∈ normalizer (O : Set G))
    (hOnc : ¬ O ⊓ normalizer (J : Set G) ≤ centralizer (J : Set G))
    {w : G} (hwJ : w ∈ J) (hw2 : w * w = 1) (hwz : w * z = z * w) (hw1 : w ≠ 1) :
    ¬ IsCyclic ↥(Pbar J (O ⊓ J)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, hns⟩ := Gen.quasisimple_quot hq
  have hinj := conj_injective_of_simple hs hns
  set P : Subgroup G := O ⊓ normalizer (J : Set G) with hP
  have hPN : P ≤ normalizer (J : Set G) := inf_le_right
  have hPp : IsPGroup p ↥P := hOp.to_le inf_le_left
  have hPz : ∀ x ∈ P, z * x = x * z := fun x hx => hOz x hx.1
  have hPnorm : ∀ y ∈ J, y * z = z * y → y ∈ normalizer (P : Set G) := fun y hy hyz =>
    mem_normalizer_inf' (hOnorm y hy hyz) (Subgroup.le_normalizer (Subgroup.le_normalizer hy))
  obtain ⟨hp3, hU, h9, -⟩ := star_J hstar hq hLie hZ hzN hz2 hJz hp hp2 hPN hPp hOnc hPz hPnorm
  obtain ⟨hα2, hα1, hPbp, hPb1, hcomm, hnorm⟩ :=
    pbar_data hq hZ hzN hz2 hJz hPN hPp hOnc hPz hPnorm
  subst hp3
  have hk := (hkb _ hLie).2.2 (alphaZ J hzN) hα2 hU
  obtain ⟨E₀, hE₀le, hE₀el, hE₀card, hE₀norm, hPeq⟩ :=
    eq_map_conj_of_normalized hinj hk.1 hk.2 hPbp hcomm hnorm h9
  have := hE₀el.toIsMulCommutative
  set wb : ↥J ⧸ center ↥J := QuotientGroup.mk (⟨w, hwJ⟩ : ↥J) with hwb
  have hwbfix : alphaZ J hzN wb = wb := by
    rw [hwb, alphaZ_mk]
    congr 1
    apply Subtype.ext
    show z * w * z⁻¹ = w
    calc z * w * z⁻¹ = (w * z) * z⁻¹ := by rw [hwz]
      _ = w := by group
  have hwb2 : wb * wb = 1 := by
    rw [hwb, ← QuotientGroup.mk_mul]
    have : (⟨w, hwJ⟩ * ⟨w, hwJ⟩ : ↥J) = 1 := Subtype.ext hw2
    rw [this, QuotientGroup.mk_one]
  have hwb1 : wb ≠ 1 := by
    intro h
    have hc : (⟨w, hwJ⟩ : ↥J) ∈ center ↥J := (QuotientGroup.eq_one_iff _).mp h
    have hw1' : (⟨w, hwJ⟩ : ↥J) ≠ 1 := fun h' => hw1 (congrArg Subtype.val h')
    have h2 : orderOf (⟨w, hwJ⟩ : ↥J) = 2 :=
      orderOf_eq_prime (by
        have : ((⟨w, hwJ⟩ : ↥J) ^ 2 : ↥J) = 1 := by
          rw [pow_two]
          exact Subtype.ext hw2
        exact this) hw1'
    have h3 : orderOf (⟨(⟨w, hwJ⟩ : ↥J), hc⟩ : ↥(center ↥J)) ∣ Nat.card ↥(center ↥J) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, h2] at h3
    exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr h3)
  have hwbmem : wb ∈ fixSub (alphaZ J hzN) := mem_fixSub.mpr hwbfix
  have hwbnorm : wb ∈ normalizer (E₀ : Set (↥J ⧸ center ↥J)) := hE₀norm wb hwbmem
  have hfpf : ∀ e ∈ E₀, e ≠ 1 → wb * e ≠ e * wb := by
    intro e he he1 hc
    have hord : orderOf e = 3 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E₀) e he) he1
    exact hno3 _ hLie hs wb e hwb2 hwb1 hord hc
  let φ : ↥E₀ → ↥E₀ := fun e =>
    ⟨(e : ↥J ⧸ center ↥J) * (wb * (e : ↥J ⧸ center ↥J)⁻¹ * wb⁻¹),
      E₀.mul_mem e.2 ((Subgroup.mem_normalizer_iff.mp hwbnorm _).mp (E₀.inv_mem e.2))⟩
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : (a : ↥J ⧸ center ↥J) * (wb * (a : ↥J ⧸ center ↥J)⁻¹ * wb⁻¹) =
        (b : ↥J ⧸ center ↥J) * (wb * (b : ↥J ⧸ center ↥J)⁻¹ * wb⁻¹) := congrArg Subtype.val hab
    have hx : wb * ((a : ↥J ⧸ center ↥J)⁻¹ * b) * wb⁻¹ = (a : ↥J ⧸ center ↥J)⁻¹ * b := by
      calc wb * ((a : ↥J ⧸ center ↥J)⁻¹ * b) * wb⁻¹
          = (wb * (a : ↥J ⧸ center ↥J)⁻¹ * wb⁻¹) * (wb * (b : ↥J ⧸ center ↥J) * wb⁻¹) := by
            group
        _ = (a : ↥J ⧸ center ↥J)⁻¹ * ((a : ↥J ⧸ center ↥J) *
              (wb * (a : ↥J ⧸ center ↥J)⁻¹ * wb⁻¹)) * (wb * (b : ↥J ⧸ center ↥J) * wb⁻¹) := by
            group
        _ = (a : ↥J ⧸ center ↥J)⁻¹ * ((b : ↥J ⧸ center ↥J) *
              (wb * (b : ↥J ⧸ center ↥J)⁻¹ * wb⁻¹)) * (wb * (b : ↥J ⧸ center ↥J) * wb⁻¹) := by
            rw [h1]
        _ = (a : ↥J ⧸ center ↥J)⁻¹ * b := by group
    by_contra hne
    have hne' : (a : ↥J ⧸ center ↥J)⁻¹ * b ≠ 1 := by
      intro h
      apply hne
      apply Subtype.ext
      have : (a : ↥J ⧸ center ↥J) = b := by
        calc (a : ↥J ⧸ center ↥J) = (a : ↥J ⧸ center ↥J) * ((a : ↥J ⧸ center ↥J)⁻¹ * b) := by
              rw [h, mul_one]
          _ = b := by group
      exact this
    refine hfpf _ (E₀.mul_mem (E₀.inv_mem a.2) b.2) hne' ?_
    calc wb * ((a : ↥J ⧸ center ↥J)⁻¹ * b) = (wb * ((a : ↥J ⧸ center ↥J)⁻¹ * b) * wb⁻¹) * wb := by
          group
      _ = ((a : ↥J ⧸ center ↥J)⁻¹ * b) * wb := by rw [hx]
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
  have hsub : E₀.map (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)) ≤
      Pbar J (O ⊓ J) := by
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨e', he'⟩ := hφsurj ⟨f, hf⟩
    have hconj : (MulAut.conj (e' : ↥J ⧸ center ↥J) : MulAut (↥J ⧸ center ↥J)) ∈ Pbar J P := by
      rw [hPeq]
      exact ⟨e', e'.2, rfl⟩
    obtain ⟨x, hx, hxP, hxeq⟩ := mem_Pbar.mp hconj
    have hwO : w ∈ normalizer (O : Set G) := hOnorm w hwJ hwz
    have hxO : x ∈ O := hxP.1
    have h1 : x * w * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hx w).mp hwJ
    have hbJ : x * w * x⁻¹ * w⁻¹ ∈ J := J.mul_mem h1 (J.inv_mem hwJ)
    have hbO : x * w * x⁻¹ * w⁻¹ ∈ O := by
      have h2 : w * x⁻¹ * w⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp hwO _).mp (O.inv_mem hxO)
      have := O.mul_mem hxO h2
      simpa [mul_assoc] using this
    have himg : (QuotientGroup.mk (⟨x * w * x⁻¹ * w⁻¹, hbJ⟩ : ↥J) : ↥J ⧸ center ↥J) = f := by
      have hdecomp : (⟨x * w * x⁻¹ * w⁻¹, hbJ⟩ : ↥J) = ⟨x * w * x⁻¹, h1⟩ * (⟨w, hwJ⟩ : ↥J)⁻¹ :=
        Subtype.ext rfl
      rw [hdecomp, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hwb]
      have h3 : (QuotientGroup.mk (⟨x * w * x⁻¹, h1⟩ : ↥J) : ↥J ⧸ center ↥J) =
          YCfg.yAct J ⟨x, hx⟩ wb := (YCfg.yAct_apply_mk J ⟨x, hx⟩ ⟨w, hwJ⟩).symm
      rw [h3, hxeq, MulAut.conj_apply]
      have := congrArg Subtype.val he'
      simp only [φ] at this
      rw [← this]
      group
    have hmem : (⟨x * w * x⁻¹ * w⁻¹, hbJ⟩ : ↥J) ∈ (O ⊓ J).subgroupOf J := ⟨hbO, hbJ⟩
    have hmain : MulAut.conj f = YCfg.yAct J ⟨x * w * x⁻¹ * w⁻¹, le_normalizer hbJ⟩ := by
      rw [← himg]
      exact (YCfg.yAct_of_mem J ⟨x * w * x⁻¹ * w⁻¹, hbJ⟩).symm
    rw [hmain]
    exact yAct_mem_Pbar _ ⟨hbO, hbJ⟩
  intro hcyc
  have : IsCyclic ↥(Pbar J (O ⊓ J)) := hcyc
  have : IsCyclic ↥(E₀.map (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J))) :=
    P2S4.isCyclic_of_le hsub
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := ↥(E₀.map (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J))))
  have hcard9 : Nat.card ↥(E₀.map (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J))) =
      9 := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hE₀card
  have hg3 : g ^ 3 = 1 := by
    obtain ⟨e, he, hge⟩ := g.2
    apply Subtype.ext
    show ((g : MulAut (↥J ⧸ center ↥J))) ^ 3 = 1
    rw [← hge, ← map_pow]
    have : e ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E₀) e he
    rw [this, map_one]
  have hord : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  rw [hg, hcard9] at hord
  omega

end JLevel

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6
