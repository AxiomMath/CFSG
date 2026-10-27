module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14IdentA
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14IdentB
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SolCard
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5
public import CFSG.Foundations
public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import Certificates.Certificate43

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open Module

@[expose] def TvNormalizer : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)), IsTvIrred G →
      ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) U, (∀ x ∈ G, g * x * g⁻¹ ∈ G) → g ∈ G

@[expose] def TvCentralized : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)), IsTvIrred G →
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        ∀ A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U), IsMaxElemAbelianIn p G A →
          ∀ t ∈ G, IsF2Transvection t → HasCentralizedConj p G A t

section Assembly
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

local notation "𝔾" => LinearMap.GeneralLinearGroup (ZMod 2) M

namespace i285_Setup

variable (S : i285_Setup M)

theorem eq_of_H_eq {R R' : Submodule (ZMod 2) M} (hR : S.IsMin R) (hR' : S.IsMin R')
    (h : S.H R = S.H R') : R = R' := by
  by_contra hne
  obtain ⟨d, hd⟩ := S.T_nonempty hR
  have hdH : d ∈ S.H R := Subgroup.subset_closure hd
  rw [h] at hdH
  obtain ⟨v, hv, hne'⟩ := hd.2
  exact hne' (S.H_le_fix hR' hR (Ne.symm hne) hdH v hv)

theorem mem_stab_of_normalizer {R₀ : Submodule (ZMod 2) M} (hR₀ : S.IsMin R₀) {b : 𝔾}
    (hbX : b ∈ S.X) (hb : b ∈ Subgroup.normalizer (S.H R₀ : Set 𝔾)) : b ∈ i285_stab R₀ := by
  have hconj := S.H_conj hbX R₀
  have hbi : b⁻¹ ∈ Subgroup.normalizer (S.H R₀ : Set 𝔾) := (Subgroup.normalizer _).inv_mem hb
  have h1 : CFSG.Open.GLBConj b (S.H R₀) = S.H R₀ := by
    ext x
    rw [CFSG.Open.GLBConj, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := (Subgroup.mem_normalizer_iff.1 hbi y).1 hy
      simpa using this
    · intro hx
      refine ⟨b * x * b⁻¹, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      exact (Subgroup.mem_normalizer_iff.1 hb x).1 hx
  rw [h1] at hconj
  have hR' := S.isMin_map hR₀ (S.X.inv_mem hbX)
  have := S.eq_of_H_eq hR' hR₀ hconj.symm
  intro v
  have h2 := congrArg (fun T : Submodule (ZMod 2) M => v ∈ T) this
  simp only [i285_mem_map, inv_inv] at h2
  exact iff_of_eq h2


@[expose] noncomputable def secX (R : Submodule (ZMod 2) M) :
    ↥(S.X ⊓ i285_stab R) →* LinearMap.GeneralLinearGroup (ZMod 2) (↥R ⧸ S.Q.comap R.subtype) :=
  i285_secHom inf_le_right (inf_le_left.trans S.X_le_stab_Q)

theorem secX_eq_ρ {R : Submodule (ZMod 2) M} (hR : S.IsMin R) (h : ↥(S.H R)) :
    S.secX R ⟨h, ⟨S.H_le_X R h.2, S.H_le_stab_R hR h.2⟩⟩ = S.ρ hR h := rfl

end i285_Setup


section Main
variable [Finite M]

theorem i285_main_H (hN : TvNormalizer) (hC : TvCentralized) (S : i285_Setup M) {R₀ : Submodule (ZMod 2) M} (hR₀ : S.IsMin R₀)
    (hτ : S.τ ∈ S.T R₀) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup 𝔾} (hBX : B ≤ S.X)
    (hBel : IsElemAbelian p B)
    (hmax : ∀ B' : Subgroup 𝔾, B' ≤ S.X → IsElemAbelian p B' → Nat.card B' ≤ Nat.card B)
    (hBN : B ≤ Subgroup.normalizer (S.H R₀ : Set 𝔾)) :
    ∃ y ∈ S.H R₀, ∃ Q ≤ B, Nat.card B ≤ p * Nat.card Q ∧
      ∀ q ∈ Q, q * (y⁻¹ * S.τ * y) = (y⁻¹ * S.τ * y) * q := by
  classical
  have : Finite (M →ₗ[ZMod 2] M) :=
    Finite.of_injective (fun f : M →ₗ[ZMod 2] M => (f : M → M)) (fun f g h => LinearMap.ext (congrFun h))
  have : Finite 𝔾 := inferInstanceAs (Finite (M →ₗ[ZMod 2] M)ˣ)
  set H := S.H R₀ with hH
  set ρ := S.ρ hR₀ with hρ
  have hρinj : Function.Injective ρ := S.ρ_injective hR₀
  have hBst : ∀ b ∈ B, b ∈ i285_stab R₀ := fun b hb =>
    S.mem_stab_of_normalizer hR₀ (hBX hb) (hBN hb)
  have hBN' : B ≤ S.X ⊓ i285_stab R₀ := fun b hb => ⟨hBX hb, hBst b hb⟩
  have hHN : ∀ h ∈ H, h ∈ S.X ⊓ i285_stab R₀ := fun h hh =>
    ⟨S.H_le_X R₀ hh, S.H_le_stab_R hR₀ hh⟩
  set σ₀ := (S.secX R₀).comp (Subgroup.inclusion hBN') with hσ₀
  have hconjH : ∀ (b : ↥B) (h : ↥H), (b : 𝔾) * h * (b : 𝔾)⁻¹ ∈ H := fun b h =>
    (Subgroup.mem_normalizer_iff.1 (hBN b.2) h).1 h.2
  have hσρ : ∀ (b : ↥B) (h : ↥H),
      σ₀ b * ρ h * (σ₀ b)⁻¹ = ρ ⟨(b : 𝔾) * h * (b : 𝔾)⁻¹, hconjH b h⟩ := by
    intro b h
    rw [← S.secX_eq_ρ hR₀ h, ← S.secX_eq_ρ hR₀ ⟨_, hconjH b h⟩]
    have : (⟨(b : 𝔾) * h * (b : 𝔾)⁻¹, hHN _ (hconjH b h)⟩ : ↥(S.X ⊓ i285_stab R₀)) =
        ⟨b, hBN' b.2⟩ * ⟨h, hHN _ h.2⟩ * ⟨b, hBN' b.2⟩⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv]
    rfl
  have hG : IsTvIrred ρ.range := by
    refine ⟨⟨ρ '' (Subtype.val ⁻¹' S.T R₀), ?_, ?_, S.ρ_range hR₀⟩, S.ρ_irred hR₀⟩
    · obtain ⟨d, hd⟩ := S.T_nonempty hR₀
      exact ⟨_, ⟨⟨d, Subgroup.subset_closure hd⟩, hd, rfl⟩⟩
    · rintro _ ⟨⟨d, hdH⟩, hd, rfl⟩
      exact S.ρ_transvection hR₀ hd
  have hfinU : Finite (↥R₀ ⧸ S.Q.comap R₀.subtype) :=
    Finite.of_surjective (Submodule.Quotient.mk (p := S.Q.comap R₀.subtype)) (Submodule.Quotient.mk_surjective _)
  have hfinGL : Finite (LinearMap.GeneralLinearGroup (ZMod 2) (↥R₀ ⧸ S.Q.comap R₀.subtype)) := by
    have : Finite ((↥R₀ ⧸ S.Q.comap R₀.subtype) →ₗ[ZMod 2] (↥R₀ ⧸ S.Q.comap R₀.subtype)) :=
      Finite.of_injective (fun f => (f : _ → _)) (fun f g h => LinearMap.ext (congrFun h))
    exact inferInstanceAs (Finite ((↥R₀ ⧸ S.Q.comap R₀.subtype) →ₗ[ZMod 2]
      (↥R₀ ⧸ S.Q.comap R₀.subtype))ˣ)
  have hnormG : ∀ b : ↥B, σ₀ b ∈ ρ.range := by
    intro b
    apply hN _ _ hG
    intro x hx
    obtain ⟨h, rfl⟩ := hx
    rw [hσρ]
    exact ⟨_, rfl⟩
  have hAG : σ₀.range ≤ ρ.range := by
    rintro _ ⟨b, rfl⟩
    exact hnormG b
  have hAel : IsElemAbelian p σ₀.range := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      have := hBel.1.1.comm a b
      show σ₀ a * σ₀ b = σ₀ b * σ₀ a
      rw [← map_mul, ← map_mul, this]
    · rintro _ ⟨b, rfl⟩
      have hb : b ^ p = 1 := Subtype.ext (hBel.2 b b.2)
      rw [← map_pow, hb, map_one]
  set K₀ : Subgroup 𝔾 := σ₀.ker.map B.subtype with hK₀
  have hK₀B : K₀ ≤ B := Subgroup.map_subtype_le _
  have hK₀comm : ∀ k ∈ K₀, ∀ h ∈ H, k * h = h * k := by
    rintro _ ⟨b, hb, rfl⟩ h hh
    have h1 := hσρ b ⟨h, hh⟩
    rw [MonoidHom.mem_ker.1 hb, one_mul, inv_one, mul_one] at h1
    have h2 := hρinj h1.symm
    have h3 := congrArg Subtype.val h2
    simp only at h3
    rw [Subgroup.coe_subtype]
    calc (b : 𝔾) * h = ((b : 𝔾) * h * (b : 𝔾)⁻¹) * b := by group
      _ = h * b := by rw [h3]
  have hK₀el : IsElemAbelian p K₀ := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · intro x y
      apply Subtype.ext
      have := hBel.1.1.comm ⟨x.1, hK₀B x.2⟩ ⟨y.1, hK₀B y.2⟩
      exact congrArg (fun z : ↥B => (z : 𝔾)) this
    · intro x hx
      exact hBel.2 x (hK₀B hx)
  have hAmax : ∀ A' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2)
      (↥R₀ ⧸ S.Q.comap R₀.subtype)), A' ≤ ρ.range → IsElemAbelian p A' →
      Nat.card A' ≤ Nat.card σ₀.range := by
    intro A' hA'G hA'el
    set Ã : Subgroup 𝔾 := (A'.comap ρ).map H.subtype with hÃ
    have hÃH : ∀ x ∈ Ã, x ∈ H := by
      rintro _ ⟨h, _, rfl⟩
      exact h.2
    have hÃcard : Nat.card Ã = Nat.card A' := by
      rw [hÃ, Subgroup.card_map_of_injective H.subtype_injective]
      have h1 : (A'.comap ρ).map ρ = A' := by
        rw [Subgroup.map_comap_eq, inf_eq_right.2 hA'G]
      have h2 : Nat.card ((A'.comap ρ).map ρ) = Nat.card (A'.comap ρ) :=
        Subgroup.card_map_of_injective hρinj
      rw [h1] at h2
      exact h2.symm
    have hÃel : IsElemAbelian p Ã := by
      refine ⟨⟨⟨?_⟩⟩, ?_⟩
      · rintro ⟨_, h1, hh1, rfl⟩ ⟨_, h2, hh2, rfl⟩
        apply Subtype.ext
        have h3 := congrArg Subtype.val (hA'el.1.1.comm ⟨ρ h1, hh1⟩ ⟨ρ h2, hh2⟩)
        have h4 : h1 * h2 = h2 * h1 := hρinj (by rw [map_mul, map_mul]; exact h3)
        exact congrArg (fun z : ↥H => (z : 𝔾)) h4
      · rintro _ ⟨h, hh, rfl⟩
        have h3 : ρ (h ^ p) = 1 := by rw [map_pow]; exact hA'el.2 _ hh
        have h4 : h ^ p = 1 := hρinj (by rw [h3, map_one])
        exact congrArg Subtype.val h4
    have hcomm : ∀ (a : ↥Ã) (k : ↥K₀), Commute (Ã.subtype a) (K₀.subtype k) := fun a k =>
      (hK₀comm k k.2 a (hÃH a a.2)).symm
    set Φ := MonoidHom.noncommCoprod Ã.subtype K₀.subtype hcomm with hΦ
    have hΦapp : ∀ (a : ↥Ã) (k : ↥K₀), Φ (a, k) = (a : 𝔾) * k := fun a k => rfl
    have hΦinj : Function.Injective Φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨a, k⟩ h1
      rw [hΦapp] at h1
      obtain ⟨b, hb, hbk⟩ := k.2
      have hak : (a : 𝔾) = (k : 𝔾)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hbk' : (b : 𝔾) = k := hbk
      have hρa : ρ ⟨a, hÃH a a.2⟩ = 1 := by
        rw [← S.secX_eq_ρ hR₀]
        have : (⟨(a : 𝔾), hHN _ (hÃH a a.2)⟩ : ↥(S.X ⊓ i285_stab R₀)) =
            (⟨b, hBN' b.2⟩)⁻¹ := Subtype.ext (by rw [hak, ← hbk'] ; rfl)
        rw [this, map_inv]
        have : S.secX R₀ ⟨b, hBN' b.2⟩ = 1 := hb
        rw [this, inv_one]
      have h5 : (⟨a, hÃH a a.2⟩ : ↥H) = 1 := hρinj (by rw [hρa, map_one])
      have h6 : (a : 𝔾) = 1 := congrArg Subtype.val h5
      rw [h6, one_mul] at h1
      exact Prod.ext (Subtype.ext h6) (Subtype.ext h1)
    have hEX : Φ.range ≤ S.X := by
      rintro _ ⟨⟨a, k⟩, rfl⟩
      rw [hΦapp]
      exact S.X.mul_mem (S.H_le_X R₀ (hÃH a a.2)) (hBX (hK₀B k.2))
    have hEel : IsElemAbelian p Φ.range := by
      refine ⟨⟨⟨?_⟩⟩, ?_⟩
      · rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
        apply Subtype.ext
        show Φ x * Φ y = Φ y * Φ x
        rw [← map_mul, ← map_mul]
        congr 1
        exact Prod.ext (hÃel.1.1.comm x.1 y.1) (hK₀el.1.1.comm x.2 y.2)
      · rintro _ ⟨x, rfl⟩
        rw [← map_pow]
        have : x ^ p = 1 :=
          Prod.ext (Subtype.ext (hÃel.2 x.1 x.1.2)) (Subtype.ext (hK₀el.2 x.2 x.2.2))
        rw [this, map_one]
    have h7 := hmax Φ.range hEX hEel
    have h8 : Nat.card (↥Ã × ↥K₀) ≤ Nat.card Φ.range :=
      Nat.card_le_card_of_injective Φ.rangeRestrict (by
        intro x y hxy
        exact hΦinj (congrArg Subtype.val hxy))
    rw [Nat.card_prod] at h8
    have h9 := Subgroup.card_ker_mul_card_range σ₀
    have h10 : Nat.card K₀ = Nat.card σ₀.ker := by
      rw [hK₀, Subgroup.card_map_of_injective B.subtype_injective]
    have hpos : 0 < Nat.card K₀ := Nat.card_pos
    rw [← h10] at h9
    have h11 : Nat.card Ã * Nat.card K₀ ≤ Nat.card σ₀.range * Nat.card K₀ := by
      calc Nat.card Ã * Nat.card K₀ ≤ Nat.card Φ.range := h8
        _ ≤ Nat.card B := h7
        _ = Nat.card σ₀.range * Nat.card K₀ := by rw [← h9, mul_comm]
    rw [← hÃcard]
    exact Nat.le_of_mul_le_mul_right h11 hpos
  have hτH : S.τ ∈ H := Subgroup.subset_closure hτ
  obtain ⟨y', hy'G, E', hE'A, hcard, hcomm⟩ := hC _ _ hG p hp hp2 _
    ⟨hAG, hAel, hAmax⟩ (ρ ⟨S.τ, hτH⟩) ⟨_, rfl⟩ (S.ρ_transvection hR₀ hτ)
  obtain ⟨y, rfl⟩ := hy'G
  refine ⟨(y : 𝔾), y.2, (E'.comap σ₀).map B.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  ·
    have hC : Nat.card ((E'.comap σ₀).map B.subtype) = Nat.card (E'.comap σ₀) :=
      Subgroup.card_map_of_injective B.subtype_injective
    rw [hC]
    set f := σ₀.rangeRestrict with hf
    set E'' := E'.subgroupOf σ₀.range with hE''
    have hcomapeq : E''.comap f = E'.comap σ₀ := by
      ext b
      simp [hE'', hf, Subgroup.mem_subgroupOf]
    have hidx := Subgroup.index_comap_of_surjective (H := E'') (f := f)
      (MonoidHom.rangeRestrict_surjective σ₀)
    have h1 := Subgroup.card_mul_index (E''.comap f)
    have h2 := Subgroup.card_mul_index E''
    have h3 : Nat.card E'' = Nat.card E' := by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'A).toEquiv
    rw [hcomapeq] at h1 hidx
    rw [h3] at h2
    have hpos : 0 < Nat.card E' := Nat.card_pos
    have h4 : Nat.card B * Nat.card E' = Nat.card (E'.comap σ₀) * Nat.card σ₀.range := by
      calc Nat.card B * Nat.card E' = (Nat.card (E'.comap σ₀) * (E'.comap σ₀).index) * Nat.card E' := by
            rw [h1]
        _ = Nat.card (E'.comap σ₀) * (Nat.card E' * E''.index) := by rw [hidx]; ring
        _ = Nat.card (E'.comap σ₀) * Nat.card σ₀.range := by rw [h2]
    have h5 : Nat.card B * Nat.card E' ≤ (p * Nat.card (E'.comap σ₀)) * Nat.card E' := by
      calc Nat.card B * Nat.card E' = Nat.card (E'.comap σ₀) * Nat.card σ₀.range := h4
        _ ≤ Nat.card (E'.comap σ₀) * (p * Nat.card E') := Nat.mul_le_mul_left _ hcard
        _ = (p * Nat.card (E'.comap σ₀)) * Nat.card E' := by ring
    exact Nat.le_of_mul_le_mul_right h5 hpos
  ·
    rintro _ ⟨b, hb, rfl⟩
    set h : ↥H := y⁻¹ * ⟨S.τ, hτH⟩ * y with hhdef
    have hhcoe : ((h : ↥H) : 𝔾) = (y : 𝔾)⁻¹ * S.τ * y := rfl
    have hρh : ρ h = (ρ y)⁻¹ * ρ ⟨S.τ, hτH⟩ * ρ y := by
      rw [hhdef, map_mul, map_mul, map_inv]
    have hc := hcomm (σ₀ b) hb
    rw [← hρh] at hc
    have h1 := hσρ b h
    have h2 : σ₀ b * ρ h * (σ₀ b)⁻¹ = ρ h := by
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [h2] at h1
    have h3 := congrArg (fun z : ↥H => (z : 𝔾)) (hρinj h1.symm)
    show (b : 𝔾) * ((y : 𝔾)⁻¹ * S.τ * y) = ((y : 𝔾)⁻¹ * S.τ * y) * b
    have h4 : (b : 𝔾) * (h : 𝔾) * (b : 𝔾)⁻¹ = h := h3
    rw [hhcoe] at h4
    calc (b : 𝔾) * ((y : 𝔾)⁻¹ * S.τ * y) = ((b : 𝔾) * ((y : 𝔾)⁻¹ * S.τ * y) * (b : 𝔾)⁻¹) * b := by group
      _ = _ := by rw [h4]


end Main
section Ident

variable [Finite M]

omit [Finite M] in
theorem i285_D_ne_one (S : i285_Setup M) {d : 𝔾} (hd : d ∈ S.D) : d ≠ 1 := by
  obtain ⟨g, hg, rfl⟩ := hd
  intro h
  apply S.τ_ne_one
  calc S.τ = g * (g⁻¹ * S.τ * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem i285_ident (S : i285_Setup M) {r : ℕ} {W : Fin (r + 1) → Subgroup 𝔾}
    (hW : i285_Decomp S.X S.τ r W) :
    ∃ R₀ : Submodule (ZMod 2) M, S.IsMin R₀ ∧ S.τ ∈ S.T R₀ ∧ W 0 = S.H R₀ := by
  have hfac : ∀ R : Submodule (ZMod 2) M, S.IsMin R → ∃ j, S.T R ⊆ (W j : Set 𝔾) :=
    fun R hR => i285_T_subset_factor S hW hR
  have hgen := i285_factor_eq_closure S hW
  have hinf : ∀ i j, i ≠ j → W i ⊓ W j = ⊥ := by
    intro i j hij
    rw [eq_bot_iff]
    refine (inf_le_inf_left _ (le_iSup (fun k : {k // k ≠ i} => W k) ⟨j, hij.symm⟩)).trans
      (hW.2.2.2.1 i).le
  have hsame : ∀ {d : 𝔾} {i j : Fin (r + 1)}, d ∈ S.D → d ∈ W i → d ∈ W j → i = j := by
    intro d i j hd hi hj
    by_contra hne
    have : d ∈ W i ⊓ W j := ⟨hi, hj⟩
    rw [hinf i j hne] at this
    exact i285_D_ne_one S hd (Subgroup.mem_bot.1 this)
  obtain ⟨R₁, hR₁⟩ := S.exists_isMin
  obtain ⟨x₀, hx₀, hτ₀⟩ := S.exists_mem_T hR₁ S.τ_mem_D
  have hR₀ := S.isMin_map hR₁ hx₀
  have hτW : S.τ ∈ W 0 := hW.2.2.2.2.2.2.1
  obtain ⟨j₀, hj₀⟩ := hfac _ hR₀
  have hj₀0 : j₀ = 0 := hsame S.τ_mem_D (hj₀ hτ₀) hτW
  subst hj₀0
  refine ⟨_, hR₀, hτ₀, le_antisymm ?_ ?_⟩
  · rw [hgen 0]
    refine (Subgroup.closure_le _).2 ?_
    rintro d ⟨hdD, hdW⟩
    obtain ⟨x, hx, hdx⟩ := S.exists_mem_T hR₁ hdD
    have hR' := S.isMin_map hR₁ hx
    obtain ⟨j, hj⟩ := hfac _ hR'
    have hj0 : j = 0 := hsame hdD (hj hdx) hdW
    subst hj0
    by_cases hne : R₁.map (x : M →ₗ[ZMod 2] M) = R₁.map (x₀ : M →ₗ[ZMod 2] M)
    · rw [hne] at hdx
      exact Subgroup.subset_closure hdx
    · exact (i285_not_two_blocks (fun _ _ h hs => mcl_solvable_card h hs) S hW hgen hfac hR₀ hR' (Ne.symm hne) 0 hj₀ hj).elim
  · exact (Subgroup.closure_le _).2 hj₀

theorem i285_conc (hN : TvNormalizer) (hC : TvCentralized) (S : i285_Setup M) {r : ℕ}
    {W : Fin (r + 1) → Subgroup 𝔾} (hW : i285_Decomp S.X S.τ r W) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B : Subgroup 𝔾} (hBX : B ≤ S.X) (hBel : IsElemAbelian p B)
    (hmax : ∀ B' : Subgroup 𝔾, B' ≤ S.X → IsElemAbelian p B' → Nat.card B' ≤ Nat.card B)
    (hBW : B ≤ Subgroup.normalizer (W 0 : Set 𝔾)) :
    ∃ y ∈ W 0, ∃ Q ≤ B, Nat.card B ≤ p * Nat.card Q ∧
      ∀ q ∈ Q, q * (y⁻¹ * S.τ * y) = (y⁻¹ * S.τ * y) * q := by
  obtain ⟨R₀, hR₀, hτ, hW0⟩ := i285_ident S hW
  rw [hW0] at hBW ⊢
  exact i285_main_H hN hC S hR₀ hτ hp hp2 hBX hBel hmax hBW

end Ident

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator
