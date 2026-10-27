module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.RankThree.PartOne.Sec66T (fixSub fixSubEquiv fixSub_congr mem_innerAut_congr)

@[expose] def OuterFixedWitness (X : Type) [Group X] : Prop :=
  ∀ ψ : MulAut X, ψ ^ 3 = 1 → ψ ∉ CFSG.RankThree.PartOne.Sec66T.innerAut X →
    ThreeTwoWitness ↥(fixSub ψ)

theorem OuterFixedWitness.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : OuterFixedWitness Y) : OuterFixedWitness X := by
  intro ψ hψ3 hψi
  have h3 : MulAut.congr e ψ ^ 3 = 1 := by
    rw [← map_pow, hψ3, map_one]
  have hi : MulAut.congr e ψ ∉ CFSG.RankThree.PartOne.Sec66T.innerAut Y :=
    fun hh => hψi ((mem_innerAut_congr e ψ).1 hh)
  exact (h _ h3 hi).of_mulEquiv (fixSubEquiv e ψ).symm

theorem exists_not_inner_of_pRank_one {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (hm : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1)
    (H : Subgroup (MulAut X)) (hH : IsElemAbelian 3 H) (hc : Nat.card H = 9) :
    ∃ ψ ∈ H, ψ ∉ CFSG.RankThree.PartOne.Sec66T.innerAut X := by
  by_contra hcon
  push Not at hcon
  have hle : H ≤ CFSG.RankThree.PartOne.Sec66T.innerAut X := fun ψ hψ => hcon ψ hψ
  have h2 : 2 ≤ CFSG.Open.pRank 3 (CFSG.RankThree.PartOne.Sec66T.innerAut X) :=
    CFSG.SectionRank.le_pRank (by norm_num) hle hH (k := 2) (by rw [hc]; norm_num)
  have h3 : CFSG.Open.pRank 3 (CFSG.RankThree.PartOne.Sec66T.innerAut X) =
      CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (innerAutEquiv hZ)).symm
  omega

theorem mem_normalizer_map_of_mem {F X : Type} [Group F] [Group X] (ι : F →* X)
    {P : Subgroup F} {x : F}
    (hx : x ∈ Subgroup.normalizer (P : Set F)) :
    ι x ∈ Subgroup.normalizer ((P.map ι : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨x * y * x⁻¹, (hx y).1 hy, by simp⟩
  · rintro ⟨y, hy, hyg⟩
    refine ⟨x⁻¹ * y * x, (hx _).2 (by simpa [mul_assoc] using hy), ?_⟩
    have h1 : h = (ι x)⁻¹ * (ι x * h * (ι x)⁻¹) * ι x := by group
    rw [h1, ← hyg]
    simp

theorem fieldBonus_of_outerFixedWitness {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (hm : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1)
    (hw : GLATwoLocalRank 3 X = 1) (hO : OuterFixedWitness X)
    (H : Subgroup (MulAut X)) (hH : IsElemAbelian 3 H) (hc : Nat.card H = 9) :
    FieldBonus X 3 H := by
  obtain ⟨ψ, hψH, hψi⟩ := exists_not_inner_of_pRank_one hZ hm H hH hc
  have hψ3 : ψ ^ 3 = 1 := by
    exact hH.2 ψ hψH
  obtain ⟨P, hP, hP2, x, hx, hxN⟩ := hO ψ hψ3 hψi
  set ι : ↥(fixSub ψ) →* X := (fixSub ψ).subtype
  have hιinj : Function.Injective ι := (fixSub ψ).subtype_injective
  have hfix : ∀ y : ↥(fixSub ψ), ψ (ι y) = ι y := fun y => y.2
  have hx3 : (ι x) ^ 3 = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hxo : orderOf (ι x) = 3 := by
    rw [← hx]
    exact orderOf_injective ι hιinj x
  refine ⟨ψ, hψH, fun hin => hψi ?_, P.map ι, ?_, hP2.map ι, ?_, Subgroup.zpowers (ι x),
    Subgroup.zpowers (ι x), ⟨inferInstance, ?_⟩, ⟨inferInstance, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := hin
    exact ⟨g, MulEquiv.ext fun t => by simpa [MulAut.conj_apply] using (hg t).symm⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective P hιinj]
  · ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [show (ψ.toMonoidHom (ι z)) = ι z from hfix z]
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨ι z, ⟨z, hz, rfl⟩, hfix z⟩
  · intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  · intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  · rw [Subgroup.zpowers_le]
    exact mem_normalizer_map_of_mem ι hxN
  · rw [Nat.card_zpowers, hxo, hw, pow_one]
  · rw [Nat.card_zpowers, hxo, hm, pow_one]
  · intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    rw [map_zpow, hfix]
  · intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    rw [map_zpow, hfix]

@[expose] def FBCore (L : Type) [Group L] [Finite L] (p : ℕ) (ψ : MulAut L) : Prop :=
  ∃ T : Subgroup L, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T.map ψ.toMonoidHom = T ∧
    ∃ E₁ E₂ : Subgroup L, IsElemAbelian p E₁ ∧ IsElemAbelian p E₂ ∧
      E₁ ≤ Subgroup.normalizer (T : Set L) ∧
      Nat.card E₁ = p ^ GLATwoLocalRank p L ∧
      Nat.card E₂ = p ^ CFSG.Open.pRank p (⊤ : Subgroup L) ∧
      (∀ e ∈ E₁, ψ e = e) ∧ (∀ e ∈ E₂, ψ e = e)

theorem fieldBonus_of_fbCore {L : Type} [Group L] [Finite L] {p : ℕ}
    {H : Subgroup (MulAut L)} {ψ : MulAut L} (hψ : ψ ∈ H) (hni : ¬ IsInnerAut ψ)
    (h : FBCore L p ψ) : FieldBonus L p H := ⟨ψ, hψ, hni, h⟩

theorem FBCore.conj {L : Type} [Group L] [Finite L] {p : ℕ} {ψ : MulAut L} (u : MulAut L)
    (h : FBCore L p ψ) : FBCore L p (u * ψ * u⁻¹) := by
  obtain ⟨T, hT, hT2, hTinv, E₁, E₂, ha1, ha2, hn, hc1, hc2, hf1, hf2⟩ := h
  have hfix : ∀ e : L, ψ e = e → (u * ψ * u⁻¹) (u e) = u e := fun e he => by
    show u (ψ (u⁻¹ (u e))) = u e
    rw [MulAut.inv_apply, MulEquiv.symm_apply_apply, he]
  refine ⟨T.map u.toMonoidHom, ?_, hT2.map u.toMonoidHom, ?_, E₁.map u.toMonoidHom,
    E₂.map u.toMonoidHom, isElemAbelian_map u ha1, isElemAbelian_map u ha2, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective T u.injective]
  · ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have : (u * ψ * u⁻¹).toMonoidHom (u.toMonoidHom z) = u (ψ z) := by
        show u (ψ (u⁻¹ (u z))) = u (ψ z)
        rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rw [this]
      have hz' : ψ z ∈ T := by
        have : ψ z ∈ T.map ψ.toMonoidHom := ⟨z, hz, rfl⟩
        rwa [hTinv] at this
      exact ⟨ψ z, hz', rfl⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ∈ T.map ψ.toMonoidHom := by rwa [hTinv]
      obtain ⟨w, hw, rfl⟩ := hz'
      refine ⟨u w, ⟨w, hw, rfl⟩, ?_⟩
      show u (ψ (u⁻¹ (u w))) = u (ψ w)
      rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    rw [← normalizer_map_mulEquiv u T]
    exact Subgroup.mem_map.2 ⟨y', hn hy', rfl⟩
  · rw [Subgroup.card_map_of_injective u.injective, hc1]
  · rw [Subgroup.card_map_of_injective u.injective, hc2]
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    exact hfix x' (hf1 x' hx')
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    exact hfix x' (hf2 x' hx')

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
