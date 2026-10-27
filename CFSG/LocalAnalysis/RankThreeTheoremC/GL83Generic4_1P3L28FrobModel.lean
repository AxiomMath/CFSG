module

public import CFSG.Quasithin.Background.F6ResL28
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.Quasithin
open CFSG.Quasithin.F6.L28Res (G8 T8 tdet ga gb uHom uHom_injective frob frobF
  frobF_frobF_frobF frob_not_inner eq_one_of_commute card_G8 card_mulAut)

@[expose] def l28mRep (a : GF8) : G8 := ⟨(a, 1, 1, 0), by simp [tdet]⟩

@[expose] def l28mReps : List G8 := 1 :: (List.range 8).map fun i => l28mRep (GF8.ofNat' i)

theorem l28m_frob_check : ∀ g : G8, g * frobF g * frobF (frobF g) = 1 →
    ∃ x ∈ l28mReps, ((x⁻¹ * g * frobF x : G8) : T8).2.2.1 = 0 := by
  decide +kernel

theorem l28m_norm_check : ∀ b : G8, ((b : G8) : T8).2.2.1 = 0 → ∀ t : GF8,
    ((b * uHom (Multiplicative.ofAdd t) * b⁻¹ : G8) : T8).1 = 1 ∧
    ((b * uHom (Multiplicative.ofAdd t) * b⁻¹ : G8) : T8).2.2.1 = 0 ∧
    ((b * uHom (Multiplicative.ofAdd t) * b⁻¹ : G8) : T8).2.2.2 = 1 := by
  decide +kernel

theorem l28m_frob_unip : ∀ t : GF8,
    frobF (uHom (Multiplicative.ofAdd t)) = uHom (Multiplicative.ofAdd (t * t)) := by
  decide +kernel

@[expose] def l28mUnip : Subgroup G8 := uHom.range

theorem l28mUnip_card : Nat.card l28mUnip = 8 := by
  rw [l28mUnip, MonoidHom.range_eq_map, Subgroup.card_map_of_injective uHom_injective,
    Subgroup.card_top, Nat.card_congr (Multiplicative.toAdd : Multiplicative GF8 ≃ GF8),
    Nat.card_eq_fintype_card]
  rfl

theorem l28mUnip_mem {y : G8} (h1 : ((y : G8) : T8).1 = 1) (h2 : ((y : G8) : T8).2.2.1 = 0)
    (h3 : ((y : G8) : T8).2.2.2 = 1) : y ∈ l28mUnip := by
  refine ⟨Multiplicative.ofAdd ((y : T8).2.1), Subtype.ext ?_⟩
  obtain ⟨⟨a, b, c, d⟩, hy⟩ := y
  simp only at h1 h2 h3 ⊢
  subst h1 h2 h3
  rfl

theorem l28m_unip_normalized {b : G8} (hb : ((b : G8) : T8).2.2.1 = 0) {u : G8}
    (hu : u ∈ l28mUnip) : b * u * b⁻¹ ∈ l28mUnip := by
  obtain ⟨t, rfl⟩ := hu
  obtain ⟨h1, h2, h3⟩ := l28m_norm_check b hb t.toAdd
  exact l28mUnip_mem h1 h2 h3

theorem l28m_frobF_mem_unip {u : G8} (hu : u ∈ l28mUnip) : frobF u ∈ l28mUnip := by
  obtain ⟨t, rfl⟩ := hu
  rw [show t = Multiplicative.ofAdd t.toAdd from rfl, l28m_frob_unip]
  exact ⟨_, rfl⟩

private theorem frobF_mul' (a b : G8) : frobF (a * b) = frobF a * frobF b := map_mul frob a b

private theorem frobF_inv' (a : G8) : frobF a⁻¹ = (frobF a)⁻¹ := map_inv frob a

theorem l28m_frob_invariant {g : G8} (hg : g * frobF g * frobF (frobF g) = 1) :
    ∃ U : Subgroup G8, IsPGroup 2 U ∧ Nat.card U = 8 ∧
      U.map (MulAut.conj g * frob).toMonoidHom = U := by
  obtain ⟨x, -, hx⟩ := l28m_frob_check g hg
  have hcard : Nat.card (l28mUnip.map (MulAut.conj x).toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, l28mUnip_card]
  refine ⟨l28mUnip.map (MulAut.conj x).toMonoidHom,
    IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num), hcard, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    have hb := l28m_unip_normalized hx (l28m_frobF_mem_unip hu)
    refine Subgroup.mem_map.mpr ⟨_, hb, ?_⟩
    show x * ((x⁻¹ * g * frobF x) * frobF u * (x⁻¹ * g * frobF x)⁻¹) * x⁻¹ =
      g * frobF (x * u * x⁻¹) * g⁻¹
    rw [frobF_mul', frobF_mul', frobF_inv']
    group
  · exact (Subgroup.card_map_of_injective (f := (MulAut.conj g * frob).toMonoidHom)
      (MulAut.conj g * frob).injective).ge

theorem l28m_cocycle {g : G8} (h : (MulAut.conj g * frob) ^ 3 = 1) :
    g * frobF g * frobF (frobF g) = 1 := by
  have h3 : ∀ x : G8, (MulAut.conj g * frob) ((MulAut.conj g * frob) ((MulAut.conj g * frob) x)) =
      x := by
    intro x
    have := congrArg (fun γ : MulAut G8 => γ x) h
    simpa [pow_succ, MulAut.mul_apply] using this
  have hz : ∀ x : G8, (MulAut.conj g * frob) ((MulAut.conj g * frob) ((MulAut.conj g * frob) x)) =
      (g * frobF g * frobF (frobF g)) * x * (g * frobF g * frobF (frobF g))⁻¹ := by
    intro x
    have hβ : ∀ y : G8, (MulAut.conj g * frob) y = g * frobF y * g⁻¹ := fun y => rfl
    rw [hβ, hβ, hβ]
    simp only [frobF_mul', frobF_inv']
    rw [frobF_frobF_frobF]
    group
  have hcomm : ∀ y : G8, (g * frobF g * frobF (frobF g)) * y =
      y * (g * frobF g * frobF (frobF g)) := by
    intro y
    exact mul_inv_eq_iff_eq_mul.mp ((hz y).symm.trans (h3 y))
  exact eq_one_of_commute _ (hcomm ga) (hcomm gb)

private theorem frob_not_conj : ∀ g : G8, MulAut.conj g ≠ frob := by
  intro g h
  obtain ⟨h1, -⟩ := frob_not_inner g
  refine h1 ⟨?_, ?_⟩
  · rw [← MulAut.conj_apply, h]
    rfl
  · rw [← MulAut.conj_apply, h]
    rfl

private theorem map_inv_eq_of_map_eq {G : Type*} [Group G] {U : Subgroup G} {β : MulAut G}
    (h : U.map β.toMonoidHom = U) : U.map β⁻¹.toMonoidHom = U := by
  ext y
  rw [Subgroup.mem_map_equiv]
  have h1 := (Subgroup.ext_iff.mp h (β y)).symm
  rw [Subgroup.mem_map_equiv] at h1
  have h2 : (β⁻¹).symm = β := rfl
  rw [h2]
  simpa using h1

theorem l28m_outer_three_invariant {α : MulAut G8} (hα3 : orderOf α = 3)
    (hα : ∀ g : G8, MulAut.conj g ≠ α) :
    ∃ U : Subgroup G8, IsPGroup 2 U ∧ Nat.card U = 8 ∧ U.map α.toMonoidHom = U := by
  have hZ : ∀ x : G8, (∀ y : G8, x * y = y * x) → x = 1 := fun x hx =>
    eq_one_of_commute x (hx ga) (hx gb)
  have hA : Nat.card (MulAut G8) = 3 * Nat.card G8 := by rw [card_mulAut, card_G8]
  have key : ∀ β : MulAut G8, β ^ 3 = 1 → ∀ g : G8, β = MulAut.conj g * frob →
      ∃ U : Subgroup G8, IsPGroup 2 U ∧ Nat.card U = 8 ∧ U.map β.toMonoidHom = U := by
    intro β hβ3 g hβ
    subst hβ
    exact l28m_frob_invariant (l28m_cocycle hβ3)
  have hα3' : α ^ 3 = 1 := hα3 ▸ pow_orderOf_eq_one α
  rcases l28m_exists_conj_mul_of_outer hZ hA frob_not_conj hα with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact key α hα3' g hg
  · obtain ⟨U, h2, h8, hU⟩ := key α⁻¹ (by rw [inv_pow, hα3', inv_one]) g hg
    refine ⟨U, h2, h8, ?_⟩
    have := map_inv_eq_of_map_eq hU
    simpa using this

end CFSG.LocalAnalysis.RankThreeTheoremC
