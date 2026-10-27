module

public import CFSG.CGT.PushingUpLit.CGT6.EmbHyp

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.Quasithin
open scoped commutatorElement

section ConjClosure

variable {G : Type} [Group G]

@[expose] def conjClosure (Y Xt : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ g ∈ Xt, ∃ y ∈ Y, x = g * y * g⁻¹}

theorem mem_conjClosure_of_mem {Y Xt : Subgroup G} {g y : G} (hg : g ∈ Xt) (hy : y ∈ Y) :
    g * y * g⁻¹ ∈ conjClosure Y Xt :=
  Subgroup.subset_closure ⟨g, hg, y, hy, rfl⟩

theorem le_conjClosure {Y Xt : Subgroup G} : Y ≤ conjClosure Y Xt := fun y hy => by
  simpa using mem_conjClosure_of_mem (one_mem Xt) hy

theorem conjClosure_le {Y Xt : Subgroup G} (h : Y ≤ Xt) : conjClosure Y Xt ≤ Xt := by
  rw [conjClosure, Subgroup.closure_le]
  rintro _ ⟨g, hg, y, hy, rfl⟩
  exact Xt.mul_mem (Xt.mul_mem hg (h hy)) (Xt.inv_mem hg)

theorem le_normalizer_conjClosure {Y Xt : Subgroup G} :
    Xt ≤ Subgroup.normalizer (conjClosure Y Xt : Set G) := by
  have key : ∀ h ∈ Xt, ∀ x ∈ conjClosure Y Xt, h * x * h⁻¹ ∈ conjClosure Y Xt := by
    intro h hh x hx
    unfold conjClosure at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, hg, y, hy, rfl⟩ := hx
      refine Subgroup.subset_closure ⟨h * g, Xt.mul_mem hh hg, y, hy, ?_⟩
      group
    | one => simp
    | mul x y _ _ hx hy =>
      have : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  intro h hh
  exact mem_normalizer_of_conj_mem (key h hh) (fun x hx => by
    simpa using key h⁻¹ (Xt.inv_mem hh) x hx)

theorem map_conj_le_conjClosure {Y Xt : Subgroup G} {g : G} (hg : g ∈ Xt) :
    Y.map (MulAut.conj g).toMonoidHom ≤ conjClosure Y Xt := by
  rintro _ ⟨y, hy, rfl⟩
  simpa [MulAut.conj_apply] using mem_conjClosure_of_mem hg hy

theorem oResidualTwo_conjClosure [Finite G] {Y Xt : Subgroup G} (hY : SubTwo.NoTwoQuotient Y) :
    oResidualTwo ↥(conjClosure Y Xt) = ⊤ := by
  obtain ⟨X, hX⟩ : ∃ X, X = conjClosure Y Xt := ⟨_, rfl⟩
  rw [← hX, oResidualTwo_eq_top_iff]
  intro N hN hpow
  have hNX : X ≤ Subgroup.normalizer ((N.map X.subtype : Subgroup G) : Set G) := by
    have h1 : (⊤ : Subgroup ↥X).map X.subtype ≤
        Subgroup.normalizer ((N.map X.subtype : Subgroup G) : Set G) := by
      have := Subgroup.le_normalizer_map (H := N) X.subtype
      rwa [Subgroup.normalizer_eq_top N] at this
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  have hgen : X ≤ N.map X.subtype := by
    refine hX.le.trans ?_
    rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨g, hg, y, hy, rfl⟩
    have hFX : Y.map (MulAut.conj g).toMonoidHom ≤ X := by
      rw [hX]
      exact map_conj_le_conjClosure hg
    have hFno : SubTwo.NoTwoQuotient (Y.map (MulAut.conj g).toMonoidHom) :=
      noTwoQuotient_map_hom _ hY
    have hFle : Y.map (MulAut.conj g).toMonoidHom ≤ N.map X.subtype := by
      have h := hFno (N.map X.subtype ⊓ Y.map (MulAut.conj g).toMonoidHom) inf_le_right
        (le_trans (le_inf (hFX.trans hNX) Subgroup.le_normalizer)
          Subgroup.inf_normalizer_le_normalizer_inf) (fun f hf => by
          obtain ⟨k, hk⟩ := hpow ⟨f, hFX hf⟩
          exact ⟨k, ⟨⟨_, hk, by simp⟩, Subgroup.pow_mem _ hf _⟩⟩)
      rw [← h]
      exact inf_le_left
    exact hFle ⟨y, hy, by simp [MulAut.conj_apply]⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨z, hz, hzx⟩ := hgen x.2
  have : z = x := Subtype.ext hzx
  rwa [← this]

theorem commutator_conjClosure_eq_self {Y Xt : Subgroup G} (hY : ⁅Y, Y⁆ = Y) :
    ⁅conjClosure Y Xt, conjClosure Y Xt⁆ = conjClosure Y Xt := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  rw [conjClosure, Subgroup.closure_le]
  rintro _ ⟨g, hg, y, hy, rfl⟩
  have h1 : (g * y * g⁻¹) ∈ (⁅Y, Y⁆).map (MulAut.conj g).toMonoidHom :=
    ⟨y, by rw [hY]; exact hy, by simp [MulAut.conj_apply]⟩
  rw [Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono (map_conj_le_conjClosure hg) (map_conj_le_conjClosure hg) h1

theorem commutator_conjClosure_le {Y Xt M W : Subgroup G}
    (hW : conjClosure Y Xt ≤ Subgroup.normalizer (W : Set G))
    (h : ∀ g ∈ Xt, ∀ y ∈ Y, ∀ m ∈ M, ⁅m, g * y * g⁻¹⁆ ∈ W) :
    ⁅M, conjClosure Y Xt⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro m hm x hx
  have hx0 := hx
  unfold conjClosure at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, y, hy, rfl⟩ := hx
    exact h g hg y hy m hm
  | one => simp [W.one_mem]
  | mul x y hx' hy' ihx ihy =>
    have hxn : x ∈ Subgroup.normalizer (W : Set G) := hW hx'
    rw [commutatorElement_mul_right_eq_mul_conj]
    have : ⁅m, x⁆ * x * ⁅m, y⁆ * x⁻¹ = ⁅m, x⁆ * (x * ⁅m, y⁆ * x⁻¹) := by group
    rw [this]
    refine W.mul_mem (ihx hx') ?_
    exact (Subgroup.mem_normalizer_iff.mp hxn _).mp (ihy hy')
  | inv x hx' ihx =>
    have hxn : x⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ (hW hx')
    rw [commutatorElement_inv_right, ← commutatorElement_inv]
    have h2 : x⁻¹ * ⁅m, x⁆⁻¹ * x = x⁻¹ * ⁅m, x⁆⁻¹ * x⁻¹⁻¹ := by group
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.mp hxn _).mp (W.inv_mem (ihx hx'))

end ConjClosure

section Char

variable {G : Type} [Group G] [Finite G]

theorem isCharacteristicP_two_of_isSubnormal (hG : IsCharacteristicP 2 G) {X : Subgroup G}
    (hX : X.IsSubnormal) : IsCharacteristicP 2 ↥X := by
  have hiff : ∀ K : Subgroup G, CFSG.QuasithinUnique.CharTwo K → IsCharacteristicP 2 ↥K :=
    fun K hK => by
      unfold IsCharacteristicP
      exact CFSG.QuasithinUnique.charTwo_iff_internal.mp hK
  have key : ∀ K : Subgroup G, K.IsSubnormal → CFSG.QuasithinUnique.CharTwo K := by
    intro K hK
    induction hK with
    | top =>
      rw [CFSG.QuasithinUnique.charTwo_iff_internal]
      have h1 : Subgroup.centralizer (CFSG.Open.pCore 2 G : Set G) ≤ CFSG.Open.pCore 2 G := by
        have := hG
        unfold IsCharacteristicP at this
        assumption
      exact CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2
        Subgroup.topEquiv.symm h1
    | step H K hHK _ hN ih => exact CFSG.QuasithinUnique.CharTwo.of_normal ih hHK hN
  exact hiff X (key X hX)

theorem generalizedFitting_eq_pCore_of_isSubnormal (hG : IsCharacteristicP 2 G) {X : Subgroup G}
    (hX : X.IsSubnormal) : generalizedFitting ↥X = pCore 2 ↥X :=
  (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥X 2).mp
    (isCharacteristicP_two_of_isSubnormal hG hX)

end Char

end CFSG.CGT.PushingUpLit.CGT6
