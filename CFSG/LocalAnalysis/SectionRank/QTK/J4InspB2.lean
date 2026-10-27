module

public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA2

public section

namespace CFSG.SectionRank.QTK

theorem faithful_not_forall_apply_apply {V : Type} [CommGroup V] {X : Subgroup (MulAut V)}
    (hX : CFSG.Quasithin.IsPSL 3 2 2 ↥X) :
    ¬ ∀ x : ↥X, ∀ v : V, (x : MulAut V) ((x : MulAut V) v) = v := by
  intro hall
  have hcard : Nat.card ↥X = 20160 := CFSG.Quasithin.H13.A5.card_of_isPSL34 hX
  haveI : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 (by rw [hcard]; norm_num)
  have hsq : g * g = 1 := Subtype.ext (MulEquiv.ext fun v => hall g v)
  have h3 : g ^ 3 = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have e3 : g ^ 3 = g := by rw [pow_three, hsq, mul_one]
  have hg1 : g = 1 := e3.symm.trans h3
  rw [hg1, orderOf_one] at hg
  norm_num at hg

theorem faithful_apply_apply_of_trivial {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1)
    (W : Subgroup V) (x : MulAut V) (h1 : ∀ w ∈ W, x w = w)
    (h2 : ∀ v : V, (QuotientGroup.mk (x v) : V ⧸ W) = QuotientGroup.mk v) (v : V) :
    x (x v) = v := by
  obtain ⟨u, hu⟩ : ∃ u : V, u = (x v)⁻¹ * v := ⟨_, rfl⟩
  have huW : u ∈ W := by
    rw [hu]
    exact QuotientGroup.eq.mp (h2 v)
  have hxv : x v = v * u⁻¹ := by
    rw [hu, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  have hu2 : u⁻¹ * u⁻¹ = 1 := by
    have := hV u⁻¹
    rwa [pow_two] at this
  calc x (x v) = x (v * u⁻¹) := by rw [← hxv]
    _ = x v * x u⁻¹ := map_mul x v u⁻¹
    _ = x v * u⁻¹ := by rw [h1 u⁻¹ (W.inv_mem huW)]
    _ = v * u⁻¹ * u⁻¹ := by rw [hxv]
    _ = v * (u⁻¹ * u⁻¹) := mul_assoc _ _ _
    _ = v := by rw [hu2, mul_one]

noncomputable def faithful_restrictAut {V : Type} [CommGroup V] (e : MulAut V) (W : Subgroup V)
    (h1 : ∀ w ∈ W, e w ∈ W) (h2 : ∀ w ∈ W, e⁻¹ w ∈ W) : MulAut ↥W where
  toFun w := ⟨e (w : V), h1 (w : V) w.2⟩
  invFun w := ⟨e⁻¹ (w : V), h2 (w : V) w.2⟩
  left_inv w := Subtype.ext (by simp [MulAut.inv_apply])
  right_inv w := Subtype.ext (by simp [MulAut.inv_apply])
  map_mul' a b := Subtype.ext (map_mul e (a : V) (b : V))

noncomputable def faithful_restrictHom {V : Type} [CommGroup V] (X : Subgroup (MulAut V))
    (W : Subgroup V) (hW : CFSG.Quasithin.XMod.IsInv ↥X W) : X →* MulAut ↥W :=
  MonoidHom.mk'
    (fun x => faithful_restrictAut (x : MulAut V) W (fun w hw => hW x w hw)
      (fun w hw => hW x⁻¹ w hw))
    (fun a b => MulEquiv.ext fun w => Subtype.ext rfl)

theorem faithful_map_eq {V : Type} [CommGroup V] (X : Subgroup (MulAut V)) (W : Subgroup V)
    (hW : CFSG.Quasithin.XMod.IsInv ↥X W) (x : ↥X) :
    W.map ((x : MulAut V) : V →* V) = W := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr fun w hw => hW x w hw
  · intro w hw
    refine Subgroup.mem_map.mpr ⟨(x⁻¹ : ↥X) • w, hW x⁻¹ w hw, ?_⟩
    show (x : MulAut V) (((x : MulAut V))⁻¹ w) = w
    rw [MulAut.inv_apply]
    exact MulEquiv.apply_symm_apply _ w

noncomputable def faithful_quotHom {V : Type} [CommGroup V] (X : Subgroup (MulAut V))
    (W : Subgroup V) (hW : CFSG.Quasithin.XMod.IsInv ↥X W) : X →* MulAut (V ⧸ W) :=
  MonoidHom.mk'
    (fun x => QuotientGroup.congr W W (x : MulAut V) (faithful_map_eq X W hW x))
    (fun a b => MulEquiv.ext fun q => QuotientGroup.induction_on q fun v => rfl)

theorem faithful_injective_or_eq_one {X Y : Type} [Group X] [IsSimpleGroup X] [Group Y]
    (φ : X →* Y) : Function.Injective φ ∨ ∀ x, φ x = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · exact Or.inl ((MonoidHom.ker_eq_bot_iff φ).mp h)
  · refine Or.inr fun x => MonoidHom.mem_ker.mp ?_
    rw [h]
    exact Subgroup.mem_top x

theorem faithfulL34ModDim_aux (n : ℕ) :
    ∀ (V : Type) [CommGroup V] [Finite V], Nat.card V = n → (∀ v : V, v ^ 2 = 1) →
      ∀ X : Subgroup (MulAut V), CFSG.Quasithin.IsPSL 3 2 2 ↥X → 2 ^ 9 ≤ Nat.card V := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ hn hV X hX
  haveI : IsSimpleGroup ↥X := CFSG.Quasithin.H13.A5.isSimpleGroup_of_isPSL34 hX
  by_cases hlt : (⊥ : Subgroup V) < ⊤
  · by_cases hirr : CFSG.Quasithin.XMod.IsIrrSec ↥X (⊥ : Subgroup V) ⊤
    · exact two_pow_nine_le_of_irreducible' V hV X hX hirr
    obtain ⟨W, hW, hWbot, hWtop⟩ :
        ∃ W : Subgroup V, CFSG.Quasithin.XMod.IsInv ↥X W ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra hcon
      apply hirr
      unfold CFSG.Quasithin.XMod.IsIrrSec
      refine ⟨hlt, fun J hJ _ _ => ?_⟩
      by_contra hne
      push Not at hne
      exact hcon ⟨J, hJ, hne.1, hne.2⟩
    have hidx1 : W.index ≠ 1 := fun h => hWtop (Subgroup.index_eq_one.mp h)
    have hidx0 : W.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hmul : Nat.card W * W.index = Nat.card V := Subgroup.card_mul_index W
    have hcardW : 1 < Nat.card W := (Subgroup.one_lt_card_iff_ne_bot W).mpr hWbot
    have hcardpos : 0 < Nat.card W := Nat.card_pos
    have hidx2 : 2 ≤ W.index := by omega
    have hidxpos : 0 < W.index := by omega
    have hWlt : Nat.card W < n := by
      rw [← hn, ← hmul]
      nlinarith
    have hQlt : Nat.card (V ⧸ W) < n := by
      have hQeq : Nat.card (V ⧸ W) = W.index := rfl
      rw [← hn, ← hmul, hQeq]
      nlinarith
    have hWle : Nat.card W ≤ Nat.card V := by
      rw [hn]
      exact hWlt.le
    have hQle : Nat.card (V ⧸ W) ≤ Nat.card V := by
      rw [hn]
      exact hQlt.le
    by_cases hρ : ∀ x : ↥X, ∀ w ∈ W, (x : MulAut V) w = w
    · by_cases hσ : ∀ x : ↥X, ∀ v : V,
          (QuotientGroup.mk ((x : MulAut V) v) : V ⧸ W) = QuotientGroup.mk v
      ·
        exact (faithful_not_forall_apply_apply hX fun x v =>
          faithful_apply_apply_of_trivial hV W (x : MulAut V) (hρ x) (hσ x) v).elim
      ·
        push Not at hσ
        obtain ⟨x0, v0, hv0⟩ := hσ
        rcases faithful_injective_or_eq_one (faithful_quotHom X W hW) with hinj | htriv
        · have hexp : ∀ q : V ⧸ W, q ^ 2 = 1 := by
            intro q
            induction q using QuotientGroup.induction_on with
            | H v => rw [← QuotientGroup.mk_pow, hV v, QuotientGroup.mk_one]
          have hPSL : CFSG.Quasithin.IsPSL 3 2 2 ↥(faithful_quotHom X W hW).range :=
            isPSL_of_mulEquiv (MonoidHom.ofInjective hinj) hX
          have h9 := ih (Nat.card (V ⧸ W)) hQlt (V ⧸ W) rfl hexp _ hPSL
          exact le_trans h9 hQle
        · have h := congrArg (fun g : MulAut (V ⧸ W) => g (QuotientGroup.mk v0))
            (htriv x0)
          exact (hv0 h).elim
    ·
      push Not at hρ
      obtain ⟨x0, w0, hw0, hxw0⟩ := hρ
      rcases faithful_injective_or_eq_one (faithful_restrictHom X W hW) with hinj | htriv
      · have hexp : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
        have hPSL : CFSG.Quasithin.IsPSL 3 2 2 ↥(faithful_restrictHom X W hW).range :=
          isPSL_of_mulEquiv (MonoidHom.ofInjective hinj) hX
        have h9 := ih (Nat.card W) hWlt ↥W rfl hexp _ hPSL
        exact le_trans h9 hWle
      · have h := congrArg (fun g : MulAut ↥W => ((g ⟨w0, hw0⟩ : ↥W) : V)) (htriv x0)
        exact (hxw0 h).elim
  ·
    exfalso
    have hsub : ∀ v : V, v = 1 := by
      intro v
      by_contra hv
      apply hlt
      refine lt_of_le_of_ne bot_le ?_
      intro h
      apply hv
      have hvtop : v ∈ (⊤ : Subgroup V) := Subgroup.mem_top v
      rw [← h] at hvtop
      exact Subgroup.mem_bot.mp hvtop
    haveI : Subsingleton V := ⟨fun a b => (hsub a).trans (hsub b).symm⟩
    exact faithful_not_forall_apply_apply hX fun _ _ => Subsingleton.elim _ _

theorem faithfulL34ModDim_holds : FaithfulL34ModDim := by
  intro V _ _ hV X hX
  exact faithfulL34ModDim_aux (Nat.card V) V rfl hV X hX

end CFSG.SectionRank.QTK
