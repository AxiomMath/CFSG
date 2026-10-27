module

public import CFSG.Fischer.Classification.PartII.O2Row
public import CFSG.Fischer.Classification.PartII.Herm.Graph

public noncomputable section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace O2Mod

variable {H : Type} [Group H] {E μ : Set H}

abbrev Fib (E μ : Set H) (s : H) := ↥(twinClass E s \ μ)

theorem sign_of_eq_one_or_forall_ne :
    ∀ σ : Equiv.Perm (Fin 3), (σ = 1 ∨ ∀ i, σ i ≠ i) → Equiv.Perm.sign σ = 1 := by
  decide

theorem commute_finRotate_of_sign :
    ∀ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 → σ * finRotate 3 = finRotate 3 * σ := by
  decide

theorem sign_swap_zero_one : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 := by decide

@[expose] def swapIf (b : ZMod 2) : Equiv.Perm (Fin 3) := by
  classical exact if b = 0 then 1 else Equiv.swap 0 1

theorem finRotate_three_ne : ∀ i : Fin 3, finRotate 3 i ≠ i := by decide

theorem finRotate_three_two_ne : ∀ i : Fin 3, finRotate 3 (finRotate 3 i) ≠ i := by decide

theorem finRotate_three_three : ∀ i : Fin 3, finRotate 3 (finRotate 3 (finRotate 3 i)) = i := by
  decide

namespace IsTwinSection

variable (hμ : IsTwinSection E μ) (hP : Pair H E) (h4 : ∀ a ∈ E, (twinClass E a).ncard = 4)
include hμ hP

omit hμ hP in
theorem fib_not_commute {s t : H} (f : Fib E μ s) (hst : s * t ≠ t * s) (ht : t ∈ E) :
    (f : H) * t ≠ t * f :=
  not_commute_of_isTwin f.2.1 ht hst

@[expose] def matchEquiv {s t : H} (hs : s ∈ E) (ht : t ∈ E) (hst : s * t ≠ t * s) :
    Fib E μ s ≃ Fib E μ t where
  toFun f := ⟨mate E μ f t, hμ.isTwin_mate hP f.2.1.2.1 f.2.2 ht (fib_not_commute f hst ht),
    hμ.mate_notMem hP f.2.1.2.1 f.2.2 ht (fib_not_commute f hst ht)⟩
  invFun g := ⟨mate E μ g s, hμ.isTwin_mate hP g.2.1.2.1 g.2.2 hs
      (fib_not_commute g (fun e => hst e.symm) hs),
    hμ.mate_notMem hP g.2.1.2.1 g.2.2 hs (fib_not_commute g (fun e => hst e.symm) hs)⟩
  left_inv f := by
    have hft := fib_not_commute f hst ht
    have hmE := hμ.mate_mem hP f.2.1.2.1 f.2.2 ht hft
    have hmμ := hμ.mate_notMem hP f.2.1.2.1 f.2.2 ht hft
    have hmf : mate E μ f t * f ≠ f * mate E μ f t := fun e =>
      hμ.mate_not_commute hP f.2.1.2.1 f.2.2 ht hft e.symm
    refine Subtype.ext ?_
    show mate E μ (mate E μ f t) s = f
    rw [hμ.mate_congr hP hmE hmμ f.2.1.2.1 hmf (isTwin_symm f.2.1),
      hμ.mate_mate hP f.2.1.2.1 f.2.2 ht hft]
  right_inv g := by
    have hgs := fib_not_commute g (fun e => hst e.symm) hs
    have hmE := hμ.mate_mem hP g.2.1.2.1 g.2.2 hs hgs
    have hmμ := hμ.mate_notMem hP g.2.1.2.1 g.2.2 hs hgs
    have hmg : mate E μ g s * g ≠ g * mate E μ g s := fun e =>
      hμ.mate_not_commute hP g.2.1.2.1 g.2.2 hs hgs e.symm
    refine Subtype.ext ?_
    show mate E μ (mate E μ g s) t = g
    rw [hμ.mate_congr hP hmE hmμ g.2.1.2.1 hmg (isTwin_symm g.2.1),
      hμ.mate_mate hP g.2.1.2.1 g.2.2 hs hgs]

theorem matchEquiv_apply {s t : H} (hs : s ∈ E) (ht : t ∈ E) (hst : s * t ≠ t * s)
    (f : Fib E μ s) : (hμ.matchEquiv hP hs ht hst f : H) = mate E μ f t := rfl

include h4

theorem card_fib {s : H} (hs : s ∈ E) : Nat.card (Fib E μ s) = 3 := by
  rw [Nat.card_coe_set_eq, hμ.ncard_twinClass_diff hP h4 hs]

@[expose] def refEquiv {s : H} (hs : s ∈ E) : Fib E μ s ≃ Fin 3 :=
  have := Pair.finite hP
  (Finite.equivFin (Fib E μ s)).trans (finCongr (hμ.card_fib hP h4 hs))

@[expose] def transPerm {s t : H} (hs : s ∈ E) (ht : t ∈ E) (hst : s * t ≠ t * s) :
    Equiv.Perm (Fin 3) :=
  (hμ.refEquiv hP h4 hs).symm.trans ((hμ.matchEquiv hP hs ht hst).trans (hμ.refEquiv hP h4 ht))

theorem transPerm_symm {s t : H} (hs : s ∈ E) (ht : t ∈ E) (hst : s * t ≠ t * s) :
    hμ.transPerm hP h4 ht hs (fun e => hst e.symm) = (hμ.transPerm hP h4 hs ht hst)⁻¹ := by
  ext i
  rfl

omit h4 in
theorem monodromy_eq_or_ne {s t u : H} (hs : s ∈ μ) (ht : t ∈ μ) (hu : u ∈ μ)
    (hst : s * t ≠ t * s) (htu : t * u ≠ u * t) (hus : u * s ≠ s * u) :
    ((hμ.matchEquiv hP (hμ.subset hs) (hμ.subset ht) hst).trans
        ((hμ.matchEquiv hP (hμ.subset ht) (hμ.subset hu) htu).trans
          (hμ.matchEquiv hP (hμ.subset hu) (hμ.subset hs) hus)) = Equiv.refl _) ∨
      ∀ f, (hμ.matchEquiv hP (hμ.subset hs) (hμ.subset ht) hst).trans
        ((hμ.matchEquiv hP (hμ.subset ht) (hμ.subset hu) htu).trans
          (hμ.matchEquiv hP (hμ.subset hu) (hμ.subset hs) hus)) f ≠ f := by
  have hsE := hμ.subset hs
  have htE := hμ.subset ht
  have huE := hμ.subset hu
  have hval : ∀ f : Fib E μ s,
      (((hμ.matchEquiv hP hsE htE hst).trans ((hμ.matchEquiv hP htE huE htu).trans
        (hμ.matchEquiv hP huE hsE hus)) f : Fib E μ s) : H) =
      mate E μ (mate E μ (mate E μ f t) u) f := by
    intro f
    have hfE := f.2.1.2.1
    have hft := fib_not_commute f hst htE
    have h1E := hμ.mate_mem hP hfE f.2.2 htE hft
    have h1μ := hμ.mate_notMem hP hfE f.2.2 htE hft
    have h1u : mate E μ f t * u ≠ u * mate E μ f t :=
      not_commute_of_isTwin (hμ.isTwin_mate hP hfE f.2.2 htE hft) huE htu
    have h2E := hμ.mate_mem hP h1E h1μ huE h1u
    have h2μ := hμ.mate_notMem hP h1E h1μ huE h1u
    have h2s : mate E μ (mate E μ f t) u * s ≠ s * mate E μ (mate E μ f t) u :=
      not_commute_of_isTwin (hμ.isTwin_mate hP h1E h1μ huE h1u) hsE hus
    exact (hμ.mate_congr hP h2E h2μ hsE h2s f.2.1).symm
  have hsts : IsTwin E (s * t * s) (s * t * s) := isTwin_refl (Pair.mul_mul_mem hP hsE htE)
  have hftf : ∀ f : Fib E μ s, IsTwin E (s * t * s) ((f : H) * t * f) := fun f =>
    Pair.isTwin_mul_mul hP f.2.1 htE hst
  by_cases hcol : u = s * t * s
  · left
    ext f
    rw [hval]
    have hft := fib_not_commute f hst htE
    exact hμ.mate_mate_mate_of_isTwin hP f.2.1.2.1 f.2.2 htE hft
      (by rw [hcol]; exact isTwin_symm (hftf f))
  have hfu : ∀ f : Fib E μ s, (f : H) * u ≠ u * f := fun f =>
    fib_not_commute f (fun e => hus e.symm) huE
  by_cases hc : u * (s * t * s) = s * t * s * u
  · left
    ext f
    rw [hval]
    have hft := fib_not_commute f hst htE
    exact hμ.mate_mate_mate_of_commute hP f.2.1.2.1 f.2.2 htE huE hft htu (hfu f)
      (((hftf f).2.2.2 u huE).1 hc)
  · right
    intro f e
    have hft := fib_not_commute f hst htE
    apply hμ.mate_mate_mate_ne_of_affine hP f.2.1.2.1 f.2.2 htE huE hft htu (hfu f)
      (fun h => hc (((hftf f).2.2.2 u huE).2 h))
    rw [← hval, e]

theorem sign_monodromy {s t u : H} (hs : s ∈ μ) (ht : t ∈ μ) (hu : u ∈ μ)
    (hst : s * t ≠ t * s) (htu : t * u ≠ u * t) (hus : u * s ≠ s * u) :
    Equiv.Perm.sign (hμ.transPerm hP h4 (hμ.subset hu) (hμ.subset hs) hus *
      hμ.transPerm hP h4 (hμ.subset ht) (hμ.subset hu) htu *
      hμ.transPerm hP h4 (hμ.subset hs) (hμ.subset ht) hst) = 1 := by
  apply sign_of_eq_one_or_forall_ne
  have hσ : ∀ i, (hμ.transPerm hP h4 (hμ.subset hu) (hμ.subset hs) hus *
      hμ.transPerm hP h4 (hμ.subset ht) (hμ.subset hu) htu *
      hμ.transPerm hP h4 (hμ.subset hs) (hμ.subset ht) hst) i =
      hμ.refEquiv hP h4 (hμ.subset hs)
        (((hμ.matchEquiv hP (hμ.subset hs) (hμ.subset ht) hst).trans
          ((hμ.matchEquiv hP (hμ.subset ht) (hμ.subset hu) htu).trans
            (hμ.matchEquiv hP (hμ.subset hu) (hμ.subset hs) hus)))
          ((hμ.refEquiv hP h4 (hμ.subset hs)).symm i)) := by
    intro i
    simp [transPerm, Equiv.Perm.mul_apply]
  rcases hμ.monodromy_eq_or_ne hP hs ht hu hst htu hus with h | h
  · left
    ext i
    rw [hσ, h]
    simp
  · right
    intro i e
    rw [hσ, ← Equiv.eq_symm_apply] at e
    exact h _ e

end IsTwinSection

@[expose] def signBit (x : ℤˣ) : ZMod 2 := by
  classical exact if x = 1 then 0 else 1

theorem signBit_one : signBit 1 = 0 := by simp [signBit]

theorem signBit_neg_one : signBit (-1) = 1 := by
  unfold signBit
  split_ifs with h
  · exact absurd h (by decide)
  · rfl

theorem signBit_mul (x y : ℤˣ) : signBit (x * y) = signBit x + signBit y := by
  rcases Int.units_eq_one_or x with rfl | rfl <;> rcases Int.units_eq_one_or y with rfl | rfl
  · simp [signBit_one]
  · simp [signBit_one, signBit_neg_one]
  · simp [signBit_one, signBit_neg_one]
  · rw [show ((-1 : ℤˣ) * -1) = 1 from by decide, signBit_one, signBit_neg_one]; rfl

theorem signBit_inv (x : ℤˣ) : signBit x⁻¹ = signBit x := by
  rcases Int.units_eq_one_or x with rfl | rfl <;> simp

theorem eq_one_of_signBit (x : ℤˣ) (h : signBit x = 0) : x = 1 := by
  rcases Int.units_eq_one_or x with rfl | rfl
  · rfl
  · rw [signBit_neg_one] at h; exact absurd h (by decide)

theorem signBit_swapIf (b : ZMod 2) : signBit (Equiv.Perm.sign (swapIf b)) = b := by
  rcases Symplectic.zmod_two_cases b with rfl | rfl
  · simp [swapIf, signBit_one]
  · simp only [swapIf, one_ne_zero, ite_false]
    rw [sign_swap_zero_one, signBit_neg_one]

namespace IsTwinSection

variable (hμ : IsTwinSection E μ) (hP : Pair H E) (h4 : ∀ a ∈ E, (twinClass E a).ncard = 4)
include hμ hP h4

open Classical in
@[expose] def parity (a b : ↥μ) : ZMod 2 :=
  if h : (a : H) * b ≠ b * a then
    signBit (Equiv.Perm.sign (hμ.transPerm hP h4 (hμ.subset a.2) (hμ.subset b.2) h))
  else 0

theorem parity_of_ne {a b : ↥μ} (h : (a : H) * b ≠ b * a) :
    hμ.parity hP h4 a b =
      signBit (Equiv.Perm.sign (hμ.transPerm hP h4 (hμ.subset a.2) (hμ.subset b.2) h)) := by
  unfold parity
  split_ifs
  rfl

theorem parity_symm (a b : ↥μ) : hμ.parity hP h4 b a = hμ.parity hP h4 a b := by
  by_cases h : (a : H) * b ≠ b * a
  · have h' : (b : H) * a ≠ a * b := fun e => h e.symm
    rw [hμ.parity_of_ne hP h4 h, hμ.parity_of_ne hP h4 h', hμ.transPerm_symm hP h4, map_inv,
      signBit_inv]
  · have h' : ¬ ((b : H) * a ≠ a * b) := fun e => h fun e' => e e'.symm
    simp [parity, h, h']

theorem parity_add_add {a b c : ↥μ} (hab : (a : H) * b ≠ b * a) (hbc : (b : H) * c ≠ c * b)
    (hca : (c : H) * a ≠ a * c) :
    hμ.parity hP h4 a b + hμ.parity hP h4 b c + hμ.parity hP h4 c a = 0 := by
  have h := hμ.sign_monodromy hP h4 a.2 b.2 c.2 hab hbc hca
  rw [hμ.parity_of_ne hP h4 hab, hμ.parity_of_ne hP h4 hbc, hμ.parity_of_ne hP h4 hca]
  have := congrArg signBit h
  rw [map_mul, map_mul, signBit_mul, signBit_mul, signBit_one] at this
  rw [← this]
  ring

end IsTwinSection

@[expose] def cocycleCover (ε : ↥μ → ↥μ → ZMod 2) (hsymm : ∀ a b, ε b a = ε a b)
    (hcoc : ∀ a b c : ↥μ, (a : H) * b ≠ b * a → (b : H) * c ≠ c * b → (c : H) * a ≠ a * c →
      ε a b + ε b c + ε c a = 0) :
    TwoCover (Herm.nonCommGraph μ) (fun _ _ _ => True) where
  C := ↥μ × ZMod 2
  π := Prod.fst
  adj :=
    { Adj := fun c c' => (c.1 : H) * c'.1 ≠ c'.1 * c.1 ∧ c'.2 = c.2 + ε c.1 c'.1
      symm := ⟨fun c c' h => ⟨fun e => h.1 e.symm, by
        rw [h.2, hsymm, add_assoc, Symplectic.zmod_two_add_self, add_zero]⟩⟩
      loopless := ⟨fun c h => h.1 rfl⟩ }
  proj h := h.1
  lift c w h := ⟨(w, c.2 + ε c.1 w), ⟨⟨h, rfl⟩, rfl⟩, fun c' hc' => by
    obtain ⟨⟨-, h2⟩, h3⟩ := hc'
    refine Prod.ext h3 ?_
    rw [h2, h3]⟩
  two v := ⟨(v, 0), (v, 1), by simp, rfl, rfl, fun x hx => by
    rcases Symplectic.zmod_two_cases x.2 with h | h
    · exact Or.inl (Prod.ext hx h)
    · exact Or.inr (Prod.ext hx h)⟩
  tri c c₁ c₂ h₁ h₂ h₁₂ := by
    simp only [iff_true]
    refine ⟨h₁₂, ?_⟩
    have h := hcoc c.1 c₁.1 c₂.1 h₁.1 h₁₂ (fun e => h₂.1 e.symm)
    rw [hsymm c.1 c₂.1, add_eq_zero_iff_eq_neg, Symplectic.zmod_two_neg] at h
    rw [h₂.2, h₁.2, add_assoc, h]

namespace IsTwinSection

variable (hμ : IsTwinSection E μ) (hP : Pair H E) (h4 : ∀ a ∈ E, (twinClass E a).ncard = 4)
include hμ hP h4

omit h4 in
theorem coverRigid_section (r : ↥μ) : CoverRigid (Herm.nonCommGraph μ) r := by
  refine coverRigid_nonCommGraph
    ((Pair.isTranspositionSet hP).mono hμ.subset fun a ha b hb => hμ.mul_mul_mem a ha b hb) ?_ r
  refine Herm.connected_nonCommGraph_of_surjective (Pair.connected_nonCommGraph hP)
    (fun a => ⟨sec E μ a, hμ.sec_mem a.2⟩) (fun s => ⟨⟨s, hμ.subset s.2⟩, ?_⟩) ?_
  · exact Subtype.ext (hμ.sec_eq_self s.2)
  · intro a b hab e
    apply hab
    have h1 := hμ.isTwin_sec a.2
    have h2 := hμ.isTwin_sec b.2
    have h3 : (sec E μ a : H) * b = b * sec E μ a :=
      ((h2.2.2.2 _ (hμ.subset (hμ.sec_mem a.2))).2 e)
    exact ((h1.2.2.2 _ b.2).2 h3.symm).symm

theorem exists_potential :
    ∃ c : ↥μ → ZMod 2, ∀ a b : ↥μ, (a : H) * b ≠ b * a →
      c b = c a + hμ.parity hP h4 a b := by
  obtain ⟨s, hs⟩ := Pair.nonempty hP
  have r : ↥μ := ⟨sec E μ s, hμ.sec_mem hs⟩
  have hr := hμ.coverRigid_section hP r
  obtain ⟨β, hβπ, hβadj⟩ := TwoCover.exists_iso r hr.exists_adj_adj hr.connected
    hr.exists_adj_adj_adj
    (cocycleCover (hμ.parity hP h4) (hμ.parity_symm hP h4)
      fun a b c hab hbc hca => hμ.parity_add_add hP h4 hab hbc hca)
    (cocycleCover (μ := μ) (fun _ _ => (0 : ZMod 2)) (fun _ _ => rfl)
      fun _ _ _ _ _ _ => by simp)
  let β' : (↥μ × ZMod 2) ≃ (↥μ × ZMod 2) := β
  have hβπ' : ∀ c : ↥μ × ZMod 2, (β' c).1 = c.1 := hβπ
  have hβadj' : ∀ c c' : ↥μ × ZMod 2,
      ((c.1 : H) * c'.1 ≠ c'.1 * c.1 ∧ c'.2 = c.2 + hμ.parity hP h4 c.1 c'.1) ↔
      (((β' c).1 : H) * (β' c').1 ≠ (β' c').1 * (β' c).1 ∧ (β' c').2 = (β' c).2 + 0) := hβadj
  refine ⟨fun v => (β'.symm (v, 0)).2, fun a b hab => ?_⟩
  have hπ : ∀ v, (β'.symm (v, 0)).1 = v := fun v => by
    have := hβπ' (β'.symm (v, 0))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have h2 := ((hβadj' (β'.symm (a, 0)) (β'.symm (b, 0))).2 (by
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact ⟨hab, by simp⟩)).2
  rw [hπ a, hπ b] at h2
  exact h2

@[expose] def corrEquiv (c : ↥μ → ZMod 2) (v : ↥μ) : Fib E μ v ≃ Fin 3 :=
  (hμ.refEquiv hP h4 (hμ.subset v.2)).trans (swapIf (c v))

theorem sign_corr {c : ↥μ → ZMod 2}
    (hc : ∀ a b : ↥μ, (a : H) * b ≠ b * a → c b = c a + hμ.parity hP h4 a b) {a b : ↥μ}
    (hab : (a : H) * b ≠ b * a) :
    Equiv.Perm.sign ((hμ.corrEquiv hP h4 c a).symm.trans
      ((hμ.matchEquiv hP (hμ.subset a.2) (hμ.subset b.2) hab).trans
        (hμ.corrEquiv hP h4 c b))) = 1 := by
  have e : (hμ.corrEquiv hP h4 c a).symm.trans
      ((hμ.matchEquiv hP (hμ.subset a.2) (hμ.subset b.2) hab).trans (hμ.corrEquiv hP h4 c b)) =
      swapIf (c b) * hμ.transPerm hP h4 (hμ.subset a.2) (hμ.subset b.2) hab *
        (swapIf (c a))⁻¹ := by
    ext i
    simp [corrEquiv, transPerm, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  rw [e]
  apply eq_one_of_signBit
  rw [map_mul, map_mul, signBit_mul, signBit_mul, map_inv, signBit_inv, signBit_swapIf,
    signBit_swapIf, ← hμ.parity_of_ne hP h4 hab, hc a b hab]
  rw [show c a + hμ.parity hP h4 a b + hμ.parity hP h4 a b + c a =
    (c a + c a) + (hμ.parity hP h4 a b + hμ.parity hP h4 a b) by ring,
    Symplectic.zmod_two_add_self, Symplectic.zmod_two_add_self, add_zero]

theorem exists_orientation :
    ∃ J : ∀ s : ↥μ, Equiv.Perm (Fib E μ s),
      (∀ s f, J s f ≠ f) ∧ (∀ s f, J s (J s f) ≠ f) ∧ (∀ s f, J s (J s (J s f)) = f) ∧
      ∀ (s t : ↥μ) (hst : (s : H) * t ≠ t * s) (f : Fib E μ s),
        hμ.matchEquiv hP (hμ.subset s.2) (hμ.subset t.2) hst (J s f) =
          J t (hμ.matchEquiv hP (hμ.subset s.2) (hμ.subset t.2) hst f) := by
  obtain ⟨c, hc⟩ := hμ.exists_potential hP h4
  refine ⟨fun s => (hμ.corrEquiv hP h4 c s).trans ((finRotate 3).trans
    (hμ.corrEquiv hP h4 c s).symm), fun s f => ?_, fun s f => ?_, fun s f => ?_,
    fun s t hst f => ?_⟩
  · simp only [Equiv.trans_apply, ne_eq, Equiv.symm_apply_eq]
    exact finRotate_three_ne _
  · simp only [Equiv.trans_apply, Equiv.apply_symm_apply, ne_eq, Equiv.symm_apply_eq]
    exact finRotate_three_two_ne _
  · simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    exact finRotate_three_three _
  ·
    set σ := (hμ.corrEquiv hP h4 c s).symm.trans
      ((hμ.matchEquiv hP (hμ.subset s.2) (hμ.subset t.2) hst).trans (hμ.corrEquiv hP h4 c t))
    have hσ := commute_finRotate_of_sign σ (hμ.sign_corr hP h4 hc hst)
    have hm : ∀ x, hμ.matchEquiv hP (hμ.subset s.2) (hμ.subset t.2) hst x =
        (hμ.corrEquiv hP h4 c t).symm (σ (hμ.corrEquiv hP h4 c s x)) := fun x => by
      simp [σ]
    simp only [Equiv.trans_apply]
    rw [hm, hm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    congr 1
    have := congrArg (fun p : Equiv.Perm (Fin 3) => p (hμ.corrEquiv hP h4 c s f)) hσ
    simpa [Equiv.Perm.mul_apply] using this

end IsTwinSection

end O2Mod

end CFSG.Fischer.Classification
