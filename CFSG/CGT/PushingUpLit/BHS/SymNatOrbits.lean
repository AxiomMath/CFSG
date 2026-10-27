module

public import CFSG.CGT.PushingUpLit.BHS.SymNatSplit

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.A1b

section Defs

variable {V : Type*} [CommGroup V]

@[expose] def IsIrrSection (X : Subgroup (MulAut V)) (P Z : Subgroup V) : Prop :=
  Z < P ∧ ∀ U : Subgroup V, Z ≤ U → U ≤ P → (∀ x ∈ X, ∀ u ∈ U, x u ∈ U) → U = Z ∨ U = P

@[expose] def IsNontrivialOrbit {n : ℕ} (F : Subgroup (Equiv.Perm (Fin n))) (O : Set (Fin n)) :
    Prop :=
  (∃ x, O = MulAction.orbit F x) ∧ O.Nontrivial

@[expose] def IsMaxSwapGroup {n : ℕ} (Y : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∃ T : Set (Equiv.Perm (Fin n)), (∀ t ∈ T, t.IsSwap) ∧ (∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) ∧
    T.ncard = (n - 1) / 2 ∧ Y = Subgroup.closure T

theorem apply_mem_commV_sup_fixV {X : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ X) {p : V}
    (hp : p ∈ commV X ⊔ fixV X) : x p ∈ commV X ⊔ fixV X := by
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Subgroup.mem_sup.1 hp
  rw [map_mul, hp₂ x hx]
  exact Subgroup.mul_mem_sup (G6.apply_mem_commV
    (fun y hy => X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) hp₁) hp₂

end Defs

variable {n : ℕ}

@[expose] def compVec (hn : Odd n) (a : Fin n) : ↥(coreMod n) :=
  mkEven (fun x => (if x = a then 1 else 0) + ∑ y : Fin n, (if y = a then (1 : ZMod 2) else 0))
    (sum_shift hn _)

theorem vcoord_compVec (hn : Odd n) (a x : Fin n) :
    vcoord (compVec hn a) x = (if x = a then 1 else 0) + 1 := by
  simp [compVec, vcoord_mkEven]

theorem coreAct_compVec_mul (hn : Odd n) (σ : Equiv.Perm (Fin n)) (a : Fin n) :
    coreAct n σ (compVec hn a) * (compVec hn a)⁻¹ = pairVec (σ a) a := by
  refine vcoord_ext fun x => ?_
  rw [vcoord_mul, vcoord_inv, vcoord_coreAct, vcoord_compVec, vcoord_compVec, vcoord_pairVec]
  simp only [Equiv.Perm.inv_eq_iff_eq]
  have h : ∀ p q : ZMod 2, p + 1 + (q + 1) = p + q := by decide
  exact h _ _

theorem pairVec_mem_commV (hn : Odd n) {F : Subgroup (Equiv.Perm (Fin n))}
    {f : Equiv.Perm (Fin n)} (hf : f ∈ F) (a : Fin n) :
    pairVec (f a) a ∈ commV (F.map (coreAct n)) := by
  rw [← coreAct_compVec_mul hn f a]
  exact G6.mem_commV_of_mem (Subgroup.mem_map_of_mem _ hf) _

theorem vcoord_eq_zero_of_mem_commV {F : Subgroup (Equiv.Perm (Fin n))} {v : ↥(coreMod n)}
    (hv : v ∈ commV (F.map (coreAct n))) {i : Fin n} (hi : ∀ f ∈ F, f i = i) :
    vcoord v i = 0 := by
  let U : Subgroup ↥(coreMod n) :=
    { carrier := {w | vcoord w i = 0}
      mul_mem' := fun {a b} ha hb => by
        show vcoord (a * b) i = 0
        rw [vcoord_mul, show vcoord a i = 0 from ha, show vcoord b i = 0 from hb, add_zero]
      one_mem' := vcoord_one i
      inv_mem' := fun {a} ha => by
        show vcoord a⁻¹ i = 0
        rw [vcoord_inv]
        exact ha }
  have hle : commV (F.map (coreAct n)) ≤ U := G6.commV_le_iff.2 <| by
    rintro x hx w
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hx
    show vcoord (coreAct n f w * w⁻¹) i = 0
    rw [vcoord_mul, vcoord_inv, vcoord_coreAct, Equiv.Perm.inv_eq_iff_eq.2 (hi f hf).symm]
    exact CharTwo.add_self_eq_zero _
  exact hle hv

theorem exists_third_of_opResidual {F : Subgroup (Equiv.Perm (Fin n))} (hF : opResidual 2 F = F)
    {f : Equiv.Perm (Fin n)} (hf : f ∈ F) {a : Fin n} (ha : f a ≠ a) :
    ∃ g ∈ F, g a ≠ a ∧ g a ≠ f a := by
  by_contra hcon
  push Not at hcon
  have hodd : ∀ g ∈ F, (orderOf g).Coprime 2 → g a = a := by
    intro g hg hco
    by_contra hga
    have hgb : g a = f a := hcon g hg hga
    have hg2 : (g ^ 2) a = a := by
      by_contra hne
      have h2 := hcon (g ^ 2) (F.pow_mem hg 2) hne
      rw [pow_two, Equiv.Perm.mul_apply, ← hgb] at h2
      exact hga (g.injective h2)
    have hpow : ∀ i : ℕ, (g ^ (2 * i)) a = a := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, hg2, ih]
    obtain ⟨j, hj⟩ := Nat.coprime_two_right.1 hco
    have h1 := congrArg (fun σ : Equiv.Perm (Fin n) => σ a) (pow_orderOf_eq_one g)
    simp only [hj, pow_succ', Equiv.Perm.mul_apply, hpow, Equiv.Perm.one_apply] at h1
    exact hga h1
  have hle : opResidual 2 F ≤ MulAction.stabilizer (Equiv.Perm (Fin n)) a := by
    rw [opResidual, Subgroup.closure_le]
    rintro g ⟨hg, hco⟩
    exact MulAction.mem_stabilizer_iff.2 (hodd g hg hco)
  have hf' : f ∈ opResidual 2 F := by rw [hF]; exact hf
  exact ha (MulAction.mem_stabilizer_iff.1 (hle hf'))

theorem exists_moved_of_irr {F : Subgroup (Equiv.Perm (Fin n))}
    (hirr : IsIrrSection (F.map (coreAct n))
      (commV (F.map (coreAct n)) ⊔ fixV (F.map (coreAct n))) (fixV (F.map (coreAct n)))) :
    ∃ x, ∃ f ∈ F, f x ≠ x := by
  obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hirr.1
  by_contra hcon
  push Not at hcon
  exact hv (mem_fixV_map_iff.2 fun a ha i => by rw [hcon i a ha])

theorem moved_of_nontrivial {F : Subgroup (Equiv.Perm (Fin n))} {x : Fin n}
    (h : (MulAction.orbit F x).Nontrivial) : ∃ f ∈ F, f x ≠ x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, ⟨⟨g, hg⟩, rfl⟩, z, ⟨⟨k, hk⟩, rfl⟩, hyz⟩ := h
  apply hyz
  change g x = k x
  rw [hcon g hg, hcon k hk]

theorem same_orbit_of_moved (hn : Odd n) {F : Subgroup (Equiv.Perm (Fin n))}
    (hF : opResidual 2 F = F)
    (hirr : IsIrrSection (F.map (coreAct n))
      (commV (F.map (coreAct n)) ⊔ fixV (F.map (coreAct n))) (fixV (F.map (coreAct n))))
    {a c : Fin n} (ha : ∃ f ∈ F, f a ≠ a) (hc : ∃ f ∈ F, f c ≠ c) : ∃ f ∈ F, f c = a := by
  by_contra hno
  push Not at hno
  obtain ⟨f₁, hf₁, ha₁⟩ := ha
  obtain ⟨f₃, hf₃, hc₃⟩ := hc
  obtain ⟨f₂, hf₂, ha₂, ha₂'⟩ := exists_third_of_opResidual hF hf₁ ha₁
  obtain ⟨f₄, hf₄, hc₄, hc₄'⟩ := exists_third_of_opResidual hF hf₃ hc₃
  set Fm := F.map (coreAct n) with hFm
  let U : Subgroup ↥(coreMod n) :=
    { carrier := {v | v ∈ commV Fm ⊔ fixV Fm ∧ ∀ f ∈ F, vcoord v (f c) = vcoord v c}
      mul_mem' := fun {v w} hv hw => ⟨(commV Fm ⊔ fixV Fm).mul_mem hv.1 hw.1, fun f hf => by
        rw [vcoord_mul, vcoord_mul, hv.2 f hf, hw.2 f hf]⟩
      one_mem' := ⟨(commV Fm ⊔ fixV Fm).one_mem, fun f _ => by rw [vcoord_one, vcoord_one]⟩
      inv_mem' := fun {v} hv => ⟨(commV Fm ⊔ fixV Fm).inv_mem hv.1, fun f hf => by
        rw [vcoord_inv, vcoord_inv, hv.2 f hf]⟩ }
  have hZU : fixV Fm ≤ U := fun v hv =>
    ⟨le_sup_right (a := commV Fm) hv, fun f hf => mem_fixV_map_iff.1 hv f hf c⟩
  have hUP : U ≤ commV Fm ⊔ fixV Fm := fun v hv => hv.1
  have hinv : ∀ x ∈ Fm, ∀ u ∈ U, x u ∈ U := by
    intro x hx u hu
    refine ⟨apply_mem_commV_sup_fixV hx hu.1, fun f hf => ?_⟩
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hx
    rw [vcoord_coreAct, vcoord_coreAct]
    have h1 := hu.2 (σ⁻¹ * f) (F.mul_mem (F.inv_mem hσ) hf)
    have h2 := hu.2 σ⁻¹ (F.inv_mem hσ)
    rw [Equiv.Perm.mul_apply] at h1
    rw [h1, h2]
  rcases hirr.2 U hZU hUP hinv with h | h
  · have hv : pairVec (f₁ a) a ∈ U := by
      refine ⟨le_sup_left (b := fixV Fm) (pairVec_mem_commV hn hf₁ a), fun f hf => ?_⟩
      have e1 : f c ≠ f₁ a := fun he => hno (f₁⁻¹ * f) (F.mul_mem (F.inv_mem hf₁) hf) (by
        rw [Equiv.Perm.mul_apply, he, perm_inv_apply_self])
      have e2 : f c ≠ a := hno f hf
      have e3 : c ≠ f₁ a := fun he => hno f₁⁻¹ (F.inv_mem hf₁) (by rw [he, perm_inv_apply_self])
      have e4 : c ≠ a := fun he => hno 1 F.one_mem (by rw [Equiv.Perm.one_apply, he])
      rw [vcoord_pairVec, vcoord_pairVec]
      simp [e1, e2, e3, e4]
    rw [h] at hv
    have h5 := mem_fixV_map_iff.1 hv f₂ hf₂ a
    rw [vcoord_pairVec, vcoord_pairVec] at h5
    simp [ha₂, ha₂', ha₁.symm] at h5
  · have hv : pairVec (f₃ c) c ∈ commV Fm ⊔ fixV Fm :=
      le_sup_left (b := fixV Fm) (pairVec_mem_commV hn hf₃ c)
    have hv' : pairVec (f₃ c) c ∈ U := by
      rw [h]
      exact hv
    have h5 := hv'.2 f₄ hf₄
    rw [vcoord_pairVec, vcoord_pairVec] at h5
    simp [hc₄, hc₄', hc₃.symm] at h5

theorem two_fourteen_a (n : ℕ) (hn : Odd n) {F : Subgroup (Equiv.Perm (Fin n))}
    (hF : opResidual 2 F = F)
    (hirr : IsIrrSection (F.map (coreAct n))
      (commV (F.map (coreAct n)) ⊔ fixV (F.map (coreAct n))) (fixV (F.map (coreAct n)))) :
    ∃ O : Set (Fin n), IsNontrivialOrbit F O ∧ ∀ O', IsNontrivialOrbit F O' → O' = O := by
  obtain ⟨x₀, hx₀⟩ := exists_moved_of_irr hirr
  refine ⟨MulAction.orbit F x₀, ⟨⟨x₀, rfl⟩, ?_⟩, ?_⟩
  · obtain ⟨f, hf, hfx⟩ := hx₀
    exact ⟨x₀, MulAction.mem_orbit_self x₀, f x₀, ⟨⟨f, hf⟩, rfl⟩, hfx.symm⟩
  · rintro O' ⟨⟨x', rfl⟩, hnt⟩
    obtain ⟨f, hf, hfx⟩ := same_orbit_of_moved hn hF hirr (moved_of_nontrivial hnt) hx₀
    exact MulAction.orbit_eq_iff.2 ⟨⟨f, hf⟩, hfx⟩

end CFSG.CGT.PushingUpLit.BHS
