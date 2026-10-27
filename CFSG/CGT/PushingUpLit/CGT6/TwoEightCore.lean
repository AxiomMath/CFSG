module

public import CFSG.CGT.PushingUpLit.CGT6.TwoEightCount
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightKU
public import Mathlib.Tactic.Group

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Core

variable {F L : Type} [Field F] [AddCommGroup L] [Module F L] [CharP F 2] (D : Data F L)

theorem no_transvection [Finite F] [Finite L] (hF : 3 ≤ Nat.card F)
    {a : Equiv.Perm (Wd F L)} (hadd : IsAddPerm a) (ha2 : a * a = 1)
    (hnorm : ∀ x, ∃ x', a * sigPerm D x * a⁻¹ = sigPerm D x')
    (hnc : ∃ x, a * sigPerm D x ≠ sigPerm D x * a)
    (h2 : Nat.card (Wd F L) ≤ 2 * Nat.card {w : Wd F L // a w = w}) : False := by
  classical
  obtain ⟨x, hx⟩ := hnc
  obtain ⟨x', hx'⟩ := hnorm x
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haa : ∀ w, a (a w) = w := fun w => by
    simpa using congrArg (fun g : Equiv.Perm (Wd F L) => g w) ha2
  have hconj : ∀ w, sigFun D x' w = a (sigFun D x (a w)) := fun w => by
    have := congrArg (fun g : Equiv.Perm (Wd F L) => g w) hx'
    rw [hainv] at this
    exact this.symm
  have hxx' : x' ≠ x := by
    intro h
    apply hx
    have h1 : a * sigPerm D x * a⁻¹ = sigPerm D x := by rw [hx', h]
    calc a * sigPerm D x = a * sigPerm D x * a⁻¹ * a := by group
      _ = sigPerm D x * a := by rw [h1]
  obtain ⟨u, hu⟩ : ∃ u : L, u = x' - x := ⟨_, rfl⟩
  have hu0 : u ≠ 0 := by rw [hu]; exact sub_ne_zero.mpr hxx'
  let φ : Wd F L →+ Wd F L := AddMonoidHom.mk' (fun w => a w - w) (fun w w' => by
    rw [hadd]; abel)
  have hφ : ∀ w, φ w = a w - w := fun w => rfl
  have hker : Nat.card φ.ker = Nat.card {w : Wd F L // a w = w} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun w => by
      rw [AddMonoidHom.mem_ker, hφ, sub_eq_zero]))
  have hrange : Nat.card φ.range ≤ 2 := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
    have h3 : Nat.card (Wd F L ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv
    have hpos : 0 < Nat.card φ.ker := Nat.card_pos
    rw [h3, hker] at h1
    rw [h1, ← hker] at h2
    by_contra hcon
    have : 3 * Nat.card φ.ker ≤ Nat.card φ.range * Nat.card φ.ker :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hσadd : ∀ w w', sigFun D x (w + w') = sigFun D x w + sigFun D x w' :=
    fun w w' => sigPerm_isAdd D x w w'
  obtain ⟨T, hTdef⟩ : ∃ T : Wd F L → Wd F L, ∀ w, T w = sigFun D x' w - sigFun D x w :=
    ⟨fun w => sigFun D x' w - sigFun D x w, fun w => rfl⟩
  have hTform : ∀ w, T w = sigFun D x (φ w) + φ (sigFun D x (a w)) := fun w => by
    rw [hTdef, hconj w, hφ, hφ]
    have h2 : sigFun D x (a w) = sigFun D x w + sigFun D x (a w - w) := by
      rw [← hσadd]
      congr 1
      abel
    generalize a (sigFun D x (a w)) = P
    rw [h2]
    abel
  have hsub : Set.range T ⊆
      Set.range (fun p : φ.range × φ.range => sigFun D x p.1 + p.2) := by
    rintro _ ⟨w, rfl⟩
    exact ⟨(⟨φ w, ⟨w, rfl⟩⟩, ⟨φ (sigFun D x (a w)), ⟨_, rfl⟩⟩), (hTform w).symm⟩
  have hupper : Nat.card (Set.range T) ≤ 4 := by
    calc Nat.card (Set.range T)
        ≤ Nat.card (Set.range (fun p : φ.range × φ.range => sigFun D x p.1 + p.2)) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ ≤ Nat.card (φ.range × φ.range) :=
          Nat.card_le_card_of_surjective (Set.rangeFactorization _) Set.rangeFactorization_surjective
      _ = Nat.card φ.range * Nat.card φ.range := Nat.card_prod _ _
      _ ≤ 2 * 2 := Nat.mul_le_mul hrange hrange
  have hT : ∀ (y : L) (s : F), T (0, y, s) =
      (D.B u y + (D.Q x' - D.Q x) * s, s • u, 0) := by
    intro y s
    rw [hTdef]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show (0 + D.B x' y + D.Q x' * s) - (0 + D.B x y + D.Q x * s) =
        D.B u y + (D.Q x' - D.Q x) * s
      rw [hu, map_sub, LinearMap.sub_apply]
      ring
    · show (y + s • x') - (y + s • x) = s • u
      rw [hu, smul_sub]
      abel
    · exact sub_self s
  choose yy hyy using fun (t s : F) => B_surj D hu0 (t - (D.Q x' - D.Q x) * s)
  have hlow : Nat.card F * Nat.card F ≤ Nat.card (Set.range T) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun ts : F × F =>
      (⟨T (0, yy ts.1 ts.2, ts.2), ⟨_, rfl⟩⟩ : Set.range T)) ?_
    rintro ⟨t, s⟩ ⟨t', s'⟩ h
    have h1 := congrArg Subtype.val h
    simp only [hT, hyy] at h1
    have h2 := congrArg Prod.fst h1
    have h3 := congrArg (fun z : Wd F L => z.2.1) h1
    simp only at h2 h3
    have hss : s = s' := smul_left_injective F hu0 h3
    subst hss
    have : t = t' := by linear_combination h2
    rw [this]
  have h9 : 9 ≤ Nat.card F * Nat.card F := by nlinarith
  omega

theorem core_eq_bot [Finite F] [Finite L] [Module.Finite F L] (hF : 3 ≤ Nat.card F)
    {Γ Ā : Subgroup (Equiv.Perm (Wd F L))}
    (hΓσ : ∀ x, sigPerm D x ∈ Γ) {x₁ : L} (hx₁ : x₁ ≠ 0) (hΓl : lamPerm D x₁ ∈ Γ)
    (hΓQ : ∀ g ∈ Γ, ∀ w, Qt D (g w) = Qt D w)
    (hadd : ∀ a ∈ Ā, IsAddPerm a) (hsq : ∀ a ∈ Ā, a * a = 1)
    (hnormΓ : ∀ a ∈ Ā, ∀ g ∈ Γ, a * g * a⁻¹ ∈ Γ)
    (hnormS : ∀ a ∈ Ā, ∀ x, ∃ x', a * sigPerm D x * a⁻¹ = sigPerm D x')
    (hidx : Nat.card Ā ≤
      2 * Nat.card ↥(Ā ⊓ Subgroup.centralizer (S0 D : Set (Equiv.Perm (Wd F L)))))
    (hoff : Nat.card (Wd F L) ≤ Nat.card Ā * Nat.card (Fix Ā)) : Ā = ⊥ := by
  classical
  by_contra hne
  obtain ⟨K, hK⟩ : ∃ K : Subgroup (Equiv.Perm (Wd F L)),
      K = Ā ⊓ Subgroup.centralizer (S0 D : Set (Equiv.Perm (Wd F L))) := ⟨_, rfl⟩
  rw [← hK] at hidx
  have hKS : K ≤ S0 D := by
    intro a ha
    rw [hK] at ha
    have haĀ : a ∈ Ā := ha.1
    have hcent : ∀ x, a * sigPerm D x = sigPerm D x * a := fun x =>
      (Subgroup.mem_centralizer_iff.mp ha.2 (sigPerm D x) ⟨x, rfl⟩).symm
    refine mem_S0_of_centralizes hΓσ hx₁ hΓl hΓQ ⟨hadd a haĀ, fun x w => ?_⟩ (hsq a haĀ)
      (hnormΓ a haĀ)
    have := congrArg (fun g : Equiv.Perm (Wd F L) => g w) (hcent x)
    simpa [sigPerm_apply] using this
  by_cases hKbot : K = ⊥
  · have hcardK : Nat.card K = 1 := by rw [hKbot]; exact Subgroup.card_bot
    have hĀ2 : Nat.card Ā ≤ 2 := by rw [hcardK] at hidx; omega
    obtain ⟨a, haĀ, ha1⟩ : ∃ a ∈ Ā, a ≠ 1 := by
      obtain ⟨⟨a, ha⟩, h⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      exact ⟨a, ha, fun h1 => h (Subtype.ext h1)⟩
    have hanotK : a ∉ K := fun haK => ha1 (by
      rw [hKbot] at haK
      exact Subgroup.mem_bot.mp haK)
    have hnc : ∃ x, a * sigPerm D x ≠ sigPerm D x * a := by
      by_contra hcon
      push Not at hcon
      apply hanotK
      rw [hK]
      refine ⟨haĀ, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      obtain ⟨x, rfl⟩ := hg
      exact (hcon x).symm
    have hfix : Nat.card (Fix Ā) ≤ Nat.card {w : Wd F L // a w = w} := by
      refine Nat.card_le_card_of_injective
        (fun w : Fix Ā => (⟨w.1, w.2 a haĀ⟩ : {w : Wd F L // a w = w})) ?_
      intro w w' h
      apply Subtype.ext
      exact congrArg (fun z : {w : Wd F L // a w = w} => (z : Wd F L)) h
    exact no_transvection D hF (hadd a haĀ) (hsq a haĀ) (hnormS a haĀ) hnc (by
      calc Nat.card (Wd F L) ≤ Nat.card Ā * Nat.card (Fix Ā) := hoff
        _ ≤ 2 * Nat.card {w : Wd F L // a w = w} := Nat.mul_le_mul hĀ2 hfix)
  · have hcount := card_mul_card_fix_le D hKS hKbot
    have hKĀ : K ≤ Ā := by
      rw [hK]
      exact inf_le_left
    have hfixK : Nat.card (Fix Ā) ≤ Nat.card (Fix K) := by
      refine Nat.card_le_card_of_injective
        (fun w : Fix Ā => (⟨w.1, fun a ha => w.2 a (hKĀ ha)⟩ : Fix K)) ?_
      intro w w' h
      apply Subtype.ext
      exact congrArg (fun z : Fix K => (z : Wd F L)) h
    have hW : Nat.card (Wd F L) = Nat.card F * (Nat.card L * Nat.card F) := by
      rw [Nat.card_prod, Nat.card_prod]
    have hposF : 0 < Nat.card F := Nat.card_pos
    have hposL : 0 < Nat.card L := Nat.card_pos
    have h1 : Nat.card F * (Nat.card L * Nat.card F) ≤ 2 * (Nat.card F * Nat.card L) := by
      calc Nat.card F * (Nat.card L * Nat.card F) = Nat.card (Wd F L) := hW.symm
        _ ≤ Nat.card Ā * Nat.card (Fix Ā) := hoff
        _ ≤ (2 * Nat.card K) * Nat.card (Fix K) := Nat.mul_le_mul hidx hfixK
        _ = 2 * (Nat.card K * Nat.card (Fix K)) := by ring
        _ ≤ 2 * (Nat.card F * Nat.card L) := Nat.mul_le_mul_left _ hcount
    have h2 : Nat.card F ≤ 2 := by
      have hpos : 0 < Nat.card F * Nat.card L := Nat.mul_pos hposF hposL
      have h3 : (Nat.card F * Nat.card L) * Nat.card F ≤ (Nat.card F * Nat.card L) * 2 := by
        calc (Nat.card F * Nat.card L) * Nat.card F
            = Nat.card F * (Nat.card L * Nat.card F) := by ring
          _ ≤ 2 * (Nat.card F * Nat.card L) := h1
          _ = (Nat.card F * Nat.card L) * 2 := by ring
      exact Nat.le_of_mul_le_mul_left h3 hpos
    omega

end Core

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
