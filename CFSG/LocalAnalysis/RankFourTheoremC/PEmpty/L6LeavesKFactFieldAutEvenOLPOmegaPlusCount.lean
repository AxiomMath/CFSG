module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLinAlg

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

theorem omegaPlus_card_invariant_modEq_card_fixed {α : Type*} [Finite α] {r : ℕ} (hr : r.Prime)
    (g : α → α) (hg : ∀ x, g^[r] x = x) (T : Set α) (hT : ∀ x ∈ T, g x ∈ T) :
    Nat.card T ≡ Nat.card {x : α // x ∈ T ∧ g x = x} [MOD r] := by
  have hr1 : r = (r - 1) + 1 := by
    have := hr.one_lt
    omega
  have hginj : Function.Injective g := by
    intro x y hxy
    have hx := hg x
    have hy := hg y
    rw [hr1, Function.iterate_succ_apply] at hx hy
    rw [← hx, ← hy, hxy]
  have hinj : Function.Injective (fun x : T => (⟨g x, hT x x.2⟩ : T)) := by
    intro a b hab
    exact Subtype.ext (hginj (congrArg Subtype.val hab))
  let σ : Equiv.Perm T := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hσw : ∀ w : T, ((σ w : T) : α) = g w := fun w => rfl
  have hσ : σ ^ r = 1 := by
    ext w
    have key : ∀ (n : ℕ) (w : T), (((σ ^ n) w : T) : α) = g^[n] w := by
      intro n
      induction n with
      | zero => intro w; simp
      | succ n ih =>
        intro w
        rw [pow_succ, Equiv.Perm.mul_apply, ih (σ w), hσw, Function.iterate_succ_apply]
    have := key r w
    rw [hg] at this
    simpa using this
  have h := card_modEq_card_fixed_of_pow_eq_one hr σ hσ
  have hcard : Nat.card {x : T // σ x = x} = Nat.card {x : α // x ∈ T ∧ g x = x} :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1.1, p.1.2, congrArg Subtype.val p.2⟩
        invFun := fun q => ⟨⟨q.1, q.2.1⟩, Subtype.ext q.2.2⟩
        left_inv := fun p => rfl
        right_inv := fun q => rfl }
  rw [hcard] at h
  exact h

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Module.Finite F V]

theorem omegaPlus_card_pow_modEq_fixed {r : ℕ} (hr : r.Prime) (g : V →ₗ[F] V) (hg : g ^ r = 1)
    (W : Submodule F V) (hW : ∀ v ∈ W, g v ∈ W) :
    Nat.card F ^ Module.finrank F W ≡
      Nat.card F ^ Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1)) [MOD r] := by
  haveI : Finite V := Module.finite_of_finite F
  have hgit : ∀ x, (⇑g)^[r] x = x := fun x => by
    rw [← Module.End.pow_apply, hg]
    rfl
  have h := omegaPlus_card_invariant_modEq_card_fixed hr (⇑g) hgit (W : Set V) hW
  have h1 : Nat.card (W : Set V) = Nat.card F ^ Module.finrank F W :=
    Module.natCard_eq_pow_finrank (K := F)
  have h2 : Nat.card {x : V // x ∈ (W : Set V) ∧ g x = x} =
      Nat.card F ^ Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1)) := by
    rw [← Module.natCard_eq_pow_finrank (K := F)]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    simp only [SetLike.mem_coe, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
  rw [h1, h2] at h
  exact h

theorem omegaPlus_dvd_finrank_sub {r e : ℕ} (hr : r.Prime) (g : V →ₗ[F] V) (hg : g ^ r = 1)
    (he : 1 ≤ e) (hord : ∀ m : ℕ, r ∣ Nat.card F ^ m - 1 ↔ e ∣ m) (W : Submodule F V)
    (hW : ∀ v ∈ W, g v ∈ W) :
    e ∣ Module.finrank F W - Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1)) := by
  have h := omegaPlus_card_pow_modEq_fixed hr g hg W hW
  have hba : Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1)) ≤ Module.finrank F W :=
    Submodule.finrank_mono inf_le_left
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hrq : ¬ r ∣ Nat.card F := by
    intro hrq
    have h1 : r ∣ Nat.card F ^ e - 1 := (hord e).2 dvd_rfl
    have h2 : r ∣ Nat.card F ^ e := hrq.trans (dvd_pow_self _ (by omega))
    have h3 : r ∣ Nat.card F ^ e - (Nat.card F ^ e - 1) := Nat.dvd_sub h2 h1
    have h4 : Nat.card F ^ e - (Nat.card F ^ e - 1) = 1 := by
      have := Nat.one_le_pow e (Nat.card F) hq
      omega
    rw [h4] at h3
    exact hr.one_lt.ne' (Nat.dvd_one.mp h3)
  have hcop : Nat.gcd r (Nat.card F ^ Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1))) = 1 :=
    (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hr).2 hrq))
  have hsplit : Nat.card F ^ Module.finrank F W =
      Nat.card F ^ Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1)) *
        Nat.card F ^ (Module.finrank F W - Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1))) := by
    rw [← pow_add]
    congr 1
    omega
  have h' : Nat.card F ^ Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1)) *
      Nat.card F ^ (Module.finrank F W - Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1))) ≡
      Nat.card F ^ Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1)) * 1 [MOD r] := by
    rw [mul_one, ← hsplit]
    exact h
  have h5 := Nat.ModEq.cancel_left_of_coprime hcop h'
  have h6 : r ∣ Nat.card F ^
      (Module.finrank F W - Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1))) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq)).1 h5.symm
  exact (hord _).1 h6

theorem omegaPlus_le_ker_of_finrank_lt {r e : ℕ} (hr : r.Prime) (g : V →ₗ[F] V) (hg : g ^ r = 1)
    (he : 1 ≤ e) (hord : ∀ m : ℕ, r ∣ Nat.card F ^ m - 1 ↔ e ∣ m) (W : Submodule F V)
    (hW : ∀ v ∈ W, g v ∈ W) (hlt : Module.finrank F W < e) : W ≤ LinearMap.ker (g - 1) := by
  have hd := omegaPlus_dvd_finrank_sub hr g hg he hord W hW
  have hba : Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1)) ≤ Module.finrank F W :=
    Submodule.finrank_mono inf_le_left
  have h0 : Module.finrank F W - Module.finrank F ↥(W ⊓ LinearMap.ker (g - 1)) = 0 :=
    Nat.eq_zero_of_dvd_of_lt hd (by omega)
  have heq : W ⊓ LinearMap.ker (g - 1) = W :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  calc W = W ⊓ LinearMap.ker (g - 1) := heq.symm
    _ ≤ LinearMap.ker (g - 1) := inf_le_right

theorem omegaPlus_finrank_ker_eq_two {r e : ℕ} (hr : r.Prime) (g : V →ₗ[F] V) (hg : g ^ r = 1)
    (he : 3 ≤ e) (hord : ∀ m : ℕ, r ∣ Nat.card F ^ m - 1 ↔ e ∣ m)
    (hdim : Module.finrank F V = e + 2) (hg1 : g ≠ 1) :
    Module.finrank F ↥(LinearMap.ker (g - 1)) = 2 := by
  have hd := omegaPlus_dvd_finrank_sub hr g hg (by omega) hord ⊤ (fun v _ => Submodule.mem_top)
  rw [finrank_top, top_inf_eq, hdim] at hd
  have hk : Module.finrank F ↥(LinearMap.ker (g - 1)) ≤ e + 2 := hdim ▸ Submodule.finrank_le _
  have hkne : Module.finrank F ↥(LinearMap.ker (g - 1)) ≠ e + 2 := by
    intro hkeq
    have htop : LinearMap.ker (g - 1) = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hkeq, hdim])
    apply hg1
    have h0 : g - 1 = 0 := LinearMap.ker_eq_top.mp htop
    exact sub_eq_zero.mp h0
  obtain ⟨c, hc⟩ := hd
  rcases c with _ | _ | c
  · omega
  · omega
  · exfalso
    have h2 : 2 * e ≤ e * (c + 1 + 1) := by nlinarith
    omega

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
