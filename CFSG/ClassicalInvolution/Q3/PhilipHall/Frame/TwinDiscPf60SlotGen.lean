module

public import CFSG.ClassicalInvolution.Asc77.AscIHLie

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

theorem mulAut_eq_one_of_trivial_mod {X Q : Type} [Group X] [Group Q] {Φ : Set (Subgroup X)}
    (hgen : omegaGen Φ = ⊤) (f : X →* Q) (ζ : MulAut X)
    (hperm : ∀ L ∈ Φ, ∃ L' ∈ Φ, L.map ζ.toMonoidHom = L')
    (hζf : ∀ x, f (ζ x) = f x)
    (hinj : ∀ M ∈ Φ, ∀ M' ∈ Φ, M.map f = M'.map f → M = M')
    (hker : ∀ M ∈ Φ, ∀ m ∈ M, f m = 1 → m = 1) : ζ = 1 := by
  have hfix : ∀ M ∈ Φ, ∀ m ∈ M, ζ m = m := by
    intro M hM m hm
    obtain ⟨M', hM', hMM'⟩ := hperm M hM
    have h1 : M'.map f = M.map f := by
      rw [← hMM', Subgroup.map_map]
      have : f.comp ζ.toMonoidHom = f := MonoidHom.ext hζf
      rw [this]
    have hM'M : M' = M := hinj M' hM' M hM h1
    have hζm : ζ m ∈ M := by
      have : ζ m ∈ M.map ζ.toMonoidHom := Subgroup.mem_map_of_mem _ hm
      rw [hMM', hM'M] at this
      exact this
    have h2 : ζ m * m⁻¹ = 1 := hker M hM _ (M.mul_mem hζm (M.inv_mem hm)) (by
      rw [map_mul, map_inv, hζf]; exact mul_inv_cancel _)
    exact mul_inv_eq_one.mp h2
  have hS : omegaGen Φ ≤ MonoidHom.eqLocus ζ.toMonoidHom (MonoidHom.id X) :=
    iSup₂_le fun M hM m hm => hfix M hM m hm
  rw [hgen] at hS
  ext x
  exact hS (Subgroup.mem_top x)

theorem exists_fixed_odd_lift_central {X M : Type} [Group X] [Finite X] [Group M] (φ : X →* M)
    (hker : φ.ker ≤ Subgroup.center X) (h2 : IsPGroup 2 φ.ker) (ζ : MulAut X) (ζM : MulAut M)
    (hζ : ∀ x, φ (ζ x) = ζM (φ x)) {b : M} (hbr : b ∈ φ.range) (hodd : Odd (orderOf b))
    (hfix : ζM b = b) : ∃ h : X, φ h = b ∧ ζ h = h := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, rfl⟩ := hbr
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hcop : Nat.Coprime (2 ^ k) (orderOf (φ y)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime (x := φ y) hcop
  have hkerexp : ∀ κ : φ.ker, κ ^ (2 ^ k) = 1 := by
    intro κ
    rw [← hk]
    exact pow_card_eq_one'
  refine ⟨(y ^ 2 ^ k) ^ u, ?_, ?_⟩
  · rw [map_pow, map_pow]
    exact hu
  ·
    set κ : X := y⁻¹ * ζ y with hκ
    have hκk : κ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hκ, map_mul, map_inv, hζ, hfix]
      exact inv_mul_cancel _
    have hκc : κ ∈ Subgroup.center X := hker hκk
    have hζy : ζ y = y * κ := by rw [hκ]; group
    have hκe : κ ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val (hkerexp ⟨κ, hκk⟩)
      simpa using this
    have hcomm : Commute y κ := Subgroup.mem_center_iff.mp hκc y
    rw [map_pow, map_pow, hζy, hcomm.mul_pow, hκe, mul_one]

theorem exists_commuting_odd_lift_central {X M : Type} [Group X] [Finite X] [Group M] (φ : X →* M)
    (hker : φ.ker ≤ Subgroup.center X) (h2 : IsPGroup 2 φ.ker) (t : X) {b : M} (hbr : b ∈ φ.range)
    (hodd : Odd (orderOf b)) (hfix : b * φ t = φ t * b) : ∃ h : X, φ h = b ∧ h * t = t * h := by
  obtain ⟨h, hh, hfx⟩ := exists_fixed_odd_lift_central φ hker h2 (MulAut.conj t) (MulAut.conj (φ t))
    (fun x => by simp [MulAut.conj_apply]) hbr hodd (by
      simp only [MulAut.conj_apply]
      calc φ t * b * (φ t)⁻¹ = (b * φ t) * (φ t)⁻¹ := by rw [← hfix]
        _ = b := by group)
  refine ⟨h, hh, ?_⟩
  simp only [MulAut.conj_apply] at hfx
  calc h * t = (t * h * t⁻¹) * t := by rw [hfx]
    _ = t * h := by group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
