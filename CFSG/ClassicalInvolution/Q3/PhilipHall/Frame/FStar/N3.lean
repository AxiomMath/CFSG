module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf32Psi

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Out
open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)
open Equiv

theorem fpf_coord_of_cube :
    ∀ x : P3, x ^ 3 = 1 → x ≠ 1 → (∀ i, x.1 i ≠ i) ∨ (∀ i, x.2 i ≠ i) := by
  decide

theorem exists_fpf_of_card {H : Subgroup P3} (h : Nat.card H = 6 ∨ Nat.card H = 18) :
    ∃ x ∈ H, (∀ i, x.1 i ≠ i) ∨ (∀ i, x.2 i ≠ i) := by
  have h3 : 3 ∣ Nat.card H := by rcases h with h | h <;> rw [h] <;> norm_num
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 h3
  refine ⟨y, y.2, fpf_coord_of_cube _ ?_ ?_⟩
  · have := pow_orderOf_eq_one y
    rw [hy] at this
    exact congrArg Subtype.val this
  · intro h1
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy
    norm_num at hy


variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem exists_psiK_fpf (hC : Frame203Cent) (hO : Frame203Outer)
    (d : Std20Frame K K' J S R R' W V z t) (h3 : ¬ Concl20_3 K K' V z) :
    ∃ y : ↥(Subgroup.normalizer (K : Set G)), ∀ I, psiK K y I ≠ I := by
  obtain ⟨g, hg, hgK⟩ := d.swap
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := frameX_le_N d
  have hXN2 : ∀ y ∈ X, g⁻¹ * y * g ∈ Subgroup.normalizer (K : Set G) := fun y hy =>
    conj_swap_mem_normalizer d hg hgK ((sec20X_le_normalizers_frame d) hy).2
  obtain ⟨e⟩ := kbar_equiv_q8 d
  have hc3 : Nat.card (Idx2 (Kbar K)) = 3 := card_idx2_of_equiv_q8 e
  have hf : Fintype.card (Idx2 (Kbar K)) = 3 := by rw [← Nat.card_eq_fintype_card]; exact hc3
  let eT : Idx2 (Kbar K) ≃ Fin 3 := Fintype.equivFinOfCardEq hf
  let m : Equiv.Perm (Idx2 (Kbar K)) →* Equiv.Perm (Fin 3) := eT.permCongrHom.toMonoidHom
  have hm : ∀ σ, m σ = eT.permCongr σ := fun σ => rfl
  have hminj : ∀ σ, m σ = 1 → σ = 1 := fun σ h =>
    (map_eq_one_iff _ eT.permCongrHom.injective).mp h
  let ψ : ↥X →* P3 := (m.comp (psi1 K X hXN)).prod (m.comp (psi2 K X g hXN2))
  have hψ1 : ∀ x, (ψ x).1 = eT.permCongr (psi1 K X hXN x) := fun x => rfl
  have hψ2 : ∀ x, (ψ x).2 = eT.permCongr (psi2 K X g hXN2 x) := fun x => rfl
  have hfin : ∀ x, ((∀ i, (ψ x).1 i ≠ i) ∨ (∀ i, (ψ x).2 i ≠ i)) →
      ∃ y : ↥(Subgroup.normalizer (K : Set G)), ∀ I, psiK K y I ≠ I := by
    intro x hx
    rcases hx with hx | hx
    · refine ⟨⟨x, hXN x.2⟩, fun I hI => hx (eT I) ?_⟩
      rw [hψ1, Equiv.permCongr_apply, Equiv.symm_apply_apply, psi1_apply, hI]
    · refine ⟨⟨g⁻¹ * x * g, hXN2 x x.2⟩, fun I hI => hx (eT I) ?_⟩
      rw [hψ2, Equiv.permCongr_apply, Equiv.symm_apply_apply, psi2_apply, hI]
  have key : ∀ x : ↥X, ψ x = 1 ↔ (psi1 K X hXN x = 1 ∧ psi2 K X g hXN2 x = 1) := by
    intro x
    constructor
    · intro h
      have h1 : m (psi1 K X hXN x) = 1 := congrArg Prod.fst h
      have h2 : m (psi2 K X g hXN2 x) = 1 := congrArg Prod.snd h
      exact ⟨hminj _ h1, hminj _ h2⟩
    · rintro ⟨h1, h2⟩
      apply Prod.ext
      · show m (psi1 K X hXN x) = 1
        rw [h1, map_one]
      · show m (psi2 K X g hXN2 x) = 1
        rw [h2, map_one]
  have hA : oddCoreOf X ⊔ (K ⊔ K') ≤ kerG K ⊓ conjSub g (kerG K) := by
    refine sup_le (fun y hy => ?_) (sup_le (fun y hy => ?_) (fun y hy => ?_))
    · exact ⟨oddCoreX_le_kerG d hy,
        mem_conjSub_iff.mpr (oddCoreX_le_kerG d (conj_swap_oddCore d hg hgK hy))⟩
    · exact ⟨K_le_kerG d hy, mem_conjSub_iff.mpr (K'_le_kerG d (conj_swap_K d hg hgK hy))⟩
    · exact ⟨K'_le_kerG d hy, mem_conjSub_iff.mpr (K_le_kerG d (conj_swap_K' d hg hgK hy))⟩
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  have hVX : V ≤ X := tw.hVX
  have hker : ψ.ker = (oddCoreOf X ⊔ (K ⊔ K')).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, key, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨h1, h2⟩
      have i1 : InnerOn K x := (psiK_eq_one_iff K e ⟨x, hXN x.2⟩).mp h1
      have i2 : InnerOn K (g⁻¹ * x * g) := (psiK_eq_one_iff K e ⟨_, hXN2 x x.2⟩).mp h2
      have i3 : InnerOn K' x := by
        have := innerOn_swap i2
        rwa [hgK] at this
      exact hC G K K' J S R R' W V z t d x x.2 i1 i3
    · intro h
      refine ⟨?_, ?_⟩
      · obtain ⟨_, h1⟩ := mem_kerG.mp (hA h).1
        exact h1
      · obtain ⟨_, h1⟩ := mem_kerG.mp (mem_conjSub_iff.mp (hA h).2)
        exact h1
  have hsign : ∀ x, Perm.sign (ψ x).1 = Perm.sign (ψ x).2 := by
    intro x
    have h := epsK_prod_eq_one d hg hgK e (hO G K K' J S R R' W V z t d) x.2
    rw [epsK_of_mem K (hXN x.2), epsK_of_mem K (hXN2 x x.2)] at h
    show Equiv.Perm.sign (m (psi1 K X hXN x)) = Equiv.Perm.sign (m (psi2 K X g hXN2 x))
    rw [hm, hm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_permCongr]
    change Equiv.Perm.sign (psiK K ⟨x, hXN x.2⟩) =
      Equiv.Perm.sign (psiK K ⟨g⁻¹ * x * g, hXN2 x x.2⟩)
    have h' := eq_inv_of_mul_eq_one_left h
    rw [h', Int.units_inv_eq_self]
  obtain ⟨v, hvV, -, hvv1, hvt⟩ := exists_gen_V d
  have hvX : v ∈ X := hVX hvV
  have hvv : v * v ∈ K ⊔ K' := by rw [hvt]; exact d.htKK
  have hv1 : ψ ⟨v, hvX⟩ ≠ 1 := fun h => by
    obtain ⟨h1, -⟩ := (key ⟨v, hvX⟩).mp h
    exact (hO G K K' J S R R' W V z t d v hvV hvv1).1
      ((psiK_eq_one_iff K e ⟨v, hXN hvX⟩).mp h1)
  set O := oddCoreOf X with hO'
  have hMX : K ⊔ K' ≤ X := sup_le le_sec20X_left le_sec20X_right
  have hvker : (⟨v * v, X.mul_mem hvX hvX⟩ : ↥X) ∈ ψ.ker := by
    rw [hker, Subgroup.mem_subgroupOf]
    exact (le_sup_right : K ⊔ K' ≤ O ⊔ (K ⊔ K')) hvv
  have hy2 : ψ ⟨v, hvX⟩ * ψ ⟨v, hvX⟩ = 1 := by
    have : ψ (⟨v * v, X.mul_mem hvX hvX⟩ : ↥X) = 1 := hvker
    rw [← this, ← map_mul]; rfl
  have hyD := hsign ⟨v, hvX⟩
  have hy1 : (ψ ⟨v, hvX⟩).1 ≠ 1 := by
    intro h
    have h2 : Perm.sign (ψ ⟨v, hvX⟩).2 = 1 := by rw [← hyD, h]; simp
    have h3 : (ψ ⟨v, hvX⟩).2 = 1 :=
      perm3_eq_one_of_even_invol _ (congrArg Prod.snd hy2) h2
    exact hv1 (Prod.ext h h3)
  have hodd : Perm.sign (ψ ⟨v, hvX⟩).1 = -1 := sign_of_invol _ hy1 (congrArg Prod.fst hy2)
  have hrange : ψ.range ≤ signEq := by
    rintro _ ⟨x, rfl⟩
    exact hsign x
  rcases card_of_signEq hrange ⟨ψ ⟨v, hvX⟩, ⟨⟨v, hvX⟩, rfl⟩, hodd⟩ with h2 | h6 | h18
  · refine absurd ?_ h3
    show X = O ⊔ (V ⊔ (K ⊔ K'))
    refine le_antisymm ?_ (sup_le (oddCoreOf_le_self _) (sup_le hVX hMX))
    intro x hx
    by_cases hx1 : ψ ⟨x, hx⟩ = 1
    · have : (⟨x, hx⟩ : ↥X) ∈ ψ.ker := hx1
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact (sup_le le_sup_left ((le_sup_right : K ⊔ K' ≤ V ⊔ (K ⊔ K')).trans le_sup_right) :
        O ⊔ (K ⊔ K') ≤ O ⊔ (V ⊔ (K ⊔ K'))) this
    · have heq := eq_of_card_two h2 (⟨⟨x, hx⟩, rfl⟩ : ψ ⟨x, hx⟩ ∈ ψ.range)
        (⟨⟨v, hvX⟩, rfl⟩ : ψ ⟨v, hvX⟩ ∈ ψ.range) hx1 hv1
      have hk : (⟨x * v⁻¹, X.mul_mem hx (X.inv_mem hvX)⟩ : ↥X) ∈ ψ.ker := by
        show ψ ⟨x * v⁻¹, _⟩ = 1
        have : (⟨x * v⁻¹, X.mul_mem hx (X.inv_mem hvX)⟩ : ↥X) = ⟨x, hx⟩ * ⟨v, hvX⟩⁻¹ := rfl
        rw [this, map_mul, map_inv, heq, mul_inv_cancel]
      rw [hker, Subgroup.mem_subgroupOf] at hk
      have h1 : x * v⁻¹ ∈ O ⊔ (V ⊔ (K ⊔ K')) :=
        (sup_le le_sup_left (le_sup_right.trans le_sup_right) : O ⊔ (K ⊔ K') ≤
          O ⊔ (V ⊔ (K ⊔ K'))) hk
      have h2' : v ∈ O ⊔ (V ⊔ (K ⊔ K')) := Subgroup.mem_sup_right (Subgroup.mem_sup_left hvV)
      have := Subgroup.mul_mem _ h1 h2'
      simpa using this
  · obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_fpf_of_card (Or.inl h6)
    exact hfin x hx
  · obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_fpf_of_card (Or.inr h18)
    exact hfin x hx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar
