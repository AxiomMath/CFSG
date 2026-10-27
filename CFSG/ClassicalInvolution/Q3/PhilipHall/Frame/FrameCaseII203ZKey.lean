module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf36Outer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

open Out


theorem mem_sup_decomp_of_normalizes {G : Type} [Group G] {A B : Subgroup G}
    (hAB : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) {y : G} (hy : y ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  let T : Subgroup G :=
    { carrier := {y | ∃ a ∈ A, ∃ b ∈ B, y = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        exact ⟨a₁ * (b₁ * a₂ * b₁⁻¹), A.mul_mem ha₁ (hAB b₁ hb₁ a₂ ha₂), b₁ * b₂,
          B.mul_mem hb₁ hb₂, by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact ⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, hAB b⁻¹ (B.inv_mem hb) a⁻¹ (A.inv_mem ha), b⁻¹,
          B.inv_mem hb, by group⟩ }
  have hle : A ⊔ B ≤ T :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := hle hy
  exact ⟨a, ha, b, hb, hab⟩

theorem zpow_eq_one_or_self_203Z {Q : Type} [Group Q] {g : Q} (hg : g * g = 1) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g := by
  have h2 : g ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hg]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

section Frame203Z

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

abbrev X203 (K K' : Subgroup G) (z : G) : Subgroup G :=
  sec20X (CoreAssembly.conjClass K) z K K'

abbrev N203 (K K' : Subgroup G) (z : G) : Subgroup G :=
  oddCoreOf (X203 K K' z) ⊔ (K ⊔ K')

theorem N203_le_X203 (K K' : Subgroup G) (z : G) : N203 K K' z ≤ X203 K K' z :=
  sup_le (oddCoreOf_le_self _) (sup_le le_sec20X_left le_sec20X_right)

theorem N203_le_kerG (d : Std20Frame K K' J S R R' W V z t) : N203 K K' z ≤ kerG K :=
  sup_le (fun y hy => oddCoreX_le_kerG d hy)
    (sup_le (fun y hy => K_le_kerG d hy) (fun y hy => K'_le_kerG d hy))

theorem conj_mem_N203 (d : Std20Frame K K' J S R R' W V z t) {x n : G}
    (hx : x ∈ X203 K K' z) (hn : n ∈ N203 K K' z) : x * n * x⁻¹ ∈ N203 K K' z := by
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := frameX_le_N d hx
  have hxK' : x ∈ Subgroup.normalizer (K' : Set G) := ((sec20X_le_normalizers_frame d) hx).2
  have hxX : x ∈ Subgroup.normalizer (X203 K K' z : Set G) := Subgroup.le_normalizer hx
  have hle : N203 K K' z ≤ (N203 K K' z).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (fun m hm => ?_) (sup_le (fun k hk => ?_) (fun k hk => ?_))
    · show x * m * x⁻¹ ∈ N203 K K' z
      exact Subgroup.mem_sup_left (mem_normalizer_oddCoreOf_of_mem_normalizer hxX hm)
    · show x * k * x⁻¹ ∈ N203 K K' z
      exact Subgroup.mem_sup_right (Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.mp hxK k).mp hk))
    · show x * k * x⁻¹ ∈ N203 K K' z
      exact Subgroup.mem_sup_right (Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp hxK' k).mp hk))
  exact hle hn

theorem not_mem_N203_of_outer (d : Std20Frame K K' J S R R' W V z t) {v : G} (hvV : v ∈ V)
    (hvv : v * v ≠ 1) : v ∉ N203 K K' z := by
  intro hv
  obtain ⟨e⟩ := kbar_equiv_q8 d
  obtain ⟨h, hpsi⟩ := mem_kerG.mp (N203_le_kerG d hv)
  exact (frame203Outer G K K' J S R R' W V z t d v hvV hvv).1
    ((Out.psiK_eq_one_iff K e ⟨v, h⟩).mp hpsi)

theorem K_le_N203 (K K' : Subgroup G) (z : G) : K ≤ N203 K K' z :=
  le_sup_left.trans le_sup_right

theorem K'_le_N203 (K K' : Subgroup G) (z : G) : K' ≤ N203 K K' z :=
  le_sup_right.trans le_sup_right

theorem V_le_X203 (d : Std20Frame K K' J S R R' W V z t) : V ≤ X203 K K' z := by
  have hVC : V ≤ Subgroup.centralizer ({z} : Set G) := d.hVS.trans d.hSz
  exact le_trans (le_iSup₂ (f := fun U
      (_ : U ∈ {U : Subgroup G | U ∈ USet (CoreAssembly.conjClass K) ∧
        U ≤ Subgroup.centralizer ({z} : Set G)}) => U) V ⟨d.hV, hVC⟩)
    (le_sup_left.trans le_sup_left)

theorem isSylow2In_S_inf_X203 (d : Std20Frame K K' J S R R' W V z t) :
    IsSylow2In ((S : Subgroup G) ⊓ X203 K K' z) (X203 K K' z) :=
  Sec7.isSylow2In_inf_of_normal d.late_isSylow2In_S
    (sec20X_le_centralizer (le_trans le_sup_left d.sup_le_centralizer_z)
      (le_trans le_sup_right d.sup_le_centralizer_z))
    (le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins)

theorem isSylow2In_top_subgroupOf (d : Std20Frame K K' J S R R' W V z t) :
    IsSylow2In (((S : Subgroup G) ⊓ X203 K K' z).subgroupOf (X203 K K' z)) ⊤ := by
  have h := Hall196.isSylow2In_subgroupOf_of_le (isSylow2In_S_inf_X203 d)
    (le_refl (X203 K K' z))
  rwa [Subgroup.subgroupOf_self] at h

theorem USet_le_N203_sup_V (d : Std20Frame K K' J S R R' W V z t) {U : Subgroup G}
    (hU : U ∈ USet (CoreAssembly.conjClass K))
    (hUN : U ≤ N203 K K' z ⊔ ((S : Subgroup G) ⊓ X203 K K' z)) :
    U ≤ N203 K K' z ⊔ V := by
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ hU
  have hNX : N203 K K' z ⊔ ((S : Subgroup G) ⊓ X203 K K' z) ≤ X203 K K' z :=
    sup_le (N203_le_X203 K K' z) inf_le_right
  have hPsyl : IsSylow2In ((S : Subgroup G) ⊓ X203 K K' z)
      (N203 K K' z ⊔ ((S : Subgroup G) ⊓ X203 K K' z)) :=
    S1916.IsSylow2In.of_le (isSylow2In_S_inf_X203 d) le_sup_right hNX
  obtain ⟨y, hyNP, hUy⟩ := Sec7.exists_conj_le_of_isSylow2In hPsyl hU2 hUN
  obtain ⟨n, hn, p, hp, rfl⟩ := mem_sup_decomp_of_normalizes
    (fun b hb a ha => conj_mem_N203 d (Subgroup.mem_inf.mp hb).2 ha) hyNP
  have hnX : n ∈ X203 K K' z := N203_le_X203 K K' z hn
  have hnK : n ∈ Subgroup.normalizer (K : Set G) := frameX_le_N d hnX
  have hnK' : n ∈ Subgroup.normalizer (K' : Set G) :=
    ((sec20X_le_normalizers_frame d) hnX).2
  have hU'P : conjSub n⁻¹ U ≤ (S : Subgroup G) ⊓ X203 K K' z := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx
    have h := mem_conjSub_iff.mp (hUy hx)
    have e : (n * p)⁻¹ * (n * x * n⁻¹) * (n * p) = p⁻¹ * x * p := by group
    rw [e] at h
    have e2 : p * (p⁻¹ * x * p) * p⁻¹ = x := by group
    rw [← e2]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hp h) (Subgroup.inv_mem _ hp)
  have hU'S : conjSub n⁻¹ U ≤ (S : Subgroup G) := hU'P.trans inf_le_left
  have hU'U : conjSub n⁻¹ U ∈ USet (CoreAssembly.conjClass K) :=
    USet.conj d.hyp.conjInvariant hU n⁻¹
  intro u hu
  have hx : n⁻¹ * u * n ∈ conjSub n⁻¹ U := by
    rw [mem_conjSub_iff, inv_inv]
    have e : n * (n⁻¹ * u * n) * n⁻¹ = u := by group
    rw [e]
    exact hu
  have hback : ∀ w : G, n * (n⁻¹ * w * n) * n⁻¹ = w := fun w => by group
  have hKN : K ≤ N203 K K' z := K_le_N203 K K' z
  have hK'N : K' ≤ N203 K K' z := K'_le_N203 K K' z
  rcases d.U_cases hU'U hU'S with hW | hK | hK'
  · have hWVK : n⁻¹ * u * n ∈ V ⊔ (W ⊓ K) :=
      (d.W_le_V_sup_K (hexAllF G K K' J S R R' W V z t d) : W ≤ V ⊔ (W ⊓ K)) (hW hx)
    have hcm : V ⊔ (W ⊓ K) ≤ (N203 K K' z ⊔ V).comap (MulAut.conj n).toMonoidHom := by
      refine sup_le (fun v hv => ?_) (fun k hk => ?_)
      · show n * v * n⁻¹ ∈ N203 K K' z ⊔ V
        have e : n * v * n⁻¹ = (n * (v * n⁻¹ * v⁻¹)) * v := by group
        rw [e]
        exact Subgroup.mul_mem_sup
          (Subgroup.mul_mem _ hn (conj_mem_N203 d (V_le_X203 d hv) (Subgroup.inv_mem _ hn)))
          hv
      · show n * k * n⁻¹ ∈ N203 K K' z ⊔ V
        exact Subgroup.mem_sup_left (hKN ((Subgroup.mem_normalizer_iff.mp hnK k).mp
          (Subgroup.mem_inf.mp hk).2))
    have h1 : n * (n⁻¹ * u * n) * n⁻¹ ∈ N203 K K' z ⊔ V := hcm hWVK
    rwa [hback u] at h1
  · have h1 : n * (n⁻¹ * u * n) * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hnK _).mp (hK hx)
    rw [hback u] at h1
    exact Subgroup.mem_sup_left (hKN h1)
  · have h1 : n * (n⁻¹ * u * n) * n⁻¹ ∈ K' :=
      (Subgroup.mem_normalizer_iff.mp hnK' _).mp (hK' hx)
    rw [hback u] at h1
    exact Subgroup.mem_sup_left (hK'N h1)

theorem conj_mem_N203_sup_V_of_mem (d : Std20Frame K K' J S R R' W V z t) {v₀ x : G}
    (hv₀V : v₀ ∈ V) (hgen : ∀ w ∈ V, ∃ n : ℤ, w = v₀ ^ n)
    (h : x⁻¹ * v₀ * x ∈ N203 K K' z ⊔ ((S : Subgroup G) ⊓ X203 K K' z)) :
    x⁻¹ * v₀ * x ∈ N203 K K' z ⊔ V := by
  have hU : conjSub x⁻¹ V ∈ USet (CoreAssembly.conjClass K) :=
    USet.conj d.hyp.conjInvariant d.hV x⁻¹
  have hUle : conjSub x⁻¹ V ≤ N203 K K' z ⊔ ((S : Subgroup G) ⊓ X203 K K' z) := by
    intro w hw
    rw [mem_conjSub_iff, inv_inv] at hw
    obtain ⟨k, hk⟩ := hgen _ hw
    have hc : (x⁻¹ * v₀ * x) ^ k = x⁻¹ * v₀ ^ k * x := by
      have := conj_zpow (a := x⁻¹) (b := v₀) (i := k)
      rwa [inv_inv] at this
    have e : w = (x⁻¹ * v₀ * x) ^ k := by
      rw [hc, ← hk]
      group
    rw [e]
    exact (N203 K K' z ⊔ ((S : Subgroup G) ⊓ X203 K K' z)).zpow_mem h k
  have hxV : x⁻¹ * v₀ * x ∈ conjSub x⁻¹ V := by
    rw [mem_conjSub_iff, inv_inv]
    have e : x * (x⁻¹ * v₀ * x) * x⁻¹ = v₀ := by group
    rw [e]
    exact hv₀V
  exact USet_le_N203_sup_V d hU hUle hxV

theorem exists_conj_mem_N203_sup_V (d : Std20Frame K K' J S R R' W V z t) {U : Subgroup G}
    (hU : U ∈ USet (CoreAssembly.conjClass K)) (hUX : U ≤ X203 K K' z) :
    ∃ y ∈ X203 K K' z, ∀ w ∈ U, y⁻¹ * w * y ∈ N203 K K' z ⊔ V := by
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ hU
  obtain ⟨y, hyX, hUy⟩ := Sec7.exists_conj_le_of_isSylow2In (isSylow2In_S_inf_X203 d) hU2 hUX
  refine ⟨y, hyX, fun w hw => ?_⟩
  have hU' : conjSub y⁻¹ U ∈ USet (CoreAssembly.conjClass K) :=
    USet.conj d.hyp.conjInvariant hU y⁻¹
  have hU'P : conjSub y⁻¹ U ≤ N203 K K' z ⊔ ((S : Subgroup G) ⊓ X203 K K' z) := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx
    have h := mem_conjSub_iff.mp (hUy hx)
    have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rw [e] at h
    exact Subgroup.mem_sup_right h
  have hmem' : y⁻¹ * w * y ∈ conjSub y⁻¹ U := by
    rw [mem_conjSub_iff, inv_inv]
    have e : y * (y⁻¹ * w * y) * y⁻¹ = w := by group
    rw [e]
    exact hw
  exact USet_le_N203_sup_V d hU' hU'P hmem'

end Frame203Z

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

end
