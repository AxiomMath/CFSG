module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenCore
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenEamAmb
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenCo2
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BTwoBLocal
public import CFSG.Monster.GMS.BabyTwoAAutBridge

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.LieType.Chevalley.C2E6Std

structure C0Seven : Prop where
  oPrime : ∀ s : ↥stdGroup, orderOf s = 7 →
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({s} : Set ↥stdGroup)) = ⊥
  noSix : ∀ s : ↥stdGroup, orderOf s = 7 →
    ∀ r ∈ Subgroup.centralizer ({s} : Set ↥stdGroup), orderOf r ≠ 6

@[expose] def Co2Seven : Prop :=
  ∀ s : NativeSporadic.Co2, orderOf s = 7 → ∀ M : Subgroup NativeSporadic.Co2,
    M ≤ Subgroup.centralizer ({s} : Set NativeSporadic.Co2) → Odd (Nat.card M) →
    ¬ 7 ∣ Nat.card M → M = ⊥

private theorem odd_eq_bot_of_conj_hom_two_kernel {G Q : Type*} [Group G] [Finite G] [Group Q]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {s t c : G} (hc : c * t * c⁻¹ = s)
    (F : ↥(Subgroup.centralizer ({s} : Set G)) →* Q) (hker : IsPGroup 2 F.ker)
    (hQ : ∀ q : Q, orderOf q = p → ∀ M : Subgroup Q, M ≤ Subgroup.centralizer ({q} : Set Q) →
      Odd (Nat.card M) → ¬ p ∣ Nat.card M → M = ⊥)
    {x : G} (hxt : x ∈ Subgroup.centralizer ({t} : Set G)) (hx : orderOf x = p)
    {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
    (hodd : Odd (Nat.card K)) (hKp : ¬ p ∣ Nat.card K) : K = ⊥ := by
  obtain ⟨F', hF'⟩ : ∃ F' : ↥(Subgroup.centralizer ({t} : Set G)) →* Q,
      F' = F.comp (CFSG.Monster.B.GSide.centralizerConjEquiv c hc).symm.toMonoidHom :=
    ⟨_, rfl⟩
  have hker' : IsPGroup 2 F'.ker := by
    rw [hF', ← MonoidHom.comap_ker]
    exact hker.comap_of_injective _ (CFSG.Monster.B.GSide.centralizerConjEquiv c hc).symm.injective
  have hx' : orderOf (F' ⟨x, hxt⟩) = p := by
    have hdvd := orderOf_map_dvd F' ⟨x, hxt⟩
    rw [Subgroup.orderOf_mk, hx] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h
    · exfalso
      have hmem : (⟨x, hxt⟩ : ↥(Subgroup.centralizer ({t} : Set G))) ∈ F'.ker :=
        MonoidHom.mem_ker.2 (orderOf_eq_one_iff.1 h1)
      obtain ⟨n, hn⟩ := hker' ⟨_, hmem⟩
      have hxn : x ^ (2 ^ n) = 1 := by
        have h := congrArg
          (fun z : ↥F'.ker => ((z : ↥(Subgroup.centralizer ({t} : Set G))) : G)) hn
        simpa using h
      have hp2n : p ∣ 2 ^ n := by
        rw [← hx]
        exact orderOf_dvd_of_pow_eq_one hxn
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hp2n))
    · exact h
  exact odd_eq_bot_of_hom_two_kernel hxt F' hker' (hQ _ hx') hK hodd hKp

section Glue



theorem eq_bot_of_babyInv_zero (hC : C0Seven) {v x : NativeSporadic.B} (hv : BabyInv 0 v)
    (hxv : x ∈ Subgroup.centralizer ({v} : Set NativeSporadic.B)) (hx : orderOf x = 7)
    {K : Subgroup NativeSporadic.B}
    (hK : K ≤ Subgroup.centralizer ({x} : Set NativeSporadic.B) ⊓
      Subgroup.centralizer ({v} : Set NativeSporadic.B))
    (hKn : ∀ g ∈ Subgroup.centralizer ({x} : Set NativeSporadic.B) ⊓
      Subgroup.centralizer ({v} : Set NativeSporadic.B), ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hodd : Odd (Nat.card K)) (hK7 : ¬ 7 ∣ Nat.card K) : K = ⊥ := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨ψ⟩ := nonempty_centralizer_mulEquiv_Eam CFSG.Monster.Existence.babyTableIII hv
  obtain ⟨hidx, -, hcen, hcen', hZ2, ⟨φ⟩, -⟩ :=
    CFSG.Monster.B.TwoA.Amalgam.short_F4_derived_standard_perfect_cover
  have hZY : Subgroup.zpowers CFSG.Monster.B.TwoA.Amalgam.cE' ≤
      commutator ↥CFSG.Monster.B.TwoA.Amalgam.Eam := by
    rw [← hcen']
    exact Subgroup.map_subtype_le _
  exact eam_odd_eq_bot_ambient (by norm_num) (by norm_num) hcen.symm.le hZ2 hidx hZY φ hC.oPrime ψ
    hxv hx hK hKn hodd hK7

theorem eq_bot_of_babyInv_one (hC : Co2Seven) {t x : NativeSporadic.B} (ht : BabyInv 1 t)
    (hxt : x ∈ Subgroup.centralizer ({t} : Set NativeSporadic.B)) (hx : orderOf x = 7)
    {K : Subgroup NativeSporadic.B}
    (hK : K ≤ Subgroup.centralizer ({x} : Set NativeSporadic.B) ⊓
      Subgroup.centralizer ({t} : Set NativeSporadic.B))
    (hodd : Odd (Nat.card K)) (hK7 : ¬ 7 ∣ Nat.card K) : K = ⊥ := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨F, -, hF⟩ := exists_hom_centralizer_xB
  obtain ⟨c, hc⟩ :=
    isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 1 t xB ht babyInv_one_xB)
  exact odd_eq_bot_of_conj_hom_two_kernel (by norm_num) (by norm_num) hc F (IsPGroup.of_card hF)
    hC hxt hx hK hodd hK7

theorem le_center_of_babyInv_zero (hC : C0Seven) {α x : NativeSporadic.B} (hα : BabyInv 0 α)
    (hxα : x ∈ Subgroup.centralizer ({α} : Set NativeSporadic.B)) (hx : orderOf x = 7)
    {w y : NativeSporadic.B}
    (hw : w ∈ Subgroup.centralizer ({x} : Set NativeSporadic.B) ⊓
      Subgroup.centralizer ({α} : Set NativeSporadic.B))
    (hy : y ∈ Subgroup.centralizer ({x} : Set NativeSporadic.B) ⊓
      Subgroup.centralizer ({α} : Set NativeSporadic.B))
    (hw6 : w ^ 6 = 1) (hw2 : w ^ 2 ≠ 1 ∧ w ^ 2 ≠ α) (hw3 : w ^ 3 ≠ 1 ∧ w ^ 3 ≠ α)
    (hwy : w ^ 3 * y * (w ^ 3)⁻¹ * y⁻¹ ≠ 1 ∧ w ^ 3 * y * (w ^ 3)⁻¹ * y⁻¹ ≠ α)
    {K : Subgroup NativeSporadic.B}
    (hK : K ≤ Subgroup.centralizer ({x} : Set NativeSporadic.B) ⊓
      Subgroup.centralizer ({α} : Set NativeSporadic.B))
    (hKn : ∀ g ∈ Subgroup.centralizer ({x} : Set NativeSporadic.B) ⊓
      Subgroup.centralizer ({α} : Set NativeSporadic.B), ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hK7 : ¬ 7 ∣ Nat.card K) : ∀ k ∈ K, k = 1 ∨ k = α := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨ψ⟩ := nonempty_centralizer_mulEquiv_Eam CFSG.Monster.Existence.babyTableIII hα
  obtain ⟨hidx, -, hcen, hcen', hZ2, ⟨φ⟩, -⟩ :=
    CFSG.Monster.B.TwoA.Amalgam.short_F4_derived_standard_perfect_cover
  have hZY : Subgroup.zpowers CFSG.Monster.B.TwoA.Amalgam.cE' ≤
      commutator ↥CFSG.Monster.B.TwoA.Amalgam.Eam := by
    rw [← hcen']
    exact Subgroup.map_subtype_le _
  obtain ⟨hα2, hα1⟩ := orderOf_eq_prime_iff.1 hα.1
  have hαα : α ∈ Subgroup.centralizer ({α} : Set NativeSporadic.B) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hψα : ψ ⟨α, hαα⟩ ∈ Subgroup.zpowers CFSG.Monster.B.TwoA.Amalgam.cE' := by
    rw [← hcen, Subgroup.mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul]
    apply congrArg ψ
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 h.2
  exact eam_le_center_ambient (by norm_num) (by norm_num) hcen.symm.le hZ2 hidx hZY φ hC.oPrime
    hC.noSix ψ hα2 hα1 ⟨hαα, hψα⟩ hxα hx hw hy hw6 hw2 hw3 hwy hK hKn hK7

theorem card_gLAPPrimeCoreOf_B_le_two (hC0 : C0Seven) (hCo2 : Co2Seven)
    (hcensus : ∃ p : NativeSporadic.B, orderOf p = 7 ∧
      ∀ x : NativeSporadic.B, orderOf x = 7 → IsConj x p)
    (helems : ∃ x α y a b w : NativeSporadic.B, orderOf x = 7 ∧ BabyInv 0 α ∧
      α * x = x * α ∧ BabyInv 0 a ∧ BabyInv 0 b ∧ BabyInv 1 (a * b) ∧ a * x = x * a ∧
      b * x = x * b ∧ a * b = b * a ∧ a ≠ b ∧ a * α = α * a ∧ a ≠ α ∧ orderOf y = 5 ∧
      y * x = x * y ∧ y * α = α * y ∧ w * x = x * w ∧ w * α = α * w ∧ w ^ 6 = 1 ∧ w ^ 2 ≠ 1 ∧
      w ^ 3 = a ∧ a * y * a⁻¹ * y⁻¹ ≠ 1 ∧ a * y * a⁻¹ * y⁻¹ ≠ α) :
    ∀ x : NativeSporadic.B, orderOf x = 7 →
      Nat.card (GLAPPrimeCoreOf 7 (Subgroup.centralizer ({x} : Set NativeSporadic.B))) ≤ 2 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨p, -, hconj⟩ := hcensus
  obtain ⟨x₀, α, y, a, b, w, hx₀, hα, hαx, ha, hb, hab, hax, hbx, habc, hab1, -, haα1, -, hyx,
    hyα, hwx, hwα, hw6, hw2, hw3, hay1, hayα⟩ := helems
  have hinv : ∀ {k : Fin 4} {v : NativeSporadic.B}, BabyInv k v → v ^ 2 = 1 ∧ v ≠ 1 :=
    fun hv => orderOf_eq_prime_iff.1 hv.1
  have hx₀ab : x₀ ∈ Subgroup.centralizer ({a * b} : Set NativeSporadic.B) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x₀ * (a * b) = x₀ * a * b := (mul_assoc _ _ _).symm
      _ = a * x₀ * b := by rw [hax]
      _ = a * (x₀ * b) := mul_assoc _ _ _
      _ = a * (b * x₀) := by rw [hbx]
      _ = a * b * x₀ := (mul_assoc _ _ _).symm
  have hw2α : w ^ 2 ≠ α := by
    intro h
    apply (hinv hα).2
    calc α = α ^ 2 * α := by rw [(hinv hα).1, one_mul]
      _ = (w ^ 2) ^ 3 := by rw [h]; exact (pow_succ α 2).symm
      _ = w ^ 6 := (pow_mul w 2 3).symm
      _ = 1 := hw6
  have hmain : Nat.card (GLAPPrimeCoreOf 7
      (Subgroup.centralizer ({x₀} : Set NativeSporadic.B))) ≤ 2 := by
    refine card_gLAPPrimeCoreOf_le_two (by norm_num)
      (Subgroup.mem_centralizer_singleton_iff.2 hax) (Subgroup.mem_centralizer_singleton_iff.2 hbx)
      (Subgroup.mem_centralizer_singleton_iff.2 hαx) (hinv ha).1 (hinv hb).1 habc (hinv ha).2
      (hinv hb).2 hab1 (hinv hα).1 (hinv hα).2 ?_ ?_
    · intro v hv K hK hodd h7 hKn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · exact eq_bot_of_babyInv_zero hC0 ha (Subgroup.mem_centralizer_singleton_iff.2 hax.symm)
          hx₀ hK hKn hodd h7
      · exact eq_bot_of_babyInv_zero hC0 hb (Subgroup.mem_centralizer_singleton_iff.2 hbx.symm)
          hx₀ hK hKn hodd h7
      · exact eq_bot_of_babyInv_one hCo2 hab hx₀ab hx₀ hK hodd h7
    · intro K hK h7 hKn
      refine le_center_of_babyInv_zero hC0 hα (Subgroup.mem_centralizer_singleton_iff.2 hαx.symm)
        hx₀ ⟨Subgroup.mem_centralizer_singleton_iff.2 hwx,
          Subgroup.mem_centralizer_singleton_iff.2 hwα⟩
        ⟨Subgroup.mem_centralizer_singleton_iff.2 hyx,
          Subgroup.mem_centralizer_singleton_iff.2 hyα⟩ hw6 ⟨hw2, hw2α⟩ ?_ ?_ hK hKn h7
      · rw [hw3]
        exact ⟨(hinv ha).2, haα1⟩
      · rw [hw3]
        exact ⟨hay1, hayα⟩
  intro x hx
  obtain ⟨c, hc⟩ := isConj_iff.1 ((hconj x₀ hx₀).trans (hconj x hx).symm)
  rw [← hc, card_gLAPPrimeCoreOf_centralizer_conj]
  exact hmain

end Glue

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

