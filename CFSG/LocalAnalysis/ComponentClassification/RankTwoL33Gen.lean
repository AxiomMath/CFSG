module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL33Cert
public import CFSG.GH74.KGroups.L33Tables
public import CFSG.GH74.E2.K0Simple

public section

namespace CFSG.ComponentClassification.RankTwoL33

open Subgroup CFSG.GH74 CFSG.GH74.E2 CFSG.GH74.KGroups

variable {K : Type} [Group K]

@[expose] def fixSubgroup (φ : MulAut K) : Subgroup K where
  carrier := {x | φ x = x}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := map_one φ
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_fixSubgroup {φ : MulAut K} {x : K} : x ∈ fixSubgroup φ ↔ φ x = x := Iff.rfl

theorem eq_top_of_dvd [Finite K] [IsSimpleGroup K] (hK : Nat.card K = 5616) (H : Subgroup K)
    (h48 : 48 ∣ Nat.card H) (h13 : 13 ∣ Nat.card H) : H = ⊤ := by
  have h624 : 624 ∣ Nat.card H :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h48 h13
  obtain ⟨m, hm⟩ := h624
  have hmul := H.card_mul_index
  rw [hK, hm] at hmul
  have hmi : m * H.index = 9 :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 624) (by rw [← mul_assoc]; omega)
  have hi : H.index ∣ 9 := Dvd.intro_left m hmi
  rcases H.normalCore_normal.eq_bot_or_eq_top with h | h
  · exfalso
    have hd := H.index_normalCore_dvd_factorial_index
    rw [h, Subgroup.index_bot, hK] at hd
    have hle : H.index ≤ 9 := Nat.le_of_dvd (by norm_num) hi
    have h9 := dvd_trans hd (Nat.factorial_dvd_factorial hle)
    revert h9
    decide
  · exact eq_top_iff.2 (h ▸ H.normalCore_le)

section Model

variable {G : Type*} [Group G] (M : AutModel K G)

theorem card_eq_card_inf_centralizer (σ : G) (S : Subgroup K)
    (hS : ∀ x : K, x ∈ S ↔ (M.e x : G) * σ = σ * (M.e x : G)) :
    Nat.card S = Nat.card ↥(M.P ⊓ centralizer ({σ} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(M.e x : G), (M.e x).2,
        mem_centralizer_singleton_iff.2 ((hS x).1 x.2)⟩
      invFun := fun y => ⟨M.e.symm ⟨y, (mem_inf.1 y.2).1⟩, (hS _).2 (by
        rw [MulEquiv.apply_symm_apply]
        exact mem_centralizer_singleton_iff.1 (mem_inf.1 y.2).2)⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp }

theorem fix_iff (φ : MulAut K) (x : K) :
    φ x = x ↔ (M.e x : G) * (M.Φ φ : G) = (M.Φ φ : G) * (M.e x : G) := by
  constructor
  · intro h
    have h1 := M.spec φ x
    rw [h] at h1
    calc (M.e x : G) * (M.Φ φ : G)
        = ((M.Φ φ : G) * (M.e x : G) * (M.Φ φ : G)⁻¹) * (M.Φ φ : G) := by rw [← h1]
      _ = (M.Φ φ : G) * (M.e x : G) := by group
  · intro h
    apply M.e.injective
    apply Subtype.ext
    rw [M.spec φ x, ← h, mul_inv_cancel_right]

end Model

theorem sup_fixSubgroup_eq_top (hK : ShapeL33 K) {α β : MulAut K} (hα2 : α ^ 2 = 1)
    (hβ2 : β ^ 2 = 1) (hα1 : α ≠ 1) (hβ1 : β ≠ 1) (hαβ : α ≠ β) (hc : α * β = β * α) :
    fixSubgroup α ⊔ fixSubgroup β ⊔ fixSubgroup (α * β) = ⊤ := by
  obtain ⟨e⟩ := L33.equiv_of_lieModel hK
  obtain ⟨M, hP, hA⟩ := L33.autModel e
  have hfacts := ShapeL33.facts hK
  have := hfacts.1
  have : Finite K := L33.finite_K e
  have hcardK : Nat.card K = 5616 := by rw [L33.card_K e]; norm_num
  have hcen : center K = ⊥ := center_eq_bot_of_simple_of_not_prime hfacts.2.2
  have hsound := fourGenCheck_sound L33.QA L33.QP L33.QA_ok L33.QP_ok l33_fourgen_ok
  have hPcard : ∀ σ : Equiv.Perm (Fin 26), Nat.card ↥(M.P ⊓ centralizer ({σ} : Set _)) =
      Nat.card ↥(L33.QP.originalSubgroup ⊓ centralizer ({σ} : Set _)) := fun σ => by rw [hP]
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkc : k ∈ center K := mem_center_iff.2 fun x => by
      have h := congrArg (fun φ : MulAut K => φ x) hk
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc x * k = k * x * k⁻¹ * k := by rw [h]
        _ = k * x := by group
    rw [hcen] at hkc
    exact hkc
  have hIcard : Nat.card (MulAut.conj : K →* MulAut K).range = 5616 := by
    rw [← hcardK]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hIindex : (MulAut.conj : K →* MulAut K).range.index = 2 := by
    have h := (MulAut.conj : K →* MulAut K).range.card_mul_index
    rw [hIcard, L33.card_mulAut e] at h
    omega
  have key : ∀ ψ φ : MulAut K, ψ ∈ (MulAut.conj : K →* MulAut K).range → ψ ^ 2 = 1 →
      φ ^ 2 = 1 → ψ ≠ 1 → φ ≠ 1 → φ ≠ ψ → φ * ψ = ψ * φ →
      fixSubgroup ψ ⊔ fixSubgroup φ = ⊤ := by
    intro ψ φ hψI hψ2 hφ2 hψ1 hφ1 hne hcomm
    obtain ⟨k, rfl⟩ := hψI
    have hk1 : k ≠ 1 := fun h => hψ1 (by rw [h, map_one])
    have hk2 : k ^ 2 = 1 := by
      apply hinj
      rw [map_pow, hψ2, map_one]
    have hfix : fixSubgroup (MulAut.conj k) = centralizer ({k} : Set K) := by
      ext x
      rw [mem_fixSubgroup, mem_centralizer_singleton_iff, MulAut.conj_apply]
      constructor
      · intro h
        calc x * k = k * x * k⁻¹ * k := by rw [h]
          _ = k * x := by group
      · intro h
        rw [← h, mul_inv_cancel_right]
    have hek : (M.e k : Equiv.Perm (Fin 26)) ∈ L33.QP.originalSubgroup := hP ▸ (M.e k).2
    have hfix48 : Nat.card (fixSubgroup (MulAut.conj k)) = 48 := by
      rw [hfix, card_eq_card_inf_centralizer M (M.e k : Equiv.Perm (Fin 26)) _ (fun x => by
        rw [mem_centralizer_singleton_iff, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
          ← map_mul, ← map_mul, Subtype.ext_iff.symm.trans M.e.injective.eq_iff]), hPcard]
      refine hsound.1 _ hek ?_ ?_
      · rw [← Subgroup.coe_pow, ← map_pow, hk2, map_one, Subgroup.coe_one]
      · intro h
        apply hk1
        apply M.e.injective
        rw [map_one]
        exact Subtype.ext h
    set s : Equiv.Perm (Fin 26) := (M.Φ (MulAut.conj k) : Equiv.Perm (Fin 26)) with hs
    set b : Equiv.Perm (Fin 26) := (M.Φ φ : Equiv.Perm (Fin 26)) with hb
    have hsA : s ∈ L33.QA.originalSubgroup := hA ▸ (M.Φ (MulAut.conj k)).2
    have hbA : b ∈ L33.QA.originalSubgroup := hA ▸ (M.Φ φ).2
    have hs2 : s ^ 2 = 1 := by rw [hs, ← M.Φ_pow, hψ2, M.Φ_one]
    have hb2 : b ^ 2 = 1 := by rw [hb, ← M.Φ_pow, hφ2, M.Φ_one]
    have hs1 : s ≠ 1 := fun h => hψ1 ((M.Φ_eq_one).1 h)
    have hb1 : b ≠ 1 := fun h => hφ1 ((M.Φ_eq_one).1 h)
    have hbs : b ≠ s := fun h => hne (M.Φ.injective (Subtype.ext h))
    have hbcomm : b * s = s * b := M.Φ_comm hcomm
    have hs48 : Nat.card ↥(L33.QP.originalSubgroup ⊓
        centralizer ({s} : Set (Equiv.Perm (Fin 26)))) = 48 := by
      rw [← hPcard, ← card_eq_card_inf_centralizer M s (fixSubgroup (MulAut.conj k))
        (fun x => (fix_iff M _ x))]
      exact hfix48
    obtain ⟨c₁, hc₁, c₂, hc₂, h13, h1⟩ := hsound.2 s hsA hs2 hs1 hs48 b hbA hb2 hb1 hbs hbcomm
    have hc₁P : c₁ ∈ M.P := hP ▸ (mem_inf.1 hc₁).1
    have hc₂P : c₂ ∈ M.P := hP ▸ (mem_inf.1 hc₂).1
    set x₁ : K := M.e.symm ⟨c₁, hc₁P⟩ with hx₁
    set x₂ : K := M.e.symm ⟨c₂, hc₂P⟩ with hx₂
    have hex₁ : (M.e x₁ : Equiv.Perm (Fin 26)) = c₁ := by rw [hx₁, MulEquiv.apply_symm_apply]
    have hex₂ : (M.e x₂ : Equiv.Perm (Fin 26)) = c₂ := by rw [hx₂, MulEquiv.apply_symm_apply]
    have hx₁F : x₁ ∈ fixSubgroup (MulAut.conj k) := by
      rw [mem_fixSubgroup, fix_iff M, hex₁]
      exact mem_centralizer_singleton_iff.1 (mem_inf.1 hc₁).2
    have hx₂F : x₂ ∈ fixSubgroup φ := by
      rw [mem_fixSubgroup, fix_iff M, hex₂]
      exact mem_centralizer_singleton_iff.1 (mem_inf.1 hc₂).2
    have hord : orderOf (x₁ * x₂) = 13 := by
      have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
      rw [← MulEquiv.orderOf_eq M.e, ← Subgroup.orderOf_coe, map_mul, Subgroup.coe_mul, hex₁,
        hex₂]
      exact orderOf_eq_prime h13 h1
    set H := fixSubgroup (MulAut.conj k) ⊔ fixSubgroup φ
    have hx : x₁ * x₂ ∈ H := mul_mem (mem_sup_left hx₁F) (mem_sup_right hx₂F)
    refine eq_top_of_dvd hcardK H ?_ ?_
    · rw [← hfix48]
      exact card_dvd_of_le le_sup_left
    · have h' : orderOf (⟨x₁ * x₂, hx⟩ : H) = 13 := by
        rw [← Subgroup.orderOf_coe]
        exact hord
      rw [← h']
      exact orderOf_dvd_natCard _
  have hab2 : (α * β) ^ 2 = 1 := by
    rw [sq, show α * β * (α * β) = α * (β * α) * β by group, ← hc,
      show α * (α * β) * β = (α * α) * (β * β) by group, ← sq, ← sq, hα2, hβ2, one_mul]
  have hab1 : α * β ≠ 1 := by
    intro h
    have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hα2)
    exact hαβ ((eq_inv_of_mul_eq_one_right h).trans hαinv).symm
  have hneab : α ≠ α * β := fun h => hβ1 (by
    have := congrArg (fun x => α⁻¹ * x) h
    simpa using this.symm)
  by_cases hαI : α ∈ (MulAut.conj : K →* MulAut K).range
  · have h := key α β hαI hα2 hβ2 hα1 hβ1 (Ne.symm hαβ) hc.symm
    rw [eq_top_iff, ← h]
    exact sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left)
  by_cases hβI : β ∈ (MulAut.conj : K →* MulAut K).range
  · have h := key β α hβI hβ2 hα2 hβ1 hα1 hαβ hc
    rw [eq_top_iff, ← h]
    exact sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)
  have habI : α * β ∈ (MulAut.conj : K →* MulAut K).range :=
    (Subgroup.mul_mem_iff_of_index_two hIindex).2 (iff_of_false hαI hβI)
  have h := key (α * β) α habI hab2 hα2 hab1 hα1 hneab (by rw [mul_assoc α β α, ← hc])
  rw [eq_top_iff, ← h]
  exact sup_le le_sup_right (le_sup_left.trans le_sup_left)

end CFSG.ComponentClassification.RankTwoL33
