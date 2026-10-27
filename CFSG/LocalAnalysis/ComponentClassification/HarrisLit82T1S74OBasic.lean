module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74XBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73C

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Model

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem commute_spinJ₂_spinJ₃_odd' (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    ∀ b ∈ spinJ₂ K, ∀ c ∈ spinJ₃ K, b * c = c * b := fun _ hb _ hc =>
  commute_spinJ₂_spinJ₃_odd (odd_card_spin hp hp2 hK) hb hc

theorem eq_one_or_eq_spinZ_of_mem_sup_odd (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {x : spinGroup (quadOdd 3 K)} (hx1 : x ∈ spinJ₁ K) (hx : x ∈ spinJ₂ K ⊔ spinJ₃ K) :
    x = 1 ∨ x = spinZ K := by
  have hodd := odd_card_spin hp hp2 hK
  obtain ⟨b, hb, c, hc, rfl⟩ := exists_mul_of_mem_sup (commute_spinJ₂_spinJ₃_odd' hp hp2 hK) hx
  have hker : (((⟨(b * c)⁻¹, inv_mem hx1⟩, ⟨b, hb⟩), ⟨c, hc⟩) :
      (spinJ₁ K × spinJ₂ K) × spinJ₃ K) ∈ (spinMulOdd hodd).ker := by
    rw [MonoidHom.mem_ker, spinMulOdd_apply]
    show (b * c)⁻¹ * b * c = 1
    group
  rcases (mem_ker_spinMulOdd_iff hp hp2 hK _).mp hker with h | h
  · left
    have h' : ((b * c)⁻¹ : spinGroup (quadOdd 3 K)) = 1 := by
      have := congrArg (fun v : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        (v.1.1 : spinGroup (quadOdd 3 K))) h
      simpa using this
    exact inv_eq_one.mp h'
  · right
    have h' : ((b * c)⁻¹ : spinGroup (quadOdd 3 K)) = spinZ K := by
      have := congrArg (fun v : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        (v.1.1 : spinGroup (quadOdd 3 K))) h
      simpa using this
    calc b * c = ((b * c)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (spinZ K)⁻¹ := by rw [h']
      _ = spinZ K := inv_eq_of_mul_eq_one_right
          (CliffordAlgebra.spinGroup.negOne_mul_self _ (nondegenerate_quadOdd 3 K).ne_zero)

theorem spinJ₂_inf_spinJ₃_odd (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    spinJ₂ K ⊓ spinJ₃ K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact (mem_bot).mpr ((spinJ_inf_eq_one_odd hp hp2 hK).2.2 (mem_inf.mp hx).1 (mem_inf.mp hx).2)

theorem card_spinJ₂_sup_spinJ₃_odd (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    Nat.card ↥(spinJ₂ K ⊔ spinJ₃ K) = Nat.card ↥(spinJ₂ K) * Nat.card ↥(spinJ₃ K) :=
  card_sup_of_commute (commute_spinJ₂_spinJ₃_odd' hp hp2 hK) (spinJ₂_inf_spinJ₃_odd hp hp2 hK)

theorem sup_inf_uThree_odd (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    (spinJ₂ K ⊔ spinJ₃ K) ⊓ uThree K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxs, hxu⟩ := mem_inf.mp hx
  rcases eq_one_or_eq_spinZ_of_mem_sup_odd hp hp2 hK (uThree_le_spinJ₁ hxu) hxs with h | h
  · exact (mem_bot).mpr h
  · exact absurd (h ▸ hxu) (spinZ_not_mem_uThree hp hp2 hK)

theorem eq_of_mul_eq_mul_J₂J₃_odd (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {b b' c c' : spinGroup (quadOdd 3 K)} (hb : b ∈ spinJ₂ K) (hb' : b' ∈ spinJ₂ K)
    (hc : c ∈ spinJ₃ K) (hc' : c' ∈ spinJ₃ K) (h : b * c = b' * c') : b = b' ∧ c = c' := by
  have e : b'⁻¹ * b = c' * c⁻¹ := by
    calc b'⁻¹ * b = b'⁻¹ * (b * c) * c⁻¹ := by group
      _ = b'⁻¹ * (b' * c') * c⁻¹ := by rw [h]
      _ = c' * c⁻¹ := by group
  have h3 : b'⁻¹ * b ∈ spinJ₃ K := by
    rw [e]
    exact mul_mem hc' (inv_mem hc)
  have h1 : b'⁻¹ * b = 1 :=
    (spinJ_inf_eq_one_odd hp hp2 hK).2.2 (mul_mem (inv_mem hb') hb) h3
  refine ⟨(inv_mul_eq_one.mp h1).symm, ?_⟩
  rw [e] at h1
  exact (mul_inv_eq_one.mp h1).symm

theorem centralizer_inf_eq_odd (hA2 : A2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) =
        (spinJ₂ K ⊔ spinJ₃ K) ⊔ uThree K := by
  have hodd := odd_card_spin hp hp2 hK
  obtain ⟨hJ₁C, hJ₂C, hJ₃C⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  have hzS : spinZ K ∈ (spinJ₂ K ⊔ spinJ₃ K) ⊔ uThree K :=
    mem_sup_left (spinZ_mem_sup hp hp2 hK)
  apply le_antisymm
  · intro x hx
    have hxE : x ∈ spinE K := hA2 K hodd hx
    have hxq := (mem_inf.mp hx).2
    rw [← range_spinMulOdd hodd] at hxE
    obtain ⟨⟨⟨a, b⟩, c⟩, rfl⟩ := hxE
    rw [spinMulOdd_apply] at hxq ⊢
    change (a : spinGroup (quadOdd 3 K)) * b * c ∈ _
    change (a : spinGroup (quadOdd 3 K)) * b * c ∈ centralizer _ at hxq
    have hbq : (b : spinGroup (quadOdd 3 K)) * qThree K = qThree K * b :=
      (commute_spinJ₁_spinJ₂ qThree_mem_spinJ₁ b.2).symm
    have hcq : (c : spinGroup (quadOdd 3 K)) * qThree K = qThree K * c :=
      (commute_spinJ₁_spinJ₃ qThree_mem_spinJ₁ c.2).symm
    have haq : (a : spinGroup (quadOdd 3 K)) * qThree K = qThree K * a :=
      comm_left_of_comm hbq hcq (mem_centralizer_singleton_iff.mp hxq)
    have haS : (a : spinGroup (quadOdd 3 K)) ∈ (spinJ₂ K ⊔ spinJ₃ K) ⊔ uThree K := by
      rcases mem_J₁_centralizer_qThree a.2 haq with ha | ha
      · exact mem_sup_right ha
      · have e : (a : spinGroup (quadOdd 3 K)) = (spinZ K)⁻¹ * (spinZ K * a) :=
          (inv_mul_cancel_left _ _).symm
        rw [e]
        exact mul_mem (inv_mem hzS) (mem_sup_right ha)
    exact mul_mem (mul_mem haS (mem_sup_left (mem_sup_left b.2)))
      (mem_sup_left (mem_sup_right c.2))
  · exact sup_le (sup_le (le_inf hJ₂C fun _ hb => mem_centralizer_singleton_iff.mpr
      (commute_spinJ₁_spinJ₂ qThree_mem_spinJ₁ hb).symm) (le_inf hJ₃C fun _ hc =>
        mem_centralizer_singleton_iff.mpr (commute_spinJ₁_spinJ₃ qThree_mem_spinJ₁ hc).symm))
      (le_inf (uThree_le_spinJ₁.trans hJ₁C) uThree_le_centralizer)

theorem card_centralizer_inf_odd (hA2 : A2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    Nat.card ↥(centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) =
        Nat.card ↥(spinJ₂ K) * Nat.card ↥(spinJ₃ K) * Nat.card K := by
  rw [centralizer_inf_eq_odd hA2 hp hp2 hK, card_sup_of_commute
    (fun x hx u hu => (commute_spinJ₁_sup (uThree_le_spinJ₁ hu) hx).symm)
    (sup_inf_uThree_odd hp hp2 hK), card_spinJ₂_sup_spinJ₃_odd hp hp2 hK, card_uThree]

theorem tSeven_mem_commutator_odd (hA4 : A4) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : tSeven K ∈ ⁅spinJ₂ K, spinJ₂ K⁆ := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := odd_card_spin hp hp2 hK
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(spinJ₂ K)) := inferInstance
  have hP : (P : Subgroup ↥(spinJ₂ K)).map (spinJ₂ K).subtype ≤ spinJ₂ K := map_subtype_le _
  have hP2 : IsPGroup 2 ↥((P : Subgroup ↥(spinJ₂ K)).map (spinJ₂ K).subtype) :=
    P.isPGroup'.map _
  have hPi : ¬ 2 ∣ ((P : Subgroup ↥(spinJ₂ K)).map (spinJ₂ K).subtype).relIndex (spinJ₂ K) := by
    have e : ((P : Subgroup ↥(spinJ₂ K)).map (spinJ₂ K).subtype).subgroupOf (spinJ₂ K) =
        (P : Subgroup ↥(spinJ₂ K)) :=
      comap_map_eq_self_of_injective (spinJ₂ K).subtype_injective _
    show ¬ 2 ∣ (((P : Subgroup ↥(spinJ₂ K)).map (spinJ₂ K).subtype).subgroupOf (spinJ₂ K)).index
    rw [e]
    exact P.not_dvd_index
  set P₂ := (P : Subgroup ↥(spinJ₂ K)).map (spinJ₂ K).subtype with hP₂
  obtain ⟨⟨a, ha, b, hb, -, -, hab⟩, -⟩ := (hA4 K hodd).2 P₂ hP hP2 hPi
  have hCle : ⁅P₂, P₂⁆ ≤ P₂ := commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hCp : IsPGroup 2 ↥⁅P₂, P₂⁆ := hP2.to_le hCle
  have hab1 : ⁅a, b⁆ ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hC1 : Nat.card ↥⁅P₂, P₂⁆ ≠ 1 := by
    rw [Ne, Subgroup.card_eq_one]
    intro h
    have hm := commutator_mem_commutator ha hb
    rw [h, mem_bot] at hm
    exact hab1 hm
  have hC2 : 2 ∣ Nat.card ↥⁅P₂, P₂⁆ := hCp.card_eq_or_dvd.resolve_left hC1
  have : Fintype ↥⁅P₂, P₂⁆ := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := ↥⁅P₂, P₂⁆) 2
    (by rwa [← Nat.card_eq_fintype_card])
  have hy' : orderOf (y : spinGroup (quadOdd 3 K)) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hyy : (y : spinGroup (quadOdd 3 K)) * y = 1 := by
    have h := pow_orderOf_eq_one (y : spinGroup (quadOdd 3 K))
    rwa [hy', pow_two] at h
  have hy1 : (y : spinGroup (quadOdd 3 K)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy'
    exact absurd hy' (by norm_num)
  have hyt : (y : spinGroup (quadOdd 3 K)) = tSeven K :=
    ((hA4 K hodd).1 _ (hP (hCle y.2)) hyy).resolve_left hy1
  have htC : tSeven K ∈ ⁅P₂, P₂⁆ := hyt ▸ y.2
  exact commutator_mono hP hP htC

end Model

end CFSG.ComponentClassification.HarrisLit.T1.S74
