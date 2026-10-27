module

public import CFSG.ClassicalInvolution.Q3.E29Ker.Rels
public import CFSG.ClassicalInvolution.Q3.E29Ker.Count
public import CFSG.ClassicalInvolution.Q3.E29Ker.Elements
public import CFSG.ClassicalInvolution.Q3.E29Ker.ModelCard
public import CFSG.ClassicalInvolution.Q3.TL3T8

public section

namespace CFSG.ClassicalInvolution.Q3.E29Ker

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.E29Data
open CFSG.Certificates.CosetEnumeration
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan pSpan_le)
open CFSG.ClassicalInvolution.Q3.E64Ker (threeCent mem_threeCent_of_normalizes threeCent_conj)

theorem ker_eq_of_le {X Y : Type} [Group X] [Group Y] [Finite X] (φ : X →* Y)
    (hrange : 86016 ≤ Nat.card φ.range) {N : Subgroup X} (hN : N ≤ φ.ker)
    (hX : Nat.card X ≤ 86016 * Nat.card N) : φ.ker = N := by
  have hcard : Nat.card X = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have h1 : Nat.card φ.ker ≤ Nat.card N := by
    have h2 : 86016 * Nat.card φ.ker ≤ 86016 * Nat.card N :=
      calc 86016 * Nat.card φ.ker ≤ Nat.card φ.range * Nat.card φ.ker :=
            Nat.mul_le_mul_right _ hrange
        _ = Nat.card X := hcard.symm
        _ ≤ _ := hX
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hN h1).symm

theorem conj_comm_of_normalizes {X : Type} [Group X] {K : Subgroup X} {z y : X}
    (hz : IsUniqueInvolution K z) (hyn : ∀ k ∈ K, y * k * y⁻¹ ∈ K) : y * z = z * y := by
  have hmem := hyn z hz.mem
  have ht2 : (y * z * y⁻¹) * (y * z * y⁻¹) = 1 := by
    calc (y * z * y⁻¹) * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have ht1 : y * z * y⁻¹ ≠ 1 := by
    intro h1
    apply hz.ne_one
    calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  have h3 := (hz.unique _ hmem ht2).resolve_left ht1
  calc y * z = y * z * y⁻¹ * y := by group
    _ = z * y := by rw [h3]

section Aux

variable {X : Type} [Group X] {φ : X →* AEQ 8} {Q : Set (Subgroup X)}

namespace Lab

variable (F : Lab φ Q)

theorem closure_gen_eq_top (H : Hyp φ Q)
    (hgen : pSpan Q = ⊤) : Subgroup.closure (F.gen '' Set.Iio 56) = ⊤ := by
  rw [eq_top_iff, ← hgen]
  exact pSpan_le fun L hL => F.le_closure_gen H hL

theorem partner_mem_N0 (hn : ∀ p ∈ e29Partners, F.np p ∈ Subgroup.center X) {p : ℕ}
    (hp : p ∈ e29Partners) :
    evalWord (codeVal F.gen) (partnerRel29 p) ∈ F.N0 := by
  rw [evalWord_partnerRel29, F.gen_zero]
  have hc : ∀ x : X, x * F.np p = F.np p * x := Subgroup.mem_center_iff.mp (hn p hp)
  have hzj : F.zj p = F.z1 * F.np p := by
    unfold Lab.np
    group
  have hgg : F.gen (2 * p) * F.gen (2 * p) = F.z1 * F.np p := by
    rw [← hzj, F.zj_eq_sq]
  have hconj : F.z1 * F.np p * F.z1⁻¹ = F.np p := by
    rw [hc F.z1]
    group
  have hval : F.a * F.a * (F.gen (2 * p))⁻¹ * (F.gen (2 * p))⁻¹ = (F.np p)⁻¹ := by
    calc F.a * F.a * (F.gen (2 * p))⁻¹ * (F.gen (2 * p))⁻¹ =
          F.z1 * (F.gen (2 * p) * F.gen (2 * p))⁻¹ := by
          unfold Lab.z1
          group
      _ = (F.z1 * F.np p * F.z1⁻¹)⁻¹ := by
          rw [hgg]
          group
      _ = (F.np p)⁻¹ := by rw [hconj]
  rw [hval]
  exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨p, hp, rfl⟩)

end Lab

end Aux

theorem e29_ker_le_threeClosure' {X : Type} [Group X]
    [Finite X] (φ : X →* AE.AEQ 8) (hφ : φ.range = AE.e29Sub)
    (hker : φ.ker ≤ Subgroup.center X) (hker2 : IsPGroup 2 φ.ker)
    (Q : Set (Subgroup X)) (hgen : pSpan Q = ⊤)
    (hconj : ∀ L ∈ Q, ∀ x : X, conjSub x L ∈ Q) (hord : ∀ L ∈ Q, Nat.card L = 8)
    (hlab : ∀ L ∈ Q, ∃ α ∈ AE.e29Sets, ∃ (h : α.card = 4) (b : Bool),
      L.map φ = AE.memBar α h b)
    (hsurj : ∀ α ∈ AE.e29Sets, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Q,
      L.map φ = AE.memBar α h b)
    (hinj : ∀ L ∈ Q, ∀ L' ∈ Q, L.map φ = L'.map φ → L = L')
    {K : Subgroup X} (hK : K ∈ Q) {z : X} (hz : IsUniqueInvolution K z) :
    φ.ker ≤ Subgroup.closure {w : X | w * z = z * w ∧ ∃ a : ℕ, w ^ 3 ^ a = 1} := by
  have H : Hyp φ Q := ⟨hφ, hconj, hord, hlab, hsurj, hinj⟩
  obtain ⟨F⟩ := Lab.exists_lab H
  obtain ⟨j₀, -, rfl⟩ := F.exists_L H hK
  have hz1 : IsUniqueInvolution F.K1 F.z1 := F.isUniqueInvolution_K1 H
  have hzeq : z = F.zj j₀ := hz.eq (F.isUniqueInvolution_L H j₀)
  have hnker : ∀ p ∈ e29Partners, F.np p ∈ φ.ker := fun p hp => F.np_mem_ker H hp
  have hnc : ∀ p ∈ e29Partners, F.np p ∈ Subgroup.center X := fun p hp => hker (hnker p hp)
  have hN0ker : F.N0 ≤ φ.ker := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨p, hp, rfl⟩
    exact hnker p hp
  have hbound : Nat.card X ≤ 86016 * Nat.card F.N0 :=
    card_le_of_enum F.gen (F.closure_gen_eq_top H hgen) (hN0ker.trans hker) (F.eval_rels H)
      (fun p hp => F.partner_mem_N0 hnc hp) (U := F.K1) (by rw [F.gen_zero]; exact F.a_mem)
      (by rw [F.gen_one]; exact F.b_mem) (by rw [hord F.K1 F.mem_Q])
  have hrange : 86016 ≤ Nat.card φ.range := by
    rw [hφ]
    exact le_card_e29Sub
  have hkereq : φ.ker = F.N0 := ker_eq_of_le φ hrange hN0ker hbound
  obtain ⟨y, ⟨n, hy3⟩, hy⟩ := F.exists_y H
  have hy0 := hy 0 (by simp)
  rw [F.L_zero] at hy0
  have hyz : y * F.z1 = F.z1 * y := conj_comm_of_normalizes hz1 hy0.1
  have h1 : F.z1 ∈ threeCent F.z1 :=
    mem_threeCent_of_normalizes hz1 (F.pow_four_K1 H) hy3 hy0.1 hy0.2 (F.central_K1 H) hyz
  have hnT : ∀ p ∈ e29Partners, F.np p ∈ threeCent F.z1 := by
    intro p hp
    have hyp := hy p (List.mem_cons_of_mem _ hp)
    have hc : ∀ x : X, x * F.np p = F.np p * x := Subgroup.mem_center_iff.mp (hnc p hp)
    have hKz : ∀ k ∈ F.L p, k * F.z1 = F.z1 * k := by
      intro k hk
      have h := F.central_L H p k hk
      have hzj : F.zj p = F.z1 * F.np p := by
        unfold Lab.np
        group
      rw [hzj] at h
      have h' : k * F.z1 * F.np p = F.z1 * k * F.np p :=
        calc k * F.z1 * F.np p = k * (F.z1 * F.np p) := by group
          _ = F.z1 * F.np p * k := h
          _ = F.z1 * (F.np p * k) := by group
          _ = F.z1 * (k * F.np p) := by rw [hc k]
          _ = F.z1 * k * F.np p := by group
      exact mul_right_cancel h'
    have h2 : F.zj p ∈ threeCent F.z1 :=
      mem_threeCent_of_normalizes (F.isUniqueInvolution_L H p) (F.pow_four_L H p) hy3 hyp.1 hyp.2
        hKz hyz
    exact mul_mem (inv_mem h1) h2
  have hkerT : φ.ker ≤ threeCent F.z1 := by
    rw [hkereq]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨p, hp, rfl⟩
    exact hnT p hp
  show φ.ker ≤ threeCent z
  rw [hzeq]
  intro x hx
  have hxT : (F.T j₀)⁻¹ * x * F.T j₀ = x := by
    have := Subgroup.mem_center_iff.mp (hker hx) (F.T j₀)⁻¹
    rw [this]
    group
  have hmem : x ∈ conjSub (F.T j₀) (threeCent F.z1) := by
    rw [mem_conjSub_iff, hxT]
    exact hkerT hx
  rw [← threeCent_conj] at hmem
  exact hmem

end CFSG.ClassicalInvolution.Q3.E29Ker
