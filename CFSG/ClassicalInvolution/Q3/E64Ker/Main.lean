module

public import CFSG.ClassicalInvolution.Q3.E64Ker.Rels
public import CFSG.ClassicalInvolution.Q3.E64Ker.Count
public import CFSG.ClassicalInvolution.Q3.E64Ker.Elements
public import CFSG.ClassicalInvolution.Q3.E64Ker.ModelCard
public import CFSG.ClassicalInvolution.Q3.TL3T8

public section

namespace CFSG.ClassicalInvolution.Q3.E64Ker

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.E64Data
open CFSG.Certificates.CosetEnumeration
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan pSpan_le)

theorem ker_eq_zpowers {X Y : Type} [Group X] [Group Y] [Finite X] (φ : X →* Y)
    (hrange : 10752 ≤ Nat.card φ.range) {n₀ : X} (hn₀ : n₀ ∈ φ.ker)
    (hX : Nat.card X ≤ 10752 * Nat.card (Subgroup.zpowers n₀)) :
    φ.ker = Subgroup.zpowers n₀ := by
  have hle : Subgroup.zpowers n₀ ≤ φ.ker := Subgroup.zpowers_le.mpr hn₀
  have hcard : Nat.card X = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have h1 : Nat.card φ.ker ≤ Nat.card (Subgroup.zpowers n₀) := by
    have h2 : 10752 * Nat.card φ.ker ≤ 10752 * Nat.card (Subgroup.zpowers n₀) :=
      calc 10752 * Nat.card φ.ker ≤ Nat.card φ.range * Nat.card φ.ker :=
            Nat.mul_le_mul_right _ hrange
        _ = Nat.card X := hcard.symm
        _ ≤ _ := hX
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hle h1).symm

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

variable {X : Type} [Group X] {φ : X →* AEQ 7} {Q : Set (Subgroup X)}

namespace Lab

variable (F : Lab φ Q)

theorem closure_gen_eq_top (H : Hyp φ Q)
    (hgen : pSpan Q = ⊤) : Subgroup.closure (F.gen '' Set.Iio 28) = ⊤ := by
  rw [eq_top_iff, ← hgen]
  exact pSpan_le fun L hL => F.le_closure_gen H hL

theorem partner_mem_zpowers (hn0 : F.n0 ∈ Subgroup.center X) :
    evalWord (codeVal F.gen) e64Partner ∈ Subgroup.zpowers F.n0 := by
  rw [evalWord_partner, F.gen_zero]
  have hc : ∀ x : X, x * F.n0 = F.n0 * x := Subgroup.mem_center_iff.mp hn0
  have hzj : F.zj e64JStar = F.z1 * F.n0 := by
    unfold Lab.n0
    group
  have hgg : F.gen 4 * F.gen 4 = F.z1 * F.n0 := by
    rw [← hzj, F.zj_eq_sq]
    rfl
  have hconj : F.z1 * F.n0 * F.z1⁻¹ = F.n0 := by
    rw [hc F.z1]
    group
  have hval : F.a * F.a * (F.gen 4)⁻¹ * (F.gen 4)⁻¹ = F.n0⁻¹ := by
    calc F.a * F.a * (F.gen 4)⁻¹ * (F.gen 4)⁻¹ = F.z1 * (F.gen 4 * F.gen 4)⁻¹ := by
          unfold Lab.z1
          group
      _ = (F.z1 * F.n0 * F.z1⁻¹)⁻¹ := by
          rw [hgg]
          group
      _ = F.n0⁻¹ := by rw [hconj]
  rw [hval]
  exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

end Lab

end Aux

theorem e64_ker_le_threeClosure' {X : Type} [Group X]
    [Finite X] (φ : X →* AE.AEQ 7) (hφ : φ.range = AE.e64Sub)
    (hker : φ.ker ≤ Subgroup.center X) (hker2 : IsPGroup 2 φ.ker)
    (Q : Set (Subgroup X)) (hgen : pSpan Q = ⊤)
    (hconj : ∀ L ∈ Q, ∀ x : X, conjSub x L ∈ Q) (hord : ∀ L ∈ Q, Nat.card L = 8)
    (hlab : ∀ L ∈ Q, ∃ α ∈ AE.e64Sets, ∃ (h : α.card = 4) (b : Bool),
      L.map φ = AE.memBar α h b)
    (hsurj : ∀ α ∈ AE.e64Sets, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Q,
      L.map φ = AE.memBar α h b)
    (hinj : ∀ L ∈ Q, ∀ L' ∈ Q, L.map φ = L'.map φ → L = L')
    {K : Subgroup X} (hK : K ∈ Q) {z : X} (hz : IsUniqueInvolution K z) :
    φ.ker ≤ Subgroup.closure {w : X | w * z = z * w ∧ ∃ a : ℕ, w ^ 3 ^ a = 1} := by
  have H : Hyp φ Q := ⟨hφ, hconj, hord, hlab, hsurj, hinj⟩
  obtain ⟨F⟩ := Lab.exists_lab H
  obtain ⟨j₀, -, rfl⟩ := F.exists_L H hK
  have hz1 : IsUniqueInvolution F.K1 F.z1 := F.isUniqueInvolution_K1 H
  have hzeq : z = F.zj j₀ := hz.eq (F.isUniqueInvolution_L H j₀)
  have hn0 : F.n0 ∈ φ.ker := F.n0_mem_ker H
  have hn0c : F.n0 ∈ Subgroup.center X := hker hn0
  have hbound : Nat.card X ≤ 10752 * Nat.card (Subgroup.zpowers F.n0) :=
    card_le_of_enum F.gen (F.closure_gen_eq_top H hgen) hn0c (F.eval_rels H)
      (F.partner_mem_zpowers hn0c) (U := F.K1) (by rw [F.gen_zero]; exact F.a_mem)
      (by rw [F.gen_one]; exact F.b_mem) (by rw [hord F.K1 F.mem_Q])
  have hrange : 10752 ≤ Nat.card φ.range := by
    rw [hφ]
    exact le_card_e64Sub
  have hkereq : φ.ker = Subgroup.zpowers F.n0 := ker_eq_zpowers φ hrange hn0 hbound
  obtain ⟨y, ⟨n, hy3⟩, hyn1, hynt1, hynj, hyntj⟩ := F.exists_y H
  have hyz : y * F.z1 = F.z1 * y := conj_comm_of_normalizes hz1 hyn1
  have hc : ∀ x : X, x * F.n0 = F.n0 * x := Subgroup.mem_center_iff.mp hn0c
  have hKz : ∀ k ∈ F.L e64JStar, k * F.z1 = F.z1 * k := by
    intro k hk
    have h := F.central_L H e64JStar k hk
    have hzj : F.zj e64JStar = F.z1 * F.n0 := by
      unfold Lab.n0
      group
    rw [hzj] at h
    have h' : k * F.z1 * F.n0 = F.z1 * k * F.n0 :=
      calc k * F.z1 * F.n0 = k * (F.z1 * F.n0) := by group
        _ = F.z1 * F.n0 * k := h
        _ = F.z1 * (F.n0 * k) := by group
        _ = F.z1 * (k * F.n0) := by rw [hc k]
        _ = F.z1 * k * F.n0 := by group
    exact mul_right_cancel h'
  have h1 : F.z1 ∈ threeCent F.z1 :=
    mem_threeCent_of_normalizes hz1 (F.pow_four_K1 H) hy3 hyn1 hynt1 (F.central_K1 H) hyz
  have h2 : F.zj e64JStar ∈ threeCent F.z1 :=
    mem_threeCent_of_normalizes (F.isUniqueInvolution_L H e64JStar) (F.pow_four_L H e64JStar) hy3
      hynj hyntj hKz hyz
  have hn0T : F.n0 ∈ threeCent F.z1 := mul_mem (inv_mem h1) h2
  have hkerT : φ.ker ≤ threeCent F.z1 := by
    rw [hkereq, Subgroup.zpowers_le]
    exact hn0T
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

end CFSG.ClassicalInvolution.Q3.E64Ker
