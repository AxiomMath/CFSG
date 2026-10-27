module

public import CFSG.LargeExtraspecial.S111BComm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}
  {h k k' : G}

omit [Finite G] in
theorem mem_normalizer_of_conj_mem {H : Type*} [Group H] {N : Subgroup H} {x : H}
    (h1 : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (h2 : ∀ n ∈ N, x⁻¹ * n * x⁻¹⁻¹ ∈ N) :
    x ∈ normalizer (N : Set H) := by
  refine mem_normalizer_iff.mpr fun n => ⟨h1 n, fun hn => ?_⟩
  have := h2 _ hn
  rwa [show x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n by group] at this

theorem Ebar_sup_le (S : Setting G) (k k' : G) :
    Ebar S k k' ⊔ Ebar S k' k ≤ S.Lbar k ⊔ S.Lbar k' :=
  sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

namespace Pair111

variable (P : Pair111 S g A h k k')
include P

theorem Lbar_ne_bot : S.Lbar k ≠ ⊥ := fun h0 => by
  have h1 := P.hy.cons.card_Lbar
  rw [h0, Subgroup.card_bot] at h1
  have h2 := P.hy.hyp4.two_lt_width
  have h3 : 1 < 2 ^ (S.width - 1) := Nat.one_lt_two_pow (by omega)
  omega

theorem commute_of_mem_Ebar {e f : S.O} (he : e ∈ Ebar S k k') (hf : f ∈ Ebar S k' k) :
    e * f = f * e := by
  have h1 : e * f * e⁻¹ * f⁻¹ ∈ S.Lbar k' :=
    mul_mem ((mem_normalizer_iff.mp he.2 f).mp hf.1) (inv_mem hf.1)
  have h2 : e * f * e⁻¹ * f⁻¹ ∈ S.Lbar k := by
    have h3 : f * e⁻¹ * f⁻¹ ∈ S.Lbar k := (mem_normalizer_iff.mp hf.2 e⁻¹).mp (inv_mem he.1)
    have e3 : e * f * e⁻¹ * f⁻¹ = e * (f * e⁻¹ * f⁻¹) := by group
    rw [e3]
    exact mul_mem he.1 h3
  have hmem : e * f * e⁻¹ * f⁻¹ ∈ S.Lbar k ⊓ S.Lbar k' := ⟨h2, h1⟩
  rw [P.inf_eq_bot, Subgroup.mem_bot] at hmem
  calc e * f = e * f * e⁻¹ * f⁻¹ * (f * e) := by group
    _ = f * e := by rw [hmem, one_mul]

theorem comm_mem_Ebar {x f : S.O} (hx : x ∈ S.Lbar k) (hf : f ∈ Ebar S k' k) :
    x * f * x⁻¹ * f⁻¹ ∈ Ebar S k k' := by
  have hkQ := P.memQ
  have hff : f * f = 1 := mul_self_of_mem_Lbar S P.memQ' hf.1
  have hxx : x * x = 1 := mul_self_of_mem_Lbar S hkQ hx
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hv : f * x * f⁻¹ ∈ S.Lbar k := (mem_normalizer_iff.mp hf.2 x).mp hx
  rw [hfi] at hv
  have hcL : x * f * x⁻¹ * f⁻¹ ∈ S.Lbar k := by
    rw [hfi, hxi, show x * f * x * f = x * (f * x * f) by simp only [mul_assoc]]
    exact mul_mem hx hv
  have hcomm : x * f * x⁻¹ * f⁻¹ * f = f * (x * f * x⁻¹ * f⁻¹) := by
    rw [hfi, hxi]
    have hvx : f * x * f * x = x * (f * x * f) := Lbar_comm S hkQ hv hx
    calc x * f * x * f * f = x * (f * x * f) * f := by simp only [mul_assoc]
      _ = f * x * f * x * f := by rw [← hvx]
      _ = f * (x * f * x * f) := by simp only [mul_assoc]
  by_cases hc1 : x * f * x⁻¹ * f⁻¹ = 1
  · rw [hc1]; exact one_mem _
  by_cases hf1 : f = 1
  · exact absurd (by rw [hf1]; group : x * f * x⁻¹ * f⁻¹ = 1) hc1
  exact ⟨hcL, P.mem_normalizer_of_commute' hcL hc1 hf.1 hf1 hcomm⟩

theorem conj_mem_EF_of_mem_Lbar {x : S.O} (hx : x ∈ S.Lbar k) {n : S.O}
    (hn : n ∈ Ebar S k k' ⊔ Ebar S k' k) : x * n * x⁻¹ ∈ Ebar S k k' ⊔ Ebar S k' k := by
  have hle : Ebar S k k' ⊔ Ebar S k' k ≤
      (Ebar S k k' ⊔ Ebar S k' k).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (fun e he => ?_) (fun f hf => ?_)
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [Lbar_comm S P.memQ hx he.1, mul_inv_cancel_right]
      exact mem_sup_left he
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show x * f * x⁻¹ = x * f * x⁻¹ * f⁻¹ * f by group]
      exact mul_mem (mem_sup_left (P.comm_mem_Ebar hx hf)) (mem_sup_right hf)
  have := hle hn
  simpa only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

theorem le_normalizer_EF :
    S.Lbar k ⊔ S.Lbar k' ≤ normalizer ((Ebar S k k' ⊔ Ebar S k' k : Subgroup S.O) : Set S.O) := by
  refine sup_le (fun x hx => mem_normalizer_of_conj_mem (fun n hn =>
    P.conj_mem_EF_of_mem_Lbar hx hn) (fun n hn => P.conj_mem_EF_of_mem_Lbar (inv_mem hx) hn))
    (fun y hy => mem_normalizer_of_conj_mem (fun n hn => ?_) (fun n hn => ?_))
  · rw [sup_comm] at hn ⊢
    exact P.swap.conj_mem_EF_of_mem_Lbar hy hn
  · rw [sup_comm] at hn ⊢
    exact P.swap.conj_mem_EF_of_mem_Lbar (inv_mem hy) hn

theorem conj_mem_EF {x n : S.O} (hx : x ∈ S.Lbar k ⊔ S.Lbar k')
    (hn : n ∈ Ebar S k k' ⊔ Ebar S k' k) : x * n * x⁻¹ ∈ Ebar S k k' ⊔ Ebar S k' k :=
  (mem_normalizer_iff.mp (P.le_normalizer_EF hx) n).mp hn

theorem isPGroup_EF : IsPGroup 2 (Ebar S k k' ⊔ Ebar S k' k : Subgroup S.O) := by
  have hE : IsPGroup 2 (Ebar S k k') := (isPGroup_Lbar S P.memQ).to_le inf_le_left
  have hF : IsPGroup 2 (Ebar S k' k) := (isPGroup_Lbar S P.memQ').to_le inf_le_left
  refine hE.to_sup_of_normal_left' hF fun f hf => mem_normalizer_of_conj_mem
    (fun e he => ?_) (fun e he => ?_)
  · rw [← P.commute_of_mem_Ebar he hf, mul_inv_cancel_right]; exact he
  · rw [inv_inv, ← P.commute_of_mem_Ebar he (inv_mem hf), inv_mul_cancel_right]; exact he

theorem eq_one_of_commute {x f : S.O} (hx : x ∈ S.Lbar k) (hxE : x ∉ Ebar S k k')
    (hf : f ∈ Ebar S k' k) (hc : x * f = f * x) : f = 1 := by
  by_contra hf1
  have hx1 : x ≠ 1 := fun h1 => hxE (h1 ▸ one_mem _)
  exact hxE ⟨hx, P.mem_normalizer_of_commute' hx hx1 hf.1 hf1 hc⟩

theorem comm_injective {x : S.O} (hx : x ∈ S.Lbar k) (hxE : x ∉ Ebar S k k') {f f' : S.O}
    (hf : f ∈ Ebar S k' k) (hf' : f' ∈ Ebar S k' k)
    (he : x * f * x⁻¹ * f⁻¹ = x * f' * x⁻¹ * f'⁻¹) : f = f' := by
  have h3 : f * x⁻¹ * f⁻¹ = f' * x⁻¹ * f'⁻¹ :=
    mul_left_cancel (a := x) (by simpa only [mul_assoc] using he)
  have h2 : x * (f'⁻¹ * f) = f'⁻¹ * f * x := by
    calc x * (f'⁻¹ * f) = f'⁻¹ * (f' * x⁻¹ * f'⁻¹)⁻¹ * f' * (f'⁻¹ * f) := by group
      _ = f'⁻¹ * (f * x⁻¹ * f⁻¹)⁻¹ * f' * (f'⁻¹ * f) := by rw [h3]
      _ = f'⁻¹ * f * x := by group
  have := P.eq_one_of_commute hx hxE (mul_mem (inv_mem hf') hf) h2
  exact (inv_mul_eq_one.mp this).symm

theorem card_le_of_not_mem {x : S.O} (hx : x ∈ S.Lbar k) (hxE : x ∉ Ebar S k k') :
    Nat.card (Ebar S k' k) ≤ Nat.card (Ebar S k k') :=
  Nat.card_le_card_of_injective
    (fun f : Ebar S k' k => (⟨x * f * x⁻¹ * (f : S.O)⁻¹, P.comm_mem_Ebar hx f.2⟩ : Ebar S k k'))
    fun f f' he => Subtype.ext (P.comm_injective hx hxE f.2 f'.2 (congrArg Subtype.val he))

theorem exists_not_mem_Ebar : ∃ x ∈ S.Lbar k, x ∉ Ebar S k k' := by
  by_contra hcon
  push Not at hcon
  have hle : S.Lbar k ≤ normalizer (S.Lbar k' : Set S.O) := fun x hx => (hcon x hx).2
  obtain ⟨m, hm, hmk⟩ := P.hy'.fusion k P.memQ P.ne
  have e1 : S.Lbar (m * k') = S.Lbar k :=
    Lbar_eq_of_conj_eq S (by rw [mul_conj_z]; exact hmk)
  have e2 := P.hy'.cons.weaklyClosed m hm (by rw [e1]; exact hle)
  rw [e1] at e2
  apply P.Lbar_ne_bot
  rw [← P.inf_eq_bot, e2, inf_idem]

theorem card_Ebar_eq : Nat.card (Ebar S k k') = Nat.card (Ebar S k' k) := by
  obtain ⟨x, hx, hxE⟩ := P.exists_not_mem_Ebar
  obtain ⟨y, hy, hyF⟩ := P.swap.exists_not_mem_Ebar
  exact le_antisymm (P.swap.card_le_of_not_mem hy hyF) (P.card_le_of_not_mem hx hxE)

theorem exists_comm_eq {x : S.O} (hx : x ∈ S.Lbar k) (hxE : x ∉ Ebar S k k') {e : S.O}
    (he : e ∈ Ebar S k k') : ∃ f ∈ Ebar S k' k, x * f * x⁻¹ * f⁻¹ = e := by
  set φ : Ebar S k' k → Ebar S k k' :=
    fun f => ⟨x * f * x⁻¹ * (f : S.O)⁻¹, P.comm_mem_Ebar hx f.2⟩ with hφ
  have hinj : Function.Injective φ := fun f f' hff =>
    Subtype.ext (P.comm_injective hx hxE f.2 f'.2 (congrArg Subtype.val hff))
  obtain ⟨f, hf⟩ := (hinj.bijective_of_nat_card_le P.card_Ebar_eq.le).2 ⟨e, he⟩
  exact ⟨f, f.2, congrArg Subtype.val hf⟩

end Pair111

end CFSG.LargeExtraspecial.S11
