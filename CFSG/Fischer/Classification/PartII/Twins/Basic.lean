module

public import CFSG.Fischer.Classification.PartIII.U.Flag
public import CFSG.Fischer.Classification.Skeleton

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU

namespace O2Twin

section Rel

variable {X : Type} [Group X] {A : Set X}

@[expose] def twinClass (A : Set X) (a : X) : Set X := {b | IsTwin A a b}

theorem mem_twinClass {a b : X} : b ∈ twinClass A a ↔ IsTwin A a b := Iff.rfl

theorem isTwin_symm {a b : X} (h : IsTwin A a b) : IsTwin A b a :=
  ⟨h.2.1, h.1, h.2.2.1.symm, fun c hc => (h.2.2.2 c hc).symm⟩

theorem isTwin_trans {a b c : X} (h₁ : IsTwin A a b) (h₂ : IsTwin A b c) : IsTwin A a c :=
  ⟨h₁.1, h₂.2.1, (h₂.2.2.2 a h₁.1).1 h₁.2.2.1,
    fun d hd => (h₁.2.2.2 d hd).trans (h₂.2.2.2 d hd)⟩

theorem self_mem_twinClass {a : X} (ha : a ∈ A) : a ∈ twinClass A a :=
  isTwin_refl ha

theorem twinClass_eq {a b : X} (h : IsTwin A a b) : twinClass A a = twinClass A b := by
  ext c
  exact ⟨fun hc => isTwin_trans (isTwin_symm h) hc, fun hc => isTwin_trans h hc⟩

theorem isTwin_of_mem {a b c : X} (hb : b ∈ twinClass A a) (hc : c ∈ twinClass A a) :
    IsTwin A b c :=
  isTwin_trans (isTwin_symm hb) hc

theorem not_commute_of_isTwin {a b c : X} (h : IsTwin A a b) (hc : c ∈ A)
    (hac : a * c ≠ c * a) : b * c ≠ c * b :=
  fun e => hac ((h.2.2.2 c hc).2 e.symm).symm

end Rel

variable {H : Type} [Group H] {F : Set H}

theorem isTwin_conj (hP : Pair H F) (g : H) {a b : H} (h : IsTwin F a b) :
    IsTwin F (g * a * g⁻¹) (g * b * g⁻¹) := by
  obtain ⟨ha, hb, hab, hall⟩ := h
  refine ⟨Pair.conj_mem hP ha g, Pair.conj_mem hP hb g, (conj_commute_iff g a b).2 hab,
    fun c hc => ?_⟩
  obtain ⟨c, rfl⟩ : ∃ c', c = g * c' * g⁻¹ := ⟨g⁻¹ * c * g, by group⟩
  rw [conj_commute_iff, conj_commute_iff]
  exact hall c ((Pair.conj_mem_iff hP g).1 hc)

theorem mul_mul_mul_mul_eq {a a' b : H} (h : a * a' = a' * a) :
    a * a' * b * (a * a') = a * (a' * b * a') * a := by
  calc a * a' * b * (a * a') = a * a' * b * (a' * a) := by rw [← h]
    _ = a * (a' * b * a') * a := by group

theorem eq_one_of_pow_three {K : Subgroup H} (h2 : IsPGroup 2 K) {g : H} (hg : g ∈ K)
    (h3 : g ^ 3 = 1) : g = 1 := by
  by_contra hne
  have h1 : (⟨g, hg⟩ : K) ≠ 1 := fun e => hne (congrArg Subtype.val e)
  have h3' : orderOf (⟨g, hg⟩ : K) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h3))
  have := Nat.dvd_trans (h2.dvd_orderOf h1) h3'
  omega

theorem commute_of_mul_mem (hP : Pair H F) {K : Subgroup H} (h2 : IsPGroup 2 K) {x y : H}
    (hx : x ∈ F) (hy : y ∈ F) (hxy : x * y ∈ K) : x * y = y * x := by
  by_contra h
  have h3 : (x * y) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP hx hy h, pow_orderOf_eq_one]
  have h1 := eq_one_of_pow_three h2 hxy h3
  have hyx : y = x := by
    rw [← Pair.inv_eq hP hx]
    exact (eq_inv_of_mul_eq_one_right h1)
  exact h (by rw [hyx])

theorem commute_of_mul_mem_of_commute (hP : Pair H F) {K : Subgroup H} (hK : K.Normal)
    (h2 : IsPGroup 2 K) {x y c : H} (hx : x ∈ F) (hy : y ∈ F) (hc : c ∈ F) (hxy : x * y ∈ K)
    (hcx : c * x = x * c) : c * y = y * c := by
  by_contra hcy
  have hxy' := commute_of_mul_mem hP h2 hx hy hxy
  have hm : x * y * (c * (x * y) * c) ∈ K := by
    refine K.mul_mem hxy ?_
    have := hK.conj_mem _ hxy c
    rwa [Pair.inv_eq hP hc] at this
  have he : x * y * (c * (x * y) * c) = (y * c) ^ 2 := by
    calc x * y * (c * (x * y) * c) = x * y * (c * x) * y * c := by simp only [mul_assoc]
      _ = x * y * x * c * y * c := by rw [hcx]; simp only [mul_assoc]
      _ = y * x * x * c * y * c := by rw [hxy']
      _ = (y * c) ^ 2 := by rw [mul_assoc y x x, Pair.mul_self hP hx, mul_one, sq, mul_assoc]
  have h3 : (y * c) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP hy hc fun e => hcy e.symm, pow_orderOf_eq_one]
  have h2' : (y * c) ^ 2 = 1 := by
    refine eq_one_of_pow_three h2 (he ▸ hm) ?_
    rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
  have h1 : y * c = 1 := by
    calc y * c = (y * c) ^ 3 * ((y * c) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2', inv_one, one_mul]
  have hcy' : c = y := by
    rw [← Pair.inv_eq hP hy]
    exact eq_inv_of_mul_eq_one_right h1
  exact hcy (by rw [hcy'])

end O2Twin

open O2Twin

variable {H : Type} [Group H] {F : Set H}

theorem Pair.isTwin_mul_mul (hP : Pair H F) {a b c : H} (h : IsTwin F a b) (hc : c ∈ F)
    (hac : a * c ≠ c * a) : IsTwin F (a * c * a) (b * c * b) := by
  have h' := isTwin_conj hP c h
  rwa [Pair.inv_eq hP hc, ← Pair.mul_mul_eq hP h.1 hc hac,
    ← Pair.mul_mul_eq hP h.2.1 hc (not_commute_of_isTwin h hc hac)] at h'

theorem Pair.isTwin_of_mul_mem (hP : Pair H F) {K : Subgroup H} (hK : K.Normal)
    (h2 : IsPGroup 2 K) {x y : H} (hx : x ∈ F) (hy : y ∈ F) (hxy : x * y ∈ K) : IsTwin F x y := by
  have hyx : y * x ∈ K := by
    have := K.inv_mem hxy
    rwa [mul_inv_rev, Pair.inv_eq hP hx, Pair.inv_eq hP hy] at this
  exact ⟨hx, hy, commute_of_mul_mem hP h2 hx hy hxy, fun c hc =>
    ⟨commute_of_mul_mem_of_commute hP hK h2 hx hy hc hxy,
      commute_of_mul_mem_of_commute hP hK h2 hy hx hc hyx⟩⟩

theorem Pair.isTwin_conj_of_isPGroup (hP : Pair H F) {K : Subgroup H} (hK : K.Normal)
    (h2 : IsPGroup 2 K) {x k : H} (hx : x ∈ F) (hk : k ∈ K) : IsTwin F x (k * x * k⁻¹) := by
  refine Pair.isTwin_of_mul_mem hP hK h2 hx (Pair.conj_mem hP hx k) ?_
  have e : x * (k * x * k⁻¹) = x * k * x⁻¹ * k⁻¹ := by
    rw [Pair.inv_eq hP hx]
    simp only [mul_assoc]
  rw [e]
  exact K.mul_mem (hK.conj_mem k hk x) (K.inv_mem hk)

theorem Pair.exists_isTwin_ne (hP : Pair H F) (hZ : Subgroup.center H = ⊥)
    (h2 : HasNormalPSubgroup 2 H) : ∃ x y : H, IsTwin F x y ∧ x ≠ y := by
  obtain ⟨K, hK, hne, hp⟩ := h2
  obtain ⟨⟨k, hk⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hk1' : k ≠ 1 := fun e => hk1 (Subtype.ext e)
  obtain ⟨x, hx, hkx⟩ : ∃ x ∈ F, k * x * k⁻¹ ≠ x := by
    by_contra! h
    exact hk1' (Pair.eq_one_of_forall_conj_eq hP hZ h)
  exact ⟨x, k * x * k⁻¹, Pair.isTwin_conj_of_isPGroup hP hK hp hx hk, hkx.symm⟩

theorem Pair.isTwin_conj_mul_mul (hP : Pair H F) {a a' b : H} (h : IsTwin F a a')
    (hne : a ≠ a') (hb : b ∈ F) (hab : a * b ≠ b * a) :
    IsTwin F b (a * a' * b * (a * a')) ∧ a * a' * b * (a * a') ≠ b := by
  have ha := h.1
  have ha' := h.2.1
  have e1 := mul_mul_mul_mul_eq (b := b) h.2.2.1
  refine ⟨?_, fun heq => ?_⟩
  · have h' := isTwin_conj hP a (Pair.isTwin_mul_mul hP h hb hab)
    rwa [Pair.inv_eq hP ha, Pair.mul_mul_mul_mul hP ha, ← e1] at h'
  · rw [e1] at heq
    have h1 : a' * b * a' = a * b * a := by
      rw [← Pair.mul_mul_mul_mul hP ha (a' * b * a'), heq]
    have h2 : b * a' * b = b * a * b := by
      rw [← Pair.mul_mul_eq hP ha' hb (not_commute_of_isTwin h hb hab), h1,
        Pair.mul_mul_eq hP ha hb hab]
    exact hne (mul_left_cancel (mul_right_cancel h2)).symm

end CFSG.Fischer.Classification
