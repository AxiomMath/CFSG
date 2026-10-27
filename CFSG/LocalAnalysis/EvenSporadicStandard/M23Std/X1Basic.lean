module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NOne

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 : Subgroup G}

theorem normalizer_inf_centralizer_z_eq (h : OneClassData L z t)
    (D : NData L F)
    (hnorm : ∀ n : G, (∀ x, x ∈ F ⊔ zpowers z ↔ n * x * n⁻¹ ∈ F ⊔ zpowers z) →
      ∀ x, x ∈ L1 ↔ n * x * n⁻¹ ∈ L1)
    (hcz : ∀ x ∈ L1, z * x = x * z → x ∈ F) (hFL1 : F ≤ L1) :
    normalizer (L1 : Set G) ⊓ centralizer ({z} : Set G) =
      normalizer ((F ⊔ zpowers z : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hcX, hcC⟩ := Subgroup.mem_inf.1 hc
    have hcz' : c * z = z * c := mem_centralizer_singleton_iff.1 hcC
    have hcX' := Subgroup.mem_normalizer_iff.1 hcX
    have hcF : ∀ x ∈ F, c * x * c⁻¹ ∈ F := by
      intro x hx
      refine hcz _ ((hcX' x).1 (hFL1 hx)) ?_
      have hzx : z * x = x * z := h.z_comm x (D.F_le hx)
      calc z * (c * x * c⁻¹) = c * (z * x) * c⁻¹ := by
            rw [show z * (c * x * c⁻¹) = (z * c) * x * c⁻¹ by group, ← hcz']; group
        _ = c * (x * z) * c⁻¹ := by rw [hzx]
        _ = (c * x * c⁻¹) * z := by
            rw [show c * (x * z) * c⁻¹ = c * x * (z * c⁻¹) by group,
              show z * c⁻¹ = c⁻¹ * z by
                rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hcz', inv_mul_cancel_left]]
            group
    have hcF' := forall_mem_iff_of_forall_mem hcF
    have hcz'' : c * z * c⁻¹ = z * 1 := by
      rw [hcz', mul_one]; group
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_normalizer_iff.2
      (mem_normalizer_sup h D.F_le hcF' (Subgroup.one_mem F) hcz''), hcC⟩
  · intro c hc
    obtain ⟨hcE, hcC⟩ := Subgroup.mem_inf.1 hc
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_normalizer_iff.2
      (hnorm c (Subgroup.mem_normalizer_iff.1 hcE)), hcC⟩

omit [Finite G] in
theorem mem_sup_zpowers_cases (hz2 : z * z = 1) (hnorm : ∀ x, x ∈ L1 ↔ z * x * z⁻¹ ∈ L1)
    {k : G} (hk : k ∈ L1 ⊔ zpowers z) : k ∈ L1 ∨ ∃ l ∈ L1, k = l * z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzn : ∀ x ∈ L1, z * x * z ∈ L1 := fun x hx => by
    have := (hnorm x).1 hx
    rwa [hzi] at this
  let S : Subgroup G :=
    { carrier := {k | k ∈ L1 ∨ ∃ l ∈ L1, k = l * z}
      mul_mem' := by
        rintro a b (ha | ⟨l, hl, rfl⟩) (hb | ⟨l', hl', rfl⟩)
        · exact Or.inl (Subgroup.mul_mem _ ha hb)
        · exact Or.inr ⟨a * l', Subgroup.mul_mem _ ha hl', by group⟩
        · refine Or.inr ⟨l * (z * b * z), Subgroup.mul_mem _ hl (hzn b hb), ?_⟩
          calc l * z * b = l * (z * b * z) * (z * z)⁻¹ * z := by group
            _ = l * (z * b * z) * z := by rw [hz2]; group
        · refine Or.inl ?_
          have : l * z * (l' * z) = l * (z * l' * z) := by group
          rw [this]
          exact Subgroup.mul_mem _ hl (hzn l' hl')
      one_mem' := Or.inl (Subgroup.one_mem _)
      inv_mem' := by
        rintro a (ha | ⟨l, hl, rfl⟩)
        · exact Or.inl (Subgroup.inv_mem _ ha)
        · refine Or.inr ⟨z * l⁻¹ * z, hzn _ (Subgroup.inv_mem _ hl), ?_⟩
          rw [mul_inv_rev, hzi]
          calc z * l⁻¹ = z * l⁻¹ * z * (z * z)⁻¹ * z := by group
            _ = z * l⁻¹ * z * z := by rw [hz2]; group }
  have hle : L1 ⊔ zpowers z ≤ S := by
    refine sup_le (fun x hx => Or.inl hx) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr ⟨1, Subgroup.one_mem _, (one_mul z).symm⟩
  exact hle hk

theorem centralizer_X_z_inf_C (h : OneClassData L z t) (D : NData L F)
    (hnorm : ∀ n : G, (∀ x, x ∈ F ⊔ zpowers z ↔ n * x * n⁻¹ ∈ F ⊔ zpowers z) →
      ∀ x, x ∈ L1 ↔ n * x * n⁻¹ ∈ L1)
    (hcz : ∀ x ∈ L1, z * x = x * z → x ∈ F) (hFL1 : F ≤ L1)
    (hcomm : ∀ x ∈ L1, ∀ y ∈ L1, x * y = y * x) (hcard : Nat.card L1 = 256)
    (hK : Ksub z F = L1 ⊔ zpowers z) (hznorm : ∀ x, x ∈ L1 ↔ z * x * z⁻¹ ∈ L1) :
    normalizer (L1 : Set G) ⊓ centralizer ({z} : Set G) ⊓ centralizer (L1 : Set G) = F := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hcXz, hcC⟩ := Subgroup.mem_inf.1 hc
    rw [normalizer_inf_centralizer_z_eq h D hnorm hcz hFL1] at hcXz
    obtain ⟨hcE, hczc⟩ := Subgroup.mem_inf.1 hcXz
    have hcz' : z * c = c * z := (mem_centralizer_singleton_iff.1 hczc).symm
    have hcL1 : ∀ x ∈ L1, x * c = c * x := fun x hx => mem_centralizer_iff.1 hcC x hx
    have hcK : c ∈ Ksub z F := by
      rw [mem_Ksub]
      exact ⟨Subgroup.mem_normalizer_iff.1 hcE, fun f hf => hcL1 f (hFL1 hf)⟩
    rw [hK] at hcK
    rcases mem_sup_zpowers_cases h.z_mul_self hznorm hcK with hcl | ⟨l, hl, rfl⟩
    · exact hcz c hcl hcz'
    · exfalso
      have hzx : ∀ x ∈ L1, z * x = x * z := by
        intro x hx
        have e := hcL1 x hx
        have e2 : l * x = x * l := hcomm l hl x hx
        have e3 : l * (z * x) = l * (x * z) := by
          calc l * (z * x) = (l * z) * x := by group
            _ = x * (l * z) := e.symm
            _ = (x * l) * z := by group
            _ = (l * x) * z := by rw [e2]
            _ = l * (x * z) := by group
        exact mul_left_cancel e3
      have hLF : L1 ≤ F := fun x hx => hcz x hx (hzx x hx)
      have := Subgroup.card_le_of_le hLF
      rw [hcard, D.F_card] at this
      omega
  · intro f hf
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer (hFL1 hf), ?_⟩, ?_⟩
    · exact mem_centralizer_singleton_iff.2 (h.z_comm f (D.F_le hf)).symm
    · exact mem_centralizer_iff.2 fun x hx => hcomm x hx f (hFL1 hf)

omit [Finite G] in
theorem exists_mul_of_normalizes {N L1 : Subgroup G} (hN : ∀ l ∈ L1, ∀ x ∈ N, l * x * l⁻¹ ∈ N)
    {c : G} (hc : c ∈ N ⊔ L1) : ∃ n ∈ N, ∃ l ∈ L1, c = n * l := by
  let S : Subgroup G :=
    { carrier := {c | ∃ n ∈ N, ∃ l ∈ L1, c = n * l}
      mul_mem' := by
        rintro _ _ ⟨n, hn, l, hl, rfl⟩ ⟨n', hn', l', hl', rfl⟩
        refine ⟨n * (l * n' * l⁻¹), Subgroup.mul_mem _ hn (hN l hl n' hn'),
          l * l', Subgroup.mul_mem _ hl hl', by group⟩
      one_mem' := ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨n, hn, l, hl, rfl⟩
        refine ⟨l⁻¹ * n⁻¹ * l, ?_, l⁻¹, Subgroup.inv_mem _ hl, by group⟩
        have := hN l⁻¹ (Subgroup.inv_mem _ hl) n⁻¹ (Subgroup.inv_mem _ hn)
        simpa using this }
  have hle : N ⊔ L1 ≤ S := by
    refine sup_le (fun n hn => ⟨n, hn, 1, Subgroup.one_mem _, by simp⟩)
      (fun l hl => ⟨1, Subgroup.one_mem _, l, hl, by simp⟩)
  exact hle hc

omit [Finite G] in
theorem mem_complement_of_odd {N L1 : Subgroup G} (hN : ∀ l ∈ L1, ∀ x ∈ N, l * x * l⁻¹ ∈ N)
    (hdisj : Disjoint N L1) (hsq : ∀ x ∈ L1, x * x = 1) {c : G} (hc : c ∈ N ⊔ L1)
    (hodd : Odd (orderOf c)) : c ∈ N := by
  obtain ⟨n, hn, l, hl, rfl⟩ := exists_mul_of_normalizes hN hc
  obtain ⟨k, hk⟩ := hodd
  have hpow : ∀ j : ℕ, ∃ n' ∈ N, (n * l) ^ j = n' * l ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ j ih =>
      obtain ⟨n', hn', e⟩ := ih
      refine ⟨n' * (l ^ j * n * (l ^ j)⁻¹), Subgroup.mul_mem _ hn' ?_, ?_⟩
      · have := hN (l ^ j) (Subgroup.pow_mem _ hl j) n hn
        exact this
      · rw [pow_succ, e]
        group
  obtain ⟨n', hn', e⟩ := hpow (orderOf (n * l))
  rw [pow_orderOf_eq_one] at e
  have hl2 : l ^ orderOf (n * l) = l := by
    rw [hk, pow_succ, pow_mul, pow_two, hsq l hl, one_pow, one_mul]
  rw [hl2] at e
  have hln : l ∈ N := by
    have : l = n'⁻¹ := by
      have := congrArg (fun y => n'⁻¹ * y) e
      simp at this
      exact this.symm
    rw [this]
    exact Subgroup.inv_mem _ hn'
  have : l = 1 := Subgroup.disjoint_def.1 hdisj hln hl
  rw [this, mul_one]
  exact hn

omit [Finite G] in
theorem conj_mem_complement {N L1 : Subgroup G}
    (hNC : ∀ c ∈ centralizer (L1 : Set G), ∀ x ∈ N, c * x * c⁻¹ ∈ N)
    (hNle : N ≤ centralizer (L1 : Set G)) (hodd : ¬ 2 ∣ Nat.card N) (hdisj : Disjoint N L1)
    (hsq : ∀ x ∈ L1, x * x = 1) (hcomm : ∀ x ∈ L1, ∀ y ∈ L1, x * y = y * x)
    (hsup : N ⊔ L1 = centralizer (L1 : Set G))
    {g : G} (hg : g ∈ normalizer (L1 : Set G)) {x : G} (hx : x ∈ N) : g * x * g⁻¹ ∈ N := by
  have hxC : x ∈ centralizer (L1 : Set G) := hNle hx
  have hgx : g * x * g⁻¹ ∈ centralizer (L1 : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    have hy' : g⁻¹ * y * g ∈ L1 := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) y).1 hy
      simpa using this
    have := mem_centralizer_iff.1 hxC (g⁻¹ * y * g) hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * y := by group
  rw [← hsup] at hgx
  refine mem_complement_of_odd (fun l hl x hx => hNC l ?_ x hx) hdisj hsq hgx ?_
  · exact mem_centralizer_iff.2 fun y hy => hcomm y hy l hl
  · have hord : orderOf (g * x * g⁻¹) = orderOf x := by
      simpa [MulAut.conj_apply] using
        orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    rw [hord]
    have h1 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
    rcases Nat.even_or_odd (orderOf x) with he | ho
    · exact absurd (dvd_trans (even_iff_two_dvd.1 he) h1) hodd
    · exact ho

end CFSG.EvenSporadicStandard.M23Std
