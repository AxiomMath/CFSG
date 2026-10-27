module

public import CFSG.Goldschmidt75.Sec45
public import CFSG.Goldschmidt75.Sec43b

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {S₁ S₂ : Subgroup G}

omit [Finite G] in
theorem mem_of_sq_mem_of_odd {K : Subgroup G} {o : G} (ho : Odd (orderOf o)) (h2 : o ^ 2 ∈ K) :
    o ∈ K := by
  obtain ⟨j, hj⟩ := ho
  have h1 : o = (o ^ 2) ^ (j + 1) := by
    rw [← pow_mul]
    have : o ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one o
    calc o = o * o ^ (2 * j + 1) := by rw [this, mul_one]
      _ = o ^ (2 * (j + 1)) := by rw [← pow_succ']; ring_nf
  rw [h1]
  exact pow_mem h2 _

theorem MinCE.centralizer_le_normalizer_kSub (h : MinCE G T S₁ S₂) {s₁ : G} (hs₁ : s₁ ∈ S₁)
    (hs₁2 : orderOf s₁ = 2)
    (hinv : ∀ t ∈ S₂, t ^ 2 = 1 → oddCent s₁ ≤ centralizer ({t} : Set G)) :
    centralizer ({s₁} : Set G) ≤ normalizer ((kSub S₂ S₁ : Subgroup G) : Set G) := by
  set L := centralizer ({s₁} : Set G) with hL
  set K₂ := kSub S₂ S₁ with hK₂
  set O := oddCent s₁ with hO
  have hC₁ : S₂ ≤ centralizer (S₁ : Set G) := le_centralizer_iff.mp h.comm
  have hK₂L : K₂ ≤ L :=
    (kSub_le_centralizer hC₁).trans (centralizer_le (Set.singleton_subset_iff.mpr hs₁))
  have hLO : L ≤ normalizer (O : Set G) := centralizer_le_normalizer_oddCent s₁
  have hK₂O : K₂ ≤ centralizer (O : Set G) := by
    refine h.symm.kSub_le_closure.trans ((closure_le _).mpr ?_)
    rintro _ ⟨k, hk, t, ht, ht2, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro o ho
    have h1 : k⁻¹ * o * k ∈ O := by
      have := (mem_normalizer_iff.mp (hLO (hK₂L (inv_mem hk))) o).mp ho
      simpa using this
    have h2 := mem_centralizer_singleton_iff.mp (hinv t ht ht2 h1)
    calc o * (k * t * k⁻¹) = k * ((k⁻¹ * o * k) * t) * k⁻¹ := by group
      _ = k * (t * (k⁻¹ * o * k)) * k⁻¹ := by rw [h2]
      _ = k * t * k⁻¹ * o := by group
  have h43 := h.le_normalizer_kSub_sup (zpowers_le.mpr hs₁) (zpowers_ne_bot hs₁2)
  rw [normalizer_zpowers_eq hs₁2] at h43
  have hK₂On : K₂ ≤ normalizer (O : Set G) := hK₂L.trans hLO
  have hmap : ∀ l ∈ L, ∀ x ∈ K₂, x ^ 2 = 1 → l * x * l⁻¹ ∈ K₂ := by
    intro l hl x hx hx2
    have h1 : l * x * l⁻¹ ∈ ((K₂ ⊔ O : Subgroup G) : Set G) :=
      (mem_normalizer_iff.mp (h43 hl) x).mp (mem_sup_left hx)
    rw [coe_mul_of_left_le_normalizer_right _ _ hK₂On] at h1
    obtain ⟨k, hk, o, ho, hko⟩ := h1
    replace hko : k * o = l * x * l⁻¹ := hko
    have hc : o * k = k * o := mem_centralizer_iff.mp (hK₂O hk) o ho
    have hsq : (k * o) ^ 2 = 1 := by
      rw [hko, pow_two]
      have e : l * x * l⁻¹ * (l * x * l⁻¹) = l * (x * x) * l⁻¹ := by group
      rw [e, ← pow_two, hx2]
      group
    have ho2 : o ^ 2 ∈ K₂ := by
      have h3 : k ^ 2 * o ^ 2 = 1 := by
        rw [← (Commute.mul_pow hc.symm 2)]
        exact hsq
      rw [eq_inv_of_mul_eq_one_right h3]
      exact inv_mem (pow_mem hk 2)
    have hoodd : Odd (orderOf o) := by
      have := orderOf_dvd_natCard (⟨o, ho⟩ : O)
      rw [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat (Balance.odd_card_oddCoreOf _) this
    rw [← hko]
    exact mul_mem hk (mem_of_sq_mem_of_odd hoodd ho2)
  have hconj : ∀ l ∈ L, ∀ y ∈ K₂, l * y * l⁻¹ ∈ K₂ := by
    intro l hl y hy
    have hle : K₂ ≤ K₂.comap (MulAut.conj l).toMonoidHom := by
      refine h.symm.kSub_le_closure.trans ((closure_le _).mpr ?_)
      rintro _ ⟨k, hk, t, ht, ht2, rfl⟩
      have hx : k * t * k⁻¹ ∈ K₂ := mul_mem (mul_mem hk (le_kSub (hC₁.trans
        (centralizer_le_normalizer _)) ht)) (inv_mem hk)
      have hx2 : (k * t * k⁻¹) ^ 2 = 1 := by
        have e : (k * t * k⁻¹) ^ 2 = k * t ^ 2 * k⁻¹ := by rw [pow_two, pow_two]; group
        rw [e, ht2]
        group
      exact hmap l hl _ hx hx2
    exact hle hy
  intro l hl
  exact mem_normalizer_of_forall (hconj l hl) (by simpa using hconj l⁻¹ (inv_mem hl))

end CFSG.Goldschmidt75
