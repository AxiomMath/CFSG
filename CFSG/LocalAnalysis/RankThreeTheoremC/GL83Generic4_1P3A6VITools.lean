module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem a6vi_map_conj_zpowers (g w : G) :
    (zpowers w).map (MulAut.conj g).toMonoidHom = zpowers (g * w * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem a6vi_map_conj_mul (g h : G) (L : Subgroup G) :
    (L.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      L.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext w
  simp [MulAut.conj_apply, mul_assoc]

theorem a6vi_map_conj_injective (g : G) :
    Function.Injective fun L : Subgroup G => L.map (MulAut.conj g).toMonoidHom :=
  Subgroup.map_injective (fun _ _ h => (MulAut.conj g).injective h)

theorem a6vi_map_conj_le {Q L : Subgroup G} {g : G} (hg : g ∈ normalizer (Q : Set G))
    (hL : L ≤ Q) : L.map (MulAut.conj g).toMonoidHom ≤ Q := by
  rintro _ ⟨w, hw, rfl⟩
  exact (mem_normalizer_iff.mp hg w).mp (hL hw)

theorem a6vi_mem_normalizer_sup {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (H : Set G) → g ∈ normalizer (K : Set G) →
      ∀ w ∈ H ⊔ K, g * w * g⁻¹ ∈ H ⊔ K := by
    intro g hH hK w hw
    have hle : H ⊔ K ≤ (H ⊔ K).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun h hh => ?_) (fun k hk => ?_)
      · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_left ((mem_normalizer_iff.mp hH h).mp hh)
      · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_right ((mem_normalizer_iff.mp hK k).mp hk)
    have := hle hw
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
  rw [mem_normalizer_iff]
  intro w
  refine ⟨key g hH hK w, fun hw => ?_⟩
  have := key g⁻¹ (inv_mem hH) (inv_mem hK) _ hw
  simpa [mul_assoc] using this

theorem a6vi_isPGroup_zpowers {u : G} {e : ℕ} (hu : u ^ (3 ^ e) = 1) :
    IsPGroup 3 (zpowers u) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hu)
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])

theorem a6vi_zpowers_conj_congr {a b : G} (h : zpowers a = zpowers b) (g : G) :
    zpowers (g * a * g⁻¹) = zpowers (g * b * g⁻¹) := by
  rw [← a6vi_map_conj_zpowers, ← a6vi_map_conj_zpowers, h]

theorem a6vi_zpowers_of_conj {a b g : G} (h : zpowers (g * a * g⁻¹) = zpowers (g * b * g⁻¹)) :
    zpowers a = zpowers b := by
  rw [← a6vi_map_conj_zpowers, ← a6vi_map_conj_zpowers] at h
  exact a6vi_map_conj_injective g h

theorem a6vi_exists_cube_root [Finite G] {Z : Subgroup G} (hZc : IsCyclic Z) (hZp : IsPGroup 3 Z)
    {x : G} (hxZ : x ∈ Z) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hne : Z ≠ zpowers x) :
    ∃ w ∈ Z, w ^ 3 = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := hZc.exists_generator
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hzo : orderOf (z : G) = 3 ^ k := by
    rw [Subgroup.orderOf_coe, ← hk, orderOf_eq_card_of_forall_mem_zpowers hz]
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    apply hne
    have hle : zpowers x ≤ Z := zpowers_le.mpr hxZ
    have hcx : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hxo]
    have hdvd : (3 : ℕ) ∣ 3 ^ k := by rw [← hk, ← hcx]; exact Subgroup.card_dvd_of_le hle
    have hk1 : k = 1 := by
      interval_cases k
      · norm_num at hdvd
      · rfl
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hk, hk1, pow_one, hcx])).symm
  obtain ⟨i, hi⟩ := hz ⟨x, hxZ⟩
  have hxi : (z : G) ^ i = x := by
    have := congrArg Subtype.val hi
    simpa using this
  have h3i : (z : G) ^ (3 * i) = 1 := by
    rw [mul_comm, zpow_mul, hxi, zpow_ofNat, hx3]
  have hdvd : ((3 ^ k : ℕ) : ℤ) ∣ 3 * i := by
    rw [← hzo]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h3i
  have h3 : (3 : ℤ) ∣ i := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨3 ^ (k - 2) * c, ?_⟩
    have hk' : k = (k - 2) + 1 + 1 := by omega
    rw [hk'] at hc
    push_cast at hc
    have : (3 : ℤ) * i = 3 * (3 * (3 ^ (k - 2) * c)) := by rw [hc]; ring
    linarith [mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) this]
  obtain ⟨j, rfl⟩ := h3
  refine ⟨(z : G) ^ j, zpow_mem z.2 j, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, mul_comm]
  exact_mod_cast hxi

end CFSG.LocalAnalysis.RankThreeTheoremC
