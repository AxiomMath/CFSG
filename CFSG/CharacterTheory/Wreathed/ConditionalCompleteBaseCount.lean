module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseOrbits

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalGeneralBase

section Orbits

theorem card_orbit_representatives {m : ℕ} (V : Finset (ZMod m × ZMod m))
    (hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup m) I).ncard = 6)
    (hVrep : ∀ I, (MulAction.orbit (dualGroup m) I).ncard = 6 →
      ∃! J, J ∈ V ∧ J ∈ MulAction.orbit (dualGroup m) I) :
    V.card = ((fun I : ZMod m × ZMod m => MulAction.orbit (dualGroup m) I) ''
      {I | (MulAction.orbit (dualGroup m) I).ncard = 6}).ncard := by
  have hinj : Set.InjOn (fun I : ZMod m × ZMod m => MulAction.orbit (dualGroup m) I)
      (V : Set (ZMod m × ZMod m)) := by
    intro J₁ hJ₁ J₂ hJ₂ h
    have h₂ : J₂ ∈ MulAction.orbit (dualGroup m) J₁ := by
      have h' : MulAction.orbit (dualGroup m) J₁ = MulAction.orbit (dualGroup m) J₂ := h
      rw [h']
      exact MulAction.mem_orbit_self _
    exact (hVrep J₁ (hV6 J₁ hJ₁)).unique ⟨hJ₁, MulAction.mem_orbit_self _⟩ ⟨hJ₂, h₂⟩
  have himage : (fun I : ZMod m × ZMod m => MulAction.orbit (dualGroup m) I) ''
      {I | (MulAction.orbit (dualGroup m) I).ncard = 6} =
      (fun I : ZMod m × ZMod m => MulAction.orbit (dualGroup m) I) ''
        (V : Set (ZMod m × ZMod m)) := by
    ext O
    constructor
    · rintro ⟨I, hI, rfl⟩
      obtain ⟨J, ⟨hJV, hJI⟩, -⟩ := hVrep I hI
      exact ⟨J, hJV, MulAction.orbit_eq_iff.mpr hJI⟩
    · rintro ⟨J, hJ, rfl⟩
      exact ⟨J, hV6 J hJ, rfl⟩
  rw [himage, hinj.ncard_image, Set.ncard_coe_finset]

theorem card_orbit_representatives_two_pow {n : ℕ} (V : Finset (ZMod (2 ^ n) × ZMod (2 ^ n)))
    (hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6)
    (hVrep : ∀ I, (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6 →
      ∃! J, J ∈ V ∧ J ∈ MulAction.orbit (dualGroup (2 ^ n)) I) :
    V.card = (2 ^ n - 1) * (2 ^ n - 2) / 6 := by
  rw [card_orbit_representatives V hV6 hVrep, ncard_orbits_six]

theorem two_pow_sub_one_mul_sub_two_div_six_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < (2 ^ n - 1) * (2 ^ n - 2) / 6 := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  apply Nat.div_pos _ (by norm_num)
  calc 6 = 3 * 2 := by norm_num
    _ ≤ (2 ^ n - 1) * (2 ^ n - 2) := Nat.mul_le_mul (by omega) (by omega)

theorem card_orbit_representatives_pos {n : ℕ} (hn : 2 ≤ n)
    (V : Finset (ZMod (2 ^ n) × ZMod (2 ^ n)))
    (hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6)
    (hVrep : ∀ I, (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6 →
      ∃! J, J ∈ V ∧ J ∈ MulAction.orbit (dualGroup (2 ^ n)) I) :
    0 < V.card := by
  rw [card_orbit_representatives_two_pow V hV6 hVrep]
  exact two_pow_sub_one_mul_sub_two_div_six_pos hn

end Orbits

section Families

theorem map_image_val_eq_replicate {α ι R : Type*} [DecidableEq ι] (d : ι → R) (s : Finset α)
    (f : α → ι) (c : R) (hf : Set.InjOn f s) (hc : ∀ x ∈ s, d (f x) = c) :
    Multiset.map d (s.image f).val = Multiset.replicate s.card c := by
  rw [Finset.image_val_of_injOn hf, Multiset.map_map, Multiset.eq_replicate]
  refine ⟨by rw [Multiset.card_map, Finset.card_val], fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
  exact hc x hx

theorem union_val_of_disjoint {ι : Type*} [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t) :
    (s ∪ t).val = s.val + t.val := by
  rw [← Finset.disjUnion_eq_union s t h]
  rfl

theorem card_and_degree_multiset {ι κ' γ R : Type*} [DecidableEq ι] (B : Finset ι) (d : ι → R)
    (q₁ q₂ q₃ q₄ q₅ : ι) (hq : [q₁, q₂, q₃, q₄, q₅].Nodup) (χ : κ' → ι) (J : Finset κ')
    (hχ : Set.InjOn χ J) {M : ℕ} (P Q : ℕ → Fin 2 → ι)
    (hP : Set.InjOn (fun rl : ℕ × Fin 2 => P rl.1 rl.2)
      ↑(Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))))
    (hQ : Set.InjOn (fun rl : ℕ × Fin 2 => Q rl.1 rl.2)
      ↑(Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))))
    (V : Finset γ) (ψ : γ → ι) (hψ : Set.InjOn ψ V)
    (hdisj₁ : Disjoint ({q₁, q₂, q₃, q₄, q₅} : Finset ι) (J.image χ))
    (hdisj₂ : Disjoint (({q₁, q₂, q₃, q₄, q₅} : Finset ι) ∪ J.image χ)
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => P rl.1 rl.2))
    (hdisj₃ : Disjoint (({q₁, q₂, q₃, q₄, q₅} : Finset ι) ∪ J.image χ ∪
      (Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => P rl.1 rl.2)
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => Q rl.1 rl.2))
    (hdisj₄ : Disjoint (({q₁, q₂, q₃, q₄, q₅} : Finset ι) ∪ J.image χ ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => P rl.1 rl.2) ∪
      (Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => Q rl.1 rl.2)
      (V.image ψ))
    (hB : B = ({q₁, q₂, q₃, q₄, q₅} : Finset ι) ∪ J.image χ ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => P rl.1 rl.2) ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => Q rl.1 rl.2) ∪
      V.image ψ)
    {δ b d' Δ : R} (hdχ : ∀ j ∈ J, d (χ j) = δ)
    (hdP : ∀ r ∈ Finset.Ico 1 M, ∀ e, d (P r e) = b)
    (hdQ : ∀ r ∈ Finset.Ico 1 M, ∀ e, d (Q r e) = d') (hdψ : ∀ I ∈ V, d (ψ I) = Δ) :
    B.card = 5 + J.card + 4 * (M - 1) + V.card ∧
      Multiset.map d B.val = {d q₁, d q₂, d q₃, d q₄, d q₅} + Multiset.replicate J.card δ +
        Multiset.replicate (2 * (M - 1)) b + Multiset.replicate (2 * (M - 1)) d' +
        Multiset.replicate V.card Δ := by
  have hcard2 : (Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).card = 2 * (M - 1) := by
    rw [Finset.card_product, Nat.card_Ico, Finset.card_univ, Fintype.card_fin, mul_comm]
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hq
  obtain ⟨⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45⟩ := hq
  have hcore : ({q₁, q₂, q₃, q₄, q₅} : Finset ι).val = {q₁, q₂, q₃, q₄, q₅} := by
    rw [Finset.insert_val_of_notMem (by simp [h12, h13, h14, h15]),
      Finset.insert_val_of_notMem (by simp [h23, h24, h25]),
      Finset.insert_val_of_notMem (by simp [h34, h35]),
      Finset.insert_val_of_notMem (by simp [h45])]
    rfl
  have hcore5 : ({q₁, q₂, q₃, q₄, q₅} : Finset ι).card = 5 := by
    rw [← Finset.card_val, hcore]
    rfl
  have hBval : B.val = ({q₁, q₂, q₃, q₄, q₅} : Finset ι).val + (J.image χ).val +
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => P rl.1 rl.2).val +
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => Q rl.1 rl.2).val +
      (V.image ψ).val := by
    rw [hB, union_val_of_disjoint hdisj₄, union_val_of_disjoint hdisj₃,
      union_val_of_disjoint hdisj₂, union_val_of_disjoint hdisj₁]
  have hO := map_image_val_eq_replicate d J χ δ hχ hdχ
  have hPm := map_image_val_eq_replicate d _ _ b hP fun rl hrl =>
    hdP rl.1 (Finset.mem_product.mp hrl).1 rl.2
  have hQm := map_image_val_eq_replicate d _ _ d' hQ fun rl hrl =>
    hdQ rl.1 (Finset.mem_product.mp hrl).1 rl.2
  have hGm := map_image_val_eq_replicate d V ψ Δ hψ hdψ
  rw [hcard2] at hPm hQm
  refine ⟨?_, ?_⟩
  · rw [← Finset.card_val, hBval]
    simp only [Multiset.card_add, Finset.card_val]
    rw [hcore5, Finset.card_image_of_injOn hχ, Finset.card_image_of_injOn hP,
      Finset.card_image_of_injOn hQ, Finset.card_image_of_injOn hψ, hcard2]
    ring
  · rw [hBval, Multiset.map_add, Multiset.map_add, Multiset.map_add, Multiset.map_add, hO, hPm,
      hQm, hGm, hcore]
    rfl

end Families

section Formula

theorem six_dvd_two_pow_sub_one_mul_sub_two (n : ℕ) : 6 ∣ (2 ^ n - 1) * (2 ^ n - 2) := by
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hdvd2 : 2 ∣ (2 ^ n - 1) * (2 ^ n - 2) := by
    rcases n with _ | n
    · simp
    · apply Dvd.dvd.mul_left
      have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
      omega
  have hdvd3 : 3 ∣ (2 ^ n - 1) * (2 ^ n - 2) := by
    have hmod : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by omega
    rcases hmod with h | h
    · exact Dvd.dvd.mul_right (by omega) _
    · exact Dvd.dvd.mul_left (by omega) _
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) hdvd2 hdvd3

theorem card_formula {m M : ℕ} (hm : m = 2 * M) (hM : 2 ≤ M) (h6 : 6 ∣ (m - 1) * (m - 2)) :
    1 + 5 * M + (m - 1) * (m - 2) / 6 = (m ^ 2 + 12 * m + 8) / 6 := by
  obtain ⟨k, hk⟩ := h6
  rw [hk, Nat.mul_div_cancel_left k (by norm_num : 0 < 6)]
  have h1 : 1 ≤ m := by omega
  have h2 : 2 ≤ m := by omega
  have hsq : m ^ 2 + 12 * m + 8 = 6 * (1 + 5 * M + k) := by
    zify [h1, h2] at hk ⊢
    have hm' : (m : ℤ) = 2 * M := by exact_mod_cast hm
    linear_combination hk + 15 * hm'
  rw [hsq, Nat.mul_div_cancel_left _ (by norm_num : 0 < 6)]

end Formula

end CFSG.Wreathed.ConditionalCompleteBase
