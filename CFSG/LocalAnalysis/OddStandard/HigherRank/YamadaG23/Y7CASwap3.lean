module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CASwap2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CANo3c
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement Pointwise

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 K : Subgroup Γ}

private lemma y7c_conjSub_injective (g : Γ) : Function.Injective (conjSub g) := by
  intro A B h
  have hA : conjSub g⁻¹ (conjSub g A) = A := by
    rw [← y7c_conjSub_mul, inv_mul_cancel, y7c_conjSub_one]
  have hB : conjSub g⁻¹ (conjSub g B) = B := by
    rw [← y7c_conjSub_mul, inv_mul_cancel, y7c_conjSub_one]
  calc A = conjSub g⁻¹ (conjSub g A) := hA.symm
    _ = conjSub g⁻¹ (conjSub g B) := by rw [h]
    _ = B := hB

private lemma y7c_mem_sup_decomp {A B : Subgroup Γ}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {z : Γ} (hz : z ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = z := by
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc).2
  have hz' : z ∈ (A : Set Γ) * (B : Set Γ) := hset ▸ hz
  simpa [Set.mem_mul] using hz'

private lemma y7c_sq_eq_one_of_mem_center_map {L : Subgroup Γ} {x : Γ}
    (hx : x ∈ (Subgroup.center ↥L).map L.subtype)
    (hcard : Nat.card ↥(Subgroup.center ↥L) ∣ 2) : x * x = 1 := by
  rcases Subgroup.mem_map.mp hx with ⟨x₀, hx₀c, hx₀eq⟩
  have hdvd : orderOf x₀ ∣ 2 := dvd_trans (Subgroup.orderOf_dvd_natCard _ hx₀c) hcard
  have h2 : x₀ ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
  rw [← hx₀eq]
  simpa [pow_two] using congrArg Subtype.val h2

private lemma y7c_center_sup_map_eq {A B : Subgroup Γ}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    (Subgroup.center ↥(A ⊔ B)).map (A ⊔ B).subtype =
      (Subgroup.center ↥A).map A.subtype ⊔ (Subgroup.center ↥B).map B.subtype := by
  set ZA := (Subgroup.center ↥A).map A.subtype with hZA
  set ZB := (Subgroup.center ↥B).map B.subtype with hZB
  set ZN := (Subgroup.center ↥(A ⊔ B)).map (A ⊔ B).subtype with hZN
  have hcZ : ∀ x ∈ ZA, ∀ y ∈ ZB, x * y = y * x := by
    rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
    exact hc x' x'.2 y' y'.2
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [Subgroup.mem_map] at hz
    rcases hz with ⟨z', hz'c, rfl⟩
    rcases y7c_mem_sup_decomp hc z'.2 with ⟨a, ha, b, hb, hab⟩
    have hzcent : ∀ n ∈ A ⊔ B, (z' : Γ) * n = n * (z' : Γ) := by
      intro n hn
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨n, hn⟩)).symm
    have habc : ∀ n ∈ A ⊔ B, (a * b) * n = n * (a * b) := by
      intro n hn
      simpa [← hab] using hzcent n hn
    have haZ : a ∈ ZA := by
      rw [Subgroup.mem_map]
      refine ⟨⟨a, ha⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have hw := habc (w : Γ) (Subgroup.mem_sup_left w.2)
      have h' : (a * (w : Γ)) * b = ((w : Γ) * a) * b := by
        calc (a * (w : Γ)) * b = a * ((w : Γ) * b) := by rw [mul_assoc]
          _ = a * (b * (w : Γ)) := by rw [hc (w : Γ) w.2 b hb]
          _ = (a * b) * (w : Γ) := by rw [← mul_assoc]
          _ = (w : Γ) * (a * b) := hw
          _ = ((w : Γ) * a) * b := by rw [← mul_assoc]
      exact (mul_right_cancel h').symm
    have hbZ : b ∈ ZB := by
      rw [Subgroup.mem_map]
      refine ⟨⟨b, hb⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have hw := habc (w : Γ) (Subgroup.mem_sup_right w.2)
      have h' : a * (b * (w : Γ)) = a * ((w : Γ) * b) := by
        calc a * (b * (w : Γ)) = (a * b) * (w : Γ) := by rw [← mul_assoc]
          _ = (w : Γ) * (a * b) := hw
          _ = ((w : Γ) * a) * b := by rw [← mul_assoc]
          _ = (a * (w : Γ)) * b := by rw [← hc a ha (w : Γ) w.2]
          _ = a * ((w : Γ) * b) := by rw [mul_assoc]
      exact (mul_left_cancel h').symm
    have hmem : (z' : Γ) ∈ (ZA : Set Γ) * (ZB : Set Γ) := ⟨a, haZ, b, hbZ, hab⟩
    have hsetZ := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute ZA ZB hcZ).2
    show (z' : Γ) ∈ ((ZA ⊔ ZB : Subgroup Γ) : Set Γ)
    rw [hsetZ]
    exact hmem
  · intro z hz
    rcases y7c_mem_sup_decomp hcZ hz with ⟨x, hxZ, y, hyZ, hxy⟩
    have hxA : x ∈ A := Subgroup.map_subtype_le (Subgroup.center ↥A) hxZ
    have hyB : y ∈ B := Subgroup.map_subtype_le (Subgroup.center ↥B) hyZ
    have hzN : z ∈ A ⊔ B := by rw [← hxy]; exact mul_mem_sup hxA hyB
    refine Subgroup.mem_map.mpr ⟨⟨z, hzN⟩, ?_, rfl⟩
    · rw [Subgroup.mem_center_iff]
      intro n
      apply Subtype.ext
      change (n : Γ) * z = z * (n : Γ)
      rcases Subgroup.mem_map.mp hxZ with ⟨x', hx'c, hx'eq⟩
      rcases Subgroup.mem_map.mp hyZ with ⟨y', hy'c, hy'eq⟩
      rcases y7c_mem_sup_decomp hc n.2 with ⟨a, ha, b, hb, hab⟩
      have hxa : a * x = x * a := by
        rw [← hx'eq]
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx'c ⟨a, ha⟩)
      have hyb : b * y = y * b := by
        rw [← hy'eq]
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy'c ⟨b, hb⟩)
      have hxb : b * x = x * b := (hc x hxA b hb).symm
      have hya : a * y = y * a := hc a ha y hyB
      have habX : (a * b) * x = x * (a * b) := by
        rw [mul_assoc, hxb, ← mul_assoc, hxa, mul_assoc]
      have habY : (a * b) * y = y * (a * b) := by
        rw [mul_assoc, hyb, ← mul_assoc, hya, mul_assoc]
      rw [← hxy, ← hab]
      calc (a * b) * (x * y) = ((a * b) * x) * y := by group
        _ = (x * (a * b)) * y := by rw [habX]
        _ = x * ((a * b) * y) := by group
        _ = x * (y * (a * b)) := by rw [habY]
        _ = (x * y) * (a * b) := by group

theorem y7c_swap_N_eq (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hne : conjSub t K ≠ K) :
    Subgroup.normalClosure (J : Set Γ) = K ⊔ conjSub t K := by
  have hne' : K ≠ conjSub t K := Ne.symm hne
  have hconj : ∀ g : Γ, conjSub g (K ⊔ conjSub t K) = K ⊔ conjSub t K := by
    intro g
    rw [y7c_conjSub_sup]
    have h1 : conjSub g K = K ∨ conjSub g K = conjSub t K :=
      y7c_conj_cases c hK hJK hne g
    have h2 : conjSub g (conjSub t K) = K ∨ conjSub g (conjSub t K) = conjSub t K := by
      have h := y7c_conj_cases c hK hJK hne (g * t)
      rwa [y7c_conjSub_mul] at h
    have hne2 : conjSub g K ≠ conjSub g (conjSub t K) := fun h =>
      hne' (y7c_conjSub_injective g h)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne2
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
    · exact absurd (h1.trans h2.symm) hne2
  haveI hnorm : (K ⊔ conjSub t K).Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    change conjSub g (K ⊔ conjSub t K) = K ⊔ conjSub t K
    exact hconj g
  refine le_antisymm ?_ ?_
  · exact Subgroup.normalClosure_le_normal (fun x hx => hJK hx)
  · exact sup_le (y7c_K_le_N c hK hJK) (y7c_conjSub_K_le_N c hK hJK t)

theorem y7c_swap_center_sq (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hne : conjSub t K ≠ K)
    (hSM : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2) {z : Γ}
    (hz : z ∈ Subgroup.normalClosure (J : Set Γ))
    (hzc : ∀ n ∈ Subgroup.normalClosure (J : Set Γ), z * n = n * z) : z * z = 1 := by
  have hN : Subgroup.normalClosure (J : Set Γ) = K ⊔ conjSub t K :=
    y7c_swap_N_eq c hK hJK hne
  have hc : ∀ a ∈ K, ∀ b ∈ conjSub t K, a * b = b * a :=
    y7c_comm_of_components hK (y7c_isComponent_conjSub hK t) (Ne.symm hne)
  have hcZ : ∀ x ∈ (Subgroup.center ↥K).map K.subtype,
      ∀ y ∈ (Subgroup.center ↥(conjSub t K)).map (conjSub t K).subtype, x * y = y * x := by
    rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
    exact hc x' x'.2 y' y'.2
  have hzZ : z ∈ (Subgroup.center ↥(Subgroup.normalClosure (J : Set Γ))).map
      (Subgroup.normalClosure (J : Set Γ)).subtype := by
    rw [Subgroup.mem_map]
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro n
    exact Subtype.ext (hzc n n.2).symm
  rw [hN] at hzZ
  rw [y7c_center_sup_map_eq hc] at hzZ
  rcases y7c_mem_sup_decomp hcZ hzZ with ⟨k, hkZ, k', hk'Zt, hkk'⟩
  have hkK : k ∈ K := Subgroup.map_subtype_le (Subgroup.center ↥K) hkZ
  have hk'Kt : k' ∈ conjSub t K :=
    Subgroup.map_subtype_le (Subgroup.center ↥(conjSub t K)) hk'Zt
  have hKt : CFSG.IsComponent (conjSub t K) := y7c_isComponent_conjSub hK t
  have hsq : conjSub t (conjSub t K) = K := y7c_conjSub_conjSub_of_sq c.t_sq K
  have hJKt : J ≤ conjSub t K ⊔ conjSub t (conjSub t K) := by
    rw [hsq, sup_comm]; exact hJK
  have hneKt : conjSub t (conjSub t K) ≠ conjSub t K := by
    rw [hsq]; exact Ne.symm hne
  have hcardK : Nat.card ↥(Subgroup.center ↥K) ∣ 2 :=
    y7c_swap_center_card c hK hJK hne hSM
  have hcardKt : Nat.card ↥(Subgroup.center ↥(conjSub t K)) ∣ 2 :=
    y7c_swap_center_card c hKt hJKt hneKt hSM
  have hk2 : k * k = 1 := y7c_sq_eq_one_of_mem_center_map hkZ hcardK
  have hk'2 : k' * k' = 1 := y7c_sq_eq_one_of_mem_center_map hk'Zt hcardKt
  have hkk : k * k' = k' * k := hc k hkK k' hk'Kt
  rw [← hkk']
  calc (k * k') * (k * k') = k * ((k' * k) * k') := by group
    _ = k * ((k * k') * k') := by rw [← hkk]
    _ = (k * k) * (k' * k') := by group
    _ = 1 := by rw [hk2, hk'2, one_mul]

theorem y7c_swap_card_N (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hne : conjSub t K ≠ K) :
    Nat.card ↥(Subgroup.normalClosure (J : Set Γ)) =
      168 ^ 2 * Nat.card ↥(Subgroup.center ↥(Subgroup.normalClosure (J : Set Γ))) := by
  have hN : Subgroup.normalClosure (J : Set Γ) = K ⊔ conjSub t K :=
    y7c_swap_N_eq c hK hJK hne
  have hc : ∀ a ∈ K, ∀ b ∈ conjSub t K, a * b = b * a :=
    y7c_comm_of_components hK (y7c_isComponent_conjSub hK t) (Ne.symm hne)
  have hcZ : ∀ x ∈ (Subgroup.center ↥K).map K.subtype,
      ∀ y ∈ (Subgroup.center ↥(conjSub t K)).map (conjSub t K).subtype, x * y = y * x := by
    rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
    exact hc x' x'.2 y' y'.2
  have hKt : CFSG.IsComponent (conjSub t K) := y7c_isComponent_conjSub hK t
  have hsq : conjSub t (conjSub t K) = K := y7c_conjSub_conjSub_of_sq c.t_sq K
  have hJKt : J ≤ conjSub t K ⊔ conjSub t (conjSub t K) := by
    rw [hsq, sup_comm]; exact hJK
  have hneKt : conjSub t (conjSub t K) ≠ conjSub t K := by
    rw [hsq]; exact Ne.symm hne
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K (conjSub t K) hc).1
  have hprodZ := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      ((Subgroup.center ↥K).map K.subtype)
      ((Subgroup.center ↥(conjSub t K)).map (conjSub t K).subtype) hcZ).1
  have hcardK := y7c_swap_card_K c hK hJK hne
  have hcardKt := y7c_swap_card_K c hKt hJKt hneKt
  have hZN := y7c_center_sup_map_eq hc
  have hinf : (Subgroup.center ↥K).map K.subtype ⊓
      (Subgroup.center ↥(conjSub t K)).map (conjSub t K).subtype = K ⊓ conjSub t K := by
    refine le_antisymm ?_ ?_
    · apply le_inf
      · exact inf_le_left.trans (Subgroup.map_subtype_le (Subgroup.center ↥K))
      · exact inf_le_right.trans (Subgroup.map_subtype_le (Subgroup.center ↥(conjSub t K)))
    · rintro x ⟨hxK, hxKt⟩
      exact ⟨Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.mpr fun y =>
          Subtype.ext (hc y y.2 x hxKt), rfl⟩,
        Subgroup.mem_map.mpr ⟨⟨x, hxKt⟩, Subgroup.mem_center_iff.mpr fun y =>
          Subtype.ext (hc x hxK y y.2).symm, rfl⟩⟩
  have hcenter : Nat.card ↥(Subgroup.center ↥(K ⊔ conjSub t K)) =
      Nat.card ↥((Subgroup.center ↥K).map K.subtype ⊔
        (Subgroup.center ↥(conjSub t K)).map (conjSub t K).subtype) := by
    rw [← Subgroup.card_map_of_injective (K ⊔ conjSub t K).subtype_injective, hZN]
  have e1 : Nat.card ↥(K ⊔ conjSub t K) * Nat.card ↥(K ⊓ conjSub t K) =
      (168 * Nat.card ↥(Subgroup.center ↥K)) *
        (168 * Nat.card ↥(Subgroup.center ↥(conjSub t K))) := by
    rw [hprod, hcardK, hcardKt]
  have e2 : Nat.card ↥(Subgroup.center ↥(K ⊔ conjSub t K)) *
        Nat.card ↥(K ⊓ conjSub t K) =
      Nat.card ↥(Subgroup.center ↥K) *
        Nat.card ↥(Subgroup.center ↥(conjSub t K)) := by
    have h := hprodZ
    rw [← hcenter, hinf] at h
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective (conjSub t K).subtype_injective] at h
    exact h
  have key : Nat.card ↥(K ⊔ conjSub t K) * Nat.card ↥(K ⊓ conjSub t K) =
      (168 ^ 2 * Nat.card ↥(Subgroup.center ↥(K ⊔ conjSub t K))) *
        Nat.card ↥(K ⊓ conjSub t K) := by
    calc Nat.card ↥(K ⊔ conjSub t K) * Nat.card ↥(K ⊓ conjSub t K)
        = (168 * Nat.card ↥(Subgroup.center ↥K)) *
            (168 * Nat.card ↥(Subgroup.center ↥(conjSub t K))) := e1
      _ = 168 ^ 2 * (Nat.card ↥(Subgroup.center ↥K) *
            Nat.card ↥(Subgroup.center ↥(conjSub t K))) := by ring
      _ = 168 ^ 2 * (Nat.card ↥(Subgroup.center ↥(K ⊔ conjSub t K)) *
            Nat.card ↥(K ⊓ conjSub t K)) := by rw [← e2]
      _ = (168 ^ 2 * Nat.card ↥(Subgroup.center ↥(K ⊔ conjSub t K))) *
            Nat.card ↥(K ⊓ conjSub t K) := by ring
  rw [hN]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos key

end CFSG.OddStandard.HigherRank.YamadaG23
