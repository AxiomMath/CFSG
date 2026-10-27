module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1T13
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1PtsA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8c

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

private lemma y7a_zpowers_two_elems {x : G} (hx : x * x = 1) :
    ∀ y ∈ zpowers x, y = 1 ∨ y = x := by
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
    rw [h2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
    rw [h2, one_zpow, one_mul]

private lemma y7a_zpowers_comm_A (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {w a : G}
    (hw : w ∈ zpowers z) (ha : a ∈ A) : w * a = a * w := by
  rcases y7a_zpowers_two_elems (y7a_z_sq h) w hw with rfl | rfl
  · simp
  · exact (y6q8_z_central h.cfg.rel a (by simpa [h.cfg.hA] using ha)).symm

private lemma y7a_not_mem_zpowers_of_sq_z (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {a : G}
    (ha : a * a = z) : a ∉ zpowers z := by
  intro hZ
  rcases y7a_zpowers_two_elems (y7a_z_sq h) a hZ with h1 | hz
  · rw [h1] at ha
    exact h.cfg.z_ne (by simpa using ha.symm)
  · rw [hz, y7a_z_sq h] at ha
    exact h.cfg.z_ne ha.symm

private lemma y7a_mul_not_mem_zpowers (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : ⁅x, y⁆ = z) : x * y ∉ zpowers z := by
  intro hZ
  have hcomm := y7a_zpowers_comm_A h hZ hx
  have hyx : y * x = x * y := by
    have h2 : x⁻¹ * ((x * y) * x) = x⁻¹ * (x * (x * y)) :=
      congrArg (fun w => x⁻¹ * w) hcomm
    rwa [show x⁻¹ * ((x * y) * x) = y * x by group,
      show x⁻¹ * (x * (x * y)) = x * y by group] at h2
  exact h.cfg.z_ne (by rw [← hxy, commutatorElement_eq_one_iff_mul_comm.mpr hyx.symm])

private lemma y7a_inv_mul_not_mem_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : ⁅x, y⁆ = z) : x⁻¹ * y ∉ V := by
  intro hV
  have hZ : x⁻¹ * y ∈ zpowers z := by
    rw [← y7a_A_inf_V h]; exact ⟨A.mul_mem (A.inv_mem hx) hy, hV⟩
  have hcomm := y7a_zpowers_comm_A h hZ hx
  have hmem : x⁻¹ * y * x = y := by
    have h2 := hcomm
    rwa [show x * (x⁻¹ * y) = y by group] at h2
  have hyx : y * x = x * y := by
    have h2 : x * (x⁻¹ * y * x) = x * y := congrArg (fun w => x * w) hmem
    rwa [show x * (x⁻¹ * y * x) = y * x by group] at h2
  exact h.cfg.z_ne (by rw [← hxy, commutatorElement_eq_one_iff_mul_comm.mpr hyx.symm])

private lemma y7a_conj_not_mem_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : ⁅x, y⁆ = z) : x⁻¹ * y * x ∉ V := by
  intro hV
  have hZ : x⁻¹ * y * x ∈ zpowers z := by
    rw [← y7a_A_inf_V h]
    exact ⟨A.mul_mem (A.mul_mem (A.inv_mem hx) hy) hx, hV⟩
  have hvcomm := y7a_zpowers_comm_A h hZ hx
  have hmem : x⁻¹ * y * x = y := by
    have hconj : x * (x⁻¹ * y * x) * x⁻¹ = x⁻¹ * y * x := by rw [← hvcomm]; group
    have hxvx : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [← hconj]; exact hxvx
  have hyx : y * x = x * y := by
    have h2 : x * (x⁻¹ * y * x) = x * y := congrArg (fun w => x * w) hmem
    rwa [show x * (x⁻¹ * y * x) = y * x by group] at h2
  exact h.cfg.z_ne (by rw [← hxy, commutatorElement_eq_one_iff_mul_comm.mpr hyx.symm])

private lemma y7a_uit_inv_atv (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {a u v : G}
    (ha : a ∈ A) (hu : u ∈ A) :
    (u * t)⁻¹ * (a * t * v) = (u⁻¹ * a) * v := by
  have ht2 : t * t = 1 := y7a_t_sq h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hcomm : t * (u⁻¹ * a) = (u⁻¹ * a) * t :=
    (h.cfg.t_cent (u⁻¹ * a) (A.mul_mem (A.inv_mem hu) ha)).symm
  calc (u * t)⁻¹ * (a * t * v) = t⁻¹ * u⁻¹ * a * t * v := by rw [mul_inv_rev]; group
    _ = t * u⁻¹ * a * t * v := by rw [hti]
    _ = (t * (u⁻¹ * a) * t) * v := by group
    _ = (u⁻¹ * a) * v := by
          rw [show t * (u⁻¹ * a) * t = u⁻¹ * a by rw [hcomm, mul_assoc, ht2, mul_one]]

private lemma y7a_rel_swap {p q p' q' z : G} (h : Y6ARel p q p' q' z) :
    Y6ARel p' q' p q z where
  z_sq := h.z_sq
  a1_sq := h.a2_sq
  b1_sq := h.b2_sq
  a2_sq := h.a1_sq
  b2_sq := h.b1_sq
  comm1 := h.comm2
  comm2 := h.comm1
  a1a2 := by rw [← commutatorElement_inv, h.a1a2, inv_one]
  a1b2 := by rw [← commutatorElement_inv, h.b1a2, inv_one]
  b1a2 := by rw [← commutatorElement_inv, h.a1b2, inv_one]
  b1b2 := by rw [← commutatorElement_inv, h.b1b2, inv_one]

private lemma y7a_mixed_excl (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {X : Subgroup G}
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G))
    {p q p' q' : G} (hAeq : A = (closure {p, q, p', q'} : Subgroup G))
    (hrel : Y6ARel p q p' q' z) (hUp : ∀ w ∈ y6Up A V t, w ∈ y7aO X V t)
    (hOut : ∀ a ∈ (closure {p, q} : Subgroup G), a ∉ zpowers z → a * t ∉ y7aO X V t)
    (hIn : ∀ a ∈ (closure {p', q'} : Subgroup G), a ∉ zpowers z → a * t ∈ y7aO X V t) :
    False := by
  have hz : z ≠ 1 := h.cfg.z_ne
  have hcard : Nat.card ↥(closure {p, q, p', q'} : Subgroup G) = 32 := by
    rw [← hAeq]; exact h.cfg.card_A
  have hpA : p ∈ A := by rw [hAeq]; exact Subgroup.subset_closure (by simp)
  have hqA : q ∈ A := by rw [hAeq]; exact Subgroup.subset_closure (by simp)
  have hp2 : p * p = z := by simpa [pow_two] using hrel.a1_sq
  have hq2 : q * q = z := by simpa [pow_two] using hrel.b1_sq
  have hp'2 : p' * p' = z := by simpa [pow_two] using hrel.a2_sq
  have hpq : ⁅p, q⁆ = z := hrel.comm1
  have hpp' : p * p' = p' * p :=
    (y6q8_commUW hrel p (Subgroup.subset_closure (by simp)) p'
      (Subgroup.subset_closure (by simp))).eq
  have hEnum := y6q8_U_elems hrel
  have hInter := (y6q8_card_UW hrel hz hcard).2.2
  have hSqIn : ∀ a ∈ A, a ^ 2 = z → a ∈ (closure {p, q} : Subgroup G) ∨
      a ∈ (closure {p', q'} : Subgroup G) := by
    intro a ha haz
    have ha' : a ∈ (closure {p, q, p', q'} : Subgroup G) := by rwa [hAeq] at ha
    exact ((y6q8_sqz_iff hrel hz hcard a ha').mp haz).1
  let u : Fin 3 → G := ![p, q, p * q]
  have huA : ∀ i, u i ∈ A := by
    intro i
    fin_cases i
    · simpa [u] using hpA
    · simpa [u] using hqA
    · simpa [u] using A.mul_mem hpA hqA
  have hpq_notV : p⁻¹ * q ∉ V := y7a_inv_mul_not_mem_V h hpA hqA hpq
  have hq_notV : q ∉ V := fun hV =>
    y7a_not_mem_zpowers_of_sq_z h hq2 (by rw [← y7a_A_inf_V h]; exact ⟨hqA, hV⟩)
  have hpq_inv_notV : q⁻¹ * p ∉ V := by
    intro hh
    apply hpq_notV
    have h1 : (q⁻¹ * p)⁻¹ ∈ V := V.inv_mem hh
    rwa [show (q⁻¹ * p)⁻¹ = p⁻¹ * q by group] at h1
  have hqp : ⁅q, p⁆ = z := by
    rw [← commutatorElement_inv, hpq,
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hrel.z_sq)]
  have hconj_notV : q⁻¹ * p * q ∉ V := y7a_conj_not_mem_V h hqA hpA hqp
  have hqinv_notV : q⁻¹ ∉ V := by
    intro hh
    apply hq_notV
    have h1 : (q⁻¹)⁻¹ ∈ V := V.inv_mem hh
    rwa [inv_inv] at h1
  have hconjinv_notV : q⁻¹ * p⁻¹ * q ∉ V := by
    intro hh
    apply hconj_notV
    have h1 : (q⁻¹ * p⁻¹ * q)⁻¹ ∈ V := V.inv_mem hh
    rwa [show (q⁻¹ * p⁻¹ * q)⁻¹ = q⁻¹ * p * q by group] at h1
  have hne : ∀ i j : Fin 3, i ≠ j → (u i)⁻¹ * u j ∉ V := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · convert hpq_notV using 1; simp [u]
    · convert hq_notV using 1; simp [u]
    · convert hpq_inv_notV using 1; simp [u]
    · exact absurd rfl hij
    · convert hconj_notV using 1 <;> simp [u] <;> group
    · convert hqinv_notV using 1; simp [u]
    · convert hconjinv_notV using 1 <;> simp [u] <;> group
    · exact absurd rfl hij
  have hnO : ∀ i, u i * t ∉ y7aO X V t := by
    intro i
    fin_cases i
    · simpa [u] using hOut p (Subgroup.subset_closure (by simp))
        (y7a_not_mem_zpowers_of_sq_z h hp2)
    · simpa [u] using hOut q (Subgroup.subset_closure (by simp))
        (y7a_not_mem_zpowers_of_sq_z h hq2)
    · simpa [u] using hOut (p * q)
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
        (y7a_mul_not_mem_zpowers h hpA hqA hpq)
  have hcov : ∀ w ∈ A ⊔ C0, w ∉ A ⊔ V →
      w ∈ y7aO X V t ∨ ∃ i, (u i * t)⁻¹ * w ∈ V := by
    intro w hwC hwAV
    rcases y7a_C1_split h w hwC with h1 | h2 | h3
    · exact absurd h1 hwAV
    · obtain ⟨a, ha, haz, v, hv, rfl⟩ := h2
      rcases hSqIn a ha haz with haP | haQ
      · right
        have haz1 : a ≠ 1 := by
          intro h1; rw [h1] at haz; exact h.cfg.z_ne (by simpa using haz.symm)
        have haz2 : a ≠ z := by
          intro h1; rw [h1] at haz; rw [h.cfg.rel.z_sq] at haz; exact h.cfg.z_ne haz.symm
        rcases hEnum a haP with h1 | h2' | h3' | h4' | h5' | h6' | h7' | h8'
        · exact absurd h1 haz1
        · exact absurd h2' haz2
        · refine ⟨0, ?_⟩
          rw [h3', y7a_uit_inv_atv h hpA (huA 0),
            show (u 0)⁻¹ * p = 1 by simp [u]]
          simpa using hv
        · refine ⟨0, ?_⟩
          rw [h4', y7a_uit_inv_atv h (A.mul_mem hpA (y7a_z_mem_A h)) (huA 0),
            show (u 0)⁻¹ * (p * z) = z by simp [u]]
          exact V.mul_mem (y7a_z_mem_V h) hv
        · refine ⟨1, ?_⟩
          rw [h5', y7a_uit_inv_atv h hqA (huA 1),
            show (u 1)⁻¹ * q = 1 by simp [u]]
          simpa using hv
        · refine ⟨1, ?_⟩
          rw [h6', y7a_uit_inv_atv h (A.mul_mem hqA (y7a_z_mem_A h)) (huA 1),
            show (u 1)⁻¹ * (q * z) = z by simp [u]]
          exact V.mul_mem (y7a_z_mem_V h) hv
        · refine ⟨2, ?_⟩
          rw [h7', y7a_uit_inv_atv h (A.mul_mem hpA hqA) (huA 2),
            show (u 2)⁻¹ * (p * q) = 1 by simp [u]]
          simpa using hv
        · refine ⟨2, ?_⟩
          rw [h8', y7a_uit_inv_atv h (A.mul_mem (A.mul_mem hpA hqA) (y7a_z_mem_A h))
            (huA 2),
            show (u 2)⁻¹ * (p * q * z) = z by (simp [u]; group)]
          exact V.mul_mem (y7a_z_mem_V h) hv
      · left
        have haZ : a ∉ zpowers z :=
          y7a_not_mem_zpowers_of_sq_z h (by simpa [pow_two] using haz)
        exact y7a_O_V (hIn a haQ haZ) hv
    · exact Or.inl (hUp w h3)
  have hp'A : p' ∈ A := by rw [hAeq]; exact Subgroup.subset_closure (by simp)
  have hrA : p * p' ∈ A := A.mul_mem hpA hp'A
  have hzIn : z ∈ (closure {p', q'} : Subgroup G) := by
    rw [← hp'2]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have hZsub : zpowers z ≤ (closure {p', q'} : Subgroup G) := Subgroup.zpowers_le.mpr hzIn
  have hrV : p * p' ∉ V := by
    intro hV
    have hZ : p * p' ∈ zpowers z := by
      rw [← y7a_A_inf_V h]; exact ⟨hrA, hV⟩
    have hpInW : p ∈ (closure {p', q'} : Subgroup G) := by
      have hp'inv : p'⁻¹ ∈ (closure {p', q'} : Subgroup G) :=
        (Subgroup.closure {p', q'}).inv_mem (Subgroup.subset_closure (by simp))
      have heq : p = (p * p') * p'⁻¹ := by group
      rw [heq]
      exact (Subgroup.closure {p', q'}).mul_mem (hZsub hZ) hp'inv
    have hpInU : p ∈ (closure {p, q} : Subgroup G) := Subgroup.subset_closure (by simp)
    rcases (hInter p).mp ⟨hpInU, hpInW⟩ with h1 | hz'
    · rw [h1] at hp2
      exact h.cfg.z_ne (by simpa using hp2.symm)
    · rw [hz', y7a_z_sq h] at hp2
      exact h.cfg.z_ne hp2.symm
  have hr_sq : (p * p') * (p * p') = 1 := by
    calc (p * p') * (p * p') = p * (p' * p) * p' := by group
      _ = p * (p * p') * p' := by rw [← hpp']
      _ = (p * p) * (p' * p') := by group
      _ = z * z := by rw [hp2, hp'2]
      _ = 1 := y7a_z_sq h
  have hr : (p * p') * t ∈ y7aO X V t :=
    hUp _ ⟨p * p', hrA, by simpa [pow_two] using hr_sq, 1, one_mem V, by group⟩
  exact y7a_exclude13 h hX1 hX2 u huA hne hnO hcov (p * p') hrA hrV hr

theorem y7a_trichotomy (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {X Q : Subgroup G}
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G))
    (hQX : Q ≤ X) (hQt : ∀ k ∈ Q, k * t = t * k)
    (hU : IsOrbitMod Q (zpowers z) ((closure {a₁, b₁} : Set G) \ (zpowers z : Set G)))
    (hW : IsOrbitMod Q (zpowers z) ((closure {a₂, b₂} : Set G) \ (zpowers z : Set G)))
    (hUp : ∀ w ∈ y6Up A V t, w ∈ y7aO X V t) :
    (∀ w ∈ A ⊔ C0, w ∉ A ⊔ V → w ∈ y7aO X V t) ∨ (∀ w ∈ y6Um A V z t, w ∉ y7aO X V t) := by
  have htz : t * z = z * t := (h.cfg.t_cent z (y7a_z_mem_A h)).symm
  have hUdich := y7a_O_dich hQX hX2 hQt (y7a_z_mem_V h) htz hU
  have hWdich := y7a_O_dich hQX hX2 hQt (y7a_z_mem_V h) htz hW
  have hAeq2 : A = (closure {a₂, b₂, a₁, b₁} : Subgroup G) := by
    have hset : ({a₁, b₁, a₂, b₂} : Set G) = {a₂, b₂, a₁, b₁} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [h.cfg.hA, hset]
  rcases hUdich with hUall | hUnone
  · rcases hWdich with hWall | hWnone
    · refine Or.inl ?_
      intro w hwC hwAV
      rcases y7a_C1_split h w hwC with h1 | h2 | h3
      · exact absurd h1 hwAV
      · obtain ⟨a, ha, haz, v, hv, rfl⟩ := h2
        have hA' : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by rwa [h.cfg.hA] at ha
        obtain ⟨hUW, -, -⟩ :=
          (y6q8_sqz_iff h.cfg.rel h.cfg.z_ne (by rw [← h.cfg.hA]; exact h.cfg.card_A)
            a hA').mp haz
        have haZ : a ∉ zpowers z :=
          y7a_not_mem_zpowers_of_sq_z h (by simpa [pow_two] using haz)
        have hatO : a * t ∈ y7aO X V t := by
          rcases hUW with hu | hw
          · exact hUall a ⟨hu, haZ⟩
          · exact hWall a ⟨hw, haZ⟩
        exact y7a_O_V hatO hv
      · exact hUp w h3
    · exact (y7a_mixed_excl h hX1 hX2 hAeq2 (y7a_rel_swap h.cfg.rel) hUp
        (fun a ha hZ => hWnone a ⟨ha, hZ⟩) (fun a ha hZ => hUall a ⟨ha, hZ⟩)).elim
  · rcases hWdich with hWall | hWnone
    · exact (y7a_mixed_excl h hX1 hX2 (by rw [h.cfg.hA]) h.cfg.rel hUp
        (fun a ha hZ => hUnone a ⟨ha, hZ⟩) (fun a ha hZ => hWall a ⟨ha, hZ⟩)).elim
    · refine Or.inr ?_
      intro w hw hwO
      obtain ⟨a, ha, haz, v, hv, rfl⟩ := hw
      have hA' : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by rwa [h.cfg.hA] at ha
      obtain ⟨hUW, -, -⟩ :=
        (y6q8_sqz_iff h.cfg.rel h.cfg.z_ne (by rw [← h.cfg.hA]; exact h.cfg.card_A)
          a hA').mp haz
      have haZ : a ∉ zpowers z :=
        y7a_not_mem_zpowers_of_sq_z h (by simpa [pow_two] using haz)
      have hnotO : a * t ∉ y7aO X V t := by
        rcases hUW with hu | hw
        · exact hUnone a ⟨hu, haZ⟩
        · exact hWnone a ⟨hw, haZ⟩
      exact hnotO ((y7a_O_V_iff hv).mp hwO)

end CFSG.OddStandard.HigherRank.YamadaG23
