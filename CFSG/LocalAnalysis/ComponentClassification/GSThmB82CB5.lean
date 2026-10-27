module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB4

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer Seven
open scoped commutatorElement

namespace Eight2

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

theorem P_inf_conjugate_eq_bot' (hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a) {g : X}
    (hg : g ∈ normalizer (h.S : Set X)) (hga : g⁻¹ * h.a * g ≠ h.a) :
    h.P ⊓ conjugate h.P g = ⊥ := by
  by_contra hne
  obtain ⟨w, hw, hw1, hwZ⟩ := exists_mem_center_of_normal h.isPGroup_S
    (inf_le_left.trans h.P_le_S)
    (fun t ht v hv => mem_inf.mpr ⟨h.conj_mem_P ht (mem_inf.mp hv).1,
      h.sec8_conj_mem_conjugate_P hg ht (mem_inf.mp hv).2⟩) hne
  obtain ⟨hwP, hwg⟩ := mem_inf.mp hw
  have hPZ : ∀ v ∈ h.P, (∀ t ∈ h.S, t * v = v * t) → v ≠ 1 → v = h.a := by
    intro v hvP hvZ hv1
    have hv : v ∈ h.P ⊓ centralizer (h.S : Set X) :=
      mem_inf.mpr ⟨hvP, mem_centralizer_iff.mpr hvZ⟩
    rw [hC] at hv
    exact (eq_one_or_of_mem_zpowers h.orderOf_a hv).resolve_left hv1
  have hwa := hPZ w hwP hwZ hw1
  rw [mem_conjugate_iff] at hwg
  have hpZ : ∀ t ∈ h.S, t * (g * w * g⁻¹) = g * w * g⁻¹ * t := by
    intro t ht
    have htg : g⁻¹ * t * g ∈ h.S := by
      have := (mem_normalizer_iff.mp (inv_mem hg) t).mp ht
      rwa [inv_inv] at this
    have h1 := hwZ _ htg
    calc t * (g * w * g⁻¹) = g * ((g⁻¹ * t * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * t * g)) * g⁻¹ := by rw [h1]
      _ = g * w * g⁻¹ * t := by group
  have hp1 : g * w * g⁻¹ ≠ 1 := fun h1 => hw1 (by
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  have hpa := hPZ _ hwg hpZ hp1
  apply hga
  calc g⁻¹ * h.a * g = g⁻¹ * (g * w * g⁻¹) * g := by rw [hpa]
    _ = w := by group
    _ = h.a := hwa

theorem conjugate_P_inf_kernel' (hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a) {g : X}
    (hg : g ∈ normalizer (h.S : Set X)) (hga : g⁻¹ * h.a * g ≠ h.a) :
    conjugate h.P g ⊓ coreActionKernel h.J = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwg, hwK⟩ := mem_inf.mp hw
  have hwP : w ∈ h.P := mem_inf.mpr ⟨h.sec8_conjugate_P_le_S hg hwg, hwK⟩
  have := P_inf_conjugate_eq_bot' hC hg hga ▸ mem_inf.mpr ⟨hwP, hwg⟩
  exact this

theorem not_conj_a_az (Z : ZData h) (hSa : IsSylowIn h.S (centralizer ({h.a} : Set X)))
    (hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a)
    (hZJ : center (h.J ⧸ pPrimeCore 2 h.J) = ⊥) (hP8 : 8 ≤ Nat.card h.P) (g : X) :
    g⁻¹ * h.a * g ≠ h.a * Z.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hg
  have hzS : Z.z ∈ h.S := h.D_le_S Z.hzD
  have hSaz : h.S ≤ centralizer ({h.a * Z.z} : Set X) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    calc w * (h.a * Z.z) = (w * h.a) * Z.z := by group
      _ = (h.a * w) * Z.z := by rw [h.comm_a hw]
      _ = h.a * (w * Z.z) := by group
      _ = h.a * (Z.z * w) := by rw [Z.hzS w hw]
      _ = h.a * Z.z * w := by group
  obtain ⟨g', hg'N, hg'⟩ := exists_normalizer_conj_of_sylow hSa hSaz hg
  have hga : g'⁻¹ * h.a * g' ≠ h.a := by
    rw [hg']
    intro h1
    apply Z.hz1
    calc Z.z = h.a⁻¹ * (h.a * Z.z) := by group
      _ = 1 := by rw [h1, inv_mul_cancel]
  have hDP := h.D_inf_P_eq_bot hZJ
  have hDP' : h.D ⊓ conjugate h.P g' = ⊥ := by
    by_contra hne
    obtain ⟨w, hw, hw1, hwZ⟩ := exists_mem_center_of_normal h.isPGroup_S
      (inf_le_left.trans h.D_le_S)
      (fun t ht v hv => mem_inf.mpr ⟨h.sec8_conj_mem_D ht (mem_inf.mp hv).1,
        h.sec8_conj_mem_conjugate_P hg'N ht (mem_inf.mp hv).2⟩) hne
    obtain ⟨hwD, hwg⟩ := mem_inf.mp hw
    rw [mem_conjugate_iff] at hwg
    have hpZ : ∀ t ∈ h.S, t * (g' * w * g'⁻¹) = g' * w * g'⁻¹ * t := by
      intro t ht
      have htg : g'⁻¹ * t * g' ∈ h.S := by
        have := (mem_normalizer_iff.mp (inv_mem hg'N) t).mp ht
        rwa [inv_inv] at this
      have h1 := hwZ _ htg
      calc t * (g' * w * g'⁻¹) = g' * ((g'⁻¹ * t * g') * w) * g'⁻¹ := by group
        _ = g' * (w * (g'⁻¹ * t * g')) * g'⁻¹ := by rw [h1]
        _ = g' * w * g'⁻¹ * t := by group
    have hv : g' * w * g'⁻¹ ∈ h.P ⊓ centralizer (h.S : Set X) :=
      mem_inf.mpr ⟨hwg, mem_centralizer_iff.mpr hpZ⟩
    rw [hC] at hv
    rcases eq_one_or_of_mem_zpowers h.orderOf_a hv with h1 | h1
    · apply hw1
      calc w = g'⁻¹ * (g' * w * g'⁻¹) * g' := by group
        _ = 1 := by rw [h1]; group
    · have hw' : w = h.a * Z.z := by
        calc w = g'⁻¹ * (g' * w * g'⁻¹) * g' := by group
          _ = h.a * Z.z := by rw [h1, hg']
      have haD : h.a ∈ h.D := by
        have := mul_mem (hw' ▸ hwD) (inv_mem Z.hzD)
        rwa [mul_inv_cancel_right] at this
      have := hDP ▸ mem_inf.mpr ⟨haD, h.a_mem_P⟩
      have ha1 := mem_bot.mp this
      have h2 := h.orderOf_a
      rw [ha1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
  have hcomm : ∀ x ∈ h.D, ∀ p ∈ conjugate h.P g', x * p = p * x := by
    intro x hx p hp
    have hpS : p ∈ h.S := h.sec8_conjugate_P_le_S hg'N hp
    have h1 : x * p * x⁻¹ * p⁻¹ ∈ h.D ⊓ conjugate h.P g' := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [show x * p * x⁻¹ * p⁻¹ = x * (p * x⁻¹ * p⁻¹) by group]
        exact mul_mem hx (h.sec8_conj_mem_D hpS (inv_mem hx))
      · rw [show x * p * x⁻¹ * p⁻¹ = (x * p * x⁻¹) * p⁻¹ by group]
        exact mul_mem (h.sec8_conj_mem_conjugate_P hg'N (h.D_le_S hx) hp) (inv_mem hp)
    rw [hDP', mem_bot] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hWN : conjugate h.P g' ≤ normalizer (h.J : Set X) :=
    (h.sec8_conjugate_P_le_S hg'N).trans h.S_le_normalizer
  have hW := conjugate_P_inf_kernel' hC hg'N hga
  have hle : rhoImg h.J (conjugate h.P g') ≤
      centralizer (innOf (Dbar h) : Set (MulAut (Jbar h))) := by
    rw [← rhoImg_eq_innOf h.D_le_J]
    rintro _ ⟨⟨p, hpN⟩, hp, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hcomm x (mem_subgroupOf.mp hx) p (mem_subgroupOf.mp hp)
  have hR2 : IsPGroup 2 (rhoImg h.J (conjugate h.P g')) := by
    have hW2 : IsPGroup 2 (conjugate h.P g') :=
      h.isPGroup_S.to_le (h.sec8_conjugate_P_le_S hg'N)
    exact (hW2.of_equiv (subgroupOfEquivOfLe hWN).symm).map _
  have h4 := Z.hC4 _ hR2 hle
  rw [card_rhoImg hWN hW le_rfl, card_conjugate] at h4
  omega

omit [Finite X] in
theorem conj_mem_comm_of_normalizer {S : Subgroup X} {u w : X} (hu : u ∈ normalizer (S : Set X))
    (hw : w ∈ ⁅S, S⁆) : u⁻¹ * w * u ∈ ⁅S, S⁆ := by
  have hS : S.map (MulAut.conj u⁻¹).toMonoidHom = S := by
    ext v
    constructor
    · rintro ⟨v', hv', rfl⟩
      change u⁻¹ * v' * u⁻¹⁻¹ ∈ S
      exact (mem_normalizer_iff.mp (inv_mem hu) v').mp hv'
    · intro hv
      refine ⟨u * v * u⁻¹, (mem_normalizer_iff.mp hu v).mp hv, ?_⟩
      change u⁻¹ * (u * v * u⁻¹) * u⁻¹⁻¹ = v
      group
  have h1 : ⁅S, S⁆.map (MulAut.conj u⁻¹).toMonoidHom = ⁅S, S⁆ := by
    rw [map_commutator, hS]
  rw [← h1]
  refine ⟨w, hw, ?_⟩
  change u⁻¹ * w * u⁻¹⁻¹ = u⁻¹ * w * u
  rw [inv_inv]

omit [Finite X] in
theorem conj_mem_center' {S : Subgroup X} {u w : X} (hu : u ∈ normalizer (S : Set X))
    (hwS : w ∈ S) (hwZ : ∀ t ∈ S, t * w = w * t) :
    u⁻¹ * w * u ∈ S ∧ ∀ t ∈ S, t * (u⁻¹ * w * u) = (u⁻¹ * w * u) * t := by
  refine ⟨?_, fun t ht => ?_⟩
  · have := (mem_normalizer_iff.mp (inv_mem hu) w).mp hwS
    rwa [inv_inv] at this
  · have htu : u * t * u⁻¹ ∈ S := (mem_normalizer_iff.mp hu t).mp ht
    have h1 := hwZ _ htu
    calc t * (u⁻¹ * w * u) = u⁻¹ * ((u * t * u⁻¹) * w) * u := by group
      _ = u⁻¹ * (w * (u * t * u⁻¹)) * u := by rw [h1]
      _ = u⁻¹ * w * u * t := by group

theorem exists_swap (hComm : CF82L2Comm) (Z : ZData h)
    (hSa : IsSylowIn h.S (centralizer ({h.a} : Set X)))
    (hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a)
    (hZJ : center (h.J ⧸ pPrimeCore 2 h.J) = ⊥) (hP8 : 8 ≤ Nat.card h.P)
    (haS : h.a ∈ ⁅h.S, h.S⁆) (hzS' : Z.z ∈ ⁅h.S, h.S⁆)
    (hNS : ¬ normalizer (h.S : Set X) ≤ centralizer ({h.a} : Set X)) :
    ∃ u ∈ normalizer (h.S : Set X), u⁻¹ * h.a * u = Z.z ∧ u⁻¹ * Z.z * u = h.a ∧
      u * u ∈ h.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u₀, hu₀N, hu₀a⟩ := Set.not_subset.mp hNS
  have hu₀a' : u₀⁻¹ * h.a * u₀ ≠ h.a := by
    intro h1
    apply hu₀a
    show u₀ ∈ centralizer ({h.a} : Set X)
    rw [mem_centralizer_singleton_iff]
    calc u₀ * h.a = u₀ * (u₀⁻¹ * h.a * u₀) := by rw [h1]
      _ = h.a * u₀ := by group
  have hzZ : ∀ t ∈ h.S, t * Z.z = Z.z * t := Z.hzS
  have haZ : ∀ t ∈ h.S, t * h.a = h.a * t := fun t ht => h.comm_a ht
  have ha1 : h.a ≠ 1 := by
    intro h1
    have h2 := h.orderOf_a
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hza : Z.z ≠ h.a := fun h1 => Z.hzP (h1 ▸ h.a_mem_P)
  have hnaz := not_conj_a_az Z hSa hC hZJ hP8
  obtain ⟨-, hwZ⟩ := conj_mem_center' hu₀N h.a_mem_S haZ
  have hw : u₀⁻¹ * h.a * u₀ = Z.z := by
    rcases comm_center_cases hComm Z hC (conj_mem_comm_of_normalizer hu₀N haS) hwZ with
      h1 | h1 | h1 | h1
    · exfalso
      apply ha1
      calc h.a = u₀ * (u₀⁻¹ * h.a * u₀) * u₀⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · exact absurd h1 hu₀a'
    · exact h1
    · exact absurd h1 (hnaz u₀)
  obtain ⟨-, hw'Z⟩ := conj_mem_center' hu₀N (h.D_le_S Z.hzD) hzZ
  have hw' : u₀⁻¹ * Z.z * u₀ = h.a := by
    rcases comm_center_cases hComm Z hC (conj_mem_comm_of_normalizer hu₀N hzS') hw'Z with
      h1 | h1 | h1 | h1
    · exfalso
      apply Z.hz1
      calc Z.z = u₀ * (u₀⁻¹ * Z.z * u₀) * u₀⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · exact h1
    · exfalso
      apply hza
      have h2 : u₀⁻¹ * h.a * u₀ = u₀⁻¹ * Z.z * u₀ := by rw [hw, h1]
      have h3 : h.a = Z.z := by
        have := congrArg (fun v => u₀ * v * u₀⁻¹) h2
        simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at this
        exact this
      exact h3.symm
    · exfalso
      have haz : (u₀⁻¹)⁻¹ * h.a * u₀⁻¹ = h.a * Z.z := by
        have h2 : u₀⁻¹ * (h.a * Z.z) * u₀ = h.a := by
          rw [show u₀⁻¹ * (h.a * Z.z) * u₀ = (u₀⁻¹ * h.a * u₀) * (u₀⁻¹ * Z.z * u₀) by group,
            hw, h1, ← mul_assoc, ← hzZ _ h.a_mem_S, mul_assoc, Z.hzz, mul_one]
        calc (u₀⁻¹)⁻¹ * h.a * u₀⁻¹ = u₀ * (u₀⁻¹ * (h.a * Z.z) * u₀) * u₀⁻¹ := by
              rw [h2, inv_inv]
          _ = h.a * Z.z := by group
      exact hnaz u₀⁻¹ haz
  set N₀ := normalizer (h.S : Set X) ⊓ centralizer ({h.a} : Set X) with hN₀
  have hSN₀ : h.S ≤ N₀ := le_inf le_normalizer hSa.1
  have hN₀C : N₀ ≤ centralizer ({h.a} : Set X) := inf_le_right
  have hu₂ : u₀ * u₀ ∈ N₀ := by
    refine mem_inf.mpr ⟨mul_mem hu₀N hu₀N, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : (u₀ * u₀)⁻¹ * h.a * (u₀ * u₀) = h.a := by
      rw [show (u₀ * u₀)⁻¹ * h.a * (u₀ * u₀) = u₀⁻¹ * (u₀⁻¹ * h.a * u₀) * u₀ by group, hw, hw']
    calc u₀ * u₀ * h.a = u₀ * u₀ * ((u₀ * u₀)⁻¹ * h.a * (u₀ * u₀)) := by rw [h1]
      _ = h.a * (u₀ * u₀) := by group
  have hodd : ¬ 2 ∣ h.S.relIndex N₀ := by
    obtain ⟨-, R, hR⟩ := hSa
    have h1 : ¬ 2 ∣ (h.S.subgroupOf (centralizer ({h.a} : Set X))).index := by
      rw [← hR]; exact R.not_dvd_index
    have h2 := Subgroup.relIndex_mul_relIndex h.S N₀ (centralizer ({h.a} : Set X)) hSN₀ hN₀C
    intro h3
    apply h1
    change 2 ∣ h.S.relIndex (centralizer ({h.a} : Set X))
    rw [← h2]
    exact Dvd.dvd.mul_right h3 _
  set m := h.S.relIndex N₀ with hm
  have hmS : (u₀ * u₀) ^ m ∈ h.S := by
    have : (h.S.subgroupOf N₀).Normal := by
      refine (normal_subgroupOf_iff_le_normalizer hSN₀).mpr inf_le_left
    have h1 : (QuotientGroup.mk' (h.S.subgroupOf N₀) ⟨u₀ * u₀, hu₂⟩) ^ m = 1 := by
      rw [hm, Subgroup.relIndex, Subgroup.index]
      exact pow_card_eq_one'
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    simpa using h1
  obtain ⟨k, hk⟩ : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have hu₂z : u₀ * u₀ ∈ centralizer ({Z.z} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : (u₀ * u₀)⁻¹ * Z.z * (u₀ * u₀) = Z.z := by
      rw [show (u₀ * u₀)⁻¹ * Z.z * (u₀ * u₀) = u₀⁻¹ * (u₀⁻¹ * Z.z * u₀) * u₀ by group, hw', hw]
    calc u₀ * u₀ * Z.z = u₀ * u₀ * ((u₀ * u₀)⁻¹ * Z.z * (u₀ * u₀)) := by rw [h1]
      _ = Z.z * (u₀ * u₀) := by group
  set v := (u₀ * u₀) ^ k with hv
  have hva : v ∈ centralizer ({h.a} : Set X) := pow_mem (hN₀C hu₂) k
  have hvz : v ∈ centralizer ({Z.z} : Set X) := pow_mem hu₂z k
  rw [mem_centralizer_singleton_iff] at hva hvz
  have hcv : v * u₀ = u₀ * v := by
    have hcomm : Commute u₀ (u₀ * u₀) := (Commute.refl u₀).mul_right (Commute.refl u₀)
    exact ((hcomm.pow_right k).eq).symm
  refine ⟨u₀ * v, mul_mem hu₀N (pow_mem (mul_mem hu₀N hu₀N) k), ?_, ?_, ?_⟩
  · calc (u₀ * v)⁻¹ * h.a * (u₀ * v) = v⁻¹ * (u₀⁻¹ * h.a * u₀) * v := by group
      _ = Z.z := by rw [hw, mul_assoc, ← hvz, inv_mul_cancel_left]
  · calc (u₀ * v)⁻¹ * Z.z * (u₀ * v) = v⁻¹ * (u₀⁻¹ * Z.z * u₀) * v := by group
      _ = h.a := by rw [hw', mul_assoc, ← hva, inv_mul_cancel_left]
  · have huu : u₀ * v * (u₀ * v) = (u₀ * u₀) ^ m := by
      calc u₀ * v * (u₀ * v) = u₀ * (v * u₀) * v := by group
        _ = u₀ * (u₀ * v) * v := by rw [hcv]
        _ = (u₀ * u₀) * (v * v) := by group
        _ = (u₀ * u₀) ^ (k + k + 1) := by rw [hv, ← pow_add, ← pow_succ']
        _ = (u₀ * u₀) ^ m := by rw [hk]; ring_nf
    rw [huu]
    exact hmS

end Eight2

end CFSG.ComponentClassification.GSThmB
