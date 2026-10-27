module

public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Classes

public noncomputable section

namespace CFSG.EvenSmallLie.FFourTwo.Cover

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

variable {K : Type} [Field K] {M : Type*} [Group M] (C : Cover K M) [Finite M]
  [Group.IsPerfect M]

omit [Finite M] [Group.IsPerfect M] in
theorem card_sq_map
    (ψ : C.Uhat →* C.Uhat) (hψ : Function.Bijective ψ) (a : C.Uhat) :
    Nat.card {u : C.Uhat // (u : M) * u = (ψ a : M)} =
      Nat.card {u : C.Uhat // (u : M) * u = a} := by
  refine (Nat.card_congr ((Equiv.ofBijective ψ hψ).subtypeEquiv fun u => ?_)).symm
  change (u : M) * u = a ↔ (ψ u : M) * ψ u = ψ a
  constructor
  · intro h
    have h' : u * u = a := Subtype.ext h
    rw [← h', map_mul]; rfl
  · intro h
    have h' : ψ (u * u) = ψ a := Subtype.ext (by rw [map_mul]; exact h)
    exact congrArg Subtype.val (hψ.1 h')

theorem sqCounts_eq {c : ℕ} (hc : c < 8) {v : ℕ} (hv : v = 3 ∨ v = 7)
    (h : sqCounts.getD c 0 = sqCounts.getD v 0) : c = v := by
  rcases hv with rfl | rfl <;> interval_cases c <;> simp_all [sqCounts]

theorem aut_fixes_37
    (ψ : C.Uhat →* C.Uhat) (hψ : Function.Injective ψ) {v : ℕ}
    (hv : v = 3 ∨ v = 7) :
    (ψ ⟨Pc.nf C.gU (v * 2 ^ 22), C.nf_mem (by rcases hv with rfl | rfl <;> norm_num)⟩ : M) =
      Pc.nf C.gU (v * 2 ^ 22) := by
  have hv8 : v < 8 := by rcases hv with rfl | rfl <;> norm_num
  have hb : Function.Bijective ψ := Finite.injective_iff_bijective.1 hψ
  set a : C.Uhat := ⟨Pc.nf C.gU (v * 2 ^ 22), C.nf_mem (by omega)⟩
  have hcen : ∀ y ∈ C.Uhat, (ψ a : M) * y = y * ψ a := by
    intro y hy
    obtain ⟨b, hb'⟩ := hb.2 ⟨y, hy⟩
    have : a * b = b * a := Subtype.ext (C.nf_mul_two_pow_mem_center hv8 b.2)
    have h2 := congrArg Subtype.val (congrArg ψ this)
    simp only [map_mul, Subgroup.coe_mul, hb'] at h2
    exact h2
  obtain ⟨c, hc, hca⟩ := C.eq_of_mem_center (ψ a).2 hcen
  have h1 := C.card_sq_map ψ hb a
  rw [hca, C.card_sq hc] at h1
  change _ = Nat.card {u : C.Uhat // (u : M) * u = Pc.nf C.gU (v * 2 ^ 22)} at h1
  rw [C.card_sq hv8] at h1
  rw [hca, sqCounts_eq hc hv (by omega)]

theorem aut_fixes_z
    (ψ : C.Uhat →* C.Uhat) (hψ : Function.Injective ψ) :
    (ψ ⟨C.z, C.z_mem_Uhat⟩ : M) = C.z := by
  have hz : C.z = Pc.nf C.gU (3 * 2 ^ 22) * Pc.nf C.gU (7 * 2 ^ 22) := by
    rw [← (C.nf_mulU (by norm_num) (by norm_num)).1, small_spec.2.2.2.1, Pc.nf_two_pow, C.gU_24]
  have e : (⟨C.z, C.z_mem_Uhat⟩ : C.Uhat) =
      ⟨Pc.nf C.gU (3 * 2 ^ 22), C.nf_mem (by norm_num)⟩ *
        ⟨Pc.nf C.gU (7 * 2 ^ 22), C.nf_mem (by norm_num)⟩ := Subtype.ext hz
  rw [e, map_mul, Subgroup.coe_mul, C.aut_fixes_37 ψ hψ (Or.inl rfl),
    C.aut_fixes_37 ψ hψ (Or.inr rfl), ← hz]

omit [Group.IsPerfect M] in
theorem isPGroup_Uhat
    : IsPGroup 2 C.Uhat := IsPGroup.of_card C.card_Uhat

theorem mul_self_ne_z_of_mem
    (m : M) : m * m ≠ C.z := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : m ^ 2 = C.z := by rw [sq, h]
  have h4 : m ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, h2, sq, C.z_mul_z]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (orderOf_dvd_of_pow_eq_one (show m ^ (2 ^ 2) = 1 from h4))
  have hP : IsPGroup 2 (zpowers m) := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  set U' := C.isPGroup_Uhat.toSylow C.not_two_dvd_index_Uhat
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M Q U'
  have hU' : ((U' : Sylow 2 M) : Subgroup M) = C.Uhat := IsPGroup.toSylow_coe _ _
  have hm : c * m * c⁻¹ ∈ C.Uhat := by
    rw [← hU', ← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.2 (by
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hQ (mem_zpowers m))
  refine C.mul_self_ne_z hm ?_
  calc c * m * c⁻¹ * (c * m * c⁻¹) = c * (m * m) * c⁻¹ := by group
    _ = C.z := by rw [h, C.z_comm c, mul_inv_cancel_right]

section Witness

variable {X : ℕ} {N : Subgroup M}

theorem letter_mem
    (hX : X < 2 ^ 25)
    (hh : ∀ a < 4, C.hEl a * Pc.nf C.gU X = Pc.nf C.gU X * C.hEl a → C.hEl a ∈ N)
    (hn : ∀ u : M, u * Pc.nf C.gU X = Pc.nf C.gU X * u → ∀ n ∈ N, u * n * u⁻¹ ∈ N)
    {ra : ℕ × ℕ} (h : letterOK X ra = true) :
    Pc.nf C.gU (commHU ra.2 (2 ^ ra.1)) ∈ N ∧ commHU ra.2 (2 ^ ra.1) < 2 ^ 25 := by
  simp only [letterOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hr : 2 ^ ra.1 < 2 ^ 25 := two_pow_lt (by omega)
  obtain ⟨c1, c2⟩ := C.nf_commHU h2 hr h3
  refine ⟨?_, c2⟩
  have hx := (C.nf_hU h2 hX h4).1
  rw [h5] at hx
  have hcomm : C.hEl ra.2 * Pc.nf C.gU X = Pc.nf C.gU X * C.hEl ra.2 :=
    (eq_mul_inv_iff_mul_eq.1 hx).symm
  have hg : C.gU ra.1 * Pc.nf C.gU X = Pc.nf C.gU X * C.gU ra.1 := by
    have := congrArg (Pc.nf C.gU) h6
    rwa [(C.nf_mulU hr hX).1, (C.nf_mulU hX hr).1, Pc.nf_two_pow] at this
  rw [c1, Pc.nf_two_pow, commutatorElement_def]
  exact mul_mem (hn _ hg _ (hh _ h2 hcomm)) (inv_mem (hh _ h2 hcomm))

theorem foldl_mem
    (hX : X < 2 ^ 25)
    (hh : ∀ a < 4, C.hEl a * Pc.nf C.gU X = Pc.nf C.gU X * C.hEl a → C.hEl a ∈ N)
    (hn : ∀ u : M, u * Pc.nf C.gU X = Pc.nf C.gU X * u → ∀ n ∈ N, u * n * u⁻¹ ∈ N) :
    ∀ (w : List (ℕ × ℕ)) (acc : ℕ), acc < 2 ^ 25 → Pc.nf C.gU acc ∈ N →
      w.all (letterOK X) = true →
      Pc.nf C.gU (w.foldl (fun acc ra => mulU acc (commHU ra.2 (2 ^ ra.1))) acc) ∈ N ∧
        w.foldl (fun acc ra => mulU acc (commHU ra.2 (2 ^ ra.1))) acc < 2 ^ 25
  | [], acc, h1, h2, _ => ⟨h2, h1⟩
  | ra :: w, acc, h1, h2, h3 => by
    simp only [List.all_cons, Bool.and_eq_true] at h3
    obtain ⟨l1, l2⟩ := C.letter_mem hX hh hn h3.1
    obtain ⟨m1, m2⟩ := C.nf_mulU h1 l2
    exact foldl_mem hX hh hn w _ m2 (by rw [m1]; exact mul_mem h2 l1) h3.2

theorem witProd_mem
    (hX : X < 2 ^ 25)
    (hh : ∀ a < 4, C.hEl a * Pc.nf C.gU X = Pc.nf C.gU X * C.hEl a → C.hEl a ∈ N)
    (hn : ∀ u : M, u * Pc.nf C.gU X = Pc.nf C.gU X * u → ∀ n ∈ N, u * n * u⁻¹ ∈ N)
    {w : List (ℕ × ℕ)} (h : w.all (letterOK X) = true) :
    Pc.nf C.gU (witProd w) ∈ N ∧ witProd w < 2 ^ 25 :=
  C.foldl_mem hX hh hn w 0 (by positivity) (by rw [Pc.nf_zero]; exact one_mem _) h

theorem exists_sq_of_witOK
    (hX : X < 2 ^ 25)
    (hh : ∀ a < 4, C.hEl a * Pc.nf C.gU X = Pc.nf C.gU X * C.hEl a → C.hEl a ∈ N)
    (hn : ∀ u : M, u * Pc.nf C.gU X = Pc.nf C.gU X * u → ∀ n ∈ N, u * n * u⁻¹ ∈ N)
    {w : List (ℕ × ℕ)} (h : witOK X w = true) : ∃ y ∈ N, y * y = Pc.nf C.gU X := by
  simp only [witOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨m1, m2⟩ := C.witProd_mem hX hh hn h.1
  refine ⟨_, m1, ?_⟩
  rw [← (C.nf_mulU m2 m2).1, h.2]

theorem Uhat_le_of_genOK
    (hX : X < 2 ^ 25)
    (hh : ∀ a < 4, C.hEl a * Pc.nf C.gU X = Pc.nf C.gU X * C.hEl a → C.hEl a ∈ N)
    (hn : ∀ u : M, u * Pc.nf C.gU X = Pc.nf C.gU X * u → ∀ n ∈ N, u * n * u⁻¹ ∈ N)
    {ws : List (List (ℕ × ℕ))} (h : genOK X ws = true) : C.Uhat ≤ N := by
  simp only [genOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have := (C.witProd_mem hX hh hn (List.all_eq_true.2 (h k hk).1)).1
  rwa [(h k hk).2, Pc.nf_two_pow] at this

end Witness

end CFSG.EvenSmallLie.FFourTwo.Cover
