module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarPerm
public import CFSG.LocalAnalysis.OddStandard.AltStdBalAct
public import CFSG.LocalAnalysis.OddStandard.AltStdSecStdAlt

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm

section Ineq

theorem two_mul_factorial_lt_succ {a k : ℕ} (hk : 2 ≤ k) (h4 : 4 ≤ a + 2 * k)
    (h : 2 * (a.factorial * 2 ^ k * k.factorial) < (a + 2 * k - 4).factorial) :
    2 * ((a + 1).factorial * 2 ^ k * k.factorial) < (a + 1 + 2 * k - 4).factorial := by
  have e1 : (a + 1 + 2 * k - 4).factorial = (a + 2 * k - 3) * (a + 2 * k - 4).factorial := by
    rw [show a + 1 + 2 * k - 4 = (a + 2 * k - 4) + 1 by omega, Nat.factorial_succ]
    congr 1
    omega
  have e2 : 2 * ((a + 1).factorial * 2 ^ k * k.factorial) =
      (a + 1) * (2 * (a.factorial * 2 ^ k * k.factorial)) := by
    rw [Nat.factorial_succ]; ring
  rw [e1, e2]
  calc (a + 1) * (2 * (a.factorial * 2 ^ k * k.factorial)) < (a + 1) * (a + 2 * k - 4).factorial :=
        Nat.mul_lt_mul_of_pos_left h (by omega)
    _ ≤ (a + 2 * k - 3) * (a + 2 * k - 4).factorial :=
        Nat.mul_le_mul_right _ (by omega)

theorem two_mul_factorial_lt_of_base {k a₀ : ℕ} (hk : 2 ≤ k) (h4 : 4 ≤ a₀ + 2 * k)
    (hbase : 2 * (a₀.factorial * 2 ^ k * k.factorial) < (a₀ + 2 * k - 4).factorial) :
    ∀ a, a₀ ≤ a → 2 * (a.factorial * 2 ^ k * k.factorial) < (a + 2 * k - 4).factorial := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => exact hbase
  | succ a ha ih => exact two_mul_factorial_lt_succ hk (by omega) ih

theorem two_mul_two_pow_factorial_lt (k : ℕ) (hk : 9 ≤ k) :
    2 * (2 ^ k * k.factorial) < (2 * k - 4).factorial := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ k hk ih =>
    have e1 : (2 * (k + 1) - 4).factorial = (2 * k - 2) * ((2 * k - 3) * (2 * k - 4).factorial) := by
      rw [show 2 * (k + 1) - 4 = (2 * k - 4) + 1 + 1 by omega, Nat.factorial_succ,
        Nat.factorial_succ, show 2 * k - 4 + 1 + 1 = 2 * k - 2 by omega,
        show 2 * k - 4 + 1 = 2 * k - 3 by omega]
    have e2 : 2 * (2 ^ (k + 1) * (k + 1).factorial) = (2 * (k + 1)) * (2 * (2 ^ k * k.factorial)) := by
      rw [pow_succ, Nat.factorial_succ]; ring
    rw [e1, e2]
    have h3 : 2 * (k + 1) ≤ (2 * k - 2) * (2 * k - 3) := by
      have : 15 ≤ 2 * k - 3 := by omega
      calc 2 * (k + 1) ≤ (2 * k - 2) * 2 := by omega
        _ ≤ (2 * k - 2) * (2 * k - 3) := Nat.mul_le_mul_left _ (by omega)
    calc (2 * (k + 1)) * (2 * (2 ^ k * k.factorial)) < (2 * (k + 1)) * (2 * k - 4).factorial :=
          Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ ≤ ((2 * k - 2) * (2 * k - 3)) * (2 * k - 4).factorial := Nat.mul_le_mul_right _ h3
      _ = (2 * k - 2) * ((2 * k - 3) * (2 * k - 4).factorial) := by ring

theorem two_mul_factorial_lt (a k : ℕ) (hk : 3 ≤ k) (h : 15 ≤ a + 2 * k) :
    2 * (a.factorial * 2 ^ k * k.factorial) < (a + 2 * k - 4).factorial := by
  rcases (by omega : k ≤ 8 ∨ 9 ≤ k) with hk8 | hk9
  · interval_cases k
    · exact two_mul_factorial_lt_of_base (a₀ := 9) (by norm_num) (by norm_num)
        (by norm_num [Nat.factorial]) a (by omega)
    · exact two_mul_factorial_lt_of_base (a₀ := 7) (by norm_num) (by norm_num)
        (by norm_num [Nat.factorial]) a (by omega)
    · exact two_mul_factorial_lt_of_base (a₀ := 5) (by norm_num) (by norm_num)
        (by norm_num [Nat.factorial]) a (by omega)
    · exact two_mul_factorial_lt_of_base (a₀ := 3) (by norm_num) (by norm_num)
        (by norm_num [Nat.factorial]) a (by omega)
    · exact two_mul_factorial_lt_of_base (a₀ := 1) (by norm_num) (by norm_num)
        (by norm_num [Nat.factorial]) a (by omega)
    · exact two_mul_factorial_lt_of_base (a₀ := 0) (by norm_num) (by norm_num)
        (by norm_num [Nat.factorial]) a (by omega)
  · refine two_mul_factorial_lt_of_base (a₀ := 0) (by omega) (by omega) ?_ a (by omega)
    have := two_mul_two_pow_factorial_lt k hk9
    simpa using this

end Ineq

section PermLem

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem card_support_eq_four_of_bounds (hα : 15 ≤ Fintype.card α) {π : Perm α}
    (h2 : π * π = 1)
    (hlo : (Fintype.card α - 4).factorial ≤ 2 * Nat.card (centralizer ({π} : Set (Perm α))))
    (hhi : Nat.card (centralizer ({π} : Set (Perm α))) ≤ 8 * (Fintype.card α - 4).factorial) :
    π.support.card = 4 := by
  set N := Fintype.card α with hN
  set k := Multiset.card π.cycleType with hk
  have hs := card_support_eq_two_mul_card_cycleType h2
  have hle : π.support.card ≤ N := Finset.card_le_univ _
  rw [nat_card_centralizer_of_mul_self h2, ← hk, ← hN] at hlo hhi
  have hX : 0 < (N - 4).factorial := Nat.factorial_pos _
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k) with h0 | h1 | h2' | h3
  · exfalso
    rw [h0] at hhi
    have e : (N - 2 * 0).factorial = N * ((N - 1) * ((N - 2) * ((N - 3) * (N - 4).factorial))) := by
      rw [show N - 2 * 0 = (N - 4) + 1 + 1 + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ,
        Nat.factorial_succ, Nat.factorial_succ]
      rw [show N - 4 + 1 + 1 + 1 + 1 = N by omega, show N - 4 + 1 + 1 + 1 = N - 1 by omega,
        show N - 4 + 1 + 1 = N - 2 by omega, show N - 4 + 1 = N - 3 by omega]
    rw [e] at hhi
    simp only [pow_zero, Nat.factorial_zero, mul_one] at hhi
    have h17 : 15 * (14 * (13 * (12 * (N - 4).factorial))) ≤
        N * ((N - 1) * ((N - 2) * ((N - 3) * (N - 4).factorial))) := by
      gcongr <;> omega
    omega
  · exfalso
    rw [h1] at hhi
    have e : (N - 2 * 1).factorial = (N - 2) * ((N - 3) * (N - 4).factorial) := by
      rw [show N - 2 * 1 = (N - 4) + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ,
        show N - 4 + 1 + 1 = N - 2 by omega, show N - 4 + 1 = N - 3 by omega]
    rw [e] at hhi
    simp only [pow_one, Nat.factorial_one, mul_one] at hhi
    have h17 : 13 * (12 * (N - 4).factorial) ≤ (N - 2) * ((N - 3) * (N - 4).factorial) := by
      gcongr <;> omega
    omega
  · omega
  · exfalso
    have := two_mul_factorial_lt (N - 2 * k) k h3 (by omega)
    rw [show N - 2 * k + 2 * k - 4 = N - 4 by omega] at this
    omega

theorem card_support_eq_four_of_fourteen (hα : Fintype.card α = 14) {π : Perm α}
    (h2 : π * π = 1)
    (hdvd : (Fintype.card α - 4).factorial ∣ 2 * Nat.card (centralizer ({π} : Set (Perm α))))
    (hhi : Nat.card (centralizer ({π} : Set (Perm α))) ≤ 8 * (Fintype.card α - 4).factorial) :
    π.support.card = 4 := by
  have hs := card_support_eq_two_mul_card_cycleType h2
  have hle : π.support.card ≤ Fintype.card α := Finset.card_le_univ _
  rw [nat_card_centralizer_of_mul_self h2, hα] at hdvd hhi
  rw [hα] at hle
  obtain ⟨k, hk⟩ : ∃ k, Multiset.card π.cycleType = k := ⟨_, rfl⟩
  rw [hk] at hdvd hhi hs
  have hk7 : k ≤ 7 := by omega
  interval_cases k
  all_goals first | omega | (revert hdvd hhi; norm_num [Nat.factorial])

theorem card_support_eq_four_of_thirteen (hα : Fintype.card α = 13) {π : Perm α}
    (h2 : π * π = 1)
    (hdvd : (Fintype.card α - 4).factorial ∣ 2 * Nat.card (centralizer ({π} : Set (Perm α))))
    (hhi : Nat.card (centralizer ({π} : Set (Perm α))) ≤ 8 * (Fintype.card α - 4).factorial) :
    π.support.card = 4 := by
  have hs := card_support_eq_two_mul_card_cycleType h2
  have hle : π.support.card ≤ Fintype.card α := Finset.card_le_univ _
  rw [nat_card_centralizer_of_mul_self h2, hα] at hdvd hhi
  rw [hα] at hle
  obtain ⟨k, hk⟩ : ∃ k, Multiset.card π.cycleType = k := ⟨_, rfl⟩
  rw [hk] at hdvd hhi hs
  have hk6 : k ≤ 6 := by omega
  interval_cases k
  all_goals first | omega | (revert hdvd hhi; norm_num [Nat.factorial])

omit [Fintype α] in
theorem mem_support_iff_of_comm [Fintype α] {π σ : Perm α} (h : σ * π = π * σ) (x : α) :
    x ∈ π.support ↔ σ x ∈ π.support := by
  rw [Perm.mem_support, Perm.mem_support]
  have e : π (σ x) = σ (π x) := by
    have := DFunLike.congr_fun h x
    simp only [Perm.mul_apply] at this
    exact this.symm
  rw [e]
  exact ⟨fun h1 h2 => h1 (σ.injective h2), fun h1 h2 => h1 (by rw [h2])⟩

theorem exists_swap_mul_swap {π : Perm α} (h2 : π * π = 1) (h4 : π.support.card = 4) :
    ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      π = swap a b * swap c d ∧ π.support = {a, b, c, d} := by
  have hpp : ∀ x, π (π x) = x := apply_apply_of_mul_self h2
  obtain ⟨a, ha⟩ : π.support.Nonempty := Finset.card_pos.1 (by omega)
  have hab : π a ≠ a := Perm.mem_support.1 ha
  have hb : π a ∈ π.support := Perm.mem_support.2 (by rw [hpp a]; exact hab.symm)
  have hcard : ((π.support.erase a).erase (π a)).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hab, hb⟩), Finset.card_erase_of_mem ha, h4]
  obtain ⟨c, hc⟩ : ((π.support.erase a).erase (π a)).Nonempty := Finset.card_pos.1 (by omega)
  simp only [Finset.mem_erase] at hc
  obtain ⟨hcb, hca, hcs⟩ := hc
  have hcc : π c ≠ c := Perm.mem_support.1 hcs
  have hd : π c ∈ π.support := Perm.mem_support.2 (by rw [hpp c]; exact hcc.symm)
  have hda : π c ≠ a := fun h => hcb (by rw [← h, hpp c])
  have hdb : π c ≠ π a := fun h => hca (π.injective h)
  refine ⟨a, π a, c, π c, hab.symm, hca.symm, hda.symm, hcb.symm, hdb.symm, hcc.symm, ?_, ?_⟩
  · have hsupp : π.support = {a, π a, c, π c} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ha
        · exact hb
        · exact hcs
        · exact hd
      · rw [h4]
        rw [Finset.card_insert_of_notMem (by simp [hab.symm, hca.symm, hda.symm]),
          Finset.card_insert_of_notMem (by simp [hcb.symm, hdb.symm]),
          Finset.card_pair hcc.symm]
    apply Equiv.ext
    intro x
    rw [Perm.mul_apply]
    by_cases hxa : x = a
    · subst hxa
      rw [swap_apply_of_ne_of_ne hca.symm hda.symm, swap_apply_left]
    by_cases hxb : x = π a
    · subst hxb
      rw [swap_apply_of_ne_of_ne hcb.symm hdb.symm, swap_apply_right, hpp]
    by_cases hxc : x = c
    · subst hxc
      rw [swap_apply_left, swap_apply_of_ne_of_ne hda hdb]
    by_cases hxd : x = π c
    · subst hxd
      rw [swap_apply_right, swap_apply_of_ne_of_ne hca hcb, hpp]
    have hxs : x ∉ π.support := by
      rw [hsupp]
      simp [hxa, hxb, hxc, hxd]
    rw [Perm.notMem_support.1 hxs, swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxb]
  · symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hcs
      · exact hd
    · rw [h4]
      rw [Finset.card_insert_of_notMem (by simp [hab.symm, hca.symm, hda.symm]),
        Finset.card_insert_of_notMem (by simp [hcb.symm, hdb.symm]),
        Finset.card_pair hcc.symm]

omit [DecidableEq α] in
theorem fixes_of_simple {A : Type*} [Group A] [Finite A] [IsSimpleGroup A] (f : A →* Perm α)
    {T : Finset α} (hT : ∀ a x, x ∈ T ↔ f a x ∈ T) (hcard : T.card.factorial < Nat.card A)
    (a : A) {x : α} (hx : x ∈ T) : f a x = x := by
  let r : A →* Perm ↥T :=
    { toFun := fun a => (f a).subtypePerm (fun x => (hT a x).symm)
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext x
        simp only [Perm.mul_apply, Perm.subtypePerm_apply, map_mul] }
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal r.ker with h | h
  · exfalso
    have hinj : Function.Injective r := (MonoidHom.ker_eq_bot_iff r).1 h
    have := Nat.card_le_card_of_injective r hinj
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := ↥T), Fintype.card_coe] at this
    omega
  · have h1 : r a = 1 := by
      have : a ∈ r.ker := h ▸ mem_top a
      exact this
    have := congrArg (fun p : Perm ↥T => ((p ⟨x, hx⟩ : ↥T) : α)) h1
    simpa [r] using this

theorem nat_card_le_two_mul_inf_alt (H : Subgroup (Perm α)) :
    Nat.card H ≤ 2 * Nat.card ↥(H ⊓ alternatingGroup α) := by
  set f : ↥H →* ℤˣ := Perm.sign.comp H.subtype with hf
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card f.range ≤ 2 := by
    calc Nat.card f.range ≤ Nat.card ℤˣ := Subgroup.card_le_card_group _
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h3 : Nat.card f.ker ≤ Nat.card ↥(H ⊓ alternatingGroup α) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : H) : Perm α),
      Subgroup.mem_inf.2 ⟨(k : H).2, (Perm.mem_alternatingGroup).2 k.2⟩⟩) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    simp only at this
    exact Subtype.ext (Subtype.ext this)
  calc Nat.card H = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ Nat.card ↥(H ⊓ alternatingGroup α) * 2 := Nat.mul_le_mul h3 h2
    _ = 2 * Nat.card ↥(H ⊓ alternatingGroup α) := mul_comm _ _

end PermLem

section Alt

variable {Y : Type} [Group Y] [Finite Y] {N : ℕ}

theorem false_of_alt (hN : 13 ≤ N) {X : Subgroup Y} [X.Normal]
    (ψ : X ≃* alternatingGroup (Fin N)) {t : Y} (ht : t * t = 1) {L : Subgroup Y}
    (hLX : L ≤ X) (hLt : L ≤ centralizer ({t} : Set Y)) (eL : L ≃* alternatingGroup (Fin (N - 4)))
    (hCt : Nat.card (centralizer ({t} : Set Y)) ≤ 4 * (N - 4).factorial)
    (hK : ∀ u v : Y, u * t = t * u → u ∈ centralizer (L : Set Y) → v * t = t * v →
      v ∈ centralizer (L : Set Y) → IsConj u v → u = v) : False := by
  classical
  set α : MulAut X := MulAut.conjNormal t with hα
  set α' : MulAut (alternatingGroup (Fin N)) := ψ.symm.trans (α.trans ψ) with hα'
  set π := AltStdBal.autEquivPerm (by omega : 8 ≤ N) α' with hπdef
  have hπ : MulAut.conjNormal (H := alternatingGroup (Fin N)) π = α' :=
    AltStdBal.conjNormal_autEquivPerm _ _
  have key : ∀ x : X, π * ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N)) * π⁻¹ =
      ((ψ (α x) : alternatingGroup (Fin N)) : Perm (Fin N)) := by
    intro x
    have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin N)) =>
      ((φ (ψ x) : alternatingGroup (Fin N)) : Perm (Fin N))) hπ
    simp only [MulAut.conjNormal_apply] at h1
    rw [h1, hα']
    simp
  have hαx : ∀ x : X, ((α x : X) : Y) = t * x * t⁻¹ := fun x => MulAut.conjNormal_apply t x
  have hπ2 : π * π = 1 := by
    apply AltStdBal.conjNormal_injective' (by omega : 8 ≤ N)
    rw [map_mul, hπ, map_one]
    ext a
    simp only [hα', MulEquiv.trans_apply, MulAut.mul_apply, MulAut.one_apply]
    congr 1
    have : α (α (ψ.symm a)) = ψ.symm a := by
      apply Subtype.ext
      rw [hαx, hαx]
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
      rw [hti]
      calc t * (t * ((ψ.symm a : X) : Y) * t) * t = (t * t) * (ψ.symm a : Y) * (t * t) := by group
        _ = _ := by rw [ht]; group
    rw [MulEquiv.symm_apply_apply, this, MulEquiv.apply_symm_apply]
  set CP := centralizer ({π} : Set (Perm (Fin N))) with hCP
  have hcomm_of : ∀ x : X, ((t : Y) * x * t⁻¹ = x) →
      ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N)) * π =
        π * ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N)) := by
    intro x hx
    have h1 := key x
    have h2 : α x = x := Subtype.ext ((hαx x).trans hx)
    rw [h2] at h1
    calc ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N)) * π =
        (π * ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N)) * π⁻¹) * π := by rw [h1]
      _ = π * ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N)) := by group
  have hA : Nat.card ↥(CP ⊓ alternatingGroup (Fin N)) ≤ Nat.card (centralizer ({t} : Set Y)) := by
    refine Nat.card_le_card_of_injective (fun a => ⟨((ψ.symm ⟨(a : Perm (Fin N)),
      (Subgroup.mem_inf.1 a.2).2⟩ : X) : Y), ?_⟩) ?_
    · rw [mem_centralizer_singleton_iff]
      set x := ψ.symm ⟨(a : Perm (Fin N)), (Subgroup.mem_inf.1 a.2).2⟩
      have ha := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 a.2).1
      have h1 := key x
      rw [MulEquiv.apply_symm_apply] at h1
      have h2 : π * (a : Perm (Fin N)) * π⁻¹ = (a : Perm (Fin N)) := by
        calc π * (a : Perm (Fin N)) * π⁻¹ = (a : Perm (Fin N)) * π * π⁻¹ := by rw [ha]
          _ = (a : Perm (Fin N)) := by group
      rw [h2] at h1
      have h3 : ψ (α x) = ψ x := by
        apply Subtype.ext
        rw [← h1, MulEquiv.apply_symm_apply]
      have h4 : α x = x := ψ.injective h3
      have h5 := congrArg Subtype.val h4
      rw [hαx] at h5
      calc (x : Y) * t = (t * x * t⁻¹) * t := by rw [h5]
        _ = t * x := by group
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      simp only at h1
      have h2 := ψ.symm.injective (Subtype.ext h1)
      exact Subtype.ext (congrArg (fun x : alternatingGroup (Fin N) => (x : Perm (Fin N))) h2)
  have hLA : Nat.card L ≤ Nat.card ↥(CP ⊓ alternatingGroup (Fin N)) := by
    refine Nat.card_le_card_of_injective (fun l => ⟨((ψ ⟨l, hLX l.2⟩ : alternatingGroup (Fin N)) :
      Perm (Fin N)), Subgroup.mem_inf.2 ⟨?_, (ψ ⟨l, hLX l.2⟩).2⟩⟩) ?_
    · rw [mem_centralizer_singleton_iff]
      refine hcomm_of _ ?_
      have := mem_centralizer_singleton_iff.1 (hLt l.2)
      change t * (l : Y) * t⁻¹ = l
      rw [← this]; group
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      simp only at h1
      have h2 := ψ.injective (Subtype.ext h1)
      exact Subtype.ext (congrArg (fun x : X => (x : Y)) h2)
  have hCPA : Nat.card ↥(CP ⊓ alternatingGroup (Fin N)) ≤ Nat.card CP :=
    Subgroup.card_le_of_le inf_le_left
  have hCP2 := nat_card_le_two_mul_inf_alt CP
  have hLcard : 2 * Nat.card L = (N - 4).factorial := by
    have : Nontrivial (Fin (N - 4)) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [Nat.card_congr eL.toEquiv, two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
  have hcard : Fintype.card (Fin N) = N := Fintype.card_fin N
  set fL : L →* Perm (Fin N) := (alternatingGroup (Fin N)).subtype.comp
    (ψ.toMonoidHom.comp (Subgroup.inclusion hLX)) with hfL
  have hfLc : ∀ l : L, fL l * π = π * fL l := by
    intro l
    refine hcomm_of _ ?_
    have := mem_centralizer_singleton_iff.1 (hLt l.2)
    change t * (l : Y) * t⁻¹ = l
    rw [← this]; group
  have hdvd : (N - 4).factorial ∣ 2 * Nat.card CP := by
    have hfLinj : Function.Injective fL :=
      (Subgroup.subtype_injective _).comp (ψ.injective.comp (Subgroup.inclusion_injective hLX))
    have h1 : fL.range ≤ CP := by
      rintro _ ⟨l, rfl⟩
      exact mem_centralizer_singleton_iff.2 (hfLc l)
    have h2 := Subgroup.card_dvd_of_le h1
    rw [← Nat.card_congr (MonoidHom.ofInjective hfLinj).toEquiv] at h2
    rw [← hLcard]
    exact Nat.mul_dvd_mul_left 2 h2
  have h4 : π.support.card = 4 := by
    rcases (by omega : N = 13 ∨ N = 14 ∨ 15 ≤ N) with h13 | h14 | h15
    · exact card_support_eq_four_of_thirteen (hcard.trans h13) hπ2
        (by rw [hcard, ← hCP]; exact hdvd) (by rw [hcard, ← hCP]; omega)
    · exact card_support_eq_four_of_fourteen (hcard.trans h14) hπ2 (by rw [hcard, ← hCP]; exact hdvd)
        (by rw [hcard, ← hCP]; omega)
    · exact card_support_eq_four_of_bounds (by rw [hcard]; omega) hπ2
        (by rw [hcard, ← hCP]; omega) (by rw [hcard, ← hCP]; omega)
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hπe, hsupp⟩ := exists_swap_mul_swap hπ2 h4
  have hsL : IsSimpleGroup L := isSimpleGroup_of_alt (by omega) eL
  have hfix : ∀ l : L, ∀ x ∈ π.support, fL l x = x := by
    intro l x hx
    refine fixes_of_simple fL (fun l y => mem_support_iff_of_comm (hfLc l) y) ?_ l hx
    rw [h4]
    have : Nat.card L = (N - 4).factorial / 2 := by omega
    have h13 : Nat.factorial 9 ≤ (N - 4).factorial := Nat.factorial_le (by omega)
    have : (24 : ℕ) < Nat.factorial 9 / 2 := by decide
    have : Nat.factorial 4 = 24 := rfl
    omega
  have hsw : ∀ x y : Fin N, x ≠ y → Perm.sign (swap x y) = -1 := fun x y h => Perm.sign_swap h
  have hρA : swap a d * swap b c ∈ alternatingGroup (Fin N) := by
    rw [Perm.mem_alternatingGroup, map_mul, hsw _ _ had, hsw _ _ hbc]; rfl
  have hπA : π ∈ alternatingGroup (Fin N) := by
    rw [Perm.mem_alternatingGroup, hπe, map_mul, hsw _ _ hab, hsw _ _ hcd]; rfl
  have hgA : swap b c * swap b d ∈ alternatingGroup (Fin N) := by
    rw [Perm.mem_alternatingGroup, map_mul, hsw _ _ hbc, hsw _ _ hbd]; rfl
  have hgπ : (swap b c * swap b d) * π * (swap b c * swap b d)⁻¹ = swap a d * swap b c := by
    rw [hπe]
    have e1 : (swap b c * swap b d) * (swap a b * swap c d) * (swap b c * swap b d)⁻¹ =
        ((swap b c * swap b d) * swap a b * (swap b c * swap b d)⁻¹) *
          ((swap b c * swap b d) * swap c d * (swap b c * swap b d)⁻¹) := by group
    rw [e1, ← swap_apply_apply, ← swap_apply_apply]
    have ha' : (swap b c * swap b d) a = a := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab had, swap_apply_of_ne_of_ne hab hac]
    have hb' : (swap b c * swap b d) b = d := by
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hbd.symm hcd.symm]
    have hc' : (swap b c * swap b d) c = b := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hbc.symm hcd, swap_apply_right]
    have hd' : (swap b c * swap b d) d = c := by
      rw [Perm.mul_apply, swap_apply_right, swap_apply_left]
    rw [ha', hb', hc', hd']
  have hρπ : (swap a d * swap b c) * π = π * (swap a d * swap b c) := by
    have e1 : π * (swap a d * swap b c) * π⁻¹ = swap a d * swap b c := by
      have e2 : π * (swap a d * swap b c) * π⁻¹ =
          (π * swap a d * π⁻¹) * (π * swap b c * π⁻¹) := by group
      rw [e2, ← swap_apply_apply, ← swap_apply_apply, hπe]
      have pa : (swap a b * swap c d) a = b := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left]
      have pb : (swap a b * swap c d) b = a := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hbc hbd, swap_apply_right]
      have pc : (swap a b * swap c d) c = d := by
        rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne had.symm hbd.symm]
      have pd : (swap a b * swap c d) d = c := by
        rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hac.symm hbc.symm]
      rw [pa, pb, pc, pd]
      exact swap_mul_swap_comm_of_ne hab.symm hbd hac.symm hcd
    calc (swap a d * swap b c) * π = π * (swap a d * swap b c) * π⁻¹ * π := by rw [e1]
      _ = π * (swap a d * swap b c) := by group
  have hπρ : π ≠ swap a d * swap b c := by
    intro h
    have := DFunLike.congr_fun h a
    rw [hπe, Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left, Perm.mul_apply,
      swap_apply_of_ne_of_ne hab hac, swap_apply_left] at this
    exact hbd this
  set u : X := ψ.symm ⟨π, hπA⟩ with hu
  set v : X := ψ.symm ⟨swap a d * swap b c, hρA⟩ with hv
  set w : X := ψ.symm ⟨swap b c * swap b d, hgA⟩ with hw
  have hcomm_t : ∀ x : X, ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N)) * π =
      π * ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N)) → (x : Y) * t = t * x := by
    intro x hx
    have h1 := key x
    have h2 : π * ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N)) * π⁻¹ =
        ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N)) := by rw [← hx]; group
    rw [h2] at h1
    have h3 : α x = x := ψ.injective (Subtype.ext h1.symm)
    have h5 := congrArg Subtype.val h3
    rw [hαx] at h5
    calc (x : Y) * t = (t * x * t⁻¹) * t := by rw [h5]
      _ = t * x := by group
  have hdisj : ∀ (l : L) (σ : Perm (Fin N)), (∀ x, x ∉ π.support → σ x = x) →
      fL l * σ = σ * fL l := by
    intro l σ hσ
    refine Perm.Disjoint.commute (fun x => ?_)
    by_cases hx : x ∈ π.support
    · exact Or.inl (hfix l x hx)
    · exact Or.inr (hσ x hx)
  have hcomm_L : ∀ x : X, (∀ y, y ∉ π.support →
      ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N)) y = y) →
      (x : Y) ∈ centralizer (L : Set Y) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro l hl
    have h1 := hdisj ⟨l, hl⟩ _ hx
    have h2 : ψ (⟨l, hLX hl⟩ * x) = ψ (x * ⟨l, hLX hl⟩) := by
      apply Subtype.ext
      rw [map_mul, map_mul]
      exact h1
    have h3 := congrArg Subtype.val (ψ.injective h2)
    simpa using h3
  have hπfix : ∀ y, y ∉ π.support → π y = y := fun y hy => Perm.notMem_support.1 hy
  have hρfix : ∀ y, y ∉ π.support → (swap a d * swap b c) y = y := by
    intro y hy
    rw [hsupp] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hy.2.1 hy.2.2.1,
      swap_apply_of_ne_of_ne hy.1 hy.2.2.2]
  have hu1 : (u : Y) * t = t * u := hcomm_t u (by rw [hu, MulEquiv.apply_symm_apply])
  have hv1 : (v : Y) * t = t * v := hcomm_t v (by rw [hv, MulEquiv.apply_symm_apply]; exact hρπ)
  have hu2 : (u : Y) ∈ centralizer (L : Set Y) :=
    hcomm_L u (by rw [hu, MulEquiv.apply_symm_apply]; exact hπfix)
  have hv2 : (v : Y) ∈ centralizer (L : Set Y) :=
    hcomm_L v (by rw [hv, MulEquiv.apply_symm_apply]; exact hρfix)
  have hconj : IsConj (u : Y) (v : Y) := by
    refine isConj_iff.2 ⟨(w : Y), ?_⟩
    have h1 : w * u * w⁻¹ = v := by
      apply ψ.injective
      apply Subtype.ext
      rw [map_mul, map_mul, map_inv, hu, hv, hw, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact hgπ
    have := congrArg Subtype.val h1
    simpa using this
  have huv := hK _ _ hu1 hu2 hv1 hv2 hconj
  apply hπρ
  have h1 : u = v := Subtype.ext huv
  have h2 := congrArg (fun x => ((ψ x : alternatingGroup (Fin N)) : Perm (Fin N))) h1
  simpa [hu, hv] using h2

end Alt

end CFSG.OddStandard.AltStdSec
