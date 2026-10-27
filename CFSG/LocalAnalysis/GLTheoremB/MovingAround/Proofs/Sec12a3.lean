module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12a2
public import CFSG.LocalAnalysis.GLTheoremB.AltAut
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12a3K

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec12a3

open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremB CFSG.Open

abbrev dbl : Perm (Fin 7) := S7.a * S7.b

set_option maxRecDepth 100000 in
theorem dbl_no_involution :
    ∀ g : Perm (Fin 7), Perm.sign g = 1 → g * dbl = dbl * g → g * g = 1 → g = 1 :=
  Sec12a3K.dbl_no_involution_K

set_option maxRecDepth 100000 in
theorem three_cent_pow_six :
    ∀ g : Perm (Fin 7), Perm.sign g = 1 → g * S7.a = S7.a * g → g ^ 6 = 1 :=
  Sec12a3K.three_cent_pow_six_K

set_option maxRecDepth 100000 in
theorem three_cent_involution_mem :
    ∀ g : Perm (Fin 7), Perm.sign g = 1 → g * S7.a = S7.a * g → g * g = 1 →
      g = 1 ∨ g = S7.x ∨ g = S7.y ∨ g = S7.x * S7.y :=
  Sec12a3K.three_cent_involution_mem_K

set_option maxRecDepth 100000 in
theorem three_fpf_check :
    ∀ τ : Perm (Fin 7), τ * S7.a = S7.a * τ → τ ^ 3 = 1 → τ ≠ 1 → τ ≠ S7.a → τ ≠ S7.a ^ 2 →
      ∀ v : Perm (Fin 7), v ∈ [S7.x, S7.y, S7.x * S7.y] → τ * v * τ⁻¹ = v → v = 1 :=
  Sec12a3K.three_fpf_check_K

theorem cycleType_of_pow_three {π : Perm (Fin 7)} (h3 : π ^ 3 = 1) (h1 : π ≠ 1) :
    π.cycleType = {3} ∨ π.cycleType = {3, 3} := by
  have hdvd : orderOf π ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hall : ∀ c ∈ π.cycleType, c = 3 := by
    intro c hc
    have h1' : c ∣ orderOf π := by
      rw [← Equiv.Perm.lcm_cycleType]
      exact Multiset.dvd_lcm hc
    have h2 : c ∣ 3 := h1'.trans hdvd
    have h3' : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hc
    have : c ≤ 3 := Nat.le_of_dvd (by norm_num) h2
    interval_cases c
    · exact absurd h2 (by norm_num)
    · rfl
  have hne : π.cycleType ≠ 0 := fun h => h1 (Equiv.Perm.cycleType_eq_zero.1 h)
  have hsum : π.cycleType.sum ≤ 7 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hrep : π.cycleType = Multiset.replicate (Multiset.card π.cycleType) 3 :=
    Multiset.eq_replicate.2 ⟨rfl, hall⟩
  set k := Multiset.card π.cycleType with hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd (Multiset.card_eq_zero.1 h) hne
    · exact h
  have hk2 : k ≤ 2 := by
    rw [hrep, Multiset.sum_replicate] at hsum
    simp at hsum
    omega
  interval_cases k
  · left; simp [hrep]
  · right; simp [hrep]

set_option maxRecDepth 100000 in
theorem dbl_cycleType : dbl.cycleType = {3, 3} := by
  have h3 : dbl ^ 3 = 1 := by decide
  have h1 : dbl ≠ 1 := by decide
  have hsupp : dbl.support.card = 6 := by decide
  rcases cycleType_of_pow_three h3 h1 with h | h
  · have hs := Equiv.Perm.sum_cycleType dbl
    rw [h, hsupp] at hs
    simp at hs
  · exact h

theorem conj_of_cycleType_three {π : Perm (Fin 7)} (hπ : π.cycleType = {3}) :
    ∃ c : Perm (Fin 7), c * S7.a * c⁻¹ = π := by
  have hA : S7.a.cycleType = {3} := by
    have : S7.a.IsThreeCycle := card_support_eq_three_iff.1 (by decide)
    exact this
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 (hA.trans hπ.symm))
  exact ⟨c, hc⟩

theorem conj_of_cycleType_double {π : Perm (Fin 7)} (hπ : π.cycleType = {3, 3}) :
    ∃ c : Perm (Fin 7), c * dbl * c⁻¹ = π := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 (dbl_cycleType.trans hπ.symm))
  exact ⟨c, hc⟩

def kleinGroup : Subgroup (Perm (Fin 7)) where
  carrier := {g | g = 1 ∨ g = S7.x ∨ g = S7.y ∨ g = S7.x * S7.y}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rcases hg with rfl | rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    rcases hg with rfl | rfl | rfl | rfl <;> decide

theorem V_le_kleinGroup : S7.V ≤ kleinGroup :=
  sup_le (Subgroup.zpowers_le.2 (by
      show S7.x ∈ kleinGroup
      exact Or.inr (Or.inl rfl)))
    (Subgroup.zpowers_le.2 (by
      show S7.y ∈ kleinGroup
      exact Or.inr (Or.inr (Or.inl rfl))))

theorem mem_klein_iff (w : Perm (Fin 7)) :
    w ∈ kleinGroup ↔ w = 1 ∨ w = S7.x ∨ w = S7.y ∨ w = S7.x * S7.y := Iff.rfl

theorem x_ne_one : S7.x ≠ 1 := by decide
theorem y_ne_one : S7.y ≠ 1 := by decide
theorem xy_ne_one : S7.x * S7.y ≠ 1 := by decide

theorem conj_pow' (g x : Perm (Fin 7)) (n : ℕ) : (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
  induction n with
  | zero => group
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

theorem mem_conj_V_iff (c v : Perm (Fin 7)) :
    v ∈ S7.V.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * v * c ∈ S7.V := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    have : c⁻¹ * (MulAut.conj c).toMonoidHom w * c = w := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]; exact hw
  · intro h
    refine ⟨c⁻¹ * v * c, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem elem_two_cent_mem_V {n : Perm (Fin 7)} (hn : n * S7.a = S7.a * n)
    (hs : Perm.sign n = 1) (hk : ∃ k : ℕ, n ^ 2 ^ k = 1) : n ∈ S7.V := by
  obtain ⟨k, hk'⟩ := hk
  have h6 : n ^ 6 = 1 := three_cent_pow_six n hs hn
  have hsq : n * n = 1 := by
    rcases k with _ | j
    · simp at hk'
      rw [hk']; simp
    · have hm : (n ^ 2) ^ 3 = 1 := by rw [← pow_mul]; simpa using h6
      have hm2 : (n ^ 2) ^ 2 ^ j = 1 := by
        rw [← pow_mul, ← pow_succ']; exact hk'
      have hgcd := pow_gcd_eq_one.2 ⟨hm, hm2⟩
      have hcop : Nat.gcd 3 (2 ^ j) = 1 :=
        Nat.Coprime.pow_right j (by norm_num : Nat.Coprime 3 2)
      rw [hcop, pow_one] at hgcd
      rw [← pow_two]
      exact hgcd
  rcases three_cent_involution_mem n hs hn hsq with h | h | h | h <;> rw [h]
  · exact S7.V.one_mem
  · exact S7.x_mem_V
  · exact S7.y_mem_V
  · exact S7.V.mul_mem S7.x_mem_V S7.y_mem_V

theorem three_cycle_klein {π : Perm (Fin 7)} (hπ : π.cycleType = {3}) :
    ∃ V : Subgroup (Perm (Fin 7)), V ≤ alternatingGroup (Fin 7) ∧
      V ≤ Subgroup.centralizer ({π} : Set (Perm (Fin 7))) ∧ IsPGroup 2 ↥V ∧
      (∀ c ∈ Subgroup.centralizer ({π} : Set (Perm (Fin 7))), ∀ v ∈ V, c * v * c⁻¹ ∈ V) ∧
      (∀ n ∈ Subgroup.centralizer ({π} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7),
        ∀ k : ℕ, n ^ 2 ^ k = 1 → n ∈ V) ∧
      (∀ τ : Perm (Fin 7), τ * π = π * τ → τ ^ 3 = 1 → τ ≠ 1 → τ ≠ π → τ ≠ π ^ 2 →
        ∀ v ∈ V, τ * v * τ⁻¹ = v → v = 1) := by
  obtain ⟨c, hc⟩ := conj_of_cycleType_three hπ
  subst hc
  have comm_iff : ∀ g : Perm (Fin 7),
      g * (c * S7.a * c⁻¹) = (c * S7.a * c⁻¹) * g ↔ (c⁻¹ * g * c) * S7.a = S7.a * (c⁻¹ * g * c) := by
    intro g
    constructor
    · intro h
      calc (c⁻¹ * g * c) * S7.a = c⁻¹ * (g * (c * S7.a * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * S7.a * c⁻¹) * g) * c := by rw [h]
        _ = S7.a * (c⁻¹ * g * c) := by group
    · intro h
      calc g * (c * S7.a * c⁻¹) = c * ((c⁻¹ * g * c) * S7.a) * c⁻¹ := by group
        _ = c * (S7.a * (c⁻¹ * g * c)) * c⁻¹ := by rw [h]
        _ = (c * S7.a * c⁻¹) * g := by group
  refine ⟨S7.V.map (MulAut.conj c).toMonoidHom, S7.map_conj_le_Alt7 S7.V_le_Alt7 c, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [mem_conj_V_iff] at hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hw := Subgroup.mem_centralizer_singleton_iff.1 (S7.V_le_centralizer hv)
    have hv' : v = c * (c⁻¹ * v * c) * c⁻¹ := by group
    rw [hv']
    calc c * (c⁻¹ * v * c) * c⁻¹ * (c * S7.a * c⁻¹)
        = c * ((c⁻¹ * v * c) * S7.a) * c⁻¹ := by group
      _ = c * (S7.a * (c⁻¹ * v * c)) * c⁻¹ := by rw [hw]
      _ = (c * S7.a * c⁻¹) * (c * (c⁻¹ * v * c) * c⁻¹) := by group
  · exact S7.isPGroup_map_conj S7.isPGroup_V c
  · intro c' hc' v hv
    rw [Subgroup.mem_centralizer_singleton_iff] at hc'
    have hu : (c⁻¹ * c' * c) * S7.a = S7.a * (c⁻¹ * c' * c) := (comm_iff c').1 hc'
    have hN := (Subgroup.mem_normalizer_iff.1 (S7.mem_normalizer_V_of_comm hu) (c⁻¹ * v * c)).1
      (by rw [mem_conj_V_iff] at hv; exact hv)
    rw [mem_conj_V_iff]
    have e : c⁻¹ * (c' * v * c'⁻¹) * c = (c⁻¹ * c' * c) * (c⁻¹ * v * c) * (c⁻¹ * c' * c)⁻¹ := by
      group
    rw [e]
    exact hN
  · intro n hnCA k hk
    have hnC := (Subgroup.mem_inf.1 hnCA).1
    have hnA := (Subgroup.mem_inf.1 hnCA).2
    rw [mem_conj_V_iff]
    have hconjpow : (c⁻¹ * n * c) ^ 2 ^ k = 1 := by
      rw [conj_pow', hk]; simp
    refine elem_two_cent_mem_V ?_ ?_ ⟨k, hconjpow⟩
    · exact (comm_iff n).1 (Subgroup.mem_centralizer_singleton_iff.1 hnC)
    · have hsv : Perm.sign n = 1 := (Equiv.Perm.mem_alternatingGroup).1 hnA
      rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hsv]; simp
  · intro τ hτ h3 h1 hπ1 hπ2 v hv hfix
    rw [mem_conj_V_iff] at hv
    have hτ' : (c⁻¹ * τ * c) * S7.a = S7.a * (c⁻¹ * τ * c) := (comm_iff τ).1 hτ
    have h3' : (c⁻¹ * τ * c) ^ 3 = 1 := by
      rw [conj_pow', h3]; group
    have h1' : c⁻¹ * τ * c ≠ 1 := by
      intro h; apply h1
      have : τ = c * (c⁻¹ * τ * c) * c⁻¹ := by group
      rw [this, h]; group
    have ha' : c⁻¹ * τ * c ≠ S7.a := by
      intro h; apply hπ1
      have : τ = c * (c⁻¹ * τ * c) * c⁻¹ := by group
      rw [this, h]
    have ha2' : c⁻¹ * τ * c ≠ S7.a ^ 2 := by
      intro h; apply hπ2
      have : τ = c * (c⁻¹ * τ * c) * c⁻¹ := by group
      rw [this, h, pow_two, pow_two]; group
    have hfix' : (c⁻¹ * τ * c) * (c⁻¹ * v * c) * (c⁻¹ * τ * c)⁻¹ = c⁻¹ * v * c := by
      have : (c⁻¹ * τ * c) * (c⁻¹ * v * c) * (c⁻¹ * τ * c)⁻¹ = c⁻¹ * (τ * v * τ⁻¹) * c := by group
      rw [this, hfix]
    have hw : c⁻¹ * v * c = 1 := by
      rcases (mem_klein_iff _).1 (V_le_kleinGroup hv) with h | h | h | h
      · exact h
      · have hf : (c⁻¹ * τ * c) * S7.x * (c⁻¹ * τ * c)⁻¹ = S7.x := by rw [← h]; exact hfix'
        exact absurd (three_fpf_check _ hτ' h3' h1' ha' ha2' S7.x (by simp) hf) x_ne_one
      · have hf : (c⁻¹ * τ * c) * S7.y * (c⁻¹ * τ * c)⁻¹ = S7.y := by rw [← h]; exact hfix'
        exact absurd (three_fpf_check _ hτ' h3' h1' ha' ha2' S7.y (by simp) hf) y_ne_one
      · have hf : (c⁻¹ * τ * c) * (S7.x * S7.y) * (c⁻¹ * τ * c)⁻¹ = S7.x * S7.y := by
          rw [← h]; exact hfix'
        exact absurd (three_fpf_check _ hτ' h3' h1' ha' ha2' (S7.x * S7.y) (by simp) hf) xy_ne_one
    have : v = c * (c⁻¹ * v * c) * c⁻¹ := by group
    rw [this, hw]; group

theorem double_cent_odd {π : Perm (Fin 7)} (hπ : π.cycleType = {3, 3}) :
    Odd (Nat.card ↥(Subgroup.centralizer ({π} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7))) := by
  obtain ⟨c, hc⟩ := conj_of_cycleType_double hπ
  subst hc
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
  have hg2 : (g : Perm (Fin 7)) * g = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    have h' := congrArg Subtype.val h
    simpa [pow_two] using h'
  have hg1 : (g : Perm (Fin 7)) ≠ 1 := by
    intro h
    have : g = 1 := Subtype.ext h
    rw [this, orderOf_one] at hg
    exact absurd hg (by norm_num)
  have hcomm := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).1
  have hsgn := (Equiv.Perm.mem_alternatingGroup).1 (Subgroup.mem_inf.1 g.2).2
  have hconj : (c⁻¹ * (g : Perm (Fin 7)) * c) * dbl = dbl * (c⁻¹ * (g : Perm (Fin 7)) * c) := by
    calc (c⁻¹ * (g : Perm (Fin 7)) * c) * dbl = c⁻¹ * ((g : Perm (Fin 7)) * (c * dbl * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * dbl * c⁻¹) * (g : Perm (Fin 7))) * c := by rw [hcomm]
      _ = dbl * (c⁻¹ * (g : Perm (Fin 7)) * c) := by group
  have hsq : (c⁻¹ * (g : Perm (Fin 7)) * c) * (c⁻¹ * (g : Perm (Fin 7)) * c) = 1 := by
    calc (c⁻¹ * (g : Perm (Fin 7)) * c) * (c⁻¹ * (g : Perm (Fin 7)) * c)
        = c⁻¹ * ((g : Perm (Fin 7)) * (g : Perm (Fin 7))) * c := by group
      _ = 1 := by rw [hg2]; group
  have hs' : Perm.sign (c⁻¹ * (g : Perm (Fin 7)) * c) = 1 := by
    rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hsgn]; simp
  have := dbl_no_involution _ hs' hconj hsq
  apply hg1
  have hc' : (g : Perm (Fin 7)) = c * (c⁻¹ * (g : Perm (Fin 7)) * c) * c⁻¹ := by group
  rw [hc', this]; group

set_option maxRecDepth 100000 in
theorem centralizer_gens_trivial :
    ∀ c : Perm (Fin 7), c * S7.x = S7.x * c → c * S7.y = S7.y * c →
      c * S7.u = S7.u * c → c * S7.w = S7.w * c → c = 1 :=
  Sec12a3K.centralizer_gens_trivial_K

theorem eq_one_of_centralizes_alt7 {c : Perm (Fin 7)}
    (h : ∀ σ ∈ alternatingGroup (Fin 7), c * σ = σ * c) : c = 1 := by
  apply centralizer_gens_trivial c
  · exact h _ (S7.V_le_Alt7 S7.x_mem_V)
  · exact h _ (S7.V_le_Alt7 S7.y_mem_V)
  · exact h _ (S7.V'_le_Alt7 S7.u_mem_V')
  · exact h _ (S7.V'_le_Alt7 S7.w_mem_V')

section Block

variable {G : Type} [Group G] [Finite G]

abbrev JbarQ (J : Subgroup G) : Type _ := ↥J ⧸ CFSG.pCore 2 ↥J

noncomputable def psiOf (J : Subgroup G)
    (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃* ↥(alternatingGroup (Fin 7))) :
    ↥J →* Perm (Fin 7) :=
  (Subgroup.subtype (alternatingGroup (Fin 7))).comp
    (ι.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (JbarQ J))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥J))))

theorem psiOf_mem_alt (J : Subgroup G) (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃*
    ↥(alternatingGroup (Fin 7))) (x : ↥J) : psiOf J ι x ∈ alternatingGroup (Fin 7) :=
  (ι _).2

theorem psiOf_surj (J : Subgroup G) (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃*
    ↥(alternatingGroup (Fin 7))) :
    ∀ σ ∈ alternatingGroup (Fin 7), ∃ x : ↥J, psiOf J ι x = σ := by
  intro σ hσ
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (ι.symm ⟨σ, hσ⟩)
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective y
  refine ⟨x, ?_⟩
  have h1 : psiOf J ι x = ((ι ((QuotientGroup.mk (QuotientGroup.mk x :
      JbarQ J) : JbarQ J ⧸ Subgroup.center (JbarQ J))) : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) := rfl
  rw [h1, hx, hy]
  simp

theorem two_elem_center_eq_one (J : Subgroup G) (hX : IsHatSeven (JbarQ J)) (x : ↥J) (k : ℕ)
    (hk : (x : G) ^ 2 ^ k = 1) (hz : (QuotientGroup.mk x : JbarQ J) ∈ Subgroup.center (JbarQ J)) :
    x ∈ CFSG.pCore 2 ↥J := by
  have hz3 : Nat.card (Subgroup.center (JbarQ J)) = 3 := hX.2.1
  have hzo : orderOf (QuotientGroup.mk x : JbarQ J) ∣ 3 := by
    have h := orderOf_dvd_natCard (⟨(QuotientGroup.mk x : JbarQ J), hz⟩ : Subgroup.center (JbarQ J))
    rw [hz3] at h
    rwa [Subgroup.orderOf_mk] at h
  have hzk : (QuotientGroup.mk x : JbarQ J) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : x ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this]; rfl
  have hk2 : orderOf (QuotientGroup.mk x : JbarQ J) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
  have hgcd : orderOf (QuotientGroup.mk x : JbarQ J) ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd hzo hk2
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)),
    Nat.dvd_one, orderOf_eq_one_iff] at hgcd
  exact QuotientGroup.eq_one_iff x |>.1 hgcd

def ConjsBy (J : Subgroup G) (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃*
    ↥(alternatingGroup (Fin 7))) (g : G) (π : Perm (Fin 7)) : Prop :=
  ∀ x y : ↥J, (y : G) = g * x * g⁻¹ → psiOf J ι y = π * psiOf J ι x * π⁻¹

theorem conjsBy_pow (J : Subgroup G) (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃*
    ↥(alternatingGroup (Fin 7))) (e : G) (πe : Perm (Fin 7))
    (hne : ∀ x ∈ J, e * x * e⁻¹ ∈ J) (hE : ConjsBy J ι e πe) (n : ℕ) (x : ↥J) :
    ∃ y : ↥J, (y : G) = e ^ n * (x : G) * (e ^ n)⁻¹ ∧
      psiOf J ι y = πe ^ n * psiOf J ι x * (πe ^ n)⁻¹ := by
  induction n with
  | zero => exact ⟨x, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy1, hy2⟩ := ih
    refine ⟨⟨e * (y : G) * e⁻¹, hne _ y.2⟩, ?_, ?_⟩
    · show e * (y : G) * e⁻¹ = _
      rw [hy1]; group
    · rw [hE y ⟨e * (y : G) * e⁻¹, hne _ y.2⟩ rfl, hy2]
      rw [pow_succ]; group

theorem perm_comm_of_conjsBy (J : Subgroup G) (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃*
    ↥(alternatingGroup (Fin 7))) (a e : G) (hae : a * e = e * a)
    (hna : ∀ x ∈ J, a * x * a⁻¹ ∈ J) (hne : ∀ x ∈ J, e * x * e⁻¹ ∈ J)
    (πa πe : Perm (Fin 7)) (hA : ConjsBy J ι a πa) (hE : ConjsBy J ι e πe) :
    πe * πa = πa * πe := by
  have key : ∀ σ ∈ alternatingGroup (Fin 7),
      (πa * πe)⁻¹ * (πe * πa) * σ = σ * ((πa * πe)⁻¹ * (πe * πa)) := by
    intro σ hσ
    obtain ⟨x, rfl⟩ := psiOf_surj J ι σ hσ
    have h1 : psiOf J ι ⟨a * (x : G) * a⁻¹, hna _ x.2⟩ = πa * psiOf J ι x * πa⁻¹ :=
      hA x _ rfl
    have h2 : psiOf J ι ⟨e * (x : G) * e⁻¹, hne _ x.2⟩ = πe * psiOf J ι x * πe⁻¹ :=
      hE x _ rfl
    have h3 : psiOf J ι ⟨e * (a * (x : G) * a⁻¹) * e⁻¹, hne _ (hna _ x.2)⟩ =
        πe * psiOf J ι ⟨a * (x : G) * a⁻¹, hna _ x.2⟩ * πe⁻¹ :=
      hE _ _ rfl
    have h4 : psiOf J ι ⟨a * (e * (x : G) * e⁻¹) * a⁻¹, hna _ (hne _ x.2)⟩ =
        πa * psiOf J ι ⟨e * (x : G) * e⁻¹, hne _ x.2⟩ * πa⁻¹ :=
      hA _ _ rfl
    have hwu : (⟨e * (a * (x : G) * a⁻¹) * e⁻¹, hne _ (hna _ x.2)⟩ : ↥J) =
        ⟨a * (e * (x : G) * e⁻¹) * a⁻¹, hna _ (hne _ x.2)⟩ := by
      apply Subtype.ext
      show e * (a * (x : G) * a⁻¹) * e⁻¹ = a * (e * (x : G) * e⁻¹) * a⁻¹
      calc e * (a * (x : G) * a⁻¹) * e⁻¹ = (e * a) * (x : G) * (e * a)⁻¹ := by group
        _ = (a * e) * (x : G) * (a * e)⁻¹ := by rw [hae.symm]
        _ = a * (e * (x : G) * e⁻¹) * a⁻¹ := by group
    have hpsi := congrArg (psiOf J ι) hwu
    rw [h3, h4, h1, h2] at hpsi
    have e1 : (πe * πa) * psiOf J ι x * (πe * πa)⁻¹ =
        (πa * πe) * psiOf J ι x * (πa * πe)⁻¹ := by
      calc (πe * πa) * psiOf J ι x * (πe * πa)⁻¹
          = πe * (πa * psiOf J ι x * πa⁻¹) * πe⁻¹ := by group
        _ = πa * (πe * psiOf J ι x * πe⁻¹) * πa⁻¹ := hpsi
        _ = (πa * πe) * psiOf J ι x * (πa * πe)⁻¹ := by group
    calc (πa * πe)⁻¹ * (πe * πa) * psiOf J ι x
        = (πa * πe)⁻¹ * ((πe * πa) * psiOf J ι x * (πe * πa)⁻¹) * (πe * πa) := by group
      _ = (πa * πe)⁻¹ * ((πa * πe) * psiOf J ι x * (πa * πe)⁻¹) * (πe * πa) := by rw [e1]
      _ = psiOf J ι x * ((πa * πe)⁻¹ * (πe * πa)) := by group
  have hc := eq_one_of_centralizes_alt7 (c := (πa * πe)⁻¹ * (πe * πa)) key
  rw [inv_mul_eq_one] at hc
  exact hc.symm

theorem perm_pow_three_eq_one (J : Subgroup G) (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃*
    ↥(alternatingGroup (Fin 7))) (e : G) (πe : Perm (Fin 7))
    (hne : ∀ x ∈ J, e * x * e⁻¹ ∈ J) (hE : ConjsBy J ι e πe) (he3 : e ^ 3 = 1) :
    πe ^ 3 = 1 := by
  have hfix : ∀ σ ∈ alternatingGroup (Fin 7), πe ^ 3 * σ * (πe ^ 3)⁻¹ = σ := by
    intro σ hσ
    obtain ⟨x, rfl⟩ := psiOf_surj J ι σ hσ
    obtain ⟨y, hy1, hy2⟩ := conjsBy_pow J ι e πe hne hE 3 x
    have hyx : y = x := Subtype.ext (by rw [hy1, he3]; group)
    rw [← hy2, hyx]
  have hc := eq_one_of_centralizes_alt7 (c := πe ^ 3) (fun σ hσ => by
    calc πe ^ 3 * σ = (πe ^ 3 * σ * (πe ^ 3)⁻¹) * πe ^ 3 := by group
      _ = σ * πe ^ 3 := by rw [hfix σ hσ])
  exact hc

theorem two_elem_of_fpf (J : Subgroup G) (hX : IsHatSeven (JbarQ J))
    (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    (a e : G) (hae : a * e = e * a) (hna : ∀ x ∈ J, a * x * a⁻¹ ∈ J)
    (hne : ∀ x ∈ J, e * x * e⁻¹ ∈ J) (πa πe : Perm (Fin 7))
    (hA : ConjsBy J ι a πa) (hE : ConjsBy J ι e πe) (he3 : e ^ 3 = 1)
    (hπa : πa.cycleType = {3}) (hπe1 : πe ≠ 1) (hπea : πe ≠ πa) (hπea2 : πe ≠ πa ^ 2) :
    ∀ x : ↥J, (x : G) * a = a * (x : G) → (x : G) * e = e * (x : G) →
      (∃ k : ℕ, (x : G) ^ 2 ^ k = 1) → x ∈ CFSG.pCore 2 ↥J := by
  have hcomm : πe * πa = πa * πe := perm_comm_of_conjsBy J ι a e hae hna hne πa πe hA hE
  have hcube : πe ^ 3 = 1 := perm_pow_three_eq_one J ι e πe hne hE he3
  obtain ⟨V, -, -, -, -, hV5, hV6⟩ := three_cycle_klein hπa
  intro x hxa hxe ⟨k, hk⟩
  have hcomm_xa : psiOf J ι x * πa = πa * psiOf J ι x := by
    have h := hA x x (by
      show (x : G) = a * (x : G) * a⁻¹
      rw [← hxa]; group)
    calc psiOf J ι x * πa = πa * psiOf J ι x * πa⁻¹ * πa := by rw [← h]
      _ = πa * psiOf J ι x := by group
  have hfix_e : πe * psiOf J ι x * πe⁻¹ = psiOf J ι x := by
    have h := hE x x (by
      show (x : G) = e * (x : G) * e⁻¹
      rw [← hxe]; group)
    rw [← h]
  have hpow : (psiOf J ι x) ^ 2 ^ k = 1 := by
    have hxk : x ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [← map_pow, hxk, map_one]
  have hC : psiOf J ι x ∈ Subgroup.centralizer ({πa} : Set (Perm (Fin 7))) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcomm_xa
  have hmemV : psiOf J ι x ∈ V := hV5 _ ⟨hC, psiOf_mem_alt J ι x⟩ k hpow
  have hpsi1 : psiOf J ι x = 1 := hV6 πe hcomm hcube hπe1 hπea hπea2 _ hmemV hfix_e
  have hz : (QuotientGroup.mk x : JbarQ J) ∈ Subgroup.center (JbarQ J) := by
    have h1 : ι (QuotientGroup.mk (QuotientGroup.mk x : JbarQ J)) = 1 := Subtype.ext hpsi1
    have h2 := ι.map_eq_one_iff.1 h1
    exact (QuotientGroup.eq_one_iff _).1 h2
  exact two_elem_center_eq_one J hX x k hk hz

theorem isTwoPrimeComp_self_of_hatSeven (J : Subgroup G) (hX : IsHatSeven (JbarQ J))
    (hp : ⁅J, J⁆ = J) : IsTwoPrimeComp J J := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨ι⟩ := hX.2.2
  have hq : CFSG.Open.IsQuasisimple (JbarQ J) := ⟨hX.1, ι.isSimpleGroup⟩
  refine ⟨le_rfl, IsSubnormal.refl J, hp, ?_⟩
  have htop : (J.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) = ⊤ := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [htop]
  exact ⟨le_top, IsSubnormal.refl _,
    CFSG.ComponentClassification.Components.quasisimple_of_equiv Subgroup.topEquiv hq⟩

theorem isSubnormal_of_centralized_comp {E M : Subgroup G} {e : G}
    (hE : IsUniquenessTwoLocal 3 E M) (he : e ∈ E) (he1 : e ≠ 1)
    {J : Subgroup G} (hJM : J ≤ M) (hJsub : IsSubnormal J M) (hJp : ⁅J, J⁆ = J)
    (hX : IsHatSeven (JbarQ J)) (hJe : J ≤ Subgroup.centralizer ({e} : Set G)) :
    IsSubnormal J (Subgroup.centralizer ({e} : Set G)) := by
  have hJα : J ≤ alphaOf 3 M :=
    le_sup_of_le_right (le_iSup₂_of_le J ⟨rfl, hJM, hJsub, hJp, hX⟩ le_rfl)
  have hαM : alphaOf 3 M ≤ M := Sec12a.alphaOf_le_self (p := 3) M
  have hJα' : IsSubnormal J (alphaOf 3 M) := isSubnormal_of_le_of_le hJsub hJα hαM
  have hsub : IsSubnormal (J ⊓ Subgroup.centralizer ({e} : Set G))
      (alphaOf 3 M ⊓ Subgroup.centralizer ({e} : Set G)) :=
    Sec12a2.isSubnormal_inf hJα' _
  rw [inf_eq_left.2 hJe] at hsub
  have hTP : IsTwoPrimeComp (alphaOf 3 M ⊓ Subgroup.centralizer ({e} : Set G)) J :=
    isTwoPrimeComp_of_le (isTwoPrimeComp_self_of_hatSeven J hX hJp) (le_inf hJα hJe) hsub
  exact (hE.clause_f rfl e he he1 J hTP).2.1

theorem exists_perm_conjsBy (J : Subgroup G) (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃*
    ↥(alternatingGroup (Fin 7))) (e : G) (he : e ∈ Subgroup.normalizer (J : Set G)) :
    ∃ π : Perm (Fin 7), ConjsBy J ι e π := by
  set φ : MulAut ↥J := (Subgroup.normalizerMonoidHom J) ⟨e, he⟩ with hφ
  have hφapp : ∀ x : ↥J, ((φ x : ↥J) : G) = e * (x : G) * e⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨e, he⟩ x
  have hpc : (CFSG.pCore 2 ↥J).map φ.toMonoidHom = CFSG.pCore 2 ↥J := by
    have h := (pCore_characteristic (p := 2) (G := ↥J)).fixed φ.symm
    ext x
    rw [Subgroup.mem_map_equiv]
    have := SetLike.ext_iff.1 h x
    simpa [Subgroup.mem_comap] using this
  let Φ : JbarQ J ≃* JbarQ J := QuotientGroup.congr (CFSG.pCore 2 ↥J) (CFSG.pCore 2 ↥J) φ hpc
  have hZ : (Subgroup.center (JbarQ J)).map Φ.toMonoidHom = Subgroup.center (JbarQ J) := by
    have h := (Subgroup.centerCharacteristic (G := JbarQ J)).fixed Φ.symm
    ext x
    rw [Subgroup.mem_map_equiv]
    have := SetLike.ext_iff.1 h x
    simpa [Subgroup.mem_comap] using this
  let Zc : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃* (JbarQ J ⧸ Subgroup.center (JbarQ J)) :=
    QuotientGroup.congr (Subgroup.center (JbarQ J)) (Subgroup.center (JbarQ J)) Φ hZ
  let f : ↥(alternatingGroup (Fin 7)) ≃* ↥(alternatingGroup (Fin 7)) :=
    ι.symm.trans (Zc.trans ι)
  have hf : ∀ z : JbarQ J ⧸ Subgroup.center (JbarQ J), f (ι z) = ι (Zc z) := by
    intro z
    simp [f]
  obtain ⟨π₀, hπ₀⟩ : ∃ π₀ : Perm (Fin 7), S7.conjEquiv π₀ = f :=
    ⟨S7.conjEquiv.symm f, S7.conjEquiv.apply_symm_apply f⟩
  refine ⟨π₀, ?_⟩
  have hspec : ∀ σ : ↥(alternatingGroup (Fin 7)),
      ((f σ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) = π₀ * (σ : Perm (Fin 7)) * π₀⁻¹ := by
    intro σ
    have h2 := congrArg (fun ψ : MulAut ↥(alternatingGroup (Fin 7)) =>
      ((ψ σ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))) hπ₀
    simpa [S7.conjEquiv, MulAut.conjNormal_apply] using h2.symm
  intro x y hxy
  have hy : y = φ x := Subtype.ext (by rw [hφapp]; exact hxy)
  have hmk : (QuotientGroup.mk y : JbarQ J) = Φ (QuotientGroup.mk x) := by
    rw [hy]
    exact (QuotientGroup.congr_mk _ _ φ hpc x).symm
  have hZmk : (QuotientGroup.mk (QuotientGroup.mk y : JbarQ J) :
      JbarQ J ⧸ Subgroup.center (JbarQ J)) =
        Zc (QuotientGroup.mk (QuotientGroup.mk x : JbarQ J)) := by
    rw [hmk]
    exact (QuotientGroup.congr_mk _ _ Φ hZ _).symm
  have key : psiOf J ι y = ((f (ι (QuotientGroup.mk (QuotientGroup.mk x : JbarQ J))) :
      ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) := by
    rw [hf]
    show ((ι (QuotientGroup.mk (QuotientGroup.mk y : JbarQ J))) : Perm (Fin 7)) = _
    rw [hZmk]
  rw [key, hspec]
  rfl

section Objects

variable {G : Type} [Group G] [Finite G]

@[expose] def CompSet (M J : Subgroup G) : Prop :=
  J ≤ M ∧ IsSubnormal J M ∧ ⁅J, J⁆ = J ∧ IsHatSeven (JbarQ J)

@[expose] def ThreeCycComp (a : G) (J : Subgroup G) : Prop :=
  (∀ x ∈ J, a * x * a⁻¹ ∈ J) ∧
    ∃ (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
      (π : Perm (Fin 7)), π.cycleType = {3} ∧ ConjsBy J ι a π

@[expose] def Vpc (a : G) (J : Subgroup G) : Subgroup G :=
  CFSG.Open.pCoreOf 2 (J ⊓ Cg a)

@[expose] def Wpc (e a : G) (J : Subgroup G) : Subgroup G :=
  ⨆ k : Fin 3, CFSG.Open.pCoreOf 2 (GLBConj (e ^ (k : ℕ)) J ⊓ Cg a)

@[expose] def BlockDecomp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) (B M E A : Subgroup G) (a : G)
    (h : Cex121 G m 3 B M E A a), ¬ Tof 3 M a ≤ CFSG.Open.pCoreOf 2 M →
      ∀ e ∈ E ⊓ A, e ≠ 1 →
        Tof 3 M a ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (Cg e) ⊔
          ⨆ (J : Subgroup G) (_ : CompSet M J ∧ ThreeCycComp a J), Wpc e a J ⊓ Cg e

@[expose] def PowPiece : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M J : Subgroup G) (a e : G), CompSet M J →
    a * e = e * a → e ∈ Subgroup.normalizer (J : Set G) →
    ∀ (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
      (πa πe : Perm (Fin 7)), πa.cycleType = {3} → ConjsBy J ι a πa → ConjsBy J ι e πe →
      (πe = πa ∨ πe = πa ^ 2) → Vpc a J ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (J ⊓ Cg e)

@[expose] def DiagPiece : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) (B M E A : Subgroup G) (a : G)
    (h : Cex121 G m 3 B M E A a) (e : G), e ∈ E ⊓ A → e ≠ 1 → ∀ J : Subgroup G,
      CompSet M J → ThreeCycComp a J →
      (GLBConj e J ≠ J ∨ (e ∈ Subgroup.normalizer (J : Set G) ∧
        ∃ (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
          (πe : Perm (Fin 7)), ConjsBy J ι e πe ∧ πe = 1 ∧ ¬ J ≤ Cg e)) →
      ∃ Δ : Subgroup G, Δ ≤ alphaOf 3 M ∧ IsTwoPrimeComp (Cg e) Δ ∧
        Wpc e a J ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (Cg e) ⊔ CFSG.Open.pCoreOf 2 (Δ ⊓ Cg a)

end Objects

end Block

section SylowCore

theorem sylow_core {W : Type} [Group W] [Finite W] {K L : Subgroup W} [hK : K.Normal]
    (hLK : L ≤ K) (hL2 : IsPGroup 2 L)
    (hcomm : ∀ k ∈ K, ∀ y : W, k * y * k⁻¹ * y⁻¹ ∈ L)
    (hquot : ∀ w : W, ∃ n : ℕ, w ^ 2 ^ n ∈ K) :
    ∃ P : Subgroup W, IsPGroup 2 P ∧ L ≤ P ∧ (∀ w : W, ∀ y ∈ P, w * y * w⁻¹ ∈ P) ∧
      ∀ x : W, (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsPGroup 2 (W ⧸ K) := by
    intro g
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨n, hn⟩ := hquot w
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hn
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hq
  have hKidx : K.index = 2 ^ m := by
    rw [Subgroup.index]
    exact hm
  obtain ⟨S, hLS⟩ := hL2.exists_le_sylow
  have hodd : ¬ 2 ∣ (S : Subgroup W).index := S.not_dvd_index
  have hTtop : (S : Subgroup W) ⊔ K = ⊤ := by
    have h1 : ((S : Subgroup W) ⊔ K).index ∣ (S : Subgroup W).index :=
      Subgroup.index_dvd_of_le le_sup_left
    have h2 : ((S : Subgroup W) ⊔ K).index ∣ K.index :=
      Subgroup.index_dvd_of_le le_sup_right
    rw [hKidx] at h2
    have hcop : Nat.Coprime 2 ((S : Subgroup W) ⊔ K).index :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (fun h => hodd (h.trans h1))
    have h3 : ((S : Subgroup W) ⊔ K).index = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right m hcop.symm) h2
    exact Subgroup.index_eq_one.1 h3
  have hdecomp : ∀ w : W, ∃ s ∈ (S : Subgroup W), ∃ k ∈ K, w = s * k := by
    intro w
    have hw : w ∈ ((S : Subgroup W) ⊔ K : Subgroup W) := by
      rw [hTtop]; exact Subgroup.mem_top w
    have hw' : w ∈ ((((S : Subgroup W) ⊔ K : Subgroup W)) : Set W) := hw
    rw [Subgroup.mul_normal] at hw'
    obtain ⟨s, hs, k, hk, hsk⟩ := hw'
    exact ⟨s, hs, k, hk, hsk.symm⟩
  have hSnorm : ∀ w : W, ∀ y ∈ (S : Subgroup W), w * y * w⁻¹ ∈ (S : Subgroup W) := by
    intro w y hy
    obtain ⟨s, hs, k, hk, rfl⟩ := hdecomp w
    have hcS : k * y * k⁻¹ * y⁻¹ ∈ (S : Subgroup W) := hLS (hcomm k hk y)
    have h2 : (s * k) * y * (s * k)⁻¹ = s * ((k * y * k⁻¹ * y⁻¹) * y) * s⁻¹ := by group
    rw [h2]
    exact (S : Subgroup W).mul_mem ((S : Subgroup W).mul_mem hs
      ((S : Subgroup W).mul_mem hcS hy)) ((S : Subgroup W).inv_mem hs)
  haveI hSN : (S : Subgroup W).Normal := ⟨fun n hn g => hSnorm g n hn⟩
  refine ⟨(S : Subgroup W), S.isPGroup', hLS, fun w y hy => hSnorm w y hy, ?_⟩
  intro x ⟨n, hn⟩
  have hzp : IsPGroup 2 (Subgroup.zpowers x) := by
    intro g
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨n, Subtype.ext ?_⟩
    have hj' : (x ^ j : W) = (g : W) := hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hj']
    rw [← zpow_natCast (x ^ j) (2 ^ n), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn,
      one_zpow]
  obtain ⟨Q, hxQ⟩ := hzp.exists_le_sylow
  have hSQ : (S : Subgroup W) ≤ (Q : Subgroup W) :=
    IsPGroup.le_sylow_of_normal S.isPGroup' Q
  have hQS : (Q : Subgroup W) = (S : Subgroup W) := S.is_maximal' Q.isPGroup' hSQ
  rw [← hQS]
  exact hxQ (Subgroup.mem_zpowers x)

end SylowCore

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem mem_GLBConj_iff' (g : G) (H : Subgroup G) (x : G) :
    x ∈ GLBConj g H ↔ g * x * g⁻¹ ∈ H := by
  unfold GLBConj
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem normalizer_of_glbConj_eq (J : Subgroup G) (e : G) (hfix : GLBConj e J = J) :
    e ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have h := mem_GLBConj_iff' e J g
  rw [hfix] at h
  exact h

theorem glbConj_pow_eq_self (J : Subgroup G) (e : G) (hfix : GLBConj e J = J) (k : ℕ) :
    GLBConj (e ^ k) J = J := by
  have he := normalizer_of_glbConj_eq J e hfix
  have hk : e ^ k ∈ Subgroup.normalizer (J : Set G) := (Subgroup.normalizer (J : Set G)).pow_mem he k
  ext x
  rw [mem_GLBConj_iff']
  exact (Subgroup.mem_normalizer_iff.1 hk x).symm

theorem wpc_eq_vpc (J : Subgroup G) (e a : G) (hfix : GLBConj e J = J) :
    Wpc e a J = Vpc a J := by
  unfold Wpc Vpc
  simp [glbConj_pow_eq_self J e hfix]

theorem compSet_le_alpha {M J : Subgroup G} (hJ : CompSet M J) : J ≤ alphaOf 3 M :=
  le_sup_of_le_right (le_iSup₂_of_le J ⟨rfl, hJ.1, hJ.2.1, hJ.2.2.1, hJ.2.2.2⟩ le_rfl)

theorem exists_pow_eq_one_of_pCoreOf (H : Subgroup G) {g : G} (hg : g ∈ CFSG.Open.pCoreOf 2 H) :
    ∃ k : ℕ, g ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨g, hg⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem two_part_le_O2C {E M : Subgroup G} {e : G} (hE : IsUniquenessTwoLocal 3 E M)
    (he : e ∈ E) (he1 : e ≠ 1) {Y : Subgroup G}
    (hY : IsSubnormal Y (alphaOf 3 M ⊓ Subgroup.centralizer ({e} : Set G)))
    (hY2 : IsPGroup 2 ↥Y) : Y ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Y ≤ CFSG.Open.pCoreOf 2 (alphaOf 3 M ⊓ Subgroup.centralizer ({e} : Set G)) :=
    Sec12a2.le_pCoreOf_of_isSubnormal hY hY2
  exact h1.trans (hE.clause_b e he he1)

theorem isSubnormal_pCoreOf_self (Y : Subgroup G) : IsSubnormal (CFSG.Open.pCoreOf 2 Y) Y :=
  Sec12a2.isSubnormal_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)).2
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))

theorem piece_mem_PeT {M J' : Subgroup G} {a e : G} (hJα : J' ≤ alphaOf 3 M)
    (hJsub : IsSubnormal J' (Cg e)) :
    CFSG.Open.pCoreOf 2 (J' ⊓ Cg a) ≤
      ⨆ (J'' : Subgroup G) (_ : J'' ≤ alphaOf 3 M ∧ IsSubnormal J'' (Cg e)),
        CFSG.Open.pCoreOf 2 (J'' ⊓ Cg a) :=
  le_iSup₂_of_le (f := fun J'' (_ : J'' ≤ alphaOf 3 M ∧ IsSubnormal J'' (Cg e)) =>
    CFSG.Open.pCoreOf 2 (J'' ⊓ Cg a)) J' ⟨hJα, hJsub⟩ le_rfl

theorem delta_piece_le {M Δ : Subgroup G} {a e : G} {X : Subgroup G}
    (hΔα : Δ ≤ alphaOf 3 M) (hΔT : IsTwoPrimeComp (Cg e) Δ)
    (hX : X ≤ CFSG.Open.pCoreOf 2 (Cg e) ⊔ CFSG.Open.pCoreOf 2 (Δ ⊓ Cg a)) :
    X ≤ CFSG.Open.pCoreOf 2 (Cg e) ⊔
      ⨆ (J'' : Subgroup G) (_ : J'' ≤ alphaOf 3 M ∧ IsSubnormal J'' (Cg e)),
        CFSG.Open.pCoreOf 2 (J'' ⊓ Cg a) :=
  hX.trans (sup_le_sup_left (piece_mem_PeT hΔα hΔT.2.1) _)

theorem piece_power {E M : Subgroup G} {a e : G} {J : Subgroup G}
    (hE : IsUniquenessTwoLocal 3 E M) (heE : e ∈ E) (he1 : e ≠ 1) (hJC : CompSet M J)
    (hJα' : IsSubnormal J (alphaOf 3 M))
    (h1 : Vpc a J ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (J ⊓ Cg e)) :
    Vpc a J ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (Cg e) := by
  refine h1.trans ?_
  apply two_part_le_O2C hE heE he1 (Y := CFSG.Open.pCoreOf 2 (J ⊓ Cg e))
  · exact Sec12a2.isSubnormal_trans (isSubnormal_pCoreOf_self (J ⊓ Cg e))
      (Sec12a2.isSubnormal_inf hJα' _)
  · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (J ⊓ Cg e)

theorem piece_fpf {E M : Subgroup G} {a e : G} {J : Subgroup G}
    (hE : IsUniquenessTwoLocal 3 E M) (heE : e ∈ E) (he1 : e ≠ 1) (hJC : CompSet M J)
    (hJα' : IsSubnormal J (alphaOf 3 M))
    (hfpf : ∀ x : ↥J, (x : G) * a = a * (x : G) → (x : G) * e = e * (x : G) →
      (∃ k : ℕ, (x : G) ^ 2 ^ k = 1) → x ∈ CFSG.pCore 2 ↥J) :
    Vpc a J ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (Cg e) := by
  have hVsub : Vpc a J ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 J := by
    rintro g ⟨hgV, hge⟩
    have hgJa : g ∈ J ⊓ Cg a := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hgV
    have hgJ : g ∈ J := (Subgroup.mem_inf.1 hgJa).1
    have hga : g ∈ Cg a := (Subgroup.mem_inf.1 hgJa).2
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_pCoreOf _ hgV
    have hx := hfpf ⟨g, hgJ⟩ (Subgroup.mem_centralizer_singleton_iff.1 hga)
      (Subgroup.mem_centralizer_singleton_iff.1 hge) ⟨k, hk⟩
    exact Subgroup.mem_map.2 ⟨⟨g, hgJ⟩, hx, rfl⟩
  have hY : IsSubnormal (CFSG.Open.pCoreOf 2 J ⊓ Cg e) (alphaOf 3 M ⊓ Cg e) :=
    Sec12a2.isSubnormal_inf (Sec12a2.isSubnormal_trans (isSubnormal_pCoreOf_self J) hJα') _
  have hY2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 J ⊓ Cg e) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J).to_le inf_le_left
  exact fun g hg => two_part_le_O2C hE heE he1 hY hY2 (⟨hVsub hg, hg.2⟩ : g ∈ CFSG.Open.pCoreOf 2 J ⊓ Cg e)

theorem blockLayer_of_pow_inputs (hD : BlockDecomp) (hP : PowPiece) (hΔ : DiagPiece) :
    Sec12a2.BlockLayer := by
  unfold Sec12a2.BlockLayer
  intro G _ _ m p B M E A a h hT e he he1
  obtain ⟨rfl, -⟩ := Sec12a.caseB_p3_hatSeven hT
  have hE : IsUniquenessTwoLocal 3 E M := h.pair.1.1.2
  obtain ⟨hAM, hAel, -⟩ : IsSCp 3 M A := h.pair.1.2.1.1.1
  have heE : e ∈ E := (Subgroup.mem_inf.1 he).1
  have heA : e ∈ A := (Subgroup.mem_inf.1 he).2
  have he3 : e ^ 3 = 1 := hE.elemAbelian.2 e heE
  have hae : a * e = e * a := CFSG.Open.IsElemAbelian.comm hAel h.ha.1 heA
  have hD' := hD G m B M E A a h hT e he he1
  refine hD'.trans (sup_le le_sup_left (iSup_le fun J => iSup_le fun hJ => ?_))
  obtain ⟨hJC, hJT⟩ := hJ
  have hJα : J ≤ alphaOf 3 M := compSet_le_alpha hJC
  have hJα' : IsSubnormal J (alphaOf 3 M) :=
    isSubnormal_of_le_of_le hJC.2.1 hJα (Sec12a.alphaOf_le_self (p := 3) M)
  by_cases hfix : GLBConj e J = J
  · have he_norm := normalizer_of_glbConj_eq J e hfix
    obtain ⟨ι, πa, hπa, hA⟩ := hJT.2
    have hne : ∀ x ∈ J, e * x * e⁻¹ ∈ J := fun x hx =>
      (Subgroup.mem_normalizer_iff.1 he_norm x).1 hx
    obtain ⟨πe, hEe⟩ := exists_perm_conjsBy J ι e he_norm
    rw [wpc_eq_vpc J e a hfix]
    by_cases htriv : πe = 1
    · subst htriv
      by_cases hJe : J ≤ Cg e
      · have hsub := isSubnormal_of_centralized_comp hE heE he1 hJC.1 hJC.2.1 hJC.2.2.1
          hJC.2.2.2 hJe
        exact (inf_le_left.trans (piece_mem_PeT hJα hsub)).trans le_sup_right
      · obtain ⟨Δ, hΔα, hΔT, hle⟩ := hΔ G m B M E A a h e he he1 J hJC hJT
          (Or.inr ⟨he_norm, ι, 1, hEe, rfl, hJe⟩)
        rw [wpc_eq_vpc J e a hfix] at hle
        exact delta_piece_le hΔα hΔT hle
    · by_cases hpow : πe = πa ∨ πe = πa ^ 2
      · have h1 := hP G M J a e hJC hae he_norm ι πa πe hπa hA hEe hpow
        exact (piece_power hE heE he1 hJC hJα' h1).trans le_sup_left
      · have hfpf := two_elem_of_fpf J hJC.2.2.2 ι a e hae hJT.1 hne πa πe hA hEe he3 hπa htriv
          (fun h' => hpow (Or.inl h')) (fun h' => hpow (Or.inr h'))
        exact (piece_fpf hE heE he1 hJC hJα' hfpf).trans le_sup_left
  · obtain ⟨Δ, hΔα, hΔT, hle⟩ := hΔ G m B M E A a h e he he1 J hJC hJT (Or.inl hfix)
    exact delta_piece_le hΔα hΔT hle

end Reduction

section PowProof

variable {G : Type} [Group G] [Finite G]

theorem three_cycle_pow_three {π : Perm (Fin 7)} (h : π.cycleType = {3}) : π ^ 3 = 1 := by
  have hc : π.IsThreeCycle := h
  have := hc.orderOf
  rw [← this]
  exact pow_orderOf_eq_one π

theorem comm_of_conj_eq' {σ c : Perm (Fin 7)} (h : σ = c * σ * c⁻¹) : σ * c = c * σ := by
  calc σ * c = (c * σ * c⁻¹) * c := by rw [← h]
    _ = c * σ := by group

theorem power_piece_of_perm (M J : Subgroup G) (a e : G) (hJ : CompSet M J)
    (he_norm : e ∈ Subgroup.normalizer (J : Set G))
    (ι : (JbarQ J ⧸ Subgroup.center (JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    (πa πe : Perm (Fin 7)) (hπa : πa.cycleType = {3}) (hA : ConjsBy J ι a πa)
    (hE : ConjsBy J ι e πe) (hpow : πe = πa ∨ πe = πa ^ 2) :
    Vpc a J ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (J ⊓ Cg e) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, -, -, hV3, hV4, hV5, -⟩ := three_cycle_klein hπa
  have hπa3 : πa ^ 3 = 1 := three_cycle_pow_three hπa
  have hcommH : ∀ y : ↥J, (y : G) ∈ Cg e → psiOf J ι y * πa = πa * psiOf J ι y := by
    intro y hy
    have hyc : e * (y : G) * e⁻¹ = y := by
      have h' := Subgroup.mem_centralizer_singleton_iff.1 hy
      calc e * (y : G) * e⁻¹ = (y * e) * e⁻¹ := by rw [h']
        _ = y := by group
    have h1 := hE y y hyc.symm
    rcases hpow with h | h
    · rw [h] at h1
      exact comm_of_conj_eq' h1
    · rw [h] at h1
      have hc2 : (πa ^ 2) ^ 2 = πa := by
        rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 from rfl, pow_add, hπa3, one_mul, pow_one]
      have hσ := comm_of_conj_eq' h1
      calc psiOf J ι y * πa = psiOf J ι y * (πa ^ 2) ^ 2 := by rw [hc2]
        _ = (psiOf J ι y * πa ^ 2) * πa ^ 2 := by group
        _ = (πa ^ 2 * psiOf J ι y) * πa ^ 2 := by rw [hσ]
        _ = πa ^ 2 * (psiOf J ι y * πa ^ 2) := by group
        _ = πa ^ 2 * (πa ^ 2 * psiOf J ι y) := by rw [hσ]
        _ = (πa ^ 2) ^ 2 * psiOf J ι y := by group
        _ = πa * psiOf J ι y := by rw [hc2]
  have ker_central : ∀ y : ↥J, psiOf J ι y = 1 →
      (QuotientGroup.mk y : JbarQ J) ∈ Subgroup.center (JbarQ J) := by
    intro y hy
    have h1 : ι (QuotientGroup.mk (QuotientGroup.mk y : JbarQ J)) = 1 := Subtype.ext hy
    exact (QuotientGroup.eq_one_iff _).1 (ι.map_eq_one_iff.1 h1)
  have pcore_ker : ∀ y : ↥J, y ∈ CFSG.pCore 2 ↥J → psiOf J ι y = 1 := by
    intro y hy
    have h1 : (QuotientGroup.mk y : JbarQ J) = 1 := (QuotientGroup.eq_one_iff y).2 hy
    show ((ι (QuotientGroup.mk (QuotientGroup.mk y : JbarQ J))) : Perm (Fin 7)) = 1
    rw [h1]
    simp
  let Wc : Subgroup G := ((Subgroup.comap (psiOf J ι) V).map J.subtype) ⊓ Cg e
  let Kc : Subgroup G := ((MonoidHom.ker (psiOf J ι)).map J.subtype) ⊓ Cg e
  let Lc : Subgroup G := ((CFSG.pCore 2 ↥J).map J.subtype) ⊓ Cg e
  have mapJ : ∀ (K' : Subgroup ↥J) (y : ↥J), (y : G) ∈ K'.map J.subtype ↔ y ∈ K' := by
    intro K' y
    constructor
    · intro h
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 h
      have : z = y := Subtype.ext hzy
      rw [← this]
      exact hz
    · intro h
      exact Subgroup.mem_map.2 ⟨y, h, rfl⟩
  have memW : ∀ y : ↥J, (y : G) ∈ Wc ↔ psiOf J ι y ∈ V ∧ (y : G) ∈ Cg e := by
    intro y
    rw [show Wc = ((Subgroup.comap (psiOf J ι) V).map J.subtype) ⊓ Cg e from rfl,
      Subgroup.mem_inf, mapJ, Subgroup.mem_comap]
  have memK : ∀ y : ↥J, (y : G) ∈ Kc ↔ psiOf J ι y = 1 ∧ (y : G) ∈ Cg e := by
    intro y
    rw [show Kc = ((MonoidHom.ker (psiOf J ι)).map J.subtype) ⊓ Cg e from rfl,
      Subgroup.mem_inf, mapJ, MonoidHom.mem_ker]
  have memL : ∀ y : ↥J, (y : G) ∈ Lc ↔ y ∈ CFSG.pCore 2 ↥J ∧ (y : G) ∈ Cg e := by
    intro y
    rw [show Lc = ((CFSG.pCore 2 ↥J).map J.subtype) ⊓ Cg e from rfl, Subgroup.mem_inf, mapJ]
  have hWJ : ∀ g ∈ Wc, ∃ y : ↥J, (y : G) = g := by
    intro g hg
    have h1 := (Subgroup.mem_inf.1 hg).1
    obtain ⟨z, _, hz⟩ := Subgroup.mem_map.1 h1
    exact ⟨z, hz⟩
  have hKJ : ∀ g ∈ Kc, ∃ y : ↥J, (y : G) = g := by
    intro g hg
    have h1 := (Subgroup.mem_inf.1 hg).1
    obtain ⟨z, _, hz⟩ := Subgroup.mem_map.1 h1
    exact ⟨z, hz⟩
  have hLJ : ∀ g ∈ Lc, ∃ y : ↥J, (y : G) = g := by
    intro g hg
    have h1 := (Subgroup.mem_inf.1 hg).1
    obtain ⟨z, _, hz⟩ := Subgroup.mem_map.1 h1
    exact ⟨z, hz⟩
  have conjK : ∀ g : G, g ∈ J → g ∈ Cg e → ∀ k ∈ Kc, g * k * g⁻¹ ∈ Kc := by
    intro g hgJ hgC k hk
    obtain ⟨y, rfl⟩ := hKJ k hk
    have hk' := (memK y).1 hk
    refine (memK ⟨g * (y : G) * g⁻¹, J.mul_mem (J.mul_mem hgJ y.2) (J.inv_mem hgJ)⟩).2 ⟨?_, ?_⟩
    · have : (⟨g * (y : G) * g⁻¹, J.mul_mem (J.mul_mem hgJ y.2) (J.inv_mem hgJ)⟩ : ↥J) =
          ⟨g, hgJ⟩ * y * (⟨g, hgJ⟩)⁻¹ := by
        apply Subtype.ext; simp
      rw [this, map_mul, map_mul, map_inv, hk'.1]
      group
    · exact (Cg e).mul_mem ((Cg e).mul_mem hgC hk'.2) ((Cg e).inv_mem hgC)
  have hWJmem : ∀ g ∈ Wc, g ∈ J := fun g hg => by
    obtain ⟨y, hy⟩ := hWJ g hg
    rw [← hy]
    exact y.2
  have hWCe : ∀ g ∈ Wc, g ∈ Cg e := fun g hg => ((memW ⟨g, hWJmem g hg⟩).1 hg).2
  have hWnormH : ∀ h ∈ J ⊓ Cg e, ∀ g ∈ Wc, h * g * h⁻¹ ∈ Wc := by
    intro h hh g hg
    have hhJ : h ∈ J := (Subgroup.mem_inf.1 hh).1
    have hhC : h ∈ Cg e := (Subgroup.mem_inf.1 hh).2
    have hgJ := hWJmem g hg
    have hgW := (memW ⟨g, hgJ⟩).1 hg
    have hcen : psiOf J ι ⟨h, hhJ⟩ ∈ Subgroup.centralizer ({πa} : Set (Perm (Fin 7))) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hcommH ⟨h, hhJ⟩ hhC)
    have hconj := hV4 _ hcen _ hgW.1
    refine (memW ⟨h * g * h⁻¹, J.mul_mem (J.mul_mem hhJ hgJ) (J.inv_mem hhJ)⟩).2 ⟨?_, ?_⟩
    · have : (⟨h * g * h⁻¹, J.mul_mem (J.mul_mem hhJ hgJ) (J.inv_mem hhJ)⟩ : ↥J) =
          ⟨h, hhJ⟩ * ⟨g, hgJ⟩ * (⟨h, hhJ⟩)⁻¹ := by
        apply Subtype.ext; simp
      rw [this, map_mul, map_mul, map_inv]
      exact hconj
    · exact (Cg e).mul_mem ((Cg e).mul_mem hhC hgW.2) ((Cg e).inv_mem hhC)
  haveI hKnormal : (Kc.subgroupOf Wc).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgJ := hWJmem g.1 g.2
    have hgC := hWCe g.1 g.2
    have := conjK g.1 hgJ hgC n.1 hn
    simpa [mul_assoc] using this⟩
  have hLK : Lc.subgroupOf Wc ≤ Kc.subgroupOf Wc := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨y, hy⟩ := hLJ x.1 hx
    have hy' := (memL y).1 (hy ▸ hx)
    rw [← hy]
    exact (memK y).2 ⟨pcore_ker y hy'.1, hy'.2⟩
  have hcomm : ∀ k ∈ Kc.subgroupOf Wc, ∀ y : ↥Wc, k * y * k⁻¹ * y⁻¹ ∈ Lc.subgroupOf Wc := by
    intro k hk y
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    have hkJ : (k : G) ∈ J := hWJmem _ k.2
    have hyJ : (y : G) ∈ J := hWJmem _ y.2
    have hkC : (k : G) ∈ Cg e := hWCe _ k.2
    have hyC : (y : G) ∈ Cg e := hWCe _ y.2
    have hzJ : (k : G) * (y : G) * (k : G)⁻¹ * (y : G)⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem (J.mul_mem hkJ hyJ) (J.inv_mem hkJ)) (J.inv_mem hyJ)
    have hzC : (k : G) * (y : G) * (k : G)⁻¹ * (y : G)⁻¹ ∈ Cg e :=
      (Cg e).mul_mem ((Cg e).mul_mem ((Cg e).mul_mem hkC hyC) ((Cg e).inv_mem hkC))
        ((Cg e).inv_mem hyC)
    have hkc : (QuotientGroup.mk (⟨(k : G), hkJ⟩ : ↥J) : JbarQ J) ∈
        Subgroup.center (JbarQ J) :=
      ker_central _ ((memK ⟨(k : G), hkJ⟩).1 hk).1
    have hcen := fun g : JbarQ J => Subgroup.mem_center_iff.1 hkc g
    have hmk : (QuotientGroup.mk (⟨_, hzJ⟩ : ↥J) : JbarQ J) = 1 := by
      have hz_eq : (⟨_, hzJ⟩ : ↥J) = ⟨(k : G), hkJ⟩ * ⟨(y : G), hyJ⟩ * ⟨(k : G), hkJ⟩⁻¹ *
          ⟨(y : G), hyJ⟩⁻¹ := Subtype.ext (by simp)
      rw [hz_eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, (hcen (QuotientGroup.mk (⟨(y : G), hyJ⟩ : ↥J) :
          JbarQ J)).symm]
      group
    have hmem : (⟨_, hzJ⟩ : ↥J) ∈ CFSG.pCore 2 ↥J := (QuotientGroup.eq_one_iff _).1 hmk
    have := (memL ⟨_, hzJ⟩).2 ⟨hmem, hzC⟩
    simpa using this
  have hquot : ∀ w : ↥Wc, ∃ n : ℕ, w ^ 2 ^ n ∈ Kc.subgroupOf Wc := by
    intro w
    have hwJ : (w : G) ∈ J := hWJmem _ w.2
    have hw := (memW ⟨(w : G), hwJ⟩).1 w.2
    obtain ⟨n, hn⟩ := hV3 ⟨_, hw.1⟩
    refine ⟨n, ?_⟩
    rw [Subgroup.mem_subgroupOf]
    have hpow : ((w : G) ^ 2 ^ n) ∈ Kc := by
      refine (memK ⟨(w : G) ^ 2 ^ n, J.pow_mem hwJ _⟩).2 ⟨?_, (Cg e).pow_mem hw.2 _⟩
      have h1 : psiOf J ι ⟨(w : G) ^ 2 ^ n, J.pow_mem hwJ _⟩ = (psiOf J ι ⟨(w : G), hwJ⟩) ^ 2 ^ n := by
        rw [← map_pow]
        congr 1
      rw [h1]
      have hn' : (psiOf J ι ⟨(w : G), hwJ⟩) ^ 2 ^ n = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      exact hn'
    simpa using hpow
  have hL2 : IsPGroup 2 ↥(Lc.subgroupOf Wc) := by
    intro x
    have hxL : (x : ↥Wc).1 ∈ Lc := Subgroup.mem_subgroupOf.1 x.2
    obtain ⟨y, hy⟩ := hLJ _ hxL
    have hy' := (memL y).1 (by rw [hy]; exact hxL)
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) ⟨y, hy'.1⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have hyn : y ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have hyn' : ((x : ↥Wc).1 : G) ^ 2 ^ n = 1 := by
      rw [← hy]
      have := congrArg (fun z : ↥J => (z : G)) hyn
      simpa using this
    simpa using hyn'
  obtain ⟨P, hP2, hLP, hPnorm, hPel⟩ := sylow_core hLK hL2 hcomm hquot
  let P' : Subgroup G := P.map Wc.subtype
  have hP'mem : ∀ g : G, g ∈ P' ↔ ∃ w ∈ P, (w : G) = g := by
    intro g
    constructor
    · intro hg
      obtain ⟨w, hw, hwg⟩ := Subgroup.mem_map.1 hg
      exact ⟨w, hw, hwg⟩
    · rintro ⟨w, hw, rfl⟩
      exact Subgroup.mem_map.2 ⟨w, hw, rfl⟩
  have hP'2 : ∀ g ∈ P', ∃ n : ℕ, g ^ 2 ^ n = 1 := by
    intro g hg
    obtain ⟨w, hw, rfl⟩ := (hP'mem _).1 hg
    obtain ⟨n, hn⟩ := hP2 ⟨w, hw⟩
    refine ⟨n, ?_⟩
    have := congrArg (fun z : ↥P => ((z : ↥Wc) : G)) hn
    simpa using this
  have hP'sub : P' ≤ J ⊓ Cg e := by
    intro g hg
    obtain ⟨w, _, rfl⟩ := (hP'mem _).1 hg
    exact Subgroup.mem_inf.2 ⟨hWJmem _ w.2, hWCe _ w.2⟩
  have hconjP : ∀ h ∈ J ⊓ Cg e, ∀ g ∈ P', h * g * h⁻¹ ∈ P' := by
    intro h hh g hg
    obtain ⟨w, hw, rfl⟩ := (hP'mem _).1 hg
    have hwW : h * (w : G) * h⁻¹ ∈ Wc := hWnormH h hh _ w.2
    have hw'2 : ∃ n : ℕ, (⟨h * (w : G) * h⁻¹, hwW⟩ : ↥Wc) ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hP2 ⟨w, hw⟩
      refine ⟨n, Subtype.ext ?_⟩
      have hwn : (w : G) ^ 2 ^ n = 1 := by
        have := congrArg (fun z : ↥P => ((z : ↥Wc) : G)) hn
        simpa using this
      show (h * (w : G) * h⁻¹) ^ 2 ^ n = 1
      rw [conj_pow, hwn]
      group
    exact (hP'mem _).2 ⟨_, hPel _ hw'2, rfl⟩
  have hP'2grp : IsPGroup 2 ↥P' := by
    intro g
    obtain ⟨n, hn⟩ := hP'2 g.1 g.2
    exact ⟨n, Subtype.ext hn⟩
  have hHnorm : J ⊓ Cg e ≤ Subgroup.normalizer (P' : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hconjP h hh x hx
    · intro hx
      have := hconjP h⁻¹ ((J ⊓ Cg e).inv_mem hh) _ hx
      simpa [mul_assoc] using this
  have hPP : P' ≤ CFSG.Open.pCoreOf 2 (J ⊓ Cg e) :=
    Sec12a.le_pCoreOf_two_of_le_normalizer hP'sub hHnorm hP'2grp
  intro g hg
  obtain ⟨hgV, hgC⟩ := hg
  have hgJa : g ∈ J ⊓ Cg a := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hgV
  have hgJ : g ∈ J := (Subgroup.mem_inf.1 hgJa).1
  have hgCa : g ∈ Cg a := (Subgroup.mem_inf.1 hgJa).2
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_pCoreOf _ hgV
  have hgcomm : g = a * g * a⁻¹ := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 hgCa
    calc g = (g * a) * a⁻¹ := by group
      _ = (a * g) * a⁻¹ := by rw [h]
  have hpsi : psiOf J ι ⟨g, hgJ⟩ = πa * psiOf J ι ⟨g, hgJ⟩ * πa⁻¹ := hA ⟨g, hgJ⟩ ⟨g, hgJ⟩ hgcomm
  have hψcomm : psiOf J ι ⟨g, hgJ⟩ * πa = πa * psiOf J ι ⟨g, hgJ⟩ := comm_of_conj_eq' hpsi
  have hgJ2 : (⟨g, hgJ⟩ : ↥J) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  have hψpow : (psiOf J ι ⟨g, hgJ⟩) ^ 2 ^ k = 1 := by rw [← map_pow, hgJ2, map_one]
  have hψV : psiOf J ι ⟨g, hgJ⟩ ∈ V :=
    hV5 _ ⟨Subgroup.mem_centralizer_singleton_iff.2 hψcomm, psiOf_mem_alt J ι _⟩ k hψpow
  have hgW : g ∈ Wc := (memW ⟨g, hgJ⟩).2 ⟨hψV, hgC⟩
  have hgP : (⟨g, hgW⟩ : ↥Wc) ∈ P :=
    hPel _ ⟨k, Subtype.ext (by simpa using hk)⟩
  exact hPP ((hP'mem g).2 ⟨⟨g, hgW⟩, hgP, rfl⟩)

end PowProof

theorem powPiece_holds : PowPiece :=
  fun _ _ _ M J a e hJ _ he_norm ι πa πe hπa hA hE hpow =>
    power_piece_of_perm M J a e hJ he_norm ι πa πe hπa hA hE hpow

theorem blockLayer_of_inputs (hD : BlockDecomp) (hΔ : DiagPiece) : Sec12a2.BlockLayer :=
  blockLayer_of_pow_inputs hD powPiece_holds hΔ

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec12a3

end
