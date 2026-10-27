module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreRL2Basic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Transfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreRL2Transfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreRLChar

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

theorem exists_pow_eq_mul_zpow (hc : PartC T Q P₁ e u) {g : G} (hgT : g ∈ T) {q : G}
    (hq : q ∈ Q) (k : ℤ) (m : ℕ) : ∃ q' ∈ Q, (q * g ^ k) ^ m = q' * g ^ (k * m) := by
  induction m with
  | zero => exact ⟨1, Q.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨q', hq', h⟩ := ih
    refine ⟨q' * (g ^ (k * m) * q * (g ^ (k * m))⁻¹), Q.mul_mem hq'
      (hc.normal_left _ (T.zpow_mem hgT _) q hq), ?_⟩
    rw [pow_succ, h]
    push_cast
    group

theorem false_of_pow_generator [Finite G] (hperf : Group.IsPerfect G) (hc : PartC T Q P₁ e u)
    (S : Sylow 2 G) (hST : (S : Subgroup G) = T) {g : G} (hgT : g ∈ T)
    (hgen : ∀ t ∈ T, ∃ q ∈ Q, ∃ i : ℤ, t = q * g ^ i)
    (hgg : ∀ q ∈ Q, q * (g * g) = g * g * q) {N : ℕ} (hN : 3 ≤ N) (hgo : orderOf g = 2 ^ N)
    (hge : g ^ 2 ^ (N - 1) = e) (hQg : ∀ x ∈ Q, x ∈ Subgroup.zpowers g → x = 1 ∨ x = e) :
    False := by
  subst hST
  set E := Subgroup.zpowers e with hE
  set K := qPowSubgroup Q (g * g) hgg with hK
  set M := 2 ^ (N - 2) with hM
  have hEQ : E ≤ Q := hc.zpowers_centralElt_le_left
  have hgM : (g * g) ^ M = e := by
    rw [← hge, ← pow_two, ← pow_mul]
    congr 1
    rw [hM, ← pow_succ']
    congr 1
    omega
  have hA : ∀ q ∈ Q, ∀ l : ℤ, (q * (g * g) ^ l) ^ M ∈ E := by
    intro q hq l
    rw [((show Commute q (g * g) from hgg q hq).zpow_right l).mul_pow]
    refine E.mul_mem ?_ ?_
    · rw [hM, show N - 2 = N - 3 + 1 by omega, pow_succ', pow_mul, pow_two]
      refine E.pow_mem ?_ _
      rcases quaternion_mul_self hc.quaternion.some hc.mem_left hc.order hq with h | h <;>
        rw [h]
      · exact E.one_mem
      · exact Subgroup.mem_zpowers e
    · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgM]
      exact Subgroup.zpow_mem_zpowers e l
  have hB : ∀ q ∈ Q, ∀ l : ℤ, (q * g ^ (2 * l + 1)) ^ M ∉ E := by
    intro q hq l hmem
    obtain ⟨q', hq', h⟩ := hc.exists_pow_eq_mul_zpow hgT hq (2 * l + 1) M
    have hx : g ^ ((2 * l + 1) * (M : ℤ)) ∈ Q := by
      have h1 : g ^ ((2 * l + 1) * (M : ℤ)) = q'⁻¹ * (q * g ^ (2 * l + 1)) ^ M := by
        rw [h, inv_mul_cancel_left]
      rw [h1]
      exact Q.mul_mem (Q.inv_mem hq') (hEQ hmem)
    have h2 : g ^ ((2 * l + 1) * (M : ℤ) * 2) = 1 := by
      rw [zpow_mul]
      rcases hQg _ hx (Subgroup.zpow_mem_zpowers g _) with h' | h' <;> rw [h']
      · exact one_zpow 2
      · rw [zpow_two, hc.centralElt_mul_self]
    have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [hgo, hM, show N = N - 2 + 1 + 1 by omega] at h3
    push_cast at h3
    have h4 : (2 : ℤ) * (2 ^ (N - 2) * 2) ∣ (2 * l + 1) * (2 ^ (N - 2) * 2) := by
      convert h3 using 1
      · rw [pow_succ, pow_succ]
        ring
      · ring
    have h5 := Int.dvd_of_mul_dvd_mul_right (by positivity) h4
    omega
  have hinv : ∀ t ∈ (S : Subgroup G), t ∈ K ↔ t ^ M ∈ E := by
    intro t ht
    constructor
    · rintro ⟨q, hq, l, rfl⟩
      exact hA q hq l
    · intro htM
      obtain ⟨q, hq, i, rfl⟩ := hgen t ht
      obtain ⟨l, rfl | rfl⟩ := Int.even_or_odd' i
      · exact ⟨q, hq, l, by rw [zpow_mul, zpow_two]⟩
      · exact absurd htM (hB q hq l)
  have hgK : g ∉ K := fun h => hB 1 Q.one_mem 0 (by
    simpa using (hinv g hgT).mp h)
  have hcos : ∀ t ∈ (S : Subgroup G), t ∉ K → t * g ∈ K := by
    intro t ht htK
    obtain ⟨q, hq, i, rfl⟩ := hgen t ht
    obtain ⟨l, rfl | rfl⟩ := Int.even_or_odd' i
    · exact absurd ⟨q, hq, l, by rw [zpow_mul, zpow_two]⟩ htK
    · refine ⟨q, hq, l + 1, ?_⟩
      rw [← zpow_two, ← zpow_mul, mul_assoc, ← zpow_add_one]
      ring_nf
  have hKS : K ≤ S := by
    rintro _ ⟨q, hq, l, rfl⟩
    exact (S : Subgroup G).mul_mem (hc.left_le hq) ((S : Subgroup G).zpow_mem
      ((S : Subgroup G).mul_mem hgT hgT) l)
  refine false_of_relIndex_eq_two hperf S hKS (relIndex_eq_two_of_mul_mem hgT hgK hcos) hgT
    hgK fun m a ha => ?_
  have hgm : g ^ m ∈ (S : Subgroup G) := (S : Subgroup G).zpow_mem hgT m
  rw [hinv _ hgm, hinv _ ha, show (a⁻¹ * g ^ m * a) ^ M = a⁻¹ * (g ^ m) ^ M * a by
    simpa using conj_pow (a := a⁻¹) (b := g ^ m) (i := M)]
  constructor
  · intro h
    rwa [hc.conj_eq_of_mem_zpowers_centralElt h a]
  · intro h
    have h' := hc.conj_eq_of_mem_zpowers_centralElt h a⁻¹
    rw [show a⁻¹⁻¹ * (a⁻¹ * (g ^ m) ^ M * a) * a⁻¹ = (g ^ m) ^ M by group] at h'
    rw [h']
    exact h

theorem pow_half_eq {H : Subgroup G} (hH : ∀ x ∈ H, orderOf x = 2 → x = e) {g : G} (hg : g ∈ H)
    {N : ℕ} (hN : 1 ≤ N) (hgo : orderOf g = 2 ^ N) : g ^ 2 ^ (N - 1) = e := by
  refine hH _ (H.pow_mem hg _) ?_
  rw [orderOf_pow_of_dvd (by positivity) (by rw [hgo]; exact pow_dvd_pow 2 (Nat.sub_le N 1)),
    hgo, show N = N - 1 + 1 by omega, pow_succ, Nat.add_sub_cancel,
    Nat.mul_div_cancel_left _ (by positivity)]

theorem false_of_le_sup_of_three_le [Finite G] (hperf : Group.IsPerfect G)
    (hc : PartC T Q P₁ e u) (S : Sylow 2 G) (hST : (S : Subgroup G) = T) (hT : T ≤ Q ⊔ P₁)
    {c : G} {n : ℕ} (hcP : Subgroup.zpowers c = P₁) (hco : orderOf c = 2 ^ n) (hn : 3 ≤ n)
    (hce : c ^ 2 ^ (n - 1) = e) : False := by
  have hcP₁ : c ∈ P₁ := hcP ▸ Subgroup.mem_zpowers c
  refine hc.false_of_pow_generator hperf S hST (hc.right_le hcP₁) (fun t ht => ?_)
    (fun q hq => ?_) hn hco hce (fun x hxQ hx => hc.mem_inf x hxQ (hcP ▸ hx))
  · obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp (hT ht)
    rw [← hcP] at hp
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    exact ⟨q, hq, i, rfl⟩
  · have h := hc.commute q hq c hcP₁
    calc q * (c * c) = q * c * c := by group
      _ = c * c * q := by rw [h, mul_assoc, h]; group

theorem false_of_isCyclic_sup [Finite G] (hperf : Group.IsPerfect G) (hc : PartC T Q P₁ e u)
    (hcyc : IsCyclic P₁) (S : Sylow 2 G) (hST : (S : Subgroup G) = T) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁)
    (hPc : IsCyclic (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) : False := by
  obtain ⟨c, n, hcP, hco, hn, -⟩ := hc.exists_generator hcyc
  obtain ⟨g, hgP⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mp hPc
  have hgP' : g ∈ P₁ ⊔ Subgroup.zpowers y := hgP ▸ Subgroup.mem_zpowers g
  have hgo : orderOf g = 2 ^ (n + 1) := by
    rw [← Nat.card_zpowers, hgP, hc.card_sup_zpowers hyT hy hyy, ← hcP, Nat.card_zpowers, hco,
      pow_succ, mul_comm]
  refine hc.false_of_pow_generator hperf S hST (hc.sup_zpowers_le hyT hgP') (fun t ht => ?_)
    (fun q hq => hc.commute q hq _ (hc.mul_self_mem_right hyT hyy hgP')) (by omega) hgo
    (pow_half_eq (fun x hx hx2 => hc.eq_of_mem_sup_zpowers hyT hy hyy hx hx2) hgP' (by omega) hgo)
    (fun x hxQ hx => hc.mem_inf_sup_zpowers hyT hy hyy hxQ (hgP ▸ hx))
  obtain ⟨q, hq, w, hw, rfl⟩ := hc.exists_mul_eq_of_mem hyT hy ht
  rw [← hgP] at hw
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨q, hq, i, rfl⟩

theorem self_not_mem_left (hc : PartC T Q P₁ e u) : u ∉ Q := fun h => by
  rcases hc.mem_inf u h hc.self_mem with h' | h'
  · exact hc.self_ne.1 h'
  · exact hc.self_ne.2 h'

theorem inv_conj_mul_centralElt (hc : PartC T Q P₁ e u) (a x : G) :
    a⁻¹ * (x * e) * a = a⁻¹ * x * a * e := by
  have h := hc.conj_mul_centralElt a⁻¹ x
  rwa [inv_inv] at h

theorem relIndex_left_sup_eq_two (hc : PartC T Q P₁ e u) (hP₁ : Subgroup.zpowers u = P₁) :
    Q.relIndex (Q ⊔ P₁) = 2 := by
  refine relIndex_eq_two_of_mul_mem (Subgroup.mem_sup_right hc.self_mem) hc.self_not_mem_left
    fun t ht htQ => ?_
  obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp ht
  rw [← hP₁] at hp
  rcases hc.mem_zpowers_of_mul_self hc.sq hp with h | h | h | h <;> rw [h] at htQ ⊢
  · exact absurd (by rw [mul_one]; exact hq) htQ
  · rw [mul_assoc, hc.sq]
    exact Q.mul_mem hq hc.mem_left
  · exact absurd (Q.mul_mem hq hc.mem_left) htQ
  · have h1 : q * (u * e) * u = q * (u * u) * e := by
      calc q * (u * e) * u = q * u * (e * u) := by group
        _ = q * u * (u * e) := by rw [← hc.commute_centralElt u]
        _ = q * (u * u) * e := by group
    rw [h1, hc.sq, mul_assoc, hc.centralElt_mul_self, mul_one]
    exact hq

theorem false_of_le_sup_of_zpowers_eq [Finite G] (hperf : Group.IsPerfect G)
    (hc : PartC T Q P₁ e u) (hcyc : IsCyclic P₁) (S : Sylow 2 G) (hST : (S : Subgroup G) = T)
    (hT : T ≤ Q ⊔ P₁) (hP₁ : Subgroup.zpowers u = P₁) : False := by
  have hTeq : T = Q ⊔ P₁ := le_antisymm hT hc.sup_le
  have hNT := hc.normalizer_le_normalizer_zpowers_of_isCyclic hcyc
  have hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) :=
    Subgroup.le_normalizer.trans hNT
  have hQu : ∀ b : G, b⁻¹ * u * b ∉ Q := by
    intro b hb
    set x := b⁻¹ * u * b with hx
    have hxx : x * x = e := by
      rw [hx, show b⁻¹ * u * b * (b⁻¹ * u * b) = b⁻¹ * (u * u) * b by group, hc.sq, mul_assoc,
        ← hc.commute_centralElt b, inv_mul_cancel_left]
    have hTx : T ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
      intro t ht
      refine mem_normalizer_zpowers_of_conj_mem ?_
      obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp (hT ht)
      have h1 : q * p * x * (q * p)⁻¹ = q * x * q⁻¹ := by
        calc q * p * x * (q * p)⁻¹ = q * (p * x * p⁻¹) * q⁻¹ := by group
          _ = q * x * q⁻¹ := by rw [← hc.commute x hb p hp, mul_inv_cancel_right]
      rw [h1]
      rcases hc.comm_or_anticomm hq hb with h | h
      · rw [h, mul_inv_cancel_right]
        exact Subgroup.mem_zpowers x
      · have h' : q * x * q⁻¹ = x * e := by
          rw [h, mul_assoc x q e, hc.commute_centralElt q]
          group
        rw [h']
        exact mul_centralElt_mem_zpowers hxx
    exact hc.conj_not_mem_zpowers S hST hnorm hNT hb hxx hTx b⁻¹
      (by rw [inv_inv]; exact Subgroup.mem_zpowers x)
  have huS : u ∈ (S : Subgroup G) := hST ▸ hc.right_le hc.self_mem
  refine false_of_relIndex_eq_two hperf S (hST ▸ hc.left_le)
    (by rw [hST, hTeq]; exact hc.relIndex_left_sup_eq_two hP₁) huS hc.self_not_mem_left
    fun m a _ => ?_
  rcases hc.mem_zpowers_of_mul_self hc.sq (Subgroup.zpow_mem_zpowers u m) with h | h | h | h <;>
    rw [h]
  · simp
  · exact ⟨fun h' => absurd h' hc.self_not_mem_left, fun h' => absurd h' (hQu a)⟩
  · rw [mul_assoc, ← hc.commute_centralElt a, inv_mul_cancel_left]
  · rw [hc.inv_conj_mul_centralElt]
    refine ⟨fun h' => absurd ?_ hc.self_not_mem_left, fun h' => absurd ?_ (hQu a)⟩
    · simpa [hc.mul_centralElt_mul_centralElt] using Q.mul_mem h' hc.mem_left
    · simpa [hc.mul_centralElt_mul_centralElt] using Q.mul_mem h' hc.mem_left

theorem false_of_not_isCyclic_of_zpowers_eq [Finite G] (hperf : Group.IsPerfect G)
    (hc : PartC T Q P₁ e u) (S : Sylow 2 G) (hST : (S : Subgroup G) = T) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y = e) (hP₁ : Subgroup.zpowers u = P₁) : False := by
  set D := twoCosets Q y (fun q hq => hc.normal_left y hyT q hq) (hyy ▸ hc.mem_left) with hD
  have hDT : D ≤ T := by
    rintro x (hx | hx)
    · exact hc.left_le hx
    · rw [show x = x * y⁻¹ * y by group]
      exact T.mul_mem (hc.left_le hx) hyT
  have hyD : y ∈ D := Or.inr (by rw [mul_inv_cancel]; exact Q.one_mem)
  have hQD : Q ≤ D := fun x hx => Or.inl hx
  have h1 : Q.relIndex D = 2 := relIndex_eq_two_of_mul_mem hyD
    (fun h => hy (Subgroup.mem_sup_left h)) fun t ht htQ => by
      rcases ht with ht | ht
      · exact absurd ht htQ
      · rw [show t * y = t * y⁻¹ * (y * y) by group, hyy]
        exact Q.mul_mem ht hc.mem_left
  have h2 : Q.relIndex T = 2 * 2 := by
    rw [← Subgroup.relIndex_mul_relIndex Q (Q ⊔ P₁) T le_sup_left hc.sup_le,
      hc.relIndex_left_sup_eq_two hP₁]
    exact congrArg _ (hc.index_subgroupOf_eq_two hyT hy)
  have hDrel : D.relIndex T = 2 := by
    have h3 := Subgroup.relIndex_mul_relIndex Q D T hQD hDT
    rw [h1, h2] at h3
    omega
  have hinvD : ∀ x ∈ D, orderOf x = 2 → x = e := by
    intro x hx hx2
    have hxs := hc.involution_mem x (hDT hx) hx2
    rcases hx with hx | hx
    · have hxx : x * x = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
      rcases quaternion_eq_of_mul_self hc.quaternion.some hc.mem_left hc.order hx hxx with h | h
      · rw [h, orderOf_one] at hx2
        exact absurd hx2 (by decide)
      · exact h
    · have hyx : y = (x * y⁻¹)⁻¹ * x := by group
      exact absurd (hyx ▸ (Q ⊔ P₁).mul_mem ((Q ⊔ P₁).inv_mem (Subgroup.mem_sup_left hx)) hxs) hy
  obtain ⟨q₁, hq₁, -, -, hq₁q₁, -, -, -⟩ :=
    quaternion_exists_pair hc.quaternion.some hc.mem_left hc.order
  have hz := hc.orderOf_mul_eq_two hq₁ hc.self_mem hq₁q₁ hc.sq
  obtain ⟨g, hg⟩ := exists_conj_mem_of_relIndex_eq_two hperf.commutator_eq_top S (hST ▸ hDT)
    (hST ▸ hDrel) hz
  have hg2 : orderOf (g⁻¹ * (q₁ * u) * g) = 2 := by
    rw [show g⁻¹ * (q₁ * u) * g = g⁻¹ * (q₁ * u) * g⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, hz]
  have he := hinvD _ hg hg2
  apply hc.mul_ne_centralElt hq₁ hc.self_mem hq₁q₁
  calc q₁ * u = g * (g⁻¹ * (q₁ * u) * g) * g⁻¹ := by group
    _ = e := by rw [he, hc.commute_centralElt g, mul_inv_cancel_right]

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
