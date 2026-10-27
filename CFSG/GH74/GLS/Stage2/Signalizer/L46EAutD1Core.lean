module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutD1Rho
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E

open Subgroup CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank in
theorem autFactD1Y_proved : AutFactD1 := by
  intro Y _ _ k z X hd E hEX hodd h3 hnormI
  classical
  obtain ⟨hk, hX3, hPGL, hI, hL2, hC⟩ := hd
  have hKn : (ncl X).Normal := Subgroup.normalClosure_normal
  have hXK : X ≤ ncl X := Subgroup.subset_normalClosure
  set K : Subgroup Y := ncl X with hK
  set I : Subgroup Y := K ⊓ centralizer ({z} : Set Y) with hIdef
  have hI' : I = ⁅K, K⁆ ⊓ centralizer (X : Set Y) := hI
  obtain ⟨hIsimple, t, ht1, ht2⟩ := isL2_four hL2
  have hIK : I ≤ K := inf_le_left
  set C : Subgroup Y := centralizer (K : Set Y) with hCdef
  have hcomm_of_mem_C : ∀ c ∈ C, ∀ k ∈ K, c * k = k * c := fun c hc k hk =>
    (Subgroup.mem_centralizer_iff.1 hc k hk).symm
  have hordE : ∀ e ∈ E, Odd (orderOf e) ∧ Nat.Coprime (orderOf e) 3 := by
    intro e he
    have hde : orderOf e ∣ Nat.card E := by
      have := Subgroup.orderOf_dvd_natCard E he
      simpa using this
    refine ⟨Odd.of_dvd_nat hodd hde, ?_⟩
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => h3 ?_)
    exact h.trans hde
  have hdecomp : ∀ e ∈ E, ∃ g ∈ I, ∃ w ∈ C, e = g * w := by
    intro e he
    obtain ⟨hodd_e, hcop_e⟩ := hordE e he
    obtain ⟨g, hgK, hg⟩ := pgl3four_odd_inner' hPGL hodd_e
    have hgX : ∀ x ∈ X, g * x * g⁻¹ = x := by
      intro x hx
      rw [← hg x (hXK hx)]
      have := Subgroup.mem_centralizer_iff.1 (hEX he) x hx
      calc e * x * e⁻¹ = (x * e) * e⁻¹ := by rw [this]
        _ = x := by group
    have hpow : ∀ n : ℕ, ∀ k' ∈ K, e ^ n * k' * (e ^ n)⁻¹ = g ^ n * k' * (g ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro k' _; simp
      | succ n ih =>
        intro k' hk'
        have h1 : g ^ n * k' * (g ^ n)⁻¹ ∈ K := by
          have := hKn.conj_mem k' hk' (g ^ n)
          exact this
        calc e ^ (n + 1) * k' * (e ^ (n + 1))⁻¹
            = e * (e ^ n * k' * (e ^ n)⁻¹) * e⁻¹ := by group
          _ = e * (g ^ n * k' * (g ^ n)⁻¹) * e⁻¹ := by rw [ih k' hk']
          _ = g * (g ^ n * k' * (g ^ n)⁻¹) * g⁻¹ := hg _ h1
          _ = g ^ (n + 1) * k' * (g ^ (n + 1))⁻¹ := by group
    have hgm : g ^ orderOf e = 1 := by
      apply pgl3four_center hPGL (Subgroup.pow_mem K hgK _)
      intro k' hk'
      have := hpow (orderOf e) k' hk'
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at this
      calc g ^ orderOf e * k' = (g ^ orderOf e * k' * (g ^ orderOf e)⁻¹) * g ^ orderOf e := by group
        _ = k' * g ^ orderOf e := by rw [← this]
    have hcopg : Nat.Coprime (orderOf g) 3 :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hgm) hcop_e
    have hgL : g ∈ ⁅K, K⁆ := pgl3four_coprime_three hPGL hgK hcopg
    have hgC : g ∈ centralizer (X : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := hgX x hx
      calc x * g = (g * x * g⁻¹) * g := by rw [this]
        _ = g * x := by group
    refine ⟨g, by rw [hI']; exact ⟨hgL, hgC⟩, g⁻¹ * e, ?_, by group⟩
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro k' hk'
    have h1 := hg k' hk'
    calc k' * (g⁻¹ * e) = g⁻¹ * (g * k' * g⁻¹) * e := by group
      _ = g⁻¹ * (e * k' * e⁻¹) * e := by rw [h1]
      _ = (g⁻¹ * e) * k' := by group
  let S : Subgroup Y :=
    { carrier := {s | s ∈ I ∧ ∃ c ∈ C, s * c ∈ E}
      mul_mem' := by
        rintro a b ⟨haI, c, hc, hac⟩ ⟨hbI, d, hd, hbd⟩
        refine ⟨I.mul_mem haI hbI, c * d, C.mul_mem hc hd, ?_⟩
        have hcb : c * b = b * c := hcomm_of_mem_C c hc b (hIK hbI)
        have : a * b * (c * d) = (a * c) * (b * d) := by
          calc a * b * (c * d) = a * (b * c) * d := by group
            _ = a * (c * b) * d := by rw [hcb]
            _ = (a * c) * (b * d) := by group
        rw [this]
        exact E.mul_mem hac hbd
      one_mem' := ⟨I.one_mem, 1, C.one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨haI, c, hc, hac⟩
        refine ⟨I.inv_mem haI, c⁻¹, C.inv_mem hc, ?_⟩
        have hca : c⁻¹ * a⁻¹ = a⁻¹ * c⁻¹ :=
          hcomm_of_mem_C c⁻¹ (C.inv_mem hc) a⁻¹ (K.inv_mem (hIK haI))
        have : a⁻¹ * c⁻¹ = (a * c)⁻¹ := by rw [← hca]; group
        rw [this]
        exact E.inv_mem hac }
  have hSI : S ≤ I := fun s hs => hs.1
  have hSn : ∀ i ∈ I, ∀ s ∈ S, i * s * i⁻¹ ∈ S := by
    intro i hi s hs
    obtain ⟨hsI, c, hc, hsc⟩ := hs
    refine ⟨I.mul_mem (I.mul_mem hi hsI) (I.inv_mem hi), c, hc, ?_⟩
    have hic : i * c * i⁻¹ = c := by
      have := hcomm_of_mem_C c hc i (hIK hi)
      calc i * c * i⁻¹ = (c * i) * i⁻¹ := by rw [this]
        _ = c := by group
    have h1 : i * s * i⁻¹ * c = i * (s * c) * i⁻¹ := by
      calc i * s * i⁻¹ * c = i * s * i⁻¹ * (i * c * i⁻¹) := by rw [hic]
        _ = i * (s * c) * i⁻¹ := by group
    rw [h1]
    exact hnormI i hi (s * c) hsc
  have htK : (t : Y) ∈ K := hIK t.2
  have htt : (t : Y) * (t : Y) = 1 := congrArg Subtype.val ht2
  have hSbot : S = ⊥ := by
    by_contra hne
    have hSn' : (S.subgroupOf I).Normal := ⟨fun s hs i => by
      rw [Subgroup.mem_subgroupOf] at hs ⊢
      exact hSn i i.2 s hs⟩
    have hne' : S.subgroupOf I ≠ ⊥ := by
      intro hb
      apply hne
      refine (Subgroup.eq_bot_iff_forall _).2 fun s hs => ?_
      have : (⟨s, hSI hs⟩ : ↥I) ∈ S.subgroupOf I := Subgroup.mem_subgroupOf.2 hs
      rw [hb, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    rcases hIsimple.eq_bot_or_eq_top_of_normal (S.subgroupOf I) with h | h
    · exact hne' h
    · have htS : (t : Y) ∈ S := by
        have : t ∈ S.subgroupOf I := h ▸ Subgroup.mem_top t
        exact Subgroup.mem_subgroupOf.1 this
      obtain ⟨-, c, hc, htc⟩ := htS
      obtain ⟨hodd_u, -⟩ := hordE _ htc
      have hu2 : (t * c) * (t * c) = c * c := by
        have hct : c * t = t * c := hcomm_of_mem_C c hc t htK
        calc (t * c) * (t * c) = t * (c * t) * c := by group
          _ = t * (t * c) * c := by rw [hct]
          _ = (t * t) * (c * c) := by group
          _ = c * c := by rw [htt, one_mul]
      have huC : (t : Y) * c ∈ C := by
        obtain ⟨j, hj⟩ := hodd_u
        have h2 : ((t : Y) * c) ^ (orderOf ((t : Y) * c) + 1) = (t * c) := by
          rw [pow_succ, pow_orderOf_eq_one, one_mul]
        have h3 : ((t : Y) * c) ^ (orderOf ((t : Y) * c) + 1) = (c * c) ^ (j + 1) := by
          have : orderOf ((t : Y) * c) + 1 = 2 * (j + 1) := by omega
          rw [this, pow_mul, pow_two, hu2]
        rw [← h2, h3]
        exact Subgroup.pow_mem C (C.mul_mem hc hc) _
      have htC : (t : Y) ∈ C := by
        have := C.mul_mem huC (C.inv_mem hc)
        simpa using this
      have ht1' : (t : Y) = 1 :=
        pgl3four_center hPGL htK fun k' hk' => (Subgroup.mem_centralizer_iff.1 htC k' hk').symm
      exact ht1 (Subtype.ext ht1')
  intro e he
  obtain ⟨g, hgI, w, hwC, hew⟩ := hdecomp e he
  have hgS : g ∈ S := ⟨hgI, w, hwC, hew ▸ he⟩
  rw [hSbot, Subgroup.mem_bot] at hgS
  rw [hew, hgS, one_mul]
  exact hwC


end CFSG.GH74.GLS.Stage2.Signalizer.L46E
