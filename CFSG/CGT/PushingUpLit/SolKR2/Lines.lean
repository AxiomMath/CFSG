module

public import CFSG.CGT.PushingUpLit.SolKR2.Pair

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n (conjSubgroup_mul conjSubgroup_eq_self_iff exists_mul_of_mem_sup
  inSubgroup_pCore_two mem_normalizer_inf mem_normalizer_centralizer)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem layer_mem {v p : G} {A K : Subgroup G} (hKA : K ≤ A)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hA4 : ∀ a ∈ A, a ^ 4 = 1)
    (hvA : ∀ a ∈ A, v * a * v⁻¹ * a⁻¹ ∈ K) (hvK : ∀ b ∈ K, v * b = b * v)
    (hodd : Odd (orderOf v)) (hc : v * p * v⁻¹ * p⁻¹ ∈ A) : v * p * v⁻¹ * p⁻¹ ∈ K := by
  set c := v * p * v⁻¹ * p⁻¹ with hcdef
  have key : ∀ k : ℕ, ∃ b ∈ K, v ^ k * p * (v ^ k)⁻¹ * p⁻¹ = c ^ k * b := by
    intro k
    induction k with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨b, hbK, hb⟩ := ih
      have hb₁ : v * c * v⁻¹ * c⁻¹ ∈ K := hvA c hc
      set b₁ := v * c * v⁻¹ * c⁻¹ with hb₁def
      have hbA : b ∈ A := hKA hbK
      have hb₁A : b₁ ∈ A := hKA hb₁
      refine ⟨b₁ ^ k * b, K.mul_mem (K.pow_mem hb₁ k) hbK, ?_⟩
      have e1 : v ^ (k + 1) * p * (v ^ (k + 1))⁻¹ * p⁻¹ =
          (v * (v ^ k * p * (v ^ k)⁻¹ * p⁻¹) * v⁻¹) * c := by
        rw [hcdef, pow_succ']
        group
      have e2 : v * (c ^ k * b) * v⁻¹ = (b₁ * c) ^ k * b := by
        have h1 : v * (c ^ k * b) * v⁻¹ = (v * c * v⁻¹) ^ k * (v * b * v⁻¹) := by
          rw [conj_pow]
          group
        have h2 : v * c * v⁻¹ = b₁ * c := by
          rw [hb₁def]
          group
        have h3 : v * b * v⁻¹ = b := by
          rw [hvK b hbK]
          group
        rw [h1, h2, h3]
      have hmp : (b₁ * c) ^ k = b₁ ^ k * c ^ k :=
        Commute.mul_pow (show Commute b₁ c from hAc b₁ hb₁A c hc) k
      have hcomm1 : b₁ ^ k * c ^ k = c ^ k * b₁ ^ k :=
        hAc _ (A.pow_mem hb₁A k) _ (A.pow_mem hc k)
      have hcomm2 : b * c = c * b := hAc _ hbA _ hc
      have hcomm3 : b₁ ^ k * c = c * b₁ ^ k := hAc _ (A.pow_mem hb₁A k) _ hc
      rw [e1, hb, e2, hmp]
      calc b₁ ^ k * c ^ k * b * c = b₁ ^ k * c ^ k * (b * c) := by group
        _ = b₁ ^ k * c ^ k * (c * b) := by rw [hcomm2]
        _ = (b₁ ^ k * c ^ k) * c * b := by group
        _ = (c ^ k * b₁ ^ k) * c * b := by rw [hcomm1]
        _ = c ^ k * (b₁ ^ k * c) * b := by group
        _ = c ^ k * (c * b₁ ^ k) * b := by rw [hcomm3]
        _ = c ^ (k + 1) * (b₁ ^ k * b) := by rw [pow_succ]; group
  obtain ⟨b, hbK, hb⟩ := key (orderOf v)
  rw [pow_orderOf_eq_one] at hb
  have h1 : c ^ orderOf v * b = 1 := by
    rw [← hb]
    simp
  have hcn : c ^ orderOf v ∈ K := by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact K.inv_mem hbK
  obtain ⟨r, hr⟩ := hodd
  have hsq : c = (c ^ orderOf v) ^ orderOf v := by
    have h4 : c ^ 4 = 1 := hA4 c hc
    have e : orderOf v * orderOf v = 4 * (r * r + r) + 1 := by
      rw [hr]
      ring
    rw [← pow_mul, e, pow_succ, pow_mul, h4, one_pow, one_mul]
  rw [hsq]
  exact K.pow_mem hcn _

section Stab

variable (M P U B₀ : Subgroup G) (hU : M ≤ Subgroup.normalizer (U : Set G))
  (hB : M ≤ Subgroup.normalizer (B₀ : Set G))

def stabSeries : Subgroup G where
  carrier := {v | v ∈ M ∧ (∀ p ∈ P, v * p * v⁻¹ * p⁻¹ ∈ U) ∧
    (∀ u ∈ U, v * u * v⁻¹ * u⁻¹ ∈ B₀) ∧ ∀ b ∈ B₀, v * b = b * v}
  one_mem' := ⟨M.one_mem, fun p _ => by simp, fun u _ => by simp, fun b _ => by simp⟩
  mul_mem' := by
    rintro v w ⟨hvM, hvP, hvU, hvB⟩ ⟨hwM, hwP, hwU, hwB⟩
    refine ⟨M.mul_mem hvM hwM, fun p hp => ?_, fun u hu => ?_, fun b hb => ?_⟩
    · have h1 : v * (w * p * w⁻¹ * p⁻¹) * v⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hU hvM) _).mp (hwP p hp)
      have := U.mul_mem h1 (hvP p hp)
      rwa [show v * (w * p * w⁻¹ * p⁻¹) * v⁻¹ * (v * p * v⁻¹ * p⁻¹) =
        v * w * p * (v * w)⁻¹ * p⁻¹ by group] at this
    · have h1 : v * (w * u * w⁻¹ * u⁻¹) * v⁻¹ ∈ B₀ :=
        (Subgroup.mem_normalizer_iff.mp (hB hvM) _).mp (hwU u hu)
      have := B₀.mul_mem h1 (hvU u hu)
      rwa [show v * (w * u * w⁻¹ * u⁻¹) * v⁻¹ * (v * u * v⁻¹ * u⁻¹) =
        v * w * u * (v * w)⁻¹ * u⁻¹ by group] at this
    · calc v * w * b = v * (w * b) := by group
        _ = v * (b * w) := by rw [hwB b hb]
        _ = (v * b) * w := by group
        _ = (b * v) * w := by rw [hvB b hb]
        _ = b * (v * w) := by group
  inv_mem' := by
    rintro v ⟨hvM, hvP, hvU, hvB⟩
    refine ⟨M.inv_mem hvM, fun p hp => ?_, fun u hu => ?_, fun b hb => ?_⟩
    · have h1 : v⁻¹ * (v * p * v⁻¹ * p⁻¹)⁻¹ * v⁻¹⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hU (M.inv_mem hvM)) _).mp (U.inv_mem (hvP p hp))
      rwa [show v⁻¹ * (v * p * v⁻¹ * p⁻¹)⁻¹ * v⁻¹⁻¹ = v⁻¹ * p * v⁻¹⁻¹ * p⁻¹ by group] at h1
    · have h1 : v⁻¹ * (v * u * v⁻¹ * u⁻¹)⁻¹ * v⁻¹⁻¹ ∈ B₀ :=
        (Subgroup.mem_normalizer_iff.mp (hB (M.inv_mem hvM)) _).mp (B₀.inv_mem (hvU u hu))
      rwa [show v⁻¹ * (v * u * v⁻¹ * u⁻¹)⁻¹ * v⁻¹⁻¹ = v⁻¹ * u * v⁻¹⁻¹ * u⁻¹ by group] at h1
    · have h1 := hvB b hb
      calc v⁻¹ * b = v⁻¹ * (b * v) * v⁻¹ := by group
        _ = v⁻¹ * (v * b) * v⁻¹ := by rw [h1]
        _ = b * v⁻¹ := by group

variable {M P U B₀ hU hB}

end Stab

section Config

variable [Finite G] {M B : Subgroup G} (h : R2 M B)
include h

theorem lam_isPGroup {A : Subgroup G} (hA : A ∈ Lam M B) : IsPGroup 2 ↥A := by
  obtain ⟨g, rfl, -⟩ := hA
  exact (h.H.two.to_le (omegaOneSub_le B)).map (MulAut.conj g).toMonoidHom

theorem exists_sylow_ge {A : Subgroup G} (hA : A ∈ Lam M B) :
    ∃ S : Sylow 2 M, A ≤ (S : Subgroup M).map M.subtype ∧
      inSubgroup (pCore 2) M ≤ (S : Subgroup M).map M.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAM : A ≤ M := Lam.le_M hA
  have hA2 : IsPGroup 2 ↥(A.subgroupOf M) :=
    (lam_isPGroup h hA).of_equiv (Subgroup.subgroupOfEquivOfLe hAM).symm
  obtain ⟨S, hS⟩ := hA2.exists_le_sylow
  refine ⟨S, fun x hx => ⟨⟨x, hAM hx⟩, hS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩, ?_⟩
  exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := M)).le_sylow_of_normal S)

omit [Finite G] in
theorem le_normalizer_P : M ≤ Subgroup.normalizer
    ((inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (omegaTwoSub B : Set G) : Subgroup G) :
      Set G) :=
  fun _ hm => mem_normalizer_inf ((inSubgroup_pCore_two M).2.2 hm)
    (mem_normalizer_centralizer (Pair.le_normalizer_U h hm))

theorem eq_one_of_mem_stabSeries {v : G}
    (hv : v ∈ stabSeries M (inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (omegaTwoSub B : Set G))
      (omegaTwoSub B) (omegaOneSub B) (Pair.le_normalizer_U h) (Pair.le_normalizer_B0 h))
    (hodd : Odd (orderOf v)) : v = 1 := by
  obtain ⟨hvM, hvP, hvU, hvB⟩ := hv
  have hUM : omegaTwoSub B ≤ M := (omegaTwoSub_le B).trans h.H.le
  have hcentral : ∀ p ∈ inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (omegaTwoSub B : Set G),
      p * v = v * p := by
    intro p hp
    have hc1 : v * p * v⁻¹ * p⁻¹ ∈ omegaOneSub B :=
      layer_mem (K := omegaOneSub B) (A := omegaTwoSub B) (Pair.B0_le_U h) (Pair.comm_U h)
        (fun a ha => pow_four_of_mem_omegaTwoSub h.H.comm ha) hvU hvB hodd (hvP p hp)
    have hc2 : v * p * v⁻¹ * p⁻¹ ∈ (⊥ : Subgroup G) :=
      layer_mem (K := ⊥) (A := omegaOneSub B) bot_le
        (fun a ha a' ha' => h.H.comm _ (omegaOneSub_le B ha) _ (omegaOneSub_le B ha'))
        (fun a ha => by
          have := Pair.sq_B0 h ha
          calc a ^ 4 = (a * a) * (a * a) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
            _ = 1 := by rw [this, one_mul])
        (fun a ha => by
          rw [Subgroup.mem_bot, hvB a ha]
          group)
        (fun b hb => by
          rw [Subgroup.mem_bot] at hb
          subst hb
          simp) hodd hc1
    rw [Subgroup.mem_bot] at hc2
    calc p * v = (v * p * v⁻¹ * p⁻¹)⁻¹ * (v * p) * (p * p⁻¹)⁻¹ := by group
      _ = v * p := by rw [hc2]; group
  have hα := tim78_2_9_alpha h.H.fstar hUM (Pair.le_normalizer_U h)
    ⟨⟨fun a b => Subtype.ext (Pair.comm_U h _ a.2 _ b.2)⟩⟩ rfl
  have hvmem : v ∈ M ⊓ Subgroup.centralizer
      ((inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (omegaTwoSub B : Set G) : Subgroup G) :
        Set G) :=
    ⟨hvM, Subgroup.mem_centralizer_iff.mpr hcentral⟩
  rw [hα] at hvmem
  exact eq_one_of_odd_of_isPGroup (inSubgroup_pCore_two M).1 hvmem.1.1 hodd

end Config

section CertConfig

variable
  [Finite G] {M B : Subgroup G} (h : R2 M B)
include h

theorem comm_U_mem_B0 {A : Subgroup G} (hA : A ∈ Lam M B) {a u : G} (ha : a ∈ A)
    (hu : u ∈ omegaTwoSub B) : a * u * a⁻¹ * u⁻¹ ∈ omegaOneSub B := by
  have haM : a ∈ M := Lam.le_M hA ha
  have hUc := Pair.comm_U h
  have hw : a * u * a⁻¹ ∈ omegaTwoSub B :=
    (Subgroup.mem_normalizer_iff.mp (Pair.le_normalizer_U h haM) u).mp hu
  have huB : u ∈ B := omegaTwoSub_le B hu
  have hu2 : u * u ∈ omegaOneSub B := by
    refine (mem_omegaOneSub_iff h.H.comm).2 ⟨B.mul_mem huB huB, ?_⟩
    have := pow_four_of_mem_omegaTwoSub h.H.comm hu
    calc u * u * (u * u) = u ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  have hcomm : a * (u * u) = (u * u) * a := R2.comm_B0 h hA a ha (u * u) hu2
  have hww : (a * u * a⁻¹) * (a * u * a⁻¹) = u * u := by
    calc (a * u * a⁻¹) * (a * u * a⁻¹) = a * (u * u) * a⁻¹ := by group
      _ = u * u := by rw [hcomm]; group
  have hcomm' : u⁻¹ * (a * u * a⁻¹) = (a * u * a⁻¹) * u⁻¹ := hUc _ (Subgroup.inv_mem _ hu) _ hw
  refine (mem_omegaOneSub_iff h.H.comm).2 ⟨B.mul_mem (omegaTwoSub_le B hw) (B.inv_mem huB), ?_⟩
  calc (a * u * a⁻¹ * u⁻¹) * (a * u * a⁻¹ * u⁻¹)
      = (a * u * a⁻¹) * (u⁻¹ * (a * u * a⁻¹)) * u⁻¹ := by group
    _ = (a * u * a⁻¹) * ((a * u * a⁻¹) * u⁻¹) * u⁻¹ := by rw [hcomm']
    _ = ((a * u * a⁻¹) * (a * u * a⁻¹)) * (u⁻¹ * u⁻¹) := by group
    _ = (u * u) * (u⁻¹ * u⁻¹) := by rw [hww]
    _ = 1 := by group

end CertConfig

section Main

variable
  [Finite G] {M B : Subgroup G}
  (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) (hW : R2Weak) (hF : R2First)
  (h : R2 M B)
include hCen hU hW hF h

theorem comm_P_mem_U {A : Subgroup G} (hA : A ∈ Lam M B) {a p : G} (ha : a ∈ A)
    (hp : p ∈ inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (omegaTwoSub B : Set G)) :
    a * p * a⁻¹ * p⁻¹ ∈ omegaTwoSub B := by
  obtain ⟨hpQ, hpC⟩ := Subgroup.mem_inf.mp hp
  have hpM : p ∈ M := (inSubgroup_pCore_two M).2.1 hpQ
  have haM : a ∈ M := Lam.le_M hA ha
  have hz : a * p * a⁻¹ * p⁻¹ ∈ Subgroup.centralizer (omegaTwoSub B : Set G) := by
    have h1 : a * p * a⁻¹ ∈ (inSubgroup (pCore 2) M ⊓
        Subgroup.centralizer (omegaTwoSub B : Set G)) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_P h haM) p).mp hp
    exact (Subgroup.mem_inf.mp (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hp))).2
  by_cases hAB : A = omegaOneSub B
  · subst hAB
    have haU : a ∈ omegaTwoSub B := Pair.B0_le_U h ha
    have hap : a * p = p * a := Subgroup.mem_centralizer_iff.mp hpC a haU
    rw [hap, show p * a * a⁻¹ * p⁻¹ = 1 by group]
    exact (omegaTwoSub B).one_mem
  have hA' : conjSubgroup p A ∈ Lam M B := Lam.conj_mem hA hpM
  have hAB' : conjSubgroup p A ≠ omegaOneSub B := by
    intro heq
    apply hAB
    have h1 : conjSubgroup p⁻¹ (conjSubgroup p A) = A := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have h2 : conjSubgroup p⁻¹ (omegaOneSub B) = omegaOneSub B :=
      conjSubgroup_eq_self_iff.mpr (Pair.le_normalizer_B0 h (M.inv_mem hpM))
    rw [← h1, heq, h2]
  have he : p * a⁻¹ * p⁻¹ ∈ conjSubgroup p A := by
    rw [mem_conjSubgroup, show p⁻¹ * (p * a⁻¹ * p⁻¹) * p = a⁻¹ by group]
    exact A.inv_mem ha
  have hzeq : a * p * a⁻¹ * p⁻¹ = a * (p * a⁻¹ * p⁻¹) := by group
  rw [hzeq] at hz ⊢
  by_cases hAA' : conjSubgroup p A = A
  · have hzA : a * (p * a⁻¹ * p⁻¹) ∈ A := A.mul_mem ha (hAA' ▸ he)
    have h1 : a * (p * a⁻¹ * p⁻¹) ∈ A ⊓ Subgroup.centralizer (omegaTwoSub B : Set G) :=
      ⟨hzA, hz⟩
    rw [Pair.inf_centralizer_eq_bot hCen hU hW h hA hAB, Subgroup.mem_bot] at h1
    rw [h1]
    exact (omegaTwoSub B).one_mem
  by_cases hcomm : ∀ x ∈ A, ∀ y ∈ conjSubgroup p A, x * y = y * x
  · have := Pair.mul_mem_B0_of_commute hCen hU hW h hA hA' (Ne.symm hAA') hcomm ha he hz
    exact Pair.B0_le_U h this
  · obtain ⟨S, hAS, hQS⟩ := exists_sylow_ge h hA
    have hA'S : conjSubgroup p A ≤ (S : Subgroup M).map M.subtype := by
      intro x hx
      rw [mem_conjSubgroup] at hx
      have hxA := hAS hx
      have hpS := hQS hpQ
      have := ((S : Subgroup M).map M.subtype).mul_mem
        (((S : Subgroup M).map M.subtype).mul_mem hpS hxA)
        (((S : Subgroup M).map M.subtype).inv_mem hpS)
      rwa [show p * (p⁻¹ * x * p) * p⁻¹ = x by group] at this
    obtain ⟨-, hsup⟩ := hF G M B h S A (conjSubgroup p A) hA hA' hAS hA'S hcomm
    have hzsup : a * (p * a⁻¹ * p⁻¹) ∈ conjSubgroup p A ⊔ omegaTwoSub B := by
      rw [← hsup]
      exact Subgroup.mul_mem_sup ha he
    rw [sup_comm] at hzsup
    obtain ⟨u, hu, a₂, ha₂, hz2⟩ := exists_mul_of_mem_sup
      (fun x hx => Pair.le_normalizer_U h (Lam.le_M hA' hx)) hzsup
    have hu1 : u⁻¹ ∈ Subgroup.centralizer (omegaTwoSub B : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun w hw =>
        (Pair.comm_U h _ (Subgroup.inv_mem _ hu) w hw).symm
    have ha₂C : a₂ ∈ Subgroup.centralizer (omegaTwoSub B : Set G) := by
      have : a₂ = u⁻¹ * (a * (p * a⁻¹ * p⁻¹)) := by rw [hz2]; group
      rw [this]
      exact Subgroup.mul_mem _ hu1 hz
    have h1 : a₂ ∈ conjSubgroup p A ⊓ Subgroup.centralizer (omegaTwoSub B : Set G) :=
      ⟨ha₂, ha₂C⟩
    rw [Pair.inf_centralizer_eq_bot hCen hU hW h hA' hAB', Subgroup.mem_bot] at h1
    rw [hz2, h1, mul_one]
    exact hu

theorem iSup_lam_le_Q : (⨆ A ∈ Lam M B, A) ≤ inSubgroup (pCore 2) M := by
  set W := ⨆ A ∈ Lam M B, A with hWdef
  have hSt : W ≤ stabSeries M
      (inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (omegaTwoSub B : Set G))
      (omegaTwoSub B) (omegaOneSub B) (Pair.le_normalizer_U h) (Pair.le_normalizer_B0 h) := by
    refine iSup₂_le fun A hA a ha => ?_
    exact ⟨Lam.le_M hA ha, fun p hp => comm_P_mem_U hCen hU hW hF h hA ha hp,
      fun u hu => comm_U_mem_B0 h hA ha hu, fun b hb => R2.comm_B0 h hA a ha b hb⟩
  have hWM : W ≤ M := iSup₂_le fun A hA => Lam.le_M hA
  have hW2 : IsPGroup 2 ↥W := by
    intro w
    obtain ⟨a, ha, hex⟩ := exists_odd_orderOf_pow (w : G)
    have hwSt := Subgroup.pow_mem _ (hSt w.2) (2 ^ a)
    have h1 : (w : G) ^ 2 ^ a = 1 := eq_one_of_mem_stabSeries h hwSt ha
    obtain ⟨k, hk⟩ := hex h1
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hconj : ∀ m ∈ M, conjSubgroup m W ≤ W := by
    intro m hm
    rw [conjSubgroup, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂ (f := fun A (_ : A ∈ Lam M B) => A) (conjSubgroup m A) (Lam.conj_mem hA hm)
  have hWN : M ≤ Subgroup.normalizer (W : Set G) := by
    intro m hm
    rw [← conjSubgroup_eq_self_iff]
    refine le_antisymm (hconj m hm) ?_
    have h' := hconj m⁻¹ (M.inv_mem hm)
    intro w hw
    have : m⁻¹ * w * m ∈ W := h' (by
      rw [mem_conjSubgroup, inv_inv, show m * (m⁻¹ * w * m) * m⁻¹ = w by group]
      exact hw)
    rw [mem_conjSubgroup]
    exact this
  exact le_inSubgroup_pCore hWM hWN hW2

theorem lam_le_Q {A : Subgroup G} (hA : A ∈ Lam M B) : A ≤ inSubgroup (pCore 2) M :=
  (le_iSup₂ (f := fun A (_ : A ∈ Lam M B) => A) A hA).trans (iSup_lam_le_Q hCen hU hW hF h)

theorem isPGroup_iSup : IsPGroup 2 ↥(⨆ A ∈ Lam M B, A) :=
  (inSubgroup_pCore_two M).1.to_le (iSup_lam_le_Q hCen hU hW hF h)

theorem commutator_lam_le {F E : Subgroup G} (hF' : F ∈ Lam M B) (hE : E ∈ Lam M B) :
    ⁅F, E⁆ ≤ omegaOneSub B := by
  obtain ⟨S, -, hQS⟩ := exists_sylow_ge h hF'
  by_cases hc : ∀ f ∈ F, ∀ e ∈ E, f * e = e * f
  · refine Subgroup.commutator_le.mpr fun f hf e he => ?_
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc f hf e he)]
    exact (omegaOneSub B).one_mem
  · exact (hF G M B h S F E hF' hE ((lam_le_Q hCen hU hW hF h hF').trans hQS)
      ((lam_le_Q hCen hU hW hF h hE).trans hQS) hc).1.le

theorem commutator_iSup_le :
    ⁅⨆ A ∈ Lam M B, A, ⨆ A ∈ Lam M B, A⁆ ≤ omegaOneSub B := by
  set W := ⨆ A ∈ Lam M B, A with hWdef
  have hWcl : W = Subgroup.closure (⋃ A ∈ Lam M B, (A : Set G)) := by
    apply le_antisymm
    · exact iSup₂_le fun A hA x hx => Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨A, hA, hx⟩)
    · refine (Subgroup.closure_le _).mpr fun x hx => ?_
      obtain ⟨A, hA, hxA⟩ := Set.mem_iUnion₂.mp hx
      exact le_iSup₂ (f := fun A (_ : A ∈ Lam M B) => A) A hA hxA
  have hWc : ∀ w ∈ W, ∀ b ∈ omegaOneSub B, w * b = b * w := by
    intro w hw b hb
    have hle : W ≤ Subgroup.centralizer (omegaOneSub B : Set G) :=
      iSup₂_le fun A hA a ha => Subgroup.mem_centralizer_iff.2 fun b hb =>
        (R2.comm_B0 h hA a ha b hb).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) b hb).symm
  have hcl : ∀ w, w ∈ Subgroup.closure (⋃ A ∈ Lam M B, (A : Set G)) → w ∈ W := fun w hw => by
    rw [hWcl]
    exact hw
  have hconj : ∀ w ∈ W, ∀ b ∈ omegaOneSub B, w * b * w⁻¹ = b := fun w hw b hb => by
    rw [hWc w hw b hb]
    group
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [hWcl] at hx hy
  refine Subgroup.closure_induction₂
    (p := fun x y _ _ => ⁅x, y⁆ ∈ omegaOneSub B) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro x y hx hy
    obtain ⟨F, hF', hxF⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨E, hE, hyE⟩ := Set.mem_iUnion₂.mp hy
    exact commutator_lam_le hCen hU hW hF h hF' hE (Subgroup.commutator_mem_commutator hxF hyE)
  · intro x hx
    rw [show ⁅(1 : G), x⁆ = 1 by simp [commutatorElement_def]]
    exact (omegaOneSub B).one_mem
  · intro x hx
    rw [show ⁅x, (1 : G)⁆ = 1 by simp [commutatorElement_def]]
    exact (omegaOneSub B).one_mem
  · intro x y z hx hy hz ih₁ ih₂
    have e : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, hconj x (hcl x hx) _ ih₂]
    exact (omegaOneSub B).mul_mem ih₂ ih₁
  · intro y z x hy hz hx ih₁ ih₂
    have e : ⁅x, y * z⁆ = ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ := by
      simp only [commutatorElement_def]
      group
    have h3 : y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ := hconj y (hcl y hy) _ ih₂
    rw [e, show ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) by group, h3]
    exact (omegaOneSub B).mul_mem ih₁ ih₂
  · intro x y hx hy ih
    have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    have h3 : x⁻¹ * ⁅x, y⁆⁻¹ * x = ⁅x, y⁆⁻¹ := by
      have := hconj x⁻¹ (W.inv_mem (hcl x hx)) _ ((omegaOneSub B).inv_mem ih)
      rwa [inv_inv] at this
    rw [e, h3]
    exact (omegaOneSub B).inv_mem ih
  · intro x y hx hy ih
    have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
      simp only [commutatorElement_def]
      group
    have h3 : y⁻¹ * ⁅x, y⁆⁻¹ * y = ⁅x, y⁆⁻¹ := by
      have := hconj y⁻¹ (W.inv_mem (hcl y hy)) _ ((omegaOneSub B).inv_mem ih)
      rwa [inv_inv] at this
    rw [e, h3]
    exact (omegaOneSub B).inv_mem ih

end Main

end CFSG.CGT.PushingUpLit.SolKR2
