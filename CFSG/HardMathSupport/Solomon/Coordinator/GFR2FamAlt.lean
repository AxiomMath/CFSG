module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamPerm
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamAlt
public import CFSG.HardMathSupport.Solomon.Coordinator.GapFinalDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator Equiv Equiv.Perm
open scoped commutatorElement

theorem false_of_perfect_center_three {X : Type*} [Group X] (hperf : commutator X = ⊤)
    (hZ : Nat.card (Subgroup.center X) = 3) (h : IsSimpleGroup X ∨ Subsingleton X) : False := by
  rcases h with hs | hs
  · rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with hb | ht
    · rw [hb, Subgroup.card_bot] at hZ
      omega
    · have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.1 (ht ▸ Subgroup.mem_top b) a)
      have hsub : Subsingleton X := by
        refine ⟨fun a b => ?_⟩
        have htop : ∀ z : X, z = 1 := by
          intro z
          have hz : z ∈ commutator X := hperf ▸ Subgroup.mem_top z
          have hbot : commutator X = ⊥ := by
            refine le_bot_iff.1 ?_
            rw [commutator]
            refine Subgroup.commutator_le.2 fun x _ y _ => ?_
            rw [Subgroup.mem_bot]
            exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm x y)
          rw [hbot] at hz
          exact hz
        rw [htop a, htop b]
      have : Nat.card (Subgroup.center X) = 1 := by
        haveI : Subsingleton (Subgroup.center X) := ⟨fun a b => Subtype.ext (hsub.elim _ _)⟩
        exact Nat.card_of_subsingleton (1 : Subgroup.center X)
      omega
  · have : Nat.card (Subgroup.center X) = 1 := by
      haveI : Subsingleton (Subgroup.center X) := ⟨fun a b => Subtype.ext (hs.elim _ _)⟩
      exact Nat.card_of_subsingleton (1 : Subgroup.center X)
    omega

theorem not_type_of_simple {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y} (hs : IsSimpleGroup ↥J)
    (hty : IsHatON (barOf 3 J) ∨ IsHatSix (barOf 3 J)) : False := by
  have hperf : commutator (barOf 3 J) = ⊤ := by
    rcases hty with h | h
    · exact h.1
    · exact h.1
  have hZ : Nat.card (Subgroup.center (barOf 3 J)) = 3 := by
    rcases hty with h | h
    · exact h.2.1
    · exact h.2.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥J) with hb | ht
  · have e : barOf 3 J ≃* ↥J :=
      (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
    haveI := hs
    exact false_of_perfect_center_three hperf hZ (Or.inl e.isSimpleGroup)
  · refine false_of_perfect_center_three hperf hZ (Or.inr ?_)
    have : Subsingleton (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
      rw [ht]
      exact QuotientGroup.subsingleton_quotient_top
    exact this

theorem odd_card_center_of_core_bot {Y : Type} [Group Y] [Finite Y]
    (hcore : GLAPPrimeCore 3 Y = ⊥) : Odd (Nat.card (Subgroup.center Y)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center Y) := by
    rw [Nat.not_odd_iff_even] at hodd
    exact even_iff_two_dvd.1 hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set N : Subgroup Y := Subgroup.zpowers (t : Y) with hN
  have hNc : N ≤ Subgroup.center Y := Subgroup.zpowers_le.2 t.2
  haveI : N.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hNc hn) g
    rw [show g * n * g⁻¹ = n by rw [this]; group]
    exact hn⟩
  have hcard : Nat.card N = 2 := by
    rw [hN, Nat.card_zpowers, Subgroup.orderOf_coe, ht]
  have hle : N ≤ GLAPPrimeCore 3 Y :=
    le_sSup (show N ∈ {M : Subgroup Y | M.Normal ∧ Nat.Coprime 3 (Nat.card M)} from
      ⟨inferInstance, by rw [hcard]; norm_num⟩)
  rw [hcore] at hle
  have h1 : (t : Y) = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers _))
  have : t = 1 := Subtype.ext h1
  rw [this, orderOf_one] at ht
  omega

theorem card_ge_fixed_add_three {Ω : Type} [Fintype Ω] [DecidableEq Ω] {σ : Perm Ω}
    (hσ : σ ^ 3 = 1) (h1 : σ ≠ 1) : Nat.card (Function.fixedPoints σ) + 3 ≤ Nat.card Ω := by
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact h1 (Equiv.ext h)
  have hσa : σ (σ a) ≠ σ a := fun h => ha (σ.injective h)
  have hσσa : σ (σ (σ a)) = a := by
    have := congrArg (fun f : Perm Ω => f a) hσ
    simpa [pow_succ] using this
  have hσσ : σ (σ a) ≠ a := by
    intro h
    have : σ a = a := by
      have h2 := congrArg σ h
      rw [hσσa] at h2
      exact h2.symm
    exact ha this
  have hsub : ({a, σ a, σ (σ a)} : Finset Ω) ⊆ Finset.univ.filter (fun x => σ x ≠ x) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hσa
    · intro h
      exact hσσ (h.symm.trans hσσa)
  have h3 : ({a, σ a, σ (σ a)} : Finset Ω).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact fun h => hσa h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha h.symm, fun h => hσσ h.symm⟩
  have h4 : 3 ≤ (Finset.univ.filter (fun x => σ x ≠ x)).card := h3 ▸ Finset.card_le_card hsub
  have h5 : (Finset.univ.filter (fun x => σ x = x)).card +
      (Finset.univ.filter (fun x => σ x ≠ x)).card = Fintype.card Ω := by
    rw [Finset.card_filter_add_card_filter_not]; simp
  have h6 : Nat.card (Function.fixedPoints σ) = (Finset.univ.filter (fun x => σ x = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [h6, Nat.card_eq_fintype_card]
  omega

theorem gapFinalPumpupAlt_holds :
    ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → CFSG.Open.IsKGroup Y →
      GLAPPrimeCore 3 Y = ⊥ →
      (∃ (n : ℕ) (hn : 5 ≤ n),
        Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.alternating n hn).Group)) →
      ∀ x : MulAut Y, orderOf x = 3 →
        ∀ J₁ : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub x) J₁ →
          (IsHatON (barOf 3 J₁) ∨ IsHatSix (barOf 3 J₁)) →
            IsHatON Y ∨ IsHatSix Y ∨ IsMJRType Y := by
  intro Y _ _ hq hKg hcore ⟨n, hn, ⟨e⟩⟩ x hxo J₁ hJ₁ hty
  exfalso
  have hp : Nat.Prime 3 := Nat.prime_three
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hperf : commutator Y = ⊤ := hq.1
  let π : Y →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker ≤ Subgroup.center Y := by
    intro k hk
    have h1 : e (QuotientGroup.mk' (Subgroup.center Y) k) = e 1 := by
      rw [map_one]; exact MonoidHom.mem_ker.1 hk
    exact (QuotientGroup.eq_one_iff k).1 (e.injective h1)
  obtain ⟨β, hβdef⟩ : ∃ β : MulAut (alternatingGroup (Fin n)),
      β = MulAut.congr e (autCenterQuot Y x) := ⟨_, rfl⟩
  have hαβ : ∀ k, π (x k) = β (π k) := fun k => by
    rw [hβdef]
    show π (x k) = e ((autCenterQuot Y x) (e.symm (π k)))
    have h1 : e.symm (π k) = (QuotientGroup.mk k : Y ⧸ Subgroup.center Y) := e.symm_apply_apply _
    rw [h1]
    rfl
  have hβp : β ^ 3 = 1 := by
    rw [hβdef, ← map_pow (MulAut.congr e), ← map_pow (autCenterQuot Y), hx3, map_one, map_one]
  obtain ⟨σ, hσβ, hσ3⟩ := exists_perm_of_pow_prime hp (by norm_num) n hn β hβp
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, map_one] at hσβ
    have h1 : autCenterQuot Y x = 1 := by
      have : MulAut.congr e (autCenterQuot Y x) = 1 := by rw [← hβdef, ← hσβ]
      ext q
      have := congrArg (fun γ : MulAut (alternatingGroup (Fin n)) => γ (e q)) this
      simpa using this
    have h2 : x = 1 := autCenterQuot_injective_of_perfect hperf (by rw [h1, map_one])
    rw [h2, orderOf_one] at hxo
    omega
  have hJ₁' : GLAPComponent 3 (fixSubgroup x) J₁ := hJ₁
  have hJβ : GLAPComponent 3 (fixSubgroup β) (J₁.map π) :=
    glaPComponent_map_fixSubgroup π hker x β hαβ hπ hp hJ₁'
  have hA : CFSG.Open.IsQuasisimple ↥(J₁.map π) :=
    isQuasisimple_of_glaPComponent_of_comm hp hJβ
      (fun g hg o ho => coreA hp (by norm_num) hn β hβp _ hJβ g hg o ho)
  set ι : ↥(alternatingGroup (Fin n)) →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype with hι
  have hιinj : Function.Injective ι := Subgroup.subtype_injective _
  have hX : (fixSubgroup β).map ι = B3FamAlt.centAlt σ := by
    rw [← hσβ]; exact fixSubgroup_conjNormal_map σ
  have hc : ∀ y ∈ fixSubgroup β ⊓ ι.ker, ∀ z ∈ fixSubgroup β, z * y = y * z := by
    intro y hy z _
    have : y = 1 := hιinj ((MonoidHom.mem_ker.1 hy.2).trans (map_one ι).symm)
    rw [this, mul_one, one_mul]
  have hJ' : GLAPComponent 3 (B3FamAlt.centAlt σ) ((J₁.map π).map ι) := by
    rw [← hX]
    exact glaPComponent_map_central hp ι hc hJβ
  have hq' : CFSG.Open.IsQuasisimple ↥((J₁.map π).map ι) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      ((J₁.map π).equivMapOfInjective ι hιinj) hA
  obtain ⟨h5, ⟨eJ⟩⟩ := alt_component_struct hσ3 hJ'.1 hJ'.2.1 hq'
  have hn8 : 8 ≤ n := by
    have := card_ge_fixed_add_three hσ3 hσ1
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this h5
    omega
  have hodd := odd_card_center_of_core_bot hcore
  have hperf' : Group.IsPerfect Y := ⟨hperf⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hkerodd : Odd (Nat.card π.ker) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hker)
  have hk1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega) π hπ hker hkerodd
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ hk1
  have eJ₁ : ↥J₁ ≃* alternatingGroup (Function.fixedPoints σ) :=
    ((J₁.equivMapOfInjective π hπinj).trans ((J₁.map π).equivMapOfInjective ι hιinj)).trans eJ
  haveI : IsSimpleGroup (alternatingGroup (Function.fixedPoints σ)) :=
    alternatingGroup.isSimpleGroup h5
  haveI : IsSimpleGroup ↥J₁ := eJ₁.isSimpleGroup
  exact not_type_of_simple inferInstance hty

end CFSG.HardMathSupport.Solomon.Coordinator
