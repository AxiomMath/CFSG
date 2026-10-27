module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

open Subgroup MulAction
open CFSG.GH74.GLS.Stage2.Signalizer.L53 (IsChiefPair)
open scoped commutatorElement

section Critical

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_critical {P : Subgroup G} (hPn : P.Normal) (hPp : IsPGroup p P) :
    ∃ A : Subgroup G, A.Normal ∧ A ≤ P ∧ ⁅P, A⁆ ≤ A ⊓ centralizer (A : Set G) ∧
      P ⊓ centralizer (A : Set G) ≤ A := by
  obtain ⟨C, hC⟩ := (CFSG.SectionRank.Ccomm.thompson_critical_subgroup hPp).1
  obtain ⟨hchar, -, hcomm, hcen⟩ := hC
  refine ⟨C.map P.subtype, ?_, map_subtype_le C, ?_, ?_⟩
  · refine ⟨?_⟩
    intro a ha m
    obtain ⟨c, hc, rfl⟩ := ha
    have h := CFSG.SectionRank.Ccomm.char_apply_mem hchar (MulAut.conjNormal (H := P) m) hc
    exact ⟨_, h, by simp [MulAut.conjNormal_apply]⟩
  · rw [Subgroup.commutator_le]
    intro t ht a ha
    obtain ⟨c, hc, rfl⟩ := ha
    have h1 : ⁅(⟨t, ht⟩ : ↥P), c⁆ ∈ C ⊓ centralizer (C : Set ↥P) :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hc)
    refine Subgroup.mem_inf.mpr ⟨⟨_, (Subgroup.mem_inf.mp h1).1, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro a' ⟨c', hc', rfl⟩
    have h2 := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h1).2) c' hc'
    exact congrArg Subtype.val h2
  · rintro t ⟨htT, htc⟩
    have h1 : (⟨t, htT⟩ : ↥P) ∈ centralizer (C : Set ↥P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have := (Subgroup.mem_centralizer_iff.mp htc) (c : G) ⟨c, hc, rfl⟩
      exact Subtype.ext this
    rw [hcen] at h1
    exact ⟨_, (Subgroup.mem_inf.mp h1).1, rfl⟩

theorem comm_comm_eq_bot_of_critical {P A : Subgroup G} (hAP : A ≤ P)
    (hPA : ⁅P, A⁆ ≤ A ⊓ centralizer (A : Set G)) : ⁅⁅A, A⁆, A⁆ = ⊥ := by
  have h1 : ⁅A, A⁆ ≤ centralizer (A : Set G) :=
    ((Subgroup.commutator_mono_left hAP).trans hPA).trans inf_le_right
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1

end Critical

section TransferPow

variable {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A]

theorem transfer_eq_pow_of_conj [H.FiniteIndex] (ϕ : H →* A) (g : G) (hg : g ∈ H)
    (key : ∀ (k : ℕ) (g₀ : G) (h : g₀⁻¹ * g ^ k * g₀ ∈ H),
      ϕ ⟨g₀⁻¹ * g ^ k * g₀, h⟩ = ϕ ⟨g ^ k, H.pow_mem hg k⟩) :
    ϕ.transfer g = ϕ ⟨g, hg⟩ ^ H.index := by
  classical
  letI : Fintype (Quotient (orbitRel (zpowers g) (G ⧸ H))) := Fintype.ofFinite _
  rw [index_eq_sum_minimalPeriod H g, ← Finset.prod_pow_eq_pow_sum,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [key, ← map_pow]
  congr 1

end TransferPow

section StepIV

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

open scoped IsMulCommutative in
theorem commutator_inf_le_of_conj (S : Sylow p G) {T₀ P : Subgroup G} (hT₀S : T₀ ≤ S)
    (hST : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ T₀) (hPS : P ≤ S)
    (hconj : ∀ x ∈ P, ∀ m : G, m⁻¹ * x * m ∈ P ∧ x⁻¹ * (m⁻¹ * x * m) ∈ T₀) :
    commutator G ⊓ P ≤ T₀ := by
  set K : Subgroup ↥(S : Subgroup G) := T₀.subgroupOf S with hK
  haveI hKn : K.Normal := by
    refine ⟨fun k hk s => ?_⟩
    have e : ((s * k * s⁻¹ : ↥(S : Subgroup G)) : G) = ⁅(s : G), (k : G)⁆ * k := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
    show ((s * k * s⁻¹ : ↥(S : Subgroup G)) : G) ∈ T₀
    rw [e]
    exact T₀.mul_mem (hST (Subgroup.commutator_mem_commutator s.2 k.2)) hk
  haveI : IsMulCommutative (↥(S : Subgroup G) ⧸ K) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
    intro x hx
    have : (x : G) ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆ := by
      rw [← map_subtype_commutator]
      exact ⟨x, hx, rfl⟩
    exact hST this
  let ϕ : ↥(S : Subgroup G) →* ↥(S : Subgroup G) ⧸ K := QuotientGroup.mk' K
  rintro x ⟨hxc, hxP⟩
  have hxS : x ∈ (S : Subgroup G) := hPS hxP
  have h1 : ϕ.transfer x = 1 := Abelianization.commutator_subset_ker _ hxc
  have h2 : ϕ.transfer x = ϕ ⟨x, hxS⟩ ^ (S : Subgroup G).index := by
    refine transfer_eq_pow_of_conj ϕ x hxS fun k g₀ h => ?_
    refine (QuotientGroup.eq.mpr ?_).symm
    show (x ^ k)⁻¹ * (g₀⁻¹ * x ^ k * g₀) ∈ T₀
    exact (hconj _ (P.pow_mem hxP k) g₀).2
  rw [h1] at h2
  have hQp : IsPGroup p (↥(S : Subgroup G) ⧸ K) := S.isPGroup'.to_quotient K
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQp) (ϕ ⟨x, hxS⟩)
  have hdvd : orderOf (ϕ ⟨x, hxS⟩) ∣ (S : Subgroup G).index := orderOf_dvd_of_pow_eq_one h2.symm
  rw [hk] at hdvd
  have hcop : Nat.Coprime (p ^ k) (S : Subgroup G).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr S.not_dvd_index)
  have hk1 : p ^ k = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  rw [hk1, orderOf_eq_one_iff] at hk
  have : (⟨x, hxS⟩ : ↥(S : Subgroup G)) ∈ K := (QuotientGroup.eq_one_iff _).mp hk
  exact this

end StepIV

section Exponent

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem chief_pow_mem {P X Y : Subgroup G} (hPn : P.Normal) (hPp : IsPGroup p P) (hYP : Y ≤ P)
    (hc : IsChiefPair Y X) : ∀ y ∈ Y, y ^ p ∈ X := by
  classical
  have hYn : Y.Normal := hc.1
  have hXn : X.Normal := hc.2.1
  have hXY : X < Y := hc.2.2.1
  have hYY : ⁅Y, Y⁆ ≤ X := comm_self_le_of_chief hPp.isNilpotent hPn hYP hc
  have hcommX : ∀ a ∈ Y, ∀ b ∈ Y,
      Commute (QuotientGroup.mk' X a) (QuotientGroup.mk' X b) := by
    intro a ha b hb
    have h : QuotientGroup.mk' X ⁅a, b⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hYY (Subgroup.commutator_mem_commutator ha hb))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  let W₀ : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ y ^ p ∈ X}
      mul_mem' := by
        rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
        refine ⟨Y.mul_mem ha hb, ?_⟩
        have h : QuotientGroup.mk' X ((a * b) ^ p) = 1 := by
          rw [map_pow, map_mul, (hcommX a ha b hb).mul_pow, ← map_pow, ← map_pow,
            QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
            (QuotientGroup.eq_one_iff _).mpr hap, (QuotientGroup.eq_one_iff _).mpr hbp, mul_one]
        rw [QuotientGroup.mk'_apply] at h
        exact (QuotientGroup.eq_one_iff _).mp h
      one_mem' := ⟨Y.one_mem, by rw [one_pow]; exact X.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, hap⟩
        exact ⟨Y.inv_mem ha, by rw [inv_pow]; exact X.inv_mem hap⟩ }
  have hW₀n : W₀.Normal := by
    refine ⟨fun y hy c => ⟨hYn.conj_mem y hy.1 c, ?_⟩⟩
    have e : (c * y * c⁻¹) ^ p = c * y ^ p * c⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
    rw [e]
    exact hXn.conj_mem _ hy.2 c
  have hXW₀ : X ≤ W₀ := fun x hx => ⟨hXY.le hx, X.pow_mem hx p⟩
  have hW₀Y : W₀ ≤ Y := fun y hy => hy.1
  have hW₀X : W₀ ≠ X := by
    intro heq
    obtain ⟨y, hyY, hyX⟩ := SetLike.exists_of_lt hXY
    have hex : ∃ k, y ^ p ^ k ∈ X := by
      obtain ⟨k, hk⟩ := hPp ⟨y, hYP hyY⟩
      refine ⟨k, ?_⟩
      have : y ^ p ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      rw [this]
      exact X.one_mem
    have hk0 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, pow_one] at this
      exact hyX this
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hz : y ^ p ^ k ∈ W₀ := by
      refine ⟨Y.pow_mem hyY _, ?_⟩
      have := Nat.find_spec hex
      rw [hk, pow_succ, pow_mul] at this
      exact this
    have hzX : y ^ p ^ k ∉ X := Nat.find_min hex (by omega)
    rw [heq] at hz
    exact hzX hz
  rcases hc.2.2.2 W₀ hW₀n hXW₀ hW₀Y with h | h
  · exact absurd h hW₀X
  · intro y hy
    rw [← h] at hy
    exact hy.2

end Exponent

section Hyp

variable {G : Type*} [Group G]

theorem hypQ_of_ab {A : Subgroup G} (hZn : (A ⊓ centralizer (A : Set G)).Normal) {g : G}
    (ha : ∀ x ∈ A, iterComm x g 3 ∈ A ⊓ centralizer (A : Set G))
    (hb : ∀ z ∈ A ⊓ centralizer (A : Set G), iterComm z g 2 = 1) :
    ∀ X Y : Subgroup G, IsChiefPair X Y → X ≤ A → ∀ x ∈ X, iterComm x g 3 ∈ Y := by
  intro X Y hc hXA
  have hXn := hc.1
  have hYn := hc.2.1
  have hWn : ((X ⊓ (A ⊓ centralizer (A : Set G))) ⊔ Y).Normal := inferInstance
  rcases hc.2.2.2 _ hWn le_sup_right (sup_le inf_le_left hc.2.2.1.le) with h | h
  · intro x hx
    have h4 : iterComm x g 3 ∈ X ⊓ (A ⊓ centralizer (A : Set G)) :=
      Subgroup.mem_inf.mpr ⟨iterComm_mem hXn hx g 3, ha x (hXA hx)⟩
    have : iterComm x g 3 ∈ (X ⊓ (A ⊓ centralizer (A : Set G))) ⊔ Y := Subgroup.mem_sup_left h4
    rwa [h] at this
  · intro x hx
    have hxW : x ∈ (X ⊓ (A ⊓ centralizer (A : Set G))) ⊔ Y := by rw [h]; exact hx
    rw [Subgroup.mem_sup_of_normal_right] at hxW
    obtain ⟨z, hz, y, hy, rfl⟩ := hxW
    rw [iterComm_mul_mem_iff hYn z hy, iterComm_succ, hb z (Subgroup.mem_inf.mp hz).2,
      commutatorElement_one_left]
    exact Y.one_mem

theorem hypZ_of_ab {A : Subgroup G} {g : G}
    (hb : ∀ z ∈ A ⊓ centralizer (A : Set G), iterComm z g 2 = 1) :
    ∀ X Y : Subgroup G, IsChiefPair X Y → X ≤ A ⊓ centralizer (A : Set G) →
      ∀ x ∈ X, iterComm x g 2 ∈ Y := by
  intro X Y _ hXZ x hx
  rw [hb x (hXZ hx)]
  exact Y.one_mem

end Hyp

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

end
