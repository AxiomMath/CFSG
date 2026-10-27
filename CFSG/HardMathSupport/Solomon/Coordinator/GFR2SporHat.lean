module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltSn
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporGen
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] noncomputable def projOf {Y S : Type*} [Group Y] [Group S]
    (e : (Y ⧸ Subgroup.center Y) ≃* S) : Y →* S :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))

theorem projOf_surjective {Y S : Type*} [Group Y] [Group S] (e : (Y ⧸ Subgroup.center Y) ≃* S) :
    Function.Surjective (projOf e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ker_projOf {Y S : Type*} [Group Y] [Group S] (e : (Y ⧸ Subgroup.center Y) ≃* S) :
    (projOf e).ker = Subgroup.center Y := by
  ext y
  rw [MonoidHom.mem_ker]
  show e (QuotientGroup.mk y) = 1 ↔ _
  rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]

private theorem isSubnormal_map_centralizer_of_surjective {Y S : Type*} [Group Y] [Group S]
    (π : Y →* S) (hsurj : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y)
    (α : MulAut Y) (σ : S) (hπ : ∀ y, π (α y) = σ * π y * σ⁻¹) {J : Subgroup Y}
    (hJ : CFSG.Open.IsSubnormal J (Lemma510Ns.fixSub α)) :
    J.map π ≤ Subgroup.centralizer ({σ} : Set S) ∧
      CFSG.Open.IsSubnormal (J.map π) (Subgroup.centralizer ({σ} : Set S)) := by
  set X := Lemma510Ns.fixSub α with hXdef
  set Cs := Subgroup.centralizer ({σ} : Set S) with hCs
  set T : Subgroup Y := Cs.comap π with hT
  have hXT : X ≤ T := by
    intro y hy
    have hy' : α y = y := hy
    have h1 := hπ y
    rw [hy'] at h1
    show π y ∈ Cs
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc π y * σ = (σ * π y * σ⁻¹) * σ := by rw [← h1]
      _ = σ * π y := by group
  have hN : (X.subgroupOf T).Normal := by
    constructor
    intro x hx t
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hxα : α (x : Y) = x := hx
    have ht : π (t : Y) ∈ Cs := t.2
    have hcomm : σ * π t = π t * σ := (Subgroup.mem_centralizer_singleton_iff.1 ht).symm
    have hz : (t : Y)⁻¹ * α t ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπ]
      rw [hcomm]
      group
    have hzc := Subgroup.mem_center_iff.1 (hker hz)
    show α ((t : Y) * x * (t : Y)⁻¹) = (t : Y) * x * (t : Y)⁻¹
    rw [map_mul, map_mul, map_inv, hxα]
    generalize hzdef : (t : Y)⁻¹ * α t = z at hzc
    have hαt : α (t : Y) = (t : Y) * z := by rw [← hzdef]; group
    rw [hαt]
    have hx' : (x : Y) * z = z * x := hzc x
    calc (t : Y) * z * x * ((t : Y) * z)⁻¹ = (t : Y) * (z * x) * z⁻¹ * (t : Y)⁻¹ := by group
      _ = (t : Y) * (x * z) * z⁻¹ * (t : Y)⁻¹ := by rw [hx']
      _ = (t : Y) * x * (t : Y)⁻¹ := by group
  have h1 : CFSG.Open.IsSubnormal X T := .step hXT hN (.refl T)
  have h3 : CFSG.Open.IsSubnormal (J.map π) (T.map π) :=
    isSubnormal_map_open π (isSubnormal_trans_open hJ h1)
  rw [hT, Subgroup.map_comap_eq_self_of_surjective hsurj] at h3
  exact ⟨le_of_isSubnormal_open h3, h3⟩

theorem hatCfg_of_component (hOut : SporadicOuterLeTwo) {name : TauCeti.SporadicName}
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic name).Group)
    {x : MulAut Y} (hxo : orderOf x = 3) :
    ∃ s : (TauCeti.CFSGIndex.sporadic name).Group, orderOf s = 3 ∧
      ∀ J₁ : Subgroup Y, CFSG.Open.IsSubnormal J₁ (Lemma510Ns.fixSub x) →
        J₁.map (projOf e) ≤ Subgroup.centralizer ({s} : Set _) ∧
        CFSG.Open.IsSubnormal (J₁.map (projOf e)) (Subgroup.centralizer ({s} : Set _)) := by
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hperf : commutator Y = ⊤ := hq.1
  have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq
  have hs := hq.2
  have hcen : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 := hOut _ hs hnab name ⟨e⟩
  have hβ3 : (autCenterQuot Y x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  obtain ⟨s, hsβ, hs3⟩ := exists_conj_of_pow Nat.prime_three (by norm_num) hcen hout
    (autCenterQuot Y x) hβ3
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, map_one] at hsβ
    have h2 : x = 1 := autCenterQuot_injective_of_perfect hperf (by rw [← hsβ, map_one])
    rw [h2, orderOf_one] at hxo
    omega
  have hso : orderOf (e s) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hs3 hs1
  refine ⟨e s, hso, fun J₁ hJ₁ => ?_⟩
  refine isSubnormal_map_centralizer_of_surjective (projOf e) (projOf_surjective e)
    (ker_projOf e ▸ le_rfl) x (e s) (fun y => ?_) hJ₁
  have h1 : (autCenterQuot Y x) (y : Y ⧸ Subgroup.center Y) = (x y : Y ⧸ Subgroup.center Y) := by
    rw [autCenterQuot_mk]
  rw [← hsβ, MulAut.conj_apply] at h1
  show e (QuotientGroup.mk (x y)) = e s * e (QuotientGroup.mk y) * (e s)⁻¹
  rw [← h1, map_mul, map_mul, map_inv]

theorem card_center_le_three (hSpM : SporadicMultipliers) {name : TauCeti.SporadicName}
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hcore : GLAPPrimeCore 3 Y = ⊥)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic name).Group) :
    Nat.card (Subgroup.center Y) ∣ 3 := by
  have hzodd := odd_card_center_of_core_bot hcore
  have hzd := card_center_dvd_mult hSpM hq name e
  rcases odd_dvd_twelve (hzd.trans (sporadicMultiplierOrder_dvd_twelve name)) hzodd with h | h
  · rw [h]; exact one_dvd _
  · rw [h]

theorem center_eq_bot_of_not_three_dvd (hSpM : SporadicMultipliers) {name : TauCeti.SporadicName}
    (hm : ¬ 3 ∣ sporadicMultiplierOrder name)
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hcore : GLAPPrimeCore 3 Y = ⊥)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic name).Group) :
    Subgroup.center Y = ⊥ := by
  have h3 := card_center_le_three hSpM hq hcore e
  have hzd := card_center_dvd_mult hSpM hq name e
  have h1 : Nat.card (Subgroup.center Y) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact h
    · exact absurd (h ▸ hzd) hm
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem card_map_projOf_mul {Y S : Type*} [Group Y] [Group S] [Finite Y]
    (e : (Y ⧸ Subgroup.center Y) ≃* S) (J : Subgroup Y) :
    Nat.card ↥(J.map (projOf e)) * Nat.card ↥(J ⊓ Subgroup.center Y) = Nat.card J := by
  have h := Subgroup.card_ker_mul_card_range ((projOf e).domRestrict J)
  rw [MonoidHom.restrict_range] at h
  have hk : Nat.card ((projOf e).domRestrict J).ker = Nat.card ↥(J ⊓ Subgroup.center Y) := by
    rw [MonoidHom.ker_restrict, ker_projOf]
    exact Nat.card_congr
      { toFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, b.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hk] at h
  rw [mul_comm]
  exact h

end CFSG.HardMathSupport.Solomon.Coordinator
