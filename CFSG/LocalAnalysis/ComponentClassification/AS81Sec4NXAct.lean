module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4NXCoord
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step41
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step46

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Hexa CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native HeSylow

section Conj

variable {G : Type} [Group G]

@[expose] def conjX (X : Subgroup G) : ↥(normalizer (X : Set G)) →* Equiv.Perm ↥X where
  toFun n :=
    { toFun := fun x => ⟨n * x * (n : G)⁻¹, (mem_normalizer_iff.mp n.2 x).mp x.2⟩
      invFun := fun x => ⟨(n : G)⁻¹ * x * n, by
        have h := (mem_normalizer_iff.mp (inv_mem n.2) x).mp x.2
        rwa [inv_inv] at h⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
  map_one' := Equiv.ext fun x => Subtype.ext (by simp)
  map_mul' n m := Equiv.ext fun x => Subtype.ext (by simp [mul_assoc])

theorem coe_conjX_apply (X : Subgroup G) (n : ↥(normalizer (X : Set G))) (x : ↥X) :
    (conjX X n x : G) = n * x * (n : G)⁻¹ := rfl

end Conj

namespace HexaCoord

variable {G : Type} [Group G] {X R : Subgroup G} {pts : Set (Subgroup G)} {rep : Fin 64 → G}
variable (hc : HexaCoord X R pts rep)
include hc

@[expose] noncomputable def equiv : Fin 64 ≃ ↥X :=
  Equiv.ofBijective (fun v => ⟨rep v, hc.mem v⟩)
    ⟨fun _ _ h => hc.inj (congrArg Subtype.val h), fun x => by
      obtain ⟨v, hv⟩ := hc.surj x.1 x.2
      exact ⟨v, Subtype.ext hv⟩⟩

theorem coe_equiv (v : Fin 64) : (hc.equiv v : G) = rep v := rfl

theorem rep_symm (x : ↥X) : rep (hc.equiv.symm x) = x :=
  congrArg Subtype.val (hc.equiv.apply_symm_apply x)

theorem rep_zero : rep 0 = 1 := by
  have h := hc.add 0 0
  rw [xorF_self] at h
  exact left_eq_mul.mp h

theorem symm_one : hc.equiv.symm 1 = 0 :=
  hc.equiv.symm_apply_eq.mpr (Subtype.ext hc.rep_zero.symm)

theorem symm_mul (x y : ↥X) :
    hc.equiv.symm (x * y) = xorF (hc.equiv.symm x) (hc.equiv.symm y) := by
  refine hc.equiv.symm_apply_eq.mpr (Subtype.ext ?_)
  rw [coe_equiv, hc.add, hc.rep_symm, hc.rep_symm]
  rfl

@[expose] noncomputable def psi : ↥(normalizer (X : Set G)) →* Equiv.Perm (Fin 64) :=
  (Equiv.permCongrHom hc.equiv.symm).toMonoidHom.comp (conjX X)

theorem psi_apply (n : ↥(normalizer (X : Set G))) (v : Fin 64) :
    hc.psi n v = hc.equiv.symm (conjX X n (hc.equiv v)) := rfl

theorem rep_psi (n : ↥(normalizer (X : Set G))) (v : Fin 64) :
    rep (hc.psi n v) = n * rep v * (n : G)⁻¹ := by
  rw [psi_apply, hc.rep_symm]
  rfl

theorem psi_symm (n : ↥(normalizer (X : Set G))) (x : ↥X) :
    hc.psi n (hc.equiv.symm x) = hc.equiv.symm (conjX X n x) := by
  rw [psi_apply, Equiv.apply_symm_apply]

theorem psi_add (n : ↥(normalizer (X : Set G))) (v w : Fin 64) :
    hc.psi n (xorF v w) = xorF (hc.psi n v) (hc.psi n w) := by
  apply hc.inj
  rw [hc.rep_psi, hc.add, hc.add, hc.rep_psi, hc.rep_psi]
  group

theorem psi_eq_one_iff (n : ↥(normalizer (X : Set G))) :
    hc.psi n = 1 ↔ (n : G) ∈ centralizer (X : Set G) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨v, rfl⟩ := hc.surj x hx
    have h1 : rep (hc.psi n v) = rep v := by rw [h]; rfl
    rw [hc.rep_psi] at h1
    calc rep v * n = n * rep v * (n : G)⁻¹ * n := by rw [h1]
      _ = n * rep v := by group
  · intro h
    refine Equiv.ext fun v => hc.inj ?_
    rw [hc.rep_psi, ← mem_centralizer_iff.mp h (rep v) (hc.mem v)]
    simp

end HexaCoord

section Plane

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {X Y : Subgroup G}

theorem injective_vec_three {α : Type*} {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

namespace PlaneData

theorem inf_sup_eq_bot (hX : PlaneData G A R g X Y) (hY : PlaneData G A R g Y X)
    {P P' P'' : Subgroup G} (hP : P ∈ pointsIn R X) (hP' : P' ∈ pointsIn R X)
    (hP'' : P'' ∈ pointsIn R X) (h1 : P ≠ P') (h2 : P ≠ P'') (h3 : P' ≠ P'') :
    P'' ⊓ (P ⊔ P') = ⊥ := by
  obtain ⟨Q, hQ, hQV, -⟩ := hX.exists_point
  have hQ4 : Nat.card Q = 4 := by
    obtain ⟨-, x, rfl⟩ := hQ
    rw [rightConjugate_card, hX.frame.cardR]
  have hQne : ∀ {V : Subgroup G}, V ≤ R ⊔ rightConjugate R g → Q ≠ V := by
    rintro V hV rfl
    have hbot : Q = ⊥ := by
      rw [eq_bot_iff, ← hQV]
      exact le_inf le_rfl hV
    rw [hbot, card_bot] at hQ4
    omega
  have hf : Function.Injective ![(⟨R, hX.R_mem⟩ : ↥(pointsIn R X)), ⟨rightConjugate R g, hX.Rg_mem⟩,
      ⟨Q, hQ⟩] := injective_vec_three (fun h => hX.Rg_ne (congrArg Subtype.val h).symm)
    (fun h => hQne le_sup_left (congrArg Subtype.val h).symm)
    (fun h => hQne le_sup_right (congrArg Subtype.val h).symm)
  have hf' : Function.Injective ![(⟨P, hP⟩ : ↥(pointsIn R X)), ⟨P', hP'⟩, ⟨P'', hP''⟩] :=
    injective_vec_three (fun h => h1 (congrArg Subtype.val h))
      (fun h => h2 (congrArg Subtype.val h)) (fun h => h3 (congrArg Subtype.val h))
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ hf hf'
  obtain ⟨n, -, hn⟩ := hY.inducesSym hX σ
  have e₀ : rightConjugate R n = P := by
    have h := hn ⟨R, hX.R_mem⟩
    rw [show σ ⟨R, hX.R_mem⟩ = ⟨P, hP⟩ from hσ 0] at h
    exact h
  have e₁ : rightConjugate (rightConjugate R g) n = P' := by
    have h := hn ⟨rightConjugate R g, hX.Rg_mem⟩
    rw [show σ ⟨rightConjugate R g, hX.Rg_mem⟩ = ⟨P', hP'⟩ from hσ 1] at h
    exact h
  have e₂ : rightConjugate Q n = P'' := by
    have h := hn ⟨Q, hQ⟩
    rw [show σ ⟨Q, hQ⟩ = ⟨P'', hP''⟩ from hσ 2] at h
    exact h
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
  rw [← e₂] at hx1
  rw [← e₀, ← e₁, ← rightConjugate_sup'] at hx2
  have hm : n * x * n⁻¹ ∈ Q ⊓ (R ⊔ rightConjugate R g) :=
    mem_inf.mpr ⟨(mem_rightConjugate_iff Q n x).mp hx1, (mem_rightConjugate_iff _ n x).mp hx2⟩
  rw [hQV, mem_bot, conj_eq_one_iff] at hm
  exact (mem_bot).mpr hm

theorem exists_hexaCoord' (hS : hexaStabCheck = true) (hX : PlaneData G A R g X Y)
    (hY : PlaneData G A R g Y X) : ∃ rep : Fin 64 → G, HexaCoord X R (pointsIn R X) rep :=
  exists_hexaCoord hS hX.commE hX.sqE hX.frame.cardE (fun _ hP => hP.1)
    (fun P hP => by
      obtain ⟨-, x, rfl⟩ := hP
      rw [rightConjugate_card, hX.frame.cardR])
    (fun _ hP _ hP' _ hP'' h1 h2 h3 => hX.inf_sup_eq_bot hY hP hP' hP'' h1 h2 h3) hX.six hX.R_mem

theorem relIndex_centralizer (hX : PlaneData G A R g X Y) (hY : PlaneData G A R g Y X) :
    (centralizer (X : Set G)).relIndex (normalizer (X : Set G)) = 2160 := by
  classical
  have : Fintype ↥(pointsIn R X) := Fintype.ofFinite _
  obtain ⟨-, -, -, -, -, hK3, -, -⟩ := hX.exists_even
  have hsurj := hY.surjective_pointsAction hX
  have hK' : (ptsKer R X).subgroupOf (normalizer (X : Set G)) = (pointsAction R X).ker :=
    comap_map_eq_self_of_injective (normalizer (X : Set G)).subtype_injective _
  have hKN : (ptsKer R X).relIndex (normalizer (X : Set G)) = 720 := by
    rw [relIndex, hK', index_ker, MonoidHom.range_eq_top.mpr hsurj, card_top, Nat.card_perm,
      hX.six]
    rfl
  have hmul := relIndex_mul_relIndex (centralizer (X : Set G)) (ptsKer R X)
    (normalizer (X : Set G)) centralizer_le_ptsKer ptsKer_le_normalizer
  rw [hK3, hKN] at hmul
  omega

theorem centralizer_subgroupOf_oUpper (hX : PlaneData G A R g X Y)
    (hK : AS76b.oUpperTwoPrime (normalizer (X : Set G)) ⊓
      AS76b.oddCoreIn (centralizer (A : Set G)) = ⊥) :
    (centralizer (X : Set G)).subgroupOf (AS76b.oUpperTwoPrime (normalizer (X : Set G))) =
      X.subgroupOf (AS76b.oUpperTwoPrime (normalizer (X : Set G))) := by
  have hOX : AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (X : Set G) :=
    hX.centralizer_eq ▸ le_sup_right
  have hN : X ≤ normalizer (AS76b.oddCoreIn (centralizer (A : Set G)) : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun o ho =>
      (mem_centralizer_iff.mp (hOX ho) x hx).symm)
  have hXL : X ≤ AS76b.oUpperTwoPrime (normalizer (X : Set G)) :=
    le_oUpper_of_card le_normalizer (n := 6) (by rw [hX.frame.cardE]; norm_num)
  ext ℓ
  rw [mem_subgroupOf, mem_subgroupOf]
  constructor
  · intro h
    rw [hX.centralizer_eq] at h
    have h' : (ℓ : G) ∈ ((X ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) : Subgroup G) : Set G) := h
    rw [coe_mul_of_left_le_normalizer_right X _ hN, Set.mem_mul] at h'
    obtain ⟨x, hx, o, ho, hxo⟩ := h'
    have hoL : o ∈ AS76b.oUpperTwoPrime (normalizer (X : Set G)) := by
      have e : o = x⁻¹ * ℓ := by rw [← hxo, inv_mul_cancel_left]
      rw [e]
      exact mul_mem (inv_mem (hXL hx)) ℓ.2
    have hm : o ∈ AS76b.oUpperTwoPrime (normalizer (X : Set G)) ⊓
        AS76b.oddCoreIn (centralizer (A : Set G)) := mem_inf.mpr ⟨hoL, ho⟩
    rw [hK, mem_bot] at hm
    rw [← hxo, hm, mul_one]
    exact hx
  · intro h
    exact mem_centralizer_iff.mpr fun x hx => hX.commE x hx _ h

omit [Finite G] in
theorem _root_.CFSG.ComponentClassification.AS81.HexaCoord.psi_mem_hexaM
    {rep : Fin 64 → G} (hc : HexaCoord X R (pointsIn R X) rep) (hc15 : hexaCheck = true)
    (hS : hexaStabCheck = true) (n : ↥(normalizer (X : Set G))) : hc.psi n ∈ hexaM := by
  have hlen : hexaOval.length = 6 := rfl
  refine mem_hexaM_of_stab hc15 hS (hc.psi_add n) fun L hL => ?_
  obtain ⟨j, hj, hjL⟩ := List.mem_iff_getElem.1 hL
  rw [hlen] at hj
  obtain ⟨P, hP, hPL⟩ := hc.line j hj
  have hP' := (pointsAction R X n ⟨P, hP⟩).2
  obtain ⟨j', hj', hP'L⟩ := hc.pt _ hP'
  refine ⟨hexaOval[j']!, ?_, fun x hx => ?_⟩
  · rw [getElem!_pos hexaOval j' (by rw [hlen]; exact hj')]
    exact List.getElem_mem _
  · have hjx : x.val ∈ hexaOval[j]! := by
      rw [getElem!_pos hexaOval j (by rw [hlen]; exact hj), hjL]
      exact hx
    have hxP : rep x ∈ P := (hPL x).2 hjx
    refine (hP'L _).1 ?_
    rw [hc.rep_psi, coe_pointsAction_apply, mem_rightConjugate_iff, inv_inv]
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hxP

theorem psi_range (hc15 : hexaCheck = true) (hS : hexaStabCheck = true)
    (hX : PlaneData G A R g X Y) (hY : PlaneData G A R g Y X) {rep : Fin 64 → G}
    (hc : HexaCoord X R (pointsIn R X) rep) : hc.psi.range = hexaM := by
  obtain ⟨-, hM, -⟩ := hexaCheck_parts hc15
  have hle : hc.psi.range ≤ hexaM := by
    rintro _ ⟨n, rfl⟩
    exact hc.psi_mem_hexaM hc15 hS n
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hker : hc.psi.ker = (centralizer (X : Set G)).subgroupOf (normalizer (X : Set G)) := by
    ext n
    rw [MonoidHom.mem_ker, mem_subgroupOf, hc.psi_eq_one_iff]
  rw [card_grpN hM, ← index_ker, hker]
  exact (hX.relIndex_centralizer hY).ge

theorem exists_hexaCoord_Rg (hS : hexaStabCheck = true) (hX : PlaneData G A R g X Y)
    (hY : PlaneData G A R g Y X) : ∃ rep : Fin 64 → G, HexaCoord X R (pointsIn R X) rep ∧
      ∀ v, rep v ∈ rightConjugate R g ↔ v.val ∈ hexaOval[1]! :=
  exists_hexaCoord_two hS hX.commE hX.sqE hX.frame.cardE (fun _ hP => hP.1)
    (fun P hP => by
      obtain ⟨-, x, rfl⟩ := hP
      rw [rightConjugate_card, hX.frame.cardR])
    (fun _ hP _ hP' _ hP'' h1 h2 h3 => hX.inf_sup_eq_bot hY hP hP' hP'' h1 h2 h3) hX.six hX.R_mem
    hX.Rg_mem hX.Rg_ne

theorem mem_oval0_iff_lt : ∀ v : Fin 64, v.val ∈ hexaOval[0]! ↔ v.val < 4 := by decide

theorem nxModel (hc15 : hexaCheck = true) (hS : hexaStabCheck = true)
    (hX : PlaneData G A R g X Y) (hY : PlaneData G A R g Y X) :
    ∃ (ι : ↥X ≃* ↥hexaT) (ψ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))) →* ↥hexaM),
      Function.Surjective ψ ∧
      ψ.ker = (centralizer (X : Set G)).subgroupOf
        (AS76b.oUpperTwoPrime (normalizer (X : Set G))) ∧
      (∀ (ℓ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G)))) (x y : ↥X),
        (y : G) = ℓ * x * (ℓ : G)⁻¹ →
          (ι y : Equiv.Perm (Fin 64)) = ψ ℓ * ι x * (ψ ℓ : Equiv.Perm (Fin 64))⁻¹) ∧
      ∀ x : ↥X, (x : G) ∈ R ↔ (ι x : Equiv.Perm (Fin 64)) ∈ hexaR0 := by
  obtain ⟨rep, hc⟩ := hX.exists_hexaCoord' hS hY
  have hpsiM := hc.psi_mem_hexaM hc15 hS
  have hrange := hX.psi_range hc15 hS hY hc
  have hLN : AS76b.oUpperTwoPrime (normalizer (X : Set G)) ≤ normalizer (X : Set G) :=
    oUpper_le' _
  let ψL : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))) →* Equiv.Perm (Fin 64) :=
    hc.psi.comp (inclusion hLN)
  let ψ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))) →* ↥hexaM :=
    ψL.codRestrict hexaM fun ℓ => hpsiM _
  have hsurj : Function.Surjective ψ := by
    have hle : hexaM ≤ ψL.range := hexaM_le_of_pow_four hc15 hS fun m hm hm4 => by
      rw [← hrange] at hm
      obtain ⟨n, rfl⟩ := hm
      obtain ⟨k, c, hcodd, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (n : G)).ne'
      have hn' : (n : G) ^ (c * c) ∈ AS76b.oUpperTwoPrime (normalizer (X : Set G)) := by
        refine mem_oUpper' (pow_mem n.2 _) (n := k) ?_
        rw [← pow_mul, show c * c * 2 ^ k = 2 ^ k * c * c by ring, pow_mul, ← hk,
          pow_orderOf_eq_one, one_pow]
      refine ⟨⟨_, hn'⟩, ?_⟩
      have e : inclusion hLN ⟨_, hn'⟩ = n ^ (c * c) := rfl
      change hc.psi (inclusion hLN ⟨_, hn'⟩) = hc.psi n
      obtain ⟨j, rfl⟩ := hcodd
      rw [e, map_pow, show (2 * j + 1) * (2 * j + 1) = 4 * (j * j + j) + 1 by ring, pow_succ,
        pow_mul, hm4, one_pow, one_mul]
    intro m
    obtain ⟨ℓ, hℓ⟩ := hle m.2
    exact ⟨ℓ, Subtype.ext hℓ⟩
  have hψker : ψ.ker = (centralizer (X : Set G)).subgroupOf
      (AS76b.oUpperTwoPrime (normalizer (X : Set G))) := by
    ext ℓ
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have h' : hc.psi (inclusion hLN ℓ) = 1 := congrArg Subtype.val h
      exact (hc.psi_eq_one_iff _).1 h'
    · intro h
      exact Subtype.ext ((hc.psi_eq_one_iff (inclusion hLN ℓ)).2 h)
  have hTmem : ∀ v, transl v ∈ hexaT := fun v => by
    rw [hexaT_eq hc15 hS]
    exact ⟨v, rfl⟩
  let ι₀ : ↥X →* ↥hexaT :=
    { toFun := fun x => ⟨transl (hc.equiv.symm x), hTmem _⟩
      map_one' := Subtype.ext (by
        change transl (hc.equiv.symm 1) = 1
        rw [hc.symm_one, transl_zero])
      map_mul' := fun x y => Subtype.ext (by
        change transl (hc.equiv.symm (x * y)) =
          transl (hc.equiv.symm x) * transl (hc.equiv.symm y)
        rw [hc.symm_mul, transl_xorF]) }
  have hι₀ : Function.Bijective ι₀ := by
    refine ⟨fun x y h => ?_, fun t => ?_⟩
    · have h' : transl (hc.equiv.symm x) = transl (hc.equiv.symm y) := congrArg Subtype.val h
      exact hc.equiv.symm.injective (transl_injective h')
    · obtain ⟨t, ht⟩ := t
      have ht' : t ∈ translSub := by
        rw [← hexaT_eq hc15 hS]
        exact ht
      obtain ⟨v, rfl⟩ := ht'
      refine ⟨hc.equiv v, Subtype.ext ?_⟩
      change transl (hc.equiv.symm (hc.equiv v)) = transl v
      rw [Equiv.symm_apply_apply]
  refine ⟨MulEquiv.ofBijective ι₀ hι₀, ψ, hsurj, hψker, fun ℓ x y hy => ?_, fun x => ?_⟩
  · change transl (hc.equiv.symm y) = hc.psi (inclusion hLN ℓ) * transl (hc.equiv.symm x) *
      (hc.psi (inclusion hLN ℓ))⁻¹
    rw [mul_transl_mul_inv (hc.psi_add _), hc.psi_symm,
      show conjX X (inclusion hLN ℓ) x = y from Subtype.ext hy.symm]
  · change (x : G) ∈ R ↔ transl (hc.equiv.symm x) ∈ hexaR0
    rw [transl_mem_hexaR0_iff hS, ← mem_oval0_iff_lt, ← hc.R_iff, hc.rep_symm]

end PlaneData

end Plane

@[expose] def Sec4NXKernel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec4Setting G A R g E F → ∀ X ∈ ({E, F} : Set (Subgroup G)),
      AS76b.oUpperTwoPrime (normalizer (X : Set G)) ⊓
        AS76b.oddCoreIn (centralizer (A : Set G)) = ⊥

theorem sec4NXModel_of_check {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hc : hexaCheck = true) (hS : hexaStabCheck = true) (hK : Sec4NXKernel) : Sec4NXModel := by
  intro G _ _ A R g E F hset X hX
  have hD := planeData_of hE16 h11 hset.frame hset.even
  have hD' := planeData_of hE16 h11 hset.frame.swap hset.even
  have hKX := hK G A R g E F hset X hX
  rcases hX with rfl | rfl
  · obtain ⟨ι, ψ, hs, hk, he, hR⟩ := hD.nxModel hc hS hD'
    exact ⟨ι, ψ, hs, hk.trans (hD.centralizer_subgroupOf_oUpper hKX), he, hR⟩
  · obtain ⟨ι, ψ, hs, hk, he, hR⟩ := hD'.nxModel hc hS hD
    exact ⟨ι, ψ, hs, hk.trans (hD'.centralizer_subgroupOf_oUpper hKX), he, hR⟩

end CFSG.ComponentClassification.AS81
