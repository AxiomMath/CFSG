module

public import CFSG.GH74.Uniqueness.Section14Setup
public import CFSG.GH74.Uniqueness.Bender.SuzukiSolvable
public import CFSG.GH74.Uniqueness.Section12Aux

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

section General

variable {X : Type*} [Group X]

theorem exists_mem_not_mem_of_lt_two_part [Finite X] {T S2 : Subgroup X} (hT : IsPGroup 2 T)
    (hS2 : ABGLocalTools.IsSylowOf 2 S2 (normalizer (T : Set X)))
    (hlt : Nat.card T < 2 ^ (Nat.card X).factorization 2) : ∃ y ∈ S2, y ∉ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := hT.exists_le_sylow
  have hTS' : T < (S' : Subgroup X) := lt_of_le_of_ne hS' (fun heq => by
    have := S'.card_eq_multiplicity
    rw [← heq] at this
    omega)
  set T' := T.subgroupOf (S' : Subgroup X) with hT'
  have hT'top : T' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply (lt_iff_le_not_ge.mp hTS').2
    intro x hx
    have : (⟨x, hx⟩ : ↥(S' : Subgroup X)) ∈ T' := htop ▸ mem_top _
    exact this
  have hnil : Group.IsNilpotent ↥(S' : Subgroup X) := S'.isPGroup'.isNilpotent
  obtain ⟨y', hy'N, hy'T⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent T' hT'top)
  have hyT : (y' : X) ∉ T := hy'T
  have hyN : (y' : X) ∈ normalizer (T : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    have hN := mem_normalizer_iff.mp hy'N
    constructor
    · intro hx
      exact (hN ⟨x, hS' hx⟩).mp hx
    · intro hx
      have hxS : x ∈ (S' : Subgroup X) := by
        have h1 := hS' hx
        have := (S' : Subgroup X).mul_mem
          ((S' : Subgroup X).mul_mem ((S' : Subgroup X).inv_mem y'.2) h1) y'.2
        simpa [mul_assoc] using this
      exact (hN ⟨x, hxS⟩).mpr hx
  by_contra hcon
  push Not at hcon
  have hS2T : S2 ≤ T := hcon
  have hWN : T ⊔ zpowers (y' : X) ≤ normalizer (T : Set X) :=
    sup_le le_normalizer (zpowers_le.mpr hyN)
  have hWS' : T ⊔ zpowers (y' : X) ≤ (S' : Subgroup X) := sup_le hS' (zpowers_le.mpr y'.2)
  have hW2 : IsPGroup 2 ↥(T ⊔ zpowers (y' : X)) := S'.isPGroup'.to_le hWS'
  have heq := hS2.eq_of_le (hS2T.trans le_sup_left) hWN hW2
  have hy : (y' : X) ∈ S2 := by
    rw [← heq]
    exact mem_sup_right (mem_zpowers _)
  exact hyT (hS2T hy)

theorem exists_sq_mem_of_not_mem {T S2 : Subgroup X} (hS2 : IsPGroup 2 S2) {y₀ : X}
    (hy₀ : y₀ ∈ S2) (hy₀T : y₀ ∉ T) : ∃ y ∈ S2, y ∉ T ∧ y * y ∈ T := by
  classical
  obtain ⟨m, hm⟩ := hS2 ⟨y₀, hy₀⟩
  have hm' : y₀ ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hex : ∃ j, y₀ ^ 2 ^ j ∈ T := ⟨m, hm' ▸ T.one_mem⟩
  have hj : y₀ ^ 2 ^ Nat.find hex ∈ T := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hj
    exact hy₀T hj
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨y₀ ^ 2 ^ i, pow_mem hy₀ _, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_add, ← two_mul, ← pow_succ']
  rw [hi] at hj
  exact hj

theorem comm_of_sq_eq_one {U : Subgroup X} (hU : ∀ u ∈ U, u * u = 1) :
    ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
  intro a ha b hb
  have h1 := hU _ (U.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hU a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hU b hb)
  have : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [this, mul_inv_rev, ha', hb']

end General

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec14

variable {c : Ctx12 Z M} {n : ℕ} {Q : Sylow 2 ↥c.L} {U : Subgroup X}

theorem Mo_sq (S : ZDSetup X Z M) (h : LData c n 2) : ∀ x ∈ zHull Z M, x * x = 1 := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1, mul_one]
  have hxZ : x ∈ Z ∩ (M : Set X) := by
    have : x ∈ (zHull Z M : Set X) \ {1} := ⟨hx, hx1⟩
    rw [← h.zM_eq] at this
    exact this
  exact S.invariant.mul_self_eq_one hxZ.1

theorem T_norm_U (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    ∀ x ∈ pGrp c Q ⊔ U, ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
  intro x hx u hu
  obtain ⟨p, hp, u', hu', rfl⟩ := (mem_T_iff hU).mp hx
  have hpu : p * u = u * p := P_comm_U hU p hp u hu
  have : p * u' * u * (p * u')⁻¹ = u' * u * u'⁻¹ := by
    have h1 : p * u' = u' * p := P_comm_U hU p hp u' hu'
    calc p * u' * u * (p * u')⁻¹ = u' * (p * u) * p⁻¹ * u'⁻¹ := by rw [h1]; group
      _ = u' * u * u'⁻¹ := by rw [hpu]; group
  rw [this]
  exact U.mul_mem (U.mul_mem hu' hu) (U.inv_mem hu')

theorem T_norm_P (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    ∀ x ∈ pGrp c Q ⊔ U, ∀ p ∈ pGrp c Q, x * p * x⁻¹ ∈ pGrp c Q := by
  intro x hx p hp
  obtain ⟨p', hp', u', hu', rfl⟩ := (mem_T_iff hU).mp hx
  have h1 : u' * p = p * u' := (P_comm_U hU p hp u' hu').symm
  have : p' * u' * p * (p' * u')⁻¹ = p' * p * p'⁻¹ := by
    calc p' * u' * p * (p' * u')⁻¹ = p' * (u' * p) * u'⁻¹ * p'⁻¹ := by group
      _ = p' * p * p'⁻¹ := by rw [h1]; group
  rw [this]
  exact mul_mem (mul_mem hp' hp) (inv_mem hp')

theorem U_sq
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) {S2 : Subgroup X}
    (hS2 : ABGLocalTools.IsSylowOf 2 S2 (normalizer ((pGrp c Q ⊔ U : Subgroup X) : Set X)))
    (hTS2 : pGrp c Q ⊔ U ≤ S2) : ∀ u ∈ U, u * u = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := pGrp c Q ⊔ U with hTdef
  have hZ := S.invariant
  have hT2 := isPGroup_T S h hQ hU
  have hlt : Nat.card T < 2 ^ (Nat.card X).factorization 2 := by
    rw [two_part S h12 h hQ hU]
    have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := (n_odd h).2; omega)
    have hT0 : 0 < Nat.card T := Nat.card_pos
    nlinarith
  obtain ⟨y₀, hy₀, hy₀T⟩ := exists_mem_not_mem_of_lt_two_part hT2 hS2 hlt
  obtain ⟨y, hyS2, hyT, hy2⟩ := exists_sq_mem_of_not_mem hS2.isPGroup hy₀ hy₀T
  have hyN : y ∈ normalizer (T : Set X) := hS2.le hyS2
  have hTU := T_norm_U hU (Q := Q)
  set Uy := conjugate U y⁻¹ with hUy
  have mem_Uy : ∀ w, w ∈ Uy ↔ y⁻¹ * w * y ∈ U := by
    intro w
    rw [hUy, mem_conjugate_iff, inv_inv]
  have hy2U : ∀ w, y * w * y⁻¹ ∈ U ↔ y⁻¹ * w * y ∈ U := by
    intro w
    constructor
    · intro hw
      have := hTU _ (T.inv_mem hy2) _ hw
      have e : (y * y)⁻¹ * (y * w * y⁻¹) * (y * y)⁻¹⁻¹ = y⁻¹ * w * y := by group
      rwa [e] at this
    · intro hw
      have := hTU _ hy2 _ hw
      have e : y * y * (y⁻¹ * w * y) * (y * y)⁻¹ = y * w * y⁻¹ := by group
      rwa [e] at this
  have hW : U ⊓ Uy = ⊥ := by
    by_contra hW
    have hWJ : U ⊓ Uy ≤ centralizer (c.L : Set X) := inf_le_left.trans hU.le
    have hyW : y ∈ normalizer ((U ⊓ Uy : Subgroup X) : Set X) := by
      rw [mem_normalizer_iff]
      intro w
      simp only [mem_inf, mem_Uy]
      constructor
      · rintro ⟨hw1, hw2⟩
        refine ⟨(hy2U w).mpr hw2, ?_⟩
        simpa [mul_assoc] using hw1
      · rintro ⟨hw1, hw2⟩
        refine ⟨?_, (hy2U w).mp hw1⟩
        simpa [mul_assoc] using hw2
    have hyL := normalizer_le_of_le_J S h hWJ hW hyW
    have hWN : T ⊔ zpowers y ≤ normalizer (c.L : Set X) :=
      sup_le (T_le_NL hU) (zpowers_le.mpr hyL)
    have hWS : T ⊔ zpowers y ≤ S2 := sup_le hTS2 (zpowers_le.mpr hyS2)
    have heq := (T_sylow S h hQ hU).eq_of_le le_sup_left hWN (hS2.isPGroup.to_le hWS)
    apply hyT
    rw [← heq]
    exact mem_sup_right (mem_zpowers y)
  have hTUy : ∀ x ∈ T, ∀ w ∈ Uy, x * w * x⁻¹ ∈ Uy := by
    intro x hx w hw
    rw [mem_Uy] at hw ⊢
    have hx' : y⁻¹ * x * y ∈ T := by
      have := (mem_normalizer_iff.mp (inv_mem hyN) x).mp hx
      simpa using this
    have := hTU _ hx' _ hw
    have e : y⁻¹ * x * y * (y⁻¹ * w * y) * (y⁻¹ * x * y)⁻¹ = y⁻¹ * (x * w * x⁻¹) * y := by group
    rwa [e] at this
  have hUyT : Uy ≤ T := by
    intro w hw
    rw [mem_Uy] at hw
    have := (mem_normalizer_iff.mp hyN (y⁻¹ * w * y)).mp (mem_sup_right hw)
    simpa [mul_assoc] using this
  have hPUy : pGrp c Q ⊓ Uy = ⊥ := by
    by_contra hne
    set H : Subgroup ↥(pGrp c Q) := (pGrp c Q ⊓ Uy).subgroupOf (pGrp c Q) with hH
    have hHn : H.Normal := by
      refine ⟨fun a ha g => ?_⟩
      rw [hH, mem_subgroupOf] at ha ⊢
      obtain ⟨ha1, ha2⟩ := mem_inf.mp ha
      exact mem_inf.mpr ⟨by simpa using mul_mem (mul_mem g.2 ha1) (inv_mem g.2),
        by simpa using hTUy g (mem_sup_left g.2) a ha2⟩
    have hH1 : H ≠ ⊥ := by
      intro hbot
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, (mem_inf.mp hx).1⟩ : ↥(pGrp c Q)) ∈ H := mem_subgroupOf.mpr hx
      rw [hbot, mem_bot] at this
      rw [mem_bot]
      exact congrArg Subtype.val this
    have hnil : Group.IsNilpotent ↥(pGrp c Q) := isPGroup_P.isNilpotent
    obtain ⟨m, hm1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hH1)
    have hmH := (mem_inf.mp m.2).1
    have hmC := (mem_inf.mp m.2).2
    have hmPU := mem_subgroupOf.mp hmH
    obtain ⟨hmP, hmUy⟩ := mem_inf.mp hmPU
    have hmMo : ((m : ↥(pGrp c Q)) : X) ∈ zHull Z M := by
      apply center_P S h hQ _ hmP
      intro x hx
      have := (mem_center_iff.mp hmC) ⟨x, hx⟩
      exact (congrArg Subtype.val this).symm
    have hm1' : ((m : ↥(pGrp c Q)) : X) ≠ 1 := by
      intro h1
      apply hm1
      exact Subtype.ext (Subtype.ext h1)
    have hmZ : ((m : ↥(pGrp c Q)) : X) ∈ Z := by
      have : ((m : ↥(pGrp c Q)) : X) ∈ (zHull Z M : Set X) \ {1} := ⟨hmMo, hm1'⟩
      rw [← h.zM_eq] at this
      exact this.1
    rw [mem_Uy] at hmUy
    exact not_mem_Z_of_mem_J S h (hU.le hmUy) (hZ.2 _ hmZ y)
  have hcomm : ∀ p ∈ pGrp c Q, ∀ w ∈ Uy, p * w = w * p := by
    intro p hp w hw
    have h1 : p * w * p⁻¹ * w⁻¹ ∈ pGrp c Q ⊓ Uy := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have := T_norm_P hU w (hUyT hw) p⁻¹ (inv_mem hp)
        have e : p * w * p⁻¹ * w⁻¹ = p * (w * p⁻¹ * w⁻¹) := by group
        rw [e]
        exact mul_mem hp this
      · exact mul_mem (hTUy p (mem_sup_left hp) w hw) (inv_mem hw)
    rw [hPUy, mem_bot] at h1
    have : p * w * p⁻¹ * w⁻¹ * w * p = w * p := by rw [h1, one_mul]
    simpa using this
  have hsqUy : ∀ w ∈ Uy, w * w = 1 := by
    intro w hw
    obtain ⟨p, hp, u', hu', hpu⟩ := (mem_T_iff hU).mp (hUyT hw)
    have hpc : ∀ x ∈ pGrp c Q, p * x = x * p := by
      intro x hx
      have h1 := hcomm x hx w hw
      rw [hpu] at h1
      have h2 : u' * x = x * u' := (P_comm_U hU x hx u' hu').symm
      have : p * x * u' = x * p * u' := by
        calc p * x * u' = p * (u' * x) := by rw [h2, mul_assoc]
          _ = p * u' * x := by rw [mul_assoc]
          _ = x * (p * u') := h1.symm
          _ = x * p * u' := by rw [mul_assoc]
      exact mul_right_cancel this
    have hpMo := center_P S h hQ p hp hpc
    have hpp : p * p = 1 := Mo_sq S h p hpMo
    have hww : w * w = u' * u' := by
      rw [hpu]
      have h1 : u' * p = p * u' := (P_comm_U hU p hp u' hu').symm
      calc p * u' * (p * u') = p * (u' * p) * u' := by group
        _ = p * (p * u') * u' := by rw [h1]
        _ = (p * p) * (u' * u') := by group
        _ = u' * u' := by rw [hpp, one_mul]
    have hmem : w * w ∈ U ⊓ Uy := mem_inf.mpr ⟨hww ▸ mul_mem hu' hu', mul_mem hw hw⟩
    rw [hW, mem_bot] at hmem
    exact hmem
  intro u hu
  have hyu : y * u * y⁻¹ ∈ Uy := by
    rw [mem_Uy]
    simpa [mul_assoc] using hu
  have h1 := hsqUy _ hyu
  have e : y * u * y⁻¹ * (y * u * y⁻¹) = y * (u * u) * y⁻¹ := by group
  rw [e] at h1
  have : u * u = y⁻¹ * (y * (u * u) * y⁻¹) * y := by group
  rw [this, h1]
  group

theorem cent_U_J
    (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M) (h : LData c n 2)
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X)))
    (hUsq : ∀ u ∈ U, u * u = 1) :
    ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set X) ⊓ centralizer (c.L : Set X) = U := by
  intro u hu hu1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf⟩ := exists_injective_J h12 h131 h
  have hUc := comm_of_sq_eq_one hUsq
  have hUle : U ≤ centralizer ({u} : Set X) ⊓ centralizer (c.L : Set X) := fun v hv =>
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (hUc v hv u hu), hU.le hv⟩
  have hfu : f ⟨u, hU.le hu⟩ * f ⟨u, hU.le hu⟩ = 1 := by
    rw [← map_mul, show (⟨u, hU.le hu⟩ : ↥(centralizer (c.L : Set X))) * ⟨u, hU.le hu⟩ = 1 from
      Subtype.ext (hUsq u hu), map_one]
  have hfu1 : f ⟨u, hU.le hu⟩ ≠ 1 := by
    intro h1
    apply hu1
    have := hf (h1.trans (map_one f).symm)
    exact congrArg Subtype.val this
  have hP := h.bender.centralizer_involution_isPGroup hfu hfu1
  have h2 : IsPGroup 2 ↥(centralizer ({u} : Set X) ⊓ centralizer (c.L : Set X)) := by
    intro x
    have hxJ : (x : X) ∈ centralizer (c.L : Set X) := (mem_inf.mp x.2).2
    have hxu : (x : X) * u = u * x := mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).1
    have hfx : f ⟨x, hxJ⟩ ∈ centralizer ({f ⟨u, hU.le hu⟩} : Set ↥c.L) := by
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxu
    obtain ⟨k, hk⟩ := hP ⟨_, hfx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h3 : f (⟨x, hxJ⟩ ^ 2 ^ k) = f 1 := by
      rw [map_pow, map_one]
      simpa using congrArg Subtype.val hk
    have h4 := congrArg Subtype.val (hf h3)
    simpa using h4
  exact hU.eq_of_le hUle inf_le_right h2

theorem J_le_normalizer_P : centralizer (c.L : Set X) ≤ normalizer (pGrp c Q : Set X) := by
  intro j hj
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  intro x hx
  exact (mem_centralizer_iff.mp hj) x (P_le_L hx)

theorem cent_Mo_u
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M)
    (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X)))
    (hUsq : ∀ u ∈ U, u * u = 1) :
    ∀ u ∈ U, u ≠ 1 → centralizer (zHull Z M : Set X) ⊓ centralizer ({u} : Set X) =
      pGrp c Q ⊔ U := by
  intro u hu hu1
  have hUc := comm_of_sq_eq_one hUsq
  apply le_antisymm
  · intro g hg
    obtain ⟨hgMo, hgu⟩ := mem_inf.mp hg
    have hgN : g ∈ normalizer (c.L : Set X) := centralizer_le_of_mem_J S h (hU.le hu) hu1 hgu
    have hgPJ : g ∈ pGrp c Q ⊔ centralizer (c.L : Set X) := by
      rw [← cent_Mo_NL S h hQ]
      exact mem_inf.mpr ⟨hgMo, hgN⟩
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
      J_le_normalizer_P] at hgPJ
    obtain ⟨p, hp, j, hj, rfl⟩ := hgPJ
    have hpu : p * u = u * p := P_comm_U hU p hp u hu
    have hju : j ∈ centralizer ({u} : Set X) := by
      rw [mem_centralizer_singleton_iff] at hgu ⊢
      have : p * (j * u) = p * (u * j) := by
        calc p * (j * u) = p * j * u := by group
          _ = u * (p * j) := hgu
          _ = p * (u * j) := by rw [← mul_assoc, ← hpu, mul_assoc]
      exact mul_left_cancel this
    have hjU : j ∈ U := by
      rw [← cent_U_J h12 h131 h hU hUsq u hu hu1]
      exact mem_inf.mpr ⟨hju, hj⟩
    exact mul_mem (mem_sup_left hp) (mem_sup_right hjU)
  · refine sup_le (fun x hx => mem_inf.mpr ⟨?_, ?_⟩) (fun x hx => mem_inf.mpr ⟨?_, ?_⟩)
    · rw [mem_centralizer_iff]
      intro m hm
      exact (Mo_central S h hQ x hx m hm).symm
    · exact mem_centralizer_singleton_iff.mpr (P_comm_U hU x hx u hu)
    · rw [mem_centralizer_iff]
      intro m hm
      exact (mem_centralizer_iff.mp (hU.le hx)) m (h.m_le hm)
    · exact mem_centralizer_singleton_iff.mpr (hUc x hx u hu)

theorem comm_T (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X)))
    (hUsq : ∀ u ∈ U, u * u = 1) :
    ⁅pGrp c Q ⊔ U, pGrp c Q ⊔ U⁆ = zHull Z M := by
  have hUc := comm_of_sq_eq_one hUsq
  apply le_antisymm
  · rw [commutator_le]
    intro a ha b hb
    obtain ⟨p, hp, u, hu, rfl⟩ := (mem_T_iff hU).mp ha
    obtain ⟨p', hp', u', hu', rfl⟩ := (mem_T_iff hU).mp hb
    have c1 : u * p' = p' * u := (P_comm_U hU p' hp' u hu).symm
    have c2 : u' * p⁻¹ = p⁻¹ * u' := (P_comm_U hU _ (inv_mem hp) u' hu').symm
    have c3 : u * u' = u' * u := hUc u hu u' hu'
    have e : ⁅p * u, p' * u'⁆ = ⁅p, p'⁆ := by
      calc ⁅p * u, p' * u'⁆ = p * (u * p') * u' * u⁻¹ * p⁻¹ * u'⁻¹ * p'⁻¹ := by
            rw [commutatorElement_def]; group
        _ = p * p' * (u * u') * u⁻¹ * p⁻¹ * u'⁻¹ * p'⁻¹ := by rw [c1]; group
        _ = p * p' * (u' * p⁻¹) * u'⁻¹ * p'⁻¹ := by rw [c3]; group
        _ = ⁅p, p'⁆ := by rw [c2, commutatorElement_def]; group
    rw [e, ← comm_P S h hQ]
    exact commutator_mem_commutator hp hp'
  · rw [← comm_P S h hQ]
    exact commutator_mono le_sup_left le_sup_left

theorem card_U_le
    (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M) (h : LData c n 2)
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X)))
    (hUsq : ∀ u ∈ U, u * u = 1) : Nat.card U ≤ 2 ^ n := by
  obtain ⟨f, hf⟩ := exists_injective_J h12 h131 h
  have hE : ∀ x ∈ (U.subgroupOf (centralizer (c.L : Set X))).map f, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, show y * y = 1 from Subtype.ext (hUsq _ (mem_subgroupOf.mp hy)), map_one]
  have h1 := h.bender.card_le_of_sq_eq_one _ hE
  rw [card_map_of_injective hf] at h1
  rwa [show Nat.card (U.subgroupOf (centralizer (c.L : Set X))) = Nat.card U from
    Nat.card_congr (subgroupOfEquivOfLe hU.le).toEquiv] at h1

theorem J_sq_of_two (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X)))
    (hUsq : ∀ u ∈ U, u * u = 1) :
    ∀ x : ↥(centralizer (c.L : Set X)), ∀ k : ℕ, x ^ 2 ^ k = 1 → x * x = 1 := by
  intro x k hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (U.subgroupOf (centralizer (c.L : Set X))) =
      2 ^ (Nat.card (centralizer (c.L : Set X))).factorization 2 := by
    rw [← card_U_eq hU]
    exact Nat.card_congr (subgroupOfEquivOfLe hU.le).toEquiv
  have hxp : IsPGroup 2 (zpowers x) := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨g, hg⟩ := exists_conj_mem_of_card_eq hcard hxp
  have h1 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := Subtype.ext (hUsq _ (mem_subgroupOf.mp hg))
  have e : g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
  rw [e] at h1
  have : x * x = g⁻¹ * (g * (x * x) * g⁻¹) * g := by group
  rw [this, h1]
  group

theorem J_solvable
    (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M) (h : LData c n 2)
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X)))
    (hUsq : ∀ u ∈ U, u * u = 1) : Group.IsSolvable ↥(centralizer (c.L : Set X)) := by
  obtain ⟨f, hf⟩ := exists_injective_J h12 h131 h
  exact h.bender.isSolvable_of_injective f hf (J_sq_of_two hU hUsq)

end Sec14

end CFSG.GH74.Uniqueness
