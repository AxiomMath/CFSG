module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Lat2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Lat3
import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12

open Subgroup CFSG CFSG.GH74
open scoped commutatorElement

section Generic

variable {C P : Type} [Group C] [Group P]

theorem eq_one_of_isPGroup_of_odd {E : Type*} [Group E] (hE : IsPGroup 2 E) {e : E}
    (h : Odd (orderOf e)) : e = 1 := by
  obtain ⟨k, hk⟩ := hE e
  have h1 : orderOf e ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  rw [hj'] at h
  have hj0 : j = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.2 h) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hj0, pow_zero] at hj'
  exact orderOf_eq_one_iff.1 hj'

theorem inj_comp_of_isPGroup (ρ : C →* P) (hodd : ∀ k ∈ ρ.ker, Odd (orderOf k)) {E : Type*}
    [Group E] (hE : IsPGroup 2 E) (ι : E →* C) (hι : Function.Injective ι) :
    Function.Injective (ρ.comp ι) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro e he
  have h1 : ι e ∈ ρ.ker := he
  have h2 : Odd (orderOf e) := by
    have := hodd _ h1
    rwa [orderOf_injective ι hι] at this
  exact eq_one_of_isPGroup_of_odd hE h2

theorem exists_lift_pgroup [Finite C] (ρ : C →* P) {R : Subgroup P} (hR : R ≤ ρ.range)
    (hR2 : IsPGroup 2 ↥R) : ∃ E : Subgroup C, IsPGroup 2 ↥E ∧ E.map ρ = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y₁ : Subgroup C := R.comap ρ
  let π₁ : ↥Y₁ →* ↥R := (ρ.comp Y₁.subtype).codRestrict R (fun y => y.2)
  have hπ₁ : Function.Surjective π₁ := by
    intro r
    obtain ⟨y, hy⟩ := hR r.2
    exact ⟨⟨y, by show ρ y ∈ R; rw [hy]; exact r.2⟩, Subtype.ext hy⟩
  obtain ⟨P₁⟩ : Nonempty (Sylow 2 ↥Y₁) := inferInstance
  have hRtop : IsPGroup 2 ↥(⊤ : Subgroup ↥R) := hR2.of_equiv Subgroup.topEquiv.symm
  have hmap : (P₁ : Subgroup ↥Y₁).map π₁ = ⊤ := by
    have := (P₁.mapSurjective hπ₁).is_maximal' hRtop le_top
    rw [Sylow.coe_mapSurjective] at this
    exact this.symm
  refine ⟨(P₁ : Subgroup ↥Y₁).map Y₁.subtype, P₁.isPGroup'.map Y₁.subtype, ?_⟩
  have h1 : ((P₁ : Subgroup ↥Y₁).map π₁).map R.subtype =
      ((P₁ : Subgroup ↥Y₁).map Y₁.subtype).map ρ := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [← h1, hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem card_map_of_isPGroup (ρ : C →* P) (hodd : ∀ k ∈ ρ.ker, Odd (orderOf k)) {E : Subgroup C}
    (hE : IsPGroup 2 ↥E) : Nat.card ↥(E.map ρ) = Nat.card ↥E := by
  have hinj := inj_comp_of_isPGroup ρ hodd hE E.subtype E.subtype_injective
  have : E.map ρ = (ρ.comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [this]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_conj_le_sylow {J : Type} [Group J] [Finite J] (Q : Sylow 2 J) {E : Subgroup J}
    (hE : IsPGroup 2 ↥E) : ∃ g : J, E.map (MulAut.conj g⁻¹).toMonoidHom ≤ (Q : Subgroup J) := by
  obtain ⟨Q', hQ'⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J Q Q'
  refine ⟨g, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have h1 : e ∈ (Q' : Subgroup J) := hQ' he
  rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  simpa using h1

theorem odd_card_of_odd_orders {H : Type*} [Group H] [Finite H] (h : ∀ x : H, Odd (orderOf x)) :
    Odd (Nat.card H) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
  have := h x
  rw [hx] at this
  exact absurd this (by decide)

theorem isPGroup_of_sq_eq_one {G : Type*} [Group G] {E : Subgroup G} (h : ∀ a ∈ E, a * a = 1) :
    IsPGroup 2 ↥E := fun g => ⟨1, by
  apply Subtype.ext
  simpa [pow_two] using h g g.2⟩

end Generic

theorem BarShape.isSolvable {P : Type} [Group P] [Finite P] {zc : P} (hP : BarShape P zc) :
    Group.IsSolvable P := by
  obtain ⟨W, A, B, A₃, hS⟩ := hP.exists_spec
  obtain ⟨eA⟩ := hS.eA
  obtain ⟨eB⟩ := hS.eB
  have hWp : IsPGroup 2 ↥W := isPGroup_W hS.cp hS.normal_A eA eB
  have : Group.IsNilpotent ↥W := hWp.isNilpotent
  have : Group.IsSolvable ↥W := inferInstance
  have := hS.normal_W
  obtain ⟨e⟩ := hS.quot
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (α := Fin 3) (by simp)
  have : Group.IsSolvable (P ⧸ W) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.isSolvable_of_ker_le_range W.subtype (QuotientGroup.mk' W) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem factorization_two_pow_mul_odd (a m : ℕ) (hm : ¬ 2 ∣ m) (hm0 : m ≠ 0) :
    (2 ^ a * m).factorization 2 = a := by
  rw [Nat.factorization_mul (by positivity) hm0]
  simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm]

theorem two_pow_factorization_cases {n : ℕ} (hn : n = 8 ∨ n = 32 ∨ n = 96 ∨ n = 192) :
    2 ^ n.factorization 2 = 8 ∨ 2 ^ n.factorization 2 = 32 ∨ 2 ^ n.factorization 2 = 64 := by
  rcases hn with rfl | rfl | rfl | rfl
  · have h : (8 : ℕ).factorization 2 = 3 := by
      have := factorization_two_pow_mul_odd 3 1 (by norm_num) (by norm_num)
      simpa using this
    left
    rw [h]; norm_num
  · have h : (32 : ℕ).factorization 2 = 5 := by
      have := factorization_two_pow_mul_odd 5 1 (by norm_num) (by norm_num)
      simpa using this
    right; left
    rw [h]; norm_num
  · have h : (96 : ℕ).factorization 2 = 5 := by
      have := factorization_two_pow_mul_odd 5 3 (by norm_num) (by norm_num)
      simpa using this
    right; left
    rw [h]; norm_num
  · have h : (192 : ℕ).factorization 2 = 6 := by
      have := factorization_two_pow_mul_odd 6 3 (by norm_num) (by norm_num)
      simpa using this
    right; right
    rw [h]; norm_num

theorem isQuasisimple_of_simple_nonab {J : Type*} [Group J] (hs : IsSimpleGroup J)
    (hn : ∃ a b : J, a * b ≠ b * a) : CFSG.IsQuasisimple J := by
  have hc : center J = ⊥ := by
    rcases (inferInstance : (center J).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  let e : J ⧸ center J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨?_, e.isSimpleGroup, ?_⟩
  · refine Group.isPerfect_def.mpr ?_
    rcases (inferInstance : (commutator J).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      have hmem : ⁅a, b⁆ ∈ commutator J := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
    · exact h
  · obtain ⟨a, b, hab⟩ := hn
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem exists_elemAbelian_four_of_simple {J : Type} [Group J] [Finite J] (hs : IsSimpleGroup J)
    (hn : ∃ a b : J, a * b ≠ b * a) :
    ∃ E : Subgroup J, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a * a = 1) ∧
      4 ≤ Nat.card ↥E := by
  classical
  by_contra hcon
  push Not at hcon
  have hQ := isQuasisimple_of_simple_nonab hs hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : CFSG.pRank 2 J ≤ 1 := by
    apply csSup_le'
    rintro r ⟨A, hA, hcard⟩
    have hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have h2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
      have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
      rwa [pow_two] at this
    have h4 := hcon A hc h2
    rw [hcard] at h4
    by_contra hr1
    push Not at hr1
    have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
    omega
  obtain ⟨heven, -, hcen, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.quasisimple_rank_one_unique_central_involution hQ hr
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := J) 2 (even_iff_two_dvd.1 heven)
  have hzc := hcen z hz
  have hc : center J = ⊥ := by
    rcases (inferInstance : (center J).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  rw [hc, Subgroup.mem_bot] at hzc
  rw [hzc, orderOf_one] at hz
  omega

section Main

variable {J : Type} [Group J] [Finite J] {y : J} {P : Type} [Group P]

theorem tr_exists (Q : Sylow 2 J) (hQC : (Q : Subgroup J) ≤ centralizer ({y} : Set J))
    (ρ : ↥(centralizer ({y} : Set J)) →* P) (hodd : ∀ k ∈ ρ.ker, Odd (orderOf k))
    {E : Subgroup J} (hE : IsPGroup 2 ↥E) :
    ∃ f : ↥E →* P, Function.Injective f ∧ ∀ e, f e ∈ ρ.range := by
  obtain ⟨g, hg⟩ := exists_conj_le_sylow Q hE
  let E' : Subgroup J := E.map (MulAut.conj g⁻¹).toMonoidHom
  have hE'C : E' ≤ centralizer ({y} : Set J) := hg.trans hQC
  let eE : ↥E ≃* ↥E' :=
    E.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hE'2 : IsPGroup 2 ↥E' := hE.of_equiv eE
  have hinj := inj_comp_of_isPGroup ρ hodd hE'2 (Subgroup.inclusion hE'C)
    (Subgroup.inclusion_injective hE'C)
  exact ⟨(ρ.comp (Subgroup.inclusion hE'C)).comp eE.toMonoidHom, hinj.comp eE.injective,
    fun e => ⟨_, rfl⟩⟩

theorem tr_elemAbelian (Q : Sylow 2 J) (hQC : (Q : Subgroup J) ≤ centralizer ({y} : Set J))
    (ρ : ↥(centralizer ({y} : Set J)) →* P) (hodd : ∀ k ∈ ρ.ker, Odd (orderOf k))
    {E : Subgroup J} (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1) :
    ∃ R : Subgroup P, R ≤ ρ.range ∧ (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧ (∀ a ∈ R, a * a = 1) ∧
      Nat.card ↥R = Nat.card ↥E := by
  obtain ⟨f, hf, hfN⟩ := tr_exists Q hQC ρ hodd (isPGroup_of_sq_eq_one h2)
  refine ⟨f.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact hfN a
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc a a.2 b b.2)
  · rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (h2 a a.2)
    rw [this, map_one]
  · exact Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm

theorem lift_elemAbelian (ρ : ↥(centralizer ({y} : Set J)) →* P)
    (hodd : ∀ k ∈ ρ.ker, Odd (orderOf k)) {R : Subgroup P} (hR : R ≤ ρ.range)
    (hc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (h2 : ∀ a ∈ R, a * a = 1) :
    ∃ E : Subgroup J, E ≤ centralizer ({y} : Set J) ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a * a = 1) ∧ Nat.card ↥E = Nat.card ↥R := by
  obtain ⟨Et, hEt2, hEtR⟩ := exists_lift_pgroup ρ hR (isPGroup_of_sq_eq_one h2)
  have hinj : Function.Injective (ρ.comp Et.subtype) :=
    inj_comp_of_isPGroup ρ hodd hEt2 Et.subtype Et.subtype_injective
  have hmem : ∀ c : ↥Et, ρ (c : ↥(centralizer ({y} : Set J))) ∈ R := fun c => by
    rw [← hEtR]
    exact ⟨c, c.2, rfl⟩
  refine ⟨Et.map (centralizer ({y} : Set J)).subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, -, rfl⟩
    exact c.2
  · rintro _ ⟨c, hc', rfl⟩ _ ⟨d, hd', rfl⟩
    have : (⟨c, hc'⟩ : ↥Et) * ⟨d, hd'⟩ = ⟨d, hd'⟩ * ⟨c, hc'⟩ := by
      apply hinj
      show ρ (c * d) = ρ (d * c)
      rw [map_mul, map_mul]
      exact hc _ (hmem ⟨c, hc'⟩) _ (hmem ⟨d, hd'⟩)
    have := congrArg (fun x : ↥Et => ((x : ↥(centralizer ({y} : Set J))) : J)) this
    simpa using this
  · rintro _ ⟨c, hc', rfl⟩
    have : (⟨c, hc'⟩ : ↥Et) * ⟨c, hc'⟩ = 1 := by
      apply hinj
      show ρ (c * c) = ρ 1
      rw [map_mul, map_one]
      exact h2 _ (hmem ⟨c, hc'⟩)
    have := congrArg (fun x : ↥Et => ((x : ↥(centralizer ({y} : Set J))) : J)) this
    simpa using this
  · rw [Subgroup.card_map_of_injective (centralizer ({y} : Set J)).subtype_injective,
      ← hEtR]
    exact (card_map_of_isPGroup ρ hodd hEt2).symm

end Main

section Core

variable {J : Type} [Group J] [Finite J] {y : J} {P : Type} [Group P] [Finite P] {zc : P}

theorem data_of_core (hs : IsSimpleGroup J) (hn : ∃ a b : J, a * b ≠ b * a)
    (hy : IsCentralInvolution y) (hP : BarShape P zc)
    (ρ : ↥(centralizer ({y} : Set J)) →* P) (hodd : ∀ k ∈ ρ.ker, Odd (orderOf k))
    (hρy : ρ ⟨y, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = zc) (hN : ρ.range.Normal)
    (haut : 192 ∣ Nat.card ↥(MulAction.stabilizer (MulAut J) y)) : Ivk93M12Data J y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcentral := hy
  obtain ⟨-, Q, -, hQc⟩ := hy
  have hQC : (Q : Subgroup J) ≤ centralizer ({y} : Set J) := fun s hs' =>
    Subgroup.mem_centralizer_singleton_iff.2 (hQc s hs')
  have := hN
  have hzN : zc ∈ ρ.range := ⟨_, hρy⟩
  obtain ⟨W, A, B, A₃, hS⟩ := hP.exists_spec
  obtain ⟨hNcard, hNcases⟩ := hS.normal_cases hP ρ.range hzN
  have hrk : ∀ E : Subgroup J, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) →
      Nat.card ↥E ≤ 8 := by
    intro E hc h2
    obtain ⟨R, -, hRc, hR2, hRcard⟩ := tr_elemAbelian Q hQC ρ hodd hc h2
    rw [← hRcard]
    exact hP.card_elemAbelian_le R hRc hR2
  have hsecond : ∃ R : Subgroup P, R ≤ ρ.range ∧ (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧
      (∀ a ∈ R, a * a = 1) ∧ 8 ≤ Nat.card ↥R := by
    rcases hNcases with hone | ⟨R, hRN, hRc, hR2, hR8⟩
    · exfalso
      obtain ⟨E, hc, h2, h4⟩ := exists_elemAbelian_four_of_simple hs hn
      obtain ⟨R, hRN, hRc, hR2, hRcard⟩ := tr_elemAbelian Q hQC ρ hodd hc h2
      have hle : Nat.card ↥R ≤ 2 :=
        elemAb_card_le_two (σ := zc) hP.sq fun x hx => hone x (hRN hx) (hR2 x hx)
      omega
    · exact ⟨R, hRN, hRc, hR2, hR8⟩
  have hcent : ∃ E : Subgroup J, E ≤ centralizer ({y} : Set J) ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ Nat.card ↥E = 8 := by
    obtain ⟨R, hRN, hRc, hR2, hR8⟩ := hsecond
    obtain ⟨E, hEC, hEc, hE2, hEcard⟩ := lift_elemAbelian ρ hodd hRN hRc hR2
    have h8 := hrk E hEc hE2
    refine ⟨E, hEC, hEc, fun a ha => by rw [pow_two]; exact hE2 a ha, ?_⟩
    omega
  have hNcard' : Nat.card ↥ρ.range = 8 ∨ Nat.card ↥ρ.range = 32 ∨ Nat.card ↥ρ.range = 96 ∨
      Nat.card ↥ρ.range = 192 := by
    obtain ⟨R, hRN, -, -, hR8⟩ := hsecond
    have := Subgroup.card_le_of_le hRN
    omega
  have hker : ∀ k ∈ ρ.rangeRestrict.ker, Odd (orderOf k) := by
    intro k hk
    rw [MonoidHom.ker_rangeRestrict] at hk
    exact hodd k hk
  have hQcard : Nat.card ↥(Q : Subgroup J) = 2 ^ (Nat.card ↥ρ.range).factorization 2 := by
    let Q' : Sylow 2 ↥(centralizer ({y} : Set J)) := Q.subtype hQC
    let Q'' : Sylow 2 ↥ρ.range := Q'.mapSurjective ρ.rangeRestrict_surjective
    have h1 := Sylow.card_eq_multiplicity Q''
    have h2 : Nat.card ↥(Q'' : Subgroup ↥ρ.range) =
        Nat.card ↥(Q' : Subgroup ↥(centralizer ({y} : Set J))) := by
      rw [Sylow.coe_mapSurjective]
      exact card_map_of_isPGroup ρ.rangeRestrict hker Q'.isPGroup'
    have h3 : Nat.card ↥(Q' : Subgroup ↥(centralizer ({y} : Set J))) =
        Nat.card ↥(Q : Subgroup J) := by
      rw [Sylow.coe_subtype]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
    rw [← h3, ← h2, h1]
  have hsyl : ∀ S : Sylow 2 J, Nat.card ↥(S : Subgroup J) = 8 ∨ Nat.card ↥(S : Subgroup J) = 32 ∨
      Nat.card ↥(S : Subgroup J) = 64 := by
    intro S
    have : Nat.card ↥(S : Subgroup J) = Nat.card ↥(Q : Subgroup J) := by
      rw [Sylow.card_eq_multiplicity S, Sylow.card_eq_multiplicity Q]
    rw [this, hQcard]
    exact two_pow_factorization_cases hNcard'
  have hkerodd : Odd (Nat.card ↥ρ.ker) :=
    odd_card_of_odd_orders fun x => by
      have := hodd x x.2
      rwa [Subgroup.orderOf_coe] at this
  have hcc : ∃ n m : ℕ, (n = 8 ∨ n = 32 ∨ n = 96 ∨ n = 192) ∧ Odd m ∧
      Nat.card ↥(centralizer ({y} : Set J)) = n * m := by
    refine ⟨Nat.card ↥ρ.range, Nat.card ↥ρ.ker, hNcard', hkerodd, ?_⟩
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv] at h
    exact h
  have hsolv : Group.IsSolvable ↥(centralizer ({y} : Set J)) := by
    have : Group.IsSolvable ↥ρ.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hkerodd
    have := hP.isSolvable
    have : Group.IsSolvable ↥ρ.range := inferInstance
    exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ.rangeRestrict (by
      rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  have hquot : ∃ (P' : Type) (_ : Group P') (_ : Finite P') (zc' : P'), BarShape P' zc' ∧
      ∃ N : Subgroup P', N.Normal ∧ ∃ (hz : zc' ∈ N)
        (φ : ↥(centralizer ({y} : Set J)) →* ↥N),
        Function.Surjective φ ∧ (∀ k ∈ φ.ker, Odd (orderOf k)) ∧
          φ ⟨y, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = ⟨zc', hz⟩ :=
    ⟨P, inferInstance, inferInstance, zc, hP, ρ.range, hN, hzN, ρ.rangeRestrict,
      ρ.rangeRestrict_surjective, hker, Subtype.ext hρy⟩
  exact ⟨hs, hn, hcentral, hsolv,
    fun E hc h2 => hrk E hc (fun a ha => by rw [← pow_two]; exact h2 a ha), hcent, hsyl, hcc,
    haut, hquot⟩

end Core

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12
