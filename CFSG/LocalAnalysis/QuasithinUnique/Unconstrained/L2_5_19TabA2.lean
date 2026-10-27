module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabCases
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabA2Core
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabA2Model

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.A2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.QuasithinUnique.Id2519.Tab.L34
open scoped commutatorElement

theorem exists_center_gen {X : Type*} [Group X] (h : Nat.card (Subgroup.center X) = 2) :
    ∃ c : X, c ∈ Subgroup.center X ∧ c ≠ 1 ∧ c * c = 1 ∧
      ∀ z ∈ Subgroup.center X, z = 1 ∨ z = c := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hne, huniv⟩ := Nat.card_eq_two_iff.1 h
  have hcases : ∀ z ∈ Subgroup.center X, z = x ∨ z = y := by
    intro z hz
    have : (⟨z, hz⟩ : Subgroup.center X) ∈ ({⟨x, hx⟩, ⟨y, hy⟩} : Set (Subgroup.center X)) := by
      rw [huniv]; trivial
    rcases this with h1 | h1
    · left; exact congrArg Subtype.val h1
    · right; exact congrArg Subtype.val (Set.mem_singleton_iff.1 h1)
  have hxy : x ≠ y := fun h' => hne (Subtype.ext h')
  have h1mem : (1 : X) ∈ Subgroup.center X := Subgroup.one_mem _
  have hmain : ∃ c : X, c ∈ Subgroup.center X ∧ c ≠ 1 ∧ ∀ z ∈ Subgroup.center X, z = 1 ∨ z = c := by
    by_cases hx1 : x = 1
    · refine ⟨y, hy, fun hy1 => hxy (hx1.trans hy1.symm), fun z hz => ?_⟩
      rcases hcases z hz with h' | h'
      · left; rw [h', hx1]
      · right; exact h'
    · refine ⟨x, hx, hx1, fun z hz => ?_⟩
      rcases hcases z hz with h' | h'
      · right; exact h'
      · left
        rw [h']
        rcases hcases 1 h1mem with h'' | h''
        · exact absurd h''.symm hx1
        · exact h''.symm
  obtain ⟨c, hc, hc1, hall⟩ := hmain
  refine ⟨c, hc, hc1, ?_, hall⟩
  rcases hall (c * c) (Subgroup.mul_mem _ hc hc) with h2 | h2
  · exact h2
  · exfalso
    apply hc1
    have : c * c = c * 1 := by rw [h2, mul_one]
    exact mul_left_cancel this


theorem tabConjA2
    : TabConjA2 := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat hZcard u huK hu2
  obtain ⟨hL32, hmodel, -, -⟩ := hpat
  obtain ⟨e0⟩ := nonempty_equiv_of_stated (↥X ⧸ Subgroup.center ↥X) hmodel
  have hπ := quotProj_surjective e0
  have hker := quotProj_ker e0
  have hX : Group.IsPerfect ↥X := hXq.1
  have hKXt : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [hK]
    exact perfectResidualOf_le _
  have hKX : K ≤ X := hKXt.trans inf_le_left
  have hα2 := quotAct_mul_self (quotProj e0) hπ hker ht ht2
  have hα1 := quotAct_ne_one (quotProj e0) hπ hker ht hXq hcomm
  obtain ⟨e, he, -⟩ := full_automorphism_action
  obtain ⟨τR, hτe⟩ : ∃ τR : R, e τR = quotAct (quotProj e0) hπ hker ht :=
    ⟨e.symm _, e.apply_symm_apply _⟩
  obtain ⟨τp, hτp⟩ : ∃ τp : Equiv.Perm (Fin 42), τp = (τR : Equiv.Perm (Fin 42)) := ⟨_, rfl⟩
  have hτs : ∀ s : S, ((quotAct (quotProj e0) hπ hker ht s : S) : Equiv.Perm (Fin 42)) =
      τp * s * τp⁻¹ := by
    intro s
    rw [hτp, ← hτe]
    exact he τR s
  have hτ2 : τR * τR = 1 := by
    apply e.injective
    rw [map_mul, hτe, hα2, map_one]
  have hτ2' : τp * τp = 1 := by
    rw [hτp]
    exact congrArg Subtype.val hτ2
  have hτi : τp⁻¹ = τp := inv_eq_of_mul_eq_one_right hτ2'
  have hτ1 : τR ≠ 1 := by
    intro h
    apply hα1
    rw [← hτe, h, map_one]
  have hord : orderOf τR = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
  let ρ : ↥K →* ↥S := (quotProj e0).comp (Subgroup.inclusion hKX)
  have hKcenter : Subgroup.center ↥K = ⊥ := by
    have hf := l2pFacts ↥K (Or.inr hL32)
    exact center_eq_bot_of_simple_nonabelian hf.simple hf.nonabelian
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hz : Subgroup.inclusion hKX k ∈ Subgroup.center ↥X := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hk
    have hzk : k ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro k'
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥X → G) (hz (Subgroup.inclusion hKX k'))
    rw [hKcenter] at hzk
    exact Subgroup.mem_bot.mp hzk
  have hKbcard0 : Nat.card ρ.range = 168 := by
    have h := Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv
    rw [← h]
    exact card_of_psl_three_two hL32
  have hρfix : ∀ k : ↥K, quotAct (quotProj e0) hπ hker ht (ρ k) = ρ k := by
    intro k
    have hkt : (k : G) * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (hKXt k.2).2
    have hy : ((Subgroup.inclusion hKX k : X) : G) =
        t * ((Subgroup.inclusion hKX k : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (k : G) = (k * t) * t⁻¹ := by group
        _ = (t * k) * t⁻¹ := by rw [hkt]
    exact quotAct_apply (quotProj e0) hπ hker ht _ _ hy
  have hKbcard : Nat.card (ρ.range.map S.subtype) = 168 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hKbcard0
  have hKbC' : ρ.range.map S.subtype ≤ Subgroup.centralizer {τp} ⊓ S := by
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, (ρ k).2⟩
    have h := hτs (ρ k)
    rw [hρfix k] at h
    calc ((ρ k : S) : Equiv.Perm (Fin 42)) * τp =
        (τp * ((ρ k : S) : Equiv.Perm (Fin 42)) * τp⁻¹) * τp := by rw [← h]
      _ = τp * ((ρ k : S) : Equiv.Perm (Fin 42)) := by group
  have hKbC : ρ.range.map S.subtype ≤
      Subgroup.centralizer {(τR : Equiv.Perm (Fin 42))} ⊓ S := by
    rw [← hτp]
    exact hKbC'
  have hconj : IsConj τR r₂R := isConj_r₂_of_card hord hKbC (by rw [hKbcard])
  obtain ⟨c, hcR, hτc⟩ := eq_conj_of_isConj hconj
  have hτc' : τp = c * r₂ * c⁻¹ := by
    rw [hτp]
    exact hτc
  have hKbeq : ρ.range.map S.subtype = Subgroup.centralizer {c * r₂ * c⁻¹} ⊓ S := by
    rw [← hτc', hτp]
    exact Subgroup.eq_of_le_of_card_ge hKbC (by rw [card_cent_of_isConj hconj, hKbcard])
  obtain ⟨cX, hcXc, hcX1, hcXsq, hcXall⟩ := exists_center_gen hZcard
  obtain ⟨a₀, z, hU1, hUm, hUsq, hPU, hrU, hUP, hPS, ha₀U, ha₀1, ha₀C, htrans, hzP, hzC, hz3,
    hzfpf, hred, hwit⟩ := modelA2
  let π' : ↥X →* Equiv.Perm (Fin 42) :=
    (MulAut.conj c⁻¹).toMonoidHom.comp (S.subtype.comp (quotProj e0))
  have hπ'apply : ∀ x : ↥X,
      π' x = c⁻¹ * ((quotProj e0 x : S) : Equiv.Perm (Fin 42)) * c := by
    intro x
    show c⁻¹ * ((quotProj e0 x : S) : Equiv.Perm (Fin 42)) * c⁻¹⁻¹ = _
    rw [inv_inv]
  have hπ'1 : ∀ x : ↥X, π' x = 1 ↔ x ∈ Subgroup.center ↥X := by
    intro x
    rw [hπ'apply, ← hker, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : ((quotProj e0 x : S) : Equiv.Perm (Fin 42)) = 1 := by
        calc ((quotProj e0 x : S) : Equiv.Perm (Fin 42)) =
            c * (c⁻¹ * ((quotProj e0 x : S) : Equiv.Perm (Fin 42)) * c) * c⁻¹ := by group
          _ = 1 := by rw [h]; group
      exact Subtype.ext h1
    · intro h
      rw [h]
      simp
  let τ : ↥X →* ↥X := (conjAut X t ht).toMonoidHom
  have hτapply : ∀ x : ↥X, ((τ x : ↥X) : G) = t * (x : G) * t⁻¹ := fun x => coe_conjAut X ht x
  have hinvt : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hτ2X : ∀ x : ↥X, τ (τ x) = x := by
    intro x
    apply Subtype.ext
    rw [hτapply, hτapply]
    calc t * (t * (x : G) * t⁻¹) * t⁻¹ = (t * t) * (x : G) * (t⁻¹ * t⁻¹) := by group
      _ = x := by rw [hinvt, ht2, one_mul, mul_one]
  have hτπ : ∀ x : ↥X, π' (τ x) = r₂ * π' x * r₂⁻¹ := by
    intro x
    have h1 : quotAct (quotProj e0) hπ hker ht (quotProj e0 x) = quotProj e0 (τ x) :=
      quotAct_apply (quotProj e0) hπ hker ht x (τ x) (hτapply x)
    have h2 := hτs (quotProj e0 x)
    rw [h1] at h2
    rw [hπ'apply, hπ'apply, h2, hτc']
    group
  set K' : Subgroup ↥X := K.subgroupOf X with hK'
  have hK'mem : ∀ k : ↥X, k ∈ K' ↔ (k : G) ∈ K := fun k => Subgroup.mem_subgroupOf
  have hKτ : ∀ k ∈ K', τ k = k := by
    intro k hk
    apply Subtype.ext
    rw [hτapply]
    have hkt : (k : G) * t = t * k :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKXt ((hK'mem k).1 hk)).2
    calc t * (k : G) * t⁻¹ = (k * t) * t⁻¹ := by rw [hkt]
      _ = k := by group
  have hKker : ∀ k ∈ K', π' k = 1 → k = 1 := by
    intro k hk h1
    have hk' : (k : G) ∈ K := (hK'mem k).1 hk
    have hz : k ∈ Subgroup.center ↥X := (hπ'1 k).1 h1
    have hρk : ρ ⟨(k : G), hk'⟩ = 1 := by
      have h2 : ρ ⟨(k : G), hk'⟩ = quotProj e0 k := rfl
      rw [h2, ← MonoidHom.mem_ker, hker]
      exact hz
    have h3 := hρinj (hρk.trans (map_one ρ).symm)
    exact Subtype.ext (congrArg (fun y : ↥K => ((y : ↥K) : G)) h3)
  have hKimg : K'.map π' = C₂ := by
    ext a
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : (k : G) ∈ K := (hK'mem k).1 hk
      have hmem : ((quotProj e0 k : S) : Equiv.Perm (Fin 42)) ∈
          Subgroup.centralizer {c * r₂ * c⁻¹} ⊓ S := by
        rw [← hKbeq]
        exact ⟨quotProj e0 k, ⟨⟨(k : G), hk'⟩, rfl⟩, rfl⟩
      obtain ⟨hy, hyS⟩ := hmem
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
      · rw [hπ'apply]
        have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
        calc c⁻¹ * ((quotProj e0 k : S) : Equiv.Perm (Fin 42)) * c * r₂ =
            c⁻¹ * (((quotProj e0 k : S) : Equiv.Perm (Fin 42)) * (c * r₂ * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * r₂ * c⁻¹) * ((quotProj e0 k : S) : Equiv.Perm (Fin 42))) * c := by
            rw [hy']
          _ = r₂ * (c⁻¹ * ((quotProj e0 k : S) : Equiv.Perm (Fin 42)) * c) := by group
      · rw [hπ'apply]
        have := conj_mem_S (R.inv_mem hcR) hyS
        rwa [inv_inv] at this
    · intro ha
      obtain ⟨har, haS⟩ := ha
      have har' := Subgroup.mem_centralizer_singleton_iff.mp har
      have hmem : c * a * c⁻¹ ∈ Subgroup.centralizer {c * r₂ * c⁻¹} ⊓ S := by
        refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, conj_mem_S hcR haS⟩
        calc c * a * c⁻¹ * (c * r₂ * c⁻¹) = c * (a * r₂) * c⁻¹ := by group
          _ = c * (r₂ * a) * c⁻¹ := by rw [har']
          _ = c * r₂ * c⁻¹ * (c * a * c⁻¹) := by group
      rw [← hKbeq] at hmem
      obtain ⟨_, ⟨kk, rfl⟩, hkk⟩ := hmem
      refine ⟨⟨(kk : G), ?_⟩, ?_, ?_⟩
      · exact hKX kk.2
      · exact (hK'mem _).2 kk.2
      · rw [hπ'apply]
        have h5 : ((quotProj e0 ⟨(kk : G), hKX kk.2⟩ : S) : Equiv.Perm (Fin 42)) =
            c * a * c⁻¹ := hkk
        rw [h5]
        group
  have hlift : ∀ p ∈ PSet, ∃ x : ↥X, π' x = p := by
    intro p hp
    have hpS : c * p * c⁻¹ ∈ S := conj_mem_S hcR hp.1
    obtain ⟨x, hx⟩ := hπ ⟨c * p * c⁻¹, hpS⟩
    refine ⟨x, ?_⟩
    rw [hπ'apply, hx]
    show c⁻¹ * (c * p * c⁻¹) * c = p
    group
  have hdata : A2Data π' cX τ r₂ K' PSet USet a₀ z :=
    { cc := hcXsq
      c1 := hcX1
      cz := fun x => Subgroup.mem_center_iff.mp hcXc x
      πc := (hπ'1 cX).2 hcXc
      ker := fun x hx => hcXall x ((hπ'1 x).1 hx)
      τ2 := hτ2X
      τπ := hτπ
      Kτ := hKτ
      Kker := hKker
      U1 := hU1
      Um := hUm
      Usq := hUsq
      PU := hPU
      rU := hrU
      lift := hlift
      UP := hUP
      a₀U := ha₀U
      a₀1 := ha₀1
      a₀K := by rw [hKimg]; exact ha₀C
      trans := htrans
      zP := hzP
      zK := by rw [hKimg]; exact hzC
      z3 := hz3
      zfpf := hzfpf
      red := by
        intro k hk hk2
        have hkC : π' k ∈ C₂ := by rw [← hKimg]; exact ⟨k, hk, rfl⟩
        have hsq : π' k * π' k = 1 := by rw [← map_mul, hk2, map_one]
        obtain ⟨κ, hκC, hκU⟩ := hred _ hkC hsq
        rw [← hKimg] at hκC
        obtain ⟨k', hk', rfl⟩ := hκC
        exact ⟨k', hk', by rw [map_mul, map_mul, map_inv]; exact hκU⟩
      wit := hwit }
  have huX : u ∈ X := hKX huK
  obtain ⟨x, hx⟩ := hdata.main ⟨u, huX⟩ ((hK'mem _).2 huK) (Subtype.ext hu2)
  refine ⟨(x : G), x.2, ?_⟩
  have h3 : (t * (x : G) * t⁻¹)⁻¹ * x = u := by
    have := congrArg Subtype.val hx
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hτapply] at this
    exact this
  have h4 : (x : G)⁻¹ * t⁻¹ * x = t⁻¹ * u := by
    calc (x : G)⁻¹ * t⁻¹ * x = t⁻¹ * ((t * (x : G) * t⁻¹)⁻¹ * x) := by group
      _ = t⁻¹ * u := by rw [h3]
  rw [hinvt] at h4
  exact h4

end CFSG.QuasithinUnique.Id2519.Tab.A2

namespace CFSG.QuasithinUnique.Id2519.Tab

theorem tabConj
    : TabConj := tabConj_of_A2 A2.tabConjA2

end CFSG.QuasithinUnique.Id2519.Tab
