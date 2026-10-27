module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotZCentral
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic
import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27ComponentLayer

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section General

variable {Y : Type*} [Group Y]

theorem map_conj_map_conj_eq_map_conj_mul (H : Subgroup Y) (g s : Y) :
    (H.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      H.map (MulAut.conj (g * s)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

theorem isPGroup_two_zpowers_of_mul_self {s : Y} (hs : s * s = 1) : IsPGroup 2 (zpowers s) := by
  have h2 : orderOf s ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hs)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])

theorem centralizer_inf_centralizer_le_centralizer_sup {A B : Subgroup Y} :
    centralizer (A : Set Y) ⊓ centralizer (B : Set Y) ≤
      centralizer ((A ⊔ B : Subgroup Y) : Set Y) := by
  rintro x ⟨hxA, hxB⟩
  have h : A ⊔ B ≤ centralizer (zpowers x : Set Y) := by
    refine sup_le ?_ ?_
    · rw [← le_centralizer_iff, zpowers_le]
      exact hxA
    · rw [← le_centralizer_iff, zpowers_le]
      exact hxB
  rw [← le_centralizer_iff, zpowers_le] at h
  exact h

theorem sup_centralizer_inf_sup_centralizer_le {A B : Subgroup Y}
    (hAB : B ≤ centralizer (A : Set Y))
    (hC : centralizer (A : Set Y) ⊓ centralizer (B : Set Y) = ⊥) :
    (A ⊔ centralizer (A : Set Y)) ⊓ (B ⊔ centralizer (B : Set Y)) ≤ A ⊔ B := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨a, ha, c, hc, rfl⟩ :=
    CFSG.ComponentClassification.M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute
      (fun a ha c hc => mem_centralizer_iff.1 hc a ha) hx1
  obtain ⟨b, hb, c', hc', hbc⟩ :=
    CFSG.ComponentClassification.M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute
      (fun b hb c hc => mem_centralizer_iff.1 hc b hb) hx2
  have hBA : A ≤ centralizer (B : Set Y) := le_centralizer_iff.1 hAB
  have hz1 : c * b⁻¹ ∈ centralizer (A : Set Y) := mul_mem hc (inv_mem (hAB hb))
  have hcomm : c' * b = b * c' := (mem_centralizer_iff.1 hc' b hb).symm
  have hz : c * b⁻¹ = a⁻¹ * c' := by
    calc c * b⁻¹ = a⁻¹ * (a * c) * b⁻¹ := by group
      _ = a⁻¹ * (b * c') * b⁻¹ := by rw [hbc]
      _ = a⁻¹ * (c' * b) * b⁻¹ := by rw [hcomm]
      _ = a⁻¹ * c' := by group
  have hz2 : c * b⁻¹ ∈ centralizer (B : Set Y) := hz ▸ mul_mem (inv_mem (hBA ha)) hc'
  have hz3 : c * b⁻¹ = 1 := mem_bot.1 (hC.le ⟨hz1, hz2⟩)
  rw [mul_inv_eq_one] at hz3
  rw [hz3]
  exact mul_mem_sup ha hb

variable [Finite Y]

theorem eq_of_mem_of_card_le_two {U : Subgroup Y} (hU : Nat.card U ≤ 2) {a b : Y} (ha : a ∈ U)
    (hb : b ∈ U) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have hcard : Nat.card U = 2 := by
    have h1 : 1 < Nat.card U := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact ⟨⟨⟨a, ha⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
    omega
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : U)).1 hcard
  have e1 : (⟨a, ha⟩ : U) = y := huniq _ (fun h => ha1 (congrArg Subtype.val h))
  have e2 : (⟨b, hb⟩ : U) = y := huniq _ (fun h => hb1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (e1.trans e2.symm)

theorem false_of_isComponent_le {C K' : Subgroup Y}
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ C → Nat.card U ≤ 2)
    (hK' : IsComponent K') (hle : K' ≤ C) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect K' := hK'.1.1
  have hQ : CFSG.GorensteinWalter.IsQuasisimple K' :=
    ⟨CFSG.LocalCores.isQuasisimple_nontrivial hK'.1, Group.IsPerfect.commutator_eq_top,
      hK'.1.2.1⟩
  have h4 := CFSG.GorensteinWalter.isQuasisimple_four_dvd_card hQ
  obtain ⟨U, hU⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2) (G := K')
    (by norm_num; exact h4)
  have h := hsyl (U.map K'.subtype) ((IsPGroup.of_card hU).map _)
    ((map_subtype_le U).trans hle)
  rw [card_map_of_injective K'.subtype_injective, hU] at h
  norm_num at h

omit [Finite Y] in
theorem isComponent_map_conj {Kc : Subgroup Y} (hKc : IsComponent Kc) (g : Y) :
    IsComponent (Kc.map (MulAut.conj g).toMonoidHom) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hKc

end General

section Swap

variable {Y : Type*} [Group Y]

structure SwapComponentData (s : Y) (Kc D : Subgroup Y) : Prop where
  mul_self : s * s = 1
  isComponent : IsComponent Kc
  ne : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc
  commute : ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥
  le_sup : D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom
  mem_centralizer : s ∈ centralizer (D : Set Y)
  sylow : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2

variable {s : Y} {Kc D : Subgroup Y}

theorem SwapComponentData.le_centralizer (h : SwapComponentData s Kc D) :
    Kc.map (MulAut.conj s).toMonoidHom ≤ centralizer (Kc : Set Y) :=
  le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h.commute)

theorem SwapComponentData.not_mem_centralizer (h : SwapComponentData s Kc D) :
    s ∉ centralizer (Kc : Set Y) := fun hs =>
  h.ne (mem_normalizer_iff_map_conj_eq.1 (centralizer_le_normalizer _ hs))

variable [Finite Y]

theorem SwapComponentData.conj_eq_or_eq (h : SwapComponentData s Kc D) (g : Y) :
    Kc.map (MulAut.conj g).toMonoidHom = Kc ∨
      Kc.map (MulAut.conj g).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom := by
  have hg := isComponent_map_conj h.isComponent g
  have hs := isComponent_map_conj h.isComponent s
  rcases CFSG.LocalCores.distinct_components_commute hg h.isComponent with h1 | h1
  · exact Or.inl h1
  rcases CFSG.LocalCores.distinct_components_commute hg hs with h2 | h2
  · exact Or.inr h2
  exfalso
  refine false_of_isComponent_le h.sylow hg ?_
  have hc : Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ≤
      centralizer (Kc.map (MulAut.conj g).toMonoidHom : Set Y) :=
    sup_le (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h1))
      (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h2))
  exact le_centralizer_iff.1 (h.le_sup.trans hc)

theorem SwapComponentData.map_conj_conj_of_eq (h : SwapComponentData s Kc D) {g : Y}
    (hg : Kc.map (MulAut.conj g).toMonoidHom = Kc) :
    (Kc.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      Kc.map (MulAut.conj s).toMonoidHom := by
  rw [map_conj_map_conj_eq_map_conj_mul]
  rcases h.conj_eq_or_eq (g * s) with h1 | h1
  · exfalso
    apply h.ne
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [map_conj_map_conj_eq_map_conj_mul, h1, hg]
  · exact h1

theorem SwapComponentData.map_conj_conj_of_eq_conj (h : SwapComponentData s Kc D) {g : Y}
    (hg : Kc.map (MulAut.conj g).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom) :
    (Kc.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom = Kc := by
  rw [map_conj_map_conj_eq_map_conj_mul]
  rcases h.conj_eq_or_eq (g * s) with h1 | h1
  · exact h1
  · exfalso
    apply h.ne
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [map_conj_map_conj_eq_map_conj_mul, h1, hg]

theorem SwapComponentData.map_conj_sup (h : SwapComponentData s Kc D) (g : Y) :
    (Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom := by
  rw [Subgroup.map_sup]
  rcases h.conj_eq_or_eq g with h1 | h1
  · rw [h1, h.map_conj_conj_of_eq h1]
  · rw [h1, h.map_conj_conj_of_eq_conj h1, sup_comm]

theorem SwapComponentData.normal_sup (h : SwapComponentData s Kc D) :
    (Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom).Normal := by
  constructor
  intro n hn g
  have hmem : (MulAut.conj g).toMonoidHom n ∈
      (Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    mem_map_of_mem _ hn
  rw [h.map_conj_sup g] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem SwapComponentData.centralizer_sup_eq_bot (h : SwapComponentData s Kc D)
    (hO : oddCore Y = ⊥) :
    centralizer ((Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom : Subgroup Y) : Set Y) = ⊥ := by
  set E := Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom with hEdef
  have hE : E.Normal := h.normal_sup
  have hn : (centralizer (E : Set Y)).Normal := by
    have := hE
    infer_instance
  have hCD : centralizer (E : Set Y) ≤ centralizer (D : Set Y) := centralizer_le h.le_sup
  have h2 : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (E : Set Y) → Nat.card U ≤ 2 :=
    fun U hU hUC => h.sylow U hU (hUC.trans hCD)
  have hcard := card_le_two_of_normal_of_oddCore_eq_bot hO hn h2
  have hcen := le_center_of_normal_of_card_le_two hn hcard
  have hsK := h.not_mem_centralizer
  have hs1 : s ≠ 1 := fun hs => hsK (hs ▸ one_mem _)
  rw [eq_bot_iff]
  intro m hm
  rw [mem_bot]
  by_contra hm1
  have hmm : m * m = 1 := by
    by_contra hmm1
    have := eq_of_mem_of_card_le_two hcard (mul_mem hm hm) hm hmm1 hm1
    exact hm1 (by simpa using this)
  have hmc := hcen hm
  have hsm : zpowers s ≤ normalizer (zpowers m : Set Y) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [← le_centralizer_iff, zpowers_le]
    exact mem_centralizer_iff.2 fun x _ => mem_center_iff.1 hmc x
  have hUp : IsPGroup 2 (zpowers s ⊔ zpowers m : Subgroup Y) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_two_zpowers_of_mul_self h.mul_self)
      (isPGroup_two_zpowers_of_mul_self hmm) hsm
  have hUC : zpowers s ⊔ zpowers m ≤ centralizer (D : Set Y) :=
    sup_le (zpowers_le.2 h.mem_centralizer) (zpowers_le.2 (hCD hm))
  have hsm' := eq_of_mem_of_card_le_two (h.sylow _ hUp hUC) (mem_sup_left (mem_zpowers s))
    (mem_sup_right (mem_zpowers m)) hs1 hm1
  exact hsK (hsm' ▸ centralizer_le (le_sup_left : Kc ≤ E) hm)

theorem SwapComponentData.centralizer_inf_centralizer_eq_bot (h : SwapComponentData s Kc D)
    (hO : oddCore Y = ⊥) :
    centralizer (Kc : Set Y) ⊓ centralizer (Kc.map (MulAut.conj s).toMonoidHom : Set Y) = ⊥ :=
  eq_bot_iff.2 (centralizer_inf_centralizer_le_centralizer_sup.trans
    (h.centralizer_sup_eq_bot hO).le)

theorem SwapComponentData.center_eq_bot (h : SwapComponentData s Kc D) (hO : oddCore Y = ⊥) :
    center Kc = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxC : (x : Y) ∈ centralizer (Kc : Set Y) := mem_centralizer_iff.2 fun y hy =>
    congrArg Subtype.val (mem_center_iff.1 hx ⟨y, hy⟩)
  have hxC' : (x : Y) ∈ centralizer (Kc.map (MulAut.conj s).toMonoidHom : Set Y) :=
    commutator_eq_bot_iff_le_centralizer.1 h.commute x.2
  have h1 : (x : Y) = 1 := mem_bot.1 ((h.centralizer_inf_centralizer_eq_bot hO).le ⟨hxC, hxC'⟩)
  exact mem_bot.2 (Subtype.ext h1)

theorem SwapComponentData.inf_eq_bot (h : SwapComponentData s Kc D) (hO : oddCore Y = ⊥) :
    Kc ⊓ Kc.map (MulAut.conj s).toMonoidHom = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxs⟩
  exact (h.centralizer_inf_centralizer_eq_bot hO).le ⟨h.le_centralizer hxs,
    commutator_eq_bot_iff_le_centralizer.1 h.commute hx⟩

theorem SwapComponentData.exists_sign (h : SwapComponentData s Kc D) :
    ∃ σ : Y →* Multiplicative (ZMod 2), ∀ g, σ g = 1 → g ∈ normalizer (Kc : Set Y) := by
  classical
  let χ : Y → ZMod 2 := fun g => if Kc.map (MulAut.conj g).toMonoidHom = Kc then 0 else 1
  have hχdef : ∀ g, χ g = if Kc.map (MulAut.conj g).toMonoidHom = Kc then 0 else 1 :=
    fun g => rfl
  have hχ0 : ∀ g, χ g = 0 ↔ Kc.map (MulAut.conj g).toMonoidHom = Kc := by
    intro g
    by_cases hg : Kc.map (MulAut.conj g).toMonoidHom = Kc
    · rw [hχdef, ite_eq_left hg]
      exact ⟨fun _ => hg, fun _ => rfl⟩
    · rw [hχdef, ite_eq_right hg]
      exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h1 hg⟩
  have hχ1 : ∀ g, Kc.map (MulAut.conj g).toMonoidHom ≠ Kc → χ g = 1 := fun g hg => by
    rw [hχdef, ite_eq_right hg]
  have hmul : ∀ g k, χ (g * k) = χ g + χ k := by
    intro g k
    have hgk : Kc.map (MulAut.conj (g * k)).toMonoidHom =
        (Kc.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
      (map_conj_map_conj_eq_map_conj_mul Kc g k).symm
    rcases h.conj_eq_or_eq k with hk | hk
    · rw [(hχ0 k).2 hk, add_zero, hχdef (g * k), hχdef g, hgk, hk]
    · have hk' : Kc.map (MulAut.conj k).toMonoidHom ≠ Kc := hk ▸ h.ne
      rw [hχ1 k hk']
      rcases h.conj_eq_or_eq g with hg | hg
      · rw [(hχ0 g).2 hg, zero_add]
        apply hχ1
        rw [hgk, hk, h.map_conj_conj_of_eq hg]
        exact h.ne
      · have hg' : Kc.map (MulAut.conj g).toMonoidHom ≠ Kc := hg ▸ h.ne
        rw [hχ1 g hg', (hχ0 _).2 (by rw [hgk, hk, h.map_conj_conj_of_eq_conj hg])]
        decide
  have hone : χ 1 = 0 := (hχ0 1).2 (by
    rw [map_one]
    ext x
    simp)
  refine ⟨{ toFun := fun g => Multiplicative.ofAdd (χ g),
            map_one' := by rw [hone]; rfl,
            map_mul' := fun g k => by rw [hmul, ofAdd_add] }, fun g hg => ?_⟩
  have hg' : χ g = 0 := by
    have : Multiplicative.ofAdd (χ g) = Multiplicative.ofAdd 0 := hg
    exact Multiplicative.ofAdd.injective this
  exact mem_normalizer_iff_map_conj_eq.2 ((hχ0 g).1 hg')

theorem SwapComponentData.perfectCore_top_le (h : SwapComponentData s Kc D) (hO : oddCore Y = ⊥)
    (hOut : Group.IsSolvable (Outer Kc)) :
    perfectCore (⊤ : Subgroup Y) ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom := by
  have hP := CFSG.Quasithin.perfectCore_perfect (⊤ : Subgroup Y)
  obtain ⟨σ, hσ⟩ := h.exists_sign
  have hPN : perfectCore (⊤ : Subgroup Y) ≤ normalizer (Kc : Set Y) :=
    (perfect_le_ker σ hP).trans fun g hg => hσ g hg
  have hPN' : perfectCore (⊤ : Subgroup Y) ≤
      normalizer (Kc.map (MulAut.conj s).toMonoidHom : Set Y) :=
    hPN.trans fun g hg => mem_normalizer_iff_map_conj_eq.2
      (h.map_conj_conj_of_eq (mem_normalizer_iff_map_conj_eq.1 hg))
  have hOut' : Group.IsSolvable (Outer (Kc.map (MulAut.conj s).toMonoidHom)) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
      (Kc.equivMapOfInjective _ (MulAut.conj s).injective)).2.1 hOut
  exact (le_inf (perfect_le_sup_centralizer hOut hP hPN)
    (perfect_le_sup_centralizer hOut' hP hPN')).trans
    (sup_centralizer_inf_sup_centralizer_le h.le_centralizer
      (h.centralizer_inf_centralizer_eq_bot hO))

end Swap

end CFSG.SeitzReduction.F4Pilot
