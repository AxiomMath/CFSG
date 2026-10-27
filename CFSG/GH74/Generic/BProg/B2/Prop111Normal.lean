module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.Generic.BProg.Helpers

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

namespace Prop111Normal

open CFSG.LocalAnalysis.ComponentInitial

theorem rankCertified_of_elementary {F : Type} [Group F] [Finite F]
    (hcomm : ∀ a b : F, a * b = b * a) (hsq : ∀ a : F, a ^ 2 = 1) {r : ℕ}
    (hcard : 2 ^ r < Nat.card F) : RankCertified F r :=
  ⟨F, F, inferInstance, inferInstance, inferInstance, MonoidHom.id _, MonoidHom.id _,
    Function.surjective_id, hcomm, hsq, hcard, le_rfl⟩

theorem normal_of_component_elem {X : Type} [Group X] [Finite X] (hX : Gen4 X) {c : X}
    (hc : ∀ g : X, g * c = c * g) (hc2 : c * c = 1) (hc1 : c ≠ 1) {K E : Subgroup X}
    (hK : IsComponent K) (hEK : E ≤ K) (hE : CFSG.IsElementaryAbelian 2 ↥E)
    (hE4 : 4 ≤ Nat.card ↥E) (hEZ : ∀ e ∈ E, (∀ k ∈ K, k * e = e * k) → e = 1) : K.Normal := by
  refine ⟨fun n hn g => ?_⟩
  by_contra hmem
  set K' : Subgroup X := conjSub g K with hK'
  have hK'c : IsComponent K' := isComponent_conjSub hK g
  have hgn : g * n * g⁻¹ ∈ K' := ⟨n, hn, by simp [MulAut.conj_apply]⟩
  have hne : K ≠ K' := fun h => hmem (h ▸ hgn)
  have hcomm : ⁅K, K'⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hK hK'c).resolve_left hne
  have hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := by
    intro a ha b hb
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  set E' : Subgroup X := conjSub g E with hE'
  have hE'K' : E' ≤ K' := Subgroup.map_mono hEK
  have hinf : ∀ a ∈ E, a ∈ E' → a = 1 := fun a ha ha' =>
    hEZ a ha (fun k hk => hKK' k hk a (hE'K' ha'))
  have hE1 : RankCertified ↥E 1 := by
    refine rankCertified_of_elementary (fun a b => mul_comm' a b) (fun a => ?_) (by omega)
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 ↥E) a
  have hE1' : RankCertified ↥E' 1 :=
    hE1.of_mulEquiv (E.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  let φ : ↥E × ↥E' →* X := MonoidHom.noncommCoprod E.subtype E'.subtype
    (fun a b => hKK' a (hEK a.2) b (hE'K' b.2))
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : (a : X) * b = 1 := hab
    have ha' : (a : X) ∈ E' := by
      have : (a : X) = (b : X)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]; exact E'.inv_mem b.2
    have ha1 := hinf a a.2 ha'
    have hb1 : (b : X) = 1 := by rw [ha1, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have hcert : RankCertified ↥φ.range 3 :=
    (hE1.prod hE1').of_mulEquiv (MonoidHom.ofInjective hφ)
  have hcB : c ∉ φ.range := by
    rintro ⟨⟨a, b⟩, hab⟩
    have h1 : (a : X) * b = c := hab
    have hb' : (b : X)⁻¹ ∈ K' := K'.inv_mem (hE'K' b.2)
    have h2 : (a : X) = c * (b : X)⁻¹ := by rw [← h1]; group
    have ha1 : (a : X) = 1 := by
      refine hEZ a a.2 (fun k hk => ?_)
      calc k * a = k * (c * (b : X)⁻¹) := by rw [h2]
        _ = c * (k * (b : X)⁻¹) := by rw [← mul_assoc, hc k, mul_assoc]
        _ = c * ((b : X)⁻¹ * k) := by rw [hKK' k hk _ hb']
        _ = (c * (b : X)⁻¹) * k := by rw [mul_assoc]
        _ = a * k := by rw [h2]
    have hbc : (b : X) = c := by rw [ha1, one_mul] at h1; exact h1
    have hcE' : c ∈ E' := hbc ▸ b.2
    obtain ⟨e, he, hec⟩ := hcE'
    have hec' : e = c := by
      have e1 : g * e * g⁻¹ = c := by simpa [MulAut.conj_apply] using hec
      have e2 : g * c = c * g := hc g
      calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
        _ = g⁻¹ * c * g := by rw [e1]
        _ = c := by rw [show g⁻¹ * c * g = g⁻¹ * (c * g) from mul_assoc _ _ _, ← e2]; group
    have hcE : c ∈ E := hec' ▸ he
    exact hc1 (hEZ c hcE fun k _ => hc k)
  have := RankCertified.of_central_involution (K := φ.range) hc hc2 hcB hcert
  exact this.not_gen4 (by norm_num) hX

theorem eq_one_of_mem_pPrimeCore_of_two_pow {Y : Type} [Group Y] [Finite Y] {k : Y}
    (hk : k ∈ pPrimeCore 2 Y) {n : ℕ} (hkn : k ^ (2 ^ n) = 1) : k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf k ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hkn
  have h2 : orderOf k ∣ Nat.card (pPrimeCore 2 Y) := Subgroup.orderOf_dvd_natCard _ hk
  have h3 : orderOf k = 1 :=
    Nat.eq_one_of_dvd_coprimes ((CFSG.pPrimeCore_coprime_card (p := 2) (G := Y)).pow_left n) h1 h2
  exact orderOf_eq_one_iff.1 h3

section Bar

open CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.L5U5

variable {G : Type} [Group G]

theorem bar_normal_of_elem [Finite G] (hG : Gen4 G) {y : G} (hy : orderOf y = 2) {H E : Subgroup G}
    (hH : IsPCompIn 2 (centralizer ({y} : Set G)) H) (hEH : E ≤ H)
    (hE : CFSG.IsElementaryAbelian 2 ↥E) (hE4 : 4 ≤ Nat.card ↥E)
    (hEZ : ∀ e ∈ E, (∀ h ∈ H, ⁅h, e⁆ ∈ pPrimeCoreOf 2 (centralizer ({y} : Set G))) → e = 1) :
    (PumpCalc.bar y H).Normal := by
  set Cy : Subgroup G := centralizer ({y} : Set G) with hCy
  have hEC : E ≤ Cy := hEH.trans hH.1
  let f : ↥Cy →* TwoThin.barQ ↥Cy := TwoThin.barMk ↥Cy
  set S : Subgroup ↥Cy := E.subgroupOf Cy with hS
  set Eb : Subgroup (TwoThin.barQ ↥Cy) := S.map f with hEb
  have hSH : S ≤ H.subgroupOf Cy := fun a ha => hEH (Subgroup.mem_subgroupOf.mp ha)
  have hEbK : Eb ≤ PumpCalc.bar y H := Subgroup.map_mono hSH
  have hSel : CFSG.IsElementaryAbelian 2 ↥S := by
    have := hE
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsElementaryAbelian.subgroupOf hEC
  have hEbel : CFSG.IsElementaryAbelian 2 ↥Eb := by
    have := hSel
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsElementaryAbelian.map f
  have hinj : Function.Injective (f.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hmem : (s : ↥Cy) ∈ pPrimeCore 2 ↥Cy := (QuotientGroup.eq_one_iff (s : ↥Cy)).1 hs
    obtain ⟨n, hn⟩ := IsElementaryAbelian.isPGroup 2 ↥E ⟨(s : G), Subgroup.mem_subgroupOf.mp s.2⟩
    have hn' : (s : ↥Cy) ^ (2 ^ n) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
    exact Subtype.ext (eq_one_of_mem_pPrimeCore_of_two_pow hmem hn')
  have hrange : (f.comp S.subtype).range = Eb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardS : Nat.card ↥S = Nat.card ↥E := by
    have h1 : S.map Cy.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEC
    rw [← h1, Subgroup.card_map_of_injective Cy.subtype_injective]
  have hcard : 4 ≤ Nat.card ↥Eb := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcardS]
    exact hE4
  have hEbZ : ∀ e ∈ Eb, (∀ k ∈ PumpCalc.bar y H, k * e = e * k) → e = 1 := by
    rintro _ ⟨s, hsS, rfl⟩ hcomm
    have hsE : (s : G) ∈ E := Subgroup.mem_subgroupOf.mp hsS
    have h1 : (s : G) = 1 := by
      refine hEZ _ hsE fun h hh => ?_
      have hhC : h ∈ Cy := hH.1 hh
      have hk : f ⟨h, hhC⟩ * f s = f s * f ⟨h, hhC⟩ :=
        hcomm _ ⟨⟨h, hhC⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
      have h2 : f ⁅(⟨h, hhC⟩ : ↥Cy), s⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hk
      exact ⟨⁅(⟨h, hhC⟩ : ↥Cy), s⁆, (QuotientGroup.eq_one_iff _).1 h2, rfl⟩
    have h2 : s = 1 := Subtype.ext h1
    rw [h2, map_one]
  exact normal_of_component_elem (gen4_centralizerBar hG y) (xbar_comm y) (xbar_mul_self hy)
    (xbar_ne_one hy) (PumpCalc.isComponent_bar hH) hEbK hEbel hcard hEbZ

theorem conj_mem_sup_of_bar_normal {y : G} {H : Subgroup G} (hHC : H ≤ centralizer ({y} : Set G))
    (hN : (PumpCalc.bar y H).Normal) :
    ∀ c ∈ centralizer ({y} : Set G), ∀ h ∈ H,
      c * h * c⁻¹ ∈ H ⊔ pPrimeCoreOf 2 (centralizer ({y} : Set G)) := by
  intro c hc h hh
  set Cy : Subgroup G := centralizer ({y} : Set G) with hCy
  let f : ↥Cy →* TwoThin.barQ ↥Cy := TwoThin.barMk ↥Cy
  have hcc : c * h * c⁻¹ ∈ Cy := mul_mem (mul_mem hc (hHC hh)) (inv_mem hc)
  have hmem : f ⟨c * h * c⁻¹, hcc⟩ ∈ PumpCalc.bar y H := by
    have e : f ⟨c * h * c⁻¹, hcc⟩ = f ⟨c, hc⟩ * f ⟨h, hHC hh⟩ * (f ⟨c, hc⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact hN.conj_mem _ ⟨⟨h, hHC hh⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩ _
  obtain ⟨m, hm, hmeq⟩ := hmem
  have h1 : m⁻¹ * ⟨c * h * c⁻¹, hcc⟩ ∈ pPrimeCore 2 ↥Cy := QuotientGroup.eq.1 hmeq
  have h2 : c * h * c⁻¹ = (m : G) * ((m⁻¹ * ⟨c * h * c⁻¹, hcc⟩ : ↥Cy) : G) := by
    simp
  rw [h2]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hm))
    (Subgroup.mem_sup_right ⟨_, h1, rfl⟩)

end Bar

end Prop111Normal

end CFSG.GH74.Generic.BProg.B2
