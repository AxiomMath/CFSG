module

public import CFSG.ClassicalInvolution.Q3.TL4AE286Aut
public import CFSG.ClassicalInvolution.Q3.TL4AE286Move
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Star

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent phi_injOn)
open scoped commutatorElement

section Gen

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_oddCoreOf_of_odd_of_twoGroup {L : Subgroup G}
    (h2 : IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) {c : G} (hc : c ∈ L)
    (hodd : Odd (orderOf c)) : c ∈ oddCoreOf L := by
  obtain ⟨k, hk⟩ := h2 (QuotientGroup.mk (⟨c, hc⟩ : ↥L))
  have hc1 : (⟨c, hc⟩ : ↥L) ^ orderOf c = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_orderOf_eq_one c)
  have h1 : (QuotientGroup.mk (⟨c, hc⟩ : ↥L) : ↥L ⧸ classicalInvolutionOddCore ↥L) ^
      orderOf c = 1 := by
    rw [← QuotientGroup.mk_pow, hc1, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (orderOf c) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  have h3 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_of_pow_eq_one hk)
  have h4 : (⟨c, hc⟩ : ↥L) ∈ classicalInvolutionOddCore ↥L :=
    (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3)
  exact ⟨_, h4, rfl⟩

theorem le_sup_oddCoreOf_of_isSylow2In {L P : Subgroup G}
    (h2 : IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) (hP : IsSylow2In P L) :
    L ≤ P ⊔ oddCoreOf L := by
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥L)) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hS := isSylow2In_map_mk hodd (hP.subgroupOf (le_refl L))
  rw [Subgroup.subgroupOf_self,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hS
  have htop := hS.2.2 ⊤ le_rfl (h2.to_subgroup ⊤) hS.1
  intro z hz
  have hmem : QuotientGroup.mk' (classicalInvolutionOddCore ↥L) (⟨z, hz⟩ : ↥L) ∈
      (P.subgroupOf L).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥L)) := by
    rw [← htop]
    exact Subgroup.mem_top _
  obtain ⟨s, hs, hsz⟩ := Subgroup.mem_map.mp hmem
  have h1 : s⁻¹ * ⟨z, hz⟩ ∈ classicalInvolutionOddCore ↥L := QuotientGroup.eq.mp hsz
  have h2' : (s : G)⁻¹ * z ∈ oddCoreOf L := ⟨_, h1, by simp⟩
  have e : z = (s : G) * ((s : G)⁻¹ * z) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hs))
    (Subgroup.mem_sup_right h2')

theorem comm_mem_oddCoreOf_of_sylow {L P : Subgroup G}
    (h2 : IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) (hP : IsSylow2In P L) {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (hyP : ∀ p ∈ P, ⁅y, p⁆ ∈ oddCoreOf L) :
    ∀ k ∈ L, ⁅y, k⁆ ∈ oddCoreOf L := by
  intro k hk
  have hPN : P ≤ Subgroup.normalizer (oddCoreOf L : Set G) := fun p hp =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hP.1 hp))
  have hk' : k ∈ oddCoreOf L ⊔ P := by
    rw [sup_comm]
    exact le_sup_oddCoreOf_of_isSylow2In h2 hP hk
  obtain ⟨o, ho, p, hp, rfl⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hPN hk'
  have hyO : y * o * y⁻¹ ∈ oddCoreOf L :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer hy) o).mp ho
  have e : ⁅y, o * p⁆ = (y * o * y⁻¹) * ⁅y, p⁆ * o⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (oddCoreOf L).mul_mem ((oddCoreOf L).mul_mem hyO (hyP p hp)) ((oddCoreOf L).inv_mem ho)

theorem exists_pow_three_conj {A : Type} [Group A] [Finite A] {H : Subgroup A} (β : MulAut ↥H)
    {k : ℕ} (hβ : β ^ 3 ^ k = 1) {x₁ : A}
    (hx₁ : ∀ g : ↥H, ((β g : ↥H) : A) = x₁ * g * x₁⁻¹) :
    ∃ x : A, IsPGroup 3 (Subgroup.zpowers x) ∧ ∀ g : ↥H, ((β g : ↥H) : A) = x * g * x⁻¹ := by
  obtain ⟨a, s, hs, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x₁).ne' 3 (by norm_num)
  have hcop : Nat.Coprime s (3 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hs).symm
  have he1 : s ^ Nat.totient (3 ^ k) % 3 ^ k = 1 % 3 ^ k := Nat.ModEq.pow_totient hcop
  have hpow : ∀ j : ℕ, ∀ g : ↥H, (((β ^ j) g : ↥H) : A) = x₁ ^ j * g * (x₁ ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro g; simp
    | succ j ih =>
      intro g
      rw [pow_succ' β j, MulAut.mul_apply, hx₁, ih, pow_succ' x₁ j]
      group
  have hβe : β ^ s ^ Nat.totient (3 ^ k) = β := by
    rw [pow_eq_pow_mod _ hβ, he1, ← pow_eq_pow_mod 1 hβ, pow_one]
  refine ⟨x₁ ^ s ^ Nat.totient (3 ^ k), ?_, fun g => ?_⟩
  · apply isPGroup_zpowers_of_pow_three_pow (a := a)
    have hpos : 0 < Nat.totient (3 ^ k) := Nat.totient_pos.mpr (by positivity)
    obtain ⟨c, hc⟩ : s ∣ s ^ Nat.totient (3 ^ k) := dvd_pow_self s hpos.ne'
    rw [← pow_mul, hc, show s * c * 3 ^ a = (3 ^ a * s) * c by ring, ← hN, pow_mul,
      pow_orderOf_eq_one, one_pow]
  · rw [← hpow, hβe]

end Gen

section Cit3


theorem tightAE286NoneR_three (n : ℕ) : TightAE286NoneR 3 n := by
  intro h117 h117p Y _ _ R S t hL _ J hJ hbad J' hJ' hJJ' hAE hyE
  obtain ⟨y, hy3, hyt, hyJ, hyJ', ⟨T, hT, hyT, x₀, hx₀, hx₀ne⟩, P, hP, hyP⟩ := hyE
  obtain ⟨m, hm5, hm7, ⟨I⟩⟩ := hAE
  have h := TightLargeHypR.typeRFam hL
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hJx := xMem_of_mem_omegaNbr_core hL hJ
  have hJ'x := xMem_of_mem_omegaNbr_core hL hJ'
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  obtain ⟨w', hw'⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ'.1
  have he : w' = t * u := hbad J' hJ' hJJ' u w' hu hw'
  have hPJ : secImg (CoreAssembly.conjClass (tightCore R)) t J ∈ coreLinkFam R t := ⟨J, hJ, rfl⟩
  have hPJ' : secImg (CoreAssembly.conjClass (tightCore R)) t J' ∈ coreLinkFam R t :=
    ⟨J', hJ', rfl⟩
  obtain ⟨α, hα, b, hlab⟩ := I.label _ hPJ
  have hlab' := map_eq_memBar_not_of_mul_eq hL hm5 hm7 I hJ hJ' hu hw' he hlab
  have hcl := conjInvariant_conjClass (tightCore R)
  obtain ⟨a, ha⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
  have ha' : y ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hβ1 : I.inducedAutOf hm5 (linkAct hL hyt) ^ 3 ^ a = 1 :=
    I.inducedAutOf_pow_eq_one hm5 (linkAct_pow_eq_one hL hyt ha')
  obtain ⟨x₁, hx₁⟩ := h117 m hm5 hm7 (I.inducedAutOf hm5 (linkAct hL hyt))
    (inducedAutOf_linkAct_memberPerm hL hm5 I hyt)
  obtain ⟨x, hx3, hx⟩ := exists_pow_three_conj _ hβ1 hx₁
  have hconjφ : ∀ l : ↥(pSpan (coreLinkFam R t)), I.φ (linkAct hL hyt l) = x * I.φ l * x⁻¹ := by
    intro l
    have h1 := hx (I.toModel l)
    rw [I.inducedAutOf_apply hm5] at h1
    exact h1
  have hmapσ : ∀ {L : Subgroup Y}, y ∈ Subgroup.normalizer (L : Set Y) →
      (secImg (CoreAssembly.conjClass (tightCore R)) t L).map (secAct hcl hyt).toMonoidHom =
        secImg (CoreAssembly.conjClass (tightCore R)) t L := by
    intro L hyL
    rw [← secImg_conjSub_eq_map hcl hyt L, conjSub_eq_of_mem_normalizer hyL]
  have hxN : ∀ {L : Subgroup Y} {c : Bool}, y ∈ Subgroup.normalizer (L : Set Y) →
      ((secImg (CoreAssembly.conjClass (tightCore R)) t L).subgroupOf
        (pSpan (coreLinkFam R t))).map I.φ = AE.memBar α hα c →
      x ∈ Subgroup.normalizer ((AE.memBar α hα c : Subgroup (AE.AEQ m)) : Set (AE.AEQ m)) := by
    intro L c hyL hlabL
    refine mem_normalizer_of_forall_conj_mem fun k hk => ?_
    rw [← hlabL] at hk ⊢
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hk
    rw [← hconjφ l]
    refine Subgroup.mem_map.mpr ⟨linkAct hL hyt l, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, coe_linkAct, ← hmapσ hyL]
    exact ⟨(l : SecQuot (CoreAssembly.conjClass (tightCore R)) t),
      Subgroup.mem_subgroupOf.mp hl, rfl⟩
  have hσJ' : ∀ kb ∈ secImg (CoreAssembly.conjClass (tightCore R)) t J',
      secAct hcl hyt kb = kb := by
    have hcomm : ∀ k ∈ J', ⁅y, k⁆ ∈ oddCoreOf J' :=
      comm_mem_oddCoreOf_of_sylow (h.twoGroup J' hJ'.1) hP hyJ' fun p hp => by
        rw [commutatorElement_def, hyP p hp, mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
    intro kb hkb
    have h1 := secAct_mul_inv_mem hcl hyt hJ'x hyJ' hcomm kb hkb
    have hσkb : secAct hcl hyt kb ∈ secImg (CoreAssembly.conjClass (tightCore R)) t J' := by
      rw [← hmapσ hyJ']
      exact ⟨kb, hkb, rfl⟩
    have hmem : secAct hcl hyt kb * kb⁻¹ ∈ secImg (CoreAssembly.conjClass (tightCore R)) t J' :=
      Subgroup.mul_mem _ hσkb (Subgroup.inv_mem _ hkb)
    have h2 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h1
      ((isPGroup_secImg_of_aeIdent hL I hPJ').to_le (Subgroup.zpowers_le.mpr hmem))
    exact mul_inv_eq_one.mp h2
  have hxC' : ∀ k ∈ AE.memBar α hα (!b), x * k = k * x := by
    intro k hk
    rw [← hlab'] at hk
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hk
    have h1 : linkAct hL hyt l = l :=
      Subtype.ext (by rw [coe_linkAct]; exact hσJ' _ (Subgroup.mem_subgroupOf.mp hl))
    have h2 := hconjφ l
    rw [h1] at h2
    calc x * I.φ l = x * I.φ l * x⁻¹ * x := by group
      _ = I.φ l * x := by rw [← h2]
  have hxC := comm_memBar_of_twin h117p hm5 hm7 α hα b hx3 (hxN hyJ hlab) (hxN hyJ' hlab') hxC'
  have h8 := natCard_secImg_of_aeIdent hL I hPJ
  have hσJ : ∀ kb ∈ secImg (CoreAssembly.conjClass (tightCore R)) t J,
      secAct hcl hyt kb = kb := by
    intro kb hkb
    have hσkb : secAct hcl hyt kb ∈ secImg (CoreAssembly.conjClass (tightCore R)) t J := by
      rw [← hmapσ hyJ]
      exact ⟨kb, hkb, rfl⟩
    have hφkb : I.φ ⟨kb, le_pSpan hPJ hkb⟩ ∈ AE.memBar α hα b := by
      rw [← hlab]
      exact ⟨⟨kb, le_pSpan hPJ hkb⟩, Subgroup.mem_subgroupOf.mpr hkb, rfl⟩
    have h1 := hconjφ ⟨kb, le_pSpan hPJ hkb⟩
    have h2 : linkAct hL hyt ⟨kb, le_pSpan hPJ hkb⟩ = ⟨_, le_pSpan hPJ hσkb⟩ := Subtype.ext rfl
    rw [h2, hxC _ hφkb, mul_inv_cancel_right] at h1
    exact phi_injOn I.φ hm5 hPJ h8 hlab hσkb hkb h1
  obtain ⟨P₀, hP₀, hP₀t⟩ := XMem.exists_sylow hJx
  have hP₀c : P₀ ≤ coreAt t J := le_coreAt t hP₀.2.1 hP₀.1 hP₀t
  have hyY := mem_normalizer_layerY hcl hyt
  have hyP₀ : ∀ p ∈ P₀, ⁅y, p⁆ ∈ oddCoreOf J := by
    intro p hp
    have hpY : p ∈ layerY (CoreAssembly.conjClass (tightCore R)) t :=
      coreAt_le_layerY hJx (hP₀c hp)
    have hypY : y * p * y⁻¹ ∈ layerY (CoreAssembly.conjClass (tightCore R)) t :=
      (Subgroup.mem_normalizer_iff.mp hyY p).mp hpY
    have e := s26Act_mk (layerY (CoreAssembly.conjClass (tightCore R)) t) ⟨y, hyY⟩ ⟨p, hpY⟩
      ⟨y * p * y⁻¹, hypY⟩ rfl
    have hfix := hσJ _ ⟨⟨p, hpY⟩, Subgroup.mem_subgroupOf.mpr (hP₀c hp), rfl⟩
    have h1 : (⟨y * p * y⁻¹, hypY⟩ : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t))⁻¹ *
        ⟨p, hpY⟩ ∈ classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore R)) t) :=
      QuotientGroup.eq.mp (e.symm.trans hfix)
    have hd : (y * p * y⁻¹)⁻¹ * p ∈ oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) :=
      ⟨_, h1, by simp⟩
    have hpJ : p ∈ J := hP₀.1 hp
    have hdJ : (y * p * y⁻¹)⁻¹ * p ∈ J :=
      J.mul_mem (J.inv_mem ((Subgroup.mem_normalizer_iff.mp hyJ p).mp hpJ)) hpJ
    have hdodd : Odd (orderOf ((y * p * y⁻¹)⁻¹ * p)) :=
      (oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hd)
    have hdO := mem_oddCoreOf_of_odd_of_twoGroup (h.twoGroup J hJ.1) hdJ hdodd
    have hpdO : p * ((y * p * y⁻¹)⁻¹ * p) * p⁻¹ ∈ oddCoreOf J :=
      (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hpJ)) _).mp hdO
    have e2 : ⁅y, p⁆ = (p * ((y * p * y⁻¹)⁻¹ * p) * p⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e2]
    exact (oddCoreOf J).inv_mem hpdO
  have hyJc := comm_mem_oddCoreOf_of_sylow (h.twoGroup J hJ.1) hP₀ hyJ hyP₀
  apply hx₀ne
  have h1 : ⁅y, x₀⁆ ∈ T := by
    rw [commutatorElement_def]
    exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp hyT x₀).mp hx₀) (T.inv_mem hx₀)
  have h2 : ⁅y, x₀⁆ ∈ T ⊓ oddCoreOf J := ⟨h1, hyJc x₀ (hT.1 hx₀)⟩
  rw [S1916.inf_oddCoreOf_eq_bot hT.2.1, Subgroup.mem_bot, commutatorElement_def] at h2
  exact mul_inv_eq_one.mp h2

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
