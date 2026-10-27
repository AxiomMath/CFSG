module

import CFSG.LinearAlgebra.LinearGroups.OddPStableActions
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR10
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR11
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR7

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Pp (J : Subgroup G) (p : ℕ) : Subgroup G :=
  (pCore p ↥(pPrimeCoreOf 2 J)).map (pPrimeCoreOf 2 J).subtype

omit [Finite G] in
theorem Pp_le_O (J : Subgroup G) (p : ℕ) : Pp J p ≤ pPrimeCoreOf 2 J :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem Pp_isPGroup (J : Subgroup G) (p : ℕ) : IsPGroup p ↥(Pp J p) := by
  intro g
  obtain ⟨g, hg⟩ := g
  obtain ⟨o, ho, rfl⟩ := hg
  obtain ⟨n, hn⟩ := pCore_isPGroup (p := p) (G := ↥(pPrimeCoreOf 2 J)) ⟨o, ho⟩
  refine ⟨n, Subtype.ext ?_⟩
  have := congrArg (fun z : ↥(pCore p ↥(pPrimeCoreOf 2 J)) => ((z : ↥(pPrimeCoreOf 2 J)) : G)) hn
  simpa using this

omit [Finite G] in
theorem conj_mem_Pp {J : Subgroup G} {p : ℕ} {g : G} (hg : g ∈ normalizer (J : Set G)) {z : G}
    (hz : z ∈ Pp J p) : g * z * g⁻¹ ∈ Pp J p := by
  obtain ⟨o, ho, rfl⟩ := hz
  have hgO : g ∈ normalizer ((pPrimeCoreOf 2 J : Subgroup G) : Set G) :=
    TwoThin.mem_normalizer_pPrimeCoreOf hg
  have hmap := Subgroup.characteristic_iff_map_eq.mp
    (inferInstance : (pCore p ↥(pPrimeCoreOf 2 J)).Characteristic)
    ((pPrimeCoreOf 2 J).normalizerMonoidHom ⟨g, hgO⟩)
  refine ⟨(pPrimeCoreOf 2 J).normalizerMonoidHom ⟨g, hgO⟩ o, ?_, ?_⟩
  · rw [← hmap]
    exact Subgroup.mem_map_of_mem _ ho
  · simp [Subgroup.normalizerMonoidHom_apply_apply_coe]

omit [Finite G] in
theorem mem_normalizer_Pp {J : Subgroup G} {p : ℕ} {g : G} (hg : g ∈ normalizer (J : Set G)) :
    g ∈ normalizer (Pp J p : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => conj_mem_Pp hg hz, fun hz => ?_⟩
  have := conj_mem_Pp ((normalizer (J : Set G)).inv_mem hg) hz
  simpa [mul_assoc] using this

theorem isQuasisimple_of_pPrimeCore_le_center {J : Type*} [Group J] [Finite J]
    (hperf : Group.IsPerfect J) (hsimple : IsSimpleGroup (J ⧸ pPrimeCore 2 J))
    (hle : pPrimeCore 2 J ≤ Subgroup.center J) : CFSG.IsQuasisimple J := by
  have : Group.IsPerfect J := hperf
  have hnt : Nontrivial (J ⧸ pPrimeCore 2 J) := hsimple.toNontrivial
  have hcen : Subgroup.center J = pPrimeCore 2 J := by
    refine le_antisymm ?_ hle
    have hmap : (Subgroup.center J).map (QuotientGroup.mk' (pPrimeCore 2 J)) = ⊥ ∨
        (Subgroup.center J).map (QuotientGroup.mk' (pPrimeCore 2 J)) = ⊤ := by
      have : ((Subgroup.center J).map (QuotientGroup.mk' (pPrimeCore 2 J))).Normal :=
        Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
      exact hsimple.eq_bot_or_eq_top_of_normal _
    rcases hmap with h | h
    · intro z hz
      have : QuotientGroup.mk' (pPrimeCore 2 J) z ∈
          (Subgroup.center J).map (QuotientGroup.mk' (pPrimeCore 2 J)) := ⟨z, hz, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff z).1 this
    · exfalso
      have hcomm : ∀ a b : J, a * b = b * a := by
        intro a b
        have ha : QuotientGroup.mk' (pPrimeCore 2 J) a ∈
            (Subgroup.center J).map (QuotientGroup.mk' (pPrimeCore 2 J)) := by rw [h]; trivial
        obtain ⟨z, hz, hza⟩ := ha
        have : z⁻¹ * a ∈ pPrimeCore 2 J := QuotientGroup.eq.1 hza
        have hzc := hle this
        have ha' : a = z * (z⁻¹ * a) := by group
        rw [ha']
        have h1 := Subgroup.mem_center_iff.1 hz b
        have h2 := Subgroup.mem_center_iff.1 hzc b
        calc z * (z⁻¹ * a) * b = z * ((z⁻¹ * a) * b) := by group
          _ = z * (b * (z⁻¹ * a)) := by rw [h2]
          _ = (z * b) * (z⁻¹ * a) := by group
          _ = (b * z) * (z⁻¹ * a) := by rw [h1]
          _ = b * (z * (z⁻¹ * a)) := by group
      have hab : IsMulCommutative J := ⟨⟨fun a b => hcomm a b⟩⟩
      have hsub : Subsingleton J := by
        by_contra hns
        have : Nontrivial J := not_subsingleton_iff_nontrivial.1 hns
        exact Group.IsPerfect.not_isMulCommutative J hab
      have : Subsingleton (J ⧸ pPrimeCore 2 J) := inferInstance
      exact not_subsingleton_iff_nontrivial.2 hnt this
  have e : (J ⧸ Subgroup.center J) ≃* (J ⧸ pPrimeCore 2 J) :=
    QuotientGroup.quotientMulEquivOfEq hcen
  have hsimpleC : IsSimpleGroup (J ⧸ Subgroup.center J) := (e.isSimpleGroup_congr).2 hsimple
  refine ⟨hperf, hsimpleC, ?_⟩
  by_contra hno
  push Not at hno
  have hq : IsMulCommutative (J ⧸ Subgroup.center J) := ⟨⟨fun a b => hno a b⟩⟩
  have hnt2 : Nontrivial (J ⧸ Subgroup.center J) := hsimpleC.toNontrivial
  exact Group.IsPerfect.not_isMulCommutative (J ⧸ Subgroup.center J) hq

theorem exists_prime_noncentral {J : Subgroup G} (hperf : Group.IsPerfect ↥J)
    (hsimple : IsSimpleGroup (kBar J)) (hnqs : ¬ CFSG.IsQuasisimple ↥J) {x : G} (hxJ : x ∈ J)
    (hxO : x ∉ pPrimeCoreOf 2 J) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ z ∈ Pp J p, x * z ≠ z * x := by
  classical
  have : Group.IsPerfect ↥J := hperf
  by_contra hno
  have hno' : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ z ∈ Pp J p, x * z = z * x := by
    intro p hp hp2 z hz
    by_contra h
    exact hno ⟨p, hp, hp2, z, hz, h⟩
  have hno2 : ∀ p : ℕ, p.Prime → ∀ z ∈ Pp J p, x * z = z * x := by
    intro p hp z hz
    by_cases hp2 : p = 2
    · subst hp2
      have hzO : z ∈ pPrimeCoreOf 2 J := Pp_le_O J 2 hz
      have hodd : Odd (orderOf z) :=
        Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd J) (Subgroup.orderOf_dvd_natCard _ hzO)
      obtain ⟨n, hn⟩ := Pp_isPGroup J 2 ⟨z, hz⟩
      have hz2 : z ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have hd : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hz2
      have h1 : orderOf z = 1 := by
        have hcop : Nat.Coprime (orderOf z) 2 := Nat.coprime_two_right.2 hodd
        exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n hcop) hd
      rw [orderOf_eq_one_iff.1 h1]
      simp
    · exact hno' p hp hp2 z hz
  set O : Subgroup G := pPrimeCoreOf 2 J with hO
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.1 (coprime_card_pPrimeCoreOf J)
  have hsolv : Group.IsSolvable ↥O := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd
  set F : Subgroup ↥O := fittingSubgroup ↥O with hF
  set FG : Subgroup G := F.map O.subtype with hFG
  have hFGeq : FG = ⨆ p : (Nat.card ↥O).primeFactors, Pp J (p : ℕ) := by
    rw [hFG, hF, CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore, Subgroup.map_iSup]
    rfl
  have hxFG : x ∈ centralizer (FG : Set G) := by
    have hle : Subgroup.zpowers x ≤ centralizer ((⨆ p : (Nat.card ↥O).primeFactors, Pp J (p : ℕ) :
        Subgroup G) : Set G) := by
      refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
        (fun p : (Nat.card ↥O).primeFactors => Pp J (p : ℕ)) (fun p => ?_)
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hno2 p (Nat.prime_of_mem_primeFactors p.2) z hz).symm
    rw [hFGeq]
    exact hle (Subgroup.mem_zpowers x)
  have hJFG : ∀ j ∈ J, ∀ f ∈ FG, j * f * j⁻¹ ∈ FG := by
    intro j hj f hf
    rw [hFGeq] at hf ⊢
    refine Subgroup.iSup_induction (fun p : (Nat.card ↥O).primeFactors => Pp J (p : ℕ))
      (C := fun f => j * f * j⁻¹ ∈ ⨆ p : (Nat.card ↥O).primeFactors, Pp J (p : ℕ)) hf ?_ ?_ ?_
    · intro q z hz
      exact Subgroup.mem_iSup_of_mem q (conj_mem_Pp (Subgroup.le_normalizer hj) hz)
    · simp
    · intro a b ha hb
      have : j * (a * b) * j⁻¹ = (j * a * j⁻¹) * (j * b * j⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
  let C : Subgroup ↥J := (centralizer (FG : Set G)).comap J.subtype
  have hCmem : ∀ c : ↥J, c ∈ C ↔ ∀ f ∈ FG, f * (c : G) = (c : G) * f := by
    intro c
    show (c : G) ∈ centralizer (FG : Set G) ↔ _
    rw [Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have hCnormal : C.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hCmem] at hn ⊢
    intro h hh
    have hh' : (g : G)⁻¹ * h * (g : G) ∈ FG := by
      have := hJFG ((g : G)⁻¹) (J.inv_mem g.2) h hh
      simpa using this
    have h1 := hn _ hh'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc h * ((g : G) * (n : G) * (g : G)⁻¹) = (g : G) * (((g : G)⁻¹ * h * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
      _ = (g : G) * ((n : G) * ((g : G)⁻¹ * h * (g : G))) * (g : G)⁻¹ := by rw [h1]
      _ = ((g : G) * (n : G) * (g : G)⁻¹) * h := by group
  have hxC : (⟨x, hxJ⟩ : ↥J) ∈ C := by
    rw [hCmem]
    intro f hf
    exact (Subgroup.mem_centralizer_iff.1 hxFG f hf)
  have hOJodd : Odd (Nat.card (pPrimeCore 2 ↥J)) :=
    Nat.coprime_two_left.1 pPrimeCore_coprime_card
  by_cases hCle : C ≤ pPrimeCore 2 ↥J
  · apply hxO
    exact C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hxJ, hCle hxC⟩
  · have hCtop : C = ⊤ := eq_top_of_normal_not_le hOJodd hsimple C hCle
    have hJc : ∀ j ∈ J, ∀ f ∈ FG, f * j = j * f := by
      intro j hj f hf
      have : (⟨j, hj⟩ : ↥J) ∈ C := by rw [hCtop]; trivial
      exact (hCmem _).1 this f hf
    have hOF : O ≤ FG := by
      intro o ho
      have hoJ : o ∈ J := TwoThin.pPrimeCoreOf_le J ho
      have hoc : (⟨o, ho⟩ : ↥O) ∈ centralizer (F : Set ↥O) := by
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact hJc o hoJ f ⟨f, hf, rfl⟩
      have hoF : (⟨o, ho⟩ : ↥O) ∈ F :=
        CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hoc
      exact ⟨⟨o, ho⟩, hoF, rfl⟩
    apply hnqs
    refine isQuasisimple_of_pPrimeCore_le_center hperf hsimple (fun c hc => ?_)
    have hcO : (c : G) ∈ O := ⟨c, hc, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hJc j j.2 c (hOF hcO)).symm

theorem pStableAct_of_dihedral {J : Type} [Group J] [Finite J]
    (hdih : ∃ (S : Sylow 2 J) (n : ℕ), 2 ≤ n ∧
      Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* (S : Subgroup J)))
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup p Q)
    (ρ : J →* MulAut Q) : PStableAct p ρ := by
  classical
  obtain ⟨S, n, hn, hS⟩ := hdih
  have hst := CFSG.LinearGroups.dihedral_subgroup_actions_are_odd_p_stable S hn hS ⊤ hp hodd Q hQ
    (ρ.comp (Subgroup.subtype ⊤))
  intro x hq
  set ρ' : ↥(⊤ : Subgroup J) →* MulAut Q := ρ.comp (Subgroup.subtype ⊤) with hρ'
  have hx' := hst ⟨x, trivial⟩ (fun u => by
    rw [CFSG.GroupTheory.double_commutator_eq_one_iff]
    exact hq u)
  have hx'' : QuotientGroup.mk' ρ'.ker ⟨x, trivial⟩ ∈ pCore p (↥(⊤ : Subgroup J) ⧸ ρ'.ker) := hx'
  have hker : ρ'.ker.map (Subgroup.topEquiv : ↥(⊤ : Subgroup J) ≃* J).toMonoidHom = ρ.ker := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, trivial⟩, hz, rfl⟩
  let ψ : (↥(⊤ : Subgroup J) ⧸ ρ'.ker) ≃* (J ⧸ ρ.ker) :=
    QuotientGroup.congr ρ'.ker ρ.ker (Subgroup.topEquiv : ↥(⊤ : Subgroup J) ≃* J) hker
  have hpc := CFSG.pCore_map_iso p ψ
  have hmem : ψ (QuotientGroup.mk' ρ'.ker ⟨x, trivial⟩) ∈ pCore p (J ⧸ ρ.ker) := by
    rw [← hpc]
    exact Subgroup.mem_map_of_mem _ hx''
  have hψ : ψ (QuotientGroup.mk' ρ'.ker ⟨x, trivial⟩) = QuotientGroup.mk' ρ.ker x := rfl
  rw [hψ] at hmem
  exact hmem

theorem exists_lift_pElement {J B V : Subgroup G} {b : G} (hBN : B ≤ normalizer (J : Set G))
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hVB : V ≤ B) (hbB : b ∈ B) {c : kBar J}
    (hcp : Nat.Prime (orderOf c))
    (hVc : ∀ v (hv : v ∈ V), barAct J ⟨v, hBN (hVB hv)⟩ c = c)
    (hbc : barAct J ⟨b, hBN hbB⟩ c = c⁻¹) :
    ∃ x : G, ∃ hx : x ∈ J, (QuotientGroup.mk (⟨x, hx⟩ : ↥J) : kBar J) = c ∧
      (∃ k : ℕ, x ^ (orderOf c ^ k) = 1) ∧ (∀ v ∈ V, v * x = x * v) ∧ b * x * b⁻¹ = x⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨⟨g₀, hg₀⟩, rfl⟩ := QuotientGroup.mk_surjective c
  set O : Subgroup G := pPrimeCoreOf 2 J with hO
  have hOodd : ¬ 2 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (coprime_card_pPrimeCoreOf J)
  have hV2 : IsPGroup 2 ↥V := by
    have := isElementaryAbelian_le hBel hVB
    exact CFSG.IsElementaryAbelian.isPGroup 2 _
  have hnormO : ∀ g ∈ normalizer (J : Set G), g ∈ normalizer (O : Set G) := fun g hg =>
    TwoThin.mem_normalizer_pPrimeCoreOf hg
  have hVO : ∀ v ∈ V, ∀ o ∈ O, v * o * v⁻¹ ∈ O := fun v hv o ho =>
    (Subgroup.mem_normalizer_iff.1 (hnormO v (hBN (hVB hv))) o).1 ho
  have hb2 : b * b = 1 := by
    have := hBsq b hbB
    exact this
  have hbN : b ∈ normalizer (O : Set G) := hnormO b (hBN hbB)
  have hbV : ∀ v ∈ V, b * v = v * b := fun v hv => hBc b hbB v (hVB hv)
  have hkN : g₀ ∈ normalizer (O : Set G) := hnormO g₀ (Subgroup.le_normalizer hg₀)
  have hk : ∀ v ∈ V, g₀⁻¹ * (v * g₀ * v⁻¹) ∈ O := by
    intro v hv
    have h1 := hVc v hv
    rw [barAct_mk'] at h1
    have hmk : (QuotientGroup.mk ⟨v * g₀ * v⁻¹, normalizer_conj_mem v (hBN (hVB hv)) g₀ hg₀⟩ :
        kBar J) = QuotientGroup.mk ⟨g₀, hg₀⟩ := h1
    have hmem : g₀⁻¹ * (v * g₀ * v⁻¹) ∈ J :=
      J.mul_mem (J.inv_mem hg₀) (normalizer_conj_mem v (hBN (hVB hv)) g₀ hg₀)
    refine C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hmem, ?_⟩
    have h3 : (⟨g₀⁻¹ * (v * g₀ * v⁻¹), hmem⟩ : ↥J) =
        ((⟨v * g₀ * v⁻¹, normalizer_conj_mem v (hBN (hVB hv)) g₀ hg₀⟩ : ↥J)⁻¹ *
          ⟨g₀, hg₀⟩)⁻¹ := Subtype.ext (by simp)
    rw [h3]
    exact (pPrimeCore 2 ↥J).inv_mem (QuotientGroup.eq.1 hmk)
  have hkb : g₀ * (b * g₀ * b⁻¹) ∈ O := by
    have h1 := hbc
    rw [barAct_mk'] at h1
    have hbg : b * g₀ * b⁻¹ ∈ J := normalizer_conj_mem b (hBN hbB) g₀ hg₀
    have hmem : g₀ * (b * g₀ * b⁻¹) ∈ J := J.mul_mem hg₀ hbg
    refine C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hmem, ?_⟩
    have h2 : (QuotientGroup.mk (⟨g₀, hg₀⟩ : ↥J) : kBar J) *
        QuotientGroup.mk ⟨b * g₀ * b⁻¹, hbg⟩ = 1 := by
      rw [h1, mul_inv_cancel]
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at h2
    exact h2
  obtain ⟨o, ho, hofix, hoinv⟩ :=
    exists_fixed_inv_mem_coset hOodd hV2 hVO hb2 hbN hbV hkN hk hkb
  have hoJ : o ∈ J := TwoThin.pPrimeCoreOf_le J ho
  set g : G := g₀ * o with hg
  have hgJ : g ∈ J := J.mul_mem hg₀ hoJ
  have hmkg : (QuotientGroup.mk (⟨g, hgJ⟩ : ↥J) : kBar J) = QuotientGroup.mk ⟨g₀, hg₀⟩ := by
    rw [QuotientGroup.eq]
    obtain ⟨hoJ', hom⟩ := C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.1 ho
    have : (⟨g, hgJ⟩ : ↥J)⁻¹ * ⟨g₀, hg₀⟩ = (⟨o, hoJ'⟩ : ↥J)⁻¹ := Subtype.ext (by simp [hg])
    rw [this]
    exact (pPrimeCore 2 ↥J).inv_mem hom
  have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  rw [← hmkg] at hcp ⊢
  obtain ⟨n, hn, k, hk'⟩ := exists_pow_pPart g hg0 hcp
  set p₁ := orderOf (QuotientGroup.mk (⟨g, hgJ⟩ : ↥J) : kBar J) with hp₁
  refine ⟨g ^ n, J.pow_mem hgJ n, ?_, ⟨k, hk'⟩, ?_, ?_⟩
  · have : (QuotientGroup.mk (⟨g ^ n, J.pow_mem hgJ n⟩ : ↥J) : kBar J) =
        (QuotientGroup.mk (⟨g, hgJ⟩ : ↥J) : kBar J) ^ n := by
      rw [← QuotientGroup.mk_pow]; rfl
    rw [this, pow_eq_pow_mod n (pow_orderOf_eq_one _), ← hp₁, hn, Nat.mod_eq_of_lt hcp.one_lt, pow_one]
  · intro v hv
    have h1 := hofix v hv
    have h2 : v * g * v⁻¹ = g := h1
    have : v * g ^ n * v⁻¹ = g ^ n := by rw [← conj_pow, h2]
    exact (mul_inv_eq_iff_eq_mul.1 this)
  · have h2 : b * g * b⁻¹ = g⁻¹ := hoinv
    rw [← conj_pow, h2, inv_pow]

end CFSG.GH74.GLS.Th2.Obs
