module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.Balance.Lift
public import CFSG.GH74.GLS.Balance.Reduce
public import CFSG.GH74.Generic.BProg.B1.Lift1

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  CFSG.GH74.Generic.BProg.B1 Subgroup
open scoped MatrixGroups

namespace SolvLiftQuasi

theorem pPrimeCoreOf_le_of_subnormalIn {Q : Type} [Group Q] [Finite Q] {L M : Subgroup Q}
    (hLM : L ≤ M) (h : (L.subgroupOf M).IsSubnormal) : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := pPrimeCoreOf_le_of_subnormal (X := ↥M) 2 h
  let e : ↥(L.subgroupOf M) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLM
  have h2 : pPrimeCoreOf 2 L = (pPrimeCoreOf 2 (L.subgroupOf M)).map M.subtype := by
    unfold pPrimeCoreOf
    rw [Subgroup.map_map, ← pPrimeCore_map_iso 2 e, Subgroup.map_map]
    rfl
  rw [h2]
  exact Subgroup.map_mono h1

variable {G : Type} [Group G] [Finite G]

theorem exists_quasi_e {x e : G} {K : Subgroup G} (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hxe : x * e = e * x) (he : orderOf e = 2) {Ie : Subgroup (CentralizerBar x)}
    (hIe : IsQuasi2CompIn (centralizer ({bar x e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie)
    (P : Subgroup G) (hPA : P ≤ centralizer ({x} : Set G) ⊓ centralizer ({e} : Set G))
    (hP : ∀ (g : G) (hg : g ∈ centralizer ({x} : Set G)), g ∈ P → (∃ k : ℕ, g ^ (2 ^ k) = 1) →
      proj x ⟨g, hg⟩ ∈ Ie) :
    ∃ V : Subgroup G,
      (Balance.IsSolvTwoCompSL23In (centralizer ({x} : Set G) ⊓ centralizer ({e} : Set G)) V ∨
        IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({e} : Set G)) V) ∧
      oPrimeResidualOf 2 P ≤ oPrimeResidualOf 2 V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({e} : Set G) with hA
  have hAC : A ≤ centralizer ({x} : Set G) := inf_le_left
  set f : ↥A →* CentralizerBar x := projRes hAC with hf
  have hrange : f.range = centralizer ({bar x e} : Set (CentralizerBar x)) := by
    rw [hf, range_projRes, hA, ← centralizer_closure_pair x e]
    exact imgBar_centralizer_closure_pair hxe he
  have hodd : ¬ 2 ∣ Nat.card f.ker := not_two_dvd_card_ker_projRes hAC
  rcases hIe with hIe | hIe
  ·
    have hIe' : IsPCompIn 2 f.range Ie := by
      rw [hrange]
      exact isPCompIn_centralizer_of_isPCompIn_inf hK _ hIe
    obtain ⟨hV, -⟩ := exists_isPCompIn_lift_of_odd_ker f hodd hIe'
    refine ⟨oPrimeResidualOf 2 ((Ie.comap f).map A.subtype), Or.inr hV, ?_⟩
    refine Balance.oPrimeResidualOf_le_of_two_elements fun g hg h2 => ?_
    have hgA : g ∈ A := hPA hg
    have hgIe : proj x ⟨g, hAC hgA⟩ ∈ Ie := hP g (hAC hgA) hg h2
    have hg1 : g ∈ (Ie.comap f).map A.subtype := ⟨⟨g, hgA⟩, hgIe, rfl⟩
    exact Balance.mem_oPrimeResidualOf_of_two_element
      (Balance.mem_oPrimeResidualOf_of_two_element hg1 h2) h2
  ·
    set H : Subgroup (CentralizerBar x) :=
      centralizer ({bar x e} : Set (CentralizerBar x)) ⊓ imgBar x K with hH
    have hHr : H ≤ f.range := by
      rw [hrange]
      exact inf_le_left
    have hsubH : (H.subgroupOf f.range).IsSubnormal := by
      rw [hrange]
      exact isSubnormal_centralizer_inf_imgBar hK (bar x e)
    obtain ⟨Lb', hLb'sub, ⟨eL⟩, hIeEq⟩ := hIe
    set mkH : ↥H →* ↥H ⧸ pPrimeCore 2 ↥H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hmk
    have hIeH : Ie ≤ H := by
      rw [hIeEq]
      exact Subgroup.map_subtype_le _
    have hsubIeH : (Ie.subgroupOf H).IsSubnormal := by
      have h1 : Ie.subgroupOf H = Lb'.comap mkH := by
        rw [hIeEq]
        exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
      rw [h1]
      exact hLb'sub.comap _
    have hsubIe : (Ie.subgroupOf f.range).IsSubnormal :=
      isSubnormal_subgroupOf_trans hIeH hHr hsubIeH hsubH
    set f' : ↥A →* ↥f.range := f.rangeRestrict with hf'
    have hf's : Function.Surjective f' := f.rangeRestrict_surjective
    let Vt : Subgroup ↥A := (Ie.subgroupOf f.range).comap f'
    have hmemVt : ∀ a : ↥A, a ∈ Vt ↔ f a ∈ Ie := fun a => Iff.rfl
    have hVtsub : Vt.IsSubnormal := hsubIe.comap f'
    have hψ0 : ∀ v : ↥Vt, f (v : ↥A) ∈ H := fun v => hIeH ((hmemVt v).1 v.2)
    let ψ0 : ↥Vt →* ↥H := (f.comp Vt.subtype).codRestrict H hψ0
    have hψ1 : ∀ v : ↥Vt, mkH (ψ0 v) ∈ Lb' := by
      intro v
      have hv : f (v : ↥A) ∈ (Lb'.comap mkH).map H.subtype := by
        rw [← hIeEq]
        exact (hmemVt v).1 v.2
      obtain ⟨z, hz, hzv⟩ := hv
      have hzz : ψ0 v = z := Subtype.ext hzv.symm
      rw [hzz]
      exact hz
    let ψ1 : ↥Vt →* ↥Lb' := (mkH.comp ψ0).codRestrict Lb' hψ1
    let χ : ↥Vt →* SL(2, ZMod 3) := eL.toMonoidHom.comp ψ1
    have hχs : Function.Surjective χ := by
      intro u
      obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H)
        ((eL.symm u : ↥Lb') : ↥H ⧸ pPrimeCore 2 ↥H)
      have hzc : z ∈ Lb'.comap mkH := by
        show mkH z ∈ Lb'
        rw [show mkH z = ((eL.symm u : ↥Lb') : ↥H ⧸ pPrimeCore 2 ↥H) from hz]
        exact (eL.symm u).2
      have hzIe : (z : CentralizerBar x) ∈ Ie := by
        rw [hIeEq]
        exact ⟨z, hzc, rfl⟩
      obtain ⟨a, ha⟩ := hHr z.2
      have haVt : a ∈ Vt := by
        refine (hmemVt a).2 ?_
        rw [ha]
        exact hzIe
      refine ⟨⟨a, haVt⟩, ?_⟩
      have hz' : ψ0 ⟨a, haVt⟩ = z := Subtype.ext ha
      have hψ : ψ1 ⟨a, haVt⟩ = eL.symm u := Subtype.ext (by
        change mkH (ψ0 ⟨a, haVt⟩) = _
        rw [hz']
        exact hz)
      show eL (ψ1 ⟨a, haVt⟩) = u
      rw [hψ]
      exact eL.apply_symm_apply u
    have hkerA : ∀ n : ↥Vt, χ n = 1 → ((n : ↥A) : ↥A) ∈ pPrimeCore 2 ↥A := by
      intro n hn
      have hn' : eL (ψ1 n) = 1 := hn
      have h1 : ψ1 n = 1 := eL.map_eq_one_iff.1 hn'
      have h2 : mkH (ψ0 n) = 1 := congrArg Subtype.val h1
      have h3 : ψ0 n ∈ pPrimeCore 2 ↥H := (QuotientGroup.eq_one_iff _).1 h2
      have h4 : (f (n : ↥A) : CentralizerBar x) ∈ pPrimeCoreOf 2 H := ⟨ψ0 n, h3, rfl⟩
      have h5 : pPrimeCoreOf 2 H ≤ pPrimeCoreOf 2 f.range := pPrimeCoreOf_le_of_subnormalIn hHr hsubH
      obtain ⟨o', ho', hoe⟩ := h5 h4
      have hf'n : f' (n : ↥A) = o' := Subtype.ext hoe.symm
      have hKer : Odd (Nat.card f'.ker) := by
        rw [hf', MonoidHom.ker_rangeRestrict]
        exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
      obtain ⟨hmap, hker⟩ := Balance.map_pPrimeCore_eq f' hf's hKer
      rw [← hmap] at ho'
      obtain ⟨o, ho, hof⟩ := ho'
      have hdiv : (n : ↥A) * o⁻¹ ∈ f'.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hof, hf'n, mul_inv_cancel]
      have h6 := mul_mem (hker hdiv) ho
      simpa using h6
    have hsolv := Balance.isSolvTwoCompSL23_of_subnormal Vt hVtsub χ hχs hkerA
    refine ⟨(Vt ⊔ pPrimeCore 2 ↥A).map A.subtype, Or.inl ⟨Subgroup.map_subtype_le _, ?_⟩, ?_⟩
    · have e1 : ((Vt ⊔ pPrimeCore 2 ↥A).map A.subtype).subgroupOf A = Vt ⊔ pPrimeCore 2 ↥A :=
        Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
      rw [e1]
      exact hsolv
    · refine Balance.oPrimeResidualOf_le_of_two_elements fun g hg h2 => ?_
      have hgA : g ∈ A := hPA hg
      have hgIe : proj x ⟨g, hAC hgA⟩ ∈ Ie := hP g (hAC hgA) hg h2
      have hgV : g ∈ (Vt ⊔ pPrimeCore 2 ↥A).map A.subtype :=
        ⟨⟨g, hgA⟩, Subgroup.mem_sup_left ((hmemVt ⟨g, hgA⟩).2 hgIe), rfl⟩
      exact Balance.mem_oPrimeResidualOf_of_two_element hgV h2

end SolvLiftQuasi

end CFSG.GH74.Generic.BProg.B3
