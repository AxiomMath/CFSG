module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Tools
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20AltCent
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB Equiv

theorem exists_perm_of_pow_five (n : ℕ) (hn : 5 ≤ n) (α : MulAut (alternatingGroup (Fin n)))
    (h5 : α ^ 5 = 1) : ∃ σ : Perm (Fin n), MulAut.conjNormal σ = α ∧ σ ^ 5 = 1 := by
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
  have key : ∃ σ : Perm (Fin n), MulAut.conjNormal σ = α := by
    by_cases h6 : n = 6
    · subst h6
      have hout : IsPGroup 2 (CFSG.ComponentClassification.OuterAutomorphisms.Outer
          (alternatingGroup (Fin 6))) :=
        CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six
      obtain ⟨m, hm⟩ := hout (QuotientGroup.mk α :
        CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 6)))
      have h5' : (QuotientGroup.mk α :
          CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 6))) ^ 5
            = 1 := by
        rw [← QuotientGroup.mk_pow, h5]
        rfl
      have hd5 := orderOf_dvd_of_pow_eq_one h5'
      have hd2 := orderOf_dvd_of_pow_eq_one hm
      have hcop : Nat.Coprime 5 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
      have h1 : orderOf (QuotientGroup.mk α :
          CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 6))) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hd5 hd2
      rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
      obtain ⟨a, ha⟩ := h1
      refine ⟨(a : Perm (Fin 6)), ?_⟩
      rw [← ha]
      exact MulAut.conjNormal_val
    · obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn h6).2 α
      exact ⟨σ, hσ⟩
  obtain ⟨σ, hσ⟩ := key
  refine ⟨σ, hσ, hinj ?_⟩
  rw [map_pow, hσ, h5, map_one]

theorem fi22_card_ne_alt (m : ℕ) : m.factorial / 2 ≠ 64561751654400 := by
  intro h
  by_cases hm : m ≤ 16
  · have : m.factorial ≤ (16).factorial := Nat.factorial_le hm
    have h16 : (16).factorial = 20922789888000 := by decide +kernel
    omega
  · have : (17).factorial ≤ m.factorial := Nat.factorial_le (by omega)
    have h17 : (17).factorial = 355687428096000 := by decide +kernel
    omega

theorem noFi22Cfg_alt
    (n : ℕ) (hn : 5 ≤ n)
    (α : MulAut (alternatingGroup (Fin n))) (h5 : α ^ 5 = 1) :
    ¬ Fi22Cfg (alternatingGroup (Fin n)) α := by
  intro hcfg
  obtain ⟨hsimple, hcard⟩ := fi22_facts
  obtain ⟨σ, hσα, hσ5⟩ := exists_perm_of_pow_five n hn α h5
  obtain ⟨H, hH, f, hf⟩ := hcfg.subnormalQuotient
  let A := alternatingGroup (Fin n)
  let ι : A →* Perm (Fin n) := A.subtype
  let C : Subgroup (Perm (Fin n)) := Subgroup.centralizer ({σ} : Set (Perm (Fin n)))
  have hfix : ∀ a : A, α a = a ↔ ι a ∈ C := by
    intro a
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subtype.ext_iff, ← hσα, MulAut.conjNormal_apply]
    show σ * (a : Perm (Fin n)) * σ⁻¹ = a ↔ _
    rw [mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hX : (fixedSub α).map ι ≤ C := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hfix a).1 ha
  have hnorm : (((fixedSub α).map ι).subgroupOf C).Normal := by
    have heq : ((fixedSub α).map ι).subgroupOf C = A.subgroupOf C := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨a, -, ha⟩
        rw [← ha]
        exact a.2
      · intro hx
        exact ⟨⟨(x : Perm (Fin n)), hx⟩, (hfix ⟨(x : Perm (Fin n)), hx⟩).2 x.2, rfl⟩
    rw [heq]
    exact Subgroup.Normal.subgroupOf inferInstance C
  have hsn1 : IsSubnormal (H.map ι) ((fixedSub α).map ι) := isSubnormal_map' ι hH
  have hsn2 : IsSubnormal ((fixedSub α).map ι) C :=
    IsSubnormal.step hX hnorm (IsSubnormal.refl C)
  have hsn := isSubnormal_trans' hsn1 hsn2
  let t : ↥H ≃* ↥(H.map ι) := H.equivMapOfInjective ι A.subtype_injective
  have hq : IsSubnormalQuotient ↥C Fi22G :=
    isSubnormalQuotient_of_open hsn (f.comp t.symm.toMonoidHom) (hf.comp t.symm.surjective)
  have hL : ¬ Group.IsSolvable Fi22G := by
    intro hs
    have hcomm := IsSimpleGroup.comm_iff_isSolvable.2 hs
    have hprime := @IsSimpleGroup.prime_card _ ⟨fun a b => hcomm a b⟩ hsimple
    rw [hcard] at hprime
    exact absurd hprime (by norm_num)
  obtain ⟨β, _, _, h5β, ⟨e⟩⟩ :=
    IsSubnormalQuotient.alt_of_centralizer (p := 5) (by norm_num) hσ5 hL hq
  have hn1 : Nontrivial β := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  have hc := Nat.card_congr e.toEquiv
  rw [hcard, Nat.card_eq_fintype_card (α := alternatingGroup β), card_alternatingGroup] at hc
  exact fi22_card_ne_alt _ hc.symm

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
