module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

variable {G : Type} [Group G] [Finite G]

theorem l514vexp_map_inf_centralizer_two {K : Subgroup G} {g h : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hh : h ∈ Subgroup.normalizer (K : Set G)) (hg3 : g ^ 3 = 1) (hh3 : h ^ 3 = 1)
    (hgh : g * h = h * g) :
    ((K ⊓ Subgroup.centralizer ({g} : Set G) ⊓ Subgroup.centralizer ({h} : Set G)).subgroupOf K).map
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) =
      fixSub (barAut 3 K ⟨g, hg⟩) ⊓ fixSub (barAut 3 K ⟨h, hh⟩) := by
  have hcg := map_inf_centralizer_eq_fixSub hg hg3
  have hch := map_inf_centralizer_eq_fixSub hh hh3
  have hcs : ∀ (a x : G), x ∈ Subgroup.centralizer ({a} : Set G) ↔ Commute a x := fun a x =>
    Subgroup.mem_centralizer_singleton_iff.trans ⟨Eq.symm, Eq.symm⟩
  have hcom : Commute g h := hgh
  apply le_antisymm
  · refine le_inf ?_ ?_
    · rw [← hcg]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono K inf_le_left)
    · rw [← hch]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono K
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
  · rintro y ⟨hyg, hyh⟩
    rw [← hcg] at hyg
    obtain ⟨l, hl, rfl⟩ := hyg
    have hl' : (l : G) ∈ K ⊓ Subgroup.centralizer ({g} : Set G) := Subgroup.mem_subgroupOf.1 hl
    have hlg : Commute g (l : G) := (hcs g l).1 hl'.2
    have hy' : barAut 3 K ⟨h, hh⟩ (QuotientGroup.mk l) = QuotientGroup.mk l := hyh
    rw [barAut_mk, QuotientGroup.eq] at hy'
    have hc : (l : G)⁻¹ * (h * l * h⁻¹) ∈ GLAPPrimeCoreOf 3 K := by
      have h1 := (mem_GLAPPrimeCore_iff _).1 hy'
      have h2 : (l : G)⁻¹ * (h * l * h⁻¹) =
          ((((K.normalizerMonoidHom ⟨h, hh⟩ l)⁻¹ * l : ↥K) : G))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, normalizerMonoidHom_coe]
        group
      rw [h2]
      exact (GLAPPrimeCoreOf 3 K).inv_mem h1
    set T : Subgroup G := GLAPPrimeCoreOf 3 K ⊓ Subgroup.centralizer ({g} : Set G) with hT
    have hTc : Nat.Coprime 3 (Nat.card T) :=
      (card_gLAPPrimeCoreOf_coprime 3 K).coprime_dvd_right
        (Subgroup.card_dvd_of_le (inf_le_left : T ≤ GLAPPrimeCoreOf 3 K))
    have hconj : ∀ x : G, Commute g x → Commute g (h * x * h⁻¹) := fun x hx =>
      ((hcom.mul_right hx).mul_right hcom.inv_right)
    have hhT : ∀ t ∈ T, h * t * h⁻¹ ∈ T := fun t ht =>
      ⟨(Subgroup.mem_normalizer_iff.1 (mem_normalizer_primeCore_of_mem_normalizer hh 3) t).1 ht.1,
        (hcs g _).2 (hconj t ((hcs g t).1 ht.2))⟩
    have hcT : (l : G)⁻¹ * (h * l * h⁻¹) ∈ T :=
      ⟨hc, (hcs g _).2 (hlg.inv_right.mul_right (hconj l hlg))⟩
    obtain ⟨t, ht, hfix⟩ := exists_fixed_coset hh3 hTc hhT hcT
    have htL : t ∈ K := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.GLAPPrimeCoreOf_le 3 K) ht.1
    have hlt : (l : G) * t ∈ K := K.mul_mem l.2 htL
    refine ⟨⟨(l : G) * t, hlt⟩, Subgroup.mem_subgroupOf.2 ⟨⟨hlt, ?_⟩, ?_⟩, ?_⟩
    · exact (hcs g _).2 (hlg.mul_right ((hcs g t).1 ht.2))
    · show (l : G) * t ∈ Subgroup.centralizer ({h} : Set G)
      rw [hcs]
      have : h * ((l : G) * t) = ((l : G) * t) * h := by
        have := congrArg (· * h) hfix
        simpa [mul_assoc] using this
      exact this
    · show QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) _ = QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) l
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have : (⟨(l : G) * t, hlt⟩⁻¹ * l : ↥K) = ⟨t⁻¹, K.inv_mem htL⟩ := by
        apply Subtype.ext; simp
      rw [this, mem_GLAPPrimeCore_iff]
      exact (GLAPPrimeCoreOf 3 K).inv_mem ht.1

end CFSG.HardMathSupport.Solomon.Coordinator
