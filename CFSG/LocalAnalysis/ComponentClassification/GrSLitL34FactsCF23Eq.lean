module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23DiagJB
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Fus
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFrattini
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.CatFactsL4U4.OutInv

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem fus23ConclW_of_conj_eq_mul {d g : H} (hdD : d ∈ h.D) (hdx : d * h.x = h.x * d)
    (hdP : d ∉ h.P) (hgW : g ∈ h.W) (hg : g⁻¹ * h.a * g = h.a * d) : h.Fus23ConclW := by
  refine ⟨g, hgW, ?_, ?_, ?_⟩ <;> rw [hg]
  · exact mul_mem h.a_mem_S (h.D_le_S hdD)
  · intro hP
    exact hdP (by simpa using mul_mem (inv_mem h.a_mem_P) hP)
  · refine mem_inf.mpr ⟨mul_mem (subset_closure (Set.mem_union_right _ rfl))
      (subset_closure (Set.mem_union_left _ hdD)), ?_⟩
    rw [mem_centralizer_singleton_iff]
    calc h.a * d * h.x = h.a * (h.x * d) := by rw [mul_assoc, hdx]
      _ = h.x * (h.a * d) := by rw [← mul_assoc, ← h.x_comm_a, mul_assoc]

variable {h} (hKa : conjugate h.K h.a = h.K)

include hKa in
theorem D_le_K : h.D ≤ h.K := (CF23Diag.D_le_JB h).trans (fixedLayer_le_K h hKa)

include hKa in
theorem mem_P_of_comm {d : H} (hdD : d ∈ h.D)
    (hc : ∀ (j : H) (hjB : j ∈ GSLit.fixedLayer h.J h.B),
      (QuotientGroup.mk ⟨d, D_le_K hKa hdD⟩ : OddBar h.K) *
          QuotientGroup.mk ⟨j, fixedLayer_le_K h hKa hjB⟩ =
        QuotientGroup.mk ⟨j, fixedLayer_le_K h hKa hjB⟩ *
          QuotientGroup.mk ⟨d, D_le_K hKa hdD⟩) : d ∈ h.P := by
  have hdJ : d ∈ h.J := h.D_le_J hdD
  have hdB : d ∈ GSLit.fixedLayer h.J h.B := CF23Diag.D_le_JB h hdD
  have hBJ := h.B_le_coreActionKernel
  have hsup := (GSLit.fixedLayer_sup_pPrimeCore h.isQuasisimple_J hBJ h.isPGroup_B).2
  have hZ : jq h.J ⟨d, hdJ⟩ ∈ center (Jhat h.J) := by
    rw [mem_center_iff]
    intro e
    obtain ⟨E, hE⟩ := exists_oddBar_JB_equiv h
    obtain ⟨y, rfl⟩ := E.surjective e
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
    have htJ : (t : H) ∈ h.J := ((GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left) t.2
    have h1 := hc t t.2
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    have hu1 : ((⟨d, hdB⟩ * t)⁻¹ * (t * ⟨d, hdB⟩) : ↥(GSLit.fixedLayer h.J h.B)) ∈
        (jbToK h hKa).ker := by
      rw [MonoidHom.mem_ker, jbToK_apply, QuotientGroup.eq_one_iff]
      exact h1
    have hu2 := mem_map_of_mem (GSLit.fixedLayer h.J h.B).subtype (ker_jbToK_le h hKa hu1)
    rw [hsup] at hu2
    have hu3 := inv_mem (mem_inf.mp hu2).2
    rw [hE t htJ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq, ← mem_map_iff_mem h.J.subtype_injective]
    convert hu3 using 1
    simp only [map_mul, map_inv, Subgroup.coe_subtype]
    group
  have hmem := (mem_zStarIn_iff hdJ).2 hZ
  rw [zStarIn, map_fusionZStar_eq] at hmem
  exact mem_inf.mpr ⟨h.D_le_S hdD, (mem_inf.mp hmem).2⟩

include hKa in
theorem fus23ConclW_of_NL (hZK : center (OddBar h.K) = ⊥) {d : H} (hdD : d ∈ h.D)
    (hd2 : d * d = 1) (hdx : d * h.x = h.x * d) (hdP : d ∉ h.P) {γ : ↥(GAut hKa)}
    (hγN : γ ∈ NL hKa)
    (hγ : γ⁻¹ * phi hKa (abar h) * γ =
      phi hKa (abar h) * phi hKa (wbarMk h.B ⟨d, K_le_W h (D_le_K hKa hdD)⟩)) :
    h.Fus23ConclW := by
  obtain ⟨g, hgK, y, hy, hg⟩ := Fus23.exists_conj_of_inner hKa (D_le_K hKa hdD)
    (h.comm_a (h.D_le_S hdD)) hd2 hγN hγ
  rw [Fus23.eq_one_of_mem_B_zStar h hZK hy, mul_one] at hg
  exact fus23ConclW_of_conj_eq_mul h hdD hdx hdP (h.isPComponent_K.1 hgK) hg

include hKa in
theorem zeta_facts (hZK : center (OddBar h.K) = ⊥) {d : H} (hdD : d ∈ h.D) (hd2 : d * d = 1)
    (hdP : d ∉ h.P) :
    phi hKa (wbarMk h.B ⟨d, K_le_W h (D_le_K hKa hdD)⟩) ∈ Jhat hKa ∧
      phi hKa (wbarMk h.B ⟨d, K_le_W h (D_le_K hKa hdD)⟩) *
        phi hKa (wbarMk h.B ⟨d, K_le_W h (D_le_K hKa hdD)⟩) = 1 ∧
      phi hKa (abar h) * phi hKa (wbarMk h.B ⟨d, K_le_W h (D_le_K hKa hdD)⟩) =
        phi hKa (wbarMk h.B ⟨d, K_le_W h (D_le_K hKa hdD)⟩) * phi hKa (abar h) ∧
      phi hKa (wbarMk h.B ⟨d, K_le_W h (D_le_K hKa hdD)⟩) ≠ phi hKa (abar h) := by
  have hdK := D_le_K hKa hdD
  have hdB : d ∈ GSLit.fixedLayer h.J h.B := CF23Diag.D_le_JB h hdD
  set dW : ↥h.W := ⟨d, K_le_W h hdK⟩ with hdW
  set aW : ↥h.W := ⟨h.a, h.a_mem_normalizer⟩ with haW
  refine ⟨⟨wbarMk h.B dW, ⟨dW, mem_subgroupOf.mpr hdB, rfl⟩, rfl⟩, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul]
    have e : dW * dW = 1 := Subtype.ext hd2
    rw [e, map_one, map_one]
  · rw [← map_mul, ← map_mul]
    have e : aW * dW = dW * aW := Subtype.ext (h.comm_a (h.D_le_S hdD)).symm
    rw [abar, ← haW, e, map_mul, map_mul]
  · intro h1
    refine hdP (mem_P_of_comm hKa hdD fun j hjB => ?_)
    have h2 : rhoL hKa dW = rhoL hKa aW := by
      have := congrArg (fun g : ↥(GAut hKa) => (g : MulAut (LK h))) h1
      simp only [MonoidHom.coe_rangeRestrict] at this
      rw [← rhoBar_mk, ← rhoBar_mk]
      exact this
    set jK : ↥h.K := ⟨j, fixedLayer_le_K h hKa hjB⟩ with hjK
    have h3 := congrArg (fun φ : MulAut (LK h) => φ ((jK : OddBar h.K) : LK h)) h2
    rw [show dW = ⟨((⟨d, hdK⟩ : ↥h.K) : H), K_le_W h hdK⟩ from rfl, rhoL_of_mem_K,
      MulAut.conj_apply] at h3
    have h5 : oddBarConj h.K ⟨h.a, a_mem_normalizer_K h hKa⟩ (jK : OddBar h.K) = jK :=
      oddBarConj_a_apply_of_mem_imJB h hKa ⟨jK, mem_subgroupOf.mpr hjB, rfl⟩
    rw [rhoL, MonoidHom.comp_apply,
      show actW h hKa aW = oddBarConj h.K ⟨h.a, a_mem_normalizer_K h hKa⟩ from rfl,
      GH74.KGroups.inducedHom_mk, h5] at h3
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      QuotientGroup.eq, hZK, mem_bot] at h3
    have h4 : ((⟨d, hdK⟩ : ↥h.K) : OddBar h.K) * (jK : OddBar h.K) *
        ((⟨d, hdK⟩ : ↥h.K) : OddBar h.K)⁻¹ = (jK : OddBar h.K) := by
      rw [← inv_mul_eq_one, h3]
    calc ((⟨d, hdK⟩ : ↥h.K) : OddBar h.K) * (jK : OddBar h.K) =
        ((⟨d, hdK⟩ : ↥h.K) : OddBar h.K) * (jK : OddBar h.K) *
          ((⟨d, hdK⟩ : ↥h.K) : OddBar h.K)⁻¹ * ((⟨d, hdK⟩ : ↥h.K) : OddBar h.K) := by group
      _ = _ := by rw [h4]

theorem orderOf_mul_eq_two {G : Type*} [Group G] {α ζ : G} (hα : α * α = 1) (hζ2 : ζ * ζ = 1)
    (hc : α * ζ = ζ * α) (hne : ζ ≠ α) : orderOf (α * ζ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [sq]
    calc α * ζ * (α * ζ) = α * (ζ * α) * ζ := by group
      _ = α * (α * ζ) * ζ := by rw [← hc]
      _ = (α * α) * (ζ * ζ) := by group
      _ = 1 := by rw [hα, hζ2, one_mul]
  · intro h1
    apply hne
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hα]

end CFSG.ComponentClassification.GSThmB.CF23L34
