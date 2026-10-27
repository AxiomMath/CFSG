module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenDefs
public import CFSG.ClassicalInvolution.Q3.TL4E3C269GDefs
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import Certificates.Certificate55119

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.M12Cover

namespace E3S3M12

theorem gen_checks :
    chkCover1 () = true ∧ chkGen1 () = true ∧ chkCover2 () = true ∧ chkGen2 () = true :=
  Certificates.certificate55119

theorem gens_mem_m12 : ∀ g ∈ [m12gA, m12gB], g ∈ NativeSporadic.M12 := by
  intro g hg
  rcases List.mem_pair.1 hg with rfl | rfl
  · exact m12a.2
  · exact m12b.2

theorem sup_centralizer_eq_top_of_words {r s : ↥NativeSporadic.M12}
    {gs : List (Equiv.Perm (Fin 12))}
    (hgs : ∀ g ∈ gs, g ∈ centralizerIn NativeSporadic.M12 (r : Equiv.Perm (Fin 12)))
    {x : Equiv.Perm (Fin 12)} (hx : x ∈ NativeSporadic.M12) (hxs : x * s = s * x)
    {wa wb : List ℤ} (ha : evalCodes (gs ++ [x]) wa = m12gA)
    (hb : evalCodes (gs ++ [x]) wb = m12gB) :
    Subgroup.centralizer ({r} : Set ↥NativeSporadic.M12) ⊔
      Subgroup.centralizer ({s} : Set ↥NativeSporadic.M12) = ⊤ := by
  set K := Subgroup.centralizer ({r} : Set ↥NativeSporadic.M12) ⊔
    Subgroup.centralizer ({s} : Set ↥NativeSporadic.M12) with hK
  have hL : ∀ g ∈ gs ++ [x], g ∈ K.map NativeSporadic.M12.subtype := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨hgM, hgr⟩ := mem_centralizerIn.1 (hgs g hg)
      exact ⟨⟨g, hgM⟩, Subgroup.mem_sup_left
        (Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hgr)), rfl⟩
    · rw [List.mem_singleton] at hg
      subst hg
      exact ⟨⟨g, hx⟩, Subgroup.mem_sup_right
        (Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hxs)), rfl⟩
  have hle : Subgroup.closure {m12gA, m12gB} ≤ K.map NativeSporadic.M12.subtype := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [← ha]
      exact evalCodes_mem _ hL wa
    · rw [← hb]
      exact evalCodes_mem _ hL wb
  rw [eq_top_iff]
  rintro y -
  obtain ⟨z, hz, hzy⟩ := hle (by rw [← m12_eq]; exact y.2)
  rwa [show z = y from Subtype.ext hzy] at hz

theorem sup_centralizer_eq_top_of_checks {r : Equiv.Perm (Fin 12)}
    {gs : List (Equiv.Perm (Fin 12))} {Q : RawSchreierDatum 12} {D : List GenDatum}
    (hQ : ValidSchreier Q) (hgsQ : ∀ g ∈ gs, g ∈ Q.originalSubgroup)
    (hCr : centralizerIn NativeSporadic.M12 r = Q.originalSubgroup) (hr : r ∈ NativeSporadic.M12)
    (hro : orderOf r = 2) (hcov : coverOK gs Q r D = true) (hgen : D.all (genOK gs) = true)
    {R u : ↥NativeSporadic.M12} (hR : (R : Equiv.Perm (Fin 12)) = r) (hu : u * R = R * u)
    (huo : orderOf u = 2) (hne : u ≠ R) :
    Subgroup.centralizer ({R} : Set ↥NativeSporadic.M12) ⊔
      Subgroup.centralizer ({u} : Set ↥NativeSporadic.M12) = ⊤ := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hC : ∀ g ∈ Q.originalSubgroup, g ∈ NativeSporadic.M12 ∧ g * r = r * g := fun g hg =>
    mem_centralizerIn.1 (hCr ▸ hg)
  simp only [coverOK, Bool.and_eq_true] at hcov
  obtain ⟨hok, hord⟩ := hcov
  have hreps : ∀ x ∈ coverReps gs r D, 1⁻¹ * x ∈ Q.originalSubgroup ∧ orderOf x = 2 := by
    intro x hx
    rw [inv_one, one_mul]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hCr ▸ mem_centralizerIn.2 ⟨hr, rfl⟩, hro⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
      exact ⟨evalCodes_mem _ hgsQ d.sw, (ordTest_iff perm_faithful (rep_toTable hn _)
        (by norm_num)).1 (List.all_eq_true.1 hord d hd)⟩
  obtain ⟨hcover, -⟩ := exists_conj_of_repsOK hn Q hQ (listTables_spec hn hgsQ) 1
    (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh) (by norm_num) _ hreps 1000 hok
  have huQ : 1⁻¹ * (u : Equiv.Perm (Fin 12)) ∈ Q.originalSubgroup := by
    rw [inv_one, one_mul, ← hCr]
    refine mem_centralizerIn.2 ⟨u.2, ?_⟩
    rw [← hR]
    exact congrArg Subtype.val hu
  obtain ⟨x, hx, c, hc, hux⟩ := hcover u huQ (by rw [Subgroup.orderOf_coe, huo])
  obtain ⟨hcM, hcr⟩ := hC c hc
  set C : ↥NativeSporadic.M12 := ⟨c, hcM⟩ with hCdef
  have hCR : C⁻¹ * R = R * C⁻¹ := by
    have h1 : C * R = R * C :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hR]; exact hcr)
    calc C⁻¹ * R = C⁻¹ * (R * C) * C⁻¹ := by group
      _ = C⁻¹ * (C * R) * C⁻¹ := by rw [h1]
      _ = R * C⁻¹ := by group
  rcases List.mem_cons.1 hx with rfl | hx
  · exfalso
    apply hne
    apply Subtype.ext
    rw [hux, hR, hcr, mul_inv_cancel_right]
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
  have hsM : evalCodes gs d.sw ∈ NativeSporadic.M12 := evalCodes_mem _ (fun g hg =>
    (hC g (hgsQ g hg)).1) d.sw
  set S : ↥NativeSporadic.M12 := ⟨evalCodes gs d.sw, hsM⟩ with hSdef
  have huS : C⁻¹ * u * C⁻¹⁻¹ = S := by
    apply Subtype.ext
    show c⁻¹ * (u : Equiv.Perm (Fin 12)) * c⁻¹⁻¹ = evalCodes gs d.sw
    rw [hux]
    group
  refine E3C269G.sup_centralizer_eq_top_of_conj hCR ?_
  rw [huS]
  have h := List.all_eq_true.1 hgen d hd
  simp only [genOK, Bool.and_eq_true] at h
  obtain ⟨⟨hcomm, hA⟩, hB⟩ := h
  have hgs : ∀ g ∈ gs, g ∈ centralizerIn NativeSporadic.M12 (R : Equiv.Perm (Fin 12)) :=
    fun g hg => by rw [hR, hCr]; exact hgsQ g hg
  exact sup_centralizer_eq_top_of_words hgs (evalCodes_mem _ gens_mem_m12 d.xw)
    (eq_of_commT (rep_toTable hn _) (rep_toTable hn _) hcomm)
    (rep_unique (rep_toTable hn _) (rep_of_tblEq (rep_toTable hn m12gA) hA))
    (rep_unique (rep_toTable hn _) (rep_of_tblEq (rep_toTable hn m12gB) hB))

theorem sup_centralizer_eq_top_m12
    {t u : ↥NativeSporadic.M12} (ht : orderOf t = 2)
    (hu : orderOf u = 2) (htu : t * u = u * t) (hne : u ≠ t) :
    Subgroup.centralizer ({t} : Set ↥NativeSporadic.M12) ⊔
      Subgroup.centralizer ({u} : Set ↥NativeSporadic.M12) = ⊤ := by
  obtain ⟨r, hr, c, hc, htc⟩ := m12_involution_cover.1 (t : Equiv.Perm (Fin 12))
    (by rw [inv_one, one_mul]; exact t.2) (by rw [Subgroup.orderOf_coe, ht])
  obtain ⟨hrM, hro⟩ := m12_reps_mem r hr
  set C : ↥NativeSporadic.M12 := ⟨c, hc⟩ with hCdef
  set R : ↥NativeSporadic.M12 := ⟨r, hrM⟩ with hRdef
  have hRt : MulAut.conj C⁻¹ t = R := by
    rw [MulAut.conj_apply]
    apply Subtype.ext
    show c⁻¹ * (t : Equiv.Perm (Fin 12)) * c⁻¹⁻¹ = r
    rw [htc]
    group
  refine E3C269G.sup_centralizer_eq_top_of_equiv (MulAut.conj C⁻¹) ?_
  rw [hRt]
  have hu' : MulAut.conj C⁻¹ u * R = R * MulAut.conj C⁻¹ u := by
    rw [← hRt, ← map_mul, ← map_mul, htu]
  have huo : orderOf (MulAut.conj C⁻¹ u) = 2 := by rw [MulEquiv.orderOf_eq, hu]
  have hne' : MulAut.conj C⁻¹ u ≠ R := fun h => hne ((MulAut.conj C⁻¹).injective (h.trans hRt.symm))
  obtain ⟨hC1, hG1, hC2, hG2⟩ := gen_checks
  rcases List.mem_pair.1 hr with rfl | rfl
  · exact sup_centralizer_eq_top_of_checks m12_oddcore_cent1.1 (fun g hg => by
      rw [m12CentQ1, certificate_originalSubgroup]
      exact Subgroup.subset_closure hg) centralizerIn_m12Rep1 hrM hro hC1 hG1 rfl hu' huo hne'
  · exact sup_centralizer_eq_top_of_checks m12_oddcore_cent2.1 (fun g hg => by
      rw [m12CentQ2, certificate_originalSubgroup]
      exact Subgroup.subset_closure hg) centralizerIn_m12Rep2 hrM hro hC2 hG2 rfl hu' huo hne'

end E3S3M12

theorem e3S3GenM12_proved :
    E3S3GenM12 := by
  intro X _ _ ⟨e₀⟩ t s ht hts hne ⟨g, hg⟩
  let e : X ≃* ↥NativeSporadic.M12 := e₀
  have hs : orderOf s = 2 := by rw [hg]; exact (MulEquiv.orderOf_eq (MulAut.conj g) t).trans ht
  refine E3C269G.sup_centralizer_eq_top_of_equiv e ?_
  exact E3S3M12.sup_centralizer_eq_top_m12 (by rw [MulEquiv.orderOf_eq, ht])
    (by rw [MulEquiv.orderOf_eq, hs]) (by rw [← map_mul, hts, map_mul])
    (fun h => hne (e.injective h))

end CFSG.ClassicalInvolution.Q3.TL4
