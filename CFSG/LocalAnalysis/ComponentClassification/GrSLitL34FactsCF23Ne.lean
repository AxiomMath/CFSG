module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23JSide
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23DiagPi

public section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers.L34 CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.ComponentClassification.GSThmB.CF23Diag

theorem map_nfM {E E' : Type*} [Group E] [Group E']
    (f : E →* E') (l : Cover →* E) (x : MElt) : f (nfM l x) = nfM (f.comp l) x := by
  show f (l (cv (tw x.1)) * zz l x.2.1 x.2.2) =
    (f.comp l) (cv (tw x.1)) * zz (f.comp l) x.2.1 x.2.2
  rw [map_mul]
  rfl

theorem exists_isQSetting_comp
    {Y : Type*} [Group Y] [Finite Y] (hY : Group.IsPerfect (Y ⧸ pPrimeCore 2 Y))
    {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E} (hQ : IsQSetting q l)
    {π : Y ⧸ pPrimeCore 2 Y →* E} (hπs : Function.Surjective π)
    (hπk : π.ker ≤ center (Y ⧸ pPrimeCore 2 Y)) :
    ∃ lK : Cover →* Y ⧸ pPrimeCore 2 Y, IsQSetting (q.comp π) lK ∧ π.comp lK = l := by
  have hker : (q.comp π).ker = center (Y ⧸ pPrimeCore 2 Y) := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hQ.ker]
    constructor
    · intro hy
      refine UnbalancedCorr.mem_center_of_commutator_mem_center fun z => hπk ?_
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
        mul_assoc (π y)⁻¹, mem_center_iff.mp hy (π z)⁻¹]
      group
    · intro hy
      rw [mem_center_iff]
      intro e
      obtain ⟨z, rfl⟩ := hπs e
      rw [← map_mul, ← map_mul, mem_center_iff.mp hy z]
  have hqS : ∀ e, (q.comp π) e ∈ S := fun e => hQ.qS _
  have hqsurj : ∀ s ∈ S, ∃ e, (q.comp π) e = s := fun s hs => by
    obtain ⟨e, he⟩ := hQ.qsurj s hs
    obtain ⟨y, rfl⟩ := hπs e
    exact ⟨y, he⟩
  obtain ⟨lK, hlK, hlKs⟩ := exists_lam hY.commutator_eq_top (q.comp π) hqS hqsurj
    (hker ▸ le_refl _)
  refine ⟨lK, ⟨hqS, hqsurj, hker, fun e he h3 => ?_, hlK, hlKs⟩, ?_⟩
  · rw [hker] at he
    exact eq_one_of_mem_center_of_odd he
      (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3))
  · refine hom_ext_of_central commutator_cover q hQ.ker_le ?_
    rw [← MonoidHom.comp_assoc, hlK, hQ.ql]

theorem fus23ConclW_of_ne
    {H : Type} [Group H] [Finite H] (h : Hyp52 H)
    (hKa : conjugate h.K h.a ≠ h.K) (hL : Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2) :
    h.Fus23ConclW := by
  obtain ⟨q, l, x₀, d, hQ, hx₀, hsq, hdD, ⟨hdJ, hd⟩, hd2, hdx, hdP⟩ := exists_fixed_D h hL
  obtain ⟨ι, hι, hιj, hιr⟩ := exists_iota h hKa
  obtain ⟨π, hπs, hπk, hπ⟩ := exists_pi h hKa hι hιr
  obtain ⟨lK, hQK, hπl⟩ := exists_isQSetting_comp h.isQuasisimple_K.1 hQ hπs hπk
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (nfM lK x₀)
  have hm2 : nfM lK x₀ * nfM lK x₀ = 1 := by rw [nfM_mul hQK hx₀ hx₀, hsq, nfM_one]
  have hπm : π (nfM lK x₀) = nfM l x₀ := by rw [map_nfM, hπl]
  have hdJB := D_le_JB h hdD
  have hdV : d ∈ h.V := B5a.fixedLayer_le_V h hdJB
  have hψd : psi h ⟨d, hdV⟩ = delta h hKa k := by
    have e1 : psi h ⟨d, hdV⟩ = ι (jq h.J ⟨d, hdJ⟩) := (hιj d hdJB hdJ).symm
    have e2 : delta h hKa k = ι (nfM l x₀) := by rw [← deltaBar_mk, ← hπ, hk, hπm]
    rw [e1, e2, hd]
  have hk2 : psi h ⟨k, h.K_le_V k.2⟩ * psi h ⟨k, h.K_le_V k.2⟩ = 1 := by
    have h1 : k * k ∈ pPrimeCore 2 ↥h.K := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hk, hm2]
    rw [← ker_psiK h, MonoidHom.mem_ker, map_mul] at h1
    exact h1
  obtain ⟨g, hgV, hg⟩ := exists_conj_eq_mul h hKa hdV (h.comm_a (h.D_le_S hdD)) hd2 hk2 hψd
  refine ⟨g, map_subtype_le _ hgV, ?_, ?_, ?_⟩ <;> rw [hg]
  · exact mul_mem h.a_mem_S (h.D_le_S hdD)
  · intro hP
    exact hdP (by simpa using mul_mem (inv_mem h.a_mem_P) hP)
  · refine mem_inf.mpr ⟨mul_mem (subset_closure (Set.mem_union_right _ rfl))
      (subset_closure (Set.mem_union_left _ hdD)), ?_⟩
    rw [mem_centralizer_singleton_iff]
    calc h.a * d * h.x = h.a * (h.x * d) := by rw [mul_assoc, hdx]
      _ = h.x * (h.a * d) := by rw [← mul_assoc, ← h.x_comm_a, mul_assoc]

end CFSG.ComponentClassification.GSThmB.CF23L34
