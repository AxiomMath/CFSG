module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGamma
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
public import Certificates.Certificate5173
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCU42
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
public import CFSG.RankThree.PartOne.KE.TitsPlaneLocalCores

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits CFSG.RankThree.PartTwo.Sec4.Item434RemTits

section Fuse


theorem titsU_conj_y :
    wordIn 13 titsT titsUWord * wordIn 13 titsT yWord * (wordIn 13 titsT titsUWord)⁻¹ =
      titsWx * wordIn 13 titsT yWord := by
  obtain ⟨h1, h2, h3⟩ := Certificates.certificate5173
  have h := eq_of_eqA (rep_wordArr_titsT h1) (rep_wordArr_titsT h2) h3
  rw [wordIn_append, wordIn_append, wordIn_append] at h
  rw [h, mul_inv_cancel_right]
  rfl

theorem tits_fuse_perm_gamma {a : Equiv.Perm (Fin 1755)} (ha : a ∈ sylGrp) (ha1 : a ≠ 1)
    (hc : ∀ p ∈ sylGrp, p * a = a * p) :
    ∃ n ∈ titsD, ∃ E : Subgroup (Equiv.Perm (Fin 1755)), E ≤ sylGrp ∧ a ∈ E ∧
      n ∈ normalizer (E : Set (Equiv.Perm (Fin 1755))) ∧ n * a * n⁻¹ ∈ E ∧
      n * a * n⁻¹ ∉ zpowers a := by
  set y := wordIn 13 titsT yWord with hydef
  set u := wordIn 13 titsT titsUWord with hudef
  have huD : u ∈ titsD := wordIn_titsT_mem_titsD _
  have hyS : y ∈ sylGrp := titsY_mem
  have hy3 : y * y * y = 1 := cube_of_mem_sylPerms (mem_sylGrp.1 hyS)
  set E := closure ({titsWx, y} : Set (Equiv.Perm (Fin 1755))) with hE
  have hxE : titsWx ∈ E := subset_closure (by simp)
  have hyE : y ∈ E := subset_closure (by simp)
  have hES : E ≤ sylGrp := by
    rw [closure_le]
    rintro w (rfl | rfl)
    · exact titsX_mem
    · exact hyS
  have huE : u ∈ normalizer (E : Set (Equiv.Perm (Fin 1755))) :=
    mem_normalizer_closure_pair (by rw [hudef, ← titsY_eq]; exact hyE)
      (by rw [hudef, hydef, titsU_conj_y]; exact E.mul_mem hxE hyE)
  have hy2 : u * (titsWx * titsWx) * u⁻¹ = y * y := by rw [hydef, titsY_eq, ← hudef]; group
  rcases eq_of_mem_sylGrp_comm ha (hc _ titsY_mem).symm (hc _ titsZ_mem).symm with rfl | rfl | rfl
  · exact absurd rfl ha1
  · refine ⟨u, huD, E, hES, hxE, huE, ?_, ?_⟩
    · rw [hudef, ← titsY_eq]; exact hyE
    · rw [hudef, ← titsY_eq]; exact titsY_not_mem
  · refine ⟨u, huD, E, hES, E.mul_mem hxE hxE, huE, ?_, ?_⟩
    · rw [hy2]
      exact E.mul_mem hyE hyE
    · rw [hy2]
      intro hmem
      apply titsY_not_mem
      have hle : zpowers (titsWx * titsWx) ≤ zpowers titsWx :=
        (zpowers_le).2 (mul_mem (mem_zpowers _) (mem_zpowers _))
      have h2 : y * y * (y * y) ∈ zpowers titsWx := mul_mem (hle hmem) (hle hmem)
      have : y * y * (y * y) = y := by
        calc y * y * (y * y) = (y * y * y) * y := by group
          _ = y := by rw [hy3, one_mul]
      rw [this] at h2
      exact h2

end Fuse

@[expose] def KFactTenNineWCGammaTits : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal],
    Nonempty (K ≃* titsD) →
    ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
      (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
      GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
      ¬ IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y


theorem kFactTenNineWCGammaTits : KFactTenNineWCGammaTits := by
  intro B _ _ K _ ⟨e⟩ S A Y hA3 hY hwc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDc : Nat.card titsD = 17971200 := card_titsD
  have hZD : Subgroup.center titsD = ⊥ := by
    haveI : IsSimpleGroup titsD := titsD_simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center titsD) with h | h
    · exact h
    · exfalso
      have hc : IsMulCommutative titsD := Subgroup.center_eq_top_iff.mp h
      have hp := Group.is_simple_iff_prime_card.mp (inferInstance : IsSimpleGroup titsD)
      rw [hDc] at hp
      norm_num at hp
  have hZK : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1 := by
    intro k hk
    have hc : e k ∈ Subgroup.center titsD := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg e (hk (e.symm y))
      simpa using this.symm
    rw [hZD, Subgroup.mem_bot] at hc
    exact e.injective (by rw [hc, map_one])
  refine false_of_fuse_gamma hZK ?_ ?_ S A hA3 Y hY hwc
  ·
    intro _ φ hφ _
    have hK : Nat.card K = 17971200 := by rw [Nat.card_congr e.toEquiv, hDc]
    have hAK : Nat.card (MulAut K) = 35942400 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv,
        CFSG.RankThree.PartOne.KE.card_mulAut_titsD]
    exact inner_of_card_le_two_mul hZK (by rw [hK, hAK]) φ (m := 1) hφ
  · intro T a haT hoa hcent
    have hidx : ¬ 3 ∣ sylD.index := by
      have h := sylD.card_mul_index
      rw [card_sylD, factorization_card_titsD, hDc] at h
      have : sylD.index = 665600 := by omega
      rw [this]
      norm_num
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e (IsPGroup.of_card card_sylD) hidx T
    set ι : K →* Equiv.Perm (Fin 1755) := titsD.subtype.comp Φ.symm.toMonoidHom with hιdef
    have hι : Function.Injective ι := Subtype.val_injective.comp Φ.symm.injective
    have hTι : ∀ t : K, t ∈ (T : Subgroup K) ↔ ι t ∈ sylGrp := by
      intro t
      rw [hΦ, Subgroup.mem_map_equiv]
      simp [ι, sylD, Subgroup.mem_subgroupOf]
    have hιsurj : ∀ p (hp : p ∈ titsD), ι (Φ ⟨p, hp⟩) = p := by
      intro p hp
      simp [ι]
    have hxo : orderOf (ι a) = 3 := by rw [orderOf_injective ι hι a, hoa]
    have ha1 : ι a ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hxo
      omega
    have hc' : ∀ p ∈ sylGrp, p * ι a = ι a * p := by
      intro p hp
      have hpD := sylGrp_le_titsD hp
      have ht := (hTι (Φ ⟨p, hpD⟩)).2 (by rw [hιsurj p hpD]; exact hp)
      have h := congrArg ι (hcent _ ht)
      rw [map_mul, map_mul, map_inv, hιsurj p hpD] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    obtain ⟨nP, hnD, E, hES, haE, hnE, hinE, hout⟩ :=
      tits_fuse_perm_gamma ((hTι a).1 haT) ha1 hc'
    set n : K := Φ ⟨nP, hnD⟩
    have hιn : ι n = nP := hιsurj nP hnD
    have hιb : ι (n * a * n⁻¹) = nP * ι a * nP⁻¹ := by rw [map_mul, map_mul, map_inv, hιn]
    have hbT : n * a * n⁻¹ ∈ (T : Subgroup K) := by
      rw [hTι, hιb]
      exact hES hinE
    have hba : n * a * n⁻¹ ∉ zpowers a := by
      intro hmem
      apply hout
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
      refine mem_zpowers_iff.mpr ⟨j, ?_⟩
      have h' := congrArg ι hj
      rw [map_zpow, hιb] at h'
      exact h'
    have hRT : E.comap ι ≤ (T : Subgroup K) := fun r hr => (hTι r).2 (hES hr)
    refine ⟨E.comap ι, n, hRT, ?_, mem_normalizer_comap ι (by rw [hιn]; exact hnE), hbT, hba⟩
    refine not_isCyclic_of_mem (a := a) (b := n * a * n⁻¹) (show ι a ∈ E from haE)
      (show ι (n * a * n⁻¹) ∈ E by rw [hιb]; exact hinE) hoa ?_ hba
    rw [show n * a * n⁻¹ = MulAut.conj n a from rfl, MulEquiv.orderOf_eq, hoa]

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
