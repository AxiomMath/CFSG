module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalQ

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.PreuniquenessRankFour.Helpers

section NoE27

attribute [local irreducible] txL tU tZ tO tzc


theorem cert_a : aOK txL tU tZ = true := Certificates.certificate9557.2.2.2.2.1

theorem cert_omega : omegaOK tU tZ = true := Certificates.certificate9557.2.2.2.2.2.1

theorem cert_comp : compOK txL tU tZ = true :=
  Certificates.certificate9557.2.2.2.2.2.2.1

theorem valid_aList {t : ℕ} (ht : t < 81) : Valid (aList tU tZ)[t]! := by
  rw [getElem!_aList tU tZ ht]
  exact valid_mulCode (valid_powCode valid_tU _) (valid_powCode valid_tZ _)

variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

@[expose] noncomputable def aElt (t : ℕ) : adjointGroup .G2 K := tuE M ^ (t / 9) * tzE M ^ (t % 9)

theorem rho_aElt {t : ℕ} (ht : t < 81) : M.rho (aElt M t) = decode (aList tU tZ)[t]! := by
  obtain ⟨h1, h1'⟩ := M.rho_pow (tuE M) valid_tU (rho_tuE M) (t / 9)
  obtain ⟨h2, h2'⟩ := M.rho_pow (tzE M) valid_tZ (rho_tzE M) (t % 9)
  rw [aElt, M.rho_mul_code h1 h2 h1' h2', getElem!_aList tU tZ ht]

@[expose] noncomputable def Asub : Subgroup (adjointGroup .G2 K) where
  carrier := {g | ∃ t < 81, M.rho g = decode (aList tU tZ)[t]!}
  mul_mem' := by
    rintro a b ⟨i, hi, ha⟩ ⟨j, hj, hb⟩
    obtain ⟨k, hk, hk'⟩ := (aOK_spec cert_a).2.1 i hi j hj
    exact ⟨k, hk, by rw [M.rho_mul_code (valid_aList hi) (valid_aList hj) ha hb, hk']⟩
  one_mem' := ⟨0, by norm_num, by rw [(aOK_spec cert_a).1, map_one, decode_idCode]⟩
  inv_mem' := by
    rintro a ⟨i, hi, ha⟩
    obtain ⟨j, hj, hj'⟩ := (aOK_spec cert_a).2.2.1 i hi
    refine ⟨j, hj, ?_⟩
    have h1 : M.rho a⁻¹ * M.rho a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : decode (aList tU tZ)[i]! * decode (aList tU tZ)[j]! = 1 := by
      rw [← decode_mulCode (valid_aList hi) (valid_aList hj), hj', decode_idCode]
    calc M.rho a⁻¹ = M.rho a⁻¹ * (decode (aList tU tZ)[i]! * decode (aList tU tZ)[j]!) := by
          rw [h2, mul_one]
      _ = (M.rho a⁻¹ * M.rho a) * decode (aList tU tZ)[j]! := by rw [← ha, mul_assoc]
      _ = decode (aList tU tZ)[j]! := by rw [h1, one_mul]

theorem aElt_mem {t : ℕ} (ht : t < 81) : aElt M t ∈ Asub M := ⟨t, ht, rho_aElt M ht⟩

theorem eq_aElt_of_rho {g : adjointGroup .G2 K} {t : ℕ} (ht : t < 81)
    (hg : M.rho g = decode (aList tU tZ)[t]!) : g = aElt M t :=
  (M.eq_iff_codes (valid_aList ht) (valid_aList ht) hg (rho_aElt M ht)).2 rfl

theorem card_Asub : Nat.card (Asub M) = 81 := by
  have hbij : Function.Bijective (fun i : Fin 81 => (⟨aElt M i, aElt_mem M i.2⟩ : Asub M)) := by
    constructor
    · intro i j hij
      have h : aElt M i = aElt M j := congrArg Subtype.val hij
      have hc := (M.eq_iff_codes (valid_aList i.2) (valid_aList j.2) (rho_aElt M i.2)
        (rho_aElt M j.2)).1 h
      by_contra hne
      have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne' with h | h
      · exact (aOK_spec cert_a).2.2.2.1 j.val j.2 i.val h hc.symm
      · exact (aOK_spec cert_a).2.2.2.1 i.val i.2 j.val h hc
    · rintro ⟨g, t, ht, hg⟩
      refine ⟨⟨t, ht⟩, ?_⟩
      apply Subtype.ext
      exact (eq_aElt_of_rho M ht hg).symm
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem Asub_le_TX : Asub M ≤ TX M := by
  rintro g ⟨t, ht, hg⟩
  obtain ⟨n, hn, hn'⟩ := (aOK_spec cert_a).2.2.2.2 t ht
  rw [txL_spec.1] at hn
  exact ⟨n, hn, by rw [hg, hn']⟩

theorem relIndex_Asub : (Asub M).relIndex (TX M) = 3 := by
  have h := Subgroup.relIndex_mul_card (H := Asub M) (K := TX M)
  rw [inf_eq_left.mpr (Asub_le_TX M), card_Asub M, card_TX M] at h
  omega

theorem aElt_inj {t t' : ℕ} (ht : t < 81) (ht' : t' < 81) (h : aElt M t = aElt M t') :
    t = t' := by
  have hc := (M.eq_iff_codes (valid_aList ht) (valid_aList ht') (rho_aElt M ht)
    (rho_aElt M ht')).1 h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (aOK_spec cert_a).2.2.2.1 t' ht' t hlt hc.symm
  · exact (aOK_spec cert_a).2.2.2.1 t ht t' hlt hc

open Classical in
@[expose] noncomputable def S9 : Finset (adjointGroup .G2 K) :=
  (Finset.univ : Finset (Fin 3 × Fin 3)).image fun p => aElt M (27 * p.1 + 3 * p.2)

theorem card_S9 : (S9 M).card = 9 := by
  classical
  rw [S9, Finset.card_image_of_injective]
  · simp
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ e
    have h := aElt_inj M (by simp only; omega) (by simp only; omega) e
    simp only at h
    ext <;> simp <;> omega

theorem mem_S9_of_exps {i j : ℕ} (hi : i < 3) (hj : j < 3) : aElt M (27 * i + 3 * j) ∈ S9 M := by
  classical
  exact Finset.mem_image.mpr ⟨(⟨i, hi⟩, ⟨j, hj⟩), Finset.mem_univ _, rfl⟩

theorem zE_eq_aElt : zE M = aElt M 27 := by simp [zE, aElt]

theorem tzE_pow_three_eq_aElt : tzE M ^ 3 = aElt M 3 := by simp [aElt]

theorem zE_mem_S9 : zE M ∈ S9 M := by
  rw [zE_eq_aElt]
  exact mem_S9_of_exps M (i := 1) (j := 0) (by norm_num) (by norm_num)

theorem tzE_pow_three_mem_S9 : tzE M ^ 3 ∈ S9 M := by
  rw [tzE_pow_three_eq_aElt]
  exact mem_S9_of_exps M (i := 0) (j := 1) (by norm_num) (by norm_num)

theorem omega_S9 : ∀ x ∈ Asub M, x ^ 3 = 1 → x ∈ S9 M := by
  rintro x ⟨t, ht, hx⟩ hx3
  have h1 : M.rho (x ^ 3) = decode (powCode (aList tU tZ)[t]! 3) :=
    (M.rho_pow x (valid_aList ht) hx 3).2
  have h2 : powCode (aList tU tZ)[t]! 3 = idCode :=
    (M.eq_one_iff_code (valid_powCode (valid_aList ht) 3) h1).1 hx3
  obtain ⟨h3, h4⟩ := omegaOK_spec cert_omega t ht h2
  rw [eq_aElt_of_rho M ht hx]
  have : t = 27 * (t / 27) + 3 * (t % 9 / 3) := by omega
  rw [this]
  exact mem_S9_of_exps M (by omega) (by omega)

theorem comp_TX : ∀ c ∈ TX M, c ∉ Asub M → c ^ 3 = 1 → c * zE M = zE M * c →
    c * tzE M ^ 3 = tzE M ^ 3 * c → False := by
  intro c hc hcA hc3 h1 h2
  obtain ⟨n, hn, hcn⟩ := hc
  have hv := valid_txL hn
  have hna : ¬ ∃ t < 81, (aList tU tZ)[t]! = txL[n]! := by
    rintro ⟨t, ht, hteq⟩
    exact hcA ⟨t, ht, by rw [hcn, hteq]⟩
  have hpow : powCode txL[n]! 3 = idCode := by
    have h : M.rho (c ^ 3) = decode (powCode txL[n]! 3) := (M.rho_pow c hv hcn 3).2
    exact (M.eq_one_iff_code (valid_powCode hv 3) h).1 hc3
  obtain ⟨hz1, hz1'⟩ := M.rho_pow (tuE M) valid_tU (rho_tuE M) 3
  obtain ⟨hz2, hz2'⟩ := M.rho_pow (tzE M) valid_tZ (rho_tzE M) 3
  have c1 : mulCode txL[n]! (powCode tU 3) = mulCode (powCode tU 3) txL[n]! := by
    refine (M.eq_iff_codes (valid_mulCode hv hz1) (valid_mulCode hz1 hv)
      (M.rho_mul_code hv hz1 hcn (by rw [zE] at *; exact hz1'))
      (M.rho_mul_code hz1 hv (by rw [zE] at *; exact hz1') hcn)).1 ?_
    rw [zE] at h1
    exact h1
  have c2 : mulCode txL[n]! (powCode tZ 3) = mulCode (powCode tZ 3) txL[n]! :=
    (M.eq_iff_codes (valid_mulCode hv hz2) (valid_mulCode hz2 hv)
      (M.rho_mul_code hv hz2 hcn hz2') (M.rho_mul_code hz2 hv hz2' hcn)).1 h2
  exact compOK_spec cert_comp n hn hna hpow c1 c2

theorem no_elemAbelian_27_TX {E : Subgroup (adjointGroup .G2 K)} (hET : E ≤ TX M)
    (hE : IsElemAbelian 3 E) (h27 : Nat.card E = 27) : False :=
  no_elemAbelian_27 (relIndex_Asub M) (S9 M) (card_S9 M) (omega_S9 M) (zE M) (tzE M ^ 3)
    (zE_mem_S9 M) (tzE_pow_three_mem_S9 M) (comp_TX M) hET hE h27

include M in
theorem no_elemAbelian_27_X (hK : Nat.card K = 8) {E : Subgroup (adjointGroup .G2 K)}
    (hE : IsElemAbelian 3 E) (h27 : Nat.card E = 27) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (adjointGroup .G2 K) := Subtype.finite
  have hfac : (Nat.card (adjointGroup .G2 K)).factorization 3 = 5 :=
    factorization_eq_of_mul (card_X' hK) (by norm_num)
  obtain ⟨g, hg⟩ := exists_conj_le_of_card (Q := TX M) (E := E)
    (by rw [card_TX M, hfac]; norm_num)
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hE)
  set f : adjointGroup .G2 K →* adjointGroup .G2 K := (MulAut.conj g⁻¹).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj g⁻¹).injective
  refine no_elemAbelian_27_TX M (E := E.map f) ?_
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 f E hE) ?_
  · rintro _ ⟨e, he, rfl⟩
    have := hg e he
    simpa [hf, MulAut.conj_apply] using this
  · rw [Subgroup.card_map_of_injective hfinj, h27]

end NoE27

end CFSG.AGLEmbedding.KFactProofs.G28
