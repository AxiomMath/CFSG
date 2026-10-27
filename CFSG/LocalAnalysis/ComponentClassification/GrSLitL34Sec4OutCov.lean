module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4OutCovB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsReal
public import Certificates.Certificate22971

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4.OutCov

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.CosetTable

theorem outCov_parts :
    invOKE = true ∧ ∀ κ ∈ kGensB, ∀ ρ ∈ [r₂T, r₃T, r₄T], ∀ t₀ < 64, ∀ i₀ < 36,
      rT t₀ i₀ = ρ → invar κ i₀ = true →
        c3Case (indexOf (enumBFS 42 gensS 20160).tabs) (enumBFS 42 gensS 20160).tabs κ t₀ i₀ =
          true ∧ c4Case κ t₀ i₀ = true ∧ c5Case κ t₀ i₀ = true := by
  have h := Certificates.certificate22971
  simp only [outCovOK, Bool.and_eq_true, List.all_eq_true, allBelow_eq_true] at h
  obtain ⟨hI, h⟩ := h
  refine ⟨hI, fun κ hκ ρ hρ t₀ ht₀ i₀ hi₀ hrt hinv => ?_⟩
  have h1 := h κ hκ ρ hρ t₀ ht₀ i₀ hi₀
  rw [hrt, beq_self_eq_true, hinv, Bool.true_and, Bool.not_true, Bool.false_or] at h1
  simpa only [Bool.and_eq_true, and_assoc] using h1

theorem tabRep_rT {t j : ℕ} (hj : j < 36) :
    TabRep (rT t j) (wordPerm (tg t) * repPerm j) :=
  (tabRep_wordTab _).comp (tabRep_repTab hj)

theorem commB_iff {x y : Tab} {g h : Equiv.Perm (Fin 42)} (hx : TabRep x g) (hy : TabRep y h) :
    commB x y = true ↔ g * h = h * g :=
  (hx.comp hy).beq_iff (hy.comp hx)

theorem rho_spec
    {ρ : Equiv.Perm (Fin 42)} (hρ : ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) :
    ρ ∈ R ∧ (∀ t ∈ T0, ρ * t * ρ⁻¹ ∈ T0) ∧ ∃ ρT ∈ [r₂T, r₃T, r₄T], TabRep ρT ρ := by
  obtain ⟨i, hi, hiρ, ρT, hρT, hrep⟩ : ∃ i < 36, repPerm i = ρ ∧ ∃ ρT ∈ [r₂T, r₃T, r₄T],
      TabRep ρT ρ := by
    rcases hρ with rfl | rfl | rfl
    · exact ⟨1, by norm_num, by simp [repPerm, rPerm, realRepWords, genR, r₂], r₂T, by simp,
        tabRep_r₂⟩
    · exact ⟨2, by norm_num, by simp [repPerm, rPerm, realRepWords, genR, r₃], r₃T, by simp,
        tabRep_r₃⟩
    · exact ⟨3, by norm_num, by simp [repPerm, rPerm, realRepWords, genR, r₄], r₄T, by simp,
        tabRep_r₄⟩
  subst hiρ
  refine ⟨repPerm_mem i, fun t ht => ?_, ρT, hρT, hrep⟩
  obtain ⟨k, hk, rfl⟩ := exists_tg ht
  rw [conj_tg hi hk]
  exact tg_mem_T0 _ (alpha_lt hi hk)

theorem exists_betaE
    {E : Type*} [Group E]
    {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E} (h : IsQSetting q l) (hI : invOKE = true)
    {κ : ZMod 4 × ZMod 4} (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ inK κ i j)
    {y : Equiv.Perm (Fin 42)} (hyR : y ∈ R) (hyN : ∀ t ∈ T0, y * t * y⁻¹ ∈ T0) {β : E ≃* E}
    (hβ : ∀ e, q (β e) = y * q e * y⁻¹) :
    ∃ j < 36, ∃ t < 64, y = wordPerm (tg t) * repPerm j ∧ invar κ j = true ∧
      ∀ x : El, x.1 < 64 → β (nfE l x) = nfE l (betaE t j x) ∧ (betaE t j x).1 < 64 := by
  obtain ⟨j, hj, t, ht, hy, hform⟩ := exists_betaRep h hyR hyN hβ
  exact ⟨j, hj, t, ht, hy, invar_of_beta h hκ hj hform, fun x hx => beta_nfE h hI ht hj hform hx⟩

theorem nfE_zero_left {E : Type*} [Group E] (l : Cover →* E)
    (a b : ZMod 4) : nfE l ((0, a, b) : El) = zz l a b := by
  have h0 : tw 0 = [] := by decide
  show l (cv (tw 0)) * zz l a b = zz l a b
  rw [h0]
  rw [show cv ([] : List (Fin 2 × Bool)) = 1 from rfl, map_one, one_mul]

theorem wordPerm_tg_ne_one {k : ℕ} (hk : k < 64) (hk0 : k ≠ 0) :
    wordPerm (tg k) ≠ 1 := by
  intro h1
  have h0 : wordPerm (tg 0) = 1 := by
    rw [show tg 0 = [] by decide]
    rfl
  exact hk0 (tg_injective hk (by norm_num) (h1.trans h0.symm))

end CFSG.ComponentClassification.GrSLit.GrS4.OutCov

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open GrS4.OutCov

theorem l34OuterCentralizerCosetFact :
    L34OuterCentralizerCosetFact := by
  intro E _ q l hQ hkc hk4 ρ hρ β hβ r hrR hrN hrρ hrr hrF
  obtain ⟨hI, hcert⟩ := outCov_parts
  obtain ⟨κ, hκK, hκ⟩ := exists_kappa hQ hkc hk4
  obtain ⟨hρR, hρN, ρT, hρT, hρrep⟩ := rho_spec hρ
  obtain ⟨i₀, hi₀, t₀, ht₀, hρdec, hinv, hβE⟩ := exists_betaE hQ hI hκ hρR hρN hβ
  have hρ0 : TabRep (rT t₀ i₀) ρ := hρdec ▸ tabRep_rT hi₀
  have hc3 := (hcert κ (kGensB_eq ▸ hκK) ρT hρT t₀ ht₀ i₀ hi₀ (hρ0.tab_eq hρrep) hinv).1
  obtain ⟨j, hj, t, ht, hrdec⟩ := exists_decomp hrR hrN
  have hr0 : TabRep (rT t j) r := hrdec ▸ tabRep_rT hj
  simp only [c3Case, allBelow_eq_true] at hc3
  have h := hc3 t ht j hj
  have hp1 : commB (rT t j) (rT t₀ i₀) = true := (commB_iff hr0 hρ0).2 hrρ
  have hp2 : (comp 42 (rT t j) (rT t j) == idTab 42) = true :=
    ((hr0.comp hr0).beq_iff TabRep.idTab).2 hrr
  have hp3 : ((fixK κ t₀ i₀).all fun k => commB (rT t j) (wordTab (tg k))) = true := by
    rw [List.all_eq_true]
    intro k hk
    simp only [fixK, List.mem_filter, List.mem_range, List.any_eq_true] at hk
    obtain ⟨hk64, a, -, b, -, hab⟩ := hk
    have hx : ((k, a, b) : El).1 < 64 := hk64
    obtain ⟨hβx, hlt⟩ := hβE (k, a, b) hx
    have hfix : β (nfE l (k, a, b)) = nfE l (k, a, b) := hβx.trans ((eqE_iff hQ hκ hlt hx).1 hab)
    have hc := hrF (nfE l (k, a, b)) (by rw [q_nfE hQ hx]; exact tg_mem_T0 _ hk64) hfix
    rw [q_nfE hQ hx] at hc
    exact (commB_iff hr0 (tabRep_wordTab _)).2 hc
  rw [hp1, hp2, hp3] at h
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (mem_of_found_enum enumerates_S hr0 h)
  · exact Or.inr (mem_of_found_enum enumerates_S (hr0.comp hρ0) h)

theorem l34OuterCommutatorFact :
    L34OuterCommutatorFact := by
  intro E _ q l hQ hkc hk4 ρ hρ β hβ hβinv w hwT hww hβw
  obtain ⟨hI, hcert⟩ := outCov_parts
  obtain ⟨κ, hκK, hκ⟩ := exists_kappa hQ hkc hk4
  obtain ⟨hρR, hρN, ρT, hρT, hρrep⟩ := rho_spec hρ
  obtain ⟨i₀, hi₀, t₀, ht₀, hρdec, hinv, hβE⟩ := exists_betaE hQ hI hκ hρR hρN hβ
  have hρ0 : TabRep (rT t₀ i₀) ρ := hρdec ▸ tabRep_rT hi₀
  have hc5 := (hcert κ (kGensB_eq ▸ hκK) ρT hρT t₀ ht₀ i₀ hi₀ (hρ0.tab_eq hρrep) hinv).2.2
  have hzinv : ∀ a b : ZMod 4, eqE κ (betaE t₀ i₀ (0, a, b)) (0, -a, -b) = true := by
    intro a b
    have hx : ((0, a, b) : El).1 < 64 := by norm_num
    obtain ⟨hβx, hlt⟩ := hβE (0, a, b) hx
    refine (eqE_iff hQ hκ hlt (by norm_num)).2 ?_
    rw [← hβx, nfE_zero_left, nfE_zero_left, hβinv _ (zz_mem_ker hQ a b), zz_inv]
  have hinvts : inverts κ t₀ i₀ = true := by
    simp only [inverts, Bool.and_eq_true]
    exact ⟨by simpa using hzinv 1 0, by simpa using hzinv 0 1⟩
  rw [c5Case, hinvts, Bool.not_true, Bool.false_or, List.all_eq_true] at hc5
  obtain ⟨k, hk, a, b, rfl⟩ := exists_nf hQ hwT
  have hx : ((k, a, b) : El).1 < 64 := hk
  have h1 := hc5 (k, a, b) (mem_els hx)
  obtain ⟨hβx, hlt⟩ := hβE (k, a, b) hx
  have hq1 : eqE κ (mulE (k, a, b) (k, a, b)) oneE = true := by
    refine (eqE_iff hQ hκ (mulE_lt hx hx) (by decide : oneE.1 < 64)).2 ?_
    rw [nfE_mulE hQ hx hx, nfE_oneE]
    exact hww
  have hq2 : eqE κ (betaE t₀ i₀ (k, a, b)) (k, a, b) = true :=
    (eqE_iff hQ hκ hlt hx).2 (hβx.symm.trans hβw)
  rw [hq1, hq2, Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true] at h1
  obtain ⟨v, hv, hveq⟩ := h1
  have hvlt := lt_of_mem_els hv
  obtain ⟨hβv, hltv⟩ := hβE v hvlt
  refine ⟨nfE l v, by rw [q_nfE hQ hvlt]; exact tg_mem_T0 _ hvlt, ?_⟩
  have e1 := (eqE_iff hQ hκ hvlt (mulE_lt hltv hx)).1 hveq
  rw [nfE_mulE hQ hltv hx, ← hβv] at e1
  rw [inv_mul_eq_iff_eq_mul]
  exact e1

end CFSG.ComponentClassification.GrSLit
