module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSCheck
public import CFSG.Sporadic.SmallOddCore.HS

public section

namespace CFSG.QuasithinUnique.Bridge.HSExcl

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem hsP_le_hsR : hsP ≤ hsR := le_sup_left

theorem hsA0P_fst : hsA0P.1 = hsA0A := by simp [hsA0P]

theorem hsA0P_snd : hsA0P.2 = invCand 3850 hsA0A := by simp [hsA0P]

theorem hsA1P_fst : hsA1P.1 = hsA1A := by simp [hsA1P]

theorem hsA1P_snd : hsA1P.2 = invCand 3850 hsA1A := by simp [hsA1P]

theorem hsGen0_eq : hsGen 0 = permOfArr 3850 hsA0A := by simp [hsGen, hsStrongPerm, hsA0A]

theorem hsGen1_eq : hsGen 1 = permOfArr 3850 hsA1A := by simp [hsGen, hsStrongPerm, hsA1A]

theorem pRep_hsA0P : PRep 3850 hsA0P (hsGen 0) := by
  have h := rep_permOfArr hs_perm_check.1
  refine ⟨?_, ?_⟩
  · rw [hsA0P_fst, hsGen0_eq]
    exact h.1
  · rw [hsA0P_snd, hsGen0_eq]
    exact h.2

theorem pRep_hsA1P : PRep 3850 hsA1P (hsGen 1) := by
  have h := rep_permOfArr hs_perm_check.2.1
  refine ⟨?_, ?_⟩
  · rw [hsA1P_fst, hsGen1_eq]
    exact h.1
  · rw [hsA1P_snd, hsGen1_eq]
    exact h.2

theorem regIn_hsP : RegIn 3850 hsP [hsA0P, hsA1P] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨hsGen 0, Subgroup.subset_closure (by simp), pRep_hsA0P⟩
  · exact ⟨hsGen 1, Subgroup.subset_closure (by simp), pRep_hsA1P⟩

theorem pRep_hsTP {k : ℕ} (hk : permOK 3850 (hsCentTbl k) = true)
    (hsq : tp 3850 (hsCentTbl k) * tp 3850 (hsCentTbl k) = 1) :
    PRep 3850 (hsTP k) (tp 3850 (hsCentTbl k)) := by
  have h := (rep_permOfArr hk).1
  exact PRep.of_sq h hsq

theorem pRep_hsSP {k : ℕ} (hk : permOK 3850 (hsCentTbl k) = true) :
    PRep 3850 (hsSP k) (tp 3850 (hsCentTbl k)) :=
  rep_permOfArr hk

theorem hsSylGens_mem : ∀ k ∈ [1, 2, 3, 4], tp 3850 (hsCentTbl k) ∈ hsS := by
  intro k hk
  refine Subgroup.subset_closure ⟨hsCentTbl k, ?_, rfl⟩
  show hsCentTbl k ∈ hsSylowGenTbls.toArray
  rw [List.mem_toArray]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact List.mem_map.2 ⟨0, List.mem_range.2 (by norm_num), rfl⟩
  · exact List.mem_map.2 ⟨1, List.mem_range.2 (by norm_num), rfl⟩
  · exact List.mem_map.2 ⟨2, List.mem_range.2 (by norm_num), rfl⟩
  · exact List.mem_map.2 ⟨3, List.mem_range.2 (by norm_num), rfl⟩

theorem regIn_hsSylGens
    : RegIn 3850 hsR hsSylGens := by
  have hsub : hsS ≤ hsR := hs_involution_centralizers.1
  intro r hr
  simp only [hsSylGens, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨tp 3850 (hsCentTbl 1), hsub (hsSylGens_mem 1 (by simp)),
      pRep_hsSP (hs_perm_check.2.2 1 (by simp))⟩
  · exact ⟨tp 3850 (hsCentTbl 2), hsub (hsSylGens_mem 2 (by simp)),
      pRep_hsSP (hs_perm_check.2.2 2 (by simp))⟩
  · exact ⟨tp 3850 (hsCentTbl 3), hsub (hsSylGens_mem 3 (by simp)),
      pRep_hsSP (hs_perm_check.2.2 3 (by simp))⟩
  · exact ⟨tp 3850 (hsCentTbl 4), hsub (hsSylGens_mem 4 (by simp)),
      pRep_hsSP (hs_perm_check.2.2 4 (by simp))⟩

theorem hs_rank_R
    : ∀ B : Subgroup ↥hsR, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 6 :=
  sylVerify_sound (N := 1024) (a := 10) (m := 86625) (by norm_num)
    (by rw [hs_normalizing_model.2.2.2.2.2.2.2.2.1]; norm_num) (by decide) regIn_hsSylGens
    hs_syl_check

@[expose] def GenP (k : ℕ) (x : Equiv.Perm (Fin 3850)) : Prop :=
  ∃ gs : List (Equiv.Perm (Fin 3850)), gs.length = k ∧ (∀ g ∈ gs, g ∈ hsP) ∧
    hsP ≤ Subgroup.closure (conjSet gs {x})

theorem GenP.mono {x : Equiv.Perm (Fin 3850)} (h : GenP 3 x) : GenP 4 x := by
  obtain ⟨gs, hlen, hgs, hle⟩ := h
  refine ⟨gs ++ [1], by simp [hlen], ?_, fun a ha => ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hgs g hg
    · rw [List.mem_singleton.1 hg]
      exact hsP.one_mem
  · refine Subgroup.closure_mono ?_ (hle ha)
    rintro _ ⟨c, hc, t, ht, rfl⟩
    exact ⟨c, List.mem_append_left _ hc, t, ht, rfl⟩

theorem gen_of_check
    {t : PArr} {τ : Equiv.Perm (Fin 3850)} (ht : PRep 3850 t τ)
    {ws : List (List ℤ)} {prog : List (ℤ × ℤ)} {k : ℕ} (hws : ws.length = k)
    (hc : threeConjCheck 3850 [hsA0P, hsA1P] t ws prog [hsA0A, hsA1A] = true) : GenP k τ := by
  obtain ⟨gs, hlen, hgs, hmem⟩ := threeConj_sound regIn_hsP ht hc
  refine ⟨gs, hlen.trans hws, hgs, ?_⟩
  have hr0 : Rep 3850 hsA0A (hsGen 0) := by
    have := pRep_hsA0P.1
    rwa [hsA0P_fst] at this
  have hr1 : Rep 3850 hsA1A (hsGen 1) := by
    have := pRep_hsA1P.1
    rwa [hsA1P_fst] at this
  have h0 := hmem hsA0A (by simp) _ hr0
  have h1 := hmem hsA1A (by simp) _ hr1
  rw [hsP]
  refine (Subgroup.closure_le _).2 ?_
  rintro y (rfl | rfl)
  · exact h0
  · exact h1

theorem GenP.transfer {k : ℕ} {t x c : Equiv.Perm (Fin 3850)} (hc : c ∈ hsP)
    (hx : x = c * t * c⁻¹) (h : GenP k t) : GenP k x := by
  obtain ⟨gs, hlen, hgs, hle⟩ := h
  refine ⟨gs.map (· * c⁻¹), by simp [hlen], ?_, fun a ha => ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact hsP.mul_mem (hgs g' hg') (hsP.inv_mem hc)
  · refine closure_conjSet_transfer (T := {x}) (T' := {t}) c⁻¹ (fun t' ht' => ⟨x, rfl, ?_⟩) gs
      (hle ha)
    have : t' = t := by simpa using ht'
    rw [this, hx]
    group

theorem rows_cases : ∀ r ∈ hsRows,
    (r.rep = hsCentTbl 5 ∧ r.outer = false) ∨ (r.rep = hsCentTbl 12 ∧ r.outer = false) ∨
    (r.rep = hsCentTbl 21 ∧ r.outer = true) ∨ (r.rep = hsCentTbl 34 ∧ r.outer = true) := by
  intro r hr
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨by simp, by simp⟩
  · exact Or.inr (Or.inl ⟨by simp, by simp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by simp, by simp⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by simp, by simp⟩))

theorem rows_sq
    : ∀ r ∈ hsRows, tp 3850 r.rep * tp 3850 r.rep = 1 := by
  intro r hr
  have h2 := (hs_involution_centralizers.2.2.2.1 r hr).2.1
  have := pow_orderOf_eq_one (tp 3850 r.rep)
  rw [h2, sq] at this
  exact this

theorem hs_gen_all
    {x : Equiv.Perm (Fin 3850)} (hxR : x ∈ hsR) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    GenP 4 x := by
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  obtain ⟨r, hr, g, hg, hxg⟩ := hs_involution_centralizers.2.2.2.2.1 x hxR hord
  have hsq := rows_sq r hr
  rcases rows_cases r hr with ⟨hrep, -⟩ | ⟨hrep, -⟩ | ⟨hrep, -⟩ | ⟨hrep, -⟩
  · rw [hrep] at hsq hxg
    exact (GenP.transfer hg hxg (gen_of_check (pRep_hsTP (hs_perm_check.2.2 5 (by simp)) hsq)
      (k := 3) (by decide) hs_conj0_check)).mono
  · rw [hrep] at hsq hxg
    exact (GenP.transfer hg hxg (gen_of_check (pRep_hsTP (hs_perm_check.2.2 12 (by simp)) hsq)
      (k := 3) (by decide) hs_conj1_check)).mono
  · rw [hrep] at hsq hxg
    exact GenP.transfer hg hxg (gen_of_check (pRep_hsTP (hs_perm_check.2.2 21 (by simp)) hsq)
      (k := 4) (by decide) hs_conj2_check)
  · rw [hrep] at hsq hxg
    exact (GenP.transfer hg hxg (gen_of_check (pRep_hsTP (hs_perm_check.2.2 34 (by simp)) hsq)
      (k := 3) (by decide) hs_conj3_check)).mono

theorem hs_gen_inner
    {x : Equiv.Perm (Fin 3850)} (hxP : x ∈ hsP) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) : GenP 3 x := by
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  obtain ⟨r, hr, g, hg, hxg⟩ := hs_involution_centralizers.2.2.2.2.1 x (hsP_le_hsR hxP) hord
  have hsq := rows_sq r hr
  have hrP : tp 3850 r.rep ∈ hsP := by
    have : tp 3850 r.rep = g⁻¹ * x * g := by rw [hxg]; group
    rw [this]
    exact hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) hxP) hg
  have hout := (hs_involution_centralizers.2.2.2.1 r hr).2.2.1
  rcases rows_cases r hr with ⟨hrep, -⟩ | ⟨hrep, -⟩ | ⟨hrep, hr2⟩ | ⟨hrep, hr2⟩
  · rw [hrep] at hsq hxg
    exact GenP.transfer hg hxg (gen_of_check (pRep_hsTP (hs_perm_check.2.2 5 (by simp)) hsq)
      (k := 3) (by decide) hs_conj0_check)
  · rw [hrep] at hsq hxg
    exact GenP.transfer hg hxg (gen_of_check (pRep_hsTP (hs_perm_check.2.2 12 (by simp)) hsq)
      (k := 3) (by decide) hs_conj1_check)
  · exact absurd hrP (hout.1 hr2)
  · exact absurd hrP (hout.1 hr2)

end CFSG.QuasithinUnique.Bridge.HSExcl
