module

public import CFSG.CGT.PushingUpLit.BHS7.SevenTwelveQExch
public import CFSG.CGT.PushingUpLit.BHS7.SevenTwelveQ

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem seven_twelve_q_sub (h : MinCex G T) : Seven12QSub G T := by
  classical
  intro hZ F E hF hFC hFT hE hFE hne x hx e he
  have hG : CharTwo G := h.charTwo
  have hT : IsSylowOf 2 T G := h.sylow
  have hT2 : IsSylowTwoOf T G := hT
  have hEb : IsBTBlock G T E := hE.1.2
  have hEC : ¬ E ≤ cStarIn G T := hE.2
  have hEG : E ≤ G := hEb.le
  have hFbG : F ∈ btBlocksG G T := mem_btBlocksG_of_isBTBlock hF
  obtain ⟨m, hm, hmE⟩ : ∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥E m := by
    rcases hEb.type with ⟨k, hk2, hk⟩ | ⟨m, hm, hmE⟩
    · exact absurd (eq_of_le_linear hG hT hEb hk2 hk hFbG hFE) hne
    · exact ⟨m, hm, hmE⟩
  obtain ⟨r, hr, hrF⟩ : ∃ r : ℕ, 1 ≤ r ∧ IsNaturalAltModule ↥F r := by
    rcases hF.type with ⟨k, hk2, hk⟩ | ⟨r, hr, hrF⟩
    · exact (false_of_linear_le_symm hG hT hEb hm hmE hFbG hFE hk2 hk).elim
    · exact ⟨r, hr, hrF⟩
  obtain ⟨X⟩ := nonempty_symModel h hEb hEC hm hmE
  obtain ⟨N⟩ := nonempty_nestedData h hEb X hF hFE hr hrF
  have hVab : IsElemAbelian 2 (vSub G T) := isElemAbelian_vSub h.charTwo hT2
  have hGV : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
  have hT₀T : qSub (vSub G T) T ≤ T := qSub_le
  have hT₀G : qSub (vSub G T) T ≤ G := hT₀T.trans hT2.1
  set Cm : Subgroup Γ := cenModSub G (vSub G T) (qSub (vSub G T) T) hGV with hCm
  have hFCm : F ≤ Cm := by
    intro f hf
    refine ⟨hF.le hf, fun y hy => ?_⟩
    have := (Subgroup.centralizer (vSub G T : Set Γ)).inv_mem (hFT y hy f hf)
    rwa [commutatorElement_inv] at this
  have hWCm : pCoreOf 2 E ≤ Cm := by
    intro w hw
    refine ⟨hEG (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E hw), fun y hy => ?_⟩
    have hwV : w ∈ vSub G T := (seven_eight h hEb hEC).2.2.1 hw
    have hyV : y * (w⁻¹) * y⁻¹ ∈ vSub G T :=
      (Subgroup.mem_normalizer_iff.mp (hGV (hT₀G hy)) _).mp ((vSub G T).inv_mem hwV)
    have hcomm : ⁅w, y⁆ ∈ vSub G T := by
      have e1 : ⁅w, y⁆ = w * (y * (w⁻¹) * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact (vSub G T).mul_mem hwV hyV
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact isElemAbelian_comm' hVab hv hcomm
  obtain ⟨a, haΩ, hac⟩ : ∃ a ∈ N.Ω₀, a ≠ X.c :=
    Finset.exists_mem_ne (by have := N.hcard; omega) X.c
  obtain ⟨t₁, ht₁, ha1⟩ : ∃ t₁ ∈ X.T', t₁ a ≠ a := by
    by_contra hall
    push Not at hall
    exact hac (X.hcuniq a hall)
  set H : Subgroup (Equiv.Perm (Fin (2 * m + 1))) :=
    ((E ⊓ Cm).subgroupOf E).map X.M.Ψ with hH
  have hgood : ∀ g : ↥E, (g : Γ) ∈ Cm → X.M.Ψ g ∈ H := fun g hg =>
    ⟨g, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.2 ⟨g.2, hg⟩), rfl⟩
  have hAlt : alternatingGroup (Fin (2 * m + 1)) ≤ H := by
    refine alternatingGroup_le_of_cyc_mem H X.hs X.hc X.hne ⟨X.c, X.hcfix⟩ ?_
    intro t ht x hx c' hc'
    obtain rfl : c' = X.c := X.hcuniq c' hc'
    by_cases hxΩ : x ∈ N.Ω₀
    ·
      have hxc : x ≠ X.c := fun e' => hx (by rw [e']; exact X.hcfix t ht)
      have htx : t x ∈ N.Ω₀ := (N.hinv t ht x).2 hxΩ
      have hyc : t x ≠ X.c := fun e' => hxc (by
        have h1 := X.hcfix t ht
        rw [← e', isSwap_apply_apply (X.hs t ht) x] at h1
        exact h1.trans e')
      have hπ : cyc x (t x) X.c ∈ altOn N.Ω₀ :=
        cyc_mem_altOn hxΩ htx N.hcmem hx.symm hxc hyc
      obtain ⟨f, hf⟩ := N.hgen _ hπ
      rw [← hf]
      exact hgood ⟨f, hFE f.2⟩ (hFCm f.2)
    · obtain ⟨g, hg, hΨg⟩ :=
        exists_mem_cenModSub_cyc h hZ hEb X hF hFC hFT hFE N haΩ ht₁ ha1 ht hx hxΩ
      rw [← hΨg]
      exact hgood g hg
  have hECm : E ≤ Cm := by
    intro e' he'
    obtain ⟨g, hg, hgΨ⟩ := hAlt (X.hpar ⟨e', he'⟩)
    have hgCm : (g : Γ) ∈ Cm := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).2
    have hker : X.M.Ψ (⟨e', he'⟩ * g⁻¹) = 1 := by
      rw [map_mul, map_inv, hgΨ, mul_inv_cancel]
    have hW : ((⟨e', he'⟩ * g⁻¹ : ↥E) : Γ) ∈ pCoreOf 2 E := by
      rw [← X.hMW]
      exact (X.M.mem_W_iff _).2 hker
    have h1 : e' = ((⟨e', he'⟩ * g⁻¹ : ↥E) : Γ) * (g : Γ) := by
      show e' = e' * (g : Γ)⁻¹ * (g : Γ)
      group
    rw [h1]
    exact Cm.mul_mem (hWCm hW) hgCm
  have hmem := (hECm he).2 x hx
  have := (Subgroup.centralizer (vSub G T : Set Γ)).inv_mem hmem
  rwa [commutatorElement_inv] at this

theorem seven_twelve_q (h : MinCex G T) (h5 : Seven5 G T) : Seven12Q G T :=
  seven_twelve_q_of_sub h h5 (seven_twelve_q_sub h)

end CFSG.CGT.PushingUpLit.BHS7
