module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiDich
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoZ

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64ii

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

variable {Z : Type} [Group Z] [Finite Z] {p : ℕ}

namespace Ctx

variable {S : Sylow p Z} {x z : Z} {M : Subgroup Z} (h : Ctx p S x z M)

include h

theorem z_mem_of_not_le (hOuter : KFact64iiOuterSylow) (hI121 : KFact64iiI121)
    {K : Subgroup Z} (hK : IsComponentOf K ⊤) (hKM : ¬ K ≤ M) : z ∈ K := by
  rcases h.z_mem_or hOuter hI121 hK with hz | ⟨y₁, hy₁B, hy₁K, hy₁c, hz⟩
  · exact hz
  · exfalso
    apply hKM
    intro k hk
    apply h.Nz
    have hzy : z ∈ zpowers y₁ := hz ▸ mem_zpowers z
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hzy
    refine P64Free.mem_normalizer_zpowers_of_commute ?_
    rw [← hm]
    exact (Commute.zpow_right (show Commute k y₁ from (hy₁c k hk).symm) m).eq

theorem exists_uncovered_component (hOuter : KFact64iiOuterSylow) (hI121 : KFact64iiI121) :
    ∃ K : Subgroup Z, IsComponentOf K ⊤ ∧ ¬ K ≤ M := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨L, hL⟩ := exists_isComponentOf_Z hp h.ne_two h.core S h.not_isCyclic_sylow h.S_le
    h.gamma h.not_top
  have huniq : ∀ K : Subgroup Z, IsComponentOf K ⊤ → K = L := by
    intro K hK
    by_contra hKL
    have h2 := two_le_pRank_of_two_components hp h.ne_two h.core S hL hK (Ne.symm hKL)
    haveI hNn : (sSup {M : Subgroup Z | IsComponentOf M ⊤}).Normal := normal_sSup_components
    have hNY : sSup {M : Subgroup Z | IsComponentOf M ⊤} ≤ M := sSup_le fun K hK => hcon K hK
    exact h.not_top (top_le_of_normal hp S hNY h2 h.gamma)
  haveI hLn : L.Normal := normal_of_unique_component hL huniq
  have hLM : L ≤ M := hcon L hL
  have hcenL : Subgroup.center ↥L = ⊥ := h.center_component_eq_bot hL
  have hOp : CFSG.pCore p Z = ⊥ := by
    by_contra hne
    haveI : (CFSG.pCore p Z).Normal := CFSG.pCore_normal
    have hUS : CFSG.pCore p Z ≤ (S : Subgroup Z) := P64Free.pCore_le_sylow S
    obtain ⟨u₀, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hu₀S : ((u₀ : ↥(CFSG.pCore p Z)) : Z) ∈ (S : Subgroup Z) := hUS u₀.2
    have hu₀1' : ((u₀ : ↥(CFSG.pCore p Z)) : Z) ≠ 1 := fun h1 => hu₀1 (Subtype.ext h1)
    obtain ⟨n, hn⟩ : ∃ n, orderOf (⟨((u₀ : ↥(CFSG.pCore p Z)) : Z), hu₀S⟩ : (S : Subgroup Z)) =
        p ^ n := IsPGroup.iff_orderOf.mp S.isPGroup' ⟨_, hu₀S⟩
    rw [Subgroup.orderOf_mk] at hn
    obtain ⟨k, hk⟩ := exists_pow_orderOf_eq_prime hp hn hu₀1'
    set u : Z := ((u₀ : ↥(CFSG.pCore p Z)) : Z) ^ k with hu
    have huU : u ∈ CFSG.pCore p Z := pow_mem u₀.2 k
    have hup : u ^ p = 1 := by
      have := pow_orderOf_eq_one u
      rwa [hk] at this
    have hu1 : u ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hk
      exact hp.one_lt.ne hk
    have hucent : u ∈ centralizer (L : Set Z) := by
      have h1 := CFSG.WholeGroup.pCore_le_centralizer_layer (G := Z) p huU
      rwa [layer_eq_of_unique_component hL huniq] at h1
    obtain ⟨y, hyQL, hyo, hyc⟩ := exists_mem_inf_sylow_component hp h.ne_two h.core S hL
    have hyp : y ^ p = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hyo] at this
    have hyu : y ∉ zpowers u := by
      intro hmem
      obtain ⟨l, hl, hne'⟩ := hyc
      apply hne'
      obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hmem
      rw [← hm]
      exact (Commute.zpow_right (show Commute l u from (mem_centralizer_iff.mp hucent) l hl) m).eq
    have hcomm : u * y = y * u := ((mem_centralizer_iff.mp hucent) y hyQL.2).symm
    obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers hp hup hyp hu1 hyu hcomm
    haveI : (L ⊔ CFSG.pCore p Z).Normal := inferInstance
    have hNY : L ⊔ CFSG.pCore p Z ≤ M := sup_le hLM (hUS.trans h.S_le)
    have hle : zpowers u ⊔ zpowers y ≤ (S : Subgroup Z) ⊓ (L ⊔ CFSG.pCore p Z) :=
      sup_le (zpowers_le.mpr ⟨hUS huU, mem_sup_right huU⟩)
        (zpowers_le.mpr ⟨hyQL.1, mem_sup_left hyQL.2⟩)
    have h2 : 2 ≤ Open.pRank p ((S : Subgroup Z) ⊓ (L ⊔ CFSG.pCore p Z)) :=
      SU1.le_pRank hp.one_lt hle hel (k := 2) hcard
    exact h.not_top (top_le_of_normal hp S hNY h2 h.gamma)
  have hCL : centralizer (L : Set Z) = ⊥ :=
    centralizer_eq_bot_of_unique_component hL huniq hcenL h.core hOp
  have hzL : z ∈ L := by
    rcases h.z_mem_or hOuter hI121 hL with hz | ⟨y₁, hy₁B, hy₁K, hy₁c, -⟩
    · exact hz
    · exfalso
      have : y₁ ∈ centralizer (L : Set Z) :=
        mem_centralizer_iff.mpr fun g hg => (hy₁c g hg).symm
      rw [hCL, Subgroup.mem_bot] at this
      exact hy₁K (this ▸ L.one_mem)
  obtain ⟨P, hP⟩ := h.exists_sylow_component hL
  have hFr := Sylow.normalizer_sup_eq_top P
  rw [hP] at hFr
  obtain ⟨a, haK, haS, hao, hBK⟩ := h.exists_inf_plane hI121 hL
  have hzBK : z ∈ (zpowers x ⊔ zpowers z) ⊓ L := ⟨mem_sup_right (mem_zpowers z), hzL⟩
  have hzeq : zpowers z = zpowers a := by
    rw [hBK] at hzBK
    exact L6LeavesNS.zpowers_eq_of_mem_of_ne_one hp hao hzBK h.z_ne_one
  have hNM : normalizer (((S : Subgroup Z) ⊓ L : Subgroup Z) : Set Z) ≤ M := by
    intro n hn
    apply h.Nz
    refine L6LeavesNS.mem_normalizer_of_map_conj_le ?_
    rw [MonoidHom.map_zpowers]
    refine zpowers_le.mpr ?_
    have hzSL : z ∈ (S : Subgroup Z) ⊓ L := ⟨h.z_mem, hzL⟩
    have hnz : n * z * n⁻¹ ∈ (S : Subgroup Z) ⊓ L := (mem_normalizer_iff.mp hn z).mp hzSL
    have hnzB : n * z * n⁻¹ ∈ zpowers x ⊔ zpowers z := by
      refine h.omega _ hnz.1 ?_
      rw [conj_pow, h.z_pow]
      simp
    have : n * z * n⁻¹ ∈ (zpowers x ⊔ zpowers z) ⊓ L := ⟨hnzB, hnz.2⟩
    rw [hBK, ← hzeq] at this
    exact this
  apply h.not_top
  rw [← hFr]
  exact sup_le hNM hLM

theorem exists_component (hOuter : KFact64iiOuterSylow) (hI121 : KFact64iiI121) :
    ∃ K : Subgroup Z, IsComponentOf K ⊤ ∧ IsSimpleGroup ↥K ∧ (∃ a b : ↥K, a * b ≠ b * a) ∧
      z ∈ K ∧ Open.pRank p K ≤ 1 ∧ ¬ K ≤ M ∧ M ≤ normalizer (K : Set Z) ∧
      ∃ b ∈ zpowers x ⊔ zpowers z, b ∉ zpowers z ∧
        ((∀ g ∈ K, b * g = g * b) ∨ OuterAction p K b) := by
  obtain ⟨K, hK, hKM⟩ := h.exists_uncovered_component hOuter hI121
  have hzK := h.z_mem_of_not_le hOuter hI121 hK hKM
  have hother : ∀ K' : Subgroup Z, IsComponentOf K' ⊤ → K' ≠ K → K' ≤ M := by
    intro K' hK' hne m hm
    exact h.Nz (P64Free.mem_normalizer_zpowers_of_commute (component_commute hK' hK hne hm hzK))
  refine ⟨K, hK, (h.isSimpleGroup_component hK).1, (h.isSimpleGroup_component hK).2, hzK,
    h.pRank_component_le_one hI121 hK, hKM, fun m hm => ?_,
    h.exists_b hI121 hK hzK⟩
  by_cases hKm : K.map (MulAut.conj m).toMonoidHom = K
  · exact (map_conj_eq_self_iff m K).1 hKm
  · exfalso
    apply hKM
    intro k hk
    have hK' : IsComponentOf (K.map (MulAut.conj m).toMonoidHom) ⊤ := isComponentOf_map_conj hK m
    have hmem : m * k * m⁻¹ ∈ K.map (MulAut.conj m).toMonoidHom := ⟨k, hk, by simp⟩
    have h1 := hother _ hK' hKm hmem
    have e : k = m⁻¹ * (m * k * m⁻¹) * m := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hm) h1) hm

theorem top_le_normalizer_component {K : Subgroup Z} (hK : IsComponentOf K ⊤)
    (hMK : M ≤ normalizer (K : Set Z)) : ⊤ ≤ normalizer (K : Set Z) := by
  rintro g -
  rw [← map_conj_eq_self_iff]
  by_contra hne
  have hp := h.prime
  have h2 := two_le_pRank_of_two_components hp h.ne_two h.core S (isComponentOf_map_conj hK g)
    hK hne
  haveI : (sSup {M : Subgroup Z | IsComponentOf M ⊤}).Normal := normal_sSup_components
  have hNK : sSup {M : Subgroup Z | IsComponentOf M ⊤} ≤ normalizer (K : Set Z) := by
    refine sSup_le fun L hL => ?_
    by_cases hLK : L = K
    · exact hLK ▸ Subgroup.le_normalizer
    · exact fun l hl => centralizer_le_normalizer _
        (mem_centralizer_iff.mpr fun k hk => component_commute hK hL (Ne.symm hLK) hk hl)
  exact hne ((map_conj_eq_self_iff g K).2
    (top_le_of_normal hp S hNK h2 (fun T hT hT2 => (h.gamma T hT hT2).trans hMK) (mem_top g)))

end Ctx

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64ii
