module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR31
public import CFSG.LocalAnalysis.AGLEmbedding.AltBetaRank
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Transport
public import CFSG.GroupTheory.ConjTransport
public import CFSG.GroupTheory.Commutator.JoinNormalizer
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.GH74.GLS.Balance.CompSwap
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.InvolutionPow
public import TauCeti.Algebra.Group.Subgroup.ModularLaw

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barAct_comp_inclusion_injective {H K : Subgroup G} (hH : IsPGroup 2 ↥H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hcen : CenterlessBar K)
    (hZ : (Subgroup.center ↥H).map H.subtype ≤ K) :
    Function.Injective ((barAct K).comp (Subgroup.inclusion hHK)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥H := hH.isNilpotent
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  let ψ : ↥H →* MulAut (kBar K) := (barAct K).comp (Subgroup.inclusion hHK)
  have hker : ψ.ker ≠ ⊥ := by
    intro hbot
    have hmem : x ∈ ψ.ker := MonoidHom.mem_ker.mpr hx
    rw [hbot] at hmem
    exact hx1 (Subgroup.mem_bot.mp hmem)
  have hnb := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥H) (H := ψ.ker) hker
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ ψ.ker ⊓ Subgroup.center ↥H, z ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hnb ((Subgroup.eq_bot_iff_forall _).mpr hc)
  obtain ⟨hzk, hzc⟩ := Subgroup.mem_inf.mp hz
  have hzbar : barAct K ⟨(z : ↥H), hHK z.2⟩ = 1 := by
    have h := MonoidHom.mem_ker.mp hzk
    have h' : barAct K (Subgroup.inclusion hHK z) = 1 := h
    rwa [show Subgroup.inclusion hHK z = ⟨(z : ↥H), hHK z.2⟩ from Subtype.ext rfl] at h'
  have hcs : ((z : ↥H) : G) ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
    have h' := (barAct_eq_one_iff (J := K) ⟨(z : ↥H), hHK z.2⟩).1 hzbar
    simpa using h'
  have hzK : ((z : ↥H) : G) ∈ K := hZ (Subgroup.mem_map.mpr ⟨z, hzc, rfl⟩)
  have hzO : ((z : ↥H) : G) ∈ pPrimeCoreOf 2 K :=
    mem_pPrimeCoreOf_of_commutators hcen hzK (fun k hk => hcs.2.2 k hk)
  have hbot := C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot K hH
  have hmem : ((z : ↥H) : G) ∈ H ⊓ pPrimeCoreOf 2 K := ⟨z.2, hzO⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 (Subtype.ext hmem)

theorem inf_centralizerSection_eq_bot {H K : Subgroup G} (hH : IsPGroup 2 ↥H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hcen : CenterlessBar K)
    (hZ : (Subgroup.center ↥H).map H.subtype ≤ K) :
    H ⊓ centralizerSection K (pPrimeCoreOf 2 K) = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨hzH, hzcs⟩ := Subgroup.mem_inf.mp hz
  have hzker : (⟨z, hzH⟩ : ↥H) ∈ ((barAct K).comp (Subgroup.inclusion hHK)).ker := by
    rw [MonoidHom.mem_ker]
    change barAct K (Subgroup.inclusion hHK ⟨z, hzH⟩) = 1
    have h := (barAct_eq_one_iff (J := K) ⟨z, hHK hzH⟩).2 hzcs
    rwa [show Subgroup.inclusion hHK ⟨z, hzH⟩ = ⟨z, hHK hzH⟩ from Subtype.ext rfl]
  have hinj := barAct_comp_inclusion_injective hH hHK hcen hZ
  have h1 : (⟨z, hzH⟩ : ↥H) = 1 := hinj (by rw [hzker, map_one])
  exact congrArg Subtype.val h1

theorem pRank_le_pRank_mulAut_kBar {H K : Subgroup G} (hH : IsPGroup 2 ↥H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hcen : CenterlessBar K)
    (hZ : (Subgroup.center ↥H).map H.subtype ≤ K) :
    pRank 2 ↥H ≤ pRank 2 (MulAut (kBar K)) := by
  exact CFSG.RankThree.PartOne.Quotient36.pRank_le_of_injective' one_lt_two _
    (barAct_comp_inclusion_injective hH hHK hcen hZ)

theorem false_of_pRank_four_of_pRank_mulAut_le_three {H K F : Subgroup G}
    (hH : IsPGroup 2 ↥H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hcen : CenterlessBar K) (hZ : (Subgroup.center ↥H).map H.subtype ≤ K)
    (hFH : F ≤ H) (hF4 : 4 ≤ pRank 2 ↥F)
    (hAut : pRank 2 (MulAut (kBar K)) ≤ 3) : False := by
  have h1 : pRank 2 ↥F ≤ pRank 2 ↥H :=
    CFSG.RankThree.PartOne.Quotient36.pRank_mono_subgroup one_lt_two hFH
  have h2 := pRank_le_pRank_mulAut_kBar hH hHK hcen hZ
  omega

theorem pRank_mulAut_kBar_le_three_of_A7 {K : Subgroup G}
    (hA7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    pRank 2 (MulAut (kBar K)) ≤ 3 := by
  obtain ⟨e⟩ := hA7
  have h1 : pRank 2 (MulAut (kBar K)) = pRank 2 (Perm (Fin 7)) :=
    CFSG.RankThree.PartOne.Quotient36.pRank_congr_mulEquiv one_lt_two (autA7Equiv e)
  rw [h1, CFSG.SectionRank.pRank_eq_open_pRank_top 2 (Perm (Fin 7))]
  have h2 := CFSG.AGLEmbedding.pRank_top_perm_le (α := Fin 7) (p := 2) Nat.prime_two
  simpa using h2

theorem false_of_pRank_four_of_A7 {H K F : Subgroup G} (hH : IsPGroup 2 ↥H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hZ : (Subgroup.center ↥H).map H.subtype ≤ K)
    (hA7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hFH : F ≤ H) (hF4 : 4 ≤ pRank 2 ↥F) : False :=
  false_of_pRank_four_of_pRank_mulAut_le_three hH hHK (centerlessBar_of_A7 hA7) hZ hFH hF4
    (pRank_mulAut_kBar_le_three_of_A7 hA7)


variable {X : Type} [Group X]

theorem inf_components_eq_bot_of_ne [Finite X] {J K : Subgroup X}
    (hJ : IsComponent J) (hK : IsComponent K) (hne : J ≠ K)
    (hZJ : Subgroup.center J = ⊥) : J ⊓ K = ⊥ := by
  have hcomm : ⁅J, K⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hJ hK).resolve_left hne
  have hKcent : K ≤ Subgroup.centralizer (J : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rwa [Subgroup.commutator_comm] at hcomm)
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxJ, hxK⟩ := Subgroup.mem_inf.mp hx
  have hxcent : x ∈ Subgroup.centralizer (J : Set X) := hKcent hxK
  have hxZ : (⟨x, hxJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : X) * x = x * (y : X)
    exact Subgroup.mem_centralizer_iff.mp hxcent (y : X) y.2
  rw [hZJ, Subgroup.mem_bot] at hxZ
  exact Subtype.ext_iff.mp hxZ

section Support

theorem centralizer_commutator_iff_of_components [Finite X] {J K : Subgroup X} {b bK c : X}
    (hJ : IsComponent J) (hK : IsComponent K) (hJK : J ≠ K)
    (hZJ : Subgroup.center J = ⊥) (hZK : Subgroup.center K = ⊥)
    (hbJ : b ∈ J) (hb1 : b ≠ 1) (hbKK : bK ∈ K) (hbK1 : bK ≠ 1)
    (hc : c = bK * b⁻¹) :
    ∀ L : Subgroup X, IsComponent L →
      (L ≤ Subgroup.centralizer ({c} : Set X) ↔ L ≠ J ∧ L ≠ K) := by
  have hJKbot : ⁅J, K⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hJ hK).resolve_left hJK
  have hKcentJ : K ≤ Subgroup.centralizer (J : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rwa [Subgroup.commutator_comm] at hJKbot)
  have hJcentK : J ≤ Subgroup.centralizer (K : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJKbot
  intro L hL
  constructor
  · intro hLc
    constructor
    · intro hLJ
      have hLcJ : J ≤ Subgroup.centralizer ({c} : Set X) := hLJ ▸ hLc
      exfalso
      have hbcent : (⟨b, hbJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
        rw [Subgroup.mem_center_iff]
        intro j
        apply Subtype.ext
        change (j : X) * b = b * (j : X)
        have hjc : (j : X) * c = c * (j : X) :=
          Subgroup.mem_centralizer_singleton_iff.mp (hLcJ j.2)
        have hconj : c * (j : X) * c⁻¹ = (j : X) := by rw [← hjc]; group
        have hcalc : c * (j : X) * c⁻¹ = bK * (b⁻¹ * (j : X) * b) * bK⁻¹ := by
          rw [hc]
          have e : (bK * b⁻¹) * (j : X) * (bK * b⁻¹)⁻¹ =
              bK * (b⁻¹ * (j : X) * b) * bK⁻¹ := by group
          rw [e]
        have hmemJ : b⁻¹ * (j : X) * b ∈ J :=
          J.mul_mem (J.mul_mem (J.inv_mem hbJ) j.2) hbJ
        have hbKcomm : bK * (b⁻¹ * (j : X) * b) * bK⁻¹ = b⁻¹ * (j : X) * b := by
          have h := Subgroup.mem_centralizer_iff.mp (hKcentJ hbKK) (b⁻¹ * (j : X) * b) hmemJ
          calc bK * (b⁻¹ * (j : X) * b) * bK⁻¹ =
              ((b⁻¹ * (j : X) * b) * bK) * bK⁻¹ := by rw [h]
            _ = b⁻¹ * (j : X) * b := by group
        have hbconj : b⁻¹ * (j : X) * b = (j : X) := by
          rw [hcalc, hbKcomm] at hconj
          exact hconj
        calc (j : X) * b = b * (b⁻¹ * (j : X) * b) := by group
          _ = b * (j : X) := by rw [hbconj]
      rw [hZJ, Subgroup.mem_bot] at hbcent
      exact hb1 (Subtype.ext_iff.mp hbcent)
    · intro hLK
      have hLcK : K ≤ Subgroup.centralizer ({c} : Set X) := hLK ▸ hLc
      exfalso
      have hbKcent : (⟨bK, hbKK⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        change (k : X) * bK = bK * (k : X)
        have hkc : (k : X) * c = c * (k : X) :=
          Subgroup.mem_centralizer_singleton_iff.mp (hLcK k.2)
        have hconj : c * (k : X) * c⁻¹ = (k : X) := by rw [← hkc]; group
        have hbk : b⁻¹ * (k : X) * b = (k : X) := by
          have h := Subgroup.mem_centralizer_iff.mp (hJcentK hbJ) (k : X) k.2
          calc b⁻¹ * (k : X) * b = b⁻¹ * ((k : X) * b) := by group
            _ = b⁻¹ * (b * (k : X)) := by rw [h]
            _ = (k : X) := by group
        have hcalc : c * (k : X) * c⁻¹ = bK * (k : X) * bK⁻¹ := by
          rw [hc]
          have e : (bK * b⁻¹) * (k : X) * (bK * b⁻¹)⁻¹ =
              bK * (b⁻¹ * (k : X) * b) * bK⁻¹ := by group
          rw [e, hbk]
        have hbKconj : bK * (k : X) * bK⁻¹ = (k : X) := hcalc.symm.trans hconj
        have hbKconj' : bK⁻¹ * (k : X) * bK = (k : X) := by
          calc bK⁻¹ * (k : X) * bK = bK⁻¹ * (bK * (k : X) * bK⁻¹) * bK := by rw [hbKconj]
            _ = (k : X) := by group
        calc (k : X) * bK = bK * (bK⁻¹ * (k : X) * bK) := by group
          _ = bK * (k : X) := by rw [hbKconj']
      rw [hZK, Subgroup.mem_bot] at hbKcent
      exact hbK1 (Subtype.ext_iff.mp hbKcent)
  · rintro ⟨hLJ, hLK⟩
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hbcentL : b ∈ Subgroup.centralizer (L : Set X) := by
      have hcomm : ⁅J, L⁆ = ⊥ := by
        rcases CFSG.LocalCores.distinct_components_commute hJ hL with h | h
        · exact absurd h (Ne.symm hLJ)
        · exact h
      have hLc : L ≤ Subgroup.centralizer (J : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rwa [Subgroup.commutator_comm] at hcomm)
      exact fun y hy => (Subgroup.mem_centralizer_iff.mp (hLc hy) b hbJ).symm
    have hbKcentL : bK ∈ Subgroup.centralizer (L : Set X) := by
      have hcomm : ⁅K, L⁆ = ⊥ := by
        rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
        · exact absurd h (Ne.symm hLK)
        · exact h
      have hLc : L ≤ Subgroup.centralizer (K : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rwa [Subgroup.commutator_comm] at hcomm)
      exact fun y hy => (Subgroup.mem_centralizer_iff.mp (hLc hy) bK hbKK).symm
    have hxb : x * b = b * x := Subgroup.mem_centralizer_iff.mp hbcentL x hx
    have hxbK : x * bK = bK * x := Subgroup.mem_centralizer_iff.mp hbKcentL x hx
    calc x * c = x * (bK * b⁻¹) := by rw [hc]
      _ = (x * bK) * b⁻¹ := by group
      _ = (bK * x) * b⁻¹ := by rw [hxbK]
      _ = bK * (x * b⁻¹) := by group
      _ = bK * (b⁻¹ * x) := by rw [(show Commute x b from hxb).inv_right.eq]
      _ = (bK * b⁻¹) * x := by group
      _ = c * x := by rw [hc]

end Support


section ComponentCase

variable [Finite X]

theorem le_normalizer_of_isComponent_of_four_le_card_commutator
    {J F : Subgroup X} {b : X} (hJ : IsComponent J) (hZJ : Subgroup.center J = ⊥)
    (hbJ : b ∈ J) (hb2 : orderOf b = 2) (hFel : IsElementaryAbelian 2 ↥F)
    (hbF : b ∈ Subgroup.normalizer (F : Set X))
    (hcomm : 4 ≤ Nat.card ↥⁅F, Subgroup.zpowers b⁆) :
    F ≤ Subgroup.normalizer (J : Set X) := by
  classical
  have hFcomm : ∀ g ∈ F, ∀ h ∈ F, g * h = h * g :=
    (CFSG.GH74.GLS.C3.Layer1.Back.forall_of_isElementaryAbelian hFel).1
  have hFsq : ∀ g ∈ F, g * g = 1 := by
    intro g hg
    have := (CFSG.GH74.GLS.C3.Layer1.Back.forall_of_isElementaryAbelian hFel).2 g hg
    simpa [sq] using this
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb2
    omega
  by_contra hnot
  obtain ⟨f, hfF, hfN⟩ := Set.not_subset.mp hnot
  set K : Subgroup X := J.map (MulAut.conj f).toMonoidHom with hKdef
  have hK : IsComponent K :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj f) hJ
  have hKne : K ≠ J := by
    intro h
    apply hfN
    refine (Subgroup.mem_normalizer_iff_map_conj_eq (H := J) (g := f)).mpr ?_
    change J.map (MulAut.conj f).toMonoidHom = J
    rw [← hKdef]
    exact h
  have hZK : Subgroup.center K = ⊥ := by
    have e : ↥J ≃* ↥K := J.equivMapOfInjective (MulAut.conj f).toMonoidHom
      (MulAut.conj f).injective
    have h := Subgroup.map_center_eq e
    rw [hZJ, Subgroup.map_bot] at h
    exact h.symm
  set bK : X := MulAut.conj f b with hbKdef
  have hbKK : bK ∈ K := Subgroup.mem_map_of_mem (MulAut.conj f).toMonoidHom hbJ
  have hbK2 : orderOf bK = 2 := by
    have h := orderOf_injective (MulAut.conj f).toMonoidHom (MulAut.conj f).injective b
    rw [hbKdef]
    change orderOf ((MulAut.conj f).toMonoidHom b) = 2
    rw [h, hb2]
  have hbK1 : bK ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hbK2
    omega
  have hf2 : f * f = 1 := hFsq f hfF
  set c : X := bK * b⁻¹ with hcdef
  have hcF : c ∈ F := by
    have hbf : b * f * b⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hbF f).mp hfF
    rw [hcdef, hbKdef]
    have e : MulAut.conj f b * b⁻¹ = f * (b * f * b⁻¹) := by
      simp only [MulAut.conj_apply]
      have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
      rw [hfinv]
      group
    rw [e]
    exact F.mul_mem hfF hbf
  have hsupp := centralizer_commutator_iff_of_components hJ hK hKne.symm hZJ hZK hbJ hb1 hbKK hbK1
    hcdef.symm
  have hJnot : ¬ J ≤ Subgroup.centralizer ({c} : Set X) := by
    intro h
    exact ((hsupp J hJ).mp h).1 rfl
  have hinv : ∀ g ∈ F, ∀ L : Subgroup X, IsComponent L →
      (L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({c} : Set X) ↔
        L ≤ Subgroup.centralizer ({c} : Set X)) := by
    intro g hg L hL
    have hgc : g * c = c * g := hFcomm g hg c hcF
    have hgc' : g * c * g⁻¹ = c := by rw [hgc]; group
    have hgc'' : g⁻¹ * c * g = c := by
      calc g⁻¹ * c * g = g⁻¹ * (c * g) := by group
        _ = g⁻¹ * (g * c) := by rw [← hgc]
        _ = c := by group
    have hconj_iff : ∀ x : X,
        (g * x * g⁻¹) * c = c * (g * x * g⁻¹) ↔ x * c = c * x := by
      intro x
      constructor
      · intro h
        have h' := congrArg (fun y => g⁻¹ * y * g) h
        calc x * c = x * (g⁻¹ * c * g) := by rw [hgc'']
          _ = g⁻¹ * ((g * x * g⁻¹) * c) * g := by group
          _ = g⁻¹ * (c * (g * x * g⁻¹)) * g := h'
          _ = (g⁻¹ * c * g) * x := by group
          _ = c * x := by rw [hgc'']
      · intro h
        have h' := congrArg (fun y => g * y * g⁻¹) h
        calc (g * x * g⁻¹) * c = (g * x * g⁻¹) * (g * c * g⁻¹) := by rw [hgc']
          _ = g * (x * c) * g⁻¹ := by group
          _ = g * (c * x) * g⁻¹ := h'
          _ = (g * c * g⁻¹) * (g * x * g⁻¹) := by group
          _ = c * (g * x * g⁻¹) := by rw [hgc']
    constructor
    · intro hLc y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hy' : g * y * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hy
      have h1 : (g * y * g⁻¹) * c = c * (g * y * g⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hLc hy')
      exact (hconj_iff y).mp h1
    · intro hLc y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx1 : x * c = c * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hLc hx)
      exact (hconj_iff x).mpr hx1
  have hdich : ∀ g ∈ F, J.map (MulAut.conj g).toMonoidHom = J ∨
      J.map (MulAut.conj g).toMonoidHom = K := by
    intro g hg
    set L : Subgroup X := J.map (MulAut.conj g).toMonoidHom with hLdef
    have hL : IsComponent L :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hJ
    have hnotL : ¬ L ≤ Subgroup.centralizer ({c} : Set X) := by
      rw [hinv g hg J hJ]
      exact hJnot
    have hLsupp := (hsupp L hL).not.mp hnotL
    by_cases hLJ : L = J
    · exact Or.inl hLJ
    · exact Or.inr (by
        by_contra hLK
        exact hLsupp ⟨hLJ, hLK⟩)
  set N : Subgroup ↥F := (Subgroup.normalizer (J : Set X)).subgroupOf F with hNdef
  have hNmem : ∀ g : ↥F, g ∈ N ↔ (g : X) ∈ Subgroup.normalizer (J : Set X) := by
    intro g
    rw [hNdef, Subgroup.mem_subgroupOf]
  have hfN' : (⟨f, hfF⟩ : ↥F) ∉ N := by
    rw [hNmem]
    exact hfN
  have hidx : N.index = 2 := by
    refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr ⟨⟨f, hfF⟩, hfN', ?_⟩
    intro g
    by_cases hgN : g ∈ N
    · exact Or.inr hgN
    · left
      have hgN' : (g : X) ∉ Subgroup.normalizer (J : Set X) := by
        intro h
        exact hgN ((hNmem g).mpr h)
      have hgK : J.map (MulAut.conj (g : X)).toMonoidHom = K := by
        rcases hdich (g : X) g.2 with h | h
        · exact absurd h (by
            intro hh
            exact hgN' ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr hh))
        · exact h
      rw [hNmem]
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hcomp : J.map (MulAut.conj ((g : X) * f)).toMonoidHom =
          (J.map (MulAut.conj (g : X)).toMonoidHom).map (MulAut.conj f).toMonoidHom := by
        rw [hFcomm (g : X) g.2 f hfF]
        exact (CFSG.GroupTheory.map_conj_map_conj f (g : X) J).symm
      change J.map (MulAut.conj ((g : X) * f)).toMonoidHom = J
      rw [hcomp, hgK, hKdef]
      calc (J.map (MulAut.conj f).toMonoidHom).map (MulAut.conj f).toMonoidHom
          = J.map (MulAut.conj (f * f)).toMonoidHom :=
            CFSG.GroupTheory.map_conj_map_conj f f J
        _ = J := by
          rw [hf2]
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            simpa [MulAut.conj_apply] using hy
          · intro hx
            exact ⟨x, hx, by simp⟩
  have hJKbot : J ⊓ K = ⊥ := inf_components_eq_bot_of_ne hJ hK hKne.symm hZJ
  have hN_eq_cent : N = (Subgroup.centralizer ({b} : Set X)).subgroupOf F := by
    ext g
    rw [hNmem, Subgroup.mem_subgroupOf]
    constructor
    ·
      intro hgN
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcommJ : ⁅b, (g : X)⁆ ∈ J := CFSG.GH74.GLS.Balance.Comp.commutator_mem hgN hbJ
      have hcommF : ⁅b, (g : X)⁆ ∈ F := by
        have hbg : b * (g : X) * b⁻¹ ∈ F :=
          (Subgroup.mem_normalizer_iff.mp hbF (g : X)).mp g.2
        rw [commutatorElement_def]
        exact F.mul_mem hbg (F.inv_mem g.2)
      have hf_cent : f * ⁅b, (g : X)⁆ * f⁻¹ = ⁅b, (g : X)⁆ := by
        have h := hFcomm f hfF ⁅b, (g : X)⁆ hcommF
        rw [h]
        group
      have hmemK : ⁅b, (g : X)⁆ ∈ K := by
        rw [hKdef]
        exact Subgroup.mem_map.mpr ⟨⁅b, (g : X)⁆, hcommJ, hf_cent⟩
      have hmemBot : ⁅b, (g : X)⁆ ∈ (⊥ : Subgroup X) := by
        rw [← hJKbot]
        exact ⟨hcommJ, hmemK⟩
      rw [Subgroup.mem_bot] at hmemBot
      exact (commutatorElement_eq_one_iff_mul_comm.mp hmemBot).symm
    ·
      intro hgC
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      by_contra hne
      have hJg : IsComponent (J.map (MulAut.conj (g : X)).toMonoidHom) :=
        CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (g : X)) hJ
      have hbotJg : J ⊓ J.map (MulAut.conj (g : X)).toMonoidHom = ⊥ :=
        inf_components_eq_bot_of_ne hJ hJg (Ne.symm hne) hZJ
      have hbJg : b ∈ J.map (MulAut.conj (g : X)).toMonoidHom := by
        refine Subgroup.mem_map.mpr ⟨b, hbJ, ?_⟩
        have hgb : (g : X) * b = b * (g : X) :=
          Subgroup.mem_centralizer_singleton_iff.mp hgC
        calc (g : X) * b * (g : X)⁻¹ = b * (g : X) * (g : X)⁻¹ := by rw [hgb]
          _ = b := by group
      have hbBot : b ∈ (⊥ : Subgroup X) := by
        rw [← hbotJg]
        exact ⟨hbJ, hbJg⟩
      rw [Subgroup.mem_bot] at hbBot
      exact hb1 hbBot
  let φ : ↥F →* X :=
    { toFun := fun g => ⁅(g : X), b⁆
      map_one' := by simp
      map_mul' := fun g h => by
        have hgb' : ⁅(g : X), b⁆ ∈ F := by
          have hbg : ⁅b, (g : X)⁆ ∈ F := by
            have hbg' : b * (g : X) * b⁻¹ ∈ F :=
              (Subgroup.mem_normalizer_iff.mp hbF (g : X)).mp g.2
            rw [commutatorElement_def]
            exact F.mul_mem hbg' (F.inv_mem g.2)
          rw [← commutatorElement_inv (g₁ := b) (g₂ := (g : X))]
          exact F.inv_mem hbg
        have hgb : ⁅(h : X), b⁆ ∈ F := by
          have hbh : ⁅b, (h : X)⁆ ∈ F := by
            have hbh' : b * (h : X) * b⁻¹ ∈ F :=
              (Subgroup.mem_normalizer_iff.mp hbF (h : X)).mp h.2
            rw [commutatorElement_def]
            exact F.mul_mem hbh' (F.inv_mem h.2)
          rw [← commutatorElement_inv (g₁ := b) (g₂ := (h : X))]
          exact F.inv_mem hbh
        change ⁅(g : X) * (h : X), b⁆ = ⁅(g : X), b⁆ * ⁅(h : X), b⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hg_comm : (g : X) * ⁅(h : X), b⁆ * (g : X)⁻¹ = ⁅(h : X), b⁆ := by
          have h := hFcomm (g : X) g.2 ⁅(h : X), b⁆ hgb
          rw [h]
          group
        rw [hg_comm]
        exact hFcomm ⁅(h : X), b⁆ hgb ⁅(g : X), b⁆ hgb' }
  have hφker : φ.ker = (Subgroup.centralizer ({b} : Set X)).subgroupOf F := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_mul_comm
  have hφrange : φ.range = ⁅F, Subgroup.zpowers b⁆ := by
    have hb2sq : b * b = 1 := by
      rw [← pow_two, ← hb2, pow_orderOf_eq_one]
    have hfwd : ∀ y ∈ φ.range, b * y * b⁻¹ ∈ φ.range := by
      rintro y ⟨g, rfl⟩
      refine ⟨⟨b * (g : X) * b⁻¹, (Subgroup.mem_normalizer_iff.mp hbF (g : X)).mp g.2⟩, ?_⟩
      show ⁅b * (g : X) * b⁻¹, b⁆ = b * ⁅(g : X), b⁆ * b⁻¹
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2sq
      have h := conjugate_commutatorElement (g₁ := (g : X)) (g₂ := b) (g₃ := b)
      rw [show b * b * b⁻¹ = b by rw [hb2sq]; simpa using hbinv] at h
      exact h.symm
    refine le_antisymm ?_ ?_
    · rintro _ ⟨g, rfl⟩
      exact Subgroup.commutator_mem_commutator g.2 (Subgroup.mem_zpowers b)
    · refine CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem ?_ ?_
      · rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · exact hfwd x
        · intro hx
          have h := hfwd (b * x * b⁻¹) hx
          have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2sq
          have e : b * (b * x * b⁻¹) * b⁻¹ = x := by
            rw [hbinv]
            rw [show b * (b * x * b) * b = (b * b) * x * (b * b) by group]
            rw [hb2sq]
            group
          rw [e] at h
          exact h
      · intro a ha
        exact ⟨⟨a, ha⟩, rfl⟩
  have hcard : Nat.card ↥⁅F, Subgroup.zpowers b⁆ = 2 := by
    rw [← hφrange, ← Subgroup.index_ker φ, hφker, ← hN_eq_cent, hidx]
  omega

end ComponentCase


section GeneralCase

theorem le_normalizer_of_isPCompIn_of_four_le_card_commutator
    {H0 J F : Subgroup G} {b : G}
    (hJ : IsPCompIn 2 H0 J) (hcen : CenterlessBar J)
    (hbJ : b ∈ J) (hb2 : orderOf b = 2)
    (hF0 : F ≤ H0) (hFel : IsElementaryAbelian 2 ↥F)
    (hbF : b ∈ Subgroup.normalizer (F : Set G))
    (hcomm : 4 ≤ Nat.card ↥⁅F, Subgroup.zpowers b⁆) :
    F ≤ Subgroup.normalizer (J : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := ↥H0
  let O : Subgroup H := pPrimeCore 2 H
  have hOnormal : O.Normal := pPrimeCore_normal
  let Q := H ⧸ O
  let π : H →* Q := QuotientGroup.mk' O
  let J' : Subgroup H := J.subgroupOf H0
  let F' : Subgroup H := F.subgroupOf H0
  let b' : H := ⟨b, hJ.1 hbJ⟩
  have hJ' : IsPComponent 2 J' := hJ.2
  obtain ⟨K, hK, hsub, hmap, -⟩ := hJ'
  have hJbComp : IsComponent (J'.map π) := by
    rw [hmap]
    exact hK
  have hOddO : Odd (Nat.card O) := by
    rcases Nat.even_or_odd (Nat.card O) with h | h
    · exact absurd (even_iff_two_dvd.mp h)
        ((Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := H)))
    · exact h
  have hFel' : IsElementaryAbelian 2 F' :=
    IsElementaryAbelian.subgroupOf (p := 2) hF0
  have hF'2 : IsPGroup 2 ↥F' := IsElementaryAbelian.isPGroup 2 ↥F'
  have hFO : F' ⊓ O = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxF, hxO⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hF'2) ⟨x, hxF⟩
    have hk' : orderOf x = 2 ^ k := by
      rwa [Subgroup.orderOf_mk] at hk
    have hxodd : Odd (orderOf x) :=
      Odd.of_dvd_nat hOddO (Subgroup.orderOf_dvd_natCard _ hxO)
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.2 hxodd) (hk' ▸ Nat.even_pow.2 ⟨even_two, hk0⟩)
    rw [hk0, pow_zero] at hk'
    exact orderOf_eq_one_iff.mp hk' 
  have hπ_inj : Function.Injective (fun x : F' => π x) := by
    intro x y hxy
    have hmem : (x : H)⁻¹ * (y : H) ∈ F' := F'.mul_mem (F'.inv_mem x.2) y.2
    have hπ1 : π ((x : H)⁻¹ * (y : H)) = 1 := by
      rw [map_mul, map_inv]
      change (π (x : H))⁻¹ * π (y : H) = 1
      have hxy' : π (x : H) = π (y : H) := hxy
      rw [hxy']
      group
    have hmemO : (x : H)⁻¹ * (y : H) ∈ O := (QuotientGroup.eq_one_iff _).mp hπ1
    have hbot : (x : H)⁻¹ * (y : H) ∈ (⊥ : Subgroup H) := by
      rw [← hFO]
      exact ⟨hmem, hmemO⟩
    rw [Subgroup.mem_bot] at hbot
    have hyx : (y : H) = (x : H) := by
      calc (y : H) = (x : H) * ((x : H)⁻¹ * (y : H)) := by rw [mul_inv_cancel_left]
        _ = (x : H) * 1 := by rw [hbot]
        _ = (x : H) := by rw [mul_one]
    exact Subtype.ext hyx.symm
  have hZJ : Subgroup.center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    rw [Subgroup.mem_bot]
    exact hcen z fun w => (Subgroup.mem_center_iff.mp hz w).symm
  have hZJb : Subgroup.center (J'.map π) = ⊥ := by
    obtain ⟨e0⟩ := CFSG.OddStandard.Solomon75.nonempty_quotPPrimeCore_equiv
      (Subgroup.subgroupOfEquivOfLe hJ.1)
    let e1 := CFSG.ComponentClassification.CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage
      2 J' hsub
    have h := Subgroup.map_center_eq (e0.symm.trans e1)
    rw [hZJ, Subgroup.map_bot] at h
    exact h.symm
  let b0 : Q := π b'
  let F0 : Subgroup Q := F'.map π
  have hb0Jb : b0 ∈ J'.map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hbJ)
  have hb'2 : orderOf b' = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hb2
  have hb0_2 : orderOf b0 = 2 :=
    CFSG.ComponentClassification.UnbalancedLayer.orderOf_mk_eq_two (R := O) hOddO hb'2
  have hFel0 : IsElementaryAbelian 2 F0 := by
    have : IsElementaryAbelian 2 F' := hFel'
    exact IsElementaryAbelian.map (p := 2) π
  have hb0F0 : b0 ∈ Subgroup.normalizer (F0 : Set Q) := by
    have h := CFSG.GroupTheory.map_subgroupOf_le_normalizer
      (M := H0) (B := Subgroup.zpowers b) (X := F) π (Subgroup.zpowers_le.mpr hbF)
    exact h (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers b)))
  have hb'H0 : b ∈ H0 := hJ.1 hbJ
  have hzpow : (Subgroup.zpowers b).subgroupOf H0 = Subgroup.zpowers b' := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hcommF_le : ⁅F, Subgroup.zpowers b⁆ ≤ F := by
    refine CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem hbF ?_
    intro a ha
    rw [commutatorElement_def]
    simpa only [mul_assoc] using
      F.mul_mem ha ((Subgroup.mem_normalizer_iff.mp hbF a⁻¹).mp (F.inv_mem ha))
  have hcommF_le_H0 : ⁅F, Subgroup.zpowers b⁆ ≤ H0 := hcommF_le.trans hF0
  have hb'N : b' ∈ Subgroup.normalizer (F' : Set H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hF0]
    exact Subgroup.mem_subgroupOf.mpr hbF
  have hC_le_F' : ⁅F', Subgroup.zpowers b'⁆ ≤ F' := by
    refine CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem hb'N ?_
    intro a ha
    rw [commutatorElement_def]
    simpa only [mul_assoc] using
      F'.mul_mem ha ((Subgroup.mem_normalizer_iff.mp hb'N a⁻¹).mp (F'.inv_mem ha))
  have hCmap : (⁅F', Subgroup.zpowers b'⁆).map H0.subtype = ⁅F, Subgroup.zpowers b⁆ := by
    have h := CFSG.commutator_subgroupOf_map_eq H0 F (Subgroup.zpowers b)
      hF0 (Subgroup.zpowers_le.mpr hb'H0)
    rw [Subgroup.commutator_comm ((Subgroup.zpowers b).subgroupOf H0) (F.subgroupOf H0)] at h
    rw [Subgroup.commutator_comm (Subgroup.zpowers b) F] at h
    rw [hzpow] at h
    exact h
  have hC_eq : ⁅F', Subgroup.zpowers b'⁆ = (⁅F, Subgroup.zpowers b⁆).subgroupOf H0 := by
    refine (Subgroup.map_injective H0.subtype_injective) ?_
    rw [hCmap, Subgroup.map_subgroupOf_eq_of_le hcommF_le_H0]
  have hCcard : Nat.card ↥⁅F', Subgroup.zpowers b'⁆ = Nat.card ↥⁅F, Subgroup.zpowers b⁆ := by
    rw [hC_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcommF_le_H0).toEquiv
  let πF : F' →* Q := π.comp F'.subtype
  have hπF_inj : Function.Injective πF := hπ_inj
  have hcard_map : Nat.card ↥((⁅F', Subgroup.zpowers b'⁆).map π) =
      Nat.card ↥⁅F', Subgroup.zpowers b'⁆ := by
    have h1 := Subgroup.card_map_of_injective (f := πF) hπF_inj
      (K := (⁅F', Subgroup.zpowers b'⁆).subgroupOf F')
    have h2 : ((⁅F', Subgroup.zpowers b'⁆).subgroupOf F').map πF =
        (⁅F', Subgroup.zpowers b'⁆).map π := by
      rw [show πF = π.comp F'.subtype from rfl, ← Subgroup.map_map]
      rw [Subgroup.map_subgroupOf_eq_of_le hC_le_F']
    have h3 : Nat.card ↥((⁅F', Subgroup.zpowers b'⁆).subgroupOf F') =
        Nat.card ↥⁅F', Subgroup.zpowers b'⁆ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC_le_F').toEquiv
    rw [h2, h3] at h1
    exact h1
  have hmapC : (⁅F', Subgroup.zpowers b'⁆).map π = ⁅F0, Subgroup.zpowers b0⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
  have hcomm0 : 4 ≤ Nat.card ↥⁅F0, Subgroup.zpowers b0⁆ := by
    rw [← hmapC, hcard_map, hCcard]
    exact hcomm
  have hF0N : F0 ≤ Subgroup.normalizer (J'.map π : Set Q) :=
    le_normalizer_of_isComponent_of_four_le_card_commutator hJbComp hZJb hb0Jb hb0_2
      hFel0 hb0F0 hcomm0
  intro f hf
  let d : H := ⟨f, hF0 hf⟩
  have hdF' : d ∈ F' := Subgroup.mem_subgroupOf.mpr hf
  have hdF0 : π d ∈ F0 := Subgroup.mem_map_of_mem π hdF'
  have hdN : π d ∈ Subgroup.normalizer ((J'.map π : Subgroup Q) : Set Q) := hF0N hdF0
  have hdN' : d ∈ Subgroup.normalizer (J' : Set H) :=
    CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hJ.2 hdN
  have hdN'' : d ∈ (Subgroup.normalizer (J : Set G)).subgroupOf H0 := by
    rw [Subgroup.subgroupOf_normalizer_eq hJ.1]
    exact hdN'
  exact Subgroup.mem_subgroupOf.mp hdN''

end GeneralCase


section SourceEndgame

omit [Finite G] in
theorem center_sup_zpowers_eq_centralizer {F : Subgroup G} {b : G}
    (hFel : IsElementaryAbelian 2 ↥F) (hb2 : orderOf b = 2)
    (hbF : b ∈ Subgroup.normalizer (F : Set G))
    (hcomm_card : Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ F) = 4)
    (hFcard : Nat.card ↥F = 16) :
    (Subgroup.center ↥(F ⊔ Subgroup.zpowers b)).map
      (F ⊔ Subgroup.zpowers b).subtype =
      Subgroup.centralizer ({b} : Set G) ⊓ F := by
  classical
  have hb2sq : b * b = 1 := by
    rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x :=
    (CFSG.GH74.GLS.C3.Layer1.Back.forall_of_isElementaryAbelian hFel).1
  have hF_le_centF : F ≤ Subgroup.centralizer (F : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hFcomm x hx y hy).symm
  have hb_not_cent : b ∉ Subgroup.centralizer (F : Set G) := by
    intro hbC
    have hCF : Subgroup.centralizer ({b} : Set G) ⊓ F = F := by
      refine le_antisymm inf_le_right ?_
      intro x hx
      refine ⟨?_, hx⟩
      exact (Subgroup.mem_centralizer_singleton_iff).mpr
        (Subgroup.mem_centralizer_iff.mp hbC x hx)
    have hcardF : Nat.card ↥F = 4 := by
      rw [← hCF, hcomm_card]
    omega
  have hb_pow_bot : Subgroup.zpowers b ⊓ Subgroup.centralizer (F : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_zpowers_iff] at hxZ
    obtain ⟨k, rfl⟩ := hxZ
    rcases CFSG.GroupTheory.zpow_eq_one_or_self_of_mul_self_eq_one hb2sq k with h | h
    · rw [Subgroup.mem_bot, h]
    · exfalso
      exact absurd (h ▸ hxC) hb_not_cent
  have hH_inf_centF : (F ⊔ Subgroup.zpowers b) ⊓ Subgroup.centralizer (F : Set G) = F := by
    have hmod := Subgroup.inf_sup_assoc_of_le
      (H := Subgroup.zpowers b) (K := Subgroup.centralizer (F : Set G)) (N := F)
      (Subgroup.zpowers_le.mpr hbF) hF_le_centF
    rw [inf_comm (Subgroup.centralizer (F : Set G)) (Subgroup.zpowers b), hb_pow_bot,
      bot_sup_eq] at hmod
    rw [sup_comm (Subgroup.zpowers b) F,
      inf_comm (Subgroup.centralizer (F : Set G)) (F ⊔ Subgroup.zpowers b)] at hmod
    exact hmod.symm
  calc
    (Subgroup.center ↥(F ⊔ Subgroup.zpowers b)).map
        (F ⊔ Subgroup.zpowers b).subtype
        = (F ⊔ Subgroup.zpowers b) ⊓
            Subgroup.centralizer ((F ⊔ Subgroup.zpowers b : Subgroup G) : Set G) :=
          CFSG.center_map_subtype_eq_inf_centralizer _
    _ = (F ⊔ Subgroup.zpowers b) ⊓
          (Subgroup.centralizer (F : Set G) ⊓ Subgroup.centralizer ({b} : Set G)) := by
          rw [CFSG.centralizer_sup_zpowers_eq]
    _ = ((F ⊔ Subgroup.zpowers b) ⊓ Subgroup.centralizer (F : Set G)) ⊓
          Subgroup.centralizer ({b} : Set G) := by rw [inf_assoc]
    _ = F ⊓ Subgroup.centralizer ({b} : Set G) := by rw [hH_inf_centF]
    _ = Subgroup.centralizer ({b} : Set G) ⊓ F := by rw [inf_comm]


omit [Finite G] in
theorem center_sup_zpowers_eq_commutator {F : Subgroup G} {b : G}
    (hFel : IsElementaryAbelian 2 ↥F) (hb2 : orderOf b = 2)
    (hbF : b ∈ Subgroup.normalizer (F : Set G))
    (hcomm_eq : ⁅F, Subgroup.zpowers b⁆ = Subgroup.centralizer ({b} : Set G) ⊓ F)
    (hcomm_card : Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ F) = 4)
    (hFcard : Nat.card ↥F = 16) :
    (Subgroup.center ↥(F ⊔ Subgroup.zpowers b)).map
      (F ⊔ Subgroup.zpowers b).subtype =
      ⁅F, Subgroup.zpowers b⁆ := by
  rw [center_sup_zpowers_eq_centralizer hFel hb2 hbF hcomm_card hFcard, ← hcomm_eq]


theorem false_of_source_A7_action
    {e b : G} {J F : Subgroup G}
    (hJ : IsPCompIn 2 (Subgroup.centralizer ({e} : Set G)) J)
    (hA7 : Nonempty (kBar J ≃* alternatingGroup (Fin 7)))
    (hbJ : b ∈ J) (hb2 : orderOf b = 2)
    (hF0 : F ≤ Subgroup.centralizer ({e} : Set G))
    (hFel : IsElementaryAbelian 2 ↥F)
    (hFcard : Nat.card ↥F = 16)
    (hbF : b ∈ Subgroup.normalizer (F : Set G))
    (hcomm_eq : ⁅F, Subgroup.zpowers b⁆ = Subgroup.centralizer ({b} : Set G) ⊓ F)
    (hcomm_card : Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ F) = 4) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : CenterlessBar J := centerlessBar_of_A7 hA7
  have hcomm4 : 4 ≤ Nat.card ↥⁅F, Subgroup.zpowers b⁆ := by
    rw [hcomm_eq, hcomm_card]
  have hFN : F ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_isPCompIn_of_four_le_card_commutator hJ hcen hbJ hb2 hF0 hFel hbF hcomm4
  have hcommJ : ⁅F, Subgroup.zpowers b⁆ ≤ J := by
    refine CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem (Subgroup.le_normalizer hbJ) ?_
    intro a ha
    have h := CFSG.GH74.GLS.Balance.Comp.commutator_mem (hFN ha) hbJ
    rw [← commutatorElement_inv (g₁ := b) (g₂ := a)]
    exact J.inv_mem h
  have hZeq := center_sup_zpowers_eq_commutator hFel hb2 hbF hcomm_eq hcomm_card hFcard
  have hZH : (Subgroup.center ↥(F ⊔ Subgroup.zpowers b)).map
      (F ⊔ Subgroup.zpowers b).subtype ≤ J := hZeq.le.trans hcommJ
  have hF4eq : pRank 2 ↥F = 4 := by
    have hcard := CFSG.GH74.GLS.C3.Layer1.Back.card_eq_two_pow_pRank hFel
    have hpow : 2 ^ pRank 2 ↥F = 2 ^ 4 := by
      rw [← hcard, hFcard]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  have hF2 : IsPGroup 2 ↥F := IsElementaryAbelian.isPGroup 2 ↥F
  have hbP : IsPGroup 2 ↥(Subgroup.zpowers b) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hb2, pow_one]
  have hH2 : IsPGroup 2 ↥(F ⊔ Subgroup.zpowers b) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' (p := 2) hbP hF2 (Subgroup.zpowers_le.mpr hbF)
  have hHK : F ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (J : Set G) :=
    sup_le hFN (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hbJ))
  exact false_of_pRank_four_of_A7 hH2 hHK hZH hA7 le_sup_left (by rw [hF4eq])

end SourceEndgame

end CFSG.GH74.GLS.Th2.Obs
