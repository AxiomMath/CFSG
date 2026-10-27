module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7C
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraConfining
public import Certificates.Certificate17027
public import Certificates.Certificate5952

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

section Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_of_lt' {P K : Subgroup G} (hP : IsPGroup 2 P) (hKP : K < P) :
    ∃ y ∈ P, y ∈ Subgroup.normalizer (K : Set G) ∧ y ∉ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let KP : Subgroup P := K.subgroupOf P
  have hne : KP ≠ ⊤ := by
    intro htop
    obtain ⟨z, hzP, hzK⟩ := IsConcreteLE.exists_of_lt hKP
    have : (⟨z, hzP⟩ : P) ∈ KP := by rw [htop]; trivial
    exact hzK (Subgroup.mem_subgroupOf.mp this)
  have hlt : KP < ⊤ := lt_top_iff_ne_top.2 hne
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
  have hlt' : KP < Subgroup.normalizer (KP : Set P) := hnc KP hlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt'
  refine ⟨x, x.2, ?_, fun h => hxnot (Subgroup.mem_subgroupOf.mpr h)⟩
  have hxsub : x ∈ (Subgroup.normalizer (K : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq (show K ≤ P from hKP.le)]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

omit [Finite G] in
theorem pCore_ne_bot_of_central {X : Subgroup G} {u : G} (huX : u ∈ X) (hu1 : u ≠ 1)
    (hu2 : u * u = 1) (hXC : X ≤ Subgroup.centralizer ({u} : Set G)) : pCoreOf 2 X ≠ ⊥ := by
  intro hbot
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ((pow_two u).trans hu2) hu1
  have hle : Subgroup.zpowers u ≤ pCoreOf 2 X := by
    refine le_pCoreOf_of_normalizes (Subgroup.zpowers_le.mpr huX) ?_ hz2
    intro g hg
    have hc : u * g = g * u := Subgroup.mem_centralizer_iff.mp (hXC hg) u rfl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases (mem_zpowers_two hu2 x).mp hx with h | h
      · rw [h]
        simp
      · have : g * u * g⁻¹ = u := by
          calc g * u * g⁻¹ = u * g * g⁻¹ := by rw [hc]
            _ = u := by group
        rw [h, this]
        exact Subgroup.mem_zpowers _
    · intro hx
      rcases (mem_zpowers_two hu2 _).mp hx with h | h
      · have : x = 1 := by
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group
        rw [this]
        exact one_mem _
      · have : x = u := by
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = g⁻¹ * u * g := by rw [h]
            _ = g⁻¹ * (u * g) := by group
            _ = g⁻¹ * (g * u) := by rw [hc]
            _ = u := by group
        rw [this]
        exact Subgroup.mem_zpowers _
  rw [hbot] at hle
  have := hle (Subgroup.mem_zpowers u)
  exact hu1 (Subgroup.mem_bot.mp this)

end Generic

theorem vact_swap24_g1w : vact (Equiv.swap (2 : Fin 5) 4) g1w = g1w :=
  Subtype.ext (by decide +kernel)

theorem swap24_not_fix4 : ¬ (Equiv.swap (2 : Fin 5) 4) 4 = 4 := by decide +kernel

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem normalizer_le_M (C : StdCfg T M H S L) {A : Subgroup G} (hA : A ≠ ⊥) (hA2 : IsPGroup 2 A)
    (hTA : T ≤ Subgroup.normalizer (A : Set G)) : Subgroup.normalizer (A : Set G) ≤ M := by
  classical
  have h2 : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (A : Set G)) := ⟨A, hA, hA2, rfl⟩
  let 𝒮 : Set (Subgroup G) :=
    {H' | CFSG.Assembly.IsTwoLocal H' ∧ Subgroup.normalizer (A : Set G) ≤ H'}
  obtain ⟨H₀, hH₀⟩ := (Set.toFinite 𝒮).exists_maximal ⟨_, h2, le_rfl⟩
  have hmax : CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal H₀ :=
    ⟨hH₀.1.1, fun H' hH' hle => le_antisymm (hH₀.2 ⟨hH', hH₀.1.2.trans hle⟩ hle) hle⟩
  have hM : H₀ = M := C.hcs.setting.unique H₀ hmax (hTA.trans hH₀.1.2)
  exact hH₀.1.2.trans hM.le

theorem u0_mem_T (C : StdCfg T M H S L) : C.u0 ∈ T :=
  C.hcs.le_T (blockU_le_S C.hcs C.hj C.u0_mem_U)

theorem u0_mem_Cu (C : StdCfg T M H S L) : C.u0 ∈ centralizerElem C.u0 := by
  show C.u0 ∈ Subgroup.centralizer ({C.u0} : Set G)
  exact Subgroup.mem_centralizer_iff.2 fun g hg => by
    rw [Set.mem_singleton_iff] at hg
    rw [hg]

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem card_Tu
    (hR : C.u0 ∈ centerOf (baum S)) : Nat.card ↥(T ⊓ centralizerElem C.u0) = 128 := by
  have h1 := Subgroup.relIndex_mul_card (T ⊓ centralizerElem C.u0) T
  rw [inf_eq_left.mpr inf_le_left, X.Tu_index hR, X.card_T] at h1
  omega

theorem Tu_sylow
    (hR : C.u0 ∈ centerOf (baum S)) :
    IsSylowTwoOf (T ⊓ centralizerElem C.u0) (centralizerElem C.u0) := by
  set Tu : Subgroup G := T ⊓ centralizerElem C.u0 with hTu
  have hTu2 : IsPGroup 2 ↥Tu := C.hcs.setting.isPGroup.to_le inf_le_left
  have hTuC : Tu ≤ centralizerElem C.u0 := inf_le_right
  have hTuNe : Tu ≠ ⊥ := by
    intro h
    have : C.u0 ∈ Tu := ⟨C.u0_mem_T, C.u0_mem_Cu⟩
    rw [h] at this
    exact X.u0_ne_one (Subgroup.mem_bot.mp this)
  have hTuT : (Tu.subgroupOf T).Normal := by
    apply Subgroup.normal_of_index_eq_two
    exact X.Tu_index hR
  have hTN : T ≤ Subgroup.normalizer (Tu : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hTuT
  have hNM : Subgroup.normalizer (Tu : Set G) ≤ M := C.normalizer_le_M hTuNe hTu2 hTN
  obtain ⟨P', hTuP', hP'⟩ := exists_isSylowTwoOf_of_le hTuC hTu2
  have hP'eq : P' = Tu := by
    by_contra hne
    have hlt : Tu < P' := lt_of_le_of_ne hTuP' (Ne.symm hne)
    obtain ⟨y, hyP, hyN, hyT⟩ := exists_mem_normalizer_not_mem_of_lt' hP'.isPGroup hlt
    have hyC : y ∈ centralizerElem C.u0 := hP'.le hyP
    apply hyT
    have hyM : y ∈ M ⊓ centralizerElem C.u0 := ⟨hNM hyN, hyC⟩
    rw [← X.Tu_eq hR] at hyM
    exact hyM
  rw [← hP'eq]
  exact hP'

theorem mem_M_iff_cent (y : G) : y ∈ M ↔ y * C.zU * y⁻¹ = C.zU := by
  constructor
  · intro hy
    have hc : C.zU * y = y * C.zU := Subgroup.mem_centralizer_iff.mp (X.M_le_GZ hy) C.zU rfl
    calc y * C.zU * y⁻¹ = C.zU * y * y⁻¹ := by rw [hc]
      _ = C.zU := by group
  · intro hy
    apply X.GZ_le_M
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    rw [Set.mem_singleton_iff] at hg
    subst hg
    calc C.zU * y = (y * C.zU * y⁻¹) * y := by rw [hy]
      _ = y * C.zU := by group

theorem u_not_conj
    (hR : C.u0 ∈ centerOf (baum S)) (g : G) : g⁻¹ * C.zU * g ≠ C.u0 := by
  intro h
  have hmem : ∀ x : G, x ∈ centralizerElem C.u0 ↔ g * x * g⁻¹ ∈ M := by
    intro x
    rw [X.mem_M_iff_cent, mem_Cu_iff]
    constructor
    · intro hx
      rw [← h] at hx
      calc (g * x * g⁻¹) * C.zU * (g * x * g⁻¹)⁻¹ = g * (x * (g⁻¹ * C.zU * g) * x⁻¹) * g⁻¹ := by
            group
        _ = g * (g⁻¹ * C.zU * g) * g⁻¹ := by rw [hx]
        _ = C.zU := by group
    · intro hy
      rw [← h]
      calc x * (g⁻¹ * C.zU * g) * x⁻¹ =
          g⁻¹ * ((g * x * g⁻¹) * C.zU * (g * x * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * C.zU * g := by rw [hy]
  have hmap : (centralizerElem C.u0).map (MulAut.conj g).toMonoidHom = M := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).mp hx
    · intro hy
      refine ⟨g⁻¹ * y * g, (hmem _).mpr ?_, ?_⟩
      · have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        rw [this]
        exact hy
      · show g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have hcard : Nat.card M = Nat.card (centralizerElem C.u0) := by
    have := Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (K := centralizerElem C.u0) (MulAut.conj g).injective
    rw [hmap] at this
    exact this
  have h1 := (X.Tu_sylow hR).card_eq
  have h2 := (C.sylow_T_of_le C.hcs.setting.le).card_eq
  rw [X.card_Tu hR] at h1
  rw [X.card_T] at h2
  have h3 : twoPart M = twoPart (centralizerElem C.u0) := by
    unfold twoPart
    rw [hcard]
  omega

theorem Gu_gamma2
    (hR : C.u0 ∈ centerOf (baum S))
    (hCU : Subgroup.centralizer (blockU L : Set G) = blockU L) :
    IsGamma2 M (centralizerElem C.u0) := by
  have hcs := C.hcs
  have hSu := X.Su (u := C.u0) rfl hR
  have hRC : baum S ≤ centralizerElem C.u0 := hSu ▸ inf_le_right
  have hRH : baum S ≤ H := baum_le_H hcs
  set Hu : Subgroup G := H ⊓ centralizerElem C.u0 with hHu
  have hRHu : baum S ≤ Hu := le_inf hRH hRC
  have hUHu : blockU L ≤ Hu := C.U_le_R.trans hRHu
  have hQR : pCoreOf 2 H ≤ baum S := pCoreOf_le_baum hcs C.F
  have hC := hcs.gamma0.pCore_centralizer_le_of_charTwo hcs.setting hcs.sylow_inf hcs.charTwo hQR
  have hconf : IsConfining M (baum S) :=
    IsGamma0.isConfining_of_relIndex_two hcs.setting hcs.gamma0 hcs.sylow_inf
      (C5.thompsonJ_le_baum' S) baum_le_S X.R_index hC
  have hpcHu : pCoreOf 2 Hu ≠ ⊥ :=
    pCore_ne_bot_of_central ⟨C.u0_mem_H, C.u0_mem_Cu⟩ (by
      intro h
      have : C.iV g1w = C.iV 0 := by
        rw [C.iV_zero]
        exact Subtype.ext h
      exact g1_ne_zero (congrArg Subtype.val (C.iV_inj X.hTC this))) C.u0_mul_self inf_le_right
  have hU2 : IsPGroup 2 ↥(blockU L) := hcs.sylow.isPGroup.to_le (blockU_le_S hcs C.hj)
  have hUcore : blockU L ≤ pCoreOf 2 Hu := by
    refine le_pCoreOf_of_normalizes hUHu (fun h hh => ?_) hU2
    exact C1.mem_normalizer_blockU (C56.H_le_normalizer hcs C.hj hh.1)
  have hchar : CharTwo Hu := by
    rintro g ⟨hgHu, hgC⟩
    have hgU : g ∈ Subgroup.centralizer (blockU L : Set G) :=
      Subgroup.centralizer_le (by exact_mod_cast hUcore) hgC
    rw [hCU] at hgU
    exact hUcore hgU
  have hHuM : ¬ Hu ≤ M := by
    intro hle
    have hsH : ((X.s (Equiv.swap (2 : Fin 5) 4) : ↥H) : G) ∈ Hu := by
      refine ⟨(X.s _).2, (X.mem_cent_iff (X.s (Equiv.swap (2 : Fin 5) 4))).mpr ?_⟩
      rw [X.hs]
      exact vact_swap24_g1w
    have := (C.mem_M_iff (X.s (Equiv.swap (2 : Fin 5) 4))).mp (hle hsH)
    rw [X.hs, mem_S4std] at this
    exact swap24_not_fix4 this
  have hpc : pCoreOf 2 (centralizerElem C.u0) ≠ ⊥ :=
    pCore_ne_bot_of_central C.u0_mem_Cu (by
      intro h
      have : C.iV g1w = C.iV 0 := by
        rw [C.iV_zero]
        exact Subtype.ext h
      exact g1_ne_zero (congrArg Subtype.val (C.iV_inj X.hTC this))) C.u0_mul_self le_rfl
  have hΓ : IsGamma M (centralizerElem C.u0) :=
    ⟨hpc, baum S, Hu, ⟨hconf, hRHu, hpcHu, hchar, hHuM⟩, inf_le_right⟩
  have hT : Nat.card T = 2 * Nat.card S := by rw [X.card_T, X.card_S]
  obtain ⟨-, hext⟩ := hcs.gamma0.isGamma2_of_card_eq_two_mul hcs.setting hcs.sylow_inf hT
  have hle : Nat.card S ≤ twoPart (centralizerElem C.u0) := by
    have := (X.Tu_sylow hR).card_eq
    rw [X.card_Tu hR] at this
    rw [X.card_S]
    omega
  exact (hext _ hΓ hle).2

end Sec

end CFSG.QuasithinUnique.A5
