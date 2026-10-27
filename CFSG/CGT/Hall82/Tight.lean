module

public import CFSG.CGT.Hall82.TIBranch
public import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate
public import CFSG.Adapters.ExceptionalCatalogReverse
public import CFSG.GF2Type.Aschbacher1976Common.DihedralRank

public section

namespace CFSG.CGT.Hall82

open CFSG CFSG.Assembly CFSG.Open
  CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.CGT.PushingUpLit.SolK
open scoped commutatorElement

theorem mem_of_conj_le_of_isMaximalTwoLocal {G : Type} [Group G] [Finite G]
    {M X : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    (huniq : maximalTwoLocalsContaining (X : Set G) = {M})
    {g : G} (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ M) : g ∈ M := by
  set M' : Subgroup G := M.map (MulAut.conj g⁻¹).toMonoidHom with hM'
  have hmax : CFSG.IsMaximalTwoLocal M' := isMaximalTwoLocal_conj hM g⁻¹
  have hXM' : (X : Set G) ⊆ M' := fun x hx => ⟨g * x * g⁻¹, hg x hx, by
    simp
    group⟩
  have hmem : M' ∈ maximalTwoLocalsContaining (X : Set G) := ⟨hmax, hXM'⟩
  rw [huniq] at hmem
  have hM'M : M' = M := hmem
  have hconj_eq : M.map (MulAut.conj g).toMonoidHom = M := by
    have h := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hM'M
    rw [Subgroup.map_map] at h
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id] at h
    exact h.symm
  have hgN : g ∈ Subgroup.normalizer (M : Set G) := by
    rwa [Subgroup.mem_normalizer_iff_map_conj_eq]
  rwa [CFSG.RankThree.PartTwo.Late.normalizer_self_of_isMaximalTwoLocal hM] at hgN

theorem mem_of_common_involution_of_isMaximalTwoLocal {G : Type} [Group G] [Finite G]
    {M X : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    (huniq : maximalTwoLocalsContaining (X : Set G) = {M})
    {g z : G} (hzC : z ∈ Subgroup.centralizer (X : Set G)) (hz2 : orderOf z = 2)
    (hgz : g * z * g⁻¹ ∈ Subgroup.centralizer (X : Set G)) : g ∈ M := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; simp)
  have hZ : Subgroup.zpowers z ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hz1
  have hloc : IsPLocal 2 (Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) :=
    ⟨_, hZ, hZ2, rfl⟩
  have hCN : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hxz : ∀ x ∈ X, x * z * x⁻¹ = z := fun x hx => by
    have := Subgroup.mem_centralizer_iff.1 hzC x hx
    rw [this]
    group
  have hXN : X ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := fun x hx =>
    hCN (mem_centralizer_zpowers_iff.2 (hxz x hx))
  have hle := local_le_of_unique huniq hloc hXN
  have hconj : ∀ x ∈ X, g⁻¹ * x * g⁻¹⁻¹ ∈ M := by
    intro x hx
    rw [inv_inv]
    have hc := Subgroup.mem_centralizer_iff.1 hgz x hx
    refine hle (hCN (mem_centralizer_zpowers_iff.2 ?_))
    calc g⁻¹ * x * g * z * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g := by
          group
      _ = z := by rw [hc]; group
  have h1 : g⁻¹ ∈ M := mem_of_conj_le_of_isMaximalTwoLocal hM huniq hconj
  simpa using M.inv_mem h1

theorem le_normalizer_centralizer_of_normalizer_eq {G : Type} [Group G] {M X : Subgroup G}
    (hN : Subgroup.normalizer (X : Set G) = M) :
    M ≤ Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  have hCM : Subgroup.centralizer (X : Set G) ≤ M := by
    rw [← hN]
    exact Subgroup.centralizer_le_normalizer (X : Set G)
  have hnorm : ((Subgroup.centralizer (X : Set G)).subgroupOf M).Normal := by
    rw [← hN]
    exact Subgroup.normal_subgroupOf_centralizer_normalizer (X : Set G)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).1 hnorm

theorem pCoreOf_centralizer_eq_inf {G : Type} [Group G] {M X : Subgroup G}
    (hN : Subgroup.normalizer (X : Set G) = M) :
    pCoreOf 2 (Subgroup.centralizer (X : Set G)) =
      pCoreOf 2 M ⊓ Subgroup.centralizer (X : Set G) := by
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  have hCM : C ≤ M := by
    rw [← hN]
    exact Subgroup.centralizer_le_normalizer (X : Set G)
  have hCnorm : ∀ m ∈ M, ∀ c ∈ C, m * c * m⁻¹ ∈ C :=
    fun m hm c hc =>
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_centralizer_of_normalizer_eq hN hm) c).1 hc
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ (pCoreOf_le_self C)
    refine le_pCoreOf_of_normalized ((pCoreOf_le_self C).trans hCM) ?_ (isPGroup_pCoreOf' C)
    intro m hm x hx
    exact pCoreOf_normalized_of_normal hCnorm hm hx
  · refine le_pCoreOf_of_normalized inf_le_right ?_
      (isPGroup_of_le (isPGroup_pCoreOf' M) inf_le_left)
    intro c hc x hx
    exact Subgroup.mem_inf.2 ⟨pCoreOf_normalized M (hCM hc) hx.1, hCnorm c (hCM hc) x hx.2⟩

theorem centralizer_eq_bot_of_pCoreOf_eq_bot {G : Type} [Group G] [Finite G]
    {M X : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    (hN : Subgroup.normalizer (X : Set G) = M)
    (hchar : CFSG.Assembly.IsCharTwoType G)
    (hO : pCoreOf 2 (Subgroup.centralizer (X : Set G)) = ⊥) :
    Subgroup.centralizer (X : Set G) = ⊥ := by
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  have hCM : C ≤ M := by
    rw [← hN]
    exact Subgroup.centralizer_le_normalizer (X : Set G)
  have hCnorm : ∀ m ∈ M, ∀ c ∈ C, m * c * m⁻¹ ∈ C :=
    fun m hm c hc =>
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_centralizer_of_normalizer_eq hN hm) c).1 hc
  have hO' : pCoreOf 2 C = ⊥ := by simpa [hC] using hO
  have hCinfO_bot : C ⊓ pCoreOf 2 M = ⊥ := by
    have h := pCoreOf_centralizer_eq_inf (M := M) (X := X) hN
    have h' : pCoreOf 2 C = pCoreOf 2 M ⊓ C := by simpa [hC] using h
    rw [hO'] at h'
    rw [inf_comm]
    exact h'.symm
  have hcent : C ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hcomm_mem : ⁅c, q⁆ ∈ C ⊓ pCoreOf 2 M := by
      constructor
      · have hqc : q * c⁻¹ * q⁻¹ ∈ C := hCnorm q (pCoreOf_le_self M hq) c⁻¹ (C.inv_mem hc)
        have h1 : c * (q * c⁻¹ * q⁻¹) ∈ C := C.mul_mem hc hqc
        simpa [commutatorElement_def, mul_assoc] using h1
      · have h1 : c * q * c⁻¹ ∈ pCoreOf 2 M :=
          pCoreOf_normalized M (hCM hc) hq
        exact (pCoreOf 2 M).mul_mem h1 ((pCoreOf 2 M).inv_mem hq)
    have hcomm_one : ⁅c, q⁆ = 1 := by
      have h := hcomm_mem
      rw [hCinfO_bot] at h
      exact Subgroup.mem_bot.1 h
    exact (commutatorElement_eq_one_iff_mul_comm.1 hcomm_one).symm
  have hC_le_O : C ≤ pCoreOf 2 M := by
    have hcharM := hchar M hM.1
    intro c hc
    exact hcharM ⟨hCM hc, hcent hc⟩
  have hle : C ≤ C ⊓ pCoreOf 2 M := le_inf le_rfl hC_le_O
  rw [hCinfO_bot] at hle
  exact le_bot_iff.1 hle

theorem normalizer_centralizer_eq_of_even {G : Type} [Group G] [Finite G]
    {M X : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    (hN : Subgroup.normalizer (X : Set G) = M)
    (hchar : CFSG.Assembly.IsCharTwoType G)
    (hev : Even (Nat.card ↥(Subgroup.centralizer (X : Set G)))) :
    Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) = M := by
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  have hCM : C ≤ M := by
    rw [← hN]
    exact Subgroup.centralizer_le_normalizer (X : Set G)
  refine le_antisymm ?_ ?_
  · have hOne : pCoreOf 2 C ≠ ⊥ := by
      intro hO
      have hCbot : C = ⊥ :=
        centralizer_eq_bot_of_pCoreOf_eq_bot hM hN hchar (by simpa [hC] using hO)
      have hcard : Nat.card ↥C = 1 := by rw [hCbot, Subgroup.card_bot]
      rw [hcard] at hev
      exact absurd hev (by norm_num)
    have hOleN : Subgroup.normalizer (C : Set G) ≤
        Subgroup.normalizer (pCoreOf 2 C : Set G) := by
      have hnormC : ∀ n ∈ Subgroup.normalizer (C : Set G), ∀ k ∈ C, n * k * n⁻¹ ∈ C :=
        fun n hn k hk => (Subgroup.mem_normalizer_iff.1 hn k).1 hk
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => pCoreOf_normalized_of_normal hnormC hg hx, fun hx => ?_⟩
      have hg' : g⁻¹ ∈ Subgroup.normalizer (C : Set G) := (Subgroup.normalizer _).inv_mem hg
      have := pCoreOf_normalized_of_normal hnormC hg' hx
      simpa [mul_assoc] using this
    have hloc : IsPLocal 2 (Subgroup.normalizer (pCoreOf 2 C : Set G)) :=
      ⟨pCoreOf 2 C, hOne, isPGroup_pCoreOf' C, rfl⟩
    have hN_le_M : Subgroup.normalizer (pCoreOf 2 C : Set G) ≤ M := by
      by_contra hle
      have hlt : M < Subgroup.normalizer (pCoreOf 2 C : Set G) :=
        lt_of_le_of_ne ((le_normalizer_centralizer_of_normalizer_eq hN).trans hOleN)
          (fun h => hle (le_of_eq h.symm))
      exact hM.2 _ hlt hloc
    exact hOleN.trans hN_le_M
  · have h := le_normalizer_centralizer_of_normalizer_eq hN
    simpa [hC] using h

theorem tightlyEmbedded_centralizer_of_even {G : Type} [Group G] [Finite G]
    {M X : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    (hN : Subgroup.normalizer (X : Set G) = M)
    (huniq : maximalTwoLocalsContaining (X : Set G) = {M})
    (hev : Even (Nat.card ↥(Subgroup.centralizer (X : Set G)))) :
    TightlyEmbedded (Subgroup.centralizer (X : Set G)) :=
  CFSG.StandardSubgroupAPI.tightlyEmbedded_of_involution hev fun g z hz hz2 =>
    le_normalizer_centralizer_of_normalizer_eq hN
      (mem_of_common_involution_of_isMaximalTwoLocal hM huniq
        (Subgroup.mem_inf.1 hz).1 hz2
        ((mem_rightConjugate_iff _ g _).1 (Subgroup.mem_inf.1 hz).2))

theorem le_pCoreOf_of_isPGroup_le_of_sylow {G : Type} [Group G] [Finite G]
    {C : Subgroup G} (R : Sylow 2 C)
    (hRO : (R : Subgroup C).map C.subtype = pCoreOf 2 C)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPC : P ≤ C) : P ≤ pCoreOf 2 C := by
  have hO2 : IsPGroup 2 (pCoreOf 2 C) := isPGroup_pCoreOf' C
  have hOC : pCoreOf 2 C ≤ C := pCoreOf_le_self C
  have hPN : P ≤ Subgroup.normalizer (pCoreOf 2 C : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => pCoreOf_normalized C (hPC hp) hq, fun hq => ?_⟩
    have h1 := pCoreOf_normalized C (C.inv_mem (hPC hp)) hq
    have e : p⁻¹ * (p * q * p⁻¹) * (p⁻¹)⁻¹ = q := by group
    rwa [e] at h1
  have hsup : IsPGroup 2 ((pCoreOf 2 C ⊔ P) : Subgroup G) :=
    hO2.to_sup_of_normal_left' hP hPN
  have hleC : ((pCoreOf 2 C ⊔ P) : Subgroup G) ≤ C := sup_le hOC hPC
  have hsup' : IsPGroup 2 (((pCoreOf 2 C ⊔ P) : Subgroup G).subgroupOf C) := by
    let e : (((pCoreOf 2 C ⊔ P) : Subgroup G).subgroupOf C) ≃*
        ((pCoreOf 2 C ⊔ P) : Subgroup G) := Subgroup.subgroupOfEquivOfLe hleC
    exact hsup.of_equiv e.symm
  have hRle : (R : Subgroup C) ≤ (((pCoreOf 2 C ⊔ P) : Subgroup G).subgroupOf C) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_left (by rw [← hRO]; exact ⟨x, hx, rfl⟩)
  have heq : (((pCoreOf 2 C ⊔ P) : Subgroup G).subgroupOf C) = (R : Subgroup C) :=
    R.is_maximal' hsup' hRle
  intro p hp
  have hp' : (⟨p, hPC hp⟩ : C) ∈ (R : Subgroup C) := by
    rw [← heq]
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right hp)
  rw [← hRO]
  exact ⟨⟨p, hPC hp⟩, hp', rfl⟩

theorem isTI_pCoreOf_centralizer {G : Type} [Group G] [Finite G]
    {M X : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    (hN : Subgroup.normalizer (X : Set G) = M)
    (huniq : maximalTwoLocalsContaining (X : Set G) = {M}) :
    CFSG.CGT.Timmesfeld75.IsTI (pCoreOf 2 (Subgroup.centralizer (X : Set G))) := by
  intro g
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  set W : Subgroup G := pCoreOf 2 C with hW
  change W ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g W = ⊥ ∨
    W ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g W = W
  by_cases hdis : W ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g W = ⊥
  · exact Or.inl hdis
  · right
    have hInt2 : IsPGroup 2 ↥(W ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g W) := by
      simpa [hW] using (isPGroup_pCoreOf' C).to_inf_left
    have hcard_gt1 : 1 < Nat.card ↥(W ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g W) :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W ⊓
        CFSG.CGT.Timmesfeld75.conjSubgroup g W)).2 hdis
    have h2dvd : 2 ∣ Nat.card ↥(W ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g W) :=
      hInt2.card_eq_or_dvd.resolve_left (by omega)
    obtain ⟨z, hz⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(W ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g W))
        2 h2dvd
    let t : G := (z : G)
    have htW : t ∈ W := z.2.1
    have htC : t ∈ C := pCoreOf_le_self C htW
    have ht2 : orderOf t = 2 := by
      rw [show t = (z : G) by rfl, Subgroup.orderOf_coe]
      exact hz
    have hgtW : g⁻¹ * t * g ∈ W := by
      have := (CFSG.CGT.Timmesfeld75.mem_conjSubgroup).1 z.2.2
      simpa using this
    have hgtC : g⁻¹ * t * g ∈ C := pCoreOf_le_self C hgtW
    have hginvM : g⁻¹ ∈ M :=
      mem_of_common_involution_of_isMaximalTwoLocal hM huniq htC ht2 (by simpa using hgtC)
    have hgM : g ∈ M := by simpa using M.inv_mem hginvM
    have hMW : ∀ m ∈ M, ∀ w ∈ W, m * w * m⁻¹ ∈ W := by
      intro m hm w hw
      have hmN : m ∈ Subgroup.normalizer (C : Set G) :=
        le_normalizer_centralizer_of_normalizer_eq hN hm
      exact pCoreOf_normalized_of_normal
        (N := Subgroup.normalizer (C : Set G))
        (fun n hn k hk => (Subgroup.mem_normalizer_iff.1 hn k).1 hk) hmN hw
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g W := (Subgroup.mem_inf.1 hx).2
      obtain ⟨w, hw, rfl⟩ := (Subgroup.mem_map).1 hx'
      simpa [MulAut.conj_apply] using hMW g hgM w hw
    · intro x hx
      refine Subgroup.mem_inf.2 ⟨hx, ?_⟩
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      have h := hMW g⁻¹ (M.inv_mem hgM) x hx
      simpa using h

theorem normalizer_le_of_le_centralizer {G : Type} [Group G] [Finite G]
    {M X Z : Subgroup G} (huniq : maximalTwoLocalsContaining (X : Set G) = {M})
    (hZ : Z ≠ ⊥) (hZ2 : IsPGroup 2 Z)
    (hZC : Z ≤ Subgroup.centralizer (X : Set G)) :
    Subgroup.normalizer (Z : Set G) ≤ M :=
  local_le_of_unique huniq ⟨Z, hZ, hZ2, rfl⟩
    ((Subgroup.le_centralizer_iff.mpr hZC).trans (Subgroup.centralizer_le_normalizer (Z : Set G)))

theorem centralizer_le_of_mem_pCoreOf {G : Type} [Group G] [Finite G]
    {M X : Subgroup G} (huniq : maximalTwoLocalsContaining (X : Set G) = {M})
    {w : G} (hw : w ∈ pCoreOf 2 (Subgroup.centralizer (X : Set G))) (hw1 : w ≠ 1) :
    Subgroup.centralizer ({w} : Set G) ≤ M := by
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  have hwC : w ∈ C := pCoreOf_le_self C hw
  have hW2 : IsPGroup 2 (Subgroup.zpowers w) :=
    (isPGroup_pCoreOf' C).to_le (Subgroup.zpowers_le.mpr hw)
  have hWne : Subgroup.zpowers w ≠ ⊥ := by
    simpa [Subgroup.zpowers_eq_bot] using hw1
  have hle := normalizer_le_of_le_centralizer huniq hWne hW2
    (Subgroup.zpowers_le.mpr hwC)
  calc Subgroup.centralizer ({w} : Set G)
      = Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    _ ≤ Subgroup.normalizer (Subgroup.zpowers w : Set G) :=
        Subgroup.centralizer_le_normalizer _
    _ ≤ M := hle

theorem normalizer_pCoreOf_centralizer_eq {G : Type} [Group G] [Finite G]
    {M X : Subgroup G} (hN : Subgroup.normalizer (X : Set G) = M)
    (huniq : maximalTwoLocalsContaining (X : Set G) = {M})
    (hO : pCoreOf 2 (Subgroup.centralizer (X : Set G)) ≠ ⊥) :
    Subgroup.normalizer (pCoreOf 2 (Subgroup.centralizer (X : Set G)) : Set G) = M := by
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  have hO' : pCoreOf 2 C ≠ ⊥ := by simpa [hC] using hO
  refine le_antisymm ?_ ?_
  · have h := normalizer_le_of_le_centralizer (M := M) (X := X)
      (Z := pCoreOf 2 C) huniq hO' (isPGroup_pCoreOf' C) (pCoreOf_le_self C)
    simpa [hC] using h
  · intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have hmN : m ∈ Subgroup.normalizer (C : Set G) :=
        le_normalizer_centralizer_of_normalizer_eq hN hm
      exact pCoreOf_normalized_of_normal
        (N := Subgroup.normalizer (C : Set G))
        (fun n hn k hk => (Subgroup.mem_normalizer_iff.1 hn k).1 hk) hmN hw
    · intro hw
      have hmN : m⁻¹ ∈ Subgroup.normalizer (C : Set G) :=
        (Subgroup.normalizer (C : Set G)).inv_mem
          (le_normalizer_centralizer_of_normalizer_eq hN hm)
      have h := pCoreOf_normalized_of_normal
        (N := Subgroup.normalizer (C : Set G))
        (fun n hn k hk => (Subgroup.mem_normalizer_iff.1 hn k).1 hk) hmN hw
      simpa [mul_assoc] using h

theorem inCatalog_of_quaternion_outcome
    {G : Type} [Group G]
    (h : StatedClassicalModel G .PSL 3 3 1 ∨ StatedClassicalModel G .PSU 3 3 1 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M12 ∨
      CFSG.Blueprint.LieModel G .G2 0 3 1) : InCatalog G := by
  rcases h with h | h | h | h | h
  · exact CFSG.Assembly.LowTwoRank.inCatalog_of_classicalModel G .PSL 3 3 1 h
  · exact CFSG.Assembly.LowTwoRank.inCatalog_of_classicalModel G .PSU 3 3 1 h
  · exact CFSG.RankThree.GF2n.sporadicBridge_M11 G h
  · exact CFSG.RankThree.GF2n.sporadicBridge_M12 G h
  · exact CFSG.RankThree.GF2n.inCatalog_of_chevalleyExceptionalModel_G2_three
      (CFSG.RankThree.GF2n.chevalleyExceptionalModel_of_lieModel (by decide) h)

theorem inCatalog_or_tight
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hSTT : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight)
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hchar : CFSG.Assembly.IsCharTwoType G)
    {M X : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    (hN : Subgroup.normalizer (X : Set G) = M)
    (huniq : CFSG.maximalTwoLocalsContaining (X : Set G) = {M})
    {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) (hE8 : 8 ≤ Nat.card E) :
    CFSG.Assembly.InCatalog G ∨ Subgroup.centralizer (X : Set G) = ⊥ ∨
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G)) ≠ ⊥ ∧
        (∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) →
          P ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G))) ∧
        ((IsCyclic ↥(CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G))) ∧
            Nat.card ↥(CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G))) = 4) ∨
          CFSG.Open.IsElemAbelian 2 (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G)))) ∧
        ∃ g : G, CFSG.CGT.Timmesfeld75.conjSubgroup g
            (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G))) ≤ M ∧
          CFSG.CGT.Timmesfeld75.conjSubgroup g
            (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G))) ≠
            CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G))) := by
  classical
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  by_cases hev : Even (Nat.card ↥C)
  · have hNC : Subgroup.normalizer (C : Set G) = M := by
      rw [hC]
      exact normalizer_centralizer_eq_of_even hM hN hchar hev
    have hmaxN : CFSG.IsMaximalTwoLocal (Subgroup.normalizer (C : Set G)) := by
      rw [hNC]
      exact hM
    have hF : Subgroup.normalizer (C : Set G) ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (C : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer (C : Set G)) := by
      rw [hNC]
      exact hchar M hM.1
    have hTE : TightlyEmbedded C := by
      rw [hC]
      exact tightlyEmbedded_centralizer_of_even hM hN huniq hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨R⟩ : Nonempty (Sylow 2 C) := inferInstance
    rcases hSTT G hK hs hnonab C hTE hmaxN hF R with h1 | h2 | h3 | h4 | h5 | h6
    ·
      have hRO : (R : Subgroup C).map C.subtype = pCoreOf 2 C := h1.1
      have hab := h1.2.1
      obtain ⟨g, hgM, hgne⟩ := h1.2.2
      right
      right
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hRne : (R : Subgroup C) ≠ ⊥ := R.ne_bot_of_dvd_card (even_iff_two_dvd.mp hev)
        intro hO
        apply hRne
        exact (Subgroup.map_eq_bot_iff_of_injective (R : Subgroup C)
          C.subtype_injective).mp (by rw [hRO, hO])
      · intro P hP hPC
        exact le_pCoreOf_of_isPGroup_le_of_sylow R hRO hP hPC
      · rcases hab with ⟨hcyc, hcard⟩ | hel
        · left
          exact ⟨by rwa [← hRO], by rwa [← hRO]⟩
        · right
          rwa [← hRO]
      · refine ⟨g, ?_, ?_⟩
        · rw [← hRO, ← hNC]
          exact hgM
        · rw [← hRO]
          exact hgne
    ·
      exfalso
      have h4 := CFSG.GF2Type.Aschbacher1976Common.card_le_four_of_dihedral_or_semidihedral
        h2.2 hE
      omega
    ·
      exact Or.inl (inCatalog_of_quaternion_outcome h3.2)
    ·
      exact Or.inl (CFSG.Assembly.LowTwoRank.inCatalog_of_classicalModel G .PSL 3 2 2 h4.2)
    ·
      exact Or.inl <| by
        rcases h5 with ⟨s, _, _, hsz⟩ | ⟨s, _, hpsu⟩
        · exact CFSG.TauCetiBridge.suzukiModel_inCatalog
            (CFSG.RankThree.GF2n.suzukiModel_of_lieModel hsz)
        · exact CFSG.Assembly.LowTwoRank.inCatalog_of_classicalModel G .PSU 3 2 s hpsu
    ·
      have hRO : (R : Subgroup C).map C.subtype = pCoreOf 2 C := h6.1
      have hW := h6.2.1
      have h4 := h6.2.2.1
      have hTI := h6.2.2.2.1
      have hNrm := h6.2.2.2.2.1
      have hwc := h6.2.2.2.2.2
      refine Or.inl (inCatalog_of_isTI_of_weaklyClosedIn (W := pCoreOf 2 C)
        hNode hs hnonab ?_ ?_ ?_ ?_)
      · simpa [← hRO] using hW
      · have hW4 : 4 ≤ Nat.card ↥(pCoreOf 2 C) := by simpa [← hRO] using h4
        intro hbot
        rw [hbot, Subgroup.card_bot] at hW4
        omega
      · simpa [← hRO] using hTI
      · have hNrmM : Subgroup.normalizer (pCoreOf 2 C : Set G) = M := by
          rw [← hRO]
          exact hNrm.trans hNC
        rw [hNrmM]
        have h := hwc
        rw [hNC, hRO] at h
        exact h
  ·
    have hOdd : Odd (Nat.card ↥C) := Nat.not_even_iff_odd.1 hev
    have hO2bot : pCoreOf 2 C = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun w hw => ?_
      obtain ⟨j, hj⟩ := isPGroup_pCoreOf' C ⟨w, hw⟩
      exact eq_one_of_odd_card hOdd (pCoreOf_le_self C hw) (j := j)
        (by simpa using congrArg Subtype.val hj)
    right
    left
    have hCbot : C = ⊥ :=
      centralizer_eq_bot_of_pCoreOf_eq_bot hM hN hchar (by simpa [hC] using hO2bot)
    simpa [hC] using hCbot

end CFSG.CGT.Hall82
