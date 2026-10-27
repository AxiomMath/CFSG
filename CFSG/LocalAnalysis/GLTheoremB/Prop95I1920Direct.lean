module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Inter
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Main

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18 (le_pCoreOf_of_normal coprime_normal_criterion)
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
open CFSG.LieType.ChevTwo (Chev2KDOut Chev2CoreCent)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

section Direct

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

theorem conclusions_of_bound (hK : IsComponentOf K ⊤) {S : Subgroup X}
    (Sig : Subgroup (MulAut (Kbar K))) (h2 : IsPGroup 2 Sig) (hinn : Sig ⊓ Kinn K = ⊥)
    (hS : ∀ s ∈ S, ∃ hsN : s ∈ Subgroup.normalizer (K : Set X), rhoK K ⟨s, hsN⟩ ∈ Sig) :
    IsPGroup 2 (inducedAutGroup S K) ∧ S ≤ Subgroup.normalizer (K : Set X) ∧
      NoInnerInduced S K := by
  have hq_inj := quotAutOfCentreHom_injective hK
  have hmapA : (inducedAutGroup S K).map quotAutOfCentreHom ≤ Sig := by
    intro ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.1 hψ
    obtain ⟨w, hw, hwS, rfl⟩ := mem_inducedAutGroup.1 hφ
    obtain ⟨hwN, hmem⟩ := hS w hwS
    exact hmem
  refine ⟨?_, fun s hs => (hS s hs).1, ?_⟩
  · have hA2 : IsPGroup 2 ((inducedAutGroup S K).map quotAutOfCentreHom) := h2.to_le hmapA
    have := hA2.comap_of_injective quotAutOfCentreHom hq_inj
    rwa [Subgroup.comap_map_eq_self_of_injective hq_inj] at this
  · unfold NoInnerInduced
    rw [eq_bot_iff]
    intro φ hφ
    rw [Subgroup.mem_bot]
    obtain ⟨hφA, hφI⟩ := Subgroup.mem_inf.1 hφ
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.1 hφI
    have hSig : quotAutOfCentreHom φ ∈ Sig := hmapA (Subgroup.mem_map_of_mem _ hφA)
    have hKin : quotAutOfCentreHom φ ∈ Kinn K :=
      ⟨QuotientGroup.mk k, by rw [← hk, quotAutOfCentreHom_conj]⟩
    have h1 : quotAutOfCentreHom φ = 1 := by
      have := Subgroup.mem_inf.2 ⟨hSig, hKin⟩
      rw [hinn] at this
      exact Subgroup.mem_bot.1 this
    exact hq_inj (h1.trans (map_one _).symm)

theorem commutator_mem_ker (hKD : Chev2KDOut) (hCore : Chev2CoreCent) (hK : IsComponentOf K ⊤)
    (hCh : IsChevTwo (Kbar K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (D1 : Subgroup ↥(Subgroup.normalizer (K : Set X))) (hD1 : IsPGroup p D1)
    (S : Subgroup ↥(Subgroup.normalizer (K : Set X))) (hS2 : IsPGroup 2 S)
    (hSD : D1 ≤ Subgroup.normalizer (S : Set ↥(Subgroup.normalizer (K : Set X))))
    (d : ↥(Subgroup.normalizer (K : Set X))) (hdp : d ^ p = 1)
    (hST : S ≤ pCoreOf 2 (Subgroup.centralizer ({d} : Set ↥(Subgroup.normalizer (K : Set X))))) :
    ∀ s ∈ S, ∀ e ∈ D1, rhoK K ⁅s, e⁆ = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (Kbar K) := hK.2.2.2
  intro s hs e he
  have hPT : D1.map (rhoK K) ≤ Subgroup.normalizer ((S.map (rhoK K) : Subgroup (MulAut (Kbar K))) :
      Set (MulAut (Kbar K))) :=
    le_trans (Subgroup.map_mono hSD) (Subgroup.le_normalizer_map _)
  have hcomm := hKD (Kbar K) inferInstance (isQuasisimple_of_comp hK).2.2 hCh p hp hp2 _ _
    (hD1.map _) (hS2.map _) hPT
  have h1 : ⁅rhoK K s, rhoK K e⁆ ∈ ⁅S.map (rhoK K), D1.map (rhoK K)⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ hs) (Subgroup.mem_map_of_mem _ he)
  have hinn : rhoK K ⁅s, e⁆ ∈ Kinn K := by
    rw [map_commutatorElement]
    exact hcomm h1
  have hyS : ⁅s, e⁆ ∈ S := by
    have h2 := (Subgroup.mem_normalizer_iff.1 (hSD he) s⁻¹).1 (Subgroup.inv_mem _ hs)
    have h3 : ⁅s, e⁆ = s * (e * s⁻¹ * e⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h3]
    exact Subgroup.mul_mem _ hs h2
  have hE : IsPGroup p (Subgroup.zpowers d) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hdp)
  have hCB : Subgroup.centralizer ((Subgroup.zpowers d : Subgroup _) : Set _) =
      Subgroup.centralizer ({d} : Set _) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  refine rho_pCore_inner_eq_one hCore hK hCh hp hp2 (Subgroup.zpowers d) hE ?_ hinn
  rw [hCB]
  exact hST hyS

theorem isPGroup_subgroupOf_of_exponent {p : ℕ} {D : Subgroup X} (hDp : ∀ x ∈ D, x ^ p = 1) :
    IsPGroup p (D.subgroupOf (Subgroup.normalizer (K : Set X))) := fun x =>
  ⟨1, Subtype.ext (Subtype.ext (by
    simpa using hDp (((x : ↥(Subgroup.normalizer (K : Set X))) : X)) (Subgroup.mem_subgroupOf.1 x.2)))⟩

theorem exists_centralizing_rho_eq (hKD : Chev2KDOut) (hCore : Chev2CoreCent)
    (hK : IsComponentOf K ⊤) (hCh : IsChevTwo (Kbar K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (D1 : Subgroup ↥(Subgroup.normalizer (K : Set X))) (hD1 : IsPGroup p D1)
    (S : Subgroup ↥(Subgroup.normalizer (K : Set X))) (hS2 : IsPGroup 2 S)
    (hSD : D1 ≤ Subgroup.normalizer (S : Set ↥(Subgroup.normalizer (K : Set X))))
    (d : ↥(Subgroup.normalizer (K : Set X))) (hdp : d ^ p = 1)
    (hST : S ≤ pCoreOf 2 (Subgroup.centralizer ({d} : Set ↥(Subgroup.normalizer (K : Set X))))) :
    ∀ s ∈ S, ∃ q ∈ S, q ∈ Subgroup.centralizer (D1 : Set ↥(Subgroup.normalizer (K : Set X))) ∧
      rhoK K s = rhoK K q := by
  have hcomm := commutator_mem_ker hKD hCore hK hCh hp hp2 D1 hD1 S hS2 hSD d hdp hST
  let N' : Subgroup ↥(Subgroup.normalizer (K : Set X)) :=
    ((S ⊓ Subgroup.centralizer (D1 : Set ↥(Subgroup.normalizer (K : Set X)))).map
      (rhoK K)).comap (rhoK K)
  have hSN' : S ≤ N' := by
    refine coprime_normal_criterion hp hp2 hD1 hS2 hSD ?_ ?_
    · intro d' hd' q hq
      have h1 : d'⁻¹ * (q * d' * q⁻¹) = ⁅d'⁻¹, q⁆ := by
        simp only [commutatorElement_def]; group
      rw [h1]
      refine Subgroup.mem_comap.2 ?_
      rw [hcomm d'⁻¹ (S.inv_mem hd') q hq]
      exact Subgroup.one_mem _
    · intro x hx hxc
      exact Subgroup.mem_comap.2 (Subgroup.mem_map_of_mem _
        ⟨hx, Subgroup.mem_centralizer_iff.2 hxc⟩)
  intro s hs
  obtain ⟨r, hr, hrρ⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hSN' hs))
  exact ⟨r, hr.1, hr.2, hrρ.symm⟩

theorem rho_Sd_le_Q (hKD : Chev2KDOut) (hCore : Chev2CoreCent) (hK : IsComponentOf K ⊤)
    (hCh : IsChevTwo (Kbar K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup X}
    {Sd : X → Subgroup X} (hfam : SignalizerFamily p D Sd)
    (hB1 : ∀ d ∈ D, d ≠ 1 →
      pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X)) :
    ∀ d ∈ D, d ≠ 1 → ∀ s ∈ Sd d, ∃ hsN : s ∈ Subgroup.normalizer (K : Set X),
      ∃ q ∈ pCoreOf 2 (Subgroup.centralizer
        ((D.subgroupOf (Subgroup.normalizer (K : Set X)) : Subgroup ↥(Subgroup.normalizer (K : Set X)))
          : Set ↥(Subgroup.normalizer (K : Set X)))), rhoK K ⟨s, hsN⟩ = rhoK K q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hDp : ∀ x ∈ D, x ^ p = 1 := hfam.elemAbelian.2
  intro d hd hd1 s hs
  have hsT : s ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) := hfam.le_pCore d hd hd1 hs
  have hsN : s ∈ Subgroup.normalizer (K : Set X) := hB1 d hd hd1 hsT
  refine ⟨hsN, ?_⟩
  by_cases hdN : d ∈ Subgroup.normalizer (K : Set X)
  · set dN : ↥(Subgroup.normalizer (K : Set X)) := ⟨d, hdN⟩ with hdNdef
    set D1 : Subgroup ↥(Subgroup.normalizer (K : Set X)) :=
      D.subgroupOf (Subgroup.normalizer (K : Set X)) with hD1def
    have hD1 : IsPGroup p D1 := isPGroup_subgroupOf_of_exponent hDp
    have hdD1 : dN ∈ D1 := Subgroup.mem_subgroupOf.2 hd
    have hdp : dN ^ p = 1 := Subtype.ext (by simpa using hDp d hd)
    set S : Subgroup ↥(Subgroup.normalizer (K : Set X)) :=
      (Sd d).subgroupOf (Subgroup.normalizer (K : Set X)) with hSdef
    have hS2 : IsPGroup 2 S :=
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.centralizer ({d} : Set X))).to_le
        (hfam.le_pCore d hd hd1)).comap_of_injective (Subgroup.normalizer (K : Set X)).subtype
        (Subgroup.normalizer (K : Set X)).subtype_injective
    have hSD : D1 ≤ Subgroup.normalizer (S : Set ↥(Subgroup.normalizer (K : Set X))) := by
      intro e he
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.1
        (hfam.inv_D d hd hd1 ((e : ↥(Subgroup.normalizer (K : Set X))) : X)
          (Subgroup.mem_subgroupOf.1 he)) ((x : ↥(Subgroup.normalizer (K : Set X))) : X)
      exact h1
    have hST : S ≤ pCoreOf 2 (Subgroup.centralizer ({dN} : Set ↥(Subgroup.normalizer (K : Set X)))) :=
      fun x hx => subgroupOf_pCoreOf_le hdN
        (show x ∈ (pCoreOf 2 (Subgroup.centralizer ({d} : Set X))).subgroupOf _ from
          Subgroup.mem_subgroupOf.2 (hfam.le_pCore d hd hd1 (Subgroup.mem_subgroupOf.1 hx)))
    let A : Subgroup ↥(Subgroup.normalizer (K : Set X)) :=
      pCoreOf 2 (Subgroup.centralizer ({dN} : Set ↥(Subgroup.normalizer (K : Set X)))) ⊓
        Subgroup.centralizer (D1 : Set ↥(Subgroup.normalizer (K : Set X)))
    have hAQ : A ≤ pCoreOf 2 (Subgroup.centralizer
        (D1 : Set ↥(Subgroup.normalizer (K : Set X)))) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
      intro c hc
      have hcd : c ∈ Subgroup.centralizer ({dN} : Set ↥(Subgroup.normalizer (K : Set X))) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.2 hdD1) hc
      have hcA := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
        (Subgroup.centralizer ({dN} : Set ↥(Subgroup.normalizer (K : Set X)))) hcd
      have hcC := Subgroup.le_normalizer
        (H := Subgroup.centralizer (D1 : Set ↥(Subgroup.normalizer (K : Set X)))) hc
      rw [Subgroup.mem_normalizer_iff] at hcA hcC ⊢
      intro h
      show h ∈ pCoreOf 2 _ ⊓ Subgroup.centralizer _ ↔ c * h * c⁻¹ ∈ pCoreOf 2 _ ⊓
        Subgroup.centralizer _
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      exact and_congr (hcA h) (hcC h)
    have hmem : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (K : Set X))) ∈ S := Subgroup.mem_subgroupOf.2 hs
    obtain ⟨r, hr, hrC, hrρ⟩ := exists_centralizing_rho_eq hKD hCore hK hCh hp hp2 D1 hD1 S hS2 hSD
      dN hdp hST _ hmem
    exact ⟨r, hAQ ⟨hST hr, hrC⟩, hrρ⟩
  · have hsC : s ∈ Subgroup.centralizer (K : Set X) :=
      le_centralizer_of_not_mem_normalizer' hp hK (hDp d hd) hdN (hB1 d hd hd1) le_rfl hsT
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [map_one]
    exact (rhoK_eq_one_iff hK hsN).2 hsC

@[expose] noncomputable def SigQ (K : Subgroup X) (D : Subgroup X) : Subgroup (MulAut (Kbar K)) :=
  (pCoreOf 2 (Subgroup.centralizer
    ((D.subgroupOf (Subgroup.normalizer (K : Set X)) : Subgroup ↥(Subgroup.normalizer (K : Set X)))
      : Set ↥(Subgroup.normalizer (K : Set X))))).map (rhoK K)

theorem isPGroup_SigQ (K : Subgroup X) (D : Subgroup X) : IsPGroup 2 (SigQ K D) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).map _

theorem SigQ_inf_Kinn (hCore : Chev2CoreCent) (hK : IsComponentOf K ⊤)
    (hCh : IsChevTwo (Kbar K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup X}
    (hDp : ∀ x ∈ D, x ^ p = 1) : SigQ K D ⊓ Kinn K = ⊥ := by
  have hD1 : IsPGroup p (D.subgroupOf (Subgroup.normalizer (K : Set X))) :=
    isPGroup_subgroupOf_of_exponent hDp
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxS, hxI⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hxS
  exact Subgroup.mem_bot.2 (rho_pCore_inner_eq_one hCore hK hCh hp hp2 _ hD1 hq hxI)

theorem rho_sigma_mem_SigQ (hKD : Chev2KDOut) (hCore : Chev2CoreCent) (hK : IsComponentOf K ⊤)
    (hCh : IsChevTwo (Kbar K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup X}
    {Sd : X → Subgroup X} (hfam : SignalizerFamily p D Sd)
    (hB1 : ∀ d ∈ D, d ≠ 1 →
      pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X)) :
    ∀ s ∈ sigmaFam D Sd, ∃ hsN : s ∈ Subgroup.normalizer (K : Set X),
      rhoK K ⟨s, hsN⟩ ∈ SigQ K D := by
  have hle : sigmaFam D Sd ≤ ((SigQ K D).comap (rhoK K)).map
      (Subgroup.normalizer (K : Set X)).subtype := by
    unfold sigmaFam
    refine iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => ?_
    intro s hs
    obtain ⟨hsN, q, hq, hρ⟩ := rho_Sd_le_Q hKD hCore hK hCh hp hp2 hfam hB1 d hd hd1 s hs
    refine ⟨⟨s, hsN⟩, Subgroup.mem_comap.2 ?_, rfl⟩
    rw [hρ]
    exact Subgroup.mem_map_of_mem _ hq
  intro s hs
  obtain ⟨n, hn, rfl⟩ := hle hs
  exact ⟨n.2, hn⟩

theorem input19_20_2_direct (hKD : Chev2KDOut) (hCore : Chev2CoreCent) (hB : PNormalizesLarge) :
    Input19_20_2 := by
  intro X _ _ p hp hp2 K hK hCh D Sd hfam
  have hB1 := pCoreOf_le_normalizer_of_family hB hp hp2 hK hCh hfam
  exact conclusions_of_bound hK (SigQ K D) (isPGroup_SigQ K D)
    (SigQ_inf_Kinn hCore hK hCh hp hp2 hfam.elemAbelian.2)
    (rho_sigma_mem_SigQ hKD hCore hK hCh hp hp2 hfam hB1)

end Direct

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920
