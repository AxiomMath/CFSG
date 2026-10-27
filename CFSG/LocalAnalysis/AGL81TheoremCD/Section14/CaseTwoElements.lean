module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoPerm
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenThirteenSylow
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma caseTwo_twoSet_aut {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (hKF : KFactA11GammaTwoSet) :
    ∃ f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11),
      ((((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))).map f.toMonoidHom) =
        a11TwoSetStab 9 10 := by
  obtain ⟨e, i, j, hij, heq⟩ := h.exists_twoSet h2 hK hU hL hKF
  obtain ⟨c, hc⟩ := exists_mulAut_map_a11TwoSetStab hij
  refine ⟨e.trans c, ?_⟩
  have hcomp : (e.trans c).toMonoidHom = c.toMonoidHom.comp e.toMonoidHom := rfl
  rw [hcomp, ← Subgroup.map_map, heq]
  exact hc

private lemma caseTwo_quotient_sylow {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hU : NineNineOneAt M)
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    (hf : ((((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))).map f.toMonoidHom) =
        a11TwoSetStab 9 10) :
    ∃ T : Sylow 3 (alternatingGroup (Fin 11)),
      (T : Subgroup (alternatingGroup (Fin 11))) ≤ a11TwoSetStab 9 10 ∧
      (T : Subgroup (alternatingGroup (Fin 11))) =
        ((Q.subgroupOf (kSub 3 M H)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))).map f.toMonoidHom := by
  classical
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* threeStar K := QuotientGroup.mk' O
  have hKsub : K = kSub 3 M H := rfl
  have hQK : Q ≤ K := by
    have hsup : K ⊔ E = K := sup_eq_left.mpr (h.E_le_kSub h2)
    calc Q ≤ K ⊔ E := h.sylow.le
      _ = K := hsup
  obtain ⟨S0, hS0⟩ := (h.isSylowOf_kSub h2).exists_sylow_eq_subgroupOf
  let S : Sylow 3 (threeStar K) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective O) S0
  have hS : (S : Subgroup (threeStar K)) = (Q.subgroupOf K).map π := by
    dsimp only [S]
    rw [Sylow.coe_mapSurjective, hS0]
  have hsurj : Function.Surjective ⇑f.toMonoidHom := by
    simpa only [MulEquiv.coe_toMonoidHom] using f.surjective
  let T : Sylow 3 (alternatingGroup (Fin 11)) :=
    Sylow.mapSurjective (f := f.toMonoidHom) hsurj S
  have hT : (T : Subgroup (alternatingGroup (Fin 11))) =
      ((Q.subgroupOf K).map π).map f.toMonoidHom := by
    dsimp only [T]
    rw [Sylow.coe_mapSurjective, hS]
  refine ⟨T, ?_, hT⟩
  · rw [hT]
    have hQ0le : Q.subgroupOf K ≤ (K ⊓ M).subgroupOf K := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr
        ⟨x.2, h.Q_le_M hU (Subgroup.mem_subgroupOf.mp hx)⟩
    have hmaple : ((Q.subgroupOf K).map π).map f.toMonoidHom ≤
        (((K ⊓ M).subgroupOf K).map π).map f.toMonoidHom :=
      Subgroup.map_mono (f := f.toMonoidHom) (Subgroup.map_mono (f := π) hQ0le)
    rw [hf] at hmaple
    exact hmaple

private lemma cube_eq_one_of_injective {K : Subgroup G}
    {Q₀ : Subgroup ↥K} {ψ : ↥Q₀ →* alternatingGroup (Fin 11)}
    (hψinj : Function.Injective ψ) {x : ↥Q₀} (hx : ψ x ^ 3 = 1) :
    ((x : ↥K) : G) ^ 3 = 1 := by
  have hcubeQ : x ^ 3 = 1 := hψinj (by rwa [map_pow, hx, map_one])
  have hcube : (x : ↥K) ^ 3 = 1 := by
    simpa using congrArg (fun z : ↥Q₀ => (z : ↥K)) hcubeQ
  simpa using congrArg (fun z : ↥K => (z : G)) hcube

private lemma caseTwo_lift_props {K : Subgroup G}
    {Q₀ : Subgroup ↥K} {ψ : ↥Q₀ →* alternatingGroup (Fin 11)}
    (hψinj : Function.Injective ψ)
    {s₁ s₂ : alternatingGroup (Fin 11)} {x₁ x₂ : ↥Q₀}
    (hx1 : ψ x₁ = s₁) (hx2 : ψ x₂ = s₂)
    (hs1cube : s₁ ^ 3 = 1) (hs2cube : s₂ ^ 3 = 1) (hs1ne : s₁ ≠ 1)
    (hs12 : Commute s₁ s₂) (hs2notz : s₂ ∉ Subgroup.zpowers s₁) :
    ((x₁ : ↥K) : G) ^ 3 = 1 ∧ ((x₂ : ↥K) : G) ^ 3 = 1 ∧
      ((x₁ : ↥K) : G) ≠ 1 ∧
      Commute ((x₁ : ↥K) : G) ((x₂ : ↥K) : G) ∧
      ((x₂ : ↥K) : G) ∉ Subgroup.zpowers ((x₁ : ↥K) : G) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact cube_eq_one_of_injective hψinj (by rw [hx1, hs1cube])
  · exact cube_eq_one_of_injective hψinj (by rw [hx2, hs2cube])
  · intro h1
    have hx1K : (x₁ : ↥K) = 1 := Subtype.ext h1
    exact hs1ne (by simpa [show x₁ = 1 from Subtype.ext hx1K] using hx1.symm)
  · have hcommQ : Commute x₁ x₂ := hψinj (by rw [map_mul, map_mul, hx1, hx2, hs12.eq])
    exact congrArg (fun z : ↥Q₀ => ((z : ↥K) : G)) hcommQ.eq
  · intro hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hpowK : (x₁ : ↥K) ^ n = (x₂ : ↥K) := by
      apply Subtype.ext
      simpa [Subgroup.coe_zpow] using hn
    have hpowQ : x₁ ^ n = x₂ := Subtype.ext hpowK
    have hs : s₁ ^ n = s₂ := by
      calc s₁ ^ n = (ψ x₁) ^ n := by rw [hx1]
        _ = ψ (x₁ ^ n) := (map_zpow ψ x₁ n).symm
        _ = ψ x₂ := by rw [hpowQ]
        _ = s₂ := hx2
    exact hs2notz (Subgroup.mem_zpowers_iff.mpr ⟨n, hs⟩)

private lemma caseTwo_lift_perms {M H Q : Subgroup G} (hQp : IsPGroup 3 Q)
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    (T : Sylow 3 (alternatingGroup (Fin 11)))
    (hT : (T : Subgroup (alternatingGroup (Fin 11))) =
      ((Q.subgroupOf (kSub 3 M H)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))).map f.toMonoidHom)
    {s₁ s₂ : alternatingGroup (Fin 11)}
    (hs1T : s₁ ∈ (T : Subgroup (alternatingGroup (Fin 11))))
    (hs2T : s₂ ∈ (T : Subgroup (alternatingGroup (Fin 11))))
    (hs1cube : s₁ ^ 3 = 1) (hs2cube : s₂ ^ 3 = 1) (hs1ne : s₁ ≠ 1)
    (hs12 : Commute s₁ s₂) (hs2notz : s₂ ∉ Subgroup.zpowers s₁) :
    ∃ u₁ u₂ : ↥(kSub 3 M H),
      u₁ ∈ Q.subgroupOf (kSub 3 M H) ∧ u₂ ∈ Q.subgroupOf (kSub 3 M H) ∧
      f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) u₁) = s₁ ∧
      f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) u₂) = s₂ ∧
      ((u₁ : G) ^ 3 = 1) ∧ ((u₂ : G) ^ 3 = 1) ∧ (u₁ : G) ≠ 1 ∧
      Commute (u₁ : G) (u₂ : G) ∧ (u₂ : G) ∉ Subgroup.zpowers (u₁ : G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* threeStar K := QuotientGroup.mk' O
  let Q₀ : Subgroup ↥K := Q.subgroupOf K
  let ψ : ↥Q₀ →* alternatingGroup (Fin 11) :=
    f.toMonoidHom.comp (π.comp Q₀.subtype)
  have hfinj : Function.Injective ⇑f.toMonoidHom := by
    simpa only [MulEquiv.coe_toMonoidHom] using f.injective
  have hπinj : Function.Injective ⇑(π.comp Q₀.subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype
      (p := 3) (N := O)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card)
      (hQp.comap_subtype (K := K))
  have hψinj : Function.Injective ψ := hfinj.comp hπinj
  have hψmap : Q₀.map (f.toMonoidHom.comp π) = (T : Subgroup (alternatingGroup (Fin 11))) := by
    rw [← Subgroup.map_map]
    exact hT.symm
  obtain ⟨y₁, hy1Q, hy1⟩ := Subgroup.mem_map.mp (by rw [hψmap]; exact hs1T)
  obtain ⟨y₂, hy2Q, hy2⟩ := Subgroup.mem_map.mp (by rw [hψmap]; exact hs2T)
  let x₁ : ↥Q₀ := ⟨y₁, hy1Q⟩
  let x₂ : ↥Q₀ := ⟨y₂, hy2Q⟩
  have hx1 : ψ x₁ = s₁ := hy1
  have hx2 : ψ x₂ = s₂ := hy2
  obtain ⟨hc1, hc2, hn1, hcomm, hz⟩ :=
    caseTwo_lift_props hψinj hx1 hx2 hs1cube hs2cube hs1ne hs12 hs2notz
  exact ⟨y₁, y₂, hy1Q, hy2Q, hy1, hy2, hc1, hc2, hn1, hcomm, hz⟩

private lemma caseTwo_U0_eq_closure {M H : Subgroup G}
    {u₁ u₂ : ↥(kSub 3 M H)} :
    let K : Subgroup G := kSub 3 M H
    let U : Subgroup G := Subgroup.closure ({(u₁ : G), (u₂ : G)} : Set G)
    U.subgroupOf K = Subgroup.closure ({u₁, u₂} : Set ↥K) := by
  classical
  let K : Subgroup G := kSub 3 M H
  let U : Subgroup G := Subgroup.closure ({(u₁ : G), (u₂ : G)} : Set G)
  have hUK : U ≤ K := by
    refine (Subgroup.closure_le K).mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact u₁.2
    · exact u₂.2
  have himg : K.subtype '' ({u₁, u₂} : Set ↥K) = ({(u₁ : G), (u₂ : G)} : Set G) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl <;> simp
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨u₁, by simp, rfl⟩
      · exact ⟨u₂, by simp, rfl⟩
  apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hUK, MonoidHom.map_closure, himg]

private lemma caseTwo_U0_map_centralizer {M H Q : Subgroup G} (hQp : IsPGroup 3 Q)
    {u₁ u₂ : ↥(kSub 3 M H)}
    (hu1Q : u₁ ∈ Q.subgroupOf (kSub 3 M H))
    (hu2Q : u₂ ∈ Q.subgroupOf (kSub 3 M H)) :
    let K : Subgroup G := kSub 3 M H
    let U : Subgroup G := Subgroup.closure ({(u₁ : G), (u₂ : G)} : Set G)
    let U₀ : Subgroup ↥K := U.subgroupOf K
    let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
    let π : ↥K →* threeStar K := QuotientGroup.mk' O
    U ≤ K ∧
      U₀.map π = Subgroup.closure ({π u₁, π u₂} : Set (threeStar K)) ∧
      Subgroup.centralizer ((U₀.map π : Subgroup (threeStar K)) : Set (threeStar K)) =
        (Subgroup.centralizer (U₀ : Set ↥K)).map π := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* threeStar K := QuotientGroup.mk' O
  let U : Subgroup G := Subgroup.closure ({(u₁ : G), (u₂ : G)} : Set G)
  let U₀ : Subgroup ↥K := U.subgroupOf K
  have hu1Q' : (u₁ : G) ∈ Q := Subgroup.mem_subgroupOf.mp hu1Q
  have hu2Q' : (u₂ : G) ∈ Q := Subgroup.mem_subgroupOf.mp hu2Q
  have hUK : U ≤ K := by
    refine (Subgroup.closure_le K).mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact u₁.2
    · exact u₂.2
  have hUQ : U ≤ Q := by
    refine (Subgroup.closure_le Q).mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact hu1Q'
    · exact hu2Q'
  have hU0Q0 : U₀ ≤ Q.subgroupOf K := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hUQ (Subgroup.mem_subgroupOf.mp hx))
  have hU0p : IsPGroup 3 U₀ := (hQp.comap_subtype (K := K)).to_le hU0Q0
  have hU0eq : U₀ = Subgroup.closure ({u₁, u₂} : Set ↥K) :=
    caseTwo_U0_eq_closure
  have hU0map : U₀.map π = Subgroup.closure ({π u₁, π u₂} : Set (threeStar K)) := by
    rw [hU0eq, MonoidHom.map_closure]
    congr 1
    ext z
    simp
  have hN : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hcent : Subgroup.centralizer ((U₀.map π : Subgroup (threeStar K)) :
      Set (threeStar K)) = (Subgroup.centralizer (U₀ : Set ↥K)).map π :=
    CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 3) (N := O) hN hU0p
  exact ⟨hUK, hU0map, hcent⟩

private lemma caseTwo_centralizer_range_le {M H : Subgroup G}
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    {s₁ s₂ : alternatingGroup (Fin 11)}
    {u₁ u₂ : ↥(kSub 3 M H)}
    (hu1 : f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) u₁) = s₁)
    (hu2 : f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) u₂) = s₂) :
    let U : Subgroup G := Subgroup.closure ({(u₁ : G), (u₂ : G)} : Set G)
    let D : Subgroup G := kSub 3 M H ⊓ Subgroup.centralizer (U : Set G)
    let φ : ↥D →* alternatingGroup (Fin 11) :=
      f.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H))).comp
        (Subgroup.inclusion (inf_le_left : D ≤ kSub 3 M H)))
    φ.range ≤ Subgroup.centralizer ({s₁, s₂} : Set (alternatingGroup (Fin 11))) := by
  classical
  let K : Subgroup G := kSub 3 M H
  let π : ↥K →* threeStar K := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)
  let U : Subgroup G := Subgroup.closure ({(u₁ : G), (u₂ : G)} : Set G)
  let D : Subgroup G := K ⊓ Subgroup.centralizer (U : Set G)
  dsimp only
  intro z hz
  obtain ⟨d, rfl⟩ := hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hdK : (d : G) ∈ K := d.2.1
  have hdcent : (d : G) ∈ Subgroup.centralizer (U : Set G) := d.2.2
  have hu1U : (u₁ : G) ∈ U := Subgroup.subset_closure (by simp)
  have hu2U : (u₂ : G) ∈ U := Subgroup.subset_closure (by simp)
  have hc1 : Commute (d : G) (u₁ : G) :=
    (Subgroup.mem_centralizer_iff.mp hdcent (u₁ : G) hu1U).symm
  have hc2 : Commute (d : G) (u₂ : G) :=
    (Subgroup.mem_centralizer_iff.mp hdcent (u₂ : G) hu2U).symm
  have hc1K : Commute (⟨(d : G), hdK⟩ : ↥K) u₁ := Subtype.ext hc1.eq
  have hc2K : Commute (⟨(d : G), hdK⟩ : ↥K) u₂ := Subtype.ext hc2.eq
  have hc1A : Commute (f (π ⟨(d : G), hdK⟩)) s₁ := by
    rw [← hu1]
    exact (hc1K.map π).map f.toMonoidHom
  have hc2A : Commute (f (π ⟨(d : G), hdK⟩)) s₂ := by
    rw [← hu2]
    exact (hc2K.map π).map f.toMonoidHom
  rcases hw with rfl | rfl
  · exact hc1A.symm
  · exact hc2A.symm

private lemma caseTwo_centralizer_range_ge {M H Q : Subgroup G} (hQp : IsPGroup 3 Q)
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    {s₁ s₂ : alternatingGroup (Fin 11)}
    {u₁ u₂ : ↥(kSub 3 M H)}
    (hu1Q : u₁ ∈ Q.subgroupOf (kSub 3 M H))
    (hu2Q : u₂ ∈ Q.subgroupOf (kSub 3 M H))
    (hu1 : f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) u₁) = s₁)
    (hu2 : f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) u₂) = s₂) :
    let U : Subgroup G := Subgroup.closure ({(u₁ : G), (u₂ : G)} : Set G)
    let D : Subgroup G := kSub 3 M H ⊓ Subgroup.centralizer (U : Set G)
    let φ : ↥D →* alternatingGroup (Fin 11) :=
      f.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H))).comp
        (Subgroup.inclusion (inf_le_left : D ≤ kSub 3 M H)))
    Subgroup.centralizer ({s₁, s₂} : Set (alternatingGroup (Fin 11))) ≤ φ.range := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* threeStar K := QuotientGroup.mk' O
  let U : Subgroup G := Subgroup.closure ({(u₁ : G), (u₂ : G)} : Set G)
  let U₀ : Subgroup ↥K := U.subgroupOf K
  let D : Subgroup G := K ⊓ Subgroup.centralizer (U : Set G)
  have hdata := caseTwo_U0_map_centralizer hQp hu1Q hu2Q
  dsimp only at hdata
  obtain ⟨hUK, hU0map, hcent⟩ := hdata
  dsimp only
  intro z hz
  let t' : threeStar K := f.symm z
  have ht'U : t' ∈ Subgroup.centralizer ((U₀.map π : Subgroup (threeStar K)) :
      Set (threeStar K)) := by
    rw [hU0map, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hw with rfl | rfl
    · have hz1 : s₁ * z = z * s₁ :=
        Subgroup.mem_centralizer_iff.mp hz s₁ (by simp)
      have hs1symm : f.symm s₁ = π u₁ := by
        rw [← hu1, MulEquiv.symm_apply_apply]
      change π u₁ * f.symm z = f.symm z * π u₁
      simpa [t', hs1symm] using congrArg f.symm hz1
    · have hz2 : s₂ * z = z * s₂ :=
        Subgroup.mem_centralizer_iff.mp hz s₂ (by simp)
      have hs2symm : f.symm s₂ = π u₂ := by
        rw [← hu2, MulEquiv.symm_apply_apply]
      change π u₂ * f.symm z = f.symm z * π u₂
      simpa [t', hs2symm] using congrArg f.symm hz2
  rw [hcent] at ht'U
  obtain ⟨y, hycent, hyπ⟩ := Subgroup.mem_map.mp ht'U
  have hycentU : (y : G) ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u huU
    have hcomm : Commute (⟨u, hUK huU⟩ : ↥K) y :=
      Subgroup.mem_centralizer_iff.mp hycent ⟨u, hUK huU⟩
        (Subgroup.mem_subgroupOf.mpr huU)
    exact congrArg (fun q : ↥K => (q : G)) hcomm.eq
  have hyD : (y : G) ∈ D := ⟨y.2, hycentU⟩
  refine ⟨⟨(y : G), hyD⟩, ?_⟩
  change f (π y) = z
  rw [hyπ]
  exact f.apply_symm_apply z

private lemma caseTwo_centralizer_range {M H Q : Subgroup G} (hQp : IsPGroup 3 Q)
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    {s₁ s₂ : alternatingGroup (Fin 11)}
    {u₁ u₂ : ↥(kSub 3 M H)}
    (hu1Q : u₁ ∈ Q.subgroupOf (kSub 3 M H))
    (hu2Q : u₂ ∈ Q.subgroupOf (kSub 3 M H))
    (hu1 : f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) u₁) = s₁)
    (hu2 : f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) u₂) = s₂) :
    let U : Subgroup G := Subgroup.closure ({(u₁ : G), (u₂ : G)} : Set G)
    let D : Subgroup G := kSub 3 M H ⊓ Subgroup.centralizer (U : Set G)
    let φ : ↥D →* alternatingGroup (Fin 11) :=
      f.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H))).comp
        (Subgroup.inclusion (inf_le_left : D ≤ kSub 3 M H)))
    φ.range = Subgroup.centralizer ({s₁, s₂} : Set (alternatingGroup (Fin 11))) := by
  apply le_antisymm
  · exact caseTwo_centralizer_range_le f hu1 hu2
  · exact caseTwo_centralizer_range_ge hQp f hu1Q hu2Q hu1 hu2

private lemma caseTwo_not_isPSolvable {M H Q : Subgroup G} (hQp : IsPGroup 3 Q)
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    {s₁ s₂ : alternatingGroup (Fin 11)}
    {u₁ u₂ : ↥(kSub 3 M H)}
    (hu1Q : u₁ ∈ Q.subgroupOf (kSub 3 M H))
    (hu2Q : u₂ ∈ Q.subgroupOf (kSub 3 M H))
    (hu1 : f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) u₁) = s₁)
    (hu2 : f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) u₂) = s₂)
    (hnotC : ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(Subgroup.centralizer ({s₁, s₂} : Set (alternatingGroup (Fin 11))))) :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(kSub 3 M H ⊓ Subgroup.centralizer
        (Subgroup.closure ({(u₁ : G), (u₂ : G)} : Set G) : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* threeStar K := QuotientGroup.mk' O
  let U : Subgroup G := Subgroup.closure ({(u₁ : G), (u₂ : G)} : Set G)
  let D : Subgroup G := K ⊓ Subgroup.centralizer (U : Set G)
  have hDK : D ≤ K := inf_le_left
  let φ : ↥D →* alternatingGroup (Fin 11) :=
    f.toMonoidHom.comp (π.comp (Subgroup.inclusion hDK))
  have hrange : φ.range = Subgroup.centralizer ({s₁, s₂} :
      Set (alternatingGroup (Fin 11))) := by
    have h := caseTwo_centralizer_range hQp f hu1Q hu2Q hu1 hu2
    simpa only [K, O, π, U, D, φ] using h
  intro hsolv
  have hsolvD : CFSG.HallHigman.IsPSolvable 3 ↥D := by
    simpa [D] using hsolv
  have htop : CFSG.HallHigman.IsPSolvable 3 ↥(⊤ : Subgroup ↥D) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.topEquiv).symm hsolvD
  have hmap := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
    (p := 3) φ (N := ⊤) htop
  have hmap' : CFSG.HallHigman.IsPSolvable 3 ↥φ.range := by
    rw [MonoidHom.range_eq_map]
    exact hmap
  rw [hrange] at hmap'
  exact hnotC hmap'

private lemma caseTwo_lift_centralizer {M H Q : Subgroup G} (hQp : IsPGroup 3 Q)
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    {u₁ : ↥(kSub 3 M H)} {s₁ t : alternatingGroup (Fin 11)}
    (hu1Q : u₁ ∈ Q.subgroupOf (kSub 3 M H))
    (hu1 : f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) u₁) = s₁)
    (htord : orderOf t = 5) (hcomm : Commute s₁ t) :
    ∃ y₁ : ↥(kSub 3 M H),
      y₁ ∈ Subgroup.centralizer (Subgroup.zpowers u₁ : Set ↥(kSub 3 M H)) ∧
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) y₁ = f.symm t := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* threeStar K := QuotientGroup.mk' O
  let t' : threeStar K := f.symm t
  have hN : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have ht'ord : orderOf t' = 5 := by
    rw [show t' = f.symm t from rfl, MulEquiv.orderOf_eq, htord]
  have hcomm' : Commute (π u₁) t' := by
    have h' := hcomm.map f.symm.toMonoidHom
    have hs1symm : f.symm s₁ = π u₁ := by rw [← hu1, MulEquiv.symm_apply_apply]
    simpa [t', hs1symm] using h'
  have hzp : IsPGroup 3 (Subgroup.zpowers u₁) :=
    (hQp.comap_subtype (K := K)).to_le (Subgroup.zpowers_le.mpr hu1Q)
  have hcent : Subgroup.centralizer (((Subgroup.zpowers u₁).map π :
      Subgroup (threeStar K)) : Set (threeStar K)) =
      (Subgroup.centralizer (Subgroup.zpowers u₁ : Set ↥K)).map π :=
    CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 3) (N := O) hN hzp
  have ht'cent : t' ∈ Subgroup.centralizer (Subgroup.zpowers (π u₁) :
      Set (threeStar K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (hcomm'.zpow_left n).eq
  rw [← MonoidHom.map_zpowers] at ht'cent
  rw [hcent] at ht'cent
  obtain ⟨y₁, hy1cent, hy1π⟩ := Subgroup.mem_map.mp ht'cent
  exact ⟨y₁, hy1cent, hy1π⟩

private lemma caseTwo_lift_mem_M {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hK : KNormalAt M)
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    (hf : ((((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))).map f.toMonoidHom) =
        a11TwoSetStab 9 10)
    {t : alternatingGroup (Fin 11)} (ht : t ∈ a11TwoSetStab 9 10)
    {y₁ : ↥(kSub 3 M H)}
    (hy1π : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) y₁ = f.symm t) :
    (y₁ : G) ∈ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* threeStar K := QuotientGroup.mk' O
  let t' : threeStar K := f.symm t
  have hy1π' : π y₁ = t' := by simpa [π, t'] using hy1π
  let P : Subgroup (threeStar K) :=
    (((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H))))
  have ht'P : t' ∈ P := by
    have htP : t ∈ P.map f.toMonoidHom := by rw [hf]; exact ht
    obtain ⟨x, hxP, hxft⟩ := Subgroup.mem_map.mp htP
    have hx : f.symm t = x := by
      rw [← hxft]
      simpa only [MulEquiv.coe_toMonoidHom] using f.symm_apply_apply x
    rw [show t' = f.symm t from rfl, hx]
    exact hxP
  obtain ⟨m, hmP, hmπ⟩ := Subgroup.mem_map.mp ht'P
  have hmπ' : π m = t' := hmπ
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hmP).2
  have hπker : π (y₁ * m⁻¹) = 1 := by
    rw [map_mul, map_inv, hy1π', hmπ', mul_inv_cancel]
  have hmemO : y₁ * m⁻¹ ∈ O := (QuotientGroup.eq_one_iff _).mp hπker
  have hOM : O.map K.subtype ≤ M := h.hypCGen.pPrimeCore_map_le hK
  have hmemM : ((y₁ * m⁻¹ : ↥K) : G) ∈ M :=
    hOM (Subgroup.mem_map_of_mem K.subtype hmemO)
  have hy1eq : (y₁ : G) = ((y₁ * m⁻¹ : ↥K) : G) * (m : G) := by
    simp [Subgroup.coe_mul]
  rw [hy1eq]
  exact M.mul_mem hmemM hmM

private lemma caseTwo_lift_five {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hQp : IsPGroup 3 Q) (hK : KNormalAt M)
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    (hf : ((((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))).map f.toMonoidHom) =
        a11TwoSetStab 9 10)
    {u₁ : ↥(kSub 3 M H)} {s₁ t : alternatingGroup (Fin 11)}
    (hu1Q : u₁ ∈ Q.subgroupOf (kSub 3 M H))
    (hu1 : f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) u₁) = s₁)
    (ht : t ∈ a11TwoSetStab 9 10) (htord : orderOf t = 5) (hcomm : Commute s₁ t) :
    ∃ y₁ : ↥(kSub 3 M H),
      (y₁ : G) ∈ M ∧
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) y₁ = f.symm t ∧
      y₁ ^ 5 ∈ CFSG.pPrimeCore 3 ↥(kSub 3 M H) ∧
      Commute (u₁ : G) (y₁ : G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* threeStar K := QuotientGroup.mk' O
  let t' : threeStar K := f.symm t
  obtain ⟨y₁, hy1cent, hy1π⟩ :=
    caseTwo_lift_centralizer hQp f hu1Q hu1 htord hcomm
  have hy1π' : π y₁ = t' := hy1π
  have hy1M : (y₁ : G) ∈ M := caseTwo_lift_mem_M h hK f hf ht hy1π
  have ht5 : t ^ 5 = 1 := by rw [← htord]; exact pow_orderOf_eq_one t
  have ht'5 : t' ^ 5 = 1 := by
    have h' : (f.symm t) ^ 5 = 1 := by rw [← map_pow, ht5, map_one]
    simpa [t'] using h'
  have h5O : y₁ ^ 5 ∈ O := by
    rw [← QuotientGroup.eq_one_iff]
    change π (y₁ ^ 5) = 1
    rw [map_pow, hy1π', ht'5]
  have hcommG : Commute (u₁ : G) (y₁ : G) :=
    congrArg (fun q : ↥K => (q : G))
      (Subgroup.mem_centralizer_iff.mp hy1cent u₁ (Subgroup.mem_zpowers u₁))
  exact ⟨y₁, hy1M, hy1π, h5O, hcommG⟩

private lemma caseTwo_orderOf_lift {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H)
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    {t : alternatingGroup (Fin 11)}
    (y₁ : ↥(kSub 3 M H))
    (hy1π : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) y₁ = f.symm t)
    (htord : orderOf t = 5)
    (h5O : y₁ ^ 5 ∈ CFSG.pPrimeCore 3 ↥(kSub 3 M H)) :
    ∃ b : ℕ, orderOf ((y₁ : G) ^ 5) = 2 ^ b ∧ orderOf (y₁ : G) = 5 * 2 ^ b := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* threeStar K := QuotientGroup.mk' O
  let t' : threeStar K := f.symm t
  have hπy : π y₁ = t' := by simpa [π, t'] using hy1π
  have ht'ord : orderOf t' = 5 := by
    rw [show t' = f.symm t from rfl, MulEquiv.orderOf_eq, htord]
  have h2prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 (O.map K.subtype) := by
    rw [← h.pCoreOf_two_kSub_eq_caseTwo h2]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hmemG : ((y₁ : G) ^ 5) ∈ O.map K.subtype := by
    simpa [Subgroup.coe_pow] using Subgroup.mem_map_of_mem K.subtype h5O
  obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hO2) ⟨(y₁ : G) ^ 5, hmemG⟩
  have hbG : orderOf ((y₁ : G) ^ 5) = 2 ^ b := by
    have h := (Subgroup.orderOf_coe (⟨(y₁ : G) ^ 5, hmemG⟩ :
      ↥(O.map K.subtype))).trans hb
    simpa using h
  have h5dvd : 5 ∣ orderOf (y₁ : G) := by
    have hdvd := orderOf_map_dvd π y₁
    rw [hπy, ht'ord] at hdvd
    rwa [← Subgroup.orderOf_coe y₁] at hdvd
  have hord : orderOf (y₁ : G) = 5 * 2 ^ b := by
    have hpow := orderOf_pow (n := 5) (y₁ : G)
    rw [hbG, Nat.gcd_eq_right_iff_dvd.mpr h5dvd] at hpow
    have hmul : orderOf (y₁ : G) / 5 * 5 = orderOf (y₁ : G) :=
      Nat.div_mul_cancel h5dvd
    rw [← hpow] at hmul
    rw [← hmul, Nat.mul_comm]
  exact ⟨b, hbG, hord⟩

private lemma caseTwo_pi_pow_ne_one {M H : Subgroup G}
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    {t : alternatingGroup (Fin 11)} {y₁ : ↥(kSub 3 M H)}
    (hy1π : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) y₁ = f.symm t)
    (htord : orderOf t = 5) (b : ℕ) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) (y₁ ^ (2 ^ b)) ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* threeStar K := QuotientGroup.mk' O
  let t' : threeStar K := f.symm t
  have hπy : π y₁ = t' := by simpa [π, t'] using hy1π
  have ht'ord : orderOf t' = 5 := by
    rw [show t' = f.symm t from rfl, MulEquiv.orderOf_eq, htord]
  have hcop : Nat.Coprime 5 (2 ^ b) := (by norm_num : Nat.Coprime 5 2).pow_right b
  have ht'pow : orderOf (t' ^ (2 ^ b)) = 5 := by
    have hcop' : (orderOf t').Coprime (2 ^ b) := by rwa [ht'ord]
    rw [hcop'.orderOf_pow, ht'ord]
  intro h1
  rw [map_pow, hπy] at h1
  have h2' : orderOf (t' ^ (2 ^ b)) = 1 := by rw [h1, orderOf_one]
  omega

private lemma caseTwo_five_order {M H : Subgroup G}
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    {u₁ : ↥(kSub 3 M H)} {t : alternatingGroup (Fin 11)}
    (y₁ : ↥(kSub 3 M H)) (hy1M : (y₁ : G) ∈ M)
    (hy1π : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) y₁ = f.symm t)
    (htord : orderOf t = 5) (b : ℕ)
    (hbG : orderOf ((y₁ : G) ^ 5) = 2 ^ b)
    (hcomm : Commute (u₁ : G) (y₁ : G)) :
    ((y₁ : G) ^ (2 ^ b)) ∈ M ∧ orderOf ((y₁ : G) ^ (2 ^ b)) = 5 ∧
      Commute (u₁ : G) ((y₁ : G) ^ (2 ^ b)) := by
  classical
  have hyM : ((y₁ : G) ^ (2 ^ b)) ∈ M := M.pow_mem hy1M _
  have hcommy : Commute (u₁ : G) ((y₁ : G) ^ (2 ^ b)) := hcomm.pow_right (2 ^ b)
  have hy5 : ((y₁ : G) ^ (2 ^ b)) ^ 5 = 1 := by
    calc ((y₁ : G) ^ 2 ^ b) ^ 5 = ((y₁ : G) ^ 5) ^ (2 ^ b) := by
          rw [← pow_mul, Nat.mul_comm (2 ^ b) 5, ← pow_mul]
      _ = 1 := by rw [← hbG]; exact pow_orderOf_eq_one _
  have hπy_ne := caseTwo_pi_pow_ne_one f hy1π htord b
  have hyne : (y₁ : G) ^ (2 ^ b) ≠ 1 := by
    intro h1
    apply hπy_ne
    have hK : y₁ ^ (2 ^ b) = 1 := Subtype.ext (by
      simpa [Subgroup.coe_pow] using h1)
    rw [hK, map_one]
  have hyord : orderOf ((y₁ : G) ^ (2 ^ b)) = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime hy5 hyne
  exact ⟨hyM, hyord, hcommy⟩

private lemma caseTwo_five_not_mem {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H)
    (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet)
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    {t : alternatingGroup (Fin 11)} {y₁ : ↥(kSub 3 M H)}
    (hy1π : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) y₁ = f.symm t)
    (htord : orderOf t = 5) (b : ℕ) :
    ((y₁ : G) ^ (2 ^ b)) ∉ (CFSG.pPrimeCore 3 ↥M).map M.subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* threeStar K := QuotientGroup.mk' O
  have hπy_ne : π (y₁ ^ (2 ^ b)) ≠ 1 :=
    caseTwo_pi_pow_ne_one f hy1π htord b
  intro hyDM
  have hyK : (y₁ : G) ^ (2 ^ b) ∈ K := K.pow_mem y₁.2 _
  have hle := h.pPrimeCore_inf_kSub_le h2 hK hU hL hKF
  have hyO : (y₁ : G) ^ (2 ^ b) ∈ O.map K.subtype := hle ⟨hyDM, hyK⟩
  obtain ⟨o, hoO, hoy⟩ := Subgroup.mem_map.mp hyO
  have hyO' : (⟨(y₁ : G) ^ (2 ^ b), hyK⟩ : ↥K) ∈ O := by
    have hyo : (⟨(y₁ : G) ^ (2 ^ b), hyK⟩ : ↥K) = o := Subtype.ext hoy.symm
    rwa [hyo]
  have hπy1 : π (⟨(y₁ : G) ^ (2 ^ b), hyK⟩) ≠ 1 := by
    have hyeq : (⟨(y₁ : G) ^ (2 ^ b), hyK⟩ : ↥K) = y₁ ^ (2 ^ b) :=
      Subtype.ext (by simp [Subgroup.coe_pow])
    rwa [hyeq]
  exact hπy1 ((QuotientGroup.eq_one_iff _).mpr hyO')

private lemma caseTwo_five_element {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H)
    (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet)
    (f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11))
    {u₁ : ↥(kSub 3 M H)} {t : alternatingGroup (Fin 11)}
    (y₁ : ↥(kSub 3 M H))
    (hy1M : (y₁ : G) ∈ M)
    (hy1π : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) y₁ = f.symm t)
    (htord : orderOf t = 5)
    (h5O : y₁ ^ 5 ∈ CFSG.pPrimeCore 3 ↥(kSub 3 M H))
    (hcomm : Commute (u₁ : G) (y₁ : G)) :
    ∃ y : G, y ∈ M ∧ orderOf y = 5 ∧ Commute (u₁ : G) y ∧
      y ∉ (CFSG.pPrimeCore 3 ↥M).map M.subtype := by
  obtain ⟨b, hbG, _⟩ := caseTwo_orderOf_lift h h2 f y₁ hy1π htord h5O
  have hfive := caseTwo_five_order f y₁ hy1M hy1π htord b hbG hcomm
  have hnot := caseTwo_five_not_mem h h2 hK hU hL hKF f hy1π htord b
  exact ⟨(y₁ : G) ^ (2 ^ b), hfive.1, hfive.2.1, hfive.2.2, hnot⟩

theorem S14Choice.exists_caseTwo_elements {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (hKF : KFactA11GammaTwoSet) :
    ∃ u₁ u₂ y : G, u₁ ∈ Q ∧ u₂ ∈ Q ∧ u₁ ^ 3 = 1 ∧ u₂ ^ 3 = 1 ∧ u₁ ≠ 1 ∧ Commute u₁ u₂ ∧
      u₂ ∉ Subgroup.zpowers u₁ ∧
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥(kSub 3 M H ⊓
        Subgroup.centralizer (Subgroup.closure ({u₁, u₂} : Set G) : Set G)) ∧
      y ∈ M ∧ orderOf y = 5 ∧ Commute u₁ y ∧ y ∉ (CFSG.pPrimeCore 3 ↥M).map M.subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQp : IsPGroup 3 Q := (h.isSylowOf_kSub h2).isPGroup
  obtain ⟨f, hf⟩ := caseTwo_twoSet_aut h h2 hK hU hL hKF
  obtain ⟨T, hTle, hT⟩ := caseTwo_quotient_sylow h h2 hU f hf
  obtain ⟨s₁, s₂, t, hs1T, hs2T, hs1cube, hs2cube, hs1ne, hs12, hs2notz, hnotC, ht, htord,
    hs1t⟩ := exists_caseTwo_perms T hTle
  obtain ⟨u₁, u₂, hu1Q, hu2Q, hu1, hu2, hu1cube, hu2cube, hu1ne, hu12, hu2notz⟩ :=
    caseTwo_lift_perms hQp f T hT hs1T hs2T hs1cube hs2cube hs1ne hs12 hs2notz
  have hnot := caseTwo_not_isPSolvable hQp f hu1Q hu2Q hu1 hu2 hnotC
  obtain ⟨y₁, hy1M, hy1π, h5O, hcommy1⟩ :=
    caseTwo_lift_five h hQp hK f hf hu1Q hu1 ht htord hs1t
  obtain ⟨y, hyM, hyord, hcommy, hynot⟩ :=
    caseTwo_five_element h h2 hK hU hL hKF f y₁ hy1M hy1π htord h5O hcommy1
  exact ⟨(u₁ : G), (u₂ : G), y, Subgroup.mem_subgroupOf.mp hu1Q,
    Subgroup.mem_subgroupOf.mp hu2Q, hu1cube, hu2cube, hu1ne, hu12, hu2notz, hnot,
    hyM, hyord, hcommy, hynot⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
