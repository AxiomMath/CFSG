module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Final
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Conj
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Hall
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Solv
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Orders
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Center
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.Glauberman281.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem case1_core_of_Y {p k : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {M R T Y U : Subgroup G} {x : G}
    (hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M)
    (hM2 : pCoreOf 2 M ≠ ⊥) (hCharM : CharTwo M)
    (hRM : R ≤ M) (hRn : M ≤ normalizer (R : Set G)) (hRcop : Nat.Coprime p (Nat.card R))
    (hO2R : pCoreOf 2 M ≤ R)
    (hYn : Y ≤ normalizer ((T ⊔ R : Subgroup G) : Set G))
    (hTM : T ≤ M) (hk : 2 ≤ k) (hTcard : Nat.card T = p ^ k) (hTexp : ∀ t ∈ T, t ^ p = 1)
    (hxM : x ∈ M) (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxT : x ∉ T)
    (hxcT : ∀ t ∈ T, x * t = t * x)
    (hVp : IsPGroup p (T ⊔ zpowers x : Subgroup G))
    (hUV : U ≤ T ⊔ zpowers x) (hxU : x ∈ U) (hUcard : Nat.card U = p ^ 2)
    (hUcT : ∀ u ∈ U, ∀ t ∈ T, u * t = t * u) (hUcx : ∀ u ∈ U, u * x = x * u)
    (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M) (hUY : U ≤ normalizer (Y : Set G))
    (hYB : IsSylowOf 2 (Y ⊓ R) R) :
    normalizer (Y : Set G) ≤ M := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hVM : T ⊔ zpowers x ≤ M := sup_le hTM (zpowers_le.2 hxM)
  have hTn : T ≤ normalizer (R : Set G) := hTM.trans hRn
  have hTR : T ⊓ R = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
      (by rw [hTcard]; exact Nat.Coprime.pow_left k hRcop))
  have hxN : x ∈ normalizer ((T ⊔ R : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup T R ⟨case1_mem_normalizer_of_comm hxcT, hRn hxM⟩
  obtain ⟨c, hcR, hcU, hYB', hVN⟩ :=
    exists_conj_normalizes_inf hVp hRcop (hVM.trans hRn) hUV (hYM.trans hRn) hUY hYB
  set Y' : Subgroup G := Y.map (MulAut.conj c).toMonoidHom with hY'
  have hcM : c ∈ M := hRM hcR
  have hY'M : Y' ≤ M := map_conj_le_of_mem hcM hYM
  have hY'2 : IsPGroup 2 Y' := hY2.map _
  have hUY' : U ≤ normalizer (Y' : Set G) := fun u hu =>
    mem_normalizer_map_conj_of_commute (hcU u hu) (hUY hu)
  have hxY' : x ∈ normalizer (Y' : Set G) := hUY' hxU
  have hcN : c ∈ normalizer ((T ⊔ R : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_sup_right hcR)
  have hY'N : Y' ≤ normalizer ((T ⊔ R : Subgroup G) : Set G) := map_conj_le_of_mem hcN hYn
  have hKn' : Y' ⊔ zpowers x ≤ normalizer ((T ⊔ R : Subgroup G) : Set G) :=
    sup_le hY'N (zpowers_le.2 hxN)
  obtain ⟨hVsyl, hYsyl, hidx⟩ := case1_orders_gen hp2 hTn hRcop hKn' hTcard hxp hx1 hxT hxcT
    hY'2 hxY' hYB'
  set H₁ : Subgroup G := (T ⊔ R) ⊔ (Y' ⊔ zpowers x) with hH₁
  have hH₁M : H₁ ≤ M := sup_le (sup_le hTM hRM) (sup_le hY'M (zpowers_le.2 hxM))
  have hH₁N : H₁ ≤ normalizer ((T ⊔ R : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer hKn'
  have hRH₁ : R ≤ H₁ := le_sup_right.trans le_sup_left
  have hVH₁ : T ⊔ zpowers x ≤ H₁ := hVsyl.le
  have hY'H₁ : Y' ≤ H₁ := hYsyl.le
  have hsolv := solvable_normalizer_inf_of_sylow hp hp2 hRH₁ (hH₁M.trans hRn) hidx hYB'
  set L : Subgroup G := H₁ ⊓ normalizer ((Y' ⊓ R : Subgroup G) : Set G) with hL
  have hVL : T ⊔ zpowers x ≤ L := le_inf hVH₁ hVN
  have hY'L : Y' ≤ L :=
    le_inf hY'H₁ (le_normalizer_inf_of_le_normalizer (hY'M.trans hRn))
  have hVsylL : IsSylowOf p (T ⊔ zpowers x) L := hVsyl.of_le hVL inf_le_left
  have hYsylL : IsSylowOf 2 Y' L := hYsyl.of_le hY'L inf_le_left
  have hUL : U ≤ L := hUV.trans hVL
  obtain ⟨l, hlL, hUS, hperm⟩ :=
    exists_permutable_conj_sylow hp2 hsolv hYsylL hVsylL hUL (hVp.to_le hUV) hUY'
  set S : Subgroup G := (T ⊔ zpowers x).map (MulAut.conj l).toMonoidHom with hS
  have hlM : l ∈ M := hH₁M (Subgroup.mem_inf.1 hlL).1
  have hSM : S ≤ M := map_conj_le_of_mem hlM hVM
  have hSp : IsPGroup p S := hVp.map _
  have hexpV := pow_eq_one_of_mem_sup_zpowers hTexp hxp hxcT
  have hexp : ∀ s ∈ S, s ^ p = 1 := by
    intro s hs
    have h1 := hexpV (l⁻¹ * s * l) (mem_map_conj_iff.1 hs)
    have h2 : (l⁻¹ * s * l) ^ p = l⁻¹ * s ^ p * l := by
      simpa using conj_pow (a := l⁻¹) (b := s) (i := p)
    rw [h2] at h1
    calc s ^ p = l * (l⁻¹ * s ^ p * l) * l⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hUc : ∀ u ∈ U, ∀ s ∈ S, u * s = s * u := by
    intro u hu s hs
    have huM : u ∈ M := hVM (hUV hu)
    have hw : l⁻¹ * u * l ∈ T ⊔ zpowers x := mem_map_conj_iff.1 (hUS hu)
    have hlN : l ∈ normalizer ((T ⊔ R : Subgroup G) : Set G) := hH₁N (Subgroup.mem_inf.1 hlL).1
    have hcomm := conj_commutes_of_mem_normalizer hTn (hRn hlM) (hRn huM) hlN hTR hxcT
      (hUcT u hu) (hUcx u hu) hw
    have hv : l⁻¹ * s * l ∈ T ⊔ zpowers x := mem_map_conj_iff.1 hs
    have h := hcomm _ hv
    calc u * s = l * ((l⁻¹ * u * l) * (l⁻¹ * s * l)) * l⁻¹ := by group
      _ = l * ((l⁻¹ * s * l) * (l⁻¹ * u * l)) * l⁻¹ := by rw [h]
      _ = s * u := by group
  have hSU : ¬ S ≤ U := by
    intro h
    have hTS : T.map (MulAut.conj l).toMonoidHom ≤ S := Subgroup.map_mono le_sup_left
    have hTU : T.map (MulAut.conj l).toMonoidHom ≤ U := hTS.trans h
    have h1 : Nat.card (T.map (MulAut.conj l).toMonoidHom) ≤ Nat.card U :=
      Subgroup.card_le_of_le hTU
    rw [Subgroup.card_map_of_injective (MulAut.conj l).injective, hTcard, hUcard] at h1
    have hk2 : k = 2 := by
      by_contra hne
      have hk3 : 2 < k := lt_of_le_of_ne hk (Ne.symm hne)
      have h2 : p ^ 2 < p ^ k := Nat.pow_lt_pow_right hp.one_lt hk3
      omega
    have hTUeq : T.map (MulAut.conj l).toMonoidHom = U :=
      Subgroup.eq_of_le_of_card_ge hTU (by
        rw [Subgroup.card_map_of_injective (MulAut.conj l).injective, hTcard, hUcard, hk2])
    have hxS : l * x * l⁻¹ ∈ S := ⟨x, Subgroup.mem_sup_right (Subgroup.mem_zpowers x), rfl⟩
    have hxTl : l * x * l⁻¹ ∈ T.map (MulAut.conj l).toMonoidHom := hTUeq ▸ h hxS
    apply hxT
    have := mem_map_conj_iff.1 hxTl
    have e : l⁻¹ * (l * x * l⁻¹) * l = x := by group
    rwa [e] at this
  have hO2Y' : pCoreOf 2 M ≤ Y' ⊓ R :=
    le_of_normal_isPGroup_of_isSylowOf hYB' hO2R
      (hRM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hO2Y : pCoreOf 2 M ≤ Y' := hO2Y'.trans inf_le_left
  have hWM : Y' ⊔ S ≤ M := sup_le hY'M hSM
  have hF : CharTwo (Y' ⊔ S) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Glauberman281.charTwo_of_le hWM hCharM
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hO2Y.trans le_sup_left)
        (hWM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M))
  have hY'1 : Y' ≠ ⊥ := by
    intro h
    exact hM2 (le_bot_iff.1 (hO2Y.trans h.le))
  exact normalizer_le_of_normalizer_map_conj_le hcM
    (case1_final h5 hD1' hY'2 hY'1 hSp hSM hF hperm hexp hUS hUc hUcard hSU hUY')

theorem case1_core_gen {p k : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {M R T Y U : Subgroup G} {x : G}
    (hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M)
    (hM2 : pCoreOf 2 M ≠ ⊥) (hCharM : CharTwo M)
    (hRM : R ≤ M) (hRn : M ≤ normalizer (R : Set G)) (hRcop : Nat.Coprime p (Nat.card R))
    (hO2R : pCoreOf 2 M ≤ R)
    (hNn : M ≤ normalizer ((T ⊔ R : Subgroup G) : Set G))
    (hTM : T ≤ M) (hk : 2 ≤ k) (hTcard : Nat.card T = p ^ k) (hTexp : ∀ t ∈ T, t ^ p = 1)
    (hxM : x ∈ M) (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxT : x ∉ T)
    (hxcT : ∀ t ∈ T, x * t = t * x)
    (hVp : IsPGroup p (T ⊔ zpowers x : Subgroup G))
    (hUV : U ≤ T ⊔ zpowers x) (hxU : x ∈ U) (hUcard : Nat.card U = p ^ 2)
    (hUcT : ∀ u ∈ U, ∀ t ∈ T, u * t = t * u) (hUcx : ∀ u ∈ U, u * x = x * u)
    (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M) (hUY : U ≤ normalizer (Y : Set G))
    (hYB : IsSylowOf 2 (Y ⊓ R) R) :
    normalizer (Y : Set G) ≤ M :=
  case1_core_of_Y h5 hD1' hM2 hCharM hRM hRn hRcop hO2R (hYM.trans hNn) hTM hk hTcard hTexp hxM hxp
    hx1 hxT hxcT hVp hUV hxU hUcard hUcT hUcx hY2 hYM hUY hYB

theorem case1_core {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {M R T Y U : Subgroup G} {x : G}
    (hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M)
    (hM2 : pCoreOf 2 M ≠ ⊥) (hCharM : CharTwo M)
    (hRM : R ≤ M) (hRn : M ≤ normalizer (R : Set G)) (hRcop : Nat.Coprime p (Nat.card R))
    (hO2R : pCoreOf 2 M ≤ R)
    (hNn : M ≤ normalizer ((T ⊔ R : Subgroup G) : Set G))
    (hTM : T ≤ M) (hTcard : Nat.card T = p ^ 3) (hTexp : ∀ t ∈ T, t ^ p = 1)
    (hxM : x ∈ M) (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxT : x ∉ T)
    (hxcT : ∀ t ∈ T, x * t = t * x)
    (hVp : IsPGroup p (T ⊔ zpowers x : Subgroup G))
    (hUV : U ≤ T ⊔ zpowers x) (hxU : x ∈ U) (hUcard : Nat.card U = p ^ 2)
    (hUcT : ∀ u ∈ U, ∀ t ∈ T, u * t = t * u) (hUcx : ∀ u ∈ U, u * x = x * u)
    (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M) (hUY : U ≤ normalizer (Y : Set G))
    (hYB : IsSylowOf 2 (Y ⊓ R) R) :
    normalizer (Y : Set G) ≤ M :=
  case1_core_gen h5 hD1' hM2 hCharM hRM hRn hRcop hO2R hNn hTM (by norm_num) hTcard hTexp hxM hxp
    hx1 hxT hxcT hVp hUV hxU hUcard hUcT hUcx hY2 hYM hUY hYB

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
