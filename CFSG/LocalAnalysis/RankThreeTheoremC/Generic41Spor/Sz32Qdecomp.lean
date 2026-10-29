module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedProp31
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointSz32
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Fusion
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0 u3_T_inf_K0_gen x_mem_u3K0_gen
  u3K0_conj_gen u3_core_conj fus_mem_zpowers_of_isCyclic_of_pow_prime)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_A_T (hdata : Sz32DataFacts) (hc : PointConfig IsSz32Type G 5 P M x J) :
    ∃ a : G, a ∈ u3S P x ∧ a ∈ J ∧ orderOf a = 25 ∧ Subgroup.zpowers a = u3T P x J := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  obtain ⟨Tsyl, hTsyl, hTinj⟩ := sps_sylow_data hc.generic hc.le_cent hc.cent_le ψ hker
  obtain ⟨Tb, hTb⟩ : ∃ Tb : Sylow 5 Q, (Tb : Subgroup Q) = (Tsyl : Subgroup ↥J).map ψ :=
    ⟨Tsyl.mapSurjective hψ, Sylow.coe_mapSurjective hψ Tsyl⟩
  obtain ⟨hD, -⟩ := hdata Q hQ Tb
  have hTbcyc : IsCyclic ↥(Tb : Subgroup Q) := hD.isCyclic
  have hTb25 : Nat.card ↥(Tb : Subgroup Q) = 25 := hD.card_eq
  have hTsylcyc : IsCyclic ↥(Tsyl : Subgroup ↥J) := by
    refine sps_isCyclic_of_inj ψ _ hTinj ?_
    rw [← hTb]
    exact hTbcyc
  have hTsylcard : Nat.card ↥(Tsyl : Subgroup ↥J) = 25 := by
    rw [← sps_card_map_of_inj ψ _ hTinj, ← hTb]
    exact hTb25
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hTsyl' : (Tsyl : Subgroup ↥J) = (u3T P x J).subgroupOf J := hTsyl
  have hTuCyc : IsCyclic ↥(u3T P x J) := by
    have h : IsCyclic ↥((u3T P x J).subgroupOf J) := by
      rw [← hTsyl']
      exact hTsylcyc
    exact (Subgroup.subgroupOfEquivOfLe hTJ).isCyclic.mp h
  have hTuCard : Nat.card ↥(u3T P x J) = 25 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv, ← hTsyl']
    exact hTsylcard
  obtain ⟨g, hg⟩ := hTuCyc.exists_generator
  have hgo : orderOf (g : G) = 25 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
    exact hTuCard
  refine ⟨(g : G), g.2.1, g.2.2, hgo, ?_⟩
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr g.2
  · intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem sz32_A_D (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hc : PointConfig IsSz32Type G 5 P M x J) :
    ∃ c : G, c ∈ u3S P x ∧ c ∈ u3K0 5 x J ∧
      (∀ q ∈ u3S P x, q ∈ u3K0 5 x J → q ∈ Subgroup.zpowers c) ∧
      (∃ m : ℕ, 1 ≤ m ∧ orderOf c = 5 ^ m) ∧ x ∈ Subgroup.zpowers c := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcyc := (point_prop31_ii hS hD1 hU0 hc).1
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxS : x ∈ u3S P x := ⟨hc.generic.1, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hxK : x ∈ u3K0 5 x J := x_mem_u3K0_gen hc
  have hxD : x ∈ u3S P x ⊓ u3K0 5 x J := ⟨hxS, hxK⟩
  have hDgen : ∀ q ∈ u3S P x ⊓ u3K0 5 x J, q ∈ Subgroup.zpowers (g : G) := fun q hq => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨q, hq⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hgP : (g : G) ∈ (P : Subgroup G) := g.2.1.1
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨(g : G), hgP⟩
  have hm' : orderOf (g : G) = 5 ^ m := by
    rw [← Subgroup.orderOf_mk (g : G) hgP]
    exact hm
  refine ⟨(g : G), g.2.1, g.2.2, fun q hqS hqK => hDgen q ⟨hqS, hqK⟩, ⟨m, ?_, hm'⟩, hDgen x hxD⟩
  by_contra hm0
  have hm0' : m = 0 := by omega
  rw [hm0', pow_zero, orderOf_eq_one_iff] at hm'
  apply hx1
  have := hDgen x hxD
  rw [hm', Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
  exact this

theorem sz32_P_inf_core (P : Sylow 5 G) (J : Subgroup G) :
    (P : Subgroup G) ⊓ rankThreePrimeCore 5 J = ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hOcop : (5 : ℕ).Coprime (Nat.card (rankThreePrimeCore 5 J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime 5 J
  have hPp : IsPGroup 5 ↥((P : Subgroup G) ⊓ rankThreePrimeCore 5 J) := P.isPGroup'.to_inf_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
  have hdvd : Nat.card ((P : Subgroup G) ⊓ rankThreePrimeCore 5 J : Subgroup G) ∣
      Nat.card (rankThreePrimeCore 5 J) := Subgroup.card_dvd_of_le inf_le_right
  have hk0 : k = 0 := by
    by_contra hk0
    have : 5 ∣ Nat.card (rankThreePrimeCore 5 J) := (dvd_pow_self 5 hk0).trans (hk ▸ hdvd)
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mp hOcop) this
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem sz32_A_comm {a c : G} (haS : a ∈ u3S P x) (haJ : a ∈ J) (hcS : c ∈ u3S P x)
    (hcK : c ∈ u3K0 5 x J) : a * c = c * a := by
  have h1 : c * a * c⁻¹ * a⁻¹ ∈ rankThreePrimeCore 5 J := hcK.2.2 a haJ
  have h2 : c * a * c⁻¹ * a⁻¹ ∈ (P : Subgroup G) :=
    (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hcS.1 haS.1)
      ((P : Subgroup G).inv_mem hcS.1)) ((P : Subgroup G).inv_mem haS.1)
  have h3 : c * a * c⁻¹ * a⁻¹ ∈ (P : Subgroup G) ⊓ rankThreePrimeCore 5 J := ⟨h2, h1⟩
  rw [sz32_P_inf_core P J, Subgroup.mem_bot] at h3
  have h4 : c * a * c⁻¹ = a := mul_inv_eq_one.mp h3
  calc a * c = c * a * c⁻¹ * c := by rw [h4]
    _ = c * a := by group

theorem sz32_rho_ker {Q : Type} [Group Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hc : PointConfig IsSz32Type G 5 P M x J)
    (ρ : ↥(Subgroup.centralizer ({x} : Set G)) →* MulAut Q)
    (hρ : ∀ (c : ↥(Subgroup.centralizer ({x} : Set G))) (j : ↥J)
      (hj : (c : G) * (j : G) * (c : G)⁻¹ ∈ J), ρ c (ψ j) = ψ ⟨(c : G) * (j : G) * (c : G)⁻¹, hj⟩)
    (c : ↥(Subgroup.centralizer ({x} : Set G))) : ρ c = 1 ↔ (c : G) ∈ u3K0 5 x J := by
  have hOker : ∀ j : J, ψ j = 1 ↔ (j : G) ∈ rankThreePrimeCore 5 J := by
    intro j
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hCN := hc.cent_le
  constructor
  · intro h1
    refine ⟨c.2, hCN c.2, fun j hj => ?_⟩
    have hjj : (c : G) * j * (c : G)⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hCN c.2) j).mp hj
    have h2 := hρ c ⟨j, hj⟩ hjj
    rw [h1, MulAut.one_apply] at h2
    have h3 : ψ (⟨(c : G) * j * (c : G)⁻¹, hjj⟩ * ⟨j, hj⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h2, mul_inv_cancel]
    have := (hOker _).mp h3
    simpa using this
  · intro hcK
    ext q
    obtain ⟨j, rfl⟩ := hψ q
    have hjj : (c : G) * (j : G) * (c : G)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hCN c.2) j).mp j.2
    rw [hρ c j hjj, MulAut.one_apply]
    have h5 : (c : G) * j * (c : G)⁻¹ * (j : G)⁻¹ ∈ rankThreePrimeCore 5 J := hcK.2.2 j j.2
    have h6 : ψ (⟨(c : G) * j * (c : G)⁻¹, hjj⟩ * j⁻¹) = 1 := by
      rw [hOker]
      exact h5
    rw [map_mul, map_inv] at h6
    exact mul_inv_eq_one.mp h6

theorem sz32_A_out (hdata : Sz32DataFacts) (hc : PointConfig IsSz32Type G 5 P M x J) {a c : G}
    (hTa : Subgroup.zpowers a = u3T P x J)
    (hQC : ∀ q ∈ u3S P x, q ∈ u3K0 5 x J → q ∈ Subgroup.zpowers c) :
    ∀ s ∈ u3S P x, s * a = a * s → s ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro s hsS hsa
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  obtain ⟨Tsyl, hTsyl, hTinj⟩ := sps_sylow_data hc.generic hc.le_cent hc.cent_le ψ hker
  have hTsyl' : (Tsyl : Subgroup ↥J) = (u3T P x J).subgroupOf J := hTsyl
  obtain ⟨Tb, hTb⟩ : ∃ Tb : Sylow 5 Q, (Tb : Subgroup Q) = (Tsyl : Subgroup ↥J).map ψ :=
    ⟨Tsyl.mapSurjective hψ, Sylow.coe_mapSurjective hψ Tsyl⟩
  obtain ⟨-, haut⟩ := hdata Q hQ Tb
  obtain ⟨ρ, hρ⟩ := sps_exists_action (p := 5) (C := Subgroup.centralizer ({x} : Set G))
    hc.cent_le ψ hψ hker
  have hρk := sz32_rho_ker ψ hψ hker hc ρ hρ
  have hsC : s ∈ Subgroup.centralizer ({x} : Set G) := hsS.2
  have hfix : ∀ q ∈ (Tb : Subgroup Q), ρ ⟨s, hsC⟩ q = q := by
    intro q hq
    rw [hTb] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    have htT : (t : G) ∈ u3T P x J := by
      have h : t ∈ (u3T P x J).subgroupOf J := hTsyl' ▸ ht
      exact h
    have htz : (t : G) ∈ Subgroup.zpowers a := hTa ▸ htT
    have hcomm : s * (t : G) = (t : G) * s := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htz
      rw [← hk]
      exact (Commute.zpow_right (show Commute s a from hsa) k).eq
    have hj : s * (t : G) * s⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hc.cent_le hsC) (t : G)).mp t.2
    rw [hρ ⟨s, hsC⟩ t hj]
    congr 1
    apply Subtype.ext
    show s * (t : G) * s⁻¹ = t
    rw [hcomm]
    group
  obtain ⟨tb, htb, hf⟩ := haut (ρ ⟨s, hsC⟩) hfix
  rw [hTb] at htb
  obtain ⟨t₀, ht₀, rfl⟩ := htb
  have ht₀T : (t₀ : G) ∈ u3T P x J := by
    have h : t₀ ∈ (u3T P x J).subgroupOf J := hTsyl' ▸ ht₀
    exact h
  have ht₀S : (t₀ : G) ∈ u3S P x := (inf_le_left : u3T P x J ≤ u3S P x) ht₀T
  have ht₀C : (t₀ : G) ∈ Subgroup.centralizer ({x} : Set G) := ht₀S.2
  have hρt : ρ ⟨(t₀ : G), ht₀C⟩ = MulAut.conj (ψ t₀) := by
    ext q
    obtain ⟨j, rfl⟩ := hψ q
    have hj : (t₀ : G) * (j : G) * (t₀ : G)⁻¹ ∈ J := J.mul_mem (J.mul_mem t₀.2 j.2) (J.inv_mem t₀.2)
    rw [hρ ⟨(t₀ : G), ht₀C⟩ j hj, MulAut.conj_apply]
    have e1 : (⟨(t₀ : G) * (j : G) * (t₀ : G)⁻¹, hj⟩ : J) = t₀ * j * t₀⁻¹ := Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv]
  have hst : s * (t₀ : G)⁻¹ ∈ Subgroup.centralizer ({x} : Set G) :=
    mul_mem hsC (inv_mem ht₀C)
  have h1 : ρ ⟨s * (t₀ : G)⁻¹, hst⟩ = 1 := by
    have e2 : (⟨s * (t₀ : G)⁻¹, hst⟩ : ↥(Subgroup.centralizer ({x} : Set G))) =
        ⟨s, hsC⟩ * ⟨(t₀ : G), ht₀C⟩⁻¹ := rfl
    rw [e2, map_mul, map_inv, hf, hρt, mul_inv_cancel]
  have hK : s * (t₀ : G)⁻¹ ∈ u3K0 5 x J := (hρk ⟨s * (t₀ : G)⁻¹, hst⟩).mp h1
  have hSt : s * (t₀ : G)⁻¹ ∈ u3S P x := (u3S P x).mul_mem hsS ((u3S P x).inv_mem ht₀S)
  have hcz : s * (t₀ : G)⁻¹ ∈ Subgroup.zpowers c := hQC _ hSt hK
  have haz : (t₀ : G) ∈ Subgroup.zpowers a := hTa ▸ ht₀T
  have hs : s = (s * (t₀ : G)⁻¹) * (t₀ : G) := by group
  rw [hs]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcz) (Subgroup.mem_sup_left haz)

theorem sz32_card_pSubgroup_aut_le (Q : Type) [Group Q] [Finite Q] (hZ : Subgroup.center Q = ⊥)
    (hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Q) = 5)
    (hSyl : ∀ T : Sylow 5 Q, Nat.card (T : Subgroup Q) = 5 ^ 2) (R : Subgroup (MulAut Q))
    (hR : IsPGroup 5 R) : Nat.card R ≤ 125 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite (MulAut Q) :=
    Finite.of_injective (fun f : MulAut Q => (f : Q → Q)) DFunLike.coe_injective
  have hcinj : Function.Injective (MulAut.conj : Q →* MulAut Q) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkc : k ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun φ : MulAut Q => φ y) hk
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * k = (k * y * k⁻¹) * k := by rw [h1]
        _ = k * y := by group
    rw [hZ, Subgroup.mem_bot] at hkc
    exact hkc
  have hinn : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner Q) = Nat.card Q := by
    unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
    exact (Nat.card_congr (MonoidHom.ofInjective hcinj).toEquiv).symm
  have hAut : Nat.card (MulAut Q) = 5 * Nat.card Q := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.ComponentClassification.OuterAutomorphisms.inner Q)
    rw [hinn] at h
    have hOut' : Nat.card (MulAut Q ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner Q) = 5 :=
      hOut
    rw [hOut'] at h
    exact h
  obtain ⟨T⟩ : Nonempty (Sylow 5 Q) := inferInstance
  have hT : Nat.card (T : Subgroup Q) = 5 ^ (Nat.card Q).factorization 5 := Sylow.card_eq_multiplicity T
  have hf : (Nat.card Q).factorization 5 = 2 := by
    have h2 := hSyl T
    rw [hT] at h2
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) (show 5 ^ (Nat.card Q).factorization 5 = 5 ^ 2 from h2)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
  have hdvd : Nat.card R ∣ Nat.card (MulAut Q) := Subgroup.card_subgroup_dvd_card R
  rw [hk, hAut] at hdvd
  have hQpos : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hk3 : k ≤ 3 := by
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 5)
      (mul_ne_zero (by norm_num) hQpos)).mp hdvd
    rw [Nat.factorization_mul (by norm_num) hQpos, Finsupp.add_apply, hf] at h1
    have h5 : (Nat.factorization 5) 5 = 1 := Nat.Prime.factorization_self (by norm_num)
    rw [h5] at h1
    omega
  rw [hk]
  calc 5 ^ k ≤ 5 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 125 := by norm_num

theorem sz32_A_card (hSz : Sz32Facts) (hc : PointConfig IsSz32Type G 5 P M x J) {a c : G}
    (hao : orderOf a = 25) (hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers c = ⊥)
    (hQC : ∀ q ∈ u3S P x, q ∈ u3K0 5 x J → q ∈ Subgroup.zpowers c) :
    Nat.card (u3S P x) ≤ 5 * Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers c) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  obtain ⟨ρ, hρ⟩ := sps_exists_action (p := 5) (C := Subgroup.centralizer ({x} : Set G))
    hc.cent_le ψ hψ hker
  have hρk := sz32_rho_ker ψ hψ hker hc ρ hρ
  have hZ : Subgroup.center Q = ⊥ :=
    u3main_center_bot (CFSG.AGLEmbedding.glbPrimeCore_le 5 J)
      hc.perfect hc.lt hc.minimal ψ hψ hker
  have hSC : u3S P x ≤ Subgroup.centralizer ({x} : Set G) := inf_le_right
  let φ : ↥(u3S P x) →* MulAut Q := ρ.comp (Subgroup.inclusion hSC)
  have hφk : ∀ s : ↥(u3S P x), φ s = 1 → (s : G) ∈ Subgroup.zpowers c := by
    intro s hs
    exact hQC s s.2 ((hρk ⟨(s : G), hSC s.2⟩).mp hs)
  have hkerle : Nat.card φ.ker ≤ Nat.card (Subgroup.zpowers c) := by
    refine Nat.card_le_card_of_injective (fun s => ⟨(s.1 : G), hφk s.1 s.2⟩) ?_
    intro s t hst
    have h1 : ((s.1 : ↥(u3S P x)) : G) = ((t.1 : ↥(u3S P x)) : G) := by
      have := congrArg Subtype.val hst
      simpa using this
    exact Subtype.ext (Subtype.ext h1)
  have hpg : IsPGroup 5 ↥φ.range :=
    IsPGroup.of_surjective (P.isPGroup'.to_le (inf_le_left : u3S P x ≤ (P : Subgroup G)))
      φ.rangeRestrict φ.rangeRestrict_surjective
  have hrange : Nat.card φ.range ≤ 125 :=
    sz32_card_pSubgroup_aut_le Q hZ (hSz.outer Q hQ) (fun T => (hSz.sylow Q hQ T).2) φ.range hpg
  have hmain := Subgroup.card_ker_mul_card_range φ
  let f : ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers c) → ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers c) :=
    fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hfinj : Function.Injective f := by
    rintro ⟨⟨t, ht⟩, ⟨d, hd⟩⟩ ⟨⟨t', ht'⟩, ⟨d', hd'⟩⟩ h
    have h1 : t * d = t' * d' := congrArg Subtype.val h
    have h2 : t'⁻¹ * t = d' * d⁻¹ := by
      calc t'⁻¹ * t = t'⁻¹ * (t * d) * d⁻¹ := by group
        _ = t'⁻¹ * (t' * d') * d⁻¹ := by rw [h1]
        _ = d' * d⁻¹ := by group
    have h3 : t'⁻¹ * t ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers c :=
      ⟨(Subgroup.zpowers a).mul_mem ((Subgroup.zpowers a).inv_mem ht') ht,
        h2 ▸ (Subgroup.zpowers c).mul_mem hd' ((Subgroup.zpowers c).inv_mem hd)⟩
    rw [hinf, Subgroup.mem_bot] at h3
    have h4 : t = t' := by
      have := congrArg (t' * ·) h3
      simpa using this
    have h5 : d = d' := by
      rw [h4] at h1
      exact mul_left_cancel h1
    subst h4
    subst h5
    rfl
  have hprod : Nat.card (↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers c)) ≤
      Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers c) := Nat.card_le_card_of_injective f hfinj
  rw [Nat.card_prod, Nat.card_zpowers, hao] at hprod
  calc Nat.card (u3S P x) = Nat.card φ.ker * Nat.card φ.range := hmain.symm
    _ ≤ Nat.card (Subgroup.zpowers c) * 125 := Nat.mul_le_mul hkerle hrange
    _ = 5 * (25 * Nat.card (Subgroup.zpowers c)) := by ring
    _ ≤ 5 * Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers c) := Nat.mul_le_mul_left 5 hprod

theorem sz32_A_omega {a c x : G} (hac : a * c = c * a) (hao : orderOf a = 25)
    (hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers c = ⊥) (hxc : x ∈ Subgroup.zpowers c)
    (hx1 : x ≠ 1) (hxp : x ^ 5 = 1) :
    ∀ q ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c, q ^ 5 = 1 →
      q ∈ Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro q hq hq5
  have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Subgroup.zpowers c, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((Commute.zpow_zpow (show Commute a c from hac) i j)).eq
  obtain ⟨u, hu, v, hv, rfl⟩ := sps_mem_sup_of_commute hcomm hq
  have huv : Commute u v := hcomm u hu v hv
  rw [huv.mul_pow] at hq5
  have hu5 : u ^ 5 = 1 := by
    have h1 : u ^ 5 = (v ^ 5)⁻¹ := eq_inv_of_mul_eq_one_left hq5
    have h2 : u ^ 5 ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers c :=
      ⟨(Subgroup.zpowers a).pow_mem hu 5, h1 ▸ (Subgroup.zpowers c).inv_mem ((Subgroup.zpowers c).pow_mem hv 5)⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact h2
  have hv5 : v ^ 5 = 1 := by rw [hu5, one_mul] at hq5; exact hq5
  have hvx : v ∈ Subgroup.zpowers x :=
    fus_mem_zpowers_of_isCyclic_of_pow_prime (p := 5) (Z := Subgroup.zpowers c) inferInstance hxc hv hx1 hxp hv5
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have h25 : (25 : ℤ) ∣ 5 * k := by
    have h1 : a ^ (5 * k) = 1 := by rw [mul_comm, zpow_mul]; simpa using hu5
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hao] at this
    exact_mod_cast this
  obtain ⟨l, hl⟩ : (5 : ℤ) ∣ k := by omega
  have hk : a ^ k = (a ^ 5) ^ l := by rw [← zpow_natCast, ← zpow_mul, hl]; norm_num
  exact Subgroup.mul_mem_sup (hk ▸ Subgroup.zpow_mem_zpowers (a ^ 5) l) hvx

theorem sz32_A_card_omega {a c x : G} (hao : orderOf a = 25) (hac : a * c = c * a)
    (hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers c = ⊥) (hxc : x ∈ Subgroup.zpowers c)
    (hx1 : x ≠ 1) (hxp : x ^ 5 = 1) :
    Nat.card ↥(Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x) = 25 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hxa : x ∉ Subgroup.zpowers (a ^ 5) := by
    intro hx
    have h1 : x ∈ Subgroup.zpowers a := (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 5)) hx
    have h2 : x ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers c := ⟨h1, hxc⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact hx1 h2
  have hcomm : ∀ u ∈ Subgroup.zpowers (a ^ 5), u * x = x * u := by
    intro u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxc
    have : Commute (a ^ 5) c := (show Commute a c from hac).pow_left 5
    exact ((this.zpow_zpow i j)).eq
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers (Nat.prime_five) (Subgroup.zpowers (a ^ 5)) hxp hxa hcomm]
  rw [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) (by rw [hao]; norm_num), hao]

theorem sz32_conj_mod5 {X : Type*} [Group X] {y g : X} {n : ℤ} {k : ℕ} (hk : 1 ≤ k)
    (hg : orderOf g = 5 ^ k) (hy : y ^ 5 = 1) (hn : y * g * y⁻¹ = g ^ n) : n % 5 = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpow : ∀ i : ℕ, y ^ i * g * (y ^ i)⁻¹ = g ^ (n ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc y ^ (i + 1) * g * (y ^ (i + 1))⁻¹
          = y * (y ^ i * g * (y ^ i)⁻¹) * y⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            simp only [mul_assoc]
        _ = y * g ^ (n ^ i) * y⁻¹ := by rw [ih]
        _ = (y * g * y⁻¹) ^ (n ^ i) := conj_zpow.symm
        _ = (g ^ n) ^ (n ^ i) := by rw [hn]
        _ = g ^ (n ^ (i + 1)) := by rw [← zpow_mul, pow_succ']
  have h5 := hpow 5
  rw [hy, one_mul, inv_one, mul_one] at h5
  have h1 : g ^ (n ^ 5 - 1) = 1 := by
    rw [zpow_sub_one, ← h5, mul_inv_cancel]
  have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hg] at h2
  have h3 : (5 : ℤ) ∣ n ^ 5 - 1 := by
    have : ((5 : ℕ) : ℤ) ∣ ((5 ^ k : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr (dvd_pow_self 5 (by omega))
    exact_mod_cast this.trans h2
  have h4 : ((n ^ 5 - 1 : ℤ) : ZMod 5) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr h3
  push_cast at h4
  have h6 : (n : ZMod 5) ^ 5 = (n : ZMod 5) := ZMod.pow_card (n : ZMod 5)
  have h7 : (n : ZMod 5) = 1 := by
    rw [h6] at h4
    exact sub_eq_zero.mp h4
  have h8 : ((n : ℤ) : ZMod 5) = ((1 : ℤ) : ZMod 5) := by simpa using h7
  have := (ZMod.intCast_eq_intCast_iff' n 1 5).mp h8
  simpa using this

theorem sz32_Q_decomp (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hSz : Sz32Facts)
    (hdata : Sz32DataFacts) (hc : PointConfig IsSz32Type G 5 P M x J) :
    ∃ a c y : G, Sz32QDecomp P x J a c y := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp5 : Nat.Prime 5 := by norm_num
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ 5 = 1 := hc.generic.2.1.2.2.1
  have hxo : orderOf x = 5 := orderOf_eq_prime hxp hx1
  obtain ⟨a, haS, haJ, hao, hTa⟩ := sz32_A_T hdata hc
  obtain ⟨c, hcS, hcK, hQC, ⟨m, hm1, hcm⟩, hxc⟩ := sz32_A_D hS hD1 hU0 hc
  have hac : a * c = c * a := sz32_A_comm haS haJ hcS hcK
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff, ← u3_T_inf_K0_gen hc]
    exact inf_le_inf hTa.le (Subgroup.zpowers_le.mpr hcK)
  have hcard := sz32_A_card hSz hc hao hinf hQC
  have hout := sz32_A_out hdata hc hTa hQC
  have hOm := sz32_A_omega hac hao hinf hxc hx1 hxp
  have hWc := sz32_A_card_omega hao hac hinf hxc hx1 hxp
  obtain ⟨E, hES, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 5 hp5 (u3S P x)
  have hrank3 : CFSG.Open.pRank 5 (u3S P x) = 3 := hc.generic.2.2.2
  rw [hrank3] at hEcard
  obtain ⟨y, hyE, hyQ⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
    by_contra hcon
    push Not at hcon
    have hEW : E ≤ Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x :=
      fun q hq => hOm q (hcon q hq) (hEel.2 q hq)
    have := Subgroup.card_le_of_le hEW
    rw [hEcard, hWc] at this
    norm_num at this
  have hyS : y ∈ u3S P x := hES hyE
  have hy5 : y ^ 5 = 1 := hEel.2 y hyE
  have hyC : y ∈ Subgroup.centralizer ({x} : Set G) := hyS.2
  have hQ0le : Subgroup.zpowers a ⊔ Subgroup.zpowers c ≤ u3S P x :=
    sup_le (Subgroup.zpowers_le.mpr haS) (Subgroup.zpowers_le.mpr hcS)
  have hQ1le : Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers y ≤ u3S P x :=
    sup_le hQ0le (Subgroup.zpowers_le.mpr hyS)
  have hlt : Subgroup.zpowers a ⊔ Subgroup.zpowers c <
      Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers y := by
    refine lt_of_le_of_ne le_sup_left fun h => hyQ ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hcardlt := Subgroup.card_lt_of_lt hlt
  have hSP : u3S P x ≤ (P : Subgroup G) := inf_le_left
  have hp0 : IsPGroup 5 ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers c) := P.isPGroup'.to_le (hQ0le.trans hSP)
  have hp1 : IsPGroup 5 ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers y) :=
    P.isPGroup'.to_le (hQ1le.trans hSP)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hp0
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp hp1
  rw [hj, hi] at hcardlt
  have hji : j < i := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 5)).mp hcardlt
  have h5j : 5 * 5 ^ j ≤ 5 ^ i := by
    calc 5 * 5 ^ j = 5 ^ (j + 1) := by ring
      _ ≤ 5 ^ i := Nat.pow_le_pow_right (by norm_num) hji
  have hQ1S : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers y) ≤
      Nat.card (u3S P x) := Subgroup.card_le_of_le hQ1le
  have hgen : Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers y = u3S P x := by
    refine Subgroup.eq_of_le_of_card_ge hQ1le ?_
    rw [hj] at hcard
    rw [hi] at hQ1S
    omega
  have hySa : y * a * y⁻¹ ∈ u3S P x := (u3S P x).mul_mem ((u3S P x).mul_mem hyS haS) ((u3S P x).inv_mem hyS)
  have hyaJ : y * a * y⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hc.cent_le hyC) a).mp haJ
  have hya' : y * a * y⁻¹ ∈ Subgroup.zpowers a := hTa ▸ (⟨hySa, hyaJ⟩ : y * a * y⁻¹ ∈ u3S P x ⊓ J)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hya'
  have hn5 : n % 5 = 1 :=
    sz32_conj_mod5 (k := 2) (by norm_num) (by rw [hao]; norm_num) hy5 hn.symm
  have hn25 : n % 25 ≠ 1 := by
    intro h
    have h1 : a ^ n = a := by
      have h2 := zpow_mod_orderOf a n
      rw [hao] at h2
      simp only [Nat.cast_ofNat] at h2
      rw [h, zpow_one] at h2
      exact h2.symm
    rw [h1] at hn
    have hcomm : y * a = a * y := by
      calc y * a = (y * a * y⁻¹) * y := by group
        _ = a * y := by rw [← hn]
    exact hyQ (hout y hyS hcomm)
  have hycK : y * c * y⁻¹ ∈ u3K0 5 x J := u3K0_conj_gen hc y hyC c hcK
  have hycS : y * c * y⁻¹ ∈ u3S P x := (u3S P x).mul_mem ((u3S P x).mul_mem hyS hcS) ((u3S P x).inv_mem hyS)
  have hyc' : y * c * y⁻¹ ∈ Subgroup.zpowers c := hQC _ hycS hycK
  obtain ⟨ν, hν⟩ := Subgroup.mem_zpowers_iff.mp hyc'
  have hν5 : ν % 5 = 1 := sz32_conj_mod5 hm1 hcm hy5 hν.symm
  exact ⟨a, c, y, ⟨haS, hcS, hyS, hgen.symm, hao, ⟨m, hm1, hcm⟩, hac, hinf, hy5, hyQ,
    ⟨n, hn.symm, hn5, hn25⟩, ⟨ν, hν.symm, hν5⟩, hxc, hxo⟩, haJ, hTa, hcK, hQC⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
