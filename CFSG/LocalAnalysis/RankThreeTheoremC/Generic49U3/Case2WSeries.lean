module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Burnside
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PlaneInT
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2TorusA
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2GenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (PointConfig pointConfig_of_u3)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

private theorem isPGroup_zpowers_of_pow_eq_one' {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] {g : Y}
    {k : ℕ} (hg : g ^ (p ^ k) = 1) : IsPGroup p (Subgroup.zpowers g) := by
  obtain ⟨m, -, hm'⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hg)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm'])

private theorem two_le_pRank_of_typeTStruct {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig Typ G p P M x J) (hTstr : TypeTStruct p P x J) :
    2 ≤ CFSG.Open.pRank p (u3T P x J) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨hTcard, hTexp, hTnab, -⟩ := id hTstr
  obtain ⟨E, hET, hE, hEcard, -⟩ := exists_isElemAbelian_card_sq_of_nonabelian hTcard hTexp hTnab
  exact le_pRank_of_elemAbelian_card hET hE hEcard

theorem u3_pElement_MJ_core (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J)
    (h2 : 2 ≤ CFSG.Open.pRank p (u3T P x J)) (hmax : TypeBorelMax Typ p) :
    ∀ g ∈ M ⊓ J, (∃ k : ℕ, g ^ (p ^ k) = 1) → g ∈ u3T P x J ⊔ rankThreePrimeCore p J := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hTM : u3T P x J ≤ M := hTP.trans hPM
  have hTp : IsPGroup p (u3T P x J) := P.isPGroup'.to_le hTP
  have hNT : Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hc.sigma hc.core hTp hTM h2
  have hOM : rankThreePrimeCore p J ≤ M :=
    (u3main_core_facts hS hD1 hc.sigma hc.core hc.generic hc.le_cent hc.cent_le).1
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ, honto⟩ := u3_normalizer_onto_gen hc
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hSylJ : CFSG.ABGLocalTools.IsSylowOf p (u3T P x J) J :=
    hc.generic.2.2.1.inf_of_le_normalizer hc.le_cent hc.cent_le
  obtain ⟨Tsyl, hTsyl⟩ := hSylJ.exists_sylow_eq_subgroupOf
  let Tsyl' : Sylow p Q := Tsyl.mapSurjective hψ
  have hTsyl' : (Tsyl' : Subgroup Q) = ((u3T P x J).subgroupOf J).map ψ := by
    rw [← hTsyl]; exact Sylow.coe_mapSurjective hψ Tsyl
  have hmaxS := hmax Q hQ Tsyl'
  set A : Subgroup Q := (M.subgroupOf J).map ψ
  have hNA : Subgroup.normalizer ((Tsyl' : Subgroup Q) : Set Q) ≤ A := by
    intro q hq
    rw [hTsyl'] at hq
    obtain ⟨n, hnN, hnJ, hψn⟩ := honto q hq
    exact ⟨⟨n, hnJ⟩, hNT hnN.1, hψn⟩
  rcases (hmaxS A hNA).symm with hAtop | hAeq
  · exfalso
    apply hc.not_le
    intro j hj
    have hmem : ψ ⟨j, hj⟩ ∈ A := hAtop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hψm⟩ := hmem
    have hk : m⁻¹ * ⟨j, hj⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψm, inv_mul_cancel]
    rw [hker] at hk
    have hk' : ((m⁻¹ * ⟨j, hj⟩ : J) : G) ∈ rankThreePrimeCore p J := hk
    have hjm : j = (m : G) * (((m⁻¹ * ⟨j, hj⟩ : J)) : G) := by simp
    rw [hjm]
    exact M.mul_mem hm (hOM hk')
  · intro g hg hgp
    obtain ⟨hgM, hgJ⟩ := hg
    obtain ⟨k, hk⟩ := hgp
    have hψg : ψ ⟨g, hgJ⟩ ∈ Subgroup.normalizer ((Tsyl' : Subgroup Q) : Set Q) := by
      rw [← hAeq]; exact ⟨⟨g, hgJ⟩, hgM, rfl⟩
    have hpe : (ψ ⟨g, hgJ⟩) ^ (p ^ k) = 1 := by
      rw [← map_pow]
      have : (⟨g, hgJ⟩ : J) ^ (p ^ k) = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have hzp : IsPGroup p (Subgroup.zpowers (ψ ⟨g, hgJ⟩)) :=
      isPGroup_zpowers_of_pow_eq_one' hp hpe
    have hmem : ψ ⟨g, hgJ⟩ ∈ (Tsyl' : Subgroup Q) := by
      have h1 : ψ ⟨g, hgJ⟩ ∈ Subgroup.zpowers (ψ ⟨g, hgJ⟩) ⊓
          Subgroup.normalizer ((Tsyl' : Subgroup Q) : Set Q) := ⟨Subgroup.mem_zpowers _, hψg⟩
      have h2 := hzp.inf_normalizer_sylow Tsyl'
      have h3 : ψ ⟨g, hgJ⟩ ∈ Subgroup.zpowers (ψ ⟨g, hgJ⟩) ⊓ (Tsyl' : Subgroup Q) := by
        rw [← h2]; exact h1
      exact h3.2
    rw [hTsyl'] at hmem
    obtain ⟨t, ht, hψt⟩ := hmem
    have hk2 : t⁻¹ * ⟨g, hgJ⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψt, inv_mul_cancel]
    rw [hker] at hk2
    have hk2' : ((t⁻¹ * ⟨g, hgJ⟩ : J) : G) ∈ rankThreePrimeCore p J := hk2
    have hgt : g = (t : G) * (((t⁻¹ * ⟨g, hgJ⟩ : J)) : G) := by simp
    rw [hgt]
    exact Subgroup.mul_mem_sup ht hk2'

theorem u3_W_le_normalizer_core (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J)
    (h2 : 2 ≤ CFSG.Open.pRank p (u3T P x J)) (hTexp : ∀ t ∈ u3T P x J, t ^ p = 1)
    (hmax : TypeBorelMax Typ p) :
    M ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((u3T P x J ⊔ u3K0 p x J : Subgroup G) : Set G) := by
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have key : ∀ w ∈ M ⊓ Subgroup.centralizer ({x} : Set G), ∀ s ∈ u3T P x J ⊔ u3K0 p x J,
      w * s * w⁻¹ ∈ u3T P x J ⊔ u3K0 p x J := by
    intro w hw s hs
    have hle : u3T P x J ⊔ u3K0 p x J ≤
        (u3T P x J ⊔ u3K0 p x J).comap (MulAut.conj w).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro t ht
        have hwtM : w * t * w⁻¹ ∈ M :=
          M.mul_mem (M.mul_mem hw.1 (hPM (hTP ht))) (M.inv_mem hw.1)
        have hwtJ : w * t * w⁻¹ ∈ J :=
          ((Subgroup.mem_normalizer_iff.mp (hc.cent_le hw.2) t).mp (hTJ ht))
        have hpe : (w * t * w⁻¹) ^ (p ^ 1) = 1 := by
          rw [pow_one, conj_pow, hTexp t ht]; simp
        have h1 := u3_pElement_MJ_core hS hD1 hU0 hc h2 hmax _ ⟨hwtM, hwtJ⟩ ⟨1, hpe⟩
        exact sup_le_sup_left (u3_core_le_K0_gen hc) _ h1
      · intro k hk
        exact Subgroup.mem_sup_right (u3K0_conj_gen hc w hw.2 k hk)
    exact hle hs
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨key w hw s, fun h => ?_⟩
  have h1 := key w⁻¹ (inv_mem hw) _ h
  simpa [mul_assoc] using h1

theorem u3_centSeries_core (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J) (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (h2 : 2 ≤ CFSG.Open.pRank p (u3T P x J)) (hTexp : ∀ t ∈ u3T P x J, t ^ p = 1)
    (hmax : TypeBorelMax Typ p) (hDcyc : IsCyclic ↥((P : Subgroup G) ⊓ u3K0 p x J))
    (hxD : x ∈ (P : Subgroup G) ⊓ u3K0 p x J) (hxo : orderOf x = p)
    (hdec : (P : Subgroup G) ≤ u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J)) :
    ∃ N : Subgroup G, CentSeries p (M ⊓ Subgroup.centralizer ({x} : Set G)) (P : Subgroup G) N := by
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hPW : (P : Subgroup G) ≤ M ⊓ Subgroup.centralizer ({x} : Set G) := le_inf hPM hP
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  obtain ⟨N₀, -, hN₀C, hN₀cop, hK⟩ := u3_K0_pComplement_core hc hP hDcyc hxD hxo
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (N₀ : Set G) := by
    intro c hc'
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hN₀C c (hP hc') n hn, fun hn => ?_⟩
    have h1 := hN₀C c⁻¹ (Subgroup.inv_mem _ (hP hc')) _ hn
    simpa [mul_assoc] using h1
  have hprod : ((P : Subgroup G) ⊔ N₀ : Subgroup G) = ((P : Subgroup G) : Set G) * (N₀ : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hPN
  have hTK : u3T P x J ⊔ u3K0 p x J ≤ (P : Subgroup G) ⊔ N₀ := by
    refine sup_le (hTP.trans le_sup_left) ?_
    intro k hk
    obtain ⟨n, hn, d, hd, rfl⟩ := hK k hk
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hn) (Subgroup.mem_sup_left hd.1)
  have hPTK : (P : Subgroup G) ≤ u3T P x J ⊔ u3K0 p x J :=
    hdec.trans (sup_le_sup_left inf_le_right _)
  refine ⟨(M ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ N₀, hPW, inf_le_left, ?_, ?_, ?_⟩
  · intro c hcW n hn
    exact ⟨(M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem
      ((M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem hcW hn.1)
      ((M ⊓ Subgroup.centralizer ({x} : Set G)).inv_mem hcW), hN₀C c hcW.2 n hn.2⟩
  · intro c hcW q hq
    have hle : (P : Subgroup G) ⊔ (M ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ N₀ ≤
        ((P : Subgroup G) ⊔ (M ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ N₀).comap
          (MulAut.conj c).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro a ha
        have hcaW : c * a * c⁻¹ ∈ M ⊓ Subgroup.centralizer ({x} : Set G) :=
          (M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem
            ((M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem hcW (hPW ha))
            ((M ⊓ Subgroup.centralizer ({x} : Set G)).inv_mem hcW)
        have hnorm := u3_W_le_normalizer_core hS hD1 hU0 hc h2 hTexp hmax hcW
        have hcaTK : c * a * c⁻¹ ∈ u3T P x J ⊔ u3K0 p x J :=
          (Subgroup.mem_normalizer_iff.mp hnorm a).mp (hPTK ha)
        have hcaPN : c * a * c⁻¹ ∈ ((P : Subgroup G) ⊔ N₀ : Subgroup G) := hTK hcaTK
        have hcaPN' : c * a * c⁻¹ ∈ ((P : Subgroup G) : Set G) * (N₀ : Set G) := by
          rw [← hprod]; exact hcaPN
        obtain ⟨a', ha', n', hn', hEq⟩ := hcaPN'
        have hn'W : n' ∈ M ⊓ Subgroup.centralizer ({x} : Set G) := by
          have : n' = a'⁻¹ * (c * a * c⁻¹) := by rw [← hEq]; simp
          rw [this]
          exact (M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem
            ((M ⊓ Subgroup.centralizer ({x} : Set G)).inv_mem (hPW ha')) hcaW
        show c * a * c⁻¹ ∈ (P : Subgroup G) ⊔ (M ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ N₀
        rw [← hEq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha') (Subgroup.mem_sup_right ⟨hn'W, hn'⟩)
      · intro n hn
        have hcn : c * n * c⁻¹ ∈ (M ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ N₀ :=
          ⟨(M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem
            ((M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem hcW hn.1)
            ((M ⊓ Subgroup.centralizer ({x} : Set G)).inv_mem hcW), hN₀C c hcW.2 n hn.2⟩
        exact Subgroup.mem_sup_right hcn
    exact hle hq
  · intro n hn
    exact hN₀cop n hn.2

theorem u3_centSeries_gen (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J) (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) (hTstr : TypeTStruct p P x J) (hmax : TypeBorelMax Typ p) (hpd : PGroupData p (P : Subgroup G) (u3T P x J) ((P : Subgroup G) ⊓ u3K0 p x J) x) :
    ∃ N : Subgroup G, CentSeries p (M ⊓ Subgroup.centralizer ({x} : Set G)) (P : Subgroup G) N :=
  u3_centSeries_core hS hD1 hU0 hc hP (two_le_pRank_of_typeTStruct hc hTstr) hTstr.2.1 hmax hpd.D_cyc
    hpd.x_mem hpd.x_ord hpd.sup_eq.ge

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
