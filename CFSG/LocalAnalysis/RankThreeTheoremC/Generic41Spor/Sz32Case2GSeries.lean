module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2GenDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialCases
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointSz32
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Cor47
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Burnside
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2TorusA
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfig
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Decomp
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.BorelTorus
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Torus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0 CentSeries)

theorem szh2_normal_pgroup_image {p : ℕ} [Fact p.Prime] {Γ Λ : Type*} [Group Γ] [Finite Γ] [Group Λ]
    (φ : Γ →* Λ) (Sy : Sylow p Γ) (Γ₁ : Subgroup Γ) [Γ₁.Normal]
    (h : ∀ γ ∈ Γ₁, ∃ k : ℕ, (φ γ) ^ (p ^ k) = 1) :
    ∀ γ ∈ Γ₁, ∃ q ∈ (Sy : Subgroup Γ), φ γ = φ q := by
  intro γ hγ
  have hφ' : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  haveI : (Γ₁.map φ.rangeRestrict).Normal := Subgroup.Normal.map inferInstance _ hφ'
  have hp' : IsPGroup p (Γ₁.map φ.rangeRestrict) := by
    rintro ⟨_, g, hg, rfl⟩
    obtain ⟨k, hk⟩ := h g hg
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hk
  have hle := hp'.le_sylow_of_normal (Sy.mapSurjective hφ')
  have hmem : φ.rangeRestrict γ ∈ ((Sy : Subgroup Γ).map φ.rangeRestrict) := by
    have := hle (Subgroup.mem_map_of_mem φ.rangeRestrict hγ)
    simpa using this
  obtain ⟨q, hq, hqγ⟩ := hmem
  exact ⟨q, hq, congrArg Subtype.val hqγ.symm⟩


section MJ

variable {G : Type} [Group G] [Finite G]

theorem szh2_isPGroup_zpowers {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] {g : Y}
    {k : ℕ} (hg : g ^ (p ^ k) = 1) : IsPGroup p (Subgroup.zpowers g) := by
  obtain ⟨m, -, hm'⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hg)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm'])

theorem szh2_pElement_MJ {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    {x : G} {J : Subgroup G} (hS : Setting G) (hD1 : TheoremD1 G) (hc : PointConfig Typ G p P M x J)
    (hNJ : ∀ n ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G), n ∈ J → n ∈ M)
    (hmax : CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.TypeBorelMax Typ p) :
    ∀ g ∈ M ⊓ J, (∃ k : ℕ, g ^ (p ^ k) = 1) → g ∈ u3T P x J ⊔ rankThreePrimeCore p J := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hOM : rankThreePrimeCore p J ≤ M :=
    (u3main_core_facts hS hD1 hc.sigma hc.core hc.generic hc.le_cent hc.cent_le).1
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ, honto⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.u3_normalizer_onto_gen hc
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
    exact ⟨⟨n, hnJ⟩, hNJ n hnN.1 hnJ, hψn⟩
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
    have hzp : IsPGroup p (Subgroup.zpowers (ψ ⟨g, hgJ⟩)) := szh2_isPGroup_zpowers hp hpe
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

end MJ


section NJ

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem szh2_mem_normalizer_sup {A B : Subgroup G} {n : G}
    (hA : n ∈ Subgroup.normalizer (A : Set G)) (hB : n ∈ Subgroup.normalizer (B : Set G)) :
    n ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem szh2_NJ_le_M (hS : Setting G) (hU0 : FullCoreLocal G) (hc : PointConfig IsSz32Type G 5 P M x J)
    {a c y : G} (hP : Sz32Struct P x J a c y) :
    ∀ n ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G), n ∈ J → n ∈ M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro n hn hnJ
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hpres := hP.pres_P
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hxP : x ∈ (P : Subgroup G) :=
    (Subgroup.zpowers_le.mpr hpres.c_mem) hpres.x_mem
  have hRP : u3T P x J ⊔ Subgroup.zpowers x ≤ (P : Subgroup G) :=
    sup_le hTP (Subgroup.zpowers_le.mpr hxP)
  have hZR : sz32Z a c ≤ u3T P x J ⊔ Subgroup.zpowers x := by
    refine sup_le ?_ ?_
    · refine le_trans ?_ le_sup_left
      rw [Subgroup.zpowers_le, ← hP.decomp.T_eq]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 5
    · refine le_trans ?_ le_sup_right
      rw [← hP.facts.x_eq]
  have h2 : 2 ≤ CFSG.Open.pRank 5 (u3T P x J ⊔ Subgroup.zpowers x) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.le_pRank_of_elemAbelian_card hZR hP.facts.Z_elem hP.facts.Z_card
  have hnx : n ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    have hnC : n ∈ Subgroup.centralizer ({x} : Set G) := hc.le_cent hnJ
    rw [Subgroup.mem_centralizer_singleton_iff] at hnC
    have hxx : n * x * n⁻¹ = x := by rw [hnC]; group
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    simp [MulAut.conj_apply, hxx]
  have hnR := szh2_mem_normalizer_sup hn hnx
  exact normalizer_le_of_le_of_two_le_pRank hS hU0 hc.sigma hc.core
    (P.isPGroup'.to_le hRP) (hRP.trans hPM) h2 hnR

end NJ


section Pelt

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial (SignalizerTrivialOn)

theorem szh2_pow_apply_eq {Q : Type*} [Group Q] (h : MulAut Q) {s : Q} (hs : h s = s) (n : ℕ) :
    (h ^ n) s = s := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hs, ih]

theorem szh2_pelt {p : ℕ} [Fact p.Prime] {Q : Type} [Group Q] [Finite Q] (hsig : SignalizerTrivialOn p Q)
    (S : Sylow p Q) (h : MulAut Q) (hh : ∀ s ∈ (S : Subgroup Q), h s = s) :
    ∃ k : ℕ, h ^ (p ^ k) = 1 := by
  have hp : p.Prime := Fact.out
  haveI : Finite (MulAut Q) := Finite.of_injective (fun f : MulAut Q => (f : Q → Q)) DFunLike.coe_injective
  have hn : orderOf h ≠ 0 := (orderOf_pos h).ne'
  obtain ⟨e, m, hm, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hpe : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hdvd : p ^ e ∣ orderOf h := ⟨m, hem⟩
  have hord : orderOf (h ^ (p ^ e)) = m := by
    rw [orderOf_pow_of_dvd hpe hdvd, hem, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hpe)]
  have hfix : ∀ s ∈ (S : Subgroup Q), (h ^ (p ^ e)) s = s := fun s hs => szh2_pow_apply_eq h (hh s hs) _
  have hV : Nat.Coprime p (Nat.card (Subgroup.zpowers (h ^ (p ^ e)))) := by
    rw [Nat.card_zpowers, hord]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have hcomm : ∀ g ∈ (S : Subgroup Q), Commute (MulAut.conj g : MulAut Q) (h ^ (p ^ e)) := by
    intro g hg
    ext q
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    rw [hfix g hg]
  have hnorm : ∀ g ∈ (S : Subgroup Q), ∀ w ∈ Subgroup.zpowers (h ^ (p ^ e)),
      MulAut.conj g * w * (MulAut.conj g)⁻¹ ∈ Subgroup.zpowers (h ^ (p ^ e)) := by
    intro g hg w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have := ((hcomm g hg).zpow_right n).eq
    rw [this, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n
  have hbot := hsig S _ hV hnorm
  have h1 : h ^ (p ^ e) = 1 := by
    have : h ^ (p ^ e) ∈ Subgroup.zpowers (h ^ (p ^ e)) := Subgroup.mem_zpowers _
    rwa [hbot, Subgroup.mem_bot] at this
  exact ⟨e, h1⟩

end Pelt


section Comm

variable {G : Type} [Group G] [Finite G]

theorem szh2_comm_cyclic {Q : Type*} [Group Q] (Sb : Subgroup Q) (s₀ : Q) (hs₀ : s₀ ∈ Sb)
    (hcyc : ∀ s ∈ Sb, ∃ m : ℤ, s = s₀ ^ m) (f g : MulAut Q) (hf : ∀ s ∈ Sb, f s ∈ Sb)
    (hg : ∀ s ∈ Sb, g s ∈ Sb) : ∀ s ∈ Sb, f (g s) = g (f s) := by
  intro s hs
  obtain ⟨m, rfl⟩ := hcyc s hs
  obtain ⟨i, hi⟩ := hcyc _ (hf s₀ hs₀)
  obtain ⟨j, hj⟩ := hcyc _ (hg s₀ hs₀)
  simp only [map_zpow, hi, hj, ← zpow_mul]
  congr 1
  ring

theorem szh2_sylow_subgroupOf {p : ℕ} [Fact p.Prime] (P : Sylow p G) {W : Subgroup G}
    (hPW : (P : Subgroup G) ≤ W) :
    ∃ T : Sylow p W, (T : Subgroup W) = (P : Subgroup G).subgroupOf W := by
  have h : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) W := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hPW, P.isPGroup', fun h =>
      P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hPW))⟩
  exact h.exists_sylow_eq_subgroupOf

theorem szh2_centSeries_of_comm {p : ℕ} {W P K₀ N₀ : Subgroup G} (hPW : P ≤ W)
    (hN₀W : ∀ c ∈ W, ∀ n ∈ N₀, c * n * c⁻¹ ∈ N₀)
    (hN₀cop : ∀ n ∈ N₀, Nat.Coprime p (orderOf n))
    (hK : ∀ k ∈ K₀, ∃ n ∈ N₀, ∃ d ∈ P ⊓ K₀, k = n * d)
    (hcomm : ∀ γ ∈ W, ∀ b ∈ P, ∃ p₁ ∈ P, ∃ k ∈ K₀, γ * b * γ⁻¹ * b⁻¹ = p₁ * k) :
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CentSeries p W P (W ⊓ N₀) := by
  refine ⟨hPW, inf_le_left, ?_, ?_, ?_⟩
  · intro c hcW n hn
    exact ⟨W.mul_mem (W.mul_mem hcW hn.1) (W.inv_mem hcW), hN₀W c hcW n hn.2⟩
  · intro c hcW q hq
    have hle : P ⊔ W ⊓ N₀ ≤ (P ⊔ W ⊓ N₀).comap (MulAut.conj c).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro b hb
        obtain ⟨p₁, hp₁, k, hk, hδ⟩ := hcomm c hcW b hb
        have hkW : k ∈ W := by
          have : k = p₁⁻¹ * (c * b * c⁻¹ * b⁻¹) := by rw [hδ]; group
          rw [this]
          exact W.mul_mem (W.inv_mem (hPW hp₁))
            (W.mul_mem (W.mul_mem (W.mul_mem hcW (hPW hb)) (W.inv_mem hcW)) (W.inv_mem (hPW hb)))
        obtain ⟨n, hn, d, hd, hkd⟩ := hK k hk
        have hnW : n ∈ W := by
          have : n = k * d⁻¹ := by rw [hkd]; group
          rw [this]
          exact W.mul_mem hkW (W.inv_mem (hPW hd.1))
        have hcb : c * b * c⁻¹ = p₁ * n * d * b := by
          have h1 : c * b * c⁻¹ = (c * b * c⁻¹ * b⁻¹) * b := by group
          rw [h1, hδ, hkd]; group
        show c * b * c⁻¹ ∈ P ⊔ W ⊓ N₀
        rw [hcb]
        have hp₁' : p₁ ∈ P ⊔ W ⊓ N₀ := Subgroup.mem_sup_left hp₁
        have hn' : n ∈ P ⊔ W ⊓ N₀ := Subgroup.mem_sup_right (show n ∈ W ⊓ N₀ from ⟨hnW, hn⟩)
        have hd' : d ∈ P ⊔ W ⊓ N₀ := Subgroup.mem_sup_left hd.1
        have hb' : b ∈ P ⊔ W ⊓ N₀ := Subgroup.mem_sup_left hb
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hp₁' hn') hd') hb'
      · intro n hn
        have hcn : c * n * c⁻¹ ∈ W ⊓ N₀ :=
          ⟨W.mul_mem (W.mul_mem hcW hn.1) (W.inv_mem hcW), hN₀W c hcW n hn.2⟩
        exact Subgroup.mem_sup_right hcn
    exact hle hq
  · intro n hn
    exact hN₀cop n hn.2

end Comm


section CommMain

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

open scoped Pointwise

theorem szh2_comm (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hSz : Sz32Facts)
    (hSz' : Sz32OpenFacts) (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hP : Sz32Struct P x J a c y) :
    ∀ γ ∈ M ⊓ Subgroup.centralizer ({x} : Set G), ∀ b ∈ (P : Subgroup G),
      ∃ p₁ ∈ (P : Subgroup G), ∃ k ∈ u3K0 5 x J, γ * b * γ⁻¹ * b⁻¹ = p₁ * k := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  set W : Subgroup G := M ⊓ C with hW
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hPC : (P : Subgroup G) ≤ C := hP.le_cent
  have hPW : (P : Subgroup G) ≤ W := le_inf hPM hPC
  have hWC : W ≤ C := inf_le_right
  have hCN : C ≤ Subgroup.normalizer (J : Set G) := hc.cent_le
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hiso : ∀ (A B : Type) [Group A] [Group B], A ≃* B → IsSz32Type 5 A → IsSz32Type 5 B :=
    fun A B _ _ e h => ⟨h.1, h.2.imp fun _ hn => hn.map fun f => e.symm.trans f⟩
  obtain ⟨Q, iQ, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hOker : ∀ j : J, ψ j = 1 ↔ (j : G) ∈ rankThreePrimeCore 5 J := by
    intro j
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hZ : Subgroup.center Q = ⊥ :=
    u3main_center_bot (CFSG.AGLEmbedding.glbPrimeCore_le 5 J) hc.perfect hc.lt hc.minimal ψ hψ hker
  have hsig : CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial.SignalizerTrivialOn 5 Q :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.typeSigTrivOn_of_X hc.prime hiso
      (fun X _ _ K h => hSz.sigTriv X K h)) Q hQ hZ
  obtain ⟨ρ, hρ⟩ := sps_exists_action (p := 5) hCN ψ hψ hker
  have hker1 : ∀ (e : G) (heC : e ∈ C), ρ ⟨e, heC⟩ = 1 → e ∈ u3K0 5 x J := by
    intro e heC hmem
    refine ⟨heC, hCN heC, fun j hj => ?_⟩
    have hjj : e * j * e⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hCN heC) j).mp hj
    have h1 := hρ ⟨e, heC⟩ ⟨j, hj⟩ hjj
    rw [hmem, MulAut.one_apply] at h1
    have h2 : ψ (⟨e * j * e⁻¹, hjj⟩ * ⟨j, hj⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h1, mul_inv_cancel]
    have := (hOker _).mp h2
    simpa using this
  have hSylJ : CFSG.ABGLocalTools.IsSylowOf 5 (u3T P x J) J :=
    hc.generic.2.2.1.inf_of_le_normalizer hc.le_cent hc.cent_le
  obtain ⟨Tsyl, hTsyl⟩ := hSylJ.exists_sylow_eq_subgroupOf
  let Tsyl' : Sylow 5 Q := Tsyl.mapSurjective hψ
  have hTsyl' : (Tsyl' : Subgroup Q) = ((u3T P x J).subgroupOf J).map ψ := by
    rw [← hTsyl]; exact Sylow.coe_mapSurjective hψ Tsyl
  have hmax : CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.TypeBorelMax IsSz32Type 5 :=
    fun K _ _ hK S H hH => hSz'.maximal K hK S H hH
  have hMJ := szh2_pElement_MJ hS hD1 hc (szh2_NJ_le_M hS hU0 hc hP) hmax
  have hJN : J ≤ Subgroup.normalizer (rankThreePrimeCore 5 J : Set G) :=
    (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 5 J).2.1
  have hpres : ∀ (γ : G) (hγ : γ ∈ W), ∀ s ∈ (Tsyl' : Subgroup Q),
      ρ ⟨γ, hWC hγ⟩ s ∈ (Tsyl' : Subgroup Q) := by
    intro γ hγ s hs
    rw [hTsyl'] at hs ⊢
    obtain ⟨t', ht', rfl⟩ := hs
    have htT : (t' : G) ∈ u3T P x J := ht'
    have htP : (t' : G) ∈ (P : Subgroup G) := hTP htT
    have hconj : γ * (t' : G) * γ⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hCN (hWC hγ)) t').mp t'.2
    have hconjM : γ * (t' : G) * γ⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem hγ.1 (hPM htP)) (M.inv_mem hγ.1)
    have hp5 : ∃ k : ℕ, (γ * (t' : G) * γ⁻¹) ^ (5 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨(t' : G), htP⟩
      refine ⟨k, ?_⟩
      have : (t' : G) ^ (5 ^ k) = 1 := congrArg Subtype.val hk
      rw [conj_pow, this]
      simp
    have hmem := hMJ _ ⟨hconjM, hconj⟩ hp5
    have hTN : u3T P x J ≤ Subgroup.normalizer (rankThreePrimeCore 5 J : Set G) := hTJ.trans hJN
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at hmem
    obtain ⟨t₁, ht₁, o, ho, hto⟩ := hmem
    have ht₁J : t₁ ∈ J := hTJ ht₁
    have hoJ : o ∈ J := CFSG.AGLEmbedding.glbPrimeCore_le 5 J ho
    rw [hρ ⟨γ, hWC hγ⟩ t' hconj]
    refine ⟨⟨t₁, ht₁J⟩, ht₁, ?_⟩
    have e1 : (⟨γ * (t' : G) * γ⁻¹, hconj⟩ : J) = ⟨t₁, ht₁J⟩ * ⟨o, hoJ⟩ := Subtype.ext hto.symm
    rw [e1, map_mul, (hOker ⟨o, hoJ⟩).mpr ho, mul_one]
  have haJ : a ∈ J := hP.decomp.a_J
  have hcyc : ∀ s ∈ (Tsyl' : Subgroup Q), ∃ m : ℤ, s = (ψ ⟨a, haJ⟩) ^ m := by
    intro s hs
    rw [hTsyl'] at hs
    obtain ⟨t', ht', rfl⟩ := hs
    have htT : (t' : G) ∈ Subgroup.zpowers a := by rw [hP.decomp.T_eq]; exact ht'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp htT
    refine ⟨m, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hm.symm)
  have hs₀ : ψ ⟨a, haJ⟩ ∈ (Tsyl' : Subgroup Q) := by
    rw [hTsyl']
    refine ⟨⟨a, haJ⟩, ?_, rfl⟩
    show a ∈ u3T P x J
    rw [← hP.decomp.T_eq]
    exact Subgroup.mem_zpowers a
  let φ : ↥W →* MulAut Q := ρ.comp (Subgroup.inclusion hWC)
  have hφ : ∀ γ : ↥W, φ γ = ρ ⟨γ, hWC γ.2⟩ := fun γ => rfl
  have hpres' : ∀ (γ : ↥W), ∀ s ∈ (Tsyl' : Subgroup Q), φ γ s ∈ (Tsyl' : Subgroup Q) := by
    intro γ s hs
    rw [hφ]
    exact hpres γ γ.2 s hs
  let Γ₁ : Subgroup ↥W :=
    { carrier := {γ | ∀ s ∈ (Tsyl' : Subgroup Q), φ γ s = s}
      mul_mem' := by
        intro u v hu hv s hs
        rw [map_mul, MulAut.mul_apply, hv s hs, hu s hs]
      one_mem' := by
        intro s hs
        simp
      inv_mem' := by
        intro u hu s hs
        have h2 : (φ u)⁻¹ (φ u s) = s := by simp
        rw [hu s hs] at h2
        rw [map_inv]
        exact h2 }
  haveI hΓ₁n : Γ₁.Normal := ⟨fun u hu v s hs => by
    show φ (v * u * v⁻¹) s = s
    have hs' : φ v⁻¹ s ∈ (Tsyl' : Subgroup Q) := hpres' v⁻¹ s hs
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hu _ hs', ← MulAut.mul_apply,
      ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]⟩
  have hΓ₁p : ∀ u ∈ Γ₁, ∃ k : ℕ, (φ u) ^ (5 ^ k) = 1 := fun u hu =>
    szh2_pelt hsig Tsyl' (φ u) hu
  obtain ⟨Sy, hSy⟩ := szh2_sylow_subgroupOf P hPW
  have hmain := szh2_normal_pgroup_image φ Sy Γ₁ hΓ₁p
  intro γ hγ b hb
  have hδW : γ * b * γ⁻¹ * b⁻¹ ∈ W :=
    W.mul_mem (W.mul_mem (W.mul_mem hγ (hPW hb)) (W.inv_mem hγ)) (W.inv_mem (hPW hb))
  have hδΓ : (⟨γ * b * γ⁻¹ * b⁻¹, hδW⟩ : ↥W) ∈ Γ₁ := by
    intro s hs
    let g₁ : ↥W := ⟨γ, hγ⟩
    let b₁ : ↥W := ⟨b, hPW hb⟩
    have e1 : (⟨γ * b * γ⁻¹ * b⁻¹, hδW⟩ : ↥W) = g₁ * b₁ * g₁⁻¹ * b₁⁻¹ := rfl
    have hu : φ b₁⁻¹ s ∈ (Tsyl' : Subgroup Q) := hpres' b₁⁻¹ s hs
    have hv : φ g₁⁻¹ (φ b₁⁻¹ s) ∈ (Tsyl' : Subgroup Q) := hpres' g₁⁻¹ _ hu
    have hcm := szh2_comm_cyclic (Tsyl' : Subgroup Q) (ψ ⟨a, haJ⟩) hs₀ hcyc (φ g₁) (φ b₁)
      (hpres' g₁) (hpres' b₁) _ hv
    rw [e1]
    simp only [map_mul, map_inv, MulAut.mul_apply] at hcm ⊢
    rw [hcm]
    simp
  obtain ⟨q, hq, hφq⟩ := hmain _ hδΓ
  rw [hSy] at hq
  have hqP : (q : G) ∈ (P : Subgroup G) := hq
  refine ⟨(q : G), hqP, (q : G)⁻¹ * (γ * b * γ⁻¹ * b⁻¹), ?_, by group⟩
  apply hker1 _ (hWC (W.mul_mem (W.inv_mem q.2) hδW))
  have e2 : (⟨(q : G)⁻¹ * (γ * b * γ⁻¹ * b⁻¹), hWC (W.mul_mem (W.inv_mem q.2) hδW)⟩ : ↥C) =
      Subgroup.inclusion hWC (q⁻¹ * ⟨γ * b * γ⁻¹ * b⁻¹, hδW⟩) := rfl
  rw [e2]
  show φ (q⁻¹ * ⟨γ * b * γ⁻¹ * b⁻¹, hδW⟩) = 1
  rw [map_mul, map_inv, ← hφq, inv_mul_cancel]

end CommMain

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
