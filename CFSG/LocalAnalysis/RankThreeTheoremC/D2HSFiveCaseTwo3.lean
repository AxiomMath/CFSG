module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2HSFiveOver3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2HSFiveCaseTwo3Card
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2FusionFocal3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwo
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveFaithful

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2
open scoped commutatorElement

@[expose] def KFactBlockRankOneOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    (∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L → IsElemAbelian 3 E →
      Nat.card E ≤ 3) →
    ¬ 5 ∣ Nat.card ↥(barM M L) ∧
    ∀ x ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      ∀ y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        x * y * x⁻¹ * y⁻¹ ∈
          barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

variable {G : Type} [Group G] [Finite G]

theorem d2HSFiveCaseTwo3_of (hHS : KFactHSFiveOver)
    (hloc : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hα : KFactThreeOrFiveDvd) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hX : D1NoXBlock3 G)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hMult : KFactHSMultiplier)
    (hO3 : KFactBlockThreeOrderThree) (hC5 : KFactBlockRankOneOut) : D2HSFiveCaseTwo3 G := by
  intro hS hD1' M hM hfc hthree p hp hp5 P A H R hMP hesc hmax Rbar K hRbar hK he hne L₀ hL₀ hL₀K
    hL₀N
  subst hp5
  have hglob : AGLGlobal G := aglGlobal_of_setting hS
  have hD1 : D1For G := d1For_of_setting hS
  have hNX : NoXBlockFor G := noXBlockFor_of_setting hX hS
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hpair, U, ⟨φ₀⟩, hout₀, h5L₀, L₁, hL₁, hne₀₁, hcomps, hnoE, hC₁5⟩ :=
    hsFiveCaseTwo_twoComponents hHS hloc hα h84 h85 h86 h93 hK2 hC3 hK5 hMult hO3 hglob hD1 hNX
      hesc hRbar hK he hne hL₀ hL₀K hL₀N fun _ => by
        have h1 := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) M hesc.maxTwoLocal_M.1
        rw [hS.rank] at h1
        exact h1
  obtain ⟨hL₁5, hL₁comm⟩ := hC5 G M _ L₁ hpair.isKGroup.1 hpair.asc81bHyp hL₁
    (hpair.nineThree_not_one h85 hNX hL₁).1 (hpair.not_isSylowTwoOf_inf h85 hNX hL₁) hnoE
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hMP
  have hM5 : 3 ≤ Open.pRank 5 M :=
    hP3.symm.le.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 5 Nat.prime_five hPM)
  obtain ⟨E₅', hE₅'M, hE₅', hE₅'c⟩ := exists_isElemAbelian_card_pow_of_le_pRank (p := 5) (k := 3)
    Nat.prime_five hM5
  have hE₅'p : IsPGroup 5 E₅' := fun x => ⟨1, Subtype.ext (by simpa using hE₅'.2 x x.2)⟩
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup 5 Nat.prime_five P M hPM E₅'
    hE₅'p hE₅'M
  set E'' : Subgroup G := E₅'.map (MulAut.conj (m : G)).toMonoidHom with hE''def
  have hE''M : E'' ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem m.2 (hE₅'M hx)) (M.inv_mem m.2)
  have hE''el : IsElemAbelian 5 E'' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 5 hE₅' _
  have hE''p : IsPGroup 5 E'' := fun x => ⟨1, Subtype.ext (by simpa using hE''el.2 x x.2)⟩
  have hE''c : Nat.card E'' = 5 ^ 3 := by
    rw [hE''def, Subgroup.card_map_of_injective (MulAut.conj (m : G)).injective]
    exact hE₅'c
  have hPcomm : (P : Subgroup G) ≤ ⁅M, M⁆ :=
    sylow_le_commutator_of_gamma_two hS hp hMP (hfc 5 hp P hMP)
  have hE''comm : E'' ≤ ⁅M, M⁆ := hm.trans hPcomm
  have hLnorm : ∀ g : ↥M ⧸ CFSG.pCore 2 ↥M,
      g ∈ Subgroup.normalizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro g
    have hc : IsComponentOf ((barM M L₁).map (MulAut.conj g).toMonoidHom) ⊤ :=
      isComponentOf_map_conj_top hL₁.component g
    rcases hcomps _ hc with h0 | h1
    · exfalso
      have hcard' : Nat.card ((barM M L₁).map (MulAut.conj g).toMonoidHom) =
          Nat.card (barM M L₁) := Subgroup.card_map_of_injective (MulAut.conj g).injective
      rw [h0] at hcard'
      exact hL₁5 (hcard' ▸ h5L₀)
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h1
  set Λb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
    barM M L₁ ⊔ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hΛdef
  have hcommΛ : ⁅M, M⁆ ≤ (Λb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ M := by
      rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
    refine ⟨⟨⁅a, b⁆, hab⟩, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨⁅a, b⁆, hab⟩ ∈ Λb
    have e1 : (⟨⁅a, b⁆, hab⟩ : ↥M) = ⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩)⁻¹ * (⟨b, hb⟩)⁻¹ := by
      apply Subtype.ext
      simp [commutatorElement_def]
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hL₁comm _ (hLnorm _) _ (hLnorm _)
  have hE''bar_c : Nat.card (barM M E'') = 5 ^ 3 :=
    (hpair.card_barM_of_isPGroup hE''M hE''p).trans hE''c
  have hE''bar : IsElemAbelian 5 (barM M E'') := by
    refine ⟨isMulCommutative_iff.mpr fun a b => ?_, ?_⟩
    · obtain ⟨_, ⟨ma, hma, rfl⟩⟩ := a
      obtain ⟨_, ⟨mb, hmb, rfl⟩⟩ := b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      have := hE''el.1
      have hc : (ma : G) * mb = mb * ma := by
        have h1 := congrArg Subtype.val
          (mul_comm' (⟨ma, Subgroup.mem_subgroupOf.mp hma⟩ : E'')
            ⟨mb, Subgroup.mem_subgroupOf.mp hmb⟩)
        simpa using h1
      exact Subtype.ext hc
    · rintro _ ⟨m, hm, rfl⟩
      rw [← map_pow]
      have : m ^ 5 = 1 := Subtype.ext (by simpa using hE''el.2 _ (Subgroup.mem_subgroupOf.mp hm))
      rw [this, map_one]
  have hEΛ : barM M E'' ≤ Λb := by
    rintro _ ⟨z, hz, rfl⟩
    have hzE : (z : G) ∈ E'' := Subgroup.mem_subgroupOf.mp hz
    obtain ⟨y, hy, hyz⟩ := hcommΛ (hE''comm hzE)
    have hyz' : y = z := Subtype.ext hyz
    rw [← hyz']
    exact hy
  obtain ⟨ρ, hρ⟩ := exists_hom_centerQuotient (barM M L₁) (barM M E'').subtype
    (fun e => hEΛ e.2)
  have hρ1 : ∀ w, ρ w = 1 := by
    intro w
    have h5 : (w : ↥M ⧸ CFSG.pCore 2 ↥M) ^ 5 = 1 := hE''bar.2 w w.2
    have hw5 : w ^ 5 = 1 := Subtype.ext (by simpa using h5)
    have h1 : orderOf (ρ w) ∣ 5 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hw5, map_one])
    have h2 : orderOf (ρ w) ∣ Nat.card (↥(barM M L₁) ⧸ Subgroup.center ↥(barM M L₁)) :=
      orderOf_dvd_natCard _
    have h3 : Nat.card (↥(barM M L₁) ⧸ Subgroup.center ↥(barM M L₁)) ∣
        Nat.card ↥(barM M L₁) := Subgroup.index_dvd_card _
    have hcop : Nat.Coprime 5 (Nat.card ↥(barM M L₁)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hL₁5
    have h4 : orderOf (ρ w) = 1 :=
      Nat.eq_one_of_dvd_coprimes (hcop.coprime_dvd_right (h2.trans h3)) h1 dvd_rfl
    exact orderOf_eq_one_iff.mp h4
  have hEC : barM M E'' ≤ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun e he => (hρ ⟨e, he⟩).mp (hρ1 ⟨e, he⟩)
  have hle := card_le_five_sq_of_centralizes_component hL₀.component hL₁.component hne₀₁ hcomps
    hC₁5 hout₀ φ₀ (by rw [hK.pRank_top]) hE''bar hEC
  rw [hE''bar_c] at hle
  norm_num at hle

end CFSG.LocalAnalysis.RankThreeTheoremC
