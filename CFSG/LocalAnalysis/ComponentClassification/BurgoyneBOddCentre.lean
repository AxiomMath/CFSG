module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBTypeInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSU4Lift
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LieType.Steinberg.CentralExt.E6E7Multiplier
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.GH74.Orders.LieType
public import CFSG.Adapters.TauCetiExceptional.ReeCatalog
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped MatrixGroups

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]

theorem false_of_cover_center_pow {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {G : Type} [Group G] [Finite G] (hG : IsQuasisimple G)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* G),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : G →* E, ∀ x, π (s x) = x)
    {β : G →* (rhoZ K).range} (hβ : β.range = (liftHom K).range) {m : ℕ} (hm : Odd m)
    (hZ : ∀ z ∈ center G, z ^ m = 1) : False := by
  obtain ⟨hq, -, -, -, -, -, -, -, -, -, -, -, -, hcZ, -, hc2, -⟩ := id hH
  obtain ⟨α, -, hαs, -⟩ := exists_cover K hsplit hq hβ
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hnt : ∃ k, α k ≠ 1 := by
    obtain ⟨k, hk⟩ := hαs c
    exact ⟨k, by rw [hk]; exact hc1⟩
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hG hnt
  rw [CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hG hαs hker] at hcZ
  obtain ⟨z, hz, rfl⟩ := hcZ
  have hcm : α z ^ m = 1 := by rw [← map_pow, hZ z hz, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hcm
  rw [hc2] at hdvd
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hdvd)

theorem range_socle_comp {G T : Type} [Group G] [Group T] (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
    (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* T) {π : G →* T}
    (hπ : Function.Surjective π) :
    ((GeneralizedFitting.subgroup (rhoZ K).range).subtype.comp
      (θ.symm.toMonoidHom.comp π)).range = (liftHom K).range := by
  rw [liftHom_range_eq K hq hsimple hnab]
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact (θ.symm (π g)).2
  · intro x hx
    obtain ⟨g, hg⟩ := hπ (θ ⟨x, hx⟩)
    refine ⟨g, ?_⟩
    change ((θ.symm (π g) : GeneralizedFitting.subgroup (rhoZ K).range) : (rhoZ K).range) = x
    rw [hg, MulEquiv.symm_apply_apply]

theorem false_of_PSL_odd {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {n p' f' : ℕ} (hp2' : p' ≠ 2) (hodd : Odd n)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) .PSL n p' f') : False := by
  obtain ⟨hq, hM4, -⟩ := id hH
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  obtain ⟨hp, hf, hn2⟩ : p'.Prime ∧ 1 ≤ f' ∧ 2 ≤ n := by
    rcases hL with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact ⟨h.1, h.2.1, h.2.2.1⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  obtain ⟨F, _, _, hFc, ⟨θ⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have : Fintype F := Fintype.ofFinite F
  have : Fact p'.Prime := ⟨hp⟩
  have : CharP F p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p']; exact hp2'
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hn3 : 3 ≤ m + 1 := by obtain ⟨k, hk⟩ := hodd; omega
  have hG := CatalogueBGeneralLinear.specialLinear_quasisimple (m + 1) F (by omega)
    (Or.inl (by omega)) (Or.inl (by omega))
  refine false_of_cover_center_pow K hH hG ?_
    (range_socle_comp K hq hsimple hnab θ (LinearFlag.proj_surjective (m + 1) F)) hodd ?_
  · intro E _ _ π hπ hker h2
    obtain ⟨s, hs, -⟩ := CFSG.LieType.Steinberg.sl_central_two_extension_splitting m hF hπ hker h2
    exact ⟨s, hs⟩
  · intro z hz
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
    rw [Fintype.card_fin] at hr
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow, hr, map_one,
      Matrix.SpecialLinearGroup.coe_one]

theorem false_of_PSU_odd {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {n p' f' : ℕ} (hp2' : p' ≠ 2) (hodd : Odd n)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) .PSU n p' f') : False := by
  obtain ⟨hq, hM4, -⟩ := id hH
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  rcases hL with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨⟨hp, hf, hn3, -⟩, K₀, _, _, hKc, ⟨θ⟩⟩ := hcl
  have h : UnitaryFieldData p' f' K₀ := ⟨hp, hf, by rw [hKc, ← pow_mul, mul_comm]⟩
  have : Fact p'.Prime := ⟨hp⟩
  have := h.charP
  have hnq : (n, p' ^ f') ≠ (3, 2) := by
    intro h32
    have h2 : p' ^ f' = 2 := congrArg Prod.snd h32
    have hp2 : p' ∣ 2 := h2 ▸ dvd_pow_self p' (by omega)
    exact hp2' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2)
  obtain ⟨hG, hZG⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    h.card_eq_sq hn3 hnq
  refine false_of_cover_center_pow K hH hG
    (statedSU_central_two_splitting h.card_eq_sq hp2' (by omega))
    (range_socle_comp K hq hsimple hnab θ projH_surjective) hodd ?_
  intro z hz
  rw [hZG] at hz
  obtain ⟨r, hr⟩ := hz
  have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU z.2
  have hzr : ((z : GL (Fin n) K₀) : Matrix (Fin n) (Fin n) K₀) =
      Matrix.scalar (Fin n) (r : K₀) := by
    have h' := congrArg Units.val hr
    rw [Matrix.GeneralLinearGroup.coe_scalar] at h'
    exact h'.symm
  rw [hzr, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hzr, ← map_pow, hdet, map_one, Subgroup.coe_one,
    Units.val_one]

theorem exceptionalOrders_twistedE6 {p f : ℕ} (hp2 : p ≠ 2) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .twistedE6 0 p f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem odd_card_multiplier_twisted {τ : StatedLieTag} {p f : ℕ}
    (hτ : τ = .twistedE6 ∨ τ = .trialityD4 ∨ τ = .twistedG2) (hp2 : p ≠ 2) :
    Odd (Nat.card (CFSG.Blueprint.Multiplier.generic τ 0 p f ×
      CFSG.Blueprint.Multiplier.exceptional τ 0 p f)) := by
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ _),
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ _),
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ _),
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ _),
    Nat.card_zmod, Nat.card_zmod, Nat.card_zmod, Nat.card_zmod]
  rcases hτ with rfl | rfl | rfl
  · rw [exceptionalOrders_twistedE6 hp2, show CFSG.Blueprint.Multiplier.genericOrders
      .twistedE6 0 p f = (Nat.gcd 3 (p ^ f + 1), 1) from rfl]
    simp only [mul_one]
    exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)
  · exact odd_one
  · exact odd_one

theorem center_eq_bot_of_odd_multiplier {L S : Type} [Group L] [Finite L] [Group S]
    (hL : IsQuasisimple L) (h2 : IsPGroup 2 (center L)) (q : L →* S)
    (hq : Function.Surjective q) (hker : q.ker = center L)
    (hodd : Odd (Nat.card (CFSG.Open.griessHopfMultiplier S))) : center L = ⊥ := by
  have : Group.IsPerfect L := hL.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd := Subgroup.card_dvd_of_surjective
    (f := CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hq (hker ▸ le_rfl))
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq (hker ▸ le_rfl))
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv,
    hker] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2dvd.trans hdvd))
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk


theorem false_of_E6 {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {n p' f' : ℕ} (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) .E6 n p' f') : False := by
  obtain ⟨hq, hM4, -⟩ := id hH
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
  obtain ⟨F, _, _, hF, ⟨θ⟩⟩ := nonempty_mulEquiv_adjointGroup .E6
    (hm.2 : UntwistedChevalleyModel _ .E6 (p' ^ f'))
  have hFc : ringChar F ≠ 2 :=
    CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hm.1.1 hp2' hF
  obtain ⟨hcard, -⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 F
  have : Finite (Module.End F (Fin CFSG.LieType.Steinberg.Minuscule.e6Data.d →₀ F)) :=
    Module.finite_of_finite F
  have : Finite (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup F) := inferInstance
  have hm : Odd (Nat.card (center (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup F))) := by
    rw [hcard]
    exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)
  have hZ : ∀ z ∈ center (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup F),
      z ^ Nat.card (center (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup F)) = 1 :=
    fun z hz => congrArg Subtype.val
      (pow_card_eq_one' (G := center (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup F))
        (x := ⟨z, hz⟩))
  refine false_of_cover_center_pow K hH (CFSG.LieType.CurtisTits.isQuasisimple_e6 F) ?_
    (range_socle_comp K hq hsimple hnab θ
      (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective F)) hm hZ
  intro E _ _ π hπ hker h2
  obtain ⟨s, hs, -⟩ :=
    CFSG.LieType.Steinberg.e6_central_two_extension_splitting hFc hπ hker h2
  exact ⟨s, hs⟩

theorem false_of_adjoint {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {τ : StatedLieTag} {n p' f' : ℕ}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E8) (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) τ n p' f') : False := by
  obtain ⟨hq, hM4, -⟩ := id hH
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  have hgen : ∀ {τ' : Tag} {F : Type} [Field F] [Finite F],
      (GeneralizedFitting.subgroup (rhoZ K).range ≃* adjointGroup τ' F) →
      (∀ (E : Type) [Group E] [Finite E] (π : E →* adjointGroup τ' F),
        Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
          ∃ s : adjointGroup τ' F →* E, ∀ x, π (s x) = x) → False := by
    intro τ' F _ _ θ hsplit
    have : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range) := hsimple
    have hG := LocalCores.isQuasisimple_of_mulEquiv θ
      (LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
    refine false_of_cover_center_pow K hH hG hsplit
      (range_socle_comp K hq hsimple hnab θ (π := MonoidHom.id _) fun x => ⟨x, rfl⟩) odd_one ?_
    intro z hz
    rw [center_adjointGroup_eq_bot, mem_bot] at hz
    rw [hz, one_pow]
  rcases hτ with rfl | rfl | rfl
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    obtain ⟨F, _, _, hF, ⟨θ⟩⟩ := nonempty_mulEquiv_adjointGroup .G2
      (hm.2 : UntwistedChevalleyModel _ .G2 (p' ^ f'))
    have hFc := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hm.1.1 hp2' hF
    exact hgen θ fun E _ _ π hπ hker h2 =>
      (CFSG.LieType.Steinberg.g2_central_two_extension_splitting hFc hπ hker h2).imp
        fun _ h => h.1
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    obtain ⟨F, _, _, hF, ⟨θ⟩⟩ := nonempty_mulEquiv_adjointGroup .F4
      (hm.2 : UntwistedChevalleyModel _ .F4 (p' ^ f'))
    have hFc := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hm.1.1 hp2' hF
    exact hgen θ fun E _ _ π hπ hker h2 =>
      (CFSG.LieType.Steinberg.f4_central_two_extension_splitting hFc hπ hker h2).imp
        fun _ h => h.1
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    obtain ⟨F, _, _, hF, ⟨θ⟩⟩ := nonempty_mulEquiv_adjointGroup .E8
      (hm.2 : UntwistedChevalleyModel _ .E8 (p' ^ f'))
    have hFc := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hm.1.1 hp2' hF
    exact hgen θ fun E _ _ π hπ hker h2 =>
      (CFSG.LieType.Steinberg.e8_central_two_extension_splitting hFc hπ hker h2).imp
        fun _ h => h.1



theorem false_of_twisted (hGA : GriessMultipliersAllModels) {t : J} {Y : Subgroup J}
    {c : K ⧸ pPrimeCore 2 K} (hH : PropBHyp J K t Y c) {τ : StatedLieTag} {n p' f' : ℕ}
    (hτ : τ = .twistedE6 ∨ τ = .trialityD4 ∨ τ = .twistedG2) (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) τ n p' f') : False := by
  obtain ⟨hq, hM4, -, -, -, -, -, -, -, -, -, -, -, hcZ, -, hc2, -⟩ := id hH
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  have hmod : CFSG.Models.LieModel (GeneralizedFitting.subgroup (rhoZ K).range) τ 0 p' f' := by
    rcases hL with ⟨ht', -⟩ | ⟨h0, ht', he⟩ | ⟨h0, ht', hr⟩ | ⟨-, ht', -⟩
    · rcases hτ with rfl | rfl | rfl <;> exact absurd ht' (by decide)
    · exact ⟨he.1, Or.inr ⟨rfl, CFSG.TauCetiBridge.exists_index_of_exceptional
        CFSG.TauCetiBridge.typewiseBridges he.1.1 hp2' (.inl ⟨ht', he⟩)⟩⟩
    · exact ⟨hr.1, Or.inr ⟨rfl, CFSG.TauCetiBridge.exists_index_of_exceptional
        CFSG.TauCetiBridge.typewiseBridges hr.1.1 hp2' (.inr ⟨ht', hr⟩)⟩⟩
    · rcases hτ with rfl | rfl | rfl <;> exact absurd ht' (by decide)
  obtain ⟨-, ⟨eM⟩⟩ := hGA _ τ 0 p' f' hmod
  have hodd : Odd (Nat.card (CFSG.Open.griessHopfMultiplier
      (GeneralizedFitting.subgroup (rhoZ K).range))) := by
    rw [Nat.card_congr eM.toEquiv]
    exact odd_card_multiplier_twisted hτ hp2'
  have hrange := liftHom_range_eq K hq hsimple hnab
  let qL : K ⧸ pPrimeCore 2 K →* GeneralizedFitting.subgroup (rhoZ K).range :=
    (liftHom K).codRestrict _ fun x => hrange ▸ ⟨x, rfl⟩
  have hqs : Function.Surjective qL := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hqk : qL.ker = center (K ⧸ pPrimeCore 2 K) := by
    rw [← ker_liftHom K hq]
    ext x
    simp only [MonoidHom.mem_ker, qL]
    exact Subtype.ext_iff
  have hbot := center_eq_bot_of_odd_multiplier hq (isPGroup_center K) qL hqs hqk hodd
  rw [hbot, mem_bot] at hcZ
  rw [hcZ, orderOf_one] at hc2
  exact absurd hc2 (by norm_num)

end CFSG.ComponentClassification.Burgoyne.B
