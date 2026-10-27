module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusLieOffCharAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs
public import CFSG.LieType.SeitzGeneration.LowNarrow
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCycExc
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.LieType.SeitzGeneration CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

set_option linter.unusedSectionVars false

theorem false_of_seitzException_of_rankOne {K : Type} [Group K] [Finite K]
    (d : TauCeti.ValidLieTypeIndex) (e : K ≃* Cat d)
    (hex : CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1)
    (hL82 : ¬ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q)
    (hL34 : ¬ IsLinThreeFourIndex d) (hone : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 1)
    {E : Subgroup (MulAut (Cat d))} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hinn : ¬ InnerPlane d 3 E) : False := by
  obtain ⟨dd, hv⟩ := d
  rcases hex with ⟨-, hcase⟩ | ⟨h5, -⟩
  · rcases hcase with ⟨q, hq2, hqe, hd⟩ | ⟨q, hq2, hqe, hd⟩ | ⟨q, hq2, hqe, hd⟩ |
        ⟨q, hq2, hqe, hd | hd⟩ | hd
    · exact hL82 ⟨q, hq2, hqe, hd⟩
    · exact hL34 ⟨q, hq2, hqe, hd⟩
    · have hd' : dd = .twistedA 3 q := hd
      subst hd'
      have := two_le_pRank_three_unitaryFour q hq2 hqe hv e
      omega
    · have hd' : dd = .B 3 q := hd
      subst hd'
      have := two_le_pRank_three_typeB 3 le_rfl q hq2 hqe hv e
      omega
    · have hd' : dd = .B 4 q := hd
      subst hd'
      have := two_le_pRank_three_typeB 4 (by norm_num) q hq2 hqe hv e
      omega
    · have hd' : dd = .tits := hd
      subst hd'
      exact hinn (le_range_conj_of_not_dvd_card_outer Nat.prime_three
        (not_dvd_card_outer_tits hv (MulEquiv.refl _) Nat.prime_three (by norm_num)) hE)
  · exact absurd h5 (by norm_num)

theorem gls3PlusCase_lie_of_offChar_ne (hOff : OffCharGen) (hOut : SeitzOuterLowN)
    (d : TauCeti.ValidLieTypeIndex) (h3 : d.1.characteristic ≠ 3)
    (hL82 : ¬ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q)
    (hL34 : ¬ IsLinThreeFourIndex d) : Gls3PlusCase (.lie d) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold Gls3PlusCase
  intro X _ _ _ K hKn hKs hnc hiso hKc P hP hΓ
  exfalso
  suffices hΓtop : gammaCore 3 1 ⊤ (P : Subgroup X) = ⊤ from by
    rw [hΓtop] at hΓ; exact lt_irrefl _ hΓ
  obtain ⟨e⟩ := hiso
  have e' : ↥K ≃* Cat d := e
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := hnc
  obtain ⟨a, b, hab⟩ := hnc
  have hnt : Nontrivial ↥K := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal (G := X) (p := 3) P (N := K)
  by_cases hTc : IsCyclic (T : Subgroup ↥K)
  ·
    have hall : ∀ T' : Sylow 3 ↥K, IsCyclic (T' : Subgroup ↥K) := fun T' => isCyclic_sylow_of T T' hTc
    have hone : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 1 :=
      pRank_le_one_of_isCyclic_sylow Nat.prime_three T hTc
    have hrk1 : RankLE1 3 (Cat d) := RankLE1.of_mulEquiv e' (RankLE1.of_pRank Nat.prime_three hone)
    obtain ⟨E₀, hE₀P, hE₀el, hE₀c⟩ := exists_elemAbelian_card_sq Nat.prime_three hP
    have hψ : Function.Injective (MulAut.conjNormal : X →* MulAut ↥K) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxc : x ∈ Subgroup.centralizer (K : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have := congrArg (fun f : MulAut ↥K => (f ⟨k, hk⟩ : X)) hx
        simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
        have h2 : x * k * x⁻¹ = k := this
        rw [mul_inv_eq_iff_eq_mul] at h2
        exact h2.symm
      rw [hKc] at hxc
      exact Subgroup.mem_bot.mp hxc
    have hmemK : ∀ (x : X) (k : ↥K), (MulAut.conjNormal : X →* MulAut ↥K) x = MulAut.conj k →
        x ∈ K := by
      intro x k hk
      have : (MulAut.conjNormal : X →* MulAut ↥K) x = (MulAut.conjNormal : X →* MulAut ↥K) (k : X) := by
        rw [hk]
        ext y
        simp [MulAut.conjNormal_apply, MulAut.conj_apply]
      rw [hψ this]
      exact k.2
    have hnotK : ¬ E₀ ≤ K := by
      intro hle
      set F : Subgroup ↥K := E₀.subgroupOf K with hF
      have hFel : CFSG.Open.IsElemAbelian 3 F := by
        refine ⟨⟨⟨?_⟩⟩, ?_⟩
        · rintro ⟨x, hx⟩ ⟨y, hy⟩
          apply Subtype.ext
          apply Subtype.ext
          have := congrArg Subtype.val (hE₀el.1.is_comm.comm ⟨(x : X), hx⟩ ⟨(y : X), hy⟩)
          exact this
        · intro x hx
          exact Subtype.ext (by simpa using hE₀el.2 (x : X) hx)
      have hFc : Nat.card F = 3 ^ 2 := by
        rw [← hE₀c]
        have hm : F.map K.subtype = E₀ := by
          rw [hF, Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.mpr hle
        rw [← hm, Subgroup.card_map_of_injective K.subtype_injective]
      have := le_pRank_of_elem (G := ↥K) (by norm_num) (le_top : F ≤ ⊤) hFel hFc
      omega
    let Ψ : X →* MulAut (Cat d) := ((MulAut.congr e').toMonoidHom).comp
      (MulAut.conjNormal : X →* MulAut ↥K)
    have hΨ : Function.Injective Ψ := (MulAut.congr e').injective.comp hψ
    have hEel : CFSG.Open.IsElemAbelian 3 (E₀.map Ψ) :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₀el Ψ
    have hEc : Nat.card (E₀.map Ψ) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective hΨ, hE₀c]
    have hinner : ¬ InnerPlane d 3 (E₀.map Ψ) := by
      intro hin
      apply hnotK
      intro x hx
      obtain ⟨c, hc⟩ := hin (Subgroup.mem_map_of_mem Ψ hx)
      have h1 : (MulAut.congr e') ((MulAut.conjNormal : X →* MulAut ↥K) x) =
          (MulAut.congr e') (MulAut.conj (e'.symm c)) := by
        have h2 := mulAut_congr_conj e' (e'.symm c)
        simp only [MulEquiv.apply_symm_apply] at h2
        have h3 : Ψ x = MulAut.conj c := hc.symm
        simpa [Ψ] using h3.trans h2.symm
      exact hmemK x _ ((MulAut.congr e').injective h1)
    have hplane : PlaneGen (E₀.map Ψ) := by
      by_cases hex : CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1
      · exact (false_of_seitzException_of_rankOne d e' hex hL82 hL34 hone hEel hinner).elim
      · exact hOut d 3 Nat.prime_three (by norm_num) (Ne.symm h3) hex (E₀.map Ψ) hEel hEc
          ⟨hinner, (hrk1.rankLE2), Or.inl hrk1⟩
    have hKγ : K ≤ gammaCore 3 1 ⊤ (P : Subgroup X) :=
      le_gammaCore_of_plane e' (P : Subgroup X) E₀ hE₀P hE₀el.2 hplane
    by_cases hT1 : (T : Subgroup ↥K) = ⊥
    ·
      exfalso
      have hndvd : ¬ 3 ∣ Nat.card ↥K := by
        intro hdvd
        have h1 := Sylow.card_eq_multiplicity T
        have h2 : 0 < (Nat.card ↥K).factorization 3 :=
          Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hdvd
        have h3' : Nat.card (T : Subgroup ↥K) = 1 := by rw [hT1]; simp
        rw [h1] at h3'
        have := Nat.one_lt_pow h2.ne' (by norm_num : 1 < 3)
        omega
      obtain ⟨f, hSz⟩ := (CFSG.RankThree.PartTwo.KFacts.KS14.three_dvd_card_or_suzukiModel_of_lie d
        (G := ↥K) e).resolve_left hndvd
      have hcyc := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} ↥K 2 f hSz).1.1
      let χ : E₀ →* Outer ↥K := (QuotientGroup.mk' (inner ↥K)).comp
        ((MulAut.conjNormal : X →* MulAut ↥K).comp E₀.subtype)
      have hχ : Function.Injective χ := by
        rw [injective_iff_map_eq_one]
        intro x hx
        have hx1 : (QuotientGroup.mk' (inner ↥K))
            ((MulAut.conjNormal : X →* MulAut ↥K) (x : X)) = 1 := hx
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
        obtain ⟨k, hk⟩ := hx1
        have hxK : (x : X) ∈ K := hmemK _ k hk.symm
        have hxP : (x : X) ∈ (P : Subgroup X) := hE₀P x.2
        have hmem : (⟨(x : X), hxK⟩ : ↥K) ∈ (T : Subgroup ↥K) := by
          rw [hT, Subgroup.mem_subgroupOf]; exact ⟨hxP, hxK⟩
        rw [hT1, Subgroup.mem_bot] at hmem
        have h1 : (x : X) = 1 := congrArg Subtype.val hmem
        exact Subtype.ext h1
      have := hcyc
      exact not_isCyclic_of_elemAbelian_card_sq hE₀el hE₀c (isCyclic_of_injective χ hχ)
    ·
      have hdvd : 3 ∣ Nat.card (T : Subgroup ↥K) := by
        obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp T.isPGroup')
        rcases n with _ | n
        · exfalso
          apply hT1
          apply Subgroup.eq_bot_of_card_eq
          simpa using hn
        · rw [hn]; exact dvd_pow_self 3 (Nat.succ_ne_zero n)
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
      have ht3 : ((t : ↥K) : X) ^ 3 = 1 := by
        have : (t : ↥K) ^ 3 = 1 := by
          have h3 : orderOf (t : ↥K) = 3 := by rw [Subgroup.orderOf_coe]; exact ht
          have := pow_orderOf_eq_one (t : ↥K)
          rwa [h3] at this
        exact congrArg Subtype.val this
      have ht1 : ((t : ↥K) : X) ≠ 1 := by
        intro h
        have : (t : ↥K) = 1 := Subtype.ext h
        have h1 : orderOf t = 1 := by rw [show t = 1 from Subtype.ext this]; simp
        omega
      have htmem : ((t : ↥K) : X) ∈ (P : Subgroup X) ⊓ K := by
        have h1 : (t : ↥K) ∈ (T : Subgroup ↥K) := t.2
        have h2 := Subgroup.mem_subgroupOf.mp ((SetLike.ext_iff.mp hT _).mp h1)
        exact ⟨h2.1, (t : ↥K).2⟩
      exact gammaCore_eq_top_of_le P hKγ (one_le_pRank_of_mem htmem ht3 ht1)
  ·
    have hall : ∀ T' : Sylow 3 ↥K, ¬ IsCyclic (T' : Subgroup ↥K) := fun T' hT' =>
      hTc (isCyclic_sylow_of T' T hT')
    have hK : ∀ T' : Sylow 3 ↥K, CFSG.Open.GLBCore 3 1 (T' : Subgroup ↥K) = ⊤ := fun T' =>
      hOff ↥K hKs hnab d ⟨e'⟩ 3 Nat.prime_three (by norm_num) (Ne.symm h3) T' (hall T')
        (fun ⟨_, hl⟩ => hL34 hl)
        (fun ⟨h, _⟩ => absurd h (by norm_num))
    exact gammaCore_eq_top_of_glbCore hK P

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
