module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockCM
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallAlphaThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPThree
import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeak

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section J3

variable {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {X₀ : Subgroup X}

theorem false_of_j3_of_a6 (h : ReducedNongeneration 3 X R X₀)
    (h3P : 3 ≤ CFSG.Open.pRank 3 (R : Subgroup X)) {z : X} (hzZ : z ∈ Subgroup.center X)
    (hzp : orderOf z = 3) {KC' : Subgroup X} (hKC' : IsComponentOf KC' ⊤) (hKn : KC'.Normal)
    (hzK' : z ∈ KC') (hJ3c : KFactJ3CoverA6)
    (eJ : KC' ⧸ Subgroup.center KC' ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)
    {A : Subgroup KC'} (f : A →* alternatingGroup (Fin 6)) (hf : Function.Surjective f) :
    False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set zK : KC' := ⟨z, hzK'⟩ with hzKdef
  have hzKZ : zK ∈ Subgroup.center KC' := Subgroup.mem_center_iff.mpr fun k =>
    Subtype.ext (Subgroup.mem_center_iff.mp hzZ (k : X))
  have hzKp : orderOf zK = 3 := by rw [← Subgroup.orderOf_coe]; exact hzp
  obtain ⟨U, B, hUel, hUcard, hzU, hBU, ⟨t, htB, htp, htU⟩, hgen⟩ :=
    hJ3c KC' hKC'.2.2 ⟨eJ⟩ zK hzKZ hzKp A (alternatingGroup (Fin 6)) ⟨MulEquiv.refl _⟩ f hf
  obtain ⟨u, huU, huz⟩ : ∃ u ∈ U, u ∉ Subgroup.zpowers zK := by
    by_contra hne
    push Not at hne
    have h1 := Subgroup.card_le_of_le (hne : U ≤ Subgroup.zpowers zK)
    rw [hUcard, Nat.card_zpowers, hzKp] at h1
    omega
  have hcU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hexpU : ∀ a ∈ U, a ^ 3 = 1 := hUel.2
  have htc : ∀ a ∈ U, t * a = a * t := fun a ha =>
    (Subgroup.mem_centralizer_iff.mp (hBU htB) a ha).symm
  set E : Subgroup KC' := U ⊔ Subgroup.zpowers t with hE
  have hzE : zK ∈ E := Subgroup.mem_sup_left hzU
  have huE : u ∈ E := Subgroup.mem_sup_left huU
  have htE : t ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hz1 : zK ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hzKp; norm_num at hzKp
  have ht3 : t ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [htp] at h1
  have hE3 : 3 ≤ CFSG.Open.pRank 3 E := by
    have h3top : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup E) := by
      refine CFSG.SectionRank.ClassicalEven.three_le_pRank_of_gens (x := ⟨zK, hzE⟩)
        (y := ⟨u, huE⟩) (z := ⟨t, htE⟩) (Subtype.ext (by simpa using hexpU zK hzU))
        (Subtype.ext (by simpa using hexpU u huU))
        (Subtype.ext (by simpa using ht3))
        (Subtype.ext (hcU zK hzU u huU)) (Subtype.ext (htc zK hzU).symm)
        (Subtype.ext (htc u huU).symm) (fun h1 => hz1 (by simpa using congrArg Subtype.val h1))
        (fun n hn => huz ?_) (fun n m hnm => htU ?_)
      · have : zK ^ n = u := by simpa using congrArg Subtype.val hn
        rw [← this]
        exact Subgroup.npow_mem_zpowers zK n
      · have : zK ^ n * u ^ m = t := by simpa using congrArg Subtype.val hnm
        rw [← this]
        exact U.mul_mem (U.pow_mem hzU n) (U.pow_mem huU m)
    have h1 := pRank_map_of_injective 3 hp E.subtype E.subtype_injective ⊤
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    rw [h1]
    exact h3top
  have hUp : IsPGroup 3 U := IsPGroup.of_card (n := 2) (by rw [hUcard]; norm_num)
  have htp' : IsPGroup 3 (Subgroup.zpowers t) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, htp]
    exact ⟨1, by norm_num⟩
  have hEp : IsPGroup 3 E := hUp.to_sup_of_normal_left' htp' (Subgroup.zpowers_le.mpr
    (Subgroup.mem_normalizer_fintype fun a ha => by
      rw [htc a ha, mul_inv_cancel_right]
      exact ha))
  obtain ⟨S, hES⟩ := (hEp.map KC'.subtype).exists_le_sylow
  obtain ⟨c, hcS⟩ := MulAction.exists_smul_eq X S R
  have hcmem : ∀ x ∈ (S : Subgroup X), c * x * c⁻¹ ∈ (R : Subgroup X) := by
    intro x hx
    rw [← hcS, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨x, hx, rfl⟩
  set φ : KC' →* X := (MulAut.conj c).toMonoidHom.comp KC'.subtype with hφ
  have hφapp : ∀ k : KC', φ k = c * (k : X) * c⁻¹ := fun k => rfl
  have hφinj : Function.Injective φ := (MulAut.conj c).injective.comp KC'.subtype_injective
  have hφP : ∀ k ∈ E, φ k ∈ (R : Subgroup X) := fun k hk => by
    rw [hφapp]
    exact hcmem _ (hES ⟨k, hk, rfl⟩)
  set U₁ := U.map φ with hU₁
  have hU₁P : U₁ ≤ (R : Subgroup X) := by
    rintro _ ⟨k, hk, rfl⟩
    exact hφP k (Subgroup.mem_sup_left hk)
  have hU₁2 : 2 ≤ CFSG.Open.pRank 3 U₁ := by
    rw [hU₁, pRank_map_of_injective 3 hp φ hφinj U]
    exact le_csSup (pRank_bddAbove 3 hp U) ⟨U, le_rfl, hUel, by rw [hUcard]; norm_num⟩
  have hφtC : φ t ∈ Subgroup.centralizer (U₁ : Set X) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, htc a ha]
  have hU₁3 : 3 ≤ CFSG.Open.pRank 3 (U₁ ⊔ ((R : Subgroup X) ⊓
      Subgroup.centralizer (U₁ : Set X))) := by
    have hle : E.map φ ≤ U₁ ⊔ ((R : Subgroup X) ⊓ Subgroup.centralizer (U₁ : Set X)) := by
      rw [hE, Subgroup.map_sup, MonoidHom.map_zpowers]
      exact sup_le_sup le_rfl (Subgroup.zpowers_le.mpr ⟨hφP t htE, hφtC⟩)
    calc 3 ≤ CFSG.Open.pRank 3 E := hE3
      _ = CFSG.Open.pRank 3 (E.map φ) := (pRank_map_of_injective 3 hp φ hφinj E).symm
      _ ≤ _ := pRank_mono 3 hp hle
  have hNU : Subgroup.normalizer (U₁ : Set X) ≤ X₀ :=
    (normalizer_le_weakCore 3 hU₁P hU₁2 hU₁3).trans h.weakCore_le
  have hPX : (R : Subgroup X) ≤ X₀ := Subgroup.le_normalizer.trans
    ((normalizer_le_weakCore_of_rank 3 hp (R : Subgroup X) h3P).trans h.weakCore_le)
  have hBY : B ≤ X₀.comap φ := by
    intro b hb
    apply hNU
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨a, ha, rfl⟩ := hy
    have hab : a * b = b * a := Subgroup.mem_centralizer_iff.mp (hBU hb) a ha
    have h1 : φ b * φ a * (φ b)⁻¹ = φ a := by
      rw [← map_mul, ← map_inv, ← map_mul, ← hab, mul_inv_cancel_right]
    rw [h1]
    exact ⟨a, ha, rfl⟩
  obtain ⟨TS, hTS⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hKn.isSubnormal
  have hSY : (TS : Subgroup KC') ≤ X₀.comap φ := by
    intro k hk
    have hkS : (k : X) ∈ (S : Subgroup X) := by
      have h1 : (k : X) ∈ (S : Subgroup X) ⊓ KC' := hTS ▸ ⟨k, hk, rfl⟩
      exact h1.1
    show φ k ∈ X₀
    rw [hφapp]
    exact hPX (hcmem _ hkS)
  have hYtop := hgen _ hBY ⟨TS, hSY⟩
  have hKX : KC' ≤ X₀ := by
    intro x hx
    have hx' : c⁻¹ * x * c⁻¹⁻¹ ∈ KC' := hKn.conj_mem x hx c⁻¹
    have h1 : (⟨c⁻¹ * x * c⁻¹⁻¹, hx'⟩ : KC') ∈ X₀.comap φ := hYtop ▸ Subgroup.mem_top _
    have h2 : φ ⟨c⁻¹ * x * c⁻¹⁻¹, hx'⟩ = x := by
      rw [hφapp]
      group
    rw [← h2]
    exact h1
  exact h.false_of_three_le_pRank_of_le hKn hKX (hE3.trans (pRank_mono 3 hp le_top))

theorem false_of_mem_of_a6 (h : ReducedNongeneration 3 X R X₀)
    (hR4 : 4 ≤ CFSG.Open.pRank 3 (R : Subgroup X)) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = 3) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K) (hα : KFactAlphaW)
    (hK3 : KFactAlphaThreeWeak) (hJ3c : KFactJ3CoverA6) {A : Subgroup K}
    (f : A →* alternatingGroup (Fin 6)) (hf : Function.Surjective f) : False := by
  obtain ⟨eJ⟩ := h.j3_of_alphaThree_of_mem hR4 hX hz hzp hK hKn hzK hα hK3
  exact false_of_j3_of_a6 h (le_trans (by norm_num) hR4) hz hzp hK hKn hzK hJ3c eJ f hf

end J3

@[expose] def D1Sp62CMOutResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, p = 3 → IsSpSixTwoIndex d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ L : Subgroup G, Sp62BlockShape M H R L →
          blockCentralizer M L ≤ GLBPrimeCore p H →
          (∀ d' : TauCeti.ValidLieTypeIndex, IsOmegaMinusTwoIndex 4 d' →
            IsEmpty (barM M L ≃* CatGroup d')) →
          ∀ x ∈ R, orderOf x = p → ¬ Subgroup.centralizer ({x} : Set G) ⊓ H ≤ M →
            pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ →
            (∃ A : Subgroup G, A ≤ R ⊓ Subgroup.centralizer ({x} : Set G) ∧
              IsElemAbelian p A ∧ Nat.card A = p ^ 3) →
            (∃ E : Subgroup G, E ≤ M ⊓ Subgroup.centralizer ({x} : Set G) ∧
              IsElemAbelian p E ∧ Nat.card E = p ^ 4) →
            (∃ Y : Subgroup G, Y ≤ M ⊓ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup p Y ∧
              p ^ 5 ≤ Nat.card Y ∧ 4 ≤ CFSG.Open.pRank p Y) →
            (∃ (W : Subgroup G) (φ : W →* alternatingGroup (Fin 6)),
              W ≤ Subgroup.centralizer ({x} : Set G) ⊓ H ∧ Function.Surjective φ) →
            ∀ (Tb : Sylow 3 (Subgroup.centralizer ({x} : Set G) ⧸
                primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3))
              (KC : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
                primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)),
              ReducedNongeneration 3 (Subgroup.centralizer ({x} : Set G) ⧸
                primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3) Tb
                (((Subgroup.centralizer ({x} : Set G) ⊓ M).subgroupOf
                  (Subgroup.centralizer ({x} : Set G))).map
                    (QuotientGroup.mk' (primeComplementCore 3))) →
              4 ≤ CFSG.Open.pRank 3 (Tb : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
                primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)) →
              CatalogSimpleSections (Subgroup.centralizer ({x} : Set G) ⧸
                primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3) →
              QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)
                ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ Subgroup.center _ →
              IsComponentOf KC ⊤ → KC.Normal →
              (∀ L' : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
                primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3),
                  IsComponentOf L' ⊤ → L' = KC) →
              (∃ (B : Subgroup KC) (f : B →* alternatingGroup (Fin 6)), Function.Surjective f) →
              QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)
                ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∉ KC →
              False

theorem d1Sp62CMResidue_of_out (hα : KFactAlphaW) (hK3 : KFactAlphaThreeWeak)
    (hJ3c : KFactJ3CoverA6) (hres : D1Sp62CMOutResidue) : D1Sp62CMResidue := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd e L hL hCL h4 x hxR hx3
    hxH hO hA hE hY hW Tb KC hred hR4 hcat hzZ hKC hKCn huniqC hB
  by_cases hzK : QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer
      ({x} : Set G)) 3) ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ KC
  · subst hp3
    have hzp : orderOf (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer
        ({x} : Set G)) 3) ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) = 3 :=
      orderOf_mk_of_coprime Nat.prime_three _ (primeComplementCore_coprime 3)
        (by rw [← Subgroup.orderOf_coe]; exact hx3)
    obtain ⟨B, f, hf⟩ := hB
    exact false_of_mem_of_a6 hred hR4 hcat hzZ hzp hKC hKCn hzK hα hK3 hJ3c f hf
  · exact hres G p P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd e L hL hCL h4 x hxR hx3
      hxH hO hA hE hY hW Tb KC hred hR4 hcat hzZ hKC hKCn huniqC hB hzK

end CFSG.AGLEmbedding
