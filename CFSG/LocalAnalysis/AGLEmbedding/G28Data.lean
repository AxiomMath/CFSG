module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorSocle
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorCenter
public import CFSG.LocalAnalysis.AGLEmbedding.G28InSituAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Piece

variable {G : Type} [Group G] [Finite G] {H M : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_comap_map {p : ℕ} {V₀ : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    {g : G} (hgH : g ∈ H) (hg : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨g, hgH⟩ ∈
      Subgroup.normalizer (V₀ : Set (H ⧸ primeComplementCore (G := H) p))) :
    g ∈ Subgroup.normalizer
      (((V₀.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype :
        Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨h', hh', rfl⟩
    refine ⟨⟨g, hgH⟩ * h' * ⟨g, hgH⟩⁻¹, ?_, by simp⟩
    show QuotientGroup.mk' _ (⟨g, hgH⟩ * h' * ⟨g, hgH⟩⁻¹) ∈ V₀
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp hh'
  · rintro ⟨h', hh', hx⟩
    have hx' : (h' : G) = g * x * g⁻¹ := hx
    have hxH : x ∈ H := by
      have : x = g⁻¹ * (h' : G) * g := by rw [hx']; group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.inv_mem hgH) h'.2) hgH
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    have he : (⟨g, hgH⟩ : H) * ⟨x, hxH⟩ * ⟨g, hgH⟩⁻¹ = h' := Subtype.ext (by simp [hx'])
    have h2 : QuotientGroup.mk' (primeComplementCore (G := H) p)
        (⟨g, hgH⟩ * ⟨x, hxH⟩ * ⟨g, hgH⟩⁻¹) ∈ V₀ := he ▸ hh'
    rw [map_mul, map_mul, map_inv] at h2
    exact (Subgroup.mem_normalizer_iff.mp hg _).mpr h2

theorem sup_glbPrimeCore_eq_preimage {p : ℕ} {V : Subgroup G} (hVH : V ≤ H)
    {V₀ : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hV : (V.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = V₀) :
    V ⊔ GLBPrimeCore p H =
      (V₀.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype := by
  apply le_antisymm
  · refine sup_le (fun v hv => ⟨⟨v, hVH hv⟩, ?_, rfl⟩) (fun n hn => ?_)
    · rw [← hV]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv)
    · refine ⟨⟨n, glbPrimeCore_le p H hn⟩, ?_, rfl⟩
      show QuotientGroup.mk' _ _ ∈ V₀
      rw [(mem_glbPrimeCore_iff_mk_eq_one (p := p) ⟨n, glbPrimeCore_le p H hn⟩).mp hn]
      exact V₀.one_mem
  · rintro _ ⟨x, hx, rfl⟩
    exact le_sup_glbPrimeCore_of_map_le (Y := Subgroup.zpowers (x : G)) (X := V)
      (Subgroup.zpowers_le.mpr x.2) (by
        rw [hV]
        rintro _ ⟨y, hy, rfl⟩
        have hy' : (y : G) ∈ Subgroup.zpowers (x : G) := Subgroup.mem_subgroupOf.mp hy
        obtain ⟨n, hn⟩ := hy'
        have : y = x ^ n := Subtype.ext (by simpa using hn.symm)
        rw [this, map_zpow]
        exact V₀.zpow_mem hx n) (Subgroup.mem_zpowers _)

theorem exists_su38Piece {T V₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    {zb : H ⧸ primeComplementCore (G := H) 3}
    (hS : G28InSitu T (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
      zb V₀) {z : G} (hzH : z ∈ H)
    (hzz : QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨z, hzH⟩ = zb) {Y : Subgroup G}
    (hYK : Y ≤ H ⊓ M)
    (hVY : V₀ ≤ (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3))) :
    ∃ V : Subgroup G, V ≤ Y ∧ SU38Piece (H ⊓ M) (GLBPrimeCore 3 H) z V := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set N := GLBPrimeCore 3 H with hN
  set Q₀ := Y.subgroupOf H ⊓ V₀.comap π with hQ₀
  have hQmap : Q₀.map π = V₀ := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
    · intro v hv
      obtain ⟨y, hy, rfl⟩ := hVY hv
      exact ⟨y, ⟨hy, hv⟩, rfl⟩
  obtain ⟨P', hP'Q, hP'P, hP'map⟩ := exists_perfect_le_map_eq' π hQmap hS.V_perfect
  set V := P'.map H.subtype with hV
  have hVH : V ≤ H := Subgroup.map_subtype_le _
  have hVsub : V.subgroupOf H = P' := Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hVmap : (V.subgroupOf H).map π = V₀ := by rw [hVsub, hP'map]
  have hVY' : V ≤ Y := by
    rintro _ ⟨p', hp', rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hP'Q hp').1
  have hVK : V ≤ H ⊓ M := hVY'.trans hYK
  refine ⟨V, hVY', ?_, hVK, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV, ← Subgroup.map_commutator, hP'P]
  ·
    intro hVN
    have hbot : V₀ = ⊥ := by
      rw [← hVmap, eq_bot_iff]
      rintro _ ⟨v, hv, rfl⟩
      exact Subgroup.mem_bot.mpr ((mem_glbPrimeCore_iff_mk_eq_one (p := 3) v).mp
        (hVN (Subgroup.mem_subgroupOf.mp hv)))
    have hz := hS.z_mem_V
    rw [hbot, Subgroup.mem_bot] at hz
    have hzo := hS.z_order
    rw [hz, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  ·
    intro k hk
    rw [sup_glbPrimeCore_eq_preimage hVH hVmap]
    refine mem_normalizer_comap_map hk.1 (hS.V_normal ?_)
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
  ·
    obtain ⟨d, ψ₀, hd, hψ₀⟩ := hS.V_onto
    have hθmem : ∀ v : V, π (Subgroup.inclusion hVH v) ∈ V₀ := fun v => by
      rw [← hVmap]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr v.2)
    let θ : V →* V₀ := (π.comp (Subgroup.inclusion hVH)).codRestrict V₀ hθmem
    have hθ : Function.Surjective θ := by
      intro w
      have hw : (w : H ⧸ primeComplementCore (G := H) 3) ∈ (V.subgroupOf H).map π :=
        hVmap ▸ w.2
      obtain ⟨v, hv, hvw⟩ := hw
      exact ⟨⟨v, Subgroup.mem_subgroupOf.mp hv⟩, Subtype.ext hvw⟩
    exact ⟨d, ψ₀.comp θ, hd, hψ₀.comp hθ⟩
  ·
    intro W hWK hVW
    have hWH : W ≤ H := hWK.trans inf_le_left
    set Wb := (W.subgroupOf H).map π with hWb
    have hWbY : Wb ≤ ((H ⊓ M).subgroupOf H).map π :=
      Subgroup.map_mono (Subgroup.comap_mono hWK)
    have hVWb : V₀ ≤ Subgroup.normalizer (Wb : Set (H ⧸ primeComplementCore (G := H) 3)) := by
      rw [← hVmap]
      rintro _ ⟨v, hv, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨v * w * v⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
        exact (Subgroup.mem_normalizer_iff.mp (hVW (Subgroup.mem_subgroupOf.mp hv)) w).mp
          (Subgroup.mem_subgroupOf.mp hw)
      · rintro ⟨w, hw, hwx⟩
        refine ⟨v⁻¹ * w * v, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hVW ((V.subgroupOf H).inv_mem hv : v⁻¹ ∈ _))
            w).mp (Subgroup.mem_subgroupOf.mp hw)
          simpa using this
        · rw [map_mul, map_mul, map_inv, hwx]
          group
    rcases hS.V_quasi Wb hWbY hVWb with h1 | h1
    · left
      exact le_sup_glbPrimeCore_of_map_le hVH (hVmap ▸ h1)
    · right
      rw [Subgroup.commutator_le]
      intro w hw v hv
      have hc : ⁅π ⟨w, hWH hw⟩, π ⟨v, hVH hv⟩⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator
          (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hw : (⟨w, hWH hw⟩ : H) ∈ _))
          (hVmap ▸ Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hv :
            (⟨v, hVH hv⟩ : H) ∈ V.subgroupOf H) : π ⟨v, hVH hv⟩ ∈ V₀)
        rw [h1, Subgroup.mem_bot] at this
        exact this
      have := (mem_glbPrimeCore_iff_mk_eq_one (p := 3) ⁅(⟨w, hWH hw⟩ : H), ⟨v, hVH hv⟩⁆).mpr
        (by rw [map_commutatorElement]; exact hc)
      simpa [commutatorElement_def] using this
  ·
    intro g hgK hgV
    have hgH : g ∈ H := hgK.1
    have hgC : π ⟨g, hgH⟩ ∈ ((H ⊓ M).subgroupOf H).map π ⊓
        Subgroup.centralizer (V₀ : Set (H ⧸ primeComplementCore (G := H) 3)) := by
      refine ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hgK), ?_⟩
      show π ⟨g, hgH⟩ ∈ Subgroup.centralizer (V₀ : Set (H ⧸ primeComplementCore (G := H) 3))
      rw [Subgroup.mem_centralizer_iff, ← hVmap]
      rintro _ ⟨v, hv, rfl⟩
      have h1 := (mem_glbPrimeCore_iff_mk_eq_one (p := 3) (⟨g, hgH⟩ * v * ⟨g, hgH⟩⁻¹ * v⁻¹)).mp
        (by simpa using hgV v (Subgroup.mem_subgroupOf.mp hv))
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 := mul_inv_eq_one.mp h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    have hgz := hS.V_centralizer hgC
    have hle : (((Subgroup.zpowers g).subgroupOf H).map π) ≤
        ((Subgroup.zpowers z).subgroupOf H).map π := by
      have e : ∀ (x : G) (hx : x ∈ H), ((Subgroup.zpowers x).subgroupOf H).map π =
          Subgroup.zpowers (π ⟨x, hx⟩) := by
        intro x hx
        have e1 : (Subgroup.zpowers x).subgroupOf H = Subgroup.zpowers (⟨x, hx⟩ : H) := by
          apply Subgroup.map_injective H.subtype_injective
          rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hx),
            MonoidHom.map_zpowers]
          rfl
        rw [e1, MonoidHom.map_zpowers]
      rw [e g hgH, e z hzH, hzz]
      exact Subgroup.zpowers_le.mpr hgz
    exact le_sup_glbPrimeCore_of_map_le (Subgroup.zpowers_le.mpr hgH) hle
      (Subgroup.mem_zpowers g)

theorem exists_g28Data_of (hKF : KFactG28Local) [Fact (Nat.Prime 3)] {P : Sylow 3 G}
    {R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hglob : CFSG.AGLEmbeddingD2.AGLGlobal G) (hext : D1Extremal 3 P M H R)
    (hrbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
    (hred : ReducedNongeneration 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))))
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K)
    (hC : Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) = ⊥)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsGTwoEightIndex d) (eK : K ≃* CatGroup d) :
    ∃ z : G, D1G28Data P M H R z := by
  obtain ⟨zb, V₀, hS⟩ := hKF _ K d hd (normal_of_forall_isComponentOf_eq hK huniq) ⟨eK⟩ hC
    Rbar _ hred.three_le_pRank hred.weakCore_le hred.ne_top
  rw [hrbar] at hS
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hRH : R ≤ H := hext.le_H
  have hR3 : IsPGroup 3 R := hext.isPGroup
  obtain ⟨r, hr, hrz⟩ := hS.z_mem
  set z : G := (r : G) with hz
  have hzR : z ∈ R := Subgroup.mem_subgroupOf.mp hr
  have hzH : z ∈ H := hRH hzR
  have hrz' : r = ⟨z, hzH⟩ := rfl
  have hz3 : z ^ 3 = 1 := by
    have hzb3 : zb ^ 3 = 1 := by
      have := pow_orderOf_eq_one zb
      rwa [hS.z_order] at this
    have h1 : π (r ^ 3) = 1 := by rw [map_pow, hrz, hzb3]
    have h2 := eq_of_map_eq_of_isPGroup hR3 (a := r ^ 3) (b := 1)
      (by simpa using R.pow_mem hzR 3) R.one_mem (by rw [h1, map_one])
    simpa [hz] using congrArg Subtype.val h2
  have hz1 : z ≠ 1 := by
    intro h1
    have : r = 1 := Subtype.ext h1
    rw [this, map_one] at hrz
    have hzo := hS.z_order
    rw [← hrz, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hzC : z ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxH := hRH hx
    have hxT : π ⟨x, hxH⟩ ∈ (R.subgroupOf H).map π :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    have hc := Subgroup.mem_centralizer_iff.mp hS.z_center _ hxT
    have h2 := eq_of_map_eq_of_isPGroup hR3 (a := ⟨x, hxH⟩ * r) (b := r * ⟨x, hxH⟩)
      (R.mul_mem hx hzR) (R.mul_mem hzR hx) (by rw [map_mul, map_mul, hrz, hc])
    simpa using congrArg Subtype.val h2
  have hzpow : ((Subgroup.zpowers z).subgroupOf H).map π = Subgroup.zpowers zb := by
    have hle : Subgroup.zpowers z ≤ H := Subgroup.zpowers_le.mpr hzH
    have e1 : (Subgroup.zpowers z).subgroupOf H = Subgroup.zpowers r := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hle, MonoidHom.map_zpowers]
      rfl
    rw [e1, MonoidHom.map_zpowers, hrz]
  have hZR : centerOf R ≤ Subgroup.zpowers z := by
    have hmap := map_inf_centralizer_eq (p := 3) hRH hR3
    refine le_of_map_le_of_isPGroup hRH hR3 inf_le_left (Subgroup.zpowers_le.mpr hzR) ?_
    have h1 : ((centerOf R).subgroupOf H).map π = centerOf ((R.subgroupOf H).map π) := hmap
    rw [h1, hzpow]
    exact hS.center_le
  have hcardR : Nat.card R = 3 ^ 6 := by
    have hRp : IsPGroup 3 (R.subgroupOf H) := hR3.comap_subtype
    rw [← hS.card_T, card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3) hRp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv]
  have hph3 : D1PhaseThree 3 P M H R :=
    hext.toPhaseThree_of_forall hglob fun W hW hWn hWc => hS.primeCore W hW hWn hWc
  refine ⟨z, hph3, hzR, hzC, hzo, hZR, hcardR, fun Y hYK hYn => ?_⟩
  have hYH : Y ≤ H := hYK.trans inf_le_left
  set Wb := (Y.subgroupOf H).map π with hWb
  have hWbY : Wb ≤ ((H ⊓ M).subgroupOf H).map π := Subgroup.map_mono (Subgroup.comap_mono hYK)
  have hWbn : ((H ⊓ M).subgroupOf H).map π ≤
      Subgroup.normalizer (Wb : Set (H ⧸ primeComplementCore (G := H) 3)) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨k * y * k⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.mp (hYn (Subgroup.mem_subgroupOf.mp hk)) y).mp
        (Subgroup.mem_subgroupOf.mp hy)
    · rintro ⟨y, hy, hyx⟩
      refine ⟨k⁻¹ * y * k, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hYn (Subgroup.mem_subgroupOf.mp
          (((H ⊓ M).subgroupOf H).inv_mem hk))) y).mp (Subgroup.mem_subgroupOf.mp hy)
        simpa using this
      · rw [map_mul, map_mul, map_inv, hyx]
        group
  rcases hS.trichotomy Wb hWbY hWbn with h1 | h1 | h1
  · exact Or.inl (le_glbPrimeCore_of_map_eq_bot hYH h1)
  · exact Or.inr (Or.inl (le_sup_glbPrimeCore_of_map_le hYH (hzpow ▸ h1)))
  · exact Or.inr (Or.inr (exists_su38Piece hS hzH hrz hYK h1))

theorem stmtG28Data_of (hSoc : StmtChevTwoSocle) (hKF : KFactG28Local) : StmtG28Data := by
  intro G _ _ _ P M H R Rbar hcfg K hK huniq hcent d hd e
  obtain ⟨hZ, -, ⟨eK⟩, -⟩ :=
    hSoc G 3 P M H R Rbar hcfg K hK huniq hcent d (Or.inr (Or.inr (Or.inl ⟨rfl, hd⟩))) e
  exact exists_g28Data_of hKF hcfg.glob hcfg.ext hcfg.rbar hcfg.red hK huniq
    (hcfg.centralizer_eq_bot hK huniq hcent hZ) hd eK

end Piece

end CFSG.AGLEmbedding
