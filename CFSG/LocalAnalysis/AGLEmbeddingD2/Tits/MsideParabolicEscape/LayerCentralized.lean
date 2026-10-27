module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoLayerCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PermuteNine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.TwoOfThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUpInput

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3)
open scoped Pointwise

theorem commutator_mem_of_perm {M : Type} [Group M] [Finite M] (hK : KFactRankTwoE9)
    (D L T B W : Subgroup M) [D.Normal] [L.Normal]
    (hs : IsSimpleGroup ↥(L.map (QuotientGroup.mk' D)))
    (hty : IsRankTwoLayerType ↥(L.map (QuotientGroup.mk' D)))
    (hB3 : IsElemAbelian 3 B) (hB9 : Nat.card B = 9) (hBD : B ⊓ D = ⊥)
    (htrans : ∀ x ∈ B, ∀ y ∈ B, x ≠ 1 → y ≠ 1 → ∃ g ∈ Subgroup.normalizer (B : Set M),
      g * x * g⁻¹ = y)
    (hTW : T ≤ W) (hB : B ≤ W) (hT : ¬ 2 ∣ T.index) (hW5 : ¬ 5 ∣ Nat.card W) :
    ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ D := by
  set π := QuotientGroup.mk' D with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hker : π.ker = D := QuotientGroup.ker_mk' D
  have hNn : (L.map π).Normal := Subgroup.Normal.map inferInstance π hsurj
  have hBinj : Set.InjOn π (B : Set M) := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [hker] at h1
    have h2 : x⁻¹ * y ∈ B ⊓ D := ⟨B.mul_mem (B.inv_mem hx) hy, h1⟩
    rw [hBD, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.mp h2
  have hQ9 : Nat.card (B.map π) = 9 := by
    rw [← hB9]
    exact Nat.card_image_of_injOn hBinj
  have hQ3 : IsElemAbelian 3 (B.map π) := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
      apply Subtype.ext
      show π a * π b = π b * π a
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hB3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hB3.2 a ha, map_one]
  have hconj : ∀ g : M, (B.map (MulAut.conj g).toMonoidHom).map π =
      (B.map π).map (MulAut.conj (π g)).toMonoidHom := by
    intro g
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have htrans' : ∀ x ∈ B.map π, ∀ y ∈ B.map π, x ≠ 1 → y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer ((B.map π : Subgroup _) : Set _), g * x * g⁻¹ = y := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hx1 hy1
    have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hy1' : y ≠ 1 := fun h => hy1 (by rw [h, map_one])
    obtain ⟨g, hg, hgxy⟩ := htrans x hx y hy hx1' hy1'
    refine ⟨π g, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h2 := hconj g
      have hg' : B.map (MulAut.conj g).toMonoidHom = B :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
      rw [hg'] at h2
      exact h2.symm
    · rw [← map_mul, ← map_inv, ← map_mul, hgxy]
  have hTW' : T.map π ≤ W.map π := Subgroup.map_mono hTW
  have hodd' : ¬ 2 ∣ (W.map π).index := fun h =>
    hT ((h.trans (Subgroup.index_dvd_of_le hTW')).trans (Subgroup.index_map_dvd T hsurj))
  have h5' : ¬ 5 ∣ Nat.card (W.map π) := fun h => hW5 (h.trans (Subgroup.card_map_dvd W π))
  have hcen := le_centralizer_of_odd_index hK (L.map π) (B.map π) (W.map π) hs hty hQ3 hQ9 htrans'
    (Subgroup.map_mono hB) hodd' h5'
  intro b hb l hl
  have h1 := Subgroup.mem_centralizer_iff.mp (hcen ⟨b, hb, rfl⟩) (π l) ⟨l, hl, rfl⟩
  rw [← hker, MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [← h1]
  group

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape in
theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.commutator_mem_of_rankTwoLayer
    (hK : KFactRankTwoE9)
    {d : TauCeti.ValidLieTypeIndex} {G : Type} [Group G] [Finite G] {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hsyl : ∀ T : Subgroup G, IsSylowTwoOf T (H ⊓ M) → IsSylowTwoOf T M) {L : Subgroup G}
    (hlay : IsRankTwoLayer M L) {a : G} (ha : a ∈ A) {l : G} (hl : l ∈ L) :
    a * l * a⁻¹ * l⁻¹ ∈ GLBPrimeCore 3 M := by
  obtain ⟨hLM, -, hLn, hs, -, hty⟩ := hlay
  obtain ⟨T, hTH⟩ := exists_isSylowTwoOf (H ⊓ M)
  have hTM : IsSylowTwoOf T M :=
    hsyl T hTH
  obtain ⟨B, ⟨g, hgHM, hBg⟩, hBHM, hBel, hB9, hBU, hTBU⟩ :=
    D2L34BetaConf3.exists_permuting_elemAbelian_conj hc hTH
  have hBM : B ≤ M := hBHM.trans inf_le_right
  have hgM : g ∈ M := (hgHM : g ∈ H ⊓ M).2
  have hT2 : IsPGroup 2 T := hTH.2.1
  have hWM : T ⊔ B ≤ M := sup_le hTM.1 hBM
  have hWcard : Nat.card (T ⊔ B : Subgroup G) = Nat.card T * 9 :=
    card_sup_of_permute hT2 hB9 inf_le_left hBU hTBU
  have hW5 : ¬ 5 ∣ Nat.card (T ⊔ B : Subgroup G) := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hWcard, hk]
    intro h
    have h5p : Nat.Prime 5 := by norm_num
    rcases (Nat.Prime.dvd_mul h5p).mp h with h | h
    · have := h5p.dvd_of_dvd_pow h
      omega
    · omega
  have hB3p : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  have hB1 : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB9
    omega
  have hBg' : ∀ z ∈ B, ∃ a ∈ A, g * a * g⁻¹ = z := by
    intro z hz
    rw [hBg] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, ha, rfl⟩
  have htransG : ∀ x ∈ B, ∀ y ∈ B, x ≠ 1 → y ≠ 1 → ∃ h ∈ Subgroup.normalizer (B : Set G),
      h * x * h⁻¹ = y := by
    intro x hx y hy hx1 hy1
    obtain ⟨a₁, ha₁, rfl⟩ := hBg' x hx
    obtain ⟨a₂, ha₂, rfl⟩ := hBg' y hy
    have ha₁1 : a₁ ≠ 1 := fun h => hx1 (by rw [h]; group)
    have ha₂1 : a₂ ≠ 1 := fun h => hy1 (by rw [h]; group)
    obtain ⟨n, hn, hna⟩ := D2Escape.exists_normalizer_conj_of_l34 hc.esc hc.l34 hc.iso hc.le_K
      a₁ ha₁ ha₁1 a₂ ha₂ ha₂1
    refine ⟨g * n * g⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hn' : A.map (MulAut.conj n).toMonoidHom = A :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
      show B.map (MulAut.conj (g * n * g⁻¹)).toMonoidHom = B
      rw [hBg, ← map_conj_mul', show g * n * g⁻¹ * g = g * n by group, map_conj_mul', hn']
    · rw [← hna]
      group
  have hNBM : ∀ h ∈ Subgroup.normalizer (B : Set G), h ∈ M := by
    intro h hh
    refine mem_of_map_conj_le_of_stronglyEmbedded Nat.prime_three hstr hB3p hB1 hBM hBM ?_
    have hh' : B.map (MulAut.conj h).toMonoidHom = B :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hh
    exact hh'.le
  have hL'n : (L.subgroupOf M).Normal := hLn
  have hD1 : Nat.Coprime 3 (Nat.card (GLBPrimeCore 3 M)) := glbPrimeCore_coprime 3 M
  have hB3' : IsElemAbelian 3 (B.subgroupOf M) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun z : ↥B => (z : G))
        (hBel.1.is_comm.comm ⟨x.1.1, Subgroup.mem_subgroupOf.mp x.2⟩
          ⟨y.1.1, Subgroup.mem_subgroupOf.mp y.2⟩)
      exact this
    · apply Subtype.ext
      have := hBel.2 x.1 (Subgroup.mem_subgroupOf.mp hx)
      simpa using this
  have hB9' : Nat.card (B.subgroupOf M) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv).trans hB9
  have hBD : B.subgroupOf M ⊓ (GLBPrimeCore 3 M).subgroupOf M = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzB : (z : G) ∈ B := Subgroup.mem_subgroupOf.mp hz.1
    have hzD : (z : G) ∈ GLBPrimeCore 3 M := Subgroup.mem_subgroupOf.mp hz.2
    have hz3 : (z : G) ^ 3 = 1 := hBel.2 _ hzB
    have h1 : orderOf (z : G) ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have h2 : orderOf (z : G) ∣ Nat.card (GLBPrimeCore 3 M) := by
      have := orderOf_dvd_natCard (⟨(z : G), hzD⟩ : ↥(GLBPrimeCore 3 M))
      simpa using this
    have h3 : orderOf (z : G) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hD1) h2
    apply Subtype.ext
    simpa using orderOf_eq_one_iff.mp h3
  have htrans' : ∀ x ∈ B.subgroupOf M, ∀ y ∈ B.subgroupOf M, x ≠ 1 → y ≠ 1 →
      ∃ h ∈ Subgroup.normalizer ((B.subgroupOf M : Subgroup ↥M) : Set ↥M), h * x * h⁻¹ = y := by
    intro x hx y hy hx1 hy1
    have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hy1' : (y : G) ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨h, hh, hhxy⟩ := htransG x (Subgroup.mem_subgroupOf.mp hx) y
      (Subgroup.mem_subgroupOf.mp hy) hx1' hy1'
    have hhM : h ∈ M := hNBM h hh
    refine ⟨⟨h, hhM⟩, ?_, Subtype.ext hhxy⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hh (z : G)
  have hTW : T.subgroupOf M ≤ (T ⊔ B).subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ((le_sup_left : T ≤ T ⊔ B) (Subgroup.mem_subgroupOf.mp hx))
  have hBW : B.subgroupOf M ≤ (T ⊔ B).subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ((le_sup_right : B ≤ T ⊔ B) (Subgroup.mem_subgroupOf.mp hx))
  have hW5' : ¬ 5 ∣ Nat.card ((T ⊔ B).subgroupOf M) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv]
  have hres := commutator_mem_of_perm (M := ↥M) hK ((GLBPrimeCore 3 M).subgroupOf M)
    (L.subgroupOf M) (T.subgroupOf M) (B.subgroupOf M) ((T ⊔ B).subgroupOf M) hs hty hB3' hB9' hBD
    htrans' hTW hBW hTM.2.2 hW5'
  have hbB : g * a * g⁻¹ ∈ B := by
    rw [hBg]
    exact ⟨a, ha, rfl⟩
  have hgl : g * l * g⁻¹ ∈ L := by
    have := hL'n.conj_mem (⟨l, hLM hl⟩ : ↥M) (Subgroup.mem_subgroupOf.mpr hl) ⟨g, hgM⟩
    simpa using Subgroup.mem_subgroupOf.mp this
  have hc := hres ⟨g * a * g⁻¹, hBM hbB⟩ (Subgroup.mem_subgroupOf.mpr hbB)
    ⟨g * l * g⁻¹, hLM hgl⟩ (Subgroup.mem_subgroupOf.mpr hgl)
  have hcD : (g * a * g⁻¹) * (g * l * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * l * g⁻¹)⁻¹ ∈
      GLBPrimeCore 3 M := by
    simpa using Subgroup.mem_subgroupOf.mp hc
  have hgD := le_normalizer_glbPrimeCore 3 M (M.inv_mem hgM)
  have h2 := (Subgroup.mem_normalizer_iff.mp hgD _).mp hcD
  convert h2 using 1
  group

theorem d2L34BetaLayerCentralized_of_ff
    (hFF : CitedFFL34BestOffender) (hK : KFactRankTwoE9) :
    D2L34BetaLayerCentralized := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hKmax hcon L hlay a ha l hl
  exact D2L34BetaConf3.commutator_mem_of_rankTwoLayer hK hc.toConf3 hstr
    (fun _ hTH => (D2L34BetaConf.isSylowTwoOf_of_cover (d2L34BetaPushUpCoverSyl hFF) hc hstr
      hAll.onlyL34At hTH).1) hlay ha hl

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
