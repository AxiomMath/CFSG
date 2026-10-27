module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32LeKCent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32LeKOut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableSwap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabBigKlein

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 Subgroup

section Decomp

variable {G : Type} [Group G]

theorem conj_mem_centralizer_of_mem_normalizer {K : Subgroup G} {g y : G}
    (hg : g ∈ normalizer (K : Set G)) (hy : y ∈ Subgroup.centralizer (K : Set G)) :
    g * y * g⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : g⁻¹ * k * g ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) k).mp hk
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hy _ hk'
  calc k * (g * y * g⁻¹) = g * ((g⁻¹ * k * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
    _ = (g * y * g⁻¹) * k := by group

theorem eq_of_mul_eq_of_mem_centralizer {K : Subgroup G}
    (hKC : ∀ k ∈ K, k ∈ Subgroup.centralizer (K : Set G) → k = 1) {k k' y y' : G} (hk : k ∈ K)
    (hk' : k' ∈ K) (hy : y ∈ Subgroup.centralizer (K : Set G))
    (hy' : y' ∈ Subgroup.centralizer (K : Set G)) (h : k * y = k' * y') : k = k' ∧ y = y' := by
  have h1 : k'⁻¹ * k = y' * y⁻¹ := by
    calc k'⁻¹ * k = k'⁻¹ * (k * y) * y⁻¹ := by group
      _ = k'⁻¹ * (k' * y') * y⁻¹ := by rw [h]
      _ = y' * y⁻¹ := by group
  have hK1 : k'⁻¹ * k ∈ K := mul_mem (inv_mem hk') hk
  have hC1 : k'⁻¹ * k ∈ Subgroup.centralizer (K : Set G) := by
    rw [h1]
    exact mul_mem hy' (inv_mem hy)
  have h2 := hKC _ hK1 hC1
  have hkk : k = k' := by
    have : k = k' * (k'⁻¹ * k) := by group
    rw [this, h2, mul_one]
  refine ⟨hkk, ?_⟩
  rw [hkk] at h
  exact mul_left_cancel h

theorem commute_of_decomp {K : Subgroup G}
    (hKC : ∀ k ∈ K, k ∈ Subgroup.centralizer (K : Set G) → k = 1) {g k y : G}
    (hg : g ∈ normalizer (K : Set G)) (hk : k ∈ K) (hy : y ∈ Subgroup.centralizer (K : Set G))
    (hx : g * (k * y) = (k * y) * g) : g * y = y * g := by
  have hgk : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  have hgy := conj_mem_centralizer_of_mem_normalizer hg hy
  have h1 : (g * k * g⁻¹) * (g * y * g⁻¹) = k * y := by
    calc (g * k * g⁻¹) * (g * y * g⁻¹) = (g * (k * y)) * g⁻¹ := by group
      _ = ((k * y) * g) * g⁻¹ := by rw [hx]
      _ = k * y := by group
  have h2 := (eq_of_mul_eq_of_mem_centralizer hKC hgk hk hgy hy h1).2
  calc g * y = (g * y * g⁻¹) * g := by group
    _ = y * g := by rw [h2]

theorem comm_mul_mul_eq {K : Subgroup G} {A A' B B' : G} (hA : A ∈ K) (hA' : A' ∈ K)
    (hB : B ∈ Subgroup.centralizer (K : Set G)) (hB' : B' ∈ Subgroup.centralizer (K : Set G)) :
    (A * B) * (A' * B') * (A * B)⁻¹ * (A' * B')⁻¹ =
      (A * A' * A⁻¹ * A'⁻¹) * (B * B' * B⁻¹ * B'⁻¹) := by
  have h1 : ∀ a ∈ K, ∀ b ∈ Subgroup.centralizer (K : Set G), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha
  have hC : ∀ b b' : G, b ∈ Subgroup.centralizer (K : Set G) →
      b' ∈ Subgroup.centralizer (K : Set G) → b * b' ∈ Subgroup.centralizer (K : Set G) :=
    fun b b' hb hb' => mul_mem hb hb'
  have e1 : B * A' = A' * B := (h1 A' hA' B hB).symm
  have hB3 : B * B' * B⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
    mul_mem (mul_mem hB hB') (inv_mem hB)
  have hB4 : B * B' * B⁻¹ * B'⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
    mul_mem hB3 (inv_mem hB')
  have e2 : (B * B' * B⁻¹) * A⁻¹ = A⁻¹ * (B * B' * B⁻¹) := (h1 A⁻¹ (inv_mem hA) _ hB3).symm
  have e3 : (B * B' * B⁻¹ * B'⁻¹) * A'⁻¹ = A'⁻¹ * (B * B' * B⁻¹ * B'⁻¹) :=
    (h1 A'⁻¹ (inv_mem hA') _ hB4).symm
  calc (A * B) * (A' * B') * (A * B)⁻¹ * (A' * B')⁻¹
      = A * (B * A') * B' * B⁻¹ * A⁻¹ * B'⁻¹ * A'⁻¹ := by group
    _ = A * (A' * B) * B' * B⁻¹ * A⁻¹ * B'⁻¹ * A'⁻¹ := by rw [e1]
    _ = A * A' * ((B * B' * B⁻¹) * A⁻¹) * B'⁻¹ * A'⁻¹ := by group
    _ = A * A' * (A⁻¹ * (B * B' * B⁻¹)) * B'⁻¹ * A'⁻¹ := by rw [e2]
    _ = (A * A' * A⁻¹) * ((B * B' * B⁻¹ * B'⁻¹) * A'⁻¹) := by group
    _ = (A * A' * A⁻¹) * (A'⁻¹ * (B * B' * B⁻¹ * B'⁻¹)) := by rw [e3]
    _ = (A * A' * A⁻¹ * A'⁻¹) * (B * B' * B⁻¹ * B'⁻¹) := by group

theorem exists_decomp_of_inner [Finite G] {K N : Subgroup G} (hN : N ≤ normalizer (K : Set G))
    {l : G} (hl : l ∈ N) (h : k32ActHom K N hN ⟨l, hl⟩ ∈ innAut ↥K) :
    ∃ k ∈ K, k⁻¹ * l ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨kk, hkk⟩ := h
  refine ⟨(kk : G), kk.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
  have h1 := congrArg (fun f : MulAut ↥K => ((f ⟨a, ha⟩ : ↥K) : G)) hkk
  simp only [MulAut.conj_apply, k32ActHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  calc a * ((kk : G)⁻¹ * l) = (kk : G)⁻¹ * ((kk : G) * a * (kk : G)⁻¹) * l := by group
    _ = (kk : G)⁻¹ * (l * a * l⁻¹) * l := by rw [h1]
    _ = (kk : G)⁻¹ * l * a := by group

theorem IsA4Block.le_of_isPGroup' [Finite G] {L U N : Subgroup G} (h : IsA4Block L U) (hNL : N ≤ L)
    (hN2 : IsPGroup 2 ↥N) : N ≤ U := by
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  have hLU : L ≤ normalizer (U : Set G) := by
    rw [hLc]
    exact sup_le Subgroup.le_normalizer ((zpowers_le).mpr hcN)
  have hNU : N ≤ normalizer (U : Set G) := hNL.trans hLU
  have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hNU
  obtain ⟨n, hn⟩ := hN2.exists_card_eq
  have hdvd12 : Nat.card ↥(N ⊔ U) ∣ 12 := by
    have := Subgroup.card_dvd_of_le (sup_le hNL h.le : N ⊔ U ≤ L)
    rwa [h.card_L] at this
  have hdvd : Nat.card ↥(N ⊔ U) ∣ 2 ^ (n + 2) := by
    have h1 : Nat.card ↥(N ⊔ U) ∣ Nat.card ↥N * Nat.card ↥U := Dvd.intro _ hmul
    have h2 : Nat.card ↥N * Nat.card ↥U = 2 ^ (n + 2) := by rw [hn, h.card_U]; ring
    rwa [h2] at h1
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm2 : m ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have h8 : 8 ∣ Nat.card ↥(N ⊔ U) := by
      rw [hm]
      have := pow_dvd_pow 2 (show 3 ≤ m by omega)
      simpa using this
    have := h8.trans hdvd12
    omega
  have hle : 4 ≤ Nat.card ↥(N ⊔ U) := by
    rw [← h.card_U]
    exact Subgroup.card_le_of_le le_sup_right
  have hs : Nat.card ↥(N ⊔ U) = 4 := by
    have : Nat.card ↥(N ⊔ U) ≤ 4 := by
      rw [hm]
      calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
        _ = 4 := by norm_num
    omega
  have hNU' : N ⊔ U = U :=
    (Subgroup.eq_of_le_of_card_ge (le_sup_right : U ≤ N ⊔ U) (by rw [hs, h.card_U])).symm
  rw [← hNU']
  exact le_sup_left

end Decomp

theorem k32LeK_of
    (hP : Prop121Three) (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) :
    K32LeK := by
  intro G _ _ T M H S L s x z₁ z₂ K ctx hK8
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcs := ctx.a3.cs
  have h3 := ctx.a3.a3
  have hcfg : A3A3 T M H S L s := ctx.a3.toA3A3
  have hB := basic31 hD h27_1 hcfg
  have hA4 : IsA4Block L (blockU L) := hcfg.isA4
  have hAs : IsA4Block (conjR L s) (blockU2 L s) := hcfg.isA4s
  have hLG₂ : L ≤ centralizerElem z₂ := ctx.a3.L_le_cent₂
  have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn ctx.comp
  have hZ := kInEight_center_eq_bot hq hK8
  have hKC : ∀ k ∈ K, k ∈ Subgroup.centralizer (K : Set G) → k = 1 := by
    intro k hk hkc
    have hmem : (⟨k, hk⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro a
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hkc a a.2)
    rw [hZ] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  have hKnorm : centralizerElem z₂ ≤ normalizer (K : Set G) := by
    by_cases hS : sOne S x ≤ normalizer (K : Set G)
    · have hs := hcs.setting
      have hpc : pCoreOf 2 (centralizerElem z₂) ≠ ⊥ :=
        pCoreOf_centralizerElem_ne_bot ctx.a3.z₂_ne ctx.a3.sq₂
      have hJc : K ∈ cComp (centralizerElem z₂) := mem_cComp_of_isComponentIn ctx.comp
      rcases hP G hs.simple hs.nonabelian hs.qtke _ hpc K hJc with hnorm | ⟨hcard, -⟩
      · exact hnorm
      · exact (false_of_card_conj_eq_two ctx.sylow hS hcard).elim
    · exact (k32_false_of_swapped hP hD h27_1 k32AltOut_proved ctx hS).elim
  have hLN_K : L ≤ normalizer (K : Set G) := hLG₂.trans hKnorm
  have hz1U : z₁ ∈ blockU L := ctx.a3.z₁_mem.1
  have hz2U : z₂ ∈ blockU2 L s := ctx.a3.z₂_mem.1
  have hQeq : pCoreOf 2 H = blockD S L ⊔ (blockU L ⊔ blockU2 L s) := by
    rw [hB.hQ, hcfg.blockU0_eq hB.hU0]
  have hUQ : blockU L ≤ pCoreOf 2 H := by
    rw [hQeq]
    exact le_sup_left.trans le_sup_right
  have hU2Q : blockU2 L s ≤ pCoreOf 2 H := by
    rw [hQeq]
    exact le_sup_right.trans le_sup_right
  have hCQ : Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H :=
    centralizer_pCore_le hD h27_1 hcfg (mul_mem (hUQ hz1U) (hU2Q hz2U)) ctx.a3.z_ne
      (z_central hB ctx.a3)
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 H) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hHN : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hLH : L ≤ H := C56.le_H hcs
  have hBL : baum S ≤ normalizer (L : Set G) := ((C56.baumann_A3_cs hcs h3).2).1
  have hLJ : L ≤ conjJoin S L := by
    rw [hcfg.join]
    exact le_sup_left
  have hLsJ : conjR L s ≤ conjJoin S L := by
    rw [hcfg.join]
    exact le_sup_right
  have hz₂Ls : z₂ ∈ conjR L s := hAs.le hz2U
  have hDc : ∀ d ∈ blockD S L, ∀ l ∈ conjJoin S L, d * l = l * d := fun d hd l hl =>
    (Subgroup.mem_centralizer_iff.mp hd.2 l hl).symm
  have hDG₂ : blockD S L ≤ centralizerElem z₂ := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hDc d hd z₂ (hLsJ hz₂Ls))
  have hU2G₂ : blockU2 L s ≤ centralizerElem z₂ := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAs.comm_U u hu z₂ hz2U)
  have hUG₂ : blockU L ≤ centralizerElem z₂ := hA4.le.trans hLG₂
  have hequi : ∀ g ∈ centralizerElem z₂, ∀ (k y : G), k ∈ K →
      y ∈ Subgroup.centralizer (K : Set G) → g * (k * y) = (k * y) * g → g * y = y * g :=
    fun g hg k y hk hy hx => commute_of_decomp hKC (hKnorm hg) hk hy hx
  have hQcent : ∀ y : G, blockD S L ⊔ (blockU L ⊔ blockU2 L s) ≤ centralizerElem y →
      y ∈ pCoreOf 2 H := by
    intro y hle
    apply hCQ
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : q ∈ blockD S L ⊔ (blockU L ⊔ blockU2 L s) := by rw [← hQeq]; exact hq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hq')
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := hA4.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hcG₂ : c ∈ centralizerElem z₂ := hLG₂ hcL
  let φ := k32ActHom K (centralizerElem z₂) hKnorm
  have hφc : φ ⟨c, hcG₂⟩ ∈ innAut ↥K := by
    refine kInEight_aut_three_inner hq hK8 _ ?_
    rw [← map_pow]
    have : (⟨c, hcG₂⟩ : ↥(centralizerElem z₂)) ^ 3 = 1 := Subtype.ext (by simpa using hc3')
    rw [this, map_one]
  let φL : ↥L →* MulAut ↥K := φ.comp (Subgroup.inclusion hLG₂)
  let N'' : Subgroup ↥L := (innAut ↥K).comap φL
  have hN''n : N''.Normal := (innAut_normal ↥K).comap φL
  let N : Subgroup G := N''.map L.subtype
  have hNL : N ≤ L := Subgroup.map_subtype_le N''
  have hNsub : N.subgroupOf L = N'' :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective N''
  have hLN : L ≤ normalizer (N : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mp ?_
    rw [hNsub]
    exact hN''n
  have hcNmem : c ∈ N := ⟨⟨c, hcL⟩, hφc, rfl⟩
  have hdec : ∀ l ∈ N, ∃ k ∈ K, k⁻¹ * l ∈ Subgroup.centralizer (K : Set G) := by
    intro l hl
    obtain ⟨l', hl'N, rfl⟩ := hl
    exact exists_decomp_of_inner hKnorm (hLG₂ l'.2) hl'N
  obtain ⟨u₁, hu₁U, hu₁1, -⟩ := exists_two_ne_one_of_card_four
    (fun v hv => by simpa [sq] using hA4.sq_U v hv) hA4.card_U
  have hu₁L : u₁ ∈ L := hA4.le hu₁U
  obtain ⟨w, hwdef⟩ : ∃ w : G, w = u₁ * c * u₁⁻¹ * c⁻¹ := ⟨_, rfl⟩
  have hwU : w ∈ blockU L := by
    have h1 : c * u₁⁻¹ * c⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp hcN u₁⁻¹).mp (inv_mem hu₁U)
    have e : w = u₁ * (c * u₁⁻¹ * c⁻¹) := by rw [hwdef]; group
    rw [e]
    exact mul_mem hu₁U h1
  have hw1 : w ≠ 1 := by
    intro h
    apply hcfp u₁ hu₁U hu₁1
    have h1 : u₁ * c = c * u₁ := by
      calc u₁ * c = (u₁ * c * u₁⁻¹ * c⁻¹) * (c * u₁) := by group
        _ = c * u₁ := by rw [← hwdef, h, one_mul]
    calc c * u₁ * c⁻¹ = (u₁ * c) * c⁻¹ := by rw [h1]
      _ = u₁ := by group
  have hwN : w ∈ N := by
    have h1 : u₁ * c * u₁⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hLN hu₁L) c).mp hcNmem
    rw [hwdef]
    exact mul_mem h1 (inv_mem hcNmem)
  have hUN : blockU L ≤ N := hA4.le_of_mem hLN hwN hwU hw1
  obtain ⟨k', hk'K, hy'C⟩ := hdec u₁ (hUN hu₁U)
  obtain ⟨k₀, hk₀K, hy₀C⟩ := hdec c hcNmem
  obtain ⟨y', hy'def⟩ : ∃ y' : G, y' = k'⁻¹ * u₁ := ⟨_, rfl⟩
  obtain ⟨y₀, hy₀def⟩ : ∃ y₀ : G, y₀ = k₀⁻¹ * c := ⟨_, rfl⟩
  rw [← hy'def] at hy'C
  rw [← hy₀def] at hy₀C
  have hu₁eq : u₁ = k' * y' := by rw [hy'def]; group
  have hceq : c = k₀ * y₀ := by rw [hy₀def]; group
  have hy'Q : y' ∈ pCoreOf 2 H := by
    apply hQcent
    refine sup_le ?_ (sup_le ?_ ?_)
    · intro d hd
      refine Subgroup.mem_centralizer_singleton_iff.mpr
        (hequi d (hDG₂ hd) k' y' hk'K hy'C ?_)
      rw [← hu₁eq]
      exact hDc d hd u₁ (hLJ hu₁L)
    · intro u hu
      refine Subgroup.mem_centralizer_singleton_iff.mpr
        (hequi u (hUG₂ hu) k' y' hk'K hy'C ?_)
      rw [← hu₁eq]
      exact hA4.comm_U u hu u₁ hu₁U
    · intro u hu
      refine Subgroup.mem_centralizer_singleton_iff.mpr
        (hequi u (hU2G₂ hu) k' y' hk'K hy'C ?_)
      rw [← hu₁eq]
      exact (hcfg.comm_elem u₁ hu₁L u (hAs.le hu)).symm
  have hk'Q : k' ∈ pCoreOf 2 H := by
    have e : k' = u₁ * y'⁻¹ := by rw [hu₁eq]; group
    rw [e]
    exact mul_mem (hUQ hu₁U) (inv_mem hy'Q)
  have hk'NL : k' ∈ normalizer (L : Set G) := hBL (hB.Q_le_R hk'Q)
  have hκQL : k' * c * k'⁻¹ * c⁻¹ ∈ pCoreOf 2 H ⊓ L := by
    refine ⟨?_, ?_⟩
    · have h1 : c * k'⁻¹ * c⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (hHN (hLH hcL)) k'⁻¹).mp (inv_mem hk'Q)
      have e : k' * c * k'⁻¹ * c⁻¹ = k' * (c * k'⁻¹ * c⁻¹) := by group
      rw [e]
      exact mul_mem hk'Q h1
    · have h1 : k' * c * k'⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hk'NL c).mp hcL
      exact L.mul_mem h1 (L.inv_mem hcL)
  have hκU : k' * c * k'⁻¹ * c⁻¹ ∈ blockU L :=
    hA4.le_of_isPGroup' (N := pCoreOf 2 H ⊓ L) inf_le_right (hQ2.to_le inf_le_left) hκQL
  have hκeq : k' * c * k'⁻¹ * c⁻¹ = k' * k₀ * k'⁻¹ * k₀⁻¹ := by
    have h := comm_mul_mul_eq (A := k') (A' := k₀) (B := 1) (B' := y₀) hk'K hk₀K (one_mem _) hy₀C
    simp only [mul_one, one_mul, inv_one, mul_inv_cancel] at h
    rw [← hceq] at h
    exact h
  have hκU' : k' * k₀ * k'⁻¹ * k₀⁻¹ ∈ blockU L := by rw [← hκeq]; exact hκU
  have hweq : w = (k' * k₀ * k'⁻¹ * k₀⁻¹) * (y' * y₀ * y'⁻¹ * y₀⁻¹) := by
    have h := comm_mul_mul_eq hk'K hk₀K hy'C hy₀C
    rw [← hu₁eq, ← hceq] at h
    rw [hwdef]
    exact h
  have hηC : y' * y₀ * y'⁻¹ * y₀⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
    mul_mem (mul_mem (mul_mem hy'C hy₀C) (inv_mem hy'C)) (inv_mem hy₀C)
  have hηU : y' * y₀ * y'⁻¹ * y₀⁻¹ ∈ blockU L := by
    have e : y' * y₀ * y'⁻¹ * y₀⁻¹ = (k' * k₀ * k'⁻¹ * k₀⁻¹)⁻¹ * w := by rw [hweq]; group
    rw [e]
    exact mul_mem (inv_mem hκU') hwU
  have hη1 : y' * y₀ * y'⁻¹ * y₀⁻¹ = 1 := by
    have hLfaith : L ⊓ Subgroup.centralizer (K : Set G) = ⊥ :=
      k32_inf_centralizer_eq_bot hA4 hz1U hLN_K (k32_z₁_not_central ctx)
    have hmem : y' * y₀ * y'⁻¹ * y₀⁻¹ ∈ L ⊓ Subgroup.centralizer (K : Set G) :=
      ⟨hA4.le hηU, hηC⟩
    rw [hLfaith] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hwK : w ∈ K := by
    rw [hweq, hη1, mul_one]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk'K hk₀K) (K.inv_mem hk'K)) (K.inv_mem hk₀K)
  have hUK : blockU L ≤ K := hA4.le_of_mem hLN_K hwK hwU hw1
  have hy₀Q : y₀ ∈ pCoreOf 2 H := by
    apply hQcent
    refine sup_le ?_ (sup_le ?_ ?_)
    · intro d hd
      refine Subgroup.mem_centralizer_singleton_iff.mpr
        (hequi d (hDG₂ hd) k₀ y₀ hk₀K hy₀C ?_)
      rw [← hceq]
      exact hDc d hd c (hLJ hcL)
    · intro u hu
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hy₀C u (hUK hu))
    · intro u hu
      refine Subgroup.mem_centralizer_singleton_iff.mpr
        (hequi u (hU2G₂ hu) k₀ y₀ hk₀K hy₀C ?_)
      rw [← hceq]
      exact (hcfg.comm_elem c hcL u (hAs.le hu)).symm
  have hy₀3 : y₀ ^ 3 = 1 := by
    have hcomm : Commute k₀ y₀ := Subgroup.mem_centralizer_iff.mp hy₀C k₀ hk₀K
    have h1 : (k₀ * y₀) ^ 3 = k₀ ^ 3 * y₀ ^ 3 := hcomm.mul_pow 3
    rw [← hceq, hc3'] at h1
    have hk3 : k₀ ^ 3 ∈ K := pow_mem hk₀K 3
    have hk3C : k₀ ^ 3 ∈ Subgroup.centralizer (K : Set G) := by
      have e : k₀ ^ 3 = (y₀ ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
      rw [e]
      exact inv_mem (pow_mem hy₀C 3)
    have hk31 : k₀ ^ 3 = 1 := hKC _ hk3 hk3C
    rw [hk31, one_mul] at h1
    exact h1.symm
  have hy₀1 : y₀ = 1 := by
    obtain ⟨m, hm⟩ := hQ2 ⟨y₀, hy₀Q⟩
    have h1 : y₀ ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h2 : orderOf y₀ ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf y₀ ∣ 3 := orderOf_dvd_of_pow_eq_one hy₀3
    have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
    have h4 : orderOf y₀ ∣ Nat.gcd (2 ^ m) 3 := Nat.dvd_gcd h2 h3
    rw [hcop.gcd_eq_one] at h4
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  have hcK : c ∈ K := by
    rw [hceq, hy₀1, mul_one]
    exact hk₀K
  rw [hLc]
  exact sup_le hUK ((zpowers_le).mpr hcK)

end CFSG.QuasithinUnique.DoubleA3
