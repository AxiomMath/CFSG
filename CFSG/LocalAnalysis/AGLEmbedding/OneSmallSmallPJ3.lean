module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSP

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem d1SmallA6J3_of (hSch : KFactCatalogSchreier) (hJ3c : KFactJ3CoverA6) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
      (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
      D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
      p = 3 → IsAltTwoP 3 K → D1CzSP p z → D1CzJ3 p z → False := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hp3 hA hSP hJ
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨P', Pbar, KC, -, -, -, hRC⟩ := hd.exists_reducedCentralizer hz hSP
  obtain ⟨KC', hKC', hzK', ⟨eJ⟩⟩ := hJ
  obtain rfl : KC' = KC := hRC.unique KC' hKC'
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨hzZ, hzp⟩ := hRC.center ⟨z, hzC⟩ rfl
  have := hRC.normal
  set zK : KC' := ⟨d1CzElt 3 z, hzK'⟩ with hzKdef
  have hzKZ : zK ∈ Subgroup.center KC' := Subgroup.mem_center_iff.mpr fun k =>
    Subtype.ext (Subgroup.mem_center_iff.mp hzZ (k : D1CzQuot 3 z))
  have hzKp : orderOf zK = 3 := by rw [← Subgroup.orderOf_coe]; exact hzp
  obtain ⟨A, f, hf⟩ := hd.exists_surjective_of_reducedCentralizer hz hRC hSch
  obtain ⟨U, B, hUel, hUcard, hzU, hBU, ⟨t, htB, htp, htU⟩, hgen⟩ :=
    hJ3c KC' hKC'.2.2 ⟨eJ⟩ zK hzKZ hzKp A K hA f hf
  obtain ⟨u, huU, huz⟩ : ∃ u ∈ U, u ∉ Subgroup.zpowers zK := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (h : U ≤ Subgroup.zpowers zK)
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
  have hE3 : 3 ≤ Open.pRank 3 E := by
    have h3top : 3 ≤ Open.pRank 3 (⊤ : Subgroup E) := by
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
  have hred := hRC.red
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : Subgroup (D1CzQuot 3 z), X₀ = ((Subgroup.centralizer ({z} : Set G) ⊓
      M).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3)) :=
    ⟨_, rfl⟩
  rw [← hX₀] at hred
  have hUp : IsPGroup 3 U := IsPGroup.of_card (n := 2) (by rw [hUcard]; norm_num)
  have htp' : IsPGroup 3 (Subgroup.zpowers t) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, htp]
    exact ⟨1, by norm_num⟩
  have hEp : IsPGroup 3 E := hUp.to_sup_of_normal_left' htp' (Subgroup.zpowers_le.mpr
    (Subgroup.mem_normalizer_fintype fun a ha => by
      rw [htc a ha, mul_inv_cancel_right]
      exact ha))
  obtain ⟨S, hES⟩ := (hEp.map KC'.subtype).exists_le_sylow
  obtain ⟨c, hcS⟩ := MulAction.exists_smul_eq (D1CzQuot 3 z) S Pbar
  have hcmem : ∀ x ∈ (S : Subgroup (D1CzQuot 3 z)), c * x * c⁻¹ ∈ (Pbar : Subgroup _) := by
    intro x hx
    rw [← hcS, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨x, hx, rfl⟩
  set φ : KC' →* D1CzQuot 3 z := (MulAut.conj c).toMonoidHom.comp KC'.subtype with hφ
  have hφapp : ∀ k : KC', φ k = c * (k : D1CzQuot 3 z) * c⁻¹ := fun k => rfl
  have hφinj : Function.Injective φ := (MulAut.conj c).injective.comp KC'.subtype_injective
  have hφP : ∀ k ∈ E, φ k ∈ (Pbar : Subgroup _) := fun k hk => by
    rw [hφapp]
    exact hcmem _ (hES ⟨k, hk, rfl⟩)
  set U₁ := U.map φ with hU₁
  have hU₁P : U₁ ≤ (Pbar : Subgroup _) := by
    rintro _ ⟨k, hk, rfl⟩
    exact hφP k (Subgroup.mem_sup_left hk)
  have hU₁2 : 2 ≤ Open.pRank 3 U₁ := by
    rw [hU₁, pRank_map_of_injective 3 hp φ hφinj U]
    exact le_csSup (pRank_bddAbove 3 hp U) ⟨U, le_rfl, hUel, by rw [hUcard]; norm_num⟩
  have hφtC : φ t ∈ Subgroup.centralizer (U₁ : Set (D1CzQuot 3 z)) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, htc a ha]
  have hU₁3 : 3 ≤ Open.pRank 3 (U₁ ⊔ ((Pbar : Subgroup _) ⊓
      Subgroup.centralizer (U₁ : Set (D1CzQuot 3 z)))) := by
    have hle : E.map φ ≤ U₁ ⊔ ((Pbar : Subgroup _) ⊓
        Subgroup.centralizer (U₁ : Set (D1CzQuot 3 z))) := by
      rw [hE, Subgroup.map_sup, MonoidHom.map_zpowers]
      exact sup_le_sup le_rfl (Subgroup.zpowers_le.mpr ⟨hφP t htE, hφtC⟩)
    calc 3 ≤ Open.pRank 3 E := hE3
      _ = Open.pRank 3 (E.map φ) := (pRank_map_of_injective 3 hp φ hφinj E).symm
      _ ≤ _ := pRank_mono 3 hp hle
  have hNU : Subgroup.normalizer (U₁ : Set (D1CzQuot 3 z)) ≤ X₀ :=
    (normalizer_le_weakCore 3 hU₁P hU₁2 hU₁3).trans hred.weakCore_le
  have h3P : 3 ≤ Open.pRank 3 (Pbar : Subgroup (D1CzQuot 3 z)) :=
    le_trans (by norm_num) hRC.four_le_pRank
  have hPX : (Pbar : Subgroup (D1CzQuot 3 z)) ≤ X₀ := Subgroup.le_normalizer.trans
    ((normalizer_le_weakCore_of_rank 3 hp (Pbar : Subgroup (D1CzQuot 3 z)) h3P).trans
      hred.weakCore_le)
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
  obtain ⟨TS, hTS⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    hRC.normal.isSubnormal
  have hSY : (TS : Subgroup KC') ≤ X₀.comap φ := by
    intro k hk
    have hkS : (k : D1CzQuot 3 z) ∈ (S : Subgroup (D1CzQuot 3 z)) := by
      have h1 : (k : D1CzQuot 3 z) ∈ (S : Subgroup (D1CzQuot 3 z)) ⊓ KC' := hTS ▸ ⟨k, hk, rfl⟩
      exact h1.1
    show φ k ∈ X₀
    rw [hφapp]
    exact hPX (hcmem _ hkS)
  have hYtop := hgen _ hBY ⟨TS, hSY⟩
  have hKX : KC' ≤ X₀ := by
    intro x hx
    have hx' : c⁻¹ * x * c⁻¹⁻¹ ∈ KC' := hRC.normal.conj_mem x hx c⁻¹
    have h1 : (⟨c⁻¹ * x * c⁻¹⁻¹, hx'⟩ : KC') ∈ X₀.comap φ := hYtop ▸ Subgroup.mem_top _
    have h2 : φ ⟨c⁻¹ * x * c⁻¹⁻¹, hx'⟩ = x := by
      rw [hφapp]
      group
    rw [← h2]
    exact h1
  exact hred.false_of_three_le_pRank_of_le hRC.normal hKX (hE3.trans (pRank_mono 3 hp le_top))

end CFSG.AGLEmbedding
