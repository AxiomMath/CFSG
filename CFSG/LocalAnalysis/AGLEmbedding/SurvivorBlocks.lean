module

public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_isPGroup_map_eq' {H K : Type*} [Group H] [Group K] [Finite H] {q : ℕ}
    [Fact q.Prime] {f : H →* K} (hf : Function.Surjective f) {E : Subgroup K}
    (hE : IsPGroup q E) : ∃ P : Subgroup H, IsPGroup q P ∧ P.map f = E := by
  set W := E.comap f with hW
  let ψ : W →* E := (f.comp W.subtype).codRestrict E fun w => w.2
  have hψ : Function.Surjective ψ := by
    intro e
    obtain ⟨x, hx⟩ := hf e
    exact ⟨⟨x, show f x ∈ E by rw [hx]; exact e.2⟩, Subtype.ext hx⟩
  obtain ⟨T⟩ : Nonempty (Sylow q W) := inferInstance
  have htop : ((T.mapSurjective hψ : Sylow q E) : Subgroup E) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hE.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨(T : Subgroup W).map W.subtype, T.isPGroup'.map _, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact w.2
  · intro e he
    have : (⟨e, he⟩ : E) ∈ (T : Subgroup W).map ψ := htop ▸ Subgroup.mem_top _
    obtain ⟨w, hw, hwe⟩ := this
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwe⟩

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_isPGroup_le_of_le_barM {M T : Subgroup G} (_hTM : T ≤ M)
    (hQT : pCoreOf 2 M ≤ T) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hA : IsPGroup p A) (hAT : A ≤ barM M T) :
    ∃ B : Subgroup G, B ≤ T ∧ IsPGroup p B ∧ Nat.card B = Nat.card A := by
  have hp : p.Prime := Fact.out
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  obtain ⟨B₀, hB₀, hB₀A⟩ := exists_isPGroup_map_eq' (QuotientGroup.mk'_surjective
    (CFSG.pCore 2 ↥M)) hA
  set B := B₀.map M.subtype with hB
  have hBM : B ≤ M := Subgroup.map_subtype_le _
  have hBp : IsPGroup p B := hB₀.map _
  have hbarB : barM M B = A := by
    rw [hB, barM, ← hB₀A]
    congr 1
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  refine ⟨B, ?_, hBp, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨⟨t, htM⟩, ht, htb⟩ := hAT (hB₀A ▸ Subgroup.mem_map_of_mem _ hb)
    have h1 : mk (⟨t, htM⟩⁻¹ * b) = 1 := by rw [map_mul, map_inv, htb, inv_mul_cancel]
    have h2 : (b : G) = t * ((⟨t, htM⟩⁻¹ * b : M) : G) := by simp
    show (b : G) ∈ T
    rw [h2]
    exact T.mul_mem (Subgroup.mem_subgroupOf.mp ht)
      (hQT (coe_mem_pCoreOf_two_of_mk_eq_one _ h1))
  · rw [← hbarB, card_barM_of_isPGroup hp hp2 hBM hBp]

end Lift

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section OrbitOne

variable {G : Type} [Group G] [Finite G]

theorem barM_conj_eq_of_small {M L T : Subgroup G} (hL : IsTwoPrimeComponent M L) {y : G}
    (hyL : y ∈ L) (hy3 : IsPGroup 3 (Subgroup.zpowers y))
    (hyl : ∃ l ∈ L, y * l * y⁻¹ * l⁻¹ ∉ pCoreOf 2 M) {k : G} (hkM : k ∈ M) (hTM : T ≤ M)
    (hQT : pCoreOf 2 M ≤ T) (hyT : y ∈ T) (hykT : k * y * k⁻¹ ∈ T)
    (hT3 : ∀ B : Subgroup G, B ≤ T → IsPGroup 3 B → Nat.card B ≤ 3) :
    barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L := by
  by_contra hne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hyM : y ∈ M := hL.le hyL
  set yb := mk ⟨y, hyM⟩ with hyb
  set yb' := mk ⟨k * y * k⁻¹, M.mul_mem (M.mul_mem hkM hyM) (M.inv_mem hkM)⟩ with hyb'
  have hLc : IsComponentOf (barM M L) ⊤ := hL.component
  have hLc' : IsComponentOf (barM M (L.map (MulAut.conj k).toMonoidHom)) ⊤ :=
    (hL.map_conj hkM).component
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hLc' hLc hne
  have hyb'C : yb' ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨y, hyL, rfl⟩))
  have hybL : yb ∈ barM M L := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL)
  have hybC : yb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro hC
    obtain ⟨l, hl, hyl'⟩ := hyl
    apply hyl'
    have hlb : mk ⟨l, hL.le hl⟩ ∈ barM M L :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)
    have h1 := Subgroup.mem_centralizer_iff.mp hC _ hlb
    have h2 : mk (⟨y, hyM⟩ * ⟨l, hL.le hl⟩ * ⟨y, hyM⟩⁻¹ * ⟨l, hL.le hl⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hyb, ← h1]
      group
    exact coe_mem_pCoreOf_two_of_mk_eq_one _ h2
  have hcy : yb * yb' = yb' * yb := Subgroup.mem_centralizer_iff.mp hyb'C yb hybL
  obtain ⟨e, he⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
  have hye : y ^ 3 ^ e = 1 := by simpa using congrArg Subtype.val he
  have hybe : yb ^ 3 ^ e = 1 := by
    rw [hyb, ← map_pow]
    have : (⟨y, hyM⟩ : M) ^ 3 ^ e = 1 := Subtype.ext (by simpa using hye)
    rw [this, map_one]
  have hyb'e : yb' ^ 3 ^ e = 1 := by
    rw [hyb', ← map_pow]
    have : (⟨k * y * k⁻¹, M.mul_mem (M.mul_mem hkM hyM) (M.inv_mem hkM)⟩ : M) ^ 3 ^ e = 1 :=
      Subtype.ext (by simp [conj_pow, hye])
    rw [this, map_one]
  set A := Subgroup.zpowers yb ⊔ Subgroup.zpowers yb' with hA
  have hA3 : IsPGroup 3 A := by
    refine IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_prime_pow_eq_one hybe)
      (isPGroup_zpowers_of_pow_prime_pow_eq_one hyb'e) ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer
      (s := (Subgroup.zpowers yb : Set (↥M ⧸ CFSG.pCore 2 ↥M))))
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact (Commute.zpow_left hcy n).eq
  have hyb'1 : yb' ≠ 1 := by
    intro h1
    apply hybC
    have hconj : yb' = mk ⟨k, hkM⟩ * yb * (mk ⟨k, hkM⟩)⁻¹ := by
      rw [hyb', hyb, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have : yb = 1 := by
      rw [h1] at hconj
      have h2 := congrArg (fun x => (mk ⟨k, hkM⟩)⁻¹ * x * mk ⟨k, hkM⟩) hconj
      simpa [mul_assoc] using h2.symm
    rw [this]
    exact Subgroup.one_mem _
  have hle' : Subgroup.zpowers yb' ≤ A := le_sup_right
  have hybA : yb ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers yb)
  have hybn : yb ∉ Subgroup.zpowers yb' := fun h' =>
    hybC ((Subgroup.zpowers_le.mpr hyb'C) h')
  obtain ⟨a, ha⟩ := (isPGroup_zpowers_of_pow_prime_pow_eq_one hyb'e).exists_card_eq
  obtain ⟨b, hb⟩ := hA3.exists_card_eq
  have ha1 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at ha
    exact hyb'1 (Subgroup.zpowers_eq_bot.mp ha)
  have hab : a < b := by
    have hdvd := Subgroup.card_dvd_of_le hle'
    rw [ha, hb] at hdvd
    have hab' := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp hdvd
    rcases hab'.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      apply hybn
      have heq := Subgroup.eq_of_le_of_card_ge hle' (by rw [ha, hb, h'])
      exact heq ▸ hybA
  have hA9 : 9 ≤ Nat.card A := by
    rw [hb]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAT : A ≤ barM M T := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyT)
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hykT)
  obtain ⟨B, hBT, hB3, hBc⟩ := exists_isPGroup_le_of_le_barM hTM hQT (by norm_num) hA3 hAT
  have := hT3 B hBT hB3
  omega

end OrbitOne

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section SmallSylow

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_le_sup_glbPrimeCore {p : ℕ} [Fact p.Prime] {H A B : Subgroup G}
    (hAH : A ≤ H) (hBH : B ≤ H) (hB : IsPGroup p B) (hBA : B ≤ A ⊔ GLBPrimeCore p H) :
    Nat.card B ≤ Nat.card A := by
  have hp : p.Prime := Fact.out
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hBp : IsPGroup p (B.subgroupOf H) := hB.comap_subtype
  have hcB : Nat.card ((B.subgroupOf H).map π) = Nat.card B := by
    rw [card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hBp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv]
  have hle : (B.subgroupOf H).map π ≤ (A.subgroupOf H).map π := by
    rintro _ ⟨b, hb, rfl⟩
    have hbA : (b : G) ∈ A ⊔ GLBPrimeCore p H := hBA (Subgroup.mem_subgroupOf.mp hb)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A (GLBPrimeCore p H)
      (hAH.trans (le_normalizer_glbPrimeCore p H))] at hbA
    obtain ⟨a, ha, n, hn, han⟩ := hbA
    have hnH : n ∈ H := glbPrimeCore_le p H hn
    refine ⟨⟨a, hAH ha⟩, Subgroup.mem_subgroupOf.mpr ha, ?_⟩
    have hb' : b = ⟨a, hAH ha⟩ * ⟨n, hnH⟩ := Subtype.ext han.symm
    rw [hb', map_mul, (mem_glbPrimeCore_iff_mk_eq_one (p := p) (⟨n, hnH⟩ : H)).mp hn, mul_one]
  calc Nat.card B = Nat.card ((B.subgroupOf H).map π) := hcB.symm
    _ ≤ Nat.card ((A.subgroupOf H).map π) := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (A.subgroupOf H) := Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    _ = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv

end SmallSylow

end CFSG.AGLEmbedding
