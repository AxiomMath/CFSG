module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.OrderSweep
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoPairsBase
public import CFSG.RankThree.CentralCover.FourGroupWitness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockThreeFivesGroup
public import CFSG.CharacterTheory.Semidihedral.Local.FourGroupCyclingOddControlSupport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

open CFSG.HardMathSupport.Solomon.Coordinator Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

theorem not_seven_dvd_of_mul_dvd_pow_mul {a b m : ℕ} (hb : 7 ^ 3 ∣ b)
    (hdiv : a * b ∣ 7 ^ 3 * m) (hm : ¬ 7 ∣ m) : ¬ 7 ∣ a := by
  obtain ⟨b', rfl⟩ := hb
  rw [show a * (7 ^ 3 * b') = 7 ^ 3 * (a * b') by ring] at hdiv
  have h1 : a * b' ∣ m := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdiv
  exact fun h7 => hm (h7.trans ((dvd_mul_right a b').trans h1))

theorem isSimpleGroup_normalClosure_map {G : Type} [Group G] {W H : Subgroup G}
    (hHW : H ≤ W) (hHs : IsSimpleGroup H) (hH7 : 7 ^ 3 ∣ Nat.card H)
    (hGm : Nat.card G = 7 ^ 3 * (Nat.card G / 7 ^ 3))
    (hng : ¬ 7 ∣ Nat.card G / 7 ^ 3)
    (hF1 : ∀ N : Subgroup G, ¬ 7 ∣ Nat.card N → H ≤ normalizer (N : Set G) → N = ⊥) :
    IsSimpleGroup
      ((Subgroup.normalClosure ((H.subgroupOf W : Subgroup W) : Set W)).map W.subtype) := by
  classical
  let K : Subgroup W := Subgroup.normalClosure ((H.subgroupOf W : Subgroup W) : Set W)
  let L : Subgroup G := K.map W.subtype
  haveI : IsSimpleGroup H := hHs
  have hHL : H ≤ L := by
    intro h hh
    exact Subgroup.mem_map.mpr
      ⟨⟨h, hHW hh⟩, Subgroup.le_normalClosure (Subgroup.mem_subgroupOf.mpr hh), rfl⟩
  have hLW : L ≤ W := Subgroup.map_subtype_le K
  haveI : K.Normal := Subgroup.normalClosure_normal
  have hWnorm : W ≤ Subgroup.normalizer (L : Set G) :=
    fun w hw => CFSG.Semidihedral.Local.mem_normalizer_map_of_normal K hw
  have hHne : H ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot H).mp inferInstance
  haveI : Nontrivial L := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    exact hHne (le_bot_iff.mp (hHL.trans (le_of_eq hbot)))
  refine IsSimpleGroup.mk fun M hM => ?_
  by_cases hMbot : M = ⊥
  · exact Or.inl hMbot
  right
  let M' : Subgroup G := M.map L.subtype
  have hM'L : M' ≤ L := Subgroup.map_subtype_le M
  have hM'W : M' ≤ W := hM'L.trans hLW
  have hM'norm : L ≤ Subgroup.normalizer (M' : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro l hl x hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact Subgroup.mem_map.mpr
      ⟨⟨l, hl⟩ * m * ⟨l, hl⟩⁻¹, hM.conj_mem m hm ⟨l, hl⟩, rfl⟩
  have hconj_le : ∀ w : W, H.map (MulAut.conj (w : G)).toMonoidHom ≤ M' := by
    intro w
    let Hw : Subgroup G := H.map (MulAut.conj (w : G)).toMonoidHom
    have hHwL : Hw ≤ L := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := hx
      exact (Subgroup.mem_normalizer_iff.mp (hWnorm w.2) h).mp (hHL hh)
    have hHwsimple : IsSimpleGroup Hw :=
      (Subgroup.equivMapOfInjective H _ (MulAut.conj (w : G)).injective).symm.isSimpleGroup
    have hHw7 : 7 ^ 3 ∣ Nat.card Hw := by
      rw [show Nat.card Hw = Nat.card H from
        Subgroup.card_map_of_injective (MulAut.conj (w : G)).injective]
      exact hH7
    have hHwN : Hw ≤ Subgroup.normalizer (M' : Set G) := hHwL.trans hM'norm
    have hInt : ((M' ⊓ Hw).subgroupOf Hw).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
      exact (le_inf hHwN Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
    haveI := hInt
    rcases hHwsimple.eq_bot_or_eq_top_of_normal ((M' ⊓ Hw).subgroupOf Hw) with hb | ht
    · exfalso
      have hdisj : M' ⊓ Hw = ⊥ := by
        have h := Subgroup.subgroupOf_eq_bot.mp hb
        rwa [disjoint_iff, inf_eq_left.mpr inf_le_right] at h
      have hcardSup : Nat.card (M' ⊔ Hw : Subgroup G) = Nat.card M' * Nat.card Hw :=
        CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hHwN hdisj
      have hdiv : Nat.card M' * Nat.card Hw ∣ 7 ^ 3 * (Nat.card G / 7 ^ 3) := by
        rw [← hcardSup, ← hGm]
        exact Subgroup.card_subgroup_dvd_card (M' ⊔ Hw : Subgroup G)
      have h7M' : ¬ 7 ∣ Nat.card M' := not_seven_dvd_of_mul_dvd_pow_mul hHw7 hdiv hng
      exact hMbot ((Subgroup.map_eq_bot_iff_of_injective M L.subtype_injective).mp
        (hF1 M' h7M' (hHL.trans hM'norm)))
    · exact (Subgroup.subgroupOf_eq_top.mp ht).trans inf_le_left
  have hKle : K ≤ M'.subgroupOf W := by
    change Subgroup.closure (Group.conjugatesOfSet ((H.subgroupOf W : Subgroup W) : Set W)) ≤
      M'.subgroupOf W
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    obtain ⟨y, hy, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    change ((c * y * c⁻¹ : W) : G) ∈ M'
    exact hconj_le c (Subgroup.mem_map_of_mem (MulAut.conj (c : G)).toMonoidHom
      (Subgroup.mem_subgroupOf.mp hy))
  have hLle : L ≤ M' := by
    have h : L ≤ (M'.subgroupOf W).map W.subtype :=
      Subgroup.map_mono (f := W.subtype) hKle
    rwa [Subgroup.map_subgroupOf_eq_of_le hM'W] at h
  have hM'eq : M' = L := le_antisymm hM'L hLle
  have htopmap : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
  rw [show M.map L.subtype = L from hM'eq, htopmap]

theorem eq_of_isKGroup_of_le (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    {G : Type} [Group G] [Finite G] (hG : Nat.card G = 1255205709190661721292800)
    {W H Q : Subgroup G} (hWK : CFSG.Open.IsKGroup W) (hWtop : W ≠ ⊤) (hHW : H ≤ W)
    (hHs : IsSimpleGroup H) (hHc : Nat.card H = 4030387200) (hQH : Q ≤ H)
    (hQc : Nat.card Q = 7 ^ 3)
    (hF1 : ∀ N : Subgroup G, ¬ 7 ∣ Nat.card N → H ≤ normalizer (N : Set G) → N = ⊥)
    (hNs : IsSolvable (normalizer (Q : Set G)))
    {Jt : Subgroup G} (hJW : Jt ≤ W) (hJ1 : Jt ≠ ⊥) (hJp : ⁅Jt, Jt⁆ = Jt)
    (hJs : CFSG.Open.IsSubnormal Jt W) : Jt = H := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let K : Subgroup W := Subgroup.normalClosure ((H.subgroupOf W : Subgroup W) : Set W)
  let L : Subgroup G := K.map W.subtype
  have hHL : H ≤ L := by
    intro h hh
    exact Subgroup.mem_map.mpr
      ⟨⟨h, hHW hh⟩, Subgroup.le_normalClosure (Subgroup.mem_subgroupOf.mpr hh), rfl⟩
  have hLW : L ≤ W := Subgroup.map_subtype_le K
  have hH7 : 7 ^ 3 ∣ Nat.card H := by
    have h := Subgroup.card_dvd_of_le hQH
    rwa [hQc] at h
  have hGm : Nat.card G = 7 ^ 3 * (Nat.card G / 7 ^ 3) := by
    rw [hG]
    exact (Nat.mul_div_cancel' (by norm_num : 7 ^ 3 ∣ 1255205709190661721292800)).symm
  have hng : ¬ 7 ∣ Nat.card G / 7 ^ 3 := by
    rw [hG]
    norm_num
  have hLs : IsSimpleGroup L := isSimpleGroup_normalClosure_map hHW hHs hH7 hGm hng hF1
  haveI : IsSimpleGroup L := hLs
  have hLnab : ∃ a b : L, a * b ≠ b * a := by
    have hHnab : ∃ a b : H, a * b ≠ b * a :=
      CFSG.AGLEmbedding.ThreeFives.exists_noncomm_of_simple hHs (by rw [hHc]; norm_num)
    obtain ⟨a, b, hab⟩ := hHnab
    exact ⟨⟨a, hHL a.2⟩, ⟨b, hHL b.2⟩, fun h =>
      hab (Subtype.ext (by
        simpa using congrArg (fun z : L => (z : G)) h))⟩
  have hLcat : CFSG.Open.IsCatalogGroup L := by
    refine hWK.isCatalogGroup_of_surjective (L.subgroupOf W) hLnab
      (Subgroup.subgroupOfEquivOfLe hLW).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hLW).surjective
  have hdvd : Nat.card L ∣ Nat.card G := Subgroup.card_subgroup_dvd_card L
  have h7L : 7 ^ 3 ∣ Nat.card L := by
    have h := (Subgroup.card_dvd_of_le hQH).trans (Subgroup.card_dvd_of_le hHL)
    rwa [hQc] at h
  have hHL' : H = L := by
    rcases card_eq_of_isCatalogGroup_of_dvd hb hOrd hLcat (hG ▸ hdvd) h7L with h | h
    · exact Subgroup.eq_of_le_of_card_ge hHL (le_of_eq (h.trans hHc.symm))
    · exfalso
      have hLtop : L = ⊤ := Subgroup.eq_top_of_card_eq L (h.trans hG.symm)
      exact hWtop (top_unique (hLtop ▸ hLW))
  haveI : K.Normal := Subgroup.normalClosure_normal
  have hWnormH : W ≤ Subgroup.normalizer (H : Set G) := by
    rw [hHL']
    exact fun w hw => CFSG.Semidihedral.Local.mem_normalizer_map_of_normal K hw
  haveI hHn : (H.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHW).mpr hWnormH
  let N : Subgroup W := H.subgroupOf W
  let QW : Subgroup W := Q.subgroupOf W
  have hQW : Q ≤ W := hQH.trans hHW
  have hQWc : Nat.card QW = 7 ^ 3 := by
    rw [show Nat.card QW = Nat.card Q from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQW).toEquiv, hQc]
  have hQWN : QW ≤ N := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hQH hx
  have hNcard : Nat.card N = 4030387200 := by
    rw [show Nat.card N = Nat.card H from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHW).toEquiv, hHc]
  have hNfac : (Nat.card N).factorization 7 = 3 := by
    rw [hNcard, show (4030387200 : ℕ) = 7 ^ 3 * 11750400 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 7), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hPsubc : Nat.card (QW.subgroupOf N) = 7 ^ (Nat.card N).factorization 7 := by
    rw [hNfac, show Nat.card (QW.subgroupOf N) = Nat.card QW from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQWN).toEquiv, hQWc]
  let P : Sylow 7 N := Sylow.ofCard (QW.subgroupOf N) hPsubc
  have hPmap : (P : Subgroup N).map N.subtype = QW :=
    Subgroup.map_subgroupOf_eq_of_le hQWN
  haveI : N.Normal := hHn
  have hFr : Subgroup.normalizer (QW : Set W) ⊔ N = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top P
    rwa [hPmap] at h
  let π : W →* W ⧸ N := QuotientGroup.mk' N
  have hsurj : Function.Surjective (π.comp (Subgroup.normalizer (QW : Set W)).subtype) := by
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hwtop : w ∈ (N ⊔ Subgroup.normalizer (QW : Set W) : Subgroup W) := by
      rw [sup_comm, hFr]
      exact Subgroup.mem_top w
    obtain ⟨n, hn, q, hq, hwq⟩ := Subgroup.mem_sup_of_normal_left.mp hwtop
    refine ⟨⟨q, hq⟩, ?_⟩
    have hn1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    change π q = π w
    rw [← hwq, map_mul, hn1, one_mul]
  have hNQsolv : Group.IsSolvable (Subgroup.normalizer (QW : Set W)) := by
    have hle : Subgroup.normalizer (QW : Set W) ≤
        (Subgroup.normalizer (Q : Set G)).subgroupOf W := by
      intro x hx
      rw [Subgroup.subgroupOf_normalizer_eq hQW]
      exact hx
    haveI : Group.IsSolvable (Subgroup.normalizer (Q : Set G)) := hNs
    let φ : Subgroup.normalizer (QW : Set W) →* Subgroup.normalizer (Q : Set G) :=
      (W.subtype.comp (Subgroup.normalizer (QW : Set W)).subtype).codRestrict _
        (fun x => Subgroup.mem_subgroupOf.mp (hle x.2))
    refine Group.isSolvable_of_isSolvable_injective (f := φ) ?_
    intro x y hxy
    have h1 : ((x : W) : G) = ((y : W) : G) :=
      congrArg (fun z : Subgroup.normalizer (Q : Set G) => (z : G)) hxy
    exact Subtype.ext (W.subtype_injective h1)
  have hqSolv : Group.IsSolvable (W ⧸ N) :=
    Group.isSolvable_of_surjective (f := π.comp (Subgroup.normalizer (QW : Set W)).subtype)
      hsurj
  have hJH : Jt ≤ H := by
    let K₂ : Subgroup W := Jt.subgroupOf W
    have hK₂map : K₂.map W.subtype = Jt := Subgroup.map_subgroupOf_eq_of_le hJW
    have hK₂p : ⁅K₂, K₂⁆ = K₂ := by
      apply Subgroup.map_injective (f := W.subtype) W.subtype_injective
      rw [Subgroup.map_commutator, hK₂map, hJp]
    have hK₂π : ⁅K₂.map π, K₂.map π⁆ = K₂.map π := by
      rw [← Subgroup.map_commutator (f := π) (H₁ := K₂) (H₂ := K₂), hK₂p]
    have htopSolv : Group.IsSolvable (⊤ : Subgroup (W ⧸ N)) := by
      haveI : Group.IsSolvable (W ⧸ N) := hqSolv
      infer_instance
    have hK₂bot : K₂.map π = ⊥ :=
      eq_bot_of_perfect_of_le_isSolvable (J := K₂.map π) (S := ⊤) le_top htopSolv hK₂π
    have hK₂N : K₂ ≤ N := by
      have h := (Subgroup.map_eq_bot_iff (H := K₂) (f := π)).mp hK₂bot
      rwa [QuotientGroup.ker_mk'] at h
    intro j hj
    have hmem : (⟨j, hJW hj⟩ : W) ∈ K₂ := by
      rw [Subgroup.mem_subgroupOf]
      exact hj
    exact Subgroup.mem_subgroupOf.mp (hK₂N hmem)
  have hJsH : CFSG.Open.IsSubnormal Jt H := by
    have h := hJs.inf_of_le hHW
    rwa [inf_eq_left.mpr hJH] at h
  rcases hJsH.eq_bot_or_eq_of_isSimpleGroup hHs with h | h
  · exact absurd h hJ1
  · exact h

end CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K
