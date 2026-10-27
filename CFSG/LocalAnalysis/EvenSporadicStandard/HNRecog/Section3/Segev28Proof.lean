module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Generic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup

variable {H : Type} [Group H] [Finite H] {t : H}

private lemma conj_comm {G : Type*} [Group G] {a b c : G} (h : b * c = c * b) :
    (a * c * a⁻¹) * (a * b * a⁻¹) = (a * b * a⁻¹) * (a * c * a⁻¹) := by
  calc (a * c * a⁻¹) * (a * b * a⁻¹) = a * (c * b) * a⁻¹ := by group
    _ = a * (b * c) * a⁻¹ := by rw [h]
    _ = (a * b * a⁻¹) * (a * c * a⁻¹) := by group

private lemma subgroupOf_Gx_eq_bot {t : H}
    (hN : ∀ N : Subgroup ↥(Gx t), N.Normal → N ≠ ⊥ → GxSelf t ∈ N)
    {M : Subgroup H} (hM : M.Normal) (htM : t ∉ M) : M.subgroupOf (Gx t) = ⊥ := by
  by_contra hne
  have hmem : GxSelf t ∈ M.subgroupOf (Gx t) := hN _ (hM.subgroupOf (Gx t)) hne
  rw [Subgroup.mem_subgroupOf] at hmem
  exact htM hmem

theorem segev28_normalizer_le (ht : orderOf t = 2) (S : Sylow 2 ↥(Gx t))
    (hS : ∀ x : ↥(Gx t),
      (x ∈ centerOf (S : Subgroup ↥(Gx t)) ∧ x ^ 2 = 1) ↔ x ∈ zpowers (GxSelf t)) :
    normalizer (((S : Subgroup ↥(Gx t)).map (Gx t).subtype : Subgroup H) : Set H) ≤ Gx t := by
  set S' : Subgroup H := (S : Subgroup ↥(Gx t)).map (Gx t).subtype with hS'def
  have hS'_le : S' ≤ Gx t := by
    rintro z ⟨s, -, rfl⟩
    exact s.2
  intro g hg
  have ht_center : GxSelf t ∈ centerOf (S : Subgroup ↥(Gx t)) :=
    ((hS (GxSelf t)).mpr (Subgroup.mem_zpowers (GxSelf t))).1
  have htS' : t ∈ S' := by
    rw [hS'def]
    exact ⟨GxSelf t, ht_center.1, rfl⟩
  set y : H := g * t * g⁻¹ with hydef
  have hyS' : y ∈ S' := ((Subgroup.mem_set_normalizer_iff).1 hg t).1 htS'
  have hyGx : y ∈ Gx t := hS'_le hyS'
  have hyS : (⟨y, hyGx⟩ : ↥(Gx t)) ∈ (S : Subgroup ↥(Gx t)) := by
    rw [hS'def] at hyS'
    obtain ⟨a, haS, ha⟩ := Subgroup.mem_map.mp hyS'
    have : a = ⟨y, hyGx⟩ := Subtype.ext ha
    rw [← this]
    exact haS
  have hcent : (⟨y, hyGx⟩ : ↥(Gx t)) ∈ centerOf (S : Subgroup ↥(Gx t)) := by
    rw [centerOf, Subgroup.mem_inf]
    refine ⟨hyS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply Subtype.ext
    change (s : H) * y = y * (s : H)
    have hsS' : (s : H) ∈ S' := by
      rw [hS'def]
      exact ⟨s, hs, rfl⟩
    have hs0S' : g⁻¹ * (s : H) * g ∈ S' :=
      ((Subgroup.mem_set_normalizer_iff'').1 hg (s : H)).1 hsS'
    have hs0Gx : g⁻¹ * (s : H) * g ∈ Gx t := hS'_le hs0S'
    have hcomm : t * (g⁻¹ * (s : H) * g) = (g⁻¹ * (s : H) * g) * t :=
      mem_Gx.mp hs0Gx
    calc (s : H) * y = (g * (g⁻¹ * (s : H) * g) * g⁻¹) * (g * t * g⁻¹) := by
          rw [hydef]; group
      _ = (g * t * g⁻¹) * (g * (g⁻¹ * (s : H) * g) * g⁻¹) := conj_comm hcomm
      _ = y * (s : H) := by rw [hydef]; group
  have hy2 : (⟨y, hyGx⟩ : ↥(Gx t)) ^ 2 = 1 := by
    apply Subtype.ext
    change y ^ 2 = (1 : H)
    have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
    rw [hydef]
    calc (g * t * g⁻¹) ^ 2 = (g * t * g⁻¹) * (g * t * g⁻¹) := by rw [pow_two]
      _ = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hy_zpow : (⟨y, hyGx⟩ : ↥(Gx t)) ∈ zpowers (GxSelf t) :=
    (hS ⟨y, hyGx⟩).1 ⟨hcent, hy2⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy_zpow
  have horder : orderOf (GxSelf t) = 2 := by
    change orderOf (⟨t, self_mem_Gx t⟩ : ↥(Gx t)) = 2
    rw [Subgroup.orderOf_mk, ht]
  have hmod_eq : (GxSelf t) ^ (k % 2) = (GxSelf t) ^ k := by
    have h2 : (2 : ℤ) = (orderOf (GxSelf t) : ℤ) := by rw [horder]; norm_num
    rw [h2]
    exact zpow_mod_orderOf _ _
  have hyne : y ≠ 1 := by
    intro hy1
    have ht1 : t = 1 := by
      have h := congrArg (fun z => g⁻¹ * z * g) hy1
      rw [hydef] at h
      have h2 : g⁻¹ * (g * t * g⁻¹) * g = t := by group
      rw [h2] at h
      simpa using h
    rw [ht1, orderOf_one] at ht
    omega
  rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
  · exfalso
    have hkz : (⟨y, hyGx⟩ : ↥(Gx t)) = 1 := by
      have h1 : (GxSelf t) ^ k = 1 := by rw [← hmod_eq, hk0, zpow_zero]
      rw [hk] at h1
      exact h1
    have hy1 : y = 1 := by simpa using congrArg (Subtype.val) hkz
    exact hyne hy1
  · have heq : GxSelf t = (⟨y, hyGx⟩ : ↥(Gx t)) := by
      have h1 : (GxSelf t) ^ k = GxSelf t := by rw [← hmod_eq, hk1, zpow_one]
      exact h1.symm.trans hk
    have hty : t = g * t * g⁻¹ := by
      have h := congrArg (fun z : ↥(Gx t) => (z : H)) heq
      change t = y at h
      rw [hydef] at h
      exact h
    rw [mem_Gx]
    have hconj : g * t * g⁻¹ = t := hty.symm
    calc t * g = (g * t * g⁻¹) * g := by rw [hconj]
      _ = g * t := by group

theorem segev28_isSylow (ht : orderOf t = 2) (S : Sylow 2 ↥(Gx t))
    (hS : ∀ x : ↥(Gx t),
      (x ∈ centerOf (S : Subgroup ↥(Gx t)) ∧ x ^ 2 = 1) ↔ x ∈ zpowers (GxSelf t)) :
    ∃ P : Sylow 2 H, (P : Subgroup H) = (S : Subgroup ↥(Gx t)).map (Gx t).subtype := by
  set S' : Subgroup H := (S : Subgroup ↥(Gx t)).map (Gx t).subtype with hS'def
  have hS'p : IsPGroup 2 S' := by
    rw [hS'def]
    exact S.isPGroup'.map (Gx t).subtype
  obtain ⟨Q, hS'Q⟩ := hS'p.exists_le_sylow
  refine ⟨Q, ?_⟩
  set K : Subgroup ↥(Gx t) := (((Q : Subgroup H) ⊓ Gx t).subgroupOf (Gx t)) with hKdef
  have hKp : IsPGroup 2 K := by
    let QI : Subgroup H := (Q : Subgroup H) ⊓ Gx t
    have hQinf : IsPGroup 2 QI :=
      IsPGroup.to_le (p := 2) Q.isPGroup' (inf_le_left : QI ≤ (Q : Subgroup H))
    rw [hKdef]
    exact hQinf.comap_of_injective (Gx t).subtype Subtype.coe_injective
  have hSK : (S : Subgroup ↥(Gx t)) ≤ K := by
    intro s hs
    rw [hKdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨hS'Q ⟨s, hs, rfl⟩, s.2⟩
  have hKS : K = (S : Subgroup ↥(Gx t)) := S.is_maximal' hKp hSK
  have hmapTop : (⊤ : Subgroup ↥Q).map (Q : Subgroup H).subtype = (Q : Subgroup H) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have htop : S'.subgroupOf Q = ⊤ := by
    by_contra hne
    have hlt : S'.subgroupOf Q < (⊤ : Subgroup ↥Q) := lt_of_le_of_ne le_top hne
    haveI : Group.IsNilpotent ↥Q := Q.isPGroup'.isNilpotent
    have hA : S'.subgroupOf Q <
        Subgroup.normalizer (((S'.subgroupOf Q : Subgroup ↥Q) : Set ↥Q)) :=
      Group.normalizerCondition_of_isNilpotent (G := ↥Q) (S'.subgroupOf Q) hlt
    obtain ⟨q, hqN, hqA⟩ := SetLike.exists_of_lt hA
    have hqN' : q ∈ (normalizer (S' : Set H)).subgroupOf Q := by
      rw [Subgroup.subgroupOf_normalizer_eq hS'Q]
      exact hqN
    have hqNormal : (q : H) ∈ normalizer (S' : Set H) := Subgroup.mem_subgroupOf.mp hqN'
    have hqGx : (q : H) ∈ Gx t := by
      rw [hS'def] at hqNormal
      exact segev28_normalizer_le ht S hS hqNormal
    have hqK : (⟨(q : H), hqGx⟩ : ↥(Gx t)) ∈ K := by
      rw [hKdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨q.2, hqGx⟩
    have hqS : (⟨(q : H), hqGx⟩ : ↥(Gx t)) ∈ (S : Subgroup ↥(Gx t)) := by
      rw [← hKS]
      exact hqK
    have hqS' : (q : H) ∈ S' := by
      rw [hS'def]
      exact ⟨⟨(q : H), hqGx⟩, hqS, rfl⟩
    exact hqA (Subgroup.mem_subgroupOf.mpr hqS')
  rw [← Subgroup.map_subgroupOf_eq_of_le hS'Q, htop, hmapTop]

theorem segev28_eq_top_of_mem (ht : orderOf t = 2)
    (hS : ∀ S : Sylow 2 ↥(Gx t), ∀ x : ↥(Gx t),
      (x ∈ centerOf (S : Subgroup ↥(Gx t)) ∧ x ^ 2 = 1) ↔ x ∈ zpowers (GxSelf t))
    (hgen : Gx t = closure ((Gx t : Set H) ∩ {x | IsConj t x}))
    {M : Subgroup H} (hM : M.Normal) (htM : t ∈ M) : M = ⊤ := by
  have hGxM : Gx t ≤ M := by
    rw [hgen, Subgroup.closure_le]
    rintro x ⟨hxGx, hxConj⟩
    change IsConj t x at hxConj
    rw [isConj_iff] at hxConj
    obtain ⟨c, hc⟩ := hxConj
    rw [← hc]
    exact hM.conj_mem t htM c
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := ↥(Gx t))
  obtain ⟨P, hP⟩ := segev28_isSylow ht S (hS S)
  have hS'Gx : (S : Subgroup ↥(Gx t)).map (Gx t).subtype ≤ Gx t := by
    rintro z ⟨s, -, rfl⟩
    exact s.2
  have hP_le_M : (P : Subgroup H) ≤ M := by
    rw [hP]
    exact hS'Gx.trans hGxM
  haveI : M.Normal := hM
  haveI : Finite (Sylow 2 ↥M) :=
    Finite.of_injective (fun P : Sylow 2 ↥M => (((P : Subgroup ↥M) : Set ↥M)))
      (fun P Q h => Sylow.ext (SetLike.ext' h))
  have hfr := Sylow.normalizer_sup_eq_top' (p := 2) P hP_le_M
  have hnormGx : normalizer (P : Set H) ≤ Gx t := by
    have h := segev28_normalizer_le ht S (hS S)
    rw [← hP] at h
    exact h
  have hnormM : normalizer (P : Set H) ≤ M := hnormGx.trans hGxM
  have htop : (⊤ : Subgroup H) ≤ M := by
    rw [← hfr]
    exact sup_le hnormM le_rfl
  exact top_le_iff.mp htop

theorem segev28_inv_of_not_mem (ht : orderOf t = 2)
    (hN : ∀ N : Subgroup ↥(Gx t), N.Normal → N ≠ ⊥ → GxSelf t ∈ N)
    {M : Subgroup H} (hM : M.Normal) (htM : t ∉ M) : ∀ m ∈ M, t * m * t⁻¹ = m⁻¹ := by
  haveI : M.Normal := hM
  have hNbot : M.subgroupOf (Gx t) = ⊥ := subgroupOf_Gx_eq_bot hN hM htM
  have hfix : ∀ m : ↥M, MulAut.conjNormal (H := M) t m = m → m = 1 := by
    intro m hm
    have hcoe : t * (m : H) * t⁻¹ = (m : H) := by
      simpa using congrArg (Subtype.val) hm
    have htcomm : t * (m : H) = (m : H) * t := (mul_inv_eq_iff_eq_mul).mp hcoe
    have hmemN : (⟨(m : H), mem_Gx.mpr htcomm⟩ : ↥(Gx t)) ∈ M.subgroupOf (Gx t) :=
      Subgroup.mem_subgroupOf.mpr m.2
    rw [hNbot] at hmemN
    have h1 := Subgroup.mem_bot.mp hmemN
    exact Subtype.ext (by simpa using congrArg (Subtype.val) h1)
  have hφinv : Function.Involutive (MulAut.conjNormal (H := M) t) := by
    intro m
    ext
    simp only [MulAut.conjNormal_apply]
    have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
    have hinv2 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
    calc t * (t * (m : H) * t⁻¹) * t⁻¹ = (t * t) * (m : H) * (t⁻¹ * t⁻¹) := by group
      _ = (m : H) := by rw [ht2, hinv2]; group
  have hφ : MonoidHom.FixedPointFree (MulAut.conjNormal (H := M) t) := hfix
  have hval := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive
    (φ := MulAut.conjNormal (H := M) t) hφ hφinv
  intro m hm
  have h2 := congrArg (Subtype.val) (congrFun hval ⟨m, hm⟩)
  simpa [MulAut.conjNormal_apply] using h2

theorem segev28_eq_bot_of_not_mem (ht : orderOf t = 2)
    (hcard : ∀ S : Sylow 2 ↥(Gx t), 2 < Nat.card S)
    (hgen : Gx t = closure ((Gx t : Set H) ∩ {x | IsConj t x}))
    (hN : ∀ N : Subgroup ↥(Gx t), N.Normal → N ≠ ⊥ → GxSelf t ∈ N)
    {M : Subgroup H} (hM : M.Normal) (htM : t ∉ M) : M = ⊥ := by
  haveI : M.Normal := hM
  have hinv : ∀ m ∈ M, t * m * t⁻¹ = m⁻¹ := segev28_inv_of_not_mem ht hN hM htM
  have hNbot : M.subgroupOf (Gx t) = ⊥ := subgroupOf_Gx_eq_bot hN hM htM
  have huinv : ∀ u, IsConj t u → ∀ m ∈ M, u * m * u⁻¹ = m⁻¹ := by
    intro u hu m hm
    rw [isConj_iff] at hu
    obtain ⟨c, rfl⟩ := hu
    have hcm : c⁻¹ * m * c ∈ M := by simpa using hM.conj_mem m hm c⁻¹
    calc (c * t * c⁻¹) * m * (c * t * c⁻¹)⁻¹
        = c * (t * (c⁻¹ * m * c) * t⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * m * c)⁻¹ * c⁻¹ := by rw [hinv (c⁻¹ * m * c) hcm]
      _ = m⁻¹ := by group
  have htuc : ∀ u, IsConj t u → ∀ m ∈ M, (t * u) * m * (t * u)⁻¹ = m := by
    intro u hu m hm
    calc (t * u) * m * (t * u)⁻¹ = t * (u * m * u⁻¹) * t⁻¹ := by group
      _ = t * m⁻¹ * t⁻¹ := by rw [huinv u hu m hm]
      _ = (t * m * t⁻¹)⁻¹ := by group
      _ = (m⁻¹)⁻¹ := by rw [hinv m hm]
      _ = m := by group
  set L : Subgroup ↥(Gx t) := (centralizer (M : Set H)).subgroupOf (Gx t) with hLdef
  have hLnorm : L.Normal := by
    rw [hLdef]
    exact Subgroup.Normal.subgroupOf
      (inferInstance : (centralizer (M : Set H)).Normal) (Gx t)
  by_cases hLbot : L = ⊥
  · exfalso
    have hu_eq_t : ∀ u ∈ Gx t, IsConj t u → u = t := by
      intro u huGx huConj
      have htuGx : t * u ∈ Gx t := (Gx t).mul_mem (self_mem_Gx t) huGx
      have htuC : (⟨t * u, htuGx⟩ : ↥(Gx t)) ∈ L := by
        rw [hLdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
        intro m hm
        exact ((mul_inv_eq_iff_eq_mul).mp (htuc u huConj m hm)).symm
      rw [hLbot] at htuC
      have h1 : (⟨t * u, htuGx⟩ : ↥(Gx t)) = 1 := Subgroup.mem_bot.mp htuC
      have htu1 : t * u = 1 := by simpa using congrArg (Subtype.val) h1
      have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
      calc u = t⁻¹ * (t * u) := by group
        _ = t⁻¹ := by rw [htu1, mul_one]
        _ = t := inv_eq_of_mul_eq_one_right ht2
    have hsubset : ((Gx t : Set H) ∩ {x | IsConj t x}) ⊆ {t} := by
      rintro u ⟨huGx, huConj⟩
      exact Set.mem_singleton_iff.mpr (hu_eq_t u huGx huConj)
    have hle : Gx t ≤ Subgroup.zpowers t := by
      calc Gx t = Subgroup.closure ((Gx t : Set H) ∩ {x | IsConj t x}) := hgen
        _ ≤ Subgroup.closure {t} := Subgroup.closure_mono hsubset
        _ = Subgroup.zpowers t := (Subgroup.zpowers_eq_closure t).symm
    have hcardGx : Nat.card ↥(Gx t) ≤ 2 := by
      have h1 : Nat.card (Gx t : Subgroup H) ≤ Nat.card (Subgroup.zpowers t) :=
        Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, ht] at h1
      exact h1
    obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := ↥(Gx t))
    have h1 : Nat.card (S : Subgroup ↥(Gx t)) ≤ Nat.card ↥(Gx t) :=
      Subgroup.card_le_card_group _
    have h2 : 2 < Nat.card (S : Subgroup ↥(Gx t)) := hcard S
    omega
  · rw [Subgroup.eq_bot_iff_forall]
    intro m hm
    have htL : GxSelf t ∈ L := hN L hLnorm hLbot
    have htC : t ∈ centralizer (M : Set H) := by
      have h := Subgroup.mem_subgroupOf.mp htL
      change t ∈ centralizer (M : Set H) at h
      exact h
    have hcomm : t * m = m * t := (Subgroup.mem_centralizer_iff.mp htC m hm).symm
    have hmN : (⟨m, mem_Gx.mpr hcomm⟩ : ↥(Gx t)) ∈ M.subgroupOf (Gx t) :=
      Subgroup.mem_subgroupOf.mpr hm
    rw [hNbot] at hmN
    have h1 := Subgroup.mem_bot.mp hmN
    exact by simpa using congrArg (Subtype.val) h1

theorem segev28_holds : Segev28 := by
  intro H _ _ t ht hS hgen hN
  have ht_ne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  haveI : Nontrivial H := nontrivial_of_ne t 1 ht_ne
  refine IsSimpleGroup.mk ?_
  intro N hNnormal
  by_cases htN : t ∈ N
  · right
    exact segev28_eq_top_of_mem ht (fun S => (hS S).1) hgen hNnormal htN
  · left
    exact segev28_eq_bot_of_not_mem ht (fun S => (hS S).2) hgen hN hNnormal htN

end CFSG.EvenSporadicStandard.HNRecog.Section3
