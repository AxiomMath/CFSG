module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PG
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5AtlasProved

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open KFactsSmall

theorem normal_big_of_not_L3_aux_lthree {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {n : ℕ}
    (h : IsLThreeOfExp n S') : IsLThreeOfExp n S := by
  rcases h with ⟨h1, d, q, hq, hd, ⟨e'⟩⟩ | ⟨h2, d, Q, hQ, hQe, hd, ⟨e'⟩⟩
  · exact Or.inl ⟨h1, d, q, hq, hd, ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨h2, d, Q, hQ, hQe, hd, ⟨e.trans e'⟩⟩

theorem normal_big_of_not_L3_aux_cover {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : IsAltSixCoverThree S') : IsAltSixCoverThree S := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := h
  refine ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e hq, ?_, ⟨?_⟩⟩
  · rw [← hc, ← Subgroup.map_center_eq e]
    exact (Subgroup.card_map_of_injective e.injective).symm
  · exact (QuotientGroup.congr (Subgroup.center S) (Subgroup.center S') e
      (Subgroup.map_center_eq e)).trans f

theorem normal_big_of_not_L3_aux_comp {Y : Type} [Group Y] {Ls Js : Subgroup Y}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤) (hle : Ls ≤ Js) :
    CFSG.Open.IsComponentOf (Ls.subgroupOf Js) (⊤ : Subgroup ↥Js) := by
  obtain ⟨-, hsub, hqs⟩ := hLs
  refine ⟨le_top, ?_, ?_⟩
  · have hJ : CFSG.Open.IsSubnormal Ls Js := by
      have h := hsub.inf_of_le (le_top : Js ≤ ⊤)
      rwa [inf_eq_left.2 hle] at h
    exact CFSG.Open.IsSubnormal.of_mathlib hJ.subgroupOf
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) hqs

theorem normal_big_of_not_L3_aux_eq {Y : Type} [Group Y] {Ls Js : Subgroup Y}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤) (hle : Ls ≤ Js) (hJ : IsSimpleGroup ↥Js) : Ls = Js := by
  have hJs : CFSG.Open.IsSubnormal Ls Js := by
    have h := hLs.2.1.inf_of_le (le_top : Js ≤ ⊤)
    rwa [inf_eq_left.2 hle] at h
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hJs hJ with h | h
  · exact absurd h (liftOf_unique_aux2 hLs)
  · exact h

theorem normal_big_of_not_L3_aux_gen {W : Type} [Group W] [Finite W] {C : Subgroup W}
    (hC : CFSG.Open.IsComponentOf C ⊤) (S : Set (Subgroup W)) (hS : ∀ N ∈ S, N.Normal)
    (hgen : sSup S = ⊤) : ∃ N ∈ S, C ≤ N := by
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ N ∈ S, ⁅C, N⁆ = ⊥ := fun N hN => by
    rcases kComp_holds.2 W C N (hS N hN) hC with h | h
    · exact absurd h (hcon N hN)
    · exact h
  have hle : sSup S ≤ Subgroup.centralizer (C : Set W) := by
    refine sSup_le fun N hN => ?_
    have h1 := hcomm N hN
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
    exact h1
  rw [hgen] at hle
  apply liftOf_unique_aux1 hC
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact fun c _ => hle (Subgroup.mem_top c)

theorem normal_big_of_not_L3_aux_proj {W P : Type} [Group W] [Group P] [IsSimpleGroup P]
    {C : Subgroup W} (hsub : CFSG.Open.IsSubnormal C ⊤) (hbot : C ≠ ⊥) (π : W →* P)
    (hπ : Function.Surjective π) (hinj : ∀ c ∈ C, π c = 1 → c = 1) : Nonempty (↥C ≃* P) := by
  have hinj' : Function.Injective (π.comp C.subtype) := by
    rw [injective_iff_map_eq_one]
    intro c hc
    exact Subtype.ext (hinj c c.2 hc)
  have himg : C.map π = ⊤ := by
    have hmap := hsub.map π
    rw [Subgroup.map_top_of_surjective π hπ] at hmap
    rcases CFSG.Open.IsSubnormal.eq_bot_or_top hmap with h | h
    · exfalso
      apply hbot
      rw [eq_bot_iff]
      intro c hc
      have : π c ∈ C.map π := ⟨c, hc, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (hinj c hc this)
    · exact h
  have hrange : (π.comp C.subtype).range = ⊤ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, himg]
  exact ⟨(MonoidHom.ofInjective hinj').trans ((MulEquiv.subgroupCongr hrange).trans
    Subgroup.topEquiv)⟩

theorem normal_big_of_not_L3_aux_two {W P : Type} [Group W] [Finite W] [Group P] [IsSimpleGroup P]
    {C : Subgroup W} (hC : CFSG.Open.IsComponentOf C ⊤) (π₁ π₂ : W →* P)
    (h₁ : Function.Surjective π₁) (h₂ : Function.Surjective π₂)
    (hinj : ∀ w, π₁ w = 1 → π₂ w = 1 → w = 1)
    (hfac : ∀ w, ∃ n₁ n₂, π₂ n₁ = 1 ∧ π₁ n₂ = 1 ∧ w = n₁ * n₂) : Nonempty (↥C ≃* P) := by
  obtain ⟨N, hN, hCN⟩ := normal_big_of_not_L3_aux_gen hC {π₂.ker, π₁.ker}
    (by
      rintro N (rfl | hN)
      · exact MonoidHom.normal_ker _
      · rw [Set.mem_singleton_iff] at hN
        subst hN
        exact MonoidHom.normal_ker _)
    (by
      rw [sSup_pair, eq_top_iff]
      intro w _
      obtain ⟨n₁, n₂, hn₁, hn₂, rfl⟩ := hfac w
      exact Subgroup.mul_mem_sup (MonoidHom.mem_ker.2 hn₁) (MonoidHom.mem_ker.2 hn₂))
  have hbot := liftOf_unique_aux2 hC
  rcases hN with rfl | hN
  · exact normal_big_of_not_L3_aux_proj hC.2.1 hbot π₁ h₁
      (fun c hc h => hinj c h (MonoidHom.mem_ker.1 (hCN hc)))
  · rw [Set.mem_singleton_iff] at hN
    subst hN
    exact normal_big_of_not_L3_aux_proj hC.2.1 hbot π₂ h₂
      (fun c hc h => hinj c (MonoidHom.mem_ker.1 (hCN hc)) h)

theorem normal_big_of_not_L3_aux_three {W P : Type} [Group W] [Finite W] [Group P] [IsSimpleGroup P]
    {C : Subgroup W} (hC : CFSG.Open.IsComponentOf C ⊤) (π₁ π₂ π₃ : W →* P)
    (h₁ : Function.Surjective π₁) (h₂ : Function.Surjective π₂) (h₃ : Function.Surjective π₃)
    (hinj : ∀ w, π₁ w = 1 → π₂ w = 1 → π₃ w = 1 → w = 1)
    (hfac : ∀ w, ∃ n₁ n₂ n₃, (π₂ n₁ = 1 ∧ π₃ n₁ = 1) ∧ (π₁ n₂ = 1 ∧ π₃ n₂ = 1) ∧
      (π₁ n₃ = 1 ∧ π₂ n₃ = 1) ∧ w = n₁ * n₂ * n₃) : Nonempty (↥C ≃* P) := by
  obtain ⟨N, hN, hCN⟩ := normal_big_of_not_L3_aux_gen hC
    {π₂.ker ⊓ π₃.ker, π₁.ker ⊓ π₃.ker, π₁.ker ⊓ π₂.ker}
    (by
      intro N hN
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
      rcases hN with rfl | rfl | rfl <;>
        exact Subgroup.normal_inf_normal _ _)
    (by
      rw [sSup_insert, sSup_pair, eq_top_iff]
      intro w _
      obtain ⟨n₁, n₂, n₃, ⟨h12, h13⟩, ⟨h21, h23⟩, ⟨h31, h32⟩, rfl⟩ := hfac w
      rw [mul_assoc]
      exact Subgroup.mul_mem_sup
        (Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 h12, MonoidHom.mem_ker.2 h13⟩)
        (Subgroup.mul_mem_sup
          (Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 h21, MonoidHom.mem_ker.2 h23⟩)
          (Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 h31, MonoidHom.mem_ker.2 h32⟩)))
  have hbot := liftOf_unique_aux2 hC
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
  rcases hN with rfl | rfl | rfl
  · exact normal_big_of_not_L3_aux_proj hC.2.1 hbot π₁ h₁ (fun c hc h =>
      hinj c h (MonoidHom.mem_ker.1 (hCN hc).1) (MonoidHom.mem_ker.1 (hCN hc).2))
  · exact normal_big_of_not_L3_aux_proj hC.2.1 hbot π₂ h₂ (fun c hc h =>
      hinj c (MonoidHom.mem_ker.1 (hCN hc).1) h (MonoidHom.mem_ker.1 (hCN hc).2))
  · exact normal_big_of_not_L3_aux_proj hC.2.1 hbot π₃ h₃ (fun c hc h =>
      hinj c (MonoidHom.mem_ker.1 (hCN hc).1) (MonoidHom.mem_ker.1 (hCN hc).2) h)

theorem normal_big_of_not_L3_aux_sq {W P : Type} [Group W] [Finite W] [Group P] [IsSimpleGroup P]
    {C : Subgroup W} (hC : CFSG.Open.IsComponentOf C ⊤) (φ : W ≃* P × P) :
    Nonempty (↥C ≃* P) := by
  refine normal_big_of_not_L3_aux_two hC ((MonoidHom.fst P P).comp φ.toMonoidHom)
    ((MonoidHom.snd P P).comp φ.toMonoidHom) (Prod.fst_surjective.comp φ.surjective)
    (Prod.snd_surjective.comp φ.surjective) ?_ ?_
  · intro w h1 h2
    apply φ.injective
    rw [map_one]
    exact Prod.ext h1 h2
  · intro w
    refine ⟨φ.symm ((φ w).1, 1), φ.symm (1, (φ w).2), by simp, by simp, ?_⟩
    apply φ.injective
    simp

theorem normal_big_of_not_L3_aux_cube {W P : Type} [Group W] [Finite W] [Group P] [IsSimpleGroup P]
    {C : Subgroup W} (hC : CFSG.Open.IsComponentOf C ⊤) (φ : W ≃* P × P × P) :
    Nonempty (↥C ≃* P) := by
  refine normal_big_of_not_L3_aux_three hC ((MonoidHom.fst P (P × P)).comp φ.toMonoidHom)
    ((MonoidHom.fst P P).comp ((MonoidHom.snd P (P × P)).comp φ.toMonoidHom))
    ((MonoidHom.snd P P).comp ((MonoidHom.snd P (P × P)).comp φ.toMonoidHom))
    (Prod.fst_surjective.comp φ.surjective)
    (Prod.fst_surjective.comp (Prod.snd_surjective.comp φ.surjective))
    (Prod.snd_surjective.comp (Prod.snd_surjective.comp φ.surjective)) ?_ ?_
  · intro w h1 h2 h3
    apply φ.injective
    rw [map_one]
    exact Prod.ext h1 (Prod.ext h2 h3)
  · intro w
    refine ⟨φ.symm ((φ w).1, 1, 1), φ.symm (1, (φ w).2.1, 1), φ.symm (1, 1, (φ w).2.2),
      ⟨by simp, by simp⟩, ⟨by simp, by simp⟩, ⟨by simp, by simp⟩, ?_⟩
    apply φ.injective
    simp

theorem normal_big_of_not_L3_aux_le_eq {W : Type} [Group W] [Finite W] {C K : Subgroup W}
    (hC : CFSG.Open.IsComponentOf C ⊤) (hK : CFSG.Open.IsComponentOf K ⊤) (hCK : C ≤ K) :
    C = K := by
  by_contra hne
  have h := kComp_holds.1 W C K hC hK hne
  apply liftOf_unique_aux1 hC
  exact le_bot_iff.1 (h ▸ Subgroup.commutator_mono le_rfl hCK)

theorem normal_big_of_not_L3_aux_cp {W : Type} [Group W] [Finite W] {C K₁ K₂ : Subgroup W}
    (hC : CFSG.Open.IsComponentOf C ⊤) (h1 : IsAltSixCoverThree ↥K₁) (h2 : IsAltSixCoverThree ↥K₂)
    (hsup : K₁ ⊔ K₂ = ⊤) (hcent : K₁ ≤ Subgroup.centralizer (K₂ : Set W)) :
    IsAltSixCoverThree ↥C := by
  have hcent' : K₂ ≤ Subgroup.centralizer (K₁ : Set W) := fun y hy x hx =>
    (Subgroup.mem_centralizer_iff.1 (hcent hx) y hy).symm
  have hn : ∀ {A B : Subgroup W}, A ⊔ B = ⊤ → B ≤ Subgroup.centralizer (A : Set W) → A.Normal :=
    fun {A B} hAB hB => by
      refine Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 ?_)
      rw [← hAB]
      refine sup_le Subgroup.le_normalizer ?_
      rw [Subgroup.le_normalizer_iff]
      intro y hy k hk
      have := Subgroup.mem_centralizer_iff.1 (hB hy) k hk
      rw [← this, mul_inv_cancel_right]
      exact hk
  have hK₁ : K₁.Normal := hn hsup hcent'
  have hK₂ : K₂.Normal := hn (by rw [sup_comm]; exact hsup) hcent
  have hcomp : ∀ {K : Subgroup W}, K.Normal → IsAltSixCoverThree ↥K →
      CFSG.Open.IsComponentOf K ⊤ := fun {K} hK hq =>
    ⟨le_top, CFSG.Open.IsSubnormal.step le_top (hK.subgroupOf ⊤) (CFSG.Open.IsSubnormal.refl ⊤),
      hq.1⟩
  obtain ⟨N, hN, hCN⟩ := normal_big_of_not_L3_aux_gen hC {K₁, K₂}
    (by
      intro N hN
      rcases hN with rfl | hN
      · exact hK₁
      · rw [Set.mem_singleton_iff] at hN
        subst hN
        exact hK₂)
    (by rw [sSup_pair]; exact hsup)
  rcases hN with rfl | hN
  · exact normal_big_of_not_L3_aux_cover (MulEquiv.subgroupCongr
      (normal_big_of_not_L3_aux_le_eq hC (hcomp hK₁ h1) hCN)) h1
  · rw [Set.mem_singleton_iff] at hN
    subst hN
    exact normal_big_of_not_L3_aux_cover (MulEquiv.subgroupCongr
      (normal_big_of_not_L3_aux_le_eq hC (hcomp hK₂ h2) hCN)) h2

theorem normal_big_of_not_L3_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (hgn : GNSetting ↥M (T.subgroupOf M)) (h22 : Row1522 G M T T₁ T₂)
    (h24 : Row1524 G M T T₁ T₂) {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hnot : ¬ IsLThreeOfExp 1 ↥Ls) : L.Normal ∧ Big1525 ↥Ls := by
  have hcomp : CFSG.Open.IsComponentOf Ls ⊤ := hLs.1
  set Js := gnImg (T.subgroupOf M) (Subgroup.normalClosure (L : Set ↥M)) with hJs
  have hLJ : Ls ≤ Js := by
    rw [← hL.2]
    exact Subgroup.map_mono (fun x hx => Subgroup.subset_normalClosure hx)
  have hJnormal : Js.Normal :=
    Subgroup.Normal.map Subgroup.normalClosure_normal _ (QuotientGroup.mk'_surjective _)
  have hC := normal_big_of_not_L3_aux_comp hcomp hLJ
  rcases h22 Ls L hLs hL _ rfl _ rfl with h1 | ⟨hprod, -⟩ | hbig | ⟨hcp, -⟩
  ·
    exfalso
    obtain ⟨hs, -⟩ := small1522_simple_center (Or.inl h1)
    apply hnot
    rw [normal_big_of_not_L3_aux_eq hcomp hLJ hs]
    exact h1
  ·
    exfalso
    apply hnot
    rcases hprod with ⟨P, _, hP, ⟨φ⟩⟩ | ⟨P, _, hP, ⟨φ⟩⟩
    · obtain ⟨hs, -⟩ := small1522_simple_center (Or.inl hP)
      haveI := hs
      obtain ⟨e⟩ := normal_big_of_not_L3_aux_sq hC φ
      exact normal_big_of_not_L3_aux_lthree
        ((Subgroup.subgroupOfEquivOfLe hLJ).symm.trans e) hP
    · obtain ⟨hs, -⟩ := small1522_simple_center (Or.inl hP)
      haveI := hs
      obtain ⟨e⟩ := normal_big_of_not_L3_aux_cube hC φ
      exact normal_big_of_not_L3_aux_lthree
        ((Subgroup.subgroupOfEquivOfLe hLJ).symm.trans e) hP
  ·
    obtain ⟨hs, -⟩ := small1522_simple_center (Or.inr hbig)
    have heq := normal_big_of_not_L3_aux_eq hcomp hLJ hs
    refine ⟨⟨fun n hn g => ?_⟩, by rw [heq]; exact hbig⟩
    have hLsn : Ls.Normal := by rw [heq]; exact hJnormal
    have hx : toStar (T.subgroupOf M) g ∈
        Subgroup.normalizer (Ls : Set (↥M ⧸ gnC (T.subgroupOf M))) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    have hmap := liftOf_conj hgn hcomp hL g hx
    rw [← hmap]
    exact ⟨n, hn, rfl⟩
  ·
    exfalso
    obtain ⟨K₁, K₂, h1, h2, hsup, hcent, -, -⟩ := hcp
    exact h24 Ls L hLs hL (normal_big_of_not_L3_aux_cover (Subgroup.subgroupOfEquivOfLe hLJ).symm
      (normal_big_of_not_L3_aux_cp hC h1 h2 hsup hcent))

theorem exists_E9_of_order_three_aux_pair {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {a w : Y} (ha : orderOf a = p) (hw : orderOf w = p) (hcomm : a * w = w * a)
    (hnot : w ∉ Subgroup.zpowers a) :
    IsElemAbelian p (Subgroup.zpowers a ⊔ Subgroup.zpowers w) ∧
      Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers w : Subgroup Y) = p ^ 2 := by
  have hc : Commute a w := hcomm
  have hcz : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers w, x * y = y * x := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact (hc.zpow_zpow i j).eq
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcz
  have hA : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, ha]
  have hW : Nat.card (Subgroup.zpowers w) = p := by rw [Nat.card_zpowers, hw]
  have hpa : ∀ x ∈ Subgroup.zpowers a, x ^ p = 1 := by
    rintro x ⟨i, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ha, pow_orderOf_eq_one,
      one_zpow]
  have hpw : ∀ x ∈ Subgroup.zpowers w, x ^ p = 1 := by
    rintro x ⟨i, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hw, pow_orderOf_eq_one,
      one_zpow]
  have hinf1 : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers w : Subgroup Y) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers w : Subgroup Y) ∣ p := by
      rw [← hA]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact h
    · exfalso
      have h1 : Subgroup.zpowers a ⊓ Subgroup.zpowers w = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hA])
      have h2 : Subgroup.zpowers a ≤ Subgroup.zpowers w := h1 ▸ inf_le_right
      have h3 : Subgroup.zpowers a = Subgroup.zpowers w :=
        Subgroup.eq_of_le_of_card_ge h2 (by rw [hA, hW])
      exact hnot (h3 ▸ Subgroup.mem_zpowers w)
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · have hx : (x : Y) ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers w : Subgroup Y) : Set Y) := x.2
    have hy : (y : Y) ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers w : Subgroup Y) : Set Y) := y.2
    rw [hset] at hx hy
    obtain ⟨u, hu, v, hv, hxe⟩ := hx
    obtain ⟨u', hu', v', hv', hye⟩ := hy
    apply Subtype.ext
    change (x : Y) * y = y * x
    have c1 : Commute u u' := by
      obtain ⟨i, rfl⟩ := hu
      obtain ⟨j, rfl⟩ := hu'
      exact (Commute.refl a).zpow_zpow i j
    have c2 : Commute u v' := hcz u hu v' hv'
    have c3 : Commute v u' := (hcz u' hu' v hv).symm
    have c4 : Commute v v' := by
      obtain ⟨i, rfl⟩ := hv
      obtain ⟨j, rfl⟩ := hv'
      exact (Commute.refl w).zpow_zpow i j
    have c : Commute (u * v) (u' * v') :=
      Commute.mul_left (Commute.mul_right c1 c2) (Commute.mul_right c3 c4)
    have hxe' : u * v = (x : Y) := hxe
    have hye' : u' * v' = (y : Y) := hye
    rw [hxe', hye'] at c
    exact c
  · have hx' : x ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers w : Subgroup Y) : Set Y) := hx
    rw [hset] at hx'
    obtain ⟨u, hu, v, hv, rfl⟩ := hx'
    have c : Commute u v := hcz u hu v hv
    rw [c.mul_pow, hpa u hu, hpw v hv, one_mul]
  · rw [hA, hW, hinf1] at hcard
    simpa [sq] using hcard

theorem exists_E9_of_order_three_aux_conj {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {E₀ : Subgroup Y} (hE₀ : IsPGroup p E₀) (S : Sylow p Y) :
    ∃ g : Y, ∀ x ∈ E₀, g * x * g⁻¹ ∈ (S : Subgroup Y) := by
  obtain ⟨S₀, hS₀⟩ := hE₀.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S₀ S
  refine ⟨g, fun x hx => ?_⟩
  have h1 : g * x * g⁻¹ ∈ ((g • S₀ : Sylow p Y) : Subgroup Y) := by
    rw [Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (S₀ : Subgroup Y) (hS₀ hx)
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rwa [hg] at h1

theorem exists_E9_of_order_three_aux_w {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {E₀ : Subgroup Y} (hE₀ : IsElemAbelian p E₀) (hcard : p < Nat.card E₀) {a : Y}
    (ha : orderOf a = p) :
    ∃ w : Y, orderOf w = p ∧ a * w = w * a ∧ w ∉ Subgroup.zpowers a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hE₀p : IsPGroup p E₀ := fun x => ⟨1, Subtype.ext (by simpa using hE₀.2 x.1 x.2)⟩
  have hA : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, ha]
  have hza : IsPGroup p (Subgroup.zpowers a) := IsPGroup.of_card (n := 1) (by rw [hA, pow_one])
  obtain ⟨S, hS⟩ := hza.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_E9_of_order_three_aux_conj hE₀p S
  have haS : a ∈ (S : Subgroup Y) := hS (Subgroup.mem_zpowers a)
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; exact hp.one_lt.ne ha
  by_cases hz : ∀ s ∈ (S : Subgroup Y), a * s = s * a
  ·
    let E₁ : Subgroup Y := E₀.map (MulAut.conj g).toMonoidHom
    have hE₁S : E₁ ≤ (S : Subgroup Y) := by
      rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using hg x hx
    have hE₁card : Nat.card E₁ = Nat.card E₀ :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hex : ∃ w ∈ E₁, w ∉ Subgroup.zpowers a := by
      by_contra hall
      push Not at hall
      have hle : E₁ ≤ Subgroup.zpowers a := hall
      have := Subgroup.card_le_of_le hle
      rw [hE₁card, hA] at this
      omega
    obtain ⟨w, hwE, hwn⟩ := hex
    have hwp : w ^ p = 1 := by
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hwE
      rw [← map_pow, hE₀.2 x hx, map_one]
    have hw1 : w ≠ 1 := fun h => hwn (h ▸ Subgroup.one_mem _)
    exact ⟨w, orderOf_eq_prime hwp hw1, hz w (hE₁S hwE), hwn⟩
  ·
    push Not at hz
    obtain ⟨s, hsS, hs⟩ := hz
    have hSp : IsPGroup p (S : Subgroup Y) := S.isPGroup'
    haveI : Nontrivial (S : Subgroup Y) := ⟨⟨⟨a, haS⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
    haveI := hSp.center_nontrivial
    have hCp : IsPGroup p (Subgroup.center (S : Subgroup Y)) := hSp.to_subgroup _
    have hCdvd : p ∣ Nat.card (Subgroup.center (S : Subgroup Y)) := by
      rcases hCp.card_eq_or_dvd with h | h
      · exfalso
        have := Nat.card_eq_one_iff_unique.1 h
        obtain ⟨c, d, hcd⟩ := exists_pair_ne (Subgroup.center (S : Subgroup Y))
        exact hcd (this.1.elim c d)
      · exact h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hCdvd
    let w : Y := ((z : (S : Subgroup Y)) : Y)
    have hwo : orderOf w = p := by
      have h1 : orderOf (z : (S : Subgroup Y)) = p := (Subgroup.orderOf_coe z).trans hz
      exact (Subgroup.orderOf_coe (z : (S : Subgroup Y))).trans h1
    have hcen : ∀ t ∈ (S : Subgroup Y), t * w = w * t := fun t ht => by
      have := Subgroup.mem_center_iff.1 z.2 ⟨t, ht⟩
      exact congrArg Subtype.val this
    refine ⟨w, hwo, hcen a haS, fun hmem => hs ?_⟩
    have h1 : Subgroup.zpowers w ≤ Subgroup.zpowers a := (Subgroup.zpowers_le).2 hmem
    have h2 : Subgroup.zpowers w = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge h1 (by rw [hA, Nat.card_zpowers, hwo])
    have ha' : a ∈ Subgroup.zpowers w := h2 ▸ Subgroup.mem_zpowers a
    obtain ⟨k, hk⟩ := ha'
    rw [← hk]
    have hc : Commute s w := hcen s hsS
    exact (hc.symm.zpow_left k).eq

theorem exists_E9_of_order_three_aux_rank {Y : Type} [Group Y] [Finite Y] {H : Subgroup Y} {a w : Y}
    (haH : a ∈ H) (hwH : w ∈ H) (ha : orderOf a = 3) (hw : orderOf w = 3) (hcomm : a * w = w * a)
    (hnot : w ∉ Subgroup.zpowers a) : 2 ≤ CFSG.Open.pRank 3 H := by
  obtain ⟨hE, hcard⟩ := exists_E9_of_order_three_aux_pair Nat.prime_three ha hw hcomm hnot
  exact CFSG.SectionRank.le_pRank (by norm_num) (sup_le ((Subgroup.zpowers_le).2 haH)
    ((Subgroup.zpowers_le).2 hwH)) hE hcard

theorem exists_E9_of_order_three_aux_perm {α : Type} [Fintype α] [DecidableEq α]
    {H : Subgroup (Equiv.Perm α)} {a w : Equiv.Perm α} (haH : a ∈ H) (hwH : w ∈ H)
    (ha3 : a ^ 3 = 1) (hw3 : w ^ 3 = 1) (ha1 : a ≠ 1) (hw1 : w ≠ 1) (hcomm : a * w = w * a)
    (hfix : ∃ x, a x = x ∧ w x ≠ x) : 2 ≤ CFSG.Open.pRank 3 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hax, hwx⟩ := hfix
  refine exists_E9_of_order_three_aux_rank haH hwH (orderOf_eq_prime ha3 ha1)
    (orderOf_eq_prime hw3 hw1) hcomm fun hmem => ?_
  have hle : Subgroup.zpowers a ≤ MulAction.stabilizer (Equiv.Perm α) x :=
    (Subgroup.zpowers_le).2 (by rw [MulAction.mem_stabilizer_iff]; exact hax)
  have := hle hmem
  rw [MulAction.mem_stabilizer_iff] at this
  exact hwx this

theorem exists_E9_of_order_three_aux_alt6 :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 6))) := by
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact exists_E9_of_order_three_aux_perm
    (a := Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) (w := Equiv.swap 3 4 * Equiv.swap 4 5)
    (by rw [Equiv.Perm.mem_alternatingGroup]; decide)
    (by rw [Equiv.Perm.mem_alternatingGroup]; decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ⟨3, by decide⟩

theorem exists_E9_of_order_three_aux_alt8 :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 8))) := by
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact exists_E9_of_order_three_aux_perm
    (a := Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) (w := Equiv.swap 3 4 * Equiv.swap 4 5)
    (by rw [Equiv.Perm.mem_alternatingGroup]; decide)
    (by rw [Equiv.Perm.mem_alternatingGroup]; decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ⟨3, by decide⟩

theorem exists_E9_of_order_three_aux_zpowers {Y : Type} [Group Y] {a : Y} (ha : a ^ 3 = 1) {w : Y}
    (hw : w ∈ Subgroup.zpowers a) : w = 1 ∨ w = a ∨ w = a * a := by
  obtain ⟨k, rfl⟩ := hw
  show a ^ k = 1 ∨ a ^ k = a ∨ a ^ k = a * a
  have hk : k = k % 3 + 3 * (k / 3) := (Int.emod_add_mul_ediv k 3).symm
  have h3 : a ^ k = a ^ (k % 3) := by
    conv_lhs => rw [hk]
    rw [zpow_add, zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ha, one_zpow,
      mul_one]
  rw [h3]
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h]
  · left; exact zpow_zero a
  · right; left; exact zpow_one a
  · right; right; rw [zpow_two]

private def gl5a : GL (Fin 5) (ZMod 2) :=
  ⟨!![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![1, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1], by decide,
    by decide⟩

private def gl5w : GL (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0], by decide,
    by decide⟩

theorem exists_E9_of_order_three_aux_gl5 :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (GL (Fin 5) (ZMod 2))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : gl5a ^ 3 = 1 := by decide
  have hw3 : gl5w ^ 3 = 1 := by decide
  have ha1 : gl5a ≠ 1 := by decide
  have hw1 : gl5w ≠ 1 := by decide
  refine exists_E9_of_order_three_aux_rank (a := gl5a) (w := gl5w) trivial trivial
    (orderOf_eq_prime ha3 ha1) (orderOf_eq_prime hw3 hw1) (by decide) fun hmem => ?_
  rcases exists_E9_of_order_three_aux_zpowers ha3 hmem with h | h | h
  · exact hw1 h
  · revert h; decide
  · revert h; decide

theorem exists_E9_of_order_three_aux_big {S : Type} [Group S] [Finite S] (h : Big1525 S) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | h | h
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact exists_E9_of_order_three_aux_alt6
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact exists_E9_of_order_three_aux_alt8
  · obtain ⟨e⟩ := CFSG.AGLEmbeddingD2.McLaughlin.nonempty_equiv_G52_of_isL5Two
      (isL5Two_iff_isLinTwo_five.2 h)
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact exists_E9_of_order_three_aux_gl5
  · exact ((CFSG.AGLEmbeddingD2.McLaughlin.u33FactsExact_proved S h).2).ge

theorem exists_E9_of_order_three_gen {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L)
    (hbig : Big1525 ↥Ls) {A : Subgroup X} (hAL : A ≤ L) (hA : Nat.card A = 3) :
    ∃ E : Subgroup X, A ≤ E ∧ E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : 2 ≤ CFSG.Open.pRank 3 (L.map (toStar T)) := by
    rw [hl.lift.2, CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact exists_E9_of_order_three_aux_big hbig
  have h2 : 2 ≤ CFSG.Open.pRank 3 L :=
    two_le_pRank_of_map (toStar T) Nat.prime_three (by norm_num) L h1
  obtain ⟨E₀, hE₀L, hE₀, hE₀card⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L
  have hE' : IsElemAbelian 3 (E₀.subgroupOf L) := by
    have := hE₀.1
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext (hE₀.2 _ hx)⟩
    change ((a : L) : X) * ((b : L) : X) = ((b : L) : X) * ((a : L) : X)
    exact congrArg Subtype.val (mul_comm' (⟨(a : L), a.2⟩ : E₀) ⟨(b : L), b.2⟩)
  have hcard' : 3 < Nat.card (E₀.subgroupOf L) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀L).toEquiv, hE₀card]
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 L := Nat.pow_le_pow_right (by norm_num) h2
  have hAbot : A ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hA
    omega
  obtain ⟨a₀, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAbot
  have ha₀1' : (a₀ : X) ≠ 1 := fun h => ha₀1 (Subtype.ext h)
  have hord : orderOf (a₀ : X) = 3 := by
    have hdvd : orderOf (a₀ : X) ∣ 3 := by
      rw [Subgroup.orderOf_coe a₀, ← hA]
      exact orderOf_dvd_natCard a₀
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha₀1'
    · exact h
  have hAeq : Subgroup.zpowers (a₀ : X) = A := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 a₀.2) ?_
    rw [Nat.card_zpowers, hord, hA]
  have ha₀L : (a₀ : X) ∈ L := hAL a₀.2
  obtain ⟨w', hw'o, hw'c, hw'n⟩ := exists_E9_of_order_three_aux_w Nat.prime_three hE' hcard'
    (a := (⟨(a₀ : X), ha₀L⟩ : L)) (by rw [← Subgroup.orderOf_coe]; exact hord)
  have hwo : orderOf (w' : X) = 3 := by rw [Subgroup.orderOf_coe]; exact hw'o
  have hwc : (a₀ : X) * (w' : X) = (w' : X) * (a₀ : X) := congrArg Subtype.val hw'c
  have hwn : (w' : X) ∉ Subgroup.zpowers (a₀ : X) := by
    rintro ⟨k, hk⟩
    apply hw'n
    refine ⟨k, Subtype.ext ?_⟩
    simpa using hk
  obtain ⟨hE, hEcard⟩ := exists_E9_of_order_three_aux_pair Nat.prime_three hord hwo hwc hwn
  refine ⟨Subgroup.zpowers (a₀ : X) ⊔ Subgroup.zpowers (w' : X), ?_, ?_, hE, ?_⟩
  · exact hAeq.symm.le.trans le_sup_left
  · exact sup_le ((Subgroup.zpowers_le).2 ha₀L) ((Subgroup.zpowers_le).2 w'.2)
  · rw [hEcard]
    norm_num

end CFSG.LocalAnalysis.RankThreeUC.S15
