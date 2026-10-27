module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8Lift
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511D
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding Subgroup
section XLevel

variable {X : Type} [Group X] [Finite X]

theorem gnYComponent_conj_of_mem_aux1 {T₁ : Subgroup X} {t : X}
    (ht : t ∈ normalizer (T₁ : Set X)) :
    (centralizer (T₁ : Set X)).map (MulAut.conj t).toMonoidHom = centralizer (T₁ : Set X) :=
  map_conj_eq_of_conj_mem (conj_mem_centralizer_of_mem_normalizer ht)
    (conj_mem_centralizer_of_mem_normalizer (Subgroup.inv_mem _ ht) (t := t⁻¹)
      |> fun h' => by simpa using h')

theorem gnYComponent_conj_of_mem_aux2 {T₂ : Subgroup X} {t : X}
    (ht : t ∈ normalizer (T₂ : Set X)) :
    (normalizer (T₂ : Set X)).map (MulAut.conj t).toMonoidHom = normalizer (T₂ : Set X) :=
  map_conj_eq_of_conj_mem (fun x hx => Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hx)
      (Subgroup.inv_mem _ ht))
    (fun x hx => by
      simpa using Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) hx) ht)

theorem gnYComponent_conj_of_mem {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls) {x : X} (hx₁ : x ∈ normalizer (T₁ : Set X))
    (hx₂ : x ∈ normalizer (T₂ : Set X)) :
    GNYComponent T T₁ T₂ (Ls.map (MulAut.conj (toStar T x)).toMonoidHom) := by
  obtain ⟨hcomp, hC, hN⟩ := hLs
  refine ⟨isComponentOf_conj_aux hcomp _, ?_, ?_⟩
  · intro hle
    apply hC
    rw [← gnImg_map_conj_eq (T := T) (gnYComponent_conj_of_mem_aux1 hx₁)] at hle
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj (toStar T x)).injective).1 hle
  · intro hle
    apply hN
    rw [← gnImg_map_conj_eq (T := T) (gnYComponent_conj_of_mem_aux2 hx₂)] at hle
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj (toStar T x)).injective).1 hle

theorem ystar_normal_aux1 {Y : Type} [Group Y] (A : Subgroup Y) (a b : Y) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem ystar_normal_aux2 {Y : Type} [Group Y] (A : Subgroup Y) :
    A.map (MulAut.conj (1 : Y)).toMonoidHom = A := by
  ext x
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem ystar_normal_aux3 {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y} {g : Y}
    (hg : g ∈ normalizer (A : Set Y)) : A.map (MulAut.conj g).toMonoidHom = A :=
  map_conj_eq_of_conj_mem (fun x hx => (Subgroup.mem_normalizer_iff.1 hg x).1 hx)
    (fun x hx => (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * x * g)).2
      (by simpa [mul_assoc] using hx))

theorem ystar_normal_aux4 {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls) (huniq : ∀ Is, GNYComponent T T₁ T₂ Is → Is = Ls) {x : X}
    (hx₁ : x ∈ normalizer (T₁ : Set X)) (hx₂ : x ∈ normalizer (T₂ : Set X)) :
    Ls.map (MulAut.conj (toStar T x)).toMonoidHom = Ls :=
  huniq _ (gnYComponent_conj_of_mem hLs hx₁ hx₂)

theorem ystar_normal_aux5 {T T₁ T₂ : Subgroup X} (hg : IsGNPair T T₁ T₂) :
    normalizer (T : Set X) ≤ normalizer (T₁ : Set X) ⊓ normalizer (T₂ : Set X) :=
  le_inf (normalizer_le_normalizer_of_characteristic
      (hg.le_center.trans (omegaOneCenterOf_le_subgroup T)) hg.char₁)
    (normalizer_le_normalizer_of_characteristic hg.le₂ hg.char₂)

theorem ystar_normal_aux6 {T H : Subgroup X} {t : X}
    (hH : H.map (MulAut.conj t).toMonoidHom = H) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {L' : Subgroup (X ⧸ gnC T)} (hL' : CFSG.Open.IsComponentOf L' ⊤) (hcov : L' ≤ gnImg T H)
    (hne : L'.map (MulAut.conj (toStar T t)).toMonoidHom ≠ L')
    (hZ : ¬ q ∣ Nat.card (Subgroup.center ↥L')) (hdvd : q ∣ Nat.card ↥L') :
    2 ≤ CFSG.Open.pRank q H := by
  have hL'' : CFSG.Open.IsComponentOf (L'.map (MulAut.conj (toStar T t)).toMonoidHom) ⊤ :=
    isComponentOf_conj_aux hL' _
  have hB : (gnImg T H).map (MulAut.conj (toStar T t)).toMonoidHom = gnImg T H :=
    gnImg_map_conj_eq hH
  have hle'' : L'.map (MulAut.conj (toStar T t)).toMonoidHom ≤ gnImg T H := by
    rw [← hB]
    exact Subgroup.map_mono hcov
  have hdvd'' : q ∣ Nat.card ↥(L'.map (MulAut.conj (toStar T t)).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj (toStar T t)).injective]
  have h2 := two_le_pRank_of_two_components' (B := gnImg T H) hL' hL'' hne.symm hq hq2 hZ
    (by rwa [inf_eq_right.2 hcov]) (by rwa [inf_eq_right.2 hle''])
  exact two_le_pRank_of_map (toStar T) hq hq2 H h2

theorem ystar_normal_aux7 {T : Subgroup X} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (g : X) :
    CFSG.ABGLocalTools.IsSylowOf 2 (T.map (MulAut.conj g).toMonoidHom) ⊤ := by
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact hT.card_eq

theorem ystar_normal_aux8 {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) (hg : IsGNPair T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (huniq : ∀ Is, GNYComponent T T₁ T₂ Is → Is = Ls) (m : X)
    (hT : ∀ t ∈ T, (Ls.map (MulAut.conj (toStar T m)).toMonoidHom).map
      (MulAut.conj (toStar T t)).toMonoidHom = Ls.map (MulAut.conj (toStar T m)).toMonoidHom) :
    ∃ x ∈ normalizer (T : Set X), Ls.map (MulAut.conj (toStar T x)).toMonoidHom =
      Ls.map (MulAut.conj (toStar T m)).toMonoidHom := by
  set N : Subgroup X := (normalizer (Ls : Set (X ⧸ gnC T))).comap (toStar T)
  have hTN : T ≤ N := fun t ht => gnImg_le_normalizer_of_unique hg hLs huniq ⟨t, ht, rfl⟩
  have hT'N : T.map (MulAut.conj m⁻¹).toMonoidHom ≤ N := by
    rintro _ ⟨t, ht, rfl⟩
    show toStar T ((MulAut.conj m⁻¹).toMonoidHom t) ∈ normalizer (Ls : Set (X ⧸ gnC T))
    refine mem_normalizer_of_map_conj_eq_s15 ?_
    have hel : toStar T ((MulAut.conj m⁻¹).toMonoidHom t) =
        (toStar T m)⁻¹ * toStar T t * toStar T m := by
      simp [MulAut.conj_apply]
    rw [hel]
    calc Ls.map (MulAut.conj ((toStar T m)⁻¹ * toStar T t * toStar T m)).toMonoidHom
        = ((Ls.map (MulAut.conj (toStar T m)).toMonoidHom).map
            (MulAut.conj (toStar T t)).toMonoidHom).map
            (MulAut.conj (toStar T m)⁻¹).toMonoidHom := by
          rw [ystar_normal_aux1, ystar_normal_aux1]
      _ = (Ls.map (MulAut.conj (toStar T m)).toMonoidHom).map
            (MulAut.conj (toStar T m)⁻¹).toMonoidHom := by rw [hT t ht]
      _ = Ls := by rw [ystar_normal_aux1, inv_mul_cancel, ystar_normal_aux2]
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.2 hX.sylow
  obtain ⟨n, hnN, hn⟩ := normalizer_inf_le_of_sylow_aux2
    ((ystar_normal_aux7 hSyl m⁻¹).of_le hT'N le_top) (hSyl.of_le hTN le_top)
  rw [ystar_normal_aux1] at hn
  have hy : n * m⁻¹ ∈ normalizer (T : Set X) := mem_normalizer_of_map_conj_eq_s15 hn.symm
  have hx : m * n⁻¹ ∈ normalizer (T : Set X) := by simpa [mul_inv_rev] using Subgroup.inv_mem _ hy
  have hnLs : toStar T n ∈ normalizer (Ls : Set (X ⧸ gnC T)) := hnN
  refine ⟨m * n⁻¹, hx, ?_⟩
  calc Ls.map (MulAut.conj (toStar T (m * n⁻¹))).toMonoidHom
      = (Ls.map (MulAut.conj (toStar T n)⁻¹).toMonoidHom).map
          (MulAut.conj (toStar T m)).toMonoidHom := by
        rw [ystar_normal_aux1, map_mul, map_inv]
    _ = Ls.map (MulAut.conj (toStar T m)).toMonoidHom := by
        rw [ystar_normal_aux3 (Subgroup.inv_mem _ hnLs)]

theorem ystar_normal {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) (hg : IsGNPair T T₁ T₂)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h₁ : CFSG.Open.pRank q (Subgroup.normalizer (T₁ : Set X)) ≤ 1)
    (h₂ : CFSG.Open.pRank q (Subgroup.normalizer (T₂ : Set X)) ≤ 1)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (huniq : ∀ Is, GNYComponent T T₁ T₂ Is → Is = Ls)
    (hconj : ∀ g : X ⧸ gnC T,
      ¬ q ∣ Nat.card (Subgroup.center ↥(Ls.map (MulAut.conj g).toMonoidHom)) ∧
        q ∣ Nat.card ↥(Ls.map (MulAut.conj g).toMonoidHom)) :
    Ls.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (gnC T) g
  have key : Ls.map (MulAut.conj (toStar T m)).toMonoidHom = Ls := by
    by_contra hne
    have hL' : CFSG.Open.IsComponentOf (Ls.map (MulAut.conj (toStar T m)).toMonoidHom) ⊤ :=
      isComponentOf_conj_aux hLs.1 _
    have hcov : Ls.map (MulAut.conj (toStar T m)).toMonoidHom ≤
          gnImg T (centralizer (T₁ : Set X)) ∨
        Ls.map (MulAut.conj (toStar T m)).toMonoidHom ≤ gnImg T (normalizer (T₂ : Set X)) := by
      by_contra hcon
      rw [not_or] at hcon
      exact hne (huniq _ ⟨hL', hcon.1, hcon.2⟩)
    obtain ⟨hZ, hd⟩ := hconj (toStar T m)
    by_cases hmove : ∀ t ∈ T, (Ls.map (MulAut.conj (toStar T m)).toMonoidHom).map
        (MulAut.conj (toStar T t)).toMonoidHom = Ls.map (MulAut.conj (toStar T m)).toMonoidHom
    · obtain ⟨x, hx, hxeq⟩ := ystar_normal_aux8 hX hg hLs huniq m hmove
      have hx' := ystar_normal_aux5 hg hx
      exact hne (hxeq.symm.trans (ystar_normal_aux4 hLs huniq hx'.1 hx'.2))
    · push Not at hmove
      obtain ⟨t, ht, htne⟩ := hmove
      rcases hcov with hc | hc
      · have h2 := ystar_normal_aux6 (gnYComponent_conj_of_mem_aux1
          (IsGNPair.le_normalizer₁ hg ht)) hq hq2 hL' hc htne hZ hd
        have h3 := CFSG.SectionRank.pRank_mono (p := q) hq.one_lt
          (Subgroup.centralizer_le_normalizer (T₁ : Set X))
        omega
      · have h2 := ystar_normal_aux6 (gnYComponent_conj_of_mem_aux2
          (IsGNPair.le_normalizer₂ hg ht)) hq hq2 hL' hc htne hZ hd
        omega
  have hmem : (MulAut.conj (toStar T m)) n ∈ Ls.map (MulAut.conj (toStar T m)).toMonoidHom :=
    ⟨n, hn, rfl⟩
  rw [key] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem hLN_aux_eq_ystar_of_simple {T T₁ T₂ : Subgroup X}
    (hS : IsSimpleGroup ↥(Ystar T T₁ T₂)) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls) : Ls = Ystar T T₁ T₂ := by
  have hle : Ls ≤ Ystar T T₁ T₂ :=
    le_iSup₂ (f := fun L (_ : L ∈ {L : Subgroup (X ⧸ gnC T) | GNYComponent T T₁ T₂ L}) => L) Ls hLs
  have hnorm : Ystar T T₁ T₂ ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := by
    refine iSup₂_le fun J hJ => ?_
    by_cases hJL : J = Ls
    · subst hJL
      exact Subgroup.le_normalizer
    · have hc := kComp_holds.1 (X ⧸ gnC T) J Ls hJ.1 hLs.1 hJL
      have hcen : J ≤ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
      exact hcen.trans (Subgroup.centralizer_le_normalizer _)
  haveI : (Ls.subgroupOf (Ystar T T₁ T₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hnorm
  rcases hS.eq_bot_or_eq_top_of_normal (Ls.subgroupOf (Ystar T T₁ T₂)) with h | h
  · exfalso
    have hLsbot : Ls = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hle hx⟩ : ↥(Ystar T T₁ T₂)) ∈ Ls.subgroupOf (Ystar T T₁ T₂) := hx
      rw [h, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hx'
    have hs : IsSimpleGroup (↥Ls ⧸ Subgroup.center ↥Ls) := hLs.1.2.2.2
    obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
    apply hab
    have h3 : Subsingleton ↥Ls := by
      rw [hLsbot]; exact inferInstance
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a' b']
  · apply le_antisymm hle
    intro y hy
    have : (⟨y, hy⟩ : ↥(Ystar T T₁ T₂)) ∈ Ls.subgroupOf (Ystar T T₁ T₂) := by
      rw [h]; exact Subgroup.mem_top _
    exact this

end XLevel

section LThreeFacts

open KFactsPair

theorem hLN_aux_isLThreeTwo {S : Type} [Group S] (h : IsLThreeOfExp 1 S) :
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsLThreeTwo S := by
  rcases h with ⟨-, d, q, hq, hd, e⟩ | ⟨h, -⟩
  · exact ⟨d, ⟨q, hq, hd⟩, e⟩
  · omega

theorem hLN_aux_isSimpleGroup {S : Type} [Group S] (h : IsLThreeOfExp 1 S) : IsSimpleGroup S :=
  CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_simple (hLN_aux_isLThreeTwo h)

theorem hLN_aux_card_eq {S : Type} [Group S] (h : IsLThreeOfExp 1 S) : Nat.card S = 168 :=
  CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_card_eq (hLN_aux_isLThreeTwo h)

theorem isLThreeOfExp_one_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : IsLThreeOfExp 1 S) : IsLThreeOfExp 1 S' := by
  rcases h with ⟨h1, d, q, hq, hd, ⟨f⟩⟩ | ⟨h2, -⟩
  · exact Or.inl ⟨h1, d, q, hq, hd, ⟨e.symm.trans f⟩⟩
  · omega

theorem dvd_and_center_of_isLThreeOfExp_one {S : Type} [Group S] (h : IsLThreeOfExp 1 S) :
    7 ∣ Nat.card S ∧ Nat.card (Subgroup.center S) = 1 := by
  have hc := hLN_aux_card_eq h
  have hs := hLN_aux_isSimpleGroup h
  refine ⟨by rw [hc]; norm_num, ?_⟩
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h0 | h1
  · rw [h0, Subgroup.card_bot]
  · exfalso
    have hcomm : ∀ x y : S, x * y = y * x := fun x y =>
      Subgroup.mem_center_iff.mp (by rw [h1]; exact Subgroup.mem_top y) x
    let _ : CommGroup S := { ‹Group S› with mul_comm := hcomm }
    have hp := (CommGroup.is_simple_iff_prime_card (α := S)).1 hs
    rw [hc] at hp
    norm_num at hp

end LThreeFacts

section LiftLevel

open KFactsPair

theorem liftOf_normal {X : Type} [Group X] [Finite X] {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (h : LiftOf T L Ls) (hn : Ls.Normal) : L.Normal := by
  refine ⟨fun n hn' g => ?_⟩
  have hx : toStar T g ∈ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hn]
    exact Subgroup.mem_top _
  have hmap := liftOf_conj hX hLs h g hx
  have : g * n * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
    ⟨n, hn', by simp [MulAut.conj_apply]⟩
  rwa [hmap] at this

theorem hLN_of_rows_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hgn : GNSetting ↥M (T.subgroupOf M)) (hpair : IsGNPair (T.subgroupOf M) T₁ T₂)
    (hrN₁ : ∀ q ∈ sigmaM G M, CFSG.Open.pRank q (normalizer (T₁ : Set ↥M)) ≤ 1)
    (hrN₂ : ∀ q ∈ sigmaM G M, CFSG.Open.pRank q (normalizer (T₂ : Set ↥M)) ≤ 1)
    (h25 : Row1525 G M T T₁ T₂) (h27 : Row1527 G M T T₁ T₂) :
    ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls → L.Normal := by
  intro Ls L hLs hL
  have h7 : 7 ∈ sigmaM G M := by rw [h25.1]; exact rfl
  have hS : IsSimpleGroup ↥(Ystar (T.subgroupOf M) T₁ T₂) := hLN_aux_isSimpleGroup h27
  have huniq : ∀ Is, GNYComponent (T.subgroupOf M) T₁ T₂ Is → Is = Ls := fun Is hIs =>
    (hLN_aux_eq_ystar_of_simple hS hIs).trans (hLN_aux_eq_ystar_of_simple hS hLs).symm
  have h3 : IsLThreeOfExp 1 ↥Ls := h25.2 Ls L hLs hL
  have hconj : ∀ g : ↥M ⧸ gnC (T.subgroupOf M),
      ¬ 7 ∣ Nat.card (Subgroup.center ↥(Ls.map (MulAut.conj g).toMonoidHom)) ∧
        7 ∣ Nat.card ↥(Ls.map (MulAut.conj g).toMonoidHom) := by
    intro g
    have e : ↥Ls ≃* ↥(Ls.map (MulAut.conj g).toMonoidHom) :=
      Ls.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    obtain ⟨hd, hz⟩ := dvd_and_center_of_isLThreeOfExp_one (isLThreeOfExp_one_of_mulEquiv e h3)
    refine ⟨?_, hd⟩
    rw [hz]
    norm_num
  have hn := ystar_normal hgn hpair (q := 7) (by norm_num) (by norm_num)
    (hrN₁ 7 h7) (hrN₂ 7 h7) hLs huniq hconj
  exact liftOf_normal hgn hLs.1 hL hn

end LiftLevel

end CFSG.LocalAnalysis.RankThreeUC.S15
