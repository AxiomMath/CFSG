module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenTrans
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenLayerGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenCompGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenOrbit

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {Q H E : Subgroup G}

namespace NineSettingGen

section Certified


theorem pLayerIn_le_of_three_components (h62 : NineSixTwoComp)
    (h : NineSettingGen G M 3 Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : 3 ∉ sigmaM G M)
    {C : Subgroup (StarGroup 3 H)} {q : StarGroup 3 H} (hq : q ∈ starImg 3 H Q)
    (hcomp : ∀ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D ↔
      ∃ i : Fin 3, D = C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom)
    (hinj : Function.Injective (fun i : Fin 3 => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom)) :
    pLayerIn 3 H ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hL
  have hm : ¬ CFSG.layer (StarGroup 3 H) ≤ starImg 3 H M :=
    fun hm => hL ((h.pLayerIn_le_iff).mpr hm)
  have hex : ∃ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D ∧
      ¬ D ≤ starImg 3 H M := by
    by_contra hcon
    refine hm (sSup_le fun D hD => ?_)
    by_contra hDM
    exact hcon ⟨D, hD, hDM⟩
  obtain ⟨D, hDcomp, hDnotle⟩ := hex
  obtain ⟨i₀, hi₀⟩ := (hcomp D).mp hDcomp
  let f : Fin 3 → Subgroup (StarGroup 3 H) :=
    fun i => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom
  have hf0 : f 0 = C := by
    show C.map (MulAut.conj (q ^ (0 : ℕ))).toMonoidHom = C
    rw [pow_zero, map_one]
    change C.map (MonoidHom.id (StarGroup 3 H)) = C
    rw [Subgroup.map_id]
  have hqM : q ∈ starImg 3 H M := starImg_mono h.Q_le_M hq
  have hfi₀ : (f 0).map (MulAut.conj (q ^ (i₀ : ℕ))).toMonoidHom = f i₀ := by
    rw [hf0]
  have hfnot₀ : ¬ f i₀ ≤ starImg 3 H M := by
    intro hx
    exact hDnotle (by rwa [hi₀])
  have hfnot0 : ¬ f 0 ≤ starImg 3 H M := by
    intro hle0
    have hgM : q ^ (i₀ : ℕ) ∈ starImg 3 H M := (starImg 3 H M).pow_mem hqM i₀
    have hfix : (starImg 3 H M).map
        (MulAut.conj (q ^ (i₀ : ℕ))).toMonoidHom = starImg 3 H M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.le_normalizer (H := starImg 3 H M)) hgM)
    have hmap : (f 0).map
        (MulAut.conj (q ^ (i₀ : ℕ))).toMonoidHom ≤ starImg 3 H M := by
      rw [← hfix]
      exact Subgroup.map_mono hle0
    have hlej : f i₀ ≤ starImg 3 H M := by
      rw [← hfi₀]
      exact hmap
    exact hfnot₀ hlej
  have hfnot : ∀ i : Fin 3, ¬ f i ≤ starImg 3 H M := by
    intro i hlei
    have hqi : q ^ (i : ℕ) ∈ starImg 3 H M := (starImg 3 H M).pow_mem hqM i
    have hfi : (f 0).map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom = f i := by
      rw [hf0]
    have hmap : (f 0).map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom ≤ starImg 3 H M := by
      rw [hfi]
      exact hlei
    exact hfnot0 (CFSG.AGLEmbedding.le_of_map_conj_le hqi hmap)
  have hfcomp_i : ∀ i : Fin 3, CFSG.IsComponent (f i) :=
    fun i => (hcomp (f i)).mpr ⟨i, rfl⟩
  have hexJ : ∀ i : Fin 3, ∃ J : Subgroup G, IsPComponentIn 3 J H ∧ starImg 3 H J = f i :=
    fun i => exists_isPComponentIn_starImg_eq (p := 3) (H := H) Nat.prime_three (hfcomp_i i)
  choose J hJ using hexJ
  have hJinj : Function.Injective J := by
    intro i j hij
    apply hinj
    have h1 : f i = f j := by rw [← (hJ i).2, ← (hJ j).2, hij]
    exact h1
  have hJnotM : ∀ i : Fin 3, ¬ J i ≤ M := by
    intro i hle
    have hstar : starImg 3 H (J i) ≤ starImg 3 H M := (h.le_iff_starImg_le (hJ i).1.1).mp hle
    rw [(hJ i).2] at hstar
    exact hfnot i hstar
  have hsub : Set.range J ⊆ {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} := by
    rintro _ ⟨i, rfl⟩
    exact ⟨(hJ i).1, hJnotM i⟩
  have hbound := h62 G M Q H E 3 h hH2 hp hL
  have hcard : (Set.range J).ncard = 3 := by
    rw [Set.ncard_range_of_injective hJinj]
    simp
  have hle2 : (Set.range J).ncard ≤ 2 := (Set.ncard_le_ncard hsub).trans hbound
  omega

theorem not_starImg_le_compNormalizer (h713 : SevenOneThree) (hI : NineTenInputs)
    (h : NineSettingGen G M 3 Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : 3 ∉ sigmaM G M)
    (hU : NineNineOne M 3) (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q H) (hLM : pLayerIn 3 H ≤ M)
    (hY : centralizer (CFSG.layer (StarGroup 3 H) : Set (StarGroup 3 H)) = ⊥) :
    ¬ starImg 3 H E ≤ compNormalizer (StarGroup 3 H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hE
  let π : ↥H →* StarGroup 3 H := QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)
  let N : Subgroup G := ((compNormalizer (StarGroup 3 H)).comap π).map H.subtype
  have hNsub : N.subgroupOf H = (compNormalizer (StarGroup 3 H)).comap π := by
    dsimp only [N]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hstarN : starImg 3 H N = compNormalizer (StarGroup 3 H) := by
    have h1 : starImg 3 H N = ((compNormalizer (StarGroup 3 H)).comap π).map π := by
      rw [starImg, hNsub]
    rw [h1]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hSsub : (Q ⊓ N).subgroupOf H = Q.subgroupOf H ⊓ N.subgroupOf H :=
    Subgroup.comap_inf Q N H.subtype
  have hSstar : starImg 3 H (Q ⊓ N) =
      starImg 3 H Q ⊓ compNormalizer (StarGroup 3 H) := by
    rw [starImg, hSsub, hNsub, Subgroup.map_inf_comap (Q.subgroupOf H)
      (compNormalizer (StarGroup 3 H)) π]
    rfl
  haveI hNnorm : (compNormalizer (StarGroup 3 H)).Normal := compNormalizer_normal
  have hb : CFSG.ABGLocalTools.IsSylowOf 3
      (starImg 3 H Q ⊓ compNormalizer (StarGroup 3 H))
      (compNormalizer (StarGroup 3 H)) :=
    (h.isSylowOf_starImg_top hQ).inf_of_le_normalizer le_top
      (le_of_eq (Subgroup.normalizer_eq_top (H := compNormalizer (StarGroup 3 H))).symm)
  have hEN : E ≤ N := by
    intro e he
    have heH : e ∈ H := h.stdE.2.1.trans h.Q_le_H he
    have hπe : π ⟨e, heH⟩ ∈ compNormalizer (StarGroup 3 H) :=
      hE (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr he))
    exact Subgroup.mem_map.mpr ⟨⟨e, heH⟩, Subgroup.mem_comap.mpr hπe, rfl⟩
  have hES : E ≤ Q ⊓ N := le_inf h.stdE.2.1 hEN
  have hd : normalizer (starImg 3 H Q ⊓ compNormalizer (StarGroup 3 H) :
      Set (StarGroup 3 H)) ≤ starImg 3 H M := by
    have hSH : Q ⊓ N ≤ H := inf_le_left.trans h.Q_le_H
    have hSM : Q ⊓ N ≤ M := inf_le_left.trans h.Q_le_M
    have hSp : IsPGroup 3 ↥(Q ⊓ N) := (QSet.isPGroup_of_mem h.mem_Q).to_le inf_le_left
    have h := h.normalizer_starImg_le_of_le hU hSH hSM hSp hES
    rwa [hSstar] at h
  have he : compNormalizer (StarGroup 3 H) ≤ starImg 3 H M := by
    have h1 := le_inf_sup_starImg_of_le h713 hI h hH2 hp
      (B := compNormalizer (StarGroup 3 H))
      (S := starImg 3 H Q ⊓ compNormalizer (StarGroup 3 H)) le_rfl hb hd
    have hLle : CFSG.layer (StarGroup 3 H) ≤ starImg 3 H M := (h.pLayerIn_le_iff).mp hLM
    rw [hY, sup_bot_eq] at h1
    exact h1.trans (sup_le (inf_le_right.trans hLle) le_rfl)
  obtain ⟨P, hP⟩ := hb
  have hfr := Sylow.normalizer_sup_eq_top P
  rw [hP] at hfr
  have htop : (⊤ : Subgroup (StarGroup 3 H)) ≤ starImg 3 H M := by
    rw [← hfr]
    exact sup_le hd he
  refine h.not_le ((h.le_iff_starImg_le (A := H) le_rfl).mpr ?_)
  rwa [starImg_self]

private theorem exists_moving_component_data (h : NineSettingGen G M 3 Q H E 2)
    {C : Subgroup (StarGroup 3 H)} {q : StarGroup 3 H}
    (hcomp : ∀ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D ↔
      ∃ i : Fin 3, D = C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom)
    (hinj : Function.Injective (fun i : Fin 3 => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom))
    (hE : ¬ starImg 3 H E ≤ compNormalizer (StarGroup 3 H)) :
    ∃ (x₀ : StarGroup 3 H) (_ : x₀ ∈ starImg 3 H E) (D₀ : Subgroup (StarGroup 3 H))
      (_ : CFSG.IsComponent D₀) (_ : x₀ ∉ normalizer (D₀ : Set (StarGroup 3 H))),
      orderOf x₀ = 3 ∧
      (∀ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D ↔
        ∃ i : Fin 3, D = D₀.map (MulAut.conj (x₀ ^ (i : ℕ))).toMonoidHom) ∧
      Function.Injective (fun i : Fin 3 =>
        D₀.map (MulAut.conj (x₀ ^ (i : ℕ))).toMonoidHom) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₀, hx₀E, hx₀N⟩ : ∃ x ∈ starImg 3 H E, x ∉ compNormalizer (StarGroup 3 H) := by
    by_contra hcon
    exact hE fun x hx => by
      by_contra hxN
      exact hcon ⟨x, hx, hxN⟩
  obtain ⟨D₀, hD₀comp, hx₀notnorm⟩ : ∃ D₀ : Subgroup (StarGroup 3 H),
      CFSG.IsComponent D₀ ∧ x₀ ∉ normalizer (D₀ : Set (StarGroup 3 H)) := by
    by_contra hcon
    exact hx₀N ((mem_compNormalizer_iff).mpr fun D hD => by
      by_contra hxN
      exact hcon ⟨D, hD, hxN⟩)
  have hx₀pow : x₀ ^ 3 = 1 := by
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx₀E
    rw [← map_pow,
      show e ^ 3 = 1 from Subtype.ext (h.stdE.2.2.1.2 (e : G) (Subgroup.mem_subgroupOf.mp he)),
      map_one]
  have hx₀ne : x₀ ≠ 1 := by
    intro h1
    exact hx₀N (by rw [h1]; exact (compNormalizer (StarGroup 3 H)).one_mem)
  have hx₀ord : orderOf x₀ = 3 := orderOf_eq_prime hx₀pow hx₀ne
  let g : Fin 3 → Subgroup (StarGroup 3 H) :=
    fun i => D₀.map (MulAut.conj (x₀ ^ (i : ℕ))).toMonoidHom
  have hginj : Function.Injective g :=
    conj_pow_injective (p := 3) (n := 1) Nat.prime_three (by simpa using hx₀ord) hx₀notnorm
  have hgcomp : ∀ i : Fin 3, CFSG.IsComponent (g i) :=
    fun i => CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (x₀ ^ (i : ℕ))) hD₀comp
  have hgsub : Set.range g ⊆ Set.range
      (fun i : Fin 3 => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom) := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := (hcomp (g i)).mp (hgcomp i)
    exact ⟨j, hj.symm⟩
  have hcardg : (Set.range g).ncard = 3 := by
    rw [Set.ncard_range_of_injective hginj]
    simp
  have hcardf : (Set.range
      (fun i : Fin 3 => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom)).ncard = 3 := by
    rw [Set.ncard_range_of_injective hinj]
    simp
  have heq : Set.range g = Set.range
      (fun i : Fin 3 => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom) :=
    Set.eq_of_subset_of_ncard_le hgsub (by omega)
  have hcorr : ∀ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D ↔ ∃ i : Fin 3, D = g i := by
    intro D
    constructor
    · intro hD
      have hmem : D ∈ Set.range
          (fun i : Fin 3 => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom) := by
        obtain ⟨i, hi⟩ := (hcomp D).mp hD
        exact ⟨i, hi.symm⟩
      rw [← heq] at hmem
      obtain ⟨i, hi⟩ := hmem
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      exact hgcomp i
  exact ⟨x₀, hx₀E, D₀, hD₀comp, hx₀notnorm, hx₀ord, hcorr, hginj⟩

theorem exists_conj_of_three_components (h : NineSettingGen G M 3 Q H E 2)
    {C : Subgroup (StarGroup 3 H)} {q : StarGroup 3 H}
    (hcomp : ∀ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D ↔
      ∃ i : Fin 3, D = C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom)
    (hinj : Function.Injective (fun i : Fin 3 => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom))
    (hE : ¬ starImg 3 H E ≤ compNormalizer (StarGroup 3 H)) {D D' : Subgroup (StarGroup 3 H)}
    (hD : CFSG.IsComponent D) (hD' : CFSG.IsComponent D') :
    ∃ x ∈ starImg 3 H E, D' = D.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨x₀, hx₀E, D₀, hD₀comp, hx₀notnorm, hx₀ord, hcorr, hginj⟩ :=
    exists_moving_component_data h hcomp hinj hE
  let g : Fin 3 → Subgroup (StarGroup 3 H) :=
    fun i => D₀.map (MulAut.conj (x₀ ^ (i : ℕ))).toMonoidHom
  obtain ⟨i, hi⟩ := (hcorr D).mp hD
  obtain ⟨j, hj⟩ := (hcorr D').mp hD'
  let x : StarGroup 3 H := x₀ ^ (j : ℕ) * (x₀ ^ (i : ℕ))⁻¹
  refine ⟨x, ?_, ?_⟩
  · exact (starImg 3 H E).mul_mem ((starImg 3 H E).pow_mem hx₀E j)
      ((starImg 3 H E).inv_mem ((starImg 3 H E).pow_mem hx₀E i))
  · rw [hj, hi]
    have hmul : x * x₀ ^ (i : ℕ) = x₀ ^ (j : ℕ) := by
      dsimp only [x]
      group
    calc g j = D₀.map (MulAut.conj (x₀ ^ (j : ℕ))).toMonoidHom := rfl
      _ = D₀.map (MulAut.conj (x * x₀ ^ (i : ℕ))).toMonoidHom := by rw [hmul]
      _ = (D₀.map (MulAut.conj (x₀ ^ (i : ℕ))).toMonoidHom).map
            (MulAut.conj x).toMonoidHom :=
            (Subgroup.map_conj_map_conj D₀ (x₀ ^ (i : ℕ)) x).symm
      _ = (g i).map (MulAut.conj x).toMonoidHom := rfl

theorem exists_ne_one_mem_compNormalizer (h : NineSettingGen G M 3 Q H E 2)
    {C : Subgroup (StarGroup 3 H)} {q : StarGroup 3 H}
    (hcomp : ∀ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D ↔
      ∃ i : Fin 3, D = C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom)
    (hinj : Function.Injective (fun i : Fin 3 => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom))
    (hE : ¬ starImg 3 H E ≤ compNormalizer (StarGroup 3 H)) :
    ∃ y ∈ starImg 3 H E, y ≠ 1 ∧ y ∈ compNormalizer (StarGroup 3 H) := by
  obtain ⟨x₀, hx₀E, D₀, hD₀comp, hx₀notnorm, hx₀ord, hcorr, hginj⟩ :=
    exists_moving_component_data h hcomp hinj hE
  let g : Fin 3 → Subgroup (StarGroup 3 H) :=
    fun i => D₀.map (MulAut.conj (x₀ ^ (i : ℕ))).toMonoidHom
  have hEcard : Nat.card (starImg 3 H E) = 9 := by
    have hAH : E ≤ H := h.stdE.2.1.trans h.Q_le_H
    have hpE : IsPGroup 3 E := fun g => ⟨1, by
      refine Subtype.ext ?_
      have hg := h.stdE.2.2.1.2 (g : G) g.2
      simpa using hg⟩
    rw [card_starImg_eq Nat.prime_three hAH hpE, h.stdE.2.2.2.1]
    norm_num
  have hx₀card : Nat.card (Subgroup.zpowers x₀) = 3 := by
    rw [Nat.card_zpowers, hx₀ord]
  have hex : ∃ e ∈ starImg 3 H E, e ∉ Subgroup.zpowers x₀ := by
    by_contra hcon
    have hle : starImg 3 H E ≤ Subgroup.zpowers x₀ := by
      intro x hx
      by_contra hxz
      exact hcon ⟨x, hx, hxz⟩
    have hle' := Subgroup.card_le_of_le hle
    have h9 : (9 : ℕ) ≤ 3 := by
      calc (9 : ℕ) = Nat.card (starImg 3 H E) := hEcard.symm
        _ ≤ Nat.card (Subgroup.zpowers x₀) := hle'
        _ = 3 := hx₀card
    omega
  obtain ⟨e, heE, hez⟩ := hex
  have hcomp_e : CFSG.IsComponent (D₀.map (MulAut.conj e).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj e) hD₀comp
  obtain ⟨i, hi⟩ := (hcorr (D₀.map (MulAut.conj e).toMonoidHom)).mp hcomp_e
  let y : StarGroup 3 H := (x₀ ^ (i : ℕ))⁻¹ * e
  have hyE : y ∈ starImg 3 H E :=
    (starImg 3 H E).mul_mem ((starImg 3 H E).inv_mem ((starImg 3 H E).pow_mem hx₀E i)) heE
  have hyne : y ≠ 1 := by
    intro hy
    apply hez
    have h1 : x₀ ^ (i : ℕ) * y = e := by
      dsimp only [y]
      group
    rw [hy, mul_one] at h1
    rw [← h1]
    exact Subgroup.npow_mem_zpowers x₀ i
  have hyD₀ : D₀.map (MulAut.conj y).toMonoidHom = D₀ := by
    have h1 : D₀.map (MulAut.conj y).toMonoidHom =
        (D₀.map (MulAut.conj e).toMonoidHom).map
          (MulAut.conj ((x₀ ^ (i : ℕ))⁻¹)).toMonoidHom := by
      rw [show y = (x₀ ^ (i : ℕ))⁻¹ * e from rfl,
        Subgroup.map_conj_map_conj D₀ e ((x₀ ^ (i : ℕ))⁻¹)]
    rw [h1, hi]
    change (D₀.map (MulAut.conj (x₀ ^ (i : ℕ))).toMonoidHom).map
        (MulAut.conj ((x₀ ^ (i : ℕ))⁻¹)).toMonoidHom = D₀
    rw [Subgroup.map_conj_map_conj D₀ (x₀ ^ (i : ℕ)) ((x₀ ^ (i : ℕ))⁻¹),
      inv_mul_cancel]
    rw [map_one]
    change D₀.map (MonoidHom.id (StarGroup 3 H)) = D₀
    rw [Subgroup.map_id]
  have hycomm : ∀ j : Fin 3, y * x₀ ^ (j : ℕ) = x₀ ^ (j : ℕ) * y := by
    intro j
    haveI : IsMulCommutative ↥(starImg 3 H E) := by
      haveI : IsMulCommutative ↥E := h.stdE.2.2.1.1
      show IsMulCommutative ↥((E.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)))
      infer_instance
    have h1 := (inferInstance : IsMulCommutative ↥(starImg 3 H E)).is_comm.comm
      (⟨y, hyE⟩ : ↥(starImg 3 H E))
      (⟨x₀ ^ (j : ℕ), (starImg 3 H E).pow_mem hx₀E j⟩ : ↥(starImg 3 H E))
    exact congrArg Subtype.val h1
  refine ⟨y, hyE, hyne, ?_⟩
  rw [mem_compNormalizer_iff]
  intro D hD
  obtain ⟨j, hj⟩ := (hcorr D).mp hD
  rw [hj, Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 : (g j).map (MulAut.conj y).toMonoidHom =
      (D₀.map (MulAut.conj y).toMonoidHom).map
        (MulAut.conj (x₀ ^ (j : ℕ))).toMonoidHom := by
    change (D₀.map (MulAut.conj (x₀ ^ (j : ℕ))).toMonoidHom).map
        (MulAut.conj y).toMonoidHom =
      (D₀.map (MulAut.conj y).toMonoidHom).map
        (MulAut.conj (x₀ ^ (j : ℕ))).toMonoidHom
    rw [Subgroup.map_conj_map_conj D₀ (x₀ ^ (j : ℕ)) y,
      Subgroup.map_conj_map_conj D₀ y (x₀ ^ (j : ℕ)), hycomm j]
  have hgj : D₀.map (MulAut.conj (x₀ ^ (j : ℕ))).toMonoidHom = g j := rfl
  calc (g j).map (MulAut.conj y).toMonoidHom
      = (D₀.map (MulAut.conj y).toMonoidHom).map
          (MulAut.conj (x₀ ^ (j : ℕ))).toMonoidHom := h1
    _ = D₀.map (MulAut.conj (x₀ ^ (j : ℕ))).toMonoidHom := by rw [hyD₀]
    _ = g j := hgj

theorem nineTenTwo_list (h : NineSettingGen G M 3 Q H E 2) {C : Subgroup (StarGroup 3 H)}
    {q : StarGroup 3 H}
    (hcomp : ∀ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D ↔
      ∃ i : Fin 3, D = C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom)
    (hinj : Function.Injective (fun i : Fin 3 => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom))
    (hrank : ∀ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D → CFSG.Open.pRank 3 D = 1)
    (hE : ¬ starImg 3 H E ≤ compNormalizer (StarGroup 3 H)) :
    ∃ S : Set (Subgroup G), S.ncard = 3 ∧
      (∀ J ∈ S, IsPComponentIn 3 J H ∧ CFSG.Open.pRank 3 J = 1) ∧ pLayerIn 3 H = sSup S ∧
      ∀ J ∈ S, ∀ J' ∈ S, ∃ e ∈ E, J' = J.map (MulAut.conj e).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : Fin 3 → Subgroup (StarGroup 3 H) :=
    fun i => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom
  have hfcomp : ∀ i : Fin 3, CFSG.IsComponent (f i) :=
    fun i => (hcomp (f i)).mpr ⟨i, rfl⟩
  have hexJ : ∀ i : Fin 3, ∃ J : Subgroup G, IsPComponentIn 3 J H ∧ starImg 3 H J = f i :=
    fun i => exists_isPComponentIn_starImg_eq (p := 3) (H := H) Nat.prime_three (hfcomp i)
  choose J hJ using hexJ
  have hJinj : Function.Injective J := by
    intro i j hij
    apply hinj
    have h1 : f i = f j := by rw [← (hJ i).2, ← (hJ j).2, hij]
    exact h1
  refine ⟨Set.range J, ?_, ?_, ?_, ?_⟩
  · rw [Set.ncard_range_of_injective hJinj]
    simp
  · rintro _ ⟨i, rfl⟩
    refine ⟨(hJ i).1, ?_⟩
    rw [← pRank_starImg_eq (p := 3) (H := H) (A := J i) Nat.prime_three (hJ i).1.1, (hJ i).2]
    exact hrank (f i) (hfcomp i)
  · apply le_antisymm
    · rw [pLayerIn, Subgroup.map_le_iff_le_comap, CFSG.pLayer]
      refine sSup_le fun L hL => ?_
      have hLmem : L.map H.subtype ∈ Set.range J := by
        have hcompL : CFSG.IsComponent (starImg 3 H (L.map H.subtype)) :=
          isComponent_starImg (isPComponentIn_map_subtype hL)
        obtain ⟨i, hi⟩ := (hcomp (starImg 3 H (L.map H.subtype))).mp hcompL
        refine ⟨i, eq_of_starImg_eq Nat.prime_three (hJ i).1 (isPComponentIn_map_subtype hL)
          (by rw [(hJ i).2, hi])⟩
      intro z hz
      exact le_sSup hLmem (Subgroup.mem_map_of_mem H.subtype hz)
    · refine sSup_le ?_
      rintro _ ⟨i, rfl⟩
      exact le_pLayerIn (hJ i).1
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨x, hxE, hxeq⟩ := exists_conj_of_three_components h hcomp hinj hE
      (isComponent_starImg (hJ i).1) (isComponent_starImg (hJ j).1)
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxE
    refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, ?_⟩
    refine eq_of_starImg_eq Nat.prime_three (hJ j).1
      (isPComponentIn_conj (hJ i).1 y.2) ?_
    rw [starImg_map_conj]
    exact hxeq

end Certified

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
