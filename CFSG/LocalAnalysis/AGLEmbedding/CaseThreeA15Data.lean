module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA15Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA15DataAux
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Transfer

variable {G : Type} [Group G] [Finite G] {p : ℕ} {H : Subgroup G}

theorem eq_of_mk_primeComplementCore_eq [Fact p.Prime] {R : Subgroup G} (hR : IsPGroup p R)
    {a b : H} (ha : (a : G) ∈ R) (hb : (b : G) ∈ R)
    (hab : QuotientGroup.mk' (primeComplementCore (G := H) p) a =
      QuotientGroup.mk' (primeComplementCore (G := H) p) b) : a = b := by
  have h1 : ((a⁻¹ * b : H) : G) ∈ R ⊓ GLBPrimeCore p H := by
    refine ⟨?_, (mem_glbPrimeCore_iff_mk_eq_one _).mpr ?_⟩
    · simpa using R.mul_mem (R.inv_mem ha) hb
    · rw [map_mul, map_inv, hab, inv_mul_cancel]
  rw [inf_eq_bot_of_isPGroup Fact.out hR (glbPrimeCore_coprime p H), Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp (Subtype.ext h1)

theorem exists_lift_mem_normalizer_map [Fact p.Prime] {M R : Subgroup G}
    (hNM : GLBPrimeCore p H ≤ M) (hRH : R ≤ H) (hR : IsPGroup p R)
    {x : H ⧸ primeComplementCore (G := H) p}
    (hx : x ∈ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    (hxN : x ∈ Subgroup.normalizer (((R.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) : Set _)) :
    ∃ t : H, (t : G) ∈ M ∧ (t : G) ∈ Subgroup.normalizer (R : Set G) ∧
      QuotientGroup.mk' (primeComplementCore (G := H) p) t = x := by
  obtain ⟨k, hkX, rfl⟩ := hx
  obtain ⟨o, ho, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
    (comap_normalizer_map_le_sup Fact.out (primeComplementCore (G := H) p)
      (primeComplementCore_coprime p) hR.comap_subtype hxN)
  have hπo : QuotientGroup.mk' (primeComplementCore (G := H) p) o = 1 :=
    (QuotientGroup.eq_one_iff o).mpr ho
  have hoM : (o : G) ∈ M := hNM ((mem_glbPrimeCore_iff_mk_eq_one o).mpr hπo)
  refine ⟨t, ?_, ?_, by rw [map_mul, hπo, one_mul]⟩
  · have h := M.mul_mem (M.inv_mem hoM) (Subgroup.mem_subgroupOf.mp hkX).2
    simpa using h
  · have h1 : (t : G) ∈ Subgroup.normalizer
        (((R.subgroupOf H).map H.subtype : Subgroup G) : Set G) :=
      Subgroup.le_normalizer_map H.subtype ⟨t, ht, rfl⟩
    rwa [Subgroup.map_subgroupOf_eq_of_le hRH] at h1

theorem le_glbPrimeCore_of_forall_isPGroup_map {M : Subgroup G}
    (hP : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup p W →
      W = ⊥)
    {Y : Subgroup G} (hY : Y ≤ H ⊓ M) (hYN : H ⊓ M ≤ Subgroup.normalizer (Y : Set G))
    (hYp : ∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k ∈ GLBPrimeCore p H) : Y ≤ GLBPrimeCore p H :=
  le_glbPrimeCore_of_map_eq_bot (hY.trans inf_le_left)
    (hP _ (Subgroup.map_mono (Subgroup.subgroupOf_mono H hY)) (map_mk_le_normalizer_map_mk hYN)
      (isPGroup_map_of_forall_pow_mem hYp))

theorem card_quotient_eq_of_forall_map {M : Subgroup G} {n : ℕ}
    (hS : ∀ U : Subgroup (H ⧸ primeComplementCore (G := H) p),
      U ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      ∀ (V : Subgroup U) [V.Normal], IsSimpleGroup (U ⧸ V) → (∃ a b : U ⧸ V, a * b ≠ b * a) →
        Nat.card (U ⧸ V) = n)
    {L : Subgroup G} (hL : L ≤ H ⊓ M) (V : Subgroup L) [V.Normal]
    (hV : (GLBPrimeCore p H).subgroupOf L ≤ V) (hs : IsSimpleGroup (L ⧸ V))
    (hna : ∃ a b : L ⧸ V, a * b ≠ b * a) : Nat.card (L ⧸ V) = n := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hLH : L ≤ H := hL.trans inf_le_left
  set U := (L.subgroupOf H).map π with hU
  let f : L →* U := (π.comp (Subgroup.inclusion hLH)).codRestrict U fun x =>
    ⟨Subgroup.inclusion hLH x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  have hker : f.ker ≤ V := by
    intro x hx
    refine hV (Subgroup.mem_subgroupOf.mpr ?_)
    have h1 : π (Subgroup.inclusion hLH x) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact (mem_glbPrimeCore_iff_mk_eq_one (Subgroup.inclusion hLH x)).mpr h1
  set V' : Subgroup U := V.map f
  have hV' : V'.Normal := Subgroup.Normal.map inferInstance f hf
  let g : L →* U ⧸ V' := (QuotientGroup.mk' V').comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective V').comp hf
  have hgker : V = g.ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_map_eq,
      sup_eq_left.mpr hker]
  let e : L ⧸ V ≃* U ⧸ V' :=
    (QuotientGroup.quotientMulEquivOfEq hgker).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  have : IsSimpleGroup (U ⧸ V') := MulEquiv.isSimpleGroup e.symm
  obtain ⟨a, b, hab⟩ := hna
  rw [Nat.card_congr e.toEquiv]
  refine hS U (Subgroup.map_mono (Subgroup.subgroupOf_mono H hL)) V' this ⟨e a, e b, fun h => ?_⟩
  exact hab (e.injective (by rw [map_mul, map_mul, h]))

omit [Finite G] in
private theorem commutator_subgroupOf_eq_of_le {A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    ⁅A, B⁆.subgroupOf H = ⁅A.subgroupOf H, B.subgroupOf H⁆ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le
      ((Subgroup.commutator_mono hA hB).trans (A3.commutator_self_le H))]

theorem exists_perfect_of_forall_map [Fact p.Prime] {M R : Subgroup G}
    (hNM : GLBPrimeCore p H ≤ M) (hRH : R ≤ H) (hR : IsPGroup p R) {A : Type} [Group A]
    [Group.IsPerfect A] {ι : Type}
    (hJ : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) →
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ W →
      ∃ J : ι → Subgroup (H ⧸ primeComplementCore (G := H) p),
        (∀ i, J i ≤ W ∧ Nonempty (J i ≃* A)) ∧ (∀ i j, i ≠ j → ⁅J i, J j⁆ = ⊥) ∧
        (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ ⨆ i, J i)
    {Y : Subgroup G} (hY : Y ≤ H ⊓ M) (hYN : H ⊓ M ≤ Subgroup.normalizer (Y : Set G))
    (hRY : R ≤ Y) :
    ∃ J : ι → Subgroup G, (∀ i, J i ≤ Y ∧ ⁅J i, J i⁆ = J i ∧
      ∃ φ : ↥(J i) →* A, Function.Surjective φ ∧
        ∀ x : ↥(J i), φ x = 1 ↔ (x : G) ∈ GLBPrimeCore p H) ∧
      (∀ i j, i ≠ j → ⁅J i, J j⁆ ≤ GLBPrimeCore p H) ∧ R ≤ ⨆ i, J i := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hYH : Y ≤ H := hY.trans inf_le_left
  obtain ⟨Jb, hJb, hJbc, hRJb⟩ := hJ ((Y.subgroupOf H).map π)
    (Subgroup.map_mono (Subgroup.subgroupOf_mono H hY)) (map_mk_le_normalizer_map_mk hYN)
    (Subgroup.map_mono (Subgroup.subgroupOf_mono H hRY))
  have e : ∀ i, Jb i ≃* A := fun i => Classical.choice (hJb i).2
  set Yh : ι → Subgroup G := fun i => ((Jb i).comap π).map H.subtype ⊓ Y with hYh
  set J : ι → Subgroup G := fun i => perfectCore (Yh i) with hJdef
  have hYhH : ∀ i, Yh i ≤ H := fun i => inf_le_right.trans hYH
  have hYhsub : ∀ i, (Yh i).subgroupOf H = (Jb i).comap π ⊓ Y.subgroupOf H := fun i => by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap]
    refine and_congr_left fun _ => ⟨fun ⟨y, hy, hyx⟩ => ?_, fun h => ⟨x, h, rfl⟩⟩
    exact (Subtype.ext hyx : y = x) ▸ hy
  have hYhmap : ∀ i, ((Yh i).subgroupOf H).map π = Jb i := fun i => by
    rw [hYhsub i]
    exact map_comap_inf_eq π (hJb i).1
  have hJH : ∀ i, J i ≤ H := fun i => (perfectCore_le _).trans (hYhH i)
  have hJsub : ∀ i, (J i).subgroupOf H = perfectCore ((Yh i).subgroupOf H) := fun i => by
    have h1 : J i = (perfectCore ((Yh i).subgroupOf H)).map H.subtype := by
      rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le (hYhH i)]
    rw [h1]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hJbperf : ∀ i, ⁅Jb i, Jb i⁆ = Jb i := fun i =>
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective (f := (e i).symm.toMonoidHom)
      (e i).symm.surjective)
  have hJmap : ∀ i, ((J i).subgroupOf H).map π = Jb i := fun i => by
    rw [hJsub i, map_perfectCore, hYhmap i, perfectCore_eq_self_of_perfect (hJbperf i)]
  have hφ : ∀ i, ∃ φ : ↥(J i) →* A, Function.Surjective φ ∧
      ∀ x : ↥(J i), φ x = 1 ↔ (x : G) ∈ GLBPrimeCore p H := by
    intro i
    let g : ↥(J i) →* H ⧸ primeComplementCore (G := H) p := π.comp (Subgroup.inclusion (hJH i))
    have hgr : g.range = Jb i := by
      rw [← hJmap i, MonoidHom.range_comp]
      congr 1
      ext x
      simp only [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    refine ⟨(e i).toMonoidHom.comp ((MulEquiv.subgroupCongr hgr).toMonoidHom.comp
      g.rangeRestrict), (e i).surjective.comp ((MulEquiv.subgroupCongr hgr).surjective.comp
        g.rangeRestrict_surjective), fun x => ?_⟩
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      EmbeddingLike.map_eq_one_iff]
    change _ ↔ ((Subgroup.inclusion (hJH i) x : H) : G) ∈ GLBPrimeCore p H
    rw [mem_glbPrimeCore_iff_mk_eq_one]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  refine ⟨J, fun i => ⟨(perfectCore_le _).trans inf_le_right, perfectCore_perfect _, hφ i⟩,
    fun i j hij => ?_, ?_⟩
  ·
    refine le_glbPrimeCore_of_map_eq_bot
      ((Subgroup.commutator_mono (hJH i) (hJH j)).trans (A3.commutator_self_le H)) ?_
    rw [commutator_subgroupOf_eq_of_le (hJH i) (hJH j), Subgroup.map_commutator, hJmap, hJmap,
      hJbc i j hij]
  ·
    have hle : (R.subgroupOf H).map π ≤ ((⨆ i, J i).subgroupOf H).map π := by
      refine hRJb.trans (iSup_le fun i => ?_)
      rw [← hJmap i]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono H (le_iSup J i))
    have hNJ : GLBPrimeCore p H ≤ Subgroup.normalizer ((⨆ i, J i : Subgroup G) : Set G) := by
      intro n hn
      have hnH : n ∈ H := (glbPrimeCore_le p H) hn
      have hnJ : ∀ i, n ∈ Subgroup.normalizer (J i : Set G) := by
        intro i
        refine normalizer_le_normalizer_perfectCore _ (Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer ?_, hYN ⟨hnH, hNM hn⟩⟩)
        refine ⟨⟨n, hnH⟩, ?_, rfl⟩
        show π ⟨n, hnH⟩ ∈ Jb i
        rw [(mem_glbPrimeCore_iff_mk_eq_one ⟨n, hnH⟩).mp hn]
        exact Subgroup.one_mem _
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
      exact iSup_congr fun i => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnJ i)
    exact le_of_le_sup_of_isPGroup_of_coprime hR (glbPrimeCore_coprime p H) hNJ
      (le_sup_glbPrimeCore_of_map_le hRH hle)

end Transfer

open CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierAlternating in
theorem exists_a15Data_of (hL : KFactA15Local) {G : Type} [Group G] [Finite G]
    [Fact (Nat.Prime 5)] {P : Sylow 5 G} {M H R : Subgroup G}
    {Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5)}
    (hglob : CFSG.AGLEmbeddingD2.AGLGlobal G) (hind : ∀ q ∈ GLBBetaFour G, q < 5 → D1At G q)
    (hext : D1Extremal 5 P M H R)
    (hrbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)))
    (hred : ReducedNongeneration 5 (H ⧸ primeComplementCore (G := H) 5) Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5))))
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 5)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 5), IsComponentOf L ⊤ → L = K)
    (hC : Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 5)) = ⊥)
    (hZ : Subgroup.center K = ⊥)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 15))) :
    ∃ (c : Fin 3 → G) (σ τ : G), D1A15Data P M H R c σ τ := by
  have hp : (5 : ℕ).Prime := by norm_num
  obtain ⟨e'⟩ := e
  have e₀ : K ≃* alternatingGroup (Fin 15) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e'
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hRH : R ≤ H := hext.le_H
  have hRp : IsPGroup 5 R := hext.isPGroup
  have hNM : GLBPrimeCore 5 H ≤ M := hext.primeCore_le
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 5) with hπ
  set X₀ := ((H ⊓ M).subgroupOf H).map π with hX₀
  have hIS : A15InSitu (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) X₀ :=
    hL _ K hKn ⟨e₀⟩ hC Rbar X₀ hred.weakCore_le hred.ne_top
  have hTK : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) ≤ K := by
    have : Finite (MulAut K) := MulEquiv.finite_left
    have hOut : ¬ 5 ∣ Nat.card (Outer K) := fun hd =>
      absurd (hd.trans (outer_card_dvd_two_of_equiv_outside_six (n := 15) (by norm_num) e₀))
        (by norm_num)
    intro x hx
    obtain ⟨k, hk⟩ := Rbar.isPGroup' ⟨x, hx⟩
    have hxk : x ^ 5 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hmem := mem_sup_centralizer_of_pow hp hOut hxk
    rwa [hC, sup_bot_eq] at hmem
  obtain ⟨ψ, hψ, -, hψB⟩ := exists_injective_map_a15Base_eq e₀ Rbar hTK
  rw [hrbar] at hψB
  have hNT : ∀ g ∈ Subgroup.normalizer (a15Base : Set (alternatingGroup (Fin 15))),
      ψ g ∈ X₀ ⊓ Subgroup.normalizer (((R.subgroupOf H).map π : Subgroup _) : Set _) := by
    intro g hg
    have h1 : ψ g ∈ Subgroup.normalizer (((R.subgroupOf H).map π : Subgroup _) : Set _) := by
      rw [← hψB]
      exact Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem ψ hg)
    refine ⟨?_, h1⟩
    have h2 := (normalizer_le_weakCore_of_rank 5 hp _ hred.three_le_pRank).trans
      hred.weakCore_le
    rw [hrbar] at h2
    exact h2 h1
  choose c' hc'R hc'π using fun i : Fin 3 =>
    Subgroup.mem_map.mp (hψB ▸ Subgroup.mem_map_of_mem ψ (a15c_mem i) :
      ψ (a15c i) ∈ (R.subgroupOf H).map π)
  obtain ⟨tσ, htσM, htσN, htσπ⟩ := exists_lift_mem_normalizer_map hNM hRH hRp
    (hNT _ a15σ_mem_normalizer).1 (hNT _ a15σ_mem_normalizer).2
  obtain ⟨tτ, htτM, htτN, htτπ⟩ := exists_lift_mem_normalizer_map hNM hRH hRp
    (hNT _ a15τ_mem_normalizer).1 (hNT _ a15τ_mem_normalizer).2
  have hcR : ∀ i, ((c' i : H) : G) ∈ R := fun i => Subgroup.mem_subgroupOf.mp (hc'R i)
  have hinj : ∀ {a b : H}, (a : G) ∈ R → (b : G) ∈ R → π a = π b → a = b :=
    fun ha hb hab => eq_of_mk_primeComplementCore_eq hRp ha hb hab
  have hlift : ∀ {t y z : H} {g a b : alternatingGroup (Fin 15)}, π t = ψ g →
      (t : G) ∈ Subgroup.normalizer (R : Set G) → (y : G) ∈ R → (z : G) ∈ R → π y = ψ a →
      π z = ψ b → g * a * g⁻¹ = b → (t : G) * y * (t : G)⁻¹ = z := by
    intro t y z g a b ht htN hy hz hya hzb hab
    have h := hinj (a := t * y * t⁻¹) (by simpa using (Subgroup.mem_normalizer_iff.mp htN y).mp hy)
      hz (by rw [map_mul, map_mul, map_inv, ht, hya, hzb, ← hab, map_mul, map_mul, map_inv])
    simpa using congrArg Subtype.val h
  have hRB : ∀ r : H, (r : G) ∈ R → ∃ x ∈ a15Base, π r = ψ x := fun r hr => by
    obtain ⟨x, hx, hxr⟩ := (hψB.symm ▸ Subgroup.mem_map_of_mem π
      (Subgroup.mem_subgroupOf.mpr hr) : π r ∈ a15Base.map ψ)
    exact ⟨x, hx, hxr.symm⟩
  have hcardR : Nat.card R = 5 ^ 3 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv,
      ← card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime 5) (T := R.subgroupOf H)
        hRp.comap_subtype, ← hψB,
      Subgroup.card_map_of_injective hψ, card_a15Base]
  refine ⟨fun i => (c' i : G), tσ, tτ, ?_⟩
  refine
    { surv := ?_
      ind := hind
      elem := ?_
      card_R := hcardR
      pcore := fun Y hY hYN hYp => le_glbPrimeCore_of_forall_isPGroup_map hIS.pcore hY hYN hYp
      c_mem := hcR
      closure_eq := ?_
      σ_mem := ⟨tσ.2, htσM⟩
      σ_conj := fun i => ?_
      τ_mem := ⟨tτ.2, htτM⟩
      τ_conj := ?_
      section_card := fun L hL V _ hV hs hna =>
        card_quotient_eq_of_forall_map hIS.section_card hL V hV hs hna
      normal_closure := fun Y hY hYN hRY => ?_ }
  ·
    have hR1 : R ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hcardR
      norm_num at hcardR
    refine hext.survivorData_of_map hglob le_rfl hR1 (fun W hW hWn hWc => ?_) ?_ ?_
    · exact hIS.primeCore W hW ((Subgroup.normal_subgroupOf_iff_le_normalizer hW).mp hWn) hWc
    · rw [← hrbar]
      exact hIS.normal_dichotomy
    · rw [← hrbar]
      exact hIS.centralizer_le
  ·
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun r hr => ?_⟩
    · obtain ⟨x, hx, hxa⟩ := hRB ⟨a, hRH a.2⟩ a.2
      obtain ⟨y, hy, hyb⟩ := hRB ⟨b, hRH b.2⟩ b.2
      have hxy : x * y = y * x := congrArg Subtype.val
        ((isMulCommutative_iff.mp isElemAbelian_a15Base.1) ⟨x, hx⟩ ⟨y, hy⟩)
      exact congrArg (fun x : H => (x : G)) (hinj (a := ⟨a, hRH a.2⟩ * ⟨b, hRH b.2⟩)
        (b := ⟨b, hRH b.2⟩ * ⟨a, hRH a.2⟩) (R.mul_mem a.2 b.2) (R.mul_mem b.2 a.2)
        (by rw [map_mul, map_mul, hxa, hyb, ← map_mul, ← map_mul, hxy]))
    · obtain ⟨x, hx, hxr⟩ := hRB ⟨r, hRH hr⟩ hr
      exact congrArg (fun x : H => (x : G)) (hinj (a := ⟨r, hRH hr⟩ ^ 5) (b := 1)
        (R.pow_mem hr 5) R.one_mem
        (by rw [map_pow, hxr, ← map_pow, isElemAbelian_a15Base.2 x hx, map_one, map_one]))
  ·
    have hle : Subgroup.closure (Set.range c') ≤ R.subgroupOf H :=
      Subgroup.closure_le _ |>.mpr (Set.range_subset_iff.mpr hc'R)
    have hmap : (Subgroup.closure (Set.range c')).map π = (R.subgroupOf H).map π := by
      rw [MonoidHom.map_closure, ← Set.range_comp, ← hψB, ← closure_range_a15c,
        MonoidHom.map_closure, ← Set.range_comp]
      exact congrArg _ (congrArg _ (funext hc'π))
    have hcop := primeComplementCore_coprime (G := H) 5
    have heq : Subgroup.closure (Set.range c') = R.subgroupOf H :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [← card_map_mk_of_isPGroup hp _ hcop (T := R.subgroupOf H) hRp.comap_subtype, ← hmap,
          card_map_mk_of_isPGroup hp _ hcop (hRp.comap_subtype.to_le hle)])
    rw [show (fun i => (c' i : G)) = H.subtype ∘ c' from rfl, Set.range_comp,
      ← MonoidHom.map_closure, heq, Subgroup.map_subgroupOf_eq_of_le hRH]
  ·
    exact hlift htσπ htσN (hcR i) (hcR (i + 1)) (hc'π i) (hc'π (i + 1)) (a15σ_conj i)
  ·
    obtain ⟨h0, h1, h2⟩ := a15τ_conj
    have hsq : ∀ i, π (c' i ^ 2) = ψ (a15c i ^ 2) := fun i => by rw [map_pow, hc'π, map_pow]
    exact ⟨hlift htτπ htτN (hcR 0) (R.pow_mem (hcR 0) 2) (hc'π 0) (hsq 0) h0,
      hlift htτπ htτN (hcR 1) (hcR 1) (hc'π 1) (hc'π 1) h1,
      hlift htτπ htτN (hcR 2) (R.pow_mem (hcR 2) 2) (hc'π 2) (hsq 2) h2⟩
  ·
    have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    refine exists_perfect_of_forall_map hNM hRH hRp (fun W hW hWn hRW => ?_) hY hYN hRY
    rw [← hrbar] at hRW ⊢
    exact hIS.normal_closure W hW hWn hRW

theorem stmtA15Data_of (hL : KFactA15Local) : StmtA15Data := by
  intro G _ _ _ P M H R Rbar hcfg K hK huniq hcent hZ e
  exact exists_a15Data_of hL hcfg.glob hcfg.ind hcfg.ext hcfg.rbar hcfg.red hK huniq
    (hcfg.centralizer_eq_bot hK huniq hcent hZ) hZ e

end CFSG.AGLEmbedding
