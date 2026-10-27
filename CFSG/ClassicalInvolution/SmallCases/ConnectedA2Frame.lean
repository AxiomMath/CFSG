module

public import CFSG.ClassicalInvolution.SmallCases.Endpoints
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open scoped IsMulCommutative MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.SmallWeyl CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime] {F : Type} [Field F] {G : Type} [Group G]
  {Ω : Set (Subgroup G)} {A : Subgroup G} {S : Set (Subgroup G)}

theorem nonCommConnected_of_frameSpan_eq_top [IsSimpleGroup G] (hZ : Subgroup.center G = ⊥)
    (hne : S.Nonempty) (hnt : ∀ K ∈ S, K ≠ ⊥) (hspan : frameSpan S = ⊤) :
    NonCommConnected S := by
  classical
  obtain ⟨K₀, hK₀⟩ := hne
  have hnonempty : Nonempty ↥S := ⟨⟨K₀, hK₀⟩⟩
  rw [NonCommConnected, SimpleGraph.connected_iff]
  refine ⟨fun K L => ?_, hnonempty⟩
  by_contra hLK
  set N : Subgroup G := ⨆ M : ↥S, ⨆ (_ : (nonCommGraph S).Reachable K M), (M : Subgroup G) with hN
  set N' : Subgroup G :=
    ⨆ M : ↥S, ⨆ (_ : ¬ (nonCommGraph S).Reachable K M), (M : Subgroup G) with hN'
  have hcomm : ∀ M M' : ↥S, (nonCommGraph S).Reachable K M → ¬ (nonCommGraph S).Reachable K M' →
      ∀ x ∈ (M : Subgroup G), ∀ y ∈ (M' : Subgroup G), x * y = y * x := by
    intro M M' hM hM'
    by_contra hnc
    push Not at hnc
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    have hne : M ≠ M' := by
      rintro rfl
      exact hM' hM
    have hadj : (nonCommGraph S).Adj M M' :=
      nonCommGraph_adj.mpr ⟨hne, fun h => hxy (h x hx y hy)⟩
    exact hM' (hM.trans hadj.reachable)
  have hN'c : N' ≤ Subgroup.centralizer (N : Set G) := by
    refine iSup_le fun M' => iSup_le fun hM' => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have : (N : Subgroup G) ≤ Subgroup.centralizer ((M' : Subgroup G) : Set G) := by
      refine iSup_le fun M => iSup_le fun hM => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y' hy'
      exact (hcomm M M' hM hM' x hx y' hy').symm
    have h2 := this hn
    rw [Subgroup.mem_centralizer_iff] at h2
    exact (h2 y hy).symm
  have hsup : N ⊔ N' = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine iSup₂_le fun M hM => ?_
    by_cases hr : (nonCommGraph S).Reachable K ⟨M, hM⟩
    · exact le_sup_of_le_left
        (le_iSup₂_of_le (f := fun (M : ↥S) (_ : (nonCommGraph S).Reachable K M) =>
          (M : Subgroup G)) ⟨M, hM⟩ hr le_rfl)
    · exact le_sup_of_le_right
        (le_iSup₂_of_le (f := fun (M : ↥S) (_ : ¬ (nonCommGraph S).Reachable K M) =>
          (M : Subgroup G)) ⟨M, hM⟩ hr le_rfl)
  have hnorm : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    refine sup_le Subgroup.le_normalizer ?_
    exact hN'c.trans (Subgroup.centralizer_le_normalizer _)
  have hK : (K : Subgroup G) ≤ N :=
    le_iSup₂_of_le (f := fun (M : ↥S) (_ : (nonCommGraph S).Reachable K M) => (M : Subgroup G))
      K (SimpleGraph.Reachable.refl K) le_rfl
  have hNbot : N ≠ ⊥ := fun h => hnt K K.2 (le_bot_iff.mp (h ▸ hK))
  have hNtop : N = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_left hNbot
  have hL : (L : Subgroup G) ≤ N' :=
    le_iSup₂_of_le (f := fun (M : ↥S) (_ : ¬ (nonCommGraph S).Reachable K M) => (M : Subgroup G))
      L hLK le_rfl
  refine hnt L L.2 ?_
  rw [eq_bot_iff]
  intro y hy
  have h1 := hN'c (hL hy)
  rw [Subgroup.mem_centralizer_iff] at h1
  have h2 : y ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact h1 g (by rw [hNtop]; exact Subgroup.mem_top g)
  rw [hZ] at h2
  exact h2

theorem bootData_of_indepTriple {Ω : Set (Subgroup G)} (h : IndepTriple p f Ω) :
    BootData p f Ω := by
  obtain ⟨K, z, hmem, hcomm, hel, hcard⟩ := h
  refine ⟨K 0, z 0, Subgroup.closure (Set.range z), (hmem 0).1, (hmem 0).2, hel, hcard,
    Subgroup.subset_closure ⟨0, rfl⟩, ?_⟩
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    by_cases hi : i = 0
    · subst hi
      have := Subgroup.mem_centralizer_iff.mp (le_centralizer (hmem 0).2 hk) (z 0)
        (Set.mem_singleton _)
      exact this
    · exact (hcomm 0 i (Ne.symm hi) k hk (z i) (hmem i).2.mem).symm
  | one => simp
  | mul x y _ _ hx hy =>
    calc x * y * k = x * (y * k) := by rw [mul_assoc]
      _ = x * (k * y) := by rw [hy]
      _ = (x * k) * y := by rw [mul_assoc]
      _ = (k * x) * y := by rw [hx]
      _ = k * (x * y) := by rw [mul_assoc]
  | inv x _ hx =>
    calc x⁻¹ * k = x⁻¹ * (k * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * k) * x⁻¹ := by rw [hx]
      _ = k * x⁻¹ := by group

theorem isClassicalMember_of_isUniqueInvolution {K K' : Subgroup G} {z w : G}
    (hz : IsClassicalMember p f K z) (hK' : K' ∈ conjClass K) (hw : IsUniqueInvolution K' w) :
    IsClassicalMember p f K' w := by
  obtain ⟨g, rfl⟩ := hK'
  have hc := hz.conj g
  have h2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    have h := pow_orderOf_eq_one (g * z * g⁻¹)
    rwa [hc.orderOf_eq_two, pow_two] at h
  rcases hw.unique _ hc.mem h2 with h | h
  · exact absurd h hc.ne_one
  · rw [← h]
    exact hc

theorem card_le_eight_of_not_bootData [Finite G] {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (Fr : RankFrame F Ω A S) (hΩ : Ω = conjClass K)
    (hne : S.Nonempty) (hB : ¬ BootData p f (conjClass K)) : Nat.card A ≤ 8 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨K', hK'⟩ := hne
  obtain ⟨w, hw⟩ := Fr.exists_isUniqueInvolution hK'
  have hK'Ω : K' ∈ conjClass K := hΩ ▸ Fr.subset hK'
  have hcl := isClassicalMember_of_isUniqueInvolution hz hK'Ω hw
  set C := axisSub A K' with hC
  have hCA : C ≤ A := inf_le_left
  have hidx : C.relIndex A = 2 := Fr.relIndex_axisSub hK'
  have hcardC : Nat.card C * 2 = Nat.card A := by
    have h1 := (C.subgroupOf A).card_mul_index
    have h3 : Nat.card (C.subgroupOf A) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv
    rw [h3] at h1
    rw [Subgroup.relIndex] at hidx
    rw [hidx] at h1
    exact h1
  have hC2 : IsPGroup 2 C := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    refine ⟨1, ?_⟩
    have h := Fr.elem g (hCA g.2)
    apply Subtype.ext
    simpa [pow_two] using h
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hC2
  have hn3 : 3 ≤ n := by
    by_contra h
    push Not at h
    have h4 : Nat.card C ≤ 4 := by
      rw [hn]
      calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    omega
  have hdvd : 2 ^ 3 ∣ Nat.card C := by
    rw [hn]
    exact pow_dvd_pow 2 hn3
  have hwC : Subgroup.zpowers w ≤ C :=
    (Subgroup.zpowers_le).mpr (Fr.mem_axisSub_of_isUniqueInvolution hK' hw)
  have hcardw : Nat.card (Subgroup.zpowers w) ∣ 2 ^ 3 := by
    rw [Nat.card_zpowers, hcl.orderOf_eq_two]
    norm_num
  obtain ⟨B, hBcard, hwB, hBC⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hcardw hdvd hwC
  apply hB
  refine ⟨K', w, B, hK'Ω, hcl, ⟨?_, ?_⟩, by rw [hBcard]; norm_num,
    hwB (Subgroup.mem_zpowers w), ?_⟩
  · exact ⟨⟨fun x y => Subtype.ext (Fr.comm_of_mem (hCA (hBC x.2)) (hCA (hBC y.2)))⟩⟩
  · intro x hx
    rw [pow_two]
    exact Fr.elem x (hCA (hBC hx))
  · intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact ((mem_axisSub_iff.mp (hBC hb)).2 k hk).symm

theorem exists_ne_one_centralizes_of_card_three [Finite ↥A] [IsMulCommutative ↥A]
    (Fr : RankFrame F Ω A S) (hd : Fr.dataFinset.card = 3) {K L : ↥S}
    (hKL : (Fr.datum K).Adj (Fr.datum L)) :
    ∃ t ∈ A, t ≠ 1 ∧ ∀ M ∈ S, ∀ m ∈ M, m * t = t * m := by
  classical
  obtain ⟨t, ht, ht1⟩ := Fr.exists_ne_one_mem_axisSub_inf_axisSub K.2 L.2
  obtain ⟨htK, htL⟩ := Subgroup.mem_inf.mp ht
  have htA : t ∈ A := (mem_axisSub_iff.mp htK).1
  set d₁ := Fr.datum K with hd₁
  set d₂ := Fr.datum L with hd₂
  have h₁ : d₁ ∈ Fr.dataFinset := Fr.mem_dataFinset.mpr ⟨K, rfl⟩
  have h₂ : d₂ ∈ Fr.dataFinset := Fr.mem_dataFinset.mpr ⟨L, rfl⟩
  have hc : d₁.conj d₂ ∈ Fr.dataFinset := Fr.dataFinset_isClosed d₁ h₁ d₂ h₂
  have hne12 : d₁ ≠ d₂ := by
    intro h
    have := hKL.1
    rw [h, Datum.pair_self] at this
    exact zero_ne_one this
  have hvec : (d₁.conj d₂).vec = d₂.vec + d₁.vec := by
    simp [Datum.conj, hKL.1]
  have hne1c : d₁ ≠ d₁.conj d₂ := by
    intro h
    have h1 := congrArg Datum.vec h
    rw [hvec] at h1
    have : d₂.vec = 0 := by
      have h2 : d₂.vec + d₁.vec = d₁.vec := h1.symm
      simpa using h2
    exact d₂.vec_ne_zero this
  have hne2c : d₂ ≠ d₁.conj d₂ := by
    intro h
    have h1 := congrArg Datum.vec h
    rw [hvec] at h1
    have : d₁.vec = 0 := by
      have h2 : d₂.vec + d₁.vec = d₂.vec := h1.symm
      simpa using h2
    exact d₁.vec_ne_zero this
  have hsub : ({d₁, d₂, d₁.conj d₂} : Finset (Datum (Additive ↥A))) ⊆ Fr.dataFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact hc
  have hcard3 : ({d₁, d₂, d₁.conj d₂} : Finset (Datum (Additive ↥A))).card = 3 :=
    Finset.card_eq_three.mpr ⟨d₁, d₂, d₁.conj d₂, hne12, hne1c, hne2c, rfl⟩
  have heq : ({d₁, d₂, d₁.conj d₂} : Finset (Datum (Additive ↥A))) = Fr.dataFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hd, hcard3])
  have hform : ∀ M : ↥S, t ∈ axisSub A (M : Subgroup G) ↔
      (Fr.datum M).form (Additive.ofMul ⟨t, htA⟩) = 0 := by
    intro M
    rw [← axisChar_eq_zero_iff]
    rfl
  have hform₁ : d₁.form (Additive.ofMul ⟨t, htA⟩) = 0 := (hform K).mp htK
  have hform₂ : d₂.form (Additive.ofMul ⟨t, htA⟩) = 0 := (hform L).mp htL
  refine ⟨t, htA, ht1, fun M hM m hm => ?_⟩
  have hmem : Fr.datum ⟨M, hM⟩ ∈ ({d₁, d₂, d₁.conj d₂} : Finset (Datum (Additive ↥A))) := by
    rw [heq]
    exact Fr.mem_dataFinset.mpr ⟨⟨M, hM⟩, rfl⟩
  have hzero : (Fr.datum ⟨M, hM⟩).form (Additive.ofMul ⟨t, htA⟩) = 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · rw [h]; exact hform₁
    · rw [h]; exact hform₂
    · rw [h]
      show (d₂.form + (if d₂.pair d₁ = 1 then d₁.form else 0)) _ = 0
      split_ifs
      · simp [hform₁, hform₂]
      · simp [hform₂]
  have htM := (hform ⟨M, hM⟩).mpr hzero
  exact (mem_axisSub_iff.mp htM).2 m hm

theorem dataFinset_card_six [Finite ↥A] [IsMulCommutative ↥A] (Fr : RankFrame F Ω A S)
    (hcard : Nat.card A = 8) (hS : S.Nonempty) (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S)
    (hconn : NonCommConnected S) (hZ : Subgroup.center G = ⊥) (hspan : frameSpan S = ⊤)
    {K L : Subgroup G} (hK : K ∈ S) (hL : L ∈ S) (hne : K ≠ L) (hnc : ¬ Commutes K L) :
    Fr.dataFinset.card = 6 ∧ ∃ K' ∈ S, ∃ L' ∈ S, K' ≠ L' ∧ Commutes K' L' := by
  have hadj : (Fr.datum ⟨K, hK⟩).Adj (Fr.datum ⟨L, hL⟩) :=
    (Fr.datum_adj_iff_not_commutes hA2 hfib (fun h => hne (congrArg Subtype.val h))).mpr hnc
  rcases Fr.datum_classification_three hcard hS hA2 hfib hconn with h1 | ⟨h3, -⟩ | ⟨h6, hval⟩
  · exfalso
    have h := Finset.card_le_one.mp h1.le
    have e : Fr.datum ⟨K, hK⟩ = Fr.datum ⟨L, hL⟩ :=
      h _ (Fr.mem_dataFinset.mpr ⟨_, rfl⟩) _ (Fr.mem_dataFinset.mpr ⟨_, rfl⟩)
    have h' := hadj.1
    rw [e, Datum.pair_self] at h'
    exact zero_ne_one h'
  · exfalso
    obtain ⟨t, htA, ht1, htc⟩ := exists_ne_one_centralizes_of_card_three Fr h3 hadj
    apply ht1
    have hcent : frameSpan S ≤ Subgroup.centralizer ({t} : Set G) := by
      refine iSup₂_le fun M hM m hm => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact (htc M hM m hm).symm
    have : t ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({t} : Set G) :=
        hcent (by rw [hspan]; exact Subgroup.mem_top g)
      rw [Subgroup.mem_centralizer_iff] at hg
      exact (hg t (Set.mem_singleton t)).symm
    rw [hZ] at this
    exact this
  · refine ⟨h6, ?_⟩
    obtain ⟨q, ⟨hqR, hqne, hqna⟩, -⟩ := hval _ (Fr.mem_dataFinset.mpr ⟨⟨K, hK⟩, rfl⟩)
    obtain ⟨M, rfl⟩ := Fr.mem_dataFinset.mp hqR
    have hMK : (⟨K, hK⟩ : ↥S) ≠ M := fun h => hqne (by rw [← h])
    exact ⟨K, hK, M, M.2, fun h => hMK (Subtype.ext h), Fr.commutes_of_not_adj hA2 hfib hMK hqna⟩

theorem datumInjective_of_axis [Finite ↥A] [IsMulCommutative ↥A] (Fr : RankFrame F Ω A S)
    (h : ∀ K ∈ S, ∀ L ∈ S, (∃ w, IsUniqueInvolution K w ∧ IsUniqueInvolution L w) →
      axisSub A K = axisSub A L → K = L) : Fr.DatumInjective := by
  intro K L hd
  have hz : Fr.zOf K = Fr.zOf L :=
    congrArg (fun d : Datum (Additive ↥A) => ((Additive.toMul d.vec : ↥A) : G)) hd
  refine Subtype.ext (h K K.2 L L.2 ⟨Fr.zOf K, Fr.isUniqueInvolution_zOf K, ?_⟩ ?_)
  · rw [hz]
    exact Fr.isUniqueInvolution_zOf L
  · ext x
    constructor
    · intro hx
      have hxA : x ∈ A := (mem_axisSub_iff.mp hx).1
      have h1 := congrArg (fun d : Datum (Additive ↥A) => d.form (Additive.ofMul ⟨x, hxA⟩)) hd
      have h2 : axisChar A K x = axisChar A L x := h1
      rw [← axisChar_eq_zero_iff] at hx ⊢
      rw [← h2]
      exact hx
    · intro hx
      have hxA : x ∈ A := (mem_axisSub_iff.mp hx).1
      have h1 := congrArg (fun d : Datum (Additive ↥A) => d.form (Additive.ofMul ⟨x, hxA⟩)) hd
      have h2 : axisChar A K x = axisChar A L x := h1
      rw [← axisChar_eq_zero_iff] at hx ⊢
      rw [h2]
      exact hx

theorem eq_of_twins (hfib : FibreLE2 S)
    (h : ∀ K ∈ S, ∃ L ∈ S, (∃ w, IsUniqueInvolution K w ∧ IsUniqueInvolution L w) ∧
      axisSub A L ≠ axisSub A K) :
    ∀ K ∈ S, ∀ L ∈ S, (∃ w, IsUniqueInvolution K w ∧ IsUniqueInvolution L w) →
      axisSub A K = axisSub A L → K = L := by
  rintro K hK L hL ⟨w, hwK, hwL⟩ hax
  obtain ⟨M, hM, ⟨w', hwK', hwM⟩, hne⟩ := h K hK
  have hww : w' = w := hwK'.eq hwK
  subst hww
  rcases hfib w' K hK L hL M hM hwK hwL hwM with h1 | h1 | h1
  · exact h1
  · exact absurd (by rw [← h1]) hne
  · exact absurd (by rw [← h1, hax]) hne


theorem datumInjective_of_twins [Finite ↥A] [IsMulCommutative ↥A] (Fr : RankFrame F Ω A S)
    (hfib : FibreLE2 S)
    (h : ∀ K ∈ S, ∃ L ∈ S, (∃ w, IsUniqueInvolution K w ∧ IsUniqueInvolution L w) ∧
      axisSub A L ≠ axisSub A K) : Fr.DatumInjective :=
  datumInjective_of_axis Fr (eq_of_twins hfib h)

theorem oddLieType_of_frame_linear [IsSimpleGroup G] (hp2 : p ≠ 2) (hf : 0 < f)
    (hq : 4 ≤ p ^ f) (hZ : Subgroup.center G = ⊥) (Fr : RankFrame F Ω A S)
    [Finite ↥A] [IsMulCommutative ↥A] (hF : Nat.card F = p ^ f) (hcard : Nat.card A = 8)
    (hS : S.Nonempty) (hfib : FibreLE2 S) (hconn : NonCommConnected S)
    (hd : Fr.dataFinset.card = 6)
    (hlin : ∀ K ∈ S, ∀ L ∈ S, K ≠ L →
      Commutes K L ∨ LinearA2Pair F A K L ∨ LinearA2Pair F A L K)
    (hinj : Fr.DatumInjective) (hspan : frameSpan S = ⊤) : CFSG.Blueprint.OddLieType G := by
  obtain ⟨-, -, -, -, hmodel⟩ := weakCT_recognition_of_frame_three_of_linear Fact.out hF hq Fr
    hcard hS hfib hconn hd hlin hinj hspan
  exact ⟨.PSL, 4, p, f, Fact.out, hp2, ⟨Fact.out, hf, by norm_num, by simp, by simp⟩,
    CFSG.Timmesfeld.lieModel_of_center_eq_bot hZ hmodel⟩

theorem oddLieType_of_frame_unitary [IsSimpleGroup G] {K₀ : Type} [Field K₀] [Finite K₀]
    [CharP K₀ p] (hK : Nat.card K₀ = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hnab : ∃ a b : G, a * b ≠ b * a) (Fr : RankFrame F Ω A S) [Finite ↥A]
    [IsMulCommutative ↥A] (hcard : Nat.card A = 8) (hS : S.Nonempty) (hfib : FibreLE2 S)
    (hconn : NonCommConnected S) (hd : Fr.dataFinset.card = 6)
    (hlin : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
      Commutes P Q ∨ UnitaryA2Pair K₀ p f A P Q ∨ UnitaryA2Pair K₀ p f A Q P)
    (hinj : Fr.DatumInjective) (hspan : frameSpan S = ⊤) : CFSG.Blueprint.OddLieType G := by
  have hq2 : p ^ f ≠ 2 := by omega
  refine (weakPhan_simple_recognition_of_frame_three hK hp2 hq Fr hcard hS
    (a2Dichotomy_of_rankFrame_unitary Fr hK hlin) hfib hconn hd (fun P hP => ?_)
    (fun P hP Q hQ hne hnc => exists_unitaryBlockStandardPair_sup hK hq2 (hlin P hP Q hQ hne) hnc)
    hinj hspan hnab).2
  obtain ⟨L, hL, hne, hnc⟩ := Fr.exists_not_commutes hconn hP
  rcases hlin P hP L hL hne with h | h | h
  · exact absurd h hnc
  · exact nonempty_equiv_left_of_a2Pair hK h
  · exact nonempty_equiv_right_of_a2Pair hK h

end CFSG.ClassicalInvolution.ConnectedA2
