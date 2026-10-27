module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Engine
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.CharTwoOver
import CFSG.Adapters.GeneralizedFittingTop

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped Pointwise

variable {G : Type*} [Group G]

theorem le_of_isUniqueMaxOver [Finite G] {H T M K : Subgroup G} (h : IsUniqueMaxOver H T M)
    (hTK : T ≤ K) (hKH : K ≤ H) (hKne : K ≠ H) : K ≤ M := by
  obtain ⟨N, hN, hKN⟩ := exists_isMaxSubgroupIn (lt_of_le_of_ne hKH hKne)
  exact hKN.trans ((isUniqueMaxOver_iff.mp h).2.2 N hN (hTK.trans hKN)).le

theorem exists_minParabolic_of_map_minParabolic [Finite G] (N : Subgroup G) [N.Normal]
    {T H : Subgroup G} (hT : IsSylowTwoOf T H) {M₀ : Subgroup (G ⧸ N)}
    (h : MinParabolic (H.map (QuotientGroup.mk' N)) (T.map (QuotientGroup.mk' N)) M₀) :
    ∃ H₁ M₁ : Subgroup G, T ≤ H₁ ∧ H₁ ≤ H ∧
      H₁.map (QuotientGroup.mk' N) = H.map (QuotientGroup.mk' N) ∧ MinParabolic H₁ T M₁ := by
  set π := QuotientGroup.mk' N
  obtain ⟨H₁, -, ⟨hH₁H, hTH₁, hmap⟩, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun K : Subgroup G => K ≤ H ∧ T ≤ K ∧ K.map π = H.map π) H ⟨le_rfl, hT.1, rfl⟩
  have hlift : ∀ K : Subgroup G, T ≤ K → K ≤ H₁ → K ≠ H₁ → K ≤ H₁ ⊓ M₀.comap π := by
    intro K hTK hKH₁ hKne
    have hKH : K ≤ H := hKH₁.trans hH₁H
    have hne : K.map π ≠ H.map π := fun heq =>
      hKne (le_antisymm hKH₁ (hmin ⟨hKH, hTK, heq⟩ hKH₁))
    have hle : K.map π ≤ M₀ := le_of_isUniqueMaxOver h.uniqueMax (Subgroup.map_mono hTK)
      (Subgroup.map_mono hKH) hne
    exact le_inf hKH₁ fun x hx => hle ⟨x, hx, rfl⟩
  have hTM : T ≤ H₁ ⊓ M₀.comap π := le_inf hTH₁ fun x hx => h.le ⟨x, hx, rfl⟩
  have hMH : H₁ ⊓ M₀.comap π < H₁ := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    have : H.map π ≤ M₀ := by
      rw [← hmap]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ H₁ ⊓ M₀.comap π := by rw [heq]; exact hx
      exact hx'.2
    exact absurd (h.maximal.1.trans_le this) (lt_irrefl _)
  refine ⟨H₁, H₁ ⊓ M₀.comap π, hTH₁, hH₁H, hmap, B6.isSylowTwoOf_mono hT hTH₁ hH₁H, ?_, ?_⟩
  · intro hnorm
    refine h.not_normal ?_
    rw [← hmap]
    exact (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map _)
  · refine isUniqueMaxOver_iff.mpr ⟨⟨hMH, fun K hMK hKH => ?_⟩, hTM, fun N' hN' hTN' => ?_⟩
    · by_contra hne
      exact absurd (hlift K (hTM.trans hMK.le) hKH hne) (not_le_of_gt hMK)
    · have hle : N' ≤ H₁ ⊓ M₀.comap π := hlift N' hTN' hN'.1.le hN'.1.ne
      refine le_antisymm hle (by_contra fun hnot => ?_)
      exact hMH.ne (hN'.2 _ (lt_of_le_not_ge hle hnot) hMH.le)

section Components

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
private theorem isComponentOf_conjSub {L : Subgroup Y} (hL : Open.IsComponentOf L ⊤) (t : Y) :
    Open.IsComponentOf (B6.conjSub t L) ⊤ :=
  (CFSG.Adapters.isComponentOf_top_iff _).2
    (CFSG.GorensteinWalter.fstar_isComponentOf_conjugateSubgroup_of_mem
      ((CFSG.Adapters.isComponentOf_top_iff L).1 hL) t (Subgroup.mem_top t))

private theorem conjSub_le_centralizer_of_notMem_normalizer {L : Subgroup Y}
    (hL : Open.IsComponentOf L ⊤) {t : Y} (ht : t ∉ Subgroup.normalizer (L : Set Y)) :
    B6.conjSub t L ≤ Subgroup.centralizer (L : Set Y) := by
  have hne : B6.conjSub t L ≠ L := fun h =>
    ht (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.GorensteinWalter.component_commute_of_ne
      ((CFSG.Adapters.isComponentOf_top_iff _).1 (isComponentOf_conjSub hL t))
      ((CFSG.Adapters.isComponentOf_top_iff L).1 hL) hne)

private theorem conjClosure_le_sup_centralizer {L T W : Subgroup Y} (hL : Open.IsComponentOf L ⊤)
    (hWL : W ≤ L)
    (hRW : T ⊓ Subgroup.normalizer (L : Set Y) ≤ Subgroup.normalizer (W : Set Y)) :
    conjClosure W T ≤ W ⊔ Subgroup.centralizer (L : Set Y) := by
  refine conjClosure_le fun h hh z hz => ?_
  by_cases hn : h ∈ Subgroup.normalizer (L : Set Y)
  · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hRW ⟨hh, hn⟩) z).mp hz)
  · refine Subgroup.mem_sup_right (conjSub_le_centralizer_of_notMem_normalizer hL hn ?_)
    rw [B6.mem_conjSub]
    simpa [mul_assoc] using hWL hz

private theorem le_of_le_sup_centralizer {L W S K : Subgroup Y} (hWL : W ≤ L)
    (hgen : pElementSubgroup 2 W = W) (hS : IsSylowTwoOf S W) (hSK : S ≤ K)
    (hKL : K ≤ Subgroup.normalizer (L : Set Y))
    (hW : W ≤ K ⊔ Subgroup.centralizer (L : Set Y)) : W ≤ K := by
  have hKC : K ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set Y) : Set Y) :=
    hKL.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup L)
  have key : ∀ x : Y, x ∈ W → (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ K := by
    rintro x hxW ⟨k, hk⟩
    have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.iff_card.mpr ⟨k, by rw [Nat.card_zpowers, hk]⟩
    obtain ⟨S', hS', hxS'⟩ := B6.exists_isSylowTwoOf_ge hxp (Subgroup.zpowers_le.mpr hxW)
    obtain ⟨g, hgW, hg⟩ := B6.isSylowTwoOf_exists_conj hS hS'
    have hxS : x ∈ S' := hxS' (Subgroup.mem_zpowers x)
    rw [hg, B6.mem_conjSub] at hxS
    have hg' : g ∈ (K : Set Y) * (Subgroup.centralizer (L : Set Y) : Set Y) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right K _ hKC]
      exact hW hgW
    obtain ⟨k₀, hk₀, c, hc, rfl⟩ := hg'
    obtain ⟨s, hsS, hxs⟩ : ∃ s ∈ S, x = (k₀ * c) * s * (k₀ * c)⁻¹ :=
      ⟨(k₀ * c)⁻¹ * x * (k₀ * c), hxS, by group⟩
    have hcs : c * s = s * c := (Subgroup.mem_centralizer_iff.mp hc s (hWL (hS.1 hsS))).symm
    have hx : x = k₀ * s * k₀⁻¹ := by
      rw [hxs]
      calc k₀ * c * s * (k₀ * c)⁻¹ = k₀ * (c * s * c⁻¹) * k₀⁻¹ := by group
        _ = k₀ * s * k₀⁻¹ := by rw [hcs, mul_inv_cancel_right]
    rw [hx]
    exact K.mul_mem (K.mul_mem hk₀ (hSK hsS)) (K.inv_mem hk₀)
  calc W = pElementSubgroup 2 W := hgen.symm
    _ ≤ K := (Subgroup.closure_le K).2 fun x hx => key x hx.1 hx.2

omit [Finite Y] in
private theorem conjSub_eq_of_conjSub_eq {L T W : Subgroup Y}
    (hRW : T ⊓ Subgroup.normalizer (L : Set Y) ≤ Subgroup.normalizer (W : Set Y)) {s t : Y}
    (hs : s ∈ T) (ht : t ∈ T) (h : B6.conjSub s L = B6.conjSub t L) :
    B6.conjSub s W = B6.conjSub t W := by
  have hL : s⁻¹ * t ∈ Subgroup.normalizer (L : Set Y) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    show B6.conjSub (s⁻¹ * t) L = L
    rw [B6.conjSub_mul, ← h, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  have hW : B6.conjSub (s⁻¹ * t) W = W :=
    B6.conjSub_eq_self (hRW ⟨T.mul_mem (T.inv_mem hs) ht, hL⟩)
  calc B6.conjSub s W = B6.conjSub s (B6.conjSub (s⁻¹ * t) W) := by rw [hW]
    _ = B6.conjSub t W := by rw [← B6.conjSub_mul, mul_inv_cancel_left]

private theorem commute_of_conjSub_ne {L : Subgroup Y} (hL : Open.IsComponentOf L ⊤) {s t : Y}
    (h : B6.conjSub s L ≠ B6.conjSub t L) {x y : Y} (hx : x ∈ B6.conjSub s L)
    (hy : y ∈ B6.conjSub t L) : x * y = y * x :=
  (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.GorensteinWalter.component_commute_of_ne
      ((CFSG.Adapters.isComponentOf_top_iff _).1 (isComponentOf_conjSub hL s))
      ((CFSG.Adapters.isComponentOf_top_iff _).1 (isComponentOf_conjSub hL t)) h) hx) y hy).symm

end Components

section SylowJoin

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
private theorem isSylowTwoOf_sup_of_commute {A B SA SB : Subgroup Y}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : IsSylowTwoOf SA A)
    (hB : IsSylowTwoOf SB B) : IsSylowTwoOf (SA ⊔ SB) (A ⊔ B) := by
  let φ : ↥A × ↥B →* Y := A.subtype.noncommCoprod B.subtype fun a b => hAB a.1 a.2 b.1 b.2
  have hSAB : SA ≤ Subgroup.normalizer (SB : Set Y) := fun a ha =>
    B6.mem_normalizer_of_forall_mem
      (fun b hb => by rw [hAB a (hA.1 ha) b (hB.1 hb), mul_inv_cancel_right]; exact hb)
      (fun b hb => by
        rw [hAB a⁻¹ (A.inv_mem (hA.1 ha)) b (hB.1 hb), inv_mul_cancel_right]; exact hb)
  have himg : ((SA.subgroupOf A).prod (SB.subgroupOf B)).map φ = SA ⊔ SB := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact Subgroup.mul_mem_sup ha hb
    · intro hx
      have hx' : x ∈ (SA : Set Y) * (SB : Set Y) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right SA SB hSAB]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      exact ⟨(⟨a, hA.1 ha⟩, ⟨b, hB.1 hb⟩), ⟨ha, hb⟩, rfl⟩
  have hrange : (⊤ : Subgroup (↥A × ↥B)).map φ = A ⊔ B := by
    rw [← MonoidHom.range_eq_map]
    have := MonoidHom.noncommCoprod_range A.subtype B.subtype fun a b => hAB a.1 a.2 b.1 b.2
    rwa [A.range_subtype, B.range_subtype] at this
  refine ⟨sup_le_sup hA.1 hB.1, fun x => ?_, fun h2 => ?_⟩
  · have hx : (x : Y) ∈ (SA : Set Y) * (SB : Set Y) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right SA SB hSAB]
      exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    obtain ⟨m, hm⟩ := hA.2.1 ⟨a, ha⟩
    obtain ⟨n, hn⟩ := hB.2.1 ⟨b, hb⟩
    have hm' : a ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hn' : b ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    replace hab : a * b = (x : Y) := hab
    have hcomm : Commute a b := hAB a (hA.1 ha) b (hB.1 hb)
    have ha' : a ^ 2 ^ (m + n) = 1 := by rw [pow_add, pow_mul, hm', one_pow]
    have hb' : b ^ 2 ^ (m + n) = 1 := by rw [add_comm, pow_add, pow_mul, hn', one_pow]
    refine ⟨m + n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hab, hcomm.mul_pow, ha', hb', mul_one]
    rfl
  · have h1 : (SA ⊔ SB).relIndex (A ⊔ B) ∣
        ((SA.subgroupOf A).prod (SB.subgroupOf B)).index := by
      rw [← himg, ← hrange, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
      exact Subgroup.index_dvd_of_le le_sup_left
    rw [Subgroup.index_prod] at h1
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp (h2.trans h1) with h | h
    · exact hA.2.2 h
    · exact hB.2.2 h

omit [Finite Y] in
private theorem isSylowTwoOf_bot : IsSylowTwoOf (⊥ : Subgroup Y) ⊥ :=
  ⟨le_rfl, IsPGroup.of_card (n := 0) (by simp), by
    show ¬ 2 ∣ (⊥ : Subgroup Y).relIndex ⊥
    rw [Subgroup.relIndex_eq_one.mpr le_rfl]
    decide⟩

omit [Finite Y] in
private theorem isSylowTwoOf_iSup_inf (T : Subgroup Y) (𝒢 : Finset (Subgroup Y))
    (hcomm : ∀ a ∈ 𝒢, ∀ b ∈ 𝒢, a ≠ b → ∀ x ∈ a, ∀ y ∈ b, x * y = y * x)
    (hS : ∀ a ∈ 𝒢, IsSylowTwoOf (a ⊓ T) a) :
    IsSylowTwoOf (⨆ a ∈ 𝒢, a ⊓ T) (⨆ a ∈ 𝒢, a) := by
  classical
  induction 𝒢 using Finset.induction_on with
  | empty => simpa using isSylowTwoOf_bot (Y := Y)
  | insert a 𝒢 ha ih =>
    rw [Finset.iSup_insert, Finset.iSup_insert]
    refine isSylowTwoOf_sup_of_commute (fun x hx y hy => ?_) (hS a (Finset.mem_insert_self a 𝒢))
      (ih (fun b hb c hc => hcomm b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc))
        (fun b hb => hS b (Finset.mem_insert_of_mem hb)))
    have hle : (⨆ b ∈ 𝒢, b) ≤ Subgroup.centralizer ({x} : Set Y) := by
      refine iSup₂_le fun b hb z hz => ?_
      have hne : a ≠ b := fun h => ha (h ▸ hb)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hcomm b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self a 𝒢) hne.symm z hz x hx)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

end SylowJoin

section Wreath

variable {Y : Type*} [Group Y] [Finite Y]

private theorem isSylowTwoOf_conjClosure_inf {L T W : Subgroup Y} (hL : Open.IsComponentOf L ⊤)
    (hT : IsPGroup 2 T) (hWL : W ≤ L)
    (hRW : T ⊓ Subgroup.normalizer (L : Set Y) ≤ Subgroup.normalizer (W : Set Y))
    (hS : IsSylowTwoOf (T ⊓ L) W) : IsSylowTwoOf (conjClosure W T ⊓ T) (conjClosure W T) := by
  classical
  let Ω : Set (Subgroup Y) := {a | ∃ t ∈ T, a = B6.conjSub t W}
  let 𝒢 : Finset (Subgroup Y) := (Set.toFinite Ω).toFinset
  have hmem : ∀ a, a ∈ 𝒢 ↔ ∃ t ∈ T, a = B6.conjSub t W := fun a =>
    Set.Finite.mem_toFinset _
  have hD : conjClosure W T = ⨆ a ∈ 𝒢, a := by
    refine le_antisymm (conjClosure_le fun h hh z hz => ?_) (iSup₂_le fun a ha x hx => ?_)
    · refine Subgroup.mem_iSup_of_mem (B6.conjSub h W)
        (Subgroup.mem_iSup_of_mem ((hmem _).2 ⟨h, hh, rfl⟩) ?_)
      rw [B6.mem_conjSub]
      simpa [mul_assoc] using hz
    · obtain ⟨t, ht, rfl⟩ := (hmem a).1 ha
      rw [B6.mem_conjSub] at hx
      simpa [mul_assoc] using mem_conjClosure ht hx
  have hWT : W ⊓ T = T ⊓ L :=
    le_antisymm (le_inf inf_le_right (inf_le_left.trans hWL)) (le_inf hS.1 inf_le_left)
  have hSyl : ∀ a ∈ 𝒢, IsSylowTwoOf (a ⊓ T) a := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := (hmem a).1 ha
    have hTt : B6.conjSub t T = T := B6.conjSub_eq_self (Subgroup.le_normalizer ht)
    have : B6.conjSub t W ⊓ T = B6.conjSub t (T ⊓ L) := by
      rw [← hWT, OrderIso.map_inf, hTt]
    rw [this]
    exact B6.isSylowTwoOf_conjSub hS t
  have hcomm : ∀ a ∈ 𝒢, ∀ b ∈ 𝒢, a ≠ b → ∀ x ∈ a, ∀ y ∈ b, x * y = y * x := by
    intro a ha b hb hab x hx y hy
    obtain ⟨s, hs, rfl⟩ := (hmem a).1 ha
    obtain ⟨t, ht, rfl⟩ := (hmem b).1 hb
    have hne : B6.conjSub s L ≠ B6.conjSub t L := fun h =>
      hab (conjSub_eq_of_conjSub_eq hRW hs ht h)
    exact commute_of_conjSub_ne hL hne ((B6.conjSub s).monotone hWL hx)
      ((B6.conjSub t).monotone hWL hy)
  have h := isSylowTwoOf_iSup_inf T 𝒢 hcomm hSyl
  rw [← hD] at h
  have hle : (⨆ a ∈ 𝒢, a ⊓ T) ≤ conjClosure W T ⊓ T := by
    refine iSup₂_le fun a ha => inf_le_inf_right T ?_
    rw [hD]
    exact le_iSup₂ (f := fun a (_ : a ∈ 𝒢) => a) a ha
  exact ⟨inf_le_left, hT.to_le inf_le_right,
    fun h2 => h.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left _ hle))⟩

private theorem isSylowTwoOf_conjClosure_sup {L T W : Subgroup Y} (hL : Open.IsComponentOf L ⊤)
    (hT : IsPGroup 2 T) (hWL : W ≤ L)
    (hRW : T ⊓ Subgroup.normalizer (L : Set Y) ≤ Subgroup.normalizer (W : Set Y))
    (hS : IsSylowTwoOf (T ⊓ L) W) : IsSylowTwoOf T (conjClosure W T ⊔ T) := by
  refine ⟨le_sup_right, hT, ?_⟩
  have h := B6.relIndex_inf_eq_relIndex_sup (le_normalizer_conjClosure W T)
  show ¬ 2 ∣ T.relIndex (conjClosure W T ⊔ T)
  rw [sup_comm, ← h, inf_comm]
  exact (isSylowTwoOf_conjClosure_inf hL hT hWL hRW hS).2.2

theorem exists_minParabolic_conjClosure_sup {L T W : Subgroup Y} (hL : Open.IsComponentOf L ⊤)
    (hT : IsPGroup 2 T) (hWL : W ≤ L)
    (hRW : T ⊓ Subgroup.normalizer (L : Set Y) ≤ Subgroup.normalizer (W : Set Y))
    (hgen : pElementSubgroup 2 W = W) (hS : IsSylowTwoOf (T ⊓ L) W)
    (hM : ∃ M, MinParabolic (W ⊔ T ⊓ Subgroup.normalizer (L : Set Y))
      (T ⊓ Subgroup.normalizer (L : Set Y)) M) :
    ∃ M' : Subgroup Y, MinParabolic (conjClosure W T ⊔ T) T M' := by
  obtain ⟨M, hM⟩ := hM
  have hSyl := isSylowTwoOf_conjClosure_sup hL hT hWL hRW hS
  set R : Subgroup Y := T ⊓ Subgroup.normalizer (L : Set Y)
  set C : Subgroup Y := Subgroup.centralizer (L : Set Y)
  set D : Subgroup Y := conjClosure W T
  have hWC : W ≤ Subgroup.normalizer (C : Set Y) := by
    refine le_trans (fun w hw => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    exact fun c hc => (Subgroup.mem_centralizer_iff.mp hc w (hWL hw)).symm
  have hDWC : D ≤ W ⊔ C := conjClosure_le_sup_centralizer hL hWL hRW
  have hWLN : W ≤ Subgroup.normalizer (L : Set Y) := hWL.trans Subgroup.le_normalizer
  have hDN : D ≤ Subgroup.normalizer (L : Set Y) :=
    hDWC.trans (sup_le hWLN (Subgroup.centralizer_le_normalizer _))
  have hTD : T ≤ Subgroup.normalizer (D : Set Y) := le_normalizer_conjClosure W T
  have hWD : W ≤ D := le_conjClosure W T
  have hTDR : T ⊓ D ≤ R := fun x hx => ⟨hx.1, hDN hx.2⟩
  have hS₁R : T ⊓ L ≤ R := fun x hx => ⟨hx.1, Subgroup.le_normalizer hx.2⟩
  have hRM : R ≤ M := hM.le
  have hMlt : M < W ⊔ R := hM.maximal.1
  have hMN : M ≤ Subgroup.normalizer (L : Set Y) := hMlt.le.trans (sup_le hWLN inf_le_right)
  set E : Subgroup Y := ⨅ t ∈ T, B6.conjSub t (M ⊔ C) with hE
  set DM : Subgroup Y := D ⊓ E
  have hmemE : ∀ x, x ∈ E ↔ ∀ t ∈ T, t⁻¹ * x * t ∈ M ⊔ C := fun x => by
    simp only [hE, Subgroup.mem_iInf, B6.mem_conjSub]
  have hTE : T ≤ Subgroup.normalizer (E : Set Y) := fun s hs =>
    B6.mem_normalizer_of_forall_mem
      (fun x hx => (hmemE _).2 fun t ht => by
        have := (hmemE x).1 hx (s⁻¹ * t) (T.mul_mem (T.inv_mem hs) ht)
        simpa [mul_assoc] using this)
      (fun x hx => (hmemE _).2 fun t ht => by
        have := (hmemE x).1 hx (s * t) (T.mul_mem hs ht)
        simpa [mul_assoc] using this)
  have hTDM : T ≤ Subgroup.normalizer (DM : Set Y) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTD ht, hTE ht⟩
  have hmain : ∀ K : Subgroup Y, T ≤ K → K ≤ D ⊔ T → K ≠ D ⊔ T → K ≤ DM ⊔ T := by
    intro K hTK hKG hKne
    have hWU : ¬ W ≤ (K ⊓ Subgroup.normalizer (L : Set Y)) ⊔ C := by
      intro hWU
      have hWK : W ≤ K ⊓ Subgroup.normalizer (L : Set Y) :=
        le_of_le_sup_centralizer hWL hgen hS
          (le_inf (inf_le_left.trans hTK) (hS₁R.trans inf_le_right)) inf_le_right hWU
      have hDK : D ≤ K := conjClosure_le fun h hh z hz =>
        K.mul_mem (K.mul_mem (hTK hh) (hWK hz).1) (K.inv_mem (hTK hh))
      exact hKne (le_antisymm hKG (sup_le hDK hTK))
    have hRU : R ≤ (K ⊓ Subgroup.normalizer (L : Set Y)) ⊔ C := fun x hx =>
      Subgroup.mem_sup_left ⟨hTK hx.1, hx.2⟩
    have hPi : (W ⊔ R) ⊓ ((K ⊓ Subgroup.normalizer (L : Set Y)) ⊔ C) ≤ M := by
      refine le_of_isUniqueMaxOver hM.uniqueMax (le_inf le_sup_right hRU) inf_le_left ?_
      intro heq
      exact hWU (le_sup_left.trans (heq.symm.le.trans inf_le_right))
    have hdMc : ∀ d ∈ K ⊓ D, d ∈ M ⊔ C := by
      intro d hd
      have hd' : d ∈ (W : Set Y) * (C : Set Y) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right W C hWC]
        exact hDWC hd.2
      obtain ⟨w, hw, c, hc, rfl⟩ := hd'
      have hwU : w ∈ (K ⊓ Subgroup.normalizer (L : Set Y)) ⊔ C := by
        have h1 : w * c ∈ (K ⊓ Subgroup.normalizer (L : Set Y)) ⊔ C :=
          Subgroup.mem_sup_left ⟨hd.1, hDN hd.2⟩
        have h2 : c⁻¹ ∈ (K ⊓ Subgroup.normalizer (L : Set Y)) ⊔ C :=
          Subgroup.mem_sup_right (C.inv_mem hc)
        simpa using Subgroup.mul_mem _ h1 h2
      exact Subgroup.mul_mem_sup (hPi ⟨Subgroup.mem_sup_left hw, hwU⟩) hc
    intro k hk
    have hKG' : K ≤ T ⊔ D := hKG.trans (sup_comm D T).le
    have hk' : k ∈ (T : Set Y) * (D : Set Y) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T D hTD]
      exact hKG' hk
    obtain ⟨t, ht, d, hd, rfl⟩ := hk'
    have hdK : d ∈ K := by simpa using K.mul_mem (K.inv_mem (hTK ht)) hk
    have hdDM : d ∈ DM := by
      refine ⟨hd, (hmemE d).2 fun s hs => hdMc _ ⟨?_, ?_⟩⟩
      · exact K.mul_mem (K.mul_mem (K.inv_mem (hTK hs)) hdK) (hTK hs)
      · simpa using (Subgroup.mem_normalizer_iff.mp (hTD (T.inv_mem hs)) d).mp hd
    rw [sup_comm]
    exact Subgroup.mul_mem_sup ht hdDM
  have hlt : DM ⊔ T < D ⊔ T := by
    refine lt_of_le_of_ne (sup_le_sup_right inf_le_left T) fun heq => ?_
    have hWM : W ≤ M ⊔ C := by
      intro w hw
      have hwG : w ∈ T ⊔ DM := by
        have : w ∈ D ⊔ T := Subgroup.mem_sup_left (hWD hw)
        rw [← heq, sup_comm] at this
        exact this
      have hw' : w ∈ (T : Set Y) * (DM : Set Y) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right T DM hTDM]
        exact hwG
      obtain ⟨t, ht, e, he, rfl⟩ := hw'
      have htD : t ∈ D := by simpa using D.mul_mem (hWD hw) (D.inv_mem he.1)
      have htM : t ∈ M := hRM (hTDR ⟨ht, htD⟩)
      have heMc : e ∈ M ⊔ C := by simpa using (hmemE e).1 he.2 1 T.one_mem
      exact (M ⊔ C).mul_mem (Subgroup.mem_sup_left htM) heMc
    exact absurd (sup_le (le_of_le_sup_centralizer hWL hgen hS (hS₁R.trans hRM) hMN hWM) hRM)
      (not_le_of_gt hMlt)
  refine ⟨DM ⊔ T, hSyl, fun hnorm => ?_, ?_⟩
  ·
    have hWN : W ≤ Subgroup.normalizer (T : Set Y) := hWD.trans (le_sup_left.trans hnorm)
    have hwR : ∀ w ∈ W, ∀ r ∈ R, w * r * w⁻¹ ∈ R := fun w hw r hr =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hWN hw) r).mp hr.1,
        (Subgroup.normalizer (L : Set Y)).mul_mem
          ((Subgroup.normalizer (L : Set Y)).mul_mem (hWLN hw) hr.2)
          ((Subgroup.normalizer (L : Set Y)).inv_mem (hWLN hw))⟩
    refine hM.not_normal (sup_le (fun w hw => ?_) Subgroup.le_normalizer)
    exact B6.mem_normalizer_of_forall_mem (fun r hr => hwR w hw r hr)
      (fun r hr => by simpa using hwR w⁻¹ (W.inv_mem hw) r hr)
  · refine isUniqueMaxOver_iff.mpr ⟨⟨hlt, fun K hK1 hK2 => ?_⟩, le_sup_right, fun N hN hTN => ?_⟩
    · by_contra hne
      exact absurd (hmain K (le_sup_right.trans hK1.le) hK2 hne) (not_le_of_gt hK1)
    · have hle := hmain N hTN hN.1.le hN.1.ne
      refine le_antisymm hle (by_contra fun hnot => ?_)
      exact hlt.ne (hN.2 _ (lt_of_le_not_ge hle hnot) hlt.le)

end Wreath

section PElement

variable {Y : Type*} [Group Y]

theorem pElementSubgroup_pElementSubgroup (p : ℕ) (A : Subgroup Y) :
    pElementSubgroup p (pElementSubgroup p A) = pElementSubgroup p A :=
  le_antisymm (pElementSubgroup_le _)
    (Subgroup.closure_mono fun _ hx => ⟨Subgroup.subset_closure hx, hx.2⟩)

theorem normalizer_le_normalizer_pElementSubgroup (p : ℕ) (A : Subgroup Y) :
    Subgroup.normalizer (A : Set Y) ≤ Subgroup.normalizer (pElementSubgroup p A : Set Y) := by
  have key : ∀ g ∈ Subgroup.normalizer (A : Set Y), ∀ x ∈ pElementSubgroup p A,
      g * x * g⁻¹ ∈ pElementSubgroup p A := by
    intro g hg x hx
    change x ∈ Subgroup.closure {y : Y | y ∈ A ∧ ∃ k : ℕ, orderOf y = p ^ k} at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hx.1, ?_⟩
      obtain ⟨k, hk⟩ := hx.2
      refine ⟨k, ?_⟩
      rw [← hk, ← MulAut.conj_apply]
      exact (MulAut.conj g).orderOf_eq x
    | one => simp
    | mul x y _ _ hx hy => simpa [mul_assoc] using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa [mul_assoc] using Subgroup.inv_mem _ hx
  intro g hg
  exact B6.mem_normalizer_of_forall_mem (key g hg)
    fun x hx => by simpa using key g⁻¹ (Subgroup.inv_mem _ hg) x hx

end PElement

section Packaging

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem kFact_of_le (hK : KFactChevMinParabolic) (hX : GNSetting X T)
    {L P R : Subgroup (X ⧸ gnC T)} (hL : Open.IsComponentOf L ⊤)
    (hChev : IsChevTwo (↥L ⧸ Subgroup.center ↥L)) (hP : IsMinOverBorel L (gnImg T T ⊓ L) P)
    (hRT : R ≤ gnImg T T) (hRN : R ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    (hLR : gnImg T T ⊓ L ≤ R) :
    (∃ M : Subgroup (X ⧸ gnC T),
      MinParabolic (pElementSubgroup 2 (conjClosure P R) ⊔ R) R M) ∧
    (conjClosure P R ≠ L →
      ⁅pCoreOf 2 (twoResidual (pElementSubgroup 2 (conjClosure P R))),
        twoResidual (pElementSubgroup 2 (conjClosure P R))⁆ ≠ ⊥) := by
  have hTp : IsPGroup 2 (gnImg T T) := hX.sylow.2.1.map _
  have hSyl : IsSylowTwoOf (gnImg T T ⊓ L) L :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow
      hL.2.1
  have hRL : R ⊓ L = gnImg T T ⊓ L :=
    le_antisymm (le_inf (inf_le_left.trans hRT) inf_le_right) (le_inf hLR inf_le_right)
  exact hK _ L R P hL.2.2 hChev hRN (hTp.to_le hRT) (by rw [hRL]; exact hSyl)
    (by rw [hRL]; exact hP)

theorem pElementSubgroup_conjClosure_facts (hX : GNSetting X T) {L P R : Subgroup (X ⧸ gnC T)}
    (hL : Open.IsComponentOf L ⊤) (hP : IsMinOverBorel L (gnImg T T ⊓ L) P)
    (hRN : R ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T))) :
    pElementSubgroup 2 (conjClosure P R) ≤ L ∧
      R ≤ Subgroup.normalizer (pElementSubgroup 2 (conjClosure P R) : Set (X ⧸ gnC T)) ∧
      IsSylowTwoOf (gnImg T T ⊓ L) (pElementSubgroup 2 (conjClosure P R)) := by
  have hTp : IsPGroup 2 (gnImg T T) := hX.sylow.2.1.map _
  have hSyl : IsSylowTwoOf (gnImg T T ⊓ L) L :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow
      hL.2.1
  have hPS : gnImg T T ⊓ L ≤ P := fun x hx => hP.2.1.le ⟨hx.2, Subgroup.le_normalizer hx⟩
  have hWL : pElementSubgroup 2 (conjClosure P R) ≤ L :=
    (pElementSubgroup_le _).trans (conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp (hRN hh) z).mp (hP.1 hz))
  refine ⟨hWL, (le_normalizer_conjClosure P R).trans
    (normalizer_le_normalizer_pElementSubgroup 2 _), ?_⟩
  refine B6.isSylowTwoOf_mono hSyl (fun x hx => ?_) hWL
  refine Subgroup.subset_closure ⟨le_conjClosure P R (hPS hx), ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hTp ⟨x, hx.1⟩
  exact ⟨k, (Subgroup.orderOf_coe ⟨x, hx.1⟩).trans hk⟩

theorem exists_minParabolic_of_gnSetting (hK : KFactChevMinParabolic) (hX : GNSetting X T)
    {L P : Subgroup (X ⧸ gnC T)} (hL : Open.IsComponentOf L ⊤)
    (hChev : IsChevTwo (↥L ⧸ Subgroup.center ↥L)) (hP : IsMinOverBorel L (gnImg T T ⊓ L) P) :
    ∃ H₁ M₁ : Subgroup X, T ≤ H₁ ∧
      H₁.map (QuotientGroup.mk' (gnC T)) =
        conjClosure (pElementSubgroup 2 (conjClosure P
          (gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T T) ⊔ gnImg T T ∧
      MinParabolic H₁ T M₁ ∧ CharTwo H₁ := by
  set π := QuotientGroup.mk' (gnC T)
  set T' : Subgroup (X ⧸ gnC T) := gnImg T T
  set R : Subgroup (X ⧸ gnC T) := T' ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))
  set W : Subgroup (X ⧸ gnC T) := pElementSubgroup 2 (conjClosure P R)
  have hTp : IsPGroup 2 T' := hX.sylow.2.1.map _
  have hM : ∃ M, MinParabolic (W ⊔ R) R M :=
    (kFact_of_le hK hX hL hChev hP inf_le_left inf_le_right
      fun x hx => ⟨hx.1, Subgroup.le_normalizer hx.2⟩).1
  obtain ⟨hWL, hRW, hS⟩ := pElementSubgroup_conjClosure_facts hX hL hP (R := R) inf_le_right
  obtain ⟨M', hM'⟩ := exists_minParabolic_conjClosure_sup hL hTp hWL hRW
    (pElementSubgroup_pElementSubgroup 2 _) hS hM
  set H : Subgroup X := (conjClosure W T' ⊔ T').comap π
  have hHmap : H.map π = conjClosure W T' ⊔ T' :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hTH : T ≤ H := fun x hx => Subgroup.mem_sup_right ⟨x, hx, rfl⟩
  obtain ⟨H₁, M₁, hTH₁, -, hmap, hmin⟩ := exists_minParabolic_of_map_minParabolic (gnC T)
    (B6.isSylowTwoOf_mono hX.sylow hTH le_top) (by rw [hHmap]; exact hM')
  refine ⟨H₁, M₁, hTH₁, hmap.trans hHmap, hmin, ?_⟩
  exact Tits.GN516.charTwo_of_pCoreOf_le hX
    ((B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow).trans hTH₁)

end Packaging

end CFSG.AGLEmbeddingD2.GN
