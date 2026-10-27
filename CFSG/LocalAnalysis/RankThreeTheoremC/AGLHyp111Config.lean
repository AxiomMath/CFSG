module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles
public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.CharacterTheory.Semidihedral.PrimeOrderCyclicConfinementLift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {X : Type*} [Group X] [Finite X] {S : Subgroup X} {g : X}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) : g ∈ Subgroup.normalizer (S : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    simpa using h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem fusionIsSylowIn_map_conj {X : Type*} [Group X] {q : ℕ} {S W : Subgroup X} {k : X}
    (hk : k ∈ Subgroup.normalizer (W : Set X)) (hS : fusionIsSylowIn q S W) :
    fusionIsSylowIn q (S.map (MulAut.conj k).toMonoidHom) W := by
  obtain ⟨hSW, hSq, hmax⟩ := hS
  refine ⟨?_, hSq.map _, fun P hPW hPq hSP => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    simpa using (Subgroup.mem_normalizer_iff.mp hk x).mp (hSW hx)
  · have hcW : P.comap (MulAut.conj k).toMonoidHom ≤ W := fun x hx => by
      have hx' : k * x * k⁻¹ ∈ W := hPW (by simpa using hx)
      have := (Subgroup.mem_normalizer_iff.mp hk x).mpr hx'
      exact this
    have hcq : IsPGroup q (P.comap (MulAut.conj k).toMonoidHom) :=
      hPq.comap_of_injective _ (MulAut.conj k).injective
    have hle : S ≤ P.comap (MulAut.conj k).toMonoidHom := Subgroup.map_le_iff_le_comap.mp hSP
    have heq := hmax _ hcW hcq hle
    rw [← heq, Subgroup.map_comap_eq_self_of_surjective (MulAut.conj k).surjective]

@[expose] def IsAGLQ (p : ℕ) (M Q : Subgroup G) : Prop :=
  Q ≤ M ∧ IsPGroup p Q ∧ (3 ≤ pRank p Q ∨ ∃ E : Subgroup G, E ≤ Q ∧ IsElemAbelian p E ∧
    Nat.card E = p ^ 2 ∧ rankThreeGamma 1 p E ≤ M)

@[expose]
def AGLCovers (p : ℕ) (H N : Subgroup G) (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
    Prop :=
  K ≤ ((H ⊓ N).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))

@[expose]
def AGLAbsorbs (p : ℕ) (M H : Subgroup G) (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
    Prop :=
  ∀ Q N : Subgroup G, IsAGLQ p M Q → Q ≤ H → IsTwoLocal N → ¬ N ≤ M → Q ≤ N →
    AGLCovers p H N K → N ≤ H

structure AGLHyp111Pair (p : ℕ) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop where
  base : IsAGLQ p M Q
  le_H : Q ≤ H
  not_le : ¬ H ≤ M
  not_le_X0 : ¬ K ≤ d1X0 p M H
  primeCore_le : (primeComplementCore (G := H) p).map H.subtype ≤ M
  absorbs : AGLAbsorbs p M H K

theorem AGLHyp111Pair.rebase {p : ℕ} {M H Q A : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h : AGLHyp111Pair p M H Q K)
    (hA : IsAGLQ p M A) (hAH : A ≤ H) : AGLHyp111Pair p M H A K :=
  { h with base := hA, le_H := hAH }

@[expose] def IsMaxInvariantTwoIn (A R Y : Subgroup G) : Prop :=
  R ≤ Y ∧ IsPGroup 2 R ∧ A ≤ Subgroup.normalizer (R : Set G) ∧
    ∀ S : Subgroup G, S ≤ Y → IsPGroup 2 S → A ≤ Subgroup.normalizer (S : Set G) → R ≤ S → S = R

open QuotientGroup in
theorem cover_normalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H Q R : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hQH : Q ≤ H) (hQp : IsPGroup p Q)
    (hR : IsMaxInvariantTwoIn Q R (d1PlusCore p H K)) :
    K ≤ ((H ⊓ Subgroup.normalizer (R : Set G)).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRX, hR2, hQR, hRmax⟩ := hR
  set O := primeComplementCore (G := H) p with hOdef
  set π := QuotientGroup.mk' O with hπ
  have hXH : d1PlusCore p H K ≤ H := Subgroup.map_subtype_le _
  have hRH : R ≤ H := hRX.trans hXH
  set R' := R.subgroupOf H with hR'
  set Q' := Q.subgroupOf H with hQ'
  set W := R' ⊔ O with hW
  have hRmap : R'.map H.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRH
  have hQmap : Q'.map H.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQH
  have hR'C : R' ≤ (Subgroup.centralizer (K : Set _)).comap π := by
    intro x hx
    have hxX : (x : G) ∈ d1PlusCore p H K := hRX hx
    obtain ⟨y, hy, hyx⟩ := hxX
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have hOC : O ≤ (Subgroup.centralizer (K : Set _)).comap π := by
    intro x hx
    have h1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    simp only [Subgroup.mem_comap, h1]
    exact Subgroup.one_mem _
  have hWC : W ≤ (Subgroup.centralizer (K : Set _)).comap π := sup_le hR'C hOC
  have hR'2 : IsPGroup 2 R' := hR2.comap_subtype
  have hR'cop : p.Coprime (Nat.card R') := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR'2
    rw [hn]
    exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right n
  have hWcop : p.Coprime (Nat.card W) :=
    normal_coprime_sup_coprime p R' O (primeComplementCore_normal p) hR'cop
      (primeComplementCore_coprime p)
  have hQ'R' : Q' ≤ Subgroup.normalizer (R' : Set H) := by
    intro q hq
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    show ((q * x * q⁻¹ : H) : G) ∈ R
    push_cast
    exact (Subgroup.mem_normalizer_iff.mp (hQR hq) x).mp hx
  have hQ'W : Q' ≤ Subgroup.normalizer (W : Set H) := by
    intro q hq
    refine mem_normalizer_of_conj_mem fun w hw => ?_
    have hw' : w ∈ ((R' ⊔ O : Subgroup H) : Set H) := hw
    rw [Subgroup.mul_normal R' O] at hw'
    obtain ⟨r, hr, o, ho, rfl⟩ := hw'
    have : q * (r * o) * q⁻¹ = (q * r * q⁻¹) * (q * o * q⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp (hQ'R' hq) r).mp hr)
      ((primeComplementCore_normal p).conj_mem o ho q)
  obtain ⟨S, hSsyl, hRS, hQS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp
    Nat.prime_two (hQp.comap_subtype) ((Nat.Prime.coprime_iff_not_dvd hp).mp hWcop) hQ'W
    le_sup_left hR'2 hQ'R'
  have hSR : S = R' := by
    have hSX : S.map H.subtype ≤ d1PlusCore p H K := Subgroup.map_mono (hSsyl.1.trans hWC)
    have hS2 : IsPGroup 2 (S.map H.subtype) := hSsyl.2.1.map _
    have hQS' : Q ≤ Subgroup.normalizer ((S.map H.subtype : Subgroup G) : Set G) :=
      hQmap ▸ (Subgroup.map_mono hQS).trans (Subgroup.le_normalizer_map _)
    have hRS' : R ≤ S.map H.subtype := hRmap ▸ Subgroup.map_mono hRS
    have heq := hRmax _ hSX hS2 hQS' hRS'
    rw [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective S, heq]
    rfl
  have hR'syl : fusionIsSylowIn 2 R' W := hSR ▸ hSsyl
  intro kb hkb
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective O kb
  have hkW : k ∈ Subgroup.normalizer (W : Set H) := by
    refine mem_normalizer_of_conj_mem fun w hw => ?_
    have hwC : π w ∈ Subgroup.centralizer (K : Set _) := hWC hw
    have hcomm : π k * π w = π w * π k := (Subgroup.mem_centralizer_iff.mp hwC (π k) hkb)
    have hker : (k * w * k⁻¹) * w⁻¹ ∈ O := by
      rw [← QuotientGroup.eq_one_iff]
      show π ((k * w * k⁻¹) * w⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have := W.mul_mem (le_sup_right (a := R') hker) hw
    simpa using this
  obtain ⟨P₁, hP₁⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hR'syl
  obtain ⟨P₂, hP₂⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn
    (fusionIsSylowIn_map_conj hkW hR'syl)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W P₁ P₂
  have hconj : R'.map (MulAut.conj k).toMonoidHom = R'.map (MulAut.conj (g : H)).toMonoidHom := by
    rw [← hP₂, ← hg, CFSG.Goldschmidt.G310.map_subtype_smul_sylow, hP₁]
  have hg' : (g : H) ∈ ((O ⊔ R' : Subgroup H) : Set H) := by
    rw [sup_comm]; exact g.2
  rw [Subgroup.normal_mul O R'] at hg'
  obtain ⟨o, ho, r, hr, hgor⟩ := hg'
  set h := o⁻¹ * k with hh
  have hhR : ((h : H) : G) ∈ Subgroup.normalizer (R : Set G) := by
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have hxH : x ∈ H := hRH hx
    have hx' : (⟨x, hxH⟩ : H) ∈ R' := hx
    have hmem : k * ⟨x, hxH⟩ * k⁻¹ ∈ R'.map (MulAut.conj (g : H)).toMonoidHom := by
      rw [← hconj]; exact ⟨_, hx', by simp⟩
    obtain ⟨y, hy, hyeq⟩ := hmem
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyeq
    have hkey : h * ⟨x, hxH⟩ * h⁻¹ = r * y * r⁻¹ := by
      rw [hh]
      have : o⁻¹ * k * ⟨x, hxH⟩ * (o⁻¹ * k)⁻¹ = o⁻¹ * (k * ⟨x, hxH⟩ * k⁻¹) * o := by group
      rw [this, ← hyeq, ← hgor]
      group
    have hin : h * ⟨x, hxH⟩ * h⁻¹ ∈ R' := by
      rw [hkey]
      exact R'.mul_mem (R'.mul_mem hr hy) (R'.inv_mem hr)
    have : ((h * ⟨x, hxH⟩ * h⁻¹ : H) : G) = (h : G) * x * (h : G)⁻¹ := by push_cast; rfl
    rw [← this]
    exact hin
  refine ⟨h, ⟨h.2, hhR⟩, ?_⟩
  show π (o⁻¹ * k) = π k
  have ho1 : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  rw [map_mul, map_inv, ho1, inv_one, one_mul]

theorem star_of_pair {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M H Q R : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h : AGLHyp111Pair p M H Q K)
    (hb3 : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → Q ≤ Subgroup.normalizer (S : Set G) →
      S ≤ d1PlusCore p H K)
    (hR : IsMaxInvariantTwoIn Q R (d1PlusCore p H K)) (hR1 : R ≠ ⊥) :
    CFSG.Quasithin.CGS R ≤ H ∧ CFSG.LocalAnalysis.RankThreeUC.S15.IsMaxInvariantTwo Q R := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcov := cover_normalizer hp hp2 h.le_H h.base.2.1 hR
  obtain ⟨hRX, hR2, hQR, hRmax⟩ := hR
  have hN : ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H := by
    intro C hCR hC1 hchar
    have hNRC : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) :=
      CFSG.Semidihedral.PrimeOrderCyclicConfinementLift.normalizer_le_of_characteristic_subgroupOf
        hCR hchar
    have hcovC : AGLCovers p H (Subgroup.normalizer (C : Set G)) K :=
      hcov.trans (Subgroup.map_mono fun x hx => ⟨hx.1, hNRC hx.2⟩)
    have hNM : ¬ Subgroup.normalizer (C : Set G) ≤ M := by
      intro hNM
      exact h.not_le_X0 (hcovC.trans (Subgroup.map_mono fun x hx => ⟨hx.1, hNM hx.2⟩))
    exact h.absorbs Q _ h.base h.le_H ⟨C, hC1, hR2.to_le hCR, rfl⟩ hNM (hQR.trans hNRC) hcovC
  have hCGS : CFSG.Quasithin.CGS R ≤ H :=
    iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hchar => hN C hCR hC1 hchar
  refine ⟨hCGS, hR2, hQR, fun S hS2 hQS hRS => ?_⟩
  have hNRH : Subgroup.normalizer (R : Set G) ≤ H := by
    refine hN R le_rfl hR1 ?_
    rw [Subgroup.subgroupOf_self]
    infer_instance
  set T := S ⊓ Subgroup.normalizer (R : Set G) with hT
  have hT2 : IsPGroup 2 T := hS2.to_le inf_le_left
  have hQT : Q ≤ Subgroup.normalizer (T : Set G) :=
    (le_inf hQS (hQR.trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf)
  have hTX := hb3 T hT2 (inf_le_right.trans hNRH) hQT
  have hTR : T = R := hRmax T hTX hT2 hQT (le_inf hRS Subgroup.le_normalizer)
  by_contra hSR
  have hlt : R.subgroupOf S ≠ ⊤ := by
    intro htop
    exact hSR (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hRS)
  haveI : Group.IsNilpotent S := hS2.isNilpotent
  obtain ⟨x, hxN, hxR⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (R.subgroupOf S) (lt_top_iff_ne_top.mpr hlt))
  have hmapR : (R.subgroupOf S).map S.subtype = R := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRS]
  have hxN' : (x : G) ∈ Subgroup.normalizer (R : Set G) := by
    have := Subgroup.le_normalizer_map S.subtype ⟨x, hxN, rfl⟩
    rwa [hmapR] at this
  have hxT : (x : G) ∈ T := ⟨x.2, hxN'⟩
  rw [hTR] at hxT
  exact hxR hxT

theorem eq_of_factor {M H₁ H₂ U : Subgroup G} (hM : IsTwoLocal M) (hH₁ : GLBIsMaxTwoLocal H₁)
    (hH₂ : GLBIsMaxTwoLocal H₂) (hUH : H₁ ≤ Subgroup.normalizer (U : Set G)) (hUM : U ≤ M)
    (hOU : pCoreOf 2 M ≤ U)
    (h₁ : ∀ x ∈ H₁, ∃ m ∈ H₁ ⊓ M, ∃ y ∈ H₁ ⊓ H₂, x = m * y)
    (h₂ : ∀ x ∈ H₂, ∃ m ∈ H₂ ⊓ M, ∃ y ∈ H₁ ⊓ H₂, x = m * y) : H₁ = H₂ := by
  classical
  set W := (H₁ ⊓ M) ⊔ (H₂ ⊓ M) with hW
  set Y := H₁ ⊓ H₂ with hY
  have hWM : W ≤ M := sup_le inf_le_right inf_le_right
  have key : ∀ w ∈ W, ∀ y ∈ Y, ∃ w' ∈ W, ∃ y' ∈ Y, y * w = w' * y' := by
    intro w hw
    rw [hW, Subgroup.sup_eq_closure] at hw
    induction hw using Subgroup.closure_induction'' with
    | mem x hx =>
      intro y hy
      rcases hx with hx | hx
      · obtain ⟨m, hm, y', hy', he⟩ := h₁ (y * x) (H₁.mul_mem hy.1 hx.1)
        exact ⟨m, Subgroup.mem_sup_left hm, y', hy', he⟩
      · obtain ⟨m, hm, y', hy', he⟩ := h₂ (y * x) (H₂.mul_mem hy.2 hx.1)
        exact ⟨m, Subgroup.mem_sup_right hm, y', hy', he⟩
    | inv_mem x hx =>
      intro y hy
      rcases hx with hx | hx
      · obtain ⟨m, hm, y', hy', he⟩ := h₁ (y * x⁻¹) (H₁.mul_mem hy.1 (H₁.inv_mem hx.1))
        exact ⟨m, Subgroup.mem_sup_left hm, y', hy', he⟩
      · obtain ⟨m, hm, y', hy', he⟩ := h₂ (y * x⁻¹) (H₂.mul_mem hy.2 (H₂.inv_mem hx.1))
        exact ⟨m, Subgroup.mem_sup_right hm, y', hy', he⟩
    | one =>
      intro y hy
      exact ⟨1, W.one_mem, y, hy, by simp⟩
    | mul a b _ _ iha ihb =>
      intro y hy
      obtain ⟨a', ha', y', hy', he⟩ := iha y hy
      obtain ⟨b', hb', y'', hy'', he'⟩ := ihb y' hy'
      refine ⟨a' * b', W.mul_mem ha' hb', y'', hy'', ?_⟩
      rw [← mul_assoc, he, mul_assoc, he', ← mul_assoc]
  have hD : ∀ d ∈ H₁ ⊔ H₂, ∃ w ∈ W, ∃ y ∈ Y, d = w * y := by
    intro d hd
    rw [Subgroup.sup_eq_closure] at hd
    induction hd using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨m, hm, y, hy, he⟩ := h₁ x hx
        exact ⟨m, Subgroup.mem_sup_left hm, y, hy, he⟩
      · obtain ⟨m, hm, y, hy, he⟩ := h₂ x hx
        exact ⟨m, Subgroup.mem_sup_right hm, y, hy, he⟩
    | one => exact ⟨1, W.one_mem, 1, Y.one_mem, by simp⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨w₁, hw₁, y₁, hy₁, rfl⟩ := iha
      obtain ⟨w₂, hw₂, y₂, hy₂, rfl⟩ := ihb
      obtain ⟨w', hw', y', hy', he⟩ := key w₂ hw₂ y₁ hy₁
      refine ⟨w₁ * w', W.mul_mem hw₁ hw', y' * y₂, Y.mul_mem hy' hy₂, ?_⟩
      calc w₁ * y₁ * (w₂ * y₂) = w₁ * (y₁ * w₂) * y₂ := by group
        _ = w₁ * (w' * y') * y₂ := by rw [he]
        _ = w₁ * w' * (y' * y₂) := by group
    | inv a _ ih =>
      obtain ⟨w, hw, y, hy, rfl⟩ := ih
      obtain ⟨w', hw', y', hy', he⟩ := key w⁻¹ (W.inv_mem hw) y⁻¹ (Y.inv_mem hy)
      exact ⟨w', hw', y', hy', by rw [mul_inv_rev, he]⟩
  set V := ⨆ d : (H₁ ⊔ H₂ : Subgroup G), U.map (MulAut.conj (d : G)).toMonoidHom with hV
  have hVM : V ≤ M := by
    refine iSup_le fun d => ?_
    obtain ⟨w, hw, y, hy, hd⟩ := hD d d.2
    rintro _ ⟨u, hu, rfl⟩
    have hyu : y * u * y⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hUH hy.1) u).mp hu
    have : (MulAut.conj (d : G)).toMonoidHom u = w * (y * u * y⁻¹) * w⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hd]; group
    rw [this]
    exact M.mul_mem (M.mul_mem (hWM hw) (hUM hyu)) (M.inv_mem (hWM hw))
  have hUV : U ≤ V := by
    refine le_trans ?_ (le_iSup (fun d : (H₁ ⊔ H₂ : Subgroup G) =>
      U.map (MulAut.conj (d : G)).toMonoidHom) 1)
    intro u hu
    exact ⟨u, hu, by simp⟩
  have hDV : H₁ ⊔ H₂ ≤ Subgroup.normalizer (V : Set G) := by
    intro e he
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    refine Subgroup.iSup_induction (fun d : (H₁ ⊔ H₂ : Subgroup G) =>
      U.map (MulAut.conj (d : G)).toMonoidHom) (C := fun x => e * x * e⁻¹ ∈ V) hx ?_ ?_ ?_
    · intro d x hx
      obtain ⟨u, hu, rfl⟩ := hx
      have hmem : (MulAut.conj (((⟨e, he⟩ : (H₁ ⊔ H₂ : Subgroup G)) * d : _) : G)).toMonoidHom u ∈
          U.map (MulAut.conj (((⟨e, he⟩ : (H₁ ⊔ H₂ : Subgroup G)) * d : _) : G)).toMonoidHom :=
        ⟨u, hu, rfl⟩
      have hV' := le_iSup (fun d : (H₁ ⊔ H₂ : Subgroup G) =>
        U.map (MulAut.conj (d : G)).toMonoidHom) (⟨e, he⟩ * d) hmem
      rw [hV]
      simpa [mul_assoc] using hV'
    · simp
    · intro a b ha hb
      have : e * (a * b) * e⁻¹ = (e * a * e⁻¹) * (e * b * e⁻¹) := by group
      rw [this]; exact V.mul_mem ha hb
  have hOV : pCoreOf 2 M ≤ pCoreOf 2 V := by
    refine normal_pSubgroup_le_pCoreOf 2 (hOU.trans hUV) ?_
      (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 M)
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (hOU.trans hUV)).mpr ?_
    exact hVM.trans (subgroup_normalizes_pCoreOf 2 M)
  have hT1 : pCoreOf 2 V ≠ ⊥ := fun h => twoLocal_pCoreOf_ne_bot hM (le_bot_iff.mp (h ▸ hOV))
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 V : Set G)) :=
    ⟨pCoreOf 2 V, hT1, CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 V, rfl⟩
  have hDN : H₁ ⊔ H₂ ≤ Subgroup.normalizer (pCoreOf 2 V : Set G) :=
    hDV.trans (normalizer_le_normalizer_characteristic (pCore 2 V)
      (CFSG.PreuniquenessRankFour.Helpers.pCore_characteristic (G := V) 2))
  have he₁ := hH₁.2 _ hloc (le_sup_left.trans hDN)
  have he₂ := hH₂.2 _ hloc (le_sup_right.trans hDN)
  rw [← he₁, he₂]

theorem absorbs_of_factor {p : ℕ} {M H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hM : IsTwoLocal M)
    (hH : GLBIsMaxTwoLocal H) (hOH : pCoreOf 2 M ≤ pCoreOf 2 H) (hHM : pCoreOf 2 H ≤ M)
    (hOM : (primeComplementCore (G := H) p).map H.subtype ≤ M)
    (hHfac : ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ k : H, QuotientGroup.mk' _ k ∈ K ∧ x = m * k)
    (hfac : ∀ Q N : Subgroup G, IsAGLQ p M Q → Q ≤ H → GLBIsMaxTwoLocal N → ¬ N ≤ M → Q ≤ N →
      AGLCovers p H N K → ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y) :
    AGLAbsorbs p M H K := by
  intro Q N hQ hQH hN hNM hQN hcov
  obtain ⟨N', hNN', hN'⟩ := exists_maximal_twoLocal hN
  have hN'M : ¬ N' ≤ M := fun h => hNM (hNN'.trans h)
  have hcov' : AGLCovers p H N' K :=
    hcov.trans (Subgroup.map_mono fun x hx => ⟨hx.1, hNN' hx.2⟩)
  have h₁ : ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ y ∈ H ⊓ N', x = m * y := by
    intro x hx
    obtain ⟨m, hm, k, hk, rfl⟩ := hHfac x hx
    obtain ⟨n, hn, hnk⟩ := hcov' hk
    have ho : n⁻¹ * k ∈ primeComplementCore (G := H) p := by
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' (primeComplementCore (G := H) p) (n⁻¹ * k) = 1
      rw [map_mul, map_inv, hnk, inv_mul_cancel]
    set o := n⁻¹ * k with hodef
    have hoM : (o : G) ∈ M := hOM ⟨o, ho, rfl⟩
    have hnoM : ((n * o * n⁻¹ : H) : G) ∈ M := by
      have : n * o * n⁻¹ ∈ primeComplementCore (G := H) p :=
        (primeComplementCore_normal p).conj_mem o ho n
      exact hOM ⟨_, this, rfl⟩
    refine ⟨m * ((n * o * n⁻¹ : H) : G), ⟨H.mul_mem hm.1 (n * o * n⁻¹).2, M.mul_mem hm.2 hnoM⟩,
      (n : G), Subgroup.mem_subgroupOf.mp hn, ?_⟩
    have hk : k = n * o := by rw [hodef]; group
    rw [hk]; push_cast; group
  exact le_of_le_of_eq hNN' (eq_of_factor hM hH hN' (subgroup_normalizes_pCoreOf 2 H) hHM hOH
    h₁ (hfac Q N' hQ hQH hN' hN'M (hQN.trans hNN') hcov')).symm

@[expose] def AGLCompetitorFactor (p : ℕ) (M H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ∀ Q N : Subgroup G, IsAGLQ p M Q → Q ≤ H → GLBIsMaxTwoLocal N → ¬ N ≤ M → Q ≤ N →
    AGLCovers p H N K → ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
