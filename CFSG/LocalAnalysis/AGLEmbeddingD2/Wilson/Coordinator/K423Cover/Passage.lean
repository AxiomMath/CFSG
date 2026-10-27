module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res5ProofTools
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers
public import CFSG.RankThree.PartTwo.Sec4.Item422Proof
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Cover423.Defs
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.PerfectAut
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4
open Subgroup

section ZQuot

variable (K : Type*) [Group K]

theorem map_center_mulAut (σ : MulAut K) : (center K).map σ.toMonoidHom = center K :=
  (Subgroup.characteristic_iff_map_eq.mp inferInstance) σ

@[expose] noncomputable def zQuot : MulAut K →* MulAut (K ⧸ center K) where
  toFun σ := QuotientGroup.congr (center K) (center K) σ (map_center_mulAut K σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

variable {K}

theorem zQuot_mk (σ : MulAut K) (k : K) :
    zQuot K σ (k : K ⧸ center K) = ((σ k : K) : K ⧸ center K) := rfl

theorem zQuot_conj (k : K) : zQuot K (MulAut.conj k) = MulAut.conj (k : K ⧸ center K) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x => rfl

theorem zQuot_injective (hK : Group.IsPerfect K) : Function.Injective (zQuot K) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine Proving.eq_one_of_isPerfect_of_mul_inv_mem_center hK σ fun k => ?_
  have h := congrArg (fun τ : MulAut (K ⧸ center K) => τ (k : K ⧸ center K)) hσ
  simp only [zQuot_mk, MulAut.one_apply] at h
  rw [QuotientGroup.eq] at h
  have hz : k⁻¹ * σ k ∈ center K := by
    have := inv_mem h
    rwa [mul_inv_rev, inv_inv] at this
  have hc := Subgroup.mem_center_iff.mp hz k
  have heq : σ k * k⁻¹ = k⁻¹ * σ k :=
    calc σ k * k⁻¹ = (k * (k⁻¹ * σ k)) * k⁻¹ := by group
      _ = (k⁻¹ * σ k * k) * k⁻¹ := by rw [hc]
      _ = k⁻¹ * σ k := by group
  rw [heq]
  exact hz

theorem center_quot_eq_bot (hs : IsSimpleGroup (K ⧸ center K))
    (hnc : ∃ a b : K ⧸ center K, a * b ≠ b * a) : center (K ⧸ center K) = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (K ⧸ center K)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hb : b ∈ center (K ⧸ center K) := h ▸ mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

end ZQuot

theorem isElemAbelian_of_map {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {D : Subgroup G} (h : CFSG.Assembly.IsElemAbelian 3 (D.map f)) :
    CFSG.Assembly.IsElemAbelian 3 D := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · change f ((a : G) * b) = f ((b : G) * a)
    rw [map_mul, map_mul]
    exact Res423Two.comm_of_isElemAbelian h _ ⟨a, a.2, rfl⟩ _ ⟨b, b.2, rfl⟩
  · rw [map_pow, map_one]
    exact h.2 (f x) ⟨x, hx, rfl⟩

section AutIn

variable {H : Type} [Group H] [Finite H] {L : Subgroup H} [L.Normal] {A : Subgroup H} {c : H}

omit [Finite H] in
theorem le_normalizer_of_normal' (B : Subgroup H) : B ≤ normalizer (L : Set H) := by
  intro b _
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => ‹L.Normal›.conj_mem x hx b, fun hx => ?_⟩
  have := ‹L.Normal›.conj_mem _ hx b⁻¹
  simpa [mul_assoc] using this

omit [Finite H] in
theorem autIn_facts (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hc3 : orderOf c = 3) (hAc : A ⊓ centralizer (L : Set H) = zpowers c) :
    CFSG.Assembly.IsElemAbelian 3 (autIn A L) ∧ Nat.card (autIn A L) = 9 := by
  refine ⟨Item422Proof.isElemAbelian_autIn hA, ?_⟩
  have h := Item422Proof.card_autIn_mul_card_inf (le_normalizer_of_normal' (L := L) A)
  rw [hAc, Nat.card_zpowers, hc3, hA27] at h
  omega

theorem false_of_alphaNine (hLq : IsQuasisimple L) (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hc3 : orderOf c = 3)
    (hAc : A ⊓ centralizer (L : Set H) = zpowers c)
    (hinn : autIn A L ≤ (MulAut.conj : L →* MulAut L).range)
    {Y : Subgroup (MulAut L)} (hY : (MulAut.conj : L →* MulAut L).range ≤ Y)
    (hα : thetaAlpha 3 ((autIn A L).subgroupOf Y) ≠ ⊥)
    {S : Type} [Group S] (e : L ⧸ center L ≃* S)
    (hS : Census.Karpilovsky.Coordinator.Cover423.AlphaNine S) : False := by
  obtain ⟨hBel, hB9⟩ := autIn_facts hA hA27 hc3 hAc
  set B := autIn A L with hB
  set ρ := zQuot L with hρ
  have hρi : Function.Injective ρ := zQuot_injective hLq.1
  set π := QuotientGroup.mk' (center L) with hπ
  set D : Subgroup (L ⧸ center L) := (B.comap (MulAut.conj : L →* MulAut L)).map π with hD
  have hZ : center (L ⧸ center L) = ⊥ := center_quot_eq_bot hLq.2.1 hLq.2.2
  have hci : Function.Injective (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)) :=
    Res423Two.conj_injective_of_center hZ
  have hcomp : (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).comp π =
      ρ.comp (MulAut.conj : L →* MulAut L) := by
    refine MonoidHom.ext fun l => ?_
    exact (zQuot_conj l).symm
  have hDB : D.map (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)) = B.map ρ := by
    rw [hD, Subgroup.map_map, hcomp, ← Subgroup.map_map, Subgroup.map_comap_eq,
      inf_eq_right.mpr hinn]
  have hD9 : Nat.card D = 9 := by
    rw [← Subgroup.card_map_of_injective hci, hDB, Subgroup.card_map_of_injective hρi, hB9]
  have hDel : CFSG.Assembly.IsElemAbelian 3 D := by
    refine isElemAbelian_of_map hci ?_
    rw [hDB]
    exact Res423Two.isElemAbelian_map' ρ hBel
  have hα0 : Res423Two.AlphaVanishes (L ⧸ center L) D := by
    refine Res423Two.alphaVanishes_of_mulEquiv e (hS _ (Res423Two.isElemAbelian_map' _ hDel) ?_)
    rw [Subgroup.card_map_of_injective e.injective, hD9]
  have hY' : (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range ≤ Y.map ρ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨MulAut.conj l, hY ⟨l, rfl⟩, zQuot_conj l⟩
  have h1 := hα0 (Y.map ρ) hY'
  rw [hDB] at h1
  exact hα (Res423Five.thetaAlpha_subgroupOf_eq_bot_of_map ρ hρi B Y h1)

theorem map_center_eq_zpowers (hZ3 : Nat.card (center L) = 3)
    (hAm : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hc3 : orderOf c = 3) (hAc : A ⊓ centralizer (L : Set H) = zpowers c) :
    (center L).map L.subtype = zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := (center L).map L.subtype with hZdef
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Subgroup.card_map_of_injective L.subtype_injective, hZ3]
  obtain ⟨z₀, hz₀Z, hz₀1⟩ : ∃ z₀ ∈ Z, z₀ ≠ 1 := by
    by_contra hcon
    have hbot : Z = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [mem_bot]
      by_contra hz1
      exact hcon ⟨z, hz, hz1⟩
    rw [hbot, card_bot] at hZcard
    norm_num at hZcard
  have hz₀3 : z₀ ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := Z) (x := ⟨z₀, hz₀Z⟩)
    rw [hZcard] at h1
    simpa using congrArg Subtype.val h1
  have hz₀o : orderOf z₀ = 3 := orderOf_eq_prime hz₀3 hz₀1
  have hZeq : Z = zpowers z₀ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz₀Z) ?_
    rw [hZcard, Nat.card_zpowers, hz₀o]
  have hZnorm : ∀ a ∈ A, ∀ z ∈ Z, a * z * a⁻¹ ∈ Z := by
    intro a _ z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hmem : a * (w : H) * a⁻¹ ∈ L := ‹L.Normal›.conj_mem _ w.2 a
    rw [SetLike.mem_coe] at hw
    refine ⟨⟨_, hmem⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hy : a⁻¹ * (y : H) * a ∈ L := by
      have := ‹L.Normal›.conj_mem _ y.2 a⁻¹
      simpa [mul_assoc] using this
    have hwy := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨_, hy⟩)
    simp only [Subgroup.coe_mul] at hwy
    calc (y : H) * (a * w * a⁻¹) = a * ((a⁻¹ * y * a) * w) * a⁻¹ := by group
      _ = a * (w * (a⁻¹ * y * a)) * a⁻¹ := by rw [hwy]
      _ = a * w * a⁻¹ * y := by group
  have hcomm : ∀ a ∈ A, a * z₀ = z₀ * a := by
    intro a ha
    have hw := hZnorm a ha z₀ hz₀Z
    rw [hZeq] at hw
    have hne : a * z₀ * a⁻¹ ≠ 1 := by
      intro h
      apply hz₀1
      have : z₀ = a⁻¹ * (a * z₀ * a⁻¹) * a := by group
      rw [this, h]
      group
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, hz₀o] at hw
    simp only [Finset.mem_image, Finset.mem_range] at hw
    obtain ⟨k, hk, hkw⟩ := hw
    interval_cases k
    · exact absurd (by rw [← hkw, pow_zero]) hne
    · rw [pow_one] at hkw
      calc a * z₀ = a * z₀ * a⁻¹ * a := by group
        _ = z₀ * a := by rw [← hkw]
    · exfalso
      have ha3 : a ^ 3 = 1 := hAm.prop.2 a ha
      have hsq : a * z₀ ^ 2 * a⁻¹ = z₀ := by
        have : a * z₀ ^ 2 * a⁻¹ = (a * z₀ * a⁻¹) ^ 2 := conj_pow.symm
        rw [this, ← hkw, ← pow_mul]
        rw [show 2 * 2 = 3 + 1 by norm_num, pow_succ, hz₀3, one_mul]
      have ha3' : a * a * a = 1 := by rw [← pow_three']; exact ha3
      have h3 : (a * a * a) * z₀ * (a * a * a)⁻¹ = z₀ ^ 2 := by
        calc (a * a * a) * z₀ * (a * a * a)⁻¹ = a * (a * (a * z₀ * a⁻¹) * a⁻¹) * a⁻¹ := by
              group
          _ = a * (a * z₀ ^ 2 * a⁻¹) * a⁻¹ := by rw [← hkw]
          _ = a * z₀ * a⁻¹ := by rw [hsq]
          _ = z₀ ^ 2 := hkw.symm
      rw [ha3', one_mul, inv_one, mul_one] at h3
      apply hz₀1
      calc z₀ = z₀ ^ 2 * z₀⁻¹ := by group
        _ = z₀ * z₀⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel z₀
  have hz₀A : z₀ ∈ A := by
    by_contra hz
    obtain ⟨hE, hEcard⟩ := Sec5.isElemAbelian_sup_zpowers hAm.prop hz hz₀3
      (fun a ha => hcomm a ha)
    have hle := Subgroup.card_le_of_le (hAm.2 hE le_sup_left)
    rw [hEcard] at hle
    have hpos : 0 < Nat.card A := Nat.card_pos
    omega
  have hz₀C : z₀ ∈ centralizer (L : Set H) := by
    obtain ⟨w, hw, hwz⟩ := hz₀Z
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [← hwz]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨x, hx⟩)
  have hz₀c : z₀ ∈ zpowers c := hAc ▸ ⟨hz₀A, hz₀C⟩
  rw [hZeq]
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz₀c) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hz₀o, hc3]

end AutIn

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover
