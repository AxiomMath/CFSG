module

public import CFSG.GroupTheory.QuasisimpleCenterDivisibility
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDOrthGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SK

open scoped commutatorElement

@[expose] def SkGood (p : ℕ) (H : Type*) [Group H] : Prop :=
  CFSG.IsQuasisimple ↥(commutator H) ∧
    (∀ z ∈ commutator H, (∀ l ∈ commutator H, z * l = l * z) → ∀ n : ℕ, z ^ 2 ^ n = 1 → z = 1) ∧
    (p ∣ Nat.card ↥(commutator H) ∨ ∀ w : H, w ^ p = 1 → w ∈ commutator H)

@[expose] def SkBad (p : ℕ) (H : Type*) [Group H] : Prop :=
  ∀ u v : H, u ^ p = 1 → u * v = v * u

section Transfer

variable {H H' : Type*} [Group H] [Group H']

theorem sk_map_commutator (e : H ≃* H') : (commutator H).map e.toMonoidHom = commutator H' := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 e.surjective]

theorem sk_mem_commutator_iff (e : H ≃* H') (w : H) : e w ∈ commutator H' ↔ w ∈ commutator H := by
  rw [← sk_map_commutator e, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem skGood_of_mulEquiv {p : ℕ} (e : H ≃* H') (h : SkGood p H') : SkGood p H := by
  obtain ⟨hq, hz, hp⟩ := h
  let ec : ↥(commutator H) ≃* ↥(commutator H') :=
    (e.subgroupMap (commutator H)).trans (MulEquiv.subgroupCongr (sk_map_commutator e))
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv ec.symm hq, fun z hzc hc n hzn => ?_, ?_⟩
  · have h1 : e z ∈ commutator H' := (sk_mem_commutator_iff e z).2 hzc
    have h2 : e z = 1 := by
      refine hz (e z) h1 (fun l hl => ?_) n (by rw [← map_pow, hzn, map_one])
      have hl' : e.symm l ∈ commutator H := by
        rw [← sk_mem_commutator_iff e, MulEquiv.apply_symm_apply]
        exact hl
      have h3 := congrArg e (hc (e.symm l) hl')
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    exact e.injective (by rw [h2, map_one])
  · rcases hp with hp | hp
    · left
      rw [Nat.card_congr ec.toEquiv]
      exact hp
    · right
      intro w hw
      exact (sk_mem_commutator_iff e w).1 (hp (e w) (by rw [← map_pow, hw, map_one]))

theorem skBad_of_mulEquiv {p : ℕ} (e : H ≃* H') (h : SkBad p H') : SkBad p H := fun u v hu =>
  e.injective (by
    rw [map_mul, map_mul]
    exact h (e u) (e v) (by rw [← map_pow, hu, map_one]))

end Transfer

section Select

variable {G : Type*} [Group G]

theorem sk_commutator_le_self (A : Subgroup G) : ⁅A, A⁆ ≤ A :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)

theorem sk_conj_mem_commutator {A : Subgroup G} {c : G} (hc : ∀ a ∈ A, c * a * c⁻¹ ∈ A) {w : G}
    (hw : w ∈ ⁅A, A⁆) : c * w * c⁻¹ ∈ ⁅A, A⁆ := by
  have hle : ⁅A, A⁆ ≤ (⁅A, A⁆).comap (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha a' ha'
    rw [Subgroup.mem_comap]
    change MulAut.conj c ⁅a, a'⁆ ∈ ⁅A, A⁆
    rw [map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply]
    exact Subgroup.commutator_mem_commutator (hc a ha) (hc a' ha')
  have h1 := hle hw
  rw [Subgroup.mem_comap] at h1
  exact h1

theorem sk_coe_mem_commutator_iff (A : Subgroup G) (a : ↥A) :
    (a : G) ∈ ⁅A, A⁆ ↔ a ∈ commutator ↥A := by
  rw [← Subgroup.map_subtype_commutator A]
  exact Subgroup.mem_map_iff_mem A.subtype_injective

@[expose] noncomputable def skCommEquiv (A : Subgroup G) : ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
  ((commutator ↥A).equivMapOfInjective A.subtype A.subtype_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))

theorem sk_select_of_blocks [Finite G] {ι : Type*} [Finite ι] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (A : ι → Subgroup G) (hpair : ∀ i j, i ≠ j → ∀ u ∈ A i, ∀ v ∈ A j, Commute u v)
    (hind : iSupIndep A) (C : Subgroup G) (hC : (⨆ i, A i) = C)
    (hgb : ∀ i, SkGood p ↥(A i) ∨ SkBad p ↥(A i))
    (B Y : Subgroup G) (hBC : B ≤ C) (hYC : Y ≤ C) (hBp : ∀ b ∈ B, b ^ p = 1)
    (hY2 : ∀ y ∈ Y, ∃ n : ℕ, y ^ 2 ^ n = 1) (hYB : ∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y)
    (hne : ⁅B, Y⁆ ≠ ⊥) :
    ∃ J : Subgroup G, CFSG.Open.IsComponentOf J C ∧ p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧
      ⁅⁅B, Y⁆, J⁆ ≠ ⊥ ∧ ⁅B, Y⁆ ≤ J ⊔ (C ⊓ Subgroup.centralizer (J : Set G)) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hpw : Pairwise fun i j : ι => ∀ x y : G, x ∈ A i → y ∈ A j → Commute x y :=
    fun i j hij x y hx hy => hpair i j hij x hx y hy
  set Φ : ((i : ι) → ↥(A i)) →* G := Subgroup.noncommPiCoprod hpw with hΦ
  have hΦinj : Function.Injective Φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hΦr : Φ.range = C := by rw [hΦ, Subgroup.noncommPiCoprod_range, hC]
  have hdec : ∀ c ∈ C, ∃ f, Φ f = c := fun c hc => by
    rw [← hΦr] at hc
    exact hc
  have hpow : ∀ f, Φ f ^ p = 1 → ∀ i, f i ^ p = 1 := fun f hf i => by
    have h1 : f ^ p = 1 := hΦinj (by rw [map_pow, hf, map_one])
    have h2 := congrFun h1 i
    rwa [Pi.pow_apply] at h2
  have hconj : ∀ (f : (i : ι) → ↥(A i)) (i : ι), ∀ l ∈ A i,
      Φ f * l * (Φ f)⁻¹ = (f i : G) * l * (f i : G)⁻¹ := by
    intro f i l hl
    have hl' : Φ (Pi.mulSingle i ⟨l, hl⟩) = l := Subgroup.noncommPiCoprod_mulSingle i ⟨l, hl⟩
    have hfun : f * Pi.mulSingle i ⟨l, hl⟩ * f⁻¹ = Pi.mulSingle i (f i * ⟨l, hl⟩ * (f i)⁻¹) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    calc Φ f * l * (Φ f)⁻¹ = Φ (f * Pi.mulSingle i ⟨l, hl⟩ * f⁻¹) := by
          rw [map_mul, map_mul, map_inv, hl']
      _ = (f i : G) * l * (f i : G)⁻¹ := by
          rw [hfun, Subgroup.noncommPiCoprod_mulSingle]
          rfl
  have hAC : ∀ i, A i ≤ C := fun i => hC ▸ le_iSup A i
  have hnorm : ∀ i, ∀ c ∈ C, ∀ a ∈ A i, c * a * c⁻¹ ∈ A i := by
    intro i c hc a ha
    have hN : C ≤ Subgroup.normalizer (A i : Set G) := by
      rw [← hC]
      refine iSup_le fun j => ?_
      by_cases hji : j = i
      · subst hji
        exact Subgroup.le_normalizer
      · refine le_trans (fun c' hc' => ?_) (Subgroup.centralizer_le_normalizer (A i : Set G))
        rw [Subgroup.mem_centralizer_iff]
        intro a' ha'
        exact (hpair i j (Ne.symm hji) a' ha' c' hc').eq
    exact (Subgroup.mem_normalizer_iff.1 (hN hc) a).1 ha
  set D : ι → Subgroup G := fun i => ⁅A i, A i⁆ with hD
  set J : ι → Subgroup G := fun i => if SkGood p ↥(A i) then D i else ⊥ with hJdef
  have hJg : ∀ i, SkGood p ↥(A i) → J i = D i := fun i h => if_pos h
  have hJb : ∀ i, ¬ SkGood p ↥(A i) → J i = ⊥ := fun i h => if_neg h
  have hDA : ∀ i, D i ≤ A i := fun i => sk_commutator_le_self (A i)
  have hJA : ∀ i, J i ≤ A i := by
    intro i
    by_cases hg : SkGood p ↥(A i)
    · rw [hJg i hg]
      exact hDA i
    · rw [hJb i hg]
      exact bot_le
  have hJC : ∀ i, J i ≤ C := fun i => (hJA i).trans (hAC i)
  have hcommJ : ∀ i j, i ≠ j → ∀ u ∈ J i, ∀ v ∈ J j, u * v = v * u := fun i j hij u hu v hv =>
    (hpair i j hij u (hJA i hu) v (hJA j hv)).eq
  have hq : ∀ i, J i = ⊥ ∨ CFSG.Open.IsComponentOf (J i) C := by
    intro i
    by_cases hg : SkGood p ↥(A i)
    · right
      rw [hJg i hg]
      have hDC : D i ≤ C := (hDA i).trans (hAC i)
      refine ⟨hDC, ?_, DX.open_of_native_dx (CFSG.LocalCores.isQuasisimple_of_mulEquiv (skCommEquiv (A i)) hg.1)⟩
      refine CFSG.Open.IsSubnormal.step hDC ?_ (CFSG.Open.IsSubnormal.refl C)
      rw [Subgroup.normal_subgroupOf_iff hDC]
      intro w c hw hc
      exact sk_conj_mem_commutator (hnorm i c hc) hw
    · left
      exact hJb i hg
  have hz : ∀ i, ∀ z ∈ J i, (∀ l ∈ J i, z * l = l * z) → ∀ n : ℕ, z ^ 2 ^ n = 1 → z = 1 := by
    intro i z hz hc n hzn
    by_cases hg : SkGood p ↥(A i)
    · rw [hJg i hg] at hz hc
      have hzA : z ∈ A i := hDA i hz
      have hz' : (⟨z, hzA⟩ : ↥(A i)) ∈ commutator ↥(A i) := (sk_coe_mem_commutator_iff (A i) _).1 hz
      have h1 := hg.2.1 ⟨z, hzA⟩ hz' (fun l hl => Subtype.ext (hc (l : G)
        ((sk_coe_mem_commutator_iff (A i) l).2 hl))) n (Subtype.ext (by simpa using hzn))
      exact congrArg Subtype.val h1
    · rw [hJb i hg] at hz
      exact Subgroup.mem_bot.1 hz
  have hinn : ∀ i, p ∣ Nat.card (↥(J i) ⧸ Subgroup.center ↥(J i)) ∨
      ∀ b ∈ B, ∃ c ∈ J i, ∀ l ∈ J i, b * l * b⁻¹ = c * l * c⁻¹ := by
    intro i
    by_cases hg : SkGood p ↥(A i)
    · rw [hJg i hg]
      rcases hg.2.2 with hpd | hpw'
      · left
        refine CFSG.dvd_card_quotient_center_of_quasisimple
          (CFSG.LocalCores.isQuasisimple_of_mulEquiv (skCommEquiv (A i)) hg.1) hp ?_
        rw [← Nat.card_congr (skCommEquiv (A i)).toEquiv]
        exact hpd
      · right
        intro b hb
        obtain ⟨f, rfl⟩ := hdec b (hBC hb)
        have hfp := hpow f (hBp _ hb) i
        refine ⟨(f i : G), (sk_coe_mem_commutator_iff (A i) (f i)).2 (hpw' (f i) hfp), fun l hl => ?_⟩
        exact hconj f i l (hDA i hl)
    · rw [hJb i hg]
      right
      intro b _
      refine ⟨1, Subgroup.one_mem _, fun l hl => ?_⟩
      rw [Subgroup.mem_bot.1 hl]
      simp
  have hR : ⁅B, Y⁆ ≤ ⨆ i, J i := by
    rw [Subgroup.commutator_le]
    intro b hb y hy
    obtain ⟨f, rfl⟩ := hdec b (hBC hb)
    obtain ⟨g, rfl⟩ := hdec y (hYC hy)
    rw [← map_commutatorElement, hΦ, Subgroup.noncommPiCoprod_apply]
    refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
    refine le_iSup J i ?_
    have hfg : ((⁅f, g⁆ i : ↥(A i)) : G) = ⁅(f i : G), (g i : G)⁆ := by
      simp [commutatorElement_def]
    rw [hfg]
    by_cases hgd : SkGood p ↥(A i)
    · rw [hJg i hgd]
      exact Subgroup.commutator_mem_commutator (f i).2 (g i).2
    · have hfp := hpow f (hBp _ hb) i
      have hbad : SkBad p ↥(A i) := (hgb i).resolve_left hgd
      have h1 : (f i : G) * (g i : G) = (g i : G) * (f i : G) := congrArg Subtype.val (hbad (f i) (g i) hfp)
      rw [commutatorElement_def, h1, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
  obtain ⟨i, hi1, hi2, hi3, hi4⟩ := SD.sdo_select_component p hp hp2 J C B Y hJC hcommJ hq hz hBp hY2 hYB
    hR hne hinn
  exact ⟨J i, hi1, hi2, hi3, hi4⟩

end Select

end CFSG.LocalAnalysis.GLTheoremA.T263.SK

end
