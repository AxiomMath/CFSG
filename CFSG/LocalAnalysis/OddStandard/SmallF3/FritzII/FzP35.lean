module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Wreath

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

private theorem card_sup_of_commute {G : Type} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype hcomm) := by
    refine (MonoidHom.noncommCoprod_injective A.subtype B.subtype hcomm).2 ?_
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hd
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  calc Nat.card ↥(A ⊔ B) = Nat.card (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range := by
        rw [hrange]
    _ = Nat.card (↥A × ↥B) := (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

private theorem card_comap_of_surjective {G H : Type} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (K : Subgroup H) :
    Nat.card (K.comap f) = Nat.card f.ker * Nat.card K := by
  let φ : K.comap f →* K :=
    { toFun := fun x => ⟨f x, x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hcard := Subgroup.card_ker_mul_card_of_surjective hφ
  have hker : φ.ker = f.ker.subgroupOf (K.comap f) := by
    ext x
    simp [φ, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subtype.ext_iff]
  have hle : f.ker ≤ K.comap f := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact K.one_mem
  have hker_card : Nat.card φ.ker = Nat.card f.ker := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hker_card] at hcard
  exact hcard.symm

private theorem twoCore_commute_of_hyp {t : G} {L : Subgroup G} (h : Hyp G t L) :
    ∀ a ∈ twoCore t, ∀ b ∈ L, a * b = b * a := by
  intro a ha b hb
  have ha' : a ∈ Subgroup.centralizer (L : Set G) := by
    have hmem : a ∈ Subgroup.centralizer (L : Set G) ⊓ invCent t := by
      rw [h.centralizer_eq]
      exact ha
    exact (Subgroup.mem_inf.mp hmem).1
  exact (Subgroup.mem_centralizer_iff.mp ha' b hb).symm

private theorem card_ctxW_eq_32 {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    Nat.card (ctxW t x₁ x₂) = 32 := by
  have hbase_le_L : baseGrp x₁ x₂ ≤ L := by
    have h1 : baseGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
      rw [baseGrp, wreathGrp]
      exact Subgroup.closure_mono (by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        tauto)
    exact h1.trans (by rw [← h.inf_eq]; exact inf_le_right)
  have hPA : ∀ p ∈ twoCore t, ∀ a ∈ baseGrp x₁ x₂, p * a = a * p :=
    fun p hp a ha => twoCore_commute_of_hyp h.hyp p hp a (hbase_le_L ha)
  have hinf : twoCore t ⊓ baseGrp x₁ x₂ = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hxL : x ∈ twoCore t ⊓ L := ⟨hx.1, hbase_le_L hx.2⟩
    have h' := hxL
    rw [h.hyp.twoCore_inf, Subgroup.mem_bot] at h'
    simpa using h'
  have hbase_card : Nat.card (baseGrp x₁ x₂) = 16 := (WreathRel.baseGrp_eq h.wreath).2.2
  calc Nat.card (ctxW t x₁ x₂) = Nat.card ↥(twoCore t ⊔ baseGrp x₁ x₂) := rfl
    _ = Nat.card (twoCore t) * Nat.card (baseGrp x₁ x₂) := card_sup_of_commute hPA hinf
    _ = 2 * 16 := by rw [hK, hbase_card]
    _ = 32 := by norm_num

private theorem not_three_dvd_orderOf_of_isPGroup {H : Subgroup G} (hH : IsPGroup 2 H)
    {g : G} (hg : g ∈ H) : ¬ 3 ∣ orderOf g := by
  obtain ⟨n, hn⟩ := hH ⟨g, hg⟩
  have hn' : g ^ 2 ^ n = 1 := by
    have := congrArg (Subtype.val) hn
    simpa using this
  have hdvd : orderOf g ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hn'
  intro h3
  have h32 : 3 ∣ 2 ^ n := h3.trans hdvd
  have h32' : 3 ∣ 2 := (by norm_num : Nat.Prime 3).dvd_of_dvd_pow h32
  norm_num at h32'

private def fzD1 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

private def fzD2 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

private def fzV4 : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {x | x = 1 ∨ x = fzD1 ∨ x = fzD2 ∨ x = fzD1 * fzD2}
  one_mem' := by simp
  mul_mem' := by decide
  inv_mem' := by decide

private instance fzV4Decidable : DecidablePred (· ∈ fzV4) := fun x =>
  decidable_of_iff (x = 1 ∨ x = fzD1 ∨ x = fzD2 ∨ x = fzD1 * fzD2) (by simp [fzV4])

private theorem fzV4_card : Nat.card fzV4 = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem fzV4_normal : fzV4.Normal where
  conj_mem := by decide

private def fzV4' : Subgroup FzZ2xSigma4 :=
  (⊤ : Subgroup (Multiplicative (ZMod 2))).prod fzV4

private instance fzV4'Decidable : DecidablePred (· ∈ fzV4') := fun x =>
  decidable_of_iff (x.2 ∈ fzV4) (by simp [fzV4', Subgroup.mem_prod])

private theorem fzV4'_normal : fzV4'.Normal := by
  haveI : fzV4.Normal := fzV4_normal
  dsimp [fzV4']
  infer_instance

private theorem fzV4'_card : Nat.card fzV4' = 8 := by
  dsimp [fzV4']
  rw [Nat.card_congr (Subgroup.prodEquiv ⊤ fzV4).toEquiv, Nat.card_prod,
    Subgroup.card_top, Nat.card_eq_fintype_card, fzV4_card]
  norm_num [ZMod.card]

private theorem fzV4'_isPGroup : IsPGroup 2 fzV4' := by
  apply IsPGroup.of_card (n := 3)
  rw [fzV4'_card]
  norm_num

private theorem fzV4'_le_pCore : fzV4' ≤ CFSG.pCore 2 FzZ2xSigma4 :=
  le_sSup (show fzV4' ∈ {K : Subgroup FzZ2xSigma4 | K.Normal ∧ IsPGroup 2 K} from
    ⟨fzV4'_normal, fzV4'_isPGroup⟩)

private theorem card_FzZ2xSigma4 : Nat.card FzZ2xSigma4 = 48 := by
  rw [Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial, ZMod.card]

private theorem FzZ2xSigma4_pow_twelve (z : FzZ2xSigma4) : z ^ 12 = 1 := by
  have h : ∀ z : FzZ2xSigma4, z ^ 12 = 1 := by decide +kernel
  exact h z

private theorem three_dvd_orderOf_of_pow_twelve (z : FzZ2xSigma4) (h12 : z ^ 12 = 1)
    (h4 : z ^ 4 ≠ 1) : 3 ∣ orderOf z := by
  have hdvd : orderOf z ∣ 12 := orderOf_dvd_iff_pow_eq_one.mpr h12
  by_contra h3
  have hcop : Nat.Coprime (orderOf z) 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm
  have hdvd4 : orderOf z ∣ 4 := hcop.dvd_of_dvd_mul_right (m := 4) hdvd
  exact h4 (orderOf_dvd_iff_pow_eq_one.mp hdvd4)

private theorem fz_finite_check (g : FzZ2xSigma4) (hg : g ∉ fzV4') :
    (∃ h : FzZ2xSigma4, (g * (h * g * h⁻¹)) ^ 4 ≠ 1) ∨ g ^ 4 ≠ 1 := by
  revert g
  decide +kernel

private theorem pCore_le_fzV4' : CFSG.pCore 2 FzZ2xSigma4 ≤ fzV4' := by
  intro x hx
  by_contra hxV
  rcases fz_finite_check x hxV with ⟨h, hh⟩ | hx4
  · have hmem : x * (h * x * h⁻¹) ∈ CFSG.pCore 2 FzZ2xSigma4 :=
      (CFSG.pCore 2 FzZ2xSigma4).mul_mem hx
        ((CFSG.pCore_normal (p := 2) (G := FzZ2xSigma4)).conj_mem x hx h)
    have h3 : 3 ∣ orderOf (x * (h * x * h⁻¹)) :=
      three_dvd_orderOf_of_pow_twelve _ (FzZ2xSigma4_pow_twelve _) hh
    exact (not_three_dvd_orderOf_of_isPGroup
      (CFSG.pCore_isPGroup (p := 2) (G := FzZ2xSigma4)) hmem) h3
  · have h3 : 3 ∣ orderOf x :=
      three_dvd_orderOf_of_pow_twelve x (FzZ2xSigma4_pow_twelve x) hx4
    exact (not_three_dvd_orderOf_of_isPGroup
      (CFSG.pCore_isPGroup (p := 2) (G := FzZ2xSigma4)) hx) h3

private theorem card_pCore_FzZ2xSigma4 : Nat.card (CFSG.pCore 2 FzZ2xSigma4) = 8 := by
  have heq : CFSG.pCore 2 FzZ2xSigma4 = fzV4' := le_antisymm pCore_le_fzV4' fzV4'_le_pCore
  rw [heq, fzV4'_card]

theorem fz37R_of_35b (h : Fz35b) : Fz37R := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT
  obtain ⟨f, hf, hker⟩ := h G t L S x₁ x₂ lam rho tau hr4 hctx hK
  have hW_le_N2 : ctxW t x₁ x₂ ≤ fzN2 t x₁ x₂ := Subgroup.le_normalizer
  have hWker : Nat.card f.ker = 32 := by
    rw [hker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_N2).toEquiv]
    exact card_ctxW_eq_32 hctx hK
  have hN2card : Nat.card ↥(fzN2 t x₁ x₂) = 2 ^ 9 * 3 := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective hf
    rw [hWker, card_FzZ2xSigma4] at h1
    rw [← h1]
    norm_num
  have hTcard : Nat.card T₂ = 2 ^ 9 := by
    have hrel : T₂.relIndex (fzN2 t x₁ x₂) * Nat.card T₂ = Nat.card (fzN2 t x₁ x₂) := by
      have h := Subgroup.relIndex_mul_card (H := T₂) (K := fzN2 t x₁ x₂)
      rwa [inf_eq_left.mpr hT.le_N2] at h
    have hodd : Odd (T₂.relIndex (fzN2 t x₁ x₂)) :=
      Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hT.odd_relIndex)
    have hcop_r : Nat.Coprime 2 (T₂.relIndex (fzN2 t x₁ x₂)) :=
      Nat.coprime_two_left.mpr hodd
    obtain ⟨k, hk⟩ := hT.isPGroup.exists_card_eq
    have hR : T₂.relIndex (fzN2 t x₁ x₂) * 2 ^ k = 2 ^ 9 * 3 := by
      rw [← hk, hrel, hN2card]
    have hk_le : k ≤ 9 := by
      have hdvd : 2 ^ k ∣ 2 ^ 9 * 3 := by
        rw [← hR]
        exact dvd_mul_left _ _
      have hcop3 : Nat.Coprime (2 ^ k) 3 := (by decide : Nat.Coprime 2 3).pow_left k
      have hdvd' : 2 ^ k ∣ 2 ^ 9 := hcop3.dvd_of_dvd_mul_right hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd'
    have hk_ge : 9 ≤ k := by
      have hdvd : 2 ^ 9 ∣ 2 ^ k := by
        have hdvd' : 2 ^ 9 ∣ 2 ^ k * T₂.relIndex (fzN2 t x₁ x₂) := by
          rw [mul_comm, hR]
          exact dvd_mul_right _ _
        exact (hcop_r.pow_left 9).dvd_of_dvd_mul_right hdvd'
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
    rw [hk, le_antisymm hk_le hk_ge]
  have hcomap_card : Nat.card ((CFSG.pCore 2 FzZ2xSigma4).comap f) = 2 ^ 8 := by
    have h := card_comap_of_surjective f hf (CFSG.pCore 2 FzZ2xSigma4)
    rw [h, hWker, card_pCore_FzZ2xSigma4]
    norm_num
  have hC_eq : CFSG.pCore 2 ↥(fzN2 t x₁ x₂) = (CFSG.pCore 2 FzZ2xSigma4).comap f := by
    apply le_antisymm
    · rw [← Subgroup.map_le_iff_le_comap]
      refine le_sSup (show (CFSG.pCore 2 ↥(fzN2 t x₁ x₂)).map f ∈
          {K : Subgroup FzZ2xSigma4 | K.Normal ∧ IsPGroup 2 K} from
        ⟨(CFSG.pCore_normal (p := 2) (G := ↥(fzN2 t x₁ x₂))).map f hf,
          (CFSG.pCore_isPGroup (p := 2) (G := ↥(fzN2 t x₁ x₂))).map f⟩)
    · refine le_sSup (show (CFSG.pCore 2 FzZ2xSigma4).comap f ∈
          {K : Subgroup ↥(fzN2 t x₁ x₂) | K.Normal ∧ IsPGroup 2 K} from
        ⟨(CFSG.pCore_normal (p := 2) (G := FzZ2xSigma4)).comap f,
          IsPGroup.of_card (n := 8) hcomap_card⟩)
  have hRcard : Nat.card (fzR t x₁ x₂) = Nat.card (CFSG.pCore 2 ↥(fzN2 t x₁ x₂)) := by
    unfold fzR CFSG.Open.pCoreOf
    exact Subgroup.card_map_of_injective (K := CFSG.pCore 2 ↥(fzN2 t x₁ x₂))
      (f := (fzN2 t x₁ x₂).subtype) (fzN2 t x₁ x₂).subtype_injective
  constructor
  · rw [hRcard, hC_eq, hcomap_card]
  · exact hTcard

end CFSG.OddStandard.SmallF3.FritzII
