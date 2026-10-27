module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.AbstractGroup
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {X W : Type} [Group X] [Group W]

theorem block_image (C : Subgroup X) [C.Normal] (ρ : X →* W) (hρC : ρ.ker ≤ C) {L : Subgroup X}
    (hnC : ¬ L ≤ C) (hLb : Open.IsQuasisimple ↥(L.map ρ)) :
    ∃ φ : ↥(L.map ρ) →* ↥(L.map (QuotientGroup.mk' C)),
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center ↥(L.map ρ) := by
  let ψρ : ↥L →* ↥(L.map ρ) := ρ.subgroupMap L
  have hψρ : Function.Surjective ψρ := ρ.subgroupMap_surjective L
  let ψC : ↥L →* ↥(L.map (QuotientGroup.mk' C)) := (QuotientGroup.mk' C).subgroupMap L
  have hψC : Function.Surjective ψC := (QuotientGroup.mk' C).subgroupMap_surjective L
  have hker : ψρ.ker ≤ ψC.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : ρ (l : X) = 1 := congrArg Subtype.val hl
    apply Subtype.ext
    have : (l : X) ∈ C := hρC (by simpa [MonoidHom.mem_ker] using h1)
    exact (QuotientGroup.eq_one_iff (l : X)).mpr this
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(L.map ρ) →* ↥(L.map (QuotientGroup.mk' C)), φ.comp ψρ = ψC :=
    ⟨ψρ.liftOfRightInverse (Function.surjInv hψρ) (Function.rightInverse_surjInv hψρ) ⟨ψC, hker⟩,
      MonoidHom.liftOfRightInverse_comp _ _ _ ⟨ψC, hker⟩⟩
  have hφs : Function.Surjective φ := by
    have : Function.Surjective (φ.comp ψρ) := hφ ▸ hψC
    exact Function.Surjective.of_comp this
  refine ⟨φ, hφs, ?_⟩
  rcases quasisimple_normal_le_center_or_eq_top' hLb (MonoidHom.normal_ker φ) with h | h
  · exact h
  · exfalso
    apply hnC
    intro l hl
    have h1 : φ (ψρ ⟨l, hl⟩) = 1 := by
      have : ψρ ⟨l, hl⟩ ∈ φ.ker := by rw [h]; exact Subgroup.mem_top _
      exact this
    rw [← MonoidHom.comp_apply, hφ] at h1
    have h2 : (QuotientGroup.mk' C) l = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff l).mp h2

section Facts

variable {A B : Type} [Group A] [Finite A] [Group B] [Finite B]

theorem central_quotient_facts (hA : Open.IsQuasisimple A) (φ : A →* B)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center A) :
    Open.IsQuasisimple B ∧ Nat.card (Subgroup.center B) ∣ Nat.card (Subgroup.center A) ∧
      Nonempty (A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B) ∧
      (¬ 3 ∣ Nat.card (Subgroup.center A) →
        (3 ∣ Nat.card A ↔ 3 ∣ Nat.card B) ∧
          Open.pRank 3 (⊤ : Subgroup A) = Open.pRank 3 (⊤ : Subgroup B)) := by
  have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect (Group.IsPerfect.mk hA.1) φ hφ hker
  have hQ : Open.IsQuasisimple B :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.isQuasisimple_iff_cfsg B).mpr
      (CFSG.LocalCores.isQuasisimple_of_surjective
        ((CFSG.LocalAnalysis.RankThreeTheoremC.isQuasisimple_iff_cfsg A).mp hA) φ hφ hker)
  have hcenter : Subgroup.center B = (Subgroup.center A).map φ := by
    rw [← hcomap, Subgroup.map_comap_eq_self_of_surjective hφ]
  have hc : Subgroup.center A = ((QuotientGroup.mk' (Subgroup.center B)).comp φ).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  refine ⟨hQ, ?_, ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp hφ))⟩, fun h3 => ?_⟩
  · rw [hcenter]
    exact Subgroup.card_map_dvd _ _
  · have hk3 : ¬ 3 ∣ Nat.card φ.ker := fun hd =>
      h3 (hd.trans (Subgroup.card_dvd_of_le hker))
    refine ⟨⟨fun hd => ?_, fun hd => ?_⟩, ?_⟩
    · have hcard : Nat.card A = Nat.card φ.ker * Nat.card B := by
        have := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv] at this
        rw [this]; ring
      rw [hcard] at hd
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with h | h
      · exact absurd h hk3
      · exact h
    · exact hd.trans (Subgroup.card_dvd_of_surjective hφ)
    · exact CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel 3 Nat.prime_three φ hφ
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hk3)

end Facts

section Kernel

theorem mem_center_of_commutator_mem_center {A : Type*} [Group A] (hA : Open.IsQuasisimple A)
    {a : A} (h : ∀ l : A, ⁅a, l⁆ ∈ Subgroup.center A) : a ∈ Subgroup.center A := by
  obtain ⟨hp, hs⟩ := hA
  have := hs
  have hcenter : Subgroup.center (A ⧸ Subgroup.center A) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (A ⧸ Subgroup.center A))
      with h' | h'
    · exact h'
    · exfalso
      have hc : commutator A ≤ Subgroup.center A := by
        rw [commutator_def]
        refine (Subgroup.commutator_le).mpr fun x _ y _ => ?_
        rw [← QuotientGroup.eq_one_iff]
        change (QuotientGroup.mk' (Subgroup.center A)) ⁅x, y⁆ = 1
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        have hx : (QuotientGroup.mk' (Subgroup.center A)) x ∈
            Subgroup.center (A ⧸ Subgroup.center A) := by rw [h']; exact Subgroup.mem_top _
        exact ((Subgroup.mem_center_iff.mp hx) _).symm
      rw [hp, top_le_iff] at hc
      have : Nontrivial (A ⧸ Subgroup.center A) := IsSimpleGroup.toNontrivial
      obtain ⟨x, y, hxy⟩ := exists_pair_ne (A ⧸ Subgroup.center A)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      apply hxy
      have hx : x ∈ Subgroup.center A := hc ▸ Subgroup.mem_top x
      have hy : y ∈ Subgroup.center A := hc ▸ Subgroup.mem_top y
      rw [(QuotientGroup.eq_one_iff x).mpr hx, (QuotientGroup.eq_one_iff y).mpr hy]
  have : (QuotientGroup.mk' (Subgroup.center A)) a ∈ Subgroup.center (A ⧸ Subgroup.center A) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (QuotientGroup.mk' (Subgroup.center A)) ⁅a, l⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (h l)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rw [hcenter, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff a).mp this

end Kernel

section KernelSup

variable {W : Type*} [Group W]

theorem factor_mem_center {L₁ L₂ : Subgroup W} (h₁ : IsComponentOf L₁ ⊤)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    {N : Subgroup W} (hNn : ∀ x ∈ L₁ ⊔ L₂, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hN₁ : ¬ L₁ ≤ N)
    {a b : W} (ha : a ∈ L₁) (hb : b ∈ L₂) (hab : a * b ∈ N) :
    a ∈ L₁ ⊓ Subgroup.centralizer (L₁ : Set W) := by
  have hq : Open.IsQuasisimple ↥L₁ := h₁.2.2
  let N₁ : Subgroup ↥L₁ := (N ⊓ L₁).subgroupOf L₁
  have hN₁n : N₁.Normal := ⟨fun x hx g => by
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, L₁.mul_mem (L₁.mul_mem g.2 x.2) (L₁.inv_mem g.2)⟩
    exact hNn g (Subgroup.mem_sup_left g.2) x (Subgroup.mem_subgroupOf.mp hx).1⟩
  have hle : N₁ ≤ Subgroup.center ↥L₁ := by
    rcases CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.quasisimple_normal_le_center_or_eq_top'
      hq hN₁n with h | h
    · exact h
    · exfalso
      apply hN₁
      intro l hl
      have : (⟨l, hl⟩ : ↥L₁) ∈ N₁ := by rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
  have hcen : (⟨a, ha⟩ : ↥L₁) ∈ Subgroup.center ↥L₁ := by
    refine mem_center_of_commutator_mem_center hq fun l => ?_
    apply hle
    have hlW : (l : W) ∈ L₁ := l.2
    have e : b * (l : W) * b⁻¹ = l := by
      have := hcomm l hlW b hb
      rw [← this]; group
    have hm1 : ⁅a, (l : W)⁆ ∈ N := by
      have h1 : (l : W) * (a * b)⁻¹ * (l : W)⁻¹ ∈ N := by
        have := hNn l (Subgroup.mem_sup_left hlW) (a * b)⁻¹ (N.inv_mem hab)
        simpa [mul_assoc] using this
      have h2 := N.mul_mem hab h1
      have h3 : (a * b) * ((l : W) * (a * b)⁻¹ * (l : W)⁻¹) = ⁅a, (l : W)⁆ := by
        calc (a * b) * ((l : W) * (a * b)⁻¹ * (l : W)⁻¹)
            = a * (b * (l : W) * b⁻¹) * a⁻¹ * (l : W)⁻¹ := by group
          _ = ⁅a, (l : W)⁆ := by rw [e]; simp [commutatorElement_def]
      rwa [h3] at h2
    refine Subgroup.mem_subgroupOf.mpr ⟨hm1, ?_⟩
    simp only [commutatorElement_def]
    exact L₁.mul_mem (L₁.mul_mem (L₁.mul_mem ha hlW) (L₁.inv_mem ha)) (L₁.inv_mem hlW)
  refine ⟨ha, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  have := Subgroup.mem_center_iff.mp hcen ⟨g, hg⟩
  exact congrArg Subtype.val this

theorem normal_sup_le_center_mul {L₁ L₂ : Subgroup W} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    {N : Subgroup W} (hN : N ≤ L₁ ⊔ L₂) (hNn : ∀ x ∈ L₁ ⊔ L₂, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hN₁ : ¬ L₁ ≤ N) (hN₂ : ¬ L₂ ≤ N) :
    ∀ n ∈ N, ∃ a ∈ L₁ ⊓ Subgroup.centralizer (L₁ : Set W),
      ∃ b ∈ L₂ ⊓ Subgroup.centralizer (L₂ : Set W), n = a * b := by
  intro n hn
  have hle : L₁ ≤ Subgroup.normalizer (L₂ : Set W) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hcomm a ha b hb]
      simpa using hb
    · intro hb
      have h1 := hcomm a⁻¹ (L₁.inv_mem ha) _ hb
      have : b = a⁻¹ * (a * b * a⁻¹) * a := by group
      rw [this, h1]
      simpa using hb
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right L₁ L₂ hle
  have hn' : n ∈ (L₁ : Set W) * (L₂ : Set W) := by rw [← hset]; exact hN hn
  obtain ⟨a, ha, b, hb, rfl⟩ := hn'
  have hcomm' : ∀ x ∈ L₂, ∀ y ∈ L₁, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hsupC : ∀ x ∈ L₁ ⊔ L₂, ∀ n ∈ N, x * n * x⁻¹ ∈ N := hNn
  refine ⟨a, factor_mem_center h₁ hcomm hNn hN₁ ha hb hn, b, ?_, rfl⟩
  refine factor_mem_center (L₁ := L₂) (L₂ := L₁) h₂ hcomm' (N := N) (fun x hx n hn' => hNn x ?_ n hn') hN₂ hb ha ?_
  · rw [sup_comm]; exact hx
  · have : a * b = b * a := hcomm a ha b hb
    rw [← this]; exact hn

theorem eq_one_of_three_pow_of_normal_sup {L₁ L₂ : Subgroup W} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hZ₁ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L₁)) (hZ₂ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L₂))
    {N : Subgroup W} (hN : N ≤ L₁ ⊔ L₂) (hNn : ∀ x ∈ L₁ ⊔ L₂, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hN₁ : ¬ L₁ ≤ N) (hN₂ : ¬ L₂ ≤ N) {n : W} (hn : n ∈ N) (h3 : ∃ k : ℕ, n ^ 3 ^ k = 1) :
    n = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := normal_sup_le_center_mul h₁ h₂ hcomm hN hNn hN₁ hN₂ n hn
  obtain ⟨k, hk⟩ := h3
  have hab : a * b = b * a := hcomm a ha.1 b hb.1
  have hZa := Subgroup.orderOf_dvd_natCard (L₁ ⊓ Subgroup.centralizer (L₁ : Set W)) ha
  have hZb := Subgroup.orderOf_dvd_natCard (L₂ ⊓ Subgroup.centralizer (L₂ : Set W)) hb
  have hc1 : Nat.card ↥(L₁ ⊓ Subgroup.centralizer (L₁ : Set W)) = Nat.card (Subgroup.center ↥L₁) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.card_inf_centralizer_eq_card_center L₁
  have hc2 : Nat.card ↥(L₂ ⊓ Subgroup.centralizer (L₂ : Set W)) = Nat.card (Subgroup.center ↥L₂) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.card_inf_centralizer_eq_card_center L₂
  rw [hc1] at hZa
  rw [hc2] at hZb
  have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥L₁) * Nat.card (Subgroup.center ↥L₂)) 3 := by
    exact Nat.coprime_mul_iff_left.mpr
      ⟨((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ₁).symm,
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ₂).symm⟩
  have hpow : (a * b) ^ (Nat.card (Subgroup.center ↥L₁) * Nat.card (Subgroup.center ↥L₂)) = 1 := by
    rw [(show Commute a b from hab).mul_pow]
    have h1 : a ^ (Nat.card (Subgroup.center ↥L₁) * Nat.card (Subgroup.center ↥L₂)) = 1 := by
      obtain ⟨c, hc⟩ := hZa
      rw [hc, mul_assoc, pow_mul, pow_orderOf_eq_one, one_pow]
    have h2 : b ^ (Nat.card (Subgroup.center ↥L₁) * Nat.card (Subgroup.center ↥L₂)) = 1 := by
      obtain ⟨c, hc⟩ := hZb
      rw [hc, mul_comm (Nat.card (Subgroup.center ↥L₁)), mul_assoc, pow_mul,
        pow_orderOf_eq_one, one_pow]
    rw [h1, h2, one_mul]
  have hd1 : orderOf (a * b) ∣ Nat.card (Subgroup.center ↥L₁) * Nat.card (Subgroup.center ↥L₂) :=
    orderOf_dvd_of_pow_eq_one hpow
  have hd2 : orderOf (a * b) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hd := Nat.dvd_gcd hd1 hd2
  have : Nat.gcd (Nat.card (Subgroup.center ↥L₁) * Nat.card (Subgroup.center ↥L₂)) (3 ^ k) = 1 :=
    Nat.Coprime.pow_right k hcop
  rw [this] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

end KernelSup

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
