module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.GroupTheory.CoprimeSection

open scoped commutatorElement

private theorem card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G]
    {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 : A.relIndex (B ⊔ A) * Nat.card A = Nat.card ↥(B ⊔ A) := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := B ⊔ A)
    rwa [inf_eq_left.mpr le_sup_right] at h
  have h2 : A.relIndex B * Nat.card ↥(A ⊓ B) = Nat.card B :=
    Subgroup.relIndex_mul_card (H := A) (K := B)
  have h3 : A.relIndex (B ⊔ A) = A.relIndex B := by
    letI : (A.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hB
    letI : (A.subgroupOf (B ⊔ A)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hB
    exact (Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient B A hB).toEquiv).symm
  calc
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)
        = Nat.card ↥(B ⊔ A) * Nat.card ↥(A ⊓ B) := by rw [sup_comm]
    _ = (A.relIndex (B ⊔ A) * Nat.card A) * Nat.card ↥(A ⊓ B) := by rw [h1]
    _ = (A.relIndex B * Nat.card A) * Nat.card ↥(A ⊓ B) := by rw [h3]
    _ = Nat.card A * (A.relIndex B * Nat.card ↥(A ⊓ B)) := by ac_rfl
    _ = Nat.card A * Nat.card B := by rw [h2]

private theorem fixedPointSubgroup_map_subtype_eq_inf_centralizer
    {G : Type*} [Group G] {D N : Subgroup G} [Subgroup.Normalizes D N] :
    (fixedPointSubgroup ↥D ↥N).map N.subtype =
      N ⊓ Subgroup.centralizer (D : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    intro d hd
    have hfix : (d : G) * (y : G) * (d : G)⁻¹ = (y : G) := by
      have h := congrArg Subtype.val (hy ⟨d, hd⟩)
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using h
    calc d * (y : G) = d * (y : G) * (d : G)⁻¹ * d := by simp [mul_assoc]
      _ = (y : G) * d := by rw [hfix]
  · rintro ⟨hxN, hxc⟩
    refine ⟨⟨x, hxN⟩, ?_, rfl⟩
    simp only [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro a
    apply Subtype.ext
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    have hac := hxc a a.property
    calc (a : G) * x * (a : G)⁻¹ = ((a : G) * x) * (a : G)⁻¹ := rfl
      _ = (x * (a : G)) * (a : G)⁻¹ := by rw [hac]
      _ = x := by simp [mul_assoc]

private theorem mem_fixedPointSubgroup_quotient_iff
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (H : Subgroup G) [H.Normal] [MulDistribMulAction A (G ⧸ H)]
    (hsmul : ∀ (a : A) (g : G), a • (g : G ⧸ H) = ((a • g : G) : G ⧸ H)) (x : G) :
    (x : G ⧸ H) ∈ fixedPointSubgroup A (G ⧸ H) ↔ ∀ a : A, a • x * x⁻¹ ∈ H := by
  simp only [fixedPointSubgroup, FixedPoints.mem_subgroup]
  constructor
  · intro h a
    have ha : (((a • x : G)) : G ⧸ H) = (x : G ⧸ H) := by
      rw [← hsmul]
      exact h a
    have hmem := (QuotientGroup.eq_iff_div_mem).1 ha
    simpa [div_eq_mul_inv] using hmem
  · intro h a
    have ha : (((a • x : G)) : G ⧸ H) = (x : G ⧸ H) := by
      rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
      simpa [mul_assoc] using h a
    rw [hsmul, ha]

theorem mem_centralizer_sup_iff
    {G : Type*} [Group G] [Finite G]
    {D N M : Subgroup G}
    (hMN : M ≤ N)
    (hMN_norm : N ≤ Subgroup.normalizer (M : Set G))
    (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hDM : D ≤ Subgroup.normalizer (M : Set G))
    (hcop : Nat.Coprime (Nat.card D) (Nat.card N))
    (hsolv : Group.IsSolvable ↥N)
    {n : G} (hn : n ∈ N) :
    (∀ d ∈ D, d * n * d⁻¹ * n⁻¹ ∈ M) ↔
      n ∈ (N ⊓ Subgroup.centralizer (D : Set G)) ⊔ M := by
  classical
  haveI : Subgroup.Normalizes D N := ⟨hDN⟩
  let MD : Subgroup ↥N := M.subgroupOf N
  have hMDnormal : MD.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMN).2 hMN_norm
  letI : MD.Normal := hMDnormal
  have hMDinv : IsInvariant ↥D ↥N MD := by
    refine ⟨fun a g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hDM a.property) (g : G))
  haveI : MulAction.QuotientAction (↥D) MD :=
    quotientAction_of_isInvariant (A := ↥D) (G := ↥N) MD hMDinv
  letI : MulDistribMulAction ↥D (↥N ⧸ MD) :=
    quotientMulDistribMulAction (A := ↥D) (G := ↥N) MD hMDinv
  have hquot : fixedPointSubgroup ↥D (↥N ⧸ MD) =
      (fixedPointSubgroup ↥D ↥N).map (QuotientGroup.mk' MD) :=
    fixedPointSubgroup_quotient_eq_map_of_solvable_coprime
      (G := ↥N) (A := ↥D) hsolv hcop MD hMDinv
  have hmapF := fixedPointSubgroup_map_subtype_eq_inf_centralizer (D := D) (N := N)
  have hA : ((⟨n, hn⟩ : ↥N) : ↥N ⧸ MD) ∈ fixedPointSubgroup ↥D (↥N ⧸ MD) ↔
      ∀ d ∈ D, d * n * d⁻¹ * n⁻¹ ∈ M := by
    have hsmul : ∀ (a : ↥D) (g : ↥N), a • (g : ↥N ⧸ MD) = (a • g : ↥N ⧸ MD) :=
      fun a g => MulAction.Quotient.smul_mk (H := MD) a g
    have h := mem_fixedPointSubgroup_quotient_iff (A := ↥D) (G := ↥N) MD hsmul
      (⟨n, hn⟩ : ↥N)
    simpa [Subtype.forall, MD, Subgroup.mem_subgroupOf, mul_assoc,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using h
  have hB : ((⟨n, hn⟩ : ↥N) : ↥N ⧸ MD) ∈
      (fixedPointSubgroup ↥D ↥N).map (QuotientGroup.mk' MD) ↔
      n ∈ (N ⊓ Subgroup.centralizer (D : Set G)) ⊔ M := by
    constructor
    · rintro ⟨f, hf, hqf⟩
      have hf_inf : (f : G) ∈ N ⊓ Subgroup.centralizer (D : Set G) := by
        rw [← hmapF]
        exact ⟨f, hf, rfl⟩
      have hmem : (f : G) * n⁻¹ ∈ M := by
        have h := (QuotientGroup.eq_iff_div_mem).1 hqf
        simpa [MD, Subgroup.mem_subgroupOf, div_eq_mul_inv] using h
      rw [show n = ((f : G) * n⁻¹)⁻¹ * (f : G) by simp [mul_assoc]]
      have hsup : ((f : G) * n⁻¹)⁻¹ * (f : G) ∈
          M ⊔ (N ⊓ Subgroup.centralizer (D : Set G)) :=
        Subgroup.mul_mem_sup (Subgroup.inv_mem _ hmem) hf_inf
      simpa [sup_comm] using hsup
    · intro hnmem
      have hCn : N ⊓ Subgroup.centralizer (D : Set G) ≤
          Subgroup.normalizer (M : Set G) := fun x hx => hMN_norm hx.1
      have hnmem' : n ∈ (↑((N ⊓ Subgroup.centralizer (D : Set G)) ⊔ M) : Set G) := hnmem
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ M hCn] at hnmem'
      rcases hnmem' with ⟨c, hc, m, hm, hcm⟩
      have hc' : c ∈ N ⊓ Subgroup.centralizer (D : Set G) := hc
      refine ⟨⟨c, hc'.1⟩, ?_, ?_⟩
      · simp only [fixedPointSubgroup, FixedPoints.mem_subgroup]
        intro a
        apply Subtype.ext
        rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        have hac := hc'.2 a a.property
        calc (a : G) * c * (a : G)⁻¹ = ((a : G) * c) * (a : G)⁻¹ := rfl
          _ = (c * (a : G)) * (a : G)⁻¹ := by rw [hac]
          _ = c := by simp [mul_assoc]
      · have hn_eq : (⟨n, hn⟩ : ↥N) = ⟨c, hc'.1⟩ * ⟨m, hMN hm⟩ := by
          apply Subtype.ext
          simp [hcm]
        change (QuotientGroup.mk' MD) ⟨c, hc'.1⟩ = (QuotientGroup.mk' MD) ⟨n, hn⟩
        rw [hn_eq, map_mul]
        have hqm : QuotientGroup.mk' MD ⟨m, hMN hm⟩ = 1 := by
          change ((⟨m, hMN hm⟩ : ↥N) : ↥N ⧸ MD) = 1
          rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          simpa using hm
        rw [hqm, mul_one]
  rw [← hquot] at hB
  exact hA.symm.trans hB

theorem card_centralizer_section
    {G : Type*} [Group G] [Finite G]
    {D N M : Subgroup G}
    (hMN : M ≤ N)
    (hMN_norm : N ≤ Subgroup.normalizer (M : Set G)) :
    Nat.card ↥((N ⊓ Subgroup.centralizer (D : Set G)) ⊔ M) *
        Nat.card ↥(M ⊓ Subgroup.centralizer (D : Set G)) =
      Nat.card ↥(N ⊓ Subgroup.centralizer (D : Set G)) * Nat.card M := by
  set C : Subgroup G := N ⊓ Subgroup.centralizer (D : Set G) with hCdef
  set CM : Subgroup G := M ⊓ Subgroup.centralizer (D : Set G) with hCMdef
  have hCnorm : C ≤ Subgroup.normalizer (M : Set G) := by
    intro x hx
    rw [hCdef] at hx
    exact hMN_norm hx.1
  have hCMeq : C ⊓ M = CM := by
    ext x
    simp only [hCdef, hCMdef, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hc⟩, hM⟩; exact ⟨hM, hc⟩
    · rintro ⟨hM, hc⟩; exact ⟨⟨hMN hM, hc⟩, hM⟩
  have h := card_sup_mul_card_inf_of_le_normalizer (A := M) (B := C) hCnorm
  have hsup : M ⊔ C = C ⊔ M := sup_comm ..
  have hinf : M ⊓ C = CM := by rw [inf_comm, hCMeq]
  rw [hsup, hinf] at h
  exact h.trans (mul_comm (Nat.card M) (Nat.card C))

theorem index_centralizer_mul
    {G : Type*} [Group G] [Finite G]
    {D N M : Subgroup G}
    (hMN : M ≤ N)
    (hMN_norm : N ≤ Subgroup.normalizer (M : Set G)) :
    (N ⊓ Subgroup.centralizer (D : Set G)).relIndex N =
      (M ⊓ Subgroup.centralizer (D : Set G)).relIndex M *
        ((N ⊓ Subgroup.centralizer (D : Set G)) ⊔ M).relIndex N := by
  set C : Subgroup G := N ⊓ Subgroup.centralizer (D : Set G) with hCdef
  set CM : Subgroup G := M ⊓ Subgroup.centralizer (D : Set G) with hCMdef
  have hCnorm : C ≤ Subgroup.normalizer (M : Set G) := by
    intro x hx
    rw [hCdef] at hx
    exact hMN_norm hx.1
  have hCMeq : C ⊓ M = CM := by
    ext x
    simp only [hCdef, hCMdef, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hc⟩, hM⟩; exact ⟨hM, hc⟩
    · rintro ⟨hM, hc⟩; exact ⟨⟨hMN hM, hc⟩, hM⟩
  have hCMle : CM ≤ M := by
    intro x hx
    rw [hCMdef] at hx
    exact hx.1
  have hAB : M.relIndex C * C.relIndex (C ⊔ M) = CM.relIndex (C ⊔ M) := by
    have h := Subgroup.relIndex_inf_mul_relIndex (H := M) (K := C) (L := C ⊔ M)
    rw [inf_eq_left.mpr le_sup_left, inf_comm, hCMeq] at h
    exact h
  have hBC : CM.relIndex (C ⊔ M) = CM.relIndex M * M.relIndex (C ⊔ M) :=
    (Subgroup.relIndex_mul_relIndex (H := CM) (K := M) (L := C ⊔ M)
      hCMle le_sup_right).symm
  have hMC : M.relIndex (C ⊔ M) = M.relIndex C := by
    letI : (M.subgroupOf C).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hCnorm
    letI : (M.subgroupOf (C ⊔ M)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hCnorm
    exact (Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient C M hCnorm).toEquiv).symm
  have hkey : C.relIndex (C ⊔ M) = CM.relIndex M := by
    have hnonzero : M.relIndex (C ⊔ M) ≠ 0 := by
      intro h0
      have h := Subgroup.relIndex_mul_card (H := M) (K := C ⊔ M)
      rw [inf_eq_left.mpr le_sup_right, h0, zero_mul] at h
      exact (Nat.card_pos (α := ↥(C ⊔ M))).ne' h.symm
    have heq : M.relIndex (C ⊔ M) * C.relIndex (C ⊔ M) =
        M.relIndex (C ⊔ M) * CM.relIndex M := by
      calc M.relIndex (C ⊔ M) * C.relIndex (C ⊔ M)
          = M.relIndex C * C.relIndex (C ⊔ M) := by rw [hMC]
        _ = CM.relIndex (C ⊔ M) := hAB
        _ = CM.relIndex M * M.relIndex (C ⊔ M) := hBC
        _ = M.relIndex (C ⊔ M) * CM.relIndex M := by rw [mul_comm]
    exact mul_left_cancel₀ hnonzero heq
  calc
    C.relIndex N = C.relIndex (C ⊔ M) * (C ⊔ M).relIndex N :=
      (Subgroup.relIndex_mul_relIndex (H := C) (K := C ⊔ M) (L := N)
        le_sup_left (sup_le inf_le_left hMN)).symm
    _ = CM.relIndex M * (C ⊔ M).relIndex N := by rw [hkey]

theorem commutator_eq_bot_of_two_step {G : Type*} [Group G]
    {D Y Y₁ : Subgroup G} (hperf : ⁅D, D⁆ = D)
    (h1 : ⁅Y, D⁆ ≤ Y₁) (h2 : ⁅Y₁, D⁆ = ⊥) : ⁅Y, D⁆ = ⊥ := by
  have hDY : ⁅⁅D, Y⁆, D⁆ = ⊥ := by
    have hle : ⁅⁅D, Y⁆, D⁆ ≤ ⁅Y₁, D⁆ := by
      rw [Subgroup.commutator_comm D Y]
      exact Subgroup.commutator_mono h1 le_rfl
    rw [h2] at hle
    exact le_bot_iff.mp hle
  have hYY : ⁅⁅Y, D⁆, D⁆ = ⊥ := by
    have hle : ⁅⁅Y, D⁆, D⁆ ≤ ⁅Y₁, D⁆ := Subgroup.commutator_mono h1 le_rfl
    rw [h2] at hle
    exact le_bot_iff.mp hle
  have hrot :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := D) (H₂ := D) (H₃ := Y) hDY hYY
  rw [hperf] at hrot
  rw [← Subgroup.commutator_comm]
  exact hrot

theorem commutator_eq_bot_of_series {G : Type*} [Group G]
    {D : Subgroup G} (hperf : ⁅D, D⁆ = D) (Y : ℕ → Subgroup G) (n : ℕ)
    (hstep : ∀ i < n, ⁅Y i, D⁆ ≤ Y (i + 1))
    (hn : Y n = ⊥) : ⁅Y 0, D⁆ = ⊥ := by
  have hbase : ⁅Y n, D⁆ = ⊥ := by rw [hn, Subgroup.commutator_bot_left]
  exact Nat.decreasingInduction (motive := fun i _ => ⁅Y i, D⁆ = ⊥)
    (fun k hk ih => commutator_eq_bot_of_two_step hperf (hstep k hk) ih)
    hbase (Nat.zero_le n)

end CFSG.GroupTheory.CoprimeSection

end
