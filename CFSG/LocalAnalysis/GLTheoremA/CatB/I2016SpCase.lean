module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8c

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016Sp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.CatB CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8

@[expose] def QuotU4 {S : Type} [Group S] (I : Subgroup S) : Prop :=
  ∃ (T : Type) (_ : Group T) (f : ↥I →* T), Function.Surjective f ∧ Nat.card T = 25920

theorem quotU4_kernel {S : Type} [Group S] [Finite S] {I : Subgroup S} (h : QuotU4 I) :
    ∃ N : Subgroup ↥I, N.Normal ∧ Nat.card ↥I = 25920 * Nat.card ↥N := by
  obtain ⟨T, _, f, hf, hT⟩ := h
  refine ⟨f.ker, inferInstance, ?_⟩
  have e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr e.toEquiv, hT] at h1
  exact h1

theorem quotU4_le {S : Type} [Group S] [Finite S] {I : Subgroup S} (h : QuotU4 I) :
    25920 ≤ Nat.card ↥I := by
  obtain ⟨N, -, hN⟩ := quotU4_kernel h
  rw [hN]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

theorem exclude_small {g : StatedSp 4 (ZMod 2)} {s₀ m : ℕ} {A₀ A₁ : Subgroup (StatedSp 4 (ZMod 2))}
    (hC : Sp8Class g s₀ m A₀ A₁) (hsmall : Nat.card ↥A₀ * Nat.card ↥A₁ < 25920)
    {I : Subgroup (StatedSp 4 (ZMod 2))} (hI : I ≤ Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2))))
    (hq : QuotU4 I) : False := by
  have h1 := quotU4_le hq
  have h2 : Nat.card ↥I ≤ Nat.card ↥(Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2)))) :=
    Subgroup.card_le_of_le hI
  rw [hC.centralizer_eq] at h2
  have h3 : Nat.card ↥(A₀ ⊔ A₁) ≤ Nat.card ↥A₀ * Nat.card ↥A₁ := card_sup_le hC.commute
  omega

theorem card_product_two {g : StatedSp 4 (ZMod 2)} {A₀ A₁ : Subgroup (StatedSp 4 (ZMod 2))}
    (hC : Sp8Class g 2 2 A₀ A₁) : Nat.card ↥A₀ * Nat.card ↥A₁ = 12960 := by
  obtain ⟨e₀⟩ : Nonempty (↥A₀ ≃* StatedSp 2 (ZMod 2)) := (hC.fixed.resolve_left (by norm_num)).2
  obtain ⟨E, _, hE, W, _, _, _, Hf, hsymm, hsep, hdim, ⟨e₁⟩⟩ := hC.unitary
  have h0 : Nat.card ↥A₀ = 720 := by rw [Nat.card_congr e₀.toEquiv]; exact card_sp_two
  have h1 : Nat.card ↥A₁ = 18 := by
    rw [Nat.card_congr e₁.toEquiv]; exact card_unitary_two hE hsymm hsep hdim
  rw [h0, h1]

theorem card_product_three {g : StatedSp 4 (ZMod 2)} {A₀ A₁ : Subgroup (StatedSp 4 (ZMod 2))}
    (hC : Sp8Class g 1 3 A₀ A₁) : Nat.card ↥A₀ * Nat.card ↥A₁ = 3888 := by
  obtain ⟨e₀⟩ : Nonempty (↥A₀ ≃* StatedSp 1 (ZMod 2)) := (hC.fixed.resolve_left (by norm_num)).2
  obtain ⟨E, _, hE, W, _, _, _, Hf, hsymm, hsep, hdim, ⟨e₁⟩⟩ := hC.unitary
  have h0 : Nat.card ↥A₀ = 6 := by rw [Nat.card_congr e₀.toEquiv]; exact card_sp_one
  have h1 : Nat.card ↥A₁ = 648 := by
    rw [Nat.card_congr e₁.toEquiv]; exact card_unitary_three hE hsymm hsep hdim
  rw [h0, h1]

theorem exclude_m1 {g : StatedSp 4 (ZMod 2)} {A₀ A₁ : Subgroup (StatedSp 4 (ZMod 2))}
    (hC : Sp8Class g 3 1 A₀ A₁) {I : Subgroup (StatedSp 4 (ZMod 2))}
    (hI : CFSG.Open.IsSubnormal I (Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2)))))
    (hq : QuotU4 I) : False := by
  obtain ⟨e₀⟩ : Nonempty (↥A₀ ≃* StatedSp 3 (ZMod 2)) := (hC.fixed.resolve_left (by norm_num)).2
  haveI := isSimpleGroup_sp_three
  haveI : IsSimpleGroup ↥A₀ := e₀.isSimpleGroup
  have hcardA₀ : Nat.card ↥A₀ = 1451520 := by
    rw [Nat.card_congr e₀.toEquiv]; exact card_sp_three
  obtain ⟨E, _, hE, W, _, _, _, Hf, hsymm, hsep, hdim, ⟨e₁⟩⟩ := hC.unitary
  have hcardA₁ : Nat.card ↥A₁ = 3 := by
    rw [Nat.card_congr e₁.toEquiv]; exact card_unitary_one hE hsymm hsep hdim
  have hncomm : ¬ ∀ a b : ↥A₀, a * b = b * a :=
    not_comm_of_simple_of_card (by rw [hcardA₀]; norm_num)
  have hZ : Subgroup.center ↥A₀ = ⊥ := center_eq_bot_of_simple_of_not_comm hncomm
  have hcenter_eq : Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2))) = A₀ ⊔ A₁ :=
    hC.centralizer_eq
  have hA₀C : A₀ ≤ Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2))) := hcenter_eq ▸ le_sup_left
  have hcomm : ∀ a ∈ A₀, ∀ b ∈ A₁, a * b = b * a := hC.commute
  have hsub : CFSG.Open.IsSubnormal (I ⊓ A₀) A₀ := CFSG.Open.IsSubnormal.inf_of_le hI hA₀C
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub inferInstance with hbot | htop
  ·
    have hdec : ∀ c : ↥I, ∃ b : ↥A₁, ∃ a ∈ A₀, (c : StatedSp 4 (ZMod 2)) = a * b := by
      intro c
      have hc : (c : StatedSp 4 (ZMod 2)) ∈ A₀ ⊔ A₁ := by
        rw [← hcenter_eq]
        exact hI.le c.2
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup hcomm hc
      exact ⟨⟨b, hb⟩, a, ha, hab⟩
    choose φ ψ hψA hψ using hdec
    have hinj : Function.Injective φ := by
      intro c d hcd
      have hb : ((φ d : ↥A₁) : StatedSp 4 (ZMod 2)) = ((φ c : ↥A₁) : StatedSp 4 (ZMod 2)) := by
        rw [hcd]
      have h1 : (d : StatedSp 4 (ZMod 2)) = ψ d * ((φ c : ↥A₁) : StatedSp 4 (ZMod 2)) := by
        rw [hψ d, hb]
      have h2 : (c : StatedSp 4 (ZMod 2)) = ψ c * ((φ c : ↥A₁) : StatedSp 4 (ZMod 2)) := hψ c
      have hdc : (d : StatedSp 4 (ZMod 2)) * (c : StatedSp 4 (ZMod 2))⁻¹ = ψ d * (ψ c)⁻¹ := by
        rw [h1, h2]
        group
      have hmem : (d : StatedSp 4 (ZMod 2)) * (c : StatedSp 4 (ZMod 2))⁻¹ ∈ I ⊓ A₀ := by
        refine ⟨I.mul_mem d.2 (I.inv_mem c.2), ?_⟩
        rw [hdc]
        exact A₀.mul_mem (hψA d) (A₀.inv_mem (hψA c))
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      exact Subtype.ext hmem.symm
    have hle := Nat.card_le_card_of_injective φ hinj
    have hq' := quotU4_le hq
    rw [hcardA₁] at hle
    omega
  ·
    have hA₀I : A₀ ≤ I := inf_eq_right.1 htop
    obtain ⟨N, hN, hcardI⟩ := quotU4_kernel hq
    let NS : Subgroup (StatedSp 4 (ZMod 2)) := N.map I.subtype
    have hcardNS : Nat.card ↥NS = Nat.card ↥N :=
      Subgroup.card_map_of_injective Subtype.val_injective
    have hNSI : NS ≤ I := by
      rintro _ ⟨x, _, rfl⟩
      exact x.2
    have hNSnorm : ∀ x ∈ I, ∀ n ∈ NS, x * n * x⁻¹ ∈ NS := by
      rintro x hx _ ⟨m, hm, rfl⟩
      have hg : x ∈ I := hx
      apply Subgroup.mem_map.2
      refine ⟨(⟨x, hg⟩ : ↥I) * m * (⟨x, hg⟩ : ↥I)⁻¹, hN.conj_mem m hm _, ?_⟩
      rfl
    have hsubNS : CFSG.Open.IsSubnormal NS I := by
      refine CFSG.Open.IsSubnormal.step hNSI ?_ (CFSG.Open.IsSubnormal.refl I)
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hNSnorm g.1 g.2 _ hn
    have hsubK : CFSG.Open.IsSubnormal (NS ⊓ A₀) A₀ :=
      CFSG.Open.IsSubnormal.inf_of_le hsubNS hA₀I
    have hCcard : Nat.card ↥(A₀ ⊔ A₁) ≤ Nat.card ↥A₀ * Nat.card ↥A₁ := card_sup_le hcomm
    have hIC : Nat.card ↥I ≤ Nat.card ↥(A₀ ⊔ A₁) := by
      rw [← hcenter_eq]
      exact Subgroup.card_le_of_le hI.le
    have hA₀card : Nat.card ↥A₀ ≤ Nat.card ↥I := Subgroup.card_le_of_le hA₀I
    rw [hcardA₀, hcardA₁] at hCcard
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsubK inferInstance with hK | hK
    ·
      have hNSA₁ : NS ≤ A₁ := by
        intro n hn
        have hnC : n ∈ A₀ ⊔ A₁ := by
          rw [← hcenter_eq]
          exact hI.le (hNSI hn)
        obtain ⟨a, ha, b, hb, hnab⟩ := exists_mul_of_mem_sup hcomm hnC
        have hnx : ∀ x ∈ A₀, n * x = x * n := by
          intro x hx
          have hmemNS : n * x * n⁻¹ * x⁻¹ ∈ NS := by
            have h1 : x * n⁻¹ * x⁻¹ ∈ NS := hNSnorm x (hA₀I hx) n⁻¹ (NS.inv_mem hn)
            have h2 : n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) := by group
            rw [h2]
            exact NS.mul_mem hn h1
          have hnxn : n * x * n⁻¹ = a * x * a⁻¹ := by
            rw [hnab]
            calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
              _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [hcomm x hx b hb]
              _ = a * x * a⁻¹ := by group
          have hmemA₀ : n * x * n⁻¹ * x⁻¹ ∈ A₀ := by
            rw [hnxn]
            exact A₀.mul_mem (A₀.mul_mem (A₀.mul_mem ha hx) (A₀.inv_mem ha)) (A₀.inv_mem hx)
          have hmem : n * x * n⁻¹ * x⁻¹ ∈ NS ⊓ A₀ := ⟨hmemNS, hmemA₀⟩
          rw [hK, Subgroup.mem_bot, mul_inv_eq_one] at hmem
          calc n * x = n * x * n⁻¹ * n := by group
            _ = x * n := by rw [hmem]
        have hcomm_a : ∀ x ∈ A₀, x * a = a * x := by
          intro x hx
          have hnx' := hnx x hx
          rw [hnab] at hnx'
          have key : a * x * b = x * a * b := by
            calc a * x * b = a * (x * b) := by rw [mul_assoc]
              _ = a * (b * x) := by rw [hcomm x hx b hb]
              _ = a * b * x := by rw [mul_assoc]
              _ = x * (a * b) := hnx'
              _ = x * a * b := by rw [mul_assoc]
          exact (mul_right_cancel key).symm
        have hamem : (⟨a, ha⟩ : ↥A₀) ∈ Subgroup.center ↥A₀ := by
          rw [Subgroup.mem_center_iff]
          intro y
          apply Subtype.ext
          exact hcomm_a y.1 y.2
        rw [hZ, Subgroup.mem_bot] at hamem
        have ha1 : a = 1 := congrArg Subtype.val hamem
        rw [hnab, ha1, one_mul]
        exact hb
      have h1 : Nat.card ↥NS ≤ Nat.card ↥A₁ := Subgroup.card_le_of_le hNSA₁
      rw [hcardA₁] at h1
      omega
    ·
      have hA₀NS : A₀ ≤ NS := inf_eq_right.1 hK
      have h2 : Nat.card ↥A₀ ≤ Nat.card ↥NS := Subgroup.card_le_of_le hA₀NS
      omega

theorem sp8Class_m4_of_quotU4 {g : StatedSp 4 (ZMod 2)} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    {I : Subgroup (StatedSp 4 (ZMod 2))}
    (hI : CFSG.Open.IsSubnormal I (Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2)))))
    (hq : QuotU4 I) : ∃ A₀ A₁ : Subgroup (StatedSp 4 (ZMod 2)), Sp8Class g 0 4 A₀ A₁ := by
  obtain ⟨s₀, m, A₀, A₁, hC⟩ := exists_class hg3 hg1
  have hsum := hC.sum_eq
  have hone := hC.one_le
  rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with rfl | rfl | rfl | rfl
  · obtain rfl : s₀ = 3 := by omega
    exact (exclude_m1 hC hI hq).elim
  · obtain rfl : s₀ = 2 := by omega
    exact (exclude_small hC (by rw [card_product_two hC]; norm_num) hI.le hq).elim
  · obtain rfl : s₀ = 1 := by omega
    exact (exclude_small hC (by rw [card_product_three hC]; norm_num) hI.le hq).elim
  · obtain rfl : s₀ = 0 := by omega
    exact ⟨A₀, A₁, hC⟩

end CFSG.LocalAnalysis.GLTheoremA.I2016Sp

end
