module

public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup

section Generic

variable {G : Type} [Group G]

theorem s4o_inf_subgroupOf (H K L : Subgroup G) :
    H.subgroupOf L ⊓ K.subgroupOf L = (H ⊓ K).subgroupOf L := by
  ext x
  simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]

theorem s4o_card_subgroupOf {X Y : Subgroup G} (hY : Y ≤ X) :
    Nat.card ↥(Y.subgroupOf X) = Nat.card ↥Y :=
  Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv

theorem s4o_card_inf_centralizer_mul {X A B : Subgroup G} (H : Subgroup G)
    (hA : A ≤ X) (hB : B ≤ X) (hAB : A ⊓ B = ⊥)
    (hX : ∀ x ∈ X, ∃ a ∈ A, ∃ b ∈ B, x = a * b)
    (hHA : H ≤ normalizer (A : Set G)) (hHB : H ≤ normalizer (B : Set G)) :
    Nat.card ↥(X ⊓ centralizer (H : Set G)) =
      Nat.card ↥(A ⊓ centralizer (H : Set G)) * Nat.card ↥(B ⊓ centralizer (H : Set G)) := by
  have hmem : ∀ (a b : G), a ∈ A ⊓ centralizer (H : Set G) → b ∈ B ⊓ centralizer (H : Set G) →
      a * b ∈ X ⊓ centralizer (H : Set G) := by
    intro a b ha hb
    obtain ⟨haA, haC⟩ := Subgroup.mem_inf.1 ha
    obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.1 hb
    refine Subgroup.mem_inf.2 ⟨mul_mem (hA haA) (hB hbB), ?_⟩
    rw [mem_centralizer_iff]
    intro h hh
    rw [← mul_assoc, mem_centralizer_iff.1 haC h hh, mul_assoc, mem_centralizer_iff.1 hbC h hh,
      mul_assoc]
  let F : ↥(A ⊓ centralizer (H : Set G)) × ↥(B ⊓ centralizer (H : Set G)) →
      ↥(X ⊓ centralizer (H : Set G)) := fun p => ⟨p.1.1 * p.2.1, hmem _ _ p.1.2 p.2.2⟩
  have hbij : Function.Bijective F := by
    constructor
    · rintro ⟨⟨a₁, ha₁'⟩, ⟨b₁, hb₁'⟩⟩ ⟨⟨a₂, ha₂'⟩, ⟨b₂, hb₂'⟩⟩ he
      have ha₁ := (Subgroup.mem_inf.1 ha₁').1
      have ha₂ := (Subgroup.mem_inf.1 ha₂').1
      have hb₁ := (Subgroup.mem_inf.1 hb₁').1
      have hb₂ := (Subgroup.mem_inf.1 hb₂').1
      have he' : a₁ * b₁ = a₂ * b₂ := congrArg Subtype.val he
      have h1 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
        calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
          _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [he']
          _ = b₂ * b₁⁻¹ := by group
      have h2 : a₂⁻¹ * a₁ ∈ A ⊓ B :=
        Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha₂) ha₁, h1 ▸ mul_mem hb₂ (inv_mem hb₁)⟩
      rw [hAB, mem_bot] at h2
      have h3 : a₁ = a₂ := by
        calc a₁ = a₂ * (a₂⁻¹ * a₁) := by group
          _ = a₂ := by rw [h2, mul_one]
      have h4 : b₁ = b₂ := by
        have : b₂ * b₁⁻¹ = 1 := by rw [← h1, h2]
        calc b₁ = (b₂ * b₁⁻¹)⁻¹ * b₂ := by group
          _ = b₂ := by rw [this, inv_one, one_mul]
      subst h3; subst h4; rfl
    · rintro ⟨x, hx⟩
      obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hX x hxX
      have hcomm : ∀ h ∈ H, h * a = a * h ∧ h * b = b * h := by
        intro h hh
        have haA : h * a * h⁻¹ ∈ A := (mem_normalizer_iff.1 (hHA hh) a).1 ha
        have hbB : h * b * h⁻¹ ∈ B := (mem_normalizer_iff.1 (hHB hh) b).1 hb
        have e : (h * a * h⁻¹) * (h * b * h⁻¹) = a * b := by
          have := mem_centralizer_iff.1 hxC h hh
          calc (h * a * h⁻¹) * (h * b * h⁻¹) = h * (a * b) * h⁻¹ := by group
            _ = a * b := by rw [this]; group
        have h1 : a⁻¹ * (h * a * h⁻¹) = b * (h * b * h⁻¹)⁻¹ := by
          calc a⁻¹ * (h * a * h⁻¹) = a⁻¹ * ((h * a * h⁻¹) * (h * b * h⁻¹)) * (h * b * h⁻¹)⁻¹ := by
                group
            _ = a⁻¹ * (a * b) * (h * b * h⁻¹)⁻¹ := by rw [e]
            _ = b * (h * b * h⁻¹)⁻¹ := by group
        have h2 : a⁻¹ * (h * a * h⁻¹) ∈ A ⊓ B :=
          Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha) haA, h1 ▸ mul_mem hb (inv_mem hbB)⟩
        rw [hAB, mem_bot] at h2
        have h3 : h * a * h⁻¹ = a := by
          calc h * a * h⁻¹ = a * (a⁻¹ * (h * a * h⁻¹)) := by group
            _ = a := by rw [h2, mul_one]
        have h4 : h * b * h⁻¹ = b := by
          have : b * (h * b * h⁻¹)⁻¹ = 1 := by rw [← h1, h2]
          have h5 : (h * b * h⁻¹)⁻¹ = b⁻¹ := by
            calc (h * b * h⁻¹)⁻¹ = b⁻¹ * (b * (h * b * h⁻¹)⁻¹) := by group
              _ = b⁻¹ := by rw [this, mul_one]
          exact inv_injective h5
        exact ⟨mul_inv_eq_iff_eq_mul.1 h3, mul_inv_eq_iff_eq_mul.1 h4⟩
      refine ⟨⟨⟨a, Subgroup.mem_inf.2 ⟨ha, mem_centralizer_iff.2 fun h hh => (hcomm h hh).1⟩⟩,
        ⟨b, Subgroup.mem_inf.2 ⟨hb, mem_centralizer_iff.2 fun h hh => (hcomm h hh).2⟩⟩⟩, rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective F hbij)).symm

section Equivariant

variable [Finite G]

theorem s4o_card_mul_card_of_equivariant
    {X N A B H : Subgroup G} [(B.subgroupOf A).Normal]
    (hNX : N ≤ X) (hBA : B ≤ A)
    (hHX : H ≤ normalizer (X : Set G)) (hHN : H ≤ normalizer (N : Set G))
    (hHA : H ≤ normalizer (A : Set G)) (hHB : H ≤ normalizer (B : Set G))
    (hXs : Group.IsSolvable X) (hAs : Group.IsSolvable A)
    (hXc : (Nat.card H).Coprime (Nat.card X)) (hAc : (Nat.card H).Coprime (Nat.card A))
    (ψ : X →* A ⧸ B.subgroupOf A) (hψ : Function.Surjective ψ) (hker : ψ.ker = N.subgroupOf X)
    (hequ : ∀ c ∈ H, ∀ (e : X) (a : A) (he : c * e * c⁻¹ ∈ X) (ha : c * a * c⁻¹ ∈ A),
      ψ e = QuotientGroup.mk a → ψ ⟨c * e * c⁻¹, he⟩ = QuotientGroup.mk ⟨c * a * c⁻¹, ha⟩) :
    Nat.card ↥(X ⊓ centralizer (H : Set G)) * Nat.card ↥(B ⊓ centralizer (H : Set G)) =
      Nat.card ↥(N ⊓ centralizer (H : Set G)) * Nat.card ↥(A ⊓ centralizer (H : Set G)) := by
  classical
  have hXN : X ≤ normalizer (N : Set G) := by
    have : (N.subgroupOf X).Normal := hker ▸ MonoidHom.normal_ker ψ
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).1 this
  have hAB : A ≤ normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBA).1 inferInstance
  set K : Subgroup X := (X ⊓ centralizer (H : Set G)).subgroupOf X with hK
  set C : Subgroup A := (A ⊓ centralizer (H : Set G)).subgroupOf A with hC
  have hmap : K.map ψ = C.map (QuotientGroup.mk' (B.subgroupOf A)) := by
    ext y
    constructor
    · rintro ⟨e, heK, rfl⟩
      have heC : (e : G) ∈ centralizer (H : Set G) :=
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 heK)).2
      obtain ⟨a₀, ha₀⟩ := QuotientGroup.mk_surjective (ψ e)
      have hfix : ∀ c ∈ H, (a₀ : G)⁻¹ * (c * (a₀ : G) * c⁻¹) ∈ B := by
        intro c hc
        have hcA : c * (a₀ : G) * c⁻¹ ∈ A := (mem_normalizer_iff.1 (hHA hc) _).1 a₀.2
        have hcX : c * (e : G) * c⁻¹ ∈ X := (mem_normalizer_iff.1 (hHX hc) _).1 e.2
        have h1 := hequ c hc e a₀ hcX hcA ha₀.symm
        have he' : (⟨c * (e : G) * c⁻¹, hcX⟩ : X) = e := by
          apply Subtype.ext
          show c * (e : G) * c⁻¹ = e
          rw [mul_inv_eq_iff_eq_mul]
          exact mem_centralizer_iff.1 heC c hc
        rw [he'] at h1
        have h2 : (QuotientGroup.mk a₀ : A ⧸ B.subgroupOf A) =
            QuotientGroup.mk ⟨c * (a₀ : G) * c⁻¹, hcA⟩ := ha₀.trans h1
        exact Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h2)
      obtain ⟨c₀, hc₀, b, hb, hab⟩ :=
        Common.exists_mem_inf_centralizer_mul_of_coprime hBA hAB hHA hHB hAs hAc a₀.2 hfix
      refine ⟨⟨c₀, (Subgroup.mem_inf.1 hc₀).1⟩, Subgroup.mem_subgroupOf.2 hc₀, ?_⟩
      show (QuotientGroup.mk ⟨c₀, (Subgroup.mem_inf.1 hc₀).1⟩ : A ⧸ B.subgroupOf A) = ψ e
      rw [← ha₀]
      refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
      show c₀⁻¹ * (a₀ : G) ∈ B
      rw [hab, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hb
    · rintro ⟨a₀, ha₀C, rfl⟩
      have ha₀C' : (a₀ : G) ∈ centralizer (H : Set G) :=
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ha₀C)).2
      obtain ⟨e, he⟩ := hψ (QuotientGroup.mk' (B.subgroupOf A) a₀)
      have hfix : ∀ c ∈ H, (e : G)⁻¹ * (c * (e : G) * c⁻¹) ∈ N := by
        intro c hc
        have hcA : c * (a₀ : G) * c⁻¹ ∈ A := (mem_normalizer_iff.1 (hHA hc) _).1 a₀.2
        have hcX : c * (e : G) * c⁻¹ ∈ X := (mem_normalizer_iff.1 (hHX hc) _).1 e.2
        have h1 := hequ c hc e a₀ hcX hcA he
        have ha₀' : (⟨c * (a₀ : G) * c⁻¹, hcA⟩ : A) = a₀ := by
          apply Subtype.ext
          show c * (a₀ : G) * c⁻¹ = a₀
          rw [mul_inv_eq_iff_eq_mul]
          exact mem_centralizer_iff.1 ha₀C' c hc
        rw [ha₀'] at h1
        have he2 : ψ e = (QuotientGroup.mk a₀ : A ⧸ B.subgroupOf A) := he
        have h2 : ψ ((e⁻¹) * ⟨c * (e : G) * c⁻¹, hcX⟩) = 1 := by
          rw [map_mul, map_inv, h1, he2]
          exact inv_mul_cancel _
        have h3 : (e⁻¹) * ⟨c * (e : G) * c⁻¹, hcX⟩ ∈ ψ.ker := h2
        rw [hker] at h3
        exact Subgroup.mem_subgroupOf.1 h3
      obtain ⟨c₀, hc₀, n, hn, hen⟩ :=
        Common.exists_mem_inf_centralizer_mul_of_coprime hNX hXN hHX hHN hXs hXc e.2 hfix
      refine ⟨⟨c₀, (Subgroup.mem_inf.1 hc₀).1⟩, Subgroup.mem_subgroupOf.2 hc₀, ?_⟩
      have hee : e = ⟨c₀, (Subgroup.mem_inf.1 hc₀).1⟩ * ⟨n, hNX hn⟩ := Subtype.ext hen
      have hn1 : ψ ⟨n, hNX hn⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact Subgroup.mem_subgroupOf.2 hn
      rw [← he, hee, map_mul, hn1, mul_one]
  have hKcard : Nat.card K = Nat.card ↥(X ⊓ centralizer (H : Set G)) :=
    s4o_card_subgroupOf inf_le_left
  have hCcard : Nat.card C = Nat.card ↥(A ⊓ centralizer (H : Set G)) :=
    s4o_card_subgroupOf inf_le_left
  have h1 : Nat.card (K.map ψ) * Nat.card ↥(ψ.ker ⊓ K) = Nat.card K := by
    rw [← Subgroup.relIndex_ker (K := K) (f := ψ)]
    exact Subgroup.relIndex_mul_card _ _
  have h2 : Nat.card (C.map (QuotientGroup.mk' (B.subgroupOf A))) *
      Nat.card ↥((QuotientGroup.mk' (B.subgroupOf A)).ker ⊓ C) = Nat.card C := by
    rw [← Subgroup.relIndex_ker (K := C) (f := QuotientGroup.mk' (B.subgroupOf A))]
    exact Subgroup.relIndex_mul_card _ _
  rw [QuotientGroup.ker_mk'] at h2
  rw [hker] at h1
  have h3 : N.subgroupOf X ⊓ K = (N ⊓ centralizer (H : Set G)).subgroupOf X := by
    rw [hK, s4o_inf_subgroupOf, ← inf_assoc, inf_of_le_left hNX]
  have h4 : B.subgroupOf A ⊓ C = (B ⊓ centralizer (H : Set G)).subgroupOf A := by
    rw [hC, s4o_inf_subgroupOf, ← inf_assoc, inf_of_le_left hBA]
  rw [h3, s4o_card_subgroupOf (inf_le_left.trans hNX), hKcard] at h1
  rw [h4, s4o_card_subgroupOf (inf_le_left.trans hBA), hCcard] at h2
  rw [hmap] at h1
  calc Nat.card ↥(X ⊓ centralizer (H : Set G)) * Nat.card ↥(B ⊓ centralizer (H : Set G))
      = (Nat.card (C.map (QuotientGroup.mk' (B.subgroupOf A))) *
          Nat.card ↥(N ⊓ centralizer (H : Set G))) * Nat.card ↥(B ⊓ centralizer (H : Set G)) := by
        rw [h1]
    _ = Nat.card ↥(N ⊓ centralizer (H : Set G)) *
          (Nat.card (C.map (QuotientGroup.mk' (B.subgroupOf A))) *
            Nat.card ↥(B ⊓ centralizer (H : Set G))) := by ring
    _ = _ := by rw [h2]

theorem s4o_card_of_equivariant_subgroup
    {X N Y H : Subgroup G}
    (hNX : N ≤ X)
    (hHX : H ≤ normalizer (X : Set G)) (hHN : H ≤ normalizer (N : Set G))
    (hHY : H ≤ normalizer (Y : Set G))
    (hXs : Group.IsSolvable X) (hYs : Group.IsSolvable Y)
    (hXc : (Nat.card H).Coprime (Nat.card X)) (hYc : (Nat.card H).Coprime (Nat.card Y))
    (ψ : X →* Y) (hψ : Function.Surjective ψ) (hker : ψ.ker = N.subgroupOf X)
    (hequ : ∀ c ∈ H, ∀ x : X, ∃ hx : c * x * c⁻¹ ∈ X,
      (ψ ⟨c * x * c⁻¹, hx⟩ : G) = c * (ψ x : G) * c⁻¹) :
    Nat.card ↥(X ⊓ centralizer (H : Set G)) =
      Nat.card ↥(N ⊓ centralizer (H : Set G)) * Nat.card ↥(Y ⊓ centralizer (H : Set G)) := by
  classical
  haveI : ((⊥ : Subgroup G).subgroupOf Y).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  let ψ' : X →* Y ⧸ (⊥ : Subgroup G).subgroupOf Y :=
    (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf Y)).comp ψ
  have hbot : ∀ y z : Y, (QuotientGroup.mk y : Y ⧸ (⊥ : Subgroup G).subgroupOf Y) =
      QuotientGroup.mk z → y = z := by
    intro y z hyz
    have := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hyz)
    rw [Subgroup.mem_bot] at this
    have h2 : (y : G)⁻¹ * z = 1 := this
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  have hψ' : Function.Surjective ψ' :=
    (QuotientGroup.mk'_surjective _).comp hψ
  have hker' : ψ'.ker = N.subgroupOf X := by
    rw [← hker]
    ext x
    simp only [MonoidHom.mem_ker, ψ', MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    constructor
    · intro hx
      exact hbot _ 1 (by rw [hx]; rfl)
    · intro hx
      rw [hx]
      rfl
  have key := s4o_card_mul_card_of_equivariant (X := X) (N := N) (A := Y) (B := ⊥) (H := H) hNX
    bot_le hHX hHN hHY (by
      intro c hc
      rw [mem_normalizer_iff]
      intro x
      simp only [Subgroup.mem_bot, SetLike.mem_coe]
      constructor
      · intro hx; rw [hx]; simp
      · intro hx
        have : c⁻¹ * (c * x * c⁻¹) * c = x := by group
        rw [← this, hx]; simp) hXs hYs hXc hYc ψ' hψ' hker' (by
      intro c hc e a he ha hea
      have h1 : ψ e = a := hbot _ _ hea
      obtain ⟨hx, hx2⟩ := hequ c hc e
      have : ψ ⟨c * e * c⁻¹, he⟩ = ⟨c * a * c⁻¹, ha⟩ := by
        apply Subtype.ext
        have := hx2
        rw [h1] at this
        exact this
      show (QuotientGroup.mk (ψ ⟨c * e * c⁻¹, he⟩) : Y ⧸ (⊥ : Subgroup G).subgroupOf Y) = _
      rw [this])
  have hbc : Nat.card ↥((⊥ : Subgroup G) ⊓ centralizer (H : Set G)) = 1 := by
    rw [bot_inf_eq]; exact Subgroup.card_bot
  rw [hbc, mul_one] at key
  exact key

end Equivariant

end Generic

end CFSG.LocalAnalysis.EvenBN.U5
