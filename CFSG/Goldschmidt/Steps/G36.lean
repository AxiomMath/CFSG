module

public import CFSG.Goldschmidt.Steps.G36Setup
public import CFSG.Goldschmidt.Steps.G36TypeIMain

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped commutatorElement

section Transfer

variable {G : Type*} [Group G] {A L : Subgroup G}
  (hdecomp : ∀ a ∈ A, ∃ a₁ ∈ A ⊓ L, ∃ a₂ ∈ A ⊓ Subgroup.centralizer (L : Set G), a = a₁ * a₂)
include hdecomp

theorem mem_centralizer_of_decomp {c : G} (hcL : c ∈ L) (hc : ∀ b ∈ A ⊓ L, b * c = c * b) :
    c ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hdecomp a ha
  have h2 := Subgroup.mem_centralizer_iff.mp ha₂.2 c hcL
  calc a₁ * a₂ * c = a₁ * (c * a₂) := by rw [mul_assoc, ← h2]
    _ = (a₁ * c) * a₂ := by group
    _ = (c * a₁) * a₂ := by rw [hc a₁ ha₁]
    _ = c * (a₁ * a₂) := by group

theorem mem_normalizer_of_decomp [Finite G] {n : G} (hnL : n ∈ L)
    (hn : ∀ b ∈ A ⊓ L, n * b * n⁻¹ ∈ A ⊓ L) : n ∈ Subgroup.normalizer (A : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro a ha
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hdecomp a ha
  have h2 := Subgroup.mem_centralizer_iff.mp ha₂.2 n hnL
  have : n * (a₁ * a₂) * n⁻¹ = (n * a₁ * n⁻¹) * a₂ := by
    calc n * (a₁ * a₂) * n⁻¹ = (n * a₁ * n⁻¹) * (n * a₂ * n⁻¹) := by group
      _ = (n * a₁ * n⁻¹) * a₂ := by rw [h2, mul_inv_cancel_right]
  rw [this]
  exact A.mul_mem (hn a₁ ha₁).1 ha₂.1

theorem commutator_eq_of_decomp {y : G} (hyL : y ∈ L) :
    ⁅A, Subgroup.zpowers y⁆ = ⁅A ⊓ L, Subgroup.zpowers y⁆ := by
  apply le_antisymm _ (Subgroup.commutator_mono inf_le_left le_rfl)
  rw [Subgroup.commutator_le]
  intro a ha g hg
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hdecomp a ha
  have hgL : g ∈ L := (Subgroup.zpowers_le.mpr hyL) hg
  have h2 := Subgroup.mem_centralizer_iff.mp ha₂.2 g hgL
  have : ⁅a₁ * a₂, g⁆ = ⁅a₁, g⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a₁ * a₂ * g * (a₁ * a₂)⁻¹ * g⁻¹ = a₁ * (a₂ * g) * a₂⁻¹ * a₁⁻¹ * g⁻¹ := by group
      _ = a₁ * (g * a₂) * a₂⁻¹ * a₁⁻¹ * g⁻¹ := by rw [← h2]
      _ = a₁ * g * a₁⁻¹ * g⁻¹ := by group
  rw [this]
  exact Subgroup.commutator_mem_commutator ha₁ hg

end Transfer

theorem G36_of
    (h32 : S_G32) (hNP : S_GNewPair) (h31 : S_G31) : S_G36 := by
  intro G _ _ H A hS hE L hL
  classical
  obtain ⟨hdecomp, T₀, hyp, htype⟩ := exists_g36Hyp h31 hS hE hL
  obtain ⟨y', hyN, hyodd, htrans, hcent, hcase⟩ := g36Local h32 hNP hyp htype
  have hyL : (y' : G) ∈ L := y'.2
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hconjL : ∀ n : L, n ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup L) : Set L) →
      ∀ b ∈ A ⊓ L, (n : G) * b * (n : G)⁻¹ ∈ A ⊓ L := by
    intro n hn b hb
    have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨b, hb.2⟩).mp hb.1
    exact ⟨h1, L.mul_mem (L.mul_mem n.2 hb.2) (L.inv_mem n.2)⟩
  have hNiff : ∀ n : L, n ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup L) : Set L) ↔
      (n : G) ∈ Subgroup.normalizer (A : Set G) := by
    intro n
    constructor
    · intro hn
      exact mem_normalizer_of_decomp hdecomp n.2 (hconjL n hn)
    · intro hn
      apply mem_normalizer_of_conj_mem
      intro b hb
      exact (Subgroup.mem_normalizer_iff.mp hn b).mp hb
  have hCiff : ∀ c : L, c ∈ Subgroup.centralizer ((A.subgroupOf L : Subgroup L) : Set L) ↔
      (c : G) ∈ Subgroup.centralizer (A : Set G) := by
    intro c
    constructor
    · intro hc
      refine mem_centralizer_of_decomp hdecomp c.2 fun b hb => ?_
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc ⟨b, hb.2⟩ hb.1)
    · intro hc
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc b hb)
  have hyNG : (y' : G) ∈ Subgroup.normalizer (A : Set G) := (hNiff y').mp hyN
  have hCmap : (Subgroup.centralizer ((A.subgroupOf L : Subgroup L) : Set L)).map L.subtype =
      L ⊓ Subgroup.centralizer (A : Set G) := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, (hCiff c).mp hc⟩
    · rintro ⟨hxL, hxC⟩
      exact ⟨⟨x, hxL⟩, (hCiff ⟨x, hxL⟩).mpr hxC, rfl⟩
  have hNmap : (Subgroup.normalizer ((A.subgroupOf L : Subgroup L) : Set L)).map L.subtype =
      L ⊓ Subgroup.normalizer (A : Set G) := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n.2, (hNiff n).mp hn⟩
    · rintro ⟨hxL, hxN⟩
      exact ⟨⟨x, hxL⟩, (hNiff ⟨x, hxL⟩).mpr hxN, rfl⟩
  have hsupmap : (Subgroup.zpowers y' ⊔
      Subgroup.centralizer ((A.subgroupOf L : Subgroup L) : Set L)).map L.subtype ≤
      Subgroup.zpowers (y' : G) ⊔ L ⊓ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hCmap]
    rfl
  have hcomm : ⁅A, Subgroup.zpowers (y' : G)⁆ =
      (⁅A.subgroupOf L, Subgroup.zpowers y'⁆).map L.subtype := by
    rw [commutator_eq_of_decomp hdecomp hyL, Subgroup.map_commutator,
      Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers]
    rfl
  refine ⟨y', ⟨hyL, hyNG⟩, by rw [Subgroup.orderOf_coe]; exact hyodd, ?_, ?_, ?_⟩
  ·
    intro b hb c hc hb1 hc1
    rw [hcomm] at hb hc
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨k, hk⟩ := htrans b' hb' c' hc' (fun h => hb1 (by rw [h]; rfl))
      (fun h => hc1 (by rw [h]; rfl))
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  ·
    apply le_antisymm
    · intro a ha
      obtain ⟨haA, hay⟩ := Subgroup.mem_inf.mp ha
      rw [Subgroup.mem_centralizer_singleton_iff] at hay
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hdecomp a haA
      have h2 := Subgroup.mem_centralizer_iff.mp ha₂.2 _ hyL
      have h1 : a₁ * (y' : G) = (y' : G) * a₁ := by
        have : a₁ * a₂ * (y' : G) = a₁ * (y' : G) * a₂ := by rw [mul_assoc, ← h2]; group
        rw [this, ← mul_assoc] at hay
        exact mul_right_cancel hay
      have hz := hcent ⟨a₁, ha₁.2⟩ ha₁.1 (Subtype.ext h1)
      refine ⟨haA, Subgroup.mul_mem _ ?_ ha₂.2⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩)
    · intro a ha
      obtain ⟨haA, haC⟩ := Subgroup.mem_inf.mp ha
      refine Subgroup.mem_inf.mpr ⟨haA, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp haC _ hyL).symm
  rcases hcase with ⟨m, hym, hz⟩ | ⟨hSz8, hidx, hyC, hy7, hself⟩
  ·
    left
    rintro x ⟨hxA, hxL⟩
    have hxL' : x⁻¹ * (y' : G) * x ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set G)).inv_mem hxL) (y' : G)).mp hyL
      simpa using this
    set z : L := ⟨x⁻¹ * (y' : G) * x, hxL'⟩ with hzdef
    have hxconj : ∀ b ∈ A ⊓ L, x * b * x⁻¹ ∈ A ⊓ L := fun b hb =>
      ⟨(Subgroup.mem_normalizer_iff.mp hxA b).mp hb.1,
        (Subgroup.mem_normalizer_iff.mp hxL b).mp hb.2⟩
    have hxconj' : ∀ b ∈ A ⊓ L, x⁻¹ * b * x ∈ A ⊓ L := by
      intro b hb
      have hxA' := (Subgroup.normalizer (A : Set G)).inv_mem hxA
      have hxL'' := (Subgroup.normalizer (L : Set G)).inv_mem hxL
      have h1 := (Subgroup.mem_normalizer_iff.mp hxA' b).mp hb.1
      have h2 := (Subgroup.mem_normalizer_iff.mp hxL'' b).mp hb.2
      rw [inv_inv] at h1 h2
      exact ⟨h1, h2⟩
    have hzN : z ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup L) : Set L) := by
      apply mem_normalizer_of_conj_mem
      intro b hb
      have h1 := hxconj' _ (hconjL y' hyN _ (hxconj (b : G) ⟨hb, b.2⟩))
      have : ((z * b * z⁻¹ : L) : G) =
          x⁻¹ * ((y' : G) * (x * (b : G) * x⁻¹) * (y' : G)⁻¹) * x := by
        simp only [hzdef, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      show ((z * b * z⁻¹ : L) : G) ∈ A
      rw [this]
      exact h1.1
    have hzm : z ^ m ∈ Subgroup.centralizer ((A.subgroupOf L : Subgroup L) : Set L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      apply Subtype.ext
      have hbx := hxconj (b : G) ⟨hb, b.2⟩
      have hy1 := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hym ⟨_, hbx.2⟩ hbx.1)
      simp only [Subgroup.coe_mul, Subgroup.coe_pow] at hy1 ⊢
      have hzpow : ((z : G)) ^ m = x⁻¹ * (y' : G) ^ m * x := by
        show (x⁻¹ * (y' : G) * x) ^ m = x⁻¹ * (y' : G) ^ m * x
        have := conj_pow (a := x⁻¹) (b := (y' : G)) (i := m)
        rwa [inv_inv] at this
      rw [hzpow]
      calc (b : G) * (x⁻¹ * (y' : G) ^ m * x) =
          x⁻¹ * ((x * b * x⁻¹) * (y' : G) ^ m) * x := by group
        _ = x⁻¹ * ((y' : G) ^ m * (x * b * x⁻¹)) * x := by rw [hy1]
        _ = x⁻¹ * (y' : G) ^ m * x * b := by group
    have h1 := hz z hzN hzm
    exact hsupmap ⟨z, h1, rfl⟩
  ·
    right
    refine ⟨hSz8, ?_, fun h => hyC ((hCiff y').mpr h), ?_, ?_⟩
    · rw [← hCmap, ← hNmap]
      change (Subgroup.map L.subtype _).relIndex (Subgroup.map L.subtype _) = 56
      rw [Subgroup.relIndex_map_map_of_injective _ _ L.subtype_injective]
      exact hidx
    · exact (hCiff (y' ^ 7)).mp hy7
    · rintro x ⟨hxL, hxA⟩ hxy
      set x' : L := ⟨x, hxL⟩ with hx'def
      have hx'N : x' ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup L) : Set L) :=
        (hNiff x').mpr hxA
      have hyCA : Subgroup.zpowers (y' : G) ≤
          Subgroup.normalizer ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
        rw [Subgroup.zpowers_le]
        apply mem_normalizer_of_conj_mem
        intro c hc
        rw [Subgroup.mem_centralizer_iff] at hc ⊢
        intro a ha
        have ha' : (y' : G)⁻¹ * a * (y' : G) ∈ A := by
          have := (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (A : Set G)).inv_mem hyNG) a).mp ha
          simpa using this
        have h1 := hc _ ha'
        calc a * ((y' : G) * c * (y' : G)⁻¹) =
            (y' : G) * (((y' : G)⁻¹ * a * (y' : G)) * c) * (y' : G)⁻¹ := by group
          _ = (y' : G) * (c * ((y' : G)⁻¹ * a * (y' : G))) * (y' : G)⁻¹ := by rw [h1]
          _ = (y' : G) * c * (y' : G)⁻¹ * a := by group
      have hw : x'⁻¹ * y' * x' ∈ Subgroup.zpowers y' ⊔
          Subgroup.centralizer ((A.subgroupOf L : Subgroup L) : Set L) := by
        have hxy' : x⁻¹ * (y' : G) * x ∈ ((Subgroup.zpowers (y' : G) ⊔
            Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := hxy
        rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hyCA] at hxy'
        obtain ⟨g, hg, c, hc, hgc⟩ := Set.mem_mul.mp hxy'
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        have hcL : c ∈ L := by
          have : c = ((y' : G) ^ j)⁻¹ * (x⁻¹ * (y' : G) * x) := by rw [← hgc]; group
          rw [this]
          exact L.mul_mem (L.inv_mem (L.zpow_mem hyL j))
            (L.mul_mem (L.mul_mem (L.inv_mem hxL) hyL) hxL)
        have hc' : (⟨c, hcL⟩ : L) ∈
            Subgroup.centralizer ((A.subgroupOf L : Subgroup L) : Set L) :=
          (hCiff ⟨c, hcL⟩).mpr hc
        have heq : x'⁻¹ * y' * x' = y' ^ j * ⟨c, hcL⟩ := by
          apply Subtype.ext
          simp only [hx'def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
          exact hgc.symm
        rw [heq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers y' j))
          (Subgroup.mem_sup_right hc')
      have h1 := hself x' hx'N hw
      have h2 := hsupmap ⟨x', h1, rfl⟩
      exact (sup_le_sup_left (inf_le_right : L ⊓ Subgroup.centralizer (A : Set G) ≤ _)
        (Subgroup.zpowers (y' : G))) h2

end CFSG.Goldschmidt
