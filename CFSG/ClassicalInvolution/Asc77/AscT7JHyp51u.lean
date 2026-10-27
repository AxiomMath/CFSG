module

public import CFSG.ClassicalInvolution.Asc77.AscT7S22Z
public import CFSG.ClassicalInvolution.Asc77.AscT7JSq
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.AscT7BSylow
import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec
import CFSG.ClassicalInvolution.Asc77.WP3FrameChain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected

namespace T7J

section Cmt

variable {G : Type} [Group G] {z v₁ v₂ v₃ : G}

structure Cmt (z v₁ v₂ v₃ : G) : Prop where
  s₁ : v₁ * v₁ = z
  s₂ : v₂ * v₂ = z
  s₃ : v₃ * v₃ = z
  z2 : z * z = 1
  c₁₂ : v₁ * v₂ = v₂ * v₁
  c₁₃ : v₁ * v₃ = v₃ * v₁
  c₂₃ : v₂ * v₃ = v₃ * v₂

theorem Cmt.zc₁ (h : Cmt z v₁ v₂ v₃) : z * v₁ = v₁ * z := by
  rw [← h.s₁]; group

theorem Cmt.zc₂ (h : Cmt z v₁ v₂ v₃) : z * v₂ = v₂ * z := by
  rw [← h.s₂]; group

theorem Cmt.zc₃ (h : Cmt z v₁ v₂ v₃) : z * v₃ = v₃ * z := by
  rw [← h.s₃]; group

theorem Cmt.rot (h : Cmt z v₁ v₂ v₃) : Cmt z v₂ v₃ v₁ :=
  ⟨h.s₂, h.s₃, h.s₁, h.z2, h.c₂₃, h.c₁₂.symm, h.c₁₃.symm⟩

theorem Cmt.rel (h : Cmt z v₁ v₂ v₃) : (v₁ * v₂) * (v₂ * v₃) = z * (v₁ * v₃) := by
  calc (v₁ * v₂) * (v₂ * v₃) = v₁ * (v₂ * v₂) * v₃ := by group
    _ = v₁ * z * v₃ := by rw [h.s₂]
    _ = z * v₁ * v₃ := by rw [← h.zc₁]
    _ = z * (v₁ * v₃) := by group

theorem Cmt.sq_pair (h : Cmt z v₁ v₂ v₃) : (v₁ * v₂) * (v₁ * v₂) = 1 := by
  calc (v₁ * v₂) * (v₁ * v₂) = v₁ * (v₂ * v₁) * v₂ := by group
    _ = v₁ * (v₁ * v₂) * v₂ := by rw [h.c₁₂]
    _ = (v₁ * v₁) * (v₂ * v₂) := by group
    _ = 1 := by rw [h.s₁, h.s₂, h.z2]

theorem Cmt.rel' (h : Cmt z v₁ v₂ v₃) : (v₂ * v₃) * (v₃ * v₁) = z * (v₁ * v₂) := by
  have := h.rot.rel
  calc (v₂ * v₃) * (v₃ * v₁) = z * (v₂ * v₁) := this
    _ = z * (v₁ * v₂) := by rw [h.c₁₂]

theorem Cmt.sq_z (h : Cmt z v₁ v₂ v₃) : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z2

theorem Cmt.inv_v₁ (h : Cmt z v₁ v₂ v₃) : v₁⁻¹ = v₁ * z :=
  inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, h.s₁, h.z2])

theorem Cmt.zc₁₃ (h : Cmt z v₁ v₂ v₃) : z * (v₁ * v₃) = (v₁ * v₃) * z := by
  calc z * (v₁ * v₃) = (z * v₁) * v₃ := by rw [mul_assoc]
    _ = (v₁ * z) * v₃ := by rw [h.zc₁]
    _ = v₁ * (z * v₃) := by rw [mul_assoc]
    _ = v₁ * (v₃ * z) := by rw [h.zc₃]
    _ = (v₁ * v₃) * z := by rw [mul_assoc]

theorem Cmt.zc₂₃ (h : Cmt z v₁ v₂ v₃) : z * (v₂ * v₃) = (v₂ * v₃) * z := by
  calc z * (v₂ * v₃) = (z * v₂) * v₃ := by rw [mul_assoc]
    _ = (v₂ * z) * v₃ := by rw [h.zc₂]
    _ = v₂ * (z * v₃) := by rw [mul_assoc]
    _ = v₂ * (v₃ * z) := by rw [h.zc₃]
    _ = (v₂ * v₃) * z := by rw [mul_assoc]

theorem Cmt.eq_xw (h : Cmt z v₁ v₂ v₃) : (v₁ * v₂) * (v₂ * v₃) = (v₃ * v₁) * z := by
  rw [h.rel, h.zc₁₃, h.c₁₃]

theorem Cmt.eq_xyw (h : Cmt z v₁ v₂ v₃) : (v₁ * v₂) * z * (v₂ * v₃) = v₃ * v₁ := by
  calc (v₁ * v₂) * z * (v₂ * v₃) = (v₁ * v₂) * (z * (v₂ * v₃)) := by rw [mul_assoc]
    _ = (v₁ * v₂) * ((v₂ * v₃) * z) := by rw [h.zc₂₃]
    _ = ((v₁ * v₂) * (v₂ * v₃)) * z := (mul_assoc _ _ _).symm
    _ = ((v₃ * v₁) * z) * z := by rw [h.eq_xw]
    _ = (v₃ * v₁) * (z * z) := mul_assoc _ _ _
    _ = v₃ * v₁ := by rw [h.z2, mul_one]

theorem Cmt.commute_xz (h : Cmt z v₁ v₂ v₃) : Commute (v₁ * v₂) z :=
  Commute.mul_left (h.zc₁.symm : Commute v₁ z) (h.zc₂.symm : Commute v₂ z)

theorem Cmt.commute_wz (h : Cmt z v₁ v₂ v₃) : Commute (v₂ * v₃) z :=
  Commute.mul_left (h.zc₂.symm : Commute v₂ z) (h.zc₃.symm : Commute v₃ z)

theorem Cmt.commute_xw (h : Cmt z v₁ v₂ v₃) : Commute (v₁ * v₂) (v₂ * v₃) :=
  Commute.mul_left (Commute.mul_right (h.c₁₂ : Commute v₁ v₂) (h.c₁₃ : Commute v₁ v₃))
    (Commute.mul_right (Commute.refl v₂) (h.c₂₃ : Commute v₂ v₃))

end Cmt

section Twins

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem twin_le_trivialOnQuot (hΩ : HypOmegaMod p f Ω) {J J' : Subgroup G} {z : G}
    (hJ : J ∈ Ω) (hJ' : J' ∈ Ω) (hne : J ≠ J') (hz : IsUniqueInvolution J z)
    (hz' : IsUniqueInvolution J' z) : J ≤ trivialOnQuot J' := by
  have h4 := hΩ.omega4 J hJ J' hJ' hne
  have hmem : z ∈ J ⊓ J' := ⟨hz.mem, hz'.mem⟩
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hdvd : 2 ∣ Nat.card ↥(J ⊓ J') := by
    have := Subgroup.orderOf_dvd_natCard (J ⊓ J') hmem
    rwa [hz2] at this
  have hpos : Nat.card ↥(J ⊓ J') ≠ 0 := Nat.card_pos.ne'
  have h1 : 1 ≤ padicValNat 2 (Nat.card ↥(J ⊓ J')) :=
    (padicValNat_dvd_iff_le (p := 2) hpos).mp (by simpa using hdvd)
  have heq : padicValNat 2 (Nat.card ↥(J ⊓ J')) = 1 := le_antisymm h4.1 h1
  exact le_trivialOnQuot_of_commutator_le ((h4.2 heq).trans inf_le_right)

end Twins

section Triple

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem commute_pair {x a b : G} (ha : a * x = x * a) (hb : b * x = x * b) :
    (a * b) * x = x * (a * b) := by
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

structure Triple (Ω : Set (Subgroup G)) (z : G) (J₁ J₂ J₃ : Subgroup G) (v₁ v₂ v₃ : G)
    (R₁ R₂ R₃ B : Subgroup G) : Prop where
  mem₁ : J₁ ∈ Ω
  mem₂ : J₂ ∈ Ω
  mem₃ : J₃ ∈ Ω
  uniq₁ : IsUniqueInvolution J₁ z
  uniq₂ : IsUniqueInvolution J₂ z
  uniq₃ : IsUniqueInvolution J₃ z
  ne₁₂ : J₁ ≠ J₂
  ne₁₃ : J₁ ≠ J₃
  ne₂₃ : J₂ ≠ J₃
  syl₁ : IsSylow2In R₁ J₁
  syl₂ : IsSylow2In R₂ J₂
  syl₃ : IsSylow2In R₃ J₃
  v₁R : v₁ ∈ R₁
  v₂R : v₂ ∈ R₂
  v₃R : v₃ ∈ R₃
  cm : Cmt z v₁ v₂ v₃
  c₁₂ : Commutes R₁ R₂
  c₁₃ : Commutes R₁ R₃
  c₂₃ : Commutes R₂ R₃
  hB : IsElemAbelian 2 B
  hzB : z ∈ B
  hz1 : z ≠ 1
  h₁₂ : v₁ * v₂ ∈ B
  h₂₃ : v₂ * v₃ ∈ B
  hgen : B ≤ Subgroup.closure ({v₁ * v₂, z, v₂ * v₃} : Set G)

variable {z : G} {J₁ J₂ J₃ : Subgroup G} {v₁ v₂ v₃ : G} {R₁ R₂ R₃ B : Subgroup G}

omit [Finite G] in
theorem Triple.h₁₃ (hT : Triple Ω z J₁ J₂ J₃ v₁ v₂ v₃ R₁ R₂ R₃ B) : v₁ * v₃ ∈ B := by
  have h : v₁ * v₃ = z * ((v₁ * v₂) * (v₂ * v₃)) := by
    calc v₁ * v₃ = (z * z) * (v₁ * v₃) := by rw [hT.cm.z2, one_mul]
      _ = z * (z * (v₁ * v₃)) := by rw [mul_assoc]
      _ = z * ((v₁ * v₂) * (v₂ * v₃)) := by rw [hT.cm.rel]
  rw [h]
  exact B.mul_mem hT.hzB (B.mul_mem hT.h₁₂ hT.h₂₃)

omit [Finite G] in
theorem Triple.h₃₁ (hT : Triple Ω z J₁ J₂ J₃ v₁ v₂ v₃ R₁ R₂ R₃ B) : v₃ * v₁ ∈ B := by
  rw [← hT.cm.c₁₃]
  exact hT.h₁₃

omit [Finite G] in
theorem Triple.rot (hT : Triple Ω z J₁ J₂ J₃ v₁ v₂ v₃ R₁ R₂ R₃ B) :
    Triple Ω z J₂ J₃ J₁ v₂ v₃ v₁ R₂ R₃ R₁ B where
  mem₁ := hT.mem₂
  mem₂ := hT.mem₃
  mem₃ := hT.mem₁
  uniq₁ := hT.uniq₂
  uniq₂ := hT.uniq₃
  uniq₃ := hT.uniq₁
  ne₁₂ := hT.ne₂₃
  ne₁₃ := hT.ne₁₂.symm
  ne₂₃ := hT.ne₁₃.symm
  syl₁ := hT.syl₂
  syl₂ := hT.syl₃
  syl₃ := hT.syl₁
  v₁R := hT.v₂R
  v₂R := hT.v₃R
  v₃R := hT.v₁R
  cm := hT.cm.rot
  c₁₂ := hT.c₂₃
  c₁₃ := hT.c₁₂.symm
  c₂₃ := hT.c₁₃.symm
  hB := hT.hB
  hzB := hT.hzB
  hz1 := hT.hz1
  h₁₂ := hT.h₂₃
  h₂₃ := hT.h₃₁
  hgen := by
    refine hT.hgen.trans ((Subgroup.closure_le _).mpr ?_)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · have h : v₁ * v₂ = z * ((v₂ * v₃) * (v₃ * v₁)) := by
        calc v₁ * v₂ = (z * z) * (v₁ * v₂) := by rw [hT.cm.z2, one_mul]
          _ = z * (z * (v₁ * v₂)) := by rw [mul_assoc]
          _ = z * ((v₂ * v₃) * (v₃ * v₁)) := by rw [hT.cm.rel']
      rw [h]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

end Triple

section Hyp51

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {z : G} {J₁ J₂ J₃ : Subgroup G} {v₁ v₂ v₃ : G} {R₁ R₂ R₃ B : Subgroup G}

theorem Triple.hyp51At (hT : Triple Ω z J₁ J₂ J₃ v₁ v₂ v₃ R₁ R₂ R₃ B) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (hBelow : CITBelowU p f (Nat.card G))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) (hex : G2D4VertexExcl p f) (hres : TwinSqAlphaRows p) {c : G}
    (hc : c = v₁ * v₂ ∨ c = v₁ * v₂ * z) (hc1 : c ≠ 1) (hcz : c ≠ z) {M' : Subgroup G}
    (hM'Ω : M' ∈ Ω) (hM'u : IsUniqueInvolution M' z) (hM'₁ : M' ≠ J₁) (hM'₂ : M' ≠ J₂)
    (hM'₃ : M' ≠ J₃) : Hyp51At B c := by
  have cm := hT.cm
  have hcB : c ∈ B := by
    rcases hc with rfl | rfl
    · exact hT.h₁₂
    · exact B.mul_mem hT.h₁₂ hT.hzB
  have hcc : c * c = 1 := Lemma52Proof.mul_self_eq_one_of_mem hT.hB hcB
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hcc
  have hcomm_c : ∀ x : G, v₁ * x = x * v₁ → v₂ * x = x * v₂ → z * x = x * z → c * x = x * c := by
    intro x h1 h2 hz
    rcases hc with rfl | rfl
    · exact commute_pair h1 h2
    · exact commute_pair (commute_pair h1 h2) hz
  have hzcomm : ∀ x : G, v₁ * x = x * v₁ → z * x = x * z := by
    intro x h1
    calc z * x = v₁ * (v₁ * x) := by rw [← cm.s₁, mul_assoc]
      _ = v₁ * (x * v₁) := by rw [h1]
      _ = (v₁ * x) * v₁ := by rw [mul_assoc]
      _ = (x * v₁) * v₁ := by rw [h1]
      _ = x * z := by rw [mul_assoc, cm.s₁]
  have hR₃c : R₃ ≤ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : v₁ * x = x * v₁ := hT.c₁₃ v₁ hT.v₁R x hx
    have h2 : v₂ * x = x * v₂ := hT.c₂₃ v₂ hT.v₂R x hx
    exact (hcomm_c x h1 h2 (hzcomm x h1)).symm
  have hJ₃t : J₃ ∈ tqMembers Ω c :=
    ⟨hT.mem₃, (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hc2 hT.mem₃).mpr
      ⟨R₃, hT.syl₃, hR₃c⟩⟩
  have hMz : IsClassicalMember p f J₃ z := isClassicalMember_of_twin hΩ hT.mem₃ hT.uniq₃
  have hm : v₃ ∈ exactCore c J₃ :=
    ((isSylow2In_exactCore_iff hΩ hc2 hT.mem₃ hJ₃t.2).mpr ⟨hT.syl₃, hR₃c⟩).1 hT.v₃R
  have hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one (exists_noncomm_of_isClassicalMember hMz) hc1
  have hv₁M' : v₁ ∈ trivialOnQuot M' :=
    twin_le_trivialOnQuot hΩ hT.mem₁ hM'Ω (fun h => hM'₁ h.symm) hT.uniq₁ hM'u
      (hT.syl₁.1 hT.v₁R)
  have hv₂M' : v₂ ∈ trivialOnQuot M' :=
    twin_le_trivialOnQuot hΩ hT.mem₂ hM'Ω (fun h => hM'₂ h.symm) hT.uniq₂ hM'u
      (hT.syl₂.1 hT.v₂R)
  have hzM' : z ∈ trivialOnQuot M' :=
    twin_le_trivialOnQuot hΩ hT.mem₁ hM'Ω (fun h => hM'₁ h.symm) hT.uniq₁ hM'u hT.uniq₁.mem
  have hcM' : c ∈ trivialOnQuot M' := by
    rcases hc with rfl | rfl
    · exact Subgroup.mul_mem _ hv₁M' hv₂M'
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hv₁M' hv₂M') hzM'
  have hM't : M' ∈ tqMembers Ω c := ⟨hM'Ω, hcM'⟩
  have hM'z : IsClassicalMember p f M' z := isClassicalMember_of_twin hΩ hM'Ω hM'u
  have h12 : ∀ S : Subgroup G, c ∈ S → z ∈ S → v₁ * v₂ ∈ S := by
    intro S hcS hzS'
    rcases hc with rfl | rfl
    · exact hcS
    · have : v₁ * v₂ = (v₁ * v₂ * z) * z := by rw [mul_assoc, cm.z2, mul_one]
      rw [this]
      exact S.mul_mem hcS hzS'
  have hgen' : ∀ S : Subgroup G, v₁ * v₂ ∈ S → z ∈ S → v₂ * v₃ ∈ S → B ≤ S := by
    intro S h1 h2 h3
    refine hT.hgen.trans ((Subgroup.closure_le _).mpr ?_)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hc_v₁ : c * v₁ = v₁ * c := hcomm_c v₁ rfl cm.c₁₂.symm cm.zc₁
  have hBle₁ : B ≤ Subgroup.closure ({c, z, v₁ * v₃} : Set G) := by
    set S := Subgroup.closure ({c, z, v₁ * v₃} : Set G) with hS
    have hzS' : z ∈ S := Subgroup.subset_closure (by simp)
    have hcS : c ∈ S := Subgroup.subset_closure (by simp)
    have havS : v₁ * v₃ ∈ S := Subgroup.subset_closure (by simp)
    have h12S := h12 S hcS hzS'
    refine hgen' S h12S hzS' ?_
    have h : v₂ * v₃ = (v₁ * v₂) * (z * (v₁ * v₃)) := by
      calc v₂ * v₃ = ((v₁ * v₂) * (v₁ * v₂)) * (v₂ * v₃) := by rw [cm.sq_pair, one_mul]
        _ = (v₁ * v₂) * ((v₁ * v₂) * (v₂ * v₃)) := by rw [mul_assoc]
        _ = (v₁ * v₂) * (z * (v₁ * v₃)) := by rw [cm.rel]
    rw [h]
    exact S.mul_mem h12S (S.mul_mem hzS' havS)
  have hv₁J₃ : v₁ ∈ trivialOnQuot J₃ :=
    twin_le_trivialOnQuot hΩ hT.mem₁ hT.mem₃ hT.ne₁₃ hT.uniq₁ hT.uniq₃ (hT.syl₁.1 hT.v₁R)
  have hα : ∀ (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card),
      modOdd c (exactCore c J₃) ≤
        (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range →
      MovedByAll B c
        (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range →
      CFSG.IsComponent
        (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range →
        alphaOf (inducedImage
          (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range
          (modOdd c B)) = ⊥ := by
    intro D j hMj hmov hLc
    exact alpha_of_twinSq hp hq hΩ hex hA hres hc2 hT.hB hcB hc1 hT.hzB hT.hz1 hcz.symm
      hJ₃t hM't hMz hM'z hM'₃ (Subgroup.mem_centralizer_singleton_iff.mpr hc_v₁.symm) cm.s₁
      hv₁J₃ hv₁M' hm cm.s₃ hT.h₁₃ hBle₁ D j hMj hmov hLc
  exact FrameVertex.hyp51At_of_witness_alpha' hp hq hΩ.conjInvariant hΩ.classical hBelow hc2 hnc
    hT.hB hcB hc1 hT.hzB hT.hz1 hcz.symm hJ₃t hMz hα

end Hyp51

section Setting

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

omit [Finite G] in
theorem pow_mul_pow_self_of_mul_self {x : G} (hx : x * x = 1) (i : ℕ) : x ^ i * x ^ i = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, sq, hx, one_pow]

omit [Finite G] in
theorem mem_closure_three {x y w : G} (hxy : Commute x y) (hxw : Commute x w) (hyw : Commute y w)
    (hx : x * x = 1) (hy : y * y = 1) (hw : w * w = 1) {g : G}
    (hg : g ∈ Subgroup.closure ({x, y, w} : Set G)) :
    g = 1 ∨ g = x ∨ g = y ∨ g = w ∨ g = x * y ∨ g = x * w ∨ g = y * w ∨ g = x * y * w := by
  have key : ∃ i j k : ℕ, g = x ^ i * y ^ j * w ^ k := by
    induction hg using Subgroup.closure_induction with
    | mem u hu =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
    | one => exact ⟨0, 0, 0, by simp⟩
    | mul u v _ _ hu hv =>
      obtain ⟨i, j, k, rfl⟩ := hu
      obtain ⟨i', j', k', rfl⟩ := hv
      refine ⟨i + i', j + j', k + k', ?_⟩
      have h1 : Commute (y ^ j * w ^ k) (x ^ i') :=
        ((hxy.pow_pow i' j).symm).mul_left ((hxw.pow_pow i' k).symm)
      have h2 : Commute (w ^ k) (y ^ j') := (hyw.pow_pow j' k).symm
      calc x ^ i * y ^ j * w ^ k * (x ^ i' * y ^ j' * w ^ k') =
            x ^ i * ((y ^ j * w ^ k) * x ^ i') * y ^ j' * w ^ k' := by simp only [mul_assoc]
        _ = x ^ i * (x ^ i' * (y ^ j * w ^ k)) * y ^ j' * w ^ k' := by rw [h1.eq]
        _ = x ^ i * x ^ i' * y ^ j * (w ^ k * y ^ j') * w ^ k' := by simp only [mul_assoc]
        _ = x ^ i * x ^ i' * y ^ j * (y ^ j' * w ^ k) * w ^ k' := by rw [h2.eq]
        _ = x ^ (i + i') * y ^ (j + j') * w ^ (k + k') := by
          simp only [pow_add, mul_assoc]
    | inv u _ hu =>
      obtain ⟨i, j, k, rfl⟩ := hu
      refine ⟨i, j, k, ?_⟩
      have ex := inv_eq_of_mul_eq_one_right (pow_mul_pow_self_of_mul_self hx i)
      have ey := inv_eq_of_mul_eq_one_right (pow_mul_pow_self_of_mul_self hy j)
      have ez := inv_eq_of_mul_eq_one_right (pow_mul_pow_self_of_mul_self hw k)
      rw [mul_inv_rev, mul_inv_rev, ex, ey, ez]
      calc w ^ k * (y ^ j * x ^ i) = w ^ k * (x ^ i * y ^ j) := by
            rw [(hxy.pow_pow i j).eq]
        _ = (w ^ k * x ^ i) * y ^ j := by rw [mul_assoc]
        _ = (x ^ i * w ^ k) * y ^ j := by rw [(hxw.pow_pow i k).eq]
        _ = x ^ i * (w ^ k * y ^ j) := by rw [mul_assoc]
        _ = x ^ i * y ^ j * w ^ k := by rw [← (hyw.pow_pow j k).eq, mul_assoc]
  obtain ⟨i, j, k, rfl⟩ := key
  have hpow : ∀ {t : G}, t * t = 1 → ∀ n : ℕ, t ^ n = 1 ∨ t ^ n = t := fun {t} ht n => by
    rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · left
      rw [← two_mul, pow_mul, sq, ht, one_pow]
    · right
      rw [pow_succ, pow_mul, sq, ht, one_pow, one_mul]
  rcases hpow hx i with hi | hi <;> rcases hpow hy j with hj | hj <;>
    rcases hpow hw k with hk | hk <;> rw [hi, hj, hk] <;> simp

theorem comm₁₃ (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₃ = u₃ * u₁ :=
  T7B.comm_of_mul_self_eq_one h.sq₁ h.sq₃ h.hz.sq h.comm_z₁ (h.hB.2 _ h.mem_B_13)

theorem exists_sylow_triple (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    ∃ R R' R₃ : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ IsSylow2In R₃ K₃ ∧
      u₁ ∈ R ∧ u₂ ∈ R' ∧ u₃ ∈ R₃ ∧ Commutes R R' ∧ Commutes R R₃ ∧ Commutes R' R₃ := by
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hK : K ∈ Ω := h.stand.mem
  have hK' : K' ∈ Ω := h.hK'.1
  have hK₃ : K₃ ∈ Ω := h.hK₃.1
  have hz := h.hz
  have hz' := h.hzK'
  have hz₃ := h.hzK₃
  have hne : K' ≠ K := h.hne
  have hne₃ : K₃ ≠ K := h.hK₃K
  have hne₃' : K₃ ≠ K' := h.hK₃K'
  set Z₁ := Subgroup.zpowers u₁ with hZ₁
  set Z₂ := Subgroup.zpowers u₂ with hZ₂
  set Z₃ := Subgroup.zpowers u₃ with hZ₃
  have p₁ : IsPGroup 2 ↥Z₁ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₁.2
  have p₂ : IsPGroup 2 ↥Z₂ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₂.2
  have p₃ : IsPGroup 2 ↥Z₃ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₃.2
  have cm : ∀ {a b : G}, a * b = b * a → Commutes (Subgroup.zpowers a) (Subgroup.zpowers b) := by
    intro a b hab x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
  have c12 : Commutes Z₁ Z₂ := cm h.comm₁₂
  have c13 : Commutes Z₁ Z₃ := cm (comm₁₃ h)
  have c23 : Commutes Z₂ Z₃ := cm h.comm₂₃
  have hP12 : IsPGroup 2 ↥(Z₁ ⊔ Z₂) :=
    p₁.to_sup_of_normal_right' p₂ (T7A.le_normalizer_of_commutes c12.symm)
  have hP : IsPGroup 2 ↥((Z₁ ⊔ Z₂) ⊔ Z₃) :=
    hP12.to_sup_of_normal_right' p₃ (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  set P := (Z₁ ⊔ Z₂) ⊔ Z₃ with hPdef
  have hZ₁P : Z₁ ≤ P := le_sup_left.trans le_sup_left
  have hZ₂P : Z₂ ≤ P := le_sup_right.trans le_sup_left
  have hZ₃P : Z₃ ≤ P := le_sup_right
  have hz₁P : u₁ ∈ P := hZ₁P (Subgroup.mem_zpowers u₁)
  have hz₂P : u₂ ∈ P := hZ₂P (Subgroup.mem_zpowers u₂)
  have hz₃P : u₃ ∈ P := hZ₃P (Subgroup.mem_zpowers u₃)
  have nK₁ : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK' hne.symm hz hz'
  have nK₂ : K ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₃ hne₃.symm hz hz₃
  have nK₃ : K' ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₃ hne₃'.symm hz' hz₃
  have nK₄ : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK' hK hne hz' hz
  have nK₅ : K₃ ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK₃ hK hne₃ hz₃ hz
  have nK₆ : K₃ ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK₃ hK' hne₃' hz₃ hz'
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans Subgroup.le_normalizer)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans nK₄))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans nK₅)
  have hPK' : P ≤ Subgroup.normalizer (K' : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans nK₁)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans Subgroup.le_normalizer))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans nK₆)
  have hPK₃ : P ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans nK₂)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans nK₃))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans Subgroup.le_normalizer)
  obtain ⟨R, hR, hRfix⟩ := exists_sylow_normalized hP hPK
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix x hx)
  have hu₁R : u₁ ∈ R := T7B.mem_of_normalizes hR p₁ h.hu₁.1 (hRfix u₁ hz₁P)
  have hP₁ : IsPGroup 2 ↥(P ⊔ R) := hP.to_sup_of_normal_right' hR.2.1 hPR
  have hPR₁ : P ⊔ R ≤ Subgroup.normalizer (K' : Set G) := sup_le hPK' (hR.1.trans nK₁)
  obtain ⟨R', hR', hR'fix⟩ := exists_sylow_normalized hP₁ hPR₁
  have hPR' : P ⊔ R ≤ Subgroup.normalizer (R' : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix x hx)
  have hPle₁ : P ≤ P ⊔ R := le_sup_left
  have hu₂R' : u₂ ∈ R' := T7B.mem_of_normalizes hR' p₂ h.hu₂.1 (hR'fix u₂ (hPle₁ hz₂P))
  have hP₂ : IsPGroup 2 ↥((P ⊔ R) ⊔ R') := hP₁.to_sup_of_normal_right' hR'.2.1 hPR'
  have hPR₂ : (P ⊔ R) ⊔ R' ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (sup_le hPK₃ (hR.1.trans nK₂)) (hR'.1.trans nK₃)
  obtain ⟨R₃, hR₃, hR₃fix⟩ := exists_sylow_normalized hP₂ hPR₂
  have hPR₃ : (P ⊔ R) ⊔ R' ≤ Subgroup.normalizer (R₃ : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR₃fix x hx)
  have hPle₂ : P ⊔ R ≤ (P ⊔ R) ⊔ R' := le_sup_left
  have hu₃R₃ : u₃ ∈ R₃ :=
    T7B.mem_of_normalizes hR₃ p₃ h.hu₃.1 (hR₃fix u₃ (hPle₂ (hPle₁ hz₃P)))
  have hQ : IsPGroup 2 ↥(((P ⊔ R) ⊔ R') ⊔ R₃) := hP₂.to_sup_of_normal_right' hR₃.2.1 hPR₃
  have hRQ : R ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hR'Q : R' ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right.trans le_sup_left
  have hR₃Q : R₃ ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right
  refine ⟨R, R', R₃, hR, hR', hR₃, hu₁R, hu₂R', hu₃R₃, ?_, ?_, ?_⟩
  · exact hΩ.commutes_of_twin_of_isPGroup hK hK' hne.symm hz hz' hR.1 hR'.1
      (hQ.to_le (sup_le hRQ hR'Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK hK₃ hne₃.symm hz hz₃ hR.1 hR₃.1
      (hQ.to_le (sup_le hRQ hR₃Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK' hK₃ hne₃'.symm hz' hz₃ hR'.1 hR₃.1
      (hQ.to_le (sup_le hR'Q hR₃Q))


theorem exists_triple (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    ∃ R R' R₃ : Subgroup G, Triple Ω z K K' K₃ u₁ u₂ u₃ R R' R₃
      (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
  obtain ⟨R, R', R₃, hR, hR', hR₃, hu₁R, hu₂R', hu₃R₃, c12, c13, c23⟩ := exists_sylow_triple h
  exact ⟨R, R', R₃,
    { mem₁ := h.stand.mem
      mem₂ := h.hK'.1
      mem₃ := h.hK₃.1
      uniq₁ := h.hz
      uniq₂ := h.hzK'
      uniq₃ := h.hzK₃
      ne₁₂ := h.hne.symm
      ne₁₃ := h.hK₃K.symm
      ne₂₃ := h.hK₃K'.symm
      syl₁ := hR
      syl₂ := hR'
      syl₃ := hR₃
      v₁R := hu₁R
      v₂R := hu₂R'
      v₃R := hu₃R₃
      cm := ⟨h.sq₁, h.sq₂, h.sq₃, h.hz.sq, h.comm₁₂, comm₁₃ h, h.comm₂₃⟩
      c₁₂ := c12
      c₁₃ := c13
      c₂₃ := c23
      hB := h.isElemAbelian_B
      hzB := T7B.mem_closure_snd
      hz1 := h.hz.ne_one
      h₁₂ := T7B.mem_closure_fst
      h₂₃ := T7B.mem_closure_thd
      hgen := le_rfl }⟩

end Setting

end T7J

section Residual

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Hyp22Hyp51uV3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃) →
      ∀ c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G), c ≠ 1 → c ≠ z →
        Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) c

@[expose] def Hyp22FourthTwin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      ∃ K₄ ∈ twinSet Ω K, K₄ ≠ K ∧ K₄ ≠ K' ∧ K₄ ≠ K₃

variable {p f}

theorem hyp22Hyp51uV3_of_fourthTwin (h4 : Hyp22FourthTwin p f) : Hyp22Hyp51uV3 p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h hV c _ _ _
  obtain ⟨K₄, hK₄, h1, h2, h3⟩ := h4 G Ω K K' K₃ z u₁ u₂ u₃ h
  rcases hV K₄ hK₄ with h' | h' | h'
  · exact absurd h' h1
  · exact absurd h' h2
  · exact absurd h' h3

theorem hyp22Hyp51u_of_residuals (hres : TwinSqAlphaRows p) (hV3 : Hyp22Hyp51uV3 p f) :
    Hyp22Hyp51u p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h c hc hc1 hcz
  by_cases hV : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃
  · exact hV3 G Ω K K' K₃ z u₁ u₂ u₃ h hV c hc hc1 hcz
  · push Not at hV
    obtain ⟨K₄, hK₄, hK₄K, hK₄K', hK₄K₃⟩ := hV
    obtain ⟨R, R', R₃, hT⟩ := T7J.exists_triple h
    have hq : 5 ≤ p ^ f := h.stand.five
    have hp : p ≠ 2 := h.stand.odd
    have hΩ : HypOmegaMod p f Ω := h.stand.hyp
    have hBelow : CITBelowU p f (Nat.card G) := h.stand.below f hq
    have hA : ∀ M ∈ Ω, AEmpty Ω M := h.stand.aEmpty
    have hex : G2D4VertexExcl p f := g2d4VertexExcl_proved
    have hK₄u : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet h.hz hK₄
    have cm := hT.cm
    have hcm := T7J.mem_closure_three cm.commute_xz cm.commute_xw cm.commute_wz.symm cm.sq_pair
      cm.z2 cm.rot.sq_pair hc
    rcases hcm with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · exact absurd h1 hc1
    · exact hT.hyp51At hp hq hΩ hBelow hA hex hres (Or.inl h2) hc1 hcz hK₄.1 hK₄u hK₄K hK₄K'
        hK₄K₃
    · exact absurd h3 hcz
    · exact hT.rot.hyp51At hp hq hΩ hBelow hA hex hres (Or.inl h4) hc1 hcz hK₄.1 hK₄u hK₄K'
        hK₄K₃ hK₄K
    · exact hT.hyp51At hp hq hΩ hBelow hA hex hres (Or.inr h5) hc1 hcz hK₄.1 hK₄u hK₄K hK₄K'
        hK₄K₃
    · exact hT.rot.rot.hyp51At hp hq hΩ hBelow hA hex hres (Or.inr (h6.trans cm.eq_xw)) hc1 hcz
        hK₄.1 hK₄u hK₄K₃ hK₄K hK₄K'
    · exact hT.rot.hyp51At hp hq hΩ hBelow hA hex hres (Or.inr (h7.trans cm.zc₂₃)) hc1 hcz
        hK₄.1 hK₄u hK₄K' hK₄K₃ hK₄K
    · exact hT.rot.rot.hyp51At hp hq hΩ hBelow hA hex hres (Or.inl (h8.trans cm.eq_xyw)) hc1 hcz
        hK₄.1 hK₄u hK₄K₃ hK₄K hK₄K'

theorem hyp22Hyp51u_of_fourthTwin (hres : TwinSqAlphaRows p) (h4 : Hyp22FourthTwin p f) :
    Hyp22Hyp51u p f :=
  hyp22Hyp51u_of_residuals hres (hyp22Hyp51uV3_of_fourthTwin h4)

end Residual

end CFSG.ClassicalInvolution.Asc77
