module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L55Key
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOverlap
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Tools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingDefs

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding (relStronglyClosed overlapClosure)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsSemidihedralTwoGroup)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Lemma34Trichotomy (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (S : Sylow 2 G) (A₁ A₂ : Subgroup G), A₁ ≤ S → A₂ ≤ S → ⁅A₁, A₂⁆ = ⊥ →
    2 ≤ CFSG.Open.pRank 2 A₁ → 2 ≤ CFSG.Open.pRank 2 A₂ →
    relStronglyClosed (overlapClosure A₁ A₂) ((A₁ : Set G) ∪ A₂) (overlapClosure A₁ A₂ ⊓ S) →
    relStronglyClosed ⊤ ((A₁ : Set G) ∪ A₂) (S ⊓ Subgroup.normalizer (A₁ : Set G)) →
    relStronglyClosed ⊤ ((A₁ : Set G) ∪ A₂) (S ⊓ Subgroup.normalizer (A₂ : Set G)) →
    overlapClosure A₁ A₂ = ⊤ ∨ A₁ ≤ A₂ ∨ A₂ ≤ A₁ ∨
      ((∃ g : G, rightConjugate A₁ g = A₂) ∧
        (IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁) ∧
        Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2)

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem fourGroupMeet_of_trichotomy (hA : FooteTheoremA) {z₀ : G} (hz₀ : ZData J z₀)
    (hT : TwoOrbit M J) (htri : Lemma34Trichotomy G) : FourGroupMeet M J := by
  classical
  by_contra hNF
  obtain ⟨J', hJ'ne, hJ'⟩ := hT
  obtain ⟨m₀, hm₀, hm₀ne⟩ := c.exists_conj_ne
  have hJ'eq : rightConjugate J m₀ = J' := (hJ' m₀ hm₀).resolve_left hm₀ne
  subst hJ'eq
  set J₂ := rightConjugate J m₀ with hJ₂
  have hJorb : ConjIn M J J := ⟨1, M.one_mem, (rightConjugate_one J).symm⟩
  have hJ₂orb : ConjIn M J J₂ := ⟨m₀, hm₀, rfl⟩
  have c₂ : CE G M J₂ := c.conj hm₀
  have hcomm : ⁅J, J₂⁆ = ⊥ := c.commutator_conj_eq_bot hm₀ hm₀ne
  have hcomm' : ⁅J₂, J⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcomm
  have hJC : J ≤ Subgroup.centralizer (J₂ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hUC : blockU J ≤ Subgroup.centralizer (blockU J₂ : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_iff.1 (hJC (blockU_le J hu)) v (blockU_le J₂ hv)
  have hp : IsPGroup 2 ↥(blockU J ⊔ blockU J₂) :=
    c.block.isPGroup_blockU.to_sup_of_normal_right' c₂.block.isPGroup_blockU
      (hUC.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hU₁ : blockU J ≤ S := le_sup_left.trans hS
  have hU₂ : blockU J₂ ≤ S := le_sup_right.trans hS
  have hSp : IsPGroup 2 (S : Subgroup G) := S.2
  have horb : ∀ {X : Subgroup G}, ConjIn M J X → ∀ y ∈ M,
      rightConjugate X y = J ∨ rightConjugate X y = J₂ := by
    rintro X ⟨m, hm, rfl⟩ y hy
    rw [rightConjugate_mul]
    exact hJ' (m * y) (M.mul_mem hm hy)
  have hSCM : ∀ a ∈ ((J ⊓ S : Subgroup G) : Set G) ∪ ((J₂ ⊓ S : Subgroup G) : Set G),
      ∀ y ∈ M, y⁻¹ * a * y ∈ (S : Subgroup G) →
        y⁻¹ * a * y ∈ ((J ⊓ S : Subgroup G) : Set G) ∪ ((J₂ ⊓ S : Subgroup G) : Set G) := by
    intro a ha y hy hyS
    have key : ∀ X : Subgroup G, ConjIn M J X → a ∈ X →
        y⁻¹ * a * y ∈ J ⊓ S ∨ y⁻¹ * a * y ∈ J₂ ⊓ S := by
      intro X hX haX
      have hmem : y⁻¹ * a * y ∈ rightConjugate X y := by
        rw [mem_rightConjugate_iff]
        have e : y * (y⁻¹ * a * y) * y⁻¹ = a := by group
        rw [e]
        exact haX
      rcases horb hX y hy with h | h
      · exact Or.inl (Subgroup.mem_inf.2 ⟨h ▸ hmem, hyS⟩)
      · exact Or.inr (Subgroup.mem_inf.2 ⟨h ▸ hmem, hyS⟩)
    rcases ha with ha | ha
    · exact key J hJorb (Subgroup.mem_inf.1 ha).1
    · exact key J₂ hJ₂orb (Subgroup.mem_inf.1 ha).1
  have hOver : ∀ X K : Subgroup G, ConjIn M J X → ConjIn M J K → ∀ g : G,
      rightConjugate (K ⊓ S : Subgroup G) g ⊓ (X ⊓ S : Subgroup G) ≠ ⊥ → g ∈ M := by
    intro X K hX hK g hne
    by_contra hg
    obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have htmem := t.2
    have htS : (t : G) ∈ S := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 htmem).2).2
    have h2 : ∃ n : ℕ, (t : G) ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hSp ⟨(t : G), htS⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    obtain ⟨i, hi, hi1, hi2⟩ := exists_involution_mem_zpowers h2
      (fun h => ht1 (Subtype.ext h))
    have hi' := (Subgroup.zpowers_le.2 htmem) hi
    have hiX : i ∈ X := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hi').2).1
    have hiK : i ∈ rightConjugate K g :=
      Subgroup.map_mono (inf_le_left : K ⊓ S ≤ K) (Subgroup.mem_inf.1 hi').1
    exact hNF (c.fourGroupMeet_of_involution hA hz₀ hX hK hi2 hi1 (Subgroup.le_normalizer hiX)
      hiK hg)
  have hHM : overlapClosure (J ⊓ S : Subgroup G) (J₂ ⊓ S : Subgroup G) ≤ M := by
    refine (Subgroup.closure_le M).2 ?_
    rintro g ⟨X, hX, Y, hY, hne⟩
    have hconj : ∀ Z : Subgroup G, Z ∈ ({J ⊓ S, J₂ ⊓ S} : Set (Subgroup G)) →
        ∃ W : Subgroup G, ConjIn M J W ∧ Z = W ⊓ S := by
      intro Z hZ
      rcases hZ with rfl | hZ
      · exact ⟨J, hJorb, rfl⟩
      · rw [Set.mem_singleton_iff] at hZ
        exact ⟨J₂, hJ₂orb, hZ⟩
    obtain ⟨W₁, hW₁, rfl⟩ := hconj X hX
    obtain ⟨W₂, hW₂, rfl⟩ := hconj Y hY
    exact hOver W₂ W₁ hW₂ hW₁ g hne
  have hcl : relStronglyClosed (overlapClosure (J ⊓ S : Subgroup G) (J₂ ⊓ S : Subgroup G))
      (((J ⊓ S : Subgroup G) : Set G) ∪ ((J₂ ⊓ S : Subgroup G) : Set G))
      (overlapClosure (J ⊓ S : Subgroup G) (J₂ ⊓ S : Subgroup G) ⊓ S) := by
    intro a ha y hy hyS
    exact hSCM a ha y (hHM hy) (Subgroup.mem_inf.1 hyS).2
  have hNorm : ∀ X : Subgroup G, ConjIn M J X → blockU X ≤ S →
      ∀ a ∈ ((J ⊓ S : Subgroup G) : Set G) ∪ ((J₂ ⊓ S : Subgroup G) : Set G), ∀ y : G,
        y⁻¹ * a * y ∈ (S ⊓ Subgroup.normalizer ((X ⊓ S : Subgroup G) : Set G) : Subgroup G) →
        y⁻¹ * a * y ∈ ((J ⊓ S : Subgroup G) : Set G) ∪ ((J₂ ⊓ S : Subgroup G) : Set G) := by
    intro X hX hUX a ha y hyb
    by_cases hyM : y ∈ M
    · exact hSCM a ha y hyM (Subgroup.mem_inf.1 hyb).1
    by_cases ha1 : a = 1
    · left
      subst ha1
      simp
    obtain ⟨Xk, hXk, haX, haS⟩ : ∃ Xk : Subgroup G, ConjIn M J Xk ∧ a ∈ Xk ∧ a ∈ S := by
      rcases ha with ha | ha
      · exact ⟨J, hJorb, (Subgroup.mem_inf.1 ha).1, (Subgroup.mem_inf.1 ha).2⟩
      · exact ⟨J₂, hJ₂orb, (Subgroup.mem_inf.1 ha).1, (Subgroup.mem_inf.1 ha).2⟩
    have ha2 : ∃ n : ℕ, a ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hSp ⟨a, haS⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    obtain ⟨i, hi, hi1, hi2⟩ := exists_involution_mem_zpowers ha2 ha1
    have hbi : y⁻¹ * i * y ∈ Subgroup.zpowers (y⁻¹ * a * y) := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hi
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have := conj_zpow (a := y⁻¹) (b := a) (i := k)
      simpa using this
    have hbS' := (Subgroup.zpowers_le.2 hyb) hbi
    have hbS : y⁻¹ * i * y ∈ S := (Subgroup.mem_inf.1 hbS').1
    have hbN : y⁻¹ * i * y ∈ Subgroup.normalizer ((X ⊓ S : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.1 hbS').2
    have hbM : y⁻¹ * i * y ∈ M := c.mem_of_normalizes_inf hX hSp hUX hbS hbN
    have hbN' : y⁻¹ * i * y ∈ Subgroup.normalizer (X : Set G) :=
      c.mem_normalizer_of_mem hX hUX hbM hbN
    have hb2 : (y⁻¹ * i * y) * (y⁻¹ * i * y) = 1 := by
      calc (y⁻¹ * i * y) * (y⁻¹ * i * y) = y⁻¹ * (i * i) * y := by group
        _ = 1 := by rw [hi2]; group
    have hb1 : y⁻¹ * i * y ≠ 1 := fun h => hi1 (by
      have : i = y * (y⁻¹ * i * y) * y⁻¹ := by group
      rw [this, h]
      group)
    have hiK : i ∈ Xk := Subgroup.zpowers_le.2 haX hi
    have hbK : y⁻¹ * i * y ∈ rightConjugate Xk y := by
      rw [mem_rightConjugate_iff]
      have e : y * (y⁻¹ * i * y) * y⁻¹ = i := by group
      rw [e]
      exact hiK
    exact absurd (c.fourGroupMeet_of_involution hA hz₀ hX hXk hb2 hb1 hbN' hbK hyM) hNF
  have hcl₁ : relStronglyClosed ⊤
      (((J ⊓ S : Subgroup G) : Set G) ∪ ((J₂ ⊓ S : Subgroup G) : Set G))
      (S ⊓ Subgroup.normalizer ((J ⊓ S : Subgroup G) : Set G)) :=
    fun a ha y _ hyb => hNorm J hJorb hU₁ a ha y hyb
  have hcl₂ : relStronglyClosed ⊤
      (((J ⊓ S : Subgroup G) : Set G) ∪ ((J₂ ⊓ S : Subgroup G) : Set G))
      (S ⊓ Subgroup.normalizer ((J₂ ⊓ S : Subgroup G) : Set G)) :=
    fun a ha y _ hyb => hNorm J₂ hJ₂orb hU₂ a ha y hyb
  have hrank : ∀ X : Subgroup G, ConjIn M J X → blockU X ≤ S →
      2 ≤ CFSG.Open.pRank 2 (X ⊓ S : Subgroup G) := by
    intro X hX hUX
    have cX := c.orb_ce hX
    have hE := cX.block.isElemAbelian_blockU
    have h8 := cX.block.eight_le_card_blockU
    obtain ⟨n, hn⟩ := cX.block.isPGroup_blockU.exists_card_eq
    have hn3 : 3 ≤ n := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have := le_pRank_of_isElemAbelian (R := X ⊓ S) (le_inf (blockU_le X) hUX) hE hn
    omega
  have hc : ⁅J ⊓ (S : Subgroup G), J₂ ⊓ (S : Subgroup G)⁆ = ⊥ :=
    le_bot_iff.1 (hcomm ▸ Subgroup.commutator_mono inf_le_left inf_le_left)
  rcases htri S (J ⊓ S) (J₂ ⊓ S) inf_le_right inf_le_right hc (hrank J hJorb hU₁)
      (hrank J₂ hJ₂orb hU₂) hcl hcl₁ hcl₂ with h | h | h | ⟨-, hd, -⟩
  ·
    apply c.ne_top
    rw [eq_top_iff]
    intro x _
    apply hHM
    rw [h]
    exact Subgroup.mem_top x
  ·
    have hUJ₂ : blockU J ≤ J₂ := fun u hu =>
      (Subgroup.mem_inf.1 (h (Subgroup.mem_inf.2 ⟨blockU_le J hu, hU₁ hu⟩))).1
    have h1 : ⁅blockU J, J⁆ = ⊥ := le_bot_iff.1 (hcomm' ▸ Subgroup.commutator_mono hUJ₂ le_rfl)
    rw [c.block.blockU_stable] at h1
    exact blockU_ne_bot_of_short c.block.short h1
  ·
    have hUJ : blockU J₂ ≤ J := fun u hu =>
      (Subgroup.mem_inf.1 (h (Subgroup.mem_inf.2 ⟨blockU_le J₂ hu, hU₂ hu⟩))).1
    have h1 : ⁅blockU J₂, J₂⁆ = ⊥ := le_bot_iff.1 (hcomm ▸ Subgroup.commutator_mono hUJ le_rfl)
    rw [c₂.block.blockU_stable] at h1
    exact blockU_ne_bot_of_short c₂.block.short h1
  ·
    have h4 := CFSG.ComponentClassification.Foote5.card_le_four_of_dihedral_or_semidihedral hd
      (le_inf (blockU_le J) hU₁ : blockU J ≤ J ⊓ S) (fun x hx => c.block.blockU_sq_eq_one x hx)
    have h8 := c.block.eight_le_card_blockU
    omega

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
