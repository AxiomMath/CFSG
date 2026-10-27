module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DComp
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DSylow
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DCal

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Conj

variable {B K : Subgroup G} {y : G}

theorem y_pow_three {B : Subgroup G} (hB : IsElemAbelian 3 B) {y : G} (hy : y ∈ B) : y ^ 3 = 1 :=
  hB.2 y hy

theorem three_conjugates (hB : IsElemAbelian 3 B) (hy : y ∈ B)
    (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3) :
    K ≠ GLBConj y K ∧ K ≠ GLBConj y (GLBConj y K) ∧ GLBConj y K ≠ GLBConj y (GLBConj y K) ∧
      ∀ g ∈ B, GLBConj g K = K ∨ GLBConj g K = GLBConj y K ∨
        GLBConj g K = GLBConj y (GLBConj y K) := by
  have hy3 : y ^ 3 = 1 := y_pow_three hB hy
  have hcomm : IsMulCommutative B := hB.1
  have hne1 : K ≠ GLBConj y K := by
    intro h
    exact hyN (mem_normalizer_iff_gLBConj_eq.2 h.symm)
  have hyy : y * y ∈ B := B.mul_mem hy hy
  have hne2 : K ≠ GLBConj y (GLBConj y K) := by
    intro h
    rw [gLBConj_gLBConj] at h
    have : y * y ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_gLBConj_eq.2 h.symm
    have hyi : y = (y * y)⁻¹ := by
      have : y * y * y = 1 := by simpa [pow_succ] using hy3
      exact (inv_eq_of_mul_eq_one_right this).symm
    exact hyN (by rw [hyi]; exact Subgroup.inv_mem _ this)
  have hne3 : GLBConj y K ≠ GLBConj y (GLBConj y K) := by
    intro h
    apply hne1
    have := congrArg (GLBConj y⁻¹) h
    rwa [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at this
  refine ⟨hne1, hne2, hne3, ?_⟩
  obtain ⟨L₂, L₃, ⟨g₂, hg₂, hL₂⟩, ⟨g₃, hg₃, hL₃⟩, h12, h13, h23, hall⟩ :=
    exists_three_conjugates hcomm h3
  intro g hg
  have hyK : GLBConj y K = L₂ ∨ GLBConj y K = L₃ := by
    rcases hall (GLBConj y K) ⟨y, hy, rfl⟩ with h | h | h
    · exact absurd h.symm hne1
    · exact Or.inl h
    · exact Or.inr h
  have hyyK : GLBConj y (GLBConj y K) = L₂ ∨ GLBConj y (GLBConj y K) = L₃ := by
    rcases hall (GLBConj y (GLBConj y K)) ⟨y * y, hyy, by rw [gLBConj_gLBConj]⟩ with h | h | h
    · exact absurd h.symm hne2
    · exact Or.inl h
    · exact Or.inr h
  rcases hall (GLBConj g K) ⟨g, hg, rfl⟩ with h | h | h
  · exact Or.inl h
  · rcases hyK with h' | h' <;> rcases hyyK with h'' | h''
    · exact absurd (h'.trans h''.symm) hne3
    · exact Or.inr (Or.inl (h.trans h'.symm))
    · exact Or.inr (Or.inr (h.trans h''.symm))
    · exact absurd (h'.trans h''.symm) hne3
  · rcases hyK with h' | h' <;> rcases hyyK with h'' | h''
    · exact absurd (h'.trans h''.symm) hne3
    · exact Or.inr (Or.inr (h.trans h''.symm))
    · exact Or.inr (Or.inl (h.trans h'.symm))
    · exact absurd (h'.trans h''.symm) hne3

end Conj


theorem bClosure_conj_le {B L : Subgroup G} {g : G} (hg : g ∈ B) :
    GLBConj g (bClosure B L) ≤ bClosure B L := by
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  unfold bClosure
  refine iSup₂_le fun b hb => ?_
  intro z hz
  rw [Subgroup.mem_comap]
  have e : (MulAut.conj g⁻¹).toMonoidHom z = g⁻¹ * z * g := by
    simp
  rw [e]
  have hm : g⁻¹ * z * g ∈ GLBConj (b * g) L := by
    rw [mem_gLBConj]
    have e2 : b * g * (g⁻¹ * z * g) * (b * g)⁻¹ = b * z * b⁻¹ := by group
    rw [e2]
    exact mem_gLBConj.1 hz
  exact (le_iSup₂ (f := fun (c : G) (_ : c ∈ B) => GLBConj c L) (b * g)
    (B.mul_mem hb hg)) hm

theorem bClosure_conj_eq {B L : Subgroup G} {g : G} (hg : g ∈ B) :
    GLBConj g (bClosure B L) = bClosure B L := by
  refine le_antisymm (bClosure_conj_le hg) ?_
  have h0 : GLBConj g⁻¹ (bClosure B L) ≤ bClosure B L :=
    bClosure_conj_le (B.inv_mem hg)
  have h1 : GLBConj g (GLBConj g⁻¹ (bClosure B L)) ≤ GLBConj g (bClosure B L) :=
    gLBConj_mono g h0
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h1

theorem le_normalizer_bClosure (B L : Subgroup G) :
    B ≤ Subgroup.normalizer (bClosure B L : Set G) := fun g hg =>
  mem_normalizer_iff_gLBConj_eq.2 (bClosure_conj_eq hg)

theorem le_bClosure_self {B : Subgroup G} (L : Subgroup G) : L ≤ bClosure B L := by
  intro z hz
  have : z ∈ GLBConj (1 : G) L := by rw [gLBConj_one]; exact hz
  exact (le_iSup₂ (f := fun (c : G) (_ : c ∈ B) => GLBConj c L) 1 B.one_mem) this

section A

variable {X B K : Subgroup G} {y : G}

theorem bClosure_eq_three (hB : IsElemAbelian 3 B) (hy : y ∈ B)
    (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3) :
    bClosure B K = K ⊔ GLBConj y K ⊔ GLBConj y (GLBConj y K) := by
  obtain ⟨-, -, -, hall⟩ := three_conjugates hB hy hyN h3
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rcases hall g hg with h | h | h <;> rw [h]
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  · refine sup_le (sup_le (le_bClosure_self K) ?_) ?_
    · intro z hz
      exact (le_iSup₂ (f := fun (c : G) (_ : c ∈ B) => GLBConj c K) y hy) hz
    · intro z hz
      rw [gLBConj_gLBConj] at hz
      exact (le_iSup₂ (f := fun (c : G) (_ : c ∈ B) => GLBConj c K) (y * y) (B.mul_mem hy hy)) hz

theorem phase1_comps (hK : GLAPComponent 3 X K) (hBX : B ≤ X) (hy : y ∈ B) :
    GLAPComponent 3 X (GLBConj y K) ∧ GLAPComponent 3 X (GLBConj y (GLBConj y K)) := by
  have h2 := comp_conj hK (hBX hy)
  exact ⟨h2, comp_conj h2 (hBX hy)⟩

end A


theorem coprime_card_core (p : ℕ) (X : Subgroup G) : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p X)) := by
  have := coprime_card_gLAPPrimeCore_aux p ↥X
  unfold GLAPPrimeCoreOf
  rwa [Subgroup.card_map_of_injective X.subtype_injective]

theorem pgroup_inf_core_eq_bot {p : ℕ} [hp : Fact p.Prime] {R : Subgroup G} (X : Subgroup G)
    (hR : IsPGroup p ↥R) : R ⊓ GLAPPrimeCoreOf p X = ⊥ := by
  have hd := Subgroup.disjoint_of_coprime_natCard (H := R) (K := GLAPPrimeCoreOf p X) (by
    obtain ⟨k, hk⟩ := exists_card_eq_pow hR
    rw [hk]
    exact Nat.Coprime.pow_left k (coprime_card_core p X))
  exact hd.eq_bot

section Q

variable {X B K : Subgroup G} {y : G}

theorem comm_of_inf {R Ki Kj : Subgroup G} (hR : IsPGroup 3 ↥R) (hKi : GLAPComponent 3 X Ki)
    (hKj : GLAPComponent 3 X Kj) (hne : Ki ≠ Kj) {r s : G} (hr : r ∈ R ⊓ Ki) (hs : s ∈ R ⊓ Kj) :
    r * s = s * r := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : ⁅r, s⁆ ∈ GLAPPrimeCoreOf 3 X :=
    commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hKi hKj hne
      (Subgroup.commutator_mem_commutator hr.2 hs.2)
  have h2 : ⁅r, s⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hr.1 hs.1) (R.inv_mem hr.1)) (R.inv_mem hs.1)
  have h3 : ⁅r, s⁆ ∈ R ⊓ GLAPPrimeCoreOf 3 X := ⟨h2, h1⟩
  rw [pgroup_inf_core_eq_bot X hR, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h3

end Q


section Q2

variable {X B K : Subgroup G} {y : G}

theorem mem_normalizer_sup {A C : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hC : g ∈ Subgroup.normalizer (C : Set G)) : g ∈ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hA hC ⊢
  have : GLBConj g (A ⊔ C) = GLBConj g A ⊔ GLBConj g C := by
    unfold GLBConj; exact Subgroup.map_sup _ _ _
  rw [this, hA, hC]

theorem cj_inv_inf {R K : Subgroup G} (hy : y ∈ Subgroup.normalizer (R : Set G)) :
    cj y⁻¹ (R ⊓ K) = R ⊓ GLBConj y K := by
  ext z
  rw [mem_cj, Subgroup.mem_inf, Subgroup.mem_inf, mem_gLBConj, inv_inv]
  have := Subgroup.mem_normalizer_iff.1 hy z
  rw [← this]

theorem phase1_sylow (hB : IsElemAbelian 3 B) (hBX : B ≤ X) (hK : GLAPComponent 3 X K)
    (hy : y ∈ B) (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3)
    {R : Subgroup G} (hRle : R ≤ bClosure B K) (hRp : IsPGroup 3 ↥R)
    (hRc : Nat.card R = 3 ^ (Nat.card ↥(bClosure B K)).factorization 3)
    (hRB : B ≤ Subgroup.normalizer (R : Set G)) :
    Nat.card ↥(R ⊓ K) = 3 ^ (Nat.card K).factorization 3 ∧
    Nat.card ↥(R ⊓ GLBConj y K) = 3 ^ (Nat.card ↥(GLBConj y K)).factorization 3 ∧
    Nat.card ↥(R ⊓ GLBConj y (GLBConj y K)) =
      3 ^ (Nat.card ↥(GLBConj y (GLBConj y K))).factorization 3 ∧
    (∀ r ∈ R ⊓ K, ∀ s ∈ R ⊓ GLBConj y K, r * s = s * r) ∧
    (∀ r ∈ R ⊓ K, ∀ s ∈ R ⊓ GLBConj y (GLBConj y K), r * s = s * r) ∧
    (∀ r ∈ R ⊓ GLBConj y K, ∀ s ∈ R ⊓ GLBConj y (GLBConj y K), r * s = s * r) ∧
    R = (R ⊓ K) ⊔ (R ⊓ GLBConj y K) ⊔ (R ⊓ GLBConj y (GLBConj y K)) := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hne1, hne2, hne3, -⟩ := three_conjugates hB hy hyN h3
  obtain ⟨hK2, hK3⟩ := phase1_comps hK hBX hy
  have hcl := bClosure_eq_three hB hy hyN h3
  have n12 : GLBConj y K ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_ne hK2 hK hne1.symm
  have n13 : GLBConj y (GLBConj y K) ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_ne hK3 hK hne2.symm
  have n21 : K ≤ Subgroup.normalizer ((GLBConj y K : Subgroup G) : Set G) :=
    le_normalizer_of_ne hK hK2 hne1
  have n23 : GLBConj y (GLBConj y K) ≤ Subgroup.normalizer ((GLBConj y K : Subgroup G) : Set G) :=
    le_normalizer_of_ne hK3 hK2 hne3.symm
  have n31 : K ≤ Subgroup.normalizer ((GLBConj y (GLBConj y K) : Subgroup G) : Set G) :=
    le_normalizer_of_ne hK hK3 hne2
  have n32 : GLBConj y K ≤ Subgroup.normalizer ((GLBConj y (GLBConj y K) : Subgroup G) : Set G) :=
    le_normalizer_of_ne hK2 hK3 hne3
  have hstar1 : bClosure B K ≤ Subgroup.normalizer (K : Set G) := by
    rw [hcl]; exact sup_le (sup_le Subgroup.le_normalizer n12) n13
  have hstar2 : bClosure B K ≤ Subgroup.normalizer ((GLBConj y K : Subgroup G) : Set G) := by
    rw [hcl]; exact sup_le (sup_le n21 Subgroup.le_normalizer) n23
  have hstar3 : bClosure B K ≤
      Subgroup.normalizer ((GLBConj y (GLBConj y K) : Subgroup G) : Set G) := by
    rw [hcl]; exact sup_le (sup_le n31 n32) Subgroup.le_normalizer
  have hK1s : K ≤ bClosure B K := le_bClosure_self K
  have hK2s : GLBConj y K ≤ bClosure B K := by rw [hcl]; exact le_sup_right.trans le_sup_left
  have hK3s : GLBConj y (GLBConj y K) ≤ bClosure B K := by rw [hcl]; exact le_sup_right
  have c1 := card_inf_sylow hstar1 hK1s hRle hRp hRc
  have c2 := card_inf_sylow hstar2 hK2s hRle hRp hRc
  have c3 := card_inf_sylow hstar3 hK3s hRle hRp hRc
  have hRp1 : IsPGroup 3 ↥(R ⊓ K) := hRp.to_inf_left
  have hRp2 : IsPGroup 3 ↥(R ⊓ GLBConj y K) := hRp.to_inf_left
  have hRp3 : IsPGroup 3 ↥(R ⊓ GLBConj y (GLBConj y K)) := hRp.to_inf_left
  have cm12 := fun r hr s hs => comm_of_inf hRp hK hK2 hne1 (r := r) (s := s) hr hs
  have cm13 := fun r hr s hs => comm_of_inf hRp hK hK3 hne2 (r := r) (s := s) hr hs
  have cm23 := fun r hr s hs => comm_of_inf hRp hK2 hK3 hne3 (r := r) (s := s) hr hs
  refine ⟨c1, c2, c3, cm12, cm13, cm23, ?_⟩
  have hs12 := card_sup_sylow (p := 3) (M₁ := K) (M₂ := GLBConj y K) (S := R ⊓ K)
    (T := R ⊓ GLBConj y K) n12 n21 inf_le_right inf_le_right hRp1 hRp2 c1 c2 cm12
  have hK12n : K ⊔ GLBConj y K ≤ Subgroup.normalizer ((GLBConj y (GLBConj y K) : Subgroup G) : Set G) :=
    sup_le n31 n32
  have hK3n : GLBConj y (GLBConj y K) ≤
      Subgroup.normalizer ((K ⊔ GLBConj y K : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_sup (n13 hg) (n23 hg)
  have hcomm12_3 : ∀ s ∈ (R ⊓ K) ⊔ (R ⊓ GLBConj y K), ∀ t ∈ R ⊓ GLBConj y (GLBConj y K),
      s * t = t * s := by
    intro s hs t ht
    have : (R ⊓ K) ⊔ (R ⊓ GLBConj y K) ≤ Subgroup.centralizer ((R ⊓ GLBConj y (GLBConj y K) : Subgroup G) : Set G) := by
      refine sup_le (fun r hr => ?_) (fun r hr => ?_)
      · rw [Subgroup.mem_centralizer_iff]; intro t ht; exact (cm13 r hr t ht).symm
      · rw [Subgroup.mem_centralizer_iff]; intro t ht; exact (cm23 r hr t ht).symm
    exact (Subgroup.mem_centralizer_iff.1 (this hs) t ht).symm
  have hs123 := card_sup_sylow (p := 3) (M₁ := K ⊔ GLBConj y K) (M₂ := GLBConj y (GLBConj y K))
    (S := (R ⊓ K) ⊔ (R ⊓ GLBConj y K)) (T := R ⊓ GLBConj y (GLBConj y K)) hK3n hK12n
    (sup_le_sup inf_le_right inf_le_right) inf_le_right hs12.1 hRp3 hs12.2 c3 hcomm12_3
  have hsub : (R ⊓ K) ⊔ (R ⊓ GLBConj y K) ⊔ (R ⊓ GLBConj y (GLBConj y K)) ≤ R :=
    sup_le (sup_le inf_le_left inf_le_left) inf_le_left
  refine (Subgroup.eq_of_le_of_card_ge hsub ?_).symm
  rw [hs123.2, ← hcl, hRc]
end Q2

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
