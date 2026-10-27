module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG

open scoped commutatorElement

variable {G : Type} [Group G]



theorem mem_sup_of_commute {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro y (hy | hy)
      · exact ⟨y, hy, 1, B.one_mem, by simp⟩
      · exact ⟨1, A.one_mem, y, hy, by simp⟩
    · exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
      refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
      symm
      calc
        a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
        _ = a₁ * (a₂ * b₁) * b₂ := by rw [(hcomm a₂ ha₂ b₁ hb₁).eq]
        _ = (a₁ * a₂) * (b₁ * b₂) := by group
    · rintro _ _ ⟨a, ha, b, hb, rfl⟩
      refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
      exact ((hcomm a ha b hb).inv).symm
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem card_sup_eq_mul_of_commute (A B : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hdisj : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun x =>
    ⟨(x.1 : G) * (x.2 : G), Subgroup.mul_mem_sup x.1.2 x.2.2⟩
  have hinjective : Function.Injective toSup := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    simp only [toSup, Subtype.mk.injEq] at h
    have hmemA : (a1 : G)⁻¹ * a2 ∈ A :=
      A.mul_mem (A.inv_mem a1.2) a2.2
    have hmemB : (b1 : G) * (b2 : G)⁻¹ ∈ B :=
      B.mul_mem b1.2 (B.inv_mem b2.2)
    have heq : (b1 : G) * (b2 : G)⁻¹ = (a1 : G)⁻¹ * a2 := by
      have h' := congrArg (fun y : G => (a1 : G)⁻¹ * y * (b2 : G)⁻¹) h
      simpa [mul_assoc] using h'
    have hmem : (a1 : G)⁻¹ * a2 ∈ A ⊓ B :=
      ⟨hmemA, by rw [← heq]; exact hmemB⟩
    have hone : (a1 : G)⁻¹ * a2 = 1 := by
      have := hmem
      rw [hdisj] at this
      simpa using this
    have ha : (a1 : G) = a2 := by
      have h := congrArg (fun y : G => (a1 : G) * y) hone
      simpa [mul_assoc] using h.symm
    have hb : (b1 : G) = b2 := by
      have hb1 : (b1 : G) * (b2 : G)⁻¹ = 1 := by rw [heq, hone]
      have := congrArg (fun y : G => y * (b2 : G)) hb1
      simpa [mul_assoc] using this
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hsurjective : Function.Surjective toSup := by
    intro x
    have hx : (x : G) ∈ A ⊔ B := x.2
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_of_commute hcomm).mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinjective, hsurjective⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

theorem isMulCommutative_of_card_two (A : Subgroup G) (h : Nat.card A = 2) :
    IsMulCommutative A := by
  haveI : IsCyclic A := isCyclic_of_prime_card (p := 2) h
  infer_instance

theorem commute_of_mem_of_isMulCommutative {A : Subgroup G}
    (hA : IsMulCommutative A) {a a' : G} (ha : a ∈ A) (ha' : a' ∈ A) : Commute a a' := by
  have h : a ∈ Subgroup.centralizer (A : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).mpr hA ha
  exact (Subgroup.mem_centralizer_iff.mp h a' ha').symm

theorem commutator_sup_le_commutator_right {A B : Subgroup G}
    (hAA : ∀ a ∈ A, ∀ a' ∈ A, Commute a a')
    (hAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b) :
    ⁅A ⊔ B, A ⊔ B⁆ ≤ ⁅B, B⁆ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [mem_sup_of_commute hAB] at hx hy
  obtain ⟨a1, ha1, b1, hb1, rfl⟩ := hx
  obtain ⟨a2, ha2, b2, hb2, rfl⟩ := hy
  have h12 : Commute a1 a2 := hAA a1 ha1 a2 ha2
  have h1b2 : Commute a1 b2 := hAB a1 ha1 b2 hb2
  have hb1a2 : Commute b1 a2 := (hAB a2 ha2 b1 hb1).symm
  have h1b1 : Commute a1 b1 := hAB a1 ha1 b1 hb1
  have h2b2 : Commute a2 b2 := hAB a2 ha2 b2 hb2
  have h1 : ⁅a1, a2 * b2⁆ = 1 := (h12.mul_right h1b2).commutator_eq
  have h2 : ⁅b1, a2⁆ = 1 := hb1a2.commutator_eq
  have hcommA1 : Commute a1 ⁅b1, b2⁆ := by
    rw [commutatorElement_def]
    exact ((h1b1.mul_right h1b2).mul_right h1b1.inv_right).mul_right h1b2.inv_right
  have hcommA2 : Commute a2 ⁅b1, b2⁆ := by
    rw [commutatorElement_def]
    exact ((hb1a2.symm.mul_right h2b2).mul_right hb1a2.symm.inv_right).mul_right
      h2b2.inv_right
  have hcalc : ⁅a1 * b1, a2 * b2⁆ = ⁅b1, b2⁆ := by
    calc
      ⁅a1 * b1, a2 * b2⁆
          = a1 * ⁅b1, a2 * b2⁆ * a1⁻¹ * ⁅a1, a2 * b2⁆ :=
            commutatorElement_mul_left_eq_conj_mul _ _ _
      _ = a1 * ⁅b1, a2 * b2⁆ * a1⁻¹ := by rw [h1, mul_one]
      _ = a1 * (⁅b1, a2⁆ * a2 * ⁅b1, b2⁆ * a2⁻¹) * a1⁻¹ := by
            rw [commutatorElement_mul_right_eq_mul_conj]
      _ = a1 * (a2 * ⁅b1, b2⁆ * a2⁻¹) * a1⁻¹ := by rw [h2, one_mul]
      _ = ⁅b1, b2⁆ := by rw [hcommA2.mul_inv_cancel, hcommA1.mul_inv_cancel]
  rw [hcalc]
  exact Subgroup.commutator_mem_commutator hb1 hb2

theorem le_centralizer_sup_of_commute_both {A B C : Subgroup G}
    (hBC : ∀ b ∈ B, ∀ c ∈ C, Commute b c)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, Commute a c) :
    A ≤ Subgroup.centralizer ((B ⊔ C : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  change x ∈ (B ⊔ C : Subgroup G) at hx
  rw [mem_sup_of_commute hBC] at hx
  obtain ⟨b, hb, c, hc, rfl⟩ := hx
  exact ((hAB a ha b hb).mul_right (hAC a ha c hc)).symm

theorem centerIn_sup_eq_sup_center {T F : Subgroup G}
    (hTT : ∀ t ∈ T, ∀ t' ∈ T, Commute t t')
    (hTF : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hdisj : T ⊓ F = ⊥) :
    centerIn (T ⊔ F) = T ⊔ (Subgroup.center F).map F.subtype := by
  have hTcentral : T ≤ Subgroup.centralizer ((T ⊔ F : Subgroup G) : Set G) :=
    le_centralizer_sup_of_commute_both hTF hTT hTF
  have hC_le_F : (Subgroup.center F).map F.subtype ≤ F :=
    Subgroup.map_subtype_le _
  have hC_comm_F : ∀ c ∈ (Subgroup.center F).map F.subtype, ∀ f ∈ F, Commute c f := by
    intro c hc f hf
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hc
    have h := (Subgroup.mem_center_iff.mp hc' ⟨f, hf⟩).symm
    exact congrArg Subtype.val h
  have hCcentral :
      (Subgroup.center F).map F.subtype ≤
        Subgroup.centralizer ((T ⊔ F : Subgroup G) : Set G) :=
    le_centralizer_sup_of_commute_both hTF
      (fun c hc t ht => (hTF t ht c (hC_le_F hc)).symm) hC_comm_F
  apply le_antisymm
  · intro x hx
    have hxTF : x ∈ T ⊔ F := hx.1
    have hxCJ : x ∈ Subgroup.centralizer ((T ⊔ F : Subgroup G) : Set G) := hx.2
    obtain ⟨t, ht, f, hf, htf⟩ := (mem_sup_of_commute hTF).mp hxTF
    have hfC : f ∈ (Subgroup.center F).map F.subtype := by
      rw [Subgroup.mem_map]
      refine ⟨⟨f, hf⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hgJ : (g : G) ∈ T ⊔ F := Subgroup.mem_sup_right g.property
      have hxg : (g : G) * x = x * (g : G) :=
        Subgroup.mem_centralizer_iff.mp hxCJ (g : G) (Subgroup.mem_sup_right g.property)
      have htg : (g : G) * t = t * (g : G) :=
        (hTF t ht (g : G) g.property).symm
      have hf_eq : f = t⁻¹ * x := by
        rw [← htf]
        group
      have hgt : Commute (g : G) t := htg
      have hgx : Commute (g : G) x := hxg
      calc
        (g : G) * f = (g : G) * (t⁻¹ * x) := by rw [hf_eq]
        _ = (t⁻¹ * x) * (g : G) := (hgt.inv_right.mul_right hgx).eq
        _ = f * (g : G) := by rw [hf_eq]
    rw [← htf]
    exact Subgroup.mul_mem_sup ht hfC
  · apply sup_le
    · intro t ht
      exact ⟨Subgroup.mem_sup_left ht, hTcentral ht⟩
    · intro c hc
      exact ⟨Subgroup.mem_sup_right (hC_le_F hc), hCcentral hc⟩


end CFSG
