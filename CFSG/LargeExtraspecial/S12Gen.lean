module

public import CFSG.LargeExtraspecial.S12Fuse

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def commSubSet12 (T : Set S.O) : Submodule (ZMod 2) S.Qt :=
  Submodule.span (ZMod 2) {v | ∃ x ∈ T, ∃ w : S.Qt, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w = v}

@[expose] noncomputable def commSub12 (H : Subgroup S.O) : Submodule (ZMod 2) S.Qt :=
  S.commSubSet12 (H : Set S.O)

variable {S}

theorem apply_sub_mem_commSubSet12 {T : Set S.O} {x : S.O} (hx : x ∈ T) (v : S.Qt) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ S.commSubSet12 T :=
  Submodule.subset_span ⟨x, hx, v, rfl⟩

theorem commSpace_le_commSubSet12 {T : Set S.O} {x : S.O} (hx : x ∈ T) :
    commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ S.commSubSet12 T := by
  intro v hv
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  exact apply_sub_mem_commSubSet12 hx w

theorem commSubSet12_le {T : Set S.O} {U : Submodule (ZMod 2) S.Qt}
    (h : ∀ x ∈ T, commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ U) : S.commSubSet12 T ≤ U := by
  rw [commSubSet12, Submodule.span_le]
  rintro _ ⟨x, hx, w, rfl⟩
  exact h x hx (sub_mem_commSpace _ w)

theorem commSub12_closure_le (T : Set S.O) :
    S.commSub12 (closure T) ≤ S.commSubSet12 T := by
  set U := S.commSubSet12 T
  have key : ∀ x ∈ closure T, (∀ v ∈ U, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ U) ∧
      ∀ v, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ U := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx =>
      refine ⟨fun v hv => ?_, apply_sub_mem_commSubSet12 hx⟩
      have := U.add_mem hv (apply_sub_mem_commSubSet12 hx v)
      simpa using this
    | one => exact ⟨fun v hv => hv, fun v => by simp⟩
    | mul x y _ _ hx hy =>
      refine ⟨fun v hv => ?_, fun v => ?_⟩
      · rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
        exact hx.1 _ (hy.1 v hv)
      · rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
        have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) - v =
            ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) -
              (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) := by abel
        rw [e]
        exact U.add_mem (hx.2 _) (hy.2 v)
    | inv x _ hx =>
      have hinv : ∀ v, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
        intro v
        rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]
        rfl
      refine ⟨fun v hv => ?_, fun v => ?_⟩
      · obtain ⟨w, rfl⟩ := (x : S.Qt ≃ₗ[ZMod 2] S.Qt).surjective v
        rw [hinv]
        have := U.sub_mem hv (hx.2 w)
        simpa using this
      · obtain ⟨w, rfl⟩ := (x : S.Qt ≃ₗ[ZMod 2] S.Qt).surjective v
        rw [hinv]
        have := U.neg_mem (hx.2 w)
        simpa using this
  rw [commSub12, commSubSet12, Submodule.span_le]
  rintro _ ⟨x, hx, w, rfl⟩
  exact (key x hx).2 w

theorem commSpace_le_commSub12 {H : Subgroup S.O} {x : S.O} (hx : x ∈ H) :
    commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ S.commSub12 H :=
  commSpace_le_commSubSet12 (T := (H : Set S.O)) hx

variable (S)

theorem s12_isReducible12_of_finrank_lt {H : Subgroup S.O}
    (hN : S.Mbar ≤ normalizer (H : Set S.O)) {x : S.O} (hxH : x ∈ H) (hx1 : x ≠ 1)
    (hdim : finrank (ZMod 2) (S.commSub12 H) < finrank (ZMod 2) S.Qt) : S.IsReducible12 := by
  refine ⟨S.commSub12 H, ?_, ?_, ?_⟩
  · intro hb
    apply hx1
    refine Subtype.ext (OrthoF2.eq_one_of_forall_apply_eq fun v => ?_)
    have := commSpace_le_commSub12 hxH (sub_mem_commSpace _ v)
    rw [hb] at this
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp this)
  · intro ht
    rw [ht, finrank_top] at hdim
    exact lt_irrefl _ hdim
  · intro m v hv
    have hmM : S.ρ m ∈ S.Mbar := ⟨m, rfl⟩
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨y, hy, w, rfl⟩ := hv
      have hy' : S.ρ m * y * (S.ρ m)⁻¹ ∈ H := (mem_normalizer_iff.mp (hN hmM) y).mp hy
      have e : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) =
          ((S.ρ m * y * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
              ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by
        rw [map_sub]
        congr 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply]
        rw [← LinearEquiv.mul_apply (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))⁻¹, inv_mul_cancel]
        rfl
      rw [e]
      exact apply_sub_mem_commSubSet12 (T := (H : Set S.O)) hy' _
    | zero => simp
    | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw
    | smul c v _ hv => rw [map_smul]; exact Submodule.smul_mem _ c hv

omit [Finite G] in
theorem s12_finrank_span_singleton_le (x : S.Qt) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) ({x} : Set S.Qt)) ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    rw [Submodule.span_zero_singleton, finrank_bot]
    exact zero_le_one
  · exact (finrank_span_singleton (K := ZMod 2) hx).le

theorem s12_finrank_span_insert_le (x : S.Qt) (s : Set S.Qt) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (insert x s)) ≤
      finrank (ZMod 2) (Submodule.span (ZMod 2) s) + 1 := by
  rw [Submodule.span_insert]
  refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
  rw [add_comm]
  exact Nat.add_le_add_left (S.s12_finrank_span_singleton_le x) _

theorem s12_finrank_span_le_three (x y w : S.Qt) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) ({x, y, w} : Set S.Qt)) ≤ 3 := by
  refine (S.s12_finrank_span_insert_le _ _).trans ?_
  refine Nat.add_le_add_right ((S.s12_finrank_span_insert_le _ _).trans ?_) 1
  exact Nat.add_le_add_right (S.s12_finrank_span_singleton_le w) 1

theorem s12_finrank_span_le_four (x y w u : S.Qt) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) ({x, y, w, u} : Set S.Qt)) ≤ 4 :=
  (S.s12_finrank_span_insert_le _ _).trans
    (Nat.add_le_add_right (S.s12_finrank_span_le_three _ _ _) 1)

theorem s12_commSpace_le_span_pair {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {d : S.O} (hd : d ∈ S.Lbar g)
    (hdA : IsTypeA S.q (d : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    ∃ u : S.Qt, commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      Submodule.span (ZMod 2) {S.cl (g * S.z * g⁻¹), u} := by
  obtain ⟨-, u, -, -, hspan, -⟩ := S.timmesfeld_12_6 haQ hne hd hdA
  exact ⟨u, hspan⟩

theorem s12_isReducible12_of_gen_three_two {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width) (h : S.M) {d₁ d₂ d₃ d₄ d₅ : S.O}
    (h₁ : d₁ ∈ S.Lbar g) (h₂ : d₂ ∈ S.Lbar g) (h₃ : d₃ ∈ S.Lbar g)
    (h₄ : d₄ ∈ S.Lbar ((h : G) * g)) (h₅ : d₅ ∈ S.Lbar ((h : G) * g))
    (hA₁ : IsTypeA S.q (d₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hA₂ : IsTypeA S.q (d₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hA₃ : IsTypeA S.q (d₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hA₄ : IsTypeA S.q (d₄ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hA₅ : IsTypeA S.q (d₅ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hgen : S.Xbar12 g = closure {d₁, d₂, d₃, d₄, d₅}) : S.IsReducible12 := by
  obtain ⟨hbQ, hbne⟩ := S.s12_conj_mem haQ hne h
  obtain ⟨u₁, e₁⟩ := S.s12_commSpace_le_span_pair haQ hne h₁ hA₁
  obtain ⟨u₂, e₂⟩ := S.s12_commSpace_le_span_pair haQ hne h₂ hA₂
  obtain ⟨u₃, e₃⟩ := S.s12_commSpace_le_span_pair haQ hne h₃ hA₃
  obtain ⟨u₄, e₄⟩ := S.s12_commSpace_le_span_pair hbQ hbne h₄ hA₄
  obtain ⟨u₅, e₅⟩ := S.s12_commSpace_le_span_pair hbQ hbne h₅ hA₅
  set A := Submodule.span (ZMod 2) ({S.cl (g * S.z * g⁻¹), u₁, u₂, u₃} : Set S.Qt)
  set B := Submodule.span (ZMod 2)
    ({S.cl (((h : G) * g) * S.z * ((h : G) * g)⁻¹), u₄, u₅} : Set S.Qt)
  have hle : S.commSub12 (S.Xbar12 g) ≤ A ⊔ B := by
    rw [hgen]
    refine (commSub12_closure_le _).trans (commSubSet12_le fun x hx => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rw [e₁]; exact le_sup_of_le_left (Submodule.span_mono (by intro v; simp; tauto))
    · rw [e₂]; exact le_sup_of_le_left (Submodule.span_mono (by intro v; simp; tauto))
    · rw [e₃]; exact le_sup_of_le_left (Submodule.span_mono (by intro v; simp; tauto))
    · rw [e₄]; exact le_sup_of_le_right (Submodule.span_mono (by intro v; simp; tauto))
    · rw [e₅]; exact le_sup_of_le_right (Submodule.span_mono (by intro v; simp; tauto))
  have hdim : finrank (ZMod 2) (S.commSub12 (S.Xbar12 g)) ≤ 7 := by
    refine (Submodule.finrank_mono hle).trans
      ((Submodule.finrank_add_le_finrank_add_finrank A B).trans ?_)
    have hA : finrank (ZMod 2) A ≤ 4 := S.s12_finrank_span_le_four _ _ _ _
    have hB : finrank (ZMod 2) B ≤ 3 := S.s12_finrank_span_le_three _ _ _
    omega
  have hd₁ : d₁ ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar h₁ hA₁)
  have hd₁1 : d₁ ≠ 1 := fun e => hA₁.2.1 (by rw [e]; rfl)
  refine S.s12_isReducible12_of_finrank_lt Mbar_le_normalizer_Xbar12 hd₁ hd₁1 ?_
  rw [S.finrank_Qt_eq_two_mul_width]
  omega

theorem s12_isReducible12_of_gen_three {g : G} (hn : 4 ≤ S.width) {d₁ d₂ d₃ : S.O}
    (h₁ : d₁ ∈ S.Ebar12 g) (hA₂ : IsTypeA S.q (d₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hA₃ : IsTypeA S.q (d₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hgen : S.Xbar12 g = closure {d₁, d₂, d₃}) : S.IsReducible12 := by
  have hA₁ := isTypeA_of_mem_Ebar12 h₁
  have hle : S.commSub12 (S.Xbar12 g) ≤
      commSpace (d₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (d₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔
        commSpace (d₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [hgen]
    refine (commSub12_closure_le _).trans (commSubSet12_le fun x hx => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  have hdim : finrank (ZMod 2) (S.commSub12 (S.Xbar12 g)) ≤ 6 := by
    refine (Submodule.finrank_mono hle).trans ?_
    refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
    have := Submodule.finrank_add_le_finrank_add_finrank
      (commSpace (d₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) (commSpace (d₂ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    have h1 := hA₁.2.2.2.1
    have h2 := hA₂.2.2.2.1
    have h3 := hA₃.2.2.2.1
    omega
  have hd₁ : d₁ ∈ S.Xbar12 g := subset_Xbar12 h₁
  have hd₁1 : d₁ ≠ 1 := fun e => hA₁.2.1 (by rw [e]; rfl)
  refine S.s12_isReducible12_of_finrank_lt Mbar_le_normalizer_Xbar12 hd₁ hd₁1 ?_
  rw [S.finrank_Qt_eq_two_mul_width]
  omega

end Setting

end CFSG.LargeExtraspecial
