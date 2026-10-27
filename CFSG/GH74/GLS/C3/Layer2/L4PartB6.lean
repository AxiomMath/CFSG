module

public import CFSG.GH74.GLS.C3.Layer2.L4Wreath
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4.PartB6

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2.L4.Wreath

theorem card_conj_mul_card_centralizer {C : Type*} [Group C] [Finite C] (x : C) :
    Set.ncard {y : C | ∃ c : C, c * x * c⁻¹ = y} * Nat.card (centralizer ({x} : Set C)) =
      Nat.card C := by
  have h1 := MulAction.index_stabilizer (ConjAct C) x
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct C) x)
  have h3 : Nat.card (ConjAct C) = Nat.card C := Nat.card_congr ConjAct.toConjAct.toEquiv.symm
  have h4 := Subgroup.nat_card_centralizer_nat_card_stabilizer x
  have h5 : MulAction.orbit (ConjAct C) x = {y : C | ∃ c : C, c * x * c⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨ConjAct.ofConjAct g, by simp [ConjAct.smul_def]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨ConjAct.toConjAct c, by simp [ConjAct.smul_def]⟩
  rw [h5] at h1
  rw [← h1, h4, mul_comm, h2, h3]

section Perm

variable {C : Type*} [Group C]

theorem exists_perm (b : Fin 4 → C) (hbinj : Function.Injective b)
    (hbperm : ∀ c i, ∃ j, c * b i * c⁻¹ = b j) :
    ∃ σ : C →* Perm (Fin 4), ∀ c i, c * b i * c⁻¹ = b (σ c i) := by
  classical
  let f : C → Fin 4 → Fin 4 := fun c i => Classical.choose (hbperm c i)
  have hf : ∀ c i, c * b i * c⁻¹ = b (f c i) := fun c i => Classical.choose_spec (hbperm c i)
  have hmul : ∀ c c' i, f (c * c') i = f c (f c' i) := by
    intro c c' i
    apply hbinj
    rw [← hf, mul_inv_rev]
    calc c * c' * b i * (c'⁻¹ * c⁻¹) = c * (c' * b i * c'⁻¹) * c⁻¹ := by group
      _ = c * b (f c' i) * c⁻¹ := by rw [hf c' i]
      _ = b (f c (f c' i)) := hf c _
  have hone : ∀ i, f 1 i = i := by
    intro i
    apply hbinj
    rw [← hf]; group
  let σ : C →* Perm (Fin 4) :=
    MonoidHom.mk' (fun c => ⟨f c, f c⁻¹, fun i => by rw [← hmul, inv_mul_cancel, hone],
      fun i => by rw [← hmul, mul_inv_cancel, hone]⟩) (by
      intro c c'
      refine Equiv.ext fun i => ?_
      exact hmul c c' i)
  exact ⟨σ, fun c i => hf c i⟩

end Perm

theorem exists_sylow_eq_of_isSylowOf_top {H : Type*} [Group H] [Finite H] {P : Subgroup H}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 P ⊤) : ∃ Q : Sylow 2 H, (Q : Subgroup H) = P := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right] at h
  obtain ⟨-, hpg, hidx⟩ := h
  exact ⟨hpg.toSylow hidx, IsPGroup.toSylow_coe hpg hidx⟩

variable {C : Type*} [Group C] [Finite C]

theorem card_of_classes (v x : C) (E : Subgroup C)
    (hv1 : v ≠ 1) (hvc : ∀ c : C, c * v = v * c)
    (hEn : E.Normal) (hEcard : Nat.card E = 8)
    (hvE : v ∈ E) (hxE : x ∈ E) (hx1 : x ≠ 1) (hxv : x ≠ v)
    (hcls : ∀ e ∈ E, e ≠ 1 → e ≠ v → ∃ c : C, c * x * c⁻¹ = e) :
    Nat.card C = 6 * Nat.card (centralizer ({x} : Set C)) := by
  classical
  have h1 := card_conj_mul_card_centralizer x
  have h2 : {y : C | ∃ c : C, c * x * c⁻¹ = y} = (E : Set C) \ {1, v} := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨hEn.conj_mem x hxE c, ?_⟩
      rintro (h | h)
      · exact hx1 (by
          have : c * x * c⁻¹ = 1 := h
          simpa using this)
      · apply hxv
        have h' : c * x * c⁻¹ = v := h
        have e1 : x = c⁻¹ * (c * x * c⁻¹) * c := by group
        rw [e1, h', hvc c⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    · rintro ⟨hy, hy'⟩
      exact hcls y hy (fun h => hy' (Or.inl h)) (fun h => hy' (Or.inr h))
  have h3 : Set.ncard ((E : Set C) \ {1, v}) = 6 := by
    rw [Set.ncard_sdiff (by
      intro y hy
      rcases hy with rfl | rfl
      · exact one_mem E
      · exact hvE), Set.ncard_pair hv1.symm]
    have h4 : (E : Set C).ncard = Nat.card E := (Nat.card_coe_set_eq _).symm
    omega
  rw [h2, h3] at h1
  exact h1.symm

theorem exists_theta_s_of_data (hCcard : Nat.card C = 384) (E A : Subgroup C) (b : Fin 4 → C)
    (P : Sylow 2 C) (R : Subgroup C)
    (hEn : E.Normal) (hEcomm : ∀ a ∈ E, ∀ a' ∈ E, a * a' = a' * a)
    (hA : ∀ c : C, c ∈ A ↔ ∀ e ∈ E, c * e = e * c) (hAcard : Nat.card A = 16)
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hbA : ∀ i, b i ∈ A) (hbsq : ∀ i, b i * b i = 1)
    (hbinj : Function.Injective b) (hbgen : ∀ t ∈ A, t ∈ Subgroup.closure (Set.range b))
    (hbperm : ∀ c i, ∃ j, c * b i * c⁻¹ = b j)
    (hAP : A ≤ (P : Subgroup C)) (hAR : A ⊓ R = ⊥) (hARP : A ⊔ R = (P : Subgroup C)) :
    ∃ (θ : N4 →* C) (s : Perm (Fin 4) →* C), Function.Injective θ ∧
      (∀ i, θ (Pi.mulSingle i (-1)) = b i) ∧ (∀ ε, θ ε ∈ A) ∧
      (∀ π, θ.comp (MulEquiv.toMonoidHom (actHom π)) =
        (MulEquiv.toMonoidHom (MulAut.conj (s π))).comp θ) ∧
      (∀ π i, s π * b i * (s π)⁻¹ = b (π i)) := by
  classical
  have hEA : ∀ e ∈ E, e ∈ A := fun e he => (hA e).2 (fun e' he' => hEcomm e he e' he')
  have hAn : A.Normal := ⟨fun a ha g => by
    rw [hA]
    intro e he
    have he' : g⁻¹ * e * g ∈ E := by
      have := hEn.conj_mem e he g⁻¹
      simpa using this
    have h1 := (hA a).1 ha _ he'
    calc g * a * g⁻¹ * e = g * (a * (g⁻¹ * e * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * e * g) * a) * g⁻¹ := by rw [h1]
      _ = e * (g * a * g⁻¹) := by group⟩
  obtain ⟨σ, hσ⟩ := exists_perm b hbinj hbperm
  have hker : σ.ker = A := by
    ext c
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      rw [hA]
      intro e he
      have he' : e ∈ Subgroup.closure (Set.range b) := hbgen e (hEA e he)
      have hcomm : ∀ i, c * b i = b i * c := by
        intro i
        have := hσ c i
        rw [h1, Perm.one_apply] at this
        calc c * b i = (c * b i * c⁻¹) * c := by group
          _ = b i * c := by rw [this]
      have hle : Subgroup.closure (Set.range b) ≤ Subgroup.centralizer {c} := by
        rw [Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm i).symm
      have := hle he'
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this.symm
    · intro hc
      refine Equiv.ext fun i => ?_
      apply hbinj
      rw [← hσ]
      have hcb := hAcomm c hc (b i) (hbA i)
      calc c * b i * c⁻¹ = b i * c * c⁻¹ := by rw [hcb]
        _ = b i := by group
  have hrange : σ.range = ⊤ := by
    have h1 := Subgroup.card_mul_index σ.ker
    rw [Subgroup.index_ker, hker, hAcard, hCcard] at h1
    have h2 : Nat.card σ.range = 24 := by omega
    apply Subgroup.eq_top_of_card_eq
    rw [h2, Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have : IsMulCommutative A := ⟨⟨fun a a' => Subtype.ext (hAcomm a a.2 a' a'.2)⟩⟩
  have hApg : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hAcard]; norm_num)
  obtain ⟨D, hAD, hADt⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.exists_complement_of_sylow_complement Nat.prime_two hApg
      P hAP hAR hARP
  let τ : D →* Perm (Fin 4) := σ.comp D.subtype
  have hτinj : Function.Injective τ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have h1 : (d : C) ∈ σ.ker := hd
    rw [hker] at h1
    have h2 : (d : C) ∈ A ⊓ D := ⟨h1, d.2⟩
    rw [hAD, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.2 (Subtype.ext h2)
  have hτsurj : Function.Surjective τ := by
    intro π
    have : π ∈ σ.range := by rw [hrange]; exact mem_top _
    obtain ⟨c, rfl⟩ := this
    have hc : c ∈ ((A ⊔ D : Subgroup C) : Set C) := by rw [hADt]; exact mem_top _
    rw [Subgroup.normal_mul] at hc
    obtain ⟨a, ha, d, hd, rfl⟩ := hc
    refine ⟨⟨d, hd⟩, ?_⟩
    have : σ a = 1 := by rw [← MonoidHom.mem_ker, hker]; exact ha
    show σ d = σ (a * d)
    rw [map_mul, this, one_mul]
  let e : D ≃* Perm (Fin 4) := MulEquiv.ofBijective τ ⟨hτinj, hτsurj⟩
  let s : Perm (Fin 4) →* C := D.subtype.comp e.symm.toMonoidHom
  have hσs : ∀ π, σ (s π) = π := by
    intro π
    show τ (e.symm π) = π
    exact e.apply_symm_apply π
  have hs : ∀ π i, s π * b i * (s π)⁻¹ = b (π i) := by
    intro π i
    rw [hσ (s π) i, hσs]
  have hbcomm : ∀ i j, b i * b j = b j * b i := fun i j => hAcomm _ (hbA i) _ (hbA j)
  have hcl : Subgroup.closure (Set.range b) = A := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hbA i
    · exact fun t ht => hbgen t ht
  have hcard : Nat.card (Subgroup.closure (Set.range b)) = 16 := by rw [hcl]; exact hAcard
  refine ⟨bHom b hbcomm hbsq, s, bHom_injective b hbcomm hbsq hcard, fun i => ?_, fun ε => ?_,
    bHom_compat b hbcomm hbsq s hs, hs⟩
  · rw [bHom_mulSingle, unitsHom_neg_one]
  · have h1 : bHom b hbcomm hbsq ε ∈ Subgroup.closure (Set.range b) := by
      rw [← bHom_range b hbcomm hbsq]; exact ⟨ε, rfl⟩
    rwa [hcl] at h1

theorem exists_mulEquiv_W_of_data (v x : C) (E A : Subgroup C) (b : Fin 4 → C)
    (P : Sylow 2 C) (R : Subgroup C)
    (hv1 : v ≠ 1) (hvc : ∀ c : C, c * v = v * c)
    (hEn : E.Normal) (hEcard : Nat.card E = 8) (hEcomm : ∀ a ∈ E, ∀ a' ∈ E, a * a' = a' * a)
    (hvE : v ∈ E) (hxE : x ∈ E) (hx1 : x ≠ 1) (hxv : x ≠ v)
    (hcls : ∀ e ∈ E, e ≠ 1 → e ≠ v → ∃ c : C, c * x * c⁻¹ = e)
    (hD : Nat.card (centralizer ({x} : Set C)) = 64)
    (hA : ∀ c : C, c ∈ A ↔ ∀ e ∈ E, c * e = e * c) (hAcard : Nat.card A = 16)
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hbA : ∀ i, b i ∈ A) (hbsq : ∀ i, b i * b i = 1)
    (hbinj : Function.Injective b) (hbgen : ∀ t ∈ A, t ∈ Subgroup.closure (Set.range b))
    (hbperm : ∀ c i, ∃ j, c * b i * c⁻¹ = b j)
    (hAP : A ≤ (P : Subgroup C)) (hAR : A ⊓ R = ⊥) (hARP : A ⊔ R = (P : Subgroup C)) :
    Nonempty (W ≃* C) := by
  have hCcard : Nat.card C = 384 := by
    rw [card_of_classes v x E hv1 hvc hEn hEcard hvE hxE hx1 hxv hcls, hD]
  obtain ⟨θ, s, hθ, -, -, hcomp, -⟩ := exists_theta_s_of_data hCcard E A b P R hEn hEcomm hA hAcard
    hAcomm hbA hbsq hbinj hbgen hbperm hAP hAR hARP
  exact exists_mulEquiv_W' θ hθ s hcomp hCcard

end CFSG.GH74.GLS.C3.Layer2.L4.PartB6
