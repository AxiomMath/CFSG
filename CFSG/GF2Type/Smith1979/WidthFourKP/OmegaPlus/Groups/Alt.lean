module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.LayerData
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsA6
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltCent
public import CFSG.Holt.PermFactsInvolutions
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Equiv Equiv.Perm Finset

variable {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {τ : MulAut X}
  {B : Subgroup X}

private theorem congr_conjNormal {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    (g k : G) :
    MulAut.congr (MulAut.conjNormal (H := H) g) (MulAut.conjNormal (H := H) k) =
      MulAut.conjNormal (H := H) (g * k * g⁻¹) := by
  have hs : ∀ x : H, (MulAut.conjNormal (H := H) g).symm x =
      MulAut.conjNormal (H := H) g⁻¹ x := by
    intro x
    apply (MulAut.conjNormal (H := H) g).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
    group
  refine MulEquiv.ext fun h => Subtype.ext ?_
  simp only [MulAut.congr_apply, MulEquiv.trans_apply]
  rw [hs]
  simp only [MulAut.conjNormal_apply]
  group

private theorem sq_eq_one_of_conjNormal_sq {α : Type} [Fintype α] [DecidableEq α]
    (hα : 5 ≤ Nat.card α) {σ : Perm α}
    (hτ : MulAut.conjNormal (H := alternatingGroup α) σ *
        MulAut.conjNormal (H := alternatingGroup α) σ = 1) :
    σ * σ = 1 := by
  have hσ2' : ∀ g : alternatingGroup α,
      (σ * σ) * (g : Perm α) * (σ * σ)⁻¹ = (g : Perm α) := by
    intro g
    have h1 : (MulAut.conjNormal (H := alternatingGroup α) σ)
        ((MulAut.conjNormal (H := alternatingGroup α) σ) g) = g := by
      have := congrArg (fun f : MulAut (alternatingGroup α) => f g) hτ
      simpa using this
    have h2 := congrArg (fun z : alternatingGroup α => (z : Perm α)) h1
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply] at h2
    calc (σ * σ) * (g : Perm α) * (σ * σ)⁻¹
        = σ * (σ * (g : Perm α) * σ⁻¹) * σ⁻¹ := by group
      _ = (g : Perm α) := h2
  refine CFSG.GH74.GLS.IVK.GHInv.eq_one_of_commute_alternating hα ?_
  intro g hg
  calc σ * σ * g = ((σ * σ) * g * (σ * σ)⁻¹) * (σ * σ) := by group
    _ = g * (σ * σ) := by rw [hσ2' ⟨g, hg⟩]

private theorem conjNormal_fix_of_commute {n : ℕ} {x : Perm (Fin n)}
    (hx : x * x = 1) {y : alternatingGroup (Fin n)}
    (hy : (y : Perm (Fin n)) * x = x * (y : Perm (Fin n))) :
    MulAut.conjNormal (H := alternatingGroup (Fin n)) x y = y := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  calc x * (y : Perm (Fin n)) * x⁻¹ = x * (y : Perm (Fin n)) * x := by rw [hxinv]
    _ = x * ((y : Perm (Fin n)) * x) := by group
    _ = x * (x * (y : Perm (Fin n))) := by rw [hy]
    _ = (y : Perm (Fin n)) := by rw [← mul_assoc, hx, one_mul]

private theorem false_of_involution_W1 {n : ℕ}
    {A : Subgroup (MulAut (alternatingGroup (Fin n)))}
    {B : Subgroup (alternatingGroup (Fin n))}
    {τ : MulAut (alternatingGroup (Fin n))} {σ r : Perm (Fin n)}
    (D : LayerData (alternatingGroup (Fin n)) A τ B)
    (hτ : τ = MulAut.conjNormal σ) (hσ2 : σ * σ = 1) (hr2 : r * r = 1)
    (hs : σ.support.card = r.support.card)
    (hW1 : ∀ y : alternatingGroup (Fin n),
      (y : Perm (Fin n)) * r = r * (y : Perm (Fin n)) → (y : Perm (Fin n)) ^ 3 = 1 → y = 1) :
    False := by
  obtain ⟨h₀, -, hconj⟩ :=
    CFSG.Holt.exists_mem_alternatingGroup_conj_eq_of_card_support_eq
      (by simpa [pow_two] using hσ2) (by simpa [pow_two] using hr2) hs
  let e : MulAut (alternatingGroup (Fin n)) := MulAut.conjNormal h₀
  have hτe : MulAut.congr e τ = MulAut.conjNormal r := by
    rw [hτ, congr_conjNormal, hconj]
  refine (D.map e).false_of_W1 ?_
  intro y hyfix hy3
  have hfix := congrArg (fun z : alternatingGroup (Fin n) => (z : Perm (Fin n))) hyfix
  rw [hτe, MulAut.conjNormal_apply] at hfix
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  rw [hrinv] at hfix
  have hycomm : (y : Perm (Fin n)) * r = r * (y : Perm (Fin n)) := by
    calc (y : Perm (Fin n)) * r = (r * (y : Perm (Fin n)) * r) * r := by rw [hfix]
      _ = (r * (y : Perm (Fin n))) * (r * r) := by group
      _ = r * (y : Perm (Fin n)) := by rw [hr2, mul_one]
  have hy3' : (y : Perm (Fin n)) ^ 3 = 1 := by
    simpa using congrArg (fun z : alternatingGroup (Fin n) => (z : Perm (Fin n))) hy3
  exact hW1 y hycomm hy3'

private theorem false_of_involution_W2 {n : ℕ}
    {A : Subgroup (MulAut (alternatingGroup (Fin n)))}
    {B : Subgroup (alternatingGroup (Fin n))}
    {τ : MulAut (alternatingGroup (Fin n))} {σ r : Perm (Fin n)}
    (D : LayerData (alternatingGroup (Fin n)) A τ B)
    (hτ : τ = MulAut.conjNormal σ) (hσ2 : σ * σ = 1) (hr2 : r * r = 1)
    (hs : σ.support.card = r.support.card)
    {y₁ y₂ : alternatingGroup (Fin n)}
    (h₁ : (y₁ : Perm (Fin n)) * r = r * (y₁ : Perm (Fin n)))
    (h₂ : (y₂ : Perm (Fin n)) * r = r * (y₂ : Perm (Fin n)))
    (h₁3 : (y₁ : Perm (Fin n)) ^ 3 = 1) (h₂3 : (y₂ : Perm (Fin n)) ^ 3 = 1)
    (h : ((y₁ : Perm (Fin n)) * (y₂ : Perm (Fin n))) ^ 3 ≠ 1) : False := by
  obtain ⟨h₀, -, hconj⟩ :=
    CFSG.Holt.exists_mem_alternatingGroup_conj_eq_of_card_support_eq
      (by simpa [pow_two] using hσ2) (by simpa [pow_two] using hr2) hs
  let e : MulAut (alternatingGroup (Fin n)) := MulAut.conjNormal h₀
  have hτe : MulAut.congr e τ = MulAut.conjNormal r := by
    rw [hτ, congr_conjNormal, hconj]
  refine (D.map e).false_of_W2 (y₁ := y₁) (y₂ := y₂) ?_ ?_ ?_ ?_ ?_
  · rw [hτe]
    exact conjNormal_fix_of_commute hr2 h₁
  · rw [hτe]
    exact conjNormal_fix_of_commute hr2 h₂
  · exact Subtype.ext (by simpa using h₁3)
  · exact Subtype.ext (by simpa using h₂3)
  · exact fun hy => h (by simpa using congrArg Subtype.val hy)

private theorem false_of_involution_W5 {n : ℕ}
    {A : Subgroup (MulAut (alternatingGroup (Fin n)))}
    {B : Subgroup (alternatingGroup (Fin n))}
    {τ : MulAut (alternatingGroup (Fin n))} {σ r : Perm (Fin n)}
    (D : LayerData (alternatingGroup (Fin n)) A τ B)
    (hτ : τ = MulAut.conjNormal σ) (hσ2 : σ * σ = 1) (hr2 : r * r = 1)
    (hs : σ.support.card = r.support.card)
    {T : Subgroup (alternatingGroup (Fin n))}
    (hfix : ∀ y ∈ T, MulAut.conjNormal r y = y) (h2 : IsPGroup 2 T)
    (hinv : ∀ f : MulAut (alternatingGroup (Fin n)),
      f * MulAut.conjNormal r = MulAut.conjNormal r * f → ∀ y ∈ T, f y ∈ T)
    (h4 : Nat.card T = 4)
    (hconjT : ∀ y₁ ∈ T, ∀ y₂ ∈ T, orderOf y₁ = 2 → orderOf y₂ = 2 → IsConj y₁ y₂) :
    False := by
  obtain ⟨h₀, -, hconj⟩ :=
    CFSG.Holt.exists_mem_alternatingGroup_conj_eq_of_card_support_eq
      (by simpa [pow_two] using hσ2) (by simpa [pow_two] using hr2) hs
  let e : MulAut (alternatingGroup (Fin n)) := MulAut.conjNormal h₀
  have hτe : MulAut.congr e τ = MulAut.conjNormal r := by
    rw [hτ, congr_conjNormal, hconj]
  rw [← hτe] at hfix hinv
  exact (D.map e).false_of_W5 hfix h2 hinv h4 hconjT

private theorem a5_invol_W1 : ∀ v : Perm (Fin 5), v * v = 1 → v ≠ 1 →
    Perm.sign v = 1 →
    ∀ y : Perm (Fin 5), y * v = v * y → y ^ 3 = 1 → Perm.sign y = 1 → y = 1 := by
  decide +kernel

theorem false_of_alt5 (D : LayerData X A τ B) (e : X ≃* alternatingGroup (Fin 5)) : False := by
  have hnonab : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 2 3, ?_⟩,
      ⟨List.formPerm [0, 1, 2], ?_⟩, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    · rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    · intro h
      have h' := congrArg (fun x : alternatingGroup (Fin 5) => (x : Perm (Fin 5))) h
      simp only [Subgroup.coe_mul] at h'
      revert h'
      decide +kernel
  have hA : Nat.card (MulAut (alternatingGroup (Fin 5))) ≤
      2 * Nat.card (alternatingGroup (Fin 5)) := by
    have hsurj : Function.Surjective (MulAut.conjNormal (H := alternatingGroup (Fin 5)) :
        Perm (Fin 5) → MulAut (alternatingGroup (Fin 5))) := by
      intro f
      obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj
        (α := Fin 5) (by decide) f
      refine ⟨σ, ?_⟩
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [MulAut.conjNormal_apply]
      exact (hσ g).symm
    calc Nat.card (MulAut (alternatingGroup (Fin 5)))
        ≤ Nat.card (Perm (Fin 5)) := Nat.card_le_card_of_surjective _ hsurj
      _ = 120 := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
      _ = 2 * Nat.card (alternatingGroup (Fin 5)) := by
          rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
          norm_num
  have hC : ∀ v y : alternatingGroup (Fin 5), orderOf v = 2 → y * v = v * y →
      y ^ 3 = 1 → y = 1 := by
    intro v y hv hcomm hy3
    obtain ⟨hv2, hv1⟩ := (orderOf_eq_prime_iff (p := 2)).mp hv
    have hv2' : (v : Perm (Fin 5)) * (v : Perm (Fin 5)) = 1 := by
      simpa [pow_two] using
        congrArg (fun z : alternatingGroup (Fin 5) => (z : Perm (Fin 5))) hv2
    have hv1' : (v : Perm (Fin 5)) ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hcomm' : (y : Perm (Fin 5)) * (v : Perm (Fin 5)) =
        (v : Perm (Fin 5)) * (y : Perm (Fin 5)) := by
      simpa using congrArg (fun z : alternatingGroup (Fin 5) => (z : Perm (Fin 5))) hcomm
    have hy3' : (y : Perm (Fin 5)) ^ 3 = 1 := by
      simpa using congrArg (fun z : alternatingGroup (Fin 5) => (z : Perm (Fin 5))) hy3
    exact Subtype.ext
      (a5_invol_W1 (v : Perm (Fin 5)) hv2' hv1' v.2 (y : Perm (Fin 5)) hcomm' hy3' y.2)
  exact (D.map e).false_of_outTwo hnonab hA hC


private def c6 : Perm (Fin 6) := c[0, 1, 2]
private def d6 : Perm (Fin 6) := c[0, 1, 2] * c[3, 4, 5]

private def c6A : alternatingGroup (Fin 6) :=
  ⟨c6, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def d6A : alternatingGroup (Fin 6) :=
  ⟨d6, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

private theorem a6_classes_differ : ∀ k : Perm (Fin 6), k * c6 * k⁻¹ ≠ d6 := by
  decide +kernel

private theorem a6_transp :
    let x : Perm (Fin 6) := swap 0 1
    let y₁ : Perm (Fin 6) := List.formPerm [3, 4, 5]
    let y₂ : Perm (Fin 6) := List.formPerm [2, 3, 4]
    Perm.sign y₁ = 1 ∧ Perm.sign y₂ = 1 ∧ y₁ * x = x * y₁ ∧ y₂ * x = x * y₂ ∧
      y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧ (y₁ * y₂) ^ 3 ≠ 1 := by
  decide +kernel

private theorem a6_three :
    let x : Perm (Fin 6) := swap 0 1 * swap 2 3 * swap 4 5
    let y₁ : Perm (Fin 6) := List.formPerm [0, 2, 4] * List.formPerm [1, 3, 5]
    let y₂ : Perm (Fin 6) := List.formPerm [0, 4, 3] * List.formPerm [1, 5, 2]
    Perm.sign y₁ = 1 ∧ Perm.sign y₂ = 1 ∧ y₁ * x = x * y₁ ∧ y₂ * x = x * y₂ ∧
      y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧ (y₁ * y₂) ^ 3 ≠ 1 := by
  decide +kernel

private theorem a6_double_W1 :
    ∀ y : Perm (Fin 6), Perm.sign y = 1 →
      y * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * y → y ^ 3 = 1 → y = 1 := by
  decide +kernel

private theorem false_of_alt6_support_two (D : LayerData X A τ B)
    (e : X ≃* alternatingGroup (Fin 6)) {g : Perm (Fin 6)}
    (hg : MulAut.congr e τ = MulAut.conjNormal g) (hg2 : g * g = 1)
    (hcard : g.support.card = 2) : False := by
  have hr : (swap 0 1 : Perm (Fin 6)) * swap 0 1 = 1 := by decide +kernel
  have hs : g.support.card = (swap 0 1 : Perm (Fin 6)).support.card := by
    rw [hcard]
    decide +kernel
  have h := a6_transp
  dsimp only at h
  obtain ⟨hs₁, hs₂, hc₁, hc₂, hp₁, hp₂, hne⟩ := h
  let y₁ : alternatingGroup (Fin 6) := ⟨List.formPerm [3, 4, 5], hs₁⟩
  let y₂ : alternatingGroup (Fin 6) := ⟨List.formPerm [2, 3, 4], hs₂⟩
  have hc₁' : (y₁ : Perm (Fin 6)) * (swap 0 1) = (swap 0 1) * (y₁ : Perm (Fin 6)) := hc₁
  have hc₂' : (y₂ : Perm (Fin 6)) * (swap 0 1) = (swap 0 1) * (y₂ : Perm (Fin 6)) := hc₂
  have hp₁' : (y₁ : Perm (Fin 6)) ^ 3 = 1 := hp₁
  have hp₂' : (y₂ : Perm (Fin 6)) ^ 3 = 1 := hp₂
  have hne' : ((y₁ : Perm (Fin 6)) * (y₂ : Perm (Fin 6))) ^ 3 ≠ 1 := hne
  exact false_of_involution_W2 (D.map e) hg hg2 hr hs hc₁' hc₂' hp₁' hp₂' hne'

private theorem false_of_alt6_support_four (D : LayerData X A τ B)
    (e : X ≃* alternatingGroup (Fin 6)) {g : Perm (Fin 6)}
    (hg : MulAut.congr e τ = MulAut.conjNormal g) (hg2 : g * g = 1)
    (hcard : g.support.card = 4) : False := by
  have hr : (swap 0 1 * swap 2 3 : Perm (Fin 6)) * (swap 0 1 * swap 2 3) = 1 := by
    decide +kernel
  have hs : g.support.card = (swap 0 1 * swap 2 3 : Perm (Fin 6)).support.card := by
    rw [hcard]
    decide +kernel
  exact false_of_involution_W1 (D.map e) hg hg2 hr hs
    (fun y hycomm hy3 => Subtype.ext (a6_double_W1 (y : Perm (Fin 6)) y.2 hycomm hy3))

private theorem false_of_alt6_support_six (D : LayerData X A τ B)
    (e : X ≃* alternatingGroup (Fin 6)) {g : Perm (Fin 6)}
    (hg : MulAut.congr e τ = MulAut.conjNormal g) (hg2 : g * g = 1)
    (hcard : g.support.card = 6) : False := by
  have hr : (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 6)) *
      (swap 0 1 * swap 2 3 * swap 4 5) = 1 := by decide +kernel
  have hs : g.support.card = (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 6)).support.card := by
    rw [hcard]
    decide +kernel
  have h := a6_three
  dsimp only at h
  obtain ⟨hs₁, hs₂, hc₁, hc₂, hp₁, hp₂, hne⟩ := h
  let y₁ : alternatingGroup (Fin 6) := ⟨List.formPerm [0, 2, 4] * List.formPerm [1, 3, 5], hs₁⟩
  let y₂ : alternatingGroup (Fin 6) := ⟨List.formPerm [0, 4, 3] * List.formPerm [1, 5, 2], hs₂⟩
  have hc₁' : (y₁ : Perm (Fin 6)) * (swap 0 1 * swap 2 3 * swap 4 5) =
      (swap 0 1 * swap 2 3 * swap 4 5) * (y₁ : Perm (Fin 6)) := hc₁
  have hc₂' : (y₂ : Perm (Fin 6)) * (swap 0 1 * swap 2 3 * swap 4 5) =
      (swap 0 1 * swap 2 3 * swap 4 5) * (y₂ : Perm (Fin 6)) := hc₂
  have hp₁' : (y₁ : Perm (Fin 6)) ^ 3 = 1 := hp₁
  have hp₂' : (y₂ : Perm (Fin 6)) ^ 3 = 1 := hp₂
  have hne' : ((y₁ : Perm (Fin 6)) * (y₂ : Perm (Fin 6))) ^ 3 ≠ 1 := hne
  exact false_of_involution_W2 (D.map e) hg hg2 hr hs hc₁' hc₂' hp₁' hp₂' hne'

private theorem false_of_alt6_inner (D : LayerData X A τ B)
    (e : X ≃* alternatingGroup (Fin 6)) {g : Perm (Fin 6)}
    (hg : MulAut.congr e τ = MulAut.conjNormal g) : False := by
  have hg2 : g * g = 1 := by
    apply sq_eq_one_of_conjNormal_sq (α := Fin 6)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have hsq := (D.map e).sq_A (MulAut.congr e τ) (D.map e).mem_A
    rwa [hg] at hsq
  have hg1 : g ≠ 1 := by
    intro h
    apply (D.map e).ne_one
    rw [hg, h]
    exact map_one _
  have hg2' : g ^ 2 = 1 := by simpa [pow_two] using hg2
  have h2dvd : 2 ∣ g.support.card := Equiv.Perm.two_dvd_card_support hg2'
  have h1lt : 1 < g.support.card := Equiv.Perm.one_lt_card_support_of_ne_one hg1
  have hle : g.support.card ≤ 6 := by
    simpa using Finset.card_le_univ g.support
  have hcard : g.support.card = 2 ∨ g.support.card = 4 ∨ g.support.card = 6 := by
    omega
  rcases hcard with h2 | h4 | h6
  · exact false_of_alt6_support_two D e hg hg2 h2
  · exact false_of_alt6_support_four D e hg hg2 h4
  · exact false_of_alt6_support_six D e hg hg2 h6

private theorem false_of_alt6_exotic (D : LayerData X A τ B)
    (e : X ≃* alternatingGroup (Fin 6)) {g : alternatingGroup (Fin 6)}
    (hg : ((g * MulAut.congr e τ CFSG.QuasithinUnique.Setup.X3E.gx * g⁻¹ :
      alternatingGroup (Fin 6)) : Perm (Fin 6)) = d6) : False := by
  have hτ2 : MulAut.congr e τ * MulAut.congr e τ = 1 :=
    (D.map e).sq_A (MulAut.congr e τ) (D.map e).mem_A
  have hττ : ∀ z : alternatingGroup (Fin 6), MulAut.congr e τ (MulAut.congr e τ z) = z := by
    intro z
    have h := congrArg (fun f : MulAut (alternatingGroup (Fin 6)) => f z) hτ2
    simpa using h
  have hgx : (CFSG.QuasithinUnique.Setup.X3E.gx : alternatingGroup (Fin 6)) = c6A := by
    decide +kernel
  have hex : IsConj (MulAut.congr e τ c6A) d6A := by
    refine isConj_iff.mpr ⟨g, ?_⟩
    apply Subtype.ext
    change ↑(g * MulAut.congr e τ c6A * g⁻¹) = (d6 : Perm (Fin 6))
    rw [hgx] at hg
    exact hg
  refine (D.map e).false_of_W1 ?_
  intro y hyfix hy3
  by_contra hy1
  have hy3' : (y : Perm (Fin 6)) ^ 3 = 1 := by
    simpa using congrArg (fun z : alternatingGroup (Fin 6) => (z : Perm (Fin 6))) hy3
  have hy1' : (y : Perm (Fin 6)) ≠ 1 := fun h => hy1 (Subtype.ext h)
  rcases CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.order_three_cases
    (y : Perm (Fin 6)) hy3' hy1' with ⟨k, hk, hky⟩ | ⟨k, hk, hky⟩
  · let kA : alternatingGroup (Fin 6) := ⟨k, by rw [Equiv.Perm.mem_alternatingGroup]; exact hk⟩
    have hkA : kA * y * kA⁻¹ = c6A := by
      apply Subtype.ext
      change k * (y : Perm (Fin 6)) * k⁻¹ = c6
      exact hky
    have hconj_y_c : IsConj y c6A := isConj_iff.mpr ⟨kA, hkA⟩
    have hconj_y_tc : IsConj y (MulAut.congr e τ c6A) := by
      have h : IsConj (MulAut.congr e τ y) (MulAut.congr e τ c6A) :=
        MonoidHom.map_isConj (MulAut.congr e τ).toMonoidHom hconj_y_c
      rw [hyfix] at h
      exact h
    have hconj_c_d : IsConj c6A d6A :=
      (hconj_y_c.symm.trans hconj_y_tc).trans hex
    have hperm : IsConj c6 d6 :=
      MonoidHom.map_isConj (Subgroup.subtype (alternatingGroup (Fin 6))) hconj_c_d
    rcases isConj_iff.mp hperm with ⟨m, hm⟩
    exact a6_classes_differ m hm
  · let kA : alternatingGroup (Fin 6) := ⟨k, by rw [Equiv.Perm.mem_alternatingGroup]; exact hk⟩
    have hkA : kA * y * kA⁻¹ = d6A := by
      apply Subtype.ext
      change k * (y : Perm (Fin 6)) * k⁻¹ = d6
      exact hky
    have hconj_y_d : IsConj y d6A := isConj_iff.mpr ⟨kA, hkA⟩
    have hconj_d_td : IsConj d6A (MulAut.congr e τ d6A) := by
      have h : IsConj (MulAut.congr e τ y) (MulAut.congr e τ d6A) :=
        MonoidHom.map_isConj (MulAut.congr e τ).toMonoidHom hconj_y_d
      rw [hyfix] at h
      exact hconj_y_d.symm.trans h
    have hconj_c_td : IsConj c6A (MulAut.congr e τ d6A) := by
      have h : IsConj (MulAut.congr e τ (MulAut.congr e τ c6A)) (MulAut.congr e τ d6A) :=
        MonoidHom.map_isConj (MulAut.congr e τ).toMonoidHom hex
      rw [hττ c6A] at h
      exact h
    have hconj_c_d : IsConj c6A d6A := hconj_c_td.trans hconj_d_td.symm
    have hperm : IsConj c6 d6 :=
      MonoidHom.map_isConj (Subgroup.subtype (alternatingGroup (Fin 6))) hconj_c_d
    rcases isConj_iff.mp hperm with ⟨m, hm⟩
    exact a6_classes_differ m hm

theorem false_of_alt6 (D : LayerData X A τ B) (e : X ≃* alternatingGroup (Fin 6)) : False := by
  rcases CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.mulAut_alt6_cases
    (MulAut.congr e τ) with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact false_of_alt6_inner D e hg
  · exact false_of_alt6_exotic D e hg


private def a7x : Perm (Fin 7) := swap 0 1 * swap 2 3
private def a7x2 : Perm (Fin 7) := swap 0 2 * swap 1 3
private def a7x3 : Perm (Fin 7) := swap 0 3 * swap 1 2

private def a7xA : alternatingGroup (Fin 7) :=
  ⟨a7x, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def a7x2A : alternatingGroup (Fin 7) :=
  ⟨a7x2, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def a7x3A : alternatingGroup (Fin 7) :=
  ⟨a7x3, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

private def a7S : Finset (alternatingGroup (Fin 7)) := {1, a7xA, a7x2A, a7x3A}

private theorem a7S_cases (y : alternatingGroup (Fin 7)) (hy : y ∈ a7S) :
    y = 1 ∨ y = a7xA ∨ y = a7x2A ∨ y = a7x3A := by
  simpa [a7S] using hy

private theorem a7S_mul (y z : alternatingGroup (Fin 7)) (hy : y ∈ a7S) (hz : z ∈ a7S) :
    y * z ∈ a7S := by
  rcases a7S_cases y hy with rfl | rfl | rfl | rfl <;>
    rcases a7S_cases z hz with rfl | rfl | rfl | rfl <;>
    decide +kernel

private theorem a7S_inv (y : alternatingGroup (Fin 7)) (hy : y ∈ a7S) : y⁻¹ ∈ a7S := by
  rcases a7S_cases y hy with rfl | rfl | rfl | rfl <;> decide +kernel

private def a7V : Subgroup (alternatingGroup (Fin 7)) where
  carrier := (a7S : Set (alternatingGroup (Fin 7)))
  one_mem' := by simp [a7S]
  mul_mem' := by
    intro y z hy hz
    exact a7S_mul y z hy hz
  inv_mem' := by
    intro y hy
    exact a7S_inv y hy

private theorem mem_a7V_iff {y : alternatingGroup (Fin 7)} : y ∈ a7V ↔ y ∈ a7S := Iff.rfl

private theorem a7V_cases (y : alternatingGroup (Fin 7)) (hy : y ∈ a7V) :
    y = 1 ∨ y = a7xA ∨ y = a7x2A ∨ y = a7x3A :=
  a7S_cases y (mem_a7V_iff.mp hy)

private theorem a7V_card : Nat.card a7V = 4 := by
  have h := Nat.subtype_card a7S (p := fun y : alternatingGroup (Fin 7) => y ∈ a7V)
    (fun y => mem_a7V_iff)
  rw [h]
  decide +kernel

private theorem a7V_mem_x : a7xA ∈ a7V := by
  change a7xA ∈ a7S
  simp [a7S]

private theorem a7V_mem_x2 : a7x2A ∈ a7V := by
  change a7x2A ∈ a7S
  simp [a7S]

private theorem a7V_mem_x3 : a7x3A ∈ a7V := by
  change a7x3A ∈ a7S
  simp [a7S]

private theorem a7V_fix : ∀ y ∈ a7V,
    MulAut.conjNormal (H := alternatingGroup (Fin 7)) a7x y = y := by
  intro y hy
  rcases a7V_cases y hy with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem a7_transp :
    let x : Perm (Fin 7) := swap 0 1
    let y₁ : Perm (Fin 7) := List.formPerm [4, 5, 6]
    let y₂ : Perm (Fin 7) := List.formPerm [3, 4, 5]
    Perm.sign y₁ = 1 ∧ Perm.sign y₂ = 1 ∧ y₁ * x = x * y₁ ∧ y₂ * x = x * y₂ ∧
      y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧ (y₁ * y₂) ^ 3 ≠ 1 := by
  decide +kernel

private theorem a7_three :
    let x : Perm (Fin 7) := swap 0 1 * swap 2 3 * swap 4 5
    let y₁ : Perm (Fin 7) := List.formPerm [0, 2, 4] * List.formPerm [1, 3, 5]
    let y₂ : Perm (Fin 7) := List.formPerm [0, 4, 3] * List.formPerm [1, 5, 2]
    Perm.sign y₁ = 1 ∧ Perm.sign y₂ = 1 ∧ y₁ * x = x * y₁ ∧ y₂ * x = x * y₂ ∧
      y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧ (y₁ * y₂) ^ 3 ≠ 1 := by
  decide +kernel

private theorem a7_double :
    let x : Perm (Fin 7) := swap 0 1 * swap 2 3
    let x₂ : Perm (Fin 7) := swap 0 2 * swap 1 3
    let x₃ : Perm (Fin 7) := swap 0 3 * swap 1 2
    let g₂ : Perm (Fin 7) := List.formPerm [0, 1, 3, 2] * swap 4 6
    let g₃ : Perm (Fin 7) := List.formPerm [1, 3, 2]
    Perm.sign g₂ = 1 ∧ Perm.sign g₃ = 1 ∧ g₂ * x * g₂⁻¹ = x₂ ∧ g₃ * x * g₃⁻¹ = x₃ ∧
      x₂ * x = x * x₂ ∧ x₃ = x * x₂ := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem a7_double_inv :
    ∀ ρ : Perm (Fin 7), ρ * a7x = a7x * ρ →
      ρ * a7x2 * ρ⁻¹ = a7x ∨ ρ * a7x2 * ρ⁻¹ = a7x2 ∨ ρ * a7x2 * ρ⁻¹ = a7x3 := by
  decide +kernel


private theorem a7V_hinv :
    ∀ f : MulAut (alternatingGroup (Fin 7)),
      f * MulAut.conjNormal (H := alternatingGroup (Fin 7)) a7x =
        MulAut.conjNormal (H := alternatingGroup (Fin 7)) a7x * f →
      ∀ y ∈ a7V, f y ∈ a7V := by
  intro f hf y hy
  obtain ⟨ρ, hρ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj
    (α := Fin 7) (by decide) f
  have hfe : f = MulAut.conjNormal (H := alternatingGroup (Fin 7)) ρ := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    exact hρ g
  have hf' : MulAut.conjNormal (H := alternatingGroup (Fin 7)) ρ *
      MulAut.conjNormal (H := alternatingGroup (Fin 7)) a7x =
      MulAut.conjNormal (H := alternatingGroup (Fin 7)) a7x *
        MulAut.conjNormal (H := alternatingGroup (Fin 7)) ρ := by
    rwa [hfe] at hf
  have hρx : ρ * a7x * ρ⁻¹ = a7x := by
    have hcomm : ∀ g ∈ alternatingGroup (Fin 7),
        (a7x⁻¹ * ρ * a7x * ρ⁻¹) * g = g * (a7x⁻¹ * ρ * a7x * ρ⁻¹) := by
      intro g hg
      have hgs : Equiv.Perm.sign g = 1 := Equiv.Perm.mem_alternatingGroup.mp hg
      let g' : alternatingGroup (Fin 7) :=
        ⟨ρ⁻¹ * g * ρ, by
          rw [Equiv.Perm.mem_alternatingGroup]
          rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
          rw [hgs]
          rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h <;> rw [h] <;> norm_num⟩
      have h := congrArg (fun z : alternatingGroup (Fin 7) => (z : Perm (Fin 7)))
        (congrArg (fun f : MulAut (alternatingGroup (Fin 7)) => f g') hf')
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conjNormal_apply,
        MulAut.conjNormal_apply, MulAut.conjNormal_apply, MulAut.conjNormal_apply] at h
      change ρ * (a7x * (ρ⁻¹ * g * ρ) * a7x⁻¹) * ρ⁻¹ =
        a7x * (ρ * (ρ⁻¹ * g * ρ) * ρ⁻¹) * a7x⁻¹ at h
      have h'' : (ρ * a7x * ρ⁻¹) * g * (ρ * a7x * ρ⁻¹)⁻¹ = a7x * g * a7x⁻¹ := by
        calc (ρ * a7x * ρ⁻¹) * g * (ρ * a7x * ρ⁻¹)⁻¹
            = ρ * (a7x * (ρ⁻¹ * g * ρ) * a7x⁻¹) * ρ⁻¹ := by group
          _ = a7x * (ρ * (ρ⁻¹ * g * ρ) * ρ⁻¹) * a7x⁻¹ := h
          _ = a7x * g * a7x⁻¹ := by group
      have hp : (ρ * a7x * ρ⁻¹) * g = a7x * g * a7x⁻¹ * (ρ * a7x * ρ⁻¹) := by
        calc (ρ * a7x * ρ⁻¹) * g
            = ((ρ * a7x * ρ⁻¹) * g * (ρ * a7x * ρ⁻¹)⁻¹) * (ρ * a7x * ρ⁻¹) := by group
          _ = (a7x * g * a7x⁻¹) * (ρ * a7x * ρ⁻¹) := by rw [h'']
          _ = a7x * g * a7x⁻¹ * (ρ * a7x * ρ⁻¹) := by group
      calc (a7x⁻¹ * ρ * a7x * ρ⁻¹) * g
          = a7x⁻¹ * ((ρ * a7x * ρ⁻¹) * g) := by group
        _ = a7x⁻¹ * (a7x * g * a7x⁻¹ * (ρ * a7x * ρ⁻¹)) := by rw [hp]
        _ = g * (a7x⁻¹ * ρ * a7x * ρ⁻¹) := by group
    have hc1 : a7x⁻¹ * ρ * a7x * ρ⁻¹ = 1 :=
      CFSG.GH74.GLS.IVK.GHInv.eq_one_of_commute_alternating
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num) hcomm
    calc ρ * a7x * ρ⁻¹ = a7x * (a7x⁻¹ * ρ * a7x * ρ⁻¹) := by group
      _ = a7x := by rw [hc1]; group
  have hcommx : ρ * a7x = a7x * ρ := by
    calc ρ * a7x = (ρ * a7x * ρ⁻¹) * ρ := by group
      _ = a7x * ρ := by rw [hρx]
  have hfx : f a7xA = a7xA := by
    apply Subtype.ext
    rw [hfe, MulAut.conjNormal_apply]
    exact hρx
  have hf2mem : f a7x2A ∈ a7V := by
    have hf2 : (f a7x2A : Perm (Fin 7)) = ρ * a7x2 * ρ⁻¹ := by
      rw [hfe, MulAut.conjNormal_apply]
      rfl
    rcases a7_double_inv ρ hcommx with h | h | h
    · have hx : f a7x2A = a7xA := by
        apply Subtype.ext
        rw [hf2, h]
        rfl
      rw [hx]
      exact a7V_mem_x
    · have hx : f a7x2A = a7x2A := by
        apply Subtype.ext
        rw [hf2, h]
        rfl
      rw [hx]
      exact a7V_mem_x2
    · have hx : f a7x2A = a7x3A := by
        apply Subtype.ext
        rw [hf2, h]
        rfl
      rw [hx]
      exact a7V_mem_x3
  have hf3mem : f a7x3A ∈ a7V := by
    have hmul : a7x3A = a7xA * a7x2A := by
      apply Subtype.ext
      decide +kernel
    rw [hmul, map_mul, hfx]
    exact a7V.mul_mem a7V_mem_x hf2mem
  rcases a7V_cases y hy with rfl | rfl | rfl | rfl
  · simpa using a7V.one_mem
  · simpa [hfx] using a7V_mem_x
  · exact hf2mem
  · exact hf3mem

private theorem a7V_hconj : ∀ y₁ ∈ a7V, ∀ y₂ ∈ a7V, orderOf y₁ = 2 → orderOf y₂ = 2 →
    IsConj y₁ y₂ := by
  have h := a7_double
  dsimp only at h
  obtain ⟨hg₂, hg₃, hconj₂, hconj₃, -, -⟩ := h
  let g₂A : alternatingGroup (Fin 7) := ⟨_, hg₂⟩
  let g₃A : alternatingGroup (Fin 7) := ⟨_, hg₃⟩
  have hx_x2 : IsConj a7xA a7x2A := by
    refine isConj_iff.mpr ⟨g₂A, ?_⟩
    apply Subtype.ext
    simpa [g₂A, a7xA, a7x, a7x2A, a7x2] using hconj₂
  have hx_x3 : IsConj a7xA a7x3A := by
    refine isConj_iff.mpr ⟨g₃A, ?_⟩
    apply Subtype.ext
    simpa [g₃A, a7xA, a7x, a7x3A, a7x3] using hconj₃
  have hx2_x3 : IsConj a7x2A a7x3A := hx_x2.symm.trans hx_x3
  intro y₁ hy₁ y₂ hy₂ ho₁ ho₂
  rcases a7V_cases y₁ hy₁ with rfl | rfl | rfl | rfl <;>
    rcases a7V_cases y₂ hy₂ with rfl | rfl | rfl | rfl <;>
    first
      | exact IsConj.refl _
      | exact hx_x2
      | exact hx_x3
      | exact hx_x2.symm
      | exact hx_x3.symm
      | exact hx2_x3
      | exact hx2_x3.symm
      | (simp [orderOf_one] at ho₁)
      | (simp [orderOf_one] at ho₂)

private theorem false_of_alt7_support_two (D : LayerData X A τ B)
    (e : X ≃* alternatingGroup (Fin 7)) {σ : Perm (Fin 7)}
    (hσ : MulAut.congr e τ = MulAut.conjNormal σ) (hσ2 : σ * σ = 1)
    (hcard : σ.support.card = 2) : False := by
  have hr : (swap 0 1 : Perm (Fin 7)) * swap 0 1 = 1 := by decide +kernel
  have hs : σ.support.card = (swap 0 1 : Perm (Fin 7)).support.card := by
    rw [hcard]
    decide +kernel
  have h := a7_transp
  dsimp only at h
  obtain ⟨hs₁, hs₂, hc₁, hc₂, hp₁, hp₂, hne⟩ := h
  let y₁ : alternatingGroup (Fin 7) := ⟨List.formPerm [4, 5, 6], hs₁⟩
  let y₂ : alternatingGroup (Fin 7) := ⟨List.formPerm [3, 4, 5], hs₂⟩
  have hc₁' : (y₁ : Perm (Fin 7)) * (swap 0 1) = (swap 0 1) * (y₁ : Perm (Fin 7)) := hc₁
  have hc₂' : (y₂ : Perm (Fin 7)) * (swap 0 1) = (swap 0 1) * (y₂ : Perm (Fin 7)) := hc₂
  have hp₁' : (y₁ : Perm (Fin 7)) ^ 3 = 1 := hp₁
  have hp₂' : (y₂ : Perm (Fin 7)) ^ 3 = 1 := hp₂
  have hne' : ((y₁ : Perm (Fin 7)) * (y₂ : Perm (Fin 7))) ^ 3 ≠ 1 := hne
  exact false_of_involution_W2 (D.map e) hσ hσ2 hr hs hc₁' hc₂' hp₁' hp₂' hne'

private theorem false_of_alt7_support_four (D : LayerData X A τ B)
    (e : X ≃* alternatingGroup (Fin 7)) {σ : Perm (Fin 7)}
    (hσ : MulAut.congr e τ = MulAut.conjNormal σ) (hσ2 : σ * σ = 1)
    (hcard : σ.support.card = 4) : False := by
  have hr : a7x * a7x = 1 := by decide +kernel
  have hs : σ.support.card = a7x.support.card := by
    rw [hcard]
    decide +kernel
  have h2 : IsPGroup 2 a7V := by
    apply IsPGroup.of_card (n := 2)
    rw [a7V_card]
    norm_num
  exact false_of_involution_W5 (D.map e) hσ hσ2 hr hs a7V_fix h2 a7V_hinv a7V_card a7V_hconj

private theorem false_of_alt7_support_six (D : LayerData X A τ B)
    (e : X ≃* alternatingGroup (Fin 7)) {σ : Perm (Fin 7)}
    (hσ : MulAut.congr e τ = MulAut.conjNormal σ) (hσ2 : σ * σ = 1)
    (hcard : σ.support.card = 6) : False := by
  have hr : (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)) *
      (swap 0 1 * swap 2 3 * swap 4 5) = 1 := by decide +kernel
  have hs : σ.support.card = (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)).support.card := by
    rw [hcard]
    decide +kernel
  have h := a7_three
  dsimp only at h
  obtain ⟨hs₁, hs₂, hc₁, hc₂, hp₁, hp₂, hne⟩ := h
  let y₁ : alternatingGroup (Fin 7) :=
    ⟨List.formPerm [0, 2, 4] * List.formPerm [1, 3, 5], hs₁⟩
  let y₂ : alternatingGroup (Fin 7) :=
    ⟨List.formPerm [0, 4, 3] * List.formPerm [1, 5, 2], hs₂⟩
  have hc₁' : (y₁ : Perm (Fin 7)) * (swap 0 1 * swap 2 3 * swap 4 5) =
      (swap 0 1 * swap 2 3 * swap 4 5) * (y₁ : Perm (Fin 7)) := hc₁
  have hc₂' : (y₂ : Perm (Fin 7)) * (swap 0 1 * swap 2 3 * swap 4 5) =
      (swap 0 1 * swap 2 3 * swap 4 5) * (y₂ : Perm (Fin 7)) := hc₂
  have hp₁' : (y₁ : Perm (Fin 7)) ^ 3 = 1 := hp₁
  have hp₂' : (y₂ : Perm (Fin 7)) ^ 3 = 1 := hp₂
  have hne' : ((y₁ : Perm (Fin 7)) * (y₂ : Perm (Fin 7))) ^ 3 ≠ 1 := hne
  exact false_of_involution_W2 (D.map e) hσ hσ2 hr hs hc₁' hc₂' hp₁' hp₂' hne'

theorem false_of_alt7 (D : LayerData X A τ B) (e : X ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj
    (α := Fin 7) (by decide) (MulAut.congr e τ)
  have hσeq : MulAut.congr e τ = MulAut.conjNormal σ := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    exact hσ g
  have hσ2 : σ * σ = 1 := by
    apply sq_eq_one_of_conjNormal_sq (α := Fin 7)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have hsq := (D.map e).sq_A (MulAut.congr e τ) (D.map e).mem_A
    rwa [hσeq] at hsq
  have hσ1 : σ ≠ 1 := by
    intro h
    apply (D.map e).ne_one
    rw [hσeq, h]
    exact map_one _
  have hσ2' : σ ^ 2 = 1 := by simpa [pow_two] using hσ2
  have h2dvd : 2 ∣ σ.support.card := Equiv.Perm.two_dvd_card_support hσ2'
  have h1lt : 1 < σ.support.card := Equiv.Perm.one_lt_card_support_of_ne_one hσ1
  have hle : σ.support.card ≤ 7 := by
    simpa using Finset.card_le_univ σ.support
  have hcard : σ.support.card = 2 ∨ σ.support.card = 4 ∨ σ.support.card = 6 := by
    omega
  rcases hcard with h2 | h4 | h6
  · exact false_of_alt7_support_two D e hσeq hσ2 h2
  · exact false_of_alt7_support_four D e hσeq hσ2 h4
  · exact false_of_alt7_support_six D e hσeq hσ2 h6


private theorem a8_witness :
    let x : Perm (Fin 8) := swap 0 1 * swap 2 3
    let y₁ : Perm (Fin 8) := List.formPerm [5, 6, 7]
    let y₂ : Perm (Fin 8) := List.formPerm [4, 5, 6]
    let x' : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7
    let y₁' : Perm (Fin 8) := List.formPerm [2, 4, 6] * List.formPerm [3, 5, 7]
    let y₂' : Perm (Fin 8) := List.formPerm [2, 6, 5] * List.formPerm [3, 7, 4]
    Perm.sign y₁ = 1 ∧ Perm.sign y₂ = 1 ∧ y₁ * x = x * y₁ ∧ y₂ * x = x * y₂ ∧
      y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧ (y₁ * y₂) ^ 3 ≠ 1 ∧
      Perm.sign y₁' = 1 ∧ Perm.sign y₂' = 1 ∧ y₁' * x' = x' * y₁' ∧ y₂' * x' = x' * y₂' ∧
      y₁' ^ 3 = 1 ∧ y₂' ^ 3 = 1 ∧ (y₁' * y₂') ^ 3 ≠ 1 := by
  decide +kernel

private theorem false_of_alt8_support_four (D : LayerData X A τ B)
    (e : X ≃* alternatingGroup (Fin 8)) {σ : Perm (Fin 8)}
    (hσ : MulAut.congr e τ = MulAut.conjNormal σ) (hσ2 : σ * σ = 1)
    (hcard : σ.support.card = 4) : False := by
  have hr : (swap 0 1 * swap 2 3 : Perm (Fin 8)) * (swap 0 1 * swap 2 3) = 1 := by
    decide +kernel
  have hs : σ.support.card = (swap 0 1 * swap 2 3 : Perm (Fin 8)).support.card := by
    rw [hcard]
    decide +kernel
  have h := a8_witness
  dsimp only at h
  obtain ⟨hs₁, hs₂, hc₁, hc₂, hp₁, hp₂, hne, -, -, -, -, -, -, -⟩ := h
  let y₁ : alternatingGroup (Fin 8) := ⟨List.formPerm [5, 6, 7], hs₁⟩
  let y₂ : alternatingGroup (Fin 8) := ⟨List.formPerm [4, 5, 6], hs₂⟩
  have hc₁' : (y₁ : Perm (Fin 8)) * (swap 0 1 * swap 2 3) =
      (swap 0 1 * swap 2 3) * (y₁ : Perm (Fin 8)) := hc₁
  have hc₂' : (y₂ : Perm (Fin 8)) * (swap 0 1 * swap 2 3) =
      (swap 0 1 * swap 2 3) * (y₂ : Perm (Fin 8)) := hc₂
  have hp₁' : (y₁ : Perm (Fin 8)) ^ 3 = 1 := hp₁
  have hp₂' : (y₂ : Perm (Fin 8)) ^ 3 = 1 := hp₂
  have hne' : ((y₁ : Perm (Fin 8)) * (y₂ : Perm (Fin 8))) ^ 3 ≠ 1 := hne
  exact false_of_involution_W2 (D.map e) hσ hσ2 hr hs hc₁' hc₂' hp₁' hp₂' hne'

private theorem false_of_alt8_support_eight (D : LayerData X A τ B)
    (e : X ≃* alternatingGroup (Fin 8)) {σ : Perm (Fin 8)}
    (hσ : MulAut.congr e τ = MulAut.conjNormal σ) (hσ2 : σ * σ = 1)
    (hcard : σ.support.card = 8) : False := by
  have hr : (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 : Perm (Fin 8)) *
      (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7) = 1 := by decide +kernel
  have hs : σ.support.card =
      (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 : Perm (Fin 8)).support.card := by
    rw [hcard]
    decide +kernel
  have h := a8_witness
  dsimp only at h
  obtain ⟨-, -, -, -, -, -, -, hs₁, hs₂, hc₁, hc₂, hp₁, hp₂, hne⟩ := h
  let y₁ : alternatingGroup (Fin 8) :=
    ⟨List.formPerm [2, 4, 6] * List.formPerm [3, 5, 7], hs₁⟩
  let y₂ : alternatingGroup (Fin 8) :=
    ⟨List.formPerm [2, 6, 5] * List.formPerm [3, 7, 4], hs₂⟩
  have hc₁' : (y₁ : Perm (Fin 8)) * (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7) =
      (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7) * (y₁ : Perm (Fin 8)) := hc₁
  have hc₂' : (y₂ : Perm (Fin 8)) * (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7) =
      (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7) * (y₂ : Perm (Fin 8)) := hc₂
  have hp₁' : (y₁ : Perm (Fin 8)) ^ 3 = 1 := hp₁
  have hp₂' : (y₂ : Perm (Fin 8)) ^ 3 = 1 := hp₂
  have hne' : ((y₁ : Perm (Fin 8)) * (y₂ : Perm (Fin 8))) ^ 3 ≠ 1 := hne
  exact false_of_involution_W2 (D.map e) hσ hσ2 hr hs hc₁' hc₂' hp₁' hp₂' hne'

theorem false_of_alt8 (D : LayerData X A τ B) (e : X ≃* alternatingGroup (Fin 8)) : False := by
  have hcard8 : 15120 < Nat.card (alternatingGroup (Fin 8)) := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  obtain ⟨x, hx⟩ := (D.map e).inner hcard8
  have hσeq : MulAut.congr e τ =
      MulAut.conjNormal (H := alternatingGroup (Fin 8)) (x : Perm (Fin 8)) := by
    rw [hx]
    exact (MulAut.conjNormal_val (H := alternatingGroup (Fin 8)) (h := x)).symm
  have hσ2 : (x : Perm (Fin 8)) * (x : Perm (Fin 8)) = 1 := by
    apply sq_eq_one_of_conjNormal_sq (α := Fin 8)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have hsq := (D.map e).sq_A (MulAut.congr e τ) (D.map e).mem_A
    rwa [hσeq] at hsq
  have hσ1 : (x : Perm (Fin 8)) ≠ 1 := by
    intro h
    apply (D.map e).ne_one
    rw [hσeq, h]
    exact map_one _
  have hσ2' : (x : Perm (Fin 8)) ^ 2 = 1 := by simpa [pow_two] using hσ2
  have h4dvd : 4 ∣ (x : Perm (Fin 8)).support.card :=
    (CFSG.Holt.sign_eq_one_iff_four_dvd_card_support hσ2').mp x.2
  have h1lt : 1 < (x : Perm (Fin 8)).support.card :=
    Equiv.Perm.one_lt_card_support_of_ne_one hσ1
  have hle : (x : Perm (Fin 8)).support.card ≤ 8 := by
    simpa using Finset.card_le_univ (x : Perm (Fin 8)).support
  have hcard : (x : Perm (Fin 8)).support.card = 4 ∨
      (x : Perm (Fin 8)).support.card = 8 := by
    omega
  rcases hcard with h4 | h8
  · exact false_of_alt8_support_four D e hσeq hσ2 h4
  · exact false_of_alt8_support_eight D e hσeq hσ2 h8

end CFSG.GF2Type.Smith1979.OmegaPlus

end
