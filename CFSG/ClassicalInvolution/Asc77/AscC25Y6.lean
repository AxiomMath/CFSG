module

public import CFSG.ClassicalInvolution.Asc77.AscC25X13
public import CFSG.ClassicalInvolution.Asc77.AscC25Y4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace C25Y

section Four

variable {G : Type} [Group G]

theorem eq_closure_of_card_le_four [Finite G] {A : Subgroup G} {a z : G}
    (hcard : Nat.card A ≤ 4) (ha2 : a * a = 1) (hz2 : z * z = 1) (ha1 : a ≠ 1) (hz1 : z ≠ 1)
    (haz : a ≠ z) (hcomm : a * z = z * a) (haA : a ∈ A) (hzA : z ∈ A) :
    A = Subgroup.closure ({a, z} : Set G) ∧ IsElemAbelian2 A 2 := by
  have hE := T7A.isElemAbelian2_closure_pair ha2 hz2 ha1 hz1 haz hcomm
  have hle : Subgroup.closure ({a, z} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact haA
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hzA
  have hc : Nat.card ↥(Subgroup.closure ({a, z} : Set G)) = 4 := by
    rw [hE.1]; norm_num
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hc]; exact hcard)
  refine ⟨heq.symm, ?_⟩
  rw [← heq]
  exact hE

theorem comm_of_forall_sq_eq_one {A : Subgroup G} (hA : ∀ x ∈ A, x * x = 1) {x y : G} (hx : x ∈ A)
    (hy : y ∈ A) : x * y = y * x := by
  have h1 := hA (x * y) (A.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hA x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hA y hy)
  have : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [mul_inv_rev, hxi, hyi] at this
  exact this

end Four

section Swap

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem exceptional_swap (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G}
    (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) :
    ∃ t' : G, t' ∈ (S : Subgroup G) ∧ t' * t' = 1 ∧ t' * a = a * t' ∧ t' * z = z * t' ∧
      conjSub t' R = R' ∧ (∃ g : G, g * z * g⁻¹ = t') ∧ (¬ ∃ y : G, y * z * y⁻¹ = t' * z) ∧
      ((∀ h ∈ Subgroup.centralizer ({a} : Set G), h * z * h⁻¹ ≠ t') ∨
        (∀ m ∈ Subgroup.centralizer ({a * z} : Set G), m * z * m⁻¹ ≠ t')) := by
  classical
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have haS : a ∈ (S : Subgroup G) := haA.1
  have hcent := Subgroup.mem_centralizer_iff.mp haA.2
  have haR : ∀ x ∈ R, a * x = x * a := fun x hx => (hcent x (Subgroup.mem_sup_left hx)).symm
  have haR' : ∀ x ∈ R', a * x = x * a := fun x hx => (hcent x (Subgroup.mem_sup_right hx)).symm
  obtain ⟨-, -, -, hK₂, hK₂', -⟩ := C25X.layer_a_frame hyp ha2 ha1 haR haR'
  obtain ⟨t', ht'S, ht'2, ⟨g, hg⟩, ht'R, hnf⟩ := T7G2.exists_swap_nonfused hyp
  have hRne : R ≠ R' := T7ER.ne_of_hyp25 hyp
  have hzt : z ≠ t' := by
    intro h
    apply hRne
    have h1 : conjSub t' R = R := by
      rw [← h]
      exact T7F2.conjSub_eq_of_centralizes fun r hr => hyp.hzS r (hyp.hR.2.2 hr)
    rw [← ht'R, h1]
  have ht'z : t' * z = z * t' := hyp.hzS t' ht'S
  have hzc : z * t' * z⁻¹ = t' := by
    calc z * t' * z⁻¹ = (t' * z) * z⁻¹ := by rw [ht'z]
      _ = t' := by group
  have hat : t' * a = a * t' := T7U.comm_swap_of_normal_four hyp ht'S ht'2 hg hnf haS hconj
  refine ⟨t', ht'S, ht'2, hat, ht'z, ht'R, ⟨g, hg⟩, hnf, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨h, hhC, hh⟩, ⟨m, hmC, hm⟩⟩ := hcon
  exact not_swap_in_both hyp hK₂.2 hK₂'.2 hzt hzc hnf hh
    (Subgroup.mem_centralizer_singleton_iff.mp hhC) hm
    (Subgroup.mem_centralizer_singleton_iff.mp hmC)

end Swap

section SwapFusion

variable {G : Type} [Group G]

theorem swap_fusion_left {a z t' h : G} (hh : h * z * h⁻¹ = t') (hha : h * a = a * h) :
    h * (a * z) * h⁻¹ = a * t' := by
  calc h * (a * z) * h⁻¹ = (h * a * h⁻¹) * (h * z * h⁻¹) := by group
    _ = a * t' := by
      rw [hh]
      congr 1
      calc h * a * h⁻¹ = (a * h) * h⁻¹ := by rw [hha]
        _ = a := by group

theorem swap_fusion_right {a z t' m : G} (hz2 : z * z = 1) (hm : m * z * m⁻¹ = t')
    (hma : m * (a * z) = (a * z) * m) : m * a * m⁻¹ = (a * z) * t' := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  calc m * a * m⁻¹ = (m * (a * z) * m⁻¹) * (m * z⁻¹ * m⁻¹) := by group
    _ = (a * z) * t' := by
      rw [hzi, hm]
      congr 1
      calc m * (a * z) * m⁻¹ = ((a * z) * m) * m⁻¹ := by rw [hma]
        _ = a * z := by group

end SwapFusion

section Assembly

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C25_11Ω5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z →
          (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) →
          (∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
            b = 1 ∨ b = a ∨ b = z ∨ b = a * z) →
          z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
          z ∉ zStarOf (Subgroup.centralizer ({a * z} : Set G)) →
          LayerOrthType p f Ω (a * z) 5 true →
            ¬ LayerOrthType p f Ω a 5 true

variable {p f}



theorem c25_11Typed_of_residuals (h9 : C25_9 p f) (hM6 : Layer6Cen4 p f) (h5 : C25_11Ω5 p f) :
    C25X.C25_11Typed p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj
  have hzA := T7T.z_mem_centralizer_of_hyp hyp
  obtain ⟨hcard, hex⟩ := h9 G Ω K K' W S R R' z t u₁ u₂ hyp
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have haz' : a * z = z * a := hyp.hzS a haA.1
  obtain ⟨hAeq, hE⟩ := eq_closure_of_card_le_four hcard ha2 hz2 ha1 hz1 haz haz' haA hzA
  have hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      b = 1 ∨ b = a ∨ b = z ∨ b = a * z := fun b hb =>
    mem_closure_pair ha2 hz2 haz' (hAeq ▸ hb)
  have hc4 : Nat.card ↥((S : Subgroup G) ⊓
      Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 4 := by
    rw [hE.1]; norm_num
  obtain ⟨a', hcl, hb1, hb2⟩ := hex hc4
  have ha'A : a' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    rw [← hcl]
    exact Subgroup.subset_closure (by simp)
  have ha'2 : a' * a' = 1 := hE.2 a' ha'A
  have ha'z : a' * z = z * a' := comm_of_forall_sq_eq_one hE.2 ha'A hzA
  have haa' : a = a' ∨ a = a' * z := by
    have hmem : a ∈ Subgroup.closure ({a', z} : Set G) := by rw [hcl]; exact haA
    rcases mem_closure_pair ha'2 hz2 ha'z hmem with h | h | h | h
    · exact absurd h ha1
    · exact Or.inl h
    · exact absurd h haz
    · exact Or.inr h
  have hazz : a' * z * z = a' := by rw [mul_assoc, hz2, mul_one]
  have hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
    rcases haa' with h | h
    · rw [h]; exact hb1
    · rw [h]; exact hb2
  have hbad' : z ∉ zStarOf (Subgroup.centralizer ({a * z} : Set G)) := by
    rcases haa' with h | h
    · rw [h]; exact hb2
    · rw [h, hazz]; exact hb1
  have haA₂ : a * z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ haA hzA
  have ha₂2 : (a * z) * (a * z) = 1 := hE.2 _ (hAeq ▸ haA₂)
  have ha₂1 : a * z ≠ 1 := by
    intro h
    apply haz
    have : a = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right hz2]
  have ha₂z : a * z ≠ z := by
    intro h
    apply ha1
    calc a = (a * z) * z⁻¹ := by group
      _ = z * z⁻¹ := by rw [h]
      _ = 1 := by group
  have hazz' : (a * z) * z = a := by rw [mul_assoc, hz2, mul_one]
  have hconj₂ : ∀ s ∈ (S : Subgroup G), s * (a * z) * s⁻¹ = a * z ∨
      s * (a * z) * s⁻¹ = (a * z) * z := by
    intro s hs
    have hszs : s * z * s⁻¹ = z := by
      calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hyp.hzS s hs]
        _ = z := by group
    have hsa : s * (a * z) * s⁻¹ = (s * a * s⁻¹) * z := by
      calc s * (a * z) * s⁻¹ = (s * a * s⁻¹) * (s * z * s⁻¹) := by group
        _ = (s * a * s⁻¹) * z := by rw [hszs]
    rcases hconj s hs with h | h
    · left; rw [hsa, h]
    · right; rw [hsa, h, hazz']
  have hA0₂ : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      b = 1 ∨ b = a * z ∨ b = z ∨ b = (a * z) * z := by
    intro b hb
    rcases hA0 b hb with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (by rw [hazz', h])))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  have haR₂ : ∀ x ∈ R, (a * z) * x = x * (a * z) := by
    intro x hx
    have hcent := Subgroup.mem_centralizer_iff.mp haA.2
    have h1 : a * x = x * a := (hcent x (Subgroup.mem_sup_left hx)).symm
    have h2 : x * z = z * x := hyp.hzS x (hyp.hR.2.2 hx)
    calc (a * z) * x = a * (z * x) := by group
      _ = a * (x * z) := by rw [h2]
      _ = (a * x) * z := by group
      _ = (x * a) * z := by rw [h1]
      _ = x * (a * z) := by group
  have haR'₂ : ∀ x ∈ R', (a * z) * x = x * (a * z) := by
    intro x hx
    have hcent := Subgroup.mem_centralizer_iff.mp haA.2
    have h1 : a * x = x * a := (hcent x (Subgroup.mem_sup_right hx)).symm
    have h2 : x * z = z * x := hyp.hzS x (hyp.hR'.2.2 hx)
    calc (a * z) * x = a * (z * x) := by group
      _ = a * (x * z) := by rw [h2]
      _ = (a * x) * z := by group
      _ = (x * a) * z := by rw [h1]
      _ = x * (a * z) := by group
  have h5z : LayerOrthType p f Ω (a * z) 5 true := by
    rcases C25X.layer_a_typed_proved hyp ha₂2 ha₂1 haR₂ haR'₂ with h | h | h
    · exact absurd h hbad'
    · exact h
    · exact absurd h (not_layerOrthSix hM6 hyp ha₂2 ha₂1 ha₂z haA₂ hconj₂ hA0₂)
  rintro (hL5 | hL6)
  · exact h5 G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hA0 hbad hbad' h5z hL5
  · exact not_layerOrthSix hM6 hyp ha2 ha1 haz haA hconj hA0 hL6

theorem c25_11E4_of_residuals (h9 : C25_9 p f) (hM6 : Layer6Cen4 p f) (h5 : C25_11Ω5 p f) :
    T7U.C25_11E4 p f :=
  C25X.c25_11E4_of_typed (c25_11Typed_of_residuals h9 hM6 h5)

theorem c25_11_of_residuals (h9 : C25_9 p f) (hM6 : Layer6Cen4 p f) (h5 : C25_11Ω5 p f) :
    C25_11 p f :=
  C25X.c25_11_of_typed (c25_11Typed_of_residuals h9 hM6 h5)

end Assembly

end C25Y

end CFSG.ClassicalInvolution.Asc77
