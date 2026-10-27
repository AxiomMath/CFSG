module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Prod
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.WreathCj
import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std

variable {V : Type} [Group V] {G : Type} [Group G] {ρ : G →* MulAut V}

theorem isSimpleGroup_alt6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem exists_noncomm_alt6 : ∃ x y : alternatingGroup (Fin 6), x * y ≠ y * x :=
  ⟨c5, ⟨Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    by decide⟩

theorem Config.isSimpleGroup_C (c : Config ρ) : IsSimpleGroup c.C :=
  haveI := isSimpleGroup_alt6
  c.eC.isSimpleGroup

theorem Config.isSimpleGroup_D (c : Config ρ) : IsSimpleGroup c.D :=
  haveI := isSimpleGroup_alt6
  c.eD.isSimpleGroup

theorem Config.noncomm_C (c : Config ρ) : ∃ x ∈ c.C, ∃ y ∈ c.C, x * y ≠ y * x := by
  obtain ⟨x, y, h⟩ := exists_noncomm_alt6
  refine ⟨(c.eC.symm x : G), (c.eC.symm x).2, (c.eC.symm y : G), (c.eC.symm y).2, fun h' => h ?_⟩
  have h'' : c.eC.symm x * c.eC.symm y = c.eC.symm y * c.eC.symm x := Subtype.ext h'
  exact c.eC.symm.injective (by rw [map_mul, map_mul]; exact h'')

theorem Config.noncomm_D (c : Config ρ) : ∃ x ∈ c.D, ∃ y ∈ c.D, x * y ≠ y * x := by
  obtain ⟨x, y, h⟩ := exists_noncomm_alt6
  refine ⟨(c.eD.symm x : G), (c.eD.symm x).2, (c.eD.symm y : G), (c.eD.symm y).2, fun h' => h ?_⟩
  have h'' : c.eD.symm x * c.eD.symm y = c.eD.symm y * c.eD.symm x := Subtype.ext h'
  exact c.eD.symm.injective (by rw [map_mul, map_mul]; exact h'')

theorem Config.card_C_eq_card_D (c : Config ρ) : Nat.card c.C = Nat.card c.D := by
  rw [Nat.card_congr c.eC.toEquiv, Nat.card_congr c.eD.toEquiv]

theorem Config.sup_normal [Finite G] (c : Config ρ) (hN : fusionOddCore G = ⊥) :
    (c.C ⊔ c.D).Normal := by
  have hker : (QuotientGroup.mk' (fusionOddCore G)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact hN
  have h : c.C ⊔ c.D =
      (egaLayer (G ⧸ fusionOddCore G)).comap (QuotientGroup.mk' (fusionOddCore G)) := by
    rw [← c.map_eq, Subgroup.comap_map_eq, hker, sup_bot_eq]
  rw [h]
  have := egaLayer_normal (G ⧸ fusionOddCore G)
  exact Subgroup.Normal.comap inferInstance _

theorem Config.C_ne_D (c : Config ρ) : c.C ≠ c.D := by
  intro h
  have h1 : c.C = ⊥ := by
    have := c.inf_CD
    rwa [← h, inf_idem] at this
  have h2 := c.card_C_eq_card_D
  have h3 : Nat.card c.C = 360 := by
    rw [Nat.card_congr c.eC.toEquiv, card_alternatingGroup_six]
  rw [h1] at h3
  simp at h3

theorem Config.conj_dichotomy [Finite G] (c : Config ρ) (hN : fusionOddCore G = ⊥) (g : G) :
    (cj g c.C = c.C ∧ cj g c.D = c.D) ∨ (cj g c.C = c.D ∧ cj g c.D = c.C) := by
  have := c.isSimpleGroup_C
  have := c.isSimpleGroup_D
  have hK := c.sup_normal hN
  have h1 := cj_eq_or c.comm c.card_C_eq_card_D c.noncomm_C hK g
  have hcomm' : ∀ x ∈ c.D, ∀ y ∈ c.C, x * y = y * x := fun x hx y hy => (c.comm y hy x hx).symm
  have hK' : (c.D ⊔ c.C).Normal := by rw [sup_comm]; exact hK
  have h2 := cj_eq_or hcomm' c.card_C_eq_card_D.symm c.noncomm_D hK' g
  have hne := c.C_ne_D
  have hinj : ∀ H H' : Subgroup G, cj g H = cj g H' → H = H' := by
    intro H H' h
    rw [← cj_inv_cj g H, ← cj_inv_cj g H', h]
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact absurd (hinj _ _ (h1.trans h2.symm)) hne
  · rcases h2 with h2 | h2
    · exact absurd (hinj _ _ (h1.trans h2.symm)) hne
    · exact Or.inr ⟨h1, h2⟩

theorem fix_map {g : G} {S S' : Subgroup G} (h : cj g S = S') {v : V}
    (hv : ∀ x ∈ S, ρ x v = v) : ∀ x ∈ S', ρ x (ρ g v) = ρ g v := by
  intro y hy
  rw [← h, mem_cj] at hy
  have h1 := hv _ hy
  have : ρ y (ρ g v) = ρ g (ρ (g⁻¹ * y * g) v) := by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
    simp [mul_assoc]
  rw [this, h1]

theorem Config.exists_mul (c : Config ρ) (hV : Nat.card V = 256) (v : V) :
    ∃ u₁ ∈ c.U₁, ∃ u₂ ∈ c.U₂, v = u₁ * u₂ := by
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : Finite c.U₁ := Nat.finite_of_card_ne_zero (by rw [c.card_U₁]; omega)
  have : Finite c.U₂ := Nat.finite_of_card_ne_zero (by rw [c.card_U₂]; omega)
  let φ : c.U₁ × c.U₂ → V := fun p => (p.1 : V) * p.2
  have hinj : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : V) * b = a' * b' := h
    have e : ((a' : V)⁻¹ * a) = b' * (b : V)⁻¹ := by
      calc (a' : V)⁻¹ * a = (a' : V)⁻¹ * (a * b) * (b : V)⁻¹ := by group
        _ = (a' : V)⁻¹ * (a' * b') * (b : V)⁻¹ := by rw [h']
        _ = b' * (b : V)⁻¹ := by group
    have hm : ((a' : V)⁻¹ * a) ∈ c.U₁ ⊓ c.U₂ :=
      Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ a'.2) a.2, by
        rw [e]; exact Subgroup.mul_mem _ b'.2 (Subgroup.inv_mem _ b.2)⟩
    rw [c.inf_U, Subgroup.mem_bot] at hm
    have hb : (b' : V) * (b : V)⁻¹ = 1 := by rw [← e]; exact hm
    have ha : a = a' := Subtype.ext (inv_mul_eq_one.1 hm).symm
    subst ha
    exact Prod.ext rfl (Subtype.ext (mul_inv_eq_one.1 hb).symm)
  have hcard : Nat.card V ≤ Nat.card (c.U₁ × c.U₂) := by
    rw [Nat.card_prod, c.card_U₁, c.card_U₂, hV]
  obtain ⟨⟨a, b⟩, hab⟩ := (hinj.bijective_of_nat_card_le hcard).2 v
  exact ⟨a, a.2, b, b.2, hab.symm⟩

theorem Config.eq_one_of_fix (c : Config ρ) (hV : Nat.card V = 256) (hρ : Function.Injective ρ)
    (g : G) (h1 : ∀ v ∈ c.U₁, ρ g v = v) (h2 : ∀ v ∈ c.U₂, ρ g v = v) : g = 1 := by
  apply hρ
  rw [map_one]
  ext v
  obtain ⟨a, ha, b, hb, rfl⟩ := c.exists_mul hV v
  simp [map_mul, h1 a ha, h2 b hb]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
