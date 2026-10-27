module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.AGLEmbedding.U62O10Cent

variable {P G A : Type*} [Group P] [Group G] [Group A]

theorem card_centralizer_aut_mul (c : G →* MulAut P) (f : MulAut P →* A)
    (hker : f.ker = c.range) (hZ : c.ker ≤ Subgroup.center G) (x : P) (y : G)
    (hy : c y = MulAut.conj x) :
    ∃ r s : ℕ, r ∣ Nat.card A ∧ s ∣ Nat.card c.ker ∧
      ((∀ g : G, c g * c y = c y * c g → g * y = y * g) → s = 1) ∧
      Nat.card (Subgroup.centralizer ({MulAut.conj x} : Set (MulAut P))) * Nat.card c.ker =
        Nat.card (Subgroup.centralizer ({y} : Set G)) * s * r := by
  classical
  set S := Subgroup.centralizer ({MulAut.conj x} : Set (MulAut P)) with hS
  set T : Subgroup G := S.comap c with hT
  have hTmem : ∀ g : G, g ∈ T ↔ c g * c y = c y * c g := fun g => by
    rw [hT, Subgroup.mem_comap, hS, Subgroup.mem_centralizer_singleton_iff, hy]
  have hkerT : c.ker ≤ T := fun g hg => by
    rw [hTmem, MonoidHom.mem_ker.1 hg, one_mul, mul_one]
  have hCT : Subgroup.centralizer ({y} : Set G) ≤ T := fun g hg => by
    rw [hTmem, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hg]
  let cT : T →* MulAut P := c.comp T.subtype
  have h1 := Subgroup.card_ker_mul_card_range cT
  have h1k : Nat.card cT.ker = Nat.card c.ker :=
    Nat.card_congr
      { toFun := fun g => ⟨(g.1 : G), g.2⟩
        invFun := fun g => ⟨⟨g.1, hkerT g.2⟩, g.2⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
  have h1r : cT.range = S ⊓ c.range := by
    ext s
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨Subgroup.mem_comap.1 g.2, g.1, rfl⟩
    · rintro ⟨hsS, g, rfl⟩
      exact ⟨⟨g, Subgroup.mem_comap.2 hsS⟩, rfl⟩
  let fS : S →* A := f.comp S.subtype
  have h2 := Subgroup.card_ker_mul_card_range fS
  have h2k : Nat.card fS.ker = Nat.card (S ⊓ c.range : Subgroup (MulAut P)) :=
    Nat.card_congr
      { toFun := fun s => ⟨s.1.1, s.1.2, by
          rw [← hker]; exact MonoidHom.mem_ker.2 s.2⟩
        invFun := fun s => ⟨⟨s.1, s.2.1⟩, by
          change f s.1 = 1
          rw [← MonoidHom.mem_ker, hker]; exact s.2.2⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
  have h2r : Nat.card fS.range ∣ Nat.card A := Subgroup.card_subgroup_dvd_card fS.range
  have hz : ∀ z ∈ c.ker, ∀ w : G, w * z = z * w := fun z hz w =>
    Subgroup.mem_center_iff.1 (hZ hz) w
  have hψmem : ∀ g : T, ((g : G) * y * (g : G)⁻¹ * y⁻¹) ∈ c.ker := fun g => by
    have := (hTmem g).1 g.2
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, this]
    group
  let ψ : T →* c.ker :=
    { toFun := fun g => ⟨(g : G) * y * (g : G)⁻¹ * y⁻¹, hψmem g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g g' => by
        apply Subtype.ext
        have h' := hz _ (hψmem g') (g : G)
        change (g : G) * (g' : G) * y * ((g : G) * (g' : G))⁻¹ * y⁻¹ =
          ((g : G) * y * (g : G)⁻¹ * y⁻¹) * ((g' : G) * y * (g' : G)⁻¹ * y⁻¹)
        calc (g : G) * (g' : G) * y * ((g : G) * (g' : G))⁻¹ * y⁻¹
            = (g : G) * ((g' : G) * y * (g' : G)⁻¹ * y⁻¹) * (g : G)⁻¹ *
                ((g : G) * y * (g : G)⁻¹ * y⁻¹) := by group
          _ = ((g' : G) * y * (g' : G)⁻¹ * y⁻¹) * ((g : G) * y * (g : G)⁻¹ * y⁻¹) := by
            rw [h']
            group
          _ = ((g : G) * y * (g : G)⁻¹ * y⁻¹) * ((g' : G) * y * (g' : G)⁻¹ * y⁻¹) :=
            hz _ (hψmem g) _ }
  have h3 := Subgroup.card_ker_mul_card_range ψ
  have hψker : ∀ g : T, g ∈ ψ.ker ↔ (g : G) * y = y * (g : G) := fun g => by
    rw [MonoidHom.mem_ker]
    change (⟨(g : G) * y * (g : G)⁻¹ * y⁻¹, hψmem g⟩ : c.ker) = 1 ↔ _
    rw [Subtype.ext_iff]
    change (g : G) * y * (g : G)⁻¹ * y⁻¹ = 1 ↔ _
    constructor
    · intro h
      calc (g : G) * y = ((g : G) * y * (g : G)⁻¹ * y⁻¹) * (y * (g : G)) := by group
        _ = y * (g : G) := by rw [h, one_mul]
    · intro h
      calc (g : G) * y * (g : G)⁻¹ * y⁻¹ = (y * (g : G)) * (g : G)⁻¹ * y⁻¹ := by rw [h]
        _ = 1 := by group
  have h3k : Nat.card ψ.ker = Nat.card (Subgroup.centralizer ({y} : Set G)) :=
    Nat.card_congr
      { toFun := fun g => ⟨(g.1 : G), Subgroup.mem_centralizer_singleton_iff.2
          ((hψker g.1).1 g.2)⟩
        invFun := fun g => ⟨⟨g.1, hCT g.2⟩, (hψker ⟨g.1, hCT g.2⟩).2
          (Subgroup.mem_centralizer_singleton_iff.1 g.2)⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
  have h3r : Nat.card ψ.range ∣ Nat.card c.ker := Subgroup.card_subgroup_dvd_card ψ.range
  refine ⟨Nat.card fS.range, Nat.card ψ.range, h2r, h3r, fun hall => ?_, ?_⟩
  · have : ψ.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      have := hall g ((hTmem g).1 g.2)
      change (g : G) * y * (g : G)⁻¹ * y⁻¹ = 1
      rw [this]
      group
    rw [this, Subgroup.card_bot]
  · rw [h3k] at h3
    rw [h1k, h1r] at h1
    rw [h2k] at h2
    have e1 : Nat.card S = Nat.card (S ⊓ c.range : Subgroup (MulAut P)) * Nat.card fS.range :=
      h2.symm
    have e2 : Nat.card T = Nat.card c.ker * Nat.card (S ⊓ c.range : Subgroup (MulAut P)) :=
      h1.symm
    have e3 : Nat.card T = Nat.card (Subgroup.centralizer ({y} : Set G)) * Nat.card ψ.range :=
      h3.symm
    calc Nat.card S * Nat.card c.ker
        = Nat.card (S ⊓ c.range : Subgroup (MulAut P)) * Nat.card fS.range * Nat.card c.ker := by
          rw [e1]
      _ = (Nat.card c.ker * Nat.card (S ⊓ c.range : Subgroup (MulAut P))) *
          Nat.card fS.range := by ring
      _ = Nat.card T * Nat.card fS.range := by rw [e2]
      _ = Nat.card (Subgroup.centralizer ({y} : Set G)) * Nat.card ψ.range *
          Nat.card fS.range := by rw [e3]

end CFSG.AGLEmbedding.U62O10Cent
