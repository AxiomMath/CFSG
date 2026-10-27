module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

section Rho

variable {G : Type} [Group G] (V : Subgroup G) [V.Normal]

theorem top_le_normalizer_of_normal : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := by
  rw [Subgroup.normalizer_eq_top V]

@[expose] noncomputable def ambRho : G →* MulAut ↥V :=
  (actOn V ⊤ (top_le_normalizer_of_normal V)).comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom

theorem ambRho_apply_coe (g : G) (v : ↥V) : ((ambRho V g v : ↥V) : G) = g * v * g⁻¹ :=
  actOn_apply_coe (V := V) (X := ⊤) (top_le_normalizer_of_normal V) ⟨g, trivial⟩ v

theorem ker_ambRho : (ambRho V).ker = Subgroup.centralizer (V : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h
    simp only [ambRho_apply_coe, MulAut.one_apply] at this
    have h2 : g * v * g⁻¹ = v := this
    calc v * g = (g * v * g⁻¹) * g := by rw [h2]
      _ = g * v := by group
  · intro h
    ext v
    rw [ambRho_apply_coe, MulAut.one_apply]
    have h1 := h v v.2
    show g * v * g⁻¹ = v
    rw [← h1, mul_inv_cancel_right]

theorem map_ambRho (A : Subgroup G) : A.map (ambRho V) = autOn A V := by
  ext x
  rw [mem_autOn_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, by rw [Subgroup.normalizer_eq_top V]; exact trivial⟩, hg, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

@[expose] noncomputable def ambRhoHat : G →* ↥(autOn (⊤ : Subgroup G) V) :=
  (ambRho V).codRestrict (autOn (⊤ : Subgroup G) V) fun g => by
    rw [← map_ambRho V]
    exact ⟨g, trivial, rfl⟩

theorem ambRhoHat_surjective : Function.Surjective (ambRhoHat V) := by
  rintro ⟨x, hx⟩
  rw [← map_ambRho V] at hx
  obtain ⟨g, -, rfl⟩ := hx
  exact ⟨g, rfl⟩

theorem centralizer_le_comap_ambRho (B : Subgroup (MulAut ↥V)) :
    Subgroup.centralizer (V : Set G) ≤ B.comap (ambRho V) := by
  intro g hg
  rw [← ker_ambRho V] at hg
  rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hg]
  exact B.one_mem

end Rho

end CFSG.CGT.PushingUpLit.CGT6
