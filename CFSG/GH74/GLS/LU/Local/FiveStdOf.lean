module

public import CFSG.GH74.GLS.LU.Local.FiveStdSetting

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.FiveStd

variable {G G' : Type} [Group G] [Group G']

theorem Model.comp_equiv {ι : E → G} (hM : Model ι) (Φ : G ≃* G') : Model (fun x => Φ (ι x)) where
  valid_one := hM.valid_one
  valid_mul := hM.valid_mul
  valid_inv := hM.valid_inv
  map_one := by
    show Φ (ι oneE) = 1
    rw [hM.map_one]
    exact _root_.map_one Φ
  map_mul := fun x y hx hy => by
    show Φ (ι (mulE x y)) = Φ (ι x) * Φ (ι y)
    rw [hM.map_mul x y hx hy]
    exact _root_.map_mul Φ _ _
  map_inv := fun x hx => by
    show Φ (ι (invE x)) = (Φ (ι x))⁻¹
    rw [hM.map_inv x hx]
    exact _root_.map_inv Φ _
  inj := fun x y hx hy h => hM.inj x y hx hy (Φ.injective h)

omit [Group G] [Group G'] in
theorem S_comp_image {ι : E → G} (f : G → G') (L : List E) : S (fun x => f (ι x)) L = f '' S ι L := by
  ext g
  simp only [mem_S, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨ι x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

end CFSG.GH74.GLS.LU.Local.FiveStd

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd

variable {G G' : Type} [Group G] [Group G']

theorem map_cjL (Φ : G ≃* G') (g : G) (K : Subgroup G) :
    cjL (Φ g) (K.map Φ.toMonoidHom) = (cjL g K).map Φ.toMonoidHom := by
  unfold cjL
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul]

theorem centralizer_equiv_eq (Φ : G ≃* G') (z : G) :
    Cz (Φ z) = (Cz z).map Φ.toMonoidHom := by
  have : (Subgroup.centralizer ({z} : Set G)).map Φ.toMonoidHom = Subgroup.centralizer ({Φ z} : Set G') := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      show Φ y * Φ z = Φ z * Φ y
      rw [← map_mul, ← map_mul, hy]
    · intro hx
      refine ⟨Φ.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
  exact this.symm

@[expose] noncomputable def FiveStdSetting.ofEquiv (st : FiveStdSetting G) (Φ : G ≃* G') : FiveStdSetting G' where
  ι := fun x => Φ (st.ι x)
  model := st.model.comp_equiv Φ
  K₁ := st.K₁.map Φ.toMonoidHom
  K₂ := st.K₂.map Φ.toMonoidHom
  hK₁ := by
    rw [S_comp_image, ← st.hK₁]
    rfl
  hK₂ := by
    rw [S_comp_image, ← st.hK₂]
    rfl
  hC := by
    rw [S_comp_image, ← st.hC, centralizer_equiv_eq]
    rfl
  hcomm := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show Φ x * Φ y = Φ y * Φ x
    rw [← map_mul, ← map_mul, st.hcomm x hx y hy]
  hKK := by
    intro x hx
    rw [st.hKK x hx]
    constructor
    · intro h
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 h
      exact Set.mem_mul.2 ⟨Φ a, ⟨a, ha, rfl⟩, Φ b, ⟨b, hb, rfl⟩, by rw [← map_mul, hab]⟩
    · intro h
      obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩ := Set.mem_mul.1 h
      refine Set.mem_mul.2 ⟨a, ha, b, hb, Φ.injective ?_⟩
      rw [map_mul]
      exact hab
  hblock := by
    intro x hx hs
    obtain ⟨h1, h2⟩ := st.hblock x hx hs
    show cjL (Φ (st.ι x)) (st.K₁.map Φ.toMonoidHom) = st.K₁.map Φ.toMonoidHom ∧
      cjL (Φ (st.ι x)) (st.K₂.map Φ.toMonoidHom) = st.K₂.map Φ.toMonoidHom
    rw [map_cjL, map_cjL, h1, h2]
    exact ⟨rfl, rfl⟩

end CFSG.GH74.GLS.LU.Local.Five
