module

public import CFSG.GH74.QTGen4.U42.CoordsB
public import CFSG.GH74.QTGen4.U42.CoordsC
public import CFSG.GH74.QTGen4.U42.ElemAb16

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

theorem sign_of_InK4 : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → σ.sign = 1 := by
  decide +kernel

section Plain

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem LT_le_normalizer (S : A5.Setting G T L V) : L ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
  sup_le S.frame.L_le S.frame.T_le

theorem V_le_LT (S : A5.Setting G T L V) : V ≤ L ⊔ T := S.reduced.1

noncomputable def coordData (S : A5.Setting G T L V) (hO : pCoreOf 2 (L ⊔ T) = V) :
    CoordData ↥(L ⊔ T) where
  V := V.subgroupOf (L ⊔ T)
  hV := (Subgroup.normal_subgroupOf_iff_le_normalizer (V_le_LT S)).mpr (LT_le_normalizer S)
  ψ := (Subgroup.subgroupOfEquivOfLe (V_le_LT S)).trans S.frame.ψ
  ρ := S.frame.ρ.comp (Subgroup.inclusion (LT_le_normalizer S))
  ker_ρ := by
    have h1 : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) = V := S.cLT.trans hO
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show S.frame.ρ ⟨(m : G), LT_le_normalizer S m.2⟩ = 1 ↔ (m : G) ∈ V
    rw [S.rho_eq_one_iff]
    constructor
    · intro h
      have hm : (m : G) ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := ⟨m.2, h⟩
      rw [h1] at hm
      exact hm
    · intro h
      have hm : (m : G) ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
        rw [h1]; exact h
      exact hm.2
  conj_ψ := fun m v => S.psi_conj ⟨(m : G), LT_le_normalizer S m.2⟩
    ⟨(v : G), Subgroup.mem_subgroupOf.mp v.2⟩

theorem coordData_V (S : A5.Setting G T L V) (hO : pCoreOf 2 (L ⊔ T) = V) :
    (coordData S hO).V = V.subgroupOf (L ⊔ T) := by
  simp only [coordData]

theorem mem_coordData_V (S : A5.Setting G T L V) (hO : pCoreOf 2 (L ⊔ T) = V)
    (m : ↥(L ⊔ T)) : m ∈ (coordData S hO).V ↔ (m : G) ∈ V := Iff.rfl

theorem coordData_psi_apply (S : A5.Setting G T L V) (hO : pCoreOf 2 (L ⊔ T) = V)
    (v : ↥(coordData S hO).V) :
    (coordData S hO).ψ v = S.frame.ψ
      ⟨((v : ↥(L ⊔ T)) : G), (mem_coordData_V S hO _).mp v.2⟩ := by
  simp only [coordData, MulEquiv.trans_apply] <;> rfl

theorem coordData_rho_apply (S : A5.Setting G T L V) (hO : pCoreOf 2 (L ⊔ T) = V)
    (m : ↥(L ⊔ T)) :
    (coordData S hO).ρ m = S.frame.ρ ⟨(m : G), LT_le_normalizer S m.2⟩ := by
  simp only [coordData, MonoidHom.comp_apply] <;> rfl

def IsCoords (S : A5.Setting G T L V) {R : Subgroup (Equiv.Perm (Fin 5))}
    (e : ↥(L ⊔ T) ≃* Mof R) : Prop :=
  (∀ (v : G) (hv : v ∈ V),
      ((e ⟨v, V_le_LT S hv⟩ : Mof R) : Mc) = SemidirectProduct.inl (S.frame.ψ ⟨v, hv⟩)) ∧
    ∀ m : ↥(L ⊔ T),
      ((e m : Mof R) : Mc).right = S.frame.ρ ⟨(m : G), LT_le_normalizer S m.2⟩

theorem IsCoords.mk {S : A5.Setting G T L V} {R : Subgroup (Equiv.Perm (Fin 5))}
    (e : ↥(L ⊔ T) ≃* Mof R)
    (hV : ∀ (v : G) (hv : v ∈ V),
      ((e ⟨v, V_le_LT S hv⟩ : Mof R) : Mc) = SemidirectProduct.inl (S.frame.ψ ⟨v, hv⟩))
    (hR : ∀ m : ↥(L ⊔ T),
      ((e m : Mof R) : Mc).right = S.frame.ρ ⟨(m : G), LT_le_normalizer S m.2⟩) :
    IsCoords S e := ⟨hV, hR⟩

theorem IsCoords.left {S : A5.Setting G T L V} {R : Subgroup (Equiv.Perm (Fin 5))}
    {e : ↥(L ⊔ T) ≃* Mof R} (he : IsCoords S e) (v : G) (hv : v ∈ V) :
    ((e ⟨v, V_le_LT S hv⟩ : Mof R) : Mc) = SemidirectProduct.inl (S.frame.ψ ⟨v, hv⟩) :=
  he.1 v hv

theorem IsCoords.right {S : A5.Setting G T L V} {R : Subgroup (Equiv.Perm (Fin 5))}
    {e : ↥(L ⊔ T) ≃* Mof R} (he : IsCoords S e) (m : ↥(L ⊔ T)) :
    ((e m : Mof R) : Mc).right = S.frame.ρ ⟨(m : G), LT_le_normalizer S m.2⟩ :=
  he.2 m

theorem sign_rho_LT (S : A5.Setting G T L V)
    (hP : _root_.CFSG.GH74.QTGen4.U42.Setting.PlainCase S) (m : ↥(L ⊔ T)) :
    (S.frame.ρ ⟨(m : G), LT_le_normalizer S m.2⟩).sign = 1 := by
  let Ke : Subgroup ↥(Subgroup.normalizer (V : Set G)) :=
    (Equiv.Perm.sign.comp S.frame.ρ).ker
  let K : Subgroup G := Ke.map (Subgroup.normalizer (V : Set G)).subtype
  have hL : L ≤ K := by
    intro g hg
    refine Subgroup.mem_map.mpr ⟨⟨g, S.frame.L_le hg⟩, ?_, rfl⟩
    show (S.frame.ρ ⟨g, S.frame.L_le hg⟩).sign = 1
    exact (S.frame.image_L _).1 ⟨⟨g, S.frame.L_le hg⟩, hg, rfl⟩
  have hT : T ≤ K := by
    intro g hg
    refine Subgroup.mem_map.mpr ⟨⟨g, S.frame.T_le hg⟩, ?_, rfl⟩
    show (S.frame.ρ ⟨g, S.frame.T_le hg⟩).sign = 1
    exact sign_of_InK4 _ (hP ⟨g, S.frame.T_le hg⟩ hg)
  obtain ⟨y, hy, hym⟩ := Subgroup.mem_map.mp ((sup_le hL hT) m.2)
  have hyeq : y = ⟨(m : G), LT_le_normalizer S m.2⟩ := Subtype.ext hym
  rw [← hyeq]
  exact MonoidHom.mem_ker.mp hy

theorem rho_range_LT (S : A5.Setting G T L V)
    (hP : _root_.CFSG.GH74.QTGen4.U42.Setting.PlainCase S) (hO : pCoreOf 2 (L ⊔ T) = V) :
    (coordData S hO).ρ.range = alternatingGroup (Fin 5) := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.2 (sign_rho_LT S hP m)
  · intro σ hσ
    obtain ⟨g, hgL, hgσ⟩ := (S.frame.image_L σ).2 (Equiv.Perm.mem_alternatingGroup.1 hσ)
    exact MonoidHom.mem_range.mpr ⟨⟨(g : G), (le_sup_left : L ≤ L ⊔ T) hgL⟩, hgσ⟩

theorem exists_coords_plain (S : A5.Setting G T L V) (hO : pCoreOf 2 (L ⊔ T) = V)
    (hP : _root_.CFSG.GH74.QTGen4.U42.Setting.PlainCase S) :
    ∃ e : ↥(L ⊔ T) ≃* Mof (alternatingGroup (Fin 5)), IsCoords S e := by
  classical
  have hVT : (coordData S hO).V ≤ T.subgroupOf (L ⊔ T) :=
    fun x hx => Subgroup.mem_subgroupOf.mpr (S.V_le_T (Subgroup.mem_subgroupOf.mp hx))
  have hT : IsPGroup 2 (T.subgroupOf (L ⊔ T)) := by
    intro g
    obtain ⟨k, hk⟩ := S.isPGroup_T ⟨((g : ↥(L ⊔ T)) : G), Subgroup.mem_subgroupOf.mp g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun x : ↥T => (x : G)) hk
    simpa using this
  have hTi : ¬ 2 ∣ (T.subgroupOf (L ⊔ T)).index := S.sylow_LT.2.2
  have hρT : ∀ t ∈ T.subgroupOf (L ⊔ T), InK4 ((coordData S hO).ρ t) := fun t ht =>
    hP ⟨(t : G), LT_le_normalizer S t.2⟩ (Subgroup.mem_subgroupOf.mp ht)
  have hK4 : ∀ σ : Equiv.Perm (Fin 5), InK4 σ →
      ∃ t ∈ T.subgroupOf (L ⊔ T), (coordData S hO).ρ t = σ := by
    intro σ hσ
    obtain ⟨g, hgT, hgσ⟩ := S.frame.K4_T σ hσ
    exact ⟨⟨(g : G), (le_sup_right : T ≤ L ⊔ T) hgT⟩, Subgroup.mem_subgroupOf.mpr hgT, hgσ⟩
  obtain ⟨A, hA, hA'⟩ := (coordData S hO).exists_complement_plain (T.subgroupOf (L ⊔ T))
    hVT hT hTi hρT hK4
  obtain ⟨e, he1, he2⟩ := (coordData S hO).equiv_of_complement A hA hA'
  refine ⟨e.trans (MulEquiv.subgroupCongr (congrArg Mof (rho_range_LT S hP hO))), ?_, ?_⟩
  · intro v hv
    exact he1 ⟨⟨v, V_le_LT S hv⟩, Subgroup.mem_subgroupOf.mpr hv⟩
  · intro m
    exact he2 m

end Plain

end CFSG.GH74.QTGen4.U42
