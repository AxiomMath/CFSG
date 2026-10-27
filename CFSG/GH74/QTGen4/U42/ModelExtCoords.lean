module

public import CFSG.GH74.QTGen4.U42.ModelExtFrame
public import CFSG.GH74.QTGen4.U42.ModelExtComplement
public import CFSG.GH74.QTGen4.U42.CoordsC
public import CFSG.GH74.QTGen4.U42.ModelCoords

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5 CFSG.Quasithin.H13.F431.U42 U42F431
open CFSG.Quasithin.H13.F431.U42Aut

@[expose] noncomputable def permHat4 (g : ↥P2h) : Equiv.Perm (Fin 5) :=
  sigma0 * permHat g * sigma0⁻¹

@[expose] noncomputable def permHomHat4 : ↥P2h →* Equiv.Perm (Fin 5) :=
  (MulAut.conj sigma0).toMonoidHom.comp permHomHat

theorem permHomHat4_apply (g : ↥P2h) : permHomHat4 g = permHat4 g := rfl

theorem permHat4_inclP2 (g : ↥P2) : permHat4 (inclP2 g) = permOf4 g := by
  rw [permHat4, permOf4_apply, permHat_inclP2]

theorem permHat4_eq_one_iff (g : ↥P2h) : permHat4 g = 1 ↔ permHat g = 1 := by
  change sigma0 * permHat g * sigma0⁻¹ = 1 ↔ permHat g = 1
  constructor
  · intro h
    have h' := congrArg (fun t => sigma0⁻¹ * t * sigma0) h
    simpa [mul_assoc] using h'
  · intro h
    simp [h]

theorem hatV_subgroupOf_normal : (VA.subgroupOf P2h).Normal := by
  refine ⟨fun v hv g => ?_⟩
  change (g : Ah) * (v : Ah) * (g : Ah)⁻¹ ∈ VA
  exact P2h_conj_VA g.2 (Subgroup.mem_subgroupOf.mp hv)

@[expose] noncomputable def modelCoordDataExt : CoordData ↥P2h where
  V := VA.subgroupOf P2h
  hV := hatV_subgroupOf_normal
  ψ := (Subgroup.subgroupOfEquivOfLe VA_le_P2h).trans (psiHat.trans (pact sigma0))
  ρ := permHomHat4
  ker_ρ := by
    ext g
    rw [MonoidHom.mem_ker, permHomHat4_apply, permHat4_eq_one_iff]
    change permHomHat g = 1 ↔ _
    rw [← MonoidHom.mem_ker, ker_permHomHat]
  conj_ψ := by
    intro g v
    have hv : (v : Ah) ∈ VA := Subgroup.mem_subgroupOf.mp v.2
    show pact sigma0 (psiHat ⟨(g : Ah) * (v : Ah) * (g : Ah)⁻¹,
        P2h_conj_VA g.2 hv⟩) = pact (permHomHat4 g) (pact sigma0 (psiHat ⟨(v : Ah), hv⟩))
    rw [psiHat_conj, permHomHat4_apply]
    exact (pact_conj sigma0 (permHat g) (psiHat ⟨(v : Ah), hv⟩)).symm

theorem modelCoordDataExt_V : modelCoordDataExt.V = VA.subgroupOf P2h := rfl

theorem range_permHomHat4 : permHomHat4.range = ⊤ := by
  apply MonoidHom.range_eq_top.mpr
  intro σ
  obtain ⟨g, hg⟩ := permHomHat_surjective (sigma0⁻¹ * σ * sigma0)
  refine ⟨g, ?_⟩
  rw [permHomHat4_apply]
  change sigma0 * permHomHat g * sigma0⁻¹ = σ
  rw [hg]
  group

theorem exists_model_coords_extension :
    ∃ e : ↥P2h ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))),
      (∀ (v : Ah) (hv : v ∈ VA),
        ((e ⟨v, VA_le_P2h hv⟩ : Mof _) : Mc) =
          SemidirectProduct.inl (pact sigma0 (psiHat ⟨v, hv⟩))) ∧
      ∀ g : ↥P2h, ((e g : Mof _) : Mc).right = permHat4 g := by
  obtain ⟨A, hAP, hAV, hVA⟩ := exists_complement_P2h
  have hA0V : A.subgroupOf P2h ⊓ modelCoordDataExt.V = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    have h : (g : Ah) ∈ A ⊓ VA :=
      ⟨Subgroup.mem_subgroupOf.mp hg.1, Subgroup.mem_subgroupOf.mp hg.2⟩
    have hg1 : (g : Ah) = 1 := by simpa only [hAV, Subgroup.mem_bot] using h
    exact Subgroup.mem_bot.mpr (Subtype.ext hg1)
  have hVA0 : modelCoordDataExt.V ⊔ A.subgroupOf P2h = ⊤ := by
    rw [modelCoordDataExt_V, ← Subgroup.subgroupOf_sup VA_le_P2h hAP, hVA,
      Subgroup.subgroupOf_self]
  obtain ⟨e, heV, heR⟩ := modelCoordDataExt.equiv_of_complement (A.subgroupOf P2h) hA0V hVA0
  let e' := e.trans (MulEquiv.subgroupCongr (congrArg Mof range_permHomHat4))
  refine ⟨e', ?_, ?_⟩
  · intro v hv
    exact heV ⟨⟨v, VA_le_P2h hv⟩, Subgroup.mem_subgroupOf.mpr hv⟩
  · intro g
    exact heR g

end CFSG.GH74.QTGen4.U42
