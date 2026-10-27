module

public import CFSG.GH74.QTGen4.U42.ModelExtSubgroups
public import CFSG.GH74.QTGen4.U42.ModelExtPairCore
public import CFSG.GH74.QTGen4.U42.CoreFrameBounds
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Mod2

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13.A5 CFSG.Quasithin.H13.F431.U42 U42F431
open CFSG.Quasithin.H13.F431.U42Aut
open CFSG.LieType.BorelTits


theorem not_VA_le_pCoreOf_P1h : ¬ VA ≤ pCoreOf 2 P1h := by
  let C : Subgroup Y := (pCoreOf 2 P1h).comap incl
  have hCP : C ≤ P1 := by
    intro y hy
    have h : incl y ∈ P1h := pCoreOf_le 2 P1h hy
    change y ∈ P1h.comap incl at h
    rwa [comap_P1h] at h
  have hPC : P1 ≤ Subgroup.normalizer (C : Set Y) := by
    intro y hy
    have hyh : incl y ∈ P1h := by
      change y ∈ P1h.comap incl
      rwa [comap_P1h]
    rw [Subgroup.mem_normalizer_iff]
    intro c
    change incl c ∈ pCoreOf 2 P1h ↔ incl (y * c * y⁻¹) ∈ pCoreOf 2 P1h
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 P1h hyh) _
  let ψ : C →* pCoreOf 2 P1h :=
    (incl.comp C.subtype).codRestrict (pCoreOf 2 P1h) (fun c => c.2)
  have hψ : Function.Injective ψ := by
    intro c d h
    exact Subtype.ext (incl_injective (congrArg Subtype.val h))
  have hC2 : IsPGroup 2 C := (pCoreOf_isPGroup 2 P1h).of_injective ψ hψ
  have hCQ : C ≤ pCoreOf 2 P1 := le_pCoreOf_of_le_normalizer 2 hCP hPC hC2
  intro hVA
  apply not_Vsub_le_pCoreOf_P1
  intro v hv
  exact hCQ (hVA (by rw [VA_eq_map_Vsub]; exact Subgroup.mem_map_of_mem incl hv))

theorem map_VA_aligned
    (e : ↥P2h ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))))
    (heV : ∀ (v : Ah) (hv : v ∈ VA),
      ((e ⟨v, VA_le_P2h hv⟩ : Mof _) : Mc) =
        SemidirectProduct.inl (pact (extAlignTau * sigma0) (psiHat ⟨v, hv⟩))) :
    (VA.subgroupOf P2h).map ((Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp
      e.toMonoidHom) = Wc := by
  let φ : ↥P2h →* Mc := (Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hle : (VA.subgroupOf P2h).map φ ≤ Wc := by
    rintro _ ⟨v, hv, rfl⟩
    have hvA := Subgroup.mem_subgroupOf.mp hv
    have h := heV (v : Ah) hvA
    change φ v = _ at h
    rw [h]
    exact ⟨_, rfl⟩
  have hcardV : Nat.card ((VA.subgroupOf P2h).map φ) = 16 := by
    rw [Subgroup.card_map_of_injective hφ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe VA_le_P2h).toEquiv,
      ← Nat.card_congr hatVEquiv.toEquiv, card_Vsub_eq]
  have hcardW : Nat.card Wc = 16 := by
    change Nat.card (SemidirectProduct.inl : W5 →* Mc).range = 16
    have hinj : Function.Injective (SemidirectProduct.inl : W5 →* Mc) := by
      intro v w h
      exact congrArg (fun x : Mc => x.left) h
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact CFSG.Quasithin.H13.A5.card_W5
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardV, hcardW])

private theorem modelCore_image_properties
    (e : ↥P2h ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))))
    (he : ∀ g : ↥P2h, ((e g : Mof _) : Mc).right = extAlignedPerm g) :
    let φ := (Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp e.toMonoidHom
    let X := ((pCoreOf 2 P1h).subgroupOf P2h).map φ
    X ≤ Thc ∧ (∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X) ∧
      Nat.card X = Nat.card (pCoreOf 2 P1h) := by
  let φ : ↥P2h →* Mc := (Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp e.toMonoidHom
  let X : Subgroup Mc := ((pCoreOf 2 P1h).subgroupOf P2h).map φ
  change X ≤ Thc ∧ (∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X) ∧
    Nat.card X = Nat.card (pCoreOf 2 P1h)
  have hQThat := model_pairCore_extension.U_le_T
  have hQP2 : pCoreOf 2 P1h ≤ P2h := hQThat.trans (That_le_Bh.trans inf_le_right)
  refine ⟨?_, ?_, ?_⟩
  · have hle : (pCoreOf 2 P1h).subgroupOf P2h ≤ That.subgroupOf P2h := by
      intro q hq
      exact Subgroup.mem_subgroupOf.mpr (hQThat (Subgroup.mem_subgroupOf.mp hq))
    exact (Subgroup.map_mono hle).trans (map_That_aligned e he).le
  · intro b hb x hx
    have hb' : b ∈ (Bh.subgroupOf P2h).map φ := by
      rw [map_Bh_aligned e he]
      exact Bc_le_Bhc hb
    obtain ⟨g, hg, hgb⟩ := Subgroup.mem_map.mp hb'
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hx
    have hh : (g : Ah) ∈ P1h := Bh_le_P1h (Subgroup.mem_subgroupOf.mp hg)
    have huQ := Subgroup.mem_subgroupOf.mp hu
    have hconj : g * u * g⁻¹ ∈ (pCoreOf 2 P1h).subgroupOf P2h :=
      Subgroup.mem_subgroupOf.mpr (model_pairCore_extension.U_normal _ hh _ huQ)
    have heq : φ (g * u * g⁻¹) = b * x * b⁻¹ := by
      simp only [map_mul, map_inv, hgb, hux]
    rw [← heq]
    exact Subgroup.mem_map_of_mem φ hconj
  · have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
    rw [Subgroup.card_map_of_injective hφ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP2).toEquiv]

theorem card_pCoreOf_P1h : Nat.card (pCoreOf 2 P1h) = 32 := by
  obtain ⟨e, heV, heR⟩ := exists_model_coords_aligned
  let φ : ↥P2h →* Mc := (Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp e.toMonoidHom
  let X : Subgroup Mc := ((pCoreOf 2 P1h).subgroupOf P2h).map φ
  obtain ⟨hXT, hXB, hXcard⟩ := modelCore_image_properties e heR
  have hXV : ¬ Wc ≤ X := by
    intro hW
    apply not_VA_le_pCoreOf_P1h
    intro v hv
    let vP : ↥P2h := ⟨v, VA_le_P2h hv⟩
    have hmem : φ vP ∈ X := hW (by
      rw [← map_VA_aligned e heV]
      exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hv))
    obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.mp hmem
    have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
    exact Subgroup.mem_subgroupOf.mp (hφ huv ▸ hu)
  have hupper : Nat.card (pCoreOf 2 P1h) ≤ 32 := by
    rw [← hXcard]
    exact card_le_32_of_normalized_Bc hXT hXB hXV
  have hc : Nat.card (pCoreOf 2 P1h) = Nat.card (CFSG.Open.pCore 2 ↥P1h) := by
    unfold pCoreOf
    exact Subgroup.card_map_of_injective P1h.subtype_injective
  have hlower : 32 ≤ Nat.card (pCoreOf 2 P1h) := hc.symm ▸ card_pCore_P1h_ge
  omega

theorem map_pCoreOf_P1h_aligned
    (e : ↥P2h ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))))
    (he : ∀ g : ↥P2h, ((e g : Mof _) : Mc).right = extAlignedPerm g) :
    ((pCoreOf 2 P1h).subgroupOf P2h).map
      ((Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp e.toMonoidHom) = U0 := by
  obtain ⟨hXT, hXB, hXcard⟩ := modelCore_image_properties e he
  have hc : Nat.card (((pCoreOf 2 P1h).subgroupOf P2h).map
      ((Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp e.toMonoidHom)) = 32 := by
    rw [hXcard, card_pCoreOf_P1h]
  exact U0_unique hXT hc hXB (not_Wc_le_of_card32_normalized_Bc hXT hXB hc)

end CFSG.GH74.QTGen4.U42
