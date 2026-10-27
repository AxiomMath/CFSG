module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviCentral
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParW
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Chev
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.KFactLevi
public import CFSG.Quasithin.Background.C118WeakPair
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

section Transport

variable {W : Type} [Group W] [Finite W] {L : Subgroup W}

theorem leviAlt_of_center_quotient {A : Subgroup ↥L} (hZ : Subgroup.center ↥L ≤ A)
    (hbar : LeviAlt ↥(pElementSubgroup 2 (A.map (QuotientGroup.mk' (Subgroup.center ↥L))))) :
    LeviAlt ↥(pElementSubgroup 2 A) := by
  set q : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  have hqker : q.ker = Subgroup.center ↥L := by rw [hq, QuotientGroup.ker_mk']
  have hmap : ∀ x ∈ pElementSubgroup 2 A, q x ∈ pElementSubgroup 2 (A.map q) := fun x hx =>
    map_pElementSubgroup_le_pElementSubgroup_map q A ⟨x, hx, rfl⟩
  let φ : ↥(pElementSubgroup 2 A) →* ↥(pElementSubgroup 2 (A.map q)) :=
    (q.comp (pElementSubgroup 2 A).subtype).codRestrict _ (fun x => hmap x.1 x.2)
  have hcomap : (A.map q).comap q = A := by
    rw [Subgroup.comap_map_eq, hqker]; exact sup_eq_left.2 hZ
  have hφ : Function.Surjective φ := by
    rintro ⟨w, hw⟩
    have h1 := pElementSubgroup_le_map_pElementSubgroup_comap (L := L) (A.map q) hw
    rw [hcomap] at h1
    obtain ⟨x, hx, hxw⟩ := h1
    exact ⟨⟨x, hx⟩, Subtype.ext hxw⟩
  have hker : φ.ker ≤ Subgroup.center ↥(pElementSubgroup 2 A) := by
    intro x hx
    have h1 : q (x : ↥L) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 : (x : ↥L) ∈ Subgroup.center ↥L := hqker ▸ MonoidHom.mem_ker.2 h1
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 h2 g)
  have hgen : Subgroup.closure {x : ↥(pElementSubgroup 2 A) | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤ := by
    set C := Subgroup.closure {x : ↥(pElementSubgroup 2 A) | ∃ k : ℕ, orderOf x = 2 ^ k} with hC
    have hle : pElementSubgroup 2 A ≤ C.map (pElementSubgroup 2 A).subtype := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      have hxW : x ∈ pElementSubgroup 2 A := Subgroup.subset_closure hx
      obtain ⟨-, k, hk⟩ := hx
      refine ⟨⟨x, hxW⟩, Subgroup.subset_closure ⟨k, ?_⟩, rfl⟩
      rw [← hk]; exact Subgroup.orderOf_mk x hxW
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨c, hc, hcy⟩ := hle hy
    have : c = ⟨y, hy⟩ := Subtype.ext hcy
    rwa [← this]
  exact leviAlt_of_central_cover φ hφ hker hgen hbar

theorem leviAlt_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (h : LeviAlt A) :
    LeviAlt B := by
  rcases h with hs | hq
  · left
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  · right
    have hmap : (CFSG.pCore 2 A).map e.toMonoidHom = CFSG.pCore 2 B := CFSG.pCore_map_iso 2 e
    exact isQuasisimple_of_mulEquiv_open (QuotientGroup.congr _ _ e hmap) hq

theorem pElementSubgroup_map_injective {S S' : Type*} [Group S] [Group S'] (f : S →* S')
    (hf : Function.Injective f) (P : Subgroup S) :
    pElementSubgroup 2 (P.map f) = (pElementSubgroup 2 P).map f := by
  unfold pElementSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, k, hk⟩
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨hy, k, by rwa [orderOf_injective f hf y] at hk⟩, rfl⟩
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, k, by rwa [orderOf_injective f hf y]⟩

variable {W : Type} [Group W] [Finite W] {L : Subgroup W} 

theorem leviAlt_of_isMinOverBorel_of_quotient {S₀ A : Subgroup W} (hS : IsSylowTwoOf S₀ L)
    (hA : IsMinOverBorel L S₀ A)
    (hbar : LeviAlt ↥(pElementSubgroup 2
      ((A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))))) :
    LeviAlt ↥(pElementSubgroup 2 A) := by
  have hZA : Subgroup.center ↥L ≤ A.subgroupOf L :=
    (center_le_comap_normalizer hS).trans (comap_normalizer_le hS hA)
  have h1 := leviAlt_of_center_quotient hZA hbar
  have hAe : (A.subgroupOf L).map L.subtype = A := Subgroup.map_subgroupOf_eq_of_le hA.1
  have h2 : pElementSubgroup 2 A = (pElementSubgroup 2 (A.subgroupOf L)).map L.subtype := by
    rw [← pElementSubgroup_map_injective L.subtype L.subtype_injective, hAe]
  rw [h2]
  exact leviAlt_of_mulEquiv (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective) h1

end Transport

end CFSG.AGLEmbeddingD2.Tits.GN516
