module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5IsoCommon
public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open Certificates.A5GL42 (Mat4 Vec4 FixZero fixSet invSubspaces aO bO HO)
open CFSG.QuasithinUnique.A5.Delta5 (Alt5 pact vact pact_add pact_one pact_mul pact_mem
  pact_faithful isEven mem_evenWeight_iff)
open Equiv (Perm)
open scoped commutatorElement Matrix

@[expose] def orthCoord (c : Vec4) : Fin 5 → ZMod 2 :=
  ![c 0, c 1, c 2, c 3, c 0 + c 1 + c 2 + c 3]

@[expose] def orthCoordInv (y : Fin 5 → ZMod 2) : Vec4 := fun i => y i.castSucc

theorem orthCoord_add (c d : Vec4) : orthCoord (c + d) = orthCoord c + orthCoord d := by
  funext i
  fin_cases i <;> simp [orthCoord] <;> ring

theorem orthCoordInv_orthCoord (c : Vec4) : orthCoordInv (orthCoord c) = c := by
  funext i
  fin_cases i <;> rfl

theorem isEven_orthCoord : ∀ c : Vec4, isEven (orthCoord c) := by
  decide +kernel

theorem orthCoord_orthCoordInv : ∀ y : Fin 5 → ZMod 2, isEven y → orthCoord (orthCoordInv y) = y := by
  decide +kernel

theorem pact_isEven (σ : Perm (Fin 5)) {x : Fin 5 → ZMod 2} (hx : isEven x) : isEven (pact σ x) :=
  (mem_evenWeight_iff _).mp (pact_mem σ ((mem_evenWeight_iff _).mpr hx))

theorem orthCoord_smul (a : ZMod 2) (c : Vec4) : orthCoord (a • c) = a • orthCoord c := by
  funext i
  fin_cases i <;> simp [orthCoord] <;> ring

theorem pact_smul (σ : Perm (Fin 5)) (a : ZMod 2) (x : Fin 5 → ZMod 2) :
    pact σ (a • x) = a • pact σ x := by
  funext i
  simp [pact]

theorem orthCoordInv_smul (a : ZMod 2) (y : Fin 5 → ZMod 2) :
    orthCoordInv (a • y) = a • orthCoordInv y := rfl

@[expose] def orthLin (σ : Perm (Fin 5)) : Vec4 →ₗ[ZMod 2] Vec4 where
  toFun c := orthCoordInv (pact σ (orthCoord c))
  map_add' c d := by
    show orthCoordInv (pact σ (orthCoord (c + d))) =
      orthCoordInv (pact σ (orthCoord c)) + orthCoordInv (pact σ (orthCoord d))
    rw [orthCoord_add, pact_add σ]
    rfl
  map_smul' a c := by
    show orthCoordInv (pact σ (orthCoord (a • c))) =
      (RingHom.id (ZMod 2)) a • orthCoordInv (pact σ (orthCoord c))
    rw [orthCoord_smul, pact_smul, orthCoordInv_smul, RingHom.id_apply]

theorem orthLin_apply (σ : Perm (Fin 5)) (c : Vec4) :
    orthLin σ c = orthCoordInv (pact σ (orthCoord c)) := rfl

theorem orthLin_one : orthLin 1 = LinearMap.id := by
  apply LinearMap.ext
  intro c
  rw [orthLin_apply, LinearMap.id_apply, pact_one, orthCoordInv_orthCoord]

theorem orthLin_mul (σ τ : Perm (Fin 5)) : orthLin (σ * τ) = (orthLin σ).comp (orthLin τ) := by
  apply LinearMap.ext
  intro c
  simp only [LinearMap.comp_apply, orthLin_apply]
  rw [orthCoord_orthCoordInv _ (pact_isEven τ (isEven_orthCoord c)), pact_mul]

@[expose] noncomputable def orthMatHom : Alt5 →* Mat4 where
  toFun σ := LinearMap.toMatrix' (orthLin (σ : Perm (Fin 5)))
  map_one' := by
    show LinearMap.toMatrix' (orthLin 1) = 1
    rw [orthLin_one, LinearMap.toMatrix'_id]
  map_mul' σ τ := by
    show LinearMap.toMatrix' (orthLin ((σ : Perm (Fin 5)) * (τ : Perm (Fin 5)))) =
      LinearMap.toMatrix' (orthLin (σ : Perm (Fin 5))) * LinearMap.toMatrix' (orthLin (τ : Perm (Fin 5)))
    rw [orthLin_mul, LinearMap.toMatrix'_comp]

theorem orthMatHom_mulVec (σ : Alt5) (c : Vec4) :
    orthMatHom σ *ᵥ c = orthCoordInv (pact (σ : Perm (Fin 5)) (orthCoord c)) := by
  show LinearMap.toMatrix' (orthLin (σ : Perm (Fin 5))) *ᵥ c = _
  rw [LinearMap.toMatrix'_mulVec, orthLin_apply]

theorem orthMatHom_x0 : orthMatHom x0 = aO := by
  decide +kernel

theorem orthMatHom_y0 : orthMatHom y0 = bO := by
  decide +kernel

@[expose] noncomputable def orthRho : Alt5 →* GL (Fin 4) (ZMod 2) := orthMatHom.toHomUnits

theorem orthRho_inj : Function.Injective orthRho := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have h1 : LinearMap.toMatrix' (orthLin (σ : Perm (Fin 5))) = 1 := by
    have := congrArg (fun g : GL (Fin 4) (ZMod 2) => glMat g) hσ
    exact this
  have h2 : orthLin (σ : Perm (Fin 5)) = LinearMap.id := by
    apply LinearMap.toMatrix'.injective
    rw [h1, LinearMap.toMatrix'_id]
  have hfix : ∀ x : Fin 5 → ZMod 2, isEven x → pact (σ : Perm (Fin 5)) x = x := by
    intro x hx
    have e2 : orthCoordInv (pact (σ : Perm (Fin 5)) x) = orthCoordInv x := by
      have := LinearMap.congr_fun h2 (orthCoordInv x)
      rw [orthLin_apply, orthCoord_orthCoordInv x hx, LinearMap.id_apply] at this
      exact this
    calc pact (σ : Perm (Fin 5)) x
        = orthCoord (orthCoordInv (pact (σ : Perm (Fin 5)) x)) :=
          (orthCoord_orthCoordInv _ (pact_isEven _ hx)).symm
      _ = orthCoord (orthCoordInv x) := by rw [e2]
      _ = x := orthCoord_orthCoordInv x hx
  apply Subtype.ext
  exact pact_faithful _ hfix

theorem orthRho_mem (hF : Certificates.A5GL42.Facts) (σ : Alt5) : glMat (orthRho σ) ∈ HO :=
  glMat_mem_of_closure hF.groupO hF.gens.2.2.1 hF.gens.2.2.2 orthRho orthMatHom_x0 orthMatHom_y0 σ

@[expose] noncomputable def orthRep (hF : Certificates.A5GL42.Facts) :
    Rep4 Alt5 Certificates.A5GL42.HO where
  rho := orthRho
  inj := orthRho_inj
  mem := orthRho_mem hF
  surj := fun m hm => by
    obtain ⟨σ, hσ⟩ := exists_eq_of_injective hF.groupO (fun σ => glMat (orthRho σ))
      (fun a b h => orthRho_inj (Units.ext h)) (orthRho_mem hF) m hm
    exact ⟨σ, hσ⟩

instance evenWeight5_addCommGroup : AddCommGroup ↥(CFSG.QuasithinUnique.evenWeight 5) :=
  AddSubgroup.toAddCommGroup _

@[expose] def orthPsi : Vec4 →+ ↥(CFSG.QuasithinUnique.evenWeight 5) where
  toFun c := ⟨orthCoord c, (mem_evenWeight_iff _).mpr (isEven_orthCoord c)⟩
  map_zero' := by
    apply Subtype.ext
    show orthCoord 0 = 0
    decide +kernel
  map_add' c d := Subtype.ext (orthCoord_add c d)

theorem orthPsi_inj : Function.Injective orthPsi := by
  intro c d h
  have h1 : orthCoord c = orthCoord d := congrArg Subtype.val h
  have h2 := congrArg orthCoordInv h1
  rwa [orthCoordInv_orthCoord, orthCoordInv_orthCoord] at h2

theorem orthPsi_surj (x : ↥(CFSG.QuasithinUnique.evenWeight 5)) : ∃ c : Vec4, orthPsi c = x :=
  ⟨orthCoordInv x.1, Subtype.ext (orthCoord_orthCoordInv x.1 ((mem_evenWeight_iff _).mp x.2))⟩

@[expose] def orthAct (t : Alt5) (w : ↥(CFSG.QuasithinUnique.evenWeight 5)) :
    ↥(CFSG.QuasithinUnique.evenWeight 5) :=
  vact (t : Perm (Fin 5)) w

theorem orthAct_intertwine (hF : Certificates.A5GL42.Facts) :
    ∀ (t : Alt5) (v : Vec4), orthPsi (glMat ((orthRep hF).rho t) *ᵥ v) = orthAct t (orthPsi v) := by
  intro t v
  apply Subtype.ext
  have h : glMat ((orthRep hF).rho t) *ᵥ v = orthCoordInv (pact (t : Perm (Fin 5)) (orthCoord v)) :=
    orthMatHom_mulVec t v
  show orthCoord (glMat ((orthRep hF).rho t) *ᵥ v) = pact (t : Perm (Fin 5)) (orthCoord v)
  rw [h, orthCoord_orthCoordInv _ (pact_isEven _ (isEven_orthCoord v))]

section FixZeroSection

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

theorem fixZero_HO (hF : Certificates.A5GL42.Facts) : FixZero HO := by
  have mem_fix : ∀ {A : Finset Mat4} {v : Vec4}, v ∈ fixSet A ↔ ∀ a ∈ A, a *ᵥ v = v := by
    intro A v
    simp [fixSet]
  have hinv : fixSet HO ∈ invSubspaces HO := by
    rw [invSubspaces, Finset.mem_filter]
    refine ⟨hF.subspaces_complete _ ?_ ?_, ?_⟩
    · exact mem_fix.mpr fun a _ => Matrix.mulVec_zero a
    · intro x hx y hy
      refine mem_fix.mpr fun a ha => ?_
      rw [Matrix.mulVec_add, (mem_fix.mp hx) a ha, (mem_fix.mp hy) a ha]
    · intro h hh w hw
      refine mem_fix.mpr fun a ha => ?_
      rw [(mem_fix.mp hw) h hh, (mem_fix.mp hw) a ha]
  rw [hF.groupO.2.2.2.2.2] at hinv
  intro v hv
  have hvm : v ∈ fixSet HO := mem_fix.mpr hv
  rcases Finset.mem_insert.mp hinv with h1 | h1
  · rw [h1, Finset.mem_singleton] at hvm
    exact hvm
  · exfalso
    rw [Finset.mem_singleton] at h1
    have hw : (![0, 1, 0, 0] : Vec4) ∈ fixSet HO := by
      rw [h1]
      exact Finset.mem_univ _
    have h2 := (mem_fix.mp hw) aO hF.gens.2.2.1
    revert h2
    decide

end FixZeroSection

theorem leafAlt5OfOrth : LeafAlt5OfOrth := by
  intro G _ _ L hq hc he hn hnat
  have hF : Certificates.A5GL42.Facts := a5Facts
  have hA : A5Pre L L (pCoreOf 2 L) ⊥ := a5Pre_self hq hc he hn
  rcases iso_models hq hc he hn with ⟨hnat', -⟩ | ⟨-, ⟨M⟩⟩
  · exact absurd hnat' hnat
  · obtain ⟨α, β, hαs, hαk, -, hβk, hβim, hint⟩ :=
      recog_exists hF hF.groupO (fixZero_HO hF) hA M (orthRep hF) orthPsi orthPsi_inj orthAct (orthAct_intertwine hF)
    unfold CFSG.QuasithinUnique.IsAltType
    refine ⟨α, hαs, hαk, β, ?_, hβk, ?_⟩
    · intro w
      obtain ⟨c, hcw⟩ := orthPsi_surj (Multiplicative.toAdd w)
      obtain ⟨u, hu⟩ := (hβim (Multiplicative.toAdd w)).mpr ⟨c, hcw⟩
      exact ⟨u, Multiplicative.toAdd.injective hu⟩
    · intro ℓ u v huv i
      exact congrArg (fun w : ↥(CFSG.QuasithinUnique.evenWeight 5) => (w : Fin 5 → ZMod 2) i)
        (hint ℓ u v huv)

end CFSG.GH74.QTGen4.DSGen4
