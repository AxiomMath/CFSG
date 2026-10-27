module

public import CFSG.Quasithin.MS93.S32Desc
public import CFSG.Quasithin.MS93.S32Nat

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Quasithin CFSG.Quasithin.MS93.S32 CFSG.Assembly.LowTwoRank
open scoped Matrix commutatorElement

private theorem conj_mem_statedSL {F : Type} [Field F] (a : GL (Fin 3) F) {γ : GL (Fin 3) F}
    (hγ : γ ∈ StatedSL 3 F) : a * γ * a⁻¹ ∈ StatedSL 3 F := by
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ?_
    have h : (x : Matrix (Fin 3) (Fin 3) F).det = 1 := hx
    show ((a * x * a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv,
      mul_comm (Matrix.GeneralLinearGroup.det a), mul_assoc, mul_inv_cancel, mul_one,
      Matrix.GeneralLinearGroup.val_det_apply, h]
  | one => simp
  | mul x y _ _ hx hy =>
    have : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

section Coord

variable {V : Type} [CommGroup V] {F : Type} [Field F]

private structure CoordData (K : Subgroup (MulAut V)) (U Z : Subgroup V)
    (π : ↥(StatedSL 3 F) →* ↥K) where
  β : ↥U →* Multiplicative (Fin 3 → F)
  surj : Function.Surjective β
  ker : ∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z
  equiv : ∀ (γ : ↥(StatedSL 3 F)) (u : ↥U) (hu : ((π γ : ↥K) : MulAut V) (u : V) ∈ U),
    β ⟨((π γ : ↥K) : MulAut V) (u : V), hu⟩ =
      Multiplicative.ofAdd (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (β u))

variable {K : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥(StatedSL 3 F) →* ↥K}

private noncomputable def CoordData.coord (c : CoordData K U Z π) (v : V) : Fin 3 → F :=
  open scoped Classical in
  if h : v ∈ U then Multiplicative.toAdd (c.β ⟨v, h⟩) else 0

private theorem CoordData.coord_mk (c : CoordData K U Z π) (u : ↥U) :
    c.coord (u : V) = Multiplicative.toAdd (c.β u) := by
  simp [CoordData.coord, u.2]

private theorem CoordData.coord_of_mem (c : CoordData K U Z π) {u : V} (hu : u ∈ U) :
    c.coord u = Multiplicative.toAdd (c.β ⟨u, hu⟩) :=
  c.coord_mk ⟨u, hu⟩

private theorem CoordData.coord_mul (c : CoordData K U Z π) {u w : V} (hu : u ∈ U) (hw : w ∈ U) :
    c.coord (u * w) = c.coord u + c.coord w := by
  rw [c.coord_of_mem (U.mul_mem hu hw), c.coord_of_mem hu, c.coord_of_mem hw]
  exact congrArg Multiplicative.toAdd (map_mul c.β ⟨u, hu⟩ ⟨w, hw⟩)

private theorem CoordData.exists_coord (c : CoordData K U Z π) (x : Fin 3 → F) :
    ∃ u ∈ U, c.coord u = x := by
  obtain ⟨u, hu⟩ := c.surj (Multiplicative.ofAdd x)
  exact ⟨u, u.2, by rw [c.coord_mk, hu, toAdd_ofAdd]⟩

private theorem CoordData.mul_inv_mem (c : CoordData K U Z π) {u w : V} (hu : u ∈ U)
    (hw : w ∈ U) (h : c.coord u = c.coord w) : u * w⁻¹ ∈ Z := by
  rw [c.coord_of_mem hu, c.coord_of_mem hw] at h
  have h1 : c.β ⟨u, hu⟩ = c.β ⟨w, hw⟩ := Multiplicative.toAdd.injective h
  exact (c.ker (⟨u, hu⟩ * ⟨w, hw⟩⁻¹)).1 (by rw [map_mul, map_inv, h1, mul_inv_cancel])

private theorem CoordData.coord_eq (c : CoordData K U Z π) {u w : V} (hu : u ∈ U)
    (hw : w ∈ U) (h : u * w⁻¹ ∈ Z) : c.coord u = c.coord w := by
  rw [c.coord_of_mem hu, c.coord_of_mem hw]
  have := (c.ker (⟨u, hu⟩ * ⟨w, hw⟩⁻¹)).2 h
  rw [map_mul, map_inv, mul_inv_eq_one] at this
  rw [this]

private theorem CoordData.coord_equiv (c : CoordData K U Z π) (γ : ↥(StatedSL 3 F)) {u : V}
    (hu : u ∈ U) (hγu : ((π γ : ↥K) : MulAut V) u ∈ U) :
    c.coord (((π γ : ↥K) : MulAut V) u) =
      ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ c.coord u := by
  rw [c.coord_of_mem hγu, c.coord_of_mem hu, c.equiv γ ⟨u, hu⟩ hγu, toAdd_ofAdd]

private theorem CoordData.exists_induced (c : CoordData K U Z π) {p : MulAut V}
    (hpU : ∀ u ∈ U, p u ∈ U) (hpZ : ∀ z ∈ Z, p z ∈ Z) :
    ∃ D : (Fin 3 → F) →+ (Fin 3 → F), ∀ u ∈ U, c.coord (p u) = D (c.coord u) := by
  choose! s hsU hs using c.exists_coord
  have key : ∀ u ∈ U, c.coord (p u) = c.coord (p (s (c.coord u))) := by
    intro u hu
    have hmem : u * (s (c.coord u))⁻¹ ∈ Z := c.mul_inv_mem hu (hsU _) (hs _).symm
    have := hpZ _ hmem
    rw [map_mul, map_inv] at this
    exact c.coord_eq (hpU u hu) (hpU _ (hsU _)) this
  refine ⟨AddMonoidHom.mk' (fun x => c.coord (p (s x))) fun x y => ?_, fun u hu => key u hu⟩
  have h := key (s x * s y) (U.mul_mem (hsU x) (hsU y))
  rw [map_mul, c.coord_mul (hpU _ (hsU x)) (hpU _ (hsU y)), c.coord_mul (hsU x) (hsU y), hs,
    hs] at h
  exact h.symm

end Coord


section Normalize

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)}

private theorem apply_mem_commV_of_normalizes {p : MulAut V} (hn : ∀ k ∈ K, p * k * p⁻¹ ∈ K)
    {u : V} (hu : u ∈ commV K) : p u ∈ commV K :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hn hu

private theorem apply_mem_fixV_of_normalizes {p : MulAut V} (hn : ∀ k ∈ K, p⁻¹ * k * p ∈ K)
    {z : V} (hz : z ∈ fixV K) : p z ∈ fixV K := fun k hk => by
  have h := hz _ (hn k hk)
  apply p⁻¹.injective
  simpa [MulAut.mul_apply] using h

private def trivSec (U F : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | (∀ v, g v ∈ U ↔ v ∈ U) ∧ ∀ u ∈ U, g u * u⁻¹ ∈ F}
  one_mem' := ⟨fun _ => Iff.rfl, fun u _ => by simp⟩
  mul_mem' := fun {a b} ha hb => by
    refine ⟨fun v => (ha.1 _).trans (hb.1 v), fun u hu => ?_⟩
    have hbu : b u ∈ U := (hb.1 u).2 hu
    have h := F.mul_mem (ha.2 _ hbu) (hb.2 u hu)
    show a (b u) * u⁻¹ ∈ F
    rwa [mul_assoc (a (b u)), inv_mul_cancel_left] at h
  inv_mem' := fun {g} hg => by
    refine ⟨fun v => by rw [← hg.1 (g⁻¹ v), MulAut.apply_inv_self], fun u hu => ?_⟩
    have hw : g⁻¹ u ∈ U := by rw [← hg.1 (g⁻¹ u), MulAut.apply_inv_self]; exact hu
    have h := F.inv_mem (hg.2 _ hw)
    rw [MulAut.apply_inv_self, mul_inv_rev, inv_inv] at h
    exact h

end Normalize

private theorem exists_scalar_of_equivariant {F : Type} [Field F] (a : GL (Fin 3) F)
    (D : (Fin 3 → F) →+ (Fin 3 → F))
    (hD : ∀ γ ∈ StatedSL 3 F, ∀ x, D ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ x) =
      ((a * γ * a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ D x) :
    ∃ s : F, ∀ x, D x = s • ((a : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
  let φ : (Fin 3 → F) →+ (Fin 3 → F) :=
    (Matrix.mulVecLin ((a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).toAddMonoidHom.comp D
  have hφ : ∀ γ ∈ StatedSL 3 F, ∀ v, φ ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ φ v := by
    intro γ hγ v
    have e : ((a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((a * γ * a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (γ : Matrix (Fin 3) (Fin 3) F) * ((a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    show ((a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        D ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ (((a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ D v)
    rw [hD γ hγ v, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]
  obtain ⟨s, hs⟩ := eq_smul_of_commute_sl3 φ hφ
  refine ⟨s, fun x => ?_⟩
  have h1 : ((a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ D x = s • x := hs x
  have h2 : (a : Matrix (Fin 3) (Fin 3) F) *ᵥ (((a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      D x) = D x := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← h2, h1, Matrix.mulVec_smul]

variable {V : Type} [CommGroup V]

theorem commutator_trivial_of_natural_diag {K P : Subgroup (MulAut V)} {F : Type} [Field F]
    (π : ↥(StatedSL 3 F) →* ↥K)
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia K (commV K) (fixV K ⊓ commV K) π)
    (A : MulAut V → GL (Fin 3) F)
    (hA : ∀ p ∈ P, ∀ γ γ' : ↥(StatedSL 3 F),
      (γ' : GL (Fin 3) F) = A p * (γ : GL (Fin 3) F) * (A p)⁻¹ →
        p * (π γ : MulAut V) * p⁻¹ = (π γ' : MulAut V))
    (hcomm : ∀ p ∈ P, ∀ q ∈ P, A p * A q = A q * A p) :
    ∀ x ∈ ⁅P, P⁆, ∀ u ∈ commV K, x u * u⁻¹ ∈ fixV K := by
  obtain ⟨β, hβs, hβk, hβe⟩ := natReal_coord hπ
  have hπU := hπ.2.2.2.1
  let c : CoordData K (commV K) (fixV K ⊓ commV K) π := ⟨β, hβs, hβk, hβe⟩
  have hnormP : ∀ p ∈ P, ∀ k ∈ K, p * k * p⁻¹ ∈ K := by
    intro p hp k hk
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL 3 F), π γ = ⟨k, hk⟩ := hπ.1 ⟨k, hk⟩
    have hk' : k = (π γ : MulAut V) := (congrArg Subtype.val hγ).symm
    have h := hA p hp γ ⟨A p * γ * (A p)⁻¹, conj_mem_statedSL _ γ.2⟩ rfl
    rw [hk', h]
    exact (π _).2
  have hnormP' : ∀ p ∈ P, ∀ k ∈ K, p⁻¹ * k * p ∈ K := fun p hp k hk => by
    simpa using hnormP p⁻¹ (P.inv_mem hp) k hk
  have hPU : ∀ p ∈ P, ∀ u ∈ commV K, p u ∈ commV K := fun p hp u hu =>
    apply_mem_commV_of_normalizes (hnormP p hp) hu
  have hPUiff : ∀ p ∈ P, ∀ v, p v ∈ commV K ↔ v ∈ commV K := fun p hp v =>
    ⟨fun h => by simpa using hPU p⁻¹ (P.inv_mem hp) _ h, hPU p hp v⟩
  have hPZ : ∀ p ∈ P, ∀ z ∈ fixV K ⊓ commV K, p z ∈ fixV K ⊓ commV K := fun p hp z hz =>
    ⟨apply_mem_fixV_of_normalizes (hnormP' p hp) hz.1, hPU p hp z hz.2⟩
  choose! D hD using fun p (hp : p ∈ P) => c.exists_induced (hPU p hp) (hPZ p hp)
  have hscal : ∀ p ∈ P, ∃ s : F, ∀ x, D p x =
      s • (((A p : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
    intro p hp
    refine exists_scalar_of_equivariant (A p) (D p) fun γ hγ x => ?_
    obtain ⟨u, huU, hux⟩ := c.exists_coord x
    have hγu : ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) u ∈ commV K := hπU (π ⟨γ, hγ⟩) u huU
    have e1 := c.coord_equiv ⟨γ, hγ⟩ huU hγu
    have hγ' : A p * γ * (A p)⁻¹ ∈ StatedSL 3 F := conj_mem_statedSL _ hγ
    have e2 := hA p hp ⟨γ, hγ⟩ ⟨_, hγ'⟩ rfl
    have hpu : p u ∈ commV K := hPU p hp u huU
    have e3 := c.coord_equiv ⟨_, hγ'⟩ hpu (hπU _ _ hpu)
    have e4 : p (((π ⟨γ, hγ⟩ : ↥K) : MulAut V) u) =
        ((π ⟨_, hγ'⟩ : ↥K) : MulAut V) (p u) := by
      rw [← e2]
      simp [MulAut.mul_apply]
    rw [← hux, ← e1, ← hD p hp _ hγu, e4, e3, hD p hp u huU]
  have hDcomm : ∀ p ∈ P, ∀ q ∈ P, ∀ x, D p (D q x) = D q (D p x) := by
    intro p hp q hq x
    obtain ⟨s, hs⟩ := hscal p hp
    obtain ⟨t, ht⟩ := hscal q hq
    have hm : ((A p : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((A q : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((A q : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((A p : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm p hp q hq]
    rw [ht x, hs, hs x, ht, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, smul_smul,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm, mul_comm s t]
  have hDinv : ∀ p ∈ P, ∀ x, D p (D p⁻¹ x) = x := by
    intro p hp x
    obtain ⟨u, hu, rfl⟩ := c.exists_coord x
    have hu' : p⁻¹ u ∈ commV K := hPU _ (P.inv_mem hp) u hu
    rw [← hD p⁻¹ (P.inv_mem hp) u hu, ← hD p hp _ hu', MulAut.apply_inv_self]
  have hcoordComm : ∀ a ∈ P, ∀ b ∈ P, ∀ u ∈ commV K,
      c.coord ((⁅a, b⁆ : MulAut V) u) = c.coord u := by
    intro a ha b hb u hu
    have hu1 : b⁻¹ u ∈ commV K := hPU _ (P.inv_mem hb) u hu
    have hu2 : a⁻¹ (b⁻¹ u) ∈ commV K := hPU _ (P.inv_mem ha) _ hu1
    have hu3 : b (a⁻¹ (b⁻¹ u)) ∈ commV K := hPU _ hb _ hu2
    have e : (⁅a, b⁆ : MulAut V) u = a (b (a⁻¹ (b⁻¹ u))) := rfl
    rw [e, hD a ha _ hu3, hD b hb _ hu2, hD a⁻¹ (P.inv_mem ha) _ hu1,
      hD b⁻¹ (P.inv_mem hb) _ hu, hDcomm b hb a⁻¹ (P.inv_mem ha), hDinv a ha, hDinv b hb]
  have hker : ⁅P, P⁆ ≤ trivSec (commV K) (fixV K) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab : (⁅a, b⁆ : MulAut V) ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
    refine ⟨hPUiff _ hab, fun u hu => ?_⟩
    have hmem := c.mul_inv_mem ((hPUiff _ hab u).2 hu) hu (hcoordComm a ha b hb u hu)
    exact hmem.1
  intro x hx u hu
  exact (hker hx).2 u hu

end CFSG.HardMathSupport.Curtis.Coordinator
