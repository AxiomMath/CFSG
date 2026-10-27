module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesPrimeField
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup
open scoped commutatorElement MatrixGroups LinearAlgebra.Projectivization Pointwise

namespace C56

section BlockQ

variable {G : Type} [Group G]

theorem blockQ_eq_map (L : Subgroup G) : blockQ L = (CFSG.pCore 2 ↥L).map L.subtype := by
  unfold blockQ pCoreOf
  try with_reducible rfl

theorem mem_blockQ_iff {L : Subgroup G} (l : ↥L) : (l : G) ∈ blockQ L ↔ l ∈ CFSG.pCore 2 ↥L := by
  rw [blockQ_eq_map]
  exact Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective


end BlockQ

section Plane

variable {F : Type} [Field F]

open CFSG.QuasithinUnique.Setup.SL2Modules in
theorem semilin_smul (g : Matrix.GeneralLinearGroup (Fin 2) F) (σ : RingAut F) (c : F)
    (v : Fin 2 → F) :
    (semilin g σ).val (c • v) = σ c • (semilin g σ).val v := by
  rw [semilin_apply, semilin_apply]
  have : (fun i => σ ((c • v) i)) = σ c • (fun i => σ (v i)) := by
    funext i; simp
  rw [this, Matrix.mulVec_smul]

open CFSG.QuasithinUnique.Setup.SL2Modules in
theorem exists_sigma_of_mem_normalizer [Finite F] (h : (AddMonoid.End (Fin 2 → F))ˣ)
    (hN : h ∈ Subgroup.normalizer ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ)) :
    ∃ σ : RingAut F, ∀ (c : F) (v : Fin 2 → F), h.val (c • v) = σ c • h.val v := by
  obtain ⟨g, σ, rfl⟩ := exists_semilin_of_mem_normalizer h hN
  exact ⟨σ, semilin_smul g σ⟩

theorem sigma_unique (h : (AddMonoid.End (Fin 2 → F))ˣ) {σ σ' : RingAut F}
    (h1 : ∀ (c : F) (v : Fin 2 → F), h.val (c • v) = σ c • h.val v)
    (h2 : ∀ (c : F) (v : Fin 2 → F), h.val (c • v) = σ' c • h.val v) : σ = σ' := by
  ext c
  have hs : ∃ v : Fin 2 → F, h.val v = Pi.single 0 1 := by
    refine ⟨(h⁻¹).val (Pi.single 0 1), ?_⟩
    have := congrArg (fun u : AddMonoid.End (Fin 2 → F) => u (Pi.single 0 1)) (Units.mul_inv h)
    exact this
  obtain ⟨v, hv⟩ := hs
  have := congrFun (h1 c v ▸ h2 c v) 0
  rw [hv] at this
  simpa using this

theorem sigma_mul (h h' : (AddMonoid.End (Fin 2 → F))ˣ) {σ σ' : RingAut F}
    (h1 : ∀ (c : F) (v : Fin 2 → F), h.val (c • v) = σ c • h.val v)
    (h2 : ∀ (c : F) (v : Fin 2 → F), h'.val (c • v) = σ' c • h'.val v) (c : F)
    (v : Fin 2 → F) : (h * h').val (c • v) = (σ * σ') c • (h * h').val v := by
  show h.val (h'.val (c • v)) = (σ * σ') c • h.val (h'.val v)
  rw [h2, h1]
  rfl


end Plane

section Lin2

variable {G : Type} [Group G]

structure Lin2Data (L : Subgroup G) (F : Type) [Field F] where
  α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F
  surj_α : Function.Surjective α
  ker_α : α.ker = CFSG.pCore 2 ↥L
  β : ↥(blockU L) →* Multiplicative (Fin 2 → F)
  surj_β : Function.Surjective β
  ker_β : β.ker = (blockZ L).subgroupOf (blockU L)
  equiv : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β v) =
      (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))

variable {L : Subgroup G} {F : Type} [Field F]

theorem Lin2Data.equiv_smul (D : Lin2Data L F) (ℓ : ↥L) (u v : ↥(blockU L))
    (h : (v : G) = ℓ * u * ℓ⁻¹) :
    Multiplicative.toAdd (D.β v) = D.α ℓ • Multiplicative.toAdd (D.β u) := by
  have := D.equiv ℓ u v h
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
  exact this

variable [Finite G]

section Action

open CFSG.QuasithinUnique.Setup.SL2Modules

omit [Finite G] in
theorem exists_psi (D : Lin2Data L F) {S : Subgroup G}
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    ∃ Ψ : ↥S →* AddMonoid.End (Fin 2 → F), ∀ (s : ↥S) (u v : ↥(blockU L)),
      (v : G) = (s : G) * u * (s : G)⁻¹ →
        Ψ s (Multiplicative.toAdd (D.β u)) = Multiplicative.toAdd (D.β v) := by
  classical
  have hSU : ∀ s : ↥S, (s : G) ∈ Subgroup.normalizer (blockU L : Set G) := fun s =>
    C1.mem_normalizer_blockU (hSL s.2)
  have hZstab : ∀ (s : ↥S) (z : G), z ∈ blockZ L → (s : G) * z * (s : G)⁻¹ ∈ blockZ L := by
    intro s z hz
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hSU s) z).mp hz.1,
      Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hl' : (s : G)⁻¹ * l * (s : G) ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hSL s.2)) l).mp hl
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hl'
    calc l * ((s : G) * z * (s : G)⁻¹)
        = (s : G) * (((s : G)⁻¹ * l * (s : G)) * z) * (s : G)⁻¹ := by group
      _ = (s : G) * (z * ((s : G)⁻¹ * l * (s : G))) * (s : G)⁻¹ := by rw [hc]
      _ = ((s : G) * z * (s : G)⁻¹) * l := by group
  let cs : ↥S → ↥(blockU L) → ↥(blockU L) := fun s u =>
    ⟨(s : G) * u * (s : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hSU s) u).mp u.2⟩
  have hcs_mul : ∀ s u v, cs s (u * v) = cs s u * cs s v := fun s u v => Subtype.ext (by
    simp only [cs, Subgroup.coe_mul]; group)
  have hcs_comp : ∀ s s' u, cs (s * s') u = cs s (cs s' u) := fun s s' u => Subtype.ext (by
    simp only [cs, Subgroup.coe_mul, mul_inv_rev]; group)
  have hcs_one : ∀ u, cs 1 u = u := fun u => Subtype.ext (by simp [cs])
  have hker : ∀ (s : ↥S) (u u' : ↥(blockU L)), D.β u = D.β u' →
      D.β (cs s u) = D.β (cs s u') := by
    intro s u u' h
    have hz : u'⁻¹ * u ∈ D.β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [D.ker_β, Subgroup.mem_subgroupOf] at hz
    have hmem : ((cs s u')⁻¹ * cs s u : ↥(blockU L)) ∈ D.β.ker := by
      rw [D.ker_β, Subgroup.mem_subgroupOf]
      have : (((cs s u')⁻¹ * cs s u : ↥(blockU L)) : G) =
          (s : G) * ((u'⁻¹ * u : ↥(blockU L)) : G) * (s : G)⁻¹ := by
        simp only [cs, Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [this]
      exact hZstab s _ hz
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hmem
    exact hmem.symm
  let σβ : Multiplicative (Fin 2 → F) → ↥(blockU L) := Function.surjInv D.surj_β
  have hσβ : ∀ w, D.β (σβ w) = w := fun w => Function.surjInv_eq D.surj_β w
  let ψf : ↥S → (Fin 2 → F) → (Fin 2 → F) := fun s w =>
    Multiplicative.toAdd (D.β (cs s (σβ (Multiplicative.ofAdd w))))
  have hψf : ∀ (s : ↥S) (u : ↥(blockU L)),
      ψf s (Multiplicative.toAdd (D.β u)) = Multiplicative.toAdd (D.β (cs s u)) := by
    intro s u
    show Multiplicative.toAdd (D.β (cs s (σβ (Multiplicative.ofAdd
      (Multiplicative.toAdd (D.β u)))))) = _
    rw [ofAdd_toAdd]
    exact congrArg Multiplicative.toAdd (hker s _ _ (hσβ _))
  have hψadd : ∀ (s : ↥S) (a b : Fin 2 → F), ψf s (a + b) = ψf s a + ψf s b := by
    intro s a b
    obtain ⟨ua, hua⟩ := D.surj_β (Multiplicative.ofAdd a)
    obtain ⟨ub, hub⟩ := D.surj_β (Multiplicative.ofAdd b)
    have ha : Multiplicative.toAdd (D.β ua) = a := by rw [hua]; rfl
    have hb : Multiplicative.toAdd (D.β ub) = b := by rw [hub]; rfl
    have hab : Multiplicative.toAdd (D.β (ua * ub)) = a + b := by
      rw [map_mul, toAdd_mul, ha, hb]
    calc ψf s (a + b) = ψf s (Multiplicative.toAdd (D.β (ua * ub))) := by rw [hab]
      _ = Multiplicative.toAdd (D.β (cs s (ua * ub))) := hψf s _
      _ = Multiplicative.toAdd (D.β (cs s ua)) + Multiplicative.toAdd (D.β (cs s ub)) := by
          rw [hcs_mul, map_mul, toAdd_mul]
      _ = ψf s a + ψf s b := by rw [← hψf, ← hψf, ha, hb]
  let ψ : ↥S → AddMonoid.End (Fin 2 → F) := fun s => AddMonoidHom.mk' (ψf s) (hψadd s)
  have hψ : ∀ (s : ↥S) (u : ↥(blockU L)),
      ψ s (Multiplicative.toAdd (D.β u)) = Multiplicative.toAdd (D.β (cs s u)) := hψf
  refine ⟨{ toFun := ψ, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · refine AddMonoidHom.ext fun w => ?_
    obtain ⟨u, hu⟩ := D.surj_β (Multiplicative.ofAdd w)
    have hw : Multiplicative.toAdd (D.β u) = w := by rw [hu]; rfl
    show ψ 1 w = w
    rw [← hw, hψ, hcs_one]
  · intro s s'
    refine AddMonoidHom.ext fun w => ?_
    obtain ⟨u, hu⟩ := D.surj_β (Multiplicative.ofAdd w)
    have hw : Multiplicative.toAdd (D.β u) = w := by rw [hu]; rfl
    show ψ (s * s') w = ψ s (ψ s' w)
    rw [← hw, hψ, hψ, hψ, hcs_comp]
  · intro s u v hv
    have : v = cs s u := Subtype.ext hv
    rw [this]
    exact hψ s u

theorem psi_conj (D : Lin2Data L F) {S : Subgroup G}
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (Ψ : ↥S →* AddMonoid.End (Fin 2 → F))
    (hΨ : ∀ (s : ↥S) (u v : ↥(blockU L)), (v : G) = (s : G) * u * (s : G)⁻¹ →
      Ψ s (Multiplicative.toAdd (D.β u)) = Multiplicative.toAdd (D.β v))
    (s : ↥S) (l l' : ↥L) (hl : (l' : G) = (s : G) * l * (s : G)⁻¹) (w : Fin 2 → F) :
    Ψ s (natEndHom F (D.α l) w) = natEndHom F (D.α l') (Ψ s w) := by
  have hlU : ∀ (l : ↥L) (u : ↥(blockU L)), (l : G) * u * (l : G)⁻¹ ∈ blockU L := fun l u =>
    (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L l.2) u).mp u.2
  have hsU : ∀ (s : ↥S) (u : ↥(blockU L)), (s : G) * u * (s : G)⁻¹ ∈ blockU L := fun s u =>
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (hSL s.2)) u).mp u.2
  obtain ⟨u, hu⟩ := D.surj_β (Multiplicative.ofAdd w)
  have hw : Multiplicative.toAdd (D.β u) = w := by rw [hu]; rfl
  subst hw
  set ul : ↥(blockU L) := ⟨(l : G) * u * (l : G)⁻¹, hlU l u⟩ with hul
  set us : ↥(blockU L) := ⟨(s : G) * u * (s : G)⁻¹, hsU s u⟩ with hus
  set uls : ↥(blockU L) := ⟨(s : G) * ul * (s : G)⁻¹, hsU s ul⟩ with huls
  set usl : ↥(blockU L) := ⟨(l' : G) * us * (l' : G)⁻¹, hlU l' us⟩ with husl
  have e1 : natEndHom F (D.α l) (Multiplicative.toAdd (D.β u)) =
      Multiplicative.toAdd (D.β ul) := (D.equiv l u ul rfl).symm
  have e2 : Ψ s (Multiplicative.toAdd (D.β ul)) = Multiplicative.toAdd (D.β uls) :=
    hΨ s ul uls rfl
  have e3 : Ψ s (Multiplicative.toAdd (D.β u)) = Multiplicative.toAdd (D.β us) := hΨ s u us rfl
  have e4 : natEndHom F (D.α l') (Multiplicative.toAdd (D.β us)) =
      Multiplicative.toAdd (D.β usl) := (D.equiv l' us usl rfl).symm
  have e5 : uls = usl := by
    apply Subtype.ext
    show (s : G) * ((l : G) * u * (l : G)⁻¹) * (s : G)⁻¹ =
      (l' : G) * ((s : G) * u * (s : G)⁻¹) * (l' : G)⁻¹
    rw [hl]
    group
  rw [e1, e2, e5, e3, e4]

theorem exists_phi [Finite F] (D : Lin2Data L F) {S : Subgroup G}
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (Ψ : ↥S →* AddMonoid.End (Fin 2 → F))
    (hΨ : ∀ (s : ↥S) (u v : ↥(blockU L)), (v : G) = (s : G) * u * (s : G)⁻¹ →
      Ψ s (Multiplicative.toAdd (D.β u)) = Multiplicative.toAdd (D.β v)) :
    ∃ Φ : ↥S →* RingAut F, ∀ (s : ↥S) (c : F) (v : Fin 2 → F), Ψ s (c • v) = Φ s c • Ψ s v := by
  classical
  let Ψu : ↥S →* (AddMonoid.End (Fin 2 → F))ˣ := Ψ.toHomUnits
  have hconj : ∀ (s : ↥S) (l : ↥L), ∃ l' : ↥L,
      Ψu s * natEnd F (D.α l) * (Ψu s)⁻¹ = natEnd F (D.α l') := by
    intro s l
    have hlmem : (s : G) * l * (s : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hSL s.2) l).mp l.2
    refine ⟨⟨_, hlmem⟩, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    refine Units.ext (AddMonoidHom.ext fun w => ?_)
    exact psi_conj D hSL Ψ hΨ s l ⟨_, hlmem⟩ rfl w
  have hN : ∀ s : ↥S, Ψu s ∈ Subgroup.normalizer
      ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) := by
    intro s
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨l, rfl⟩ := D.surj_α g
      obtain ⟨l', hl'⟩ := hconj s l
      exact ⟨D.α l', hl'.symm⟩
    · rintro ⟨g, hg⟩
      obtain ⟨l, rfl⟩ := D.surj_α g
      obtain ⟨l', hl'⟩ := hconj s⁻¹ l
      refine ⟨D.α l', ?_⟩
      rw [map_inv, inv_inv] at hl'
      rw [← hl', hg]
      group
  have hσ := fun s : ↥S => exists_sigma_of_mem_normalizer (Ψu s) (hN s)
  choose φ hφ using hσ
  refine ⟨MonoidHom.mk' φ fun s s' => ?_, fun s c v => hφ s c v⟩
  refine sigma_unique (Ψu (s * s')) (hφ (s * s')) ?_
  rw [map_mul]
  exact sigma_mul (Ψu s) (Ψu s') (hφ s) (hφ s')

end Action


end Lin2

end C56

end CFSG.QuasithinUnique
