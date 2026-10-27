module

public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.Gen
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.Gl
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Link

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

set_option linter.unusedSectionVars false

open CFSG.Quasithin CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Ree
  CFSG.AGLEmbedding.ChevOuter
open CFSG.Open (quasithinRootElt quasithinD4Root)
open CFSG.AGLEmbedding.ChevOuterD48 (map_rootElt coe_map_gl d48bΨ' d48bΨ_xElement d48bΨ_yElement
  map_d4bNat d48bΨ_frobeniusTwist gam coe_gam)

theorem map_Xm {k : Type*} [CommRing k] (f : k →+* GF64) (a : k) (s : Bool) :
    (quasithinRootElt (quasithinD4Root 0 s) a * quasithinRootElt (quasithinD4Root 2 s) (a ^ 4) *
      quasithinRootElt (quasithinD4Root 3 s) (a ^ 16)).map f =
    quasithinRootElt (quasithinD4Root 0 s) (f a) *
      quasithinRootElt (quasithinD4Root 2 s) (f a ^ 4) *
      quasithinRootElt (quasithinD4Root 3 s) (f a ^ 16) := by
  rw [Matrix.map_mul, Matrix.map_mul, map_rootElt, map_rootElt, map_rootElt, map_pow, map_pow]

section Outer

variable {k : Type} [Field k] [CharP k 2]

theorem coe_outer_nat (a : k) (s : Bool) :
    ((d4bNat k (nd 0) s a * d4bNat k (nd 1) s (a ^ 4) * d4bNat k (nd 3) s (a ^ 16) :
      GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) =
    quasithinRootElt (quasithinD4Root 0 s) a * quasithinRootElt (quasithinD4Root 2 s) (a ^ 4) *
      quasithinRootElt (quasithinD4Root 3 s) (a ^ 16) := by
  rw [Units.val_mul, Units.val_mul]
  exact d4bUm_outer (nd 0) (nd 1) (nd 3) rfl rfl rfl s a _ _

theorem map_outer_nat (e : k ≃+* GF64) (b : GF64) (s : Bool) :
    ((Matrix.GeneralLinearGroup.map e.toRingHom
      (d4bNat k (nd 0) s (e.symm b) * d4bNat k (nd 1) s (e.symm b ^ 4) *
        d4bNat k (nd 3) s (e.symm b ^ 16)) : GL (Fin 8) GF64) : Matrix (Fin 8) (Fin 8) GF64) =
    quasithinRootElt (quasithinD4Root 0 s) b * quasithinRootElt (quasithinD4Root 2 s) (b ^ 4) *
      quasithinRootElt (quasithinD4Root 3 s) (b ^ 16) := by
  rw [coe_map_gl, coe_outer_nat, map_Xm]
  simp

end Outer

section Psi

variable {k : Type} [Field k] [CharP k 2] [Finite k]

@[expose] noncomputable def psiTw (σ : k →+* k) (e : k ≃+* GF64) :
    twistedGroup σ →* GL (Fin 8) GF64 :=
  (Matrix.GeneralLinearGroup.map e.toRingHom).comp
    ((d48bΨ' (k := k)).comp (twistedGroup σ).subtype)

variable (σ : k →+* k) (hk : Nat.card k = 4 ^ 3) (hσ : ∀ c, σ c = c ^ 4) (e : k ≃+* GF64)

include hk hσ in
theorem range_psiTw :
    (psiTw σ e).range = letterGroup := by
  have hmap := g4_map_twistedGroup hk σ hσ
  have hpre : ∀ A : GL (Fin 8) k, A ∈ g4Group k →
      Matrix.GeneralLinearGroup.map e.toRingHom A ∈ (psiTw σ e).range := by
    intro A hA
    rw [← hmap] at hA
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hA
    exact ⟨⟨g, hg⟩, rfl⟩
  apply le_antisymm
  ·
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    have hgg : d48bΨ' (k := k) g ∈ g4Group k := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hg
    show Matrix.GeneralLinearGroup.map e.toRingHom (d48bΨ' (k := k) g) ∈ letterGroup
    generalize d48bΨ' (k := k) g = y at hgg
    unfold g4Group at hgg
    induction hgg using Subgroup.closure_induction with
    | mem A hA =>
      rcases hA with ⟨a, s, hs⟩ | ⟨c, s, hc, hs⟩
      · have : Matrix.GeneralLinearGroup.map e.toRingHom A =
            if s then XGL (e a) else YGL (e a) := by
          apply Units.ext
          rw [coe_map_gl, hs, map_Xm]
          cases s <;> rfl
        rw [this]
        cases s
        · exact YGL_mem _
        · exact XGL_mem _
      · have hc' : (e c) ^ 4 = e c := by rw [← map_pow, hc]
        have : Matrix.GeneralLinearGroup.map e.toRingHom A = ZGL s (e c) := by
          apply Units.ext
          rw [coe_map_gl, hs, map_rootElt]
          cases s <;> rfl
        rw [this]
        exact ZGL_mem s hc'
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
  ·
    rw [letterGroup, Subgroup.closure_le]
    rintro _ ⟨n, hn, rfl⟩
    have hOuter : ∀ (s : Bool) (b : GF64),
        Matrix.GeneralLinearGroup.map e.toRingHom
          (d4bNat k (nd 0) s (e.symm b) * d4bNat k (nd 1) s (e.symm b ^ 4) *
            d4bNat k (nd 3) s (e.symm b ^ 16)) ∈ (psiTw σ e).range := fun s b =>
      hpre _ (g4_mem_outer (nd 0) (nd 1) (nd 3) rfl rfl rfl s (e.symm b))
    have hX : ∀ b : GF64, XGL b ∈ (psiTw σ e).range := by
      intro b
      have h := hOuter true b
      have : Matrix.GeneralLinearGroup.map e.toRingHom
          (d4bNat k (nd 0) true (e.symm b) * d4bNat k (nd 1) true (e.symm b ^ 4) *
            d4bNat k (nd 3) true (e.symm b ^ 16)) = XGL b :=
        Units.ext (map_outer_nat e b true)
      rwa [this] at h
    have hY : ∀ b : GF64, YGL b ∈ (psiTw σ e).range := by
      intro b
      have h := hOuter false b
      have : Matrix.GeneralLinearGroup.map e.toRingHom
          (d4bNat k (nd 0) false (e.symm b) * d4bNat k (nd 1) false (e.symm b ^ 4) *
            d4bNat k (nd 3) false (e.symm b ^ 16)) = YGL b :=
        Units.ext (map_outer_nat e b false)
      rwa [this] at h
    have hZ : ∀ (s : Bool) (c : GF64), c ^ 4 = c → ZGL s c ∈ (psiTw σ e).range := by
      intro s c hc
      have hc' : (e.symm c) ^ 4 = e.symm c := by
        rw [← map_pow, hc]
      have h := hpre _ (g4_mem_mid (k := k) (nd 2) rfl s hc')
      have : Matrix.GeneralLinearGroup.map e.toRingHom (d4bNat k (nd 2) s (e.symm c)) =
          ZGL s c := by
        apply Units.ext
        rw [coe_map_gl]
        have hm : ((d4bNat k (nd 2) s (e.symm c) : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) =
            quasithinRootElt (quasithinD4Root 1 s) (e.symm c) := d4bUm_mid (nd 2) rfl s _
        rw [hm, map_rootElt]
        simp [ZGL, Zm]
      rwa [this] at h
    by_cases h12 : n < 12
    · by_cases hev : n % 2 = 0
      · rw [letterGL_of_even h12 hev]; exact hX _
      · rw [letterGL_of_odd h12 (by omega)]; exact hY _
    · by_cases hev : n % 2 = 0
      · rw [letterGL_pos_mid (by omega) hn hev]
        refine hZ true _ ?_
        split_ifs
        · simp
        · exact wqC_pow_four
      · rw [letterGL_neg_mid (by omega) hn (by omega)]
        refine hZ false _ ?_
        split_ifs
        · simp
        · exact wqC_pow_four

end Psi

section Graph

variable {k : Type} [Field k] [CharP k 2] [Finite k]
  (σ : k ≃+* k) (hk : Nat.card k = 4 ^ 3) (hσ : ∀ c, σ c = c ^ 4) (e : k ≃+* GF64)

include hk hσ in
theorem graph_eq_map :
    graphFixedRootGroup TwistTag.D4 k σ.toRingHom =
      (twistedGroup σ.toRingHom).map (adjointGroup d4 k).subtype := by
  have hk' : Nat.card k = (2 ^ 2) ^ 3 := by rw [hk]; norm_num
  have hσ' : ∀ c, σ.toRingHom c = c ^ (2 ^ 2) := fun c => by simpa using hσ c
  have hσ4 : ∀ c, σ.toRingHom c = c ^ 4 := fun c => by simpa using hσ c
  exact (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two (f := 2) (by norm_num) k hk'
    σ.toRingHom hσ').2.2.1.symm.trans
    (commutator_twistedFixedGroup_eq_map σ.toRingHom (q := 4) (by norm_num) hk hσ4)

@[expose] noncomputable def psiC (hC0 : graphFixedRootGroup TwistTag.D4 k σ.toRingHom =
    (twistedGroup σ.toRingHom).map (adjointGroup d4 k).subtype) :
    ↥(graphFixedRootGroup TwistTag.D4 k σ.toRingHom) →* GL (Fin 8) GF64 :=
  (psiTw σ.toRingHom e).comp (gam σ hC0).toMonoidHom

include hk hσ in
theorem range_psiC (hC0 : graphFixedRootGroup TwistTag.D4 k σ.toRingHom =
    (twistedGroup σ.toRingHom).map (adjointGroup d4 k).subtype) :
    (psiC σ e hC0).range = letterGroup := by
  have hσ4 : ∀ c, σ.toRingHom c = c ^ 4 := fun c => by simpa using hσ c
  rw [← range_psiTw σ.toRingHom hk hσ4 e]
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨gam σ hC0 g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨(gam σ hC0).symm g, by
      simp only [psiC, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]⟩

include hk hσ in
theorem psiC_fieldActor (hC0 : graphFixedRootGroup TwistTag.D4 k σ.toRingHom =
    (twistedGroup σ.toRingHom).map (adjointGroup d4 k).subtype) (δ : k ≃+* k)
    (g : ↥(graphFixedRootGroup TwistTag.D4 k σ.toRingHom)) :
    psiC σ e hC0 (fieldActor (t := TwistTag.D4) σ δ g) =
      Matrix.GeneralLinearGroup.map (e.symm.trans (δ.trans e)).toRingHom (psiC σ e hC0 g) := by
  have h1 : ((gam σ hC0 (fieldActor (t := TwistTag.D4) σ δ g) : twistedGroup σ.toRingHom) :
      adjointGroup d4 k) =
      frobeniusTwist d4 k δ.toRingHom ((gam σ hC0 g : twistedGroup σ.toRingHom) :
        adjointGroup d4 k) := by
    apply Subtype.ext
    rw [coe_gam, coe_frobeniusTwist, coe_fieldActor, ← coe_gam σ hC0 g]
    rfl
  simp only [psiC, psiTw, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [h1, d48bΨ_frobeniusTwist]
  apply Units.ext
  simp only [coe_map_gl, Matrix.map_map]
  congr 1
  funext x
  simp

end Graph

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
