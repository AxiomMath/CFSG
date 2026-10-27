module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Gen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Gl
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.LieType.Steinberg.TwistedD4.Quasisimple

public section

namespace CFSG.AGLEmbedding.ChevOuterD48

set_option linter.unusedSectionVars false

open CFSG.Quasithin CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Ree
open CFSG.Open (quasithinRootElt quasithinD4Root)

theorem map_rootElt {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (pos : List (Fin 8 × Fin 8)) (t : K) :
    (quasithinRootElt pos t).map f = quasithinRootElt pos (f t) := by
  ext r c
  simp only [quasithinRootElt, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem map_Xm {k : Type*} [CommRing k] (f : k →+* GF512) (a : k) (s : Bool) :
    (quasithinRootElt (quasithinD4Root 0 s) a * quasithinRootElt (quasithinD4Root 2 s) (a ^ 8) *
      quasithinRootElt (quasithinD4Root 3 s) (a ^ 64)).map f =
    quasithinRootElt (quasithinD4Root 0 s) (f a) *
      quasithinRootElt (quasithinD4Root 2 s) (f a ^ 8) *
      quasithinRootElt (quasithinD4Root 3 s) (f a ^ 64) := by
  rw [Matrix.map_mul, Matrix.map_mul, map_rootElt, map_rootElt, map_rootElt, map_pow, map_pow]

theorem coe_map_gl {k L : Type*} [CommRing k] [CommRing L] (f : k →+* L) (A : GL (Fin 8) k) :
    ((Matrix.GeneralLinearGroup.map f A : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) =
      (A : Matrix (Fin 8) (Fin 8) k).map f := by
  simp [Matrix.GeneralLinearGroup.map]

section Outer

variable {k : Type} [Field k] [CharP k 2]

theorem coe_outer_nat (a : k) (s : Bool) :
    ((d4bNat k (nd 0) s a * d4bNat k (nd 1) s (a ^ 8) * d4bNat k (nd 3) s (a ^ 64) :
      GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) =
    quasithinRootElt (quasithinD4Root 0 s) a * quasithinRootElt (quasithinD4Root 2 s) (a ^ 8) *
      quasithinRootElt (quasithinD4Root 3 s) (a ^ 64) := by
  rw [Units.val_mul, Units.val_mul]
  exact d4bUm_outer (nd 0) (nd 1) (nd 3) rfl rfl rfl s a _ _

theorem map_outer_nat (e : k ≃+* GF512) (b : GF512) (s : Bool) :
    ((Matrix.GeneralLinearGroup.map e.toRingHom
      (d4bNat k (nd 0) s (e.symm b) * d4bNat k (nd 1) s (e.symm b ^ 8) *
        d4bNat k (nd 3) s (e.symm b ^ 64)) : GL (Fin 8) GF512) : Matrix (Fin 8) (Fin 8) GF512) =
    quasithinRootElt (quasithinD4Root 0 s) b * quasithinRootElt (quasithinD4Root 2 s) (b ^ 8) *
      quasithinRootElt (quasithinD4Root 3 s) (b ^ 64) := by
  rw [coe_map_gl, coe_outer_nat, map_Xm]
  simp

end Outer

section Psi

variable {k : Type} [Field k] [CharP k 2] [Finite k]

@[expose] noncomputable def psiTw (σ : k →+* k) (e : k ≃+* GF512) :
    twistedGroup σ →* GL (Fin 8) GF512 :=
  (Matrix.GeneralLinearGroup.map e.toRingHom).comp
    ((d48bΨ' (k := k)).comp (twistedGroup σ).subtype)

variable (σ : k →+* k) (hk : Nat.card k = 8 ^ 3) (hσ : ∀ c, σ c = c ^ 8) (e : k ≃+* GF512)

include hk hσ in
theorem range_psiTw :
    (psiTw σ e).range = letterGroup := by
  have hmap := g8_map_twistedGroup hk σ hσ
  have hpre : ∀ A : GL (Fin 8) k, A ∈ g8Group k →
      Matrix.GeneralLinearGroup.map e.toRingHom A ∈ (psiTw σ e).range := by
    intro A hA
    rw [← hmap] at hA
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hA
    exact ⟨⟨g, hg⟩, rfl⟩
  apply le_antisymm
  ·
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    have hgg : d48bΨ' (k := k) g ∈ g8Group k := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hg
    show Matrix.GeneralLinearGroup.map e.toRingHom (d48bΨ' (k := k) g) ∈ letterGroup
    generalize d48bΨ' (k := k) g = y at hgg
    unfold g8Group at hgg
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
      · have hc' : (e c) ^ 8 = e c := by rw [← map_pow, hc]
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
    have hOuter : ∀ (s : Bool) (b : GF512),
        Matrix.GeneralLinearGroup.map e.toRingHom
          (d4bNat k (nd 0) s (e.symm b) * d4bNat k (nd 1) s (e.symm b ^ 8) *
            d4bNat k (nd 3) s (e.symm b ^ 64)) ∈ (psiTw σ e).range := fun s b =>
      hpre _ (g8_mem_outer (nd 0) (nd 1) (nd 3) rfl rfl rfl s (e.symm b))
    have hX : ∀ b : GF512, XGL b ∈ (psiTw σ e).range := by
      intro b
      have h := hOuter true b
      have : Matrix.GeneralLinearGroup.map e.toRingHom
          (d4bNat k (nd 0) true (e.symm b) * d4bNat k (nd 1) true (e.symm b ^ 8) *
            d4bNat k (nd 3) true (e.symm b ^ 64)) = XGL b :=
        Units.ext (map_outer_nat e b true)
      rwa [this] at h
    have hY : ∀ b : GF512, YGL b ∈ (psiTw σ e).range := by
      intro b
      have h := hOuter false b
      have : Matrix.GeneralLinearGroup.map e.toRingHom
          (d4bNat k (nd 0) false (e.symm b) * d4bNat k (nd 1) false (e.symm b ^ 8) *
            d4bNat k (nd 3) false (e.symm b ^ 64)) = YGL b :=
        Units.ext (map_outer_nat e b false)
      rwa [this] at h
    have hZ : ∀ (s : Bool) (c : GF512), c ^ 8 = c → ZGL s c ∈ (psiTw σ e).range := by
      intro s c hc
      have hc' : (e.symm c) ^ 8 = e.symm c := by
        rw [← map_pow, hc]
      have h := hpre _ (g8_mem_mid (k := k) (nd 2) rfl s hc')
      have : Matrix.GeneralLinearGroup.map e.toRingHom (d4bNat k (nd 2) s (e.symm c)) =
          ZGL s c := by
        apply Units.ext
        rw [coe_map_gl]
        have hm : ((d4bNat k (nd 2) s (e.symm c) : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) =
            quasithinRootElt (quasithinD4Root 1 s) (e.symm c) := d4bUm_mid (nd 2) rfl s _
        rw [hm, map_rootElt]
        simp [ZGL, Zm]
      rwa [this] at h
    by_cases h9 : n < 9
    · rw [letterGL_of_lt_nine h9]; exact hX _
    by_cases h12 : n < 12
    · rw [letterGL_of_mid_pos (by omega) h12]; exact hZ true _ (xC_pow_eight _)
    by_cases h21 : n < 21
    · rw [letterGL_of_neg (by omega) h21]; exact hY _
    · rw [letterGL_of_mid_neg (by omega)]; exact hZ false _ (xC_pow_eight _)

end Psi

section Graph

variable {k : Type} [Field k] [CharP k 2] [Finite k]
  (σ : k ≃+* k) (hk : Nat.card k = 8 ^ 3) (hσ : ∀ c, σ c = c ^ 8) (e : k ≃+* GF512)

include hk hσ in
theorem graph_eq_map :
    graphFixedRootGroup TwistTag.D4 k σ.toRingHom =
      (twistedGroup σ.toRingHom).map (adjointGroup d4 k).subtype := by
  have hk' : Nat.card k = (2 ^ 3) ^ 3 := by rw [hk]; norm_num
  have hσ' : ∀ c, σ.toRingHom c = c ^ (2 ^ 3) := fun c => by simpa using hσ c
  have hσ8 : ∀ c, σ.toRingHom c = c ^ 8 := fun c => by simpa using hσ c
  exact (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two (f := 3) (by norm_num) k hk'
    σ.toRingHom hσ').2.2.1.symm.trans
    (commutator_twistedFixedGroup_eq_map σ.toRingHom (q := 8) (by norm_num) hk hσ8)

@[expose] noncomputable def gam (hC0 : graphFixedRootGroup TwistTag.D4 k σ.toRingHom =
    (twistedGroup σ.toRingHom).map (adjointGroup d4 k).subtype) :
    ↥(graphFixedRootGroup TwistTag.D4 k σ.toRingHom) ≃* twistedGroup σ.toRingHom :=
  (MulEquiv.subgroupCongr hC0).trans (Subgroup.equivMapOfInjective _ (adjointGroup d4 k).subtype
    (adjointGroup d4 k).subtype_injective).symm

theorem coe_gam (hC0 : graphFixedRootGroup TwistTag.D4 k σ.toRingHom =
    (twistedGroup σ.toRingHom).map (adjointGroup d4 k).subtype)
    (x : ↥(graphFixedRootGroup TwistTag.D4 k σ.toRingHom)) :
    (((gam σ hC0 x : twistedGroup σ.toRingHom) : adjointGroup d4 k) : ModGL d4 k) =
      (x : ModGL d4 k) := by
  have h := (Subgroup.equivMapOfInjective _ (adjointGroup d4 k).subtype
    (adjointGroup d4 k).subtype_injective).apply_symm_apply (MulEquiv.subgroupCongr hC0 x)
  have h2 := congrArg (fun z : ↥((twistedGroup σ.toRingHom).map (adjointGroup d4 k).subtype) =>
    (z : ModGL d4 k)) h
  simp only [Subgroup.coe_equivMapOfInjective_apply] at h2
  exact h2

@[expose] noncomputable def psiC (hC0 : graphFixedRootGroup TwistTag.D4 k σ.toRingHom =
    (twistedGroup σ.toRingHom).map (adjointGroup d4 k).subtype) :
    ↥(graphFixedRootGroup TwistTag.D4 k σ.toRingHom) →* GL (Fin 8) GF512 :=
  (psiTw σ.toRingHom e).comp (gam σ hC0).toMonoidHom

include hk hσ in
theorem range_psiC (hC0 : graphFixedRootGroup TwistTag.D4 k σ.toRingHom =
    (twistedGroup σ.toRingHom).map (adjointGroup d4 k).subtype) :
    (psiC σ e hC0).range = letterGroup := by
  have hσ8 : ∀ c, σ.toRingHom c = c ^ 8 := fun c => by simpa using hσ c
  rw [← range_psiTw σ.toRingHom hk hσ8 e]
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨gam σ hC0 g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨(gam σ hC0).symm g, by
      simp only [psiC, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]⟩

theorem d48bΨ_xElement (i : Fin d4.rank) (c : k) :
    d48bΨ' (k := k) (xElement i c) = d4bNat k i true c :=
  d48bΨ_of_xOp k _ i c rfl

theorem d48bΨ_yElement (i : Fin d4.rank) (c : k) :
    d48bΨ' (k := k) (yElement i c) = d4bNat k i false c :=
  d48bΨ_of_yOp k _ i c rfl

theorem map_d4bNat (δ : k →+* k) (i : Fin d4.rank) (s : Bool) (c : k) :
    Matrix.GeneralLinearGroup.map δ (d4bNat k i s c) = d4bNat k i s (δ c) := by
  apply Units.ext
  rw [coe_map_gl]
  have hφ : δ.comp (d4bφ k) = d4bφ k := RingHom.ext_zmod _ _
  have hE : ∀ r q, δ (d4bEk k i s r q) = d4bEk k i s r q := by
    intro r q
    simp only [d4bEk, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact congrArg (fun f : ZMod 2 →+* k => f (d4bEs i s r q)) hφ
  ext r q
  show δ (d4bUm k i s c r q) = d4bUm k i s (δ c) r q
  simp only [d4bUm, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, hE,
    Matrix.one_apply]
  split_ifs <;> simp

theorem d48bΨ_frobeniusTwist (δ : k →+* k) (x : adjointGroup d4 k) :
    d48bΨ' (k := k) (frobeniusTwist d4 k δ x) =
      Matrix.GeneralLinearGroup.map δ (d48bΨ' (k := k) x) := by
  have := adjointGroup_hom_ext
    (f := (d48bΨ' (k := k)).comp (frobeniusTwist d4 k δ))
    (g := (Matrix.GeneralLinearGroup.map δ).comp (d48bΨ' (k := k))) (fun i c => ?_)
    (fun i c => ?_)
  · exact DFunLike.congr_fun this x
  · simp only [MonoidHom.comp_apply, frobeniusTwist_xElement, d48bΨ_xElement, map_d4bNat]
  · simp only [MonoidHom.comp_apply, frobeniusTwist_yElement, d48bΨ_yElement, map_d4bNat]

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
  ext x
  simp

end Graph

end CFSG.AGLEmbedding.ChevOuterD48
