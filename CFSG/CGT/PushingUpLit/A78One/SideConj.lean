module

public import CFSG.CGT.PushingUpLit.A78.Cfg
public import CFSG.CGT.PushingUpLit.A78One.OneStmts

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG CFSG.Open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.A78

variable {G : Type} [Group G]

theorem mem_cj_iff (g : G) (H : Subgroup G) (x : G) : x ∈ cj g H ↔ g⁻¹ * x * g ∈ H := by
  show x ∈ H.map (MulAut.conj g).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem cj_sup (g : G) (A B : Subgroup G) : cj g (A ⊔ B) = cj g A ⊔ cj g B :=
  Subgroup.map_sup _ _ _

theorem cj_card (g : G) (H : Subgroup G) : Nat.card (cj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem cj_normalizer (g : G) (H : Subgroup G) :
    Subgroup.normalizer ((cj g H : Subgroup G) : Set G) = cj g (Subgroup.normalizer (H : Set G)) :=
  Subgroup.map_equiv_normalizer_eq H (MulAut.conj g) |>.symm

theorem cj_centralizer (g : G) (H : Subgroup G) :
    Subgroup.centralizer ((cj g H : Subgroup G) : Set G) =
      cj g (Subgroup.centralizer (H : Set G)) := by
  ext x
  rw [mem_cj_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have h1 := h (g * y * g⁻¹) ((mem_cj_iff g H _).2 (by simpa [mul_assoc] using hy))
    have h2 : g * y * g⁻¹ * x = x * (g * y * g⁻¹) := h1
    calc y * (g⁻¹ * x * g) = g⁻¹ * (g * y * g⁻¹ * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h2]
      _ = g⁻¹ * x * g * y := by group
  · intro h y hy
    have h1 := h (g⁻¹ * y * g) ((mem_cj_iff g H y).1 hy)
    have h2 : g⁻¹ * y * g * (g⁻¹ * x * g) = g⁻¹ * x * g * (g⁻¹ * y * g) := h1
    calc y * x = g * (g⁻¹ * y * g * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ := by rw [h2]
      _ = x * y := by group

@[expose] def cjEquiv (g : G) (H : Subgroup G) : ↥H ≃* ↥(cj g H) := (MulAut.conj g).subgroupMap H

theorem cjEquiv_coe (g : G) (H : Subgroup G) (x : H) :
    ((cjEquiv g H x : cj g H) : G) = g * x * g⁻¹ := rfl

theorem cjEquiv_symm_coe (g : G) (H : Subgroup G) (y : cj g H) :
    (((cjEquiv g H).symm y : H) : G) = g⁻¹ * y * g := by
  have h := cjEquiv_coe g H ((cjEquiv g H).symm y)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  group

section Finite

variable [Finite G]

theorem isSylowOf_cj {P K : Subgroup G} (g : G) (h : CFSG.ABGLocalTools.IsSylowOf 2 P K) :
    CFSG.ABGLocalTools.IsSylowOf 2 (cj g P) (cj g K) := by
  refine CFSG.ABGLocalTools.isSylowOf_of_card (Subgroup.map_mono h.le) ?_
  rw [cj_card, cj_card]
  exact h.card_eq

omit [Finite G] in
theorem isElemAbelian_cj {H : Subgroup G} (g : G) (h : CFSG.Open.IsElemAbelian 2 H) :
    CFSG.Open.IsElemAbelian 2 (cj g H) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have h1 := h.1.1.comm ⟨g⁻¹ * a * g, (mem_cj_iff g H a).1 a.2⟩
      ⟨g⁻¹ * b * g, (mem_cj_iff g H b).1 b.2⟩
    apply Subtype.ext
    have h2 : g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * b * g * (g⁻¹ * a * g) :=
      congrArg Subtype.val h1
    calc (a : G) * b = g * (g⁻¹ * a * g * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * b * g * (g⁻¹ * a * g)) * g⁻¹ := by rw [h2]
      _ = b * a := by group
  · have h1 := h.2 _ ((mem_cj_iff g H x).1 hx)
    have h2 : (g⁻¹ * x * g⁻¹⁻¹) ^ 2 = g⁻¹ * x ^ 2 * g⁻¹⁻¹ := conj_pow
    rw [inv_inv] at h2
    rw [h2] at h1
    have h3 : g⁻¹ * x ^ 2 * g⁻¹⁻¹ = 1 := by rw [inv_inv]; exact h1
    exact (conj_eq_one_iff.1 h3)

omit [Finite G] in
theorem cj_oTwoIn (g : G) (X : Subgroup G) : oTwoIn (cj g X) = cj g (oTwoIn X) :=
  oTwoIn_map_equiv (MulAut.conj g) X

omit [Finite G] in
theorem quot_cj {E W : Subgroup G} {n : ℕ} (g : G)
    (h : ∃ φ : ↥(E ⊔ W) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Function.Surjective φ ∧ φ.ker = W.subgroupOf (E ⊔ W)) :
    ∃ φ : ↥(cj g E ⊔ cj g W) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Function.Surjective φ ∧ φ.ker = (cj g W).subgroupOf (cj g E ⊔ cj g W) := by
  obtain ⟨φ, hs, hk⟩ := h
  rw [← cj_sup]
  have key : ∀ y : ↥(cj g (E ⊔ W)),
      φ ((cjEquiv g (E ⊔ W)).symm y) = 1 ↔ (y : G) ∈ cj g W := by
    intro y
    rw [← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf, cjEquiv_symm_coe, mem_cj_iff]
  refine ⟨φ.comp (cjEquiv g (E ⊔ W)).symm.toMonoidHom,
    hs.comp (cjEquiv g (E ⊔ W)).symm.surjective, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, key x,
    Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem isNatSL_cj {E W : Subgroup G} {n : ℕ} (g : G) (h : IsNatSL E W n) :
    IsNatSL (cj g E) (cj g W) n := by
  obtain ⟨φ, ψ, hφs, hφk, hψs, hψk, hequiv⟩ := h
  refine ⟨φ.comp (cjEquiv g E).symm.toMonoidHom, ψ.comp (cjEquiv g W).symm.toMonoidHom,
    hφs.comp (cjEquiv g E).symm.surjective, ?_, hψs.comp (cjEquiv g W).symm.surjective, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker,
      hφk, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, cjEquiv_symm_coe, Subgroup.mem_inf,
      Subgroup.mem_inf, cj_centralizer, mem_cj_iff g E,
      mem_cj_iff g (Subgroup.centralizer (W : Set G))]
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker,
      hψk, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, cjEquiv_symm_coe, Subgroup.mem_inf,
      Subgroup.mem_inf, cj_centralizer, mem_cj_iff g W,
      mem_cj_iff g (Subgroup.centralizer (E : Set G))]
  · intro e' w' hw
    have hw' : ((cjEquiv g E).symm e' : G) * ((cjEquiv g W).symm w' : G) *
        ((cjEquiv g E).symm e' : G)⁻¹ ∈ W := by
      have h1 := (mem_cj_iff g W _).1 hw
      rw [cjEquiv_symm_coe, cjEquiv_symm_coe]
      have e1 : g⁻¹ * (e' : G) * g * (g⁻¹ * (w' : G) * g) * (g⁻¹ * (e' : G) * g)⁻¹ =
          g⁻¹ * ((e' : G) * w' * (e' : G)⁻¹) * g := by group
      rw [e1]
      exact h1
    have hsub : (cjEquiv g W).symm ⟨(e' : G) * w' * (e' : G)⁻¹, hw⟩ =
        ⟨((cjEquiv g E).symm e' : G) * ((cjEquiv g W).symm w' : G) *
          ((cjEquiv g E).symm e' : G)⁻¹, hw'⟩ := by
      apply Subtype.ext
      have h1 : (((cjEquiv g W).symm ⟨(e' : G) * w' * (e' : G)⁻¹, hw⟩ : W) : G) =
          g⁻¹ * ((e' : G) * w' * (e' : G)⁻¹) * g := cjEquiv_symm_coe g W _
      have h2 : (((cjEquiv g E).symm e' : E) : G) = g⁻¹ * (e' : G) * g :=
        cjEquiv_symm_coe g E e'
      have h3 : (((cjEquiv g W).symm w' : W) : G) = g⁻¹ * (w' : G) * g :=
        cjEquiv_symm_coe g W w'
      show (((cjEquiv g W).symm ⟨(e' : G) * w' * (e' : G)⁻¹, hw⟩ : W) : G) =
        ((cjEquiv g E).symm e' : G) * ((cjEquiv g W).symm w' : G) *
          ((cjEquiv g E).symm e' : G)⁻¹
      rw [h1, h2, h3]
      group
    have key := hequiv ((cjEquiv g E).symm e') ((cjEquiv g W).symm w') hw'
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hsub]
    exact key

omit [Finite G] in
theorem cj_cj_inv (g : G) (N : Subgroup G) : cj g (cj g⁻¹ N) = N := by
  ext x
  rw [mem_cj_iff, mem_cj_iff]
  simp [mul_assoc]

omit [Finite G] in
theorem mem_cj_of_mem (g : G) {H : Subgroup G} {x : G} (hx : x ∈ H) : g * x * g⁻¹ ∈ cj g H :=
  Subgroup.mem_map.2 ⟨x, hx, rfl⟩

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.conj {L T J : Subgroup G} {e : ℕ}
    (h : A78Side G L T J e) (g : G) : A78Side G (cj g L) (cj g T) (cj g J) e := by
  have hX : cj g L ⊔ cj g T = cj g (L ⊔ T) := (cj_sup g L T).symm
  have hW : oTwoIn (cj g L ⊔ cj g T) = cj g (oTwoIn (L ⊔ T)) := by rw [hX, cj_oTwoIn]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cj_normalizer]
    exact isSylowOf_cj g h.sylow
  · rw [hW]
    exact isElemAbelian_cj g h.elem
  · rw [hW]
    exact quot_cj g h.quot
  · rw [hW]
    exact isNatSL_cj g h.nat
  · rw [hW, ← cj_sup]
    exact isSylowOf_cj g h.sylowJ
  · rw [hX, cj_normalizer]
    have hu := h.unique
    have hmem : Subgroup.normalizer (L : Set G) ∈
        maximalTwoLocalsContaining ((L ⊔ T : Subgroup G) : Set G) := by rw [hu]; rfl
    ext N
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hN, hNle⟩
      have hN' : CFSG.IsMaximalTwoLocal (cj g⁻¹ N) :=
        CFSG.CGT.PushingUp.isMaximalTwoLocal_map_conj hN g⁻¹
      have hle : ((L ⊔ T : Subgroup G) : Set G) ⊆ (cj g⁻¹ N : Subgroup G) := by
        intro x hx
        rw [SetLike.mem_coe, mem_cj_iff, inv_inv]
        exact hNle (mem_cj_of_mem g hx)
      have h1 : cj g⁻¹ N ∈ maximalTwoLocalsContaining ((L ⊔ T : Subgroup G) : Set G) :=
        ⟨hN', hle⟩
      rw [hu, Set.mem_singleton_iff] at h1
      rw [← cj_cj_inv g N, h1]
    · rintro rfl
      refine ⟨CFSG.CGT.PushingUp.isMaximalTwoLocal_map_conj hmem.1 g, fun y hy => ?_⟩
      have hLT : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := fun x hx => hmem.2 hx
      exact Subgroup.map_mono hLT hy

end Finite

end CFSG.CGT.PushingUpLit.A78One
