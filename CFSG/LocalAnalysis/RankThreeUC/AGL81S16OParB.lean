module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OAct
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ORad

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite)

section ParB

variable {G : Type} [Group G] [Finite G] {n : ℕ} {M L V : Subgroup G} (d : O6NatData G n L V)

theorem O6NatData.one_le_n (d : O6NatData G n L V) : 1 ≤ n := by
  have h1 := d.card_F
  have h2 : 1 < Nat.card d.F := Finite.one_lt_card
  by_contra h
  have h0 : n = 0 := by omega
  have h3 : (2 : ℕ) ^ n = 1 := by rw [h0]; rfl
  rw [h3] at h1
  omega

instance O6NatData.instCharP : CharP d.F 2 := d.charP d.one_le_n

theorem O6NatData.act_mul (hMV : M ≤ normalizer (V : Set G)) {m m' : G} (hm : m ∈ M)
    (hm' : m' ∈ M) (x : OW d.F) :
    d.act (m * m') (hMV (M.mul_mem hm hm')) x = d.act m (hMV hm) (d.act m' (hMV hm') x) := by
  have h := congrArg (fun f => f x) ((d.rho M hMV).map_mul ⟨m, hm⟩ ⟨m', hm'⟩)
  exact h

theorem O6NatData.act_one (hMV : M ≤ normalizer (V : Set G)) (x : OW d.F) :
    d.act 1 (hMV M.one_mem) x = x := by
  have h := congrArg (fun f => f x) (d.rho M hMV).map_one
  exact h

def O6NatData.Lam (hMV : M ≤ normalizer (V : Set G)) : Subgroup G where
  carrier := {m | ∃ hm : m ∈ M, ∃ g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F,
    g ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c) ∧ ∀ x, d.act m (hMV hm) x = gv g x}
  mul_mem' := by
    rintro m m' ⟨hm, g, hg, hgx⟩ ⟨hm', g', hg', hg'x⟩
    refine ⟨M.mul_mem hm hm', g * g', mul_mem hg hg', fun x => ?_⟩
    rw [d.act_mul hMV hm hm', hg'x, hgx, gv_mul]
  one_mem' := ⟨M.one_mem, 1, one_mem _, fun x => by rw [d.act_one hMV, gv_one]⟩
  inv_mem' := by
    rintro m ⟨hm, g, hg, hgx⟩
    refine ⟨M.inv_mem hm, g⁻¹, inv_mem hg, fun x => ?_⟩
    have h1 := d.act_inv_act hMV hm (gv g⁻¹ x)
    rw [hgx, gv_gv_inv] at h1
    exact h1

theorem O6NatData.Lam_le (hMV : M ≤ normalizer (V : Set G)) : d.Lam hMV ≤ M :=
  fun _ hm => hm.1

theorem O6NatData.L_le_Lam (hLM : L ≤ M) (hMV : M ≤ normalizer (V : Set G)) : L ≤ d.Lam hMV :=
  fun l hl => by
  refine ⟨hLM hl, ((d.ε ⟨l, hl⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
    GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F), (d.ε ⟨l, hl⟩).2, fun x => ?_⟩
  obtain ⟨v, rfl⟩ := d.eqv.surjective x
  rw [d.act_eqv, ← d.eps_eqv hl (hMV (hLM hl)) v]

theorem O6NatData.C_le_Lam (hMV : M ≤ normalizer (V : Set G)) :
    M ⊓ centralizer (V : Set G) ≤ d.Lam hMV := fun c hc => by
  refine ⟨hc.1, 1, one_mem _, fun x => ?_⟩
  obtain ⟨v, rfl⟩ := d.eqv.surjective x
  rw [d.act_eqv, gv_one]
  refine congrArg d.eqv (Subtype.ext ?_)
  have h1 : (v : G) * c = c * (v : G) := Subgroup.mem_centralizer_iff.mp hc.2 v v.2
  show c * (v : G) * c⁻¹ = (v : G)
  rw [← h1]
  group

theorem O6NatData.Lam_conj_mem (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) {m : G} (hm : m ∈ M) {l : G} (hl : l ∈ d.Lam hMV) :
    m * l * m⁻¹ ∈ d.Lam hMV := by
  obtain ⟨hlM, g, hg, hgx⟩ := hl
  obtain ⟨g', hg', hg'x⟩ := d.act_normalizes hLM hML hMV hm hg
  refine ⟨M.mul_mem (M.mul_mem hm hlM) (M.inv_mem hm), g', hg', fun x => ?_⟩
  rw [d.act_mul hMV (M.mul_mem hm hlM) (M.inv_mem hm), d.act_mul hMV hm hlM, hgx]
  have := hg'x (d.act m⁻¹ (hMV (M.inv_mem hm)) x)
  rw [d.act_act_inv hMV hm] at this
  exact this

theorem O6NatData.Lam_normal (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) : M ≤ normalizer (d.Lam hMV : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => d.Lam_conj_mem hLM hML hMV hm hl, fun hl => ?_⟩
  have := d.Lam_conj_mem hLM hML hMV (M.inv_mem hm) hl
  simpa [mul_assoc] using this

theorem O6NatData.exists_mat (hMV : M ≤ normalizer (V : Set G)) {m : G} (hm : m ∈ d.Lam hMV) :
    ∃ g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F,
      g ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c) ∧
        ∀ (hmM : m ∈ M) (x : OW d.F), d.act m (hMV hmM) x = gv g x := by
  obtain ⟨hmM, g, hg, hgx⟩ := hm
  exact ⟨g, hg, fun _ x => hgx x⟩

noncomputable def O6NatData.matHom (hMV : M ≤ normalizer (V : Set G)) :
    ↥(d.Lam hMV) →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F where
  toFun m := Classical.choose (d.exists_mat hMV m.2)
  map_one' := by
    refine gl_ext fun x => ?_
    have h1 := (Classical.choose_spec (d.exists_mat hMV (1 : ↥(d.Lam hMV)).2)).2
      (d.Lam_le hMV (1 : ↥(d.Lam hMV)).2) x
    rw [gv_one]
    exact h1.symm.trans (d.act_one hMV x)
  map_mul' m m' := by
    refine gl_ext fun x => ?_
    have h1 := (Classical.choose_spec (d.exists_mat hMV (m * m').2)).2
      (d.Lam_le hMV (m * m').2) x
    have h2 := (Classical.choose_spec (d.exists_mat hMV m.2)).2 (d.Lam_le hMV m.2)
      (gv (Classical.choose (d.exists_mat hMV m'.2)) x)
    have h3 := (Classical.choose_spec (d.exists_mat hMV m'.2)).2 (d.Lam_le hMV m'.2) x
    rw [gv_mul, ← h2, ← h3, ← d.act_mul hMV (d.Lam_le hMV m.2) (d.Lam_le hMV m'.2) x]
    exact h1.symm

theorem O6NatData.matHom_mem (hMV : M ≤ normalizer (V : Set G)) (m : ↥(d.Lam hMV)) :
    d.matHom hMV m ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c) :=
  (Classical.choose_spec (d.exists_mat hMV m.2)).1

theorem O6NatData.act_eq_matHom (hMV : M ≤ normalizer (V : Set G)) {m : G} (hm : m ∈ d.Lam hMV)
    (hmM : m ∈ M) (x : OW d.F) : d.act m (hMV hmM) x = gv (d.matHom hMV ⟨m, hm⟩) x :=
  (Classical.choose_spec (d.exists_mat hMV hm)).2 hmM x

theorem O6NatData.eps_conj (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) {t : G} (ht : t ∈ d.Lam hMV) {l : G} (hl : l ∈ L)
    (htl : t * l * t⁻¹ ∈ L) :
    ((d.ε ⟨t * l * t⁻¹, htl⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) =
      d.matHom hMV ⟨t, ht⟩ *
        ((d.ε ⟨l, hl⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
          GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) * (d.matHom hMV ⟨t, ht⟩)⁻¹ := by
  refine gl_ext fun y => ?_
  have htM : t ∈ M := d.Lam_le hMV ht
  have htV : t ∈ normalizer (V : Set G) := hMV htM
  have hlV : l ∈ normalizer (V : Set G) := hMV (hLM hl)
  have htlV : t * l * t⁻¹ ∈ normalizer (V : Set G) := hMV (hLM htl)
  set m := d.matHom hMV ⟨t, ht⟩ with hm
  have hact : ∀ x, d.act t htV x = gv m x := fun x => d.act_eq_matHom hMV ht htM x
  have h1 := d.act_eps hl hlV htl htlV htV (gv m⁻¹ y)
  rw [hact (gv m⁻¹ y), gv_gv_inv, hact] at h1
  rw [gv_mul, gv_mul]
  exact h1.symm

theorem O6NatData.eps_comm (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) {a : G} (ha : a ∈ d.Lam hMV) {x : G} (hx : x ∈ L)
    (hxa : ⁅x, a⁆ ∈ L) :
    ((d.ε ⟨⁅x, a⁆, hxa⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) =
      ((d.ε ⟨x, hx⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
          GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) * d.matHom hMV ⟨a, ha⟩ *
        ((d.ε ⟨x, hx⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
          GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F)⁻¹ * (d.matHom hMV ⟨a, ha⟩)⁻¹ := by
  have haM : a ∈ M := d.Lam_le hMV ha
  have hxi : x⁻¹ ∈ L := L.inv_mem hx
  have hy : a * x⁻¹ * a⁻¹ ∈ L := (mem_normalizer_iff.mp (hML haM) x⁻¹).mp hxi
  have e1 : (⟨⁅x, a⁆, hxa⟩ : ↥L) = ⟨x, hx⟩ * ⟨a * x⁻¹ * a⁻¹, hy⟩ :=
    Subtype.ext (by show ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹); rw [commutatorElement_def]; group)
  have e2 := d.eps_conj hLM hML hMV ha hxi hy
  have e3 : (⟨x⁻¹, hxi⟩ : ↥L) = (⟨x, hx⟩ : ↥L)⁻¹ := rfl
  rw [e1, map_mul, Subgroup.coe_mul, e2, e3, map_inv, Subgroup.coe_inv]
  group

end ParB

end CFSG.LocalAnalysis.RankThreeUC
