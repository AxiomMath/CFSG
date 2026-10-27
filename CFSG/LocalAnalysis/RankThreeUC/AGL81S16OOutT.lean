module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOut
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OSemi
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OAct

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus)

variable {G : Type} [Group G] [Finite G] {n p : ℕ} {M L V : Subgroup G}

namespace OutT

theorem act_mul (d : O6NatData G n L V) (hMV : M ≤ normalizer (V : Set G)) {m m' : G} (hm : m ∈ M)
    (hm' : m' ∈ M) (hmm' : m * m' ∈ M) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) :
    d.act (m * m') (hMV hmm') x = d.act m (hMV hm) (d.act m' (hMV hm') x) := by
  have h : d.rho M hMV ⟨m * m', hmm'⟩ = d.rho M hMV ⟨m, hm⟩ * d.rho M hMV ⟨m', hm'⟩ := by
    rw [← map_mul]
    rfl
  have h2 := congrArg (fun f => f x) h
  simp only [Equiv.Perm.mul_apply] at h2
  rw [O6NatData.rho_apply, O6NatData.rho_apply, O6NatData.rho_apply] at h2
  exact h2

theorem act_eq_of_mem_centralizer (d : O6NatData G n L V) (hMV : M ≤ normalizer (V : Set G))
    {m : G} (hm : m ∈ M) (hc : m ∈ centralizer (V : Set G))
    (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) : d.act m (hMV hm) x = x := by
  obtain ⟨v, rfl⟩ := d.eqv.surjective x
  rw [d.act_eqv]
  refine congrArg d.eqv (Subtype.ext ?_)
  show m * (v : G) * m⁻¹ = (v : G)
  have := Subgroup.mem_centralizer_iff.mp hc (v : G) v.2
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm


@[expose] def LinAct (d : O6NatData G n L V) (hMV : M ≤ normalizer (V : Set G)) (A : Subgroup G)
    (hAM : A ≤ M) : Prop :=
  ∀ (a : G) (ha : a ∈ A) (c : d.F) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F),
    d.act a (hMV (hAM ha)) (c • x) = c • d.act a (hMV (hAM ha)) x

@[expose] noncomputable def linEquiv (d : O6NatData G n L V) (hMV : M ≤ normalizer (V : Set G))
    {m : G} (hm : m ∈ M)
    (hlin : ∀ (c : d.F) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F),
      d.act m (hMV hm) (c • x) = c • d.act m (hMV hm) x) :
    (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) ≃ₗ[d.F]
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) where
  toFun := d.act m (hMV hm)
  invFun := d.act m⁻¹ (hMV (M.inv_mem hm))
  left_inv := d.act_inv_act hMV hm
  right_inv := d.act_act_inv hMV hm
  map_add' := d.act_add m (hMV hm)
  map_smul' c x := by simpa using hlin c x

@[expose] noncomputable def linHom (d : O6NatData G n L V) (hMV : M ≤ normalizer (V : Set G))
    {A : Subgroup G} (hAM : A ≤ M) (hL : LinAct d hMV A hAM) :
    ↥A →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F :=
  MonoidHom.mk' (fun a => (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F).symm
    (linEquiv d hMV (hAM a.2) (hL a.1 a.2))) (fun a b => by
      apply (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F).injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply]
      refine LinearEquiv.ext fun x => ?_
      show d.act (a * b).1 (hMV (hAM (a * b).2)) x =
        d.act a.1 (hMV (hAM a.2)) (d.act b.1 (hMV (hAM b.2)) x)
      exact act_mul d hMV (hAM a.2) (hAM b.2) (hAM (a * b).2) x)

theorem linHom_apply (d : O6NatData G n L V) (hMV : M ≤ normalizer (V : Set G)) {A : Subgroup G}
    (hAM : A ≤ M) (hL : LinAct d hMV A hAM) (a : ↥A)
    (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) :
    ((linHom d hMV hAM hL a : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) *ᵥ x =
      d.act a.1 (hMV (hAM a.2)) x := by
  show (((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F).symm
    (linEquiv d hMV (hAM a.2) (hL a.1 a.2)) : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) *ᵥ x = _
  rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
  rfl


theorem act_involution (d : O6NatData G n L V) (hMV : M ≤ normalizer (V : Set G)) {a : G}
    (ha : a ∈ M) (haa : a * a = 1) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) :
    d.act a (hMV ha) (d.act a (hMV ha) x) = x := by
  have h : d.rho M hMV ⟨a, ha⟩ * d.rho M hMV ⟨a, ha⟩ = 1 := by
    rw [← map_mul]
    have : (⟨a, ha⟩ : ↥M) * ⟨a, ha⟩ = 1 := Subtype.ext haa
    rw [this, map_one]
  have h' := congrArg (fun f => f x) h
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h'
  exact h'

theorem act_smul_of_involution (d : O6NatData G n L V) (hn : 1 ≤ n) (hLM : L ≤ M)
    (hML : M ≤ normalizer (L : Set G)) (hMV : M ≤ normalizer (V : Set G)) {a : G} (ha : a ∈ M)
    (haa : a * a = 1) (c : d.F) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) :
    d.act a (hMV ha) (c • x) = c • d.act a (hMV ha) x := by
  haveI := d.charP hn
  obtain ⟨θ, hθ⟩ := d.act_semilinear hn hLM hML hMV ha
  by_cases hθid : θ = RingHom.id d.F
  · rw [hθ c x, hθid]
    rfl
  · exfalso
    exact no_semilinear_involution d.irred (d.actAddEquiv hMV ha) θ hθid hθ
      (fun x' => act_involution d hMV ha haa x')
      (fun g hg => d.act_normalizes hLM hML hMV ha hg)

end OutT

theorem O6NatData.outer_rank (d : O6NatData G n L V) (hn : 1 ≤ n) (hLM : L ≤ M)
    (hML : M ≤ normalizer (L : Set G)) (hMV : M ≤ normalizer (V : Set G)) {A : Subgroup G}
    (hAM : A ≤ M) (hA : IsElemAbelian 2 A) (hAL : ¬ A ≤ L ⊔ (M ⊓ centralizer (V : Set G))) :
    (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A ≤ 2 ^ (3 * n + 1) := by
  haveI := d.charP hn
  have hsq : ∀ {a : G}, a ∈ A → a * a = 1 := fun {a} ha => by
    rw [← pow_two]
    exact hA.2 a ha
  haveI := hA.1
  have hL : OutT.LinAct d hMV A hAM := fun a ha c x =>
    OutT.act_smul_of_involution d hn hLM hML hMV (hAM ha) (hsq ha) c x
  set lin := OutT.linHom d hMV hAM hL with hlin
  have hspec : ∀ (a : ↥A) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F),
      ((lin a : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) *ᵥ x =
        d.act a.1 (hMV (hAM a.2)) x := OutT.linHom_apply d hMV hAM hL
  set E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) := lin.range with hE
  have hE2 : ∀ g ∈ E, g * g = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hsq a.2)
    rw [this, map_one]
  have hEab : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    have : a * b = b * a := mul_comm' a b
    rw [this]
  have hEN : ∀ g ∈ E, ∀ h ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c),
      g * h * g⁻¹ ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c) := by
    rintro _ ⟨a, rfl⟩ h hh
    obtain ⟨h', hh', hx⟩ := d.act_normalizes hLM hML hMV (hAM a.2) hh
    have : lin a * h * (lin a)⁻¹ = h' := by
      apply gl_ext
      intro x
      show gv (lin a * h * (lin a)⁻¹) x = gv h' x
      rw [gv_mul, gv_mul]
      have e1 : gv (lin a) (gv h (gv (lin a)⁻¹ x)) =
          d.act a.1 (hMV (hAM a.2)) (gv h (gv (lin a)⁻¹ x)) := hspec a _
      have e2 : gv (lin a) (gv (lin a)⁻¹ x) = d.act a.1 (hMV (hAM a.2)) (gv (lin a)⁻¹ x) :=
        hspec a _
      rw [e1, hx, ← e2, gv_gv_inv]
    rw [this]
    exact hh'
  have hEnot : ¬ E ≤ StatedOmega (StatedQuadMinus 3 d.F d.b d.c) := by
    intro hle
    obtain ⟨a, haA, haLC⟩ := SetLike.not_le_iff_exists.mp hAL
    have hgΩ : lin ⟨a, haA⟩ ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c) :=
      hle ⟨⟨a, haA⟩, rfl⟩
    obtain ⟨l, hl⟩ := d.ε_surj ⟨_, hgΩ⟩
    have hlL : (l : G) ∈ L := l.2
    have hlV : (l : G) ∈ normalizer (V : Set G) := hMV (hLM hlL)
    have hlM : (l : G) ∈ M := hLM hlL
    have haM : a ∈ M := hAM haA
    have hgl : ((d.ε ⟨(l : G), hlL⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) = lin ⟨a, haA⟩ := congrArg Subtype.val hl
    have hact : ∀ x, d.act (l : G) hlV x = d.act a (hMV haM) x := by
      intro x
      obtain ⟨v, rfl⟩ := d.eqv.surjective x
      rw [d.act_eqv, ← d.eps_eqv hlL hlV v, hgl]
      exact hspec ⟨a, haA⟩ _
    have hm : a⁻¹ * (l : G) ∈ M := M.mul_mem (M.inv_mem haM) hlM
    have htriv : ∀ x, d.act (a⁻¹ * (l : G)) (hMV hm) x = x := by
      intro x
      rw [OutT.act_mul d hMV (M.inv_mem haM) hlM hm, hact x]
      exact d.act_inv_act hMV haM x
    have hcent := d.mem_centralizer_of_act_eq hMV hm htriv
    apply haLC
    have : a = (l : G) * (a⁻¹ * (l : G))⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem_sup hlL (Subgroup.inv_mem _ ⟨hm, hcent⟩)
  have hcard := outer_rank_linear d.irred d.card_F hn E hE2 hEab hEN hEnot
  have hker : lin.ker = (A ⊓ (M ⊓ centralizer (V : Set G))).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have htriv : ∀ x, d.act a.1 (hMV (hAM a.2)) x = x := by
        intro x
        rw [← hspec a x, h1]
        simp
      exact ⟨a.2, hAM a.2, d.mem_centralizer_of_act_eq hMV (hAM a.2) htriv⟩
    · rintro ⟨-, -, hc⟩
      apply gl_ext
      intro x
      show ((lin a : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) *ᵥ x =
        (((1 : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F)) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) *ᵥ x
      rw [hspec a x, OutT.act_eq_of_mem_centralizer d hMV (hAM a.2) hc x]
      simp
  calc (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A
      = ((A ⊓ (M ⊓ centralizer (V : Set G))).subgroupOf A).index := rfl
    _ = lin.ker.index := by rw [hker]
    _ = Nat.card ↥lin.range := Subgroup.index_ker lin
    _ ≤ 2 ^ (3 * n + 1) := hcard

end CFSG.LocalAnalysis.RankThreeUC
