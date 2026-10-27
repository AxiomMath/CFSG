module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4CoplPoint
public import CFSG.ClassicalGroups.Alternating.I4SpChain
public import CFSG.ClassicalGroups.Alternating.I4SpLeviHom

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem apply_eq_self_of_map_eq {u : V ≃ₗ[K] V} (hu : u * u = 1) {P : Submodule K V}
    (hP : finrank K P = 1) (hmap : P.map (u : V →ₗ[K] V) = P) : ∀ v ∈ P, u v = v := by
  obtain ⟨p, hp0, rfl⟩ := exists_ne_zero_span_eq_of_finrank_eq_one hP
  have hup : u p ∈ Submodule.span K {p} := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self p)
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hup
  have hu2 : u (u p) = p := by
    have h := congrArg (fun g : V ≃ₗ[K] V => g p) hu
    simpa using h
  have hss : s * s = 1 := by
    have h1 : (s * s) • p = (1 : K) • p := by
      calc (s * s) • p = s • (s • p) := mul_smul _ _ _
        _ = s • u p := by rw [hs]
        _ = u (s • p) := (map_smul u s p).symm
        _ = u (u p) := by rw [hs]
        _ = (1 : K) • p := by rw [hu2, one_smul]
    exact smul_left_injective K hp0 h1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs1 : s = 1 := by
    have h3 : (s - 1) * (s - 1) = 0 := by linear_combination hss - s * h2 + h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  intro v hv
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, ← hs, hs1, one_smul]

theorem map_eq_of_forall_apply_eq {u : V ≃ₗ[K] V} {S : Submodule K V} (h : ∀ v ∈ S, u v = v) :
    S.map (u : V →ₗ[K] V) = S := by
  refine le_antisymm ?_ fun y hy => ⟨y, hy, h y hy⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [LinearEquiv.coe_coe, h x hx]
  exact hx

@[expose] noncomputable def restrictHom {L : Type*} [Group L] (ψ : L →* (V ≃ₗ[K] V))
    (A : Submodule K V) (hA : ∀ g, A.map (ψ g : V →ₗ[K] V) = A) : L →* (A ≃ₗ[K] A) where
  toFun g := LinearEquiv.ofSubmodules (ψ g) A A (hA g)
  map_one' := LinearEquiv.ext fun x => Subtype.ext (by simp)
  map_mul' g h := LinearEquiv.ext fun x => Subtype.ext (by simp)

theorem coe_restrictHom_apply {L : Type*} [Group L] (ψ : L →* (V ≃ₗ[K] V)) (A : Submodule K V)
    (hA : ∀ g, A.map (ψ g : V →ₗ[K] V) = A) (g : L) (x : A) :
    ((restrictHom ψ A hA g x : A) : V) = ψ g x := by
  simp [restrictHom]

section Plane

variable {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}
  (hs : I4Setting hBN Qf ρ) (hcopl : ∀ π, IsPlane BN π → Copl (planeFamily hBN ρ π))

include hs hcopl

theorem planePt_eq_of_adj {π π' : Submodule K N} (hπ : IsPlane BN π) (hπ' : IsPlane BN π')
    (hfin : finrank K ↥(π ⊓ π') = 2) {a : N} (ha : a ∈ π ⊓ π') (ha0 : a ≠ 0) :
    planePt hBN ρ π a = planePt hBN ρ π' a := by
  have hℓ : IsLine BN (π ⊓ π') := ⟨fun x hx y hy => hπ.1 x hx.1 y hy.1, hfin⟩
  have hℓπ : π ⊓ π' ≤ π := inf_le_left
  have hℓπ' : π ⊓ π' ≤ π' := inf_le_right
  obtain ⟨H, hH⟩ := exists_isLeviSpace hBN hs.nondegN hℓ
  obtain ⟨n, hn, hn0, hπeq⟩ := exists_isPlane_eq_sup hBN hs.nondegN hH hπ hℓπ
  obtain ⟨b, hb, hab, -⟩ := hℓ.exists_pair_of_mem ha ha0
  have hT : Tsp hBN n 1 ∈ leviGroup BN H := Tsp_mem_leviGroup hBN hn 1
  have hTfix : ∀ x ∈ π, (Tsp hBN n 1).app x = x := fun x hx =>
    app_eq_of_mem_leviRoot hBN hH hn ((mem_leviRoot_iff hBN).mpr ⟨1, rfl⟩) (hπeq ▸ hx)
  have hTmap : π.map (Tsp hBN n 1).lin = π := map_lin_eq_of_fixed _ hTfix
  have hTinv : ρ (Tsp hBN n 1) * ρ (Tsp hBN n 1) = 1 := by
    rw [← map_mul, Tsp_mul_self, map_one]
  have hPT : ∀ c : N, c ∈ π ⊓ π' → c ≠ 0 → ∀ v ∈ planePt hBN ρ π c, ρ (Tsp hBN n 1) v = v := by
    intro c hc hc0
    have h1 := planePt_map hBN ρ (Tsp hBN n 1) π c
    rw [hTmap, hTfix c hc.1] at h1
    exact apply_eq_self_of_map_eq hTinv (finrank_planePt hs hcopl hπ hc.1 hc0) h1.symm
  have hAT : ∀ v ∈ famSpace hBN ρ (π ⊓ π'), ρ (Tsp hBN n 1) v = v := by
    have hb0 : b ≠ 0 := by simpa using hab.ne_zero (1 : Fin 2)
    intro v hv
    rw [famSpace_eq_sup_planePt hs hcopl hπ hℓ hℓπ ha hb hab, Submodule.mem_sup] at hv
    obtain ⟨x, hx, y, hy, rfl⟩ := hv
    rw [map_add, hPT a ha ha0 x hx, hPT b hb hb0 y hy]
  have hAinv : ∀ g : leviGroup BN H,
      (famSpace hBN ρ (π ⊓ π')).map ((ρ.comp (leviGroup BN H).subtype) g : V →ₗ[K] V) =
        famSpace hBN ρ (π ⊓ π') := by
    intro g
    have h1 := famSpace_map hBN ρ g.1 (π ⊓ π')
    rwa [map_lin_eq_of_fixed g.1 fun x hx => leviGroup_fix_line hH g.2 hx, eq_comm] at h1
  set φ := restrictHom (ρ.comp (leviGroup BN H).subtype) (famSpace hBN ρ (π ⊓ π')) hAinv
    with hφ
  have hφT : φ ⟨Tsp hBN n 1, hT⟩ = 1 := by
    refine LinearEquiv.ext fun x => Subtype.ext ?_
    rw [hφ, coe_restrictHom_apply]
    exact hAT x x.2
  have hφ1 : φ = 1 := by
    rcases levi_hom_eq_one_or_injective hBN hs.nondegN hH (by simpa using hs.card) hs.dimN φ with
      h | hinj
    · exact h
    · exfalso
      have h1 : (⟨Tsp hBN n 1, hT⟩ : leviGroup BN H) = 1 := hinj (by rw [hφT, map_one])
      have h2 : Tsp hBN n 1 = 1 := congrArg Subtype.val h1
      rcases (Tsp_eq_one_iff hBN hs.nondegN n 1).mp h2 with h | h
      · exact hn0 h
      · exact one_ne_zero h
  obtain ⟨g, hg, hgπ⟩ := exists_mem_leviGroup_map_eq hBN hH hs.nondegN hπ hℓπ hπ' hℓπ'
  have hga : g.app a = a := hg a (hH.2.1 ha)
  have hφg : φ ⟨g, hg⟩ = 1 := by rw [hφ1, MonoidHom.one_apply]
  have hgA : ∀ v ∈ famSpace hBN ρ (π ⊓ π'), ρ g v = v := by
    intro v hv
    have := congrArg (fun f : (famSpace hBN ρ (π ⊓ π')) ≃ₗ[K] (famSpace hBN ρ (π ⊓ π')) =>
      ((f ⟨v, hv⟩ : famSpace hBN ρ (π ⊓ π')) : V)) hφg
    simpa [hφ, coe_restrictHom_apply] using this
  have h1 := planePt_map hBN ρ g π a
  rw [hgπ, hga] at h1
  rw [h1]
  exact (map_eq_of_forall_apply_eq fun v hv => hgA v (planePt_le hBN ρ hℓ ha hℓπ hv)).symm

theorem planePt_eq {π π' : Submodule K N} (hπ : IsPlane BN π) (hπ' : IsPlane BN π') {a : N}
    (ha : a ∈ π ⊓ π') (ha0 : a ≠ 0) : planePt hBN ρ π a = planePt hBN ρ π' a := by
  have hchain := exists_planeAdj_chain_through hBN hπ hπ' ha
  suffices key : ∀ σ, Relation.ReflTransGen
      (fun σ σ' => PlaneAdj BN (π ⊓ π') σ σ' ∧ a ∈ σ ∧ a ∈ σ') π σ →
      planePt hBN ρ π a = planePt hBN ρ σ a from key π' hchain
  intro σ hσ
  induction hσ with
  | refl => rfl
  | tail _ hstep ih =>
    exact ih.trans (planePt_eq_of_adj hs hcopl hstep.1.1 hstep.1.2.1 hstep.1.2.2.1
      ⟨hstep.2.1, hstep.2.2⟩ ha0)

end Plane

@[expose] noncomputable def pt (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) (a : N) :
    Submodule K V :=
  planePt hBN ρ ⊤ a

theorem pt_le_famSpace (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) {ℓ : Submodule K N}
    (hℓ : IsLine BN ℓ) {a : N} (ha : a ∈ ℓ) : pt hBN ρ a ≤ famSpace hBN ρ ℓ :=
  planePt_le hBN ρ hℓ ha le_top

theorem pt_smul (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) {c : K} (hc : c ≠ 0) (a : N) :
    pt hBN ρ (c • a) = pt hBN ρ a :=
  planePt_smul hBN ρ ⊤ hc a

theorem Gsp.map_lin_top (g : Gsp BN) : (⊤ : Submodule K N).map g.lin = ⊤ :=
  eq_top_iff.mpr fun y _ => ⟨g⁻¹.app y, trivial, by simp [Gsp.lin_apply, Gsp.app_app_inv]⟩

theorem pt_map (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) (g : Gsp BN) (a : N) :
    pt hBN ρ (g.app a) = (pt hBN ρ a).map (ρ g : V →ₗ[K] V) := by
  have h := planePt_map hBN ρ g ⊤ a
  rwa [Gsp.map_lin_top] at h

section Point

variable {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}
  (hs : I4Setting hBN Qf ρ) (hcopl : ∀ π, IsPlane BN π → Copl (planeFamily hBN ρ π))

omit hcopl in
include hs in
theorem exists_isPlane_mem {a : N} (ha0 : a ≠ 0) : ∃ π, IsPlane BN π ∧ a ∈ π := by
  obtain ⟨ℓ, hℓ, haℓ⟩ := exists_isLine_of_ne_zero hBN hs.nondegN hs.dimN ha0
  obtain ⟨π, -, hπ, -, hℓπ, -, -⟩ := exists_two_planes_through hBN hs.nondegN hs.dimN hℓ
  exact ⟨π, hπ, hℓπ haℓ⟩

include hs hcopl

theorem pt_eq_planePt {π : Submodule K N} (hπ : IsPlane BN π) {a : N} (ha : a ∈ π)
    (ha0 : a ≠ 0) : pt hBN ρ a = planePt hBN ρ π a := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_planePt_iff]
    intro ℓ hℓ haℓ _
    exact pt_le_famSpace hBN ρ hℓ haℓ hx
  · unfold pt
    rw [mem_planePt_iff]
    intro ℓ hℓ haℓ _
    obtain ⟨π₁, -, hπ₁, -, hℓπ₁, -, -⟩ := exists_two_planes_through hBN hs.nondegN hs.dimN hℓ
    rw [planePt_eq hs hcopl hπ hπ₁ ⟨ha, hℓπ₁ haℓ⟩ ha0] at hx
    exact planePt_le hBN ρ hℓ haℓ hℓπ₁ hx

theorem finrank_pt {a : N} (ha0 : a ≠ 0) : finrank K (pt hBN ρ a) = 1 := by
  obtain ⟨π, hπ, haπ⟩ := exists_isPlane_mem hs ha0
  rw [pt_eq_planePt hs hcopl hπ haπ ha0]
  exact finrank_planePt hs hcopl hπ haπ ha0

theorem famSpace_eq_sup_pt {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) {a b : N} (ha : a ∈ ℓ)
    (hb : b ∈ ℓ) (hab : LinearIndependent K ![a, b]) :
    famSpace hBN ρ ℓ = pt hBN ρ a ⊔ pt hBN ρ b := by
  obtain ⟨π, -, hπ, -, hℓπ, -, -⟩ := exists_two_planes_through hBN hs.nondegN hs.dimN hℓ
  have ha0 : a ≠ 0 := by simpa using hab.ne_zero (0 : Fin 2)
  have hb0 : b ≠ 0 := by simpa using hab.ne_zero (1 : Fin 2)
  rw [pt_eq_planePt hs hcopl hπ (hℓπ ha) ha0, pt_eq_planePt hs hcopl hπ (hℓπ hb) hb0]
  exact famSpace_eq_sup_planePt hs hcopl hπ hℓ hℓπ ha hb hab

theorem iSup_pt_eq_top : (⨆ (a : N) (_ : a ≠ 0), pt hBN ρ a) = ⊤ := by
  set S : Submodule K V := ⨆ (a : N) (_ : a ≠ 0), pt hBN ρ a with hSdef
  let M : Subgroup (Gsp BN) :=
    { carrier := {g | ∀ v, ρ g v - v ∈ S}
      one_mem' := fun v => by simp
      mul_mem' := fun {g h} hg hh v => by
        have := S.add_mem (hg (ρ h v)) (hh v)
        simpa [map_mul] using this
      inv_mem' := fun {g} hg v => by
        have := S.neg_mem (hg (ρ g⁻¹ v))
        simpa [map_inv] using this }
  have hMline : ∀ a c : N, BN a c = 0 → LinearIndependent K ![a, c] → lineElt hBN a c ∈ M := by
    intro a c hac hind v
    have hℓ := isLine_span_pair hBN hac hind
    have hg : lineElt hBN a c ∈ planeGroup hBN (Submodule.span K {a, c}) :=
      lineElt_mem_planeGroup hBN (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))
    have hmem : ρ (lineElt hBN a c) v - v ∈ movedSpace (ρ (lineElt hBN a c)) :=
      sub_mem_movedSpace _ v
    rw [movedSpace_eq_famSpace_of_isLine hs hcopl hℓ hg (lineElt_ne_one hBN hs.nondegN hac hind),
      famSpace_eq_sup_pt hs hcopl hℓ (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp)) hind] at hmem
    have ha0 : a ≠ 0 := by simpa using hind.ne_zero (0 : Fin 2)
    have hc0 : c ≠ 0 := by simpa using hind.ne_zero (1 : Fin 2)
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hmem
    rw [← hxy]
    exact S.add_mem ((le_iSup₂ (f := fun (a : N) (_ : a ≠ 0) => pt hBN ρ a) a ha0) hx)
      ((le_iSup₂ (f := fun (a : N) (_ : a ≠ 0) => pt hBN ρ a) c hc0) hy)
  have hNpos : 0 < finrank K N := by have := hs.dimN; omega
  haveI : Nontrivial N := Module.nontrivial_of_finrank_pos hNpos
  obtain ⟨a₁, ha₁⟩ := exists_ne (0 : N)
  obtain ⟨ℓ, hℓ, -⟩ := exists_isLine_of_ne_zero hBN hs.nondegN hs.dimN ha₁
  obtain ⟨a₀, c₀, hac₀, hind₀, -⟩ := hℓ.exists_pair
  haveI : IsSimpleGroup (Gsp BN) :=
    isSimpleGroup_Gsp hs.card hBN hs.nondegN (by have := hs.dimN; omega)
  have hx1 : lineElt hBN a₀ c₀ ≠ 1 := lineElt_ne_one hBN hs.nondegN hac₀ hind₀
  have htop : Subgroup.normalClosure {lineElt hBN a₀ c₀} = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.normalClosure {lineElt hBN a₀ c₀}) with
      h | h
    · exfalso
      apply hx1
      have : lineElt hBN a₀ c₀ ∈ Subgroup.normalClosure {lineElt hBN a₀ c₀} :=
        Subgroup.subset_normalClosure rfl
      rw [h] at this
      exact (Subgroup.mem_bot.mp this)
    · exact h
  have hle : Subgroup.normalClosure {lineElt hBN a₀ c₀} ≤ M := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    obtain ⟨x', hx', hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    rw [Set.mem_singleton_iff.mp hx'] at hc
    rw [← hc, SetLike.mem_coe, conj_lineElt hBN c a₀ c₀]
    refine hMline _ _ (by rw [Gsp.form_app]; exact hac₀) ?_
    have h := hind₀.map' c.lin (LinearMap.ker_eq_bot.mpr (Gsp.lin_injective c))
    convert h using 1
    ext i
    fin_cases i <;> rfl
  have hMtop : ∀ g : Gsp BN, g ∈ M := fun g => hle (htop ▸ Subgroup.mem_top g)
  have hcomm : commutatorSpace ρ.range ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, ⟨g, rfl⟩, v, rfl⟩
    exact hMtop g v
  rw [hs.gen] at hcomm
  exact top_le_iff.mp hcomm

end Point

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
