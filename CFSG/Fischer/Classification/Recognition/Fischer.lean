module

public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.Milestones.CL_LIT_Fischer_3T_existence_uniqueness

public section

namespace CFSG.Fischer.Classification.Recognition

open CFSG.Blueprint.Fischer CFSG.Open

variable {G H : Type} [Group G] [Group H]

theorem pair_image_mulEquiv {D : Set G} (hP : Pair G D) (ψ : G ≃* H) : Pair H (ψ '' D) := by
  obtain ⟨hfin, ⟨e, rfl⟩, hinv, hprod, hgen⟩ := hP
  refine ⟨Finite.of_equiv G ψ.toEquiv, ⟨ψ e, ?_⟩, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (isConj_iff.mp hx).elim fun c hc => isConj_iff.mpr ⟨ψ c, by rw [← hc]; simp⟩
    · intro hy
      refine ⟨ψ.symm y, ?_, ψ.apply_symm_apply y⟩
      obtain ⟨c, hc⟩ := isConj_iff.mp hy
      exact isConj_iff.mpr ⟨ψ.symm c, ψ.injective (by simp [← hc])⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.orderOf_eq]
    exact hinv x hx
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact hprod x hx y hy
  · have h := congrArg (Subgroup.map ψ.toMonoidHom) hgen
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ ψ.surjective] at h
    simpa using h

theorem exists_class_of_mulEquiv_carrier
    {D : Set G} (hP : Pair G D) (k : Fin 3)
    (ψ : G ≃* Carrier k) :
    ∃ D₀ : Set (Carrier k), HasType k (Carrier k) D₀ ∧ LocalStructure k D₀ ∧ ψ '' D = D₀ := by
  obtain ⟨-, -, D₀, hD₀, huniq, hloc, -⟩ :=
    CFSG.Milestones.cl_lit_fischer_3t_existence_uniqueness_full k
  exact ⟨D₀, hD₀, hloc, huniq _ (pair_image_mulEquiv hP ψ)⟩

@[expose] noncomputable def centralizerEquiv (ψ : G ≃* H) (d : G) :
    Subgroup.centralizer ({d} : Set G) ≃* Subgroup.centralizer ({ψ d} : Set H) :=
  (ψ.subgroupMap _).trans (MulEquiv.subgroupCongr (map_centralizer_singleton ψ d))

theorem centralizerEquiv_apply (ψ : G ≃* H) (d : G) (x : Subgroup.centralizer ({d} : Set G)) :
    (centralizerEquiv ψ d x : H) = ψ x := rfl

section Transport

variable {A B : Type*} [Group A] [Group B]

theorem commutator_eq_top_of_mulEquiv (e : A ≃* B) (h : commutator B = ⊤) : commutator A = ⊤ := by
  rw [_root_.commutator_def] at h ⊢
  have h' := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.symm.surjective] at h'

theorem center_map_mulEquiv (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B :=
  Subgroup.map_center_eq e

theorem card_center_of_mulEquiv (e : A ≃* B) :
    Nat.card (Subgroup.center A) = Nat.card (Subgroup.center B) := by
  rw [← center_map_mulEquiv e]
  exact (Nat.card_congr ((Subgroup.center A).equivMapOfInjective _ e.injective).toEquiv)

noncomputable def quotientCenterEquiv (e : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr _ _ e (center_map_mulEquiv e)

end Transport

theorem map_center_centralizer (ψ : G ≃* H) (d : G) :
    ((Subgroup.center (Subgroup.centralizer ({ψ d} : Set H))).map
      (Subgroup.centralizer ({ψ d} : Set H)).subtype).map ψ.symm.toMonoidHom =
    (Subgroup.center (Subgroup.centralizer ({d} : Set G))).map
      (Subgroup.centralizer ({d} : Set G)).subtype := by
  rw [← center_map_mulEquiv (centralizerEquiv ψ d), Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [centralizerEquiv_apply]

theorem centralizer_perfect_center
    {D : Set G} (hP : Pair G D) {k : Fin 3} (hk : k.val ≠ 2)
    (ψ : G ≃* Carrier k) {d : G} (hd : d ∈ D) :
    commutator (Subgroup.centralizer ({d} : Set G)) = ⊤ ∧
      (Subgroup.center (Subgroup.centralizer ({d} : Set G))).map
        (Subgroup.centralizer ({d} : Set G)).subtype = Subgroup.zpowers d ∧
      Nat.card (Subgroup.center (Subgroup.centralizer ({d} : Set G))) = 2 := by
  obtain ⟨D₀, -, hloc, himg⟩ := exists_class_of_mulEquiv_carrier hP k ψ
  have hd₀ : ψ d ∈ D₀ := himg ▸ ⟨d, hd, rfl⟩
  have h := hloc (ψ d) hd₀
  obtain ⟨hcomm, hcen, hcard⟩ : commutator (Subgroup.centralizer ({ψ d} : Set (Carrier k))) = ⊤ ∧
      (Subgroup.center (Subgroup.centralizer ({ψ d} : Set (Carrier k)))).map
        (Subgroup.centralizer ({ψ d} : Set (Carrier k))).subtype = Subgroup.zpowers (ψ d) ∧
      Nat.card (Subgroup.center (Subgroup.centralizer ({ψ d} : Set (Carrier k)))) = 2 := by
    rcases k with ⟨_ | _ | _ | k, hk'⟩
    · obtain ⟨h1, h2, h3, -⟩ := h.1 rfl
      exact ⟨h1, h2, h3⟩
    · obtain ⟨h1, h2, h3, -⟩ := h.2.1 rfl
      exact ⟨h1, h2, h3⟩
    · exact absurd rfl hk
    · omega
  refine ⟨commutator_eq_top_of_mulEquiv (centralizerEquiv ψ d) hcomm, ?_, ?_⟩
  · rw [← map_center_centralizer ψ d, hcen, MonoidHom.map_zpowers]
    simp
  · rw [card_center_of_mulEquiv (centralizerEquiv ψ d), hcard]

theorem localStructure_at
    {D : Set G} (hP : Pair G D) {k : Fin 3} (ψ : G ≃* Carrier k) {d : G}
    (hd : d ∈ D) : ∃ D₀ : Set (Carrier k), LocalStructure k D₀ ∧ ψ d ∈ D₀ := by
  obtain ⟨D₀, -, hloc, himg⟩ := exists_class_of_mulEquiv_carrier hP k ψ
  exact ⟨D₀, hloc, himg ▸ ⟨d, hd, rfl⟩⟩

theorem centralizer_quotient_of_fi22
    {D : Set G} (hP : Pair G D) {k : Fin 3} (hk : k.val = 0)
    (ψ : G ≃* Carrier k) {d : G}
    (hd : d ∈ D) : ∃ H : Matrix (Fin 6) (Fin 6) K, IsNondegenerateHermitian H ∧
      Nonempty (Subgroup.centralizer ({d} : Set G) ⧸
        Subgroup.center (Subgroup.centralizer ({d} : Set G)) ≃* PSU H) := by
  obtain ⟨D₀, hloc, hd₀⟩ := localStructure_at hP ψ hd
  obtain ⟨-, -, -, H, hH, ⟨e⟩⟩ := (hloc (ψ d) hd₀).1 hk
  exact ⟨H, hH, ⟨(quotientCenterEquiv (centralizerEquiv ψ d)).trans e⟩⟩

theorem centralizer_quotient_of_fi23
    {D : Set G} (hP : Pair G D) {k : Fin 3} (hk : k.val = 1)
    (ψ : G ≃* Carrier k) {d : G} (hd : d ∈ D) :
    Nonempty (Subgroup.centralizer ({d} : Set G) ⧸
      Subgroup.center (Subgroup.centralizer ({d} : Set G)) ≃*
        CFSG.Blueprint.NativeSporadic.Fi22) := by
  obtain ⟨D₀, hloc, hd₀⟩ := localStructure_at hP ψ hd
  obtain ⟨-, -, -, ⟨e⟩⟩ := (hloc (ψ d) hd₀).2.1 hk
  exact ⟨(quotientCenterEquiv (centralizerEquiv ψ d)).trans e⟩

theorem centralizer_of_fi24
    {D : Set G} (hP : Pair G D) {k : Fin 3} (hk : k.val = 2)
    (ψ : G ≃* Carrier k) {d : G} (hd : d ∈ D) :
    ∃ L : Subgroup G, Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.Fi23) ∧
      Subgroup.centralizer ({d} : Set G) = Subgroup.zpowers d ⊔ L ∧
      Subgroup.zpowers d ⊓ L = ⊥ ∧ Subgroup.zpowers d ≤ Subgroup.centralizer (L : Set G) := by
  obtain ⟨D₀, hloc, hd₀⟩ := localStructure_at hP ψ hd
  obtain ⟨L', ⟨e⟩, hC, hinf, hcen⟩ := (hloc (ψ d) hd₀).2.2 hk
  have hzp : (Subgroup.zpowers (ψ d)).map ψ.symm.toMonoidHom = Subgroup.zpowers d := by
    rw [MonoidHom.map_zpowers]
    simp
  refine ⟨L'.map ψ.symm.toMonoidHom,
    ⟨(L'.equivMapOfInjective _ ψ.symm.injective).symm.trans e⟩, ?_, ?_, ?_⟩
  · have h := congrArg (Subgroup.map ψ.symm.toMonoidHom) hC
    rwa [Subgroup.map_sup, hzp, map_centralizer_singleton ψ.symm, ψ.symm_apply_apply] at h
  · rw [← hzp, ← Subgroup.map_inf_eq _ _ ψ.symm.toMonoidHom ψ.symm.injective, hinf,
      Subgroup.map_bot]
  · rw [← hzp]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    have := (Subgroup.mem_centralizer_iff.mp (hcen hy)) z hz
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]

end CFSG.Fischer.Classification.Recognition
