module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace SuzukiAut

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Matrix LinearAlgebra.Projectivization

variable (m : ℕ)

noncomputable abbrev tits : BinaryGaloisField (2 * m + 1) ≃+* BinaryGaloisField (2 * m + 1) :=
  iterateFrobeniusEquiv (BinaryGaloisField (2 * m + 1)) 2 (m + 1)

theorem tits_apply (x : BinaryGaloisField (2 * m + 1)) : tits m x = x ^ (2 ^ (m + 1)) :=
  iterateFrobeniusEquiv_def _ 2 (m + 1) x

theorem tits_tits (x : BinaryGaloisField (2 * m + 1)) : tits m (tits m x) = x ^ 2 :=
  External.binaryGaloisField_tits_formula_sq m (tits m) (tits_apply m) x

@[expose] noncomputable def root (a b : BinaryGaloisField (2 * m + 1)) : SuzukiMatrixGroup m :=
  ⟨SuzukiRootGL m a b, Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)⟩

@[expose] noncomputable def torus (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    SuzukiMatrixGroup m :=
  ⟨SuzukiTorusGL m x, Subgroup.subset_closure (Or.inr (Or.inl ⟨x, rfl⟩))⟩

@[expose] noncomputable def weyl : SuzukiMatrixGroup m :=
  ⟨SuzukiWeylGL m, Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩

@[expose] noncomputable def rootSub : Subgroup (SuzukiMatrixGroup m) :=
  (Subgroup.closure {A | ∃ a b : BinaryGaloisField (2 * m + 1), A = SuzukiRootGL m a b}).subgroupOf
    (SuzukiMatrixGroup m)

@[expose] noncomputable def torusSub : Subgroup (SuzukiMatrixGroup m) :=
  (Subgroup.closure {A | ∃ x : (BinaryGaloisField (2 * m + 1))ˣ, A = SuzukiTorusGL m x}).subgroupOf
    (SuzukiMatrixGroup m)

theorem root_mem (a b : BinaryGaloisField (2 * m + 1)) : root m a b ∈ rootSub m := by
  rw [rootSub, Subgroup.mem_subgroupOf]
  exact Subgroup.subset_closure ⟨a, b, rfl⟩

theorem torus_mem (x : (BinaryGaloisField (2 * m + 1))ˣ) : torus m x ∈ torusSub m := by
  rw [torusSub, Subgroup.mem_subgroupOf]
  exact Subgroup.subset_closure ⟨x, rfl⟩

theorem mem_rootSub {g : SuzukiMatrixGroup m} :
    g ∈ rootSub m ↔ ∃ a b : BinaryGaloisField (2 * m + 1), g = root m a b := by
  rw [rootSub, Subgroup.mem_subgroupOf,
    External.suzukiRootGL_mem_closure_iff m (tits m) (tits_tits m) (tits_apply m)]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, Subtype.ext h⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, rfl⟩

theorem root_mul (hm : 0 < m) (a b a' b' : BinaryGaloisField (2 * m + 1)) :
    root m a b * root m a' b' = root m (a + a') (b + b' + a * tits m a') := by
  rcases External.huppert_blackburn_XI_3_1 m hm (tits m) (tits_tits m) with
    ⟨_, _, _, _, _, _, _, _, hroot_mul, _⟩
  exact Subtype.ext (hroot_mul a b a' b')

theorem root_injective {a b a' b' : BinaryGaloisField (2 * m + 1)}
    (h : root m a b = root m a' b') : a = a' ∧ b = b' := by
  have h' := congrArg (fun g : SuzukiMatrixGroup m =>
    ((g : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
      Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)))) h
  have h01 := congrFun (congrFun h' 0) 1
  have h02 := congrFun (congrFun h' 0) 2
  simp only [root, SuzukiRootGL, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    SuzukiRootMatrix] at h01 h02
  exact ⟨by simpa using h01, by simpa using h02⟩

theorem root_zero_zero : root m 0 0 = 1 :=
  Subtype.ext (External.suzukiRootGL_zero_zero m)

theorem torus_conj_root (a b : BinaryGaloisField (2 * m + 1))
    (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    torus m x * root m a b * (torus m x)⁻¹ =
      root m ((x : BinaryGaloisField (2 * m + 1)) * a)
        ((x : BinaryGaloisField (2 * m + 1)) * tits m (x : BinaryGaloisField (2 * m + 1)) * b) :=
  Subtype.ext (External.suzukiTorusGL_conj_root m (tits m) (tits_tits m) (tits_apply m) a b x)

theorem mem_torusSub (hm : 0 < m) {g : SuzukiMatrixGroup m} :
    g ∈ torusSub m ↔ ∃ x : (BinaryGaloisField (2 * m + 1))ˣ, g = torus m x := by
  rcases External.huppert_blackburn_XI_3_1 m hm (tits m) (tits_tits m) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, he⟩, _⟩
  constructor
  · intro hg
    rw [torusSub, Subgroup.mem_subgroupOf] at hg
    refine ⟨e.symm ⟨(g : GL (Fin 4) _), hg⟩, Subtype.ext ?_⟩
    change (g : GL (Fin 4) _) = SuzukiTorusGL m _
    rw [← he, MulEquiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    exact torus_mem m x

theorem torusSub_le_normalizer :
    torusSub m ≤ Subgroup.normalizer ((rootSub m : Subgroup _) : Set _) := by
  intro h hh
  have hNF := External.suzukiTorusClosure_le_normalizer_rootClosure m (tits m) (tits_tits m)
    (tits_apply m)
  rw [torusSub, Subgroup.mem_subgroupOf] at hh
  have hn := hNF hh
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro r
  rw [rootSub, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact hn (r : GL (Fin 4) _)

theorem weyl_conj_torus (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    weyl m * torus m x * (weyl m)⁻¹ = torus m x⁻¹ := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (SuzukiWeylMatrix m * SuzukiTorusMatrix m x * SuzukiWeylMatrix m) i j =
    SuzukiTorusMatrix m x⁻¹ i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiWeylMatrix, SuzukiTorusMatrix, Matrix.mul_apply, Fin.sum_univ_four, inv_pow]

theorem weyl_not_mem_normalizer :
    weyl m ∉ Subgroup.normalizer ((rootSub m : Subgroup _) : Set _) := by
  intro hw
  have hmem : weyl m * root m 1 0 * (weyl m)⁻¹ ∈ rootSub m :=
    (Subgroup.mem_normalizer_iff.mp hw _).mp (root_mem m 1 0)
  obtain ⟨a, b, hab⟩ := (mem_rootSub m).mp hmem
  have h' := congrArg (fun g : SuzukiMatrixGroup m =>
    ((g : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
      Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) 3 2) hab
  change (SuzukiWeylMatrix m * SuzukiRootMatrix m 1 0 * SuzukiWeylMatrix m) 3 2 =
    SuzukiRootMatrix m a b 3 2 at h'
  simp [SuzukiWeylMatrix, SuzukiRootMatrix, Matrix.mul_apply, Fin.sum_univ_four] at h'

theorem mem_sylowCenter_rootSub (hm : 0 < m) {z : SuzukiMatrixGroup m} :
    z ∈ sylowCenter (rootSub m) ↔ ∃ b : BinaryGaloisField (2 * m + 1), z = root m 0 b := by
  rcases External.huppert_blackburn_XI_3_1 m hm (tits m) (tits_tits m) with
    ⟨_, _, _, _, _, _, _, _, hroot_mul, _⟩
  rw [mem_sylowCenter]
  constructor
  · rintro ⟨hz, hc⟩
    obtain ⟨a, b, rfl⟩ := (mem_rootSub m).mp hz
    refine ⟨b, ?_⟩
    by_contra hne
    have ha : a ≠ 0 := by
      rintro rfl
      exact hne rfl
    obtain ⟨u, hu⟩ : ∃ u : BinaryGaloisField (2 * m + 1), tits m u ≠ u := by
      by_contra hcon
      push Not at hcon
      have h2 : ∀ u : BinaryGaloisField (2 * m + 1), u ^ 2 = u := fun u => by
        rw [← tits_tits, hcon, hcon]
      have hcard : Nat.card (BinaryGaloisField (2 * m + 1)) ≤ 2 := by
        have hsub : (Set.univ : Set (BinaryGaloisField (2 * m + 1))) ⊆ {0, 1} := by
          intro u _
          have := h2 u
          have h3 : u * (u - 1) = 0 := by rw [mul_sub, mul_one, ← sq, this, sub_self]
          rcases mul_eq_zero.mp h3 with h | h
          · exact Or.inl h
          · exact Or.inr (sub_eq_zero.mp h)
        calc Nat.card (BinaryGaloisField (2 * m + 1))
            = (Set.univ : Set (BinaryGaloisField (2 * m + 1))).ncard := Set.ncard_univ _ |>.symm
          _ ≤ ({0, 1} : Set (BinaryGaloisField (2 * m + 1))).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ ({1} : Set (BinaryGaloisField (2 * m + 1))).ncard + 1 := Set.ncard_insert_le 0 {1}
          _ = 2 := by rw [Set.ncard_singleton]
      have hKcard : Nat.card (BinaryGaloisField (2 * m + 1)) = 2 ^ (2 * m + 1) := by
        simpa [BinaryGaloisField] using GaloisField.card 2 (2 * m + 1) (by omega)
      rw [hKcard] at hcard
      have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    let a' := u * a
    have hcomm := hc (root m a' 0) (root_mem m a' 0)
    rw [root_mul m hm, root_mul m hm] at hcomm
    have hinj := root_injective m hcomm
    have h2 : a' * tits m a = a * tits m a' := by
      have := hinj.2
      linear_combination this
    have hta : tits m a ≠ 0 := (map_ne_zero (tits m)).mpr ha
    apply hu
    have h3 : u * a * tits m a = a * (tits m u * tits m a) := by
      rw [← map_mul]
      exact h2
    have h4 : (u - tits m u) * (a * tits m a) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h (mul_ne_zero ha hta)
  · rintro ⟨b, rfl⟩
    refine ⟨root_mem m 0 b, fun t ht => ?_⟩
    obtain ⟨a', b', rfl⟩ := (mem_rootSub m).mp ht
    apply Subtype.ext
    change SuzukiRootGL m a' b' * SuzukiRootGL m 0 b = SuzukiRootGL m 0 b * SuzukiRootGL m a' b'
    rw [hroot_mul, hroot_mul]
    congr 1
    · ring
    · simp only [map_zero, mul_zero, zero_mul, add_zero]
      ring


theorem exists_sylow_eq_rootSub (hm : 0 < m) :
    ∃ S : Sylow 2 (SuzukiMatrixGroup m), (S : Subgroup (SuzukiMatrixGroup m)) = rootSub m := by
  rcases External.huppert_blackburn_XI_3_1 m hm (tits m) (tits_tits m) with
    ⟨_, _, hFp, _, _, _, hFcard, _⟩
  let F : Subgroup (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
    Subgroup.closure {A | ∃ a b : BinaryGaloisField (2 * m + 1), A = SuzukiRootGL m a b}
  have hF_le_G : F ≤ SuzukiMatrixGroup m := by
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hRp : IsPGroup 2 (rootSub m) :=
    hFp.of_equiv (Subgroup.subgroupOfEquivOfLe hF_le_G).symm
  have hRcard : Nat.card (rootSub m) = (2 ^ (2 * m + 1)) ^ 2 := by
    rw [rootSub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF_le_G).toEquiv]
    exact hFcard
  have hB := bender_suzukiMatrixGroup_borel m hm
  obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
  refine ⟨S, ?_⟩
  obtain ⟨-, -, -, hScard⟩ := benderBorel_sylowCenter hB S
  exact (Subgroup.eq_of_le_of_card_ge hRS (by rw [hScard, hRcard])).symm

theorem normalizer_and_card_sylow (hm : 0 < m) :
    (∀ g ∈ Subgroup.normalizer ((rootSub m : Subgroup (SuzukiMatrixGroup m)) : Set _),
      ∃ r ∈ rootSub m, ∃ h ∈ torusSub m, g = r * h) ∧
    Nat.card (Sylow 2 (SuzukiMatrixGroup m)) = Nat.card (rootSub m) + 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let q := 2 ^ (2 * m + 1)
  let pi : K ≃+* K := tits m
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := tits_apply m
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 := tits_tits m
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
  let G := SuzukiMatrixGroup m
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  rcases External.huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_, hpi_formula, _, _, _, _, hFcard, _⟩
  rcases External.huppert_blackburn_XI_3_3 m hm pi hpi with
    ⟨hpres, _hrecognition, _hfaithful, htwo_raw, _hthree,
      hOcard_raw, _hGcard, hstabilizer_raw⟩
  have hF_le_G : F ≤ SuzukiMatrixGroup m := by
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hH_le_G : H ≤ SuzukiMatrixGroup m := by
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  let U : Subgroup G := (F ⊔ H).subgroupOf (SuzukiMatrixGroup m)
  have hH_le_normalizerF : H ≤ Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
    External.suzukiTorusClosure_le_normalizer_rootClosure m pi hpi_sq hpi_formula
  have hU_le_normalizerR : U ≤ Subgroup.normalizer ((rootSub m : Subgroup G) : Set G) := by
    intro g hg
    have hg_normalizes : ((g : G) : GL (Fin 4) K) ∈
        Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
      sup_le Subgroup.le_normalizer hH_le_normalizerF hg
    rw [Subgroup.mem_normalizer_iff] at hg_normalizes ⊢
    intro r
    exact hg_normalizes ((r : G) : GL (Fin 4) K)
  let linRep : G →* LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (SuzukiMatrixGroup m).subtype
  let : MulAction G (ℙ K (Fin 4 → K)) :=
    MulAction.compHom (ℙ K (Fin 4 → K)) linRep
  let ovoid : SubMulAction G (ℙ K (Fin 4 → K)) :=
    { carrier := O
      smul_mem' := by
        intro g z hz
        change (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O
        exact hpres g z hz }
  let : MulAction G Omega := ovoid.mulAction
  let pinfO : Omega := ⟨pinf, Or.inl rfl⟩
  have hU_eq_stabilizer : U = MulAction.stabilizer G pinfO := by
    ext g
    rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
    change (g : GL (Fin 4) K) ∈ F ⊔ H ↔
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf
    exact (hstabilizer_raw g).symm
  have hRregular : ∀ a b : Omega, a ≠ pinfO → b ≠ pinfO →
      ∃! r : rootSub m, (r : G) • a = b := by
    intro a b ha hb
    have ha_raw : (a : ℙ K (Fin 4 → K)) ≠ pinf := by
      intro h
      exact ha (Subtype.ext h)
    have hb_raw : (b : ℙ K (Fin 4 → K)) ≠ pinf := by
      intro h
      exact hb (Subtype.ext h)
    rcases External.suzukiRootClosure_regular_on_ovoid_complement
        m pi hpi (a : ℙ K (Fin 4 → K)) b
          a.property b.property ha_raw hb_raw with
      ⟨r, hr, hr_unique⟩
    let rR : rootSub m :=
      ⟨⟨(r : GL (Fin 4) K), hF_le_G r.property⟩, r.property⟩
    refine ⟨rR, ?_, ?_⟩
    · apply Subtype.ext
      change (Matrix.GeneralLinearGroup.toLin
        (r : GL (Fin 4) K)).toLinearEquiv •
          (a : ℙ K (Fin 4 → K)) = b
      exact hr
    · intro s hs
      let sF : F := ⟨((s : G) : GL (Fin 4) K), s.property⟩
      have hs_raw :
          (Matrix.GeneralLinearGroup.toLin
            (sF : GL (Fin 4) K)).toLinearEquiv •
              (a : ℙ K (Fin 4 → K)) = b := by
        exact congrArg Subtype.val hs
      have hsF_eq : sF = r := hr_unique sF hs_raw
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : F => (x : GL (Fin 4) K)) hsF_eq
  have hR_le_stab : rootSub m ≤ MulAction.stabilizer G pinfO := by
    rw [← hU_eq_stabilizer]
    intro r hr
    exact (le_sup_left : F ≤ F ⊔ H) hr
  have hRne : rootSub m ≠ ⊥ := by
    intro h
    have h1 : root m 1 0 ∈ rootSub m := root_mem m 1 0
    rw [h, Subgroup.mem_bot, ← root_zero_zero m] at h1
    exact one_ne_zero (root_injective m h1).1
  have hnorm := CFSG.BenderSuzuki.normalizer_eq_stabilizer_of_regular_compl (rootSub m) pinfO
    hR_le_stab hRne hRregular (hU_eq_stabilizer ▸ hU_le_normalizerR)
  constructor
  · intro g hg
    rw [hnorm, ← hU_eq_stabilizer] at hg
    have hgFH : ((g : G) : GL (Fin 4) K) ∈ F ⊔ H := hg
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left F H hH_le_normalizerF,
      Set.mem_mul] at hgFH
    obtain ⟨f, hf, h, hh, hfh⟩ := hgFH
    refine ⟨⟨f, hF_le_G hf⟩, hf, ⟨h, hH_le_G hh⟩, hh, Subtype.ext hfh.symm⟩
  · obtain ⟨S, hS⟩ := exists_sylow_eq_rootSub m hm
    have htwo : MulAction.IsMultiplyPretransitive G Omega 2 := by
      rw [MulAction.is_two_pretransitive_iff]
      intro a b c d hab hcd
      have hab_raw : (a : ℙ K (Fin 4 → K)) ≠ b := by
        intro h
        exact hab (Subtype.ext h)
      have hcd_raw : (c : ℙ K (Fin 4 → K)) ≠ d := by
        intro h
        exact hcd (Subtype.ext h)
      rcases htwo_raw (a : ℙ K (Fin 4 → K)) b c d
          a.property b.property c.property d.property hab_raw hcd_raw with
        ⟨g, hga, hgb⟩
      exact ⟨g, Subtype.ext hga, Subtype.ext hgb⟩
    have : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hindex := MulAction.index_stabilizer_of_transitive G pinfO
    have hOcard : Nat.card Omega = q ^ 2 + 1 := hOcard_raw
    have hRcard : Nat.card (rootSub m) = q ^ 2 := by
      rw [rootSub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF_le_G).toEquiv]
      exact hFcard
    rw [Sylow.card_eq_index_normalizer S]
    change (Subgroup.normalizer (((S : Subgroup G)) : Set G)).index = _
    rw [hS, hnorm, hindex, hOcard, hRcard]

end SuzukiAut

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
