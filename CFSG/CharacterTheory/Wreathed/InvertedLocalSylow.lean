module

public import CFSG.CharacterTheory.Wreathed.InvertedLocalSylowSupport
public import CFSG.CharacterTheory.Wreathed.LocalOddCorePerfectNormalizer
public import CFSG.CharacterTheory.Wreathed.StationaryScalarCoverage
public import CFSG.CharacterTheory.Wreathed.OddEigenCyclicActor

public section

namespace CFSG.Wreathed.InvertedLocalSylow

open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem originalY_equiv_quaternion (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    Nonempty (Original.Y (2 ^ n) ≃* QuaternionGroup (2 ^ (n - 1))) :=
  ⟨((Original.Y (2 ^ n)).equivMapOfInjective (wreathModelHom S e)
    (wreathModelHom_injective S e)).trans (BrauerWong.modelYEquiv n hn S e)⟩

theorem centralizer_singleton_eq_subgroupOf (K : Subgroup G) (y : G) (hy : y ∈ K) :
    Subgroup.centralizer ({(⟨y, hy⟩ : K)} : Set K) =
      (Subgroup.centralizer ({y} : Set G)).subgroupOf K := by
  ext c
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

variable [Finite G]

open CFSG.Wreathed.LocalOddCorePerfectNormalizer in
theorem inverted_local_sylow_has_actual_cyclic_actor_and_controlled_eigensubgroup_centralizer
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal] [Group.IsPerfect J]
    (himage : J.map (centralizerOddCoreMap n S e) =
      CFSG.layer (centralizerOddCoreQuotient n S e))
    (hcomm : ∀ j ∈ J, ∀ r ∈ centralizerOddCore n S e, Commute j r)
    (H0 : Subgroup G) (hJ0 : J.map (involutionCentralizer n S e).subtype ≤ H0)
    (hfactor : CFSG.oddCore H0 ⊔ (involutionCentralizer n S e).subgroupOf H0 = ⊤)
    (ell : ℕ) (hell : ell.Prime) (hdiv : ell ∣ Nat.card (CFSG.oddCore H0))
    (W : Sylow ell (CFSG.oddCore H0)) :
    let s := wreathModelHom S e (Original.s (2 ^ n))
    let t := wreathModelHom S e (Original.t (2 ^ n))
    let z := wreathModelHom S e (Original.z (2 ^ n))
    let x := wreathModelHom S e (Original.x (2 ^ n))
    let y := wreathModelHom S e (Original.x2 (2 ^ n))
    let T := Subgroup.closure ({x, y} : Set G)
    let Wι : Subgroup G :=
      ((W : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype).map H0.subtype
    T ≤ H0 → T ≤ Subgroup.normalizer (Wι : Set G) → (∀ w ∈ Wι, x * w * x⁻¹ = w⁻¹) →
    let E := Wι ⊓ Subgroup.centralizer ({y} : Set G)
    let F := Wι ⊓ Subgroup.centralizer ({x * y} : Set G)
    let A := Subgroup.zpowers (s * t⁻¹)
    let d := y * z
    let K := Subgroup.centralizer (E : Set G)
    IsMulCommutative Wι ∧
    (E ⊔ F = Wι ∧ E ⊓ F = ⊥) ∧
    (E ≠ ⊥ ∧ F ≠ ⊥) ∧
    (E.map (MulAut.conj d).toMonoidHom = F ∧ F.map (MulAut.conj d).toMonoidHom = E) ∧
    Nat.card Wι = Nat.card E ^ 2 ∧
    (IsCyclic A ∧ Nat.card A = 2 ^ n) ∧
    A ≤ J.map (involutionCentralizer n S e).subtype ∧
    A ≤ Subgroup.normalizer (E : Set G) ∧
    (x ∈ A ∧ orderOf x = 2 ∧ ∀ a ∈ A, orderOf a = 2 → a = x) ∧
    (∀ w ∈ E, x * w * x⁻¹ = w⁻¹) ∧
    y ∈ K ∧
    ((∃ D : Subgroup K, D.Normal ∧ Odd (Nat.card D) ∧ ∃ k : ℕ, D.index = 2 ^ k) ∨
      ((∀ P : Sylow 2 K, Nonempty ((P : Subgroup K) ≃* QuaternionGroup (2 ^ (n - 1))) ∧
          Nat.card P = 2 * 2 ^ n) ∧
        (¬ ∃ K₀ : Subgroup K, K₀.Normal ∧ K₀.index = 2) ∧
        CFSG.oddCore K ⊔ (Subgroup.centralizer ({y} : Set G)).subgroupOf K = ⊤)) ∧
    ∀ u ∈ K, Odd (orderOf u) → y * u * y⁻¹ = u⁻¹ → u ∈ (CFSG.oddCore K).map K.subtype := by
  intro s t z x y T Wι hT0 hTW hinv E F A d K
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact ell.Prime := ⟨hell⟩
  have hx2 : orderOf x = 2 := CompatibleFamilies.orderOf_x S e hn
  have hy2 : orderOf y = 2 := CompatibleFamilies.orderOf_x2 S e hn
  have hxx : x * x = 1 := CompatibleFamilies.sq_eq_one_of_orderOf hx2
  have hyy : y * y = 1 := CompatibleFamilies.sq_eq_one_of_orderOf hy2
  have hxT : x ∈ T := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyT : y ∈ T := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hx0 : (centralInvolution n S e : G) ∈ H0 := hT0 hxT
  have hxW : (⟨(centralInvolution n S e : G), hx0⟩ : H0) ∈ Subgroup.normalizer
      (((W : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype) : Set H0) :=
    StationaryScalarCoverage.mem_normalizer_of_map_subtype _ _ (hTW hxT)
  have hdata :=
    local_odd_core_factorization_forces_actual_perfect_lift_to_normalize_Sylows
      hnonab n hn S e hfour J himage hcomm H0 hJ0 hx0 hfactor ell hell hdiv W hxW
  have hreq : s * t⁻¹ = wreathModelHom S e (Original.r (2 ^ n)) := by
    simp only [s, t, Original.r, map_mul, map_inv]
  have hdeq : d = wreathModelHom S e (Original.d (2 ^ n)) := by
    simp only [d, y, z, Original.d, map_mul]
  have hAeq : A = Subgroup.zpowers (wreathModelHom S e (Original.r (2 ^ n))) := by
    simp only [A, hreq]
  have hJnorm : J.map (involutionCentralizer n S e).subtype ≤
      Subgroup.normalizer (Wι : Set G) :=
    hdata.perfect_lift_normalizes.trans (Subgroup.le_normalizer_map H0.subtype)
  have hdY : wreathModelHom S e (Original.d (2 ^ n)) ∈ modelY S e :=
    Subgroup.mem_map_of_mem _
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hrY : wreathModelHom S e (Original.r (2 ^ n)) ∈ modelY S e :=
    Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
  have hdW : d ∈ Subgroup.normalizer (Wι : Set G) := by
    rw [hdeq]
    exact hJnorm (hdata.quaternion_in_lift hdY)
  have hyW : y ∈ Subgroup.normalizer (Wι : Set G) := hTW hyT
  have hdy : d * y * d⁻¹ = x * y := by
    rw [hdeq]
    exact modelHom_d_conj_x2 S e (by omega)
  have hdx : d * x * d⁻¹ = x := by
    rw [hdeq]
    exact modelHom_d_conj_x S e (by omega)
  have hcardW : Nat.card Wι = Nat.card (W : Subgroup (CFSG.oddCore H0)) := by
    simp only [Wι]
    rw [Subgroup.card_map_of_injective H0.subtype_injective,
      Subgroup.card_map_of_injective (CFSG.oddCore H0).subtype_injective]
  have hWodd : Odd (Nat.card Wι) := by
    rw [hcardW]
    exact (CFSG.Wreathed.weakClosure_oddCore_card H0).of_dvd_nat
      (Subgroup.card_subgroup_dvd_card _)
  have hWne : Wι ≠ ⊥ := by
    intro hbot
    have h1 : ell ∣ Nat.card (W : Subgroup (CFSG.oddCore H0)) := W.dvd_card_of_dvd_card hdiv
    rw [← hcardW, hbot, Subgroup.card_bot] at h1
    exact hell.one_lt.ne' (Nat.dvd_one.mp h1)
  obtain ⟨hab, ⟨hsup, hinf⟩, ⟨hEne, hFne⟩, ⟨hEF, hFE⟩, hcard⟩ :=
    eigensubgroup_structure Wι hWne hWodd x y d hxx hinv hyW hyy hdW hdy hdx
  have hAc : IsCyclic A := by
    simp only [A]
    infer_instance
  have hAcard : Nat.card A = 2 ^ n := by
    rw [hAeq]
    exact hdata.cyclic_actor_order
  have hAJ : A ≤ J.map (involutionCentralizer n S e).subtype := by
    rw [hAeq]
    exact Subgroup.zpowers_le.mpr (hdata.quaternion_in_lift hrY)
  have hAW : A ≤ Subgroup.normalizer (Wι : Set G) := by
    rw [hAeq]
    exact hdata.cyclic_actor_normalizes
  have hAy : A ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [hAeq, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact modelHom_r_comm_x2 S e
  have hAE : A ≤ Subgroup.normalizer (E : Set G) :=
    (le_inf hAW (hAy.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hxA : x ∈ A := by
    rw [hAeq]
    change wreathModelHom S e (Original.x (2 ^ n)) ∈ _
    rw [← modelHom_r_pow_half S e (by omega)]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hAinv : ∀ a ∈ A, orderOf a = 2 → a = x := by
    intro a ha hao
    have h := CFSG.Semidihedral.Principal.eq_of_orderOf_eq_two_of_isCyclic
      (a := (⟨a, ha⟩ : A)) (b := ⟨x, hxA⟩) (by rw [Subgroup.orderOf_mk]; exact hao)
      (by rw [Subgroup.orderOf_mk]; exact hx2)
    exact congrArg Subtype.val h
  have hinvE : ∀ w ∈ E, x * w * x⁻¹ = w⁻¹ := fun w hw => hinv w hw.1
  have hyK : y ∈ K := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_singleton_iff.mp hh.2)
  have hEodd : Odd (Nat.card E) := hWodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨halt, hKinv⟩ :=
    OddEigenCyclicActor.odd_eigensubgroup_cyclic_actor_centralizer_has_quaternion_factorization
      n hn S e E hEne hEodd A hAE hAc hAcard x hxA hx2 hinvE
  have hy2K : orderOf (⟨y, hyK⟩ : K) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hy2
  refine ⟨hab, ⟨hsup, hinf⟩, ⟨hEne, hFne⟩, ⟨hEF, hFE⟩, hcard, ⟨hAc, hAcard⟩, hAJ, hAE,
    ⟨hxA, hx2, hAinv⟩, hinvE, hyK, ?_, ?_⟩
  · rcases halt with h | ⟨hsyl, hno2, hfac⟩
    · exact Or.inl h
    · right
      refine ⟨fun P => ?_, hno2, ?_⟩
      · obtain ⟨⟨f⟩, hPcard⟩ := hsyl P
        obtain ⟨g⟩ := originalY_equiv_quaternion n hn S e
        exact ⟨⟨f.trans g⟩, hPcard⟩
      · rw [← centralizer_singleton_eq_subgroupOf K y hyK]
        exact hfac _ hy2K
  · intro u hu huodd huinv
    have h := hKinv ⟨y, hyK⟩ ⟨u, hu⟩ hy2K (by rw [Subgroup.orderOf_mk]; exact huodd)
      (Subtype.ext huinv)
    exact ⟨⟨u, hu⟩, h, rfl⟩

end CFSG.Wreathed.InvertedLocalSylow
