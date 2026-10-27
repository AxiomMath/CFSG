module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKD4Comm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKElem
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTriality
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate14952
public import Certificates.Certificate3951

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.K1.ExceptionalCat
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

namespace D4Exam

theorem coe_commutator {G : Type*} [Group G] (H : Subgroup G) (x y : H) :
    ((⁅x, y⁆ : H) : G) = ⁅(x : G), (y : G)⁆ := by
  simp [commutatorElement_def]

section Triality

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom

include hσ3 in
theorem triality_facts
    :
    ((∀ c d : K, trialityX₁ K τ₀ (c + d) = trialityX₁ K τ₀ c * trialityX₁ K τ₀ d) ∧
      (∀ c d : trialityFixedField K τ₀, trialityX₂ K τ₀ (c + d) = trialityX₂ K τ₀ c *
        trialityX₂ K τ₀ d) ∧
      (∀ c d : K, trialityX₃ K τ₀ (c + d) = trialityX₃ K τ₀ c * trialityX₃ K τ₀ d) ∧
      (∀ c d : K, trialityX₄ K τ₀ (c + d) = trialityX₄ K τ₀ c * trialityX₄ K τ₀ d) ∧
      (∀ c d : trialityFixedField K τ₀, trialityX₅ K τ₀ (c + d) = trialityX₅ K τ₀ c *
        trialityX₅ K τ₀ d) ∧
      (∀ c d : trialityFixedField K τ₀, trialityX₆ K τ₀ (c + d) = trialityX₆ K τ₀ c *
        trialityX₆ K τ₀ d)) ∧
    ((∀ c : K, (trialityX₁ K τ₀ c : ModGL TwistTag.D4.tag K) ∈
        graphFixedPosUnipotent TwistTag.D4 K τ₀) ∧
      (∀ c : trialityFixedField K τ₀, (trialityX₂ K τ₀ c : ModGL TwistTag.D4.tag K) ∈
        graphFixedPosUnipotent TwistTag.D4 K τ₀) ∧
      (∀ c : K, (trialityX₃ K τ₀ c : ModGL TwistTag.D4.tag K) ∈
        graphFixedPosUnipotent TwistTag.D4 K τ₀) ∧
      (∀ c : K, (trialityX₄ K τ₀ c : ModGL TwistTag.D4.tag K) ∈
        graphFixedPosUnipotent TwistTag.D4 K τ₀) ∧
      (∀ c : trialityFixedField K τ₀, (trialityX₅ K τ₀ c : ModGL TwistTag.D4.tag K) ∈
        graphFixedPosUnipotent TwistTag.D4 K τ₀) ∧
      (∀ c : trialityFixedField K τ₀, (trialityX₆ K τ₀ c : ModGL TwistTag.D4.tag K) ∈
        graphFixedPosUnipotent TwistTag.D4 K τ₀)) := by
  obtain ⟨⟨f₁, hf₁i, hf₁⟩, ⟨f₂, hf₂i, hf₂⟩, ⟨f₃, hf₃i, hf₃⟩, ⟨f₄, hf₄i, hf₄⟩,
    ⟨f₅, hf₅i, hf₅⟩, ⟨f₆, hf₆i, hf₆⟩, hbij, -, -⟩ :=
    even_triality_positive_orbit_parametrization K σ hσ3
  have mP : ∀ {M : Type} [AddCommGroup M] (f : Multiplicative M →* ↥(graphFixedPosUnipotent
      TwistTag.D4 K τ₀)) (X : M → adjointGroup TwistTag.D4.tag K),
      (∀ c : M, ((f (Multiplicative.ofAdd c) : graphFixedPosUnipotent TwistTag.D4 K τ₀) :
        ModGL TwistTag.D4.tag K) = (X c : ModGL TwistTag.D4.tag K)) →
      ∀ c, (X c : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ :=
    fun f X hf c => by rw [← hf c]; exact (f (Multiplicative.ofAdd c)).2
  exact ⟨⟨add_of_hom f₁ (trialityX₁ K τ₀) hf₁, add_of_hom f₂ (trialityX₂ K τ₀) hf₂,
    add_of_hom f₃ (trialityX₃ K τ₀) hf₃, add_of_hom f₄ (trialityX₄ K τ₀) hf₄,
    add_of_hom f₅ (trialityX₅ K τ₀) hf₅, add_of_hom f₆ (trialityX₆ K τ₀) hf₆⟩,
    ⟨mP f₁ (trialityX₁ K τ₀) hf₁, mP f₂ (trialityX₂ K τ₀) hf₂, mP f₃ (trialityX₃ K τ₀) hf₃,
      mP f₄ (trialityX₄ K τ₀) hf₄, mP f₅ (trialityX₅ K τ₀) hf₅, mP f₆ (trialityX₆ K τ₀) hf₆⟩⟩

include hσ3 in
theorem center_form
    {z : ModGL TwistTag.D4.tag K}
    (hz : z ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀)
    (hzc : ∀ y : adjointGroup TwistTag.D4.tag K,
      (y : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ →
        (y : ModGL TwistTag.D4.tag K) * z = z * (y : ModGL TwistTag.D4.tag K)) :
    ∃ f : trialityFixedField K τ₀, z = pinnedX TwistTag.D4.tag K (trialityRoot 5) (f : K) := by
  obtain ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, ⟨mP₁, mP₂, mP₃, mP₄, mP₅, mP₆⟩⟩ := triality_facts σ hσ3
  obtain ⟨-, -, -, -, -, -, hbij, -, -⟩ := even_triality_positive_orbit_parametrization K σ hσ3
  obtain ⟨k14, k34, k25, c15, c16, -, -, c26, c35, -, c45, c46, c56, htr, hnd⟩ :=
    even_triality_trace_commutators K σ.toRingHom hσ3
  obtain ⟨⟨a, b, c, d, e, f⟩, -, hzN⟩ := hbij.2.2 hz
  have hzz' : z = ((trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ c *
      trialityX₄ K τ₀ d * trialityX₅ K τ₀ e * trialityX₆ K τ₀ f : adjointGroup TwistTag.D4.tag K) :
        ModGL TwistTag.D4.tag K) := hzN.symm
  set Z' : adjointGroup TwistTag.D4.tag K :=
    trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ c * trialityX₄ K τ₀ d *
      trialityX₅ K τ₀ e * trialityX₆ K τ₀ f with hZ'
  have hcent : ∀ y : adjointGroup TwistTag.D4.tag K,
      (y : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ →
      y * Z' = Z' * y := by
    intro y hy
    apply Subtype.ext
    have e1 : ((y * Z' : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) =
        (y : ModGL TwistTag.D4.tag K) * (Z' : ModGL TwistTag.D4.tag K) := rfl
    have e2 : ((Z' * y : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) =
        (Z' : ModGL TwistTag.D4.tag K) * (y : ModGL TwistTag.D4.tag K) := rfl
    rw [e1, e2, ← hzz']
    exact hzc y hy
  have hnd₁ : ∀ s : K, (∀ t : K, trialityTrace K τ₀ hσ3 (s * t) = 0) → s = 0 := fun s hs =>
    hnd.1 s fun t => (htr s t).trans (hs t)
  have hnd₂ : ∀ t : K, (∀ s : K, trialityTrace K τ₀ hσ3 (s * t) = 0) → t = 0 := fun t ht =>
    hnd.2 t fun s => (htr s t).trans (ht s)
  have inj : ∀ (a a' : K) (b b' : trialityFixedField K τ₀) (c c' d d' : K)
      (e e' f f' : trialityFixedField K τ₀),
      trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ c * trialityX₄ K τ₀ d *
        trialityX₅ K τ₀ e * trialityX₆ K τ₀ f =
      trialityX₁ K τ₀ a' * trialityX₂ K τ₀ b' * trialityX₃ K τ₀ c' * trialityX₄ K τ₀ d' *
        trialityX₅ K τ₀ e' * trialityX₆ K τ₀ f' →
      a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' := by
    intro a a' b b' c c' d d' e e' f f' h
    have := hbij.2.1 (Set.mem_univ (a, b, c, d, e, f)) (Set.mem_univ (a', b', c', d', e', f'))
      (congrArg Subtype.val h)
    simp only [Prod.mk.injEq] at this
    exact this
  have key := triality_center_aux (trialityX₁ K τ₀) (trialityX₃ K τ₀) (trialityX₄ K τ₀)
    (trialityX₂ K τ₀) (trialityX₅ K τ₀) (trialityX₆ K τ₀)
    (fun s t => trialityTrace K τ₀ hσ3 (s * t)) (fun b e => b * e) (1 : trialityFixedField K τ₀)
    a₁ a₂ a₃ a₄ a₅ a₆ inj c15 c16 c26 c35 c45 c46 c56 k14 k34 k25 hnd₁ hnd₂
    (fun e => one_mul e) (fun b => mul_one b) a b c d e f
    (hcent _ (mP₅ 1)) (fun t => hcent _ (mP₄ t)) (fun t => hcent _ (mP₁ t))
    (hcent _ (mP₂ 1))
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := key
  have z1 := zero_of_add (trialityX₁ K τ₀) a₁
  have z2 := zero_of_add (trialityX₂ K τ₀) a₂
  have z3 := zero_of_add (trialityX₃ K τ₀) a₃
  have z4 := zero_of_add (trialityX₄ K τ₀) a₄
  have z5 := zero_of_add (trialityX₅ K τ₀) a₅
  refine ⟨f, ?_⟩
  rw [hzz', hZ', z1, z2, z3, z4, z5]
  simp only [one_mul]
  rfl

omit [Finite K] in
theorem weyl_x6_x5
    (f : K) :
    ∃ n ∈ graphFixedRootGroup TwistTag.D4 K τ₀,
      n * pinnedX TwistTag.D4.tag K (trialityRoot 5) f * n⁻¹ =
        pinnedX TwistTag.D4.tag K (trialityRoot 4) f := by
  let a₁' : Fin TwistTag.D4.foldedTag.rank := ⟨1, by decide⟩
  have hn₁ := canonicalRep_orbitReflection_mem_graphFixedRootGroup (σ := τ₀) a₁'
  have hroot6 : IsRoot TwistTag.D4.tag (trialityRoot 5) := (isRoot_trialityRoot 5 0).1
  have hr1 : TwistTag.D4.orbitReflection a₁' • trialityRoot 5 = trialityRoot 4 := by
    have hw : TwistTag.D4.orbitWord a₁' = [⟨2, by decide⟩] := by decide
    unfold TwistTag.orbitReflection
    rw [hw, CoxeterSystem.wordProd_singleton, simple_smul]
    exact List.ofFn_injective Certificates.certificate14952.1
  refine ⟨canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a₁'), hn₁, ?_⟩
  rw [canonicalRep_conj_charTwo _ hroot6, hr1]

omit [Finite K] in
theorem weyl_x5_x2
    (f : K) :
    ∃ n ∈ graphFixedRootGroup TwistTag.D4 K τ₀,
      n * pinnedX TwistTag.D4.tag K (trialityRoot 4) f * n⁻¹ =
        pinnedX TwistTag.D4.tag K (trialityRoot 1) f := by
  let a₀ : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩
  have hn₀ := canonicalRep_orbitReflection_mem_graphFixedRootGroup (σ := τ₀) a₀
  have hroot5 : IsRoot TwistTag.D4.tag (trialityRoot 4) := (isRoot_trialityRoot 4 0).1
  have hr0 : TwistTag.D4.orbitReflection a₀ • trialityRoot 4 = trialityRoot 1 := by
    have hw : TwistTag.D4.orbitWord a₀ =
        [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩] := by decide
    unfold TwistTag.orbitReflection
    rw [hw, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_singleton, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
    exact List.ofFn_injective Certificates.certificate14952.2.1
  refine ⟨canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a₀), hn₀, ?_⟩
  rw [canonicalRep_conj_charTwo _ hroot5, hr0]

omit [Finite K] [CharP K 2] in
theorem trialityRoot_one : trialityRoot 1 = rC :=
  List.ofFn_injective Certificates.certificate14952.2.2.1

omit [Finite K] [CharP K 2] in
theorem trialityRoot_four : trialityRoot 4 = rP :=
  List.ofFn_injective Certificates.certificate14952.2.2.2.1

omit [Finite K] [CharP K 2] in
theorem trialityRoot_five : trialityRoot 5 = rH :=
  List.ofFn_injective Certificates.certificate14952.2.2.2.2.1

omit [Finite K] [CharP K 2] in
theorem coe_trialityX₁_one :
    (trialityX₁ K τ₀ 1 : ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K rE0 1 *
      pinnedX TwistTag.D4.tag K rE1 1 * pinnedX TwistTag.D4.tag K rE3 1 := by
  have h0 : trialityRoot 0 = rE0 :=
    List.ofFn_injective Certificates.certificate14952.2.2.2.2.2.1
  have h1 : permLattice TwistTag.D4.perm rE0 = rE1 :=
    List.ofFn_injective Certificates.certificate14952.2.2.2.2.2.2.1
  have h2 : permLattice (TwistTag.D4.perm ^ 2) rE0 = rE3 :=
    List.ofFn_injective Certificates.certificate14952.2.2.2.2.2.2.2.1
  rw [trialityX₁, coe_trialityOrbitProd, h0, h1, h2, map_one, map_one]

omit [Finite K] [CharP K 2] in
theorem coe_trialityX₃
    (β : K) (hβ : τ₀ β = β) :
    (trialityX₃ K τ₀ β : ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K rM0 β *
      pinnedX TwistTag.D4.tag K rM1 β * pinnedX TwistTag.D4.tag K rM3 β := by
  have h0 : trialityRoot 2 = rM0 :=
    List.ofFn_injective Certificates.certificate14952.2.2.2.2.2.2.2.2.1
  have h1 : permLattice TwistTag.D4.perm rM0 = rM1 :=
    List.ofFn_injective Certificates.certificate14952.2.2.2.2.2.2.2.2.2.1
  have h2 : permLattice (TwistTag.D4.perm ^ 2) rM0 = rM3 :=
    List.ofFn_injective Certificates.certificate14952.2.2.2.2.2.2.2.2.2.2.1
  rw [trialityX₃, coe_trialityOrbitProd, h0, h1, h2, hβ, hβ]

omit [Finite K] [CharP K 2] in
theorem coe_trialityX₄
    (β : K) (hβ : τ₀ β = β) :
    (trialityX₄ K τ₀ β : ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K rN13 β *
      pinnedX TwistTag.D4.tag K rN03 β * pinnedX TwistTag.D4.tag K rN01 β := by
  have h0 : trialityRoot 3 = rN13 :=
    List.ofFn_injective Certificates.certificate14952.2.2.2.2.2.2.2.2.2.2.2.1
  have h1 : permLattice TwistTag.D4.perm rN13 = rN03 :=
    List.ofFn_injective Certificates.certificate14952.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2 : permLattice (TwistTag.D4.perm ^ 2) rN13 = rN01 :=
    List.ofFn_injective Certificates.certificate14952.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [trialityX₄, coe_trialityOrbitProd, h0, h1, h2, hβ, hβ]

omit [Finite K] in
theorem trialityX₂_comm_trialityX₁
    (β : trialityFixedField K τ₀) :
    ⁅pinnedX TwistTag.D4.tag K (trialityRoot 1) (β : K),
        (trialityX₁ K τ₀ 1 : ModGL TwistTag.D4.tag K)⁆ =
      (trialityX₃ K τ₀ (β : K) : ModGL TwistTag.D4.tag K) *
        (trialityX₄ K τ₀ (β : K) : ModGL TwistTag.D4.tag K) *
          pinnedX TwistTag.D4.tag K (trialityRoot 4) (β : K) *
            pinnedX TwistTag.D4.tag K (trialityRoot 5) ((β : K) * (β : K)) := by
  have hβ : τ₀ (β : K) = (β : K) := β.2
  rw [coe_trialityX₁_one, coe_trialityX₃ σ _ hβ, coe_trialityX₄ σ _ hβ, trialityRoot_one,
    trialityRoot_four, trialityRoot_five]
  exact comm_root (β : K)

omit [Finite K] in
theorem d4_mul_self
    (α : Fin TwistTag.D4.tag.rank → ℤ) (x : K) :
    pinnedX TwistTag.D4.tag K α x * pinnedX TwistTag.D4.tag K α x = 1 := by
  rw [← pinnedX_add, ← two_mul, CharTwo.two_eq_zero, zero_mul, pinnedX_zero]

include hσ3 in
theorem d4_core
    {R₁ A₁ A₁' : Subgroup (ModGL TwistTag.D4.tag K)}
    (hU : ∀ q ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀, ∀ r ∈ R₁, q * r * q⁻¹ ∈ R₁)
    (hstrong : ∀ r ∈ R₁, r * r = 1 → ∀ g ∈ graphFixedRootGroup TwistTag.D4 K τ₀,
      g * r * g⁻¹ ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ → g * r * g⁻¹ ∈ R₁)
    (hA : ∀ x ∈ A₁, ∀ y ∈ A₁, x * y = y * x) (hA' : ∀ x ∈ A₁', ∀ y ∈ A₁', x * y = y * x)
    (hel : ∀ e ∈ R₁, e * e = 1 → e ∈ A₁ ∨ e ∈ A₁')
    (β : trialityFixedField K τ₀) (hβ0 : (β : K) ≠ 0)
    (hz : pinnedX TwistTag.D4.tag K (trialityRoot 5) (β : K) ∈ R₁) : False := by
  obtain ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, ⟨mP₁, mP₂, mP₃, mP₄, mP₅, mP₆⟩⟩ := triality_facts σ hσ3
  obtain ⟨k14, k34, k25, c15, c16, c23, c24, c26, c35, c36, c45, c46, c56, htr, hnd⟩ :=
    even_triality_trace_commutators K σ.toRingHom hσ3
  have hβ : τ₀ (β : K) = (β : K) := β.2
  have cm : ∀ {x y : adjointGroup TwistTag.D4.tag K}, Commute x y →
      Commute (x : ModGL TwistTag.D4.tag K) (y : ModGL TwistTag.D4.tag K) := fun h =>
    congrArg Subtype.val h
  have hx5 : pinnedX TwistTag.D4.tag K (trialityRoot 4) (β : K) ∈ R₁ := by
    obtain ⟨n, hn, hc⟩ := weyl_x6_x5 σ (β : K)
    have := hstrong _ hz (d4_mul_self _ _) n hn (by rw [hc]; exact mP₅ β)
    rwa [hc] at this
  have hx2 : pinnedX TwistTag.D4.tag K (trialityRoot 1) (β : K) ∈ R₁ := by
    obtain ⟨n, hn, hc⟩ := weyl_x5_x2 σ (β : K)
    have := hstrong _ hx5 (d4_mul_self _ _) n hn (by rw [hc]; exact mP₂ β)
    rwa [hc] at this
  have trace_eq : ((trialityTrace K τ₀ hσ3 ((β : K) * (β : K)) : trialityFixedField K τ₀) : K) =
      (β : K) * (β : K) := by
    have h2 : τ₀ ((β : K) * (β : K)) = (β : K) * (β : K) := by rw [map_mul, hβ]
    show (β : K) * (β : K) + τ₀ ((β : K) * (β : K)) + τ₀ (τ₀ ((β : K) * (β : K))) = _
    rw [h2, h2, CharTwo.add_self_eq_zero, zero_add]
  have hab : ⁅(trialityX₂ K τ₀ β : ModGL TwistTag.D4.tag K),
      (trialityX₅ K τ₀ β : ModGL TwistTag.D4.tag K)⁆ =
      (trialityX₆ K τ₀ (β * β) : ModGL TwistTag.D4.tag K) := by
    have := congrArg Subtype.val (k25 β β)
    rwa [coe_commutator] at this
  have hpq : ⁅(trialityX₃ K τ₀ (β : K) : ModGL TwistTag.D4.tag K),
      (trialityX₄ K τ₀ (β : K) : ModGL TwistTag.D4.tag K)⁆ =
      (trialityX₆ K τ₀ (β * β) : ModGL TwistTag.D4.tag K) := by
    have := congrArg Subtype.val (k34 (β : K) (β : K))
    rw [coe_commutator] at this
    refine this.trans ?_
    show pinnedX TwistTag.D4.tag K (trialityRoot 5)
      ((trialityTrace K τ₀ hσ3 ((β : K) * (β : K)) : trialityFixedField K τ₀) : K) = _
    rw [trace_eq]
    rfl
  have sqk : ∀ c : trialityFixedField K τ₀, c + c = 0 := fun c =>
    Subtype.ext (CharTwo.add_self_eq_zero (c : K))
  have sqK : ∀ c : K, c + c = 0 := fun c => CharTwo.add_self_eq_zero c
  have haa : (trialityX₂ K τ₀ β : ModGL TwistTag.D4.tag K) *
      (trialityX₂ K τ₀ β : ModGL TwistTag.D4.tag K) = 1 := by
    have := a₂ β β
    rw [sqk β, zero_of_add (trialityX₂ K τ₀) a₂] at this
    exact (congrArg Subtype.val this).symm
  have hbb : (trialityX₅ K τ₀ β : ModGL TwistTag.D4.tag K) *
      (trialityX₅ K τ₀ β : ModGL TwistTag.D4.tag K) = 1 := by
    have := a₅ β β
    rw [sqk β, zero_of_add (trialityX₅ K τ₀) a₅] at this
    exact (congrArg Subtype.val this).symm
  have hhh : (trialityX₆ K τ₀ (β * β) : ModGL TwistTag.D4.tag K) *
      (trialityX₆ K τ₀ (β * β) : ModGL TwistTag.D4.tag K) = 1 := by
    have := a₆ (β * β) (β * β)
    rw [sqk (β * β), zero_of_add (trialityX₆ K τ₀) a₆] at this
    exact (congrArg Subtype.val this).symm
  have hpp : (trialityX₃ K τ₀ (β : K) : ModGL TwistTag.D4.tag K) *
      (trialityX₃ K τ₀ (β : K) : ModGL TwistTag.D4.tag K) = 1 := by
    have := a₃ (β : K) (β : K)
    rw [sqK, zero_of_add (trialityX₃ K τ₀) a₃] at this
    exact (congrArg Subtype.val this).symm
  have hqq : (trialityX₄ K τ₀ (β : K) : ModGL TwistTag.D4.tag K) *
      (trialityX₄ K τ₀ (β : K) : ModGL TwistTag.D4.tag K) = 1 := by
    have := a₄ (β : K) (β : K)
    rw [sqK, zero_of_add (trialityX₄ K τ₀) a₄] at this
    exact (congrArg Subtype.val this).symm
  have hh1 : (trialityX₆ K τ₀ (β * β) : ModGL TwistTag.D4.tag K) ≠ 1 := by
    intro hh
    have h0 : pinnedX TwistTag.D4.tag K (trialityRoot 5) ((β : K) * (β : K)) =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) 0 := hh.trans (pinnedX_zero _ _ _).symm
    exact hβ0 (mul_self_eq_zero.mp (pinnedX_injective _ _ _ h0))
  have ha : (trialityX₂ K τ₀ β : ModGL TwistTag.D4.tag K) ∈ R₁ := hx2
  have hb : (trialityX₅ K τ₀ β : ModGL TwistTag.D4.tag K) ∈ R₁ := hx5
  have hh : (trialityX₆ K τ₀ (β * β) : ModGL TwistTag.D4.tag K) ∈ R₁ := by
    rw [← hab]
    exact R₁.mul_mem (R₁.mul_mem (R₁.mul_mem ha hb) (R₁.inv_mem ha)) (R₁.inv_mem hb)
  exact core_abstract (R := R₁) (A := A₁) (A' := A₁') ha hb hh
    (trialityX₂_comm_trialityX₁ σ β) (fun r hr => hU _ (mP₁ 1) r hr) hab hpq haa hbb hpp hqq hhh
    hh1 (cm (c23 β (β : K))) (cm (c24 β (β : K))) (cm (c35 (β : K) β)).symm
    (cm (c45 (β : K) β)).symm hA hA' hel

end Triality

theorem d4_false
    {F : Type} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F)
    (hσ3 : σ.toRingHom ^ 3 = 1)
    (R₀ A₀ A₀' : Subgroup (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))
    (hRU : R₀ ≤ (graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))
    (hU : IsSylowTwoOf ((graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) ⊤)
    (hnorm : ∀ n ∈ Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) : Subgroup _) : Set _),
        ∀ r ∈ R₀, n * r * n⁻¹ ∈ R₀)
    (hne : R₀ ≠ ⊥) (hA : IsElemAbelian 2 A₀) (hA' : IsElemAbelian 2 A₀')
    (hel : ∀ e ∈ R₀, e * e = 1 → e ∈ A₀ ∨ e ∈ A₀')
    (hstrong : ∀ r ∈ R₀, r * r = 1 → ∀ g : graphFixedRootGroup TwistTag.D4 F σ.toRingHom,
      g * r * g⁻¹ ∈ (graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) → g * r * g⁻¹ ∈ R₀) : False := by
  have hQ2 : IsPGroup 2 ↥((graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) := hU.2.1
  have hCle := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 F σ.toRingHom
  obtain ⟨z, hzR, hz1, hzc⟩ := exists_ne_one_mem_centralizer hQ2 hRU
    (fun a ha q hq => by
      have := hnorm q⁻¹ (Subgroup.le_normalizer (Subgroup.inv_mem _ hq)) a ha
      rwa [inv_inv] at this) hne
  have hzU : (z : ModGL TwistTag.D4.tag F) ∈ graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom :=
    Subgroup.mem_subgroupOf.mp (hRU hzR)
  obtain ⟨β, hβ⟩ := center_form σ hσ3 hzU (fun y hy => by
    have hmem : (⟨(y : ModGL TwistTag.D4.tag F), hCle hy⟩ :
        graphFixedRootGroup TwistTag.D4 F σ.toRingHom) ∈
        (graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) := hy
    exact congrArg Subtype.val (hzc _ hmem))
  have hβ0 : (β : F) ≠ 0 := by
    intro h0
    apply hz1
    apply Subtype.ext
    rw [hβ, h0, pinnedX_zero]
    rfl
  let ι : graphFixedRootGroup TwistTag.D4 F σ.toRingHom →* ModGL TwistTag.D4.tag F :=
    (graphFixedRootGroup TwistTag.D4 F σ.toRingHom).subtype
  have hU₁ : ∀ q ∈ graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom, ∀ r ∈ R₀.map ι,
      q * r * q⁻¹ ∈ R₀.map ι := by
    intro q hq r hr
    obtain ⟨x, hx, rfl⟩ := hr
    have hqU : (⟨q, hCle hq⟩ : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) ∈
        (graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) := hq
    exact ⟨⟨q, hCle hq⟩ * x * ⟨q, hCle hq⟩⁻¹, hnorm _ (Subgroup.le_normalizer hqU) x hx, rfl⟩
  have hstrong₁ : ∀ r ∈ R₀.map ι, r * r = 1 → ∀ g ∈ graphFixedRootGroup TwistTag.D4 F σ.toRingHom,
      g * r * g⁻¹ ∈ graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom → g * r * g⁻¹ ∈ R₀.map ι := by
    intro r hr hrr g hg hgU
    obtain ⟨x, hx, rfl⟩ := hr
    have hxx : x * x = 1 := Subtype.ext hrr
    exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, hstrong x hx hxx ⟨g, hg⟩ hgU, rfl⟩
  have hel₁ : ∀ e ∈ R₀.map ι, e * e = 1 → e ∈ A₀.map ι ∨ e ∈ A₀'.map ι := by
    intro e he hee
    obtain ⟨x, hx, rfl⟩ := he
    have hxx : x * x = 1 := Subtype.ext hee
    rcases hel x hx hxx with h | h
    · exact Or.inl ⟨x, h, rfl⟩
    · exact Or.inr ⟨x, h, rfl⟩
  have hcomm : ∀ {B : Subgroup (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)},
      IsElemAbelian 2 B → ∀ a ∈ B.map ι, ∀ b ∈ B.map ι, a * b = b * a := by
    intro B hB a ha b hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have := hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg (fun w : B => ((w : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) :
      ModGL TwistTag.D4.tag F)) this
  exact d4_core σ hσ3 hU₁ hstrong₁ (hcomm hA) (hcomm hA') hel₁ β hβ0
    (hβ ▸ ⟨z, hzR, rfl⟩ : pinnedX TwistTag.D4.tag F (trialityRoot 5) (β : F) ∈ R₀.map ι)

end D4Exam

theorem examExcludes_d4
    : ExamExcludes FamD4 := by
  rintro G _ _ K B B' P R m h ⟨f, hf, hmodel⟩
  obtain ⟨-, F, _, _, hK, σ₀, hσ₀, ⟨e⟩⟩ := hmodel
  have hK3 : Nat.card F = (2 ^ f) ^ 3 := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) (show Nat.card F = 2 ^ (f * 3) by rw [hK3, ← pow_mul])
  obtain ⟨σ, rfl⟩ : ∃ σ : F ≃+* F, σ.toRingHom = σ₀ :=
    ⟨RingEquiv.ofBijective σ₀ ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩, rfl⟩
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := hσ₀
  have hσ3 : σ.toRingHom ^ 3 = 1 := RingHom.ext fun c => by
    rw [ringHom_pow_three_apply]
    exact ringEquiv_cube_apply_eq hK3 hσ c
  obtain ⟨-, -, -, -, -, -, -, ⟨E⟩⟩ := even_triality_exact_automorphism_normal_form hf F hK3 σ hσ
  let e' := e.trans E
  have : Finite (ModGL TwistTag.D4.tag F) := finite_modGL (τ := TwistTag.D4.tag) (K := F)
  let θ : ↥K →* graphFixedRootGroup TwistTag.D4 F σ.toRingHom :=
    e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hθsurj : Function.Surjective θ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : θ.ker ≤ Subgroup.center ↥K := by
    intro x hx
    have hx' : e' (QuotientGroup.mk x) = 1 := hx
    rwa [map_eq_one_iff e' e'.injective, QuotientGroup.eq_one_iff] at hx'
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨⟨P', hP'⟩, -⟩ := exceptional_fixed_Sylow_opposition TwistTag.D4 F 2 σ w₀ hw₀
  have hU : IsSylowTwoOf ((graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) ⊤ := by
    rw [← hP']
    exact isSylowTwoOf_top_iff.mpr ⟨P'.isPGroup', P'.not_dvd_index⟩
  obtain ⟨R₀, A₀, A₀', hRU, hnorm, hne, hA, hA', hel, hstrong⟩ :=
    h.toAbs.exists_RprimeE θ hθsurj hker _ hU
  exact D4Exam.d4_false σ hσ3 R₀ A₀ A₀' hRU hU hnorm hne hA hA' hel hstrong

end CFSG.QuasithinUnique.Lin2
