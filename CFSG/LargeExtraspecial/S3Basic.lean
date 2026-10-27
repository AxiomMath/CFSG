module

public import CFSG.LargeExtraspecial.Setting
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Setting

variable {G : Type*} [Group G] (S : Setting G)

theorem mem_M_iff {g : G} : g ∈ S.M ↔ g * S.z = S.z * g := mem_centralizer_singleton_iff

theorem z_mem_M : S.z ∈ S.M := S.mem_M_iff.mpr rfl

theorem mem_M_of_mem_QG {x : G} (hx : x ∈ S.QG) : x ∈ S.M := S.QG_le_M hx

@[simp] theorem coe_zQ : ((S.zQ : S.M) : G) = S.z := rfl

theorem z_comm {g : G} (hg : g ∈ S.M) : g * S.z = S.z * g := S.mem_M_iff.mp hg

@[expose] def ofQG (x : G) (hx : x ∈ S.QG) : S.Q :=
  ⟨⟨x, (S.mem_QG_iff.mp hx).1⟩, (S.mem_QG_iff.mp hx).2⟩

@[simp] theorem coe_ofQG (x : G) (hx : x ∈ S.QG) : ((S.ofQG x hx : S.M) : G) = x := rfl

theorem coe_mem_QG (x : S.Q) : ((x : S.M) : G) ∈ S.QG := ⟨x, x.2, rfl⟩

theorem ofQG_eq_iff {x : G} (hx : x ∈ S.QG) {y : S.Q} :
    S.ofQG x hx = y ↔ x = ((y : S.M) : G) :=
  ⟨fun h => h ▸ rfl, fun h => Subtype.ext (Subtype.ext h)⟩

theorem conj_mem_QG {g x : G} (hg : g ∈ S.M) (hx : x ∈ S.QG) : g * x * g⁻¹ ∈ S.QG :=
  ⟨_, S.normal.conj_mem (S.ofQG x hx : S.M) (S.ofQG x hx).2 ⟨g, hg⟩, rfl⟩

theorem mem_QG_of_commute {g : G} (hg : g ∈ S.M) (h : ∀ x ∈ S.QG, g * x = x * g) :
    g ∈ S.QG := by
  have hc : (⟨g, hg⟩ : S.M) ∈ centralizer (S.Q : Set S.M) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (h _ ⟨y, hy, rfl⟩).symm
  exact ⟨_, S.centralizer_le hc, rfl⟩

theorem eq_one_or_z_of_commute {x : G} (hx : x ∈ S.QG) (h : ∀ y ∈ S.QG, x * y = y * x) :
    x = 1 ∨ x = S.z := by
  have hc : S.ofQG x hx ∈ center S.Q := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (Subtype.ext (h _ (S.coe_mem_QG y)).symm)
  rcases S.mem_center_Q_iff.mp hc with h1 | h1
  · exact Or.inl ((S.ofQG_eq_iff hx).mp h1)
  · exact Or.inr ((S.ofQG_eq_iff hx).mp h1)

theorem z_comm_QG {x : G} (hx : x ∈ S.QG) : x * S.z = S.z * x := S.z_comm (S.QG_le_M hx)

theorem z_sq : S.z ^ 2 = 1 := by rw [pow_two, S.z_mul_z]

theorem z_inv : S.z⁻¹ = S.z := inv_eq_of_mul_eq_one_right S.z_mul_z

open Classical in
@[expose] noncomputable def cl (x : G) : S.Qt :=
  if hx : x ∈ S.QG then S.toQt (S.ofQG x hx) else 0

theorem cl_of_mem {x : G} (hx : x ∈ S.QG) : S.cl x = S.toQt (S.ofQG x hx) := by
  simp only [cl, hx, ↓reduceDIte]

theorem cl_coe (x : S.Q) : S.cl ((x : S.M) : G) = S.toQt x := S.cl_of_mem (S.coe_mem_QG x)

theorem cl_mul {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG) :
    S.cl (x * y) = S.cl x + S.cl y := by
  rw [S.cl_of_mem hx, S.cl_of_mem hy, S.cl_of_mem (S.QG.mul_mem hx hy), ← S.toQt_mul]
  rfl

theorem cl_one : S.cl 1 = 0 := by
  rw [S.cl_of_mem S.QG.one_mem, ← S.toQt_one]
  rfl

theorem cl_inv {x : G} (hx : x ∈ S.QG) : S.cl x⁻¹ = S.cl x := by
  rw [S.cl_of_mem hx, S.cl_of_mem (S.QG.inv_mem hx),
    show S.ofQG x⁻¹ (S.QG.inv_mem hx) = (S.ofQG x hx)⁻¹ from rfl, S.toQt_inv,
    ZModModule.neg_eq_self]

theorem cl_z : S.cl S.z = 0 := by
  rw [S.cl_of_mem S.z_mem_QG, S.toQt_eq_zero_iff']
  exact Or.inr rfl

theorem cl_eq_zero_iff {x : G} (hx : x ∈ S.QG) : S.cl x = 0 ↔ x = 1 ∨ x = S.z := by
  rw [S.cl_of_mem hx, S.toQt_eq_zero_iff', S.ofQG_eq_iff, S.ofQG_eq_iff]
  rfl

theorem exists_cl (v : S.Qt) : ∃ x ∈ S.QG, S.cl x = v := by
  obtain ⟨x, rfl⟩ := S.exists_toQt v
  exact ⟨_, S.coe_mem_QG x, S.cl_coe x⟩

theorem cl_mul_z {x : G} (hx : x ∈ S.QG) : S.cl (x * S.z) = S.cl x := by
  rw [S.cl_mul hx S.z_mem_QG, S.cl_z, add_zero]

theorem cl_eq_cl_iff {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG) :
    S.cl x = S.cl y ↔ y = x ∨ y = x * S.z := by
  have hxy : x⁻¹ * y ∈ S.QG := S.QG.mul_mem (S.QG.inv_mem hx) hy
  have key : S.cl x = S.cl y ↔ S.cl (x⁻¹ * y) = 0 := by
    rw [S.cl_mul (S.QG.inv_mem hx) hy, S.cl_inv hx]
    constructor
    · intro h
      rw [h]
      exact CFSG.RankThree.OrthogonalInvolutions.add_self_vec (ZMod 2) _
    · intro h
      have h' := congrArg (· + S.cl y) h
      simp only [zero_add] at h'
      rw [← h', add_assoc, CFSG.RankThree.OrthogonalInvolutions.add_self_vec (ZMod 2), add_zero]
  rw [key, S.cl_eq_zero_iff hxy]
  constructor
  · rintro (h | h)
    · left
      calc y = x * (x⁻¹ * y) := by group
        _ = x := by rw [h, mul_one]
    · right
      calc y = x * (x⁻¹ * y) := by group
        _ = x * S.z := by rw [h]
  · rintro (rfl | rfl)
    · left
      group
    · right
      group

theorem commutator_eq_one_or_z {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = S.z := by
  have h := commutatorElement_mem_center S.extraspecial (S.ofQG x hx) (S.ofQG y hy)
  rcases S.mem_center_Q_iff.mp h with h1 | h1
  · left
    have := congrArg (fun w : S.Q => ((w : S.M) : G)) h1
    simpa [commutatorElement_def] using this
  · right
    have := congrArg (fun w : S.Q => ((w : S.M) : G)) h1
    simpa [commutatorElement_def] using this

theorem mul_comm_or {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG) :
    x * y = y * x ∨ x * y = S.z * (y * x) := by
  rcases S.commutator_eq_one_or_z hx hy with h | h
  · left
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h, one_mul]
  · right
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = S.z * (y * x) := by rw [h]

@[expose] noncomputable def clSub (X : Subgroup G) : Submodule (ZMod 2) S.Qt :=
  Submodule.span (ZMod 2) {v | ∃ x ∈ X, x ∈ S.QG ∧ S.cl x = v}

theorem mem_clSub_iff {X : Subgroup G} {v : S.Qt} :
    v ∈ S.clSub X ↔ ∃ x ∈ X, x ∈ S.QG ∧ S.cl x = v := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hv
    | zero => exact ⟨1, X.one_mem, S.QG.one_mem, S.cl_one⟩
    | add v w _ _ hv hw =>
      obtain ⟨x, hxX, hxQ, rfl⟩ := hv
      obtain ⟨y, hyX, hyQ, rfl⟩ := hw
      exact ⟨x * y, X.mul_mem hxX hyX, S.QG.mul_mem hxQ hyQ, S.cl_mul hxQ hyQ⟩
    | smul a v _ hv =>
      obtain ⟨x, hxX, hxQ, rfl⟩ := hv
      rcases zmod2_cases a with rfl | rfl
      · exact ⟨1, X.one_mem, S.QG.one_mem, by rw [zero_smul, S.cl_one]⟩
      · exact ⟨x, hxX, hxQ, by rw [one_smul]⟩
  · intro hv
    exact Submodule.subset_span hv

theorem cl_mem_clSub {X : Subgroup G} {x : G} (hxX : x ∈ X) (hxQ : x ∈ S.QG) :
    S.cl x ∈ S.clSub X :=
  S.mem_clSub_iff.mpr ⟨x, hxX, hxQ, rfl⟩

theorem clSub_mono {X Y : Subgroup G} (h : X ≤ Y) : S.clSub X ≤ S.clSub Y := by
  intro v hv
  obtain ⟨x, hxX, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  exact S.cl_mem_clSub (h hxX) hxQ

@[expose] noncomputable def clPre (W : Submodule (ZMod 2) S.Qt) : Subgroup G where
  carrier := {x | x ∈ S.QG ∧ S.cl x ∈ W}
  mul_mem' := fun {x y} hx hy =>
    ⟨S.QG.mul_mem hx.1 hy.1, by rw [S.cl_mul hx.1 hy.1]; exact W.add_mem hx.2 hy.2⟩
  one_mem' := ⟨S.QG.one_mem, by rw [S.cl_one]; exact W.zero_mem⟩
  inv_mem' := fun {x} hx => ⟨S.QG.inv_mem hx.1, by rw [S.cl_inv hx.1]; exact hx.2⟩

theorem mem_clPre {W : Submodule (ZMod 2) S.Qt} {x : G} :
    x ∈ S.clPre W ↔ x ∈ S.QG ∧ S.cl x ∈ W := Iff.rfl

theorem clPre_le_QG (W : Submodule (ZMod 2) S.Qt) : S.clPre W ≤ S.QG := fun _ hx => hx.1

theorem z_mem_clPre (W : Submodule (ZMod 2) S.Qt) : S.z ∈ S.clPre W :=
  ⟨S.z_mem_QG, by rw [S.cl_z]; exact W.zero_mem⟩

theorem clPre_mono {W W' : Submodule (ZMod 2) S.Qt} (h : W ≤ W') : S.clPre W ≤ S.clPre W' :=
  fun _ hx => ⟨hx.1, h hx.2⟩

theorem clPre_top : S.clPre ⊤ = S.QG := by
  ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, Submodule.mem_top⟩⟩

theorem clSub_clPre (W : Submodule (ZMod 2) S.Qt) : S.clSub (S.clPre W) = W := by
  ext v
  rw [S.mem_clSub_iff]
  constructor
  · rintro ⟨x, hx, -, rfl⟩
    exact hx.2
  · intro hv
    obtain ⟨x, hx, rfl⟩ := S.exists_cl v
    exact ⟨x, ⟨hx, hv⟩, hx, rfl⟩

theorem clPre_clSub {X : Subgroup G} (hX : X ≤ S.QG) (hz : S.z ∈ X) :
    S.clPre (S.clSub X) = X := by
  ext x
  constructor
  · rintro ⟨hxQ, hv⟩
    obtain ⟨y, hyX, hyQ, hyx⟩ := S.mem_clSub_iff.mp hv
    rcases (S.cl_eq_cl_iff hyQ hxQ).mp hyx with rfl | rfl
    · exact hyX
    · exact X.mul_mem hyX hz
  · intro hx
    exact ⟨hX hx, S.cl_mem_clSub hx (hX hx)⟩

theorem le_clPre_clSub {X : Subgroup G} (hX : X ≤ S.QG) : X ≤ S.clPre (S.clSub X) :=
  fun _ hx => ⟨hX hx, S.cl_mem_clSub hx (hX hx)⟩

variable [Finite G]

theorem q_cl_eq_zero_iff {x : G} (hx : x ∈ S.QG) : S.q (S.cl x) = 0 ↔ x ^ 2 = 1 := by
  rw [S.cl_of_mem hx, S.q_toQt_eq_zero_iff]
  constructor
  · intro h
    have := congrArg (fun w : S.Q => ((w : S.M) : G)) h
    simpa using this
  · intro h
    exact Subtype.ext (Subtype.ext (by simpa using h))

theorem q_cl_eq_one_iff {x : G} (hx : x ∈ S.QG) : S.q (S.cl x) = 1 ↔ x ^ 2 ≠ 1 := by
  rw [ne_eq, ← S.q_cl_eq_zero_iff hx]
  rcases zmod2_cases (S.q (S.cl x)) with h | h <;> rw [h] <;> decide

theorem polar_cl_eq_zero_iff {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG) :
    polar S.q (S.cl x) (S.cl y) = 0 ↔ x * y = y * x := by
  rw [S.cl_of_mem hx, S.cl_of_mem hy, S.polar_q_toQt_eq_zero_iff]
  constructor
  · intro h
    have := congrArg (fun w : S.Q => ((w : S.M) : G)) h
    simpa using this
  · intro h
    exact Subtype.ext (Subtype.ext (by simpa using h))

theorem polar_cl_eq_one_iff {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG) :
    polar S.q (S.cl x) (S.cl y) = 1 ↔ x * y ≠ y * x := by
  rw [ne_eq, ← S.polar_cl_eq_zero_iff hx hy]
  rcases zmod2_cases (polar S.q (S.cl x) (S.cl y)) with h | h <;> rw [h] <;> decide

theorem sq_eq_one_or_z {x : G} (hx : x ∈ S.QG) : x ^ 2 = 1 ∨ x ^ 2 = S.z := by
  have h := sq_mem_center S.extraspecial (S.ofQG x hx)
  rcases S.mem_center_Q_iff.mp h with h1 | h1
  · left
    have := congrArg (fun w : S.Q => ((w : S.M) : G)) h1
    simpa using this
  · right
    have := congrArg (fun w : S.Q => ((w : S.M) : G)) h1
    simpa using this

theorem pow_four_eq_one {x : G} (hx : x ∈ S.QG) : x ^ 4 = 1 := by
  have h : x ^ 4 = x ^ 2 * x ^ 2 := by rw [← pow_add]
  rcases S.sq_eq_one_or_z hx with h2 | h2 <;> rw [h, h2]
  · rw [mul_one]
  · exact S.z_mul_z

theorem ρ_cl (g : S.M) {x : G} (hx : x ∈ S.QG) :
    ((S.ρ g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl ((g : G) * x * (g : G)⁻¹) := by
  rw [S.cl_of_mem hx, S.ρ_toQt, S.cl_of_mem (S.conj_mem_QG g.2 hx)]
  congr 1

theorem mem_QG_of_cl_conj {g : G} (hg : g ∈ S.M)
    (h : ∀ x ∈ S.QG, S.cl (g * x * g⁻¹) = S.cl x) : g ∈ S.QG := by
  have h1 : S.ρ ⟨g, hg⟩ = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    obtain ⟨x, hx, rfl⟩ := S.exists_cl v
    rw [S.ρ_cl ⟨g, hg⟩ hx]
    exact h x hx
  exact ⟨⟨g, hg⟩, S.mem_Q_of_ρ_eq_one h1, rfl⟩

theorem ρ_eq_one_iff (g : S.M) : S.ρ g = 1 ↔ (g : G) ∈ S.QG := by
  constructor
  · intro h
    exact ⟨g, S.mem_Q_of_ρ_eq_one h, rfl⟩
  · intro h
    exact S.ρ_eq_one_of_mem_Q (S.mem_QG_iff.mp h).2

theorem polarBilin_isRefl : (S.q.polarBilin : LinearMap.BilinForm (ZMod 2) S.Qt).IsRefl :=
  (QuadraticMap.isSymm_polarBilin S.q).isRefl

theorem polarBilin_isAlt : (S.q.polarBilin : LinearMap.BilinForm (ZMod 2) S.Qt).IsAlt := fun v => by
  rw [polarBilin_apply_apply]
  exact CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero S.q v

theorem centralizer_inf_QG_eq_clPre {X : Subgroup G} (hX : X ≤ S.QG) :
    S.QG ⊓ centralizer (X : Set G) =
      S.clPre (LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub X)) := by
  ext y
  simp only [mem_inf, mem_centralizer_iff, mem_clPre, LinearMap.BilinForm.mem_orthogonal_iff,
    polarBilin_apply_apply, SetLike.mem_coe]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun v hv => ?_⟩
    obtain ⟨x, hxX, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
    rw [S.polar_cl_eq_zero_iff hxQ hy]
    exact h x hxX
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun x hxX => ?_⟩
    have := h _ (S.cl_mem_clSub hxX (hX hxX))
    rwa [S.polar_cl_eq_zero_iff (hX hxX) hy] at this

omit [Finite G] in
theorem card_QG_eq_card_Q : Nat.card S.QG = Nat.card S.Q :=
  card_map_of_injective S.M.subtype_injective

omit [Finite G] in
theorem card_clPre (W : Submodule (ZMod 2) S.Qt) : Nat.card (S.clPre W) = 2 * Nat.card W := by
  classical
  let f : S.clPre W →* Multiplicative W :=
    { toFun := fun x => Multiplicative.ofAdd ⟨S.cl x, x.2.2⟩
      map_one' := Multiplicative.toAdd.injective (Subtype.ext S.cl_one)
      map_mul' := fun x y => Multiplicative.toAdd.injective (Subtype.ext (S.cl_mul x.2.1 y.2.1)) }
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨x, hx, hxw⟩ := S.exists_cl ((Multiplicative.toAdd w : W) : S.Qt)
    exact ⟨⟨x, hx, hxw ▸ (Multiplicative.toAdd w).2⟩,
      Multiplicative.toAdd.injective (Subtype.ext hxw)⟩
  have hmem : ∀ x : S.clPre W, x ∈ f.ker ↔ (x : G) = 1 ∨ (x : G) = S.z := by
    intro x
    rw [MonoidHom.mem_ker, ← S.cl_eq_zero_iff x.2.1]
    constructor
    · intro h
      exact congrArg Subtype.val (congrArg Multiplicative.toAdd h)
    · intro h
      exact Multiplicative.toAdd.injective (Subtype.ext h)
  have hker : Nat.card f.ker = 2 := by
    let z' : f.ker := ⟨⟨S.z, S.z_mem_clPre W⟩, (hmem _).mpr (Or.inr rfl)⟩
    refine (Nat.card_eq_two_iff' (1 : f.ker)).mpr ⟨z', fun h => S.z_ne_one ?_, fun y hy => ?_⟩
    · exact congrArg (fun w : f.ker => ((w : S.clPre W) : G)) h
    · rcases (hmem y).mp y.2 with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hy
      · exact Subtype.ext (Subtype.ext h)
  rw [card_eq_card_quotient_mul_card_subgroup f.ker, hker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv, mul_comm]
  rfl

omit [Finite G] in
theorem card_QG_eq : Nat.card S.QG = 2 * Nat.card S.Qt := by
  rw [← S.clPre_top, S.card_clPre]
  exact congrArg (2 * ·) (Nat.card_congr (Equiv.Set.univ S.Qt))

theorem card_Qt : Nat.card S.Qt = 2 ^ finrank (ZMod 2) S.Qt := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem card_submodule (W : Submodule (ZMod 2) S.Qt) :
    Nat.card W = 2 ^ finrank (ZMod 2) W := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

@[expose] noncomputable def width : ℕ := finrank (ZMod 2) S.Qt / 2

theorem finrank_Qt_eq_two_mul_width : finrank (ZMod 2) S.Qt = 2 * S.width := by
  obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank S.polarBilin_isAlt S.q_nondegenerate
  unfold width
  omega

theorem card_Q_eq : Nat.card S.Q = 2 ^ (1 + 2 * S.width) := by
  rw [← S.card_QG_eq_card_Q, S.card_QG_eq, S.card_Qt, S.finrank_Qt_eq_two_mul_width, pow_add,
    pow_one]

theorem finrank_Qt_eq {n : ℕ} (hn : Nat.card S.Q = 2 ^ (1 + 2 * n)) :
    finrank (ZMod 2) S.Qt = 2 * n := by
  rw [S.card_Q_eq] at hn
  rw [S.finrank_Qt_eq_two_mul_width]
  have := Nat.pow_right_injective le_rfl hn
  omega

theorem width_eq {n : ℕ} (hn : Nat.card S.Q = 2 ^ (1 + 2 * n)) : S.width = n := by
  have h1 := S.finrank_Qt_eq hn
  rw [S.finrank_Qt_eq_two_mul_width] at h1
  omega

theorem card_le_of_commute {A : Subgroup G} (hA : A ≤ S.QG)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ 2 ^ (S.width + 1) := by
  set W := S.clSub A
  have hW : W ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin W := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    obtain ⟨x, hxA, hxQ, rfl⟩ := S.mem_clSub_iff.mp hu
    obtain ⟨y, hyA, hyQ, rfl⟩ := S.mem_clSub_iff.mp hv
    rw [polarBilin_apply_apply, S.polar_cl_eq_zero_iff hxQ hyQ]
    exact hcomm x hxA y hyA
  have hdim : finrank (ZMod 2) W ≤ S.width := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
    have h2 := Submodule.finrank_mono hW
    rw [S.finrank_Qt_eq_two_mul_width] at h1
    omega
  calc Nat.card A ≤ Nat.card (S.clPre W) := Subgroup.card_le_of_le (S.le_clPre_clSub hA)
    _ = 2 * 2 ^ finrank (ZMod 2) W := by rw [S.card_clPre, S.card_submodule]
    _ ≤ 2 * 2 ^ S.width := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hdim)
    _ = 2 ^ (S.width + 1) := by rw [pow_succ, mul_comm]

theorem mem_zpowers_iff_of_mul_self {H : Type*} [Group H] {g x : H} (hg : g * g = 1) :
    x ∈ zpowers g ↔ x = 1 ∨ x = g := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      change g ^ (m + m) = 1
      rw [← two_mul, zpow_mul, zpow_two, hg, one_zpow]
    · right
      change g ^ (2 * m + 1) = g
      rw [zpow_add_one, zpow_mul, zpow_two, hg, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

omit [Finite G] in
theorem center_Q_eq_zpowers : center S.Q = zpowers S.zQ := by
  ext x
  rw [S.mem_center_Q_iff, mem_zpowers_iff_of_mul_self]
  exact Subtype.ext (Subtype.ext S.z_mul_z)

omit [Finite G] in
theorem QG_inf_centralizer_eq_zpowers : S.QG ⊓ centralizer (S.QG : Set G) = zpowers S.z := by
  ext x
  rw [mem_zpowers_iff_of_mul_self S.z_mul_z, mem_inf, mem_centralizer_iff]
  constructor
  · rintro ⟨hx, h⟩
    exact S.eq_one_or_z_of_commute hx fun y hy => (h y hy).symm
  · rintro (rfl | rfl)
    · exact ⟨one_mem _, fun y _ => by rw [mul_one, one_mul]⟩
    · exact ⟨S.z_mem_QG, fun y hy => S.z_comm_QG hy⟩

omit [Finite G] in
theorem Q_eq_pCore : S.Q = CFSG.pCore 2 S.M :=
  le_antisymm (le_sSup ⟨S.normal, S.extraspecial.1⟩)
    (S.le_of_normal _ CFSG.pCore_normal CFSG.pCore_isPGroup)

instance instNormalQ : S.Q.Normal := S.normal

@[expose] noncomputable def quotientEquivMbar : S.M ⧸ S.Q ≃* S.Mbar :=
  (QuotientGroup.quotientMulEquivOfEq S.ker_ρ.symm).trans (QuotientGroup.quotientKerEquivRange S.ρ)

theorem quotientEquivMbar_mk (g : S.M) :
    ((S.quotientEquivMbar (g : S.M ⧸ S.Q) : S.Mbar) : S.O) = S.ρ g := rfl

omit [Finite G] in
theorem pCore_quotient_eq_bot : CFSG.pCore 2 (S.M ⧸ S.Q) = ⊥ := by
  set P := CFSG.pCore 2 (S.M ⧸ S.Q)
  set f := QuotientGroup.mk' S.Q
  have hker : IsPGroup 2 f.ker := by
    rw [QuotientGroup.ker_mk']
    exact S.extraspecial.1
  have hle : P.comap f ≤ S.Q :=
    S.le_of_normal _ (CFSG.pCore_normal.comap f) (CFSG.pCore_isPGroup.comap_of_ker_isPGroup f hker)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  exact hle hx

theorem pCore_Mbar_eq_bot : CFSG.pCore 2 S.Mbar = ⊥ := by
  rw [← CFSG.pCore_map_iso 2 S.quotientEquivMbar, S.pCore_quotient_eq_bot, Subgroup.map_bot]

end Setting

end CFSG.LargeExtraspecial
