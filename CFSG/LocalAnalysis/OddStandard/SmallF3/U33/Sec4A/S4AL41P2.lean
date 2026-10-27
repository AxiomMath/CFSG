module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41GPh
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41P2A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4A

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

private def omegaOne (W : Subgroup G) (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) : Subgroup G where
  carrier := {w | w ∈ W ∧ w * w = 1}
  mul_mem' := by
    rintro a b ⟨haW, ha⟩ ⟨hbW, hb⟩
    refine ⟨W.mul_mem haW hbW, ?_⟩
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hW b hbW a haW]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  one_mem' := ⟨W.one_mem, mul_one 1⟩
  inv_mem' := by
    rintro a ⟨haW, ha⟩
    refine ⟨W.inv_mem haW, ?_⟩
    calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      _ = 1 := by rw [ha, inv_one]

private theorem mem_omegaOne {W : Subgroup G} {hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a} {w : G} :
    w ∈ omegaOne W hW ↔ w ∈ W ∧ w * w = 1 := Iff.rfl

private def sqGrp (W : Subgroup G) (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) : Subgroup G where
  carrier := {a | ∃ w ∈ W, a = w * w}
  mul_mem' := by
    rintro a b ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
    refine ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, ?_⟩
    calc w₁ * w₁ * (w₂ * w₂) = w₁ * (w₁ * w₂) * w₂ := by group
      _ = w₁ * (w₂ * w₁) * w₂ := by rw [hW w₁ hw₁ w₂ hw₂]
      _ = w₁ * w₂ * (w₁ * w₂) := by group
  one_mem' := ⟨1, W.one_mem, (mul_one 1).symm⟩
  inv_mem' := by
    rintro a ⟨w, hw, rfl⟩
    exact ⟨w⁻¹, W.inv_mem hw, by group⟩

private theorem mem_sqGrp {W : Subgroup G} {hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a} {a : G} :
    a ∈ sqGrp W hW ↔ ∃ w ∈ W, a = w * w := Iff.rfl

private theorem p2_commW (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ a ∈ ctxW t x₁ x₂, ∀ b ∈ ctxW t x₁ x₂, a * b = b * a := by
  haveI : IsMulCommutative (ctxW t x₁ x₂) := h.abelian_W
  intro a ha b hb
  simpa using congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ctxW t x₁ x₂) ⟨b, hb⟩)

private theorem p2_ctxE_le_ctxW (h : Ctx0 t L S x₁ x₂ lam rho) :
    ctxE t x₁ x₂ ≤ ctxW t x₁ x₂ := by
  have hy : x₁ ^ 2 ∈ baseGrp x₁ x₂ := by
    rw [baseGrp]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
  have hz : (x₁ * x₂) ^ 2 ∈ baseGrp x₁ x₂ := by
    rw [baseGrp]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2
  rw [ctxE]
  refine (Subgroup.closure_le (K := ctxW t x₁ x₂)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact Subgroup.mem_sup_left h.hyp.mem_twoCore
  · exact Subgroup.mem_sup_right hy
  · exact Subgroup.mem_sup_right hz

theorem l41_omega_ctxW_le (h : L41GPh1 t L S x₁ x₂ lam rho) {w : G}
    (hw : w ∈ ctxW t x₁ x₂) (hw2 : w * w = 1) : w ∈ ctxE t x₁ x₂ := by
  have hcommW := p2_commW h.toCtx0
  have hnorm : NormalIn (omegaOne (ctxW t x₁ x₂) hcommW) S := by
    refine ⟨fun e he => h.basic.normal_W.1 (mem_omegaOne.mp he).1, ?_⟩
    intro s hs e he
    obtain ⟨heW, he2⟩ := mem_omegaOne.mp he
    refine mem_omegaOne.mpr ⟨h.basic.normal_W.2 s hs e heW, ?_⟩
    calc s * e * s⁻¹ * (s * e * s⁻¹) = s * (e * e) * s⁻¹ := by group
      _ = 1 := by rw [he2]; group
  have helem : CFSG.Open.IsElemAbelian 2 (omegaOne (ctxW t x₁ x₂) hcommW) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (hcommW a (mem_omegaOne.mp a.2).1 b (mem_omegaOne.mp b.2).1)
    · rw [pow_two]
      exact (mem_omegaOne.mp hx).2
  exact h.basic.normal_elem_le _ hnorm helem (mem_omegaOne.mpr ⟨hw, hw2⟩)

theorem l41_p2_ctxE_sq (h : Ctx0 t L S x₁ x₂ lam rho) {p : G} (hp : p ∈ twoCore t)
    (hpp : p * p = t) : ∀ a ∈ ctxE t x₁ x₂, ∃ w ∈ ctxW t x₁ x₂, a = w * w := by
  have hcommW := p2_commW h
  have hx₁b : x₁ ∈ baseGrp x₁ x₂ := by
    rw [baseGrp]
    exact Subgroup.subset_closure (by simp)
  have hx₂b : x₂ ∈ baseGrp x₁ x₂ := by
    rw [baseGrp]
    exact Subgroup.subset_closure (by simp)
  have hx₁ : x₁ ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right hx₁b
  have hx₂ : x₂ ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right hx₂b
  have hle : ctxE t x₁ x₂ ≤ sqGrp (ctxW t x₁ x₂) hcommW := by
    rw [ctxE]
    refine (Subgroup.closure_le _).mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact mem_sqGrp.mpr ⟨p, Subgroup.mem_sup_left hp, hpp.symm⟩
    · exact mem_sqGrp.mpr ⟨x₁, hx₁, pow_two x₁⟩
    · exact mem_sqGrp.mpr ⟨x₁ * x₂, (ctxW t x₁ x₂).mul_mem hx₁ hx₂, pow_two _⟩
  exact fun a ha => mem_sqGrp.mp (hle ha)

theorem l41_p2_exists_u (h : L41GPh4 t L S x₁ x₂ lam rho) :
    ∃ u : G, u ∈ normalizer ((l41V S t x₁ x₂ : Subgroup G) : Set G) ∧
      u ∉ l41N t x₁ x₂ := by
  obtain ⟨𝒮, h𝒮⟩ := exists_sylow_gt h.normalizerFacts.V_pGroup h.normalizerFacts.V_not_sylow
  obtain ⟨u, hu𝒮, hun, hunV⟩ :=
    exists_mem_normalizer_not_mem (show IsPGroup 2 (𝒮 : Subgroup G) from 𝒮.isPGroup') h𝒮
  refine ⟨u, hun, fun huN => hunV ?_⟩
  have hK_le : l41V S t x₁ x₂ ⊔ zpowers u ≤ l41N t x₁ x₂ :=
    sup_le h.normalizerFacts.V_le (Subgroup.zpowers_le.mpr huN)
  have hK𝒮 : l41V S t x₁ x₂ ⊔ zpowers u ≤ (𝒮 : Subgroup G) :=
    sup_le h𝒮.le (Subgroup.zpowers_le.mpr hu𝒮)
  have hKp : IsPGroup 2 (l41V S t x₁ x₂ ⊔ zpowers u : Subgroup G) :=
    (show IsPGroup 2 (𝒮 : Subgroup G) from 𝒮.isPGroup').to_le hK𝒮
  have hEq := eq_of_isPGroup_of_odd_relIndex le_sup_left hK_le hKp h.normalizerFacts.V_sylow
  have hmem : u ∈ l41V S t x₁ x₂ ⊔ zpowers u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  rwa [hEq] at hmem

theorem l41_p2_false (h : L41GPh4 t L S x₁ x₂ lam rho) {p : G} (hp : p ∈ twoCore t)
    (hpp : p * p = t) {u : G}
    (hu : u ∈ normalizer ((l41V S t x₁ x₂ : Subgroup G) : Set G))
    (huN : u ∉ l41N t x₁ x₂) : False := by
  have hcommW := p2_commW h.toCtx0
  have hAW : ctxE t x₁ x₂ ≤ ctxW t x₁ x₂ := p2_ctxE_le_ctxW h.toCtx0
  have hWV : ctxW t x₁ x₂ ≤ l41V S t x₁ x₂ :=
    h.basic.normal_W.1.trans (le_sup_right : S ≤ l41O2 t x₁ x₂ ⊔ S)
  have huV : ∀ v, v ∈ l41V S t x₁ x₂ → u * v * u⁻¹ ∈ l41V S t x₁ x₂ := fun v hv =>
    ((Subgroup.mem_set_normalizer_iff).mp hu v).mp hv
  have hAexp : ∀ a ∈ ctxE t x₁ x₂, a * a = 1 := fun a ha => by
    have h2 := h.basic.A_elem.1.2 a ha
    rwa [pow_two] at h2
  have hAcard : Nat.card (ctxE t x₁ x₂) = 8 := h.basic.A_elem.2
  let B : Subgroup G := (ctxE t x₁ x₂).map (MulAut.conj u).toMonoidHom
  have hBmem : ∀ b, b ∈ B ↔ ∃ a ∈ ctxE t x₁ x₂, u * a * u⁻¹ = b := by
    intro b
    simp [B, Subgroup.mem_map, MulAut.conj_apply]
  have hBcard : Nat.card B = 8 := by
    rw [← hAcard]
    exact Subgroup.card_map_of_injective (MulAut.conj u).injective
  have hBexp : ∀ b ∈ B, b * b = 1 := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := (hBmem b).mp hb
    calc u * a * u⁻¹ * (u * a * u⁻¹) = u * (a * a) * u⁻¹ := by group
      _ = 1 := by rw [hAexp a ha]; group
  have hBsq : ∀ b ∈ B, ∃ v ∈ l41V S t x₁ x₂, b = v * v := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := (hBmem b).mp hb
    obtain ⟨w, hw, rfl⟩ := l41_p2_ctxE_sq h.toCtx0 hp hpp a ha
    exact ⟨u * w * u⁻¹, huV w (hWV hw), by group⟩
  have hBV : B ≤ l41V S t x₁ x₂ := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := hBsq b hb
    exact (l41V S t x₁ x₂).mul_mem hv hv
  have hBnotW : ¬ B ≤ ctxW t x₁ x₂ := by
    intro hBW
    have hBA : B ≤ ctxE t x₁ x₂ := fun b hb =>
      l41_omega_ctxW_le h.toL41GPh1 (hBW hb) (hBexp b hb)
    have hBeq : B = ctxE t x₁ x₂ :=
      Subgroup.eq_of_le_of_card_ge hBA (le_of_eq (by rw [hBcard, hAcard]))
    apply huN
    refine mem_normalizer_of_conj_mem (fun a ha => ?_)
    have hmem : u * a * u⁻¹ ∈ B := (hBmem _).mpr ⟨a, ha, rfl⟩
    rwa [hBeq] at hmem
  obtain ⟨φ, -, hker⟩ := h.normalizerFacts.quot_V
  have hD4 : 4 ≤ Nat.card (B ⊓ ctxW t x₁ x₂ : Subgroup G) := by
    have h2 := card_le_two_mul_inf_of_sq_dihedral hBV φ hker hBsq
    omega
  obtain ⟨b₀, hb₀B, hb₀W⟩ := Set.not_subset.mp hBnotW
  obtain ⟨a₀, ha₀A, rfl⟩ := (hBmem b₀).mp hb₀B
  obtain ⟨w₀, hw₀W, rfl⟩ := l41_p2_ctxE_sq h.toCtx0 hp hpp a₀ ha₀A
  have hv₀V : u * w₀ * u⁻¹ ∈ l41V S t x₁ x₂ := huV w₀ (hWV hw₀W)
  have hv₀N : u * w₀ * u⁻¹ ∈ normalizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) :=
    h.normalizerFacts.V_le hv₀V
  have hfix : B ⊓ ctxW t x₁ x₂ ≤
      ctxE t x₁ x₂ ⊓ centralizer ({u * w₀ * u⁻¹} : Set G) := by
    intro d hd
    obtain ⟨hdB, hdW⟩ := Subgroup.mem_inf.mp hd
    refine Subgroup.mem_inf.mpr ⟨l41_omega_ctxW_le h.toL41GPh1 hdW (hBexp d hdB), ?_⟩
    obtain ⟨a, haA, rfl⟩ := (hBmem d).mp hdB
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hc := hcommW w₀ hw₀W a (hAW haA)
    calc u * w₀ * u⁻¹ * (u * a * u⁻¹) = u * (w₀ * a) * u⁻¹ := by group
      _ = u * (a * w₀) * u⁻¹ := by rw [hc]
      _ = u * a * u⁻¹ * (u * w₀ * u⁻¹) := by group
  have hC4 : 4 ≤ Nat.card (ctxE t x₁ x₂ ⊓ centralizer ({u * w₀ * u⁻¹} : Set G) : Subgroup G) :=
    hD4.trans (Subgroup.card_le_of_le hfix)
  have hsq := sq_mem_centralizer_of_four_le_card_fixed hAexp hAcard hv₀N hC4
  apply hb₀W
  rw [SetLike.mem_coe, ← h.basic.cent_A, Subgroup.mem_centralizer_iff]
  intro a ha
  have e : u * (w₀ * w₀) * u⁻¹ = (u * w₀ * u⁻¹) * (u * w₀ * u⁻¹) := by group
  rw [e]
  exact hsq a ha

theorem l41_p2_of (h : L41GPh4 t L S x₁ x₂ lam rho) : Lemma4_3Concl t := by
  by_contra hne
  have hP4 : Nat.card (twoCore t) = 4 := by
    rcases card_twoCore_cases h.hyp with h2 | h4 | h8
    · exact absurd (twoCore_eq_zpowers_of_card_eq_two h.hyp h2) hne
    · exact h4
    · have h3 := h.fusion.card_P_le
      omega
  obtain ⟨p, hp, hpp⟩ := exists_sq_root_of_four_le_card h.hyp (by omega)
  obtain ⟨u, hu, huN⟩ := l41_p2_exists_u h
  exact l41_p2_false h hp hpp hu huN

end S4A

theorem l41_p2_holds : L41P2Stmt :=
  fun h => S4A.l41_p2_of h.toG

end CFSG.OddStandard.SmallF3.HarrisU33
