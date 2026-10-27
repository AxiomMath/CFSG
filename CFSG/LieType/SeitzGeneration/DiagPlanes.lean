module

public import CFSG.LieType.SeitzGeneration.ThreeIndep
public import CFSG.LieType.SeitzGeneration.InnerSymplecticThree
public import CFSG.LieType.SeitzGeneration.NonabLinear

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.KFU

section Abstract

variable {G Q : Type*} [Group G] [Group Q]

theorem exists_zpow_pair_of_mem_closure {a b : G} (hab : Commute a b)
    {x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) : ∃ i j : ℤ, x = a ^ i * b ^ j := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨i, j, rfl⟩ := ihx
    obtain ⟨i', j', rfl⟩ := ihy
    refine ⟨i + i', j + j', ?_⟩
    rw [zpow_add, zpow_add]
    have h : b ^ j * a ^ i' = a ^ i' * b ^ j := (hab.symm.zpow_zpow j i').eq
    calc a ^ i * b ^ j * (a ^ i' * b ^ j') = a ^ i * (b ^ j * a ^ i') * b ^ j' := by group
      _ = a ^ i * a ^ i' * (b ^ j * b ^ j') := by rw [h]; group
  | inv x _ ih =>
    obtain ⟨i, j, rfl⟩ := ih
    refine ⟨-i, -j, ?_⟩
    rw [mul_inv_rev, zpow_neg, zpow_neg]
    exact (hab.symm.zpow_zpow j i).inv_inv.eq

theorem plane_of_lifts (π : G →* Q) {p : ℕ} (hp : p.Prime) {a b : G} (hab : Commute a b)
    (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hind : ∀ i j : ℤ, π (a ^ i * b ^ j) = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) :
    IsElemAbelian p (Subgroup.closure ({π a, π b} : Set Q)) ∧
      Nat.card (Subgroup.closure ({π a, π b} : Set Q)) = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hπa : π a ≠ 1 := fun h => by
    have := (hind 1 0 (by simpa using h)).1
    exact hp.one_lt.ne' (Nat.dvd_one.1 (by exact_mod_cast this))
  have hπb : π b ≠ 1 := fun h => by
    have := (hind 0 1 (by simpa using h)).2
    exact hp.one_lt.ne' (Nat.dvd_one.1 (by exact_mod_cast this))
  have hpa : π a ^ p = 1 := by rw [← map_pow, ha, map_one]
  have hpb : π b ^ p = 1 := by rw [← map_pow, hb, map_one]
  have hcomm : Commute (π a) (π b) := hab.map π
  have hindπ : π b ∉ Subgroup.zpowers (π a) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : π (a ^ k * b ^ (-1 : ℤ)) = 1 := by
      rw [map_mul, map_zpow, map_zpow, hk, zpow_neg_one, mul_inv_cancel]
    have := (hind k (-1) h1).2
    exact hp.one_lt.ne' (Nat.dvd_one.1 (by exact_mod_cast dvd_neg.1 this))
  refine ⟨isElemAbelian_closure_of_comm ?_ ?_, card_closure_pair' hp hcomm
    (orderOf_eq_prime hpa hπa) (orderOf_eq_prime hpb hπb) hindπ⟩
  · intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      first | exact Commute.refl _ | exact hcomm | exact hcomm.symm
  · intro x hx
    rcases hx with rfl | rfl
    · exact hpa
    · exact hpb

end Abstract

section Linear

variable {F : Type} [Field F] {n p : ℕ}

@[expose] def dsl (ζ : Fˣ) (hn : 5 ≤ n) (k : Fin 3) : Matrix.SpecialLinearGroup (Fin n) F :=
  diagSLn (wt ζ hn k) (prod_wt ζ hn k)

theorem toGL_dsl (ζ : Fˣ) (hn : 5 ≤ n) (k : Fin 3) :
    Matrix.SpecialLinearGroup.toGL (dsl (F := F) ζ hn k) = diagU (wt ζ hn k) :=
  toGL_diagSLn _ _

theorem dsl_comm (ζ : Fˣ) (hn : 5 ≤ n) (a b : Fin 3) :
    Commute (dsl (F := F) ζ hn a) (dsl (F := F) ζ hn b) := by
  apply toGL_injective'
  rw [map_mul, map_mul, toGL_dsl, toGL_dsl, diagU_mul, diagU_mul, mul_comm]

theorem dsl_pow {ζ : Fˣ} (hζp : ζ ^ p = 1) (hn : 5 ≤ n) (a : Fin 3) :
    dsl (F := F) ζ hn a ^ p = 1 := by
  apply toGL_injective'
  rw [map_pow, map_one, toGL_dsl, diagU_pow, wt_pow hζp hn a, diagU_one]

theorem dsl_prod_center {ζ : Fˣ} (hζ : orderOf ζ = p) (hn : 5 ≤ n) {i j k : ℤ}
    (h : dsl (F := F) ζ hn 0 ^ i * dsl (F := F) ζ hn 1 ^ j * dsl (F := F) ζ hn 2 ^ k ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) :
    (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j ∧ (p : ℤ) ∣ k := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have e : ∀ (d : Fin n → Fˣ) (m : ℤ), (diagU d : GL (Fin n) F) ^ m = diagU (d ^ m) :=
    fun d m => (map_zpow diagUHom d m).symm
  have hg : Matrix.SpecialLinearGroup.toGL (dsl (F := F) ζ hn 0 ^ i * dsl (F := F) ζ hn 1 ^ j *
      dsl (F := F) ζ hn 2 ^ k) =
      diagU (wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) := by
    rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow, toGL_dsl, toGL_dsl, toGL_dsl, e, e, e,
      diagU_mul, diagU_mul]
  refine scalar_wt hζ hn fun l l' => Units.ext ?_
  have hl : ∀ l : Fin n, ((wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) l : F) = r := fun l => by
    have h1 := congrArg
      (fun g : GL (Fin n) F => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) l l) hg
    have h2 := congrArg (fun A : Matrix (Fin n) (Fin n) F => A l l) hr
    simp only [diagU_apply_same] at h1
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h2
    exact h1.symm.trans h2.symm
  exact (hl l).trans (hl l').symm

end Linear

section LinearPlane

variable {F : Type} [Field F] [Finite F] {n p : ℕ}

theorem diagSLn_mem_stabSub (w : Fin n → Fˣ) (hw : ∏ i, w i = 1) (i₀ : Fin n) :
    diagSLn (F := F) w hw ∈ stabSub (Submodule.span F {(Pi.single i₀ 1 : Fin n → F)}) := by
  rw [mem_stabSub]
  intro v hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  refine Submodule.mem_span_singleton.2 ⟨(w i₀ : F) * c, ?_⟩
  ext x
  have h : ((diagSLn (F := F) w hw : Matrix.SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = Matrix.diagonal fun i => (w i : F) := rfl
  rw [h, Matrix.mulVec_diagonal]
  by_cases hx : x = i₀
  · subst hx
    simp
  · simp [hx]

theorem exists_plane_psl_diag (hn : 5 ≤ n) (hp : p.Prime) (hpq : p ∣ Nat.card F - 1) :
    ∃ E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F), IsElemAbelian p E ∧
      Nat.card E = p ^ 2 ∧
      Subgroup.closure {k : Matrix.ProjectiveSpecialLinearGroup (Fin n) F |
        ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p (by rwa [Nat.card_units] : p ∣ Nat.card Fˣ)
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hind : ∀ i j : ℤ, toPSL (dsl (F := F) ζ hn 0 ^ i * dsl (F := F) ζ hn 1 ^ j) = 1 →
      (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := fun i j h => by
    have := dsl_prod_center hζ hn (i := i) (j := j) (k := 0)
      (by simpa using mem_center_iff_toPSL_eq_one.2 h)
    exact ⟨this.1, this.2.1⟩
  obtain ⟨hE, hcard⟩ := plane_of_lifts toPSL hp (dsl_comm ζ hn 0 1) (dsl_pow hζp hn 0)
    (dsl_pow hζp hn 1) hind
  refine ⟨_, hE, hcard, ?_⟩
  let i₀ : Fin n := ⟨0, hn0⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hne : i₁ ≠ i₀ := fun h => by simpa [i₀, i₁] using congrArg Fin.val h
  have hW0 : Submodule.span F {(Pi.single i₀ 1 : Fin n → F)} ≠ ⊥ := by
    intro h
    have h2 := congrFun (Submodule.span_singleton_eq_bot.1 h) i₀
    simp at h2
  have hWt : Submodule.span F {(Pi.single i₀ 1 : Fin n → F)} ≠ ⊤ := by
    intro h
    have hm : (Pi.single i₁ 1 : Fin n → F) ∈ Submodule.span F {(Pi.single i₀ 1 : Fin n → F)} :=
      h ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    have h2 := congrFun hc i₁
    simp [hne] at h2
  exact closure_centralizers_psl_of_reducible hp (natCast_ne_zero_of_dvd_card_sub_one hp hpq)
    (natCast_card_center_ne_zero hn0) _
    (fun x hx y hy => congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hE.2 hcard hW0 hWt
    (stable_of_gens le_rfl (diagSLn_mem_stabSub _ _ i₀) (diagSLn_mem_stabSub _ _ i₀))

end LinearPlane

theorem innerEx_linear_diag {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} (hp : p.Prime) (hpq : p ∣ q.card - 1)
    (hm : 4 ≤ m)
    (hex : ∃ E : Subgroup (MulAut (Cat ⟨.A m q, hv⟩)), IsElemAbelian p E ∧
      Nat.card E = p ^ 2 ∧ InnerPlane ⟨.A m q, hv⟩ p E) :
    ∃ E : Subgroup (MulAut (Cat ⟨.A m q, hv⟩)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane ⟨.A m q, hv⟩ p E ∧ PlaneGen E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hfour : 3 ≤ m + 1 ∨ ∃ s : Finset (GaloisField q.p q.exponent), s.card = 4 :=
    Or.inl (by omega)
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) hfour).2.1
  have : IsSimpleGroup (Cat ⟨.A m q, hv⟩) := MulEquiv.isSimpleGroup e
  obtain ⟨E₀, -, hE₀c, hE₀⟩ := hex
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.A m q, hv⟩)
    (range_conj_ne_bot_of_inner hp hE₀c hE₀)
  obtain ⟨Ē, hĒ, hĒc, hĒgen⟩ := exists_plane_psl_diag (F := GaloisField q.p q.exponent)
    (n := m + 1) (by omega) hp (by rw [hcardF]; exact hpq)
  exact exists_planeGen_of_model hinj e hĒ hĒc hĒgen

end CFSG.LieType.SeitzGeneration
