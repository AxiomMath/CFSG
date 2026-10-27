module

public import CFSG.GH74.GLS.Stage2.Final.ModelLUFam
public import CFSG.GH74.GLS.Stage2.Final.ModelLUTorus
public import CFSG.GH74.GLS.Stage2.Final.ModelCard

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

variable {F : Type} [Field F]

theorem card_BSsub_dvd [Finite F] {M : ModelData F} {N : ℕ}
    (hN : ∀ l m : Fˣ, diagGL (sc2 l) (sc2 m) ∈ M.K4 → l ^ N = 1 ∧ m ^ N = 1) :
    Nat.card ↥(BSsub M) ∣ N := by
  have hcyc : IsCyclic ↥(BSsub M) := isCyclic_BSsub M
  have hexp : Monoid.exponent ↥(BSsub M) ∣ N := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨s, p, rfl⟩
    obtain ⟨⟨l, m⟩, hp⟩ := p
    apply Subtype.ext
    show (bscP M ⟨(l, m), hp⟩) ^ N = 1
    rw [← map_pow, bscP_eq_one_iff]
    exact (hN l m hp).1.trans (hN l m hp).2.symm
  rwa [IsCyclic.exponent_eq_card] at hexp

theorem a0_card_dvd [Finite F] {M : ModelData F} (hG : GoodModel M) {N : ℕ}
    (hN : ∀ l m : Fˣ, diagGL (sc2 l) (sc2 m) ∈ M.K4 → l ^ N = 1 ∧ m ^ N = 1) :
    Nat.card ↥(CFSG.pPrimeCore 2 ↥(Cz (yP M))) ∣ N := by
  have h1 : Nat.card ↥(pPrimeCoreOf 2 (Cg M)) = Nat.card ↥(CFSG.pPrimeCore 2 ↥(Cg M)) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective (CFSG.pPrimeCore 2 ↥(Cg M)) (Cg M).subtype
      (Cg M).subtype_injective).toEquiv).symm
  have h2 : Nat.card ↥(pPrimeCoreOf 2 (Cg M)) ∣ Nat.card ↥(BSsub M) :=
    Subgroup.card_dvd_of_le (pPrimeCoreOf_le_BS hG)
  rw [← h1] at *
  exact dvd_trans h2 (card_BSsub_dvd hN)

theorem luModelData_PG_of [Finite F] {M : ModelData F} (hG : GoodModel M) {q : ℕ} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hmod8 : ¬ ((q : ℤ) ≡ ε [ZMOD 8]))
    (hSL : HasSL2Model ↥M.H2 (fun r => r = q)) (hd : dRefl F ∈ M.U2) {S : Sylow 2 (PG M)}
    (hsyl : LUSyl (PG M) (yP M) S (K1 M) (K2 M) (tP M) (dP M (dRefl F) hd))
    {N : ℕ} (hNeq : (N : ℤ) = (q : ℤ) - ε)
    (hN : ∀ l m : Fˣ, diagGL (sc2 l) (sc2 m) ∈ M.K4 → l ^ N = 1 ∧ m ^ N = 1)
    (hT : Nat.card ↥(torusT M) = N) :
    LUModelData (PG M) q ε (yP M) S (K1 M) (K2 M) (tP M) (dP M (dRefl F) hd) where
  comps := luComps_PG hG q hSL
  syl := hsyl
  eps := hε
  mod8 := hmod8
  A0_dvd := by
    rw [← hNeq]
    exact Int.natCast_dvd_natCast.2 (a0_card_dvd hG hN)
  H_cyc := isCyclic_inf_centralizer M hG.two_ne_zero hd
  H_card := by
    rw [card_inf_centralizer M hG.two_ne_zero hd, hT, hNeq]

theorem sc4_eq_one_or_neg_one {M : ModelData F} (hZ : ZsTwo M) {s : Fˣ} (hs : sc4 s ∈ M.K4) :
    s = 1 ∨ s = -1 := by
  rcases hZ _ (sc4_mem_Zs hs) with h | h
  · left
    apply scalar_injective' (F := F)
    have := congrArg Subtype.val h
    simpa using this
  · right
    apply scalar_injective' (F := F)
    have := congrArg Subtype.val h
    simp only [] at this
    rw [show ((M.xK : ↥M.K4) : GL (Fin 4) F) = xGL F from rfl, xGL_eq_neg_one] at this
    rw [CFSG.GH74.L5U5.scalar_neg_one_eq]
    exact this

theorem dRefl_pow_four : (dRefl F) ^ 4 = 1 := by
  have h := dRefl_mul_self (F := F)
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq (dRefl F), h, _root_.one_pow]

theorem hdet_zs {M : ModelData F} (h2 : (2 : F) ≠ 0) (hZ : ZsTwo M) :
    ∀ s : Fˣ, sc4 s ∈ M.K4 →
      ((dRefl F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det ≠ (s : F) ^ 2 := by
  intro s hs
  rw [det_dRefl]
  rcases sc4_eq_one_or_neg_one hZ hs with rfl | rfl
  · simp only [Units.val_one, one_pow]
    intro h; apply h2; linear_combination -h
  · simp only [Units.val_neg, Units.val_one, neg_sq, one_pow]
    intro h; apply h2; linear_combination -h

theorem torusT_lin (F : Type) [Field F] : torusT (ModelData.lin F) = ⊤ := by
  ext α
  simp only [mem_torusT, Subgroup.mem_top, iff_true]
  exact ((ModelData.lin F).mem_H2 _).2 ⟨Subgroup.mem_top _, det_dg α⟩

theorem card_torusT_lin (F : Type) [Field F] [Finite F] :
    Nat.card ↥(torusT (ModelData.lin F)) = Nat.card F - 1 := by
  rw [torusT_lin, Subgroup.card_top, Nat.card_units]

theorem pow_card_sub_one_lin {F : Type} [Field F] [Finite F] (x : Fˣ) : x ^ (Nat.card F - 1) = 1 := by
  have h := pow_card_eq_one' (G := Fˣ) (x := x)
  rwa [Nat.card_units] at h

theorem luModelData_lin_zs [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F)
    (hq4 : Nat.card F % 4 = 3) :
    ∃ (S : Sylow 2 (PG (ModelData.lin F))) (t u : PG (ModelData.lin F)),
      LUModelData (PG (ModelData.lin F)) (Nat.card F) 1 (yP _) S (K1 _) (K2 _) t u := by
  have hG := goodModel_lin h2 h5
  have hZ := zsTwo_lin hq4
  have hF := luFacts_lin h2
  have hd : dRefl F ∈ (ModelData.lin F).U2 := Subgroup.mem_top _
  have hU : Nat.card ↥(ModelData.lin F).U2 =
      Nat.card ↥(ModelData.lin F).H2 * (Nat.card F - 1) := card_U2_lin
  have hidx := index_E_Cg_eq (ModelData.lin F) (card_Cg_eq hG hZ hU)
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F = 4 * k + 3 := ⟨Nat.card F / 4, by omega⟩
  have hN : ∀ l m : Fˣ, diagGL (sc2 l) (sc2 m) ∈ (ModelData.lin F).K4 →
      l ^ (Nat.card F - 1) = 1 ∧ m ^ (Nat.card F - 1) = 1 :=
    fun l m _ => ⟨pow_card_sub_one_lin l, pow_card_sub_one_lin m⟩
  obtain ⟨S, -, hsyl, -⟩ := exists_luSylow hG hF hd dRefl_pow_four (hdet_zs h2 hZ) hd
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) (o := 2 * k + 1) ⟨k, rfl⟩
    (by rw [hidx]; omega) (hcs_gen _ (N := Nat.card F - 1) (by omega) (fun l m hlm => (hN l m hlm).1))
  exact ⟨S, tP _, dP _ (dRefl F) hd, luModelData_PG_of hG (Or.inl rfl) (by
    intro h
    unfold Int.ModEq at h
    omega) (hasSL2Model_H2_lin F) hd hsyl (N := Nat.card F - 1) (by omega) hN
    (card_torusT_lin F)⟩

theorem card_ker_pow_cyclic {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] {n : ℕ}
    (hn : n ∣ Nat.card G) (hn0 : 0 < n) :
    Nat.card ↥(powMonoidHom n : G →* G).ker = n := by
  classical
  have : Fintype G := Fintype.ofFinite G
  apply le_antisymm
  · have h := IsCyclic.card_pow_eq_one_le (α := G) hn0
    rw [Nat.card_eq_fintype_card]
    have e : Fintype.card ↥(powMonoidHom n : G →* G).ker =
        (Finset.univ.filter fun a : G => a ^ n = 1).card := by
      rw [← Fintype.card_subtype]
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun a => by simp [MonoidHom.mem_ker])
    rw [e]
    exact h
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
    have hdvd : (Nat.card G / n) ∣ orderOf g := by
      rw [hord]; exact Nat.div_dvd_of_dvd hn
    have hh : orderOf (g ^ (Nat.card G / n)) = n := by
      rw [orderOf_pow_of_dvd (by
        have := Nat.div_pos (Nat.le_of_dvd Nat.card_pos hn) hn0
        omega) hdvd, hord]
      exact Nat.div_div_self hn Nat.card_pos.ne'
    have hsub : zpowers (g ^ (Nat.card G / n)) ≤ (powMonoidHom n : G →* G).ker := by
      rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
      show (g ^ (Nat.card G / n)) ^ n = 1
      have := pow_orderOf_eq_one (g ^ (Nat.card G / n))
      rwa [hh] at this
    have := Subgroup.card_le_of_le hsub
    rwa [Nat.card_zpowers, hh] at this

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg in
theorem dg_mem_uni_iff [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (α : Fˣ) :
    dg α ∈ (ModelData.uni hF).U2 ↔ α ^ (p ^ f + 1) = 1 := by
  show dg α ∈ uniGL (unitaryInvolution F p f) 2 ↔ _
  rw [mem_uniGL]
  have hσ : ∀ x, unitaryInvolution F p f x = x ^ (p ^ f) := unitaryInvolution_apply F p f
  have hmat : conjTr (unitaryInvolution F p f) ((dg α : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((dg α : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(α : F) ^ (p ^ f) * α, ((α⁻¹ : Fˣ) : F) ^ (p ^ f) * ((α⁻¹ : Fˣ) : F)] := by
    rw [coe_dg, conjTr_diagonal', Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [hσ]
  rw [hmat, ← Matrix.diagonal_one]
  constructor
  · intro h
    have h' := Matrix.diagonal_injective h
    have h0 := congrFun h' 0
    simp only [Matrix.cons_val_zero] at h0
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rw [pow_succ]
    exact h0
  · intro h
    have h1 : (α : F) ^ (p ^ f) * α = 1 := by
      have := congrArg (fun u : Fˣ => (u : F)) h
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
      rwa [pow_succ] at this
    congr 1
    funext i
    fin_cases i
    · simpa using h1
    · have : ((α⁻¹ : Fˣ) : F) ^ (p ^ f) * ((α⁻¹ : Fˣ) : F) = ((α : F) ^ (p ^ f) * α)⁻¹ := by
        rw [Units.val_inv_eq_inv_val, inv_pow, mul_inv]
      show ((α⁻¹ : Fˣ) : F) ^ (p ^ f) * ((α⁻¹ : Fˣ) : F) = 1
      rw [this, h1, inv_one]

theorem torusT_uni_eq [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) :
    torusT (ModelData.uni hF) = (powMonoidHom (p ^ f + 1) : Fˣ →* Fˣ).ker := by
  ext α
  rw [mem_torusT, (ModelData.uni hF).mem_H2, MonoidHom.mem_ker, dg_mem_uni_iff]
  simp [det_dg]

theorem card_torusT_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) :
    Nat.card ↥(torusT (ModelData.uni hF)) = p ^ f + 1 := by
  rw [torusT_uni_eq]
  refine card_ker_pow_cyclic ?_ (Nat.succ_pos _)
  rw [Nat.card_units, hF]
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by
    have : 0 < p ^ f := pow_pos (Fact.out : Nat.Prime p).pos f
    omega⟩
  rw [hk]
  refine ⟨k, ?_⟩
  apply Nat.sub_eq_of_eq_add
  ring

theorem hN_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) :
    ∀ l m : Fˣ, diagGL (sc2 l) (sc2 m) ∈ (ModelData.uni hF).K4 →
      l ^ (p ^ f + 1) = 1 ∧ m ^ (p ^ f + 1) = 1 := fun l m h => by
  have h' := ((ModelData.uni hF).diagGL_mem_K4_iff).1 h
  exact ⟨(sc2_mem_uni_iff hF l).1 h'.1, (sc2_mem_uni_iff hF m).1 h'.2.1⟩

theorem luModelData_uni_zs [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hq4 : p ^ f % 4 = 1) :
    ∃ (S : Sylow 2 (PG (ModelData.uni hF))) (t u : PG (ModelData.uni hF)),
      LUModelData (PG (ModelData.uni hF)) (p ^ f) (-1) (yP _) S (K1 _) (K2 _) t u := by
  have hG := goodModel_uni hF hp2 h5
  have hZ := zsTwo_uni hF hq4
  have hFu := luFacts_uni hF hp2
  have hd : dRefl F ∈ (ModelData.uni hF).U2 := dRefl_mem_uni
  have hU := card_U2_uni hF hp2
  have hidx := index_E_Cg_eq (ModelData.uni hF) (card_Cg_eq hG hZ hU)
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = 4 * k + 1 := ⟨p ^ f / 4, by omega⟩
  have hN := hN_uni hF
  obtain ⟨S, -, hsyl, -⟩ := exists_luSylow hG hFu hd dRefl_pow_four (hdet_zs hG.two_ne_zero hZ) hd
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) (o := 2 * k + 1) ⟨k, rfl⟩
    (by rw [hidx]; omega)
    (hcs_gen _ (N := p ^ f + 1) (by omega) (fun l m hlm => (hN l m hlm).1))
  exact ⟨S, tP _, dP _ (dRefl F) hd, luModelData_PG_of hG (Or.inr rfl) (by
    intro h
    unfold Int.ModEq at h
    omega) (hasSL2Model_H2_uni hF) hd hsyl (N := p ^ f + 1) (by push_cast; ring) hN
    (card_torusT_uni hF)⟩

@[expose] def dgen (α β : Fˣ) : GL (Fin 2) F where
  val := Matrix.diagonal ![(α : F), (β : F)]
  inv := Matrix.diagonal ![((α⁻¹ : Fˣ) : F), ((β⁻¹ : Fˣ) : F)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

theorem coe_dgen (α β : Fˣ) :
    ((dgen α β : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(α : F), (β : F)] := rfl

theorem dgen_mul (α β γ δ : Fˣ) : (dgen α β : GL (Fin 2) F) * dgen γ δ = dgen (α * γ) (β * δ) := by
  apply Units.ext
  simp only [Units.val_mul, coe_dgen]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem det_dgen (α β : Fˣ) :
    ((dgen α β : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = (α : F) * β := by
  rw [coe_dgen, Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

theorem dgen_neg_one_one : (dgen (-1 : Fˣ) 1 : GL (Fin 2) F) = -dRefl F := by
  apply Units.ext
  have h1 : ((-dRefl F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -!![1, 0; 0, -1] := by
    rw [Units.val_neg, coe_dRefl]
  rw [h1, coe_dgen]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem dgen_inv (α β : Fˣ) : (dgen α β : GL (Fin 2) F)⁻¹ = dgen α⁻¹ β⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [dgen_mul, mul_inv_cancel, mul_inv_cancel]; apply Units.ext; simp [coe_dgen, ← Matrix.diagonal_one])

theorem dgen_pow_four {α β : Fˣ} (hα : α ^ 4 = 1) (hβ : β ^ 4 = 1) :
    (dgen α β : GL (Fin 2) F) ^ 4 = 1 := by
  have : ∀ n : ℕ, (dgen α β : GL (Fin 2) F) ^ n = dgen (α ^ n) (β ^ n) := by
    intro n
    induction n with
    | zero => apply Units.ext; simp [coe_dgen, ← Matrix.diagonal_one]
    | succ n ih => rw [pow_succ, ih, dgen_mul, ← pow_succ, ← pow_succ]
  rw [this, hα, hβ]
  apply Units.ext
  simp [coe_dgen, ← Matrix.diagonal_one]

theorem det_sc4 (c : Fˣ) :
    ((sc4 c : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = (c : F) ^ 4 := by
  simp [sc4, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]

theorem pow_four_of_sc4_mem {M : ModelData F} {s : Fˣ} (hs : sc4 s ∈ M.K4) : s ^ 4 = 1 := by
  have h := ((M.mem_K4 _).1 hs).2
  rw [det_sc4] at h
  apply Units.ext
  simpa using h

theorem units_cases_pow_four {i c : Fˣ} (hii : i * i = -1) (hc : c ^ 4 = 1) :
    c = 1 ∨ c = -1 ∨ c = i ∨ c = -i := by
  have hcc : (c * c) * (c * c) = 1 := by
    rw [← hc, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq]
  rcases units_sq_eq_one hcc with h | h
  · rcases units_sq_eq_one h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · have hi1 : (c * i⁻¹) * (c * i⁻¹) = 1 := by
      calc (c * i⁻¹) * (c * i⁻¹) = (c * c) * (i⁻¹ * i⁻¹) := mul_mul_mul_comm _ _ _ _
        _ = (c * c) * (i * i)⁻¹ := by rw [mul_inv]
        _ = 1 := by rw [h, hii]; simp
    rcases units_sq_eq_one hi1 with h1 | h1
    · right; right; left
      exact (mul_inv_eq_one.1 h1)
    · right; right; right
      have : c = -1 * i := by rw [mul_inv_eq_iff_eq_mul] at h1; exact h1
      rw [this]; simp

theorem card_Zs_four {M : ModelData F} (h2 : (2 : F) ≠ 0) {i : Fˣ} (hii : i * i = -1)
    (hi : sc4 i ∈ M.K4) : Nat.card ↥(Zs M) = 4 := by
  have hneg : (-1 : Fˣ) ≠ 1 := by
    intro h
    have := congrArg (fun u : Fˣ => (u : F)) h
    simp only [Units.val_neg, Units.val_one] at this
    apply h2
    linear_combination -this
  set ζ : ↥M.K4 := ⟨sc4 i, hi⟩ with hζ
  have hζZ : ζ ∈ Zs M := sc4_mem_Zs hi
  have hζ2 : ζ ^ 2 = (⟨sc4 (-1), by
      rw [← hii, map_mul]; exact M.K4.mul_mem hi hi⟩ : ↥M.K4) := by
    apply Subtype.ext
    show (sc4 i) ^ 2 = sc4 (-1)
    rw [sq, ← map_mul, hii]
  have hζ4 : ζ ^ 4 = 1 := by
    have e : ζ ^ 4 = (ζ ^ 2) ^ 2 := pow_mul ζ 2 2
    rw [e, hζ2]
    apply Subtype.ext
    show sc4 (-1) ^ 2 = 1
    rw [sq, ← map_mul]
    have : (-1 : Fˣ) * -1 = 1 := by simp
    rw [this, map_one]
  have hord : orderOf ζ = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := ζ) (by
      intro h
      rw [pow_one, hζ2] at h
      have := congrArg Subtype.val h
      have h' : sc4 (-1 : Fˣ) = sc4 1 := by simpa using this
      exact hneg (scalar_injective' (F := F) h')) (by
      show ζ ^ 4 = 1
      exact hζ4)
    simpa using h
  have hZs : Zs M = Subgroup.zpowers ζ := by
    apply le_antisymm
    · intro s hs
      obtain ⟨c, hc⟩ := mem_Zs.1 hs
      have hsc : sc4 c ∈ M.K4 := by
        have : sc4 c = (s : GL (Fin 4) F) := hc
        rw [this]; exact s.2
      have hc4 := pow_four_of_sc4_mem hsc
      have hs' : s = ⟨sc4 c, hsc⟩ := Subtype.ext hc.symm
      rcases units_cases_pow_four hii hc4 with rfl | rfl | rfl | rfl
      · rw [hs']
        have : (⟨sc4 1, hsc⟩ : ↥M.K4) = 1 := Subtype.ext (by simp)
        rw [this]; exact Subgroup.one_mem _
      · rw [hs']
        have : (⟨sc4 (-1), hsc⟩ : ↥M.K4) = ζ ^ 2 := Subtype.ext (by
          rw [hζ2])
        rw [this]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      · rw [hs']
        exact Subgroup.mem_zpowers _
      · rw [hs']
        have : (⟨sc4 (-i), hsc⟩ : ↥M.K4) = ζ ^ 2 * ζ := Subtype.ext (by
          show sc4 (-i) = (sc4 i) ^ 2 * sc4 i
          rw [sq, ← map_mul, ← map_mul, hii]
          congr 1
          simp)
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) (Subgroup.mem_zpowers _)
    · rw [Subgroup.zpowers_le]; exact hζZ
  rw [hZs, Nat.card_zpowers, hord]

theorem card_Cg_eq_four [Finite F] {M : ModelData F} (hG : GoodModel M)
    (hZ4 : Nat.card ↥(Zs M) = 4) {m : ℕ} (hm : Nat.card ↥M.U2 = Nat.card ↥M.H2 * m) :
    Nat.card ↥(Cg M) = m * Nat.card ↥(K1 M ⊔ K2 M) := by
  have h1 := card_Cg_mul_Zs M
  rw [hZ4, card_Nsub M hG.two_ne_zero, ModelOrd.card_centralizer_yK M hG.two_ne_zero, hm] at h1
  have h2 := two_mul_card_Ebar hG
  have h3 : Nat.card ↥(Cg M) * 4 = 4 * (m * Nat.card ↥(K1 M ⊔ K2 M)) := by
    rw [h1]
    nlinarith [h2]
  omega

theorem dP_dRefl_eq_sq {M : ModelData F} {i : Fˣ} (hii : i * i = -1) (ha₀ : dgen i 1 ∈ M.U2)
    (hd : dRefl F ∈ M.U2) : dP M (dRefl F) hd = (dP M (dgen i 1) ha₀) ^ 2 := by
  have h := diag_inv_mem_K4 M ha₀
  have hK : diagGL (dgen i 1 * dgen i 1) ((dgen i 1)⁻¹ * (dgen i 1)⁻¹) ∈ M.K4 := by
    rw [← diagGL_mul]; exact M.K4.mul_mem h h
  have e : (⟨diagGL (dgen i 1) (dgen i 1)⁻¹, h⟩ : ↥M.K4) * ⟨diagGL (dgen i 1) (dgen i 1)⁻¹, h⟩ =
      ⟨diagGL (dgen i 1 * dgen i 1) ((dgen i 1)⁻¹ * (dgen i 1)⁻¹), hK⟩ :=
    Subtype.ext (diagGL_mul _ _ _ _)
  rw [sq, dP, dP, ← map_mul, e]
  apply (mkP_diag_eq_iff (diag_inv_mem_K4 M hd) hK).2
  refine ⟨-1, ?_, ?_⟩
  · rw [dgen_mul, hii, mul_one, dgen_neg_one_one, sc2_neg_one, neg_one_mul]
  · have hinv : i⁻¹ * i⁻¹ = -1 := by rw [← mul_inv, hii, inv_neg, inv_one]
    rw [dgen_inv, dgen_mul, hinv, inv_one, mul_one, dgen_neg_one_one, sc2_neg_one, neg_one_mul,
      dRefl_inv]

theorem exists_i_of_card [Finite F] (h : Nat.card F % 4 ≠ 3) : ∃ i : Fˣ, i * i = -1 := by
  have : Fintype F := Fintype.ofFinite F
  have hsq : IsSquare (-1 : F) :=
    FiniteField.isSquare_neg_one_iff.2 (by rwa [← Nat.card_eq_fintype_card])
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr.symm)⟩

theorem pow_four_of_sq {i : Fˣ} (hii : i * i = -1) : i ^ 4 = 1 := by
  have : i ^ 4 = (i * i) * (i * i) := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq]
  rw [this, hii]
  simp

theorem det_dgen_ne_sq {M : ModelData F} (h2 : (2 : F) ≠ 0) {i : Fˣ} (hii : i * i = -1) :
    ∀ s : Fˣ, sc4 s ∈ M.K4 →
      ((dgen i 1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det ≠ (s : F) ^ 2 := by
  intro s hs h
  rw [det_dgen] at h
  have h4 := pow_four_of_sc4_mem hs
  have h4' : (s : F) ^ 4 = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) h4
    simpa using this
  have hi2 : (i : F) * i = -1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hii
    simpa using this
  apply h2
  have : (i : F) * i = (s : F) ^ 2 * (s : F) ^ 2 := by
    rw [Units.val_one, mul_one] at h
    rw [h]
  have h5' : (s : F) ^ 2 * (s : F) ^ 2 = 1 := by rw [← pow_add]; exact h4'
  linear_combination hi2 - this - h5'

theorem luModelData_lin_mu4 [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F)
    (hq8 : Nat.card F % 8 = 5) :
    ∃ (S : Sylow 2 (PG (ModelData.lin F))) (t u : PG (ModelData.lin F)),
      LUModelData (PG (ModelData.lin F)) (Nat.card F) 1 (yP _) S (K1 _) (K2 _) t u := by
  have hG := goodModel_lin h2 h5
  have hF := luFacts_lin h2
  obtain ⟨i, hii⟩ := exists_i_of_card (F := F) (by omega)
  have hi4 : i ^ 4 = 1 := pow_four_of_sq hii
  have hd : dRefl F ∈ (ModelData.lin F).U2 := Subgroup.mem_top _
  have ha₀ : dgen i 1 ∈ (ModelData.lin F).U2 := Subgroup.mem_top _
  have hi : sc4 i ∈ (ModelData.lin F).K4 := ((ModelData.lin F).mem_K4 _).2
    ⟨Subgroup.mem_top _, by
      rw [det_sc4]
      have := congrArg (fun u : Fˣ => (u : F)) hi4
      simpa using this⟩
  have hZ4 := card_Zs_four h2 hii hi
  have hU : Nat.card ↥(ModelData.lin F).U2 =
      Nat.card ↥(ModelData.lin F).H2 * (Nat.card F - 1) := card_U2_lin
  have hidx := index_E_Cg_eq (ModelData.lin F) (card_Cg_eq_four hG hZ4 hU)
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F = 8 * k + 5 := ⟨Nat.card F / 8, by omega⟩
  have hN : ∀ l m : Fˣ, diagGL (sc2 l) (sc2 m) ∈ (ModelData.lin F).K4 →
      l ^ (Nat.card F - 1) = 1 ∧ m ^ (Nat.card F - 1) = 1 :=
    fun l m _ => ⟨pow_card_sub_one_lin l, pow_card_sub_one_lin m⟩
  obtain ⟨S, -, hsyl, -⟩ := exists_luSylow hG hF ha₀ (dgen_pow_four hi4 (by simp)) (det_dgen_ne_sq h2 hii) hd
    (by
      rw [dP_dRefl_eq_sq hii ha₀ hd]
      exact Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2))
    (o := 2 * k + 1) ⟨k, rfl⟩
    (by rw [hidx]; omega) (hcs_gen _ (N := Nat.card F - 1) (by omega) (fun l m hlm => (hN l m hlm).1))
  exact ⟨S, tP _, dP _ (dRefl F) hd, luModelData_PG_of hG (Or.inl rfl) (by
    intro h
    unfold Int.ModEq at h
    omega) (hasSL2Model_H2_lin F) hd hsyl (N := Nat.card F - 1) (by omega) hN
    (card_torusT_lin F)⟩

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg in
theorem dgen_mem_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) {i : Fˣ} (hi : i ^ (p ^ f + 1) = 1) :
    (dgen i 1 : GL (Fin 2) F) ∈ (ModelData.uni hF).U2 := by
  show dgen i 1 ∈ uniGL (unitaryInvolution F p f) 2
  rw [mem_uniGL]
  have hσ : ∀ x, unitaryInvolution F p f x = x ^ (p ^ f) := unitaryInvolution_apply F p f
  have hmat : conjTr (unitaryInvolution F p f) ((dgen i 1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((dgen i 1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(i : F) ^ (p ^ f) * i, ((1 : Fˣ) : F) ^ (p ^ f) * ((1 : Fˣ) : F)] := by
    rw [coe_dgen, conjTr_diagonal', Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    fin_cases j <;> simp [hσ]
  rw [hmat, ← Matrix.diagonal_one]
  have h1 : (i : F) ^ (p ^ f) * i = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hi
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    rwa [pow_succ] at this
  congr 1
  funext j
  fin_cases j
  · simpa using h1
  · simp

theorem luModelData_uni_mu4 [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hq8 : p ^ f % 8 = 3) :
    ∃ (S : Sylow 2 (PG (ModelData.uni hF))) (t u : PG (ModelData.uni hF)),
      LUModelData (PG (ModelData.uni hF)) (p ^ f) (-1) (yP _) S (K1 _) (K2 _) t u := by
  have hG := goodModel_uni hF hp2 h5
  have hFu := luFacts_uni hF hp2
  have hcardF : Nat.card F % 4 ≠ 3 := by
    rw [hF, Nat.pow_mod, show p ^ f % 4 = 3 by omega]
    norm_num
  obtain ⟨i, hii⟩ := exists_i_of_card hcardF
  have hi4 := pow_four_of_sq hii
  have hiq : i ^ (p ^ f + 1) = 1 := by
    obtain ⟨m, hm⟩ : ∃ m, p ^ f + 1 = 4 * m := ⟨(p ^ f + 1) / 4, by omega⟩
    rw [hm, pow_mul, hi4, _root_.one_pow]
  have hd : dRefl F ∈ (ModelData.uni hF).U2 := dRefl_mem_uni
  have ha₀ : dgen i 1 ∈ (ModelData.uni hF).U2 := dgen_mem_uni hF hiq
  have hi : sc4 i ∈ (ModelData.uni hF).K4 :=
    sc4_mem_of_sc2_mem ((sc2_mem_uni_iff hF i).2 hiq) (by rw [hii]; simp)
  have hZ4 := card_Zs_four hG.two_ne_zero hii hi
  have hU := card_U2_uni hF hp2
  have hidx := index_E_Cg_eq (ModelData.uni hF) (card_Cg_eq_four hG hZ4 hU)
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = 8 * k + 3 := ⟨p ^ f / 8, by omega⟩
  have hN := hN_uni hF
  obtain ⟨S, -, hsyl, -⟩ := exists_luSylow hG hFu ha₀ (dgen_pow_four hi4 (by simp))
    (det_dgen_ne_sq hG.two_ne_zero hii) hd
    (by
      rw [dP_dRefl_eq_sq hii ha₀ hd]
      exact Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2))
    (o := 2 * k + 1) ⟨k, rfl⟩
    (by rw [hidx]; omega)
    (hcs_gen _ (N := p ^ f + 1) (by omega) (fun l m hlm => (hN l m hlm).1))
  exact ⟨S, tP _, dP _ (dRefl F) hd, luModelData_PG_of hG (Or.inr rfl) (by
    intro h
    unfold Int.ModEq at h
    omega) (hasSL2Model_H2_uni hF) hd hsyl (N := p ^ f + 1) (by push_cast; ring) hN
    (card_torusT_uni hF)⟩

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
