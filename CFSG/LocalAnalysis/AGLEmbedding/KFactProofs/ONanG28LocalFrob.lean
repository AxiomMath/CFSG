module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Code
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Gen
public import CFSG.RankThree.PartTwo.KFacts.AutG2

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.Quasithin.B42G2Id CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Timmesfeld.RankTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.Sec4.Item434G28

section Phi


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

@[expose] noncomputable def sig0 : K ≃+* K := frobeniusEquiv K 2

theorem sig0_apply (c : K) : sig0 c = c ^ 2 := by
  simp [sig0, frobeniusEquiv_apply, frobenius_def]

@[expose] noncomputable def phi : MulAut (adjointGroup .G2 K) := g2FieldHom K sig0

theorem xPar_single_eq_adjX (i : Fin Tag.G2.rank) (c : K) :
    xPar (rootOperatorFamily .G2) (Pi.single i 1) c = adjX .G2 K i c := by
  apply Subtype.ext
  apply Units.ext
  have h2 : endHom K (xPar (rootOperatorFamily .G2) (Pi.single i 1) c) = xOp .G2 K i c := by
    rw [xPar_simple, endHom_xElt]
  exact h2.trans (coe_xUnit ..).symm

theorem xPar_neg_single_eq_adjY (i : Fin Tag.G2.rank) (c : K) :
    xPar (rootOperatorFamily .G2) (-Pi.single i 1) c = adjY .G2 K i c := by
  apply Subtype.ext
  apply Units.ext
  have h2 : endHom K (xPar (rootOperatorFamily .G2) (-Pi.single i 1) c) = yOp .G2 K i c := by
    rw [xPar_neg_simple, endHom_yElt]
  exact h2.trans (coe_yUnit ..).symm

theorem phi_xPar_single (i : Fin Tag.G2.rank) (c : K) :
    phi (xPar (rootOperatorFamily .G2) (Pi.single i 1) c) =
      xPar (rootOperatorFamily .G2) (Pi.single i 1) (sig0 c) := by
  rw [xPar_single_eq_adjX, xPar_single_eq_adjX, phi, g2FieldHom]
  simp [exactNormalAut_zero_adjX]

theorem phi_xPar_neg_single (i : Fin Tag.G2.rank) (c : K) :
    phi (xPar (rootOperatorFamily .G2) (-Pi.single i 1) c) =
      xPar (rootOperatorFamily .G2) (-Pi.single i 1) (sig0 c) := by
  rw [xPar_neg_single_eq_adjY, xPar_neg_single_eq_adjY, phi, g2FieldHom]
  simp [exactNormalAut_zero_adjY]

theorem tau_sig0 (c : K) : M.τ (sig0 c) = frobGF8 (M.τ c) := by
  rw [sig0_apply, map_pow]
  rfl

theorem toNat_sq (a : GF8) : (a ^ 2).toNat = GF8.mulNat a.toNat a.toNat := by
  have h : GF8.mulNat a.val.val a.val.val < 8 := mulNat_lt' (toNat_lt' a) (toNat_lt' a)
  rw [sq]
  show (GF8.ofNat' (GF8.mulNat a.toNat a.toNat)).val.val = _
  exact Nat.mod_eq_of_lt h

theorem xPar_rootVec_eq' (r : ℕ) (c : K) :
    xPar (rootOperatorFamily .G2) (rootVec r) c = M.letterElt (8 * r + (M.τ c).toNat) := by
  have ht := toNat_lt' (M.τ c)
  have e1 : (8 * r + (M.τ c).toNat) / 8 = r := by omega
  have e2 : (8 * r + (M.τ c).toNat) % 8 = (M.τ c).toNat := by omega
  simp only [G28Model.letterElt, e1, e2, ofNat'_toNat', RingEquiv.symm_apply_apply]

theorem rho_phi_xPar (r : ℕ) (hr : r = 0 ∨ r = 5 ∨ r = 6 ∨ r = 11) (c : K) :
    M.rho (phi (xPar (rootOperatorFamily .G2) (rootVec r) c)) =
      frobM (M.rho (xPar (rootOperatorFamily .G2) (rootVec r) c)) := by
  have r5 : rootVec 5 = hexRoot 5 := by decide
  have r0 : rootVec 0 = hexRoot 0 := by decide
  have r11 : rootVec 11 = -hexRoot 5 := by decide
  have r6 : rootVec 6 = -hexRoot 0 := by decide
  have hphi : phi (xPar (rootOperatorFamily .G2) (rootVec r) c) =
      xPar (rootOperatorFamily .G2) (rootVec r) (sig0 c) := by
    rcases hr with rfl | rfl | rfl | rfl
    · rw [r0, ← single_one_eq_hexRoot]
      exact phi_xPar_single _ c
    · rw [r5, ← single_zero_eq_hexRoot]
      exact phi_xPar_single _ c
    · rw [r6, ← single_one_eq_hexRoot]
      exact phi_xPar_neg_single _ c
    · rw [r11, ← single_zero_eq_hexRoot]
      exact phi_xPar_neg_single _ c
  rw [hphi, xPar_rootVec_eq' M r (sig0 c), xPar_rootVec_eq' M r c, M.rho_letterElt,
    M.rho_letterElt, ← decode_frobCode (valid_letterCode _), frobCode_letterCode]
  have ht := toNat_lt' (M.τ c)
  have e1 : (8 * r + (M.τ c).toNat) / 8 = r := by omega
  have e2 : (8 * r + (M.τ c).toNat) % 8 = (M.τ c).toNat := by omega
  rw [e1, e2, tau_sig0, show frobGF8 (M.τ c) = M.τ c ^ 2 from rfl, toNat_sq]

theorem rho_phi (h : adjointGroup .G2 K) : M.rho (phi h) = frobM (M.rho h) := by
  let H : Subgroup (adjointGroup .G2 K) :=
    { carrier := {h | M.rho (phi h) = frobM (M.rho h)}
      mul_mem' := fun {a b} ha hb => by
        show M.rho (phi (a * b)) = frobM (M.rho (a * b))
        have ha' : M.rho (phi a) = frobM (M.rho a) := ha
        have hb' : M.rho (phi b) = frobM (M.rho b) := hb
        rw [map_mul, map_mul, map_mul, ha', hb', frobM_mul]
      one_mem' := by
        show M.rho (phi 1) = frobM (M.rho 1)
        simp [frobM_one]
      inv_mem' := fun {a} ha => by
        show M.rho (phi a⁻¹) = frobM (M.rho a⁻¹)
        have ha' : M.rho (phi a) = frobM (M.rho a) := ha
        have h2 : M.rho (phi a) * M.rho (phi a⁻¹) = 1 := by
          rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
        have h3 : frobM (M.rho a⁻¹) * frobM (M.rho a) = 1 := by
          rw [← frobM_mul, ← map_mul, inv_mul_cancel, map_one, frobM_one]
        rw [ha'] at h2
        calc M.rho (phi a⁻¹) = (frobM (M.rho a⁻¹) * frobM (M.rho a)) * M.rho (phi a⁻¹) := by
              rw [h3, one_mul]
          _ = frobM (M.rho a⁻¹) * (frobM (M.rho a) * M.rho (phi a⁻¹)) := by rw [mul_assoc]
          _ = frobM (M.rho a⁻¹) := by rw [h2, mul_one] }
  have r5 : rootVec 5 = hexRoot 5 := by decide
  have r0 : rootVec 0 = hexRoot 0 := by decide
  have r11 : rootVec 11 = -hexRoot 5 := by decide
  have r6 : rootVec 6 = -hexRoot 0 := by decide
  have hH : H = ⊤ := by
    apply G28Model.eq_top_of_simple
    · intro i c
      fin_cases i
      · have e : (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 : Fin Tag.G2.rank → ℤ) =
            rootVec 5 := by
          rw [r5]
          exact single_zero_eq_hexRoot
        show xPar (rootOperatorFamily .G2) (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1) c ∈ H
        rw [e]
        exact rho_phi_xPar M 5 (by norm_num) c
      · have e : (Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 : Fin Tag.G2.rank → ℤ) =
            rootVec 0 := by
          rw [r0]
          exact single_one_eq_hexRoot
        show xPar (rootOperatorFamily .G2) (Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1) c ∈ H
        rw [e]
        exact rho_phi_xPar M 0 (by norm_num) c
    · intro i c
      fin_cases i
      · have e : (-Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 : Fin Tag.G2.rank → ℤ) =
            rootVec 11 := by
          rw [r11]
          exact congrArg Neg.neg single_zero_eq_hexRoot
        show xPar (rootOperatorFamily .G2) (-Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1) c ∈ H
        rw [e]
        exact rho_phi_xPar M 11 (by norm_num) c
      · have e : (-Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 : Fin Tag.G2.rank → ℤ) =
            rootVec 6 := by
          rw [r6]
          exact congrArg Neg.neg single_one_eq_hexRoot
        show xPar (rootOperatorFamily .G2) (-Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1) c ∈ H
        rw [e]
        exact rho_phi_xPar M 6 (by norm_num) c
  have : h ∈ H := by rw [hH]; exact Subgroup.mem_top h
  exact this

variable (K) in
theorem card_ringAut (hK : Nat.card K = 8) : Nat.card (K ≃+* K) = 3 :=
  (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
    (by rw [hK]; norm_num : Nat.card K = 2 ^ 3)).1

theorem sig0_pow_three (hK : Nat.card K = 8) : sig0 ^ 3 = (1 : K ≃+* K) := by
  have := pow_card_eq_one' (G := K ≃+* K) (x := sig0)
  rwa [card_ringAut K hK] at this

theorem sig0_ne_one (hK : Nat.card K = 8) : (sig0 : K ≃+* K) ≠ 1 := by
  intro h
  have h1 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    have h2 : sig0 c = c := by rw [h]; rfl
    rw [sig0_apply] at h2
    have h3 : c * (c - 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact Or.inl h4
    · exact Or.inr (sub_eq_zero.mp h4)
  have h5 : Nat.card K ≤ 2 := by
    classical
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    calc (Finset.univ : Finset K).card ≤ ({0, 1} : Finset K).card :=
          Finset.card_le_card (fun c _ => by simpa using h1 c)
      _ ≤ 2 := Finset.card_le_two
  omega

theorem phi_pow_three (hK : Nat.card K = 8) : (phi : MulAut (adjointGroup .G2 K)) ^ 3 = 1 := by
  rw [phi, ← map_pow, sig0_pow_three hK, map_one]

theorem phi_pow_inner (hK : Nat.card K = 8) {i : ℕ}
    (h : (phi : MulAut (adjointGroup .G2 K)) ^ i ∈
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) : 3 ∣ i := by
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by rw [hK2]; decide
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have h1 := (g2_automorphism_normal_form hK3 hK4).2 (sig0 ^ i)
  rw [phi, ← map_pow] at h
  have h2 : sig0 ^ i = (1 : K ≃+* K) := h1 h
  have h3 : orderOf (sig0 : K ≃+* K) = 3 :=
    orderOf_eq_prime (sig0_pow_three hK) (sig0_ne_one hK)
  exact h3 ▸ orderOf_dvd_of_pow_eq_one h2

theorem conj_injective_of_center_bot {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro g h hgh
  have hc : h⁻¹ * g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 : g * x * g⁻¹ = h * x * h⁻¹ := by
      have := congrArg (fun α : MulAut G => α x) hgh
      simpa [MulAut.conj_apply] using this
    calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = h⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem conj_injective_X : Function.Injective
    (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
  conj_injective_of_center_bot center_adjointGroup_eq_bot

@[expose] noncomputable def mk (g : adjointGroup .G2 K) (i : ℕ) : MulAut (adjointGroup .G2 K) :=
  MulAut.conj g * phi ^ i

theorem phi_pow_mul_conj (g : adjointGroup .G2 K) (i : ℕ) :
    (phi : MulAut (adjointGroup .G2 K)) ^ i * MulAut.conj g =
      MulAut.conj ((phi ^ i : MulAut (adjointGroup .G2 K)) g) * phi ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : (phi : MulAut (adjointGroup .G2 K)) * MulAut.conj ((phi ^ i : MulAut _) g) =
        MulAut.conj (phi ((phi ^ i : MulAut _) g)) * phi := by
      ext x
      simp [MulAut.conj_apply, MulAut.mul_apply]
    calc (phi : MulAut (adjointGroup .G2 K)) ^ (i + 1) * MulAut.conj g
        = phi * (phi ^ i * MulAut.conj g) := by rw [pow_succ', mul_assoc]
      _ = phi * (MulAut.conj ((phi ^ i : MulAut _) g) * phi ^ i) := by rw [ih]
      _ = (phi * MulAut.conj ((phi ^ i : MulAut _) g)) * phi ^ i := by rw [mul_assoc]
      _ = MulAut.conj (phi ((phi ^ i : MulAut _) g)) * phi * phi ^ i := by rw [h1]
      _ = MulAut.conj ((phi ^ (i + 1) : MulAut _) g) * phi ^ (i + 1) := by
        rw [mul_assoc, ← pow_succ', pow_succ' (phi : MulAut (adjointGroup .G2 K)) i]
        rfl

theorem mk_mul (g h : adjointGroup .G2 K) (i j : ℕ) :
    (mk g i : MulAut (adjointGroup .G2 K)) * mk h j =
      mk (g * (phi ^ i : MulAut (adjointGroup .G2 K)) h) (i + j) := by
  unfold mk
  calc MulAut.conj g * phi ^ i * (MulAut.conj h * phi ^ j)
      = MulAut.conj g * (phi ^ i * MulAut.conj h) * phi ^ j := by simp only [mul_assoc]
    _ = MulAut.conj g * (MulAut.conj ((phi ^ i : MulAut (adjointGroup .G2 K)) h) * phi ^ i) *
          phi ^ j := by rw [phi_pow_mul_conj]
    _ = MulAut.conj (g * (phi ^ i : MulAut (adjointGroup .G2 K)) h) * phi ^ (i + j) := by
      rw [map_mul, pow_add]
      simp only [mul_assoc]

theorem sig0_generates (hK : Nat.card K = 8) (σ : K ≃+* K) : ∃ i < 3, σ = sig0 ^ i := by
  have h3 : orderOf (sig0 : K ≃+* K) = 3 :=
    orderOf_eq_prime (sig0_pow_three hK) (sig0_ne_one hK)
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [card_ringAut K hK]; norm_num)
  have hz : Subgroup.zpowers (sig0 : K ≃+* K) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, h3, card_ringAut K hK]
  have hσ : σ ∈ Subgroup.zpowers (sig0 : K ≃+* K) := by rw [hz]; exact Subgroup.mem_top σ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
  refine ⟨(k % 3).toNat, ?_, ?_⟩
  · omega
  · have h4 := zpow_mod_orderOf (sig0 : K ≃+* K) k
    rw [h3] at h4
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    exact_mod_cast h4.symm

theorem exists_mk (hK : Nat.card K = 8) (α : MulAut (adjointGroup .G2 K)) :
    ∃ g, ∃ i < 3, α = mk g i := by
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by rw [hK2]; decide
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  obtain ⟨g, σ, rfl⟩ := (g2_automorphism_normal_form hK3 hK4).1 α
  obtain ⟨i, hi, rfl⟩ := sig0_generates hK σ
  exact ⟨g, i, hi, by rw [mk, phi, map_pow]⟩

theorem mk_inj (hK : Nat.card K = 8) {g h : adjointGroup .G2 K} {i j : ℕ} (hi : i < 3)
    (hj : j < 3) (e : (mk g i : MulAut (adjointGroup .G2 K)) = mk h j) : g = h ∧ i = j := by
  have h3 := phi_pow_three hK
  have e1 : MulAut.conj g = MulAut.conj h * phi ^ (j + (3 - i)) := by
    have e2 : MulAut.conj g * phi ^ i * phi ^ (3 - i) = MulAut.conj h * phi ^ j * phi ^ (3 - i) :=
      by rw [show MulAut.conj g * phi ^ i = MulAut.conj h * phi ^ j from e]
    rw [mul_assoc, ← pow_add, show i + (3 - i) = 3 by omega, h3, mul_one] at e2
    rw [e2, mul_assoc, ← pow_add]
  have e3 : (phi : MulAut (adjointGroup .G2 K)) ^ (j + (3 - i)) =
      MulAut.conj (h⁻¹ * g) := by
    rw [map_mul, map_inv]
    calc (phi : MulAut (adjointGroup .G2 K)) ^ (j + (3 - i)) =
        (MulAut.conj h)⁻¹ * (MulAut.conj h * phi ^ (j + (3 - i))) := by group
      _ = (MulAut.conj h)⁻¹ * MulAut.conj g := by rw [← e1]
  have hd : 3 ∣ j + (3 - i) := phi_pow_inner hK ⟨h⁻¹ * g, e3.symm⟩
  have hij : i = j := by omega
  refine ⟨?_, hij⟩
  subst hij
  have : MulAut.conj (h⁻¹ * g) = (1 : MulAut (adjointGroup .G2 K)) := by
    rw [← e3, show i + (3 - i) = 3 by omega, h3]
  have := conj_injective_X (K := K) (this.trans (map_one MulAut.conj).symm)
  exact (inv_mul_eq_one.mp this).symm

theorem card_aut (hK : Nat.card K = 8) :
    Nat.card (MulAut (adjointGroup .G2 K)) = 3 * Nat.card (adjointGroup .G2 K) := by
  have hbij : Function.Bijective
      (fun p : adjointGroup .G2 K × Fin 3 => (mk p.1 p.2 : MulAut (adjointGroup .G2 K))) := by
    constructor
    · rintro ⟨g, i⟩ ⟨h, j⟩ e
      obtain ⟨rfl, hij⟩ := mk_inj hK i.2 j.2 e
      rw [Fin.ext hij]
    · intro α
      obtain ⟨g, i, hi, rfl⟩ := exists_mk hK α
      exact ⟨(g, ⟨i, hi⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3),
    Fintype.card_fin, mul_comm]

theorem card_X' (hK : Nat.card K = 8) :
    Nat.card (adjointGroup .G2 K) = 3 ^ 5 * 17816092672 := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
  norm_num [CFSG.Open.ordG2]

theorem rho_phi_pow (M : G28Model K) (k : ℕ) (h : adjointGroup .G2 K) {A : Array ℕ}
    (hA : Valid A) (hh : M.rho h = decode A) :
    M.rho ((phi ^ k : MulAut (adjointGroup .G2 K)) h) = decode (frobk k A) := by
  rw [decode_frobk hA k, ← hh]
  clear hh
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, rho_phi, ih, Function.iterate_succ_apply']

end Phi

end CFSG.AGLEmbedding.KFactProofs.G28
