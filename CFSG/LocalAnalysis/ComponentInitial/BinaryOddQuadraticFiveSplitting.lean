module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveCore

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive

open BinarySymplecticTransvection
open scoped commutatorElement

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {D : Type} [Group D] {B : Subgroup D}
  {θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2)} {b : LinearMap.BilinForm (ZMod 2) E}
  {κ : ZMod 2} {Q : QuadraticForm (ZMod 2) E}

abbrev hV (hQ : QuadraticMap.polarBilin Q = b) (s : bilinIsometryGroup b) :
    (E × ZMod 2) →ₗ[ZMod 2] (E × ZMod 2) :=
  ((hHom hQ s : LinearMap.GeneralLinearGroup (ZMod 2) (E × ZMod 2)) :
    (E × ZMod 2) →ₗ[ZMod 2] (E × ZMod 2))

theorem hV_apply (hQ : QuadraticMap.polarBilin Q = b) (s : bilinIsometryGroup b)
    (v : E × ZMod 2) : hV hQ s v = (sE s v.1, v.2 + Q v.1 + Q (sE s v.1)) :=
  rfl

theorem hV_fst (hQ : QuadraticMap.polarBilin Q = b) (s : bilinIsometryGroup b)
    (v : E × ZMod 2) : (hV hQ s v).1 = sE s v.1 :=
  rfl

theorem hV_eq_self (hQ : QuadraticMap.polarBilin Q = b) (s : bilinIsometryGroup b)
    {v : E × ZMod 2} (hv : sE s v.1 = v.1) : hV hQ s v = v := by
  rw [hV_apply, hv, add_assoc, zmod2_add_self, add_zero]

section Action

variable (hQ : QuadraticMap.polarBilin Q = b) (act : bilinIsometryGroup b →* MulAut D)
  (hact : ∀ s v ε, act s (bv θ (v, ε)) = bv θ (hV hQ s v, ε))
include hact

theorem act_zz (s : bilinIsometryGroup b) : act s (zz θ) = zz θ := by
  rw [zz, hact, map_zero]

theorem cB_act (s : bilinIsometryGroup b) {x : D} (hx : x ∈ B) :
    cB θ (act s x) = (hV hQ s (cB θ x).1, (cB θ x).2) := by
  obtain ⟨y, rfl⟩ := exists_bv_eq θ hx
  rw [← Prod.mk.eta (p := y), hact, cB_bv, cB_bv]

theorem act_mem_subA (s : bilinIsometryGroup b) {x : D} (hx : x ∈ subA θ) :
    act s x ∈ subA θ := by
  obtain ⟨v, rfl⟩ := hx
  rw [hact]
  exact ⟨_, rfl⟩

theorem act_mem_subI (s : bilinIsometryGroup b) {x : D} (hx : x ∈ subI θ) :
    act s x ∈ subI θ := by
  obtain ⟨c, rfl⟩ := hx
  rw [hact, map_smul]
  have hr : hV hQ s rV = rV := hHom_rV hQ s
  rw [hr]
  exact ⟨c, rfl⟩

theorem Labels.lab_act (L : Labels θ b κ) (s : bilinIsometryGroup b) (d : D) :
    L.lab (act s d) = hV hQ s (L.lab d) := by
  have h := congrArg (act s) (L.conj_zz d)
  rw [map_mul, map_mul, map_inv, act_zz hQ act hact, hact, L.conj_zz] at h
  exact congrArg Prod.fst (bv_injective θ h)

theorem Labels.sig_act (L : Labels θ b κ) (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (s : bilinIsometryGroup b) (d : D) : sig θ (act s d) = sE s (sig θ d) := by
  rw [sig, sig, ← map_pow, cB_act hQ act hact s (L.sq_mem hb hfaith d)]
  rfl

theorem Labels.sig_eq_zero_or_eq (L : Labels θ b κ) (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) [Finite E]
    (hE : 4 < Nat.card E) (d : D) : sig θ d = 0 ∨ sig θ d = (L.lab d).1 := by
  refine eq_zero_or_eq_of_forall_transvection hb hnd hE fun u hu => ?_
  have hsv : sE (tau hb u) (L.lab d).1 = (L.lab d).1 := by
    rw [sE_tau, hu, zero_smul, add_zero]
  have hlab : L.lab (act (tau hb u) d) = L.lab d := by
    rw [L.lab_act hQ act hact, hV_eq_self hQ _ hsv]
  have hx : d⁻¹ * act (tau hb u) d ∈ B := by
    rw [← L.ker_mu hb hQ hfaith, MonoidHom.mem_ker, map_mul, map_inv, L.mu_apply hb hQ,
      L.mu_apply hb hQ (act _ d), hlab, inv_mul_cancel]
  have h1 : sig θ (act (tau hb u) d) =
      sig θ d + (cB θ (d⁻¹ * act (tau hb u) d)).2 • (L.lab d).1 := by
    have hdecomp : act (tau hb u) d = d * (d⁻¹ * act (tau hb u) d) := by group
    have hom := L.om_bv (cB θ (d⁻¹ * act (tau hb u) d)) d
    rw [bv_cB θ hx] at hom
    rw [hdecomp, L.sig_mul hb hfaith, sig_of_mem hx, add_zero, hom, ← hdecomp]
  have h2 : sig θ (act (tau hb u) d) = sig θ d + b (sig θ d) u • u := by
    rw [L.sig_act hQ act hact hb hfaith, sE_tau]
  rw [h2, add_right_inj] at h1
  rw [h1]
  rcases zmod_two_cases (cB θ (d⁻¹ * act (tau hb u) d)).2 with h | h
  · left
    rw [h, zero_smul]
  · right
    rw [h, one_smul]

end Action

namespace Labels

variable (L : Labels θ b κ)

theorem lab_inv_fst (hb : b.IsAlt) (d : D) : (L.lab d⁻¹).1 = (L.lab d).1 := by
  have h := congrArg Prod.fst (L.lab_mul hb d⁻¹ d)
  rw [inv_mul_cancel, L.lab_one] at h
  simp only [Prod.fst_zero, Prod.fst_add, Prod.smul_fst, rV, smul_zero, add_zero] at h
  exact eq_of_add_eq_zero_zmod2 h.symm

@[expose] def subF (hb : b.IsAlt) : Subgroup D where
  carrier := {d | (L.lab d).1 = 0}
  mul_mem' {x y} hx hy := by
    change (L.lab (x * y)).1 = 0
    change (L.lab x).1 = 0 at hx
    change (L.lab y).1 = 0 at hy
    rw [L.lab_mul hb]
    simp [hx, hy, rV]
  one_mem' := by
    change (L.lab 1).1 = 0
    rw [L.lab_one]
    rfl
  inv_mem' {x} hx := by
    change (L.lab x⁻¹).1 = 0
    rw [L.lab_inv_fst hb]
    exact hx

theorem mem_subF (hb : b.IsAlt) {d : D} : d ∈ L.subF hb ↔ (L.lab d).1 = 0 :=
  Iff.rfl

theorem mem_subF_iff_conj (hb : b.IsAlt) {d : D} :
    d ∈ L.subF hb ↔ ∃ x ∈ subI θ, d⁻¹ * zz θ * d = zz θ * x := by
  rw [mem_subF, L.conj_zz]
  constructor
  · intro h
    refine ⟨bv θ ((L.lab d).2 • rV, 0), ⟨_, rfl⟩, ?_⟩
    rw [zz, ← bv_add]
    congr 1
    ext
    · simp [h, rV]
    · simp [rV]
    · simp
  · rintro ⟨x, ⟨c, rfl⟩, hx⟩
    rw [zz, ← bv_add] at hx
    have := congrArg (fun y => y.1.1) (bv_injective θ hx)
    simpa [rV] using this

theorem mem_subF_iff_comm (hb : b.IsAlt) {d : D} :
    d ∈ L.subF hb ↔ (zz θ)⁻¹ * d⁻¹ * zz θ * d ∈ subI θ := by
  rw [mem_subF, L.comm_zz]
  constructor
  · intro h
    refine ⟨(L.lab d).2, ?_⟩
    congr 1
    ext
    · simp [h, rV]
    · simp [rV]
    · rfl
  · rintro ⟨c, hc⟩
    have := congrArg (fun y => y.1.1) (bv_injective θ hc)
    simpa [rV] using this.symm

theorem le_subF (hb : b.IsAlt) : B ≤ L.subF hb := fun d hd => by
  rw [mem_subF, L.lab_of_mem hd]
  rfl

theorem subA_le_subF (hb : b.IsAlt) : subA θ ≤ L.subF hb :=
  (subA_le θ).trans (L.le_subF hb)

theorem conj_subA_of_mem_subF (hb : b.IsAlt) {f : D} (hf : f ∈ L.subF hb) (v : E × ZMod 2) :
    f⁻¹ * bv θ (v, 0) * f = bv θ (v, 0) := by
  rw [L.conj_bv, (L.mem_subF hb).1 hf, map_zero, LinearMap.zero_apply, mul_zero, zero_smul,
    zero_smul, add_zero, add_zero]

theorem commute_of_mem_subF (hb : b.IsAlt) {f x : D} (hf : f ∈ L.subF hb)
    (hx : x ∈ subA θ) : f * x = x * f := by
  obtain ⟨v, rfl⟩ := hx
  have h := L.conj_subA_of_mem_subF hb hf v
  calc f * bv θ (v, 0) = f * (f⁻¹ * bv θ (v, 0) * f) := by rw [h]
    _ = bv θ (v, 0) * f := by group

include L in
theorem commute_of_mem_subI {x : D} (hx : x ∈ subI θ) (d : D) : d * x = x * d := by
  obtain ⟨c, rfl⟩ := hx
  have h : d⁻¹ * bv θ (c • rV, 0) * d = bv θ (c • rV, 0) := by
    rw [L.conj_bv]
    simp [rV]
  calc d * bv θ (c • rV, 0) = d * (d⁻¹ * bv θ (c • rV, 0) * d) := by rw [h]
    _ = bv θ (c • rV, 0) * d := by group

end Labels

omit [AddCommGroup E] [Module (ZMod 2) E] in
theorem natCard_V [Finite E] (hcardE : Nat.card E = 16) : Nat.card (E × ZMod 2) = 32 := by
  rw [Nat.card_prod, hcardE, Nat.card_zmod]

omit [Module (ZMod 2) E] in
theorem natCard_B (θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2)) [Finite E]
    (hcardE : Nat.card E = 16) : Nat.card B = 64 := by
  rw [Nat.card_congr θ.toEquiv]
  change Nat.card ((E × ZMod 2) × ZMod 2) = 64
  rw [Nat.card_prod, natCard_V hcardE, Nat.card_zmod]

namespace Labels

variable (L : Labels θ b κ)

theorem natCard_D (hb : b.IsAlt) (hQ : QuadraticMap.polarBilin Q = b)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (hsurj : ∀ a, ∃ d, L.lab d = a) [Finite E] (hcardE : Nat.card E = 16) :
    Nat.card D = 2048 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup B, natCard_B θ hcardE,
    ← L.ker_mu hb hQ hfaith,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (L.mu_surjective hb hQ hsurj)).toEquiv]
  change Nat.card (E × ZMod 2) * 64 = 2048
  rw [natCard_V hcardE]

end Labels

namespace Labels

variable (L : Labels θ b κ)

theorem sq_mul_bv_of_mem_subF (hb : b.IsAlt) {f : D} (hf : f ∈ L.subF hb)
    (y : (E × ZMod 2) × ZMod 2) : (f * bv θ y) ^ 2 = f ^ 2 * bv θ (y.2 • L.lab f, 0) := by
  have e : (f * bv θ y) ^ 2 = f ^ 2 * (f⁻¹ * bv θ y * f) * bv θ y := by
    rw [sq, sq]
    group
  have hc : f⁻¹ * bv θ y * f = bv θ (y.1 + y.2 • L.lab f, y.2) := by
    rw [← Prod.mk.eta (p := y), L.conj_bv, (L.mem_subF hb).1 hf, map_zero, LinearMap.zero_apply,
      mul_zero, zero_smul, add_zero]
  rw [e, hc, mul_assoc, ← bv_add]
  congr 2
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_add]
    rw [add_right_comm, add_self_eq_zero_zmod_two, zero_add]
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_snd]
    rw [add_right_comm, add_self_eq_zero_zmod_two, zero_add]
  · exact zmod2_add_self _

theorem inv_mul_act_mem (hQ : QuadraticMap.polarBilin Q = b)
    (act : bilinIsometryGroup b →* MulAut D) (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) {d : D}
    (s : bilinIsometryGroup b) (h : L.lab (act s d) = L.lab d) : d⁻¹ * act s d ∈ B := by
  rw [← L.ker_mu hb hQ hfaith, MonoidHom.mem_ker, map_mul, map_inv, L.mu_apply hb hQ,
    L.mu_apply hb hQ (act s d), h, inv_mul_cancel]

end Labels

section FAction

variable (hQ : QuadraticMap.polarBilin Q = b) (act : bilinIsometryGroup b →* MulAut D)
  (hact : ∀ s v ε, act s (bv θ (v, ε)) = bv θ (hV hQ s v, ε))
include hact

namespace Labels

variable (L : Labels θ b κ)

theorem lab_act_of_mem_subF (hb : b.IsAlt) {f : D} (hf : f ∈ L.subF hb)
    (s : bilinIsometryGroup b) : L.lab (act s f) = L.lab f := by
  rw [L.lab_act hQ act hact, hV_eq_self hQ s (by rw [(L.mem_subF hb).1 hf, map_zero])]

theorem sq_mem_subI_of_mem_subF (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) {f : D}
    (hf : f ∈ L.subF hb) : f ^ 2 ∈ subI θ := by
  obtain ⟨w, hw⟩ := L.sq_mem_subA hb hfaith f
  have hfix : ∀ s : bilinIsometryGroup b, sE s w.1 = w.1 := by
    intro s
    obtain ⟨y, hy⟩ := exists_bv_eq θ
      (L.inv_mul_act_mem hQ act hb hfaith s (L.lab_act_of_mem_subF hQ act hact hb hf s))
    have hsf : act s f = f * bv θ y := by
      rw [hy]
      group
    have e := L.sq_mul_bv_of_mem_subF hb hf y
    rw [← hsf, ← map_pow, ← hw, hact, ← bv_add] at e
    have h1 := congrArg (fun x : (E × ZMod 2) × ZMod 2 => x.1.1) (bv_injective θ e)
    simp only [Prod.fst_add, Prod.smul_fst, (L.mem_subF hb).1 hf, smul_zero, add_zero] at h1
    exact h1
  have hw1 : w.1 = 0 := eq_zero_of_forall_fixed hb hnd hfix
  refine ⟨w.2, ?_⟩
  rw [← hw]
  congr 2
  ext
  · simp [rV, hw1]
  · simp [rV]

theorem exists_fixed_lift (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (hsurj : ∀ a, ∃ d, L.lab d = a) :
    ∃ f : D, L.lab f = rV ∧ f ^ 2 = 1 ∧ ∀ s, f⁻¹ * act s f ∈ subA θ := by
  obtain ⟨f₀, hf₀⟩ := hsurj rV
  have hf₀F : f₀ ∈ L.subF hb := by
    rw [mem_subF, hf₀]
    rfl
  obtain ⟨f, hlab, hf2⟩ : ∃ f : D, L.lab f = rV ∧ f ^ 2 = 1 := by
    obtain ⟨c, hc⟩ := L.sq_mem_subI_of_mem_subF hQ act hact hb hnd hfaith hf₀F
    rcases zmod_two_cases c with rfl | rfl
    · refine ⟨f₀, hf₀, ?_⟩
      rw [← hc, zero_smul]
      exact bv_zero θ
    · refine ⟨f₀ * zz θ, ?_, ?_⟩
      · rw [L.lab_mul hb, hf₀, L.lab_of_mem (zz_mem θ)]
        simp [rV]
      · rw [zz, L.sq_mul_bv_of_mem_subF hb hf₀F, ← hc, ← bv_add, hf₀, one_smul]
        simp only [add_self_eq_zero_zmod_two]
        exact bv_zero θ
  refine ⟨f, hlab, hf2, fun s => ?_⟩
  have hfF : f ∈ L.subF hb := by
    rw [mem_subF, hlab]
    rfl
  obtain ⟨y, hy⟩ := exists_bv_eq θ
    (L.inv_mul_act_mem hQ act hb hfaith s (L.lab_act_of_mem_subF hQ act hact hb hfF s))
  have hsf : act s f = f * bv θ y := by
    rw [hy]
    group
  have e := L.sq_mul_bv_of_mem_subF hb hfF y
  rw [← hsf, ← map_pow, hf2, map_one, one_mul, hlab] at e
  rw [← hy]
  refine mem_subA_of_cB θ (bv_mem θ y) ?_
  rw [cB_bv]
  rcases zmod_two_cases y.2 with h | h
  · exact h
  · exfalso
    rw [h, one_smul, ← bv_zero θ] at e
    have := congrArg (fun x : (E × ZMod 2) × ZMod 2 => x.1.2) (bv_injective θ e)
    simp [rV] at this

end Labels

end FAction

section Basis

variable (e : Module.Basis (Fin 4) (ZMod 2) E)

theorem repr_basis_apply (i j : Fin 4) : e.repr (e j) i = if j = i then 1 else 0 := by
  rw [e.repr_self, Finsupp.single_apply]

theorem coeff_triple {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {c₁ c₂ c₃ t : ZMod 2}
    (h : c₁ • (e i + e j) + c₂ • (e i + e k) + c₃ • (e j + e k) = t • (e i + e j + e k)) :
    c₁ = c₂ ∧ c₂ = c₃ := by
  have hi := congrArg (fun x => e.repr x i) h
  have hj := congrArg (fun x => e.repr x j) h
  have hk := congrArg (fun x => e.repr x k) h
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, repr_basis_apply,
    smul_eq_mul, hij, hik, hjk, hij.symm, hik.symm, hjk.symm, ↓reduceIte,
    mul_one, mul_zero, add_zero, zero_add] at hi hj hk
  revert hi hj hk
  generalize c₁ = p₁
  generalize c₂ = p₂
  generalize c₃ = p₃
  generalize t = p₄
  revert p₁ p₂ p₃ p₄
  decide

theorem coeff_pair {i j : Fin 4} (hij : i ≠ j) {c₁ c₂ t : ZMod 2}
    (h : c₁ • e i + c₂ • e j = t • (e i + e j)) : c₁ = c₂ := by
  have hi := congrArg (fun x => e.repr x i) h
  have hj := congrArg (fun x => e.repr x j) h
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, repr_basis_apply,
    smul_eq_mul, hij, hij.symm, ↓reduceIte, mul_one, mul_zero, add_zero,
    zero_add] at hi hj
  rw [hi, hj]

end Basis

theorem exists_smul_of_eq_zero_or_eq {v w : E} (h : w = 0 ∨ w = v) : ∃ c : ZMod 2, w = c • v := by
  rcases h with rfl | rfl
  · exact ⟨0, (zero_smul _ _).symm⟩
  · exact ⟨1, (one_smul _ _).symm⟩

namespace Labels

variable (L : Labels θ b κ)

theorem lab_mul_fst (hb : b.IsAlt) (d₁ d₂ : D) :
    (L.lab (d₁ * d₂)).1 = (L.lab d₁).1 + (L.lab d₂).1 := by
  rw [L.lab_mul hb]
  simp [rV]

theorem lab_fst_of_mu (hb : b.IsAlt) (hQ : QuadraticMap.polarBilin Q = b) {d : D} {w : E}
    {t : ZMod 2} (h : L.mu hb hQ d = Multiplicative.ofAdd (w, t)) : (L.lab d).1 = w := by
  rw [← L.mu_fst hb hQ d, h]
  rfl

theorem lab_mul_bv (hb : b.IsAlt) (d : D) (x : (E × ZMod 2) × ZMod 2) :
    L.lab (d * bv θ x) = L.lab d := by
  rw [L.lab_mul hb, L.lab_of_mem (bv_mem θ x)]
  simp

end Labels

section Split

variable (hQ : QuadraticMap.polarBilin Q = b) (act : bilinIsometryGroup b →* MulAut D)
  (hact : ∀ s v ε, act s (bv θ (v, ε)) = bv θ (hV hQ s v, ε))
include hact

namespace Labels

variable (L : Labels θ b κ)

theorem exists_lift (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (hsurj : ∀ a, ∃ d, L.lab d = a) [Finite E] (hE : 4 < Nat.card E) (v : E × ZMod 2) :
    ∃ d, L.mu hb hQ d = Multiplicative.ofAdd v ∧ sig θ d = 0 := by
  obtain ⟨d, hd⟩ := L.mu_surjective hb hQ hsurj (Multiplicative.ofAdd v)
  rcases L.sig_eq_zero_or_eq hQ act hact hb hnd hfaith hE d with h | h
  · exact ⟨d, hd, h⟩
  · refine ⟨d * zz θ, ?_, ?_⟩
    · rw [map_mul, hd, (L.mu_eq_one_iff hb hQ _).2 (L.lab_of_mem (zz_mem θ)), mul_one]
    · rw [L.sig_mul_zz hb hfaith, h, add_self_eq_zero_zmod_two]

theorem exists_split_data (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (hsurj : ∀ a, ∃ d, L.lab d = a) [Finite E] (hE : 4 < Nat.card E)
    (e : Module.Basis (Fin 4) (ZMod 2) E) :
    ∃ (y : Fin 4 → D) (ξ : D) (a : ZMod 2),
      (∀ i, L.mu hb hQ (y i) = Multiplicative.ofAdd (e i, 0)) ∧
      (∀ i, sig θ (y i) = a • e i) ∧ (∀ i j, om θ (y i) (y j) = 0) ∧
      L.lab ξ = rV ∧ sig θ ξ = 0 ∧ (∀ i, om θ ξ (y i) = 0) ∧
      (∀ s, ξ⁻¹ * act s ξ ∈ subA θ) := by
  choose x hxμ hxσ using fun i : Fin 4 =>
    L.exists_lift hQ act hact hb hnd hfaith hsurj hE (e i, 0)
  have hxl : ∀ i, (L.lab (x i)).1 = e i := fun i => L.lab_fst_of_mu hb hQ (hxμ i)
  have hpair : ∀ i j, ∃ c : ZMod 2, i ≠ j → om θ (x i) (x j) = c • (e i + e j) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => absurd hij h⟩
    · have h := L.sig_eq_zero_or_eq hQ act hact hb hnd hfaith hE (x i * x j)
      rw [L.sig_mul hb hfaith, hxσ, hxσ, zero_add, zero_add, L.om_comm hb hfaith,
        L.lab_mul_fst hb, hxl, hxl] at h
      obtain ⟨c, hc⟩ := exists_smul_of_eq_zero_or_eq h
      exact ⟨c, fun _ => hc⟩
  choose cf hcf using hpair
  have htriple : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → cf i j = cf i k ∧ cf i k = cf j k := by
    intro i j k hij hik hjk
    have h := L.sig_eq_zero_or_eq hQ act hact hb hnd hfaith hE (x i * x j * x k)
    have hs : sig θ (x i * x j * x k) =
        om θ (x i) (x j) + om θ (x i) (x k) + om θ (x j) (x k) := by
      rw [L.sig_mul hb hfaith, L.sig_mul hb hfaith, hxσ, hxσ, hxσ, L.om_mul_right hb hfaith,
        L.om_comm hb hfaith (x i) (x j), L.om_comm hb hfaith (x i) (x k),
        L.om_comm hb hfaith (x j) (x k)]
      abel
    have hl : (L.lab (x i * x j * x k)).1 = e i + e j + e k := by
      rw [L.lab_mul_fst hb, L.lab_mul_fst hb, hxl, hxl, hxl]
    rw [hs, hl, hcf i j hij, hcf i k hik, hcf j k hjk] at h
    obtain ⟨t, ht⟩ := exists_smul_of_eq_zero_or_eq h
    exact coeff_triple e hij hik hjk ht
  obtain ⟨h1, h2⟩ := htriple 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨h3, h4⟩ := htriple 0 1 3 (by decide) (by decide) (by decide)
  obtain ⟨-, h6⟩ := htriple 0 2 3 (by decide) (by decide) (by decide)
  set a := cf 0 1 with ha
  have hlt : ∀ i j : Fin 4, i < j → cf i j = a := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact h1.symm
      | exact (h1.trans h2).symm
      | exact h3.symm
      | exact (h3.trans h4).symm
      | exact (h3.trans h6).symm
      | exact absurd hij (by decide)
  have hom : ∀ i j, i ≠ j → om θ (x i) (x j) = a • (e i + e j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · rw [hcf i j hij, hlt i j h]
    · rw [← L.om_comm hb hfaith, hcf j i hij.symm, hlt j i h, add_comm]
  set y : Fin 4 → D := fun i => x i * bv θ (0, a) with hy
  have hyμ : ∀ i, L.mu hb hQ (y i) = Multiplicative.ofAdd (e i, 0) := fun i => by
    rw [hy, map_mul, hxμ, (L.mu_eq_one_iff hb hQ _).2 (L.lab_of_mem (bv_mem θ _)), mul_one]
  have hyl : ∀ i, (L.lab (y i)).1 = e i := fun i => L.lab_fst_of_mu hb hQ (hyμ i)
  have hyσ : ∀ i, sig θ (y i) = a • e i := fun i => by
    rw [hy, L.sig_mul hb hfaith, hxσ, sig_of_mem (bv_mem θ _), L.om_bv, hxl, zero_add, zero_add]
  have hzω : ∀ d, om θ d (bv θ (0, a)) = a • (L.lab d).1 := fun d => by
    rw [← L.om_comm hb hfaith, L.om_bv]
  have hyω : ∀ i j, om θ (y i) (y j) = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij, om_self]
    · rw [hy, L.om_mul_left hb hfaith, L.om_mul_right hb hfaith, hom i j hij, hzω, hxl,
        L.om_bv, L.lab_mul_bv hb, hxl]
      simp only [smul_add]
      rw [add_assoc (a • e i + a • e j)]
      exact add_self_eq_zero_zmod_two (a • e i + a • e j)
  obtain ⟨f, hfl, hf2, hfS⟩ := L.exists_fixed_lift hQ act hact hb hnd hfaith hsurj
  have hfσ : sig θ f = 0 := by
    rw [sig, hf2, cB_one]
    rfl
  have hfl1 : (L.lab f).1 = 0 := by
    rw [hfl]
    rfl
  have hα : ∀ i, ∃ c : ZMod 2, om θ f (y i) = c • e i := by
    intro i
    have h := L.sig_eq_zero_or_eq hQ act hact hb hnd hfaith hE (f * y i)
    rw [L.sig_mul hb hfaith, hfσ, hyσ, zero_add, L.om_comm hb hfaith, L.lab_mul_fst hb, hfl1,
      hyl, zero_add] at h
    obtain ⟨t, ht⟩ := exists_smul_of_eq_zero_or_eq h
    refine ⟨t + a, ?_⟩
    rw [add_smul, ← ht, add_comm (a • e i) (om θ f (y i)), add_assoc, add_self_eq_zero_zmod_two,
      add_zero]
  choose c hc using hα
  have hcconst : ∀ i, c i = c 0 := by
    intro i
    by_cases hi : i = 0
    · rw [hi]
    have h := L.sig_eq_zero_or_eq hQ act hact hb hnd hfaith hE (f * y 0 * y i)
    have hs : sig θ (f * y 0 * y i) = (a + c 0) • e 0 + (a + c i) • e i := by
      rw [L.sig_mul hb hfaith, L.sig_mul hb hfaith, hfσ, hyσ, hyσ, L.om_mul_right hb hfaith,
        L.om_comm hb hfaith f (y 0), L.om_comm hb hfaith f (y i), hc, hc, hyω, add_smul, add_smul]
      abel
    have hl : (L.lab (f * y 0 * y i)).1 = e 0 + e i := by
      rw [L.lab_mul_fst hb, L.lab_mul_fst hb, hfl1, hyl, hyl, zero_add]
    rw [hs, hl] at h
    obtain ⟨t, ht⟩ := exists_smul_of_eq_zero_or_eq h
    have := coeff_pair e (Ne.symm hi) ht
    rw [add_right_inj] at this
    exact this.symm
  set α := c 0 with hαdef
  refine ⟨y, f * bv θ (0, α), a, hyμ, hyσ, hyω, ?_, ?_, ?_, ?_⟩
  · rw [L.lab_mul_bv hb, hfl]
  · rw [L.sig_mul hb hfaith, hfσ, sig_of_mem (bv_mem θ _), L.om_bv, hfl1, smul_zero, add_zero,
      add_zero]
  · intro i
    rw [L.om_mul_left hb hfaith, hc, hcconst, L.om_bv, hyl]
    exact add_self_eq_zero_zmod_two (α • e i)
  · intro s
    rw [map_mul, hact, map_zero]
    have hfS' := hfS s
    have e : (f * bv θ (0, α))⁻¹ * ((act s) f * bv θ (0, α)) =
        (bv θ (0, α))⁻¹ * (f⁻¹ * act s f) * bv θ (0, α) := by group
    rw [e, mul_assoc, B_comm θ (subA_le θ hfS') (bv_mem θ _), ← mul_assoc, inv_mul_cancel,
      one_mul]
    exact hfS'

end Labels

end Split

theorem val_nsmul_eq_smul {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (c : ZMod 2) (x : M) :
    c.val • x = c • x := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]

theorem pow_val_add_of_sq {G : Type*} [Monoid G] {g : G} (hg : g ^ 2 = 1) (c c' : ZMod 2) :
    g ^ (c + c').val = g ^ c.val * g ^ c'.val := by
  rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases c' with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show ((1 : ZMod 2) + 1) = 0 by decide, ZMod.val_zero, pow_zero, ZMod.val_one, pow_one,
      ← sq, hg]

omit [Module (ZMod 2) E] in
theorem om_one_left (h : D) : om θ 1 h = 0 := by
  rw [om, inv_one, one_mul, mul_one, inv_mul_cancel, cB_one]
  rfl

namespace Labels

variable (L : Labels θ b κ)

include L in
theorem om_inv_left (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (g h : D) :
    om θ g⁻¹ h = om θ g h := by
  have e := L.om_mul_left hb hfaith g⁻¹ g h
  rw [inv_mul_cancel, om_one_left] at e
  exact eq_of_add_eq_zero_zmod2 e.symm

include L in
theorem om_eq_zero_of_mem_closure (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) {T : Set D}
    (hT : ∀ g ∈ T, ∀ h ∈ T, om θ g h = 0) {g h : D} (hg : g ∈ Subgroup.closure T)
    (hh : h ∈ Subgroup.closure T) : om θ g h = 0 := by
  have h1 : ∀ t ∈ T, om θ g t = 0 := by
    intro t ht
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hT x hx t ht
    | one => exact om_one_left t
    | mul x y _ _ hx hy => rw [L.om_mul_left hb hfaith, hx, hy, add_zero]
    | inv x _ hx => rw [L.om_inv_left hb hfaith, hx]
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact h1 x hx
  | one => rw [L.om_comm hb hfaith, om_one_left]
  | mul x y _ _ hx hy => rw [L.om_mul_right hb hfaith, hx, hy, add_zero]
  | inv x _ hx => rw [L.om_comm hb hfaith, L.om_inv_left hb hfaith, L.om_comm hb hfaith, hx]

end Labels

section IndexTwo

variable (hQ : QuadraticMap.polarBilin Q = b) (act : bilinIsometryGroup b →* MulAut D)
  (hact : ∀ s v ε, act s (bv θ (v, ε)) = bv θ (hV hQ s v, ε))
include hact

namespace Labels

variable (L : Labels θ b κ)

theorem exists_index_two (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (hsurj : ∀ a, ∃ d, L.lab d = a) [Finite E] (hE : 4 < Nat.card E)
    (e : Module.Basis (Fin 4) (ZMod 2) E) :
    ∃ (C : Subgroup D) (a : ZMod 2) (ξ : D),
      subA θ ≤ C ∧ zz θ ∉ C ∧ (∀ d, d ∈ C ∨ d * zz θ ∈ C) ∧
      (∀ s, ∀ c ∈ C, act s c ∈ C) ∧
      (∀ c ∈ C, ∀ c' ∈ C, om θ c c' = 0) ∧
      (∀ c ∈ C, sig θ c = a • (L.lab c).1) ∧
      ξ ∈ C ∧ L.lab ξ = rV ∧
      (∀ c ∈ C, (L.lab c).1 = 0 → c ∈ subA θ ∨ ξ⁻¹ * c ∈ subA θ) := by
  classical
  obtain ⟨y, ξ, a, hyμ, hyσ, hyω, hξl, hξσ, hξω, hξS⟩ :=
    L.exists_split_data hQ act hact hb hnd hfaith hsurj hE e
  have hcomm := L.commutator_eq hb hfaith hsurj
  have hof : ∀ x : D, Abelianization.of x = 1 ↔ x ∈ subA θ := fun x => by
    rw [← MonoidHom.mem_ker, Abelianization.ker_of, hcomm]
  have hyl : ∀ i, (L.lab (y i)).1 = e i := fun i => L.lab_fst_of_mu hb hQ (hyμ i)
  have hξμ : L.mu hb hQ ξ = Multiplicative.ofAdd (0, 1) := by
    rw [L.mu_apply hb hQ, hξl]
    simp [rV]
  set Y : Multiplicative (E × ZMod 2) → D := fun w =>
    y 0 ^ (e.repr (Multiplicative.toAdd w).1 0).val *
      y 1 ^ (e.repr (Multiplicative.toAdd w).1 1).val *
      y 2 ^ (e.repr (Multiplicative.toAdd w).1 2).val *
      y 3 ^ (e.repr (Multiplicative.toAdd w).1 3).val * ξ ^ (Multiplicative.toAdd w).2.val
    with hYdef
  have hY1 : Y 1 = 1 := by simp [hYdef]
  have hYξ : Y (Multiplicative.ofAdd (0, 1)) = ξ := by
    simp only [hYdef, toAdd_ofAdd, map_zero, Finsupp.coe_zero, Pi.zero_apply, ZMod.val_zero,
      pow_zero, one_mul]
    exact pow_one ξ
  have hYμ : ∀ w, L.mu hb hQ (Y w) = w := by
    intro w
    apply Multiplicative.toAdd.injective
    simp only [hYdef, map_mul, map_pow, hyμ, hξμ, toAdd_mul, toAdd_pow, toAdd_ofAdd]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, val_nsmul_eq_smul, smul_zero, add_zero]
      conv_rhs => rw [← e.sum_repr (Multiplicative.toAdd w).1, Fin.sum_univ_four]
    · simp only [Prod.snd_add, Prod.smul_snd, zero_add, val_nsmul_eq_smul, smul_eq_mul,
        mul_one, mul_zero]
  have hsq : ∀ g : D, Abelianization.of g ^ 2 = 1 := fun g => by
    rw [← map_pow, hof]
    exact L.sq_mem_subA hb hfaith g
  set Ybar : Multiplicative (E × ZMod 2) →* Abelianization D :=
    { toFun := fun w => Abelianization.of (Y w)
      map_one' := by rw [hY1, map_one]
      map_mul' := by
        intro w₁ w₂
        simp only [hYdef, map_mul, map_pow, toAdd_mul, Prod.fst_add, Prod.snd_add, map_add,
          Finsupp.add_apply, pow_val_add_of_sq (hsq _)]
        ac_rfl } with hYbar
  set C : Subgroup D := MonoidHom.eqLocus Abelianization.of (Ybar.comp (L.mu hb hQ)) with hC
  have hmemC : ∀ d, d ∈ C ↔ (Y (L.mu hb hQ d))⁻¹ * d ∈ subA θ := fun d => by
    rw [← hof, map_mul, map_inv, inv_mul_eq_one, eq_comm]
    exact Iff.rfl
  have hYB : ∀ d, (Y (L.mu hb hQ d))⁻¹ * d ∈ B := fun d => by
    have h : (Y (L.mu hb hQ d))⁻¹ * d ∈ (L.mu hb hQ).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hYμ, inv_mul_cancel]
    rwa [L.ker_mu hb hQ hfaith] at h
  have hYC : ∀ w, Y w ∈ C := fun w => by
    rw [hmemC, hYμ, inv_mul_cancel]
    exact one_mem _
  have hAC : ∀ x ∈ subA θ, x ∈ C := fun x hx => by
    rw [hmemC, (L.mu_eq_one_iff hb hQ _).2 (L.lab_of_mem (subA_le θ hx)), hY1, inv_one, one_mul]
    exact hx
  have hξC : ξ ∈ C := by
    rw [← hYξ]
    exact hYC _
  set T : Set D := Set.range y ∪ {ξ} with hT
  have hTω : ∀ g ∈ T, ∀ h ∈ T, om θ g h = 0 := by
    rintro g (⟨i, rfl⟩ | hg) h (⟨j, rfl⟩ | hh)
    · exact hyω i j
    · rw [Set.mem_singleton_iff.1 hh, L.om_comm hb hfaith, hξω]
    · rw [Set.mem_singleton_iff.1 hg]
      exact hξω j
    · rw [Set.mem_singleton_iff.1 hg, Set.mem_singleton_iff.1 hh]
      exact om_self ξ
  have hy' : ∀ i, y i ∈ Subgroup.closure T := fun i =>
    Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  have hξ' : ξ ∈ Subgroup.closure T := Subgroup.subset_closure (Or.inr rfl)
  have hYT : ∀ w, Y w ∈ Subgroup.closure T := fun w =>
    mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (hy' 0) _) (pow_mem (hy' 1) _))
      (pow_mem (hy' 2) _)) (pow_mem (hy' 3) _)) (pow_mem hξ' _)
  have hωY : ∀ w w', om θ (Y w) (Y w') = 0 := fun w w' =>
    L.om_eq_zero_of_mem_closure hb hfaith hTω (hYT w) (hYT w')
  have hσpow : ∀ (g : D) (c : ZMod 2), sig θ (g ^ c.val) = c • sig θ g := by
    intro g c
    rcases zmod_two_cases c with rfl | rfl
    · rw [ZMod.val_zero, pow_zero, sig_of_mem (one_mem B), zero_smul]
    · rw [ZMod.val_one, pow_one, one_smul]
  have hcl : ∀ g h, g ∈ Subgroup.closure T → h ∈ Subgroup.closure T →
      sig θ (g * h) = sig θ g + sig θ h := fun g h hg hh => by
    rw [L.sig_mul hb hfaith, L.om_eq_zero_of_mem_closure hb hfaith hTω hh hg, add_zero]
  have hσY : ∀ w, sig θ (Y w) = a • (Multiplicative.toAdd w).1 := by
    intro w
    simp only [hYdef]
    rw [hcl _ _ (mul_mem (mul_mem (mul_mem (pow_mem (hy' 0) _) (pow_mem (hy' 1) _))
      (pow_mem (hy' 2) _)) (pow_mem (hy' 3) _)) (pow_mem hξ' _),
      hcl _ _ (mul_mem (mul_mem (pow_mem (hy' 0) _) (pow_mem (hy' 1) _)) (pow_mem (hy' 2) _))
        (pow_mem (hy' 3) _),
      hcl _ _ (mul_mem (pow_mem (hy' 0) _) (pow_mem (hy' 1) _)) (pow_mem (hy' 2) _),
      hcl _ _ (pow_mem (hy' 0) _) (pow_mem (hy' 1) _), hσpow, hσpow, hσpow, hσpow, hσpow, hyσ,
      hyσ, hyσ, hyσ, hξσ, smul_zero, add_zero]
    conv_rhs => rw [← e.sum_repr (Multiplicative.toAdd w).1, Fin.sum_univ_four]
    simp only [smul_add, smul_comm a]
  have hdec : ∀ c ∈ C, ∃ g ∈ subA θ, c = Y (L.mu hb hQ c) * g := fun c hc =>
    ⟨_, (hmemC c).1 hc, by group⟩
  have hlabY : ∀ d, (L.lab (Y (L.mu hb hQ d))).1 = (L.lab d).1 := fun d => by
    rw [← L.mu_fst hb hQ, hYμ, L.mu_fst]
  have hcrit : ∀ d, (L.lab d).1 ≠ 0 → sig θ d = a • (L.lab d).1 → d ∈ C := by
    intro d hd hσ
    rcases mem_subA_or_mul_zz θ (hYB d) with h | h
    · exact (hmemC d).2 h
    · exfalso
      set g := (Y (L.mu hb hQ d))⁻¹ * d with hg
      have hg2 : (cB θ g).2 = 1 := by
        rcases zmod_two_cases (cB θ g).2 with h0 | h1
        · exfalso
          have hgA := mem_subA_of_cB θ (hYB d) h0
          have := mul_mem (inv_mem hgA) h
          rw [← mul_assoc, inv_mul_cancel, one_mul] at this
          exact zz_not_mem_subA θ this
        · exact h1
      have hdg : d = Y (L.mu hb hQ d) * g := by
        rw [hg]
        group
      have hom := L.om_bv (cB θ g) (Y (L.mu hb hQ d))
      rw [bv_cB θ (hYB d), hg2, one_smul, hlabY] at hom
      have hσd : sig θ d = a • (L.lab d).1 + (L.lab d).1 := by
        conv_lhs => rw [hdg]
        rw [L.sig_mul hb hfaith, sig_of_mem (hYB d), add_zero, hσY, hom, L.mu_fst]
      rw [hσ, left_eq_add] at hσd
      exact hd hσd
  refine ⟨C, a, ξ, hAC, fun hz => ?_, fun d => ?_, fun s c hc => ?_, fun c hc c' hc' => ?_,
    fun c hc => ?_, hξC, hξl, fun c hc hc1 => ?_⟩
  ·
    rw [hmemC, (L.mu_eq_one_iff hb hQ _).2 (L.lab_of_mem (zz_mem θ)), hY1, inv_one, one_mul] at hz
    exact zz_not_mem_subA θ hz
  ·
    rcases mem_subA_or_mul_zz θ (hYB d) with h | h
    · exact Or.inl ((hmemC d).2 h)
    · refine Or.inr ((hmemC _).2 ?_)
      rw [map_mul, (L.mu_eq_one_iff hb hQ _).2 (L.lab_of_mem (zz_mem θ)), mul_one, ← mul_assoc]
      exact h
  ·
    obtain ⟨g, hg, hceq⟩ := hdec c hc
    have hyS : ∀ i, act s (y i) ∈ C := by
      intro i
      refine hcrit _ ?_ ?_
      · rw [L.lab_act hQ act hact, hV_fst, hyl]
        intro h0
        apply e.ne_zero i
        rw [← sE_inv_apply s (e i), h0, map_zero]
      · rw [L.sig_act hQ act hact hb hfaith, hyσ, map_smul, L.lab_act hQ act hact, hV_fst, hyl]
    have hξS' : act s ξ ∈ C := by
      have : act s ξ = ξ * (ξ⁻¹ * act s ξ) := by group
      rw [this]
      exact mul_mem hξC (hAC _ (hξS s))
    rw [hceq, map_mul]
    refine mul_mem ?_ (hAC _ (act_mem_subA hQ act hact s hg))
    simp only [hYdef, map_mul, map_pow]
    exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (hyS 0) _) (pow_mem (hyS 1) _))
      (pow_mem (hyS 2) _)) (pow_mem (hyS 3) _)) (pow_mem hξS' _)
  ·
    obtain ⟨g, hg, hceq⟩ := hdec c hc
    obtain ⟨g', hg', hceq'⟩ := hdec c' hc'
    rw [hceq, hceq', L.om_mul_of_mem_subA hb hfaith _ _ hg, L.om_mul_right hb hfaith, hωY,
      L.om_of_mem_subA_right hb hfaith hg', add_zero]
  ·
    obtain ⟨g, hg, hceq⟩ := hdec c hc
    conv_lhs => rw [hceq]
    rw [L.sig_mul_of_mem_subA hb hfaith _ hg, hσY, L.mu_fst]
  ·
    obtain ⟨g, hg, hceq⟩ := hdec c hc
    have hμc : L.mu hb hQ c = Multiplicative.ofAdd (0, (L.lab c).2) := by
      rw [L.mu_apply hb hQ, hc1, QuadraticMap.map_zero, mul_zero, add_zero]
    rw [hμc] at hceq
    rcases zmod_two_cases (L.lab c).2 with h0 | h1
    · left
      rw [h0, Prod.mk_zero_zero, ofAdd_zero, hY1, one_mul] at hceq
      rw [hceq]
      exact hg
    · right
      rw [h1, hYξ] at hceq
      rw [hceq, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hg

end Labels

end IndexTwo

theorem normal_of_commutator_le {G : Type*} [Group G] {H : Subgroup G}
    (h : commutator G ≤ H) : H.Normal := by
  refine ⟨fun x hx g => ?_⟩
  have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [e]
  rw [commutator_def] at h
  exact mul_mem (h (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x)))
    hx

theorem mem_subI_of_mem_subA {x : D} (hx : x ∈ subA θ) (h : (cB θ x).1.1 = 0) : x ∈ subI θ := by
  obtain ⟨v, rfl⟩ := hx
  rw [cB_bv] at h
  have h' : v.1 = 0 := h
  refine ⟨v.2, ?_⟩
  congr 1
  ext
  · simp [rV, h']
  · simp [rV]
  · rfl

theorem index_two_props {C : Subgroup D} (hAC : subA θ ≤ C) (hz : zz θ ∉ C)
    (hidx : ∀ d, d ∈ C ∨ d * zz θ ∈ C) (hcard : Nat.card D = 2048) :
    Nat.card C = 1024 ∧ Subgroup.zpowers (zz θ) ⊔ C = ⊤ ∧ B ⊓ C = subA θ := by
  have hboth : ∀ d, d ∈ C → d * zz θ ∈ C → False := fun d hd hdz => hz (by
    have := mul_mem (inv_mem hd) hdz
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)
  have hidx2 : C.index = 2 := by
    refine Subgroup.index_eq_two_iff.2 ⟨zz θ, fun d => ?_⟩
    rcases hidx d with h | h
    · exact Or.inr ⟨h, fun h' => hboth d h h'⟩
    · exact Or.inl ⟨h, fun h' => hboth d h' h⟩
  refine ⟨?_, ?_, ?_⟩
  · have h := Subgroup.card_mul_index C
    rw [hidx2, hcard] at h
    omega
  · refine eq_top_iff.2 fun d _ => ?_
    rcases hidx d with h | h
    · exact Subgroup.mem_sup_right h
    · have e : d = d * zz θ * (zz θ)⁻¹ := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_right h)
        (Subgroup.mem_sup_left (inv_mem (Subgroup.mem_zpowers _)))
  · refine le_antisymm (fun x hx => ?_) (le_inf (subA_le θ) hAC)
    rcases mem_subA_or_mul_zz θ hx.1 with h | h
    · exact h
    · exact absurd (hAC h) (hboth x hx.2)

namespace Labels

variable (L : Labels θ b κ)

theorem commElt_zz_inv (d : D) : ⁅zz θ, d⁻¹⁆ = bv θ (L.lab d, 0) := by
  have hz : (zz θ)⁻¹ = zz θ := bv_inv θ _
  rw [commutatorElement_def, inv_inv, hz, ← L.comm_zz, hz]

include L in
theorem commutator_le_subI (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) {C : Subgroup D}
    (hω : ∀ c ∈ C, ∀ c' ∈ C, om θ c c' = 0) : ⁅C, C⁆ ≤ subI θ := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have e : ⁅g, h⁆ = g⁻¹⁻¹ * h⁻¹⁻¹ * g⁻¹ * h⁻¹ := by rw [commutatorElement_def, inv_inv, inv_inv]
  rw [e]
  exact mem_subI_of_mem_subA (L.comm_mem_subA hb hfaith _ _) (hω _ (inv_mem hg) _ (inv_mem hh))

theorem exists_mem_lab (hb : b.IsAlt) (hsurj : ∀ a, ∃ d, L.lab d = a) {C : Subgroup D}
    (hidx : ∀ d, d ∈ C ∨ d * zz θ ∈ C) (v : E × ZMod 2) : ∃ c ∈ C, L.lab c = v := by
  obtain ⟨d, hd⟩ := hsurj v
  rcases hidx d with h | h
  · exact ⟨d, h, hd⟩
  · exact ⟨d * zz θ, h, by rw [zz, L.lab_mul_bv hb, hd]⟩

end Labels

section FProps

variable (hQ : QuadraticMap.polarBilin Q = b) (act : bilinIsometryGroup b →* MulAut D)
  (hact : ∀ s v ε, act s (bv θ (v, ε)) = bv θ (hV hQ s v, ε))
include hact

namespace Labels

variable (L : Labels θ b κ)

theorem subF_props (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (hsurj : ∀ a, ∃ d, L.lab d = a) [Finite E] (hcardE : Nat.card E = 16) :
    (L.subF hb).Normal ∧ (∀ s, ∀ d ∈ L.subF hb, act s d ∈ L.subF hb) ∧
      Nat.card (L.subF hb) = 128 ∧
      (Subgroup.center (L.subF hb)).map (L.subF hb).subtype = subA θ ∧
      ⁅L.subF hb, L.subF hb⁆ = subI θ ∧
      Subgroup.closure {x : D | ∃ y ∈ L.subF hb, y ^ 2 = x} = subI θ := by
  have hcomm := L.commutator_eq hb hfaith hsurj
  obtain ⟨f₀, hf₀⟩ := hsurj rV
  have hf₀F : f₀ ∈ L.subF hb := by
    rw [mem_subF, hf₀]
    rfl
  have hzF : zz θ ∈ L.subF hb := L.le_subF hb (zz_mem θ)
  refine ⟨normal_of_commutator_le (hcomm.le.trans (L.subA_le_subF hb)), fun s d hd => ?_, ?_,
    ?_, ?_⟩
  · rw [mem_subF, L.lab_act hQ act hact, hV_fst, (L.mem_subF hb).1 hd, map_zero]
  ·
    set π : D →* Multiplicative E :=
      (AddMonoidHom.fst E (ZMod 2)).toMultiplicative.comp (L.mu hb hQ) with hπ
    have hker : π.ker = L.subF hb := by
      ext d
      rw [MonoidHom.mem_ker, mem_subF]
      change Multiplicative.ofAdd (L.lab d).1 = 1 ↔ _
      rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
    have hsurjπ : Function.Surjective π := fun w => by
      obtain ⟨d, hd⟩ :=
        L.mu_surjective hb hQ hsurj (Multiplicative.ofAdd (Multiplicative.toAdd w, 0))
      refine ⟨d, ?_⟩
      change Multiplicative.ofAdd (Multiplicative.toAdd (L.mu hb hQ d)).1 = w
      rw [hd]
      rfl
    have hidx : (L.subF hb).index = 16 := by
      rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurjπ, Subgroup.card_top]
      change Nat.card E = 16
      exact hcardE
    have h := Subgroup.card_mul_index (L.subF hb)
    rw [hidx, L.natCard_D hb hQ hfaith hsurj hcardE] at h
    omega
  ·
    ext x
    constructor
    · rintro ⟨⟨x, hxF⟩, hxZ, rfl⟩
      have hc := Subgroup.mem_center_iff.1 hxZ
      have hxz := congrArg Subtype.val (hc ⟨zz θ, hzF⟩)
      have hxf := congrArg Subtype.val (hc ⟨f₀, hf₀F⟩)
      change zz θ * x = x * zz θ at hxz
      change f₀ * x = x * f₀ at hxf
      have hxB : x ∈ B := by
        refine L.mem_of_lab_eq_zero hfaith ?_
        have h := L.conj_zz x
        rw [mul_assoc, hxz, ← mul_assoc, inv_mul_cancel, one_mul, zz] at h
        exact (congrArg Prod.fst (bv_injective θ h)).symm
      obtain ⟨y, rfl⟩ := exists_bv_eq θ hxB
      refine mem_subA_of_cB θ hxB ?_
      change (cB θ (bv θ y)).2 = 0
      rw [cB_bv]
      have h := L.conj_bv f₀ y.1 y.2
      rw [Prod.mk.eta, mul_assoc, ← hxf, ← mul_assoc, inv_mul_cancel, one_mul, hf₀] at h
      have h2 := congrArg (fun x : (E × ZMod 2) × ZMod 2 => x.1.2) (bv_injective θ h)
      simp [rV] at h2
      exact h2
    · intro hx
      refine ⟨⟨x, L.subA_le_subF hb hx⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
      exact Subtype.ext (L.commute_of_mem_subF hb g.2 hx)
  ·
    have hsqI : Subgroup.closure {x : D | ∃ y ∈ L.subF hb, y ^ 2 = x} ≤ subI θ := by
      rw [Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      exact L.sq_mem_subI_of_mem_subF hQ act hact hb hnd hfaith hy
    have hIc : subI θ ≤ ⁅L.subF hb, L.subF hb⁆ := by
      rintro _ ⟨c, rfl⟩
      rcases zmod_two_cases c with rfl | rfl
      · rw [zero_smul, Prod.mk_zero_zero, bv_zero]
        exact one_mem _
      · rw [one_smul, ← hf₀, ← L.commElt_zz_inv]
        exact Subgroup.commutator_mem_commutator hzF (inv_mem hf₀F)
    have hcs := commutator_le_closure_sq (L.subF hb)
    exact ⟨le_antisymm (hcs.trans hsqI) hIc, le_antisymm hsqI (hIc.trans hcs)⟩

end Labels

end FProps

end CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive
