module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KBase
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAction
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupInner

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit.L2K

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer GorensteinWalter
open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
variable {F : Type} [Field F] [Finite F]

@[expose] def actC (A : L2Data t L) (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) :
    centralizer ({t} : Set X) →* PGammaL2 F :=
  (autEquiv e).toMonoidHom.comp ((HarrisLit.barAction L).comp
    (inclusion (le_normalizer (A := A))))

@[expose] def act (A : L2Data t L) (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) (g : X) : PGammaL2 F :=
  open Classical in if h : g ∈ centralizer ({t} : Set X) then actC A e ⟨g, h⟩ else 1

@[expose] def rho (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) (g : X) : PSL2 F :=
  open Classical in if h : g ∈ L then e (QuotientGroup.mk ⟨g, h⟩) else 1

variable (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F)

theorem act_of_mem {g : X} (hg : g ∈ centralizer ({t} : Set X)) :
    act A e g = actC A e ⟨g, hg⟩ := by
  simp [act, hg]

theorem act_mul {g h : X} (hg : g ∈ centralizer ({t} : Set X))
    (hh : h ∈ centralizer ({t} : Set X)) : act A e (g * h) = act A e g * act A e h := by
  rw [act_of_mem e hg, act_of_mem e hh, act_of_mem e (mul_mem hg hh), ← map_mul]
  rfl

theorem act_inv {g : X} (hg : g ∈ centralizer ({t} : Set X)) :
    act A e g⁻¹ = (act A e g)⁻¹ := by
  rw [act_of_mem e hg, act_of_mem e (inv_mem hg), ← map_inv]
  rfl

theorem act_one : act A e (1 : X) = 1 := by
  rw [act_of_mem e (one_mem _), show (⟨1, _⟩ : centralizer ({t} : Set X)) = 1 from rfl,
    map_one]

theorem act_conj {g h : X} (hg : g ∈ centralizer ({t} : Set X))
    (hh : h ∈ centralizer ({t} : Set X)) :
    act A e (g * h * g⁻¹) = act A e g * act A e h * (act A e g)⁻¹ := by
  rw [act_mul e (mul_mem hg hh) (inv_mem hg), act_mul e hg hh, act_inv e hg]

theorem act_pow {g : X} (hg : g ∈ centralizer ({t} : Set X)) (n : ℕ) :
    act A e (g ^ n) = act A e g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, act_one]
  | succ n ih => rw [pow_succ, act_mul e (pow_mem hg n) hg, ih, pow_succ]

theorem act_eq_one_iff {g : X} (hg : g ∈ centralizer ({t} : Set X)) :
    act A e g = 1 ↔ g ∈ coreActionKernel L := by
  rw [act_of_mem e hg]
  change (autEquiv e) (HarrisLit.barAction L ⟨g, le_normalizer (A := A) hg⟩) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, HarrisLit.mem_ker_barAction]

omit [Finite X] [Finite F] in
theorem rho_of_mem {g : X} (hg : g ∈ L) : rho e g = e (QuotientGroup.mk ⟨g, hg⟩) := by
  simp [rho, hg]

omit [Finite X] [Finite F] in
theorem rho_mul {g h : X} (hg : g ∈ L) (hh : h ∈ L) : rho e (g * h) = rho e g * rho e h := by
  rw [rho_of_mem e hg, rho_of_mem e hh, rho_of_mem e (mul_mem hg hh), ← map_mul]
  rfl

omit [Finite X] [Finite F] in
theorem rho_one : rho e (1 : X) = 1 := by
  rw [rho_of_mem e (one_mem _), show (⟨1, _⟩ : L) = 1 from rfl, QuotientGroup.mk_one, map_one]

omit [Finite X] [Finite F] in
theorem rho_inv {g : X} (hg : g ∈ L) : rho e g⁻¹ = (rho e g)⁻¹ := by
  rw [rho_of_mem e hg, rho_of_mem e (inv_mem hg), ← map_inv]
  rfl

theorem act_of_mem_L {l : X} (hl : l ∈ L) : act A e l = incl F (rho e l) := by
  rw [act_of_mem e (L_le_C (A := A) hl), rho_of_mem e hl]
  change autEquiv e (HarrisLit.barAction L ⟨l, _⟩) = _
  rw [show (⟨l, _⟩ : normalizer (L : Set X)) = ⟨(⟨l, hl⟩ : L), le_normalizer (A := A)
    (L_le_C (A := A) hl)⟩ from rfl, HarrisLit.barAction_of_mem, autEquiv_conj]

omit [Finite X] [Finite F] in
include A in
theorem t_mem_coreActionKernel : t ∈ coreActionKernel L :=
  GSLit.mem_coreActionKernel_of_le_centralizer (L_le_C (A := A))

theorem act_t : act A e t = 1 :=
  (act_eq_one_iff e t_mem_C).mpr (t_mem_coreActionKernel (A := A))

theorem act_trans (c : PGammaL2 F) (g : X) :
    act A (e.trans (semilinearAction F c⁻¹)) g = c⁻¹ * act A e g * c := by
  by_cases hg : g ∈ centralizer ({t} : Set X)
  · rw [act_of_mem _ hg, act_of_mem _ hg]
    change autEquiv _ (HarrisLit.barAction L _) = c⁻¹ * autEquiv e (HarrisLit.barAction L _) * c
    rw [autEquiv_eq_conj _ e]
    have h1 : e.symm.trans (e.trans (semilinearAction F c⁻¹)) = semilinearAction F c⁻¹ := by
      ext x
      simp
    rw [h1, show semilinearAction F c⁻¹ = semilinearEquivAut F c⁻¹ from rfl,
      MulEquiv.symm_apply_apply, inv_inv]
  · simp [act, hg]

theorem rho_eq_one {r : X} (hr : r ∈ A.R) (h1 : rho e r = 1) : r = 1 := by
  have h : act A e r = 1 := by rw [act_of_mem_L e hr.2, h1, map_one]
  have hK : r ∈ A.K ⊓ L :=
    Subgroup.mem_inf.mpr ⟨⟨hr.1, (act_eq_one_iff e (L_le_C (A := A) hr.2)).mp h⟩, hr.2⟩
  rwa [A.K_inf_L, mem_bot] at hK

theorem rho_injective {r s : X} (hr : r ∈ A.R) (hs : s ∈ A.R) (h : rho e r = rho e s) :
    r = s := by
  have h1 : rho e (r * s⁻¹) = 1 := by rw [rho_mul e hr.2 (inv_mem hs.2), rho_inv e hs.2, h,
    mul_inv_cancel]
  have := rho_eq_one e (mul_mem hr (inv_mem hs)) h1
  rw [mul_inv_eq_one] at this
  exact this

omit [Finite X] [Finite F] in
theorem rho_pow {g : X} (hg : g ∈ L) (n : ℕ) : rho e (g ^ n) = rho e g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rho_one]
  | succ n ih => rw [pow_succ, rho_mul e (pow_mem hg n) hg, ih, pow_succ]

include e in
theorem isOddPrimePower_card (S : Gens A) : IsOddPrimePower (Nat.card F) := by
  apply isOddPrimePower_of_ringChar
  intro h2
  have h2' : (2 : F) = 0 := by
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [h2] at this
    exact_mod_cast this
  set E := Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  have hy4 : E (rho e S.x₀) ^ 4 = 1 := by
    rw [← map_pow, ← rho_pow e S.x₀_mem.2, S.x₀_pow_four, rho_one, map_one]
  have hy2 := sq_eq_one_of_pow_four_char_two h2' _ hy4
  rw [← map_pow, ← rho_pow e S.x₀_mem.2, MulEquiv.map_eq_one_iff] at hy2
  exact S.z_ne_one (rho_eq_one e S.z_mem hy2)

@[expose] def rhoL (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) : L →* PSL2 F :=
  e.toMonoidHom.comp (QuotientGroup.mk' _)

omit [Finite X] [Finite F] in
theorem rhoL_apply (l : L) : rhoL e l = rho e l := by
  rw [rho_of_mem e l.2]
  rfl

@[expose] def imR (A : L2Data t L) (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) : Subgroup (PSL2 F) :=
  (A.R.subgroupOf L).map (rhoL e)

omit [Finite X] [Finite F] in
theorem mem_imR {r : X} (hr : r ∈ A.R) : rho e r ∈ imR A e :=
  ⟨⟨r, hr.2⟩, hr, rhoL_apply e _⟩

omit [Finite X] [Finite F] in
theorem exists_of_mem_imR {y : PSL2 F} (hy : y ∈ imR A e) : ∃ r ∈ A.R, rho e r = y := by
  obtain ⟨l, hl, rfl⟩ := hy
  exact ⟨l, hl, (rhoL_apply e l).symm⟩

omit [Finite X] [Finite F] in
theorem isPGroup_imR : IsPGroup 2 (imR A e) :=
  (((A.isPGroup_T.to_le inf_le_left).comap_of_injective L.subtype
    (subtype_injective L))).map _

theorem act_comm_incl {g r : X} (hg : g ∈ centralizer ({t} : Set X)) (hr : r ∈ A.R)
    (hgr : g * r = r * g) : act A e g * incl F (rho e r) = incl F (rho e r) * act A e g := by
  have hrC := L_le_C (A := A) hr.2
  rw [← act_of_mem_L e hr.2, ← act_mul e hg hrC, ← act_mul e hrC hg, hgr]

theorem right_act_ne_one (S : Gens A) {κ : X} (hκ : κ ∈ A.T) (hκ2 : κ ^ 2 = 1)
    (hκR : ∀ r ∈ A.R, κ * r = r * κ) (hψκ : ψX A κ ∉ R8) :
    (act A e κ).right ≠ 1 ∧ orderOf (act A e κ) = 2 := by
  have hodd := isOddPrimePower_card e S
  have hκC := A.T_le_centralizer hκ
  have hzC := A.T_le_centralizer S.z_mem.1
  set τ := act A e κ with hτ
  set a := act A e S.z with ha
  have hτ2 : τ ^ 2 = 1 := by rw [hτ, ← act_pow e hκC, hκ2, act_one]
  have ha2 : a ^ 2 = 1 := by rw [ha, ← act_pow e hzC, S.z_sq, act_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    have hK : κ ∈ A.K := Subgroup.mem_inf.mpr ⟨hκ, (act_eq_one_iff e hκC).mp h⟩
    exact hψκ (((ψX_eq_one_iff hκ).mpr hK) ▸ one_mem R8)
  have hτa : τ ≠ a := by
    intro h
    have h1 : act A e (κ * S.z⁻¹) = 1 := by
      rw [act_mul e hκC (inv_mem hzC), act_inv e hzC, ← ha, ← h, mul_inv_cancel]
    have hK : κ * S.z⁻¹ ∈ A.K := Subgroup.mem_inf.mpr
      ⟨mul_mem hκ (inv_mem S.z_mem.1), (act_eq_one_iff e (mul_mem hκC (inv_mem hzC))).mp h1⟩
    rw [← ψX_eq_one_iff (mul_mem hκ (inv_mem S.z_mem.1)), ψX_mul hκ (inv_mem S.z_mem.1),
      ψX_inv S.z_mem.1, mul_inv_eq_one, S.ψ_z] at hK
    exact hψκ (hK ▸ z8_mem_R8)
  refine ⟨fun hr => ?_, orderOf_eq_prime hτ2 hτ1⟩
  have ha1 : a ≠ 1 := by
    intro h
    rw [ha, act_of_mem_L e S.z_mem.2, ← map_one (incl F)] at h
    exact S.z_ne_one (rho_eq_one e S.z_mem (incl_injective F h))
  have hcomm : τ * a = a * τ := by
    rw [hτ, ha, ← act_mul e hκC hzC, ← act_mul e hzC hκC, hκR _ S.z_mem]
  have hEl : ElemAbelianTwo (zpowers τ) := by
    refine ⟨fun u hu v hv => ?_, fun u hu => ?_⟩
    · rcases eq_one_or_eq_of_mem_zpowers hτ2 hu with rfl | rfl <;>
        rcases eq_one_or_eq_of_mem_zpowers hτ2 hv with rfl | rfl <;> simp
    · rcases eq_one_or_eq_of_mem_zpowers hτ2 hu with rfl | rfl
      · exact one_pow 2
      · exact hτ2
  have haE : a ∉ zpowers τ := by
    intro h
    rcases eq_one_or_eq_of_mem_zpowers hτ2 h with h | h
    · exact ha1 h
    · exact hτa h.symm
  obtain ⟨-, -, hcard⟩ := hEl.sup_zpowers ha2 haE (fun b hb => by
    rcases eq_one_or_eq_of_mem_zpowers hτ2 hb with rfl | rfl
    · simp
    · exact hcomm.symm)
  rw [Nat.card_zpowers, orderOf_eq_prime hτ2 hτ1] at hcard
  set E : Subgroup (PGammaL2 F) := zpowers τ ⊔ zpowers a with hE
  have hEr : E.map (fieldProj F) = ⊥ := by
    rw [eq_bot_iff, Subgroup.map_le_iff_le_comap]
    refine sup_le (zpowers_le.mpr hr) (zpowers_le.mpr ?_)
    rw [ha, act_of_mem_L e S.z_mem.2]
    rfl
  have hlin := card_eq_linearPart_mul E
  rw [hEr, card_bot, mul_one, hcard] at hlin
  have hxy : rho e S.x₀ * rho e S.y₀ ≠ rho e S.y₀ * rho e S.x₀ := by
    intro h
    rw [← rho_mul e S.x₀_mem.2 S.y₀_mem.2, ← rho_mul e S.y₀_mem.2 S.x₀_mem.2] at h
    have h' := rho_injective e (mul_mem S.x₀_mem S.y₀_mem) (mul_mem S.y₀_mem S.x₀_mem) h
    have h'' := congrArg (ψX A) h'
    rw [ψX_mul S.x₀_mem.1 S.y₀_mem.1, ψX_mul S.y₀_mem.1 S.x₀_mem.1, S.ψ_x₀, S.ψ_y₀] at h''
    exact absurd h'' (by decide)
  have hE2 : IsPGroup 2 E := isPGroup_two_of_forall_sq E (fun u hu => by
    obtain ⟨hEel, -, -⟩ := hEl.sup_zpowers ha2 haE (fun b hb => by
      rcases eq_one_or_eq_of_mem_zpowers hτ2 hb with rfl | rfl
      · simp
      · exact hcomm.symm)
    rw [← pow_two]
    exact hEel.sq_eq_one u hu)
  have hcent : ∀ u ∈ E, ∀ y ∈ imR A e, u * incl F y = incl F y * u := by
    intro u hu y hy
    obtain ⟨r, hr, rfl⟩ := exists_of_mem_imR e hy
    have hle : E ≤ centralizer ({incl F (rho e r)} : Set (PGammaL2 F)) := by
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_) <;>
        rw [mem_centralizer_singleton_iff]
      · exact act_comm_incl e hκC hr (hκR r hr)
      · exact act_comm_incl e hzC hr (S.z_comm_R hr)
    exact mem_centralizer_singleton_iff.mp (hle hu)
  have := card_linearPart_le_two hodd (imR A e) (isPGroup_imR e) (mem_imR e S.x₀_mem)
    (mem_imR e S.y₀_mem) hxy E hE2 hcent
  omega

theorem ofAdd_one_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide

theorem ofAdd_one_ne_one : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide

omit [Finite X] [Finite F] in
theorem sqLeft_incl (x : PSL2 F) : SqLeft (incl F x) := ⟨x, rfl⟩

theorem right_act_k_ne_one (C : A.CaseK) (S : Gens A) :
    (act A e C.k).right ≠ 1 ∧ orderOf (act A e C.k) = 2 :=
  right_act_ne_one e S C.k_mem C.k_sq (fun _ hr => commute_k C hr) (ψX_k_not_mem_R8 C)

theorem sqLeft_act (C : A.CaseK) (S : Gens A) {g : X} (hg : g ∈ centralizer ({t} : Set X)) :
    SqLeft (act A e g) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_card e S
  let χ : centralizer ({t} : Set X) →* Multiplicative (ZMod 2) :=
    { toFun := fun g => if SqLeft (actC A e g) then 1 else Multiplicative.ofAdd 1
      map_one' := by
        rw [map_one]
        split_ifs with h
        · rfl
        · exact absurd sqLeft_one h
      map_mul' := fun a b => by
        simp only [map_mul, sqLeft_mul]
        by_cases ha : SqLeft (actC A e a) <;> by_cases hb : SqLeft (actC A e b) <;>
          simp only [ha, hb, iff_true, iff_false, not_true, ite_true, ite_false, one_mul,
            mul_one, ofAdd_one_mul_self] }
  have hχ : ∀ c : centralizer ({t} : Set X), χ c = 1 ↔ SqLeft (actC A e c) := by
    intro c
    change (if SqLeft (actC A e c) then 1 else Multiplicative.ofAdd 1) = 1 ↔ _
    split_ifs with h
    · exact iff_of_true rfl h
    · exact iff_of_false ofAdd_one_ne_one h
  have hk := right_act_k_ne_one e C S
  have hkS : SqLeft (act A e C.k) := sqLeft_of_involution hodd hk.2 hk.1
  have hT : (A.syl : Subgroup (centralizer ({t} : Set X))) ≤ χ.ker := by
    intro c hc
    rw [MonoidHom.mem_ker, hχ, ← act_of_mem e c.2]
    have hcT : (c : X) ∈ A.T := ⟨c, hc, rfl⟩
    obtain ⟨r, hr, i, j, hi, hj, hc'⟩ := exists_eq_of_mem_T C hcT
    rw [hc', act_mul e (mul_mem (L_le_C (A := A) hr.2) (pow_mem t_mem_C i))
      (pow_mem (k_mem_C C) j), act_mul e (L_le_C (A := A) hr.2) (pow_mem t_mem_C i),
      act_pow e t_mem_C, act_t, one_pow, mul_one, act_of_mem_L e hr.2, act_pow e (k_mem_C C),
      sqLeft_mul]
    interval_cases j
    · simp only [pow_zero]
      exact iff_of_true (sqLeft_incl _) sqLeft_one
    · simp only [pow_one]
      exact iff_of_true (sqLeft_incl _) hkS
  have hdvd : χ.ker.index ∣ (A.syl : Subgroup (centralizer ({t} : Set X))).index :=
    Subgroup.index_dvd_of_le hT
  have hnd := Sylow.not_dvd_index A.syl
  have hle : χ.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    calc Nat.card χ.range ≤ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_le_card_group _
      _ = 2 := by rw [Nat.card_eq_fintype_card]; rfl
  have hpos : χ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : χ.ker.index = 1 := by
    by_contra hne
    have h2 : χ.ker.index = 2 := by omega
    rw [h2] at hdvd
    exact hnd hdvd
  have hker : χ.ker = ⊤ := Subgroup.index_eq_one.mp h1
  have hm : (⟨g, hg⟩ : centralizer ({t} : Set X)) ∈ χ.ker := by rw [hker]; exact mem_top _
  rw [MonoidHom.mem_ker, hχ] at hm
  rwa [act_of_mem e hg]

include e in
theorem exists_frame (S : Gens A) {κ : X} (hκ : κ ∈ A.T) (hκ2 : κ ^ 2 = 1)
    (hκR : ∀ r ∈ A.R, κ * r = r * κ) (hψκ : ψX A κ ∉ R8) :
    ∃ (e' : L ⧸ pPrimeCore 2 L ≃* PSL2 F) (σ : F ≃+* F), orderOf σ = 2 ∧
      act A e' κ = SemidirectProduct.inr σ := by
  obtain ⟨hr, ho⟩ := right_act_ne_one e S hκ hκ2 hκR hψκ
  obtain ⟨C₀, hC₀⟩ := exists_conj_inr_of_involution (isOddPrimePower_card e S) _ ho hr
  refine ⟨e.trans (semilinearAction F (SemidirectProduct.inl C₀)⁻¹), (act A e κ).right, ?_, ?_⟩
  · rw [← orderOf_injective (SemidirectProduct.inr : (F ≃+* F) →* PGammaL2 F)
      SemidirectProduct.inr_injective, ← hC₀]
    refine Eq.trans (SemiconjBy.orderOf_eq (SemidirectProduct.inl C₀)⁻¹ ?_).symm ho
    change _ * _ = _ * _
    group
  · rw [act_trans, hC₀]

end CFSG.ComponentClassification.HSFLit.L2K
