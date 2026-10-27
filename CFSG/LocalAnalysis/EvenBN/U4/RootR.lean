module

public import CFSG.LocalAnalysis.EvenBN.U4.RootQ1R

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_sup mem_normalizer_inf
  exists_mem_inf_centralizer_mul_of_coprime card_sup_mul_card_inf_eq)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem exists_torusElt_eq (hS : Setting h L η t Q T) {i : G} (hi : i ∈ miyamotoIG h L η) :
    ∃ p : Kˣ × Kˣ, ∃ hp : miyamotoIParam h p = 1, hS.torusElt p hp = i := by
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hi
  obtain ⟨p, hp, hpg⟩ := hg
  refine ⟨p, MonoidHom.mem_ker.1 hp, ?_⟩
  simp only [torusElt]
  congr 2
  exact Subtype.ext hpg

theorem exists_torusElt_eq_of_mem_I1 (hS : Setting h L η t Q T) {s : G}
    (hs : s ∈ miyamotoI1G h L η) :
    ∃ p : Kˣ × Kˣ, ∃ hp : miyamotoIParam h p = 1, hS.torusElt p hp = s ∧
      miyamotoWeightA p = 1 := by
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hs
  obtain ⟨u, -, hgu⟩ := (mem_miyamotoI1 h).1 hg
  have hp : miyamotoIParam h (u, u) = 1 :=
    (miyamotoIHom_mem_miyamotoI_iff h (u, u)).1 (hgu ▸ miyamotoI1_le_I h hg)
  refine ⟨(u, u), hp, ?_, ?_⟩
  · simp only [torusElt]
    congr 2
    exact Subtype.ext hgu.symm
  · simp [miyamotoWeightA]

theorem torusElt_mem_pull (hS : Setting h L η t Q T) {M : Subgroup (GL (Fin 4) K)}
    (p : Kˣ × Kˣ) (hp : miyamotoIParam h p = 1) (hpM : miyamotoIHom h p ∈ M) :
    hS.torusElt p hp ∈ miyamotoPull h L η M :=
  (symm_mem_miyamotoPull_iff h L η).2 hpM

theorem exists_torusElt_weightA_ne_one (hS : Setting h L η t Q T) :
    (∃ p : Kˣ × Kˣ, ∃ hp : miyamotoIParam h p = 1,
      hS.torusElt p hp ∈ miyamotoI2r1G h L η ∧ miyamotoWeightA p ≠ 1) ∧
    (∃ p : Kˣ × Kˣ, ∃ hp : miyamotoIParam h p = 1,
      hS.torusElt p hp ∈ miyamotoPull h L η (miyamotoI1r2 h) ∧ miyamotoWeightA p ≠ 1) ∧
    (∃ p : Kˣ × Kˣ, ∃ hp : miyamotoIParam h p = 1,
      hS.torusElt p hp ∈ miyamotoI2G h L η ∧ miyamotoWeightA p ≠ 1) := by
  obtain ⟨u, hu, hu2⟩ := exists_fixed_unit_sq_ne_one h hS.two_le
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hmem : ∀ {M : Subgroup (GL (Fin 4) K)} {p : Kˣ × Kˣ}, M ≤ miyamotoI h →
      miyamotoIHom h p ∈ M → miyamotoWeightA p ≠ 1 →
      ∃ p : Kˣ × Kˣ, ∃ hp : miyamotoIParam h p = 1,
        hS.torusElt p hp ∈ miyamotoPull h L η M ∧ miyamotoWeightA p ≠ 1 := by
    intro M p hMI hpM hpA
    have hp := (miyamotoIHom_mem_miyamotoI_iff h p).1 (hMI hpM)
    exact ⟨p, hp, hS.torusElt_mem_pull p hp hpM, hpA⟩
  refine ⟨hmem (miyamotoI2r1_le_I h) (miyamotoIHom_one_sq_mem_I2r1 h hu) ?_,
    hmem (miyamotoI1r2_le_I h) ((mem_miyamotoI1r2 h).2 ⟨u, hu, rfl⟩) ?_,
    hmem (miyamotoI2_le_I h) (miyamotoIHom_sq_one_mem_I2 h hu) ?_⟩
  · intro e
    have e' := congrArg (fun v : Kˣ => (v : K)) e
    simp only [coe_miyamotoWeightA, Units.val_one, Units.val_pow_eq_pow_val, one_mul] at e'
    exact hu2 (inv_eq_one.1 e')
  · intro e
    have e' := congrArg (fun v : Kˣ => (v : K)) e
    simp only [coe_miyamotoWeightA, Units.val_one, Units.val_inv_eq_inv_val, inv_inv] at e'
    exact hu2 (by rw [sq]; exact e')
  · intro e
    have e' := congrArg (fun v : Kˣ => (v : K)) e
    simp only [coe_miyamotoWeightA, Units.val_one, Units.val_pow_eq_pow_val, inv_one,
      mul_one] at e'
    exact hu2 e'

theorem IG_le_normalizer_RG (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (miyamotoRG h L η t Q : Set G) :=
  hS.IG_le_normalizer_Q1.trans hS.normalizer_Q1_le_normalizer_RG

theorem IG_le_normalizer_P1 (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤
      normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G) :=
  hS.IG_le_normalizer_Q1.trans hS.normalizer_Q1_le_normalizer_P1

theorem isPGroup_RG (hS : Setting h L η t Q T) : IsPGroup 2 (miyamotoRG h L η t Q) :=
  hS.isPGroup_miyamotoS.to_le hS.miyamotoRG_le_miyamotoS

theorem RG_le_normalizer_P1 (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ≤
      normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G) :=
  hS.miyamotoRG_le_miyamotoS.trans hS.miyamotoS_le_normalizer_P1

theorem RG_le_normalizer_F1 (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ≤ normalizer (miyamotoF1G h L η t : Set G) :=
  (hS.miyamotoRG_le_miyamotoS.trans hS.miyamotoS_le_normalizer_Q1).trans
    hS.normalizer_Q1_le_normalizer_F1

theorem mem_Q1_of_commute_torusElt (hS : Setting h L η t Q T) {s : G}
    (hs : s ∈ miyamotoS h L η t Q) (p : Kˣ × Kˣ) (hp : miyamotoIParam h p = 1)
    (hpA : miyamotoWeightA p ≠ 1) (hc : hS.torusElt p hp * s = s * hS.torusElt p hp) :
    s ∈ miyamotoF1G h L η t ⊔ Q := by
  refine (hS.crossedQ1_eq_zero_iff hs).1 ?_
  have h1 := hS.crossedQ1_torus_conj p hp (hS.miyamotoS_le_normalizer_Q1 hs)
  rw [show (hS.torusElt p hp)⁻¹ * s * hS.torusElt p hp = s by
    rw [mul_assoc, ← hc, inv_mul_cancel_left]] at h1
  exact eq_zero_of_mul_eq_self (fun e => hpA (Units.ext e)) h1.symm

theorem mem_F1_of_commute_torusElt (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) (p : Kˣ × Kˣ)
    (hp : miyamotoIParam h p = 1) (hpA : miyamotoWeightA p ≠ 1)
    (hc : hS.torusElt p hp * x = x * hS.torusElt p hp) : x ∈ miyamotoF1G h L η t := by
  refine (hS.coordP1_eq_zero_iff hx).1 ?_
  have h1 := hS.coordP1_torus_conj p hp hx
  rw [show (hS.torusElt p hp)⁻¹ * x * hS.torusElt p hp = x by
    rw [mul_assoc, ← hc, inv_mul_cancel_left]] at h1
  exact eq_zero_of_mul_eq_self (fun e => hpA (Units.ext e)) h1.symm

theorem RG_inf_centralizer_le_F1 (hS : Setting h L η t Q T) {X : Subgroup G} {p : Kˣ × Kˣ}
    {hp : miyamotoIParam h p = 1} (hpX : hS.torusElt p hp ∈ X) (hpA : miyamotoWeightA p ≠ 1) :
    miyamotoRG h L η t Q ⊓ centralizer (X : Set G) ≤ miyamotoF1G h L η t := by
  intro r hr
  obtain ⟨hrR, hrX⟩ := mem_inf.1 hr
  have hc : hS.torusElt p hp * r = r * hS.torusElt p hp := mem_centralizer_iff.1 hrX _ hpX
  have hQ := hS.mem_Q1_of_commute_torusElt (hS.miyamotoRG_le_miyamotoS hrR) p hp hpA hc
  have hP1 : r ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η := by
    rw [← hS.miyamotoRG_inf_Q1]
    exact mem_inf.2 ⟨hrR, hQ⟩
  exact hS.mem_F1_of_commute_torusElt hP1 p hp hpA hc

theorem RG_inf_centralizer_I2r1 (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2r1G h L η : Set G) = miyamotoEG h L η Q := by
  obtain ⟨⟨p, hp, hpX, hpA⟩, -, -⟩ := hS.exists_torusElt_weightA_ne_one
  refine le_antisymm (fun r hr => ?_) fun e he =>
    ⟨hS.P1_le_miyamotoRG (mem_sup_left (hS.E_le_F1 he)), hS.E_le_centralizer_S he⟩
  rw [hS.E_eq_F1_inf_centralizer_S]
  exact ⟨hS.RG_inf_centralizer_le_F1 hpX hpA hr, hr.2⟩

theorem RG_inf_centralizer_I1r2 (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ⊓ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G) =
      miyamotoF1G h L η t ⊓ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G) := by
  obtain ⟨-, ⟨p, hp, hpX, hpA⟩, -⟩ := hS.exists_torusElt_weightA_ne_one
  refine le_antisymm (fun r hr => ⟨hS.RG_inf_centralizer_le_F1 hpX hpA hr, hr.2⟩) fun y hy =>
    ⟨hS.P1_le_miyamotoRG (mem_sup_left hy.1), hy.2⟩

theorem F_eq_E_sup (hS : Setting h L η t Q T) :
    miyamotoFG h L η t Q = miyamotoEG h L η Q ⊔
      (miyamotoRG h L η t Q ⊓ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G)) := by
  rw [hS.RG_inf_centralizer_I1r2]
  rfl

theorem RG_inf_centralizer_I2 (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) =
      miyamotoF1G h L η t ⊓ centralizer (miyamotoI2G h L η : Set G) := by
  obtain ⟨-, -, ⟨p, hp, hpX, hpA⟩⟩ := hS.exists_torusElt_weightA_ne_one
  refine le_antisymm (fun r hr => ⟨hS.RG_inf_centralizer_le_F1 hpX hpA hr, hr.2⟩) fun y hy =>
    ⟨hS.P1_le_miyamotoRG (mem_sup_left hy.1), hy.2⟩

theorem exists_mul_of_mem_F1 (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF1G h L η t) :
    ∃ φ ∈ miyamotoFG h L η t Q, ∃ y ∈ miyamotoF1G h L η t ⊓
      centralizer (miyamotoI2G h L η : Set G), x = φ * y := by
  obtain ⟨-, hdec1, -, hdec2⟩ := hS.F1_torus_decomp
  obtain ⟨a, ha, c, hc, rfl⟩ := hdec1 x hx (mem_centralizer_bot x)
  obtain ⟨⟨haF, -⟩, haJ⟩ := ha
  obtain ⟨⟨hcF, -⟩, hcJ⟩ := hc
  obtain ⟨e, he, y, hy, rfl⟩ := hdec2 a haF haJ
  obtain ⟨⟨heF, -⟩, heS⟩ := he
  obtain ⟨⟨hyF, -⟩, hyI⟩ := hy
  have heE : e ∈ miyamotoEG h L η Q := by
    rw [hS.E_eq_F1_inf_centralizer_S]
    exact ⟨heF, heS⟩
  refine ⟨e * c, mul_mem (hS.E_le_F heE) (mem_sup_right ⟨hcF, hcJ⟩), y, ⟨hyF, hyI⟩, ?_⟩
  rw [mul_assoc, mul_assoc, hS.F1_comm hyF hcF]

theorem F1_eq_F_sup (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t = miyamotoFG h L η t Q ⊔
      (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)) := by
  rw [hS.RG_inf_centralizer_I2]
  refine le_antisymm (fun x hx => ?_) (sup_le hS.F_le_F1 inf_le_left)
  obtain ⟨φ, hφ, y, hy, rfl⟩ := hS.exists_mul_of_mem_F1 hx
  exact mul_mem (mem_sup_left hφ) (mem_sup_right hy)

theorem I1G_le_IG (_hS : Setting h L η t Q T) : miyamotoI1G h L η ≤ miyamotoIG h L η :=
  miyamotoPull_mono h L η (miyamotoI1_le_I h)

theorem A1G_inf_centralizer_I1 (hS : Setting h L η t Q T) :
    miyamotoA1G h L η ⊓ centralizer (miyamotoI1G h L η : Set G) = ⊥ := by
  have : CharP K 2 := h.charP
  rw [← miyamotoPull_inf_centralizer h L η _ (miyamotoI1_le_SU h)]
  have e : miyamotoA1 h ⊓ centralizer (miyamotoI1 h : Set (GL (Fin 4) K)) = ⊥ := by
    rw [← inf_eq_left.2 (miyamotoA1_le_P h), inf_assoc, miyamotoP_inf_centralizer_I1 h hS.two_le,
      miyamotoA1_inf_rootA]
  rw [e, miyamotoPull_bot]

theorem PG_inf_centralizer_I1 (hS : Setting h L η t Q T) :
    miyamotoPG h L η ⊓ centralizer (miyamotoI1G h L η : Set G) =
      miyamotoPull h L η (miyamotoRootA h) := by
  have : CharP K 2 := h.charP
  rw [← miyamotoPull_inf_centralizer h L η _ (miyamotoI1_le_SU h),
    miyamotoP_inf_centralizer_I1 h hS.two_le]

theorem F1_inf_centralizer_I1 (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊓ centralizer (miyamotoI1G h L η : Set G) = ⊥ := by
  refine eq_bot_iff.2 fun y hy => ?_
  obtain ⟨hyF, hyC⟩ := hy
  have hc := hS.crossed_mem_A1_of_mem_D1 (hS.F1_le_D1 hyF)
  have hcC := hS.crossed_mem_centralizer hS.I1G_le_IG hyC
  have h1 : y⁻¹ * t * y * t = 1 := by
    have : y⁻¹ * t * y * t ∈ (⊥ : Subgroup G) := by
      rw [← hS.A1G_inf_centralizer_I1]
      exact ⟨hc, hcC⟩
    exact mem_bot.1 this
  have hyA := (hS.crossed_eq_one_iff_F1 hyF).1 h1
  rw [← hS.A1G_inf_centralizer_I1]
  exact ⟨hyA, hyC⟩

theorem inv_mul_conj_mem_P1_of_mem_I1 (hS : Setting h L η t Q T) {r s : G}
    (hr : r ∈ miyamotoRG h L η t Q) (hs : s ∈ miyamotoI1G h L η) :
    r⁻¹ * (s * r * s⁻¹) ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η := by
  obtain ⟨p, hp, hps, hpA⟩ := hS.exists_torusElt_eq_of_mem_I1 (inv_mem hs)
  have hsR : s * r * s⁻¹ ∈ miyamotoRG h L η t Q :=
    (mem_normalizer_iff.1 (hS.IG_le_normalizer_RG (hS.I1G_le_IG hs)) r).1 hr
  have hrS := hS.miyamotoRG_le_miyamotoS hr
  have hsS := hS.miyamotoRG_le_miyamotoS hsR
  rw [← hS.miyamotoRG_inf_Q1]
  refine mem_inf.2 ⟨mul_mem (inv_mem hr) hsR,
    (hS.crossedQ1_eq_zero_iff (mul_mem (inv_mem hrS) hsS)).1 ?_⟩
  have h1 := hS.crossedQ1_torus_conj p hp (hS.miyamotoS_le_normalizer_Q1 hrS)
  rw [hps, inv_inv, hpA, Units.val_one, one_mul] at h1
  rw [hS.crossedQ1_mul (inv_mem hrS) hsS, hS.crossedQ1_inv hrS, h1, neg_add_cancel]

theorem inv_mul_conj_mem_F1_of_mem_I1 (hS : Setting h L η t Q T) {x s : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) (hs : s ∈ miyamotoI1G h L η) :
    x⁻¹ * (s * x * s⁻¹) ∈ miyamotoF1G h L η t := by
  obtain ⟨p, hp, hps, hpA⟩ := hS.exists_torusElt_eq_of_mem_I1 (inv_mem hs)
  have hsx : s * x * s⁻¹ ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η :=
    (mem_normalizer_iff.1 (hS.IG_le_normalizer_P1 (hS.I1G_le_IG hs)) x).1 hx
  refine (hS.coordP1_eq_zero_iff (mul_mem (inv_mem hx) hsx)).1 ?_
  have h1 := hS.coordP1_torus_conj p hp hx
  rw [hps, inv_inv, hpA, Units.val_one, one_mul] at h1
  have h2 := hS.coordP1_mul (inv_mem hx) hx
  rw [inv_mul_cancel, hS.coordP1_of_mem_F1 (one_mem _)] at h2
  rw [hS.coordP1_mul (inv_mem hx) hsx, h1]
  exact h2.symm

theorem exists_mul_of_mem_RG (hS : Setting h L η t Q T) {r : G}
    (hr : r ∈ miyamotoRG h L η t Q) :
    ∃ w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G),
      ∃ y ∈ miyamotoF1G h L η t, r = w * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable (miyamotoRG h L η t Q) := by
    have := hS.isPGroup_RG.isNilpotent
    infer_instance
  have hsolv' : Group.IsSolvable (miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) := by
    have := (hS.isPGroup_RG.to_le hS.P1_le_miyamotoRG).isNilpotent
    infer_instance
  have hI1 : miyamotoI1G h L η ≤ miyamotoIG h L η := hS.I1G_le_IG
  have hcop := coprime_of_odd_of_isPGroup (hS.odd_card_of_le_IG hI1) hS.isPGroup_RG
  have hcop' := coprime_of_odd_of_isPGroup (hS.odd_card_of_le_IG hI1)
    (hS.isPGroup_RG.to_le hS.P1_le_miyamotoRG)
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_mem_inf_centralizer_mul_of_coprime hS.P1_le_miyamotoRG
    hS.RG_le_normalizer_P1 (hI1.trans hS.IG_le_normalizer_RG) (hI1.trans hS.IG_le_normalizer_P1)
    hsolv hcop hr fun s hs => hS.inv_mul_conj_mem_P1_of_mem_I1 hr hs
  obtain ⟨c', hc', y, hy, rfl⟩ := exists_mem_inf_centralizer_mul_of_coprime le_sup_left
    hS.P1_le_normalizer_F1 (hI1.trans hS.IG_le_normalizer_P1)
    (hI1.trans hS.IG_le_normalizer_F1) hsolv' hcop' hn
    fun s hs => hS.inv_mul_conj_mem_F1_of_mem_I1 hn hs
  exact ⟨c * c', ⟨mul_mem hc.1 (hS.P1_le_miyamotoRG hc'.1), mul_mem hc.2 hc'.2⟩, y, hy, by group⟩

theorem card_W (hS : Setting h L η t Q T) :
    Nat.card (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) : Subgroup G) =
      (2 ^ f) ^ 4 := by
  set W := miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) with hW
  have hWF : W ≤ normalizer (miyamotoF1G h L η t : Set G) :=
    inf_le_left.trans hS.RG_le_normalizer_F1
  have h1 := card_sup_mul_card_inf_eq hWF
  have hsup : miyamotoF1G h L η t ⊔ W = miyamotoRG h L η t Q := by
    refine le_antisymm (sup_le (le_sup_left.trans hS.P1_le_miyamotoRG) inf_le_left) fun r hr => ?_
    obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hr
    have e : w * y = (w * y * w⁻¹) * w := by group
    rw [e]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 (hWF hw) y).1 hy)) (mem_sup_right hw)
  have hinf : miyamotoF1G h L η t ⊓ W = ⊥ := by
    rw [hW, ← inf_assoc, inf_comm (miyamotoF1G h L η t), inf_assoc,
      hS.F1_inf_centralizer_I1, inf_bot_eq]
  rw [hsup, hinf, card_bot, mul_one, hS.card_miyamotoRG, hS.card_F1] at h1
  have hq : 0 < (2 ^ f) ^ 8 := by positivity
  have : (2 ^ f) ^ 12 = (2 ^ f) ^ 8 * (2 ^ f) ^ 4 := by ring
  rw [this] at h1
  exact (Nat.eq_of_mul_eq_mul_left hq h1).symm

theorem RG_inf_C (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ⊓ centralizer ({t} : Set G) = miyamotoPG h L η := by
  refine le_antisymm (fun x hx => ?_) (le_inf (le_sup_right.trans hS.P1_le_miyamotoRG)
    hS.PG_le_C)
  obtain ⟨hxR, hxC⟩ := mem_inf.1 hx
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 hxC
  have hxS := hS.miyamotoRG_le_miyamotoS hxR
  have hQ : x ∈ miyamotoF1G h L η t ⊔ Q :=
    hS.mem_Q1_of_mem_miyamotoS hxS (by rw [hxt, inv_mul_cancel]; exact one_mem _)
  have hP1 : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η := by
    rw [← hS.miyamotoRG_inf_Q1]
    exact mem_inf.2 ⟨hxR, hQ⟩
  obtain ⟨y, hy, p, hp, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer' hS.PG_le_normalizer_F1 hP1
  have hyC : y ∈ centralizer ({t} : Set G) := by
    have := mul_mem hxC (inv_mem (hS.PG_le_C hp))
    rwa [mul_inv_cancel_right] at this
  have hyB : y ∈ miyamotoB1 h L η t := by
    rw [← hS.D1_inf_C]
    exact ⟨hS.F1_le_D1 hy, hyC⟩
  have hyA : y ∈ miyamotoA1G h L η := by
    rw [← hS.F1_inf_B1]
    exact ⟨hy, hyB⟩
  exact mul_mem (hS.A1G_le_PG hyA) hp

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
