module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245NaturalLin2

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.QuasithinUnique.Setup.Campbell CFSG.SL2MinimalFaithful
open scoped commutatorElement MatrixGroups LinearAlgebra.Projectivization

namespace C56

section Coordinates

variable {F : Type} [Field F]

theorem kl0 [CharP F 2] (g : (Fin 2 → F) →+ (Fin 2 → F))
    (ha : ∀ (s : F) (v : Fin 2 → F), g ![v 0 + s * v 1, v 1] = ![g v 0 + s * g v 1, g v 1])
    (hb : ∃ h' : Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ v : Fin 2 → F, g ![v 0, v 0 + v 1] = h' • g v)
    (hinj : Function.Injective g) {m : ℕ} (hm : ∀ v, g^[2 ^ m] v = v) :
    ∃ ν : F, ∀ v : Fin 2 → F, g v = ![v 0 + ν * v 1, v 1] := by
  have hdec : ∀ x y : F, (![x, y] : Fin 2 → F) = ![x, 0] + ![0, y] := by
    intro x y; ext i; fin_cases i <;> simp
  have hA : ∀ x : F, g ![x, 0] 1 = 0 := by
    intro x
    have h := congrFun (ha 1 ![x, 0]) 0
    simpa using h
  have hB : ∀ s y : F, g ![s * y, 0] 0 = s * g ![0, y] 1 := by
    intro s y
    have h := congrFun (ha s ![0, y]) 0
    have e : (![s * y, y] : Fin 2 → F) = ![s * y, 0] + ![0, y] := by
      ext i; fin_cases i <;> simp
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_add] at h
    rw [e, map_add] at h
    simp only [Pi.add_apply] at h
    linear_combination h
  set μ := g ![0, 1] 1 with hμ
  have hα : ∀ x : F, g ![x, 0] 0 = x * μ := by
    intro x
    have := hB x 1
    simpa [mul_comm] using this
  have hβ1 : ∀ y : F, g ![0, y] 1 = y * μ := by
    intro y
    have := hB 1 y
    rw [one_mul, one_mul, hα y] at this
    exact this.symm
  set δ : F → F := fun y => g ![0, y] 0 with hδ
  have hg : ∀ v : Fin 2 → F, g v = ![μ * v 0 + δ (v 1), μ * v 1] := by
    intro v
    have hv : v = ![v 0, 0] + ![0, v 1] := by rw [← hdec]; ext i; fin_cases i <;> simp
    conv_lhs => rw [hv, map_add]
    ext i
    fin_cases i
    · simp [hα, hδ, mul_comm]
    · simp [hA, hβ1, mul_comm]
  have hδ0 : δ 0 = 0 := by
    have : (![0, 0] : Fin 2 → F) = 0 := by ext i; fin_cases i <;> rfl
    simp only [hδ, this, map_zero]
    rfl
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 : g ![1, 0] = g 0 := by
      rw [map_zero]
      ext i; fin_cases i
      · simp [hα, h0]
      · simp [hA]
    have h2 := congrFun (hinj h1) 0
    simp at h2
  obtain ⟨h', hh'⟩ := hb
  have hδlin : ∀ x : F, δ x = (h' 0 0 * μ - μ) * x := by
    intro x
    have h1 := congrFun (hh' ![x, 0]) 0
    rw [hg] at h1
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, hg] at h1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hδ0] at h1
    linear_combination h1
  set ν := h' 0 0 * μ - μ with hν
  have hg2 : ∀ v : Fin 2 → F, g v = ![μ * v 0 + ν * v 1, μ * v 1] := by
    intro v; rw [hg]; ext i; fin_cases i <;> simp [hδlin]
  have hit : ∀ (k : ℕ) (w : Fin 2 → F), g^[k] w 1 = μ ^ k * w 1 := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih => intro w; rw [Function.iterate_succ_apply', hg2]; simp [ih, pow_succ]; ring
  have hμ1 : μ = 1 := by
    have h1 := hit (2 ^ m) ![0, 1]
    rw [hm] at h1
    simp at h1
    have h2 : (μ - 1) ^ 2 ^ m = 0 := by
      rw [sub_pow_char_pow, one_pow, sub_eq_zero]
      exact h1.symm
    have := pow_eq_zero_iff (by positivity) |>.mp h2
    exact sub_eq_zero.mp this
  refine ⟨ν, fun v => ?_⟩
  rw [hg2, hμ1]
  ext i; fin_cases i <;> simp

theorem kl_rootGrp [Finite F] [CharP F 2] (p : ℙ F (Fin 2 → F))
    (g : (Fin 2 → F) →+ (Fin 2 → F)) (hinj : Function.Injective g)
    (ha : ∀ t ∈ rootGrp p, ∀ v : Fin 2 → F, g (t • v) = t • g v)
    (hb : ∀ h : Matrix.SpecialLinearGroup (Fin 2) F, ∃ h' : Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ v : Fin 2 → F, g (h • v) = h' • g v)
    {m : ℕ} (hm : ∀ v, g^[2 ^ m] v = v) :
    ∃ t ∈ rootGrp p, ∀ v : Fin 2 → F, g v = t • v := by
  obtain ⟨x, hx⟩ := exists_smul_pt0 (k := F) p
  let g₀ : (Fin 2 → F) →+ (Fin 2 → F) :=
    (AddMonoidHom.mk' (fun v : Fin 2 → F => x⁻¹ • v) (fun a b => smul_add x⁻¹ a b)).comp
      (g.comp (AddMonoidHom.mk' (fun v : Fin 2 → F => x • v) (fun a b => smul_add x a b)))
  have hg₀ : ∀ v : Fin 2 → F, g₀ v = x⁻¹ • g (x • v) := fun v => rfl
  have hconj : ∀ u : Matrix.SpecialLinearGroup (Fin 2) F,
      u ∈ rootGrp (pt0 : ℙ F (Fin 2 → F)) → x * u * x⁻¹ ∈ rootGrp p := by
    intro u hu
    rw [← hx, mem_rootGrp_smul_iff]
    simpa [mul_assoc] using hu
  have hunip : ∀ s : F, unipotent s ∈ rootGrp (pt0 : ℙ F (Fin 2 → F)) := by
    intro s
    rw [rootGrp_pt0]
    exact ⟨Multiplicative.ofAdd s, rfl⟩
  have hg₀a : ∀ (s : F) (v : Fin 2 → F),
      g₀ ![v 0 + s * v 1, v 1] = ![g₀ v 0 + s * g₀ v 1, g₀ v 1] := by
    intro s v
    have h1 : (![v 0 + s * v 1, v 1] : Fin 2 → F) = (unipotent s : Matrix.SpecialLinearGroup (Fin 2) F) • v :=
      (smul_unipotent_vec s v).symm
    have h2 : g₀ ((unipotent s : Matrix.SpecialLinearGroup (Fin 2) F) • v) =
        (unipotent s : Matrix.SpecialLinearGroup (Fin 2) F) • g₀ v := by
      rw [hg₀, hg₀]
      have e : x • ((unipotent s : Matrix.SpecialLinearGroup (Fin 2) F) • v) =
          (x * unipotent s * x⁻¹) • (x • v) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        group
      rw [e, ha _ (hconj _ (hunip s)), ← mul_smul, ← mul_smul]
      congr 1
      group
    rw [h1, h2, smul_unipotent_vec]
  have hg₀b : ∃ h' : Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ v : Fin 2 → F, g₀ ![v 0, v 0 + v 1] = h' • g₀ v := by
    obtain ⟨h', hh'⟩ := hb (x * lowerElt (1 : F) * x⁻¹)
    refine ⟨x⁻¹ * h' * x, fun v => ?_⟩
    have h1 : (![v 0, v 0 + v 1] : Fin 2 → F) =
        (lowerElt (1 : F) : Matrix.SpecialLinearGroup (Fin 2) F) • v := by
      rw [smul_lowerElt_vec, one_mul]
    rw [h1, hg₀, hg₀]
    have e : x • ((lowerElt (1 : F) : Matrix.SpecialLinearGroup (Fin 2) F) • v) =
        (x * lowerElt (1 : F) * x⁻¹) • (x • v) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      group
    rw [e, hh', ← mul_smul, ← mul_smul]
    congr 1
    group
  have hinj₀ : Function.Injective g₀ := by
    intro v w h
    have h1 : g (x • v) = g (x • w) := by
      have := congrArg (fun z => x • z) h
      simpa [hg₀] using this
    have h2 := hinj h1
    exact smul_left_cancel x h2
  have hit : ∀ (k : ℕ) (v : Fin 2 → F), g₀^[k] v = x⁻¹ • g^[k] (x • v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply', ih, hg₀, smul_inv_smul, Function.iterate_succ_apply']
  have hm₀ : ∀ v, g₀^[2 ^ m] v = v := by
    intro v
    rw [hit, hm, inv_smul_smul]
  obtain ⟨ν, hν⟩ := kl0 g₀ hg₀a hg₀b hinj₀ hm₀
  refine ⟨x * unipotent ν * x⁻¹, hconj _ (hunip ν), fun v => ?_⟩
  have h1 : g v = x • g₀ (x⁻¹ • v) := by
    rw [hg₀, smul_inv_smul, smul_inv_smul]
  rw [h1, hν, ← smul_unipotent_vec, ← mul_smul, ← mul_smul]

end Coordinates

section SC

variable {G : Type} [Group G] [Finite G]

theorem lin2_selfCentralizing {L T : Subgroup G} (hL : IsShort2 L) {n : ℕ} (hn : 1 ≤ n)
    (hlin : IsLin2Type L n) (hT : IsSylowTwoOf T L) {r : G} (hrN : r ∈ normalizer (L : Set G))
    {m : ℕ} (hrm : r ^ 2 ^ m = 1)
    (hcomm : ∀ t ∈ T, ∀ u ∈ blockU L, (r * t * r⁻¹) * u * (r * t * r⁻¹)⁻¹ = t * u * t⁻¹) :
    ∃ b ∈ T, ∀ u ∈ blockU L, r * u * r⁻¹ = b * u * b⁻¹ := by
  classical
  obtain ⟨F, hFfield, hFfin, hcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hlin
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hq
  obtain ⟨p, hTp, hT2⟩ := lin2_exists_point hn hT hq α hαs hαk
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hL).trans (C1.blockQ_le L)
  have hrU : r ∈ normalizer (blockU L : Set G) := C1.mem_normalizer_blockU hrN
  have hrZ : r ∈ normalizer (blockZ L : Set G) := C1.mem_normalizer_blockZ hrN
  have hrU' : ∀ u ∈ blockU L, r * u * r⁻¹ ∈ blockU L := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hrU u).mp hu
  have hrZ' : ∀ z, z ∈ blockZ L ↔ r * z * r⁻¹ ∈ blockZ L := fun z =>
    Subgroup.mem_normalizer_iff.mp hrZ z
  have hrL : ∀ l ∈ L, r * l * r⁻¹ ∈ L := fun l hl => (Subgroup.mem_normalizer_iff.mp hrN l).mp hl
  let ρ : ↥(blockU L) → ↥(blockU L) := fun u => ⟨r * u * r⁻¹, hrU' u u.2⟩
  have hρmul : ∀ u v : blockU L, ρ (u * v) = ρ u * ρ v := by
    intro u v
    apply Subtype.ext
    show r * ((u : G) * v) * r⁻¹ = (r * u * r⁻¹) * (r * v * r⁻¹)
    group
  have hρinv : ∀ u : blockU L, ρ u⁻¹ = (ρ u)⁻¹ := fun u => Subtype.ext (by
    show r * ((u⁻¹ : blockU L) : G) * r⁻¹ = (r * (u : G) * r⁻¹)⁻¹
    rw [Subgroup.coe_inv]; group)
  have hkerZ : ∀ u : blockU L, β u = 1 → (u : G) ∈ blockZ L := fun u hu => by
    have : u ∈ (blockZ L).subgroupOf (blockU L) := hβk ▸ hu
    exact this
  have hZker : ∀ u : blockU L, (u : G) ∈ blockZ L → β u = 1 := fun u hu => by
    have : u ∈ (blockZ L).subgroupOf (blockU L) := hu
    rw [← hβk] at this
    exact this
  have hwd : ∀ u u' : blockU L, β u = β u' → β (ρ u) = β (ρ u') := by
    intro u u' h
    have h1 : β (u⁻¹ * u') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 : ((u⁻¹ * u' : blockU L) : G) ∈ blockZ L := hkerZ _ h1
    have h3 : r * ((u⁻¹ * u' : blockU L) : G) * r⁻¹ ∈ blockZ L := (hrZ' _).mp h2
    have h4 : (β (ρ u))⁻¹ * β (ρ u') = 1 := by
      rw [← map_inv, ← map_mul, ← hρinv, ← hρmul]
      apply hZker
      show r * ((u⁻¹ * u' : blockU L) : G) * r⁻¹ ∈ blockZ L
      exact h3
    exact (inv_mul_eq_one.mp h4)
  let cj : ↥L → ↥(blockU L) → ↥(blockU L) := fun l u =>
    ⟨(l : G) * u * (l : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L l.2) u).mp u.2⟩
  have hequiv : ∀ (l : L) (u : blockU L),
      Multiplicative.toAdd (β (cj l u)) = (α l) • Multiplicative.toAdd (β u) := by
    intro l u
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
    exact hβe l u (cj l u) (by simp [cj])
  let σ : Multiplicative (Fin 2 → F) → ↥(blockU L) := Function.surjInv hβs
  have hσ : ∀ w, β (σ w) = w := fun w => Function.surjInv_eq hβs w
  let gf : (Fin 2 → F) → (Fin 2 → F) := fun w =>
    Multiplicative.toAdd (β (ρ (σ (Multiplicative.ofAdd w))))
  have hgβ : ∀ u : blockU L,
      gf (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (ρ u)) := by
    intro u
    show Multiplicative.toAdd (β (ρ (σ (Multiplicative.ofAdd (Multiplicative.toAdd (β u)))))) = _
    rw [ofAdd_toAdd]
    congr 1
    exact hwd _ _ (hσ _)
  have hσt : ∀ w : Fin 2 → F, Multiplicative.toAdd (β (σ (Multiplicative.ofAdd w))) = w := by
    intro w; rw [hσ]; rfl
  have hgadd : ∀ w w' : Fin 2 → F, gf (w + w') = gf w + gf w' := by
    intro w w'
    set u := σ (Multiplicative.ofAdd w) with hu
    set u' := σ (Multiplicative.ofAdd w') with hu'
    have e1 : Multiplicative.toAdd (β u) = w := hσt w
    have e2 : Multiplicative.toAdd (β u') = w' := hσt w'
    have e3 : w + w' = Multiplicative.toAdd (β (u * u')) := by
      rw [map_mul, toAdd_mul, e1, e2]
    have g1 : gf w = Multiplicative.toAdd (β (ρ u)) := e1 ▸ hgβ u
    have g2 : gf w' = Multiplicative.toAdd (β (ρ u')) := e2 ▸ hgβ u'
    rw [e3, hgβ, hρmul, map_mul, toAdd_mul, g1, g2]
  let g : (Fin 2 → F) →+ (Fin 2 → F) := AddMonoidHom.mk' gf hgadd
  have hgapp : ∀ w, g w = gf w := fun w => rfl
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    set u := σ (Multiplicative.ofAdd w) with hu
    have e1 : Multiplicative.toAdd (β u) = w := hσt w
    have h1 : Multiplicative.toAdd (β (ρ u)) = 0 := by
      rw [← hgβ u, e1]; exact hw
    have h2 : β (ρ u) = 1 := toAdd_eq_zero.mp h1
    have h3 : ((ρ u : blockU L) : G) ∈ blockZ L := hkerZ _ h2
    have h4 : (u : G) ∈ blockZ L := (hrZ' _).mpr h3
    have h5 : β u = 1 := hZker _ h4
    rw [← e1, h5]; rfl
  have hgk : ∀ (k : ℕ) (u : blockU L), gf^[k] (Multiplicative.toAdd (β u)) =
      Multiplicative.toAdd (β ⟨r ^ k * u * (r ^ k)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hrU k) u).mp u.2⟩) := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [Function.iterate_succ_apply, hgβ, ih]
      congr 2
      apply Subtype.ext
      show r ^ k * (r * (u : G) * r⁻¹) * (r ^ k)⁻¹ = r ^ (k + 1) * u * (r ^ (k + 1))⁻¹
      rw [pow_succ]; group
  have hgm : ∀ w : Fin 2 → F, g^[2 ^ m] w = w := by
    intro w
    set u := σ (Multiplicative.ofAdd w) with hu
    have e1 : Multiplicative.toAdd (β u) = w := hσt w
    have : (g^[2 ^ m]) w = gf^[2 ^ m] w := rfl
    rw [this, ← e1, hgk]
    congr 2
    apply Subtype.ext
    show r ^ 2 ^ m * (u : G) * (r ^ 2 ^ m)⁻¹ = u
    rw [hrm]; group
  have hga : ∀ t ∈ rootGrp p, ∀ v : Fin 2 → F, g (t • v) = t • g v := by
    intro t ht v
    obtain ⟨l, rfl⟩ := hαs t
    have hlT : (l : G) ∈ T := (hT2 l).mp ht
    set u := σ (Multiplicative.ofAdd v) with hu
    have e1 : Multiplicative.toAdd (β u) = v := hσt v
    have e2 : (α l) • v = Multiplicative.toAdd (β (cj l u)) := by rw [hequiv, e1]
    have e3 : ρ (cj l u) = cj l (ρ u) := by
      apply Subtype.ext
      show r * ((l : G) * u * (l : G)⁻¹) * r⁻¹ = (l : G) * (r * u * r⁻¹) * (l : G)⁻¹
      have := hcomm l hlT (r * u * r⁻¹) (hrU' u u.2)
      calc r * ((l : G) * u * (l : G)⁻¹) * r⁻¹
          = (r * l * r⁻¹) * (r * u * r⁻¹) * (r * l * r⁻¹)⁻¹ := by group
        _ = l * (r * u * r⁻¹) * l⁻¹ := this
    have g1 : gf v = Multiplicative.toAdd (β (ρ u)) := e1 ▸ hgβ u
    rw [hgapp, hgapp, e2, hgβ, e3, hequiv, g1]
  have hgb : ∀ h : Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ h' : Matrix.SpecialLinearGroup (Fin 2) F, ∀ v : Fin 2 → F, g (h • v) = h' • g v := by
    intro h
    obtain ⟨l, rfl⟩ := hαs h
    refine ⟨α ⟨r * l * r⁻¹, hrL l l.2⟩, fun v => ?_⟩
    set u := σ (Multiplicative.ofAdd v) with hu
    have e1 : Multiplicative.toAdd (β u) = v := hσt v
    have e2 : (α l) • v = Multiplicative.toAdd (β (cj l u)) := by rw [hequiv, e1]
    have e3 : ρ (cj l u) = cj ⟨r * l * r⁻¹, hrL l l.2⟩ (ρ u) := by
      apply Subtype.ext
      show r * ((l : G) * u * (l : G)⁻¹) * r⁻¹ =
        (r * l * r⁻¹) * (r * u * r⁻¹) * (r * l * r⁻¹)⁻¹
      group
    have g1 : gf v = Multiplicative.toAdd (β (ρ u)) := e1 ▸ hgβ u
    rw [hgapp, hgapp, e2, hgβ, e3, hequiv, g1]
  obtain ⟨t, ht, hgt⟩ := kl_rootGrp p g hginj hga hgb (m := m) hgm
  obtain ⟨bL, rfl⟩ := hαs t
  have hbT : (bL : G) ∈ T := (hT2 bL).mp ht
  refine ⟨bL, hbT, ?_⟩
  have hUab : ∀ a ∈ blockU L, ∀ c ∈ blockU L, a * c = c * a := (C1.elemAb2_blockU hL).1
  have hT1 : ∀ l : L, l ∈ α.ker ↔ (l : G) ∈ blockQ L := fun l => by
    rw [hαk]; exact (mem_blockQ_iff l).symm
  set b : G := (bL : G) with hb
  set r' : G := b⁻¹ * r with hr'
  have hbN : b ∈ normalizer (L : Set G) := Subgroup.le_normalizer bL.2
  have hr'N : r' ∈ normalizer (L : Set G) := mul_mem (inv_mem hbN) hrN
  have hr'U : r' ∈ normalizer (blockU L : Set G) := C1.mem_normalizer_blockU hr'N
  have hr'U' : ∀ u ∈ blockU L, r' * u * r'⁻¹ ∈ blockU L := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hr'U u).mp hu
  have hr'U'' : ∀ u ∈ blockU L, r'⁻¹ * u * r' ∈ blockU L := fun u hu => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hr'U) u).mp hu
    simpa using this
  let ρ' : ↥(blockU L) → ↥(blockU L) := fun u => ⟨r' * u * r'⁻¹, hr'U' u u.2⟩
  let ρ'' : ↥(blockU L) → ↥(blockU L) := fun u => ⟨r'⁻¹ * u * r', hr'U'' u u.2⟩
  have hρ'ρ'' : ∀ u, ρ' (ρ'' u) = u := fun u =>
    Subtype.ext (by show r' * (r'⁻¹ * u * r') * r'⁻¹ = u; group)
  have hρ'_eq : ∀ u : blockU L, ρ' u = cj (bL⁻¹) (ρ u) := fun u => Subtype.ext (by
    show r' * u * r'⁻¹ = ((bL⁻¹ : L) : G) * (r * u * r⁻¹) * ((bL⁻¹ : L) : G)⁻¹
    rw [hr', Subgroup.coe_inv, ← hb]; group)
  have hβtriv : ∀ u : blockU L, β (ρ' u) = β u := by
    intro u
    apply Multiplicative.toAdd.injective
    have h1 : Multiplicative.toAdd (β (ρ u)) = (α bL) • Multiplicative.toAdd (β u) := by
      rw [← hgβ u, ← hgapp, hgt]
    rw [hρ'_eq, hequiv, map_inv, h1, inv_smul_smul]
  have hβtriv' : ∀ u : blockU L, β (ρ'' u) = β u := by
    intro u
    have := hβtriv (ρ'' u)
    rw [hρ'ρ''] at this
    exact this.symm
  have hαl' : ∀ (l : L) (hl' : r' * (l : G) * r'⁻¹ ∈ L),
      α ⟨r' * (l : G) * r'⁻¹, hl'⟩ = α l := by
    intro l hl'
    set l' : L := ⟨r' * (l : G) * r'⁻¹, hl'⟩ with hl'def
    have key : ∀ w : Fin 2 → F, (α l') • w = (α l) • w := by
      intro w
      set u := σ (Multiplicative.ofAdd w) with hu
      have e1 : Multiplicative.toAdd (β u) = w := hσt w
      have e2 : cj l' u = ρ' (cj l (ρ'' u)) := by
        apply Subtype.ext
        show (r' * (l : G) * r'⁻¹) * u * (r' * (l : G) * r'⁻¹)⁻¹ =
          r' * ((l : G) * (r'⁻¹ * u * r') * (l : G)⁻¹) * r'⁻¹
        group
      have h3 : Multiplicative.toAdd (β (cj l' u)) = (α l) • Multiplicative.toAdd (β u) := by
        rw [e2, hβtriv, hequiv, hβtriv']
      rw [← e1, ← hequiv l' u, h3]
    have h4 : (α l)⁻¹ * α l' = 1 :=
      sl2_eq_one_of_forall_smul_eq (fun w => by rw [mul_smul, key w, inv_smul_smul])
    exact (inv_mul_eq_one.mp h4).symm
  have hcjl : ∀ (l : L) (hl' : r' * (l : G) * r'⁻¹ ∈ L) (u : blockU L),
      cj ⟨r' * (l : G) * r'⁻¹, hl'⟩ u = cj l u := by
    intro l hl' u
    set l' : L := ⟨r' * (l : G) * r'⁻¹, hl'⟩ with hl'def
    have hker : l'⁻¹ * l ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαl' l hl', inv_mul_cancel]
    have hq : ((l'⁻¹ * l : L) : G) ∈ blockQ L := (hT1 _).mp hker
    set qG : G := ((l'⁻¹ * l : L) : G) with hqG
    have hcomm' : qG * u * qG⁻¹ = u := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (C1.blockU_comm hL u u.2 qG hq).symm
    have hl_eq : (l : G) = (l' : G) * qG := by
      rw [hqG]; simp
    apply Subtype.ext
    show (l' : G) * u * (l' : G)⁻¹ = (l : G) * u * (l : G)⁻¹
    rw [hl_eq]
    calc (l' : G) * u * (l' : G)⁻¹ = (l' : G) * (qG * u * qG⁻¹) * (l' : G)⁻¹ := by rw [hcomm']
      _ = ((l' : G) * qG) * u * ((l' : G) * qG)⁻¹ := by group
  have hKU : blockU L ≤ blockU L ⊓ centralizer ({r'} : Set G) := by
    refine (C1.commutator_blockU hL).symm.le.trans ?_
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have hlU : l * u⁻¹ * l⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L hl) _).mp (inv_mem hu)
    have hcommU : ⁅u, l⁆ ∈ blockU L := by
      have := mul_mem hu hlU
      rw [commutatorElement_def]
      simpa [mul_assoc] using this
    refine ⟨hcommU, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    set lL : L := ⟨l, hl⟩ with hlL
    have hl' : r' * l * r'⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hr'N l).mp hl
    set u' : blockU L := ⟨u, hu⟩ with hu'
    set z₀ : blockU L := u'⁻¹ * ρ' u' with hz₀def
    have hz₀Z : (z₀ : G) ∈ blockZ L := hkerZ z₀ (by
      rw [hz₀def, map_mul, map_inv, hβtriv, inv_mul_cancel])
    have hz₀l : l * (z₀ : G) = (z₀ : G) * l := Subgroup.mem_centralizer_iff.mp hz₀Z.2 l hl
    have hu₂ : r' * u * r'⁻¹ = u * (z₀ : G) := by
      rw [hz₀def, Subgroup.coe_mul, Subgroup.coe_inv]
      show r' * u * r'⁻¹ = u * (u⁻¹ * (r' * u * r'⁻¹))
      group
    have hx : (r' * l * r'⁻¹) * (r' * u * r'⁻¹)⁻¹ * (r' * l * r'⁻¹)⁻¹ = l * (r' * u * r'⁻¹)⁻¹ * l⁻¹ := by
      have h1 := congrArg Subtype.val (hcjl lL hl' (ρ' u')⁻¹)
      simpa [cj, ρ', Subgroup.coe_inv] using h1
    have hfinal : r' * ⁅u, l⁆ * r'⁻¹ = ⁅u, l⁆ := by
      calc r' * ⁅u, l⁆ * r'⁻¹
          = (r' * u * r'⁻¹) * ((r' * l * r'⁻¹) * (r' * u * r'⁻¹)⁻¹ * (r' * l * r'⁻¹)⁻¹) := by
            rw [commutatorElement_def]; group
        _ = (r' * u * r'⁻¹) * (l * (r' * u * r'⁻¹)⁻¹ * l⁻¹) := by rw [hx]
        _ = (u * z₀) * (l * (u * z₀)⁻¹ * l⁻¹) := by rw [hu₂]
        _ = u * (z₀ * l * (z₀ : G)⁻¹) * u⁻¹ * l⁻¹ := by group
        _ = u * l * u⁻¹ * l⁻¹ := by
          have : (z₀ : G) * l * (z₀ : G)⁻¹ = l := by
            rw [← hz₀l]; group
          rw [this]
        _ = ⁅u, l⁆ := by rw [commutatorElement_def]
    calc r' * ⁅u, l⁆ = (r' * ⁅u, l⁆ * r'⁻¹) * r' := by group
      _ = ⁅u, l⁆ * r' := by rw [hfinal]
  intro u hu
  have hcu : r' * u = u * r' := (Subgroup.mem_centralizer_iff.mp (hKU hu).2) r' rfl
  have hrr : r = b * r' := by rw [hr']; group
  calc r * u * r⁻¹ = b * (r' * u * r'⁻¹) * b⁻¹ := by rw [hrr]; group
    _ = b * u * b⁻¹ := by rw [hcu]; group

end SC

end C56

end CFSG.QuasithinUnique
