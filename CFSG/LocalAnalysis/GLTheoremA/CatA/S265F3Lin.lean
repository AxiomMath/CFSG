module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2LinResB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Step

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.GLTheoremA.HDescLinRes

theorem glaPLayer_ne_bot_of_congr {T T' : Type} [Group T] [Group T'] [Finite T] [Finite T'] {p : ℕ}
    (hp : p.Prime) (e : T ≃* T') (a b : MulAut T)
    (h : GLAPLayer p (fixSubgroup (MulAut.congr e a) ⊓ fixSubgroup (MulAut.congr e b)) ≠ ⊥) :
    GLAPLayer p (fixSubgroup a ⊓ fixSubgroup b) ≠ ⊥ := by
  intro hbot
  apply h
  rw [fixSubgroup_mulAutCongr, fixSubgroup_mulAutCongr,
    ← Subgroup.map_inf_eq _ _ _ (e.injective : Function.Injective (e : T →* T')),
    ← glaPLayer_map_eq_of_injective hp (e : T →* T') e.injective, hbot, Subgroup.map_bot]

section Model

variable {k : Type} [Field k] [Finite k]

theorem glaPLayer_ne_bot_of_field_linear [CharP k 2] {e : ℕ} (he : Even e) (he1 : 1 ≤ e)
    (hK : Nat.card k = 2 ^ e) {x c : MulAut (projectiveSL 3 k)} (hx3 : x ^ 3 = 1)
    (hxL : x ∉ linearAutGroup 3 k) (hcL : c ∈ linearAutGroup 3 k) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1)
    (hcomm : x * c = c * x) {t : projectiveSL 3 k} (ht : orderOf t = 2) (hct : c t = t) :
    GLAPLayer 3 (fixSubgroup x ⊓ fixSubgroup c) ≠ ⊥ := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hord⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent Nat.prime_two he1
      (le_refl 3) hK
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 (fun h => hxL (h ▸ Subgroup.one_mem _))
  obtain ⟨h3e, σ, -, ⟨h, hhL, hxh⟩, hk₀⟩ := hord 3 Nat.prime_three (by norm_num) x
    (LinearFlag.mem_semilinearAutGroup_of_pow_odd (le_refl 3) (by decide) hx3) hxL hxo
  obtain ⟨H, rfl⟩ := mem_linearAutGroup_iff.1 hhL
  obtain ⟨M, rfl⟩ := mem_linearAutGroup_iff.1 hcL
  set g := LinearFlag.conjAut 3 k H with hg
  set M' := H⁻¹ * M * H with hM'
  have hcM' : LinearFlag.conjAut 3 k M' = g⁻¹ * LinearFlag.conjAut 3 k M * g := by
    rw [hM', map_mul, map_mul, map_inv]
  have hfσ : fieldAut 3 k σ = g⁻¹ * x * g := by
    rw [hxh]
    group
  have he' : e % 2 = 0 := Nat.even_iff.1 he
  have hf₀ : 2 ≤ e / 3 := by omega
  have h3₀ : 3 ∣ Nat.card (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) - 1 := by
    obtain ⟨m, hm⟩ : Even (e / 3) := Nat.even_iff.2 (by omega)
    have h4 : 2 ^ (e / 3) % 3 = 1 := by
      rw [hm, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    rw [hk₀]
    omega
  have hM1 : LinearFlag.conjAut 3 k M' ≠ 1 := by
    rw [hcM']
    intro h1
    apply hc1
    calc LinearFlag.conjAut 3 k M = g * (g⁻¹ * LinearFlag.conjAut 3 k M * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hM3 : LinearFlag.conjAut 3 k M' ^ 3 = 1 := by
    rw [hcM']
    have := conj_pow (a := g⁻¹) (b := LinearFlag.conjAut 3 k M) (i := 3)
    rw [inv_inv] at this
    rw [this, hc3]
    group
  have hcomm' : fieldAut 3 k σ * LinearFlag.conjAut 3 k M' =
      LinearFlag.conjAut 3 k M' * fieldAut 3 k σ := by
    rw [hfσ, hcM']
    calc g⁻¹ * x * g * (g⁻¹ * LinearFlag.conjAut 3 k M * g)
        = g⁻¹ * (x * LinearFlag.conjAut 3 k M) * g := by group
      _ = g⁻¹ * (LinearFlag.conjAut 3 k M * x) * g := by rw [hcomm]
      _ = g⁻¹ * LinearFlag.conjAut 3 k M * g * (g⁻¹ * x * g) := by group
  have ht' : orderOf (g⁻¹ t) = 2 := by
    rw [← ht]
    exact orderOf_injective (g⁻¹ : MulAut (projectiveSL 3 k)).toMonoidHom (MulEquiv.injective _) t
  have hfix' : LinearFlag.conjAut 3 k M' (g⁻¹ t) = g⁻¹ t := by
    rw [hcM']
    simp only [MulAut.mul_apply, MulAut.apply_inv_self, hct]
  have hred := glaPLayer_ne_bot_of_fieldAut_conjAut hf₀ hk₀ h3₀ hM1 hM3 hcomm' ht' hfix'
  apply glaPLayer_ne_bot_of_conj Nat.prime_three g⁻¹
  rw [show g⁻¹ * x * g⁻¹⁻¹ = fieldAut 3 k σ by rw [hfσ, inv_inv],
    show g⁻¹ * LinearFlag.conjAut 3 k M * g⁻¹⁻¹ = LinearFlag.conjAut 3 k M' by rw [hcM', inv_inv]]
  exact hred

theorem exists_layer_of_linear_model {T : Type} [Group T] [Finite T] [CharP k 2] {n : ℕ}
    (hn : Even n) (hn1 : 1 ≤ n) (hK : Nat.card k = 2 ^ n) (e : T ≃* projectiveSL 3 k)
    {β : MulAut T} (hβ3 : β ^ 3 = 1) (hβL : MulAut.congr e β ∉ linearAutGroup 3 k)
    (Eb : Subgroup (MulAut T)) (hE3 : ∀ c ∈ Eb, c ^ 3 = 1)
    (hEcomm : ∀ c ∈ Eb, β * c = c * β) (h9 : 9 ≤ Nat.card Eb) {t : T} (ht : orderOf t = 2)
    (hEt : ∀ c ∈ Eb, c t = t) :
    ∃ c ∈ Eb, c ∉ Subgroup.zpowers β ∧ GLAPLayer 3 (fixSubgroup β ⊓ fixSubgroup c) ≠ ⊥ := by
  classical
  haveI : Finite (MulAut (projectiveSL 3 k)) :=
    Finite.of_injective (fun (g : MulAut (projectiveSL 3 k)) (w : projectiveSL 3 k) => g w)
      (fun g h hgh => MulEquiv.ext (congrFun hgh))
  have hφinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hcard' : Nat.card (Eb.map (MulAut.congr e).toMonoidHom) = Nat.card Eb :=
    Subgroup.card_map_of_injective hφinj
  have hE3' : ∀ c ∈ Eb.map (MulAut.congr e).toMonoidHom, c ^ 3 = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow, hE3 c hc, map_one]
  have hbound := card_le_three_mul_card_inf_linear Nat.prime_two hn1 hK
    (B := Eb.map (MulAut.congr e).toMonoidHom) hE3'
  have hne : (Eb.map (MulAut.congr e).toMonoidHom ⊓ linearAutGroup 3 k :
      Subgroup (MulAut (projectiveSL 3 k))) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hbound
    omega
  obtain ⟨⟨c', hc'⟩, hc'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨hc'E, hc'L⟩ := Subgroup.mem_inf.1 hc'
  obtain ⟨c, hcE, rfl⟩ := hc'E
  have hcL : MulAut.congr e c ∈ linearAutGroup 3 k := hc'L
  have hc1 : MulAut.congr e c ≠ 1 := fun h => hc'1 (Subtype.ext h)
  have hx3 : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hc3 : MulAut.congr e c ^ 3 = 1 := by rw [← map_pow, hE3 c hcE, map_one]
  have hxc : MulAut.congr e β * MulAut.congr e c = MulAut.congr e c * MulAut.congr e β := by
    rw [← map_mul, ← map_mul, hEcomm c hcE]
  have hxo : Nat.card (Subgroup.zpowers (MulAut.congr e β)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 (fun h => hβL (h ▸ Subgroup.one_mem _))
  have hxL := CFSG.LocalAnalysis.GLTheoremA.S265.s265_inf_zpowers_bot Nat.prime_three hxo hβL
  refine ⟨c, hcE, ?_, ?_⟩
  · intro hcβ
    apply hc1
    have hmem : MulAut.congr e c ∈
        (linearAutGroup 3 k ⊓ Subgroup.zpowers (MulAut.congr e β) : Subgroup _) := by
      refine Subgroup.mem_inf.2 ⟨hcL, ?_⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hcβ
      exact Subgroup.mem_zpowers_iff.2 ⟨i, (map_zpow (MulAut.congr e) β i).symm⟩
    rw [hxL] at hmem
    exact Subgroup.mem_bot.1 hmem
  · apply glaPLayer_ne_bot_of_congr Nat.prime_three e
    have ht' : orderOf (e t) = 2 := by
      rw [← ht]
      exact orderOf_injective e.toMonoidHom e.injective t
    have hct : MulAut.congr e c (e t) = e t := by
      show e (c (e.symm (e t))) = e t
      rw [MulEquiv.symm_apply_apply, hEt c hcE]
    exact glaPLayer_ne_bot_of_field_linear hn hn1 hK hx3 hβL hcL hc1 hc3 hxc ht' hct

end Model

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end
