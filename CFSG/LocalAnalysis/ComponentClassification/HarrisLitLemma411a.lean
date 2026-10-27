module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma48
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma49E

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

theorem card_centralizer_ge_four {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ e ∈ E, e ^ 2 = 1)
    (hcard : Nat.card E = 8) {y : G} (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) (hy2 : y ^ 2 = 1) :
    4 ≤ Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq, hy2])
  let δ : ↥E →* G :=
    { toFun := fun e => (e : G)⁻¹ * (y * e * y⁻¹)
      map_one' := by simp
      map_mul' := fun a b => by
        have hc1 := hcomm _ (inv_mem b.2) _ (hyE a a.2)
        have hc2 := hcomm _ (inv_mem a.2) _ (inv_mem b.2)
        simp only [Subgroup.coe_mul]
        calc ((a : G) * b)⁻¹ * (y * (a * b) * y⁻¹) =
            ((b : G)⁻¹ * (a : G)⁻¹) * ((y * a * y⁻¹) * (y * b * y⁻¹)) := by group
          _ = ((a : G)⁻¹ * (b : G)⁻¹) * ((y * a * y⁻¹) * (y * b * y⁻¹)) := by rw [hc2]
          _ = (a : G)⁻¹ * ((b : G)⁻¹ * (y * a * y⁻¹)) * (y * b * y⁻¹) := by group
          _ = (a : G)⁻¹ * ((y * a * y⁻¹) * (b : G)⁻¹) * (y * b * y⁻¹) := by rw [hc1]
          _ = (a : G)⁻¹ * (y * a * y⁻¹) * ((b : G)⁻¹ * (y * b * y⁻¹)) := by group }
  have hδ : ∀ e : ↥E, δ e = (e : G)⁻¹ * (y * e * y⁻¹) := fun _ => rfl
  have hker : Nat.card δ.ker = Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) := by
    have : δ.ker = (centralizer ({y} : Set G)).subgroupOf E := by
      ext e
      rw [MonoidHom.mem_ker, hδ, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
      constructor
      · intro h1
        have h2 : y * (e : G) * y⁻¹ = e := by
          calc y * (e : G) * y⁻¹ = (e : G) * ((e : G)⁻¹ * (y * e * y⁻¹)) := by group
            _ = e := by rw [h1, mul_one]
        calc (e : G) * y = (y * e * y⁻¹) * y := by rw [h2]
          _ = y * e := by group
      · intro h1
        rw [← h1]
        group
    rw [this, ← Subgroup.card_map_of_injective E.subtype_injective, subgroupOf_map_subtype,
      inf_comm]
  have hrange : δ.range ≤ E ⊓ centralizer ({y} : Set G) := by
    rintro _ ⟨e, rfl⟩
    rw [hδ]
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem e.2) (hyE e e.2), ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hd : (e : G)⁻¹ * (y * e * y⁻¹) ∈ E := mul_mem (inv_mem e.2) (hyE e e.2)
    have hd2 := hsq _ hd
    have hy2' : y * y = 1 := by rw [← sq, hy2]
    have hstep : y * ((e : G)⁻¹ * (y * e * y⁻¹)) * y⁻¹ = (y * e * y⁻¹)⁻¹ * e := by
      calc y * ((e : G)⁻¹ * (y * e * y⁻¹)) * y⁻¹ =
          (y * (e : G)⁻¹ * y⁻¹) * ((y * y) * e * (y * y)⁻¹) := by group
        _ = (y * e * y⁻¹)⁻¹ * e := by rw [hy2']; group
    have hinv' : ((e : G)⁻¹ * (y * e * y⁻¹))⁻¹ = (e : G)⁻¹ * (y * e * y⁻¹) :=
      inv_eq_of_mul_eq_one_right (by rw [← sq, hd2])
    have hfix : y * ((e : G)⁻¹ * (y * e * y⁻¹)) * y⁻¹ = (e : G)⁻¹ * (y * e * y⁻¹) := by
      rw [hstep]
      calc (y * e * y⁻¹)⁻¹ * (e : G) = ((e : G)⁻¹ * (y * e * y⁻¹))⁻¹ := by group
        _ = _ := hinv'
    calc (e : G)⁻¹ * (y * e * y⁻¹) * y = (y * ((e : G)⁻¹ * (y * e * y⁻¹)) * y⁻¹) * y := by
          rw [hfix]
      _ = y * ((e : G)⁻¹ * (y * e * y⁻¹)) := by group
  have h1 := Subgroup.card_ker_mul_card_range δ
  have h2 : Nat.card δ.range ≤ Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le hrange
  rw [hker, hcard] at h1
  have h3 : 8 ≤ Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) *
      Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) := by
    rw [← h1]
    exact Nat.mul_le_mul_left _ h2
  have hdvd : Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) ∣ 8 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hc : Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) <;> omega

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem inf_centralizer_eq_of_le [Finite X] (_hσ : Setup42 h hS w z) {Y : Subgroup X}
    (hY : IsSylowOf 2 Y ⊤) (hSY : S ≤ Y) : Y ⊓ centralizer ({t} : Set X) = S :=
  hS.eq_of_le (le_inf hSY hS.le) inf_le_right (hY.isPGroup.to_le inf_le_left)

theorem inf_centralizer_le_X [Finite X] (hσ : Setup42 h hS w z) {Y : Subgroup X}
    (hY : IsSylowOf 2 Y ⊤) (hSY : S ≤ Y) {E : Subgroup X} (hEY : E ≤ Y)
    (hEn : ∀ y ∈ Y, ∀ e ∈ E, y * e * y⁻¹ ∈ E) (hE2 : ∀ e ∈ E, e ^ 2 = 1) :
    E ⊓ centralizer ({t} : Set X) ≤ closure {t, w ^ (orderOf w / 2), z} := by
  have hCS : E ⊓ centralizer ({t} : Set X) ≤ S := by
    rw [← hσ.inf_centralizer_eq_of_le hY hSY]
    exact inf_le_inf_right _ hEY
  refine hσ.le_X_of_normal_S hCS (fun d hd e he => ?_) (fun e he => hE2 e he.1)
  refine Subgroup.mem_inf.mpr ⟨hEn d (hSY hd.1) e he.1, ?_⟩
  exact mul_mem (mul_mem (hS.le hd.1) he.2) (inv_mem (hS.le hd.1))

theorem le_normalizer_X [Finite X] (hσ : Setup42 h hS w z) {Y : Subgroup X}
    (hY : IsSylowOf 2 Y ⊤) (hSY : S ≤ Y) {E : Subgroup X} (hEY : E ≤ Y)
    (hEn : ∀ y ∈ Y, ∀ e ∈ E, y * e * y⁻¹ ∈ E) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) :
    E ≤ normalizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) := by
  have hCX := hσ.inf_centralizer_le_X hY hSY hEY hEn hE2
  have htY : t ∈ Y := hSY (h.t_mem hS)
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq, ht2])
  have hXY : closure {t, w ^ (orderOf w / 2), z} ≤ Y := (hσ.X_le_T.trans hσ.T_le).trans hSY
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  intro e he
  refine mem_normalizer_of_conj_le fun x hx => ?_
  have hte : t * e * t⁻¹ ∈ E := hEn t htY e he
  have hc : t * e * t⁻¹ * e⁻¹ ∈ E ⊓ centralizer ({t} : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem hte (inv_mem he), ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hsq := hE2 _ (mul_mem hte (inv_mem he))
    have hinv : (t * e * t⁻¹ * e⁻¹)⁻¹ = t * e * t⁻¹ * e⁻¹ :=
      inv_eq_of_mul_eq_one_right (by rw [← sq, hsq])
    have htt : t * t = 1 := by rw [← sq, ht2]
    have hc1 : t * (t * e * t⁻¹ * e⁻¹) * t⁻¹ = t * e * t⁻¹ * e⁻¹ := by
      calc t * (t * e * t⁻¹ * e⁻¹) * t⁻¹ = (t * t) * e * t⁻¹ * e⁻¹ * t⁻¹ := by group
        _ = e * t⁻¹ * e⁻¹ * t⁻¹ := by rw [htt]; group
        _ = e * t * e⁻¹ * t⁻¹ := by rw [htinv]
        _ = (t * e * t⁻¹ * e⁻¹)⁻¹ := by group
        _ = t * e * t⁻¹ * e⁻¹ := hinv
    calc t * e * t⁻¹ * e⁻¹ * t = (t * (t * e * t⁻¹ * e⁻¹) * t⁻¹) * t := by rw [hc1]
      _ = t * (t * e * t⁻¹ * e⁻¹) := by group
  have hcX := hCX hc
  have hxY := hXY hx
  have hε : x⁻¹ * (e * x * e⁻¹) ∈ E := by
    have := hEn x hxY e he
    rw [show x⁻¹ * (e * x * e⁻¹) = (x⁻¹ * e * x) * e⁻¹ by group]
    exact mul_mem (by simpa using hEn x⁻¹ (inv_mem hxY) e he) (inv_mem he)
  have hxt : x * t = t * x := hσ.X_comm hx htX
  have hεt : x⁻¹ * (e * x * e⁻¹) ∈ E ⊓ centralizer ({t} : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨hε, ?_⟩
    rw [mem_centralizer_singleton_iff]
    set c := t * e * t⁻¹ * e⁻¹ with hcdef
    have hte' : t * e * t⁻¹ = c * e := by rw [hcdef]; group
    have hcx : c * x = x * c := hσ.X_comm hcX hx
    have hcε := hEc _ hc.1 _ hε
    have htε : t * (x⁻¹ * (e * x * e⁻¹)) * t⁻¹ = x⁻¹ * (e * x * e⁻¹) := by
      have hxt' : t * x * t⁻¹ = x := by rw [← hxt]; group
      calc t * (x⁻¹ * (e * x * e⁻¹)) * t⁻¹ =
          (t * x * t⁻¹)⁻¹ * ((t * e * t⁻¹) * (t * x * t⁻¹) * (t * e * t⁻¹)⁻¹) := by group
        _ = x⁻¹ * ((c * e) * x * (c * e)⁻¹) := by rw [hxt', hte']
        _ = (x⁻¹ * c) * (e * x * e⁻¹) * c⁻¹ := by group
        _ = (c * x⁻¹) * (e * x * e⁻¹) * c⁻¹ := by
            rw [show x⁻¹ * c = c * x⁻¹ by
              calc x⁻¹ * c = x⁻¹ * (c * x) * x⁻¹ := by group
                _ = x⁻¹ * (x * c) * x⁻¹ := by rw [hcx]
                _ = c * x⁻¹ := by group]
        _ = c * (x⁻¹ * (e * x * e⁻¹)) * c⁻¹ := by group
        _ = x⁻¹ * (e * x * e⁻¹) := by rw [hcε]; group
    calc x⁻¹ * (e * x * e⁻¹) * t = (t * (x⁻¹ * (e * x * e⁻¹)) * t⁻¹) * t := by rw [htε]
      _ = t * (x⁻¹ * (e * x * e⁻¹)) := by group
  have hεX := hCX hεt
  rw [show e * x * e⁻¹ = x * (x⁻¹ * (e * x * e⁻¹)) by group]
  exact mul_mem hx hεX

theorem le_normalizer_T [Finite X] (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z)
    {Y : Subgroup X} (hY : IsSylowOf 2 Y ⊤) (hSY : S ≤ Y) {E : Subgroup X} (hEY : E ≤ Y)
    (hEn : ∀ y ∈ Y, ∀ e ∈ E, y * e * y⁻¹ ∈ E) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) :
    E ≤ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) := by
  have hEX := hσ.le_normalizer_X hY hSY hEY hEn hEc hE2
  have hCY : Y ⊓ centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) =
      zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
    refine (hσ.isSylowOf_centralizer_X hKC).eq_of_le (le_inf (hσ.T_le.trans hSY) fun g hg =>
      mem_centralizer_iff.mpr fun x hx =>
        (mem_centralizer_iff.mp (hσ.X_le_center_T hx).2 g hg).symm)
      inf_le_right (hY.isPGroup.to_le inf_le_left)
  intro e he
  have heY := hEY he
  have heX := hEX he
  refine mem_normalizer_of_conj_le fun y hy => ?_
  rw [← hCY] at hy ⊢
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem heY hy.1) (inv_mem heY),
    mem_centralizer_iff.mpr fun x hx => ?_⟩
  have hx' : e⁻¹ * x * e ∈ closure {t, w ^ (orderOf w / 2), z} := by
    simpa using (mem_normalizer_iff.mp (inv_mem heX) x).mp hx
  have hc := mem_centralizer_iff.mp hy.2 _ hx'
  calc x * (e * y * e⁻¹) = e * ((e⁻¹ * x * e) * y) * e⁻¹ := by group
    _ = e * (y * (e⁻¹ * x * e)) * e⁻¹ := by rw [hc]
    _ = e * y * e⁻¹ * x := by group

theorem eq_X_of_le_S [Finite X] (hσ : Setup42 h hS w z) {Y : Subgroup X} (hSY : S ≤ Y)
    {E : Subgroup X} (hES : E ≤ S) (hEn : ∀ y ∈ Y, ∀ e ∈ E, y * e * y⁻¹ ∈ E)
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) (hE8 : Nat.card E = 8) :
    E = closure {t, w ^ (orderOf w / 2), z} :=
  Subgroup.eq_of_le_of_card_ge
    (hσ.le_X_of_normal_S hES (fun d hd e he => hEn d (hSY hd.1) e he) hE2)
    (hσ.card_X_le.trans hE8.ge)

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
