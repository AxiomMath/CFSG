module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415E8c

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem normalizer_of_beta_mem [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKC : AutPSL2CentralizerInput) (hA : AutPSL2RCentralizerInput)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱) (hz𝒱 : ∀ v ∈ 𝒱, z * v = v * z)
    {Y : Subgroup X} (hY𝒱 : Y ≤ 𝒱) (hYn : ∀ v ∈ 𝒱, ∀ y ∈ Y, v * y * v⁻¹ ∈ Y)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hY2 : ∀ y ∈ Y, y ^ 2 = 1) (hY8 : Nat.card Y = 8)
    (hzY : z ∈ Y) (hC4 : Nat.card ↥(Y ⊓ centralizer {t}) = 4)
    (hβY : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ Y) :
    (∀ v ∈ 𝒱, v ∈ normalizer (W : Set X)) ∨
      ∀ v ∈ 𝒱, v ∈ normalizer ((W ⊓ centralizer {z₁} : Subgroup X) : Set X) := by
  have hσ := hs.setup
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hz2 : z * z = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
  have hz₁2' : z₁ * z₁ = 1 := by rw [← sq]; exact hc.sq_z₁
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  have htW := hc.t_mem_W
  have ht𝒱 := hW𝒱 htW
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have htz : t * z = z * t := hc.comm_z htW
  have htβ : t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      (w ^ (orderOf w / 2) * t ^ i * z ^ j) * t :=
    mem_centralizer_singleton_iff.mp (hc.isSylowOf_W.le htW)
  have hTt : ∀ g ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w, g * t = t * g := fun g hg =>
    mem_centralizer_singleton_iff.mp (hs.sylow.le (hσ.T_le hg))
  have hconjt : ∀ g x : X, g * t = t * g → x * t = t * x →
      g * x * g⁻¹ * t = t * (g * x * g⁻¹) := by
    intro g x hg hx
    have hginv : g⁻¹ * t = t * g⁻¹ := by
      calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hg]
        _ = t * g⁻¹ := by group
    calc g * x * g⁻¹ * t = g * x * (g⁻¹ * t) := by group
      _ = g * x * (t * g⁻¹) := by rw [hginv]
      _ = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [hx]
      _ = (g * t) * x * g⁻¹ := by group
      _ = (t * g) * x * g⁻¹ := by rw [hg]
      _ = t * (g * x * g⁻¹) := by group
  have hYβ : Y ≤ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} := fun y hy =>
    mem_centralizer_singleton_iff.mpr (hYc y hy _ hβY)
  have hYW : Y ≤ W := by
    rw [← hc.inf_V_beta h𝒱 hW𝒱]
    exact le_inf hY𝒱 hYβ
  have hYW₀ : Y ≤ W ⊓ centralizer {z₁} :=
    hc.le_W₀_of_abelian hYW hYc (fun g hg y hy => hYn g (hW𝒱 hg) y hy)
  have hCle : zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z ≤
      Y ⊓ centralizer {t} :=
    sup_le (zpowers_le.mpr (mem_inf.mpr ⟨hβY, mem_centralizer_singleton_iff.mpr htβ.symm⟩))
      (zpowers_le.mpr (mem_inf.mpr ⟨hzY, mem_centralizer_singleton_iff.mpr htz.symm⟩))
  have hCeq : zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z =
      Y ⊓ centralizer {t} := eq_of_le_of_card_ge hCle (by rw [hC4, hc.card_beta_z])
  have hYz : ¬ Y ≤ zpowers z := by
    intro h1
    have h2 := Subgroup.card_le_of_le h1
    rw [hY8, L415.card_zpowers_two hz2 hσ.z_ne_one] at h2
    omega
  obtain ⟨e, heY, hez, hecomm⟩ := L415.exists_normal_four h𝒱.isPGroup hY𝒱 hYn
    (fun v hv => (hz𝒱 v hv).symm) hYz
  by_cases het : e * t = t * e
  ·
    left
    have heC : e ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z := by
      rw [hCeq]
      exact mem_inf.mpr ⟨heY, mem_centralizer_singleton_iff.mpr het⟩
    obtain ⟨a, ha, b, hb, hab⟩ := L415.mem_sup_of_commute hc.comm_beta_z heC
    have ha' : a = w ^ (orderOf w / 2) * t ^ i * z ^ j := by
      rcases L415.mem_zpowers_two hβ2 ha with h | h
      · exfalso
        apply hez
        rw [hab, h, one_mul]
        exact hb
      · exact h
    have hbc : ∀ v ∈ 𝒱, v * b * v⁻¹ = b := by
      intro v hv
      rcases L415.mem_zpowers_two hz2 hb with h | h
      · rw [h]
        group
      · rw [h, ← hz𝒱 v hv]
        group
    have hvβ : ∀ v ∈ 𝒱, v * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * v⁻¹ =
        w ^ (orderOf w / 2) * t ^ i * z ^ j ∨
        v * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * v⁻¹ =
          z * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
      intro v hv
      have h1 := hecomm v hv
      have h2 : v * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * v⁻¹ =
          (v * e * v⁻¹ * e⁻¹) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
        have h3 : v * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * v⁻¹ =
            (v * e * v⁻¹) * (v * b * v⁻¹)⁻¹ := by
          rw [hab, ha']
          group
        rw [h3, hbc v hv, hab, ha']
        group
      rcases L415.mem_zpowers_two hz2 h1 with h3 | h3
      · left
        rw [h2, h3, one_mul]
      · right
        rw [h2, h3]
    intro v hv
    apply mem_normalizer_of_conj_le
    intro x hx
    rw [← hc.inf_V_beta h𝒱 hW𝒱]
    refine mem_inf.mpr ⟨mul_mem (mul_mem hv (hW𝒱 hx)) (inv_mem hv),
      mem_centralizer_singleton_iff.mpr ?_⟩
    have hxβ := hc.comm_beta hx
    have hxz := hz𝒱 x (hW𝒱 hx)
    have h1 : x * (v⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * v) =
        (v⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * v) * x := by
      have h2 := hvβ v⁻¹ (inv_mem hv)
      rw [inv_inv] at h2
      rcases h2 with h2 | h2 <;> rw [h2]
      · exact hxβ
      · calc x * (z * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
            z * (x * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
              rw [← mul_assoc, ← hxz, mul_assoc]
          _ = z * ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * x) := by rw [hxβ]
          _ = z * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * x := by group
    calc v * x * v⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
        v * (x * (v⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * v)) * v⁻¹ := by group
      _ = v * ((v⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * v) * x) * v⁻¹ := by rw [h1]
      _ = w ^ (orderOf w / 2) * t ^ i * z ^ j * (v * x * v⁻¹) := by group
  ·
    have hte : t * e * t⁻¹ = e * z := by
      have h1 := hecomm t ht𝒱
      rcases L415.mem_zpowers_two hz2 h1 with h2 | h2
      · exfalso
        apply het
        calc e * t = (t * e * t⁻¹ * e⁻¹)⁻¹ * (t * e) := by group
          _ = t * e := by rw [h2, inv_one, one_mul]
      · calc t * e * t⁻¹ = (t * e * t⁻¹ * e⁻¹) * e := by group
          _ = z * e := by rw [h2]
          _ = e * z := (hYc z hzY e heY)
    have hidx : ((Y ⊓ centralizer {t}).subgroupOf Y).index = 2 := by
      have h1 := ((Y ⊓ centralizer {t}).subgroupOf Y).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : Y ⊓ centralizer {t} ≤ Y)).toEquiv,
        hC4, hY8] at h1
      omega
    have hYt' : ∀ y ∈ Y, y⁻¹ * (t * y * t⁻¹) = 1 ∨ y⁻¹ * (t * y * t⁻¹) = z := by
      intro y hy
      by_cases hyt : y * t = t * y
      · left
        calc y⁻¹ * (t * y * t⁻¹) = y⁻¹ * (y * t * t⁻¹) := by rw [hyt]
          _ = 1 := by group
      · right
        have heH : (⟨e, heY⟩ : ↥Y)⁻¹ ∉ (Y ⊓ centralizer {t}).subgroupOf Y := by
          intro h1
          have h2 := inv_mem h1
          rw [inv_inv] at h2
          exact het (mem_centralizer_singleton_iff.mp (mem_inf.mp h2).2)
        have hyH : (⟨y, hy⟩ : ↥Y) ∉ (Y ⊓ centralizer {t}).subgroupOf Y := fun h1 =>
          hyt (mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2)
        have h1 := (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false heH hyH)
        have h2 : e⁻¹ * y ∈ Y ⊓ centralizer {t} := h1
        have h3 : e⁻¹ * y * t = t * (e⁻¹ * y) :=
          mem_centralizer_singleton_iff.mp (mem_inf.mp h2).2
        have h4 : t * (e⁻¹ * y) * t⁻¹ = e⁻¹ * y := by
          calc t * (e⁻¹ * y) * t⁻¹ = (e⁻¹ * y * t) * t⁻¹ := by rw [h3]
            _ = e⁻¹ * y := by group
        have h5 : t * y * t⁻¹ = (t * e * t⁻¹) * (t * (e⁻¹ * y) * t⁻¹) := by group
        rw [h5, hte, h4]
        have hzc := hz𝒱 (e⁻¹ * y) (hY𝒱 (mul_mem (inv_mem heY) hy))
        calc y⁻¹ * (e * z * (e⁻¹ * y)) = y⁻¹ * e * (z * (e⁻¹ * y)) := by group
          _ = y⁻¹ * e * ((e⁻¹ * y) * z) := by rw [hzc]
          _ = z := by group
    have hz₂eq : t * z₁ * t⁻¹ = z₁ * z := by
      rw [hc.z_eq]
      calc t * z₁ * t⁻¹ = (z₁ * z₁) * (t * z₁ * t⁻¹) := by rw [hz₁2', one_mul]
        _ = z₁ * (z₁ * (t * z₁ * t⁻¹)) := by group
    by_cases hz₁Y : z₁ ∈ Y
    ·
      right
      have hz₂Y : t * z₁ * t⁻¹ ∈ Y := by rw [hz₂eq]; exact mul_mem hz₁Y hzY
      have hY₃Y : zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ⊔
          zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤ Y :=
        sup_le (sup_le (zpowers_le.mpr hz₁Y) (zpowers_le.mpr hz₂Y)) (zpowers_le.mpr hβY)
      have hY₃eq := eq_of_le_of_card_ge hY₃Y (by rw [hY8, hc.card_Y₃.1])
      intro v hv
      rw [← hc.inf_centralizer_Y₃ h𝒱 hW𝒱]
      apply mem_normalizer_of_conj_le
      intro x hx
      refine mem_inf.mpr ⟨mul_mem (mul_mem hv (mem_inf.mp hx).1) (inv_mem hv), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hY₃eq] at hy
      have hy' : v⁻¹ * y * v ∈ Y := by
        have := hYn v⁻¹ (inv_mem hv) y hy
        rwa [inv_inv] at this
      rw [← hY₃eq] at hy'
      have h1 := (Subgroup.mem_centralizer_iff.mp (mem_inf.mp hx).2) _ hy'
      calc y * (v * x * v⁻¹) = v * ((v⁻¹ * y * v) * x) * v⁻¹ := by group
        _ = v * (x * (v⁻¹ * y * v)) * v⁻¹ := by rw [h1]
        _ = v * x * v⁻¹ * y := by group
    ·
      exfalso
      have hz₁c : ∀ y ∈ Y, y * z₁ = z₁ * y := fun y hy =>
        mem_centralizer_singleton_iff.mp (mem_inf.mp (hYW₀ hy)).2
      have hY2' : ∀ y ∈ Y, y * y = 1 := fun y hy => by rw [← sq]; exact hY2 y hy
      obtain ⟨hY₁c, hY₁2, hY₁card⟩ := L415.elem_sup hYc hY2' hz₁2' hz₁Y hz₁c
      rw [hY8] at hY₁card
      have hcommY : ∀ a ∈ Y, ∀ b ∈ zpowers z₁, a * b = b * a := by
        intro a ha b hb
        rcases L415.mem_zpowers_two hz₁2' hb with hb' | hb' <;> rw [hb']
        · simp
        · exact hz₁c a ha
      have hY₁n : ∀ g ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w, ∀ x ∈ Y ⊔ zpowers z₁,
          g * x * g⁻¹ ∈ Y ⊔ zpowers z₁ := by
        intro g hg x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := L415.mem_sup_of_commute hcommY hx
        have hgW := hc.T_le_W hg
        have h1 : g * a * g⁻¹ ∈ Y := hYn g (hW𝒱 hgW) a ha
        have h2 : g * b * g⁻¹ ∈ Y ⊔ zpowers z₁ := by
          rcases L415.mem_zpowers_two hz₁2' hb with hb' | hb'
          · rw [hb', mul_one, mul_inv_cancel]
            exact one_mem _
          · rw [hb']
            rcases hc.conj_mem_of_normalizer_W hnab hKC hA h412 (le_normalizer hgW) with h3 | h3
            · rw [h3]
              exact mem_sup_right (mem_zpowers z₁)
            · rw [h3, hz₂eq]
              exact mul_mem (mem_sup_right (mem_zpowers z₁)) (mem_sup_left hzY)
        rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
        exact mul_mem (mem_sup_left h1) h2
      have hY₁t : ∀ x ∈ Y ⊔ zpowers z₁,
          x⁻¹ * (t * x * t⁻¹) = 1 ∨ x⁻¹ * (t * x * t⁻¹) = z := by
        intro x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := L415.mem_sup_of_commute hcommY hx
        have hra := hYt' a ha
        have hbz : b⁻¹ * z = z * b⁻¹ := by
          rcases L415.mem_zpowers_two hz₁2' hb with hb' | hb' <;> rw [hb']
          · simp
          · have h1 := hc.comm_z hc.z₁_mem
            calc z₁⁻¹ * z = z₁⁻¹ * (z * z₁) * z₁⁻¹ := by group
              _ = z₁⁻¹ * (z₁ * z) * z₁⁻¹ := by rw [h1]
              _ = z * z₁⁻¹ := by group
        have hrb : b⁻¹ * (a⁻¹ * (t * a * t⁻¹)) = (a⁻¹ * (t * a * t⁻¹)) * b⁻¹ := by
          rcases hra with h | h <;> rw [h]
          · simp
          · exact hbz
        have h1 : (a * b)⁻¹ * (t * (a * b) * t⁻¹) =
            (a⁻¹ * (t * a * t⁻¹)) * (b⁻¹ * (t * b * t⁻¹)) := by
          calc (a * b)⁻¹ * (t * (a * b) * t⁻¹) =
              b⁻¹ * (a⁻¹ * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
            _ = (a⁻¹ * (t * a * t⁻¹)) * b⁻¹ * (t * b * t⁻¹) := by rw [hrb]
            _ = (a⁻¹ * (t * a * t⁻¹)) * (b⁻¹ * (t * b * t⁻¹)) := by group
        have hz₁i : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁2'
        have hb2 : b⁻¹ * (t * b * t⁻¹) = 1 ∨ b⁻¹ * (t * b * t⁻¹) = z := by
          rcases L415.mem_zpowers_two hz₁2' hb with hb' | hb' <;> rw [hb']
          · left
            group
          · right
            rw [hz₁i, hc.z_eq]
        rw [h1]
        rcases hra with h | h <;> rcases hb2 with h' | h' <;> rw [h, h']
        · left
          group
        · right
          group
        · right
          group
        · left
          exact hz2
      have htT : t ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :=
        mem_sup_left (mem_sup_left (mem_zpowers t))
      have hcard := L415.card_le_of_commutator hY₁c (fun x hx => hY₁n t htT x hx) hY₁t
      have hle : (Y ⊔ zpowers z₁) ⊓ centralizer {t} ≤ closure {t, w ^ (orderOf w / 2), z} :=
        hσ.le_X_of_elem_centralizer inf_le_right
          (fun x hx => by rw [sq]; exact hY₁2 x (mem_inf.mp hx).1)
          (fun g hg x hx => mem_inf.mpr ⟨hY₁n g hg x (mem_inf.mp hx).1,
            mem_centralizer_singleton_iff.mpr (hconjt g x (hTt g hg)
              (mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2))⟩)
      have heq : (Y ⊔ zpowers z₁) ⊓ centralizer {t} = closure {t, w ^ (orderOf w / 2), z} :=
        eq_of_le_of_card_ge hle (by rw [hσ.card_X]; omega)
      have htY₁ : t ∈ (Y ⊔ zpowers z₁) ⊓ centralizer {t} := by
        rw [heq]
        exact htX
      apply hc.t_not_comm
      exact hY₁c t (mem_inf.mp htY₁).1 z₁ (mem_sup_right (mem_zpowers z₁))

end Config415

end CFSG.ComponentClassification.HarrisLit
