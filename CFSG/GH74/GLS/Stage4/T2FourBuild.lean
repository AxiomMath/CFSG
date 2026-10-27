module

public import CFSG.GH74.GLS.Stage4.T2BSL
public import CFSG.GH74.GLS.Stage4.T2P51
public import CFSG.GH74.GLS.Stage4.T2Four
public import CFSG.GH74.GLS.Stage4.T2HAnti

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage4.Rest.T2

section Factor

variable {G : Type} [Group G]

theorem t2B_factor {z t : G} {K : Subgroup G} {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (hz : orderOf z = 2) (hzK : z ∈ K)
    (htt : t * t = 1) (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) (g : GL (Fin 2) F)
    (hns : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) (hact : ActsAsConj t K e g)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hq : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (d : ℕ)
    (hd : (d : ℤ) = Nat.card F + ε) :
    ∃ (Hd : Subgroup G) (w : G), Hd ≤ K ∧ IsCyclic ↥Hd ∧ Nat.card ↥Hd = d ∧
      (∀ x ∈ K, x ∈ Hd ↔ x * t = t * x) ∧ w ∈ K ∧ w * w = z ∧ t * w * t⁻¹ = w⁻¹ ∧
      (∀ x ∈ Hd, w * x * w⁻¹ = x⁻¹) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨φ, hinj, hrange, hzφ, hτ, hsq⟩ := exists_coords0 h2 hz hzK htt e g hact
  have hg2 : (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      (-((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) • (1 : Matrix (Fin 2) (Fin 2) F) :=
    sq_eq_neg_det_of_slConj_sq g hns hsq
  have hnsc : ¬ ∃ s : F, (g : Matrix (Fin 2) (Fin 2) F) = s • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rintro ⟨s, hs⟩
    apply hns
    refine ⟨s, ?_⟩
    have hdd : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = (g : Matrix (Fin 2) (Fin 2) F).det :=
      rfl
    rw [hdd, hs]
    simp [Matrix.det_one, sq]
  have hdet : ¬ IsSquare (g : Matrix (Fin 2) (Fin 2) F).det := hns
  obtain ⟨hcyc, hcard⟩ := t2SlCent_cyclic hodd h3 ε hε hq d hd g ⟨_, hg2⟩ hnsc hdet
  obtain ⟨W, hWW, hWg, hWanti⟩ := t2B_exists_W hodd h3 g hsq hns
  have heq := Subgroup.equivMapOfInjective (t2SlCent g) φ hinj
  have hmemK : ∀ M : SL2 F, φ M ∈ K := fun M => hrange ▸ ⟨M, rfl⟩
  have hcomm : ∀ M : SL2 F, M ∈ t2SlCent g ↔ slConj g M = M := by
    intro M
    rw [mem_t2SlCent]
    constructor
    · intro hM
      apply Subtype.ext
      rw [coe_slConj]
      have hgg : (g : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          1 := by simp
      calc (g : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          = ((M : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by rw [hM]
        _ = (M : Matrix (Fin 2) (Fin 2) F) := by rw [Matrix.mul_assoc, hgg, Matrix.mul_one]
    · intro hM
      have := congrArg (fun y : SL2 F => (y : Matrix (Fin 2) (Fin 2) F) *
        (g : Matrix (Fin 2) (Fin 2) F)) hM
      simp only [coe_slConj] at this
      have hgg : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
          1 := by simp
      rw [Matrix.mul_assoc, hgg, Matrix.mul_one] at this
      exact this.symm
  refine ⟨(t2SlCent g).map φ, φ W, ?_, heq.isCyclic.1 hcyc, ?_, ?_, hmemK W, ?_, ?_, ?_⟩
  · rintro _ ⟨M, -, rfl⟩
    exact hmemK M
  · exact (Nat.card_congr heq.toEquiv.symm).trans hcard
  · intro x hx
    obtain ⟨M, rfl⟩ : x ∈ φ.range := hrange ▸ hx
    constructor
    · rintro ⟨M', hM', hMM'⟩
      have : M' = M := hinj hMM'
      subst this
      have hc := (hcomm M').1 hM'
      have := hτ M'
      rw [hc] at this
      have h3 : t * φ M' = φ M' * t := by
        calc t * φ M' = (t * φ M' * t⁻¹) * t := by group
          _ = φ M' * t := by rw [this]
      exact h3.symm
    · intro hxt
      refine ⟨M, (hcomm M).2 ?_, rfl⟩
      apply hinj
      rw [← hτ M]
      calc t * φ M * t⁻¹ = (φ M * t) * t⁻¹ := by rw [hxt]
        _ = φ M := by group
  · rw [← map_mul, hWW, hzφ]
  · rw [hτ W, hWg, map_inv]
  · rintro _ ⟨M, hM, rfl⟩
    have hM' : (M : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
        (g : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) := mem_t2SlCent.1 hM
    have := t2H_inv_of_anticomm h2 g _ hg2 hnsc W M hWW hWanti hM'.symm
    calc φ W * φ M * (φ W)⁻¹ = φ (W * M * W⁻¹) := by simp [map_mul, map_inv]
      _ = φ M⁻¹ := by rw [this]
      _ = (φ M)⁻¹ := map_inv φ M

end Factor

section Aux

theorem t2B_eps (q : ℕ) (hq : Odd q) : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (q : ℤ) ≡ ε [ZMOD 4] := by
  have h4 : q % 4 = 1 ∨ q % 4 = 3 := by
    obtain ⟨k, hk⟩ := hq
    omega
  rcases h4 with h | h
  · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
  · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩

theorem t2B_d (q : ℕ) (hq : 5 ≤ q) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ d : ℕ, (d : ℤ) = q + ε := by
  refine ⟨(q + ε).toNat, Int.toNat_of_nonneg ?_⟩
  rcases hε with rfl | rfl <;> omega

variable {G : Type} [Group G]

theorem t2B_sup_comm {A B : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hAB x).1 hx
  obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_of_comm hAB y).1 hy
  have e1 : a * b * (a' * b') = (a * a') * (b * b') := by
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hAB a' ha' b hb]
      _ = (a * a') * (b * b') := by group
  have e2 : a' * b' * (a * b) = (a' * a) * (b' * b) := by
    calc a' * b' * (a * b) = a' * (b' * a) * b := by group
      _ = a' * (a * b') * b := by rw [← hAB a ha b' hb']
      _ = (a' * a) * (b' * b) := by group
  rw [e1, e2, hA a ha a' ha', hB b hb b' hb']

theorem t2B_cyclic_comm (A : Subgroup G) (hA : IsCyclic ↥A) :
    ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  intro x hx y hy
  let _ : CommGroup ↥A := IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥A) ⟨y, hy⟩)

end Aux

section Assembly

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

omit [Finite G] in
theorem t2B_t_notin (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) :
    t ∉ K₁ ⊔ K₂ := by
  have hgen := hRem.gen
  have hidx := hSet.index_two
  intro htK
  have hle : oPrimeResidualOf 2 (centralizer ({z} : Set G)) ≤ K₁ ⊔ K₂ := by
    rw [← hgen]; exact sup_le le_rfl (Subgroup.zpowers_le.2 htK)
  have h1 : (K₁ ⊔ K₂).relIndex (oPrimeResidualOf 2 (centralizer ({z} : Set G))) = 1 :=
    Subgroup.relIndex_eq_one.2 hle
  rw [h1] at hidx
  exact absurd hidx (by norm_num)

theorem t2Four_of_rem (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hC₁ : centralizer ({z} : Set G) ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)))
    (h5₂ : 5 ≤ q₂) :
    ∃ (H : Subgroup G) (w₁ w₂ : G), T2Four z t K₁ K₂ H w₁ w₂ ∧
      ∃ ε₁ ε₂ : ℤ, (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧ (q₁ : ℤ) ≡ ε₁ [ZMOD 4] ∧
        (q₂ : ℤ) ≡ ε₂ [ZMOD 4] ∧ IsCyclic ↥(H ⊓ K₁) ∧ IsCyclic ↥(H ⊓ K₂) ∧
        (Nat.card ↥(H ⊓ K₁) : ℤ) = q₁ + ε₁ ∧ (Nat.card ↥(H ⊓ K₂) : ℤ) = q₂ + ε₂ ∧
        (∀ x ∈ H, x ∈ (H ⊓ K₁) ⊔ (H ⊓ K₂) ∨ ∃ y ∈ (H ⊓ K₁) ⊔ (H ⊓ K₂), x = y * t) := by
  have := hSet.finite₁
  have := hSet.finite₂
  have hzord : orderOf z = 2 := hSet.central.1
  have hzz : z * z = 1 := t2C_zz hSet
  have htt : t * t = 1 := hRem.sq
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  have h3₁ : 3 < Nat.card F₁ := by rw [hSet.card₁]; have := hSet.five; omega
  have h3₂ : 3 < Nat.card F₂ := by rw [hSet.card₂]; omega
  obtain ⟨ε₁, hε₁, hq₁⟩ := t2B_eps q₁ hSet.odd₁
  obtain ⟨ε₂, hε₂, hq₂⟩ := t2B_eps q₂ hSet.odd₂
  obtain ⟨d₁, hd₁⟩ := t2B_d q₁ hSet.five ε₁ hε₁
  obtain ⟨d₂, hd₂⟩ := t2B_d q₂ h5₂ ε₂ hε₂
  obtain ⟨e₁, g₁, hns₁, hact₁⟩ := hRem.diag₁
  obtain ⟨e₂, g₂, hns₂, hact₂⟩ := hRem.diag₂
  obtain ⟨Hd₁, w₁, hHd₁K, hcyc₁, hcard₁, hiff₁, hw₁K, hw₁sq, hw₁t, hw₁inv⟩ :=
    t2B_factor hodd₁ h3₁ hzord hSet.z_mem₁ htt e₁ g₁ hns₁ hact₁ ε₁ hε₁
      (by rw [hSet.card₁]; exact hq₁) d₁ (by rw [hSet.card₁]; exact hd₁)
  obtain ⟨Hd₂, w₂, hHd₂K, hcyc₂, hcard₂, hiff₂, hw₂K, hw₂sq, hw₂t, hw₂inv⟩ :=
    t2B_factor hodd₂ h3₂ hzord hSet.z_mem₂ htt e₂ g₂ hns₂ hact₂ ε₂ hε₂
      (by rw [hSet.card₂]; exact hq₂) d₂ (by rw [hSet.card₂]; exact hd₂)
  have htK := t2B_t_notin hSet hRem
  have hHd₁c := t2B_cyclic_comm Hd₁ hcyc₁
  have hHd₂c := t2B_cyclic_comm Hd₂ hcyc₂
  have hHd₁₂ : ∀ x ∈ Hd₁, ∀ y ∈ Hd₂, x * y = y * x := fun x hx y hy =>
    hSet.comm x (hHd₁K hx) y (hHd₂K hy)
  have hHd₁t : ∀ x ∈ Hd₁, x * t = t * x := fun x hx => (hiff₁ x (hHd₁K hx)).1 hx
  have hHd₂t : ∀ x ∈ Hd₂, x * t = t * x := fun x hx => (hiff₂ x (hHd₂K hx)).1 hx
  have hAc : ∀ x ∈ Hd₁ ⊔ Hd₂, ∀ y ∈ Hd₁ ⊔ Hd₂, x * y = y * x :=
    t2B_sup_comm hHd₁c hHd₂c hHd₁₂
  have hAt : ∀ x ∈ Hd₁ ⊔ Hd₂, x * t = t * x := by
    have : Hd₁ ⊔ Hd₂ ≤ centralizer ({t} : Set G) :=
      sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hHd₁t x hx))
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hHd₂t x hx))
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (this hx)
  have hZc : ∀ x ∈ Subgroup.zpowers t, ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self t m n).eq
  have hAZ : ∀ x ∈ Hd₁ ⊔ Hd₂, ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hxt : Commute x t := hAt x hx
    exact (hxt.zpow_right n).eq
  set H : Subgroup G := (Hd₁ ⊔ Hd₂) ⊔ Subgroup.zpowers t with hHdef
  have hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := t2B_sup_comm hAc hZc hAZ
  have htH : t ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hHd₁H : Hd₁ ≤ H := le_sup_left.trans le_sup_left
  have hHd₂H : Hd₂ ≤ H := le_sup_right.trans le_sup_left
  have hzH : z ∈ H :=
    hHd₁H ((hiff₁ z hSet.z_mem₁).2 hRem.comm_z.symm)
  have hform : ∀ x ∈ H, ∃ h₁ ∈ Hd₁, ∃ h₂ ∈ Hd₂, x = h₁ * h₂ ∨ x = h₁ * h₂ * t := by
    intro x hx
    obtain ⟨p, hp, s, hs, rfl⟩ := (mem_sup_iff_of_comm hAZ x).1 hx
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := (mem_sup_iff_of_comm hHd₁₂ p).1 hp
    rcases t2C_zpowers_cases htt hs with rfl | rfl
    · exact ⟨h₁, hh₁, h₂, hh₂, Or.inl (mul_one _)⟩
    · exact ⟨h₁, hh₁, h₂, hh₂, Or.inr rfl⟩
  have hHK₁ : H ⊓ K₁ = Hd₁ :=
    le_antisymm (fun x hx => (hiff₁ x hx.2).2 (hHc x hx.1 t htH))
      (fun x hx => ⟨hHd₁H hx, hHd₁K hx⟩)
  have hHK₂ : H ⊓ K₂ = Hd₂ :=
    le_antisymm (fun x hx => (hiff₂ x hx.2).2 (hHc x hx.1 t htH))
      (fun x hx => ⟨hHd₂H hx, hHd₂K hx⟩)
  have hw₁z : w₁ * z = z * w₁ :=
    Subgroup.mem_centralizer_singleton_iff.1 (hSet.le_centralizer (Subgroup.mem_sup_left hw₁K))
  have hw₂z : w₂ * z = z * w₂ :=
    Subgroup.mem_centralizer_singleton_iff.1 (hSet.le_centralizer (Subgroup.mem_sup_right hw₂K))
  have hw₁t' : t * w₁ * t = w₁⁻¹ := by rw [hti] at hw₁t; exact hw₁t
  have hw₂t' : t * w₂ * t = w₂⁻¹ := by rw [hti] at hw₂t; exact hw₂t
  have hw₁tz : w₁ * t * w₁⁻¹ = t * z := by
    have h1 : w₁ * t = t * w₁⁻¹ := by
      calc w₁ * t = (t * t) * w₁ * t := by rw [htt, one_mul]
        _ = t * (t * w₁ * t) := by group
        _ = t * w₁⁻¹ := by rw [hw₁t']
    calc w₁ * t * w₁⁻¹ = t * (w₁⁻¹ * w₁⁻¹) := by rw [h1]; group
      _ = t * (w₁ * w₁)⁻¹ := by group
      _ = t * z := by rw [hw₁sq]; rw [inv_eq_of_mul_eq_one_right hzz]
  have hw₂tz : w₂ * t * w₂⁻¹ = t * z := by
    have h1 : w₂ * t = t * w₂⁻¹ := by
      calc w₂ * t = (t * t) * w₂ * t := by rw [htt, one_mul]
        _ = t * (t * w₂ * t) := by group
        _ = t * w₂⁻¹ := by rw [hw₂t']
    calc w₂ * t * w₂⁻¹ = t * (w₂⁻¹ * w₂⁻¹) := by rw [h1]; group
      _ = t * (w₂ * w₂)⁻¹ := by group
      _ = t * z := by rw [hw₂sq]; rw [inv_eq_of_mul_eq_one_right hzz]
  have hw₁w₂ : w₁ * w₂ = w₂ * w₁ := hSet.comm w₁ hw₁K w₂ hw₂K
  have hc₁₁ : ∀ x ∈ Hd₁, w₁ * x * w₁⁻¹ = x⁻¹ := hw₁inv
  have hc₂₂ : ∀ x ∈ Hd₂, w₂ * x * w₂⁻¹ = x⁻¹ := hw₂inv
  have hc₁₂ : ∀ y ∈ Hd₂, w₁ * y * w₁⁻¹ = y := by
    intro y hy
    rw [hSet.comm w₁ hw₁K y (hHd₂K hy)]; group
  have hc₂₁ : ∀ x ∈ Hd₁, w₂ * x * w₂⁻¹ = x := by
    intro x hx
    rw [(hSet.comm x (hHd₁K hx) w₂ hw₂K).symm]; group
  have hzcomm₁ : ∀ x ∈ H, x * z = z * x := fun x hx => hHc x hx z hzH
  have hinv2 : ∀ h₁ ∈ Hd₁, ∀ h₂ ∈ Hd₂, (h₁ * h₂)⁻¹ = h₁⁻¹ * h₂⁻¹ := by
    intro h₁ hh₁ h₂ hh₂
    have := hHd₁₂ h₁⁻¹ (Hd₁.inv_mem hh₁) h₂⁻¹ (Hd₂.inv_mem hh₂)
    calc (h₁ * h₂)⁻¹ = h₂⁻¹ * h₁⁻¹ := by group
      _ = h₁⁻¹ * h₂⁻¹ := this.symm
  have hinv3 : ∀ h₁ ∈ Hd₁, ∀ h₂ ∈ Hd₂, (h₁ * h₂ * t)⁻¹ = h₁⁻¹ * h₂⁻¹ * t := by
    intro h₁ hh₁ h₂ hh₂
    have hp : (h₁ * h₂)⁻¹ ∈ Hd₁ ⊔ Hd₂ :=
      Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hh₁) (Subgroup.mem_sup_right hh₂))
    have := hAt _ hp
    calc (h₁ * h₂ * t)⁻¹ = t⁻¹ * (h₁ * h₂)⁻¹ := by group
      _ = t * (h₁ * h₂)⁻¹ := by rw [hti]
      _ = (h₁ * h₂)⁻¹ * t := this.symm
      _ = h₁⁻¹ * h₂⁻¹ * t := by rw [hinv2 h₁ hh₁ h₂ hh₂]
  have hw₀inv : ∀ x ∈ H, (w₁ * w₂) * x * (w₁ * w₂)⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨h₁, hh₁, h₂, hh₂, hxe⟩ := hform x hx
    have e1 : (w₁ * w₂) * h₁ * (w₁ * w₂)⁻¹ = h₁⁻¹ := by
      calc (w₁ * w₂) * h₁ * (w₁ * w₂)⁻¹ = w₁ * (w₂ * h₁ * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * h₁ * w₁⁻¹ := by rw [hc₂₁ h₁ hh₁]
        _ = h₁⁻¹ := hc₁₁ h₁ hh₁
    have e2 : (w₁ * w₂) * h₂ * (w₁ * w₂)⁻¹ = h₂⁻¹ := by
      calc (w₁ * w₂) * h₂ * (w₁ * w₂)⁻¹ = w₁ * (w₂ * h₂ * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * h₂⁻¹ * w₁⁻¹ := by rw [hc₂₂ h₂ hh₂]
        _ = h₂⁻¹ := hc₁₂ h₂⁻¹ (Hd₂.inv_mem hh₂)
    have e3 : (w₁ * w₂) * t * (w₁ * w₂)⁻¹ = t := by
      calc (w₁ * w₂) * t * (w₁ * w₂)⁻¹ = w₁ * (w₂ * t * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * (t * z) * w₁⁻¹ := by rw [hw₂tz]
        _ = (w₁ * t * w₁⁻¹) * (w₁ * z * w₁⁻¹) := by group
        _ = (t * z) * z := by
            rw [hw₁tz, show w₁ * z * w₁⁻¹ = z by rw [hw₁z]; group]
        _ = t := by rw [mul_assoc, hzz, mul_one]
    rcases hxe with rfl | rfl
    · rw [hinv2 h₁ hh₁ h₂ hh₂]
      calc (w₁ * w₂) * (h₁ * h₂) * (w₁ * w₂)⁻¹
          = ((w₁ * w₂) * h₁ * (w₁ * w₂)⁻¹) * ((w₁ * w₂) * h₂ * (w₁ * w₂)⁻¹) := by group
        _ = h₁⁻¹ * h₂⁻¹ := by rw [e1, e2]
    · rw [hinv3 h₁ hh₁ h₂ hh₂]
      calc (w₁ * w₂) * (h₁ * h₂ * t) * (w₁ * w₂)⁻¹
          = ((w₁ * w₂) * h₁ * (w₁ * w₂)⁻¹) * ((w₁ * w₂) * h₂ * (w₁ * w₂)⁻¹) *
              ((w₁ * w₂) * t * (w₁ * w₂)⁻¹) := by group
        _ = h₁⁻¹ * h₂⁻¹ * t := by rw [e1, e2, e3]
  have hw₁norm : ∀ x ∈ H, w₁ * x * w₁⁻¹ ∈ H := by
    intro x hx
    obtain ⟨h₁, hh₁, h₂, hh₂, hxe⟩ := hform x hx
    have hH1 : h₁⁻¹ ∈ H := H.inv_mem (hHd₁H hh₁)
    have hH2 : h₂ ∈ H := hHd₂H hh₂
    rcases hxe with rfl | rfl
    · have : w₁ * (h₁ * h₂) * w₁⁻¹ = h₁⁻¹ * h₂ := by
        calc w₁ * (h₁ * h₂) * w₁⁻¹ = (w₁ * h₁ * w₁⁻¹) * (w₁ * h₂ * w₁⁻¹) := by group
          _ = h₁⁻¹ * h₂ := by rw [hc₁₁ h₁ hh₁, hc₁₂ h₂ hh₂]
      rw [this]; exact H.mul_mem hH1 hH2
    · have : w₁ * (h₁ * h₂ * t) * w₁⁻¹ = h₁⁻¹ * h₂ * (t * z) := by
        calc w₁ * (h₁ * h₂ * t) * w₁⁻¹
            = (w₁ * h₁ * w₁⁻¹) * (w₁ * h₂ * w₁⁻¹) * (w₁ * t * w₁⁻¹) := by group
          _ = h₁⁻¹ * h₂ * (t * z) := by rw [hc₁₁ h₁ hh₁, hc₁₂ h₂ hh₂, hw₁tz]
      rw [this]; exact H.mul_mem (H.mul_mem hH1 hH2) (H.mul_mem htH hzH)
  have hw₂norm : ∀ x ∈ H, w₂ * x * w₂⁻¹ ∈ H := by
    intro x hx
    obtain ⟨h₁, hh₁, h₂, hh₂, hxe⟩ := hform x hx
    have hH1 : h₁ ∈ H := hHd₁H hh₁
    have hH2 : h₂⁻¹ ∈ H := H.inv_mem (hHd₂H hh₂)
    rcases hxe with rfl | rfl
    · have : w₂ * (h₁ * h₂) * w₂⁻¹ = h₁ * h₂⁻¹ := by
        calc w₂ * (h₁ * h₂) * w₂⁻¹ = (w₂ * h₁ * w₂⁻¹) * (w₂ * h₂ * w₂⁻¹) := by group
          _ = h₁ * h₂⁻¹ := by rw [hc₂₁ h₁ hh₁, hc₂₂ h₂ hh₂]
      rw [this]; exact H.mul_mem hH1 hH2
    · have : w₂ * (h₁ * h₂ * t) * w₂⁻¹ = h₁ * h₂⁻¹ * (t * z) := by
        calc w₂ * (h₁ * h₂ * t) * w₂⁻¹
            = (w₂ * h₁ * w₂⁻¹) * (w₂ * h₂ * w₂⁻¹) * (w₂ * t * w₂⁻¹) := by group
          _ = h₁ * h₂⁻¹ * (t * z) := by rw [hc₂₁ h₁ hh₁, hc₂₂ h₂ hh₂, hw₂tz]
      rw [this]; exact H.mul_mem (H.mul_mem hH1 hH2) (H.mul_mem htH hzH)
  have hw₀notin : w₁ * w₂ ∉ H := by
    refine t2C_w0_not_mem (K := K₁) hHc hw₀inv ?_ ?_
    · rw [hHK₁]; exact hcyc₁
    · rw [hHK₁, hcard₁]
      have := hSet.five
      rcases hε₁ with h | h <;> rw [h] at hd₁ <;> omega
  have hC₁eq : centralizer ({z} : Set G) = oPrimeResidualOf 2 (centralizer ({z} : Set G)) :=
    le_antisymm hC₁ (Subgroup.map_subtype_le _)
  have hidx : (K₁ ⊔ K₂).relIndex (centralizer ({z} : Set G)) = 2 := by
    have := hSet.index_two
    rwa [← hC₁eq] at this
  refine ⟨H, w₁, w₂, ?_, ε₁, ε₂, hε₁, hε₂, hq₁, hq₂, ?_, ?_, ?_, ?_, ?_⟩
  · refine
      { zz := hzz, z_ne := t2C_z_ne hSet, uu := htt,
        u_ne := fun h1 => htK (h1 ▸ (K₁ ⊔ K₂).one_mem), zu_ne := fun h1 => htK (h1 ▸
          Subgroup.mem_sup_left hSet.z_mem₁),
        zu_comm := hRem.comm_z.symm, K_comm := hSet.comm, K_inter := hSet.inter_eq.le,
        K_le_C := hSet.le_centralizer,
        C_norm₁ := fun c hc => (t2C_C₁_normalizes hRem hSet.comm).1 c (hC₁ hc),
        C_norm₂ := fun c hc => (t2C_C₁_normalizes hRem hSet.comm).2 c (hC₁ hc),
        C_idx := hidx, H_comm := hHc, z_mem_H := hzH, u_mem_H := htH,
        H_le_C := ?_, H_not_le_K := fun hle => htK (hle htH),
        H₁_iff := ?_, H₂_iff := ?_, w₁_mem := hw₁K, w₂_mem := hw₂K, w₁_sq := hw₁sq,
        w₂_sq := hw₂sq, w₁_u := hw₁tz, w₂_u := hw₂tz, w₁_normH := hw₁norm,
        w₂_normH := hw₂norm, w₀_inv := hw₀inv, w₀_not_mem := hw₀notin }
    ·
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.2 (hzcomm₁ x hx)
    · intro x hx
      exact ⟨fun hxH => hHc x hxH t htH, fun hxt => hHd₁H ((hiff₁ x hx).2 hxt)⟩
    · intro x hx
      exact ⟨fun hxH => hHc x hxH t htH, fun hxt => hHd₂H ((hiff₂ x hx).2 hxt)⟩
  · rw [hHK₁]; exact hcyc₁
  · rw [hHK₂]; exact hcyc₂
  · rw [hHK₁, hcard₁, hd₁]
  · rw [hHK₂, hcard₂, hd₂]
  · intro x hx
    obtain ⟨h₁, hh₁, h₂, hh₂, hxe⟩ := hform x hx
    have hp : h₁ * h₂ ∈ (H ⊓ K₁) ⊔ (H ⊓ K₂) := by
      rw [hHK₁, hHK₂]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh₁) (Subgroup.mem_sup_right hh₂)
    rcases hxe with rfl | rfl
    · exact Or.inl hp
    · exact Or.inr ⟨h₁ * h₂, hp, rfl⟩

end Assembly

end CFSG.GH74.GLS.Stage4.Rest
