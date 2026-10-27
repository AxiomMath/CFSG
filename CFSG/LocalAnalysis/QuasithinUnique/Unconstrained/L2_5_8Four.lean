module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Small

public section

namespace CFSG.QuasithinUnique.Unc25Small

theorem nat_eq_four (n : ℕ) (h1 : n % 3 = 1) (h2 : n ∣ 8) (hle : n ≤ 8) (hne : n ≠ 1) :
    n = 4 := by
  interval_cases n <;> omega

theorem card_subtype_ne {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have h := Fintype.card_subtype_compl (fun x : α => x = a)
  rw [Fintype.card_subtype_eq] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

variable {N : Type*} [Group N]

theorem exists_two_nonid {F : Subgroup N} (hFcard : Nat.card F = 4) :
    ∃ f ∈ F, ∃ b ∈ F, f ≠ 1 ∧ b ≠ 1 ∧ f ≠ b := by
  classical
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hFcard]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  have h4 : ((F : Set N).toFinset).card = 4 := by
    rw [← hFcard, Nat.card_eq_fintype_card]
    exact (Set.toFinset_card (F : Set N))
  obtain ⟨f, hfF, hf1⟩ := Finset.exists_mem_ne (s := (F : Set N).toFinset) (by omega) 1
  obtain ⟨b, hbF, hbs⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({1, f} : Finset N))
    (t := (F : Set N).toFinset) (by
      have := Finset.card_le_two (a := (1 : N)) (b := f)
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbs
  exact ⟨f, by simpa using hfF, b, by simpa using hbF, hf1, hbs.1, fun h => hbs.2 h.symm⟩

theorem mem_klein_iff {F : Subgroup N} (hFcard : Nat.card F = 4) (hFexp : ∀ x ∈ F, x * x = 1)
    {f b : N} (hf : f ∈ F) (hb : b ∈ F) (hf1 : f ≠ 1) (hb1 : b ≠ 1) (hfb : f ≠ b) (x : N) :
    x ∈ F ↔ x = 1 ∨ x = f ∨ x = b ∨ x = f * b := by
  classical
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hFcard]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hFexp b hb)
  have h1 : (1 : N) ≠ f := fun h => hf1 h.symm
  have h2 : (1 : N) ≠ b := fun h => hb1 h.symm
  have h3 : (1 : N) ≠ f * b := by
    intro h
    apply hfb
    have : f = b⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    rw [this, hbinv]
  have h4 : f ≠ f * b := by
    intro h
    apply hb1
    have : f * b = f * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  have h5 : b ≠ f * b := by
    intro h
    apply hf1
    have : 1 * b = f * b := by rw [one_mul]; exact h
    exact (mul_right_cancel this).symm
  let S : Finset N := {1, f, b, f * b}
  have hS : S.card = 4 := by
    have e1 : (1 : N) ∉ ({f, b, f * b} : Finset N) := by simp [h1, h2, h3]
    have e2 : f ∉ ({b, f * b} : Finset N) := by simp [hfb, h4]
    have e3 : b ∉ ({f * b} : Finset N) := by simp [h5]
    simp only [S]
    rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
      Finset.card_insert_of_notMem e3, Finset.card_singleton]
  have hsub : S ⊆ (F : Set N).toFinset := by
    intro y hy
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Set.mem_toFinset, SetLike.mem_coe]
    rcases hy with rfl | rfl | rfl | rfl
    · exact F.one_mem
    · exact hf
    · exact hb
    · exact F.mul_mem hf hb
  have hFs : ((F : Set N).toFinset).card = 4 := by
    rw [← hFcard, Nat.card_eq_fintype_card]
    exact (Set.toFinset_card (F : Set N))
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hS, hFs])
  constructor
  · intro hx
    have : x ∈ (F : Set N).toFinset := by simpa using hx
    rw [← heq] at this
    simpa [S] using this
  · intro hx
    have : x ∈ S := by simpa [S] using hx
    have := hsub this
    simpa using this

theorem commutes_of_fixed_of_pow_three {F : Subgroup N} [F.Normal] (hFcard : Nat.card F = 4)
    (hFexp : ∀ x ∈ F, x * x = 1) {w : N} (hw3 : w ^ 3 = 1) {f : N} (hf : f ∈ F) (hf1 : f ≠ 1)
    (hfw : w * f = f * w) : ∀ x ∈ F, w * x = x * w := by
  obtain ⟨f₁, hf₁, b, hb, hf₁1, hb1, hf₁b⟩ := exists_two_nonid hFcard
  obtain ⟨b, hb, hb1, hfb⟩ : ∃ b ∈ F, b ≠ 1 ∧ f ≠ b := by
    by_cases h : f = f₁
    · exact ⟨b, hb, hb1, fun h' => hf₁b (h ▸ h')⟩
    · exact ⟨f₁, hf₁, hf₁1, h⟩
  have hmem := mem_klein_iff hFcard hFexp hf hb hf1 hb1 hfb
  have hwb : w * b * w⁻¹ ∈ F := ‹F.Normal›.conj_mem b hb w
  have hcf : w * f * w⁻¹ = f := by rw [hfw]; group
  have hne1 : w * b * w⁻¹ ≠ 1 := by
    intro h
    apply hb1
    have : w * b = w := by simpa using (mul_inv_eq_one.mp h)
    simpa using this
  have hnef : w * b * w⁻¹ ≠ f := by
    intro h
    apply hfb
    have h' : w * b * w⁻¹ = w * f * w⁻¹ := by rw [h, hcf]
    exact (mul_left_cancel (mul_right_cancel h')).symm
  have hwb_comm : w * b = b * w := by
    rcases (hmem _).mp hwb with h | h | h | h
    · exact absurd h hne1
    · exact absurd h hnef
    · calc w * b = w * b * w⁻¹ * w := by group
        _ = b * w := by rw [h]
    · exfalso
      have hfinv : f * f = 1 := hFexp f hf
      have h2 : w * (w * b * w⁻¹) * w⁻¹ = b := by
        rw [h]
        calc w * (f * b) * w⁻¹ = (w * f * w⁻¹) * (w * b * w⁻¹) := by group
          _ = f * (f * b) := by rw [hcf, h]
          _ = (f * f) * b := by rw [mul_assoc]
          _ = b := by rw [hfinv, one_mul]
      have h3 : w ^ 2 * b = b * w ^ 2 := by
        have : w ^ 2 * b * (w ^ 2)⁻¹ = b := by
          calc w ^ 2 * b * (w ^ 2)⁻¹ = w * (w * b * w⁻¹) * w⁻¹ := by rw [pow_two]; group
            _ = b := h2
        calc w ^ 2 * b = (w ^ 2 * b * (w ^ 2)⁻¹) * w ^ 2 := by group
          _ = b * w ^ 2 := by rw [this]
      have hww : w = (w ^ 2) ^ 2 := by
        calc w = w ^ 3 * w := by rw [hw3, one_mul]
          _ = (w ^ 2) ^ 2 := by rw [← pow_mul, ← pow_succ]
      have hc : Commute w b := by
        have : Commute (w ^ 2) b := h3
        have h4 := this.pow_left 2
        rw [← hww] at h4
        exact h4
      have : w * b * w⁻¹ = b := by rw [hc.eq]; group
      rw [this] at h
      apply hf1
      have : f * b = 1 * b := by rw [← h, one_mul]
      exact mul_right_cancel this
  intro x hx
  rcases (hmem x).mp hx with rfl | rfl | rfl | rfl
  · simp
  · exact hfw
  · exact hwb_comm
  · calc w * (f * b) = (w * f) * b := by rw [mul_assoc]
      _ = (f * w) * b := by rw [hfw]
      _ = f * (w * b) := by rw [mul_assoc]
      _ = f * (b * w) := by rw [hwb_comm]
      _ = (f * b) * w := by rw [mul_assoc]

theorem card_mulAut_le_six {F : Subgroup N} (hFcard : Nat.card F = 4) :
    Nat.card (MulAut F) ≤ 6 := by
  classical
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hFcard]; norm_num)
  have hQ : Nat.card {x : F // x ≠ 1} = 3 := by
    rw [card_subtype_ne, hFcard]
  have hQfin : Finite {x : F // x ≠ 1} := inferInstance
  let g : MulAut F → Equiv.Perm {x : F // x ≠ 1} := fun ψ =>
    Equiv.Perm.subtypePerm (ψ.toEquiv : Equiv.Perm F) (fun x => by
      simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
      exact (map_ne_one_iff ψ ψ.injective))
  have hinj : Function.Injective g := by
    intro ψ₁ ψ₂ h
    apply MulEquiv.ext
    intro x
    by_cases hx : x = 1
    · rw [hx, map_one, map_one]
    · have h2 : ((g ψ₁) ⟨x, hx⟩ : F) = ((g ψ₂) ⟨x, hx⟩ : F) := by rw [h]
      exact h2
  have hfinA : Finite (Equiv.Perm {x : F // x ≠ 1}) := inferInstance
  calc Nat.card (MulAut F) ≤ Nat.card (Equiv.Perm {x : F // x ≠ 1}) :=
        Nat.card_le_card_of_injective g hinj
    _ = 6 := by rw [Nat.card_perm, hQ]; rfl

theorem card_le_24_of_klein [Finite N] (F : Subgroup N) [F.Normal] (hFcard : Nat.card F = 4)
    (hC : ∀ g : N, (∀ f ∈ F, g * f = f * g) → g ∈ F) : Nat.card N ≤ 24 := by
  classical
  let ρ : N →* MulAut F := MulAut.conjNormal
  have hker : ρ.ker ≤ F := by
    intro g hg
    refine hC g fun f hf => ?_
    have h1 : ρ g = 1 := hg
    have h2 := congrArg (fun φ : MulAut F => ((φ ⟨f, hf⟩ : F) : N)) h1
    simp only [ρ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
    have h3 : g * f * g⁻¹ = f := h2
    calc g * f = g * f * g⁻¹ * g := by group
      _ = f * g := by rw [h3]
  have h1 : Nat.card ρ.ker ≤ 4 := by
    rw [← hFcard]
    exact Subgroup.card_le_of_le hker
  have hfinM : Finite (MulAut F) := by
    have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hFcard]; norm_num)
    exact Finite.of_injective (fun ψ : MulAut F => (ψ : F → F))
      (fun a b h => MulEquiv.ext (congrFun h))
  have h2 : Nat.card ρ.range ≤ 6 :=
    (Subgroup.card_le_card_group ρ.range).trans (card_mulAut_le_six hFcard)
  have h3 := Subgroup.card_ker_mul_card_range ρ
  calc Nat.card N = Nat.card ρ.ker * Nat.card ρ.range := h3.symm
    _ ≤ 4 * 6 := Nat.mul_le_mul h1 h2

theorem perm_four_of_klein [Finite N] (F : Subgroup N) [F.Normal] (hFcard : Nat.card F = 4)
    (hFexp : ∀ x ∈ F, x * x = 1) (hC : ∀ g : N, (∀ f ∈ F, g * f = f * g) → g ∈ F)
    (h24 : 24 ∣ Nat.card N) : Nonempty (N ≃* Equiv.Perm (Fin 4)) := by
  classical
  have hN : Nat.card N = 24 := by
    have hle := card_le_24_of_klein F hFcard hC
    have hpos : 0 < Nat.card N := Nat.card_pos
    obtain ⟨k, hk⟩ := h24
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let T : Sylow 3 N := default
  have hT : Nat.card T = 3 := by
    rw [Sylow.card_eq_multiplicity T, hN]
    have : (24 : ℕ).factorization 3 = 1 := by
      rw [Nat.factorization_def _ Nat.prime_three]
      decide +kernel
    rw [this]; norm_num
  have hTpow : ∀ x ∈ (T : Subgroup N), x ^ 3 = 1 := by
    intro x hx
    have := pow_card_eq_one' (G := (T : Subgroup N)) (x := (⟨x, hx⟩ : T))
    rw [hT] at this
    exact congrArg Subtype.val this
  obtain ⟨t₀, ht₀T, ht₀1⟩ : ∃ t₀ ∈ (T : Subgroup N), t₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : (T : Subgroup N) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.mpr (hcon x hx)
    have h1 : Nat.card T = 1 := by
      rw [show (T : Subgroup N) = ⊥ from this]
      exact Subgroup.card_bot
    omega
  have hTF : ∀ x ∈ (T : Subgroup N), x ∈ F → x = 1 := by
    intro x hxT hxF
    have h3 : x ^ 3 = 1 := hTpow x hxT
    have h2 : x * x = 1 := hFexp x hxF
    calc x = x * (x * x) := by rw [h2, mul_one]
      _ = x ^ 3 := by rw [pow_three]
      _ = 1 := h3
  have hcomm_of_one : ∀ a b : N, a * b * a⁻¹ * b⁻¹ = 1 → a * b = b * a := by
    intro a b h
    have : a * b * a⁻¹ = b := mul_inv_eq_one.mp h
    calc a * b = (a * b * a⁻¹) * a := by group
      _ = b * a := by rw [this]
  have hidx : (T : Subgroup N).index = 8 := by
    have := (T : Subgroup N).index_mul_card
    rw [hT, hN] at this
    omega
  have hn3 : Nat.card (Sylow 3 N) = 4 := by
    have h1 := card_sylow_modEq_one 3 N
    have h2 : Nat.card (Sylow 3 N) ∣ 8 := by
      have := Sylow.card_dvd_index T
      rwa [hidx] at this
    have hle : Nat.card (Sylow 3 N) ≤ 8 := Nat.le_of_dvd (by norm_num) h2
    have hne1 : Nat.card (Sylow 3 N) ≠ 1 := by
      intro h1'
      have hsub : Subsingleton (Sylow 3 N) := (Nat.card_eq_one_iff_unique.mp h1').1
      have hnorm : (T : Subgroup N).Normal := Sylow.normal_of_subsingleton T
      apply ht₀1
      refine hTF t₀ ht₀T (hC t₀ fun f hf => ?_)
      have hTm : t₀ * f * t₀⁻¹ * f⁻¹ ∈ (T : Subgroup N) := by
        have h1 := (T : Subgroup N).mul_mem ht₀T
          (hnorm.conj_mem t₀⁻¹ ((T : Subgroup N).inv_mem ht₀T) f)
        simpa [mul_assoc] using h1
      have hFm : t₀ * f * t₀⁻¹ * f⁻¹ ∈ F :=
        F.mul_mem (‹F.Normal›.conj_mem f hf t₀) (F.inv_mem hf)
      exact hcomm_of_one _ _ (hTF _ hTm hFm)
    exact nat_eq_four _ h1 h2 hle hne1
  let H : Subgroup N := Subgroup.normalizer ((T : Subgroup N) : Set N)
  have hHidx : H.index = 4 := by
    rw [← hn3]
    exact (Sylow.card_eq_index_normalizer T).symm
  have hHF : ∀ f ∈ F, f ∈ H → f = 1 := by
    intro f hf hfH
    by_contra hf1
    have hfT : f * t₀ * f⁻¹ ∈ (T : Subgroup N) :=
      (Subgroup.mem_normalizer_iff.mp hfH t₀).mp ht₀T
    have hTm : f * t₀ * f⁻¹ * t₀⁻¹ ∈ (T : Subgroup N) :=
      (T : Subgroup N).mul_mem hfT ((T : Subgroup N).inv_mem ht₀T)
    have hFm : f * t₀ * f⁻¹ * t₀⁻¹ ∈ F := by
      have h1 := F.mul_mem hf (‹F.Normal›.conj_mem f⁻¹ (F.inv_mem hf) t₀)
      simpa [mul_assoc] using h1
    have hcomm : f * t₀ = t₀ * f := hcomm_of_one _ _ (hTF _ hTm hFm)
    have hall := commutes_of_fixed_of_pow_three hFcard hFexp (hTpow t₀ ht₀T) hf hf1 hcomm.symm
    have : t₀ ∈ F := hC t₀ hall
    exact ht₀1 (hTF t₀ ht₀T this)
  let φ : N →* Equiv.Perm (N ⧸ H) := MulAction.toPermHom N (N ⧸ H)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkg : ∀ g : N, g⁻¹ * k * g ∈ H := by
      intro g
      have h1 : φ k (g : N ⧸ H) = (g : N ⧸ H) := by rw [hk]; rfl
      have h2 : ((k * g : N) : N ⧸ H) = (g : N ⧸ H) := h1
      have h3 := QuotientGroup.eq.mp h2
      have h4 := H.inv_mem h3
      simpa [mul_assoc] using h4
    have hkH : k ∈ H := by simpa using hkg 1
    have hkF : k ∈ F := by
      refine hC k fun f hf => ?_
      have h1 : f * k⁻¹ * f⁻¹ ∈ H := by
        have := H.inv_mem (hkg f⁻¹)
        simpa [mul_assoc] using this
      have hc : k * f * k⁻¹ * f⁻¹ ∈ H := by
        have := H.mul_mem hkH h1
        simpa [mul_assoc] using this
      have hcF : k * f * k⁻¹ * f⁻¹ ∈ F :=
        F.mul_mem (‹F.Normal›.conj_mem f hf k) (F.inv_mem hf)
      exact hcomm_of_one _ _ (hHF _ hcF hc)
    exact hHF k hkF hkH
  have hcardQ : Nat.card (N ⧸ H) = 4 := hHidx
  have hperm : Nat.card (Equiv.Perm (N ⧸ H)) = 24 := by
    rw [Nat.card_perm, hcardQ]; rfl
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, by rw [hN, hperm]⟩
  let e : (N ⧸ H) ≃ Fin 4 := (Finite.equivFin (N ⧸ H)).trans (finCongr hcardQ)
  exact ⟨(MulEquiv.ofBijective φ hbij).trans (Equiv.permCongrHom e)⟩


end CFSG.QuasithinUnique.Unc25Small
