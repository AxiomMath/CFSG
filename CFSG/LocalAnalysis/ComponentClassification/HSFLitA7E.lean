module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Fusion

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup
open scoped Pointwise

@[expose] def numFixed (σ : Perm (Fin 7)) : ℕ := (Finset.univ.filter fun i => σ i = i).card

theorem numFixed_conj (σ τ : Perm (Fin 7)) : numFixed (σ * τ * σ⁻¹) = numFixed τ := by
  classical
  unfold numFixed
  refine Finset.card_bij (fun i _ => σ⁻¹ i) (fun i hi => ?_) (fun _ _ _ _ h => ?_)
    (fun j hj => ⟨σ j, ?_, by simp⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have : σ (τ (σ⁻¹ i)) = i := by simpa [Perm.mul_apply] using hi
    calc τ (σ⁻¹ i) = σ⁻¹ (σ (τ (σ⁻¹ i))) := by simp
      _ = σ⁻¹ i := by rw [this]
  · exact σ⁻¹.injective h
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simp [Perm.mul_apply, hj]

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

theorem E_eq_sup (yi : X) : S.E yi = ⊥ ⊔ zpowers S.z ⊔ zpowers yi ⊔ zpowers S.t ⊔ zpowers S.k := by
  apply le_antisymm
  · rw [E, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _))))
    · exact mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _)))
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · exact mem_sup_right (mem_zpowers _)
  · refine sup_le (sup_le (sup_le (sup_le bot_le ?_) ?_) ?_) ?_ <;> rw [zpowers_le, E] <;>
      exact subset_closure (by simp)

theorem eq_of_mem_E {yi : X} (hyi : yi ∈ S.data.R) (hyi2 : yi ^ 2 = 1)
    (hzyi : S.z * yi = yi * S.z) {g : X} (hg : g ∈ S.E yi) :
    ∃ a b c d : Fin 2, g = S.z ^ (a : ℕ) * yi ^ (b : ℕ) * S.t ^ (c : ℕ) * S.k ^ (d : ℕ) := by
  have hz2 : S.z ^ 2 = 1 := S.sq_of_mem_B (subset_closure (by simp))
  have hcomm : ∀ a ∈ (⊥ ⊔ zpowers S.z ⊔ zpowers yi ⊔ zpowers S.t : Subgroup X), S.k * a =
      a * S.k := by
    intro a ha
    have hle : (⊥ ⊔ zpowers S.z ⊔ zpowers yi ⊔ zpowers S.t : Subgroup X) ≤ S.data.T :=
      sup_le (sup_le (sup_le bot_le (zpowers_le.mpr S.z_mem.1)) (zpowers_le.mpr hyi.1))
        (zpowers_le.mpr S.data.t_mem_T)
    exact S.central_of_mem_B (subset_closure (by simp)) (hle ha)
  have hN : ∀ {P : Subgroup X} {u : X}, (∀ a ∈ P, u * a = a * u) →
      u ∈ normalizer (P : Set X) := by
    intro P u hu
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    exact fun a ha => (hu a ha).symm
  rw [S.E_eq_sup] at hg
  have hpow : ∀ (u : X) (e : Fin 2), u ^ 2 = 1 → (u ^ (e : ℕ))⁻¹ = u ^ (e : ℕ) := by
    intro u e hu
    fin_cases e
    · simp
    · simp only [pow_one]
      rw [inv_eq_iff_mul_eq_one, ← pow_two, hu]
  have step : ∀ {P : Subgroup X} {u g : X}, u ^ 2 = 1 → (∀ a ∈ P, u * a = a * u) →
      g ∈ P ⊔ zpowers u → ∃ e : Fin 2, g * u ^ (e : ℕ) ∈ P := by
    intro P u g hu hc hg
    rcases mem_or_mul_mem_of_mem_sup_zpowers hu (hN hc) hg with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨d, hd⟩ := step S.k_sq hcomm hg
  obtain ⟨c, hc⟩ := step S.t_sq (fun a ha => (S.data.commute_t (by
      have hle : (⊥ ⊔ zpowers S.z ⊔ zpowers yi : Subgroup X) ≤ S.data.T :=
        sup_le (sup_le bot_le (zpowers_le.mpr S.z_mem.1)) (zpowers_le.mpr hyi.1)
      exact hle ha)).symm) hd
  obtain ⟨b, hb⟩ := step hyi2 (fun a ha => by
      rcases eq_one_or_eq_of_mem_zpowers hz2 ((sup_le bot_le le_rfl :
        (⊥ ⊔ zpowers S.z : Subgroup X) ≤ zpowers S.z) ha) with rfl | rfl
      · rw [mul_one, one_mul]
      · exact hzyi.symm) hc
  obtain ⟨a, ha⟩ := step hz2 (fun a ha => by rw [mem_bot.mp ha, mul_one, one_mul]) hb
  rw [mem_bot] at ha
  refine ⟨a, b, c, d, ?_⟩
  have h1 : g = (S.z ^ (a : ℕ))⁻¹ * (yi ^ (b : ℕ))⁻¹ * (S.t ^ (c : ℕ))⁻¹ *
      (S.k ^ (d : ℕ))⁻¹ := by
    calc g = g * S.k ^ (d : ℕ) * S.t ^ (c : ℕ) * yi ^ (b : ℕ) * S.z ^ (a : ℕ) *
          (S.z ^ (a : ℕ))⁻¹ * (yi ^ (b : ℕ))⁻¹ * (S.t ^ (c : ℕ))⁻¹ * (S.k ^ (d : ℕ))⁻¹ := by
          group
      _ = _ := by rw [ha, one_mul]
  rw [h1, hpow _ _ hz2, hpow _ _ hyi2, hpow _ _ S.t_sq, hpow _ _ S.k_sq]

theorem card_T_eq_of_le {H : Subgroup X} (hTH : S.data.T ≤ H)
    (hH : H ≤ centralizer ({S.t} : Set X)) :
    Nat.card S.data.T = 2 ^ (Nat.card H).factorization 2 := by
  have hC := S.card_T_eq_two_pow
  have h1 : Nat.card H ∣ Nat.card (centralizer ({S.t} : Set X)) := Subgroup.card_dvd_of_le hH
  have h2 : Nat.card S.data.T ∣ Nat.card H := Subgroup.card_dvd_of_le hTH
  have hpos : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hposC : Nat.card (centralizer ({S.t} : Set X)) ≠ 0 := Nat.card_pos.ne'
  have h3 : (Nat.card H).factorization 2 ≤
      (Nat.card (centralizer ({S.t} : Set X))).factorization 2 :=
    (Nat.factorization_le_iff_dvd hpos hposC).mpr h1 2
  have h4 : (Nat.card (centralizer ({S.t} : Set X))).factorization 2 ≤
      (Nat.card H).factorization 2 := by
    rw [hC] at h2
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp h2
  rw [hC, le_antisymm h3 h4]

theorem conj_eq_of_mem_pair {G' : Subgroup X} (hTG : S.data.T ≤ G')
    (hG : G' ≤ centralizer ({S.t} : Set X)) {e : X}
    (hTe : S.data.T ≤ centralizer ({e} : Set X))
    (hpair : ∀ n ∈ G', n * e * n⁻¹ = e ∨ n * e * n⁻¹ = S.t * e) {n : X} (hn : n ∈ G') :
    n * e * n⁻¹ = e := by
  classical
  have hsub : {y | ∃ g ∈ G', g * e * g⁻¹ = y} ⊆ ({e, S.t * e} : Set X) := by
    rintro _ ⟨g, hg, rfl⟩
    rcases hpair g hg with h | h <;> simp [h]
  have hle2 : (G' ⊓ centralizer ({e} : Set X)).relIndex G' ≤ 2 := by
    rw [relIndex_inf_centralizer_eq_ncard]
    calc _ ≤ ({e, S.t * e} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({S.t * e} : Set X).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hT₁ := S.card_T_eq_of_le hTG hG
  have hT₂ := S.card_T_eq_of_le (le_inf hTG hTe) (inf_le_left.trans hG)
  have hidx : (G' ⊓ centralizer ({e} : Set X)).relIndex G' = 1 := by
    by_contra hne
    have h2 : (G' ⊓ centralizer ({e} : Set X)).relIndex G' = 2 := by
      have hpos : (G' ⊓ centralizer ({e} : Set X)).relIndex G' ≠ 0 := by
        intro h0
        have := relIndex_mul_card (H := G' ⊓ centralizer ({e} : Set X)) (K := G')
        rw [h0, zero_mul] at this
        exact Nat.card_pos.ne' this.symm
      omega
    have h3 := card_eq_mul_two_pow (P := S.data.T) (Q := S.data.T) inf_le_left hT₁ hT₂
    rw [h2, Nat.Prime.factorization_self Nat.prime_two, pow_one] at h3
    have : 0 < Nat.card S.data.T := Nat.card_pos
    omega
  have := (relIndex_eq_one.mp hidx) hn
  rw [mem_inf, mem_centralizer_singleton_iff] at this
  calc n * e * n⁻¹ = e * n * n⁻¹ := by rw [this.2]
    _ = e := by group

theorem E_le_T {yi : X} (hyi : yi ∈ S.data.R) : S.E yi ≤ S.data.T := by
  rw [E, closure_le]
  intro c hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact S.z_mem.1
  · exact hyi.1
  · exact S.data.t_mem_T
  · exact S.k_mem

theorem T_le_normalizer_E {yi : X} (hyi : yi ∈ S.data.R) :
    S.data.T ≤ normalizer (S.E yi : Set X) := by
  have hzE : S.z ∈ S.E yi := subset_closure (by simp)
  have hconj : ∀ g ∈ S.data.T, ∀ h ∈ S.E yi, g * h * g⁻¹ ∈ S.E yi := by
    intro g hg h hh
    rcases S.commutator_eq hg (S.E_le_T hyi hh) with h1 | h1
    · have : g * h * g⁻¹ = h := by
        calc g * h * g⁻¹ = g * h * g⁻¹ * h⁻¹ * h := by group
          _ = h := by rw [h1, one_mul]
      rw [this]
      exact hh
    · have : g * h * g⁻¹ = S.z * h := by
        calc g * h * g⁻¹ = g * h * g⁻¹ * h⁻¹ * h := by group
          _ = S.z * h := by rw [h1]
      rw [this]
      exact mul_mem hzE hh
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  refine ⟨hconj g hg h, fun hh => ?_⟩
  have := hconj g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem numFixed_ψ_conj (Λ : A7Sigma S.t S.L S.data) {n e : X}
    (hn : n ∈ centralizer ({S.t} : Set X)) (he : e ∈ S.data.T) (hne : n * e * n⁻¹ ∈ S.data.T) :
    numFixed (S.data.ψ ⟨n * e * n⁻¹, hne⟩) = numFixed (S.data.ψ ⟨e, he⟩) := by
  have hnN : n ∈ normalizer (S.L : Set X) := S.data.config.le_normalizer hn
  rw [Λ.Ψ_T, Λ.Ψ_T]
  have : (⟨n * e * n⁻¹, S.data.T_le_normalizer hne⟩ : normalizer (S.L : Set X)) =
      ⟨n, hnN⟩ * ⟨e, S.data.T_le_normalizer he⟩ * (⟨n, hnN⟩)⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, numFixed_conj]

theorem xy_mem : S.x * S.y ∈ S.data.R := mul_mem S.x_mem S.y_mem

theorem xy_sq : (S.x * S.y) ^ 2 = 1 := by
  calc (S.x * S.y) ^ 2 = S.x * (S.y * S.x * S.y⁻¹) * (S.y * S.y) := by rw [pow_two]; group
    _ = 1 := by rw [S.y_x_y, S.y_mul_y]; group

theorem z_comm_of_mem_T {g : X} (hg : g ∈ S.data.T) : S.z * g = g * S.z :=
  S.central_of_mem_B (subset_closure (by simp)) hg

theorem conj_k_eq_of_mem_normalizer_of_sigma (Λ : A7Sigma S.t S.L S.data) {n : X}
    (hn : n ∈ normalizer (S.E (S.x * S.y) : Set X) ⊓ centralizer ({S.t} : Set X)) :
    n * S.k * n⁻¹ = S.k := by
  have hkB : S.k ∈ S.B := subset_closure (by simp)
  refine S.conj_eq_of_mem_pair (le_inf (S.T_le_normalizer_E S.xy_mem) S.data.T_le_centralizer)
    inf_le_right (fun h hh => mem_centralizer_singleton_iff.mpr (S.central_of_mem_B hkB hh).symm)
    (fun n hn => ?_) hn
  have hkE : S.k ∈ S.E (S.x * S.y) := subset_closure (by simp)
  have hnkE : n * S.k * n⁻¹ ∈ S.E (S.x * S.y) := (mem_normalizer_iff.mp hn.1 _).mp hkE
  obtain ⟨a, b, c, d, habcd⟩ := S.eq_of_mem_E S.xy_mem S.xy_sq
    (S.z_comm_of_mem_T S.xy_mem.1) hnkE
  have hT : n * S.k * n⁻¹ ∈ S.data.T := S.E_le_T S.xy_mem hnkE
  have h5 : numFixed (S.data.ψ ⟨n * S.k * n⁻¹, hT⟩) = 5 := by
    rw [S.numFixed_ψ_conj Λ hn.2 S.k_mem hT, S.ψ_k]
    decide
  have hψ : S.data.ψ ⟨n * S.k * n⁻¹, hT⟩ =
      (a0 ^ 2) ^ (a : ℕ) * (rho0 * (c0 * b0)) ^ (b : ℕ) * c0 ^ (d : ℕ) := by
    have e : (⟨n * S.k * n⁻¹, hT⟩ : S.data.T) = (⟨S.z, S.z_mem.1⟩ : S.data.T) ^ (a : ℕ) *
        ((⟨S.x, S.x_mem.1⟩ : S.data.T) * ⟨S.y, S.y_mem.1⟩) ^ (b : ℕ) *
        (⟨S.t, S.data.t_mem_T⟩ : S.data.T) ^ (c : ℕ) * (⟨S.k, S.k_mem⟩ : S.data.T) ^ (d : ℕ) :=
      Subtype.ext habcd
    rw [e, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, map_mul, S.ψ_z,
      S.ψ_x, S.ψ_y, S.ψ_t, one_pow, mul_one, S.ψ_k]
  have key : ∀ a b d : Fin 2, numFixed ((a0 ^ 2) ^ (a : ℕ) * (rho0 * (c0 * b0)) ^ (b : ℕ) *
      c0 ^ (d : ℕ)) = 5 → a = 0 ∧ b = 0 ∧ d = 1 := by decide
  obtain ⟨rfl, rfl, rfl⟩ := key a b d (hψ ▸ h5)
  fin_cases c
  · left
    simpa using habcd
  · right
    simpa using habcd

theorem conj_zk_eq_of_mem_normalizer_of_sigma (Λ : A7Sigma S.t S.L S.data) {n : X}
    (hn : n ∈ normalizer (S.E S.y : Set X) ⊓ centralizer ({S.t} : Set X)) :
    n * (S.z * S.k) * n⁻¹ = S.z * S.k := by
  have hzkB : S.z * S.k ∈ S.B := mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  refine S.conj_eq_of_mem_pair (le_inf (S.T_le_normalizer_E S.y_mem) S.data.T_le_centralizer)
    inf_le_right (fun h hh => mem_centralizer_singleton_iff.mpr (S.central_of_mem_B hzkB hh).symm)
    (fun n hn => ?_) hn
  have hzk : S.z * S.k ∈ S.data.T := mul_mem S.z_mem.1 S.k_mem
  have hzkE : S.z * S.k ∈ S.E S.y := mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hnkE : n * (S.z * S.k) * n⁻¹ ∈ S.E S.y := (mem_normalizer_iff.mp hn.1 _).mp hzkE
  obtain ⟨a, b, c, d, habcd⟩ := S.eq_of_mem_E S.y_mem S.y_sq (S.z_comm_of_mem_T S.y_mem.1) hnkE
  have hT : n * (S.z * S.k) * n⁻¹ ∈ S.data.T := S.E_le_T S.y_mem hnkE
  have h1 : numFixed (S.data.ψ ⟨n * (S.z * S.k) * n⁻¹, hT⟩) = 1 := by
    rw [S.numFixed_ψ_conj Λ hn.2 hzk hT]
    have e : (⟨S.z * S.k, hzk⟩ : S.data.T) = ⟨S.z, S.z_mem.1⟩ * ⟨S.k, S.k_mem⟩ := rfl
    rw [e, map_mul, S.ψ_z, S.ψ_k]
    decide
  have hψ : S.data.ψ ⟨n * (S.z * S.k) * n⁻¹, hT⟩ =
      (a0 ^ 2) ^ (a : ℕ) * (c0 * b0) ^ (b : ℕ) * c0 ^ (d : ℕ) := by
    have e : (⟨n * (S.z * S.k) * n⁻¹, hT⟩ : S.data.T) = (⟨S.z, S.z_mem.1⟩ : S.data.T) ^ (a : ℕ) *
        (⟨S.y, S.y_mem.1⟩ : S.data.T) ^ (b : ℕ) *
        (⟨S.t, S.data.t_mem_T⟩ : S.data.T) ^ (c : ℕ) * (⟨S.k, S.k_mem⟩ : S.data.T) ^ (d : ℕ) :=
      Subtype.ext habcd
    rw [e, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, S.ψ_z, S.ψ_y, S.ψ_t,
      one_pow, mul_one, S.ψ_k]
  have key : ∀ a b d : Fin 2, numFixed ((a0 ^ 2) ^ (a : ℕ) * (c0 * b0) ^ (b : ℕ) *
      c0 ^ (d : ℕ)) = 1 → a = 1 ∧ b = 0 ∧ d = 1 := by decide
  obtain ⟨rfl, rfl, rfl⟩ := key a b d (hψ ▸ h1)
  fin_cases c
  · left
    simpa using habcd
  · right
    have hzt := S.data.commute_t S.z_mem.1
    calc n * (S.z * S.k) * n⁻¹ = S.z * S.t * S.k := by simpa using habcd
      _ = S.t * (S.z * S.k) := by rw [hzt, mul_assoc]

theorem conj_k_eq_of_mem_normalizer {n : X}
    (hn : n ∈ normalizer (S.E (S.x * S.y) : Set X) ⊓ centralizer ({S.t} : Set X)) :
    n * S.k * n⁻¹ = S.k := by
  rcases S.facts with h | hΛ
  · exact h.k_fixed hn
  · obtain ⟨Λ⟩ := hΛ
    exact S.conj_k_eq_of_mem_normalizer_of_sigma Λ hn

theorem conj_zk_eq_of_mem_normalizer {n : X}
    (hn : n ∈ normalizer (S.E S.y : Set X) ⊓ centralizer ({S.t} : Set X)) :
    n * (S.z * S.k) * n⁻¹ = S.z * S.k := by
  rcases S.facts with h | hΛ
  · exact h.zk_fixed hn
  · obtain ⟨Λ⟩ := hΛ
    exact S.conj_zk_eq_of_mem_normalizer_of_sigma Λ hn

end A7Base

end CFSG.ComponentClassification.HSFLit
