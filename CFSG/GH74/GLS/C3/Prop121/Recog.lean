module

public import CFSG.GH74.GLS.C3.Prop121.CoreWeak
public import CFSG.GH74.GLS.C3.Prop121.Fin6Clause

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS

@[expose] def S_recog (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G ≤ 4 →
    ∀ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfig n x K T Q S a →
      IsApproxTo G (alternatingGroup (Fin (n + 4))) →
        ∀ t u g : G, Stage3Loc n x K Q t u g →
          ∃ L : Subgroup G, (∀ l ∈ L, l * t = t * l) ∧
            (∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l) ∧
            (∀ i : ℤ, t ^ i ∈ L → t ^ i = 1) ∧
            Nonempty (↥L ≃* alternatingGroup (Fin (n + 1)))

theorem stab_iso_of_recog {G : Type} [Group G] [Finite G] {n : ℕ} (hn5 : 5 ≤ n) {x : G}
    {K Q : Subgroup G} {t u g : G} (hS : Stage3Loc n x K Q t u g) {L : Subgroup G}
    (hLt : ∀ l ∈ L, l * t = t * l)
    (hC' : ∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l)
    (lam₀ : ↥L ≃* alternatingGroup (Fin (n + 1))) :
    K ≤ L ∧ ∃ lam : ↥L ≃* alternatingGroup (Fin (n + 1)),
      ∀ l : ↥L, (l : G) ∈ K ↔
        ((lam l : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) 0 = 0 := by
  obtain ⟨eK⟩ := hS.K_alt
  have hKperf : K ≤ ⁅K, K⁆ := Coord.le_commutator_of_equiv hn5 eK
  have hKL : K ≤ L :=
    Derive.le_of_perfect hKperf (fun k hk => (hS.t_comm_K k hk).symm) hLt hC'
  obtain ⟨lam, hstab⟩ := CosetIso.exists_stab_iso hn5 hKL lam₀ eK
    (Coord.commutator_eq_top_of_equiv (by omega) lam₀)
  exact ⟨hKL, lam, hstab⟩

theorem exists_rho_six
    {G : Type} [Group G] {x : G} {K Q : Subgroup G} {t u g : G}
    (hS : Stage3Loc 6 x K Q t u g) {L : Subgroup G} (hLt : ∀ l ∈ L, l * t = t * l)
    (hC' : ∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l) :
    ∃ l ∈ L, l * l * l = 1 ∧ l ≠ 1 ∧
      ∀ q ∈ Q, (g * q * g⁻¹) * l = l * (g * q * g⁻¹) := by
  classical
  obtain ⟨eK⟩ := hS.K_alt
  have hginv : g⁻¹ = g := sq_eq_one_inv hS.g_sq
  have hg2 : g * g = 1 := by rw [← sq]; exact hS.g_sq
  have ht3 : t ^ 3 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hS.t_order] at this
  have ht3' : t * t * t = 1 := (pow_three' t).symm.trans ht3
  have ht1 : t ≠ 1 := by
    intro h1
    have := hS.t_order
    rw [h1, orderOf_one] at this
    omega
  let τ0 : ↥K := ⟨g * t * g⁻¹, hS.gt_K⟩
  have hτ03 : τ0 * τ0 * τ0 = 1 := by
    apply Subtype.ext
    show (g * t * g⁻¹) * (g * t * g⁻¹) * (g * t * g⁻¹) = 1
    calc (g * t * g⁻¹) * (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht3']; group
  have hτ01 : τ0 ≠ 1 := by
    intro h1
    have h2 : g * t * g⁻¹ = 1 := congrArg Subtype.val h1
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h2]; group
  let σ : alternatingGroup (Fin 6) := eK τ0
  have hσ3' : σ * σ * σ = 1 := by rw [← map_mul, ← map_mul, hτ03, map_one]
  have hσ3 : (σ : Perm (Fin 6)) * σ * σ = 1 := by
    have := congrArg Subtype.val hσ3'
    simpa using this
  have hσ1 : (σ : Perm (Fin 6)) ≠ 1 := by
    intro h1
    apply hτ01
    have h2 : σ = 1 := Subtype.ext (by simpa using h1)
    exact eK.injective (by rw [map_one]; exact h2)
  obtain ⟨k', hk3, hk1, hkc, hkσ, hkσi⟩ := exists_comm_ord3_six ⟨hσ3, hσ1⟩
  have hks : sign k' = 1 := by
    have h3 : sign k' * sign k' * sign k' = 1 := by rw [← map_mul, ← map_mul, hk3, map_one]
    rcases Int.units_eq_one_or (sign k') with h | h
    · exact h
    · rw [h] at h3
      exact absurd h3 (by decide)
  let κ : alternatingGroup (Fin 6) := ⟨k', mem_alternatingGroup.2 hks⟩
  let kk : ↥K := eK.symm κ
  have hekk : eK kk = κ := eK.apply_symm_apply κ
  have hkk3 : kk * kk * kk = 1 := by
    apply eK.injective
    rw [map_mul, map_mul, hekk, map_one]
    apply Subtype.ext
    simpa using hk3
  have hkk1 : kk ≠ 1 := by
    intro h1
    apply hk1
    have := congrArg (fun z : ↥K => ((eK z : alternatingGroup (Fin 6)) : Perm (Fin 6))) h1
    simpa [hekk, κ] using this
  have hkkc : kk * τ0 = τ0 * kk := by
    apply eK.injective
    rw [map_mul, map_mul, hekk]
    apply Subtype.ext
    simpa [κ, σ] using hkc
  have hkkτ : kk ≠ τ0 := by
    intro h1
    apply hkσ
    have := congrArg (fun z : ↥K => ((eK z : alternatingGroup (Fin 6)) : Perm (Fin 6))) h1
    simpa [hekk, κ, σ] using this
  have hkkτi : kk ≠ τ0⁻¹ := by
    intro h1
    apply hkσi
    have := congrArg (fun z : ↥K => ((eK z : alternatingGroup (Fin 6)) : Perm (Fin 6))) h1
    simpa [hekk, κ, σ] using this
  let ρ : G := g * (kk : G) * g⁻¹
  have hρ3 : ρ * ρ * ρ = 1 := by
    have h1 : (kk : G) * kk * kk = 1 := congrArg Subtype.val hkk3
    calc ρ * ρ * ρ = g * ((kk : G) * kk * kk) * g⁻¹ := by simp only [ρ]; group
      _ = 1 := by rw [h1]; group
  have hρt : ρ * t = t * ρ := by
    have h1 : (kk : G) * (g * t * g⁻¹) = (g * t * g⁻¹) * kk := congrArg Subtype.val hkkc
    have h1' : (kk : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * kk := by
      rw [hginv] at h1 ⊢
      exact h1
    calc ρ * t = g * ((kk : G) * (g⁻¹ * t * g)) * g⁻¹ := by simp only [ρ]; group
      _ = g * ((g⁻¹ * t * g) * kk) * g⁻¹ := by rw [h1']
      _ = t * ρ := by simp only [ρ]; group
  have hρQ : ∀ q ∈ Q, (g * q * g⁻¹) * ρ = ρ * (g * q * g⁻¹) := by
    intro q hq
    have h1 : (kk : G) * q = q * kk := hS.K_comm_Q kk kk.2 q hq
    calc (g * q * g⁻¹) * ρ = g * (q * kk) * g⁻¹ := by simp only [ρ]; group
      _ = g * (kk * q) * g⁻¹ := by rw [h1]
      _ = ρ * (g * q * g⁻¹) := by simp only [ρ]; group
  have hτ0pow : τ0 ^ 3 = 1 := by rw [pow_three']; exact hτ03
  have hτ0ord : orderOf τ0 = 3 := orderOf_eq_prime hτ0pow hτ01
  have hτ0sq : τ0 ^ (2 : ℤ) = τ0⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc τ0 ^ (2 : ℤ) * τ0 = τ0 ^ 3 := by group
      _ = 1 := hτ0pow
  have hρnt : ∀ i : ℤ, ρ ≠ t ^ i := by
    intro i hi
    have h2 : (kk : G) = (τ0 : G) ^ i := by
      have h1 : (kk : G) = g⁻¹ * ρ * g := by simp only [ρ]; group
      rw [h1, hi]
      show g⁻¹ * t ^ i * g = (g * t * g⁻¹) ^ i
      rw [conj_zpow, hginv]
    have h3 : kk = τ0 ^ i := Subtype.ext h2
    have h5 : τ0 ^ i = τ0 ^ (i % 3) := by
      have := zpow_mod_orderOf τ0 i
      rw [hτ0ord] at this
      exact this.symm
    have h6 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases h6 with h6 | h6 | h6
    · apply hkk1
      rw [h3, h5, h6, zpow_zero]
    · apply hkkτ
      rw [h3, h5, h6, zpow_one]
    · apply hkkτi
      rw [h3, h5, h6, hτ0sq]
  obtain ⟨i, l, hl, hρl⟩ := hC' ρ hρt
  have hlt : Commute l t := hLt l hl
  have hc : Commute (t ^ i) l := hlt.symm.zpow_left i
  refine ⟨l, hl, ?_, ?_, ?_⟩
  · have hti : (t ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, Int.mul_comm, zpow_mul, zpow_natCast, ht3, one_zpow]
    have h1 : ρ ^ 3 = 1 := by rw [pow_three']; exact hρ3
    have h2 : (t ^ i * l) ^ 3 = (t ^ i) ^ 3 * l ^ 3 := hc.mul_pow 3
    rw [← hρl, hti, one_mul] at h2
    rw [h1] at h2
    have h3 : l ^ 3 = 1 := h2.symm
    rwa [pow_three'] at h3
  · intro hl1
    apply hρnt i
    rw [hρl, hl1, mul_one]
  · intro q hq
    have ha : Commute (g * q * g⁻¹) t := (hS.t_comm_K _ (hS.g_Q q hq)).symm
    have ha2 : Commute (g * q * g⁻¹) (t ^ i)⁻¹ := (ha.zpow_right i).inv_right
    have ha3 : Commute (g * q * g⁻¹) ρ := hρQ q hq
    have hl' : l = (t ^ i)⁻¹ * ρ := by rw [hρl]; group
    rw [hl']
    exact (ha2.mul_right ha3).eq

theorem clause4_six_core
    {G : Type} [Group G] {x : G} {K Q : Subgroup G} {t u g : G}
    (hS : Stage3Loc 6 x K Q t u g) (φ : ↥K →* Perm (Fin 7)) (hφinj : Function.Injective φ)
    (hφsign : ∀ k, sign (φ k) = 1) (hφ0 : ∀ k, φ k 0 = 0)
    (hρ : ∃ ρ : Perm (Fin 7), ρ * ρ * ρ = 1 ∧ ρ ≠ 1 ∧
      ∀ k : ↥K, (∃ q ∈ Q, (k : G) = g * q * g⁻¹) → ρ * φ k = φ k * ρ) :
    (φ ⟨g * t * g⁻¹, hS.gt_K⟩).IsThreeCycle := by
  classical
  have hginv : g⁻¹ = g := sq_eq_one_inv hS.g_sq
  have hg2 : g * g = 1 := by rw [← sq]; exact hS.g_sq
  obtain ⟨y₀, hy₀Q, hy₀1, hy₀x⟩ := TU.exists_y hS.Q_card (x := x)
  have hQall := TU.Q_four hS.Q_card hS.Q_sq hS.x_mem hy₀Q hS.x_ne hy₀1 hy₀x
  let cg : G ≃* G := MulAut.conj g
  have hcg : ∀ z : G, cg z = g * z * g⁻¹ := fun z => rfl
  have hXK : cg x ∈ K := hS.g_Q x hS.x_mem
  have hYK : cg y₀ ∈ K := hS.g_Q y₀ hy₀Q
  have hTK : cg t ∈ K := hS.gt_K
  let X : ↥K := ⟨cg x, hXK⟩
  let Y : ↥K := ⟨cg y₀, hYK⟩
  let T' : ↥K := ⟨cg t, hTK⟩
  show (φ T').IsThreeCycle
  have hx2 : x * x = 1 := by rw [← sq]; exact hS.x_sq
  have hy2 : y₀ * y₀ = 1 := by rw [← sq]; exact hS.Q_sq y₀ hy₀Q
  have hxy : x * y₀ = y₀ * x := hS.Q_comm x hS.x_mem y₀ hy₀Q
  have ht3 : t ^ 3 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hS.t_order] at this
  have ht3' : t * t * t = 1 := by
    calc t * t * t = t ^ 3 := (pow_three' t).symm
      _ = 1 := ht3
  have ht1 : t ≠ 1 := by
    intro h1
    have := hS.t_order
    rw [h1, orderOf_one] at this
    omega
  have hcgne : ∀ z : G, z ≠ 1 → cg z ≠ 1 := fun z hz h1 =>
    hz (cg.injective (by rw [h1, map_one]))
  have hXX : X * X = 1 := by
    apply Subtype.ext
    show cg x * cg x = 1
    rw [← map_mul, hx2, map_one]
  have hYY : Y * Y = 1 := by
    apply Subtype.ext
    show cg y₀ * cg y₀ = 1
    rw [← map_mul, hy2, map_one]
  have hXY : X * Y = Y * X := by
    apply Subtype.ext
    show cg x * cg y₀ = cg y₀ * cg x
    rw [← map_mul, ← map_mul, hxy]
  have hX1 : X ≠ 1 := fun h1 => hcgne x hS.x_ne (congrArg Subtype.val h1)
  have hY1 : Y ≠ 1 := fun h1 => hcgne y₀ hy₀1 (congrArg Subtype.val h1)
  have hXYne : X ≠ Y := fun h1 => hy₀x (cg.injective (congrArg Subtype.val h1)).symm
  have hT3 : T' * T' * T' = 1 := by
    apply Subtype.ext
    show cg t * cg t * cg t = 1
    rw [← map_mul, ← map_mul, ht3', map_one]
  have hT1 : T' ≠ 1 := fun h1 => hcgne t ht1 (congrArg Subtype.val h1)
  have hαp : φ X * φ X = 1 ∧ φ X ≠ 1 ∧ sign (φ X) = 1 :=
    ⟨by rw [← map_mul, hXX, map_one],
      fun h1 => hX1 (hφinj (h1.trans (map_one φ).symm)), hφsign X⟩
  have hβp : φ Y * φ Y = 1 ∧ φ Y ≠ 1 ∧ sign (φ Y) = 1 :=
    ⟨by rw [← map_mul, hYY, map_one],
      fun h1 => hY1 (hφinj (h1.trans (map_one φ).symm)), hφsign Y⟩
  have habp : φ X * φ Y = φ Y * φ X ∧ φ X ≠ φ Y :=
    ⟨by rw [← map_mul, ← map_mul, hXY], fun h1 => hXYne (hφinj h1)⟩
  have hσp : φ T' * φ T' * φ T' = 1 ∧ φ T' ≠ 1 :=
    ⟨by rw [← map_mul, ← map_mul, hT3, map_one],
      fun h1 => hT1 (hφinj (h1.trans (map_one φ).symm))⟩
  have htx : t * x * t⁻¹ ∈ Q := hS.t_norm_Q x hS.x_mem
  have htx1 : t * x * t⁻¹ ≠ 1 := by
    intro h1
    apply hS.x_ne
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group
  have htxx : t * x * t⁻¹ ≠ x := by
    intro h1
    have hc : t * x = x * t := by
      calc t * x = (t * x * t⁻¹) * t := by group
        _ = x * t := by rw [h1]
    have h3 : (t * x) ^ 3 = 1 := hS.tx_cube
    have h4 : (t * x) ^ 3 = x := by
      rw [Commute.mul_pow (show Commute t x from hc), ht3, one_mul]
      calc x ^ 3 = x ^ 2 * x := pow_succ x 2
        _ = x := by rw [hS.x_sq, one_mul]
    exact hS.x_ne (h4.symm.trans h3)
  have hTXT : T' * X * T'⁻¹ = Y ∨ T' * X * T'⁻¹ = X * Y := by
    rcases hQall (t * x * t⁻¹) htx with h1 | h1 | h1 | h1
    · exact absurd h1 htx1
    · exact absurd h1 htxx
    · left
      apply Subtype.ext
      show cg t * cg x * (cg t)⁻¹ = cg y₀
      rw [← map_inv, ← map_mul, ← map_mul, h1]
    · right
      apply Subtype.ext
      show cg t * cg x * (cg t)⁻¹ = cg x * cg y₀
      rw [← map_inv, ← map_mul, ← map_mul, h1, map_mul]
  have hσa : φ T' * φ X * (φ T')⁻¹ = φ Y ∨ φ T' * φ X * (φ T')⁻¹ = φ X * φ Y := by
    have e : φ T' * φ X * (φ T')⁻¹ = φ (T' * X * T'⁻¹) := by rw [map_mul, map_mul, map_inv]
    rcases hTXT with h1 | h1
    · left; rw [e, h1]
    · right; rw [e, h1, map_mul]
  have hty : t * y₀ * t⁻¹ ∈ Q := hS.t_norm_Q y₀ hy₀Q
  have hty1 : t * y₀ * t⁻¹ ≠ 1 := by
    intro h1
    apply hy₀1
    calc y₀ = t⁻¹ * (t * y₀ * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group
  have hTYT : T' * Y * T'⁻¹ = X ∨ T' * Y * T'⁻¹ = Y ∨ T' * Y * T'⁻¹ = X * Y := by
    rcases hQall (t * y₀ * t⁻¹) hty with h1 | h1 | h1 | h1
    · exact absurd h1 hty1
    · left
      apply Subtype.ext
      show cg t * cg y₀ * (cg t)⁻¹ = cg x
      rw [← map_inv, ← map_mul, ← map_mul, h1]
    · right; left
      apply Subtype.ext
      show cg t * cg y₀ * (cg t)⁻¹ = cg y₀
      rw [← map_inv, ← map_mul, ← map_mul, h1]
    · right; right
      apply Subtype.ext
      show cg t * cg y₀ * (cg t)⁻¹ = cg x * cg y₀
      rw [← map_inv, ← map_mul, ← map_mul, h1, map_mul]
  have hσb : φ T' * φ Y * (φ T')⁻¹ = φ X ∨ φ T' * φ Y * (φ T')⁻¹ = φ Y ∨
      φ T' * φ Y * (φ T')⁻¹ = φ X * φ Y := by
    have e : φ T' * φ Y * (φ T')⁻¹ = φ (T' * Y * T'⁻¹) := by rw [map_mul, map_mul, map_inv]
    rcases hTYT with h1 | h1 | h1
    · left; rw [e, h1]
    · right; left; rw [e, h1]
    · right; right; rw [e, h1, map_mul]
  obtain ⟨ρ, hρ3, hρ1, hρc⟩ := hρ
  have hρα : ρ * φ X = φ X * ρ := hρc X ⟨x, hS.x_mem, rfl⟩
  have hρβ : ρ * φ Y = φ Y * ρ := hρc Y ⟨y₀, hy₀Q, rfl⟩
  exact finite_six_clause4 hαp hβp habp ⟨ρ, hρ3, hρ1, hρα, hρβ⟩ hσp hσa hσb
    ⟨hφ0 X, hφ0 Y, hφ0 T'⟩

theorem clause4_six
    {G : Type} [Group G] {x : G} {K Q : Subgroup G} {t u g : G}
    (hS : Stage3Loc 6 x K Q t u g) {L : Subgroup G} (hKL : K ≤ L)
    (hLt : ∀ l ∈ L, l * t = t * l)
    (hC' : ∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l)
    (lam : ↥L ≃* alternatingGroup (Fin 7))
    (hstab : ∀ l : ↥L, (l : G) ∈ K ↔
      ((lam l : alternatingGroup (Fin 7)) : Perm (Fin 7)) 0 = 0) :
    ((lam ⟨g * t * g⁻¹, hKL hS.gt_K⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)).IsThreeCycle := by
  let φ : ↥K →* Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp (lam.toMonoidHom.comp (Subgroup.inclusion hKL))
  have hφ : ∀ k : ↥K, φ k = ((lam (Subgroup.inclusion hKL k) : alternatingGroup (Fin 7)) :
      Perm (Fin 7)) := fun k => rfl
  obtain ⟨l, hl, hl3, hl1, hlQ⟩ := exists_rho_six hS hLt hC'
  refine clause4_six_core hS φ ?_ ?_ ?_ ⟨((lam ⟨l, hl⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)),
    ?_, ?_, ?_⟩
  · intro k₁ k₂ h
    have h1 : lam (Subgroup.inclusion hKL k₁) = lam (Subgroup.inclusion hKL k₂) :=
      Subtype.ext h
    exact Subgroup.inclusion_injective hKL (lam.injective h1)
  · intro k
    rw [hφ]
    exact mem_alternatingGroup.1 (lam _).2
  · intro k
    rw [hφ]
    exact (hstab (Subgroup.inclusion hKL k)).1 k.2
  · have h1 : lam ⟨l, hl⟩ * lam ⟨l, hl⟩ * lam ⟨l, hl⟩ = 1 := by
      rw [← map_mul, ← map_mul]
      have : (⟨l, hl⟩ : ↥L) * ⟨l, hl⟩ * ⟨l, hl⟩ = 1 := Subtype.ext hl3
      rw [this, map_one]
    have := congrArg Subtype.val h1
    simpa using this
  · intro h1
    apply hl1
    have h2 : lam ⟨l, hl⟩ = 1 := Subtype.ext (by simpa using h1)
    have h3 : (⟨l, hl⟩ : ↥L) = 1 := lam.injective (by rw [h2, map_one])
    exact congrArg Subtype.val h3
  · intro k ⟨q, hq, hkq⟩
    rw [hφ]
    have h1 : ((l : G)) * (k : G) = (k : G) * l := by
      rw [hkq]
      exact (hlQ q hq).symm
    have h2 : (⟨l, hl⟩ : ↥L) * Subgroup.inclusion hKL k = Subgroup.inclusion hKL k * ⟨l, hl⟩ :=
      Subtype.ext h1
    have h3 := congrArg (fun z : ↥L => ((lam z : alternatingGroup (Fin 7)) : Perm (Fin 7))) h2
    simpa using h3

theorem s_lemma123_core6_of_recog
    (h5 : S_recog 5) (h6 : S_recog 6) (h7 : S_recog 7) :
    S_lemma123_core6 := by
  intro G _ _ hC n hn x K T Q S a h hap t u g hS
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hn
  have hrec : ∃ L : Subgroup G, (∀ l ∈ L, l * t = t * l) ∧
      (∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l) ∧
      (∀ i : ℤ, t ^ i ∈ L → t ^ i = 1) ∧ Nonempty (↥L ≃* alternatingGroup (Fin (n + 1))) := by
    rcases hn' with rfl | rfl | rfl
    · exact h5 G hC x K T Q S a h hap t u g hS
    · exact h6 G hC x K T Q S a h hap t u g hS
    · exact h7 G hC x K T Q S a h hap t u g hS
  obtain ⟨L, hLt, hC', hZ, ⟨lam₀⟩⟩ := hrec
  obtain ⟨hKL, lam, hstab⟩ := stab_iso_of_recog (by omega) hS hLt hC' lam₀
  refine ⟨L, lam, hLt, hC', hZ, fun h6' hgtL => ?_⟩
  subst h6'
  exact clause4_six hS hKL hLt hC' lam hstab

end CFSG.GH74.GLS.C3.Prop121
