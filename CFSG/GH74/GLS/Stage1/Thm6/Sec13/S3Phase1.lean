module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Quot
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Sq
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Lift
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3ChainN
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Fus
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3NF

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_of_involution {y : G} (hy : y * y = 1) {N : Subgroup G}
    (h : ∀ g ∈ N, y * g * y⁻¹ ∈ N) : y ∈ normalizer (N : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  refine ⟨h g, fun hg => ?_⟩
  have := h _ hg
  have e : y * (y * g * y⁻¹) * y⁻¹ = g := by
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
    rw [hyi]
    calc y * (y * g * y) * y = (y * y) * g * (y * y) := by group
      _ = g := by rw [hy]; group
  rwa [e] at this

theorem four_mul_le_card_cent' [Finite G] {S P : Subgroup G} (hPS : P ≤ S) {y : G}
    (e₁ e₂ e₃ : G) (h₁ : e₁ ∈ S ⊓ centralizer ({y} : Set G))
    (h₂ : e₂ ∈ S ⊓ centralizer ({y} : Set G)) (h₃ : e₃ ∈ S ⊓ centralizer ({y} : Set G))
    (h01 : e₁ ∉ P) (h02 : e₂ ∉ P) (h03 : e₃ ∉ P) (h12 : e₁⁻¹ * e₂ ∉ P) (h13 : e₁⁻¹ * e₃ ∉ P)
    (h23 : e₂⁻¹ * e₃ ∉ P) :
    4 * Nat.card ↥(P ⊓ centralizer ({y} : Set G)) ≤ Nat.card ↥(S ⊓ centralizer ({y} : Set G)) := by
  refine four_mul_le_card_cent hPS ![1, e₁, e₂, e₃] ?_ ?_
  · intro i
    fin_cases i
    · exact (S ⊓ centralizer ({y} : Set G)).one_mem
    · exact h₁
    · exact h₂
    · exact h₃
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> assumption

namespace Ctx3

variable {x : G} {T V H : Subgroup G} {f : G} (c : Ctx3 G x T V H f)
include c

theorem phase1 [Finite G] (h9 : IG_9_16) (h10 : IG_10_31) (h15 : IG_15_15)
    (hY : YFacts V (Hzero H f))
    (hchain : ∀ (y : G) (S : Subgroup G), YCtx (Hzero H f) V y → Hzero H f ≤ S → y ∈ S →
      y ∉ Hzero H f → (∀ s ∈ S, ∀ n ∈ V ⊓ centralizer ({y} : Set G), s * n * s⁻¹ = n) →
      Nat.card ↥(S ⊓ centralizer ({y} : Set G)) ≤ 16 →
      ∃ (n : ℕ) (Pi : ℕ → Subgroup G), Pi 0 = ⊥ ∧ Pi n = Hzero H f ∧
        ∀ i < n, FreeSec2 y (Pi i) (Pi (i + 1))) :
    Sylow2In (H ⊔ T) ⊤ ∧ (∀ s ∈ H ⊔ T, ∀ q ∈ Hzero H f, s * q * s⁻¹ ∈ Hzero H f) ∧
      (Hzero H f).relIndex (H ⊔ T) = 4 ∧ (∀ s ∈ H ⊔ T, s * s ∈ Hzero H f) ∧
      Nat.card (Hzero H f) = 16 ∧
      ∃ w : G, w * x * w⁻¹ ∈ H ⊔ T ∧ w * x * w⁻¹ ∉ H ∧ YCtx (Hzero H f) V (w * x * w⁻¹) := by
  obtain ⟨⟨D, hD⟩, hQ, hA, hsqne, m, hm2, hPcard⟩ := hY
  have hVsq : V ≤ sq (Hzero H f) := c.V_le_sq hsqne
  have hPn := c.Hstar_norm_H0 h9 hD
  have hSyl := c.Hstar_sylow_top h9 hD hVsq hQ
  have hP2 : IsPGroup 2 ↥(Hzero H f) := c.H_two.to_le c.H0_le
  have hfus := not_fused_of_abelian c.out hP2 hA
  obtain ⟨w, hwS, hwH, hext⟩ := c.exists_y h15 c.out.simple c.out.nonabelian hSyl hPn hfus
  have hcardT := card_extremal c.out hext.2
  have hy2 : (w * x * w⁻¹) * (w * x * w⁻¹) = 1 := by
    calc (w * x * w⁻¹) * (w * x * w⁻¹) = w * (x * x) * w⁻¹ := by group
      _ = 1 := by rw [c.x_sq]; group
  generalize hyw : w * x * w⁻¹ = y at hwS hwH hext hcardT hy2
  have hPS : Hzero H f ≤ H ⊔ T := c.H0_le.trans le_sup_left
  have hyP' : y ∉ Hzero H f := fun h => hwH (c.H0_le h)
  have hyinv : y⁻¹ ∉ H := fun h => hwH (by simpa using H.inv_mem h)
  have hY' : YCtx (Hzero H f) V y := by
    refine ⟨hy2, hPn y hwS, ?_, ?_⟩
    · intro v hv
      exact (mem_normalizer_iff.1 (c.Hstar_le_N hwS) v).1 hv
    · by_contra hcon
      push Not at hcon
      apply hwH
      have hmem : y ∈ (H ⊔ T) ⊓ centralizer (V : Set G) := by
        refine ⟨hwS, ?_⟩
        show y ∈ centralizer (V : Set G)
        rw [mem_centralizer_iff]
        intro v hv
        have h := hcon v hv
        calc v * y = (y * v * y⁻¹) * y := by rw [h]
          _ = y * v := by group
      rw [c.Hstar_inf_C] at hmem
      exact hmem
  have hprod := (index_two_rules (le_sup_left : H ≤ H ⊔ T) (c.Hstar_card_two hwS hwH).1).1
  have hSZ : ∀ s ∈ H ⊔ T, ∀ n ∈ V ⊓ centralizer ({y} : Set G), s * n * s⁻¹ = n := by
    intro s hs n hn
    by_cases hsH : s ∈ H
    · exact c.H_cent_V hsH hn.1
    · have h1 : s * y⁻¹ ∈ H := hprod s hs y⁻¹ ((H ⊔ T).inv_mem hwS) hsH hyinv
      have hcy : y * n = n * y := mem_centralizer_iff.1 hn.2 y rfl
      have h2 : y * n * y⁻¹ = n := by
        calc y * n * y⁻¹ = (n * y) * y⁻¹ := by rw [hcy]
          _ = n := by group
      have e : s * n * s⁻¹ = (s * y⁻¹) * (y * n * y⁻¹) * (s * y⁻¹)⁻¹ := by group
      rw [e, h2]
      exact c.H_cent_V h1 hn.1
  have hSy : Nat.card ↥((H ⊔ T) ⊓ centralizer ({y} : Set G)) ≤ 16 := by
    rw [hcardT]; exact c.out.T_card
  obtain ⟨n', Pi, h0, hn', hfree⟩ := hchain y (H ⊔ T) hY' hPS hwS hyP' hSZ hSy
  have hmono : ∀ d i, i + d = n' → Pi i ≤ Hzero H f := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have : i = n' := by omega
      exact le_of_eq (by rw [this, hn'])
    | succ d ih =>
      intro i hi
      have hlt : i < n' := by omega
      exact (hfree i hlt).1.trans (ih (i + 1) (by omega))
  have hynot : ∀ i ≤ n', y ∉ Pi i := fun i hi h => hyP' (hmono (n' - i) i (by omega) h)
  have hyN : ∀ i ≤ n', y ∈ normalizer ((Pi i : Subgroup G) : Set G) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0' | hpos
    · rw [h0', h0]
      exact mem_normalizer_of_involution hy2 (fun g hg => by
        rw [Subgroup.mem_bot] at hg ⊢
        rw [hg]; group)
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact mem_normalizer_of_involution hy2 (hfree j (by omega)).2.2.2.2.1
  have hconj : ∀ i ≤ n', ∀ p ∈ Pi i, (p * y) * (p * y) = 1 → ∃ q ∈ Pi i, p * y = q * y * q⁻¹ :=
    fun i hi => h10 G (Pi i) y i Pi hy2 (hyN i hi) (hynot i hi) h0 rfl
      (fun j hj => hfree j (lt_of_lt_of_le hj hi))
  have hcc := card_cent_chain hy2 Pi h0 hfree (fun i hi => hconj i hi.le)
  rw [hn'] at hcc
  have hconjP : ∀ p ∈ Hzero H f, (p * y) * (p * y) = 1 →
      ∃ q ∈ Hzero H f, p * y = q * y * q⁻¹ := by
    have := hconj n' le_rfl
    rwa [hn'] at this
  have hyx := c.y_x_comm_mem hPn hwS hwH
  obtain ⟨k, hk, hkx⟩ := lift_cent hy2 (fun n hn => hPn y hwS n hn) hconjP hyx
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = k * x := ⟨_, rfl⟩
  rw [← hc₀] at hkx
  have hc₀H : c₀ ∈ H := by rw [hc₀]; exact H.mul_mem (c.H0_le hk) c.x_mem_H
  have hc₀S : c₀ ∈ H ⊔ T := Subgroup.mem_sup_left hc₀H
  have hc₀C : c₀ ∈ centralizer ({y} : Set G) := by
    rw [mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    calc y * c₀ = (y * c₀ * y⁻¹) * y := by group
      _ = c₀ * y := by rw [hkx]
  have hyC : y ∈ centralizer ({y} : Set G) := by
    rw [mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
  have h₁ : c₀ ∈ (H ⊔ T) ⊓ centralizer ({y} : Set G) := ⟨hc₀S, hc₀C⟩
  have h₂ : y ∈ (H ⊔ T) ⊓ centralizer ({y} : Set G) := ⟨hwS, hyC⟩
  have h₃ : c₀ * y ∈ (H ⊔ T) ⊓ centralizer ({y} : Set G) :=
    ((H ⊔ T) ⊓ centralizer ({y} : Set G)).mul_mem h₁ h₂
  have h01 : c₀ ∉ Hzero H f := by
    intro h
    apply c.x_notin_H0
    have : x = k⁻¹ * c₀ := by rw [hc₀]; group
    rw [this]
    exact (Hzero H f).mul_mem ((Hzero H f).inv_mem hk) h
  have h03 : c₀ * y ∉ Hzero H f := by
    intro h
    apply hwH
    have : y = c₀⁻¹ * (c₀ * y) := by group
    rw [this]
    exact H.mul_mem (H.inv_mem hc₀H) (c.H0_le h)
  have h12 : c₀⁻¹ * y ∉ Hzero H f := by
    intro h
    apply hwH
    have : y = c₀ * (c₀⁻¹ * y) := by group
    rw [this]
    exact H.mul_mem hc₀H (c.H0_le h)
  have h13 : c₀⁻¹ * (c₀ * y) ∉ Hzero H f := by
    have : c₀⁻¹ * (c₀ * y) = y := by group
    rw [this]; exact hyP'
  have h23 : y⁻¹ * (c₀ * y) ∉ Hzero H f := by
    have hcy : y * c₀ = c₀ * y := mem_centralizer_iff.1 hc₀C y rfl
    have : y⁻¹ * (c₀ * y) = c₀ := by
      calc y⁻¹ * (c₀ * y) = y⁻¹ * (y * c₀) := by rw [hcy]
        _ = c₀ := by group
    rw [this]; exact h01
  have h4 := four_mul_le_card_cent' hPS c₀ y (c₀ * y) h₁ h₂ h₃ h01 hyP' h03 h12 h13 h23
  rw [hcardT] at h4
  have hT16 := c.out.T_card
  have hcc4 : Nat.card ↥(Hzero H f ⊓ centralizer ({y} : Set G)) ≤ 4 := by omega
  have hP16 : Nat.card (Hzero H f) ≤ 16 := by
    calc Nat.card (Hzero H f) ≤ Nat.card ↥(Hzero H f ⊓ centralizer ({y} : Set G)) ^ 2 := hcc
      _ ≤ 4 ^ 2 := Nat.pow_le_pow_left hcc4 2
      _ = 16 := by norm_num
  have h16m : 16 ≤ 4 ^ m := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hP16' : Nat.card (Hzero H f) = 16 := by omega
  have hrel := relIndex_mul_relIndex (Hzero H f) H (H ⊔ T) c.H0_le le_sup_left
  rw [c.P_relIndex_H, (c.Hstar_card_two hwS hwH).1] at hrel
  refine ⟨hSyl, hPn, by omega, c.S_sq hPn hwS hwH hy2, hP16', w, ?_⟩
  rw [hyw]
  exact ⟨hwS, hwH, hY'⟩

end Ctx3

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
