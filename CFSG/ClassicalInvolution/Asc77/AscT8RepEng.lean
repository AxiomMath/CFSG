module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenRep

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8V

section Hooks

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

structure RepHooks (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop where
  comm_W : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x
  Dinv : ∀ {R : Subgroup G}, R ∈ DSet Ω W → ∀ {r r' : G}, r ∈ R → r' ∈ R → r ∉ W → r' ∉ W →
    r⁻¹ * r' ∈ W
  uW : ∀ {K R : Subgroup G}, K ∈ Ω → R ∈ DSet Ω W → IsSylow2In R K → ∀ {z : G},
    IsUniqueInvolution K z → z ∈ K ⊓ W
  conj_inv : ∀ (ρ : Rep Ω W) {u : G}, u ∈ ρ.K ⊓ W → ρ.r * u * ρ.r⁻¹ = u⁻¹
  conj_involution : ∀ (ρ σ : Rep Ω W), ρ.K ≠ σ.K → σ.K ∉ omegaNbr Ω ρ.K → ∀ {z j : G},
    IsUniqueInvolution ρ.K z → IsUniqueInvolution σ.K j → ρ.r * j * ρ.r⁻¹ = z * j
  centralizes : ∀ (ρ σ : Rep Ω W), σ.K ∈ omegaNbr Ω ρ.K → ∀ {v : G}, v ∈ σ.K ⊓ W →
    ρ.r * v = v * ρ.r

end Hooks

section OfCtx

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem RepHooks.ofCtx (c : Ctx p f Ω W) : RepHooks Ω W :=
  ⟨c.comm_W,
    fun hR => fun hr hr' hrW hr'W => D_inv_mul_mem c.hp c.hq c.hΩ c.hW hR hr hr' hrW hr'W,
    fun hK hR hRK => fun hz => uniqueInvolution_mem_W c.hp c.hq c.hΩ c.hW hK hR hRK hz,
    fun ρ => fun hu => c.conj_inv ρ hu,
    fun ρ σ hne hnot => fun hz hj => c.conj_involution ρ σ hne hnot hz hj,
    fun ρ σ h => fun hv => c.centralizes ρ σ h hv⟩

end OfCtx

section Alg

variable {G : Type} [Group G]

theorem mul_inv_inv_sqE {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) :
    (a * b⁻¹ * c⁻¹) * (a * b⁻¹ * c⁻¹) = (a * a) * ((b * b)⁻¹ * (c * c)⁻¹) := by
  have h1 : Commute (a * b⁻¹) c⁻¹ := (hac.inv_right).mul_left (hbc.inv_inv)
  rw [← pow_two, h1.mul_pow, (hab.inv_right).mul_pow, pow_two, pow_two, pow_two, mul_inv_rev,
    mul_inv_rev, mul_assoc]

end Alg

section Engines

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem rep_le_centralizerE (H : RepHooks Ω W) (ρ σ : Rep Ω W)
    (hσ : σ.K = ρ.K ∨ σ.K ∈ omegaNbr Ω ρ.K) {v : G} (hv : IsUniqueInvolution σ.K v) :
    ρ.R ≤ Subgroup.centralizer ({v} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hσ with h | h
  · rw [h] at hv
    have := hv.conj_eq (n := y) (conjSub_eq_self_of_mem (ρ.hRK.1 hy))
    calc y * v = (y * v * y⁻¹) * y := by group
      _ = v * y := by rw [this]
  · have hvW : v ∈ σ.K ⊓ W :=
      H.uW σ.hK σ.hR σ.hRK hv
    have hrv : ρ.r * v = v * ρ.r := H.centralizes ρ σ h hvW
    by_cases hyW : y ∈ W
    · exact H.comm_W y hyW v hvW.2
    · have hw : ρ.r⁻¹ * y ∈ W :=
        H.Dinv ρ.hR ρ.hr hy ρ.hrW hyW
      have hwv : (ρ.r⁻¹ * y) * v = v * (ρ.r⁻¹ * y) := H.comm_W _ hw v hvW.2
      have hy' : y = ρ.r * (ρ.r⁻¹ * y) := by group
      calc y * v = ρ.r * ((ρ.r⁻¹ * y) * v) := by rw [hy']; group
        _ = ρ.r * (v * (ρ.r⁻¹ * y)) := by rw [hwv]
        _ = (ρ.r * v) * (ρ.r⁻¹ * y) := by group
        _ = (v * ρ.r) * (ρ.r⁻¹ * y) := by rw [hrv]
        _ = v * y := by group

theorem centralizes_of_comm_rE (H : RepHooks Ω W) (ρ : Rep Ω W) {y : G} (hyW : y ∈ W)
    (hry : ρ.r * y = y * ρ.r) : ∀ x ∈ ρ.R, x * y = y * x := by
  intro x hx
  by_cases hxW : x ∈ W
  · exact H.comm_W x hxW y hyW
  · have hw : ρ.r⁻¹ * x ∈ W := H.Dinv ρ.hR ρ.hr hx ρ.hrW hxW
    have hwy : (ρ.r⁻¹ * x) * y = y * (ρ.r⁻¹ * x) := H.comm_W _ hw y hyW
    calc x * y = ρ.r * ((ρ.r⁻¹ * x) * y) := by group
      _ = ρ.r * (y * (ρ.r⁻¹ * x)) := by rw [hwy]
      _ = (ρ.r * y) * (ρ.r⁻¹ * x) := by group
      _ = (y * ρ.r) * (ρ.r⁻¹ * x) := by rw [hry]
      _ = y * x := by group

theorem centralizes_vgE (H : RepHooks Ω W) (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K)
    (hnot : σ.K ∉ omegaNbr Ω ρ.K) {z v g : G} (hz : IsUniqueInvolution ρ.K z)
    (hv : IsUniqueInvolution σ.K v) (hg : g ∈ ρ.K ⊓ W) (hgg : g * g = z) :
    v * g⁻¹ ∈ W ∧ (∀ x ∈ ρ.R, x * (v * g⁻¹) = (v * g⁻¹) * x) ∧
      (v * g⁻¹) * (v * g⁻¹) = z := by
  have hvW : v ∈ W :=
    (H.uW σ.hK σ.hR σ.hRK hv).2
  have hzW : z ∈ W := (H.uW ρ.hK ρ.hR ρ.hRK hz).2
  have hyW : v * g⁻¹ ∈ W := W.mul_mem hvW (W.inv_mem hg.2)
  have h1 : ρ.r * v * ρ.r⁻¹ = z * v := H.conj_involution ρ σ hne hnot hz hv
  have h2 : ρ.r * g * ρ.r⁻¹ = g⁻¹ := H.conj_inv ρ hg
  have hzz : z * z = 1 := hz.sq
  have hgi : g⁻¹ = g * z := by
    have : g * (g * z) = 1 := by rw [← mul_assoc, hgg, hzz]
    exact inv_eq_of_mul_eq_one_right this
  have hgz : g * z = z * g := H.comm_W g hg.2 z hzW
  have hvg : v * g = g * v := H.comm_W v hvW g hg.2
  have hvz : v * z = z * v := H.comm_W v hvW z hzW
  have hvv : v * v = 1 := hv.sq
  have hrg : ρ.r * g⁻¹ * ρ.r⁻¹ = g := by
    have : ρ.r * g⁻¹ * ρ.r⁻¹ = (ρ.r * g * ρ.r⁻¹)⁻¹ := by group
    rw [this, h2, inv_inv]
  have hcomm : ρ.r * (v * g⁻¹) = (v * g⁻¹) * ρ.r := by
    have : ρ.r * (v * g⁻¹) * ρ.r⁻¹ = v * g⁻¹ := by
      calc ρ.r * (v * g⁻¹) * ρ.r⁻¹ = (ρ.r * v * ρ.r⁻¹) * (ρ.r * g⁻¹ * ρ.r⁻¹) := by group
        _ = (z * v) * g := by rw [h1, hrg]
        _ = v * (z * g) := by rw [← hvz, mul_assoc]
        _ = v * g⁻¹ := by rw [hgi, hgz]
    calc ρ.r * (v * g⁻¹) = (ρ.r * (v * g⁻¹) * ρ.r⁻¹) * ρ.r := by group
      _ = (v * g⁻¹) * ρ.r := by rw [this]
  refine ⟨hyW, centralizes_of_comm_rE H ρ hyW hcomm, ?_⟩
  calc (v * g⁻¹) * (v * g⁻¹) = (v * v) * (g⁻¹ * g⁻¹) := by
        have : g⁻¹ * v = v * g⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hvg]; group
        calc (v * g⁻¹) * (v * g⁻¹) = v * (g⁻¹ * v) * g⁻¹ := by group
          _ = v * (v * g⁻¹) * g⁻¹ := by rw [this]
          _ = (v * v) * (g⁻¹ * g⁻¹) := by group
    _ = z := by
      rw [hvv, one_mul]
      have : g⁻¹ * g⁻¹ = (g * g)⁻¹ := by group
      rw [this, hgg]
      exact inv_eq_of_mul_eq_one_right hzz

theorem centralizes_mem_inf_WE (H : RepHooks Ω W) (ρ σ : Rep Ω W) (hnbr : σ.K ∈ omegaNbr Ω ρ.K)
    {g : G} (hg : g ∈ σ.K ⊓ W) : ∀ x ∈ ρ.R, x * g = g * x :=
  centralizes_of_comm_rE H ρ hg.2 (H.centralizes ρ σ hnbr hg)

theorem exists_y_bothE (H : RepHooks Ω W) (ρ₁ ρ₂ σ : Rep Ω W) {z₁ z₂ v g h : G}
    (hn12 : ρ₂.K ∈ omegaNbr Ω ρ₁.K) (hn21 : ρ₁.K ∈ omegaNbr Ω ρ₂.K) (hne1 : ρ₁.K ≠ σ.K)
    (hne2 : ρ₂.K ≠ σ.K) (hnot1 : σ.K ∉ omegaNbr Ω ρ₁.K) (hnot2 : σ.K ∉ omegaNbr Ω ρ₂.K)
    (hz₁ : IsUniqueInvolution ρ₁.K z₁) (hz₂ : IsUniqueInvolution ρ₂.K z₂)
    (hv : IsUniqueInvolution σ.K v) (hg : g ∈ ρ₁.K ⊓ W) (hgg : g * g = z₁)
    (hh : h ∈ ρ₂.K ⊓ W) (hhh : h * h = z₂) :
    ∃ y ∈ W, y = v * g⁻¹ * h⁻¹ ∧ y * y = z₁ * z₂ ∧ (∀ x ∈ ρ₁.R, x * y = y * x) ∧
      (∀ x ∈ ρ₂.R, x * y = y * x) := by
  obtain ⟨hyW1, hy1, hyy1⟩ := centralizes_vgE H ρ₁ σ hne1 hnot1 hz₁ hv hg hgg
  obtain ⟨hyW2, hy2, hyy2⟩ := centralizes_vgE H ρ₂ σ hne2 hnot2 hz₂ hv hh hhh
  have hvW : v ∈ W := (H.uW σ.hK σ.hR σ.hRK hv).2
  have hz₁W : z₁ ∈ W := (H.uW ρ₁.hK ρ₁.hR ρ₁.hRK hz₁).2
  have hz₂W : z₂ ∈ W := (H.uW ρ₂.hK ρ₂.hR ρ₂.hRK hz₂).2
  have hgh : Commute g h := H.comm_W g hg.2 h hh.2
  have hvg : Commute v g := H.comm_W v hvW g hg.2
  have hvh : Commute v h := H.comm_W v hvW h hh.2
  have hz12 : Commute z₁ z₂ := H.comm_W z₁ hz₁W z₂ hz₂W
  have hyW : v * g⁻¹ * h⁻¹ ∈ W := W.mul_mem hyW1 (W.inv_mem hh.2)
  refine ⟨v * g⁻¹ * h⁻¹, hyW, rfl, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_inv_inv_sqE hvg hvh hgh, hv.sq, hgg, hhh, one_mul]
    have i1 : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁.sq
    have i2 : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right hz₂.sq
    rw [i1, i2]
  · have h1 : Commute x (v * g⁻¹) := hy1 x hx
    have h2 : Commute x h := centralizes_mem_inf_WE H ρ₁ ρ₂ hn12 hh x hx
    exact h1.mul_right h2.inv_right
  · have h1 : Commute x (v * h⁻¹) := hy2 x hx
    have h2 : Commute x g := centralizes_mem_inf_WE H ρ₂ ρ₁ hn21 hg x hx
    have e : v * g⁻¹ * h⁻¹ = (v * h⁻¹) * g⁻¹ := by
      rw [mul_assoc, mul_assoc, hgh.inv_inv.eq]
    rw [e]
    exact h1.mul_right h2.inv_right

end Engines

end T8V

end CFSG.ClassicalInvolution.Asc77
