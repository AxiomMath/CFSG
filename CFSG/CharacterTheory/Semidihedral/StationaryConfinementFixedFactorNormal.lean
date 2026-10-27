module

public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementFixedFactorData
public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementFixedFactorCycling
public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementInverted

public section

namespace CFSG.Semidihedral.StationaryConfinement

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_commutator_self {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    g ∈ Subgroup.normalizer ((⁅R, R⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [Subgroup.map_commutator, hg]

omit [Finite G] in
theorem commutator_self_le (R : Subgroup G) : ⁅R, R⁆ ≤ R := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)

theorem mem_normalizer_closure_pair {t s d : G} (hdt : d * t * d⁻¹ = t)
    (hds : d * s * d⁻¹ ∈ Subgroup.closure ({t, s} : Set G)) :
    d ∈ Subgroup.normalizer (Subgroup.closure ({t, s} : Set G) : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  have hle : Subgroup.closure ({t, s} : Set G) ≤
      (Subgroup.closure ({t, s} : Set G)).comap (MulAut.conj d).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx, SetLike.mem_coe, Subgroup.mem_comap]
      change d * t * d⁻¹ ∈ _
      rw [hdt]
      exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff.mp hx, SetLike.mem_coe, Subgroup.mem_comap]
      exact hds
  intro v hv
  exact hle hv

theorem fixed_factor_product_normal [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    (R Ya W A₀ : Subgroup G) (d : G)
    (hRD : R ≤ C t ⊓ Subgroup.centralizer ({s} : Set G))
    (hRn : Subgroup.normalizer (Subgroup.closure ({t, s} : Set G) : Set G) ≤
      Subgroup.normalizer (R : Set G))
    (hRodd : Odd (Nat.card R))
    (hCV : Subgroup.centralizer (Subgroup.closure ({t, s} : Set G) : Set G) =
      Subgroup.closure ({t, s} : Set G) ⊔ R)
    (hYn : C t ≤ Subgroup.normalizer (Ya : Set G))
    (hBR : W ⊔ A₀ = R ⊓ Ya) (hWR : W ≤ R)
    (hWab : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w)
    (hWA : ∀ w ∈ W, ∀ a ∈ A₀, w * a = a * w)
    (hAodd : ∀ a ∈ A₀, Odd (orderOf a))
    (hAs : A₀ ≤ Subgroup.centralizer ({s} : Set G))
    (hWs : W ≤ Subgroup.centralizer ({s} : Set G))
    (hdY : d ∈ Ya) (hdC : d ∈ C t) (hd2 : d ^ 2 = t) (hds : d * s * d⁻¹ = t * s)
    (hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹) (hdA : ∀ a ∈ A₀, d * a = a * d)
    (hRR : ⁅R, R⁆ ≤ Ya)
    (hX : ∀ x ∈ R, (∀ y ∈ ⁅R, R⁆, x * y = y * x) → x ∈ Ya) :
    Subgroup.normalizer (Subgroup.closure ({t, s} : Set G) : Set G) ≤
      Subgroup.normalizer ((W ⊔ A₀ : Subgroup G) : Set G) := by
  classical
  set V := Subgroup.closure ({t, s} : Set G) with hVdef
  set M := Subgroup.normalizer (V : Set G) with hMdef
  obtain ⟨-, htV, hsV, -, ht1, hs1, -, -, hts'⟩ := pair_facts t s ht hs hsC hts
  have hcomm : Commute t s := hts'
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hBR' : W ⊔ A₀ ≤ R := hBR ▸ inf_le_left
  have hRC : R ≤ C t := hRD.trans inf_le_left
  have hRs : R ≤ Subgroup.centralizer ({s} : Set G) := hRD.trans inf_le_right
  have hCVM : Subgroup.centralizer (V : Set G) ≤ M := Subgroup.centralizer_le_normalizer _
  have hRM : R ≤ M := by
    refine le_trans ?_ hCVM
    rw [centralizer_closure_pair]
    exact hRD
  have hconjR : ∀ g ∈ M, ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg r hr =>
    (Subgroup.mem_normalizer_iff.mp (hRn hg) r).mp hr
  set X := R ⊓ Subgroup.centralizer ((⁅R, R⁆ : Subgroup G) : Set G) with hXdef
  have hXB : X ≤ W ⊔ A₀ := by
    intro x hx
    rw [hBR]
    exact ⟨hx.1, hX x hx.1 fun y hy => (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm⟩
  have hWX : W ≤ X := by
    intro w hw
    refine ⟨hWR hw, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    have hyB : y ∈ W ⊔ A₀ := by
      rw [hBR]
      exact ⟨commutator_self_le R hy, hRR hy⟩
    obtain ⟨w', hw', a, ha, rfl⟩ := mem_sup_of_commute hWA hyB
    calc w' * a * w = w' * (w * a) := by rw [mul_assoc, ← hWA w hw a ha]
      _ = w * (w' * a) := by rw [← mul_assoc, hWab w' hw' w hw, mul_assoc]
  have hXn : M ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hRn hg, normalizer_le_normalizer_centralizer' _ (mem_normalizer_commutator_self (hRn hg))⟩
  have hdt : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
  have hdM : d ∈ M := by
    apply mem_normalizer_closure_pair
    · rw [hdt, mul_inv_cancel_right]
    · rw [hds]
      exact Subgroup.mul_mem _ htV hsV
  set k := s * d with hkdef
  have hkM : k ∈ M := M.mul_mem (Subgroup.le_normalizer hsV) hdM
  have hk2 : k * k = 1 := by
    have h : k * k = s * (d * s * d⁻¹) * d ^ 2 := by rw [hkdef]; group
    rw [h, hds, hd2]
    calc s * (t * s) * t = s * (s * t) * t := by rw [hcomm.eq]
      _ = (s * s) * (t * t) := by group
      _ = 1 := by rw [hs2, ht2, one_mul]
  have hk1 : k ≠ 1 := by
    intro h
    have hd : d = s := by
      rw [hkdef] at h
      rw [← hsinv]
      exact eq_inv_of_mul_eq_one_right h
    rw [hd, pow_two, hs2] at hd2
    exact ht1 hd2.symm
  have hkord : orderOf k = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hk2) hk1
  have hkact : ∃ v ∈ V, k * v * k⁻¹ ≠ v := by
    refine ⟨s, hsV, fun h => ht1 ?_⟩
    have h' : k * s * k⁻¹ = s * t := by
      calc k * s * k⁻¹ = s * (d * s * d⁻¹) * s⁻¹ := by rw [hkdef]; group
        _ = s * t := by rw [hds]; group
    rw [h'] at h
    exact mul_left_cancel (h.trans (mul_one s).symm)
  have hkB : ∀ r ∈ R, r⁻¹ * (k * r * k⁻¹) ∈ W ⊔ A₀ := by
    intro r hr
    have hdr : d * r * d⁻¹ ∈ R := hconjR d hdM r hr
    have hsr : s * (d * r * d⁻¹) * s⁻¹ = d * r * d⁻¹ := by
      rw [(Subgroup.mem_centralizer_singleton_iff.mp (hRs hdr)).symm, mul_inv_cancel_right]
    have hkr : k * r * k⁻¹ = d * r * d⁻¹ := by
      rw [← hsr, hkdef]
      group
    rw [hkr, hBR]
    refine ⟨R.mul_mem (R.inv_mem hr) hdr, ?_⟩
    have hrY : r⁻¹ * d * r ∈ Ya := by
      have := (Subgroup.mem_normalizer_iff.mp (hYn (Subgroup.inv_mem _ (hRC hr))) d).mp hdY
      simpa only [inv_inv] using this
    have : r⁻¹ * (d * r * d⁻¹) = (r⁻¹ * d * r) * d⁻¹ := by group
    rw [this]
    exact Ya.mul_mem hrY (Ya.inv_mem hdY)
  have hkW : ∀ w ∈ W, k * w * k⁻¹ = w⁻¹ := by
    intro w hw
    have h1 : s * w⁻¹ * s⁻¹ = w⁻¹ := by
      rw [(Subgroup.mem_centralizer_singleton_iff.mp (hWs (W.inv_mem hw))).symm,
        mul_inv_cancel_right]
    calc k * w * k⁻¹ = s * (d * w * d⁻¹) * s⁻¹ := by rw [hkdef]; group
      _ = w⁻¹ := by rw [hdW w hw, h1]
  have hkA : ∀ a ∈ A₀, k * a * k⁻¹ = a := by
    intro a ha
    have h1 : s * a * s⁻¹ = a := by
      rw [(Subgroup.mem_centralizer_singleton_iff.mp (hAs ha)).symm, mul_inv_cancel_right]
    calc k * a * k⁻¹ = s * (d * a * d⁻¹) * s⁻¹ := by rw [hkdef]; group
      _ = a := by rw [hdA a ha, mul_inv_cancel_right, h1]
  have hkW' := involution_trivial_mod_of_trivial_mod_product hk2 hWA hAodd hkW hkA hkB
  have hkX : ∀ r ∈ R, r⁻¹ * (k * r * k⁻¹) ∈ X := fun r hr => hWX (hkW' r hr)
  obtain ⟨a, haM, haodd, hka, hgen⟩ := exists_inverted_odd_cycling_element n hn S0 f0 t s ht hs
    hcomm hts R hRodd hRM hRn hCV k hkM hkord hkact
  have haX := odd_trivial_mod_of_inverted (hRn haM) (hXn haM) (hRn hkM) hkX hka haodd
  apply hgen
  · intro x hx
    have hxM := hCVM hx
    rw [centralizer_closure_pair] at hx
    rw [hBR]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hRn hxM, hYn hx.1⟩
  · exact mem_normalizer_of_trivial_mod hXB hBR' hkX
  · exact mem_normalizer_of_trivial_mod hXB hBR' haX

end CFSG.Semidihedral.StationaryConfinement
