module

public import CFSG.ClassicalInvolution.AschTight.S19LU
public import CFSG.ClassicalInvolution.AschTight.S19LTrace
public import CFSG.ClassicalInvolution.AschTight.S1911E2a

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19L

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem conj_eq_zpow_of_conj_inf (hd : Sec19DataT p f K z S W L t V) {b : G}
    (hbV : b ∈ Subgroup.normalizer (V : Set G))
    (hbY : b ∈ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G)) {m : ℤ}
    (hbU : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ m) : ∀ c ∈ W ⊓ sec19Y K z, b * c * b⁻¹ = c ^ m := by
  have ef := S1911.etaYForm p f G K z S W L t V hd
  intro c hc
  have hVN : V ≤ Subgroup.normalizer ((W ⊓ K : Subgroup G) : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hvW := hd.leW hv
    constructor
    · intro hx
      have e : v * x * v⁻¹ = x := by rw [ef.comm v hvW x hx.1]; group
      rw [e]
      exact hx
    · intro hx
      have hxW : x ∈ W := by
        have e : x = v⁻¹ * (v * x * v⁻¹) * v := by group
        rw [e]
        exact W.mul_mem (W.mul_mem (W.inv_mem hvW) hx.1) hvW
      have e : v * x * v⁻¹ = x := by rw [ef.comm v hvW x hxW]; group
      rwa [e] at hx
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left (W ⊓ K) V hVN
  have hcUV : c ∈ (((W ⊓ K : Subgroup G) : Set G) * (V : Set G)) := by
    rw [← hset, ← ef.supU]
    exact hc.1
  obtain ⟨u₁, hu₁, v₁, hv₁, rfl⟩ := Set.mem_mul.mp hcUV
  have hu₁W : u₁ ∈ W := hu₁.1
  have hv₁W : v₁ ∈ W := hd.leW hv₁
  have hβV : b * v₁ * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hbV v₁).mp hv₁
  have hβW : b * v₁ * b⁻¹ ∈ W := hd.leW hβV
  have hu₁m := hbU u₁ ⟨hu₁.2, hu₁.1⟩
  set w := b * (u₁ * v₁) * b⁻¹ * ((u₁ * v₁) ^ m)⁻¹ with hw
  have hcomm := ef.comm
  have hwV : w ∈ V := by
    have e1 : (u₁ * v₁) ^ m = u₁ ^ m * v₁ ^ m := (Commute.mul_zpow (hcomm u₁ hu₁W v₁ hv₁W) m)
    have e2 : b * (u₁ * v₁) * b⁻¹ = u₁ ^ m * (b * v₁ * b⁻¹) := by
      rw [← hu₁m]
      group
    have hum : u₁ ^ m ∈ W := zpow_mem hu₁W m
    have hvm : v₁ ^ m ∈ W := zpow_mem hv₁W m
    have e3 : w = (b * v₁ * b⁻¹) * (v₁ ^ m)⁻¹ := by
      rw [hw, e1, e2]
      have hc1 := hcomm (u₁ ^ m) hum (b * v₁ * b⁻¹) hβW
      have hc2 := hcomm (u₁ ^ m) hum (v₁ ^ m) hvm
      calc u₁ ^ m * (b * v₁ * b⁻¹) * (u₁ ^ m * v₁ ^ m)⁻¹ =
          u₁ ^ m * (b * v₁ * b⁻¹) * (v₁ ^ m * u₁ ^ m)⁻¹ := by rw [hc2]
        _ = (u₁ ^ m * (b * v₁ * b⁻¹)) * (u₁ ^ m)⁻¹ * (v₁ ^ m)⁻¹ := by group
        _ = ((b * v₁ * b⁻¹) * u₁ ^ m) * (u₁ ^ m)⁻¹ * (v₁ ^ m)⁻¹ := by rw [hc1]
        _ = (b * v₁ * b⁻¹) * (v₁ ^ m)⁻¹ := by group
    rw [e3]
    exact V.mul_mem hβV (V.inv_mem (zpow_mem hv₁ m))
  have hwY : w ∈ sec19Y K z := by
    have h1 : b * (u₁ * v₁) * b⁻¹ ∈ sec19Y K z :=
      (Subgroup.mem_normalizer_iff.mp hbY _).mp hc.2
    exact (sec19Y K z).mul_mem h1 ((sec19Y K z).inv_mem (Subgroup.zpow_mem _ hc.2 m))
  have hw1 : w = 1 := by
    have h : w ∈ V ⊓ sec19Y K z := ⟨hwV, hwY⟩
    rw [ef.disj, Subgroup.mem_bot] at h
    exact h
  rw [hw, mul_inv_eq_one] at hw1
  exact hw1

omit [IsSimpleGroup G] in
theorem commutator_mem_oddCoreOf_of_mem {k : G} (hk : k ∈ K)
    (hkN : k ∈ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G)) :
    ∀ y ∈ sec19Y K z, ⁅k, y⁆ ∈ oddCoreOf (sec19Y K z) := by
  intro y hy
  have hO : oddCoreOf K ⊓ sec19Y K z ≤ oddCoreOf (sec19Y K z) := by
    refine S1916.le_oddCoreOf_of_odd inf_le_right (fun x hx => ?_) ?_
    · rw [Subgroup.mem_normalizer_iff]
      intro w
      have hxO : x ∈ Subgroup.normalizer (oddCoreOf K : Set G) := hx.2.2.1
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hxO w).mp h1,
          (sec19Y K z).mul_mem ((sec19Y K z).mul_mem hx h2) ((sec19Y K z).inv_mem hx)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp hxO w).mpr h1, ?_⟩
        have e : w = x⁻¹ * (x * w * x⁻¹) * x := by group
        rw [e]
        exact (sec19Y K z).mul_mem ((sec19Y K z).mul_mem ((sec19Y K z).inv_mem hx) h2) hx
    · exact (oddCoreOf_odd_natCard K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  refine hO ⟨?_, ?_⟩
  · have h := hy.2.2.2 k hk
    have e : ⁅k, y⁆ = ⁅y, k⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (oddCoreOf K).inv_mem h
  · rw [commutatorElement_def]
    exact (sec19Y K z).mul_mem ((Subgroup.mem_normalizer_iff.mp hkN y).mp hy)
      ((sec19Y K z).inv_mem hy)

theorem fieldPart_ne_one (hd : Sec19DataT p f K z S W L t V) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K)
    {p' e' : ℕ} [Fact p'.Prime] (hp'2 : p' ≠ 2)
    (eY : ↥(sec19Y K z) ⧸ classicalInvolutionOddCore ↥(sec19Y K z) ≃* SL(2, GaloisField p' e'))
    (hFcard : Nat.card (GaloisField p' e') = p' ^ e')
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p' e')))
    (h3 : 3 < Nat.card (GaloisField p' e'))
    (haN : a ∈ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G)) :
    (normalizerToPGammaL2Mod eY hFcard hF h3 ⟨a, haN⟩).right ≠ 1 := by
  have hd0 := hd.toSec19Data
  have hNY := S1916.sd_centralizer_le_normalizer_Y hd0
  have hzZ := S1916.isUniqueInvolution_W_inf hd
  have ef := S1911.etaYForm p f G K z S W L t V hd
  have hcomm := S1911.comm_of_mem hd0
  obtain ⟨u, hU, h8, hzu, hform⟩ := exists_gen_conj_eq hd haS ha2 haX
  have huKW : u ∈ K ⊓ W := hU ▸ Subgroup.mem_zpowers u
  have hzu' : Commute z u := hcomm z hzZ.mem.1 u huKW.2
  have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp (hd0.hSz haS)
  obtain ⟨a', ha'S, ha't, hΨ, ε, hε, ha'u⟩ : ∃ a' ∈ (S : Subgroup G), a' * t * a'⁻¹ = t ∧
      (∀ ha'N : a' ∈ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G),
        (normalizerToPGammaL2Mod eY hFcard hF h3 ⟨a', ha'N⟩).right =
          (normalizerToPGammaL2Mod eY hFcard hF h3 ⟨a, haN⟩).right) ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ a' * u * a'⁻¹ = z * u ^ ε := by
    obtain ⟨ε, hε, hau⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ a * u * a⁻¹ = z * u ^ ε := by
      rcases hform with h | h
      · exact ⟨1, Or.inl rfl, by rw [h, zpow_one]⟩
      · exact ⟨-1, Or.inr rfl, by rw [h, zpow_neg_one]⟩
    rcases S1911.conj_t_eq_or_of_le_normalizer hd (S19B.le_normalizer_W hd) haS with ht | ht
    · exact ⟨a, haS, ht, fun _ => rfl, ε, hε, hau⟩
    · obtain ⟨r, hrR, hrt⟩ := S1911.exists_conj_eq_mul hd
      have hrinv := S1911.conj_eq_inv_of_conj_eq_mul hd hrR hrt
      have hrN := hNY (hd0.hSz hrR.1)
      refine ⟨a * r, (S : Subgroup G).mul_mem haS hrR.1, ?_, fun h => ?_, -ε, ?_, ?_⟩
      · calc a * r * t * (a * r)⁻¹ = a * (r * t * r⁻¹) * a⁻¹ := by group
          _ = (a * t * a⁻¹) * (a * z * a⁻¹) := by rw [hrt]; group
          _ = t * z * z := by rw [ht, haz, mul_inv_cancel_right]
          _ = t := by rw [mul_assoc, hzZ.sq, mul_one]
      · have h1 : normalizerToPGammaL2Mod eY hFcard hF h3 ⟨r, hrN⟩ = 1 :=
          (Hall196.normalizerToPGammaL2Mod_eq_one_iff eY hFcard hF h3 _).mpr
            (commutator_mem_oddCoreOf_of_mem hrR.2 hrN)
        have e : (⟨a * r, h⟩ : Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G)) =
            ⟨a, haN⟩ * ⟨r, hrN⟩ := rfl
        rw [e, map_mul, h1, mul_one]
      · rcases hε with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (by norm_num)
      · have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzZ.sq
        calc a * r * u * (a * r)⁻¹ = a * (r * u * r⁻¹) * a⁻¹ := by group
          _ = (a * u * a⁻¹)⁻¹ := by rw [hrinv u huKW]; group
          _ = u ^ (-ε) * z := by rw [hau, mul_inv_rev, hzi, zpow_neg]
          _ = z * u ^ (-ε) := ((hzu'.zpow_right (-ε)).eq).symm
  intro hfield
  have ha'N := hNY (hd0.hSz ha'S)
  have ha'C : a' ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a' * t = a' * t * a'⁻¹ * a' := by group
      _ = t * a' := by rw [ha't]
  have ha'V := S1911.mem_normalizer_V_of_mem_A hd ha'S ha'C
  set m : ℤ := ((orderOf u / 2 : ℕ) : ℤ) + ε with hm
  have hkey : a' * u * a'⁻¹ = u ^ m := by
    rw [ha'u, ← hzu, ← zpow_natCast, ← zpow_add]
  have hU' : ∀ x ∈ K ⊓ W, a' * x * a'⁻¹ = x ^ m := by
    intro x hx
    rw [← hU] at hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hkey, ← zpow_mul, ← zpow_mul, mul_comm]
  have hC := conj_eq_zpow_of_conj_inf hd ha'V ha'N hU'
  obtain ⟨c₀, hc₀⟩ := ef.cyclic.exists_generator
  have hcC : (c₀ : G) ∈ W ⊓ sec19Y K z := c₀.2
  have hNo : orderOf (c₀ : G) = orderOf u := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hc₀, ef.card,
      ← S1911.card_inf_eq_card hd, ← hU, Nat.card_zpowers]
  have hc8 : 8 ≤ orderOf (c₀ : G) := hNo ▸ h8
  have hev : Even (orderOf (c₀ : G)) := by
    obtain ⟨k, hk⟩ := (S.isPGroup'.to_le (inf_le_left.trans hd.hWS) :
      IsPGroup 2 ↥(W ⊓ sec19Y K z)).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hc₀, hk] at hc8
      norm_num at hc8
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hc₀, hk]
    exact (Nat.even_pow' hk0).mpr even_two
  have hcz : (c₀ : G) ^ (orderOf (c₀ : G) / 2) = z :=
    (hzZ.unique _ (Subgroup.pow_mem _ hcC _) (Hall196.pow_half_mul_self hev)).resolve_left
      (Hall196.pow_half_ne_one (by omega))
  have hac : a' * (c₀ : G) * a'⁻¹ = z * (c₀ : G) ^ ε := by
    rw [hC _ hcC, hm, zpow_add, zpow_natCast, ← hNo, hcz]
  exact false_of_field_eq_one hd hp'2 eY hFcard hF h3 ha'N ((hΨ ha'N).trans hfield) hcC hc8 hε hac

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19L
