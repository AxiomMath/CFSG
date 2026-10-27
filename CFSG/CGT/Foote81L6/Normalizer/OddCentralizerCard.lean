module

public import CFSG.CGT.Foote81L6.Normalizer.Lemma10

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.Quasithin

variable {V X : Type*} [CommGroup V] [Group X]

private def permOn (ρ : X →* MulAut V) (K : Subgroup X) (U : Subgroup V)
    (hU : ∀ k ∈ K, ∀ u ∈ U, ρ k u ∈ U) : K →* Equiv.Perm U where
  toFun k :=
    { toFun := fun u => ⟨ρ k u, hU k k.2 u u.2⟩
      invFun := fun u => ⟨ρ (k : X)⁻¹ u, hU _ (K.inv_mem k.2) u u.2⟩
      left_inv := fun u => Subtype.ext (by
        show ρ (k : X)⁻¹ (ρ k u) = u
        rw [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply])
      right_inv := fun u => Subtype.ext (by
        show ρ k (ρ (k : X)⁻¹ u) = u
        rw [map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]) }
  map_one' := by
    ext u
    show ρ ((1 : K) : X) u = u
    rw [OneMemClass.coe_one, map_one, MulAut.one_apply]
  map_mul' k l := by
    ext u
    show ρ ((k * l : K) : X) u = ρ k (ρ l u)
    rw [Subgroup.coe_mul, map_mul, MulAut.mul_apply]

theorem card_oddCentralizer_eq [Finite V] [Finite X] (hV : ∀ v : V, v * v = 1)
    {ρ : X →* MulAut V} (hρ : Function.Injective ρ) {d₀ d₁ : X} {b₀ b₁ : V}
    (hd₀ : IsTransvectionWith (ρ d₀) b₀) (hd₀1 : ρ d₀ ≠ 1)
    (hd₁ : IsTransvectionWith (ρ d₁) b₁) (hd₁1 : ρ d₁ ≠ 1) (hb : b₀ ≠ b₁)
    (hcomm : d₀ * d₁ = d₁ * d₀)
    (hW : Nat.card ↥(fixV (Subgroup.zpowers (ρ d₀)) ⊓ fixV (Subgroup.zpowers (ρ d₁))) ≤ 16) :
    Nat.card ↥(pPrimeCore 2 X ⊓ Subgroup.centralizer ({d₀} : Set X) ⊓
        Subgroup.centralizer ({d₁} : Set X)) = 1 ∨
      Nat.card ↥(pPrimeCore 2 X ⊓ Subgroup.centralizer ({d₀} : Set X) ⊓
        Subgroup.centralizer ({d₁} : Set X)) = 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := pPrimeCore 2 X ⊓ Subgroup.centralizer ({d₀} : Set X) ⊓
    Subgroup.centralizer ({d₁} : Set X) with hK
  have hKmem : ∀ k ∈ K, k ∈ pPrimeCore 2 X ∧ k * d₀ = d₀ * k ∧ k * d₁ = d₁ * k := fun k hk =>
    mem_oddCentralizer.mp hk
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
  have hKodd : Odd (Nat.card K) :=
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
      (Subgroup.card_dvd_of_le (fun k hk => (hKmem k hk).1))
  set Y : Subgroup (MulAut V) := K.map ρ with hYdef
  have hYodd : Odd (Nat.card Y) := by
    rw [hYdef, Subgroup.card_map_of_injective hρ]; exact hKodd
  have hcρ : ∀ k ∈ K, ρ k * ρ d₀ = ρ d₀ * ρ k ∧ ρ k * ρ d₁ = ρ d₁ * ρ k := fun k hk => by
    obtain ⟨-, h0, h1⟩ := hKmem k hk
    exact ⟨by rw [← map_mul, ← map_mul, h0], by rw [← map_mul, ← map_mul, h1]⟩
  have happ : ∀ {g h : MulAut V}, g * h = h * g → ∀ v, g (h v) = h (g v) := fun hc v => by
    have := congrArg (fun f : MulAut V => f v) hc
    simpa only [MulAut.mul_apply] using this
  set W := fixV (Subgroup.zpowers (ρ d₀)) ⊓ fixV (Subgroup.zpowers (ρ d₁)) with hWdef
  have hWmem : ∀ v, v ∈ W ↔ ρ d₀ v = v ∧ ρ d₁ v = v := fun v => by
    rw [hWdef, Subgroup.mem_inf, mem_fixV_zpowers_iff_apply, mem_fixV_zpowers_iff_apply]
  have hYW : ∀ y ∈ Y, ∀ w ∈ W, y w ∈ W := by
    rintro _ ⟨k, hk, rfl⟩ w hw
    obtain ⟨h0, h1⟩ := (hWmem w).mp hw
    obtain ⟨c0, c1⟩ := hcρ k hk
    refine (hWmem _).mpr ⟨?_, ?_⟩
    · rw [← happ c0, h0]
    · rw [← happ c1, h1]
  obtain ⟨hsup, hinf⟩ := B1.coprime_decomp hV2 hYodd hYW
  set S := W ⊓ fixV Y with hSdef
  set U := commSub W Y with hUdef
  have hρc : ρ d₁ * ρ d₀ = ρ d₀ * ρ d₁ := by rw [← map_mul, ← map_mul, hcomm]
  have hb₀S : b₀ ∈ S := by
    refine Subgroup.mem_inf.mpr ⟨(hWmem _).mpr ⟨B1.tv_fix hd₀ hd₀1, B1.tv_comm_centre hd₀ hd₀1 hρc⟩,
      ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    exact B1.tv_comm_centre hd₀ hd₀1 (hcρ k hk).1
  have hb₁S : b₁ ∈ S := by
    refine Subgroup.mem_inf.mpr ⟨(hWmem _).mpr ⟨B1.tv_comm_centre hd₁ hd₁1 hρc.symm,
      B1.tv_fix hd₁ hd₁1⟩, ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    exact B1.tv_comm_centre hd₁ hd₁1 (hcρ k hk).2
  have hS4 : 4 ≤ Nat.card S := by
    have hb₀1 : b₀ ≠ 1 := hd₀.1
    have hb₁1 : b₁ ≠ 1 := hd₁.1
    have h01 : b₀ * b₁ ≠ 1 := fun h => hb (by
      rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_left (hV b₁)])
    have h02 : b₀ * b₁ ≠ b₀ := fun h => hb₁1 (mul_left_cancel (h.trans (mul_one b₀).symm))
    have h03 : b₀ * b₁ ≠ b₁ := fun h => hb₀1 (mul_right_cancel (h.trans (one_mul b₁).symm))
    have hsub : ({1, b₀, b₁, b₀ * b₁} : Set V) ⊆ (S : Set V) := by
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact S.one_mem
      · exact hb₀S
      · exact hb₁S
      · exact S.mul_mem hb₀S hb₁S
    have hcard : ({1, b₀, b₁, b₀ * b₁} : Set V).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hb₀1.symm, hb₁1.symm, h01.symm⟩),
        Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hb, h02.symm⟩),
        Set.ncard_pair h03.symm]
    have e : Nat.card ↥S = (S : Set V).ncard := Nat.card_coe_set_eq _
    rw [← hcard, e]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcardW : Nat.card W = Nat.card S * Nat.card U := by
    rw [← CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer S U
      (by rw [CommGroup.normalizer_eq_top]; exact le_top) (disjoint_iff.mpr hinf), hsup]
  have hU4 : Nat.card U ≤ 4 := by
    have hpos : 0 < Nat.card U := Nat.card_pos
    by_contra h5
    have : 4 * 5 ≤ Nat.card S * Nat.card U := Nat.mul_le_mul hS4 (by omega)
    omega
  have hUinv : ∀ k ∈ K, ∀ u ∈ U, ρ k u ∈ U := by
    intro k hk u hu
    refine B1.commSub_smul_mem (ρ k) (fun y hy => ?_) (fun m hm => hYW _ ⟨k, hk, rfl⟩ m hm) u hu
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨k * l * k⁻¹, K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk), by
      rw [map_mul, map_mul, map_inv]⟩
  have hinj : Function.Injective (permOn ρ K U hUinv) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hfixU : ∀ u ∈ U, ρ k u = u := fun u hu => by
      have := congrArg (fun σ : Equiv.Perm U => ((σ ⟨u, hu⟩ : U) : V)) hk
      simpa [permOn] using this
    obtain ⟨hkO, hk₀, hk₁⟩ := hKmem k k.2
    have hle : W ≤ fixV (Subgroup.zpowers (ρ k)) := by
      rw [← hsup]
      refine sup_le (fun v hv => mem_fixV_zpowers_iff_apply.mpr ?_)
        (fun v hv => mem_fixV_zpowers_iff_apply.mpr (hfixU v hv))
      exact (Subgroup.mem_inf.mp hv).2 _ ⟨k, k.2, rfl⟩
    have hk1 : (k : X) = 1 := eq_one_of_commute_of_fix hV hρ ⟨hd₀1, b₀, hd₀⟩ ⟨hd₁1, b₁, hd₁⟩
      (odd_orderOf_of_mem_pPrimeCore hkO) hk₀ hk₁ (fun v h0 h1 =>
        mem_fixV_zpowers_iff_apply.mp (hle ((hWmem v).mpr ⟨h0, h1⟩)))
    exact Subgroup.mem_bot.mpr (Subtype.ext hk1)
  have hdvd : Nat.card K ∣ 24 := by
    have h1 := Subgroup.card_dvd_of_injective _ hinj
    rw [Nat.card_perm] at h1
    have h24 : (4 : ℕ).factorial = 24 := by decide
    exact h1.trans (h24 ▸ Nat.factorial_dvd_factorial hU4)
  have hcop : Nat.Coprime (Nat.card K) (2 ^ 3) := Nat.Coprime.pow_right 3
    (Nat.coprime_two_right.mpr hKodd)
  have h3 : Nat.card K ∣ 3 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
  exact (Nat.dvd_prime Nat.prime_three).mp h3

theorem fix_mul_iff (hV : ∀ v : V, v * v = 1) {ρ : X →* MulAut V} {d₀ d₁ : X} {b₀ b₁ : V}
    (hd₀ : IsTransvectionWith (ρ d₀) b₀) (hd₁ : IsTransvectionWith (ρ d₁) b₁) (hd₁1 : ρ d₁ ≠ 1)
    (hb : b₀ ≠ b₁) (hcomm : d₀ * d₁ = d₁ * d₀) (v : V) :
    ρ (d₀ * d₁) v = v ↔ ρ d₀ v = v ∧ ρ d₁ v = v := by
  have hρc : ρ d₁ * ρ d₀ = ρ d₀ * ρ d₁ := by rw [← map_mul, ← map_mul, hcomm]
  have hb₁ : ρ d₀ b₁ = b₁ := B1.tv_comm_centre hd₁ hd₁1 hρc.symm
  rw [map_mul, MulAut.mul_apply]
  constructor
  · intro h
    rcases hd₁.2 v with h1 | h1
    · rw [h1] at h
      exact ⟨h, h1⟩
    · exfalso
      rw [h1, map_mul, hb₁] at h
      rcases hd₀.2 v with h0 | h0
      · rw [h0] at h
        exact hd₁.1 (mul_left_cancel (h.trans (mul_one v).symm))
      · rw [h0, mul_assoc] at h
        have h2 : b₀ * b₁ = 1 := mul_left_cancel (h.trans (mul_one v).symm)
        apply hb
        rw [eq_inv_of_mul_eq_one_left h2, inv_eq_of_mul_eq_one_left (hV b₁)]
  · rintro ⟨h0, h1⟩
    rw [h1, h0]

end CFSG.CGT.Foote81L6.Normalizer
