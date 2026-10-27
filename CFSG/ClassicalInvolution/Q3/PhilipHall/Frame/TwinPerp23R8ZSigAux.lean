module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.ClassicalInvolution.Q3.Q3SBasic

public section

open scoped MatrixGroups

open CFSG.Open

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig

section Layers

variable {G : Type*} [Group G] [Finite G]

theorem le_centralizer_of_layer {N P L A : Subgroup G} {e t₀ : G}
    (hPN : P ≤ N) (hPnorm : ∀ n ∈ N, ∀ p ∈ P, n * p * n⁻¹ ∈ P)
    (hPodd : Odd (Nat.card P))
    (hLN : L ≤ N) (hLe : ∀ x ∈ L, e * x = x * e)
    (hLnorm : ∀ g ∈ Subgroup.centralizer ({e} : Set G), ∀ x ∈ L, g * x * g⁻¹ ∈ L)
    (hPL : P ⊓ L = ⊥)
    (hAL : A ≤ L) (hA : IsElemAbelian 2 A) (hA4 : 2 ^ 2 ≤ Nat.card A)
    (hAcl : ∀ a ∈ A, a ≠ 1 → ∃ y ∈ L, a = y * t₀ * y⁻¹)
    (hCP : ∀ o ∈ P, o * t₀ = t₀ * o → o * e = e * o) :
    P ≤ Subgroup.centralizer (L : Set G) := by
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      exact hPnorm a (hLN (hAL ha)) p hp
    · intro hp
      have := hPnorm a⁻¹ (N.inv_mem (hLN (hAL ha))) _ hp
      simpa [mul_assoc] using this
  have hcop : Nat.Coprime 2 (Nat.card P) := (Nat.coprime_two_left).mpr hPodd
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
    Nat.prime_two hA hA4 hAP hcop
  have hCa : ∀ a ∈ A, a ≠ 1 → ∀ o ∈ P, o * a = a * o → o * e = e * o := by
    intro a ha ha1 o ho hoa
    obtain ⟨y, hyL, rfl⟩ := hAcl a ha ha1
    have hyN : y ∈ N := hLN hyL
    set o' := y⁻¹ * o * y with ho'
    have ho'P : o' ∈ P := by
      have := hPnorm y⁻¹ (N.inv_mem hyN) o ho
      simpa [ho', mul_assoc] using this
    have ho't : o' * t₀ = t₀ * o' := by
      have h1 : o * (y * t₀ * y⁻¹) = (y * t₀ * y⁻¹) * o := hoa
      calc o' * t₀ = y⁻¹ * (o * (y * t₀ * y⁻¹)) * y := by simp [ho']; group
        _ = y⁻¹ * ((y * t₀ * y⁻¹) * o) * y := by rw [h1]
        _ = t₀ * o' := by simp [ho']; group
    have h2 := hCP o' ho'P ho't
    have hye : y * e = e * y := (hLe y hyL).symm
    calc o * e = y * o' * y⁻¹ * e := by simp [ho']; group
      _ = y * (o' * e) * y⁻¹ := by
          have : y⁻¹ * e = e * y⁻¹ := by
            have := congrArg (fun z => y⁻¹ * z * y⁻¹) hye
            simp at this
            calc y⁻¹ * e = y⁻¹ * (e * y) * y⁻¹ := by group
              _ = y⁻¹ * (y * e) * y⁻¹ := by rw [hye]
              _ = e * y⁻¹ := by group
          calc y * o' * y⁻¹ * e = y * o' * (y⁻¹ * e) := by group
            _ = y * o' * (e * y⁻¹) := by rw [this]
            _ = y * (o' * e) * y⁻¹ := by group
      _ = y * (e * o') * y⁻¹ := by rw [h2]
      _ = e * (y * o' * y⁻¹) := by
          calc y * (e * o') * y⁻¹ = (y * e) * o' * y⁻¹ := by group
            _ = (e * y) * o' * y⁻¹ := by rw [hye]
            _ = e * (y * o' * y⁻¹) := by group
      _ = e * o := by simp [ho']; group
  have hPe : P ≤ Subgroup.centralizer ({e} : Set G) := by
    rw [← hgen]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    intro o ho
    obtain ⟨hoP, hoa⟩ := Subgroup.mem_inf.mp ho
    rw [Subgroup.mem_centralizer_singleton_iff] at hoa ⊢
    exact hCa a ha ha1 o hoP hoa
  intro p hp x hx
  have hpe : p * e = e * p := Subgroup.mem_centralizer_singleton_iff.mp (hPe hp)
  have hmem : p * x * p⁻¹ ∈ L := by
    refine hLnorm p ?_ x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr hpe
  have hcomm : p * x * p⁻¹ * x⁻¹ ∈ P := by
    have h1 : x * p⁻¹ * x⁻¹ ∈ P := hPnorm x (hLN hx) p⁻¹ (P.inv_mem hp)
    have : p * x * p⁻¹ * x⁻¹ = p * (x * p⁻¹ * x⁻¹) := by group
    rw [this]
    exact P.mul_mem hp h1
  have hcL : p * x * p⁻¹ * x⁻¹ ∈ L := L.mul_mem hmem (L.inv_mem hx)
  have : p * x * p⁻¹ * x⁻¹ ∈ P ⊓ L := ⟨hcomm, hcL⟩
  rw [hPL, Subgroup.mem_bot] at this
  have h3 : p * x * p⁻¹ = x := by
    calc p * x * p⁻¹ = (p * x * p⁻¹ * x⁻¹) * x := by group
      _ = x := by rw [this]; group
  show x * p = p * x
  calc x * p = (p * x * p⁻¹) * p := by rw [h3]
    _ = p * x := by group

theorem le_center_of_two_layers {N P E E' A A' : Subgroup G} {e e' t t' : G}
    (hPN : P ≤ N) (hPnorm : ∀ n ∈ N, ∀ p ∈ P, n * p * n⁻¹ ∈ P) (hPodd : Odd (Nat.card P))
    (hN : N = E ⊔ E')
    (hEe : ∀ x ∈ E, e * x = x * e)
    (hEnorm : ∀ g ∈ Subgroup.centralizer ({e} : Set G), ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    (hPE : P ⊓ E = ⊥) (hAE : A ≤ E) (hA : IsElemAbelian 2 A) (hA4 : 2 ^ 2 ≤ Nat.card A)
    (hAcl : ∀ a ∈ A, a ≠ 1 → ∃ y ∈ E, a = y * t * y⁻¹)
    (hCP : ∀ o ∈ P, o * t = t * o → o * e = e * o)
    (hEe' : ∀ x ∈ E', e' * x = x * e')
    (hEnorm' : ∀ g ∈ Subgroup.centralizer ({e'} : Set G), ∀ x ∈ E', g * x * g⁻¹ ∈ E')
    (hPE' : P ⊓ E' = ⊥) (hAE' : A' ≤ E') (hA' : IsElemAbelian 2 A') (hA4' : 2 ^ 2 ≤ Nat.card A')
    (hAcl' : ∀ a ∈ A', a ≠ 1 → ∃ y ∈ E', a = y * t' * y⁻¹)
    (hCP' : ∀ o ∈ P, o * t' = t' * o → o * e' = e' * o) :
    ∀ p ∈ P, ∀ y ∈ N, p * y = y * p := by
  have h1 : P ≤ Subgroup.centralizer (E : Set G) :=
    le_centralizer_of_layer hPN hPnorm hPodd (hN ▸ le_sup_left) hEe hEnorm hPE hAE hA hA4 hAcl hCP
  have h2 : P ≤ Subgroup.centralizer (E' : Set G) :=
    le_centralizer_of_layer hPN hPnorm hPodd (hN ▸ le_sup_right) hEe' hEnorm' hPE' hAE' hA' hA4' hAcl'
      hCP'
  intro p hp y hy
  have hE : E ≤ Subgroup.centralizer ({p} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (h1 hp) x hx)
  have hE' : E' ≤ Subgroup.centralizer ({p} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (h2 hp) x hx)
  have hNle : N ≤ Subgroup.centralizer ({p} : Set G) := hN ▸ sup_le hE hE'
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hNle hy)).symm

end Layers

section CentralizerOfOdd

variable {G : Type*} [Group G]

theorem comm_of_mem_two_normalized {N P Q : Subgroup G} {t e : G}
    (hPnorm : ∀ n ∈ N, ∀ p ∈ P, n * p * n⁻¹ ∈ P) (hPodd : Odd (Nat.card P)) (hQ2 : IsPGroup 2 Q)
    (heN : e ∈ N) (heQ : e ∈ Q)
    (hQnorm : ∀ c ∈ Subgroup.centralizer ({t} : Set G), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
    {o : G} (hoP : o ∈ P) (hot : o * t = t * o) : o * e = e * o := by
  have hoC : o ∈ Subgroup.centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hot
  set k : G := o * e * o⁻¹ * e⁻¹ with hk
  have hkP : k ∈ P := by
    have h1 : e * o⁻¹ * e⁻¹ ∈ P := hPnorm e heN o⁻¹ (P.inv_mem hoP)
    have : k = o * (e * o⁻¹ * e⁻¹) := by rw [hk]; group
    rw [this]
    exact P.mul_mem hoP h1
  have hkQ : k ∈ Q := Q.mul_mem (hQnorm o hoC e heQ) (Q.inv_mem heQ)
  have hk1 : k = 1 := by
    obtain ⟨m, hm⟩ := hQ2 ⟨k, hkQ⟩
    have hk2 : k ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hord : orderOf k ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hk2
    have hord' : orderOf k ∣ Nat.card P := by
      have := orderOf_dvd_natCard (⟨k, hkP⟩ : P)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ m) (Nat.card P) :=
      Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hPodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord hord')
  calc o * e = (o * e * o⁻¹ * e⁻¹) * e * o := by group
    _ = e * o := by rw [← hk, hk1, one_mul]

end CentralizerOfOdd

section Lift

variable {G : Type*} [Group G] [Finite G]

theorem comm_of_central_mod_odd {O : Subgroup G} (hOc : O ≤ Subgroup.center G)
    (hOodd : Odd (Nat.card O)) {a : G} (ha : a * a = 1)
    (h : ∀ y : G, a * y * a⁻¹ * y⁻¹ ∈ O) : ∀ y : G, a * y = y * a := by
  intro y
  set c : G := a * y * a⁻¹ * y⁻¹ with hc
  have hcO : c ∈ O := h y
  have hcc : ∀ z : G, z * c = c * z := fun z => (Subgroup.mem_center_iff.mp (hOc hcO) z)
  have h1 : a * y * a⁻¹ = c * y := by rw [hc]; group
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hac : a * c * a⁻¹ = c := by
    calc a * c * a⁻¹ = (c * a) * a⁻¹ := by rw [← hcc a]
      _ = c := by group
  have h2 : y = c * c * y := by
    calc y = a * (a * y * a⁻¹) * a⁻¹ := by
          calc y = (a * a) * y * (a⁻¹ * a⁻¹) := by rw [ha, ha', ha]; group
            _ = a * (a * y * a⁻¹) * a⁻¹ := by group
      _ = a * (c * y) * a⁻¹ := by rw [h1]
      _ = (a * c * a⁻¹) * (a * y * a⁻¹) := by group
      _ = c * (c * y) := by rw [hac, h1]
      _ = c * c * y := by group
  have hc2 : c * c = 1 := by
    calc c * c = (c * c * y) * y⁻¹ := by group
      _ = y * y⁻¹ := by rw [← h2]
      _ = 1 := by group
  have hc1 : c = 1 := by
    have hord : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc2)
    have hord' : orderOf c ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨c, hcO⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime 2 (Nat.card O) := Nat.coprime_two_left.mpr hOodd
    have : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hord hord'
    exact orderOf_eq_one_iff.mp this
  calc a * y = (a * y * a⁻¹ * y⁻¹) * y * a := by group
    _ = y * a := by rw [← hc, hc1, one_mul]

theorem exists_pow_three_lift {H : Type*} [Group H] (φ : G →* H) (y : G) {k : ℕ}
    (hk : φ y ^ 3 ^ k = 1) : ∃ x : G, φ x = φ y ∧ ∃ m : ℕ, x ^ 3 ^ m = 1 := by
  have hy0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨a, r, hr3, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd hy0 3 (by norm_num)
  have hcop : Nat.Coprime r (3 ^ k) := by
    apply Nat.Coprime.pow_right
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hr3).symm
  obtain ⟨u, v, huv⟩ : IsCoprime (r : ℤ) ((3 ^ k : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  refine ⟨y ^ (u * (r : ℤ)), ?_, a, ?_⟩
  · rw [map_zpow]
    have h1 : u * (r : ℤ) = 1 - v * ((3 ^ k : ℕ) : ℤ) := by linarith
    rw [h1, zpow_sub, zpow_one, zpow_mul']
    have h3 : (φ y) ^ (((3 ^ k : ℕ) : ℤ)) = 1 := by
      rw [zpow_natCast]; exact hk
    rw [h3, one_zpow, inv_one, mul_one]
  · rw [← zpow_natCast, ← zpow_mul]
    have h4 : u * (r : ℤ) * ((3 ^ a : ℕ) : ℤ) = ((orderOf y : ℕ) : ℤ) * u := by
      rw [hor]; push_cast; ring
    rw [h4, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

theorem exists_lift_three {H : Type*} [Group H] (φ : G →* H) (hker : φ.ker ≤ Subgroup.center G)
    {t : G} (ht : t * t = 1) {y : G} {k : ℕ} (hk : φ y ^ 3 ^ k = 1)
    (hyt : φ y * φ t = φ t * φ y) :
    ∃ x : G, φ x = φ y ∧ (∃ m : ℕ, x ^ 3 ^ m = 1) ∧ x * t = t * x := by
  obtain ⟨x, hxy, m, hxm⟩ := exists_pow_three_lift φ y hk
  refine ⟨x, hxy, ⟨m, hxm⟩, ?_⟩
  set d : G := x * t * x⁻¹ * t⁻¹ with hd
  have hdker : d ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hd]
    simp only [map_mul, map_inv, hxy]
    calc φ y * φ t * (φ y)⁻¹ * (φ t)⁻¹ = (φ t * φ y) * (φ y)⁻¹ * (φ t)⁻¹ := by rw [hyt]
      _ = 1 := by group
  have hdc : ∀ z : G, z * d = d * z := fun z => Subgroup.mem_center_iff.mp (hker hdker) z
  have hxt : x * t * x⁻¹ = d * t := by rw [hd]; group
  have hd2 : d * d = 1 := by
    have h1 : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
      calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [ht]; group
    rw [hxt] at h1
    calc d * d = (d * t) * (d * t) := by
          calc d * d = d * d * (t * t) := by rw [ht, mul_one]
            _ = d * (d * t) * t := by group
            _ = d * (t * d) * t := by rw [hdc t]
            _ = (d * t) * (d * t) := by group
      _ = 1 := h1
  have hpow : ∀ j : ℕ, x ^ j * t * (x ^ j)⁻¹ = d ^ j * t := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc x ^ (j + 1) * t * (x ^ (j + 1))⁻¹ = x * (x ^ j * t * (x ^ j)⁻¹) * x⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = x * (d ^ j * t) * x⁻¹ := by rw [ih]
        _ = d ^ j * (x * t * x⁻¹) := by
            have : x * d ^ j = d ^ j * x := (Commute.pow_right (hdc x) j).eq.symm ▸ rfl
            calc x * (d ^ j * t) * x⁻¹ = (x * d ^ j) * t * x⁻¹ := by group
              _ = (d ^ j * x) * t * x⁻¹ := by rw [this]
              _ = d ^ j * (x * t * x⁻¹) := by group
        _ = d ^ (j + 1) * t := by rw [hxt, pow_succ]; group
  have hd3 : d ^ 3 ^ m = 1 := by
    have := hpow (3 ^ m)
    rw [hxm, inv_one, mul_one, one_mul] at this
    have h2 : d ^ 3 ^ m * t = 1 * t := by rw [← this, one_mul]
    exact mul_right_cancel h2
  have hd1 : d = 1 := by
    have hord : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hd2)
    have hord' : orderOf d ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hd3
    have hcop : Nat.Coprime 2 (3 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord hord')
  rw [hd1] at hd
  calc x * t = (x * t * x⁻¹ * t⁻¹) * t * x := by group
    _ = t * x := by rw [← hd, one_mul]

theorem sl2_cent_card_le : ∀ g : SL(2, ZMod 3), g ^ 3 = 1 → g ≠ 1 →
    (Finset.univ.filter fun h : SL(2, ZMod 3) => g * h = h * g).card ≤ 6 := by
  decide +kernel

end Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig

namespace CFSG.ClassicalInvolution.Q3

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {z : Y}

theorem IsClassicalMember3.exists_three_elt_moving (h : IsClassicalMember3 L z) {Q : Subgroup Y}
    (hQL : Q ≤ L) (hQ2 : IsPGroup 2 Q) (hQ8 : 8 ≤ Nat.card Q) :
    ∃ ω ∈ L, (∃ k : ℕ, ω ^ 3 ^ k = 1) ∧ ∃ q ∈ Q, ω * q ≠ q * ω := by
  obtain ⟨ψ, hψs, hψ⟩ := h.exists_hom
  obtain ⟨g, hg⟩ := sl2Three_exists_orderOf_three
  have hg3 : g ^ 3 = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact this
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg
    norm_num at hg
  obtain ⟨y, hy⟩ := hψs g
  obtain ⟨x, hxy, m, hxm⟩ :=
    PhilipHall.Frame.TwinPerp23.ZSig.exists_pow_three_lift ψ y (k := 1) (by rw [hy]; simpa using hg3)
  refine ⟨(x : Y), x.2, ⟨m, by simpa using congrArg Subtype.val hxm⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  set S : Finset SL(2, ZMod 3) := Finset.univ.filter fun h : SL(2, ZMod 3) => g * h = h * g with hS
  have hS6 : S.card ≤ 6 := PhilipHall.Frame.TwinPerp23.ZSig.sl2_cent_card_le g hg3 hg1
  let φ : ↥Q → ↥S := fun q => ⟨ψ ⟨q, hQL q.2⟩, by
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : x * (⟨q, hQL q.2⟩ : ↥L) = (⟨q, hQL q.2⟩ : ↥L) * x :=
      Subtype.ext (hcon q q.2)
    have h2 := congrArg ψ h1
    rw [map_mul, map_mul, hxy, hy] at h2
    exact h2⟩
  have hφ : Function.Injective φ := by
    intro q₁ q₂ h12
    have h1 : ψ ⟨q₁, hQL q₁.2⟩ = ψ ⟨q₂, hQL q₂.2⟩ := congrArg Subtype.val h12
    have h2 : (⟨q₁, hQL q₁.2⟩ : ↥L)⁻¹ * ⟨q₂, hQL q₂.2⟩ ∈ classicalInvolutionOddCore ↥L := by
      rw [← hψ, map_mul, map_inv, h1]; group
    have hodd : Odd (orderOf ((⟨q₁, hQL q₁.2⟩ : ↥L)⁻¹ * ⟨q₂, hQL q₂.2⟩)) :=
      h.odd_orderOf_of_mem_oddCore h2
    have h3 : orderOf ((q₁ : Y)⁻¹ * (q₂ : Y)) = orderOf ((⟨q₁, hQL q₁.2⟩ : ↥L)⁻¹ * ⟨q₂, hQL q₂.2⟩) := by
      rw [← Subgroup.orderOf_coe]; rfl
    obtain ⟨k, hk⟩ := hQ2 (q₁⁻¹ * q₂)
    have hk' : ((q₁ : Y)⁻¹ * (q₂ : Y)) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hord : orderOf ((q₁ : Y)⁻¹ * (q₂ : Y)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf ((q₁ : Y)⁻¹ * (q₂ : Y))) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (h3 ▸ hodd))
    have h4 : orderOf ((q₁ : Y)⁻¹ * (q₂ : Y)) = 1 := Nat.Coprime.eq_one_of_dvd hcop hord
    have h5 : (q₁ : Y)⁻¹ * (q₂ : Y) = 1 := orderOf_eq_one_iff.mp h4
    exact Subtype.ext (inv_mul_eq_one.mp h5)
  have h6 : Nat.card Q ≤ Nat.card ↥S := Nat.card_le_card_of_injective φ hφ
  have h7 : Nat.card ↥S = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  omega

end CFSG.ClassicalInvolution.Q3
