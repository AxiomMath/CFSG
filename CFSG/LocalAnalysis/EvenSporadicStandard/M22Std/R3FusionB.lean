module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Basic

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem card_centralizer_le_sixteen {L1 F : Subgroup G} {z y : G}
    (hL1c : ∀ a ∈ L1, ∀ b ∈ L1, a * b = b * a) (hL1s : ∀ a ∈ L1, a * a = 1)
    (hz2 : z * z = 1) (hzN : ∀ a, a ∈ L1 ↔ z * a * z ∈ L1) (hyz : y * z = z * y)
    (hFz : ∀ x ∈ L1, z * x = x * z → x ∈ F)
    (hW : Nat.card ↥(centralizer ({y} : Set G) ⊓ F) = 4) :
    Nat.card ↥(centralizer ({y} : Set G) ⊓ L1) ≤ 16 := by
  set U : Subgroup G := centralizer ({y} : Set G) ⊓ L1 with hUdef
  set W : Subgroup G := centralizer ({y} : Set G) ⊓ F with hWdef
  have hUy : ∀ u ∈ U, y * u = u * y := fun u hu =>
    (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hu).1).symm
  have hUL : ∀ u ∈ U, u ∈ L1 := fun u hu => (Subgroup.mem_inf.1 hu).2
  have hc : ∀ u ∈ U, z * u * z * u ∈ W := by
    intro u hu
    have huL := hUL u hu
    have hu'L : z * u * z ∈ L1 := (hzN u).1 huL
    have hcL : z * u * z * u ∈ L1 := L1.mul_mem hu'L huL
    have hcz : z * (z * u * z * u) = (z * u * z * u) * z := by
      have h1 : z * u * z * u = u * (z * u * z) := hL1c _ hu'L u huL
      calc z * (z * u * z * u) = (z * z) * u * z * u := by group
        _ = u * z * u := by rw [hz2, one_mul]
        _ = u * (z * u * z) * z := by
          rw [show u * (z * u * z) * z = u * z * u * (z * z) by group, hz2, mul_one]
        _ = (z * u * z * u) * z := by rw [h1]
    have hcF : z * u * z * u ∈ F := hFz _ hcL hcz
    refine Subgroup.mem_inf.2 ⟨?_, hcF⟩
    rw [mem_centralizer_singleton_iff]
    have hyu := hUy u hu
    calc z * u * z * u * y = z * u * z * (u * y) := by group
      _ = z * u * z * (y * u) := by rw [← hyu]
      _ = z * u * (z * y) * u := by group
      _ = z * u * (y * z) * u := by rw [← hyz]
      _ = z * (u * y) * z * u := by group
      _ = z * (y * u) * z * u := by rw [← hyu]
      _ = (z * y) * u * z * u := by group
      _ = (y * z) * u * z * u := by rw [← hyz]
      _ = y * (z * u * z * u) := by group
  let φ : ↥U →* ↥W :=
    { toFun := fun u => ⟨z * (u : G) * z * u, hc u u.2⟩
      map_one' := by
        apply Subtype.ext
        show z * (1 : G) * z * 1 = 1
        rw [mul_one, mul_one, hz2]
      map_mul' := by
        intro u v
        apply Subtype.ext
        have hu' : z * (u : G) * z ∈ L1 := (hzN u).1 (hUL u u.2)
        have hv' : z * (v : G) * z ∈ L1 := (hzN v).1 (hUL v v.2)
        show z * ((u : G) * v) * z * ((u : G) * v) =
          z * (u : G) * z * (u : G) * (z * (v : G) * z * (v : G))
        have h1 : (u : G) * (z * (v : G) * z) = z * (v : G) * z * u :=
          hL1c _ (hUL u u.2) _ hv'
        calc z * ((u : G) * v) * z * ((u : G) * v)
            = z * u * (z * z) * v * z * (u * v) := by rw [hz2]; group
          _ = z * u * z * (z * v * z) * (u * v) := by group
          _ = z * u * z * ((z * v * z) * u) * v := by group
          _ = z * u * z * (u * (z * v * z)) * v := by rw [← h1]
          _ = z * (u : G) * z * (u : G) * (z * (v : G) * z * (v : G)) := by group }
  have hker : φ.ker ≤ (W.subgroupOf U) := by
    intro u hu
    have hu1 : z * (u : G) * z * u = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hu)
    have huL := hUL u u.2
    have hcomm : z * (u : G) = (u : G) * z := by
      have h3 : (u : G)⁻¹ = u := inv_eq_of_mul_eq_one_right (hL1s u huL)
      have h2 : z * (u : G) * z = (u : G)⁻¹ := eq_inv_of_mul_eq_one_left hu1
      rw [h3] at h2
      calc z * (u : G) = z * u * z * z := by rw [mul_assoc (z * u) z z, hz2, mul_one]
        _ = (u : G) * z := by rw [h2]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 u.2).1, hFz u huL hcomm⟩
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.ker ≤ Nat.card W := by
    calc Nat.card φ.ker ≤ Nat.card (W.subgroupOf U) := Subgroup.card_le_of_le hker
      _ ≤ Nat.card W := Nat.card_le_card_of_injective
        (fun x : ↥(W.subgroupOf U) => (⟨((x : ↥U) : G), Subgroup.mem_subgroupOf.1 x.2⟩ : ↥W))
        (fun a b h => by
          have := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext this))
  have h3 : Nat.card φ.range ≤ Nat.card W := Nat.card_le_card_of_injective
    (fun x : ↥φ.range => (x : ↥W)) Subtype.val_injective
  rw [hW] at h2 h3
  rw [← h1]
  calc Nat.card φ.ker * Nat.card φ.range ≤ 4 * 4 := Nat.mul_le_mul h2 h3
    _ = 16 := by norm_num

omit [Finite G] in
theorem card_centralizer_eq_of_conj {z y c : G} (h : c * z * c⁻¹ = y) :
    Nat.card (centralizer ({y} : Set G)) = Nat.card (centralizer ({z} : Set G)) := by
  subst h
  refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
    (fun x => (⟨c * (x : G) * c⁻¹, ?_⟩ : ↥(centralizer ({c * z * c⁻¹} : Set G)))) ⟨?_, ?_⟩))
  · rw [mem_centralizer_singleton_iff]
    have hx := mem_centralizer_singleton_iff.1 x.2
    calc c * (x : G) * c⁻¹ * (c * z * c⁻¹) = c * ((x : G) * z) * c⁻¹ := by group
      _ = c * (z * (x : G)) * c⁻¹ := by rw [hx]
      _ = c * z * c⁻¹ * (c * (x : G) * c⁻¹) := by group
  · intro a b hab
    have h1 := congrArg Subtype.val hab
    have h4 : (a : G) = b := by simpa using h1
    exact Subtype.ext h4
  · intro w
    refine ⟨⟨c⁻¹ * (w : G) * c, ?_⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      have hw := mem_centralizer_singleton_iff.1 w.2
      calc c⁻¹ * (w : G) * c * z = c⁻¹ * ((w : G) * (c * z * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * z * c⁻¹) * (w : G)) * c := by rw [hw]
        _ = z * (c⁻¹ * (w : G) * c) := by group
    · apply Subtype.ext
      show c * (c⁻¹ * (w : G) * c) * c⁻¹ = w
      group

theorem exists_sylow_R {L1 F Q : Subgroup G} {z y : G}
    (hFz : ∀ x ∈ L1, z * x = x * z → x ∈ F)
    (hU16 : Nat.card ↥(centralizer ({y} : Set G) ⊓ L1) = 16)
    (hW : Nat.card ↥(centralizer ({y} : Set G) ⊓ F) = 4)
    (hQN : Q ≤ normalizer (L1 : Set G)) (hQy : Q ≤ centralizer ({y} : Set G))
    (hQz : Q ≤ centralizer ({z} : Set G)) (hQp : IsPGroup 2 ↥Q) (hQcard : 128 ≤ Nat.card Q)
    (hCG : Nat.card (centralizer ({y} : Set G)) = 1774080) :
    Nat.card ↥((centralizer ({y} : Set G) ⊓ L1) ⊔ Q) = 512 ∧
      IsPGroup 2 ↥((centralizer ({y} : Set G) ⊓ L1) ⊔ Q) ∧
      ¬ 2 ∣ ((centralizer ({y} : Set G) ⊓ L1) ⊔ Q).relIndex (centralizer ({y} : Set G)) ∧
      (centralizer ({y} : Set G) ⊓ L1) ⊔ Q ≤
        normalizer ((centralizer ({y} : Set G) ⊓ L1 : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup G := centralizer ({y} : Set G) ⊓ L1 with hUdef
  have hUy : ∀ u ∈ U, y * u = u * y := fun u hu =>
    (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hu).1).symm
  have hUL : ∀ u ∈ U, u ∈ L1 := fun u hu => (Subgroup.mem_inf.1 hu).2
  have hUp : IsPGroup 2 ↥U := IsPGroup.of_card (n := 4) (by rw [hU16]; norm_num)
  have hQU : ∀ q ∈ Q, ∀ x, x ∈ U ↔ q * x * q⁻¹ ∈ U := by
    intro q hq x
    have hqy : y * q = q * y := (mem_centralizer_singleton_iff.1 (hQy hq)).symm
    have hqN := (Subgroup.mem_normalizer_iff.1 (hQN hq) x)
    constructor
    · intro hx
      refine Subgroup.mem_inf.2 ⟨?_, hqN.1 (hUL x hx)⟩
      rw [mem_centralizer_singleton_iff]
      have hxy := hUy x hx
      calc q * x * q⁻¹ * y = q * x * (q⁻¹ * y) := by group
        _ = q * x * (y * q⁻¹) := by
          rw [show q⁻¹ * y = y * q⁻¹ by
            rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hqy]; group]
        _ = q * (x * y) * q⁻¹ := by group
        _ = q * (y * x) * q⁻¹ := by rw [← hxy]
        _ = y * (q * x * q⁻¹) := by
          calc q * (y * x) * q⁻¹ = (q * y) * x * q⁻¹ := by group
            _ = (y * q) * x * q⁻¹ := by rw [hqy]
            _ = y * (q * x * q⁻¹) := by group
    · intro hx
      refine Subgroup.mem_inf.2 ⟨?_, hqN.2 (hUL _ hx)⟩
      rw [mem_centralizer_singleton_iff]
      have hxy := hUy _ hx
      have : y * x = x * y := by
        have h1 : y * (q * x * q⁻¹) = q * x * q⁻¹ * y := hxy
        calc y * x = q⁻¹ * (q * y) * x := by group
          _ = q⁻¹ * (y * q) * x := by rw [hqy]
          _ = q⁻¹ * (y * (q * x * q⁻¹)) * q := by group
          _ = q⁻¹ * (q * x * q⁻¹ * y) * q := by rw [h1]
          _ = x * (q⁻¹ * y * q) := by group
          _ = x * y := by
            rw [show q⁻¹ * y * q = y by
              calc q⁻¹ * y * q = q⁻¹ * (y * q) := by group
                _ = q⁻¹ * (q * y) := by rw [hqy]
                _ = y := by group]
      exact this.symm
  have hUQ : Q ≤ normalizer (U : Set G) := fun q hq =>
    Subgroup.mem_normalizer_iff.2 (hQU q hq)
  have hcard := card_sup_mul_card_inf_of_le_normalizer hUQ
  have hinf : Nat.card ↥(U ⊓ Q) ≤ 4 := by
    rw [← hW]
    refine Subgroup.card_le_of_le fun x hx => ?_
    obtain ⟨hxU, hxQ⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxU).1, hFz x (hUL x hxU) ?_⟩
    exact (mem_centralizer_singleton_iff.1 (hQz hxQ)).symm
  have hRp : IsPGroup 2 ↥(U ⊔ Q) := by
    rw [sup_comm]
    exact hQp.to_sup_of_normal_right' hUp hUQ
  have hRC : U ⊔ Q ≤ centralizer ({y} : Set G) := sup_le inf_le_left hQy
  have hge : 512 ≤ Nat.card ↥(U ⊔ Q) := by
    rw [hU16] at hcard
    have h1 : 16 * 128 ≤ 4 * Nat.card ↥(U ⊔ Q) := by
      calc 16 * 128 ≤ 16 * Nat.card Q := Nat.mul_le_mul_left 16 hQcard
        _ = Nat.card ↥(U ⊔ Q) * Nat.card ↥(U ⊓ Q) := hcard.symm
        _ ≤ Nat.card ↥(U ⊔ Q) * 4 := Nat.mul_le_mul_left _ hinf
        _ = 4 * Nat.card ↥(U ⊔ Q) := by ring
    omega
  obtain ⟨n, hn⟩ := hRp.exists_card_eq
  have hdvd : Nat.card ↥(U ⊔ Q) ∣ 1774080 := by
    rw [← hCG]
    exact Subgroup.card_dvd_of_le hRC
  have hn9 : n = 9 := by
    have h1 : 9 ≤ n := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ n ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : n ≤ 9 := by
      by_contra hlt
      push Not at hlt
      have h3 : 2 ^ 10 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      rw [hn] at hdvd
      have := dvd_trans h3 hdvd
      norm_num at this
    omega
  have hcardR : Nat.card ↥(U ⊔ Q) = 512 := by rw [hn, hn9]; norm_num
  refine ⟨hcardR, hRp, ?_, sup_le Subgroup.le_normalizer hUQ⟩
  have h := Subgroup.relIndex_mul_card (U ⊔ Q) (centralizer ({y} : Set G))
  rw [inf_of_le_left hRC, hcardR, hCG] at h
  intro h2
  obtain ⟨m, hm⟩ := h2
  rw [hm] at h
  omega

end CFSG.EvenSporadicStandard.M22Std
