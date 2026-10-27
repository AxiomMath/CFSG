module

public import CFSG.HardMathSupport.Malle.Coordinator.OuterFiveCoprime
public import CFSG.HardMathSupport.Malle.Coordinator.CaseTwoEndgame

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

variable {G : Type*} [Group G]

theorem eq_one_of_pow_eq_one_of_coprime {x : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : x ^ a = 1) (hb : x ^ b = 1) : x = 1 := by
  have h := pow_gcd_eq_one.mpr ⟨ha, hb⟩
  rwa [hab.gcd_eq_one, pow_one] at h

theorem exists_pow_prime_pow_eq_one {p : ℕ} {P : Subgroup G} (hP : IsPGroup p P) {x : G}
    (hx : x ∈ P) : ∃ n : ℕ, x ^ (p ^ n) = 1 := by
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem eq_one_of_isPGroup_of_pow_eq_one {p : ℕ} {P : Subgroup G} (hP : IsPGroup p P) {x : G}
    (hx : x ∈ P) {b : ℕ} (hb : Nat.Coprime p b) (hxb : x ^ b = 1) : x = 1 := by
  obtain ⟨n, hn⟩ := exists_pow_prime_pow_eq_one hP hx
  exact eq_one_of_pow_eq_one_of_coprime (hb.pow_left n) hn hxb

theorem exists_orderOf_eq_pow_succ {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hP : IsPGroup p P)
    {x : G} (hx : x ∈ P) (hx1 : x ≠ 1) : ∃ j : ℕ, orderOf x = p ^ (j + 1) := by
  obtain ⟨n, hn⟩ := exists_pow_prime_pow_eq_one hP hx
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hn)
  rcases j with _ | j
  · exact absurd (orderOf_eq_one_iff.mp (by simpa using hj)) hx1
  · exact ⟨j, hj⟩

theorem mul_self_mem_centralizer {Z : Subgroup G} {c : G} (hc : ∀ z ∈ Z, c * z * c⁻¹ = z⁻¹) :
    c * c ∈ Subgroup.centralizer (Z : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  calc z * (c * c) = (c * z⁻¹ * c⁻¹) * (c * c) := by rw [hc z⁻¹ (Z.inv_mem hz), inv_inv]
    _ = c * (c * z * c⁻¹) * c := by rw [hc z hz]; group
    _ = c * c * z := by group

theorem mul_conj_eq_inv {Z : Subgroup G} {c g : G} (hc : c ∈ Subgroup.centralizer (Z : Set G))
    (hg : ∀ z ∈ Z, g * z * g⁻¹ = z⁻¹) : ∀ z ∈ Z, c * g * z * (c * g)⁻¹ = z⁻¹ := by
  intro z hz
  have hcz := Subgroup.mem_centralizer_iff.mp hc z⁻¹ (Z.inv_mem hz)
  calc c * g * z * (c * g)⁻¹ = c * (g * z * g⁻¹) * c⁻¹ := by group
    _ = z⁻¹ := by rw [hg z hz, ← hcz]; group

theorem mul_eq_inv_mul_of_conj {s x : G} (hs2 : s * s = 1) (h : s * x * s = x⁻¹) :
    s * x = x⁻¹ * s := by
  calc s * x = s * x * s * s := by rw [mul_assoc (s * x), hs2, mul_one]
    _ = x⁻¹ * s := by rw [h]

theorem conj_eq_inv_of_centralizer {P : Subgroup G} (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {s : G} (hsP : s ∈ Subgroup.normalizer (P : Set G)) (hs2 : s * s = 1)
    (hC : ∀ y ∈ P, s * y = y * s → y = 1) : ∀ x ∈ P, s * x * s = x⁻¹ := by
  intro x hx
  have hsx : s * x * s ∈ P := by
    have h := (Subgroup.mem_normalizer_iff.mp hsP x).mp hx
    rwa [inv_eq_of_mul_eq_one_right hs2] at h
  have hq := hC (x * (s * x * s)) (P.mul_mem hx hsx) (by
    calc s * (x * (s * x * s)) = s * x * s * x * s := by group
      _ = x * (s * x * s) * s := by rw [hab _ hsx _ hx])
  calc s * x * s = x⁻¹ * (x * (s * x * s)) := by group
    _ = x⁻¹ := by rw [hq, mul_one]

theorem exists_inverting_involution [Finite G] {K P Z : Subgroup G} [K.Normal]
    (hKidx : K.index = 5) (_hPK : P ≤ K) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hP5 : IsPGroup 5 P) (_hZP : Z ≤ P) (hZ5 : ∀ z ∈ Z, z ^ 5 = 1)
    (hΩ : ∀ y ∈ P, y ^ 5 = 1 → y ∈ Z) (hZne : ∃ z ∈ Z, z ≠ 1)
    (hCZ : K ⊓ Subgroup.centralizer (Z : Set G) ≤ P)
    {i : G} (hiP : i ∈ Subgroup.normalizer (P : Set G))
    (hiZ : ∀ z ∈ Z, (i * i) * z * (i * i)⁻¹ = z⁻¹) :
    ∃ u ∈ K ⊓ Subgroup.normalizer (P : Set G), u ≠ 1 ∧ u * u = 1 ∧ ∀ x ∈ P, u * x * u = x⁻¹ := by
  set g := i * i
  have ho0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  set k := (orderOf g).factorization 5
  set b := orderOf g / 5 ^ k
  have hbo : 5 ^ k * b = orderOf g := Nat.ordProj_mul_ordCompl_eq_self _ 5
  have hcop : Nat.Coprime 5 b := Nat.coprime_ordCompl Nat.prime_five ho0
  obtain ⟨u, hu⟩ : ∃ u, u = g ^ (5 ^ k) := ⟨_, rfl⟩
  have hub : u ^ b = 1 := by rw [hu, ← pow_mul, hbo, pow_orderOf_eq_one]
  obtain ⟨m, hm⟩ : Odd (5 ^ k) := Odd.pow (Nat.odd_iff.mpr (by norm_num))
  have huc : u = (g * g) ^ m * g := by rw [hu, hm, pow_succ, pow_mul, pow_two]
  have huZ : ∀ z ∈ Z, u * z * u⁻¹ = z⁻¹ := by
    rw [huc]
    exact mul_conj_eq_inv (Subgroup.pow_mem _ (mul_self_mem_centralizer hiZ) m) hiZ
  have huK : u ∈ K := by
    have h5 : u ^ 5 ∈ K := by
      have h := K.pow_index_mem u
      rwa [hKidx] at h
    exact mem_of_pow_mem_of_coprime hcop h5 (by rw [hub]; exact K.one_mem)
  have huN : u ∈ Subgroup.normalizer (P : Set G) := by
    rw [hu]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ hiP hiP) _
  have huu : u * u = 1 := by
    have hP : u * u ∈ P :=
      hCZ (Subgroup.mem_inf.mpr ⟨K.mul_mem huK huK, mul_self_mem_centralizer huZ⟩)
    refine eq_one_of_isPGroup_of_pow_eq_one hP5 hP hcop ?_
    rw [← pow_two, ← pow_mul, mul_comm 2 b, pow_mul, hub, one_pow]
  have hu1 : u ≠ 1 := by
    obtain ⟨z, hz, hz1⟩ := hZne
    intro h
    have h0 := huZ z hz
    rw [h, one_mul, inv_one, mul_one] at h0
    refine hz1 (eq_one_of_pow_eq_one_of_coprime (by norm_num : Nat.Coprime 5 2) (hZ5 z hz) ?_)
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr h0
  have hC : ∀ y ∈ P, u * y = y * u → y = 1 := by
    intro y hy hyu
    by_contra hy1
    obtain ⟨j, hj⟩ := exists_orderOf_eq_pow_succ Nat.prime_five hP5 hy hy1
    have hw1 : y ^ (5 ^ j) ≠ 1 := by
      refine pow_ne_one_of_lt_orderOf (by positivity) ?_
      rw [hj]
      exact pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self j)
    have hwZ : y ^ (5 ^ j) ∈ Z := by
      refine hΩ _ (P.pow_mem hy _) ?_
      rw [← pow_mul, ← pow_succ, ← hj, pow_orderOf_eq_one]
    apply hw1
    refine eq_one_of_isPGroup_of_pow_eq_one hP5 (P.pow_mem hy _)
      (by norm_num : Nat.Coprime 5 2) ?_
    have h := huZ _ hwZ
    rw [(Commute.pow_right hyu (5 ^ j)).eq, mul_inv_cancel_right] at h
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr h
  exact ⟨u, Subgroup.mem_inf.mpr ⟨huK, huN⟩, hu1, huu, conj_eq_inv_of_centralizer hab huN huu hC⟩

theorem isolated_of_inverting_involution [Finite G] {K M P Z : Subgroup G}
    (hPK : P ≤ K) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP5 : IsPGroup 5 P)
    (hPcard : Nat.card P = 625) (hZP : Z ≤ P) (_hΩ : ∀ y ∈ P, y ^ 5 = 1 → y ∈ Z)
    (hCZ : K ⊓ Subgroup.centralizer (Z : Set G) ≤ P)
    (hNcard : Nat.card (K ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) = 60000)
    (hInv : ∀ s ∈ K, s ≠ 1 → s * s = 1 →
      ¬ 15 ∣ Nat.card (K ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G))
    (hMK : M ≤ K) (hNM : K ⊓ Subgroup.normalizer (P : Set G) ≤ M)
    (hodd : ¬ 2 ∣ (K ⊓ Subgroup.normalizer (P : Set G)).relIndex M)
    {u : G} (huN : u ∈ K ⊓ Subgroup.normalizer (P : Set G)) (hu1 : u ≠ 1) (hu2 : u * u = 1)
    (hinv : ∀ x ∈ P, u * x * u = x⁻¹) :
    ∀ g ∈ M, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) → g * u * g⁻¹ = u := by
  set N := K ⊓ Subgroup.normalizer (P : Set G)
  have huK : u ∈ K := huN.1
  have hux : ∀ x ∈ P, u * x = x⁻¹ * u := fun x hx => mul_eq_inv_mul_of_conj hu2 (hinv x hx)
  have hCP : ∀ w ∈ K, (∀ x ∈ P, x * w = w * x) → w ∈ P := fun w hwK hw =>
    hCZ (Subgroup.mem_inf.mpr
      ⟨hwK, Subgroup.mem_centralizer_iff.mpr (fun z hz => hw z (hZP hz))⟩)
  have hconj : ∀ c ∈ N, c * u * c⁻¹ * u ∈ P := by
    intro c hc
    obtain ⟨hcK, hcP⟩ := Subgroup.mem_inf.mp hc
    refine hCP _ (K.mul_mem (K.mul_mem (K.mul_mem hcK huK) (K.inv_mem hcK)) huK) fun x hx => ?_
    have hy : c⁻¹ * x⁻¹ * c ∈ P := (Subgroup.mem_normalizer_iff''.mp hcP x⁻¹).mp (P.inv_mem hx)
    symm
    calc c * u * c⁻¹ * u * x = c * u * c⁻¹ * (u * x) := by group
      _ = c * u * c⁻¹ * (x⁻¹ * u) := by rw [hux x hx]
      _ = c * (u * (c⁻¹ * x⁻¹ * c)) * c⁻¹ * u := by group
      _ = c * ((c⁻¹ * x⁻¹ * c)⁻¹ * u) * c⁻¹ * u := by rw [hux _ hy]
      _ = x * (c * u * c⁻¹ * u) := by group
  let _ : MulAction N G := MulAction.compHom G ((MulAut.conj).comp N.subtype)
  have hsmul : ∀ (n : N) (x : G), n • x = (n : G) * x * (n : G)⁻¹ := fun _ _ => rfl
  have hstab : MulAction.stabilizer N u =
      (N ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨n.2, ?_⟩
      calc (n : G) * u = (n : G) * u * (n : G)⁻¹ * n := by group
        _ = u * n := by rw [h]
    · rintro ⟨-, h⟩
      rw [h]; group
  have horbit : MulAction.orbit N u = (fun x => x * u) '' (P : Set G) := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨_, hconj n n.2, ?_⟩
      show (n : G) * u * (n : G)⁻¹ * u * u = (n : G) * u * (n : G)⁻¹
      rw [mul_assoc _ u u, hu2, mul_one]
    · rintro ⟨p, hp, rfl⟩
      have hr : p ^ 313 ∈ P := P.pow_mem hp _
      have h625 : p ^ 625 = 1 := by
        rw [← hPcard]
        exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard P hp)
      refine ⟨⟨p ^ 313, Subgroup.mem_inf.mpr ⟨hPK hr, Subgroup.le_normalizer hr⟩⟩, ?_⟩
      show p ^ 313 * u * (p ^ 313)⁻¹ = p * u
      calc p ^ 313 * u * (p ^ 313)⁻¹ = p ^ 313 * (u * (p ^ 313)⁻¹) := by group
        _ = p ^ 313 * ((p ^ 313)⁻¹⁻¹ * u) := by rw [hux _ (P.inv_mem hr)]
        _ = p ^ 625 * p * u := by group
        _ = p * u := by rw [h625, one_mul]
  have hidx := MulAction.index_stabilizer N u
  have hPn : (P : Set G).ncard = Nat.card P := by rw [← Nat.card_coe_set_eq]; rfl
  rw [hstab, horbit, Set.ncard_image_of_injective _ (mul_left_injective u), hPn, hPcard] at hidx
  have hCu : ¬ 2 ∣ (N ⊓ Subgroup.centralizer ({u} : Set G)).relIndex N := by
    rw [Subgroup.relIndex, hidx]
    norm_num
  have hcardC : Nat.card (N ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = 96 := by
    have h := ((N ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G).subgroupOf N).index_mul_card
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hNcard] at h
    omega
  have h3 : 3 ∣ Nat.card (K ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
    have h := Subgroup.card_dvd_of_le
      (inf_le_inf_right (Subgroup.centralizer ({u} : Set G)) (inf_le_left : N ≤ K))
    rw [hcardC] at h
    exact (by norm_num : 3 ∣ 96).trans h
  have hstar : ∀ s ∈ N, s * u = u * s → s * s = 1 → s ≠ u → ¬ ∃ g ∈ M, g * u * g⁻¹ = s := by
    rintro s hsN hsu hs2 hsne ⟨g, hgM, hgs⟩
    obtain ⟨hsK, hsP⟩ := Subgroup.mem_inf.mp hsN
    by_cases hC : ∀ y ∈ P, s * y = y * s → y = 1
    ·
      have hsx : ∀ x ∈ P, s * x = x⁻¹ * s := fun x hx =>
        mul_eq_inv_mul_of_conj hs2 (conj_eq_inv_of_centralizer hab hsP hs2 hC x hx)
      have hw : s * u ∈ P := by
        refine hCP _ (K.mul_mem hsK huK) fun x hx => ?_
        calc x * (s * u) = x⁻¹⁻¹ * s * u := by rw [inv_inv, mul_assoc]
          _ = s * x⁻¹ * u := by rw [hsx _ (P.inv_mem hx)]
          _ = s * (x⁻¹ * u) := by rw [mul_assoc]
          _ = s * u * x := by rw [← hux x hx, mul_assoc]
      have hw1 : s * u = 1 := by
        refine eq_one_of_isPGroup_of_pow_eq_one hP5 hw (by norm_num : Nat.Coprime 5 2) ?_
        calc (s * u) ^ 2 = s * (u * s) * u := by rw [pow_two]; group
          _ = s * s * (u * u) := by rw [← hsu]; group
          _ = 1 := by rw [hs2, hu2, one_mul]
      apply hsne
      calc s = s * u * u := by rw [mul_assoc, hu2, mul_one]
        _ = u := by rw [hw1, one_mul]
    ·
      push Not at hC
      obtain ⟨y, hyP, hys, hy1⟩ := hC
      obtain ⟨j, hj⟩ := exists_orderOf_eq_pow_succ Nat.prime_five hP5 hyP hy1
      have h5 : 5 ∣ Nat.card (K ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) := by
        have h := Subgroup.orderOf_dvd_natCard (K ⊓ Subgroup.centralizer ({s} : Set G))
          (Subgroup.mem_inf.mpr ⟨hPK hyP, Subgroup.mem_centralizer_singleton_iff.mpr hys.symm⟩)
        rw [hj] at h
        exact (dvd_pow_self 5 (Nat.succ_ne_zero j)).trans h
      rw [← hgs, card_inf_centralizer_conj (hMK hgM)] at h5
      exact hInv u huK hu1 hu2 (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5)
  exact isolated_of_odd_index hNM hodd huN hu2 hCu hstar

end CFSG.HardMathSupport.Malle.Coordinator
