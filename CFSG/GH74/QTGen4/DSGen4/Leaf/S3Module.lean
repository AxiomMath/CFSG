module

public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private lemma s3m_perm_pow_six : ∀ y : Equiv.Perm (Fin 3), y ^ 6 = 1 := by decide

private lemma s3m_gcd_six_two_pow_dvd (n : ℕ) : Nat.gcd 6 (2 ^ n) ∣ 2 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Nat.gcd_dvd_right 6 (2 ^ n))
  have h6 : 2 ^ j ∣ 6 := by rw [← hj]; exact Nat.gcd_dvd_left 6 (2 ^ n)
  rw [hj]
  rcases Nat.lt_or_ge j 2 with hlt | hge
  · simpa using pow_dvd_pow 2 (show j ≤ 1 by omega)
  · exact absurd (dvd_trans (pow_dvd_pow 2 hge) h6) (by norm_num)

private lemma s3m_perm_sq_of_pow {y : Equiv.Perm (Fin 3)} {n : ℕ} (h : y ^ 2 ^ n = 1) :
    y ^ 2 = 1 := by
  obtain ⟨c, hc⟩ := s3m_gcd_six_two_pow_dvd n
  have hg : y ^ Nat.gcd 6 (2 ^ n) = 1 := pow_gcd_eq_one.mpr ⟨s3m_perm_pow_six y, h⟩
  calc y ^ 2 = y ^ (Nat.gcd 6 (2 ^ n) * c) := by rw [← hc]
    _ = 1 := by rw [pow_mul, hg, one_pow]

private lemma s3m_perm_key_inv : ∀ x y : Equiv.Perm (Fin 3), x * x = 1 → x ≠ 1 → y * y = 1 →
    (y * x) * (y * x) = 1 → y = 1 ∨ y = x := by decide

private lemma s3m_perm_key_conj : ∀ x z : Equiv.Perm (Fin 3), x * x = 1 → x ≠ 1 → z ^ 3 = 1 →
    x * z * x⁻¹ = z⁻¹ := by decide

private lemma s3m_card_sq_of_norm {G : Type} [Group G] (Y C : Subgroup G) (t : G)
    (hcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hsq : ∀ a ∈ Y, a * a = 1)
    (htY : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) (htt : ∀ y ∈ Y, t * t * y * (t * t)⁻¹ = y)
    (hkey : ∀ z ∈ Y, t * z * t⁻¹ = z ↔ z ∈ C)
    (hsurj : ∀ z ∈ Y, t * z * t⁻¹ = z → ∃ w ∈ Y, w * (t * w * t⁻¹) = z) :
    Nat.card Y = Nat.card ↥(Y ⊓ C) ^ 2 := by
  let N : ↥Y →* ↥Y := MonoidHom.mk'
    (fun z => ⟨(z : G) * (t * (z : G) * t⁻¹), Y.mul_mem z.2 (htY _ z.2)⟩)
    (by
      intro a b
      apply Subtype.ext
      show (a : G) * b * (t * ((a : G) * b) * t⁻¹)
        = (a : G) * (t * (a : G) * t⁻¹) * ((b : G) * (t * (b : G) * t⁻¹))
      calc (a : G) * b * (t * ((a : G) * b) * t⁻¹)
          = (a : G) * (b * (t * (a : G) * t⁻¹)) * (t * (b : G) * t⁻¹) := by group
        _ = (a : G) * ((t * (a : G) * t⁻¹) * b) * (t * (b : G) * t⁻¹) := by
          rw [hcomm (b : G) b.2 _ (htY _ a.2)]
        _ = (a : G) * (t * (a : G) * t⁻¹) * ((b : G) * (t * (b : G) * t⁻¹)) := by group)
  have hN_one : ∀ z : ↥Y, N z = 1 ↔ t * (z : G) * t⁻¹ = z := by
    intro z
    constructor
    · intro h
      have h' : (z : G) * (t * (z : G) * t⁻¹) = 1 := congrArg Subtype.val h
      exact (eq_inv_of_mul_eq_one_right h').trans (inv_eq_of_mul_eq_one_right (hsq _ z.2))
    · intro h
      apply Subtype.ext
      show (z : G) * (t * (z : G) * t⁻¹) = 1
      rw [h]
      exact hsq _ z.2
  have hker_eq : N.ker = (Y ⊓ C).subgroupOf Y := by
    ext z
    rw [MonoidHom.mem_ker, hN_one, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      exact ⟨z.2, (hkey _ z.2).mp h⟩
    · intro h
      exact (hkey _ z.2).mpr h.2
  have hran_eq : N.range = (Y ⊓ C).subgroupOf Y := by
    ext z
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨w, rfl⟩
      have hwY : (w : G) ∈ Y := w.2
      have h2 : t * (t * (w : G) * t⁻¹) * t⁻¹ = w := by
        calc t * (t * (w : G) * t⁻¹) * t⁻¹ = (t * t) * (w : G) * (t * t)⁻¹ := by group
          _ = w := htt _ hwY
      have key : t * ((N w : ↥Y) : G) * t⁻¹ = ((N w : ↥Y) : G) := by
        show t * ((w : G) * (t * (w : G) * t⁻¹)) * t⁻¹ = (w : G) * (t * (w : G) * t⁻¹)
        calc t * ((w : G) * (t * (w : G) * t⁻¹)) * t⁻¹
            = (t * (w : G) * t⁻¹) * (t * (t * (w : G) * t⁻¹) * t⁻¹) := by group
          _ = (t * (w : G) * t⁻¹) * w := by rw [h2]
          _ = (w : G) * (t * (w : G) * t⁻¹) := hcomm _ (htY _ hwY) _ hwY
      exact ⟨(N w).2, (hkey _ (N w).2).mp key⟩
    · rintro ⟨hzY, hzC⟩
      obtain ⟨w, hwY, hw⟩ := hsurj z hzY ((hkey z hzY).mpr hzC)
      exact ⟨⟨w, hwY⟩, Subtype.ext hw⟩
  have hsub : Nat.card ((Y ⊓ C).subgroupOf Y) = Nat.card ↥(Y ⊓ C) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcount := Subgroup.card_ker_mul_card_range N
  rw [hker_eq, hran_eq, hsub] at hcount
  rw [← hcount, sq]

theorem leafS3Module : LeafS3Module := by
  intro G _ _ L Y T k hq hY hLY hc hk hko hff hT
  obtain ⟨e⟩ := hq
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥L →* Equiv.Perm (Fin 3), ∀ g : ↥L, φ g = e (QuotientGroup.mk g) :=
    ⟨e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥L)), fun g => rfl⟩
  have hmemO : ∀ x : ↥L, (x : G) ∈ pCoreOf 2 L ↔ x ∈ pCore 2 ↥L := by
    intro x
    constructor
    · intro h
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
      have hxy : y = x := Subtype.ext hyx
      rw [← hxy]
      exact hy
    · intro h
      exact Subgroup.mem_map_of_mem _ h
  have hker : ∀ g : ↥L, φ g = 1 → (g : G) ∈ pCoreOf 2 L := by
    intro g hg
    rw [hφ] at hg
    have h1 : (QuotientGroup.mk g : ↥L ⧸ pCore 2 ↥L) = 1 := e.injective (by rw [hg, map_one])
    exact (hmemO g).mpr ((QuotientGroup.eq_one_iff g).mp h1)
  have hcommY : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hY.1.is_comm.comm (⟨a, ha⟩ : ↥Y) ⟨b, hb⟩)
  have hcomm3 : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a * b * c = c * a * b := by
    intro a ha b hb c hc'
    calc a * b * c = a * (b * c) := mul_assoc _ _ _
      _ = a * (c * b) := by rw [hcommY b hb c hc']
      _ = (a * c) * b := (mul_assoc _ _ _).symm
      _ = (c * a) * b := by rw [hcommY a ha c hc']
  have hsqY : ∀ a ∈ Y, a * a = 1 := fun a ha => by
    have h := hY.2 a ha
    rwa [sq] at h
  have hO_comm : ∀ q ∈ pCoreOf 2 L, ∀ y ∈ Y, q * y * q⁻¹ = y := by
    intro q hq' y hy
    have h := hc q hq' y hy
    rw [commutatorElement_def] at h
    exact mul_inv_eq_one.mp h
  have hconjY : ∀ g ∈ L, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hLY hg) y).mp hy
  have hidx : (pCore 2 ↥L).index = 6 := by
    have h1 : Nat.card (↥L ⧸ pCore 2 ↥L) = Nat.card (Equiv.Perm (Fin 3)) :=
      Nat.card_congr e.toEquiv
    rw [Subgroup.index, h1, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hT_not : ∃ t ∈ T, t ∉ pCoreOf 2 L := by
    by_contra hcon
    push Not at hcon
    apply hT.2.2
    have hle : T.subgroupOf L ≤ pCore 2 ↥L := by
      intro x hx
      exact (hmemO x).mp (hcon x (Subgroup.mem_subgroupOf.mp hx))
    have h2 := Subgroup.relIndex_mul_index hle
    rw [hidx] at h2
    rw [← h2]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨t, htT, htO⟩ := hT_not
  have htL : t ∈ L := hT.1 htT
  have hTsq : ∀ g ∈ T, ∀ hgL : g ∈ L, φ ⟨g, hgL⟩ * φ ⟨g, hgL⟩ = 1 := by
    intro g hg hgL
    obtain ⟨n, hn⟩ := hT.2.1 ⟨g, hg⟩
    have hn' : g ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h1 : (⟨g, hgL⟩ : ↥L) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn')
    have h2 : φ ⟨g, hgL⟩ ^ 2 ^ n = 1 := by rw [← map_pow, h1, map_one]
    rw [← sq]
    exact s3m_perm_sq_of_pow h2
  have hx1 : φ ⟨t, htL⟩ ≠ 1 := fun h => htO (hker ⟨t, htL⟩ h)
  have hxx : φ ⟨t, htL⟩ * φ ⟨t, htL⟩ = 1 := hTsq t htT htL
  have hcoset : ∀ g ∈ T, g ∈ pCoreOf 2 L ∨ t⁻¹ * g ∈ pCoreOf 2 L := by
    intro g hg
    have hgL : g ∈ L := hT.1 hg
    have hgtL : g * t ∈ L := L.mul_mem hgL htL
    have hmul : φ ⟨g * t, hgtL⟩ = φ ⟨g, hgL⟩ * φ ⟨t, htL⟩ := map_mul φ ⟨g, hgL⟩ ⟨t, htL⟩
    have hsq : (φ ⟨g, hgL⟩ * φ ⟨t, htL⟩) * (φ ⟨g, hgL⟩ * φ ⟨t, htL⟩) = 1 := by
      rw [← hmul]
      exact hTsq (g * t) (T.mul_mem hg htT) hgtL
    rcases s3m_perm_key_inv _ _ hxx hx1 (hTsq g hg hgL) hsq with h1 | h1
    · exact Or.inl (hker ⟨g, hgL⟩ h1)
    · refine Or.inr (hker (⟨t, htL⟩⁻¹ * ⟨g, hgL⟩) ?_)
      rw [map_mul, map_inv, h1, inv_mul_cancel]
  have htt : t * t ∈ pCoreOf 2 L := by
    refine hker ⟨t * t, L.mul_mem htL htL⟩ ?_
    have hm : (⟨t * t, L.mul_mem htL htL⟩ : ↥L) = ⟨t, htL⟩ * ⟨t, htL⟩ := rfl
    rw [hm, map_mul]
    exact hxx
  have hkL : k ∈ L := hk
  have hk3 : k ^ 3 = 1 := by rw [← hko]; exact pow_orderOf_eq_one k
  have hz3 : φ ⟨k, hkL⟩ ^ 3 = 1 := by
    have h1 : (⟨k, hkL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
    rw [← map_pow, h1, map_one]
  obtain ⟨q, hqdef, hqO⟩ : ∃ q : G, q = t * k * t⁻¹ * k ∧ q ∈ pCoreOf 2 L := by
    have hqL : t * k * t⁻¹ * k ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem htL hkL) (L.inv_mem htL)) hkL
    refine ⟨t * k * t⁻¹ * k, rfl, hker ⟨t * k * t⁻¹ * k, hqL⟩ ?_⟩
    have hm : (⟨t * k * t⁻¹ * k, hqL⟩ : ↥L) = ⟨t, htL⟩ * ⟨k, hkL⟩ * ⟨t, htL⟩⁻¹ * ⟨k, hkL⟩ :=
      rfl
    rw [hm, map_mul, map_mul, map_mul, map_inv, s3m_perm_key_conj _ _ hxx hx1 hz3, inv_mul_cancel]
  have htY : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := fun y hy => hconjY t htL y hy
  have hkY : ∀ y ∈ Y, k * y * k⁻¹ ∈ Y := fun y hy => hconjY k hkL y hy
  have hkinvY : ∀ y ∈ Y, k⁻¹ * y * k ∈ Y := fun y hy => by
    have h := hconjY k⁻¹ (L.inv_mem hkL) y hy
    rwa [inv_inv] at h
  have hk2 : k * k = k⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three']
    exact hk3
  have hqinv : ∀ z ∈ Y, q⁻¹ * z * q = z := fun z hz => by
    have h := hO_comm q hqO z hz
    calc q⁻¹ * z * q = q⁻¹ * (q * z * q⁻¹) * q := by rw [h]
      _ = z := by group
  have hnorm : ∀ z ∈ Y, z * (k * z * k⁻¹) * (k⁻¹ * z * k) = 1 := by
    intro z hz
    have hA := hkY z hz
    have hB := hkinvY z hz
    have hwY : z * (k * z * k⁻¹) * (k⁻¹ * z * k) ∈ Y := Y.mul_mem (Y.mul_mem hz hA) hB
    have e2 : k * (k * z * k⁻¹) * k⁻¹ = k⁻¹ * z * k := by
      calc k * (k * z * k⁻¹) * k⁻¹ = (k * k) * z * (k * k)⁻¹ := by group
        _ = k⁻¹ * z * k := by rw [hk2, inv_inv]
    have e3 : k * (k⁻¹ * z * k) * k⁻¹ = z := by group
    have hkw : k * (z * (k * z * k⁻¹) * (k⁻¹ * z * k)) * k⁻¹
        = z * (k * z * k⁻¹) * (k⁻¹ * z * k) := by
      calc k * (z * (k * z * k⁻¹) * (k⁻¹ * z * k)) * k⁻¹
          = (k * z * k⁻¹) * (k * (k * z * k⁻¹) * k⁻¹) * (k * (k⁻¹ * z * k) * k⁻¹) := by group
        _ = (k * z * k⁻¹) * (k⁻¹ * z * k) * z := by rw [e2, e3]
        _ = z * (k * z * k⁻¹) * (k⁻¹ * z * k) := hcomm3 _ hA _ hB z hz
    have hcomm' : (z * (k * z * k⁻¹) * (k⁻¹ * z * k)) * k
        = k * (z * (k * z * k⁻¹) * (k⁻¹ * z * k)) := by
      calc (z * (k * z * k⁻¹) * (k⁻¹ * z * k)) * k
          = (k * (z * (k * z * k⁻¹) * (k⁻¹ * z * k)) * k⁻¹) * k := by rw [hkw]
        _ = k * (z * (k * z * k⁻¹) * (k⁻¹ * z * k)) := by group
    have hcm : ⁅z * (k * z * k⁻¹) * (k⁻¹ * z * k), k⁆ ∈ (⊥ : Subgroup G) := by
      rw [Subgroup.mem_bot, commutatorElement_def, hcomm']
      group
    exact Subgroup.mem_bot.mp (hff _ hwY hcm)
  have hI1 : ∀ z ∈ Y, t * z * t⁻¹ = z → t * (k * z * k⁻¹) * t⁻¹ = k⁻¹ * z * k := by
    intro z hz hzt
    calc t * (k * z * k⁻¹) * t⁻¹ = (t * k * t⁻¹) * (t * z * t⁻¹) * (t * k⁻¹ * t⁻¹) := by group
      _ = (t * k * t⁻¹) * z * (t * k⁻¹ * t⁻¹) := by rw [hzt]
      _ = q * (k⁻¹ * z * k) * q⁻¹ := by rw [hqdef]; group
      _ = k⁻¹ * z * k := hO_comm q hqO _ (hkinvY z hz)
  have hI2 : ∀ z ∈ Y, t * z * t⁻¹ = z → t * (k⁻¹ * z * k) * t⁻¹ = k * z * k⁻¹ := by
    intro z hz hzt
    calc t * (k⁻¹ * z * k) * t⁻¹ = (t * k⁻¹ * t⁻¹) * (t * z * t⁻¹) * (t * k * t⁻¹) := by group
      _ = (t * k⁻¹ * t⁻¹) * z * (t * k * t⁻¹) := by rw [hzt]
      _ = k * (q⁻¹ * z * q) * k⁻¹ := by rw [hqdef]; group
      _ = k * z * k⁻¹ := by rw [hqinv z hz]
  have hsurj : ∀ z ∈ Y, t * z * t⁻¹ = z → ∃ w ∈ Y, w * (t * w * t⁻¹) = z := by
    intro z hz hzt
    have hA := hkY z hz
    have hB := hkinvY z hz
    refine ⟨z * (k⁻¹ * z * k), Y.mul_mem hz hB, ?_⟩
    have hT' : t * (z * (k⁻¹ * z * k)) * t⁻¹ = z * (k * z * k⁻¹) := by
      calc t * (z * (k⁻¹ * z * k)) * t⁻¹ = (t * z * t⁻¹) * (t * (k⁻¹ * z * k) * t⁻¹) := by group
        _ = z * (k * z * k⁻¹) := by rw [hzt, hI2 z hz hzt]
    rw [hT']
    have hAB : (k * z * k⁻¹) * (k⁻¹ * z * k) = z := by
      have h1 : z * ((k * z * k⁻¹) * (k⁻¹ * z * k)) = 1 :=
        (mul_assoc z (k * z * k⁻¹) (k⁻¹ * z * k)).symm.trans (hnorm z hz)
      exact (eq_inv_of_mul_eq_one_right h1).trans (inv_eq_of_mul_eq_one_right (hsqY z hz))
    calc z * (k⁻¹ * z * k) * (z * (k * z * k⁻¹))
        = ((k⁻¹ * z * k) * z) * (z * (k * z * k⁻¹)) := by rw [hcommY z hz _ hB]
      _ = (k⁻¹ * z * k) * (z * z) * (k * z * k⁻¹) := by group
      _ = (k⁻¹ * z * k) * (k * z * k⁻¹) := by rw [hsqY z hz, mul_one]
      _ = (k * z * k⁻¹) * (k⁻¹ * z * k) := hcommY _ hB _ hA
      _ = z := hAB
  have hC1 : ∀ z ∈ Y, z ∈ Subgroup.centralizer (T : Set G) ↔ t * z = z * t := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact h t htT
    · intro h g hg
      rcases hcoset g hg with hgO | hgO
      · have h' := hO_comm g hgO z hz
        calc g * z = g * z * g⁻¹ * g := by group
          _ = z * g := by rw [h']
      · have h' := hO_comm (t⁻¹ * g) hgO z hz
        have hq' : (t⁻¹ * g) * z = z * (t⁻¹ * g) := by
          calc (t⁻¹ * g) * z = ((t⁻¹ * g) * z * (t⁻¹ * g)⁻¹) * (t⁻¹ * g) := by group
            _ = z * (t⁻¹ * g) := by rw [h']
        calc g * z = t * ((t⁻¹ * g) * z) := by group
          _ = t * (z * (t⁻¹ * g)) := by rw [hq']
          _ = (t * z) * (t⁻¹ * g) := by group
          _ = (z * t) * (t⁻¹ * g) := by rw [h]
          _ = z * g := by group
  have hkey : ∀ z ∈ Y, t * z * t⁻¹ = z ↔ z ∈ Subgroup.centralizer (T : Set G) := fun z hz => by
    rw [mul_inv_eq_iff_eq_mul, hC1 z hz]
  exact s3m_card_sq_of_norm Y (Subgroup.centralizer (T : Set G)) t hcommY hsqY htY
    (fun y hy => hO_comm _ htt y hy) hkey hsurj

end CFSG.GH74.QTGen4.DSGen4
