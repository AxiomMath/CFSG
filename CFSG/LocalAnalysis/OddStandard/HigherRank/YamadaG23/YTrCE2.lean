module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.Quasithin.Background.G119Group

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement Pointwise

private theorem orderOf_finRotate_three : orderOf (finRotate 3) = 3 := by
  have h3 : (finRotate 3) ^ 3 = 1 := by decide
  have h1 : finRotate 3 ≠ 1 := by decide
  have hdvd : orderOf (finRotate 3) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) h1
  · exact h

private theorem swap_inv_of_cube (c : Equiv.Perm (Fin 3)) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) :
    Equiv.swap (0 : Fin 3) 1 * c * (Equiv.swap (0 : Fin 3) 1)⁻¹ = c⁻¹ := by
  revert c
  decide +kernel

private theorem exists_perm_fin3_inv (c : Equiv.Perm (Fin 3)) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) :
    ∃ t : Equiv.Perm (Fin 3), t * t = 1 ∧ t ≠ 1 ∧ t * c * t⁻¹ = c⁻¹ :=
  ⟨Equiv.swap (0 : Fin 3) 1, by decide, by decide, swap_inv_of_cube c hc1 hc3⟩

private theorem eq_one_of_pow_three_dvd_six {b : ℕ} (h : 3 ^ b ∣ 6) (hb : b ≠ 0) : b = 1 := by
  have hle : 3 ^ b ≤ 6 := Nat.le_of_dvd (by norm_num) h
  by_contra hb1
  have hb2 : 2 ≤ b := by omega
  have hlt : 3 ^ 2 ≤ 3 ^ b := pow_le_pow_right₀ (by norm_num) hb2
  norm_num at hlt
  omega

private theorem eq_one_of_mem_inf_of_card_dvd_three_of_isPGroup_two
    {G : Type} [Group G] {Z A : Subgroup G} {x : G}
    (hZ3 : Nat.card ↥Z ∣ 3) (hA2 : IsPGroup 2 ↥A) (hxZ : x ∈ Z) (hxA : x ∈ A) :
    x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hZp : IsPGroup 3 ↥Z := IsPGroup.of_card_dvd_pow (p := 3) (n := 1) (by simpa using hZ3)
  exact Subgroup.mem_bot.mp
    ((IsPGroup.disjoint_of_ne 3 2 (by norm_num) Z A hZp hA2).le_bot ⟨hxZ, hxA⟩)

private theorem quotient_mk'_comm {H : Type} [Group H] (N : Subgroup H) [N.Normal] {x y : H}
    (h : x * y * x⁻¹ * y⁻¹ ∈ N) :
    QuotientGroup.mk' N x * QuotientGroup.mk' N y =
      QuotientGroup.mk' N y * QuotientGroup.mk' N x := by
  have hc : QuotientGroup.mk' N (x * y * x⁻¹ * y⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff (x * y * x⁻¹ * y⁻¹)).mpr h
  have h1 : QuotientGroup.mk' N x * QuotientGroup.mk' N y * (QuotientGroup.mk' N x)⁻¹ *
      (QuotientGroup.mk' N y)⁻¹ = 1 := by
    rw [show QuotientGroup.mk' N x * QuotientGroup.mk' N y * (QuotientGroup.mk' N x)⁻¹ *
        (QuotientGroup.mk' N y)⁻¹ = QuotientGroup.mk' N (x * y * x⁻¹ * y⁻¹) by
      simp only [map_mul, map_inv]]
    exact hc
  calc QuotientGroup.mk' N x * QuotientGroup.mk' N y =
        (QuotientGroup.mk' N x * QuotientGroup.mk' N y * (QuotientGroup.mk' N x)⁻¹ *
          (QuotientGroup.mk' N y)⁻¹) * (QuotientGroup.mk' N y * QuotientGroup.mk' N x) := by
        group
    _ = 1 * (QuotientGroup.mk' N y * QuotientGroup.mk' N x) := by rw [h1]
    _ = QuotientGroup.mk' N y * QuotientGroup.mk' N x := one_mul _

private theorem quotient_mk'_pow_three_eq_one {H : Type} [Group H] (N : Subgroup H) [N.Normal]
    {x : H} (h : x ^ 3 ∈ N) : (QuotientGroup.mk' N x) ^ 3 = 1 := by
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (x ^ 3)).mpr h

theorem centExt_comm_sup_eq {G : Type} [Group G] [Finite G] {N K : Subgroup G} (hKN : K ≤ N)
    (h : SecProp N K (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))) :
    ⁅N, N⁆ ⊔ K = N := by
  haveI : Group.IsPerfect (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.Quasithin.G11.g119_isPerfect_generalLinearGroup_zmod2 (n := 3) (by norm_num)
  obtain ⟨hKnorm, e⟩ := h
  letI := hKnorm
  let f := QuotientGroup.mk' (K.subgroupOf N)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective (K.subgroupOf N)
  have hperf : Group.IsPerfect (↥N ⧸ K.subgroupOf N) :=
    Group.IsPerfect.ofSurjective (f := e.some.symm.toMonoidHom) e.some.symm.surjective
  have hmap : (commutator ↥N).map f = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective f hf]
    exact hperf.commutator_eq_top
  have hsup : commutator ↥N ⊔ K.subgroupOf N = ⊤ := by
    rw [← QuotientGroup.ker_mk' (K.subgroupOf N), ← top_le_iff,
      ← Subgroup.map_le_map_iff (f := f) (H := ⊤) (K := commutator ↥N), Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective f hf, top_le_iff]
    exact hmap
  have := congrArg (Subgroup.map N.subtype) hsup
  rw [Subgroup.map_sup, Subgroup.map_subtype_commutator, Subgroup.map_subgroupOf_eq_of_le hKN,
    Subgroup.map_top, Subgroup.range_subtype] at this
  exact this

theorem exists_threeElem_not_mem_of_secProp_perm3 {G : Type} [Group G] [Finite G]
    {N K : Subgroup G} (hKN : K ≤ N)
    (h : SecProp N K (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))) :
    ∃ κ ∈ N, IsPGroup 3 ↥(zpowers κ) ∧ κ ∉ K := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hKnorm, e⟩ := h
  letI := hKnorm
  let f := QuotientGroup.mk' (K.subgroupOf N)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective (K.subgroupOf N)
  obtain ⟨x, hx⟩ := hf (e.some.symm (finRotate 3))
  set n := orderOf (x : G) with hn
  have hn0 : n ≠ 0 := (orderOf_pos (x : G)).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  have hm0 : m ≠ 0 := fun h => hn0 (by rw [hnm, h, mul_zero])
  let κ : G := (x : G) ^ m
  have hκN : κ ∈ N := pow_mem x.2 m
  refine ⟨κ, hκN, ?_, ?_⟩
  · have hκord : orderOf κ = 3 ^ a := by
      rw [show κ = (x : G) ^ m from rfl, orderOf_pow, ← hn, hnm,
        Nat.gcd_eq_right ⟨3 ^ a, by rw [mul_comm]⟩,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    have : Nat.card ↥(zpowers κ) ∣ 3 ^ a := by
      simp [Nat.card_zpowers, hκord]
    exact IsPGroup.of_card_dvd_pow (p := 3) (n := a) this
  · intro hκK
    have hmem : x ^ m ∈ f.ker := by
      rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
      simpa [κ] using hκK
    have h1 : (e.some.symm (finRotate 3)) ^ m = 1 := by
      have := MonoidHom.mem_ker.mp hmem
      rwa [map_pow, hx] at this
    have hm_dvd : orderOf (e.some.symm (finRotate 3)) ∣ m :=
      orderOf_dvd_iff_pow_eq_one.mpr h1
    have hord : orderOf (e.some.symm (finRotate 3)) = 3 :=
      (MulEquiv.orderOf_eq e.some.symm _).trans orderOf_finRotate_three
    rw [hord] at hm_dvd
    exact hm hm_dvd

theorem centExt_cube_eq_one {G : Type} [Group G] [Finite G] {N₁ Z A : Subgroup G}
    (hZA : Z ⊔ A ≤ N₁) (hZc : ∀ z ∈ Z, ∀ g ∈ N₁, z * g = g * z) (hZ3 : Nat.card ↥Z ∣ 3)
    (hA2 : IsPGroup 2 ↥A) (hAn : ∀ g ∈ N₁, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (h : SecProp N₁ (Z ⊔ A) (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))))
    {k : G} (hk : k ∈ N₁) (hk3 : IsPGroup 3 ↥(zpowers k)) (hkn : k ∉ Z ⊔ A) : k ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hBnorm, e⟩ := h
  have hBnorm' : ∀ h k : G, h ∈ Z ⊔ A → k ∈ N₁ → k * h * k⁻¹ ∈ Z ⊔ A :=
    (Subgroup.normal_subgroupOf_iff hZA).mp hBnorm
  letI := hBnorm
  let π := QuotientGroup.mk' ((Z ⊔ A).subgroupOf N₁)
  let kB : ↥N₁ := ⟨k, hk⟩
  have hA_le : A ≤ N₁ := (le_sup_right : A ≤ Z ⊔ A).trans hZA
  have hA_cent : A ≤ Subgroup.centralizer (Z : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    exact fun z hz => hZc z hz a (hA_le ha)
  have hZA_mul : (↑(Z ⊔ A) : Set G) = (Z : Set G) * (A : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Z A
      (hA_cent.trans (Subgroup.centralizer_le_normalizer (Z : Set G)))
  obtain ⟨r, hr⟩ := hk3.exists_orderOf_eq_pow ⟨k, mem_zpowers k⟩
  have hkord : orderOf k = 3 ^ r :=
    (Subgroup.orderOf_coe (⟨k, mem_zpowers k⟩ : zpowers k)).trans hr
  have hπk1 : π kB ≠ 1 := by
    intro h1
    apply hkn
    have hmem : kB ∈ π.ker := MonoidHom.mem_ker.mpr h1
    rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  have h1 : orderOf (π kB) ∣ 3 ^ r := by
    rw [← hkord, ← Subgroup.orderOf_mk k hk]
    exact orderOf_map_dvd π kB
  have h2 : orderOf (π kB) ∣ 6 := by
    have h := orderOf_dvd_natCard (e.some (π kB))
    rw [Nat.card_perm, Nat.card_fin, show Nat.factorial 3 = 6 by decide] at h
    rwa [MulEquiv.orderOf_eq e.some (π kB)] at h
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp h1
  have hb6 : 3 ^ b ∣ 6 := by rw [← hb]; exact h2
  have hb0 : b ≠ 0 := by
    intro h0
    exact hπk1 (orderOf_eq_one_iff.mp (by rw [h0, pow_zero] at hb; exact hb))
  have hπ3 : (π kB) ^ 3 = 1 := by
    rw [← show orderOf (π kB) = 3 from by rw [hb, eq_one_of_pow_three_dvd_six hb6 hb0, pow_one]]
    exact pow_orderOf_eq_one _
  have hk3B : k ^ 3 ∈ Z ⊔ A := by
    have hker : kB ^ 3 ∈ (Z ⊔ A).subgroupOf N₁ := by
      have h1 : π (kB ^ 3) = 1 := by rw [map_pow, hπ3]
      have := MonoidHom.mem_ker.mpr h1
      rwa [QuotientGroup.ker_mk'] at this
    rw [Subgroup.mem_subgroupOf] at hker
    simpa using hker
  have hwZ : k ^ 3 ∈ Z := by
    obtain ⟨z₀, hz₀Z, a₀, ha₀A, hz₀a₀⟩ : ∃ z ∈ Z, ∃ a ∈ A, z * a = k ^ 3 := by
      have hmem : k ^ 3 ∈ (↑(Z ⊔ A) : Set G) := hk3B
      rw [hZA_mul] at hmem
      exact Set.mem_mul.mp hmem
    have ha₀N : a₀ ∈ N₁ := hA_le ha₀A
    have hz₀_comm : Commute z₀ a₀ := (commute_iff_eq z₀ a₀).mpr (hZc z₀ hz₀Z a₀ ha₀N)
    have hwpow : (k ^ 3) ^ 3 ^ r = 1 := by
      have hkr : k ^ 3 ^ r = 1 := by rw [← hkord]; exact pow_orderOf_eq_one k
      calc (k ^ 3) ^ 3 ^ r = k ^ (3 * 3 ^ r) := by rw [pow_mul]
        _ = k ^ (3 ^ r * 3) := by rw [mul_comm]
        _ = (k ^ 3 ^ r) ^ 3 := by rw [pow_mul]
        _ = 1 := by rw [hkr, one_pow]
    have ha₀_pow : a₀ ^ 3 ^ r = 1 := by
      have h : z₀ ^ 3 ^ r * a₀ ^ 3 ^ r = 1 := by
        rw [← hz₀_comm.mul_pow (3 ^ r), hz₀a₀, hwpow]
      have hmemZ : a₀ ^ 3 ^ r ∈ Z := by
        rw [eq_inv_of_mul_eq_one_right h]
        exact Z.inv_mem (Z.pow_mem hz₀Z _)
      exact eq_one_of_mem_inf_of_card_dvd_three_of_isPGroup_two hZ3 hA2 hmemZ (A.pow_mem ha₀A _)
    have ha₀_eq : a₀ = 1 := by
      have hdvd3 : orderOf a₀ ∣ 3 ^ r := orderOf_dvd_iff_pow_eq_one.mpr ha₀_pow
      obtain ⟨s, hs⟩ := hA2 ⟨a₀, ha₀A⟩
      have hdvd2 : orderOf a₀ ∣ 2 ^ s := by
        rw [← Subgroup.orderOf_mk a₀ ha₀A]
        exact orderOf_dvd_iff_pow_eq_one.mpr hs
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.coprime_pow_primes r s (by norm_num) (by norm_num) (by norm_num)) hdvd3 hdvd2)
    rw [← hz₀a₀, ha₀_eq, mul_one]
    exact hz₀Z
  have hc1 : e.some (π kB) ≠ 1 := fun hc => hπk1 (e.some.injective (by rw [hc, map_one]))
  have hc3 : (e.some (π kB)) ^ 3 = 1 := by rw [← map_pow, hπ3, map_one]
  obtain ⟨t, -, -, htc⟩ := exists_perm_fin3_inv (e.some (π kB)) hc1 hc3
  let ψ : ↥N₁ →* Equiv.Perm (Fin 3) := e.some.toMonoidHom.comp π
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨z, hz⟩ := e.some.surjective y
    obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective ((Z ⊔ A).subgroupOf N₁) z
    refine ⟨w, ?_⟩
    show e.some (π w) = y
    rw [hw, hz]
  obtain ⟨τ, hτ⟩ := hψ t
  have hψrel : ψ (τ * kB * τ⁻¹) = ψ kB⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv, hτ]
    exact htc
  have hτk : τ * kB * τ⁻¹ * kB ∈ (Z ⊔ A).subgroupOf N₁ := by
    have hπ1 : π (τ * kB * τ⁻¹ * kB) = 1 := by
      apply e.some.injective
      rw [map_one]
      show ψ (τ * kB * τ⁻¹ * kB) = 1
      rw [map_mul, hψrel, map_inv, inv_mul_cancel]
    have := MonoidHom.mem_ker.mpr hπ1
    rwa [QuotientGroup.ker_mk'] at this
  have hτgmemB : (τ : G) * k * (τ : G)⁻¹ * k ∈ Z ⊔ A := by
    have := hτk
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  let mG : G := (τ : G) * k * (τ : G)⁻¹ * k
  let m'G : G := k * mG * k⁻¹
  have hm'B : m'G ∈ Z ⊔ A := hBnorm' mG k hτgmemB hk
  have hτ_conj : (τ : G) * k * (τ : G)⁻¹ = k⁻¹ * m'G := by
    rw [show m'G = k * ((τ : G) * k * (τ : G)⁻¹ * k) * k⁻¹ from rfl]
    group
  have hAnorm : (A.subgroupOf N₁).Normal :=
    (Subgroup.normal_subgroupOf_iff hA_le).mpr fun a g ha hg => hAn g hg a ha
  letI := hAnorm
  let ρ := QuotientGroup.mk' (A.subgroupOf N₁)
  have hm'G_N₁ : m'G ∈ N₁ := hZA hm'B
  let mB : ↥N₁ := ⟨m'G, hm'G_N₁⟩
  have hτkB : τ * kB * τ⁻¹ = kB⁻¹ * mB := by
    apply Subtype.ext
    show (τ : G) * k * (τ : G)⁻¹ = k⁻¹ * m'G
    exact hτ_conj
  have hρτkB : ρ (τ * kB * τ⁻¹) = (ρ kB)⁻¹ * ρ mB := by
    rw [hτkB, map_mul, map_inv]
  obtain ⟨z, hzZ, a, haA, hza⟩ : ∃ z ∈ Z, ∃ a ∈ A, z * a = m'G := by
    have hmem : m'G ∈ (↑(Z ⊔ A) : Set G) := hm'B
    rw [hZA_mul] at hmem
    exact Set.mem_mul.mp hmem
  have haN : a ∈ N₁ := hA_le haA
  have hz_comm : Commute z a := (commute_iff_eq z a).mpr (hZc z hzZ a haN)
  have hm'cube : m'G ^ 3 ∈ A := by
    have hz3 : z ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard Z hzZ).trans hZ3)
    rw [← hza, hz_comm.mul_pow 3, hz3, one_mul]
    exact A.pow_mem haA 3
  have hcube : (ρ mB) ^ 3 = 1 := by
    refine quotient_mk'_pow_three_eq_one (A.subgroupOf N₁) ?_
    rw [Subgroup.mem_subgroupOf]
    show m'G ^ 3 ∈ A
    exact hm'cube
  have hm'commA : ∀ gB : ↥N₁, mB * gB * mB⁻¹ * gB⁻¹ ∈ (A.subgroupOf N₁) := by
    intro gB
    rw [Subgroup.mem_subgroupOf]
    show m'G * (gB : G) * m'G⁻¹ * (gB : G)⁻¹ ∈ A
    rw [← hza]
    have hmiddle : a * (gB : G) * a⁻¹ ∈ N₁ :=
      N₁.mul_mem (N₁.mul_mem haN gB.2) (N₁.inv_mem haN)
    have hzg : z * (a * (gB : G) * a⁻¹) = (a * (gB : G) * a⁻¹) * z :=
      hZc z hzZ (a * (gB : G) * a⁻¹) hmiddle
    have h_eq : (z * a) * (gB : G) * (z * a)⁻¹ * (gB : G)⁻¹
        = a * ((gB : G) * a⁻¹ * (gB : G)⁻¹) := by
      calc (z * a) * (gB : G) * (z * a)⁻¹ * (gB : G)⁻¹
          = (z * (a * (gB : G) * a⁻¹)) * z⁻¹ * (gB : G)⁻¹ := by group
        _ = ((a * (gB : G) * a⁻¹) * z) * z⁻¹ * (gB : G)⁻¹ := by rw [hzg]
        _ = a * (gB : G) * a⁻¹ * (gB : G)⁻¹ := by group
        _ = a * ((gB : G) * a⁻¹ * (gB : G)⁻¹) := by group
    rw [h_eq]
    exact A.mul_mem haA (hAn (gB : G) gB.2 a⁻¹ (A.inv_mem haA))
  have hcent : ∀ gB : ↥N₁, ρ mB * ρ gB = ρ gB * ρ mB :=
    fun gB => quotient_mk'_comm (A.subgroupOf N₁) (hm'commA gB)
  have hcommρ : Commute (ρ kB) (ρ mB) := (commute_iff_eq (ρ kB) (ρ mB)).mpr (hcent kB).symm
  have hτgcomm : (τ : G) * k ^ 3 * (τ : G)⁻¹ = k ^ 3 := by
    rw [← hZc (k ^ 3) hwZ (τ : G) τ.2]
    group
  have hkB3central : τ * kB ^ 3 * τ⁻¹ = kB ^ 3 := by
    apply Subtype.ext
    show (τ : G) * k ^ 3 * (τ : G)⁻¹ = k ^ 3
    exact hτgcomm
  have hconj3 : (τ * kB * τ⁻¹) ^ 3 = kB ^ 3 := by
    rw [conj_pow, hkB3central]
  have hpow2 : ρ (kB ^ 3) = (ρ kB) ^ 3 := map_pow ρ kB 3
  have hpow : ρ (kB ^ 3) = ((ρ kB)⁻¹) ^ 3 := by
    calc ρ (kB ^ 3) = ρ ((τ * kB * τ⁻¹) ^ 3) := by rw [hconj3]
      _ = (ρ (τ * kB * τ⁻¹)) ^ 3 := map_pow ρ (τ * kB * τ⁻¹) 3
      _ = ((ρ kB)⁻¹ * ρ mB) ^ 3 := by rw [hρτkB]
      _ = ((ρ kB)⁻¹) ^ 3 * (ρ mB) ^ 3 := (hcommρ.inv_left).mul_pow 3
      _ = ((ρ kB)⁻¹) ^ 3 := by rw [hcube, mul_one]
  have h3eq : (ρ kB) ^ 3 = ((ρ kB)⁻¹) ^ 3 := hpow2.symm.trans hpow
  have h6 : (ρ kB) ^ 6 = 1 := by
    have h3self : (ρ kB) ^ 3 = ((ρ kB) ^ 3)⁻¹ := h3eq.trans (inv_pow (ρ kB) 3)
    have h3sq : ((ρ kB) ^ 3) ^ 2 = 1 := by
      rw [pow_two]
      exact (eq_inv_iff_mul_eq_one).mp h3self
    rw [show (ρ kB) ^ 6 = ((ρ kB) ^ 3) ^ 2 by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]]
    exact h3sq
  have hkB6A : kB ^ 6 ∈ (A.subgroupOf N₁) := by
    have h1 : ρ (kB ^ 6) = 1 := by rw [map_pow, h6]
    have := MonoidHom.mem_ker.mpr h1
    rwa [QuotientGroup.ker_mk'] at this
  have hw2A : (k ^ 3) ^ 2 ∈ A := by
    rw [Subgroup.mem_subgroupOf] at hkB6A
    change k ^ 6 ∈ A at hkB6A
    rwa [show (k ^ 3) ^ 2 = k ^ 6 by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]]
  have hw2 : (k ^ 3) ^ 2 = 1 :=
    eq_one_of_mem_inf_of_card_dvd_three_of_isPGroup_two hZ3 hA2 (Z.pow_mem hwZ 2) hw2A
  have hw1 : orderOf (k ^ 3) = 1 := by
    have h2 : orderOf (k ^ 3) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hw2
    have h3 : orderOf (k ^ 3) ∣ 3 := (Subgroup.orderOf_dvd_natCard Z hwZ).trans hZ3
    exact Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 2 3) h2 h3
  exact orderOf_eq_one_iff.mp hw1

end CFSG.OddStandard.HigherRank.YamadaG23
