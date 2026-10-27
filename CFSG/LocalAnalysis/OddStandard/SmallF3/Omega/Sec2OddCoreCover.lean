module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreBasic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem range_eq_bot_of_central_two {P B : Type*} [Group P] [Finite P] [Group B]
    (hP : oddCore P = ⊥) (φ : P →* B) (hker : φ.ker ≤ Subgroup.center P)
    (hcard : Nat.card φ.ker ∣ 2) (hodd : Odd (Nat.card φ.range)) : φ.range = ⊥ := by
  have hcop : Nat.Coprime (Nat.card φ.ker) φ.ker.index := by
    rw [Subgroup.index_ker]
    exact Nat.Coprime.coprime_dvd_left hcard (Nat.coprime_two_left.mpr hodd)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHn : H.Normal := by
    refine ⟨fun h hh g => ?_⟩
    have hg : g ∈ φ.ker ⊔ H := by rw [hH.sup_eq_top]; exact Subgroup.mem_top g
    obtain ⟨k, hk, h', hh', rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    have hkc : ∀ y, y * k = k * y := fun y => Subgroup.mem_center_iff.mp (hker hk) y
    have hconj : k * h' * h * (k * h')⁻¹ = h' * h * h'⁻¹ :=
      calc k * h' * h * (k * h')⁻¹ = k * (h' * h * h'⁻¹) * k⁻¹ := by group
        _ = (h' * h * h'⁻¹) * k * k⁻¹ := by rw [← hkc (h' * h * h'⁻¹)]
        _ = h' * h * h'⁻¹ := by group
    rw [hconj]
    exact H.mul_mem (H.mul_mem hh' hh) (H.inv_mem hh')
  have hHodd : Odd (Nat.card H) := by
    rw [← hH.symm.index_eq_card, Subgroup.index_ker]
    exact hodd
  have hHbot : H = ⊥ := le_bot_iff.mp (hP ▸ le_oddCore_of_normal hHn hHodd)
  have h1 : Nat.card φ.range = 1 := by
    rw [← Subgroup.index_ker, hH.symm.index_eq_card, hHbot, Subgroup.card_bot]
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem pow_eq_self_of_mul_self_eq_one {G : Type*} [Group G] {x : G} (hx : x * x = 1) {m : ℕ}
    (hm : Odd m) : x ^ m = x := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, pow_two, hx, one_pow, one_mul]

theorem exists_odd_lift_commute {A B : Type*} [Group A] [Group B] (κ : A →* B)
    (hκ : Function.Surjective κ) (hker : κ.ker ≤ Subgroup.center A)
    (hcard : Nat.card κ.ker ∣ 2) {a : A} {b : B} (hb : b * κ a = κ a * b)
    (hodd : Odd (orderOf b)) : ∃ g : A, κ g = b ∧ g * a = a * g := by
  have hsq : ∀ k ∈ κ.ker, k * k = 1 := by
    intro k hk
    have h1 : (⟨k, hk⟩ : κ.ker) ^ Nat.card κ.ker = 1 := pow_card_eq_one'
    obtain ⟨c, hc⟩ := hcard
    have h2 : (⟨k, hk⟩ : κ.ker) ^ 2 = 1 := by rw [hc, pow_mul, h1, one_pow]
    have h3 : k ^ 2 = 1 := congrArg Subtype.val h2
    rwa [pow_two] at h3
  obtain ⟨g, hg⟩ := hκ b
  set m := orderOf b with hm
  have hbm : b ^ m = 1 := pow_orderOf_eq_one b
  have hk : g ^ m ∈ κ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hg, hbm]
  have hkk := hsq _ hk
  have hkm : (g ^ m) ^ m = g ^ m := pow_eq_self_of_mul_self_eq_one hkk hodd
  refine ⟨g * (g ^ m)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, mul_one, hg]
  · set g₁ := g * (g ^ m)⁻¹ with hg₁
    have hg₁m : g₁ ^ m = 1 := by
      have hcomm : Commute g (g ^ m)⁻¹ := ((Commute.refl g).pow_right m).inv_right
      rw [hg₁, hcomm.mul_pow, inv_pow, hkm, mul_inv_cancel]
    have hκg₁ : κ g₁ = b := by
      rw [hg₁, map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, mul_one, hg]
    set z := a * g₁ * a⁻¹ * g₁⁻¹ with hz
    have hzker : z ∈ κ.ker := by
      rw [MonoidHom.mem_ker, hz]
      simp only [map_mul, map_inv, hκg₁]
      calc κ a * b * (κ a)⁻¹ * b⁻¹ = b * κ a * (κ a)⁻¹ * b⁻¹ := by rw [← hb]
        _ = 1 := by group
    have hzc : ∀ y, y * z = z * y := fun y => Subgroup.mem_center_iff.mp (hker hzker) y
    have hconj : a * g₁ * a⁻¹ = z * g₁ := by rw [hz]; group
    have hpow : (a * g₁ * a⁻¹) ^ m = 1 := by rw [conj_pow, hg₁m]; group
    have hcz : Commute z g₁ := (hzc g₁).symm
    have hz1 : z = 1 := by
      have h := hpow
      rw [hconj, hcz.mul_pow, hg₁m, mul_one,
        pow_eq_self_of_mul_self_eq_one (hsq z hzker) hodd] at h
      exact h
    have h2 : a * g₁ * a⁻¹ = g₁ := mul_inv_eq_one.mp (hz1 : a * g₁ * a⁻¹ * g₁⁻¹ = 1)
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm

theorem oddCore_centralizer_eq_bot_of_cover {A B : Type*} [Group A] [Finite A] [Group B]
    (κ : A →* B) (hκ : Function.Surjective κ) (hker : κ.ker ≤ Subgroup.center A)
    (hcard : Nat.card κ.ker ∣ 2) {a : A}
    (ha : oddCore ↥(Subgroup.centralizer ({a} : Set A)) = ⊥) :
    oddCore ↥(Subgroup.centralizer ({κ a} : Set B)) = ⊥ := by
  haveI : Finite B := Finite.of_surjective κ hκ
  set CB : Subgroup B := Subgroup.centralizer ({κ a} : Set B) with hCB
  set CA : Subgroup A := Subgroup.centralizer ({a} : Set A) with hCA
  set N : Subgroup B := (oddCore CB).map CB.subtype with hN
  have hNodd : Odd (Nat.card N) := by
    rw [hN, Nat.card_congr ((oddCore CB).equivMapOfInjective _ CB.subtype_injective).toEquiv.symm]
    exact odd_card_oddCore
  have hNn : ∀ x ∈ N, ∀ y ∈ CB, y * x * y⁻¹ ∈ N := by
    rintro _ ⟨x, hx, rfl⟩ y hy
    exact ⟨⟨y, hy⟩ * x * ⟨y, hy⟩⁻¹, (oddCore_normal (G := CB)).conj_mem x hx ⟨y, hy⟩, rfl⟩
  set P : Subgroup A := CA ⊓ N.comap κ with hP
  have hPle : P ≤ CA := inf_le_left
  have hCAmap : ∀ c ∈ CA, κ c ∈ CB := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hc])
  have hPn : (P.subgroupOf CA).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxN⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨CA.mul_mem (CA.mul_mem c.2 x.2) (CA.inv_mem c.2), ?_⟩
    rw [Subgroup.mem_comap] at hxN ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    exact hNn _ hxN _ (hCAmap _ c.2)
  have hPbot : oddCore ↥P = ⊥ :=
    oddCore_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPle)
      (oddCore_eq_bot_of_normal (P.subgroupOf CA) ha)
  set φ : ↥P →* B := κ.comp P.subtype with hφ
  have hφker : φ.ker ≤ Subgroup.center ↥P := by
    intro x hx
    have hxk : (x : A) ∈ κ.ker := hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hxk) (y : A))
  have hφcard : Nat.card φ.ker ∣ 2 := by
    let f : φ.ker →* κ.ker := (P.subtype.comp φ.ker.subtype).codRestrict κ.ker fun x => x.2
    refine (Subgroup.card_dvd_of_injective f fun x y hxy => ?_).trans hcard
    exact Subtype.ext (Subtype.ext (congrArg (fun z : κ.ker => (z : A)) hxy))
  have hφodd : Odd (Nat.card φ.range) := by
    have hle : φ.range ≤ N := by
      rintro _ ⟨x, rfl⟩
      exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp x.2).2
    exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le hle)
  have hrange := range_eq_bot_of_central_two hPbot φ hφker hφcard hφodd
  have hNbot : N = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxN : x ∈ N := hx
    obtain ⟨y, -, rfl⟩ := hx
    have hxc : (y : B) * κ a = κ a * (y : B) := Subgroup.mem_centralizer_singleton_iff.mp y.2
    have hord : Odd (orderOf (y : B)) :=
      Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hxN)
    obtain ⟨g, hg, hga⟩ := exists_odd_lift_commute κ hκ hker hcard hxc hord
    have hgP : g ∈ P := Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hga,
      Subgroup.mem_comap.mpr (hg ▸ hxN)⟩
    have : (y : B) ∈ φ.range := ⟨⟨g, hgP⟩, hg⟩
    rw [hrange, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr this
  exact (Subgroup.map_eq_bot_iff_of_injective (oddCore CB) CB.subtype_injective).mp hNbot

end CFSG.OddStandard.SmallF3.Omega
