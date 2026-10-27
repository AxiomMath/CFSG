module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Ca
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Cc

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10C_pgroup_zpowers_of_sq {x : G} (hx : x * x = 1) : IsPGroup 2 (zpowers x) := by
  have hd : orderOf x ∣ 2 ^ 1 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hx)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers]; exact hi)

theorem sec10C_part2 [Finite G] (h : Asc82Res10a) (hf : Asc82Facts10) (hb : Asc82Basic10)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} {g : G}
    (hctx : Sec109Ctx G t L S z K1 K2 g) (hCS : IsStrClosedModZ t z S) {k y : G}
    (hk : k ∈ centralizer ({z} : Set G)) (hy : y ∈ S) (hs : k⁻¹ * t * k = y * g) : False := by
  have hctx' : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  obtain ⟨hpsp, htC, htL, htS, hSN, hsyl⟩ := hb G t L S z hctx.toSec10Z
  obtain ⟨ht2, hz2, -, -, -, htz⟩ := sec10D_basic hb hctx'
  obtain ⟨s, hsdef⟩ : ∃ s, s = k⁻¹ * t * k := ⟨_, rfl⟩
  have hsyg : s = y * g := hsdef.trans hs
  have hs2 : s * s = 1 := by
    rw [hsdef]
    calc k⁻¹ * t * k * (k⁻¹ * t * k) = k⁻¹ * (t * t) * k := by group
      _ = 1 := by rw [ht2]; group
  have hgz : g * z = z * g := sec10D_g_comm_z hz2 hctx
  have hyz : y * z = z * y := hctx.central y hy
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hy)
  have hsz : s * z = z * s := by
    rw [hsyg]
    calc y * g * z = y * (g * z) := by rw [mul_assoc]
      _ = y * (z * g) := by rw [hgz]
      _ = (y * z) * g := by rw [← mul_assoc]
      _ = (z * y) * g := by rw [hyz]
      _ = z * (y * g) := by rw [mul_assoc]
  have hyt' : y⁻¹ * t * y = t := by
    calc y⁻¹ * t * y = y⁻¹ * (t * y) := by rw [mul_assoc]
      _ = y⁻¹ * (y * t) := by rw [hyt]
      _ = t := by group
  have hswap : s⁻¹ * t * s = t * z := by
    rw [hsyg]
    calc (y * g)⁻¹ * t * (y * g) = g⁻¹ * (y⁻¹ * t * y) * g := by group
      _ = g⁻¹ * t * g := by rw [hyt']
      _ = t * z := hctx.swap
  have hsN : s ∈ normalizer (S : Set G) := by
    rw [hsyg]
    exact (normalizer (S : Set G)).mul_mem (Subgroup.le_normalizer hy) hctx.norm
  obtain ⟨r, hrS, hr2, hrty, hne, hX, hconj⟩ := sec10C_exists_A2 h.l107c hctx
  have hAn : IsNormalE32In S (secA t S L) := (hX _).mpr (Or.inl rfl)
  have hAn' := (Subgroup.normal_subgroupOf_iff hAn.1).mp hAn.2.2
  have hsA : ∀ a ∈ secA t S L, s⁻¹ * a * s ∈ secA2 t r K1 K2 := by
    intro a ha
    rw [← hconj]
    refine mem_conjugate_iff'.mpr ?_
    have h1 : y⁻¹ * a * y⁻¹⁻¹ ∈ secA t S L := hAn' a y⁻¹ ha (S.inv_mem hy)
    have e : g * (s⁻¹ * a * s) * g⁻¹ = y⁻¹ * a * y⁻¹⁻¹ := by rw [hsyg]; group
    rw [e]
    exact h1
  obtain ⟨x, hxS, hx2, hxz⟩ := hf.factsC.y G t L S z K1 K2 hctx' hpsp hSN
    (h.l106 G t L S z K1 K2 hctx') hsyl r hrS hr2 hrty hne hX s hsN hs2 hsz hswap hsA
  have hxC : x ∈ centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central x hxS)
  obtain ⟨y', hy'def⟩ : ∃ y', y' = x⁻¹ * s * x := ⟨_, rfl⟩
  have hy'2 : y' * y' = 1 := by
    rw [hy'def]
    calc x⁻¹ * s * x * (x⁻¹ * s * x) = x⁻¹ * (s * s) * x := by group
      _ = 1 := by rw [hs2]; group
  have hcomm : y' * s = s * y' := by
    have hq : (y' * s) * (y' * s) = 1 := by rw [hy'def]; exact hx2
    have h1 : y' * s * y' = s := by
      calc y' * s * y' = y' * s * y' * (s * s) := by rw [hs2, mul_one]
        _ = (y' * s * (y' * s)) * s := by group
        _ = s := by rw [hq, one_mul]
    calc y' * s = y' * s * (y' * y') := by rw [hy'2, mul_one]
      _ = (y' * s * y') * y' := by group
      _ = s * y' := by rw [h1]
  have hcz_x : Commute z x := (hctx.central x hxS).symm
  have hcz_s : Commute z s := hsz.symm
  have hcz_y' : Commute z y' := by
    rw [hy'def]
    exact (hcz_x.inv_right.mul_right hcz_s).mul_right hcz_x
  have hcz_k : Commute z k := (Subgroup.mem_centralizer_singleton_iff.mp hk).symm
  have hk_s : k * s * k⁻¹ = t := by rw [hsdef]; group
  obtain ⟨y'', hy''def⟩ : ∃ y'', y'' = k * y' * k⁻¹ := ⟨_, rfl⟩
  have hy''2 : y'' * y'' = 1 := by
    rw [hy''def]
    calc k * y' * k⁻¹ * (k * y' * k⁻¹) = k * (y' * y') * k⁻¹ := by group
      _ = 1 := by rw [hy'2]; group
  have hy''t : y'' * t = t * y'' := by
    rw [hy''def, ← hk_s]
    calc k * y' * k⁻¹ * (k * s * k⁻¹) = k * (y' * s) * k⁻¹ := by group
      _ = k * (s * y') * k⁻¹ := by rw [hcomm]
      _ = k * s * k⁻¹ * (k * y' * k⁻¹) := by group
  have hy''z : Commute z y'' := by
    rw [hy''def]
    exact (hcz_k.mul_right hcz_y').mul_right hcz_k.inv_right
  have hSz : S ≤ centralizer ({z} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central u hu)
  have hSX : IsSylow2Of S (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) :=
    sec10C_isSylow2Of_mono hctx.sylow (le_inf hctx.sylow.1 hSz) inf_le_left
  have hy''X : y'' ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hy''t,
      Subgroup.mem_centralizer_singleton_iff.mpr hy''z.eq.symm⟩
  obtain ⟨Q, hQ, hyQ⟩ := exists_isSylow2Of_ge (sec10C_pgroup_zpowers_of_sq hy''2)
    (Subgroup.zpowers_le.mpr hy''X)
  obtain ⟨a, haX, haQ⟩ := IsSylow2Of.exists_conj_mem hSX hQ
  have hy'''S : a⁻¹ * y'' * a ∈ S := (haQ y'').mp (hyQ (Subgroup.mem_zpowers y''))
  have hat : a * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp haX.1
  have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp haX.2
  have hκ : k * x * k⁻¹ * a ∈ centralizer ({z} : Set G) :=
    (centralizer ({z} : Set G)).mul_mem ((centralizer ({z} : Set G)).mul_mem
      ((centralizer ({z} : Set G)).mul_mem hk hxC) ((centralizer ({z} : Set G)).inv_mem hk)) haX.2
  have hκconj : (k * x * k⁻¹ * a)⁻¹ * t * (k * x * k⁻¹ * a) = a⁻¹ * y'' * a := by
    rw [hy''def, hy'def, hsdef]
    group
  have hy''eq : y'' = t ∨ y'' = t * z := by
    rcases hCS _ hκ (by rw [hκconj]; exact Subgroup.mem_sup_left hy'''S) with e | e
    · rw [hκconj] at e
      left
      calc y'' = a * (a⁻¹ * y'' * a) * a⁻¹ := by group
        _ = a * t * a⁻¹ := by rw [e]
        _ = t := by rw [hat]; group
    · rw [hκconj] at e
      right
      calc y'' = a * (a⁻¹ * y'' * a) * a⁻¹ := by group
        _ = a * (t * z) * a⁻¹ := by rw [e]
        _ = (a * t) * z * a⁻¹ := by group
        _ = (t * a) * z * a⁻¹ := by rw [hat]
        _ = t * (a * z) * a⁻¹ := by group
        _ = t * (z * a) * a⁻¹ := by rw [haz]
        _ = t * z := by group
  have hkz : k⁻¹ * z * k = z := by
    have e : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp hk
    calc k⁻¹ * z * k = k⁻¹ * (z * k) := by rw [mul_assoc]
      _ = k⁻¹ * (k * z) := by rw [e]
      _ = z := by group
  have e1 : y' = k⁻¹ * y'' * k := by rw [hy''def]; group
  apply hxz
  have e2 : x⁻¹ * s * x * s = y' * s := by rw [hy'def]
  rw [e2]
  rcases hy''eq with e | e
  · have e3 : y' = s := by rw [e1, e, ← hsdef]
    rw [e3, hs2]
    exact Subgroup.one_mem _
  · have e3 : y' = s * z := by
      rw [e1, e]
      calc k⁻¹ * (t * z) * k = (k⁻¹ * t * k) * (k⁻¹ * z * k) := by group
        _ = s * z := by rw [← hsdef, hkz]
    have e4 : s * z * s = z := by
      calc s * z * s = z * s * s := by rw [hsz]
        _ = z := by rw [mul_assoc, hs2, mul_one]
    rw [e3, e4]
    exact Subgroup.mem_zpowers z

end CFSG.OddStandard.SmallF3.Omega
