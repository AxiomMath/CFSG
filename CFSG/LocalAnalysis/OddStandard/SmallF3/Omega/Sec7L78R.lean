module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78R2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Odd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78ActTw

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec7l78_s_not_cent [Finite G] (hP : Asc82Tab6P) {t : G} {L S : Subgroup G}
    {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B)
    (hsL : Sec7L78Side L (S ⊓ L) B (ASub S B) t) {φ : (Fin 5 → ZMod 2) → G}
    (hφ : Sec7E16Act (L ⊓ normalizer (B : Set G)) B φ) :
    ∃ n ∈ L ⊓ normalizer (B : Set G),
      (g⁻¹ * t * g) * n ≠ n * (g⁻¹ * t * g) := by
  rcases hc.choice with hs_eq | ⟨-, -, -, hbad⟩
  · by_contra hcon
    have hcent : ∀ n ∈ L ⊓ normalizer (B : Set G),
        (g⁻¹ * t * g) * n = n * (g⁻¹ * t * g) := by
      intro n hn
      by_contra hne
      exact hcon ⟨n, hn, hne⟩
    have hzB : z ∈ B :=
      hP.center_le G L hsL.om (S ⊓ L) hsL.syl B hsL.norm hc.ctx.z_mem_centerIn
    have hz_eq : z = t⁻¹ * (g⁻¹ * t * g) := by rw [hs_eq]; group
    have hzcomm : ∀ x ∈ L ⊓ normalizer (B : Set G), x * z = z * x := by
      intro x hx
      have hxt : x * t = t * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hc.ctx.le_centralizer hx.1)
      have hxti : x * t⁻¹ = t⁻¹ * x :=
        ((commute_iff_eq x t).mpr hxt).inv_right.eq
      have hsx : (g⁻¹ * t * g) * x = x * (g⁻¹ * t * g) := hcent x hx
      calc x * z = x * (t⁻¹ * (g⁻¹ * t * g)) := by rw [hz_eq]
        _ = (x * t⁻¹) * (g⁻¹ * t * g) := by group
        _ = (t⁻¹ * x) * (g⁻¹ * t * g) := by rw [hxti]
        _ = t⁻¹ * (x * (g⁻¹ * t * g)) := by group
        _ = t⁻¹ * ((g⁻¹ * t * g) * x) := by rw [← hsx]
        _ = (t⁻¹ * (g⁻¹ * t * g)) * x := by group
        _ = z * x := by rw [hz_eq]
    have hz1 : z = 1 := hφ.cent_N hzB hzcomm
    have h1 : orderOf z = 1 := by rw [hz1, orderOf_one]
    rw [(hc.ctx.pocket).1] at h1
    exact absurd h1 (by norm_num)
  · exact hbad

private theorem sec7l78_le_normalizer_A [Finite G] (hP : Asc82Tab6P)
    {L P' B A : Subgroup G} {c : G} (hs : Sec7L78Side L P' B A c) :
    L ⊓ normalizer (B : Set G) ≤ normalizer (A : Set G) := by
  have hBA : B ≤ A := (le_of_eq hs.inf_eq.symm).trans inf_le_left
  intro n hn
  have hmap : ∀ m ∈ L ⊓ normalizer (B : Set G), ∀ a ∈ A, m * a * m⁻¹ ∈ A := by
    intro m hm a ha
    obtain ⟨u, huA, hucen, b, hbB, rfl⟩ := Sec7L78Side.decomp hP hs a ha
    have hmb : m * b * m⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hm.2 b).mp hbB
    have hmu : m * u * m⁻¹ = u := by
      rw [← hucen m hm]; group
    have heq : m * (u * b) * m⁻¹ = u * (m * b * m⁻¹) := by
      rw [show m * (u * b) * m⁻¹ = (m * u * m⁻¹) * (m * b * m⁻¹) by group, hmu]
    rw [heq]
    exact A.mul_mem huA (hBA hmb)
  refine Subgroup.mem_normalizer_iff.mpr fun a => ⟨hmap n hn a, ?_⟩
  intro ha
  have h := hmap n⁻¹ ((L ⊓ normalizer (B : Set G)).inv_mem hn) (n * a * n⁻¹) ha
  have heq : n⁻¹ * (n * a * n⁻¹) * n = a := by group
  simpa [heq] using h

private theorem sec7l78_sylow_inf_normalizer [Finite G] {L P B A : Subgroup G} {c : G}
    (hs : Sec7L78Side L P B A c) :
    IsSylow2Of P (L ⊓ normalizer (B : Set G)) := by
  have hle : P ≤ L ⊓ normalizer (B : Set G) :=
    le_inf hs.syl.1 ((Subgroup.normal_subgroupOf_iff_le_normalizer hs.norm.1).mp hs.norm.2.2)
  refine ⟨hle, hs.syl.2.1, ?_⟩
  intro h2
  have h := Subgroup.relIndex_mul_relIndex P (L ⊓ normalizer (B : Set G)) L hle inf_le_left
  exact hs.syl.2.2 (h ▸ dvd_mul_of_dvd_left h2 _)

private theorem sec7l78_nu_comm [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B)
    (hsL : Sec7L78Side L (S ⊓ L) B (ASub S B) t) {P' : Subgroup G}
    (hsL' : Sec7L78Side (CFSG.conjugate L g) P'
      (ASub S B ⊓ CFSG.conjugate L g) (ASub S B) (g⁻¹ * t * g))
    {u₀ b₀ ν u : G} (hu₀cen : ∀ n ∈ L ⊓ normalizer (B : Set G), u₀ * n = n * u₀)
    (hs_eq : g⁻¹ * t * g = u₀ * b₀) (hνN : ν ∈ L ⊓ normalizer (B : Set G))
    (hνb : ν * b₀ = b₀ * ν) (hν3 : ν ^ 3 = 1) (huA : u ∈ ASub S B)
    (huN : ∀ n ∈ CFSG.conjugate L g ⊓
      normalizer ((ASub S B ⊓ CFSG.conjugate L g : Subgroup G) : Set G), u * n = n * u) :
    ν * u = u * ν := by
  have hcomm_s : ν * (g⁻¹ * t * g) = (g⁻¹ * t * g) * ν := by
    rw [hs_eq]
    exact (((commute_iff_eq u₀ ν).mpr (hu₀cen ν hνN)).symm.mul_right hνb).eq
  have hnormA : ν ∈ normalizer (ASub S B : Set G) := sec7l78_le_normalizer_A hP hsL hνN
  have hnormL' : ν ∈ normalizer (CFSG.conjugate L g : Set G) :=
    (hc.ctx.conjugate g).cent_le_normalizer h36 ν
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm_s)
  have hodd : Odd (orderOf ν) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hν3)
  exact sec7l78_odd_cent hP hsL' hnormA hnormL' hcomm_s hodd huA huN

theorem sec7l78_exists_r [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72)
    (h76 : Asc82Lemma76) (hP : Asc82Tab6P) (h77a : Asc82Lemma77a) (h77b : Asc82Lemma77b)
    {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B)
    (hne : ASub S B ≠ zpowers t ⊔ B) :
    ∃ r ∈ ASub S B, r ≠ 1 ∧ r ≠ t ∧ r ≠ g⁻¹ * t * g ∧
      (∀ n ∈ L ⊓ normalizer (B : Set G), r * n = n * r) ∧
      ∀ n ∈ CFSG.conjugate L g ⊓
        normalizer ((ASub S B ⊓ CFSG.conjugate L g : Subgroup G) : Set G), r * n = n * r := by
  have hsL := sec7l78_sideL h36 h76 hP hc
  obtain ⟨P', hsL', hMeq⟩ := sec7l78_sideL' h36 h72 h76 hP h77a hc
  have hsA : g⁻¹ * t * g ∈ ASub S B := sec7l78_s_mem_A hP h36 hc
  have hcommA := sec7l78_A_comm_sq h36 h76 hP hc
  obtain ⟨φ, hφ⟩ := sec7l78_act_of_aut_B hP hsL.om hsL.syl hsL.norm
  have hBA : B ≤ ASub S B := (le_of_eq hsL.inf_eq.symm).trans inf_le_left
  have hnotcent := sec7l78_s_not_cent hP hc hsL hφ
  have hSyl : IsSylow2Of (S ⊓ L) (L ⊓ normalizer (B : Set G)) :=
    sec7l78_sylow_inf_normalizer hsL
  obtain ⟨u₀, hu₀A, hu₀cen, b₀, hb₀B, hs_eq⟩ :=
    Sec7L78Side.decomp hP hsL (g⁻¹ * t * g) hsA
  have hb₀A : b₀ ∈ ASub S B := hBA hb₀B
  have hb₀ne : b₀ ≠ 1 := by
    intro h1
    obtain ⟨n, hn, hne'⟩ := hnotcent
    exact hne' (by rw [hs_eq, h1, mul_one]; exact hu₀cen n hn)
  have hPb : ∀ x ∈ S ⊓ L, x * b₀ = b₀ * x := by
    intro x hx
    have hxN : x ∈ L ⊓ normalizer (B : Set G) :=
      ⟨hx.2, (Subgroup.normal_subgroupOf_iff_le_normalizer hsL.norm.1).mp hsL.norm.2.2 hx⟩
    have hxs : x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x := sec7l78_s_cent_P hc x hx
    have hxu : x * u₀⁻¹ = u₀⁻¹ * x :=
      (((commute_iff_eq u₀ x).mpr (hu₀cen x hxN)).symm.inv_right).eq
    have hb₀_eq : b₀ = u₀⁻¹ * (g⁻¹ * t * g) := by rw [hs_eq]; group
    calc x * b₀ = x * (u₀⁻¹ * (g⁻¹ * t * g)) := by rw [hb₀_eq]
      _ = (x * u₀⁻¹) * (g⁻¹ * t * g) := by group
      _ = (u₀⁻¹ * x) * (g⁻¹ * t * g) := by rw [hxu]
      _ = u₀⁻¹ * (x * (g⁻¹ * t * g)) := by group
      _ = u₀⁻¹ * ((g⁻¹ * t * g) * x) := by rw [hxs]
      _ = (u₀⁻¹ * (g⁻¹ * t * g)) * x := by group
      _ = b₀ * x := by rw [hb₀_eq]
  obtain ⟨ν₁, hν₁N, ν₂, hν₂N, hν₁3, hν₂3, hν₁b, hν₂b, hfix⟩ :=
    hφ.stab_lifts hSyl hb₀B hb₀ne hPb
  obtain ⟨r₂, hr₂A, hr₂notin, hr₂cen⟩ := sec7l78_exists_r2 hP hsL hsL' hne
  obtain ⟨u₁, hu₁A, hu₁cen, b, hbB, hr₂_eq⟩ := Sec7L78Side.decomp hP hsL r₂ hr₂A
  have hν₁r₂ : ν₁ * r₂ = r₂ * ν₁ :=
    sec7l78_nu_comm h36 hP hc hsL hsL' hu₀cen hs_eq hν₁N hν₁b hν₁3 hr₂A hr₂cen
  have hν₂r₂ : ν₂ * r₂ = r₂ * ν₂ :=
    sec7l78_nu_comm h36 hP hc hsL hsL' hu₀cen hs_eq hν₂N hν₂b hν₂3 hr₂A hr₂cen
  have hν₁u₁ : ν₁ * u₁ = u₁ * ν₁ := (hu₁cen ν₁ hν₁N).symm
  have hν₂u₁ : ν₂ * u₁ = u₁ * ν₂ := (hu₁cen ν₂ hν₂N).symm
  have hcν₁u₁ : Commute ν₁ u₁ := hν₁u₁
  have hcν₂u₁ : Commute ν₂ u₁ := hν₂u₁
  have hcν₁r₂ : Commute ν₁ r₂ := hν₁r₂
  have hcν₂r₂ : Commute ν₂ r₂ := hν₂r₂
  have hν₁b' : ν₁ * b = b * ν₁ := by
    have hb_eq : b = u₁⁻¹ * r₂ := by rw [hr₂_eq]; group
    rw [hb_eq]
    exact (hcν₁u₁.inv_right.mul_right hcν₁r₂).eq
  have hν₂b' : ν₂ * b = b * ν₂ := by
    have hb_eq : b = u₁⁻¹ * r₂ := by rw [hr₂_eq]; group
    rw [hb_eq]
    exact (hcν₂u₁.inv_right.mul_right hcν₂r₂).eq
  have ne_one_of_notin : ∀ r : G, r ∉ zpowers (g⁻¹ * t * g) → r ≠ 1 := by
    intro r hr h1
    exact hr (by rw [h1]; exact (zpowers (g⁻¹ * t * g)).one_mem)
  have ne_s_of_notin : ∀ r : G, r ∉ zpowers (g⁻¹ * t * g) → r ≠ g⁻¹ * t * g := by
    intro r hr h1
    exact hr (by rw [h1]; exact Subgroup.mem_zpowers _)
  have ne_t_of_cen : ∀ r : G,
      (∀ n ∈ CFSG.conjugate L g ⊓
        normalizer ((ASub S B ⊓ CFSG.conjugate L g : Subgroup G) : Set G), r * n = n * r) →
      r ≠ t := by
    intro r hrc hrt
    obtain ⟨n, hn, hne'⟩ := h77b G t L S z g B hc
    rw [hMeq] at hn
    exact hne' (by rw [← hrt]; exact hrc n hn)
  rcases hfix b hbB hν₁b' hν₂b' with hb1 | hbb₀
  · have hr₂_eq_u₁ : r₂ = u₁ := by rw [hr₂_eq, hb1, mul_one]
    have hrcenN₁ : ∀ n ∈ L ⊓ normalizer (B : Set G), r₂ * n = n * r₂ := by
      intro n hn
      rw [hr₂_eq_u₁]
      exact hu₁cen n hn
    exact ⟨r₂, hr₂A, ne_one_of_notin r₂ hr₂notin, ne_t_of_cen r₂ hr₂cen,
      ne_s_of_notin r₂ hr₂notin, hrcenN₁, hr₂cen⟩
  · have hr_eq : (g⁻¹ * t * g) * r₂ = u₀ * u₁ := by
      rw [hs_eq, hr₂_eq, hbb₀]
      have h1 : b₀ * u₁ = u₁ * b₀ := hcommA.1 b₀ hb₀A u₁ hu₁A
      have h2 : b₀ * b₀ = 1 := hcommA.2 b₀ hb₀A
      calc (u₀ * b₀) * (u₁ * b₀) = u₀ * (b₀ * u₁) * b₀ := by group
        _ = u₀ * (u₁ * b₀) * b₀ := by rw [h1]
        _ = u₀ * u₁ * (b₀ * b₀) := by group
        _ = u₀ * u₁ := by rw [h2, mul_one]
    have hrcenN₁ : ∀ n ∈ L ⊓ normalizer (B : Set G),
        ((g⁻¹ * t * g) * r₂) * n = n * ((g⁻¹ * t * g) * r₂) := by
      intro n hn
      rw [hr_eq]
      calc (u₀ * u₁) * n = u₀ * (u₁ * n) := by group
        _ = u₀ * (n * u₁) := by rw [hu₁cen n hn]
        _ = (u₀ * n) * u₁ := by group
        _ = (n * u₀) * u₁ := by rw [hu₀cen n hn]
        _ = n * (u₀ * u₁) := by group
    have hrcenN₂ : ∀ n ∈ CFSG.conjugate L g ⊓
        normalizer ((ASub S B ⊓ CFSG.conjugate L g : Subgroup G) : Set G),
        ((g⁻¹ * t * g) * r₂) * n = n * ((g⁻¹ * t * g) * r₂) := by
      intro n hn
      have hsn : (g⁻¹ * t * g) * n = n * (g⁻¹ * t * g) :=
        (Subgroup.mem_centralizer_iff.mp hsL'.c_cent n hn.1).symm
      calc ((g⁻¹ * t * g) * r₂) * n = (g⁻¹ * t * g) * (r₂ * n) := by group
        _ = (g⁻¹ * t * g) * (n * r₂) := by rw [hr₂cen n hn]
        _ = ((g⁻¹ * t * g) * n) * r₂ := by group
        _ = (n * (g⁻¹ * t * g)) * r₂ := by rw [hsn]
        _ = n * ((g⁻¹ * t * g) * r₂) := by group
    have hrsnotin : (g⁻¹ * t * g) * r₂ ∉ zpowers (g⁻¹ * t * g) := by
      intro hmem
      apply hr₂notin
      have h2 : r₂ = (g⁻¹ * t * g)⁻¹ * ((g⁻¹ * t * g) * r₂) := by group
      rw [h2]
      exact (zpowers (g⁻¹ * t * g)).mul_mem
        ((zpowers (g⁻¹ * t * g)).inv_mem (Subgroup.mem_zpowers _)) hmem
    exact ⟨(g⁻¹ * t * g) * r₂, (ASub S B).mul_mem hsA hr₂A, ne_one_of_notin _ hrsnotin,
      ne_t_of_cen _ hrcenN₂, ne_s_of_notin _ hrsnotin, hrcenN₁, hrcenN₂⟩

end CFSG.OddStandard.SmallF3.Omega
