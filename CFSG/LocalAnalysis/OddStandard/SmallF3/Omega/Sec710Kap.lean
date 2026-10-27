module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec710Rho
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Comb5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec710_mem_A [Finite G] (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) {x : G} :
    x ∈ ASub S B ↔ ∃ j : ℤ, ∃ b ∈ B, x = t ^ j * b := by
  have hcomm : ∀ b ∈ B, Commute b t := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (hc.ctx.sylow.1 (hc.normalE16.1 hb).1)
  let K : Subgroup G :=
    { carrier := {x : G | ∃ k : ℤ, ∃ b ∈ B, x = t ^ k * b}
      one_mem' := ⟨0, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨k, b, hb, rfl⟩ ⟨l, c, hcB, rfl⟩
        refine ⟨k + l, b * c, B.mul_mem hb hcB, ?_⟩
        have hbcomm : Commute b (t ^ l) := (hcomm b hb).zpow_right l
        calc (t ^ k * b) * (t ^ l * c) = t ^ k * (b * t ^ l) * c := by group
          _ = t ^ k * (t ^ l * b) * c := by rw [hbcomm.eq]
          _ = (t ^ k * t ^ l) * (b * c) := by group
          _ = t ^ (k + l) * (b * c) := by rw [← zpow_add t k l]
      inv_mem' := by
        rintro x ⟨k, b, hb, rfl⟩
        refine ⟨-k, b⁻¹, B.inv_mem hb, ?_⟩
        have hbcomm : Commute b⁻¹ (t ^ (-k)) := (hcomm b hb).inv_left.zpow_right (-k)
        calc (t ^ k * b)⁻¹ = b⁻¹ * t ^ (-k) := by rw [mul_inv_rev, zpow_neg]
          _ = t ^ (-k) * b⁻¹ := hbcomm.eq }
  have hsupK : Subgroup.zpowers t ⊔ B ≤ K := by
    refine sup_le ?_ ?_
    · intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ⟨k, 1, B.one_mem, by simp⟩
    · intro b hb
      exact ⟨0, b, hb, by simp⟩
  rw [h78 G t L S z g B hc]
  refine ⟨fun hx => hsupK hx, fun ⟨j, b, hb, hx⟩ => ?_⟩
  rw [hx]
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers t j) hb

theorem sec710_comm_mem_B [Finite G] (hP : Asc82Tab6P) (h78 : Asc82Lemma78)
    (h710c : Asc82Lemma710c) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {k : G}
    (hk : k ∈ MSub S B ⊓ centralizer (B : Set G)) : k * t * k⁻¹ * t⁻¹ ∈ B := by
  have htA : t ∈ ASub S B := sec79_t_mem_A hc
  have hconjA : k * t * k⁻¹ ∈ ASub S B :=
    (Subgroup.mem_normalizer_iff.mp hk.1 t).mp htA
  obtain ⟨j, b, hb, hjb⟩ := (sec710_mem_A h78 hc).mp hconjA
  have hmod : t ^ (j % 2) = t ^ j := by
    simpa [hc.ctx.involution] using zpow_mod_orderOf t j
  rcases Int.emod_two_eq_zero_or_one j with h0 | h1
  · have htjeq : t ^ j = 1 := by rw [← hmod, h0, zpow_zero]
    have hb' : k * t * k⁻¹ = b := by rw [hjb, htjeq, one_mul]
    exfalso
    have ht_eq : t = k⁻¹ * b * k := by rw [← hb']; group
    have hBM : B ≤ MSub S B := (sec79_B_le_A hc).trans Subgroup.le_normalizer
    have hnorm : (B.subgroupOf (MSub S B)).Normal := (h710c G t L S z g B hc).2.2
    have hkinvM : k⁻¹ ∈ MSub S B := (MSub S B).inv_mem hk.1
    have htB : t ∈ B := by
      rw [ht_eq]
      simpa using (Subgroup.normal_subgroupOf_iff hBM).mp hnorm b k⁻¹ hb hkinvM
    have htL : t ∈ L := (hc.normalE16.1 htB).2
    have htC : t ∈ centralizer (L : Set G) := hc.ctx.t_mem_centralizer
    have htZ : t ∈ centerIn L :=
      Subgroup.mem_map.mpr ⟨⟨t, htL⟩,
        Subgroup.mem_center_iff.mpr fun y =>
          Subtype.ext (Subgroup.mem_centralizer_iff.mp htC (y : G) y.2), rfl⟩
    have ht1 : t = 1 := Subgroup.mem_bot.mp (hP.center_triv G L hc.ctx.isOm6P ▸ htZ)
    have h2 : orderOf t = 2 := hc.ctx.involution
    rw [ht1, orderOf_one] at h2
    norm_num at h2
  · have htjeq : t ^ j = t := by rw [← hmod, h1, zpow_one]
    have hkeq : k * t * k⁻¹ = t * b := by rw [hjb, htjeq]
    have hbcomm : b * t = t * b :=
      Subgroup.mem_centralizer_singleton_iff.mp (hc.ctx.sylow.1 (hc.normalE16.1 hb).1)
    rw [hkeq]
    have hbt : t * b * t⁻¹ = b := by rw [← hbcomm]; group
    rw [hbt]
    exact hb

theorem sec710_exists_kap [Finite G] (hP : Asc82Tab6P) (h78 : Asc82Lemma78)
    (h710c : Asc82Lemma710c) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    ∃ κ : ↥(MSub S B ⊓ centralizer (B : Set G)) →* ↥B,
      ∀ k : ↥(MSub S B ⊓ centralizer (B : Set G)),
        (κ k : G) = (k : G) * t * (k : G)⁻¹ * t⁻¹ := by
  haveI : IsMulCommutative (B : Subgroup G) := hc.normalE16.2.1.1.1
  refine ⟨MonoidHom.mk' (fun k => ⟨(k : G) * t * (k : G)⁻¹ * t⁻¹,
    sec710_comm_mem_B hP h78 h710c hc k.2⟩) ?_, fun k => rfl⟩
  intro k₁ k₂
  apply Subtype.ext
  change (k₁ : G) * (k₂ : G) * t * ((k₁ : G) * (k₂ : G))⁻¹ * t⁻¹ =
    ((k₁ : G) * t * (k₁ : G)⁻¹ * t⁻¹) * ((k₂ : G) * t * (k₂ : G)⁻¹ * t⁻¹)
  set b₁ : G := (k₁ : G) * t * (k₁ : G)⁻¹ * t⁻¹ with hb₁def
  set b₂ : G := (k₂ : G) * t * (k₂ : G)⁻¹ * t⁻¹ with hb₂def
  have hb₁ : b₁ ∈ B := by
    rw [hb₁def]
    exact sec710_comm_mem_B hP h78 h710c hc k₁.2
  have hb₂ : b₂ ∈ B := by
    rw [hb₂def]
    exact sec710_comm_mem_B hP h78 h710c hc k₂.2
  have hcent : (k₁ : G) * b₂ * (k₁ : G)⁻¹ = b₂ := by
    have h := Subgroup.mem_centralizer_iff.mp k₁.2.2 b₂ hb₂
    rw [← h]
    group
  have h2 : (k₂ : G) * t * (k₂ : G)⁻¹ = b₂ * t := by rw [hb₂def]; group
  have hL : (k₁ : G) * (k₂ : G) * t * ((k₁ : G) * (k₂ : G))⁻¹ * t⁻¹ =
      (k₁ : G) * ((k₂ : G) * t * (k₂ : G)⁻¹) * (k₁ : G)⁻¹ * t⁻¹ := by group
  rw [hL, h2]
  rw [show (k₁ : G) * (b₂ * t) * (k₁ : G)⁻¹ * t⁻¹ =
      (k₁ : G) * b₂ * (k₁ : G)⁻¹ * ((k₁ : G) * t * (k₁ : G)⁻¹ * t⁻¹) from by group]
  rw [← hb₁def, hcent]
  exact (setLike_mul_comm hb₁ hb₂).symm

theorem sec710_kap_eq_one_iff [Finite G] (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G}
    {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B)
    {κ : ↥(MSub S B ⊓ centralizer (B : Set G)) →* ↥B}
    (hκ : ∀ k : ↥(MSub S B ⊓ centralizer (B : Set G)),
      (κ k : G) = (k : G) * t * (k : G)⁻¹ * t⁻¹)
    (k : ↥(MSub S B ⊓ centralizer (B : Set G))) :
    κ k = 1 ↔ (k : G) ∈ centralizer (ASub S B : Set G) := by
  constructor
  · intro hk1
    have hkt : Commute (k : G) t := by
      have h1 : (k : G) * t * (k : G)⁻¹ * t⁻¹ = 1 := by
        have h := hκ k
        rw [hk1] at h
        simpa using h.symm
      calc (k : G) * t = ((k : G) * t * (k : G)⁻¹ * t⁻¹) * (t * (k : G)) := by group
        _ = 1 * (t * (k : G)) := by rw [h1]
        _ = t * (k : G) := by group
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    obtain ⟨j, b, hb, rfl⟩ := (sec710_mem_A h78 hc).mp ha
    have hbk : b * (k : G) = (k : G) * b :=
      Subgroup.mem_centralizer_iff.mp k.2.2 b hb
    have hcomm : Commute (k : G) (t ^ j * b) := (hkt.zpow_right j).mul_right hbk.symm
    exact hcomm.eq.symm
  · intro hk
    apply Subtype.ext
    rw [hκ k]
    have htk : t * (k : G) = (k : G) * t :=
      Subgroup.mem_centralizer_iff.mp hk t (sec79_t_mem_A hc)
    show (k : G) * t * (k : G)⁻¹ * t⁻¹ = 1
    rw [← htk]
    group

theorem sec710_kap_surj [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) (hF : Asc82AutFacts)
    (hP7 : Asc82Tab7P) (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710b : Asc82Lemma710b)
    (h710c : Asc82Lemma710c) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B)
    {κ : ↥(MSub S B ⊓ centralizer (B : Set G)) →* ↥B}
    (hκ : ∀ k : ↥(MSub S B ⊓ centralizer (B : Set G)),
      (κ k : G) = (k : G) * t * (k : G)⁻¹ * t⁻¹) : Function.Surjective κ := by
  classical
  have hL : IsOm6P L := hc.ctx.isOm6P
  have hNM : L ⊓ MSub S B = L ⊓ normalizer (B : Set G) := sec710_inf_M_eq h78 h710c hc
  obtain ⟨φ, hφ⟩ := (hP.aut_B G L hL (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B hc.normalE16).2.2
  let X : Subgroup G := (B.subtype.comp κ).range
  have hXinv : ∀ n ∈ L ⊓ normalizer (B : Set G), ∀ x ∈ X, n * x * n⁻¹ ∈ X := by
    intro n hn x hx
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hx
    have hk' : ((κ k : ↥B) : G) = x := hk
    have hnL : n ∈ L := (Subgroup.mem_inf.mp hn).1
    have hnNorm : n ∈ normalizer (B : Set G) := (Subgroup.mem_inf.mp hn).2
    have hnM : n ∈ MSub S B := by
      rw [← hNM] at hn
      exact (Subgroup.mem_inf.mp hn).2
    have hkM : (k : G) ∈ MSub S B := k.2.1
    have hkC : (k : G) ∈ centralizer (B : Set G) := k.2.2
    have hnt : n * t * n⁻¹ = t := by
      have hnc : Commute n t :=
        Subgroup.mem_centralizer_singleton_iff.mp (hc.ctx.le_centralizer hnL)
      rw [hnc.eq]; group
    have hk'C : n * (k : G) * n⁻¹ ∈ centralizer (B : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
      have hnb : n⁻¹ * b * n ∈ B := (Subgroup.mem_normalizer_iff''.mp hnNorm b).mp hb
      have hkcb : (n⁻¹ * b * n) * (k : G) = (k : G) * (n⁻¹ * b * n) :=
        Subgroup.mem_centralizer_iff.mp hkC (n⁻¹ * b * n) hnb
      calc b * (n * (k : G) * n⁻¹)
          = n * (n⁻¹ * b * n) * (k : G) * n⁻¹ := by group
        _ = n * ((n⁻¹ * b * n) * (k : G)) * n⁻¹ := by group
        _ = n * ((k : G) * (n⁻¹ * b * n)) * n⁻¹ := by rw [hkcb]
        _ = (n * (k : G) * n⁻¹) * b := by group
    have hk'M : n * (k : G) * n⁻¹ ∈ MSub S B :=
      (MSub S B).mul_mem ((MSub S B).mul_mem hnM hkM) ((MSub S B).inv_mem hnM)
    let k' : ↥(MSub S B ⊓ centralizer (B : Set G)) :=
      ⟨n * (k : G) * n⁻¹, hk'M, hk'C⟩
    refine MonoidHom.mem_range.mpr ⟨k', ?_⟩
    have hκ' := hκ k'
    show (κ k' : G) = n * x * n⁻¹
    rw [hκ', ← hk', hκ k]
    change (n * (k : G) * n⁻¹) * t * (n * (k : G) * n⁻¹)⁻¹ * t⁻¹ =
      n * ((k : G) * t * (k : G)⁻¹ * t⁻¹) * n⁻¹
    conv_lhs => rw [← hnt]
    group
  by_cases htriv : ∃ k : ↥(MSub S B ⊓ centralizer (B : Set G)), κ k ≠ 1
  · obtain ⟨k₀, hk₀⟩ := htriv
    have hx0ne : (κ k₀ : G) ≠ 1 := fun h => hk₀ (Subtype.ext h)
    have hcl := closure_conj_eq_of_permModule hφ inf_le_right (κ k₀).2 hx0ne
    have hBX : B ≤ X := by
      rw [hcl]
      rw [Subgroup.closure_le]
      rintro y ⟨n, hn, rfl⟩
      exact hXinv n hn (κ k₀ : G) (MonoidHom.mem_range.mpr ⟨k₀, rfl⟩)
    intro b
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (hBX b.2)
    exact ⟨k, Subtype.ext hk⟩
  · push Not at htriv
    have hKle : MSub S B ⊓ centralizer (B : Set G) ≤ centralizer ({t} : Set G) := by
      intro k hk
      have hk1 : κ ⟨k, hk⟩ = 1 := htriv ⟨k, hk⟩
      have h1 : k * t * k⁻¹ * t⁻¹ = 1 := by
        have h := hκ ⟨k, hk⟩
        rw [hk1] at h
        simpa using h.symm
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc k * t = (k * t * k⁻¹ * t⁻¹) * (t * k) := by group
        _ = 1 * (t * k) := by rw [h1]
        _ = t * k := by group
    have hLMle : L ⊓ MSub S B ≤ centralizer ({t} : Set G) :=
      inf_le_left.trans hc.ctx.le_centralizer
    have hMle : MSub S B ≤ centralizer ({t} : Set G) := by
      rw [sec710_M_eq_K_sup_N h36 hP hF hP7 h78 h710b h710c hc]
      exact sup_le hKle hLMle
    obtain ⟨n, hn, hne⟩ := h77b G t L S z g B hc
    exfalso
    exact hne (Subgroup.mem_centralizer_singleton_iff.mp (hMle hn.2)).symm

end CFSG.OddStandard.SmallF3.Omega
