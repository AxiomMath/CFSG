module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Props
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

@[expose] def Kz {G : Type} [Group G] (S : Subgroup G) : Subgroup G :=
  Subgroup.closure {g : G | g ∈ Subgroup.centralizer (centerOf S : Set G) ∧ g ^ 3 = 1}

section Generic

variable {G : Type} [Group G] [Finite G]

theorem false_of_commuting_copy (he : CFSG.Assembly.evenRank G ≤ 2) {X K K' : Subgroup G}
    (hX : pCoreOf 2 X ≠ ⊥) (hKX : K ≤ X) (hK'X : K' ≤ X) (hcomm : ⁅K, K'⁆ = ⊥)
    (hrank : ∃ E : Subgroup G, E ≤ K ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9)
    (h3 : 3 ∣ Nat.card K')
    (hZ : ∀ x ∈ K', (∀ y ∈ K', y * x = x * y) → x ^ 3 = 1 → x = 1) : False := by
  obtain ⟨E₉, hE₉K, hE₉, hE₉card⟩ := hrank
  obtain ⟨E, hEle, hE, hEcard⟩ := Unc25G2.exists_elemAbelian_card_pow_succ_of_commuting
    Nat.prime_three hcomm hE₉K hE₉ (n := 2) (by rw [hE₉card]; norm_num) hZ h3
  exact Unc25G2.false_of_isElemAbelian_card_cube he hX (hEle.trans (sup_le hKX hK'X))
    Nat.prime_three (by norm_num) hE (by rw [hEcard])

theorem mem_normalizer_Kz {S : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (S : Set G)) :
    y ∈ Subgroup.normalizer (Kz S : Set G) := by
  apply normalizer_closure_of_forall
  intro g hg
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : y⁻¹ * w * y ∈ centerOf S := inv_conj_mem_centerOf hy hw
    have hc := Subgroup.mem_centralizer_iff.mp hg.1 _ hw'
    calc w * (y * g * y⁻¹) = y * ((y⁻¹ * w * y) * g) * y⁻¹ := by group
      _ = y * (g * (y⁻¹ * w * y)) * y⁻¹ := by rw [hc]
      _ = (y * g * y⁻¹) * w := by group
  · rw [conj_pow, hg.2]
    group

end Generic

section Config

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs) {t zK : G}

theorem t_mul_self (hf : Facts2511 N t zK) : t * t = 1 := by
  have := hf.t_sq
  rwa [sq] at this

theorem t_mem_center (hf : Facts2511 N t zK) : t ∈ centerOf N.S := by
  rw [hf.centerS_z]
  exact Subgroup.subset_closure (by simp)

theorem zK_mem_center (hf : Facts2511 N t zK) : zK ∈ centerOf N.S := by
  rw [hf.centerS_zK]
  exact Subgroup.subset_closure (by simp)

theorem zK_mul_self (hf : Facts2511 N t zK) : zK * zK = 1 := by
  have := hf.centerS_E4.1.2 zK (zK_mem_center N hf)
  rwa [sq] at this

theorem zK_ne_one (hf : Facts2511 N t zK) : zK ≠ 1 := by
  intro h1
  have hcard := hf.centerS_E4.2
  have hle : centerOf N.S ≤ Subgroup.zpowers t := by
    rw [hf.centerS_zK, Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact Subgroup.mem_zpowers _
    · rw [h1]
      exact Subgroup.one_mem _
  have h2 : Nat.card (Subgroup.zpowers t) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hf.t_sq)
  have := Subgroup.card_le_of_le hle
  omega

theorem mem_centralizer_centerOf_iff (hf : Facts2511 N t zK) {g : G} :
    g ∈ Subgroup.centralizer (centerOf N.S : Set G) ↔ g * t = t * g ∧ g * zK = zK * g := by
  constructor
  · intro hg
    have h1 := (Subgroup.mem_centralizer_iff.mp hg) t (t_mem_center N hf)
    have h2 := (Subgroup.mem_centralizer_iff.mp hg) zK (zK_mem_center N hf)
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [hf.centerS_zK] at hw
    have hle : Subgroup.closure ({t, zK} : Set G) ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr h1.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr h2.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

theorem H_le_normalizer_K (h : Lv2513 N t zK) (F : K33Facts N.K) :
    N.H ≤ Subgroup.normalizer (N.K : Set G) := by
  have hsimple : IsSimpleGroup ↥N.K := h.facts258.simple
  have hZK : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  have hK0 : N.K0 = N.K := by
    rcases h.facts254.shape with h1 | ⟨s, hsS, hne, hK0, hcomm⟩
    · exact h1
    · exfalso
      refine false_of_commuting_copy hs.setting.qtke.2.2 (X := N.H) N.tuple.gamma0.isGamma.1
        N.K_le_H ?_ hcomm F.rank ?_ ?_
      · exact le_sup_right.trans (hK0 ▸ N.K0_le_H)
      · rw [BenderBranch.card_conjugate]
        rcases F.card with h3 | h3 <;> rw [h3] <;> norm_num
      · intro x hx hxc hx3
        have hk : s * x * s⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hx
        have hkc : ∀ w ∈ N.K, (s * x * s⁻¹) * w = w * (s * x * s⁻¹) := by
          intro w hw
          have hw' : s⁻¹ * w * s ∈ CFSG.conjugate N.K s := by
            rw [BenderBranch.mem_conjugate_iff]
            simpa [mul_assoc] using hw
          have := hxc _ hw'
          calc (s * x * s⁻¹) * w = s * (x * (s⁻¹ * w * s)) * s⁻¹ := by group
            _ = s * ((s⁻¹ * w * s) * x) * s⁻¹ := by rw [this]
            _ = w * (s * x * s⁻¹) := by group
        have h1 : s * x * s⁻¹ = 1 := hZK _ hk hkc
        calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
          _ = 1 := by rw [h1]; group
  rw [← hK0]
  exact N.H_le_normalizer_K0

theorem centralizer_t_le_normalizer_K (h : Lv2513 N t zK) (F : K33Facts N.K) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G) := by
  have hf := h.facts2511
  have hsimple : IsSimpleGroup ↥N.K := h.facts258.simple
  have hZK : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  have ht2 := t_mul_self N hf
  have hne : Subgroup.zpowers t ≠ ⊥ := by
    intro hbot
    apply hf.t_ne_one
    have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  have hle : Subgroup.zpowers t ≤ N.SC := Subgroup.zpowers_le.mpr hf.t_mem
  have hnorm : N.S ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    rw [normalizer_zpowers_eq_centralizer ht2]
    intro s hs'
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (t_mem_center N hf).2 s hs'
  have hcomp : IsComponentIn N.K (Subgroup.centralizer ({t} : Set G)) := by
    obtain ⟨-, -, hc | ⟨-, ⟨e6⟩, -⟩⟩ := h.concl256 (Subgroup.zpowers t) hne hle hnorm
    · rwa [normalizer_zpowers_eq_centralizer ht2] at hc
    · exfalso
      have : Nat.card N.K = 360 := (Nat.card_congr e6.toEquiv).trans card_alt_six
      rcases F.card with h1 | h1 <;> omega
  intro g hg
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
  by_contra hne'
  have hKg : IsComponentIn (CFSG.conjugate N.K g) (Subgroup.centralizer ({t} : Set G)) :=
    Unc25G2.isComponentIn_conjugate hcomp hg
  have hcomm : ⁅N.K, CFSG.conjugate N.K g⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hcomp hKg).resolve_left fun h' => hne' h'.symm
  refine false_of_commuting_copy hs.setting.qtke.2.2 hf.gammaU.isGamma.1 hcomp.1 hKg.1 hcomm
    F.rank ?_ ?_
  · rw [BenderBranch.card_conjugate]
    rcases F.card with h3 | h3 <;> rw [h3] <;> norm_num
  · intro x hx hxc hx3
    have hk : g * x * g⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hx
    have hkc : ∀ w ∈ N.K, (g * x * g⁻¹) * w = w * (g * x * g⁻¹) := by
      intro w hw
      have hw' : g⁻¹ * w * g ∈ CFSG.conjugate N.K g := by
        rw [BenderBranch.mem_conjugate_iff]
        simpa [mul_assoc] using hw
      have := hxc _ hw'
      calc (g * x * g⁻¹) * w = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by rw [this]
        _ = w * (g * x * g⁻¹) := by group
    have h1 : g * x * g⁻¹ = 1 := hZK _ hk hkc
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

theorem mem_K_of_pow_three (h : Lv2513 N t zK) (F : K33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G)) {g : G}
    (hg : g ∈ Subgroup.centralizer ({t} : Set G)) (hg3 : g ^ 3 = 1) : g ∈ N.K := by
  have hf := h.facts2511
  have hsimple : IsSimpleGroup ↥N.K := h.facts258.simple
  have hZK : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  have hgN : g ∈ Subgroup.normalizer (N.K : Set G) := hKt hg
  set φ : MulAut ↥N.K := conjAct N.K ⟨g, hgN⟩ with hφ
  have hφ3 : φ ^ 3 = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨g, hgN⟩ : Subgroup.normalizer (N.K : Set G)) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hg3
    rw [this, map_one]
  obtain ⟨k, hk⟩ := h.facts258.out_two φ
  have hcop : Nat.Coprime (2 ^ k) (orderOf φ) :=
    Nat.Coprime.pow_left k
      (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hφ3) (by norm_num))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hφin : φ ∈ (MulAut.conj : ↥N.K →* MulAut ↥N.K).range := by
    rw [← hm]
    exact Subgroup.pow_mem _ hk m
  obtain ⟨a, ha⟩ := hφin
  have hact : ∀ x : ↥N.K, (a : G) * x * (a : G)⁻¹ = g * x * g⁻¹ := by
    intro x
    have h1 := congrArg (fun ψ : MulAut ↥N.K => ((ψ x : ↥N.K) : G)) ha
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [h1, hφ]
    exact conjAct_apply' N.K ⟨g, hgN⟩ x
  set c : G := (a : G)⁻¹ * g with hc
  have hcK : ∀ x ∈ N.K, c * x = x * c := by
    intro x hx
    have := hact ⟨x, hx⟩
    simp only at this
    calc c * x = (a : G)⁻¹ * (g * x * g⁻¹) * g := by rw [hc]; group
      _ = (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * g := by rw [this]
      _ = x * c := by rw [hc]; group
  have haK : (a : G) ∈ N.K := a.2
  have hgac : g = (a : G) * c := by rw [hc]; group
  have hKH : N.K ≤ Subgroup.centralizer ({t} : Set G) := N.K_le_H.trans hf.H_le
  have hcGt : c ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKH haK)) hg
  have hcomm : Commute (a : G) c := (hcK _ haK).symm
  have hc3 : c ^ 3 = 1 := by
    have h1 : (a : G) ^ 3 * c ^ 3 = 1 := by
      rw [← hcomm.mul_pow, ← hgac]
      exact hg3
    have h2 : c ^ 3 = ((a : G) ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : c ^ 3 ∈ N.K := by
      rw [h2]
      exact Subgroup.inv_mem _ (N.K.pow_mem haK 3)
    exact hZK _ h3 fun y hy => (Commute.pow_left (show Commute c y from hcK y hy) 3).eq
  by_cases hc1 : c = 1
  · rw [hgac, hc1, mul_one]
    exact haK
  · exfalso
    obtain ⟨E₉, hE₉K, hE₉, hE₉card⟩ := F.rank
    have hcnK : c ∉ N.K := fun hcK' => hc1 (hZK c hcK' fun y hy => hcK y hy)
    have hext := exists_elemAbelian_sup_zpowers Nat.prime_three hE₉ (n := 2)
      (by rw [hE₉card]; norm_num) hc3 hc1 (fun e he => (hcK e (hE₉K he)).symm)
      (fun hcE => hcnK (hE₉K hcE))
    refine Unc25G2.false_of_isElemAbelian_card_cube hs.setting.qtke.2.2 hf.gammaU.isGamma.1
      (E := E₉ ⊔ Subgroup.zpowers c) ?_ Nat.prime_three (by norm_num) hext.1 (by rw [hext.2])
    exact sup_le (hE₉K.trans hKH) (Subgroup.zpowers_le.mpr hcGt)

theorem Kz_eq (h : Lv2513 N t zK) (F : K33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G)) :
    Kz N.S = threeCoreCent N.K zK := by
  have hf := h.facts2511
  unfold Kz threeCoreCent
  congr 1
  ext g
  constructor
  · rintro ⟨hg, hg3⟩
    obtain ⟨h1, h2⟩ := (mem_centralizer_centerOf_iff N hf).mp hg
    exact ⟨mem_K_of_pow_three N h F hKt (Subgroup.mem_centralizer_singleton_iff.mpr h1) hg3, h2,
      hg3⟩
  · rintro ⟨hgK, hgz, hg3⟩
    have hgt : g ∈ Subgroup.centralizer ({t} : Set G) := hf.H_le (N.K_le_H hgK)
    exact ⟨(mem_centralizer_centerOf_iff N hf).mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mp hgt, hgz⟩, hg3⟩

theorem zK_mem_K (h : Lv2513 N t zK) (F : K33Facts N.K) : zK ∈ N.K := by
  have hKH := H_le_normalizer_K N h F
  have := h.facts2511.zK_mem
  rwa [N.K0_eq hKH] at this

theorem z_eq_zK (h : Lv2513 N t zK) (F : K33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G)) :
    N.z = zK ∧ N.x⁻¹ * t * N.x = t * zK := by
  have hf := h.facts2511
  have hzKK : zK ∈ N.K := zK_mem_K N h F
  have hKz := F.inv zK hzKK (zK_ne_one N hf) (by rw [sq]; exact zK_mul_self N hf)
  have hQeq := Kz_eq N h F hKt
  have hxN : N.x ∈ Subgroup.normalizer (Kz N.S : Set G) := mem_normalizer_Kz N.x_mem.2
  rw [hQeq] at hxN
  have hxinv : N.x⁻¹ ∈ Subgroup.normalizer (threeCoreCent N.K zK : Set G) :=
    Subgroup.inv_mem _ hxN
  have hmem : N.x⁻¹ * zK * N.x ∈ threeCoreCent N.K zK := by
    have := (Subgroup.mem_normalizer_iff.mp hxinv zK).mp hKz.mem
    simpa using this
  have hcen : ∀ v ∈ threeCoreCent N.K zK,
      v * (N.x⁻¹ * zK * N.x) = (N.x⁻¹ * zK * N.x) * v := by
    intro v hv
    have hv' : N.x * v * N.x⁻¹ ∈ threeCoreCent N.K zK :=
      (Subgroup.mem_normalizer_iff.mp hxN v).mp hv
    have hc := threeCoreCent_comm hv'
    calc v * (N.x⁻¹ * zK * N.x) = N.x⁻¹ * ((N.x * v * N.x⁻¹) * zK) * N.x := by group
      _ = N.x⁻¹ * (zK * (N.x * v * N.x⁻¹)) * N.x := by rw [hc]
      _ = (N.x⁻¹ * zK * N.x) * v := by group
  have hxzK : N.x⁻¹ * zK * N.x = zK := by
    rcases hKz.center _ hmem hcen with hw | hw
    · exfalso
      apply zK_ne_one N hf
      calc zK = N.x * (N.x⁻¹ * zK * N.x) * N.x⁻¹ := by group
        _ = 1 := by rw [hw]; group
    · exact hw
  exact h.concl2513.2.1 hxzK

end Config

end CFSG.QuasithinUnique.Unc25K1
