module

public import CFSG.ClassicalInvolution.AschTight.Sec7L98I
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Z

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Cfg98

variable {Ω : Set (Subgroup G)} {K J K' X P : Subgroup G} {z j : G} {S : Sylow 2 G}
  {W : Subgroup G} (c : Cfg98 Ω K J K' X P z j S W)
include c

theorem fixes_of_cent [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hu : Subgroup.zpowers u = K ⊓ W) (hv : Subgroup.zpowers v = J ⊓ W)
    (hXU : ∀ x ∈ X, ∀ w ∈ W ⊓ K, x * w = w * x) {x : G} (hx : x ∈ X) :
    conjSub x K = K ∧ conjSub x J = J ∧ conjSub x K' = K' := by
  have hxK : conjSub x K = K := by
    refine Sec6Gen.eq_of_le_of_le c.hΩ (c.hΩ.conjInvariant x K c.hK) c.hK t.U_data.1 t.U_data.2
      ?_ t.hUK
    intro w hw
    have hw' : w ∈ W ⊓ K := by rw [inf_comm, ← hu]; exact hw
    have : x * w * x⁻¹ = w := by rw [hXU x hx w hw']; group
    rw [← this]
    exact conj_mem_conjSub (t.hUK hw)
  have hxz : x ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (c.hXc hx) z (by simp)).symm
  exact ⟨hxK, (c.part1 t hu hv x hx).mp hxK, (c.conj_K_iff hxz).mp hxK⟩

theorem part3 [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hu : Subgroup.zpowers u = K ⊓ W) (hv : Subgroup.zpowers v = J ⊓ W)
    (hXU : ∀ x ∈ X, ∀ w ∈ W ⊓ K, x * w = w * x) :
    ∃ A : Subgroup G,
      ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ X = ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ A ∧
      ((W ⊓ J) ⊔ (W ⊓ K)) ⊓ A = ⊥ ∧
      (∀ a ∈ A, ∀ y ∈ (W ⊓ J) ⊔ (W ⊓ K), a * y = y * a) ∧
      A ≤ centralizerModOdd ⊤ (K ⊔ K') ∧ A ≤ centralizerModOdd ⊤ J := by
  obtain ⟨A, b₂, hAN₀, hN₀eq, hinf, hb₂L, hb₂o, hb₂z, hb₂j, hb₂zj, hfix⟩ :=
    c.part3_setup t hu hv hXU
  set UV := Subgroup.zpowers u ⊔ Subgroup.zpowers v with hUV
  set L := L98 Ω UV z j with hL
  set O₁ := oddCoreOf (L ⊓ Subgroup.centralizer (UV : Set G)) with hO₁
  have hYW : (W ⊓ J) ⊔ (W ⊓ K) = UV := by
    rw [inf_comm W J, inf_comm W K, ← hu, ← hv, sup_comm]
  rw [hYW]
  have hXC := c.part2 t hu hv hXU
  have hXN : X ≤ Subgroup.normalizer (UV : Set G) := c.X_le_N_UV t hv
  have hN₀C : UV ⊔ X ≤ Subgroup.centralizer (UV : Set G) := by
    refine sup_le (fun w hw => Subgroup.mem_centralizer_iff.mpr fun y hy => t.UV_comm y hy w hw)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    have := hXC x hx y hy
    calc y * x = x * y * x⁻¹ * x := by rw [this]
      _ = x * y := by group
  have hAC : ∀ a ∈ A, ∀ w ∈ UV, a * w * a⁻¹ = w := fun a ha w hw => by
    have := Subgroup.mem_centralizer_iff.mp (hN₀C (hAN₀ ha)) w hw
    rw [← this]; group
  have hN₀L : UV ⊔ X ≤ Subgroup.normalizer (L : Set G) :=
    sup_le ((c.UV_le_L t).trans Subgroup.le_normalizer) (c.X_le_N_L t hv)
  have hN₀O : UV ⊔ X ≤ Subgroup.normalizer (O₁ : Set G) := fun g hg =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (mem_normalizer_inf (hN₀L hg)
      (normalizer_le_normalizer_centralizer UV
        (Subgroup.centralizer_le_normalizer (UV : Set G) (hN₀C hg))))
  have hO₁C : O₁ ≤ Subgroup.centralizer (UV : Set G) := (oddCoreOf_le_self _).trans inf_le_right
  have hA2 : IsPGroup 2 A :=
    (IsPGroup.to_sup_of_normal_left' t.UV_isPGroup c.hX2 hXN).to_le hAN₀
  have hb₂fp := t.fpf hb₂z hb₂j hb₂zj
  have hUVN : ∀ M : Subgroup G, Subgroup.zpowers u ≤ Subgroup.normalizer (M : Set G) →
      Subgroup.zpowers v ≤ Subgroup.normalizer (M : Set G) → (∀ x ∈ X, conjSub x M = M) →
      ∀ a ∈ A, conjSub a M = M := by
    intro M hUM hVM hXM a ha
    have hle : UV ⊔ X ≤ Subgroup.normalizer (M : Set G) :=
      sup_le (sup_le hUM hVM) (fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hXM x hx))
    exact mem_normalizer_iff_conjSub_eq.mp (hle (hAN₀ ha))
  have hVK : Subgroup.zpowers v ≤ Subgroup.normalizer (K : Set G) := by rw [hv]; exact c.V_le_N_K
  have hVK' : Subgroup.zpowers v ≤ Subgroup.normalizer (K' : Set G) := by
    rw [hv]; exact c.V_le_N_K'
  have hUJ : Subgroup.zpowers u ≤ Subgroup.normalizer (J : Set G) := by
    rw [hu]; exact inf_le_right.trans c.W_le_N_J
  have hAK := hUVN K (t.hUK.trans Subgroup.le_normalizer) hVK
    (fun x hx => (c.fixes_of_cent t hu hv hXU hx).1)
  have hAK' := hUVN K' (t.hUK.trans c.K_le) hVK'
    (fun x hx => (c.fixes_of_cent t hu hv hXU hx).2.2)
  have hAJ := hUVN J hUJ (t.hVJ.trans Subgroup.le_normalizer)
    (fun x hx => (c.fixes_of_cent t hu hv hXU hx).2.1)
  obtain ⟨r, hrR, hru⟩ := t.exists_r
  obtain ⟨r', hr'R', hr'nj⟩ := t.exists_r'
  obtain ⟨t₀, ht₀T, ht₀v⟩ := t.exists_t
  obtain ⟨u', hu', hu'U, hUV'⟩ := t.hU'
  have hzj := t.zj_comm
  have hz2 := t.hz.sq
  have hj2 := t.hj.sq
  have hprod : ∀ g : G, g * (z * j) * g⁻¹ = (g * z * g⁻¹) * (g * j * g⁻¹) := fun g => by group
  have hrz : r * z * r⁻¹ = z :=
    Tor98.comm_of_conj_eq_inv (AscL62.uniqueInvolution_comm t.hz (t.hR.1 hrR)).symm
  have hrj := t.he1 r hrR hru
  have hrzj : r * (z * j) * r⁻¹ = j := by
    rw [hprod, hrz, hrj, ← mul_assoc, hz2, one_mul]
  have hr'z : r' * z * r'⁻¹ = z :=
    Tor98.comm_of_conj_eq_inv (AscL62.uniqueInvolution_comm c.hzK' (t.hR'.1 hr'R')).symm
  have hr'j : r' * j * r'⁻¹ = z * j := by
    have hjUV : j ∈ UV := Subgroup.mem_sup_right t.j_mem_V
    have hmem : r' * j * r'⁻¹ ∈ UV := (Subgroup.mem_normalizer_iff.mp (t.hR'N hr'R') j).mp hjUV
    have hsq : (r' * j * r'⁻¹) * (r' * j * r'⁻¹) = 1 := by
      calc (r' * j * r'⁻¹) * (r' * j * r'⁻¹) = r' * (j * j) * r'⁻¹ := by group
        _ = 1 := by rw [hj2]; group
    rcases (Sec71.mem_closure_pair_iff hz2 hj2 hzj).mp (t.mem_Z_of_sq hmem hsq) with
      h | h | h | h
    · exfalso; apply t.hj.ne_one
      calc j = r'⁻¹ * (r' * j * r'⁻¹) * r' := by group
        _ = 1 := by rw [h]; group
    · exfalso; apply t.hzj
      calc z = r'⁻¹ * (r' * z * r'⁻¹) * r' := by group
        _ = r'⁻¹ * (r' * j * r'⁻¹) * r' := by rw [hr'z, h]
        _ = j := by group
    · exfalso; apply hr'nj
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc r' * j = r' * j * r'⁻¹ * r' := by group
        _ = j * r' := by rw [h]
    · exact h
  have hr'zj : r' * (z * j) * r'⁻¹ = j := by
    rw [hprod, hr'z, hr'j, ← mul_assoc, hz2, one_mul]
  have htz := t.he2 t₀ ht₀T ht₀v
  have htj : t₀ * j * t₀⁻¹ = j :=
    Tor98.comm_of_conj_eq_inv (AscL62.uniqueInvolution_comm t.hj (t.hT.1 ht₀T)).symm
  have htzj : t₀ * (z * j) * t₀⁻¹ = z := by
    rw [hprod, htz, htj, mul_assoc, hj2, mul_one]
  have hrL : r ∈ L := c.R_le_L t hrR
  have hr'L : r' ∈ L := by
    have : K' ⊓ (S : Subgroup G) ≤ L :=
      le_L98 ⟨mem_RSet_of_isSylow2In c.hK' c.sylow_R', t.hR'N, K', c.hK', t.hR'.1,
        Or.inl c.hzK'⟩
    exact this hr'R'
  have htL : t₀ ∈ L := c.T_le_L t ht₀T
  have hcomm : ∀ g : G, g ∈ L → g * b₂ * g⁻¹ * b₂ ∈ Subgroup.centralizer (UV : Set G) →
      ∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ O₁ := fun g hg hc₁ a ha =>
    c.comm_mem_O t hu hv (hAC a ha) (hN₀L (hAN₀ ha)) (hfix a ha) hg hb₂L hb₂fp hc₁
  have hc₁r := c.c1_mem_C t hu hv hrL hb₂L hb₂o
    (comm_of_transposition_z hrz hrj hrzj hb₂z hb₂j hb₂zj).1
    (comm_of_transposition_z hrz hrj hrzj hb₂z hb₂j hb₂zj).2
  have hc₁r' := c.c1_mem_C t hu hv hr'L hb₂L hb₂o
    (comm_of_transposition_z hr'z hr'j hr'zj hb₂z hb₂j hb₂zj).1
    (comm_of_transposition_z hr'z hr'j hr'zj hb₂z hb₂j hb₂zj).2
  have hc₁t := c.c1_mem_C t hu hv htL hb₂L hb₂o
    (comm_of_transposition_j htz htj htzj hb₂z hb₂j).1
    (comm_of_transposition_j htz htj htzj hb₂z hb₂j).2
  have hOodd : Odd (Nat.card O₁) := oddCoreOf_odd_natCard _
  have hgO : ∀ g ∈ L, g ∈ Subgroup.normalizer (O₁ : Set G) := fun g hg =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (mem_normalizer_inf (L.le_normalizer hg)
      (normalizer_le_normalizer_centralizer UV (L98_le_normalizer Ω UV z j hg)))
  have hAO : A ≤ Subgroup.normalizer (O₁ : Set G) := hAN₀.trans hN₀O
  have hcen : ∀ (M U₀ : Subgroup G) (w g : G), M ∈ Ω → IsUniqueInvolution M w → U₀ ∈ USet Ω →
      U₀ ≤ M → U₀ ≤ UV → g ∈ M → g ∈ L → (∀ y ∈ U₀, g * y * g⁻¹ = y⁻¹) →
      (∀ y ∈ U₀, y * y = 1 → y = 1 ∨ y = w) → (∃ y₀ ∈ U₀, y₀ * y₀ ≠ 1) →
      (∀ a ∈ A, conjSub a M = M) → g * b₂ * g⁻¹ * b₂ ∈ Subgroup.centralizer (UV : Set G) →
      ∀ k ∈ M, ∀ a ∈ A, ⁅a, k⁆ ∈ oddCoreOf M := by
    intro M U₀ w g hM hw hU₀ hU₀M hU₀UV hgM hgL hgU _ ⟨y₀, hy₀, hy₀2⟩ hAM hc₁
    refine commutator_mem_oddCoreOf_of_fixed c.hΩ hM hw hU₀ hU₀M hgM hgU hy₀ hy₀2 hA2 hAM
      (fun a ha y hy => hAC a ha y (hU₀UV hy)) hOodd
      (fun o ho => Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp (hO₁C ho) y (hU₀UV hy))
      (fun a ha => mem_normalizer_inf (hAO ha) (mem_normalizer_iff_conjSub_eq.mpr (hAM a ha)))
      (mem_normalizer_inf (hgO g hgL) (Subgroup.le_normalizer hgM)) ?_
    intro a ha
    refine ⟨hcomm g hgL hc₁ a ha, ?_⟩
    have h1 : a * g * a⁻¹ ∈ M := by
      have := conj_mem_conjSub (n := a) hgM
      rwa [hAM a ha] at this
    exact M.mul_mem h1 (M.inv_mem hgM)
  have hinvR : ∀ y ∈ Subgroup.zpowers u, r * y * r⁻¹ = y⁻¹ := fun y hy =>
    AscL62.conj_eq_inv_of_not_mem (Sec6Gen.isQuatSub_of_mem_RSet c.hΩ
      (mem_RSet_of_isSylow2In c.hK c.sylow_R))
      (AscL62.isUniqueInvolution_of_le c.hz t.hR.1 (t.huR t.z_mem_U)) t.huR inferInstance
      (t.card_sylow_eq t.hK t.hU t.hUK t.hR) hrR hru hy
  have hu'K' : Subgroup.zpowers u' ≤ K' := by rw [hu']; exact inf_le_left.trans t.hR'.1
  have hu'R' : Subgroup.zpowers u' ≤ K' ⊓ (S : Subgroup G) := by rw [hu']; exact inf_le_left
  have hr'u' : r' ∉ Subgroup.zpowers u' := by rw [hu']; exact fun h => hr'nj h.2
  have hzU' : z ∈ Subgroup.zpowers u' := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet c.hΩ hu'U
    exact c.hzK'.mem_of_le hu'K' (Sec6Gen.isPGroup_of_mem_USet c.hΩ hu'U) (by omega)
  have hinvR' : ∀ y ∈ Subgroup.zpowers u', r' * y * r'⁻¹ = y⁻¹ := fun y hy =>
    AscL62.conj_eq_inv_of_not_mem (Sec6Gen.isQuatSub_of_mem_RSet c.hΩ
      (mem_RSet_of_isSylow2In c.hK' c.sylow_R'))
      (AscL62.isUniqueInvolution_of_le c.hzK' t.hR'.1 (hu'R' hzU')) hu'R' inferInstance
      (t.card_sylow_eq c.hK' hu'U hu'K' t.hR') hr'R' hr'u' hy
  have hinvT : ∀ y ∈ Subgroup.zpowers v, t₀ * y * t₀⁻¹ = y⁻¹ := fun y hy =>
    AscL62.conj_eq_inv_of_not_mem (Sec6Gen.isQuatSub_of_mem_RSet c.hΩ
      (mem_RSet_of_isSylow2In c.hJ t.hT))
      (AscL62.isUniqueInvolution_of_le c.hj t.hT.1 (t.hvT t.j_mem_V)) t.hvT inferInstance
      (t.card_sylow_eq t.hJ t.hV t.hVJ t.hT) ht₀T ht₀v hy
  have hu'sq : u' * u' ≠ 1 := by
    intro h
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet c.hΩ hu'U
    have h1 : orderOf u' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [Nat.card_zpowers] at h4
    have := Nat.le_of_dvd two_pos h1
    omega
  have hK3 := hcen K _ z r c.hK c.hz t.hU t.hUK le_sup_left (t.hR.1 hrR) hrL hinvR
    (fun y hy hy2 => c.hz.unique y (t.hUK hy) hy2) ⟨u, Subgroup.mem_zpowers u, t.u_sq_ne⟩ hAK
    hc₁r
  have hK'3 := hcen K' _ z r' c.hK' c.hzK' hu'U hu'K' (by rw [hUV, hUV']; exact le_sup_left)
    (t.hR'.1 hr'R') hr'L hinvR' (fun y hy hy2 => c.hzK'.unique y (hu'K' hy) hy2)
    ⟨u', Subgroup.mem_zpowers u', hu'sq⟩ hAK' hc₁r'
  have hJ3 := hcen J _ j t₀ c.hJ c.hj t.hV t.hVJ le_sup_right (t.hT.1 ht₀T) htL hinvT
    (fun y hy hy2 => c.hj.unique y (t.hVJ hy) hy2) ⟨v, Subgroup.mem_zpowers v, t.v_sq_ne⟩ hAJ
    hc₁t
  refine ⟨A, hN₀eq, hinf, fun a ha y hy => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · have := hAC a ha y hy
    calc a * y = a * y * a⁻¹ * a := by group
      _ = y * a := by rw [this]
  · exact c.mem_centralizerModOdd_sup (hAK a ha) (hAK' a ha) (fun k hk => hK3 k hk a ha)
      (fun k hk => hK'3 k hk a ha)
  · have haN : a ∈ Subgroup.normalizer (J : Set G) := mem_normalizer_iff_conjSub_eq.mpr (hAJ a ha)
    exact ⟨Subgroup.mem_top a, haN, mem_normalizer_oddCoreOf_of_mem_normalizer haN,
      fun l hl => hJ3 l hl a ha⟩

end Cfg98

theorem l9_8GenS : L9_8GenSTmp := by
  intro G _ _ Ω hΩ K hK J hJ hA z j hz hj K' hK' hne htw X hX2 hXc P hP hXP S hPS hJS W hW hWS
  have c : Cfg98 Ω K J K' X P z j S W :=
    ⟨hΩ, hK, hJ, hA, hz, hj, hK', hne, htw, hX2, hXc, hP, hXP, hPS, hJS, hW, hWS⟩
  obtain ⟨u, v, T, hu, hv, t⟩ := c.exists_tor Sec6Gen.l6_4ThreeGenAll
  exact ⟨⟨fun h x hx => (c.part1 t hu hv x hx).mp (h x hx),
    fun h x hx => (c.part1 t hu hv x hx).mpr (h x hx)⟩, fun hXU => c.part3 t hu hv hXU⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
