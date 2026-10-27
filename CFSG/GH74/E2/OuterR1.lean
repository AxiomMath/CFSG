module

public import CFSG.GH74.E2.OuterL33G
public import CFSG.GH74.E2.OuterR1A
public import CFSG.GH74.E2.OuterR1B
public import CFSG.GH74.E2.L33OuterTables

public section

namespace CFSG.GH74.E2

open Subgroup Pointwise

theorem exists_conj_of_zstar {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {S : Sylow 2 G} {t : G} (ht : orderOf t = 2)
    (htS : t ∈ (S : Subgroup G)) (htc : ∀ s ∈ (S : Subgroup G), s * t = t * s) :
    ∃ g : G, g⁻¹ * t * g ∈ (S : Subgroup G) ∧ g⁻¹ * t * g ≠ t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hwc' : ∀ g : G, g⁻¹ * t * g ∈ (S : Subgroup G) → g⁻¹ * t * g = t := hcon
  have hz2 : (⟨t, htS⟩ : (S : Subgroup G)) ^ 2 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one t
    rwa [ht] at this
  have hz1 : (⟨t, htS⟩ : (S : Subgroup G)) ≠ 1 := by
    intro h
    have : t = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at ht
    omega
  let z : (S : Subgroup G) := ⟨t, htS⟩
  have hzZ : z ∈ Subgroup.center (S : Subgroup G) :=
    Subgroup.mem_center_iff.2 (fun s => Subtype.ext (htc s s.2))
  obtain ⟨hG, -⟩ := CFSG.Adapters.glauberman_zStar S z hzZ (orderOf_eq_prime hz2 hz1) hwc'
  have hodd : CFSG.oddCore G = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
    · exact h
    · exfalso
      apply CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two ht
      rw [h]; trivial
  have htcentG : t ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hG g
    rw [hodd, Subgroup.mem_bot] at hk
    subst hk
    have := mem_centralizer_iff.1 hc t (Set.mem_singleton_iff.2 rfl)
    simpa using this.symm
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at htcentG
    rw [htcentG, orderOf_one] at ht
    omega
  · obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ Subgroup.center G := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem central_conj_eq {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {t : G}
    (htc : ∀ s ∈ (S : Subgroup G), s * t = t * s)
    (hfix : ∀ n ∈ normalizer ((S : Subgroup G) : Set G), ∀ w ∈ (S : Subgroup G),
      (∀ s ∈ (S : Subgroup G), s * w = w * s) → w = n⁻¹ * t * n → w = t) :
    ∀ z ∈ (S : Subgroup G), (∀ s ∈ (S : Subgroup G), s * z = z * s) →
      ∀ m : G, z = m⁻¹ * t * m → z = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z hz hzc m hzm
  have htcent : t ∈ centralizer ((S : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    exact htc s hs
  have hwcent : m⁻¹ * t * m ∈ centralizer ((S : Subgroup G) : Set G) := by
    rw [← hzm, mem_centralizer_iff]
    intro s hs
    exact hzc s hs
  obtain ⟨n, hn, hn2⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer S t m htcent hwcent
  exact hfix n hn z hz hzc (hzm.trans hn2)

theorem noLocalL33Outer_final
    (hComp : ComponentList) (hD3 : K0Data3) (hL : L33Tables) :
    NoLocalL33Outer := by
  classical
  intro G _ _ hH t K c hd hsh hout
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := hd.order_t
  obtain ⟨-, huniq⟩ := hComp G hH t ht K hd.comp
  have huniq' : ∀ K₁ K₂ : Subgroup G, IsCompCen t K₁ → IsCompCen t K₂ → K₁ = K₂ :=
    fun K₁ K₂ h₁ h₂ => (huniq K₁ h₁).trans (huniq K₂ h₂).symm
  have hloc := localK_of_component hH ht huniq' hd.comp
  have hKC : K ≤ Cen t := hd.comp.1
  have hcen : Subgroup.center ↥K = ⊥ :=
    hD3.center_bot ↥K (Or.inr (Or.inr (Or.inr (Or.inl hsh))))
  have hT : SD16Tables ↥K := hL.tables ↥K hsh
  have hNo : NoQ8C2 (MulAut ↥K) := noQ8C2_L33 hsh
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have htcK : ∀ k ∈ K, t * k = k * t := fun k hk => mem_Cen.1 (hKC hk)
  let K' : Subgroup ↥(Cen t) := K.subgroupOf (Cen t)
  let eKK : ↥K' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC
  have hsh' : ShapeL33 ↥K' := lieModel_of_mulEquiv eKK.symm hsh
  have hcen' : Subgroup.center ↥K' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : eKK x ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨y', rfl⟩ := eKK.surjective y
      rw [← map_mul, ← map_mul, hx y']
    rw [hcen, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact eKK.injective (by rw [hx', map_one])
  have hT' : SD16Tables ↥K' := hL.tables ↥K' hsh'
  have hOut2' := l33_card_aut hsh'
  let t' : ↥(Cen t) := ⟨t, mem_Cen.2 rfl⟩
  have ht'2 : orderOf t' = 2 := (Subgroup.orderOf_coe t').symm.trans ht
  obtain ⟨_, h2⟩ := mem_Qt.1 (t_mem_Qt ht)
  have htQ' : t' ∈ CFSG.pCore 2 ↥(Cen t) := h2
  have htc' : ∀ g : ↥(Cen t), g * t' = t' * g := fun g => Subtype.ext (mem_Cen'.1 g.2)
  have hQ8' : Nonempty (↥(CFSG.pCore 2 ↥(Cen t)) ≃* QuaternionGroup 2) :=
    ⟨((CFSG.pCore 2 ↥(Cen t)).equivMapOfInjective (Cen t).subtype
      (Cen t).subtype_injective).trans hd.quat.some⟩
  let c' : ↥(Cen t) := ⟨c, hd.mem_cen⟩
  have hc3' : orderOf c' = 3 := (Subgroup.orderOf_coe c').symm.trans hd.order_c
  have hcK' : ∀ k ∈ K', c' * k = k * c' := fun k hk =>
    Subtype.ext (hd.centralizes k (Subgroup.mem_subgroupOf.1 hk))
  have hgen' : Gen4 ↥(Cen t) := Gen4.subgroup (Cen t) hH.gen4
  have hKiff : ∀ (u : G) (hu : u ∈ Cen t),
      (∃ k ∈ K', ∀ x ∈ K', (⟨u, hu⟩ : ↥(Cen t)) * x * (⟨u, hu⟩ : ↥(Cen t))⁻¹ = k * x * k⁻¹) ↔
      (∃ k ∈ K, ∀ x ∈ K, u * x * u⁻¹ = k * x * k⁻¹) := by
    intro u hu
    constructor
    · rintro ⟨k, hk, hk2⟩
      refine ⟨(k : G), Subgroup.mem_subgroupOf.1 hk, fun x hx => ?_⟩
      have := hk2 ⟨x, hKC hx⟩ (Subgroup.mem_subgroupOf.2 hx)
      exact congrArg Subtype.val this
    · rintro ⟨k, hk, hk2⟩
      refine ⟨⟨k, hKC hk⟩, Subgroup.mem_subgroupOf.2 hk, fun x hx => ?_⟩
      apply Subtype.ext
      exact hk2 x (Subgroup.mem_subgroupOf.1 hx)
  have hout' : ¬ ∀ g : ↥(Cen t), ∃ k ∈ K', ∀ x ∈ K', g * x * g⁻¹ = k * x * k⁻¹ := by
    intro h
    apply hout
    intro g hg
    exact (hKiff g hg).1 (h ⟨g, hg⟩)
  have hne48 := card_D_ne_48 hgen' hloc hQ8' ht'2 htQ' htc' hcen' hT' hOut2' hout' hc3' hcK'
  obtain ⟨-, hcases⟩ := dt_structure hloc hQ8' hc3' hcK'
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer (K' : Set ↥(Cen t)))) := inferInstance
  have hD24 : Nat.card ↥(Subgroup.centralizer (K' : Set ↥(Cen t))) = 24 := by
    rcases hcases P with ⟨h24, -⟩ | ⟨h48, -⟩
    · exact h24
    · exact absurd h48 hne48
  have hinvD := involutions_D24 hloc hQ8' ht'2 htQ' hc3' hcK' hD24
  have hTu : ∀ u ∈ Cen t, (∀ k ∈ K, u * k = k * u) → u ^ 2 = 1 → u = 1 ∨ u = t := by
    intro u hu hcomm hu2
    have huD : (⟨u, hu⟩ : ↥(Cen t)) ∈ Subgroup.centralizer (K' : Set ↥(Cen t)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subtype.ext (hcomm (k : G) (Subgroup.mem_subgroupOf.1 hk)).symm
    rcases hinvD ⟨u, hu⟩ huD (Subtype.ext (by simpa using hu2)) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hQout : ∀ (x : G) (hx : x ∈ Cen t), x * x = 1 →
      (¬ ∃ k ∈ K, ∀ y ∈ K, x * y * x⁻¹ = k * y * k⁻¹) →
      ¬ ∃ q ∈ CFSG.pCore 2 ↥(Cen t), ∀ y ∈ CFSG.pCore 2 ↥(Cen t),
        (⟨x, hx⟩ : ↥(Cen t)) * y * (⟨x, hx⟩ : ↥(Cen t))⁻¹ = q * y * q⁻¹ :=
    fun x hx hx2 hxo => not_inner_on_Q_of_outer hgen' hloc hQ8' ht'2 htQ' htc' hcen' hT' hOut2'
      hc3' hcK' hD24 (u := ⟨x, hx⟩) (by apply Subtype.ext; simpa [sq] using hx2)
      (fun h => hxo ((hKiff x hx).1 h))
  have hconj : ∀ (x y : G) (hx : x ∈ Cen t) (hy : y ∈ Cen t), x * x = 1 → y * y = 1 →
      (¬ ∃ k ∈ K, ∀ z ∈ K, x * z * x⁻¹ = k * z * k⁻¹) →
      (¬ ∃ k ∈ K, ∀ z ∈ K, y * z * y⁻¹ = k * z * k⁻¹) → ∃ c ∈ Cen t, c * x * c⁻¹ = y := by
    intro x y hx hy hx2 hy2 hxo hyo
    obtain ⟨c, hc⟩ := outer_invs_conj hloc hQ8' hcen' hOut2' (l33_outer_invs_conj hsh')
      hD24 (u := ⟨x, hx⟩) (v := ⟨y, hy⟩) (Subtype.ext hx2) (Subtype.ext hy2)
      (fun h => hxo ((hKiff x hx).1 h)) (fun h => hyo ((hKiff y hy).1 h))
      (hQout x hx hx2 hxo) (hQout y hy hy2 hyo)
    exact ⟨(c : G), c.2, congrArg Subtype.val hc⟩
  obtain ⟨TK⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨SK, hSKdef⟩ : ∃ SK : Subgroup G, SK = (TK : Subgroup ↥K).map K.subtype := ⟨_, rfl⟩
  have hSKK : SK ≤ K := by rw [hSKdef]; exact sylow_map_le K TK
  have hSKp : IsPGroup 2 SK := by rw [hSKdef]; exact sylow_map_isPGroup K TK
  have hSKmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ K → SK ≤ P → P = SK := fun P hP h1 h2 => by
    rw [hSKdef] at h2 ⊢
    exact sylow_map_max K TK P hP h1 h2
  let eK : ↥SK ≃* SD16M :=
    (MulEquiv.subgroupCongr hSKdef).trans
      (((sylowMapEquiv K TK).symm.trans (hT.sylow TK).some).trans
        (CFSG.Semidihedral.presentationEquivModel 4 (by norm_num)))
  obtain ⟨f0, g0, hf0, hfg0⟩ : ∃ f g : SD16M, f * f = 1 ∧ f * g ≠ g * f := by
    refine ⟨OuterRank.S0, OuterRank.R0, OuterRank.rel.2.2.1, fun h => ?_⟩
    have h1 : OuterRank.R0 ^ 3 = OuterRank.R0 := by
      rw [← OuterRank.rel.2.2.2.2, h]
      group
    have h2 : OuterRank.R0 ^ 2 = 1 := by
      have : OuterRank.R0 ^ 2 * OuterRank.R0 = 1 * OuterRank.R0 := by
        rw [← pow_succ, one_mul, h1]
      exact mul_right_cancel this
    apply OuterRank.rel.2.1
    show OuterRank.R0 ^ (2 * 2) = 1
    rw [pow_mul, h2, one_pow]
  have hfR : ((eK.symm f0 : ↥SK) : G) ∈ SK := (eK.symm f0).2
  have hgR : ((eK.symm g0 : ↥SK) : G) ∈ SK := (eK.symm g0).2
  have hf2 : ((eK.symm f0 : ↥SK) : G) ^ 2 = 1 := by
    have : eK.symm f0 * eK.symm f0 = 1 := by rw [← map_mul, hf0, map_one]
    simpa [sq] using congrArg (fun y : ↥SK => (y : G)) this
  have hfg : ((eK.symm f0 : ↥SK) : G) * (eK.symm g0 : ↥SK) ≠
      ((eK.symm g0 : ↥SK) : G) * (eK.symm f0 : ↥SK) := by
    intro h
    apply hfg0
    have h' : eK.symm f0 * eK.symm g0 = eK.symm g0 * eK.symm f0 := Subtype.ext h
    have := congrArg eK h'
    simpa using this
  obtain ⟨S₁, hS₁C, hS₁2, hRS, hmax, htS, haut⟩ :=
    exists_sylow_haut_of_noQ8C2 hH ht hd.comp huniq hd.quat hTu hNo hSKK hSKp hfR hgR hf2 hfg
  have hKn : ∀ x ∈ Cen t, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk
    have h1 := hloc.K_normal.conj_mem ⟨k, hKC hk⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.1 h1
  have hS₁K : ∀ y ∈ S₁, y ∈ K → y ∈ SK := by
    intro y hy hyK
    have : S₁ ⊓ K = SK := hSKmax (S₁ ⊓ K) hS₁2.to_inf_left inf_le_right (le_inf hRS hSKK)
    rw [← this]
    exact ⟨hy, hyK⟩
  obtain ⟨s, hsSK, hs1, hs2, hsc⟩ := exists_central_involution_sylow hSKK hRS
    (fun x hx k hk => hKn x (hS₁C hx) k hk) hS₁K eK
  have hone : ∀ u ∈ K, ∀ v ∈ K, orderOf u = 2 → orderOf v = 2 → ∃ g ∈ K, g * u * g⁻¹ = v := by
    intro u hu v hv hou hov
    obtain ⟨g, hg⟩ := hT.one_class ⟨u, hu⟩ ⟨v, hv⟩
      (by rw [← Subgroup.orderOf_coe]; exact hou) (by rw [← Subgroup.orderOf_coe]; exact hov)
    exact ⟨g, g.2, congrArg Subtype.val hg⟩
  have hs2' : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  have htD : t ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => (htcK k hk).symm
  have hztype : ∀ v ∈ Cen t, orderOf v = 2 → v ≠ t →
      (∃ k ∈ K, ∀ x ∈ K, v * x * v⁻¹ = k * x * k⁻¹) →
      ∃ c ∈ K, c⁻¹ * v * c ∈ S₁ ∧ c⁻¹ * v * c ≠ t ∧
        ∀ s' ∈ S₁, s' * (c⁻¹ * v * c) = (c⁻¹ * v * c) * s' := by
    intro v hvC hvo hvt ⟨k, hkK, hk⟩
    have hv2' : v ^ 2 = 1 := by rw [← hvo]; exact pow_orderOf_eq_one v
    have hdD : k⁻¹ * v ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hk x hx
      calc x * (k⁻¹ * v) = k⁻¹ * (k * x * k⁻¹) * v := by group
        _ = k⁻¹ * (v * x * v⁻¹) * v := by rw [h1]
        _ = (k⁻¹ * v) * x := by group
    obtain ⟨d, hd_def⟩ : ∃ d : G, d = k⁻¹ * v := ⟨_, rfl⟩
    rw [← hd_def] at hdD
    have hdC : d ∈ Cen t := by
      rw [hd_def]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKC hkK)) hvC
    have hv_eq : v = k * d := by rw [hd_def]; group
    have hkd : k * d = d * k := Subgroup.mem_centralizer_iff.1 hdD k hkK
    have hsq : v * v = 1 := by simpa [sq] using hv2'
    have hkk : k * k = 1 ∧ d * d = 1 := by
      have h1 : (k * k) * (d * d) = 1 := by
        calc (k * k) * (d * d) = k * (k * d) * d := by group
          _ = k * (d * k) * d := by rw [hkd]
          _ = (k * d) * (k * d) := by group
          _ = v * v := by rw [← hv_eq]
          _ = 1 := hsq
      have hdd : d * d ∈ K := by
        have : d * d = (k * k)⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact K.inv_mem (K.mul_mem hkK hkK)
      have hddc : d * d ∈ Subgroup.centralizer (K : Set G) :=
        (Subgroup.centralizer (K : Set G)).mul_mem hdD hdD
      have hz : (⟨d * d, hdd⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hddc y y.2)
      rw [hcen, Subgroup.mem_bot] at hz
      have hdd1 : d * d = 1 := congrArg Subtype.val hz
      refine ⟨?_, hdd1⟩
      rw [hdd1, mul_one] at h1
      exact h1
    have hd2 : d ^ 2 = 1 := by rw [sq]; exact hkk.2
    have hdcomm : ∀ k' ∈ K, d * k' = k' * d := fun k' hk' =>
      (Subgroup.mem_centralizer_iff.1 hdD k' hk').symm
    have hd1t : d = 1 ∨ d = t := hTu d hdC hdcomm hd2
    have hdS : d ∈ S₁ := by
      rcases hd1t with h | h
      · rw [h]; exact S₁.one_mem
      · rw [h]; exact htS
    have hdcent : ∀ s' ∈ S₁, s' * d = d * s' := by
      intro s' hs'
      rcases hd1t with h | h
      · rw [h]; simp
      · rw [h]; exact mem_Cen'.1 (hS₁C hs')
    have hk1 : k ≠ 1 := by
      intro hk1
      rw [hk1, one_mul] at hv_eq
      rcases hd1t with h | h
      · rw [h] at hv_eq
        rw [hv_eq, orderOf_one] at hvo
        exact absurd hvo (by norm_num)
      · exact hvt (hv_eq.trans h)
    have hko : orderOf k = 2 := orderOf_eq_prime (by rw [sq]; exact hkk.1) hk1
    obtain ⟨g, hgK, hg⟩ := hone k hkK s (hSKK hsSK) hko hs2'
    have hconj : g * v * g⁻¹ = s * d := by
      rw [hv_eq]
      calc g * (k * d) * g⁻¹ = (g * k * g⁻¹) * (g * d * g⁻¹) := by group
        _ = s * d := by rw [hg, (Subgroup.mem_centralizer_iff.1 hdD g hgK)]; group
    refine ⟨g⁻¹, K.inv_mem hgK, ?_, ?_, ?_⟩
    · rw [inv_inv, hconj]
      exact S₁.mul_mem (hRS hsSK) hdS
    · rw [inv_inv, hconj]
      intro hsd
      have hsDc : s ∈ Subgroup.centralizer (K : Set G) := by
        have : s = t * d⁻¹ := by rw [← hsd]; group
        rw [this]
        exact Subgroup.mul_mem _ htD (Subgroup.inv_mem _ hdD)
      have hsz : (⟨s, hSKK hsSK⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hsDc y y.2)
      rw [hcen, Subgroup.mem_bot] at hsz
      exact hs1 (congrArg Subtype.val hsz)
    · intro s' hs'
      rw [inv_inv, hconj]
      calc s' * (s * d) = (s' * s) * d := by group
        _ = (s * s') * d := by rw [hsc s' hs']
        _ = s * (s' * d) := by group
        _ = s * (d * s') := by rw [hdcent s' hs']
        _ = (s * d) * s' := by group
  have hP : ¬ ∃ P : Subgroup G, IsPGroup 2 P ∧ S₁ ≤ P ∧ P ≠ S₁ := by
    rintro hP
    obtain ⟨n, hn, hne, hmem, hcent⟩ := exists_normalizer_moving hS₁C hmax htS hP
    exact hne (hfix_of_aut htS haut n hn _ hmem hcent rfl)
  push Not at hP
  obtain ⟨S, hS⟩ := hS₁2.exists_le_sylow
  have hSeq : (S : Subgroup G) = S₁ := hP _ S.isPGroup' hS
  have htS' : t ∈ (S : Subgroup G) := hSeq ▸ htS
  have htcS : ∀ s ∈ (S : Subgroup G), s * t = t * s := fun s hs => by
    rw [hSeq] at hs
    exact mem_Cen'.1 (hS₁C hs)
  have hfixS : ∀ n ∈ normalizer ((S : Subgroup G) : Set G), ∀ w ∈ (S : Subgroup G),
      (∀ s ∈ (S : Subgroup G), s * w = w * s) → w = n⁻¹ * t * n → w = t := by
    rw [hSeq]
    exact hfix_of_aut htS haut
  have hZ := central_conj_eq (S := S) htcS hfixS
  rw [hSeq] at hZ
  obtain ⟨g₀, hg₀S, hg₀t⟩ := exists_conj_of_zstar hH.simple hH.nonabelian ht htS' htcS
  rw [hSeq] at hg₀S
  set u : G := g₀⁻¹ * t * g₀ with hu_def
  have huS : u ∈ S₁ := hg₀S
  have huC : u ∈ Cen t := hS₁C huS
  have hut : u ≠ t := hg₀t
  have hu2 : u * u = 1 := by
    calc u * u = g₀⁻¹ * (t * t) * g₀ := by rw [hu_def]; group
      _ = 1 := by rw [ht2]; group
  have hu1 : u ≠ 1 := by
    intro h
    apply ht1
    have : t = g₀ * u * g₀⁻¹ := by rw [hu_def]; group
    rw [this, h]; group
  have huo : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have huout : ¬ ∃ k ∈ K, ∀ x ∈ K, u * x * u⁻¹ = k * x * k⁻¹ := by
    intro hin
    obtain ⟨c, hcK, hc1, hc2, hc3⟩ := hztype u huC huo hut hin
    apply hc2
    refine hZ _ hc1 hc3 (g₀ * c) ?_
    rw [hu_def]; group
  have hgu : g₀ * u * g₀⁻¹ = t := by rw [hu_def]; group
  have hvC : g₀ * t * g₀⁻¹ ∈ Cen t := by
    rw [mem_Cen']
    have hut' : u * t = t * u := mem_Cen'.1 huC
    calc g₀ * t * g₀⁻¹ * t = g₀ * t * g₀⁻¹ * (g₀ * u * g₀⁻¹) := by rw [hgu]
      _ = g₀ * (t * u) * g₀⁻¹ := by group
      _ = g₀ * (u * t) * g₀⁻¹ := by rw [hut']
      _ = (g₀ * u * g₀⁻¹) * (g₀ * t * g₀⁻¹) := by group
      _ = t * (g₀ * t * g₀⁻¹) := by rw [hgu]
  have hv2 : (g₀ * t * g₀⁻¹) * (g₀ * t * g₀⁻¹) = 1 := by
    calc (g₀ * t * g₀⁻¹) * (g₀ * t * g₀⁻¹) = g₀ * (t * t) * g₀⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hvt : g₀ * t * g₀⁻¹ ≠ t := by
    intro h
    apply hut
    calc u = g₀⁻¹ * t * g₀ := hu_def
      _ = g₀⁻¹ * (g₀ * t * g₀⁻¹) * g₀ := by rw [h]
      _ = t := by group
  have hvo : orderOf (g₀ * t * g₀⁻¹) = 2 := by
    refine orderOf_eq_prime (by rw [sq]; exact hv2) (fun h => ht1 ?_)
    have : t = g₀⁻¹ * (g₀ * t * g₀⁻¹) * g₀ := by group
    rw [this, h]; group
  have hvout : ¬ ∃ k ∈ K, ∀ x ∈ K, (g₀ * t * g₀⁻¹) * x * (g₀ * t * g₀⁻¹)⁻¹ = k * x * k⁻¹ := by
    intro hin
    obtain ⟨c, hcK, hc1, hc2, hc3⟩ := hztype _ hvC hvo hvt hin
    apply hc2
    refine hZ _ hc1 hc3 (g₀⁻¹ * c) ?_
    group
  obtain ⟨c, hcC, hcuv⟩ := hconj u (g₀ * t * g₀⁻¹) huC hvC hu2 hv2 huout hvout
  set g : G := c⁻¹ * g₀ with hg_def
  have hgt : g⁻¹ * t * g = u := by
    have hct : c * t = t * c := mem_Cen'.1 hcC
    calc g⁻¹ * t * g = g₀⁻¹ * (c * t * c⁻¹) * g₀ := by rw [hg_def]; group
      _ = g₀⁻¹ * t * g₀ := by rw [hct]; group
  have hgu' : g⁻¹ * u * g = t := by
    calc g⁻¹ * u * g = g₀⁻¹ * (c * u * c⁻¹) * g₀ := by rw [hg_def]; group
      _ = g₀⁻¹ * (g₀ * t * g₀⁻¹) * g₀ := by rw [hcuv]
      _ = t := by group
  have hu2' : (⟨u, huC⟩ : ↥(Cen t)) * ⟨u, huC⟩ = 1 := Subtype.ext hu2
  have huout' : ¬ ∃ k ∈ K', ∀ x ∈ K',
      (⟨u, huC⟩ : ↥(Cen t)) * x * (⟨u, huC⟩ : ↥(Cen t))⁻¹ = k * x * k⁻¹ :=
    fun h => huout ((hKiff u huC).1 h)
  have hK'n : K'.Normal := hloc.K_normal
  let φ : MulAut ↥K' := MulAut.conjNormal (⟨u, huC⟩ : ↥(Cen t))
  have hφ2 : φ ^ 2 = 1 := by
    show (MulAut.conjNormal (⟨u, huC⟩ : ↥(Cen t))) ^ 2 = 1
    rw [← map_pow]
    have : (⟨u, huC⟩ : ↥(Cen t)) ^ 2 = 1 := by rw [sq]; exact hu2'
    rw [this, map_one]
  have hφo : ¬ ∃ k : ↥K', ∀ x : ↥K', φ x = k * x * k⁻¹ := by
    rintro ⟨k, hk⟩
    apply huout'
    refine ⟨(k : ↥(Cen t)), k.2, fun x hx => ?_⟩
    have := congrArg (fun y : ↥K' => ((y : ↥K') : ↥(Cen t))) (hk ⟨x, hx⟩)
    simpa [φ, MulAut.conjNormal_apply] using this
  obtain ⟨a₀, ha₀K, b₀, hb₀K, hua, hub, hx2, hx1⟩ : ∃ a₀ ∈ K, ∃ b₀ ∈ K, u * a₀ = a₀ * u ∧
      u * b₀ = b₀ * u ∧ (a₀ * b₀ * a₀⁻¹ * b₀⁻¹) * (a₀ * b₀ * a₀⁻¹ * b₀⁻¹) = 1 ∧
      a₀ * b₀ * a₀⁻¹ * b₀⁻¹ ≠ 1 := by
    obtain ⟨a, b, ha, hb, hab2, hab1⟩ := l33_outer_inv_commutator hsh' φ hφ2 hφo
    refine ⟨(((a : ↥K') : ↥(Cen t)) : G), Subgroup.mem_subgroupOf.1 a.2,
      (((b : ↥K') : ↥(Cen t)) : G), Subgroup.mem_subgroupOf.1 b.2, ?_, ?_, ?_, ?_⟩
    · have h1 : ((φ a : ↥K') : ↥(Cen t)) = ((a : ↥K') : ↥(Cen t)) := congrArg Subtype.val ha
      have h2 : ((φ a : ↥K') : ↥(Cen t)) =
          (⟨u, huC⟩ : ↥(Cen t)) * ((a : ↥K') : ↥(Cen t)) * (⟨u, huC⟩ : ↥(Cen t))⁻¹ :=
        MulAut.conjNormal_apply _ _
      have h3 : u * (((a : ↥K') : ↥(Cen t)) : G) * u⁻¹ = (((a : ↥K') : ↥(Cen t)) : G) :=
        congrArg Subtype.val (h2.symm.trans h1)
      calc u * (((a : ↥K') : ↥(Cen t)) : G) = (u * (((a : ↥K') : ↥(Cen t)) : G) * u⁻¹) * u := by
            group
        _ = (((a : ↥K') : ↥(Cen t)) : G) * u := by rw [h3]
    · have h1 : ((φ b : ↥K') : ↥(Cen t)) = ((b : ↥K') : ↥(Cen t)) := congrArg Subtype.val hb
      have h2 : ((φ b : ↥K') : ↥(Cen t)) =
          (⟨u, huC⟩ : ↥(Cen t)) * ((b : ↥K') : ↥(Cen t)) * (⟨u, huC⟩ : ↥(Cen t))⁻¹ :=
        MulAut.conjNormal_apply _ _
      have h3 : u * (((b : ↥K') : ↥(Cen t)) : G) * u⁻¹ = (((b : ↥K') : ↥(Cen t)) : G) :=
        congrArg Subtype.val (h2.symm.trans h1)
      calc u * (((b : ↥K') : ↥(Cen t)) : G) = (u * (((b : ↥K') : ↥(Cen t)) : G) * u⁻¹) * u := by
            group
        _ = (((b : ↥K') : ↥(Cen t)) : G) * u := by rw [h3]
    · have h1 := congrArg (fun y : ↥K' => (((y : ↥K') : ↥(Cen t)) : G)) hab2
      simpa [sq] using h1
    · intro h
      apply hab1
      apply Subtype.ext
      apply Subtype.ext
      simpa using h
  set x : G := a₀ * b₀ * a₀⁻¹ * b₀⁻¹ with hx_def
  have hxK : x ∈ K := K.mul_mem (K.mul_mem (K.mul_mem ha₀K hb₀K) (K.inv_mem ha₀K))
    (K.inv_mem hb₀K)
  have ha₀t : a₀ * t = t * a₀ := (htcK a₀ ha₀K).symm
  have hb₀t : b₀ * t = t * b₀ := (htcK b₀ hb₀K).symm
  have hag : g⁻¹ * a₀ * g ∈ Cen t ∧ (g⁻¹ * a₀ * g) * u = u * (g⁻¹ * a₀ * g) := by
    constructor
    · rw [mem_Cen']
      calc g⁻¹ * a₀ * g * t = g⁻¹ * a₀ * g * (g⁻¹ * u * g) := by rw [hgu']
        _ = g⁻¹ * (a₀ * u) * g := by group
        _ = g⁻¹ * (u * a₀) * g := by rw [hua]
        _ = (g⁻¹ * u * g) * (g⁻¹ * a₀ * g) := by group
        _ = t * (g⁻¹ * a₀ * g) := by rw [hgu']
    · calc g⁻¹ * a₀ * g * u = g⁻¹ * a₀ * g * (g⁻¹ * t * g) := by rw [hgt]
        _ = g⁻¹ * (a₀ * t) * g := by group
        _ = g⁻¹ * (t * a₀) * g := by rw [ha₀t]
        _ = (g⁻¹ * t * g) * (g⁻¹ * a₀ * g) := by group
        _ = u * (g⁻¹ * a₀ * g) := by rw [hgt]
  have hbg : g⁻¹ * b₀ * g ∈ Cen t ∧ (g⁻¹ * b₀ * g) * u = u * (g⁻¹ * b₀ * g) := by
    constructor
    · rw [mem_Cen']
      calc g⁻¹ * b₀ * g * t = g⁻¹ * b₀ * g * (g⁻¹ * u * g) := by rw [hgu']
        _ = g⁻¹ * (b₀ * u) * g := by group
        _ = g⁻¹ * (u * b₀) * g := by rw [hub]
        _ = (g⁻¹ * u * g) * (g⁻¹ * b₀ * g) := by group
        _ = t * (g⁻¹ * b₀ * g) := by rw [hgu']
    · calc g⁻¹ * b₀ * g * u = g⁻¹ * b₀ * g * (g⁻¹ * t * g) := by rw [hgt]
        _ = g⁻¹ * (b₀ * t) * g := by group
        _ = g⁻¹ * (t * b₀) * g := by rw [hb₀t]
        _ = (g⁻¹ * t * g) * (g⁻¹ * b₀ * g) := by group
        _ = u * (g⁻¹ * b₀ * g) := by rw [hgt]
  have hcomK : ∀ m₁ m₂ : G, m₁ ∈ Cen t → m₂ ∈ Cen t → m₁ * u = u * m₁ → m₂ * u = u * m₂ →
      m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∈ K := by
    intro m₁ m₂ h₁ h₂ hm₁ hm₂
    have := commutator_centralizer_in_K hloc hcen' hOut2' htc' hu2' huout'
      (centralizer_D_of_outer hloc hQ8' ht'2 htQ' hD24 hu2' (hQout u huC hu2 huout))
      ⟨m₁, h₁⟩ ⟨m₂, h₂⟩ (Subtype.ext hm₁) (Subtype.ext hm₂)
    exact Subgroup.mem_subgroupOf.1 this
  have hxgK : g⁻¹ * x * g ∈ K := by
    have := hcomK _ _ hag.1 hbg.1 hag.2 hbg.2
    have e : g⁻¹ * x * g = g⁻¹ * a₀ * g * (g⁻¹ * b₀ * g) * (g⁻¹ * a₀ * g)⁻¹ *
        (g⁻¹ * b₀ * g)⁻¹ := by rw [hx_def]; group
    rw [e]
    exact this
  have hxgu : u * (g⁻¹ * x * g) = (g⁻¹ * x * g) * u := by
    have hca : Commute u (g⁻¹ * a₀ * g) := hag.2.symm
    have hcb : Commute u (g⁻¹ * b₀ * g) := hbg.2.symm
    have hc : Commute u (g⁻¹ * a₀ * g * (g⁻¹ * b₀ * g) * (g⁻¹ * a₀ * g)⁻¹ *
        (g⁻¹ * b₀ * g)⁻¹) :=
      (((hca.mul_right hcb).mul_right hca.inv_right).mul_right hcb.inv_right)
    have e : g⁻¹ * x * g = g⁻¹ * a₀ * g * (g⁻¹ * b₀ * g) * (g⁻¹ * a₀ * g)⁻¹ *
        (g⁻¹ * b₀ * g)⁻¹ := by rw [hx_def]; group
    rw [e]
    exact hc.eq
  have hxg2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
    calc (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hx2]; group
  have hwC : u * (g⁻¹ * x * g) ∈ Cen t := Subgroup.mul_mem _ huC (hKC hxgK)
  have hw2 : (u * (g⁻¹ * x * g)) * (u * (g⁻¹ * x * g)) = 1 := by
    calc (u * (g⁻¹ * x * g)) * (u * (g⁻¹ * x * g))
        = u * ((g⁻¹ * x * g) * u) * (g⁻¹ * x * g) := by group
      _ = u * (u * (g⁻¹ * x * g)) * (g⁻¹ * x * g) := by rw [← hxgu]
      _ = (u * u) * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) := by group
      _ = 1 := by rw [hu2, hxg2]; group
  have hwout : ¬ ∃ k ∈ K, ∀ y ∈ K, (u * (g⁻¹ * x * g)) * y * (u * (g⁻¹ * x * g))⁻¹ =
      k * y * k⁻¹ := by
    rintro ⟨k, hk, hk2⟩
    apply huout
    refine ⟨k * (g⁻¹ * x * g)⁻¹, K.mul_mem hk (K.inv_mem hxgK), fun y hy => ?_⟩
    have hy' : (g⁻¹ * x * g)⁻¹ * y * (g⁻¹ * x * g) ∈ K :=
      K.mul_mem (K.mul_mem (K.inv_mem hxgK) hy) hxgK
    have := hk2 _ hy'
    calc u * y * u⁻¹ = (u * (g⁻¹ * x * g)) * ((g⁻¹ * x * g)⁻¹ * y * (g⁻¹ * x * g)) *
          (u * (g⁻¹ * x * g))⁻¹ := by group
      _ = k * ((g⁻¹ * x * g)⁻¹ * y * (g⁻¹ * x * g)) * k⁻¹ := this
      _ = (k * (g⁻¹ * x * g)⁻¹) * y * (k * (g⁻¹ * x * g)⁻¹)⁻¹ := by group
  obtain ⟨c', -, hc'⟩ := hconj u (u * (g⁻¹ * x * g)) huC hwC hu2 hw2 huout hwout
  have htxC : t * x ∈ Cen t := Subgroup.mul_mem _ (mem_Cen.2 rfl) (hKC hxK)
  have htx_comm : t * x = x * t := htcK x hxK
  have htx2 : (t * x) * (t * x) = 1 := by
    calc (t * x) * (t * x) = t * (x * t) * x := by group
      _ = t * (t * x) * x := by rw [← htx_comm]
      _ = (t * t) * (x * x) := by group
      _ = 1 := by rw [ht2, hx2]; group
  have hty1 : t * x ≠ 1 := by
    intro h
    have hxt : x = t := by
      have h' : x = t⁻¹ := by
        calc x = t⁻¹ * (t * x) := by group
          _ = t⁻¹ := by rw [h, mul_one]
      rw [h']
      exact inv_eq_of_mul_eq_one_right ht2
    have htK : t ∈ K := hxt ▸ hxK
    have hz : (⟨t, htK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 htD y y.2)
    rw [hcen, Subgroup.mem_bot] at hz
    exact ht1 (congrArg Subtype.val hz)
  have htxo : orderOf (t * x) = 2 := orderOf_eq_prime (by rw [sq]; exact htx2) hty1
  have htxt : t * x ≠ t := fun h => hx1 (mul_left_cancel (h.trans (mul_one t).symm))
  have htxin : ∃ k ∈ K, ∀ z ∈ K, (t * x) * z * (t * x)⁻¹ = k * z * k⁻¹ := by
    refine ⟨x, hxK, fun z hz => ?_⟩
    have hxzx : x * z * x⁻¹ ∈ K := K.mul_mem (K.mul_mem hxK hz) (K.inv_mem hxK)
    calc (t * x) * z * (t * x)⁻¹ = t * (x * z * x⁻¹) * t⁻¹ := by group
      _ = (x * z * x⁻¹) * t * t⁻¹ := by rw [htcK _ hxzx]
      _ = x * z * x⁻¹ := by group
  obtain ⟨cz, -, hz1, hz2, hz3⟩ := hztype (t * x) htxC htxo htxt htxin
  apply hz2
  have hgug : g * u * g⁻¹ = t := by rw [← hgt]; group
  have hgxg : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  have hdecomp : t * x = g * (u * (g⁻¹ * x * g)) * g⁻¹ := by
    calc t * x = (g * u * g⁻¹) * (g * (g⁻¹ * x * g) * g⁻¹) := by rw [hgug, hgxg]
      _ = g * (u * (g⁻¹ * x * g)) * g⁻¹ := by group
  refine hZ _ hz1 hz3 (g₀ * c'⁻¹ * g⁻¹ * cz) ?_
  calc cz⁻¹ * (t * x) * cz = cz⁻¹ * (g * (u * (g⁻¹ * x * g)) * g⁻¹) * cz := by rw [← hdecomp]
    _ = cz⁻¹ * (g * (c' * u * c'⁻¹) * g⁻¹) * cz := by rw [hc']
    _ = (g₀ * c'⁻¹ * g⁻¹ * cz)⁻¹ * t * (g₀ * c'⁻¹ * g⁻¹ * cz) := by rw [hu_def]; group

end CFSG.GH74.E2
