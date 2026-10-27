module

public import CFSG.GH74.GLS.SP.Local.SPLCtAx
public import CFSG.GH74.GLS.SP.Local.SPLCtCnt
public import CFSG.GH74.GLS.SP.Local.SPLCtT

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section Count

theorem card_sup_of_le_normalizer {G : Type} [Group G] {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  let f : ↥A × ↥B → ↥(A ⊔ B) := fun p =>
    ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : G) * b = a' * b' := congrArg Subtype.val h
    have h1 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h']
        _ = b' * (b : G)⁻¹ := by group
    have h2 : (a' : G)⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, h1 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hinf, Subgroup.mem_bot] at h2
    have ha : (a : G) = a' := by
      calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
        _ = a' := by rw [h2, mul_one]
    have hb : (b : G) = b' := by
      have h3 : (a : G) * b = a * b' := by rw [h', ← ha]
      exact mul_left_cancel h3
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    have hset := Subgroup.coe_mul_of_right_le_normalizer_left A B hB
    have : g ∈ (↑(A ⊔ B) : Set G) := hg
    rw [hset] at this
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp this
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

variable {G : Type} [Group G] [Finite G] {D : SPLNot1 G}

omit [Finite G] in
theorem T₀_norm_Act {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) :
    T₀ ≤ normalizer (D.Act : Set G) := by
  intro t₀ ht₀
  rw [mem_normalizer_iff]
  intro a
  have ht₀Ct : t₀ ∈ D.Ct := hT.T_le (T₀_le_T D hT ht₀)
  constructor
  · intro ha; exact Act_normal D t₀ ht₀Ct a ha
  · intro ha
    have h1 := Act_normal D t₀⁻¹ (D.Ct.inv_mem ht₀Ct) _ ha
    have e : t₀⁻¹ * (t₀ * a * t₀⁻¹) * t₀⁻¹⁻¹ = a := by group
    rwa [e] at h1

theorem ct_hModd (hA : SPLCtA D) (hK2 : SPLCenIAt D) {T T₀ T₁ : Subgroup G} {y : G}
    (hT : SPLCtT D T T₀ T₁ y) :
    ∀ P : Subgroup G, P ≤ D.CcI → Odd (Nat.card ↥P) → P ≤ D.Act := by
  intro P hPM hPodd p hp
  have hpM : p ∈ D.Act ⊔ T₀ := (ct_cenI D hA hK2 hT) ▸ hPM hp
  obtain ⟨a, ha, t₀, ht₀, hpe⟩ := sup_decomp_of_le_normalizer (T₀_norm_Act hT) hpM
  have hNodd : Odd (orderOf p) := by
    have : orderOf p ∣ Nat.card ↥P := by
      rw [← Subgroup.orderOf_mk p hp]; exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat hPodd this
  have hAnorm : ∀ f ∈ T₀, ∀ i ∈ D.Act, f * i * f⁻¹ ∈ D.Act := fun f hf i hi =>
    (mem_normalizer_iff.mp (T₀_norm_Act hT hf) i).mp hi
  obtain ⟨a', ha', hpow⟩ := pow_mul_mem_aux D.Act T₀ hAnorm ha ht₀ (orderOf p)
  rw [← hpe, pow_orderOf_eq_one] at hpow
  have ht₀N : t₀ ^ orderOf p = a'⁻¹ := eq_inv_of_mul_eq_one_right hpow.symm
  have hbot : t₀ ^ orderOf p ∈ D.Act ⊓ T₀ := ⟨ht₀N ▸ D.Act.inv_mem ha', T₀.pow_mem ht₀ _⟩
  rw [Act_inf_T₀ D hT, Subgroup.mem_bot] at hbot
  obtain ⟨k, hk⟩ := hT.T_p ⟨t₀, T₀_le_T D hT ht₀⟩
  have hk' : t₀ ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h1 : orderOf t₀ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf t₀ ∣ orderOf p := orderOf_dvd_of_pow_eq_one hbot
  have hcop : Nat.Coprime (2 ^ k) (orderOf p) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hNodd)
  have ht₀1 : t₀ = 1 :=
    orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2)
  rw [hpe, ht₀1, mul_one]
  exact ha

theorem ct_hgen (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) (hK2 : SPLCenIAt D)
    {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) :
    ∀ c ∈ D.Ct, ∃ m ∈ D.CcI, ∃ i ∈ D.Ict, ∃ f ∈ D.F₀, ∃ ε : ℕ, c = m * i * y ^ ε * f := by
  intro c hc
  obtain ⟨a, ha, s, hsT, c₁, hc₁, hcdec⟩ := ct_decomp D hs hA hK2 hT c hc
  have hTeq : T = (T₀ ⊔ T₁) ⊔ zpowers y := hT.T_eq
  obtain ⟨w₁, hw₁, k, hk, hsw⟩ :=
    sup_decomp_of_le_normalizer hT.y_norm_T₀T₁ (hTeq ▸ hsT)
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hk
  obtain ⟨t₀, ht₀, t₁, ht₁, hw₁e⟩ := mem_sup_of_commute hT.T₀_T₁ hw₁
  have hc₁M : c₁ ∈ (zpowers D.z ⊔ zpowers D.t) ⊔ (D.Ict ⊔ D.F₀) := by
    rw [← CCt_eq D hs]; exact hc₁
  have hcomm : ∀ a ∈ zpowers D.z ⊔ zpowers D.t, ∀ b ∈ D.Ict ⊔ D.F₀, a * b = b * a := by
    intro a ha b hb
    have hbM : b ∈ D.C ⊓ D.Ct := by
      rw [CCt_eq D hs]; exact Subgroup.mem_sup_right hb
    exact zt_comm_CCt D hbM a ha
  obtain ⟨ζ, hζ, v, hv, hc₁e⟩ := mem_sup_of_commute hcomm hc₁M
  obtain ⟨i', hi', f, hf, hve⟩ := sup_decomp_of_le_normalizer (F₀_le_normalizer_I D hs) hv
  have hζT₀ : ζ ∈ T₀ :=
    (sup_le (zpowers_le.mpr hT.z_T₀) (zpowers_le.mpr hT.t_T₀) : zpowers D.z ⊔ zpowers D.t ≤ T₀) hζ
  have hy2 : orderOf y = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact hT.y_sq) ?_
    intro h1
    apply hT.y_not_mem hs
    rw [h1]; exact one_mem _
  have hcexp : c = a * (w₁ * y ^ j) * (ζ * (i' * f)) := by
    rw [hcdec, hsw, hc₁e, hve]
  have hMm : ∀ x₁ ∈ T₀, a * x₁ ∈ D.CcI := fun x₁ hx₁ =>
    D.CcI.mul_mem (Act_le_CcI D hA ha) (T₀_le_CcI D hT hx₁)
  have hζt₁ : ζ * t₁ = t₁ * ζ := hT.T₀_T₁ ζ hζT₀ t₁ ht₁
  rcases zpow_cases_two' hy2 j with hyk | hyk
  · refine ⟨a * t₀ * ζ, ?_, t₁ * i', ?_, f, hf, 0, ?_⟩
    · exact D.CcI.mul_mem (hMm t₀ ht₀) (T₀_le_CcI D hT hζT₀)
    · exact D.Ict.mul_mem (by have : t₁ ∈ T ⊓ D.Ict := hT.T₁_eq ▸ ht₁; exact this.2) hi'
    · rw [hcexp, hyk, hw₁e, pow_zero]
      calc a * (t₀ * t₁ * 1) * (ζ * (i' * f)) = a * t₀ * (t₁ * ζ) * i' * f := by group
        _ = a * t₀ * (ζ * t₁) * i' * f := by rw [hζt₁]
        _ = a * t₀ * ζ * (t₁ * i') * 1 * f := by group
  · have hζ' : y * ζ * y⁻¹ ∈ T₀ := hT.y_norm_T₀ ζ hζT₀
    have hi'' : y * i' * y⁻¹ ∈ D.Ict := hA.I_normal y (hT.T_le hT.y_mem) i' hi'
    have hζ't₁ : (y * ζ * y⁻¹) * t₁ = t₁ * (y * ζ * y⁻¹) := hT.T₀_T₁ _ hζ' t₁ ht₁
    refine ⟨a * t₀ * (y * ζ * y⁻¹), ?_, t₁ * (y * i' * y⁻¹), ?_, f, hf, 1, ?_⟩
    · exact D.CcI.mul_mem (hMm t₀ ht₀) (T₀_le_CcI D hT hζ')
    · exact D.Ict.mul_mem (by have : t₁ ∈ T ⊓ D.Ict := hT.T₁_eq ▸ ht₁; exact this.2) hi''
    · rw [hcexp, hyk, hw₁e, pow_one]
      calc a * (t₀ * t₁ * y) * (ζ * (i' * f))
          = a * t₀ * t₁ * (y * ζ * y⁻¹) * (y * i' * y⁻¹) * y * f := by group
        _ = a * t₀ * ((y * ζ * y⁻¹) * t₁) * (y * i' * y⁻¹) * y * f := by rw [hζ't₁]; group
        _ = a * t₀ * (y * ζ * y⁻¹) * (t₁ * (y * i' * y⁻¹)) * y * f := by group

theorem ct_hCI (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u) :
    ∀ P : Subgroup G, P ≤ D.Ict → (∀ p ∈ P, p * u = u * p) → Odd (Nat.card ↥P) →
      Nat.card ↥P ∣ D.e := by
  intro P hPI hPu hPodd
  have hu' : orderOf (⟨u, hu.mem_I⟩ : ↥D.Ict) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hu.ord
  obtain ⟨φ⟩ := (L2facts D hs).2.2 ⟨u, hu.mem_I⟩ hu'
  have hd4 : 4 ≤ D.d := d_pos D.ext3 hs
  have hdeq : D.d = D.e * 2 ^ (D.n - 1) := d_eq D.ext3 hs
  have hdih : IVK.IsDihedralOrder ↥(centralizer ({(⟨u, hu.mem_I⟩ : ↥D.Ict)} : Set ↥D.Ict))
      (2 * (D.d / 2)) := ⟨D.d / 2, rfl, by omega, ⟨φ⟩⟩
  have hPle : P.subgroupOf D.Ict ≤ centralizer ({(⟨u, hu.mem_I⟩ : ↥D.Ict)} : Set ↥D.Ict) := by
    intro p hp
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (hPu p hp)
  have hPcard : Nat.card ↥(P.subgroupOf D.Ict) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPI).toEquiv
  have hdvd := dihedral_odd_subgroup_dvd _ hdih _ hPle (by rw [hPcard]; exact hPodd)
  rw [hPcard] at hdvd
  have hmul : 2 * (D.d / 2) / 2 = D.e * 2 ^ (D.n - 2) := by
    have h1 : D.d = D.e * 2 ^ (D.n - 1) := hdeq
    have hn : 2 ≤ D.n - 1 := by
      have := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
      omega
    have h2 : 2 ^ (D.n - 1) = 2 * 2 ^ (D.n - 2) := by
      have : D.n - 1 = (D.n - 2) + 1 := by omega
      rw [this, pow_succ]; ring
    have hX : D.d = 2 * (D.e * 2 ^ (D.n - 2)) := by rw [h1, h2]; ring
    rw [hX]
    generalize D.e * 2 ^ (D.n - 2) = X
    omega
  rw [hmul] at hdvd
  have hcop : Nat.Coprime (Nat.card ↥P) (2 ^ (D.n - 2)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_left.mpr hPodd).symm
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem ct_count (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) (hK2 : SPLCenIAt D) {u : G}
    (hud : SPLCtUD D u) {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) :
    Nat.card ↥D.Act = D.e ∧ D.F ≤ D.Ct := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu := hud.U
  obtain ⟨g, hgu, hgz, hgt⟩ := hud.d
  have hK3 := hud.K3
  obtain ⟨E₁, E₂, hsupE, hinfE, hcommE, -, -, hcard₁, hcard₂, -, -⟩ := hK3.prod
  have hodd : Odd D.e := e_odd D.ext3 hs
  have he : 0 < D.e := hodd.pos
  have hEcard : Nat.card ↥(D.Eu u) = D.e * D.e := by
    rw [← hsupE, IVK.Proofs2.card_sup_eq_mul hcommE hinfE, hcard₁, hcard₂]
  have hFnorm : D.F ≤ normalizer ((D.Eu u : Subgroup G) : Set G) := by
    intro f hf
    have hfC : f ∈ D.C := F_le_C hs hf
    have hfS : ∀ s ∈ D.S₁, s * f = f * s := fun s hs' =>
      mem_centralizer_iff.mp (F_le_centralizer_S₁ D.toSPLNot0 hf) s hs'
    have huf : u * f = f * u := hfS u hu.mem_S₁
    have hKC : D.K ⊓ centralizer ({u} : Set G) ≤ D.K ⊓ centralizer ({u} : Set G) := le_rfl
    have hle : Stage1.Thm3.Sec4.cmap f (D.K ⊓ centralizer ({u} : Set G)) ≤
        D.K ⊓ centralizer ({u} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · show f * x * f⁻¹ ∈ D.K
        exact hs.comps.conj_sup_mem hfC hx.1
      · show f * x * f⁻¹ ∈ centralizer ({u} : Set G)
        rw [mem_centralizer_singleton_iff]
        have hxu : x * u = u * x := mem_centralizer_singleton_iff.mp hx.2
        calc f * x * f⁻¹ * u = f * x * (f⁻¹ * u * f) * f⁻¹ := by group
          _ = f * x * u * f⁻¹ := by
              have : f⁻¹ * u * f = u := by
                calc f⁻¹ * u * f = f⁻¹ * (u * f) := by group
                  _ = f⁻¹ * (f * u) := by rw [huf]
                  _ = u := by group
              rw [this]
          _ = f * (x * u) * f⁻¹ := by group
          _ = f * (u * x) * f⁻¹ := by rw [hxu]
          _ = u * (f * x * f⁻¹) := by
              calc f * (u * x) * f⁻¹ = (f * u * f⁻¹) * (f * x * f⁻¹) := by group
                _ = u * (f * x * f⁻¹) := by
                    have : f * u * f⁻¹ = u := by
                      calc f * u * f⁻¹ = u * f * f⁻¹ := by rw [← huf]
                        _ = u := by group
                    rw [this]
    have hcardeq : Nat.card ↥(Stage1.Thm3.Sec4.cmap f (D.K ⊓ centralizer ({u} : Set G))) =
        Nat.card ↥(D.K ⊓ centralizer ({u} : Set G)) :=
      Subgroup.card_map_of_injective (MulAut.conj f).injective
    have heq : Stage1.Thm3.Sec4.cmap f (D.K ⊓ centralizer ({u} : Set G)) =
        D.K ⊓ centralizer ({u} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardeq.symm)
    have hE := Stage1.Thm3.Sec4.pPrimeCoreOf_cmap f (D.K ⊓ centralizer ({u} : Set G))
    rw [heq] at hE
    rw [mem_normalizer_iff]
    intro h
    have hEu : D.Eu u = pPrimeCoreOf 2 (D.K ⊓ centralizer ({u} : Set G)) := rfl
    constructor
    · intro hh
      have : f * h * f⁻¹ ∈ Stage1.Thm3.Sec4.cmap f (pPrimeCoreOf 2 (D.K ⊓ centralizer ({u} : Set G))) :=
        ⟨h, hh, by simp [MulAut.conj_apply]⟩
      rw [← hE] at this
      exact this
    · intro hh
      have h1 : f * h * f⁻¹ ∈ pPrimeCoreOf 2 (D.K ⊓ centralizer ({u} : Set G)) := hh
      rw [hE, Stage1.Thm3.Sec4.mem_cmap] at h1
      have e : f⁻¹ * (f * h * f⁻¹) * f = h := by group
      rw [e] at h1
      exact h1
  have hEFcard : Nat.card ↥(D.Eu u ⊔ D.F) = D.e * D.e * Nat.card ↥D.F := by
    rw [card_sup_of_le_normalizer hFnorm hK3.Eu_inf_F, hEcard]
  have hEFeq : D.Eu u ⊔ D.F = pPrimeCoreOf 2 (D.C ⊓ centralizer ({u} : Set G)) := hK3.O2_eq.symm
  have hEFodd : Odd (Nat.card ↥(D.Eu u ⊔ D.F)) := by
    rw [hEFeq]; exact TwoThin.card_pPrimeCoreOf_odd _
  have hEFle : D.Eu u ⊔ D.F ≤ D.C ⊓ centralizer ({u} : Set G) := by
    rw [hEFeq]; exact TwoThin.pPrimeCoreOf_le _
  set R : Subgroup G := (D.Eu u ⊔ D.F).map (MulAut.conj g).toMonoidHom with hR
  have hRcard : Nat.card ↥R = Nat.card ↥(D.Eu u ⊔ D.F) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hRodd : Odd (Nat.card ↥R) := by rw [hRcard]; exact hEFodd
  have hgu' : g * u * g⁻¹ = u := by
    calc g * u * g⁻¹ = g * (g⁻¹ * u * g) * g⁻¹ := by rw [hgu]
      _ = u := by group
  have hRu : ∀ r ∈ R, r * u = u * r := by
    rintro _ ⟨s, hs', rfl⟩
    have hsu : s * u = u * s := mem_centralizer_singleton_iff.mp (hEFle hs').2
    show g * s * g⁻¹ * u = u * (g * s * g⁻¹)
    calc g * s * g⁻¹ * u = g * s * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = g * (s * u) * g⁻¹ := by rw [hgu]; group
      _ = g * (u * s) * g⁻¹ := by rw [hsu]
      _ = (g * u * g⁻¹) * (g * s * g⁻¹) := by group
      _ = u * (g * s * g⁻¹) := by rw [hgu']
  have hRCt : R ≤ D.Ct := by
    rintro _ ⟨s, hs', rfl⟩
    have hsz : s * D.z = D.z * s := mem_centralizer_singleton_iff.mp (hEFle hs').1
    have hsu : s * u = u * s := mem_centralizer_singleton_iff.mp (hEFle hs').2
    show g * s * g⁻¹ ∈ centralizer ({D.t} : Set G)
    rw [mem_centralizer_singleton_iff]
    have ht : D.t = g * (D.z * u) * g⁻¹ := by
      calc D.t = g * (g⁻¹ * D.t * g) * g⁻¹ := by group
        _ = g * (D.z * u) * g⁻¹ := by rw [hgt]
    have hszu : s * (D.z * u) = (D.z * u) * s := by
      calc s * (D.z * u) = (s * D.z) * u := by group
        _ = (D.z * s) * u := by rw [hsz]
        _ = D.z * (s * u) := by group
        _ = D.z * (u * s) := by rw [hsu]
        _ = (D.z * u) * s := by group
    rw [ht]
    calc g * s * g⁻¹ * (g * (D.z * u) * g⁻¹) = g * (s * (D.z * u)) * g⁻¹ := by group
      _ = g * ((D.z * u) * s) * g⁻¹ := by rw [hszu]
      _ = g * (D.z * u) * g⁻¹ * (g * s * g⁻¹) := by group
  have hMIinf : D.CcI ⊓ D.Ict = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxM, hxI⟩
    rw [Subgroup.mem_bot]
    exact I_center_trivial D hs hxI (fun i hi => ((mem_CcI D).mp hxM).2 i hi |>.symm)
  have hbound := odd_subgroup_bound D.Ct D.CcI D.Ict D.F₀ D.Act y u D.e he
    (fun m hm => ((mem_CcI D).mp hm).1) (Ict_le_Ct D hs) (fun f hf => hf.2) (hT.T_le hT.y_mem)
    (Act_le_CcI D hA) (CcI_normal D hA) (fun c hc i hi => hA.I_normal c hc i hi)
    (fun m hm i hi => ((mem_CcI D).mp hm).2 i hi |>.symm) hMIinf (ct_hgen hs hA hK2 hT)
    hT.y_sq (F₀_odd D) (ct_hModd hA hK2 hT) hu.mem_I (ct_hCI hs hu) R hRCt hRu hRodd
  rw [hRcard, hEFcard] at hbound
  have hAle : Nat.card ↥D.Act ≤ D.e := Nat.le_of_dvd he hA.A_dvd
  have hF₀F : D.F₀ ≤ D.F := F₀_le_F D
  have hF₀le : Nat.card ↥D.F₀ ≤ Nat.card ↥D.F := Subgroup.card_le_of_le hF₀F
  have hApos : 0 < Nat.card ↥D.Act := Nat.card_pos
  have hF₀pos : 0 < Nat.card ↥D.F₀ := Nat.card_pos
  have hFpos : 0 < Nat.card ↥D.F := Nat.card_pos
  have h1 : D.e * (D.e * Nat.card ↥D.F) ≤ D.e * (Nat.card ↥D.Act * Nat.card ↥D.F₀) := by
    calc D.e * (D.e * Nat.card ↥D.F) = D.e * D.e * Nat.card ↥D.F := by ring
      _ ≤ Nat.card ↥D.Act * D.e * Nat.card ↥D.F₀ := hbound
      _ = D.e * (Nat.card ↥D.Act * Nat.card ↥D.F₀) := by ring
  have h2 : D.e * Nat.card ↥D.F ≤ Nat.card ↥D.Act * Nat.card ↥D.F₀ :=
    Nat.le_of_mul_le_mul_left h1 he
  have hAeq : Nat.card ↥D.Act = D.e := by
    by_contra hne
    have hlt : Nat.card ↥D.Act < D.e := lt_of_le_of_ne hAle hne
    have : Nat.card ↥D.Act * Nat.card ↥D.F₀ < D.e * Nat.card ↥D.F :=
      calc Nat.card ↥D.Act * Nat.card ↥D.F₀ < D.e * Nat.card ↥D.F₀ :=
            Nat.mul_lt_mul_of_pos_right hlt hF₀pos
        _ ≤ D.e * Nat.card ↥D.F := Nat.mul_le_mul_left _ hF₀le
    omega
  have hF₀eq : Nat.card ↥D.F₀ = Nat.card ↥D.F := by
    by_contra hne
    have hlt : Nat.card ↥D.F₀ < Nat.card ↥D.F := lt_of_le_of_ne hF₀le hne
    have : Nat.card ↥D.Act * Nat.card ↥D.F₀ < D.e * Nat.card ↥D.F := by
      rw [hAeq]
      exact Nat.mul_lt_mul_of_pos_left hlt he
    omega
  refine ⟨hAeq, ?_⟩
  have hFeq : D.F₀ = D.F := Subgroup.eq_of_le_of_card_ge hF₀F (le_of_eq hF₀eq.symm)
  intro f hf
  have hf₀ : f ∈ D.F₀ := hFeq ▸ hf
  exact hf₀.2

end Count

end CFSG.GH74.GLS.SP.Local
