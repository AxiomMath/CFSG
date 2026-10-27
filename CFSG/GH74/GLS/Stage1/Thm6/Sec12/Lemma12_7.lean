module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_6

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.GH74.GLS.Stage1.Thm6

variable {G : Type*} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

theorem HBase.extremal_mem_Z (h : HBase G x S T P Q Rd F) {y : G} (hyT : y ∈ T) (hy : IsConjX x y)
    (hext : IsExtremal T y) : y ∈ omegaZ T := by
  obtain ⟨g, rfl⟩ := hy
  have h1 := sylow2_conj h.T_sylow g
  rw [Hconj_centralizer] at h1
  have hcard : Nat.card ↥(T ⊓ Subgroup.centralizer ({g⁻¹ * x * g} : Set G)) =
      Nat.card ↥(Hconj g T) := sylow2_card_eq hext h1
  rw [Hconj_card] at hcard
  have hTC : T ≤ Subgroup.centralizer ({g⁻¹ * x * g} : Set G) := by
    have heq : T ⊓ Subgroup.centralizer ({g⁻¹ * x * g} : Set G) = T :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcard.symm)
    calc T = T ⊓ Subgroup.centralizer ({g⁻¹ * x * g} : Set G) := heq.symm
      _ ≤ _ := inf_le_right
  refine ⟨hyT, ?_, fun t ht => ?_⟩
  · have : g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
    rw [this, h.x_sq]; group
  · exact Subgroup.mem_centralizer_iff.1 (hTC ht) _ (Set.mem_singleton _)

theorem HBase.Rd_le_Pstar (h : HBase G x S T P Q Rd F) (hQ : Q = Subgroup.zpowers x) {u : G}
    (huRd : u ∈ Rd) (huR : u ∉ P ⊔ Q) :
    Rd ≤ (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers x := by
  intro d hd
  have hmono : P ⊔ Subgroup.zpowers x ≤ (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers x :=
    sup_le_sup_right le_sup_left _
  by_cases hdR : d ∈ P ⊔ Q
  · rw [hQ] at hdR
    exact hmono hdR
  · have huinvRd : u⁻¹ ∈ Rd := Rd.inv_mem huRd
    have huinvR : u⁻¹ ∉ P ⊔ Q := fun hh => huR (by simpa using (P ⊔ Q).inv_mem hh)
    have hmem := relIndex_two_mul_mem h.R_index_le_two huinvRd hd huinvR hdR
    rw [hQ] at hmem
    have hd' : d = u * (u⁻¹ * d) := by group
    rw [hd']
    refine Subgroup.mul_mem _ ?_ (hmono hmem)
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))

theorem HBase.normalizer_fixes_x (h : HBase G x S T P Q Rd F) (hz : HZ T P z)
    (hTsyl : IsSylow2In T ⊤) (h4 : Nat.card (omegaZ T) = 4)
    (h123 : ∀ g : G, g⁻¹ * x * g ≠ z ∧ g⁻¹ * (x * z) * g ≠ z) {n : G}
    (hn : ∀ a, a ∈ T ↔ n * a * n⁻¹ ∈ T) : n * x * n⁻¹ = x := by
  have hzn : n * z * n⁻¹ = z := by
    have hZ1 : n * z * n⁻¹ ∈ omegaZ T := omegaZ_conj_mem hn (hz.mem_Z h.P_le_T)
    have hzz : z = n⁻¹ * (n * z * n⁻¹) * n := by group
    rcases h.Z_cases hz h4 _ hZ1 with e | e | e | e
    · exfalso
      apply hz.z_ne_one
      rw [hzz, e]; group
    · exfalso
      apply (h123 n).1
      rw [e] at hzz
      exact hzz.symm
    · exact e
    · exfalso
      apply (h123 n).2
      rw [e] at hzz
      exact hzz.symm
  have hxn : n * x * n⁻¹ ∈ omegaZ T := omegaZ_conj_mem hn h.x_mem_Z
  rcases h.Z_cases hz h4 _ hxn with e | e | e | e
  · exfalso
    apply h.x_ne_one
    have : x = n⁻¹ * (n * x * n⁻¹) * n := by group
    rw [this, e]; group
  · exact e
  · exfalso
    apply (h123 n⁻¹).1
    simpa using e
  ·
    exfalso
    have hNT : T ≤ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer
    have hnN : n ∈ Subgroup.normalizer (T : Set G) := by
      rw [Subgroup.mem_normalizer_iff]; exact hn
    have hnm : n ^ T.relIndex (Subgroup.normalizer (T : Set G)) ∈ T := by
      have h1 := Subgroup.pow_index_mem (T.subgroupOf (Subgroup.normalizer (T : Set G)))
        (⟨n, hnN⟩ : ↥(Subgroup.normalizer (T : Set G)))
      exact h1
    have hodd : ¬ 2 ∣ T.relIndex (Subgroup.normalizer (T : Set G)) := by
      intro hdvd
      apply hTsyl.2.2
      rw [← Subgroup.relIndex_mul_relIndex T (Subgroup.normalizer (T : Set G)) ⊤ hNT le_top]
      exact Dvd.dvd.mul_right hdvd _
    obtain ⟨j, hj⟩ : ∃ j : ℕ, T.relIndex (Subgroup.normalizer (T : Set G)) = 2 * j + 1 :=
      ⟨T.relIndex (Subgroup.normalizer (T : Set G)) / 2, by omega⟩
    have hnxz : n * x * n⁻¹ = x * z := e
    have hn2x : (n * n) * x = x * (n * n) := by
      calc (n * n) * x = n * (n * x * n⁻¹) * n := by group
        _ = n * (x * z) * n⁻¹ * n * n := by rw [hnxz]; group
        _ = (n * x * n⁻¹) * (n * z * n⁻¹) * n * n := by group
        _ = (x * z) * z * n * n := by rw [hnxz, hzn]
        _ = x * (n * n) := by rw [mul_assoc x z z, hz.z_sq, mul_one]; group
    have hn2z : (n * n) * z = z * (n * n) := by
      calc (n * n) * z = n * (n * z * n⁻¹) * n := by group
        _ = n * z * n := by rw [hzn]
        _ = (n * z * n⁻¹) * n * n := by group
        _ = z * (n * n) := by rw [hzn]; group
    have hkx : ((n * n) ^ j) * x = x * ((n * n) ^ j) :=
      ((show Commute (n * n) x from hn2x).pow_left j).eq
    have hkz : ((n * n) ^ j) * z = z * ((n * n) ^ j) :=
      ((show Commute (n * n) z from hn2z).pow_left j).eq
    have hnpow : n ^ T.relIndex (Subgroup.normalizer (T : Set G)) = (n * n) ^ j * n := by
      rw [hj, pow_succ, pow_mul, pow_two]
    rw [hnpow] at hnm
    generalize (n * n) ^ j = k at hkx hkz hnm
    have hcx : (k * n) * x * (k * n)⁻¹ = x * z := by
      have hkxz : k * (x * z) = (x * z) * k := by
        rw [← mul_assoc, hkx, mul_assoc, hkz, ← mul_assoc]
      calc (k * n) * x * (k * n)⁻¹ = k * (n * x * n⁻¹) * k⁻¹ := by group
        _ = k * (x * z) * k⁻¹ := by rw [hnxz]
        _ = x * z := by rw [hkxz]; group
    have hcx' : (k * n) * x * (k * n)⁻¹ = x := by
      have hc := h.x_central _ hnm
      calc (k * n) * x * (k * n)⁻¹ = x * (k * n) * (k * n)⁻¹ := by rw [← hc]
        _ = x := by group
    rw [hcx'] at hcx
    apply hz.z_ne_one
    have h2 : x * 1 = x * z := by rw [mul_one]; exact hcx
    exact (mul_left_cancel h2).symm

theorem lemma_12_7_four {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}
    (hZ : IG_15_3) (hBur : IG_16_2) (hThomp : IG_15_15) (h : HBase G x S T P Q Rd F)
    (hz : HZ T P z) (hout : IP_outer x T Rd) (hcf : IP_cent_four T P Q Rd) (hP4 : IP_P_four P)
    (hRf : IP_Rd_factor T P Q Rd) (hconj : IP_P_conj x z P) (htrans : IP_P_trans P Q Rd)
    (hCRd : IP_cent_Rd P Q Rd) (hexp : IP_cent_P_exp T P Q) (hcyc : IP_Rd_cyclic T Rd)
    (hTS : T = S) (h4 : Nat.card (omegaZ T) = 4) : False := by
  have hTsyl : IsSylow2In T ⊤ := hTS ▸ h.S_sylow
  have hQ := lemma_12_6 hZ hBur h hz hout hcf hP4 hRf hconj htrans hCRd hexp
  have h123 := lemma_12_3a h hz hP4 h4
  have hxzZ : x * z ∈ omegaZ T := (omegaZ T).mul_mem h.x_mem_Z (hz.mem_Z h.P_le_T)
  have hN : ∀ n : G, (∀ a, a ∈ T ↔ n * a * n⁻¹ ∈ T) → n * x * n⁻¹ = x :=
    fun n hn => h.normalizer_fixes_x hz hTsyl h4 h123 hn
  have hwc : ∀ g : G, g⁻¹ * x * g ∈ omegaZ T → g⁻¹ * x * g = x := by
    intro g hg
    rcases h.Z_cases hz h4 _ hg with e | e | e | e
    · exfalso
      apply h.x_ne_one
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, e]; group
    · exact e
    · exact absurd e (h123 g).1
    · exfalso
      obtain ⟨n, hn, hnx⟩ := hBur G T hTsyl x (x * z) h.x_mem_T hxzZ.1 h.x_central hxzZ.2.2 ⟨g, e⟩
      have hn' : ∀ a, a ∈ T ↔ n * a * n⁻¹ ∈ T := fun a => Subgroup.mem_normalizer_iff.1 hn a
      have := hN n⁻¹ (normalizes_inv hn')
      rw [inv_inv] at this
      rw [this] at hnx
      apply hz.z_ne_one
      have h2 : x * 1 = x * z := by rw [mul_one]; exact hnx
      exact (mul_left_cancel h2).symm
  obtain ⟨g, hgT, hgx⟩ := hZ G h.simple h.nonabelian T hTsyl x h.x_mem_T h.x_sq h.x_ne_one
    h.x_central
  have h5 := lemma_12_5 h hz hout hcf hP4 hRf hconj htrans h4 hwc g hgT hgx
  have hnorm := h5.1
  set u := g⁻¹ * x * g with hu
  have hu2 : u * u = 1 := by
    have : u * u = g⁻¹ * (x * x) * g := by rw [hu]; group
    rw [this, h.x_sq]; group
  have huRd : u ∈ Rd := involution_mem_Rd h hout hgT hu2
  have huR : u ∉ P ⊔ Q := h.u_not_mem_R hz hP4 hconj hwc hgx
  have hRdle := h.Rd_le_Pstar hQ huRd huR
  have hxPs : x ∉ P ⊔ Subgroup.zpowers u := by
    intro hxPs
    exact h.x_ne_one (h.Pstar_inf_Q hgT hu2 huR hxPs h.x_mem_Q)
  have finish : ∀ T₀ : Subgroup G, T₀ ≤ T → (∀ t ∈ T, ∀ q ∈ T₀, t * q * t⁻¹ ∈ T₀) → x ∉ T₀ →
      (∃ b' ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b' ^ k)⁻¹ * t ∈ T₀) → False := by
    intro T₀ hle hnT₀ hxT₀ hcycT₀
    have hne : T₀ ≠ T := fun e => hxT₀ (e ▸ h.x_mem_T)
    have hord : ∀ v ∈ T, v ∉ T₀ → orderOf x ≤ orderOf v := by
      intro v _ hv
      have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.x_sq) h.x_ne_one
      rw [hx2]
      have hv1 : v ≠ 1 := fun e => hv (by rw [e]; exact T₀.one_mem)
      have hpos : 0 < orderOf v := orderOf_pos v
      have hne1 : orderOf v ≠ 1 := fun e => hv1 (orderOf_eq_one_iff.1 e)
      omega
    have hext : ∀ y ∈ T, (∃ g : G, g⁻¹ * x * g = y) → IsExtremal T y →
        y ∈ T₀ ∨ x⁻¹ * y ∈ T₀ := by
      intro y hyT hy hyext
      have hyZ := h.extremal_mem_Z hyT hy hyext
      obtain ⟨g', hg'⟩ := hy
      have hyx : y = x := by
        rw [← hg']
        exact hwc g' (by rw [hg']; exact hyZ)
      right
      rw [hyx]
      simp
    rcases hThomp G T T₀ x hTsyl hle hnT₀ hne hcycT₀ h.x_mem_T hxT₀ hord hext with
      ⟨N, hNn, hNcyc, _, hxN⟩ | ⟨g', hg'T₀, hg'ext, _⟩
    · have := hNn
      rcases h.simple.eq_bot_or_eq_top_of_normal N with e | e
      · subst e
        obtain ⟨a, b, hab⟩ := h.nonabelian
        have hcycG : IsCyclic G := isCyclic_of_surjective
          (QuotientGroup.quotientBot (G := G)).toMonoidHom
          (QuotientGroup.quotientBot (G := G)).surjective
        have hc : IsMulCommutative G := IsCyclic.isMulCommutative
        exact hab (hc.is_comm.comm a b)
      · exact hxN (e ▸ Subgroup.mem_top x)
    · have hg'Z := h.extremal_mem_Z (hle hg'T₀) (⟨g', rfl⟩ : IsConjX x (g'⁻¹ * x * g')) hg'ext
      have hxx : g'⁻¹ * x * g' = x := hwc g' hg'Z
      rw [hxx] at hg'T₀
      exact hxT₀ hg'T₀
  obtain ⟨b, hbT, hbcyc⟩ := hcyc
  have hbk : ∀ k : ℤ, b ^ k ∈ T := fun k => Subgroup.zpow_mem _ hbT k
  by_cases hxM : x ∈ (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers b
  ·
    refine finish (P ⊔ Subgroup.zpowers u) hnorm.1 hnorm.2 hxPs ⟨b, hbT, fun t ht => ?_⟩
    obtain ⟨k, hk⟩ := hbcyc t ht
    have hrM : (b ^ k)⁻¹ * t ∈ (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers b := by
      have hle' : (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers x ≤
          (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers b :=
        sup_le le_sup_left ((Subgroup.zpowers_le).2 hxM)
      exact hle' (hRdle hk)
    have hMt : t ∈ (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers b := by
      have e : t = b ^ k * ((b ^ k)⁻¹ * t) := by group
      rw [e]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k)) hrM
    obtain ⟨a, ha, p, hp, hap⟩ := mem_sup_zpowers_of_normalIn hnorm hbT hMt
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    refine ⟨l, ?_⟩
    rw [hap]
    simpa using hp
  ·
    have hMle : (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers b ≤ T :=
      sup_le hnorm.1 ((Subgroup.zpowers_le).2 hbT)
    have hdecomp : ∀ r ∈ Rd, ∃ p ∈ P ⊔ Subgroup.zpowers u, ∃ e : ℤ, r = p * x ^ e := by
      intro r hr
      have hcommx : ∀ a ∈ P ⊔ Subgroup.zpowers u, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
        intro a ha b hb
        obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact ((show Commute x a from h.x_central a (hnorm.1 ha)).zpow_left e).symm.eq
      obtain ⟨p, hp, a, ha, hra⟩ := mem_sup_of_commute hcommx (hRdle hr)
      obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      exact ⟨p, hp, e, hra⟩
    have hxc : ∀ e : ℤ, ∀ w ∈ T, x ^ e * w = w * x ^ e := fun e w hw =>
      ((show Commute x w from h.x_central w hw).zpow_left e).eq
    have hconjb : ∀ t ∈ T, t * b * t⁻¹ ∈ (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers b := by
      intro t ht
      obtain ⟨k, hk⟩ := hbcyc t ht
      obtain ⟨p, hp, e, hpe⟩ := hdecomp _ hk
      have ht' : t = b ^ k * (p * x ^ e) := by rw [← hpe]; group
      have hxeb : x ^ e * b = b * x ^ e := hxc e b hbT
      have hr : (p * x ^ e) * b * (p * x ^ e)⁻¹ = (p * b * p⁻¹ * b⁻¹) * b := by
        calc (p * x ^ e) * b * (p * x ^ e)⁻¹ = p * (x ^ e * b) * (x ^ e)⁻¹ * p⁻¹ := by group
          _ = p * (b * x ^ e) * (x ^ e)⁻¹ * p⁻¹ := by rw [hxeb]
          _ = (p * b * p⁻¹ * b⁻¹) * b := by group
      have hp' : p * b * p⁻¹ * b⁻¹ ∈ P ⊔ Subgroup.zpowers u := by
        have h1 := hnorm.2 b hbT p⁻¹ ((P ⊔ Subgroup.zpowers u).inv_mem hp)
        have h2 := (P ⊔ Subgroup.zpowers u).mul_mem hp h1
        simpa [mul_assoc] using h2
      have hp'' : b ^ k * (p * b * p⁻¹ * b⁻¹) * (b ^ k)⁻¹ ∈ P ⊔ Subgroup.zpowers u :=
        hnorm.2 _ (hbk k) _ hp'
      have hbkb : b ^ k * b * (b ^ k)⁻¹ = b := by
        have hc := ((show Commute b b from Commute.refl b).zpow_left k).eq
        calc b ^ k * b * (b ^ k)⁻¹ = b * b ^ k * (b ^ k)⁻¹ := by rw [hc]
          _ = b := by group
      have e2 : t * b * t⁻¹ = (b ^ k * (p * b * p⁻¹ * b⁻¹) * (b ^ k)⁻¹) * b := by
        rw [ht']
        calc b ^ k * (p * x ^ e) * b * (b ^ k * (p * x ^ e))⁻¹
            = b ^ k * ((p * x ^ e) * b * (p * x ^ e)⁻¹) * (b ^ k)⁻¹ := by group
          _ = b ^ k * ((p * b * p⁻¹ * b⁻¹) * b) * (b ^ k)⁻¹ := by rw [hr]
          _ = (b ^ k * (p * b * p⁻¹ * b⁻¹) * (b ^ k)⁻¹) * (b ^ k * b * (b ^ k)⁻¹) := by group
          _ = (b ^ k * (p * b * p⁻¹ * b⁻¹) * (b ^ k)⁻¹) * b := by rw [hbkb]
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp'')
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
    have hnormM : ∀ t ∈ T, ∀ q ∈ (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers b,
        t * q * t⁻¹ ∈ (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers b := by
      intro t ht q hq
      have hle : (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers b ≤
          Hconj t ((P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers b) := by
        refine sup_le (fun p hp => ?_) ((Subgroup.zpowers_le).2 (hconjb t ht))
        exact Subgroup.mem_sup_left (hnorm.2 t ht p hp)
      exact hle hq
    refine finish _ hMle hnormM hxM ⟨x, h.x_mem_T, fun t ht => ?_⟩
    obtain ⟨k, hk⟩ := hbcyc t ht
    obtain ⟨p, hp, e, hpe⟩ := hdecomp _ hk
    have hpT : p ∈ T := hnorm.1 hp
    have hw : b ^ k * p ∈ T := T.mul_mem (hbk k) hpT
    refine ⟨e, ?_⟩
    have ht' : t = (b ^ k * p) * x ^ e := by
      calc t = b ^ k * ((b ^ k)⁻¹ * t) := by group
        _ = b ^ k * (p * x ^ e) := by rw [hpe]
        _ = (b ^ k * p) * x ^ e := by group
    have h6 : (x ^ e)⁻¹ * t = b ^ k * p := by
      rw [ht', ← hxc e _ hw]; group
    rw [h6]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k))
      (Subgroup.mem_sup_left hp)

theorem lemma_12_7 {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}
    (hZ : IG_15_3) (hBur : IG_16_2) (hThomp : IG_15_15) (h : HBase G x S T P Q Rd F)
    (hz : HZ T P z) (hout : IP_outer x T Rd) (hcf : IP_cent_four T P Q Rd) (hP4 : IP_P_four P)
    (hRf : IP_Rd_factor T P Q Rd) (hconj : IP_P_conj x z P) (htrans : IP_P_trans P Q Rd)
    (hCRd : IP_cent_Rd P Q Rd) (hexp : IP_cent_P_exp T P Q) (hcyc : IP_Rd_cyclic T Rd)
    (hTS : T = S) : IsElemAb2 S ∧ Nat.card S = 8 := by
  rcases h.card_Z hz with h4 | h8
  · exact (lemma_12_7_four hZ hBur hThomp h hz hout hcf hP4 hRf hconj htrans hCRd hexp hcyc hTS
      h4).elim
  · have hTZ := lemma_12_3b hZ hBur h hout hcf hP4 hCRd h8
    have hSZ : S = omegaZ T := hTS.symm.trans hTZ
    refine ⟨?_, ?_⟩
    · rw [hSZ]; exact omegaZ_isElemAb2 T
    · rw [hSZ, h8]

end CFSG.GH74.GLS.Stage1.Thm6.Sec12

