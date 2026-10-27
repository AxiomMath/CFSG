module

public import CFSG.ClassicalInvolution.AschTight.Sec7L98E

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

@[expose] def fam98 (Ω : Set (Subgroup G)) (A : Subgroup G) (z j : G) : Set (Subgroup G) :=
  {Q | Q ∈ RSet Ω ∧ Q ≤ Subgroup.normalizer (A : Set G) ∧ ∃ M ∈ Ω, Q ≤ M ∧
    (IsUniqueInvolution M z ∨ IsUniqueInvolution M j ∨ IsUniqueInvolution M (z * j))}

@[expose] def L98 (Ω : Set (Subgroup G)) (A : Subgroup G) (z j : G) : Subgroup G :=
  ⨆ Q ∈ fam98 Ω A z j, Q

theorem le_L98 {Ω : Set (Subgroup G)} {A : Subgroup G} {z j : G} {Q : Subgroup G}
    (hQ : Q ∈ fam98 Ω A z j) : Q ≤ L98 Ω A z j :=
  le_iSup₂ (f := fun Q (_ : Q ∈ fam98 Ω A z j) => Q) Q hQ

theorem L98_le {Ω : Set (Subgroup G)} {A : Subgroup G} {z j : G} {H : Subgroup G}
    (h : ∀ Q ∈ fam98 Ω A z j, Q ≤ H) : L98 Ω A z j ≤ H :=
  iSup₂_le h

theorem L98_le_normalizer (Ω : Set (Subgroup G)) (A : Subgroup G) (z j : G) :
    L98 Ω A z j ≤ Subgroup.normalizer (A : Set G) :=
  L98_le fun _ hQ => hQ.2.1

theorem mem_normalizer_L98 {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {A : Subgroup G}
    {z j : G} {x : G} (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxz : x * z * x⁻¹ = z)
    (hxj : x * j * x⁻¹ = j) : x ∈ Subgroup.normalizer ((L98 Ω A z j : Subgroup G) : Set G) := by
  have hfam : ∀ y : G, y ∈ Subgroup.normalizer (A : Set G) → y * z * y⁻¹ = z →
      y * j * y⁻¹ = j → ∀ Q ∈ fam98 Ω A z j, conjSub y Q ∈ fam98 Ω A z j := by
    intro y hyA hyz hyj Q ⟨hQR, hQN, M, hM, hQM, hMinv⟩
    refine ⟨RSet.conj hΩ hQR y, ?_, conjSub y M, hΩ y M hM, conjSub_mono hQM, ?_⟩
    · have := conjSub_le_normalizer hQN y
      rwa [mem_normalizer_iff_conjSub_eq.mp hyA] at this
    · have hyzj : y * (z * j) * y⁻¹ = z * j := by
        calc y * (z * j) * y⁻¹ = (y * z * y⁻¹) * (y * j * y⁻¹) := by group
          _ = z * j := by rw [hyz, hyj]
      rcases hMinv with h | h | h
      · exact Or.inl (hyz ▸ h.conj y)
      · exact Or.inr (Or.inl (hyj ▸ h.conj y))
      · exact Or.inr (Or.inr (hyzj ▸ h.conj y))
  have hxi : x⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hxA
  have hxz' : x⁻¹ * z * x⁻¹⁻¹ = z := by
    calc x⁻¹ * z * x⁻¹⁻¹ = x⁻¹ * (x * z * x⁻¹) * x := by rw [hxz]; group
      _ = z := by group
  have hxj' : x⁻¹ * j * x⁻¹⁻¹ = j := by
    calc x⁻¹ * j * x⁻¹⁻¹ = x⁻¹ * (x * j * x⁻¹) * x := by rw [hxj]; group
      _ = j := by group
  rw [mem_normalizer_iff_conjSub_eq]
  refine le_antisymm (conjSub_iSup_le (hfam x hxA hxz hxj)) ?_
  have h1 := conjSub_mono (n := x) (conjSub_iSup_le (hfam x⁻¹ hxi hxz' hxj'))
  rwa [conjSub_conjSub_inv] at h1


namespace Tor98

variable {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {z j u v : G} {R R' T : Subgroup G}
  (t : Tor98 Ω K J K' z j u v R R' T)
include t

theorem exists_t [Finite G] : ∃ t₀ ∈ T, t₀ ∉ Subgroup.zpowers v := by
  by_contra h
  push Not at h
  have h1 := t.card_sylow_eq t.hJ t.hV t.hVJ t.hT
  have h2 : Nat.card T ≤ Nat.card (Subgroup.zpowers v) := Subgroup.card_le_of_le h
  have h3 := t.V_data.2
  omega

theorem zj_comm [Finite G] : z * j = j * z :=
  t.hcomm z t.z_mem_U j t.j_mem_V

theorem rho_conj [Finite G] {r t₀ : G} (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) (ht : t₀ ∈ T)
    (htv : t₀ ∉ Subgroup.zpowers v) :
    (r * t₀) * z * (r * t₀)⁻¹ = j ∧ (r * t₀) * j * (r * t₀)⁻¹ = z * j ∧
      (r * t₀) * (z * j) * (r * t₀)⁻¹ = z := by
  have hrz : r * z * r⁻¹ = z :=
    comm_of_conj_eq_inv (AscL62.uniqueInvolution_comm t.hz (t.hR.1 hr)).symm
  have hrj := t.he1 r hr hru
  have htz := t.he2 t₀ ht htv
  have htj : t₀ * j * t₀⁻¹ = j :=
    comm_of_conj_eq_inv (AscL62.uniqueInvolution_comm t.hj (t.hT.1 ht)).symm
  have hzz := t.hz.sq
  have hjj := t.hj.sq
  have hzj := t.zj_comm
  have h1 : (r * t₀) * z * (r * t₀)⁻¹ = j := by
    calc (r * t₀) * z * (r * t₀)⁻¹ = r * (t₀ * z * t₀⁻¹) * r⁻¹ := by group
      _ = (r * z * r⁻¹) * (r * j * r⁻¹) := by rw [htz]; group
      _ = (z * z) * j := by rw [hrz, hrj]; group
      _ = j := by rw [hzz, one_mul]
  have h2 : (r * t₀) * j * (r * t₀)⁻¹ = z * j := by
    calc (r * t₀) * j * (r * t₀)⁻¹ = r * (t₀ * j * t₀⁻¹) * r⁻¹ := by group
      _ = z * j := by rw [htj, hrj]
  refine ⟨h1, h2, ?_⟩
  calc (r * t₀) * (z * j) * (r * t₀)⁻¹
      = ((r * t₀) * z * (r * t₀)⁻¹) * ((r * t₀) * j * (r * t₀)⁻¹) := by group
    _ = j * (z * j) := by rw [h1, h2]
    _ = z * (j * j) := by rw [← mul_assoc, ← hzj, mul_assoc]
    _ = z := by rw [hjj, mul_one]

end Tor98

namespace Cfg98

variable {Ω : Set (Subgroup G)} {K J K' X P : Subgroup G} {z j : G} {S : Sylow 2 G}
  {W : Subgroup G} (c : Cfg98 Ω K J K' X P z j S W)
include c

theorem fam_le_Y_z [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hu : Subgroup.zpowers u = K ⊓ W) (hv : Subgroup.zpowers v = J ⊓ W) {Q M : Subgroup G}
    (hQR : Q ∈ RSet Ω)
    (hQN : Q ≤ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) :
      Set G)) (hM : M ∈ Ω) (hQM : Q ≤ M) (hMz : IsUniqueInvolution M z) :
    Q ≤ pairNormalizers K J z j := by
  have hMtw : M ∈ twinSet Ω K := ⟨hM, z, c.hz, hMz⟩
  rw [c.htw] at hMtw
  have hQsyl := Sec6Gen.isSylow2In_of_mem_RSet_of_le c.hΩ hM hQR hQM
  rcases hMtw with h | h
  · subst h
    have hUVW : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ W := by
      refine sup_le ?_ ?_
      · rw [hu]; exact inf_le_right
      · rw [hv]; exact inf_le_right
    have hKUV : M ⊓ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) = Subgroup.zpowers u := by
      refine le_antisymm (fun x hx => ?_) (le_inf t.hUK le_sup_left)
      rw [hu]
      exact ⟨hx.1, hUVW hx.2⟩
    have hQU : Q ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
      intro g hg
      rw [← hKUV]
      exact mem_normalizer_inf (Subgroup.le_normalizer (hQM hg)) (hQN hg)
    have h2 : IsPGroup 2 ↥(Q ⊔ Subgroup.zpowers u) :=
      IsPGroup.to_sup_of_normal_right' hQsyl.2.1 t.U_data.1 hQU
    have h3 := hQsyl.eq_of_le h2 (sup_le hQM t.hUK) le_sup_left
    have huQ : Subgroup.zpowers u ≤ Q := by rw [← h3]; exact le_sup_right
    exact t.hRY Q hQsyl huQ hQN
  · have hMK' : M = K' := h
    subst hMK'
    exact t.hR'Y Q hQsyl hQN

theorem fam_le_Y [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hu : Subgroup.zpowers u = K ⊓ W) (hv : Subgroup.zpowers v = J ⊓ W) :
    ∀ Q ∈ fam98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j,
      Q ≤ pairNormalizers K J z j := by
  obtain ⟨r, hrR, hru⟩ := t.exists_r
  obtain ⟨t₀, ht₀T, ht₀v⟩ := t.exists_t
  obtain ⟨hρz, -, -⟩ := t.rho_conj hrR hru ht₀T ht₀v
  have hρY : r * t₀ ∈ pairNormalizers K J z j :=
    Subgroup.mul_mem _ (t.R_le_Y hrR) (t.hTY ht₀T)
  have hρN : r * t₀ ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (t.hRN hrR) (t.hTN ht₀T)
  have htY := t.hTY ht₀T
  have htN := t.hTN ht₀T
  have htz := t.he2 t₀ ht₀T ht₀v
  have transport : ∀ g : G, g ∈ pairNormalizers K J z j →
      g ∈ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) →
      ∀ w : G, g * z * g⁻¹ = w → ∀ Q M : Subgroup G, Q ∈ RSet Ω →
      Q ≤ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) :
        Set G) → M ∈ Ω → Q ≤ M → IsUniqueInvolution M w → Q ≤ pairNormalizers K J z j := by
    intro g hgY hgN w hgw Q M hQR hQN hM hQM hMw
    have hMz : IsUniqueInvolution (conjSub g⁻¹ M) z := by
      have := hMw.conj g⁻¹
      rwa [← hgw, show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at this
    have hQ' := c.fam_le_Y_z t hu hv (RSet.conj c.hΩ.conjInvariant hQR g⁻¹)
      (by
        have := conjSub_le_normalizer hQN g⁻¹
        rwa [mem_normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ hgN)] at this)
      (c.hΩ.conjInvariant g⁻¹ M hM) (conjSub_mono hQM) hMz
    have h1 := conjSub_mono (n := g) hQ'
    rwa [conjSub_conjSub_inv, mem_normalizer_iff_conjSub_eq.mp
      ((pairNormalizers K J z j).le_normalizer hgY)] at h1
  intro Q ⟨hQR, hQN, M, hM, hQM, hMinv⟩
  rcases hMinv with h | h | h
  · exact c.fam_le_Y_z t hu hv hQR hQN hM hQM h
  · exact transport _ hρY hρN j hρz Q M hQR hQN hM hQM h
  · exact transport _ htY htN (z * j) htz Q M hQR hQN hM hQM h

theorem R_le_L [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T) :
    K ⊓ (S : Subgroup G) ≤ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j :=
  le_L98 ⟨mem_RSet_of_isSylow2In c.hK c.sylow_R, t.hRN, K, c.hK, t.hR.1, Or.inl c.hz⟩

theorem T_le_L [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T) :
    T ≤ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j :=
  le_L98 ⟨mem_RSet_of_isSylow2In c.hJ t.hT, t.hTN, J, c.hJ, t.hT.1, Or.inr (Or.inl c.hj)⟩

theorem L_le_Y [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hu : Subgroup.zpowers u = K ⊓ W) (hv : Subgroup.zpowers v = J ⊓ W) :
    L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j ≤ pairNormalizers K J z j :=
  L98_le (c.fam_le_Y t hu hv)

theorem X_le_C_Z [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T) :
    X ≤ Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) :=
  fun x hx => t.mem_C_Z_of_comm
    (Subgroup.mem_centralizer_iff.mp (c.hXc hx) z (by simp)).symm
    (Subgroup.mem_centralizer_iff.mp (c.hXc hx) j (by simp)).symm

theorem X_le_N_L [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hv : Subgroup.zpowers v = J ⊓ W) :
    X ≤ Subgroup.normalizer
      ((L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j : Subgroup G) : Set G) := by
  intro x hx
  exact mem_normalizer_L98 c.hΩ.conjInvariant (c.X_le_N_UV t hv hx)
    (Tor98.comm_of_conj_eq_inv (Subgroup.mem_centralizer_iff.mp (c.hXc hx) z (by simp)))
    (Tor98.comm_of_conj_eq_inv (Subgroup.mem_centralizer_iff.mp (c.hXc hx) j (by simp)))

theorem C_L_le [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hu : Subgroup.zpowers u = K ⊓ W) (hv : Subgroup.zpowers v = J ⊓ W) {g : G}
    (hgL : g ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j)
    (hgZ : g ∈ Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G)) :
    conjSub g K = K ∧ conjSub g K' = K' := by
  obtain ⟨r, hrR, hru⟩ := t.exists_r
  obtain ⟨r', hr'R', hr'j⟩ := t.exists_r'
  obtain ⟨-, hYC⟩ := t.hcent r hrR hru r' hr'R' hr'j
  have hg : g ∈ ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G))) ⊔
      Subgroup.zpowers (r * r') := by
    rw [← hYC]
    exact ⟨c.L_le_Y t hu hv hgL, hgZ⟩
  have hXK : (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) ≤
      Subgroup.normalizer (K : Set G) :=
    sup_le inf_le_right (inf_le_left.trans Subgroup.le_normalizer)
  have hXK' : (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) ≤
      Subgroup.normalizer (K' : Set G) := by
    refine sup_le (fun g hg => ?_) (inf_le_left.trans c.K_le)
    have hgz : g ∈ Subgroup.centralizer ({z} : Set G) :=
      Sec6Gen.le_centralizer_of_le_normalizer' c.hz (Subgroup.zpowers_le.mpr hg.2)
        (Subgroup.mem_zpowers g)
    rw [mem_normalizer_iff_conjSub_eq]
    exact (c.conj_K_iff hgz).mp (mem_normalizer_iff_conjSub_eq.mp hg.2)
  have hrK : r * r' ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer (t.hR.1 hrR)) (c.K'_le (t.hR'.1 hr'R'))
  have hrK' : r * r' ∈ Subgroup.normalizer (K' : Set G) :=
    Subgroup.mul_mem _ (c.K_le (t.hR.1 hrR)) (Subgroup.le_normalizer (t.hR'.1 hr'R'))
  exact ⟨mem_normalizer_iff_conjSub_eq.mp ((sup_le hXK (Subgroup.zpowers_le.mpr hrK)) hg),
    mem_normalizer_iff_conjSub_eq.mp ((sup_le hXK' (Subgroup.zpowers_le.mpr hrK')) hg)⟩

theorem part1 [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hu : Subgroup.zpowers u = K ⊓ W) (hv : Subgroup.zpowers v = J ⊓ W) (x : G) (hx : x ∈ X) :
    conjSub x K = K ↔ conjSub x J = J := by
  obtain ⟨r, hrR, hru⟩ := t.exists_r
  obtain ⟨t₀, ht₀T, ht₀v⟩ := t.exists_t
  obtain ⟨hρz, -, -⟩ := t.rho_conj hrR hru ht₀T ht₀v
  set b := r * t₀ with hb
  have hbL : b ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j :=
    Subgroup.mul_mem _ (c.R_le_L t hrR) (c.T_le_L t ht₀T)
  have hbY : b ∈ pairNormalizers K J z j := c.L_le_Y t hu hv hbL
  have hxL := c.X_le_N_L t hv hx
  have hxZ := c.X_le_C_Z t hx
  have hc₀L : x⁻¹ * b⁻¹ * x * b ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j := by
    have h1 : x⁻¹ * b⁻¹ * x⁻¹⁻¹ ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxL) b⁻¹).mp (Subgroup.inv_mem _ hbL)
    rw [inv_inv] at h1
    exact Subgroup.mul_mem _ h1 hbL
  have hc₀Z : x⁻¹ * b⁻¹ * x * b ∈
      Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) := by
    have hbN : b⁻¹ ∈ Subgroup.normalizer
        ((Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) :
          Subgroup G) : Set G) :=
      normalizer_le_normalizer_centralizer _ (Subgroup.inv_mem _ (t.hYZ hbY))
    have h1 : b⁻¹ * x * b⁻¹⁻¹ ∈
        Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hbN x).mp hxZ
    rw [inv_inv] at h1
    rw [show x⁻¹ * b⁻¹ * x * b = x⁻¹ * (b⁻¹ * x * b) by group]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxZ) h1
  obtain ⟨hcK, hcK'⟩ := c.C_L_le t hu hv hc₀L hc₀Z
  have hconj : ∀ M : Subgroup G, conjSub (x⁻¹ * b⁻¹ * x * b) M = M →
      conjSub x (conjSub b M) = conjSub b (conjSub x M) := by
    intro M hM
    rw [← conjSub_mul, ← conjSub_mul,
      show x * b = b * x * (x⁻¹ * b⁻¹ * x * b) by group, conjSub_mul, hM]
  have hxz : x ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (c.hXc hx) z (by simp)).symm
  have hJb : J = conjSub b K ∨ J = conjSub b K' := by
    have hjz : b⁻¹ * j * b⁻¹⁻¹ = z := by rw [← hρz]; group
    have h1 : conjSub b⁻¹ J ∈ twinSet Ω K :=
      ⟨c.hΩ.conjInvariant b⁻¹ J c.hJ, z, c.hz, hjz ▸ c.hj.conj b⁻¹⟩
    rw [c.htw] at h1
    rcases h1 with h | h
    · left; rw [← h, conjSub_conjSub_inv]
    · right
      have h' : conjSub b⁻¹ J = K' := h
      rw [← h', conjSub_conjSub_inv]
  rcases hJb with h | h
  · rw [h, hconj K hcK]
    exact ⟨fun h1 => by rw [h1], fun h1 => conjSub_injective b h1⟩
  · rw [h, hconj K' hcK', c.conj_K_iff hxz]
    exact ⟨fun h1 => by rw [h1], fun h1 => conjSub_injective b h1⟩

end Cfg98

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
