module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDSetup

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6.SD

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem mem_sup_of_mem_normalizer_of_allTypeTwo (ht : Setup194Three K z)
    (hA : AllTypeTwo K z) {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K))
    (hRK : R ≤ K) {T : Subgroup G} (hT2 : IsPGroup 2 T) (hRT : R ≤ T)
    (hTN : T ≤ Subgroup.normalizer (R : Set G)) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    {g : G} (htT : g * z * g⁻¹ ∈ T) (htz : g * z * g⁻¹ ≠ z) {h : G} (hsT : h * z * h⁻¹ ∈ T)
    (hsN : h * z * h⁻¹ ∈
      Subgroup.normalizer ((R ⊔ Subgroup.zpowers (g * z * g⁻¹) : Subgroup G) : Set G)) :
    h * z * h⁻¹ ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹) := by
  have hI := ht.isUniqueInvolution
  have hU := ht.uniqueInvolutionNormal
  have hconj2 : ∀ x : G, x * z * x⁻¹ * (x * z * x⁻¹) = 1 := fun x => by
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  have hconj1 : ∀ x : G, x * z * x⁻¹ ≠ 1 := fun x h1 => hI.ne_one (by
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group)
  set t := g * z * g⁻¹ with htdef
  set s := h * z * h⁻¹ with hsdef
  by_contra hsP
  have ht2 : t * t = 1 := hconj2 g
  have hs2 : s * s = 1 := hconj2 h
  have hzR : IsUniqueInvolution R z := ht.isUniqueInvolution_of_mem_rSet_of_le hR hRK
  have hRnc := (ht.exists_ne_comm_of_mem_rSet hR).1
  have hR2 : IsPGroup 2 R := isPGroup_of_mem_rSet hR
  have hord : ∀ y : G, y * y = 1 → y ≠ 1 → orderOf y = 2 := fun y hy hy1 =>
    orderOf_eq_prime (by rw [_root_.sq]; exact hy) hy1
  have htK : t ∉ K := fun htK => htz (hU.2.2.1 t htK (hord t ht2 (hconj1 g)))
  have htR : t ∉ R := fun h1 => htK (hRK h1)
  have htN : t ∈ Subgroup.normalizer (R : Set G) := hTN htT
  have hcommz : ∀ x ∈ T, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hTz hx)
  have hPT : R ⊔ Subgroup.zpowers t ≤ T := sup_le hRT (Subgroup.zpowers_le.mpr htT)
  have hsz : s ≠ z := fun h1 => hsP (by rw [h1]; exact Subgroup.mem_sup_left hzR.mem)
  have hzt : ∀ y ∈ Subgroup.zpowers t, y = 1 ∨ y = t := fun y hy =>
    eq_one_or_eq_of_mem_zpowers_of_mul_self ht2 hy
  have hCRt : ¬ 4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) := by
    have := hA K (CoreAssembly.mem_conjClass_self K) z t hI ⟨g, rfl⟩ htz (hcommz t htT)
      (R ⊓ Subgroup.centralizer ({t} : Set G)) (hR2.to_le inf_le_left) (inf_le_left.trans hRK)
      inf_le_right
    omega
  have hcfg : AscL62.CoreCfg R (Subgroup.zpowers t) z t :=
    { quat := ht.quat hR
      hz := hzR
      V2 := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, pow_one]; exact hord t ht2 (hconj1 g))
      norm := fun y hy => conjSub_eq_of_mem_normalizer (Subgroup.zpowers_le.mpr htN hy)
      inter := fun y hy hyR => (hzt y hy).resolve_right fun h1 => htR (h1 ▸ hyR)
      ht := ⟨Subgroup.mem_zpowers t, hconj1 g, ht2, fun y hy _ => hzt y hy⟩ }
  obtain ⟨-, hsd⟩ := hcfg.eq_zpowers_and_isSemidihedral hCRt
  obtain ⟨a, b, M, hsdd⟩ := exists_sdData (hT2.to_le hPT) hsd
  have hM := hsdd.M_pos
  have ha2 : a * a ∈ R := mul_self_mem_of_mem_sup_zpowers ht2 htN hsdd.a_mem
  have hza : z = a ^ (4 * (M : ℤ)) := by
    have h4 : a ^ (4 * (M : ℤ)) ∈ R := by
      rw [show 4 * (M : ℤ) = 2 * (2 * M) by ring, zpow_mul, zpow_two]
      exact R.zpow_mem ha2 _
    refine ((hzR.unique _ h4 ?_).resolve_left ?_).symm
    · rw [← zpow_add, hsdd.zpow_eq_one_iff]; exact ⟨1, by ring⟩
    · rw [hsdd.zpow_eq_one_iff]
      rintro ⟨c, hc⟩
      have : (M : ℤ) * (4 - 8 * c) = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0 <;> omega
  have hCRs : ∀ y ∈ R, y * s = s * y → y = 1 ∨ y = z := by
    intro y hyR hys
    have hle := hA K (CoreAssembly.mem_conjClass_self K) z s hI ⟨h, rfl⟩ hsz (hcommz s hsT)
      (R ⊓ Subgroup.centralizer ({s} : Set G)) (hR2.to_le inf_le_left) (inf_le_left.trans hRK)
      inf_le_right
    have hzle : Subgroup.zpowers z ≤ R ⊓ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact ⟨hzR.mem, Subgroup.mem_centralizer_singleton_iff.mpr (hcommz s hsT).symm⟩
    have heq : Subgroup.zpowers z = R ⊓ Subgroup.centralizer ({s} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hzle (by
        rw [Nat.card_zpowers, hord z hI.sq hI.ne_one]; exact hle)
    have hy : y ∈ Subgroup.zpowers z := by
      rw [heq]
      exact ⟨hyR, Subgroup.mem_centralizer_singleton_iff.mpr hys⟩
    exact eq_one_or_eq_of_mem_zpowers_of_mul_self hI.sq hy
  have hKs : conjSub h K ∈ CoreAssembly.conjClass K := ⟨h, rfl⟩
  have hIs : IsUniqueInvolution (conjSub h K) s := hI.conj h
  have hkey : ∀ x ∈ R ⊔ Subgroup.zpowers t, x ∉ R → x * s = s * x → False := by
    intro x hxP hxR hxs
    have hx2R : x * x ∈ R := mul_self_mem_of_mem_sup_zpowers ht2 htN hxP
    have hx2s : x * x * s = s * (x * x) := by
      calc x * x * s = x * (x * s) := by group
        _ = x * (s * x) := by rw [hxs]
        _ = s * x * x := by rw [← mul_assoc, hxs]
        _ = s * (x * x) := by group
    obtain ⟨hx2, y, -, hyt⟩ := conj_of_not_mem_of_isSemidihedral hR2 hzR hRnc ht2 htR htN hsd
      hxP hxR (hCRs _ hx2R hx2s)
    have hxzP : x * z ∈ R ⊔ Subgroup.zpowers t :=
      Subgroup.mul_mem _ hxP (Subgroup.mem_sup_left hzR.mem)
    have hxzR : x * z ∉ R := fun h1 => hxR (by
      have := R.mul_mem h1 (R.inv_mem hzR.mem)
      rwa [mul_inv_cancel_right] at this)
    have hxz : x * z = z * x := hcommz x (hPT hxP)
    have hxz2 : x * z * (x * z) = 1 := by
      calc x * z * (x * z) = x * (z * x) * z := by group
        _ = x * (x * z) * z := by rw [← hxz]
        _ = x * x * (z * z) := by group
        _ = 1 := by rw [hx2, hI.sq, one_mul]
    obtain ⟨-, y', -, hy't⟩ := conj_of_not_mem_of_isSemidihedral hR2 hzR hRnc ht2 htR htN hsd
      hxzP hxzR (Or.inl hxz2)
    have hxzs : x * z * s = s * (x * z) := by
      calc x * z * s = x * (z * s) := by group
        _ = x * (s * z) := by rw [(hcommz s hsT).symm]
        _ = s * x * z := by rw [← mul_assoc, hxs]
        _ = s * (x * z) := by group
    have hx1 : x ≠ 1 := fun h1 => hxR (h1 ▸ R.one_mem)
    have hxne : x ≠ z := fun h1 => hxR (h1 ▸ hzR.mem)
    have hVle : Subgroup.zpowers z ≤
        Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
      rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hx2 hw with rfl | rfl
      · group
      · exact hxz
    have hVcard : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z) = 4 := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hVle (by
          rw [Subgroup.disjoint_def]
          intro w hwx hwz
          rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hx2 hwx with h1 | rfl
          · exact h1
          · rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hI.sq hwz with h1 | h1
            · exact h1
            · exact absurd h1 hxne),
        Nat.card_zpowers, Nat.card_zpowers, hord x hx2 hx1, hord z hI.sq hI.ne_one]
    have hVs : ∀ w ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z, w * s = s * w := by
      intro w hw
      have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤
          Subgroup.centralizer ({s} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hxs
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommz s hsT).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    have hVN : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤
        Subgroup.normalizer ((conjSub h K : Subgroup G) : Set G) := fun w hw =>
      ht.mem_normalizer_of_commute hKs hIs (hVs w hw)
    have hVT : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ T :=
      sup_le (Subgroup.zpowers_le.mpr (hPT hxP)) (Subgroup.zpowers_le.mpr (hRT hzR.mem))
    obtain ⟨Rs, hRs, hRsN⟩ := AscL62.exists_sylow_normalized (hT2.to_le hVT) hVN
    have hVNRs : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤
        Subgroup.normalizer ((Rs : Subgroup G) : Set G) := fun w hw =>
      mem_normalizer_iff_conjSub_eq.mpr (hRsN w hw)
    have hRsR : Rs ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hKs hRs
    have h8 := (ht.exists_ne_comm_of_mem_rSet hRsR).2
    obtain ⟨k, hk⟩ := hRs.2.1.exists_card_eq
    have hk3 : 3 ≤ k := by
      by_contra hk3
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h4 : 4 ∣ Nat.card Rs := by
      rw [hk, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    have hsRs : s ∈ Rs := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥Rs) 2
        (dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4)
      have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
      have huu : (u : G) * u = 1 := by rw [← _root_.sq, ← hu', pow_orderOf_eq_one]
      have hu1 : (u : G) ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hu'
        omega
      have := (hIs.unique u (hRs.1 u.2) huu).resolve_left hu1
      exact this ▸ u.2
    have hfixv : ∀ v ∈ R ⊔ Subgroup.zpowers t, (∃ w : G, w * z * w⁻¹ = v) → v * s = s * v →
        Nat.card ↥(Rs ⊓ Subgroup.centralizer ({v} : Set G)) = 2 := by
      intro v hvP hvz hvs
      have hle := hA (conjSub h K) hKs s v hIs hvz (fun h1 => hsP (h1 ▸ hvP)) hvs
        (Rs ⊓ Subgroup.centralizer ({v} : Set G)) (hRs.2.1.to_le inf_le_left)
        (inf_le_left.trans hRs.1) inf_le_right
      have hne : Rs ⊓ Subgroup.centralizer ({v} : Set G) ≠ ⊥ := by
        intro hbot
        have hmem : s ∈ Rs ⊓ Subgroup.centralizer ({v} : Set G) :=
          ⟨hsRs, Subgroup.mem_centralizer_singleton_iff.mpr hvs.symm⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hconj1 h hmem
      have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
      omega
    refine false_of_card_centralizer_eq_two hVcard hVNRs h4 fun v hv hv1 => ?_
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hxz hv
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hx2 (Subgroup.zpow_mem _
        (Subgroup.mem_zpowers x) i) with hi | hi <;>
      rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hI.sq (Subgroup.zpow_mem _
        (Subgroup.mem_zpowers z) j) with hj | hj <;>
      rw [hi, hj] at hv1 ⊢
    · exact absurd (one_mul 1) hv1
    · rw [one_mul]
      exact hfixv z (Subgroup.mem_sup_left hzR.mem) ⟨1, by group⟩ (hcommz s hsT).symm
    · rw [mul_one]
      exact hfixv x hxP ⟨y * g, by rw [← hyt, htdef]; group⟩ hxs
    · exact hfixv (x * z) hxzP ⟨y' * g, by rw [← hy't, htdef]; group⟩ hxzs
  obtain ⟨x, hxP, hxs, hx1, hxa⟩ := hsdd.exists_centralized hs2 hsN
  by_cases hxR : x ∈ R
  · rcases hCRs x hxR hxs.symm with h1 | h1
    · exact hx1 h1
    · exact hxa (h1.trans hza)
  · exact hkey x hxP hxR hxs.symm

theorem mem_sup_of_allTypeTwo (ht : Setup194Three K z) (hA : AllTypeTwo K z)
    {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K)) (hRK : R ≤ K)
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hRT : R ≤ T)
    (hTN : T ≤ Subgroup.normalizer (R : Set G)) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    {g : G} (htT : g * z * g⁻¹ ∈ T) (htz : g * z * g⁻¹ ≠ z) {h : G} (hsT : h * z * h⁻¹ ∈ T) :
    h * z * h⁻¹ ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹) := by
  have hI := ht.isUniqueInvolution
  have hconj2 : ∀ x : G, x * z * x⁻¹ * (x * z * x⁻¹) = 1 := fun x => by
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  refine mem_of_mem_normalizer_imp hT2 hTN htT (hconj2 g)
    (X := {x | ∃ w : G, w * z * w⁻¹ = x}) ?_ ?_ ⟨g, rfl⟩ ?_ ⟨h, rfl⟩ hsT
  · rintro x ⟨w, rfl⟩
    exact hconj2 w
  · rintro x ⟨w, rfl⟩ y -
    exact ⟨y * w, by group⟩
  · rintro s ⟨w, rfl⟩ hsT' hsN'
    exact mem_sup_of_mem_normalizer_of_allTypeTwo ht hA hR hRK hT2 hRT hTN hTz htT htz hsT' hsN'

end CFSG.ClassicalInvolution.Q3.Q3T6.SD
