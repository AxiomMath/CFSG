module

public import CFSG.ClassicalInvolution.AschTight.S1916C14
public import CFSG.ClassicalInvolution.AschTight.S1916Inv

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.GorensteinWalter
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W : Subgroup G}

theorem exists_mul_of_mem_sup [IsSimpleGroup G] (hd : Sec19Data p f K z S W) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hs : s ∈ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ a ∈ (S : Subgroup G) ⊓ sec19X K z, a⁻¹ * s ∈ (S : Subgroup G) ⊓ centralizerModOdd ⊤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨e⟩, hFcard, hF, h3⟩ := Hall196.exists_data_of_tightBranchD hd.tight
  have : Finite (PGammaL2 (GaloisField p f)) := Hall196.finite_pGammaL2
  have hNC := sd_normalizer_eq hd
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := hd.hSz.trans hNC.ge
  set Ψ := normalizerToPGammaL2Mod e hFcard hF h3 with hΨ
  set E := ((S : Subgroup G).subgroupOf (Subgroup.normalizer (K : Set G))).map Ψ with hE
  have hE2 : IsPGroup 2 E := (S.isPGroup'.comap_subtype).map Ψ
  have hXN : sec19X K z ≤ Subgroup.normalizer (K : Set G) :=
    (sec19X_le_centralizer K z).trans hNC.ge
  have hSX' := Hall196.isSylow2In_map_hom Ψ
    (Hall196.isSylow2In_subgroupOf_of_le (isSylow2In_inf_sec19X hd) hXN)
  rw [Hall196.map_sec19X_eq_pGammaL2PGLRange hd e hFcard hF h3] at hSX'
  set D := (((S : Subgroup G) ⊓ sec19X K z).subgroupOf (Subgroup.normalizer (K : Set G))).map Ψ
    with hD
  set s' : Subgroup.normalizer (K : Set G) := ⟨s, hSN hsS⟩ with hs'
  have hsE : Ψ s' ∈ E := ⟨s', Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
  have hsL : Ψ s' ∈ pGammaL2PGLRange (GaloisField p f) := (psi_mem_iff hd e hFcard hF h3 s').mpr hs
  have hDE : D ≤ E := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).1
  have hmax := hSX'.2.2 (D ⊔ Subgroup.zpowers (Ψ s'))
    (sup_le hSX'.1 (Subgroup.zpowers_le.mpr hsL))
    (hE2.to_le (sup_le hDE (Subgroup.zpowers_le.mpr hsE))) le_sup_left
  have hsD : Ψ s' ∈ D := hmax ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨a', ha', hΨa⟩ := hsD
  have ha'A : (a' : G) ∈ (S : Subgroup G) ⊓ sec19X K z := Subgroup.mem_subgroupOf.mp ha'
  refine ⟨a', ha'A, (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem ha'A.1) hsS, ?_⟩
  have h1 : Ψ (a'⁻¹ * s') = 1 := by rw [map_mul, map_inv, hΨa, inv_mul_cancel]
  exact (psi_eq_one_iff e hFcard hF h3 (a'⁻¹ * s')).mp h1

theorem mem_sup_cStar_of_isSemidihedral [IsSimpleGroup G] (hd : Sec19Data p f K z S W)
    {R₁ : Subgroup G} (hR₁ : R₁ ∈ RSet (CoreAssembly.conjClass K)) (hR₁K : R₁ ≤ K) {s : G}
    (hsN : s ∈ Subgroup.normalizer (K : Set G)) (hsR : s ∈ Subgroup.normalizer (R₁ : Set G))
    (hs2 : s * s = 1) (hsR₁ : s ∉ R₁) (hSD : IsSemidihedral (R₁ ⊔ Subgroup.zpowers s)) :
    s ∈ sec19X K z ⊔ centralizerModOdd ⊤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := hd.tight
  obtain ⟨⟨e⟩, hFcard, hF, h3⟩ := Hall196.exists_data_of_tightBranchD ht
  have hs1 : s ≠ 1 := fun h => hsR₁ (h ▸ R₁.one_mem)
  have hsz2 : IsPGroup 2 ↥(Subgroup.zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hs2) hs1, pow_one])
  refine (psi_mem_iff hd e hFcard hF h3 ⟨s, hsN⟩).mp ?_
  rcases Nat.even_or_odd f with hfe | hfo
  swap
  · exact innerDiagonalTwo_of_odd hfo e hFcard hF h3 ⟨s, hsN⟩ (isPGroup_zpowers_mk hsz2
      (Subgroup.mem_zpowers s) hsN)
  set P := R₁ ⊔ Subgroup.zpowers s with hP
  obtain ⟨a, b, ha8, hPcard, -, -, -, hcl⟩ := hSD
  have haP : a ∈ P := hcl ▸ Subgroup.subset_closure (by simp)
  have hR₁2 := isPGroup_of_mem_rSet hR₁
  have hPN : P ≤ Subgroup.normalizer (R₁ : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hsR)
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (hR₁K.trans Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr hsN)
  have hcardP : Nat.card P = 2 * Nat.card R₁ := by
    have h1 := card_sup_mul_card_inf (A := R₁) (C := Subgroup.zpowers s)
      (Subgroup.zpowers_le.mpr hsR)
    have hbot : R₁ ⊓ Subgroup.zpowers s = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxR, hxs⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxs
      have hk : s ^ k = 1 ∨ s ^ k = s := by
        rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · left
          rw [← two_mul, zpow_mul, zpow_two, hs2, one_zpow]
        · right
          rw [zpow_add_one, zpow_mul, zpow_two, hs2, one_zpow, one_mul]
      rcases hk with hk | hk
      · rw [hk]; exact Subgroup.one_mem _
      · exact absurd (hk ▸ hxR) hsR₁
    rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers,
      orderOf_eq_prime (by rw [_root_.sq]; exact hs2) hs1] at h1
    rw [← hP] at h1
    omega
  have hP2 : IsPGroup 2 P := by
    obtain ⟨k, hk⟩ := hR₁2.exists_card_eq
    exact IsPGroup.of_card (n := k + 1) (by rw [hcardP, hk, pow_succ]; ring)
  have haN : a ∈ Subgroup.normalizer (K : Set G) := hPK haP
  have hcardinf : Nat.card R₁ ≤ 2 * Nat.card ↥(R₁ ⊓ Subgroup.zpowers a) := by
    have h1 := card_sup_mul_card_inf (A := R₁) (C := Subgroup.zpowers a)
      (Subgroup.zpowers_le.mpr (hPN haP))
    have h2 : Nat.card ↥(R₁ ⊔ Subgroup.zpowers a) ≤ Nat.card P :=
      Subgroup.card_le_of_le (sup_le le_sup_left (Subgroup.zpowers_le.mpr haP))
    rw [Nat.card_zpowers] at h1
    have h0 : 0 < orderOf a := by omega
    nlinarith
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hP2 ⟨a, haP⟩
  have ham : orderOf a = 2 ^ m := by rw [← hm, Subgroup.orderOf_mk]
  have hΨa := mem_range_inl_of_centralizes ht.branch.odd ht.branch.five hfe e hFcard hF h3 hR₁
    hR₁K (B := Subgroup.zpowers a) (fun x hx y hy => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_add, ← zpow_add, add_comm]) hcardinf ⟨m, ham⟩ haN (fun y hy => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy.2
      rw [← zpow_one_add, ← zpow_add_one, add_comm])
  have haR₁ : a ∉ R₁ := by
    intro haR
    have hle : Subgroup.zpowers a ≤ R₁ := Subgroup.zpowers_le.mpr haR
    have heq : Subgroup.zpowers a = R₁ := Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers]; omega)
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member hR₁).1
    rw [← heq] at hx hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hxy (by rw [← zpow_add, ← zpow_add, add_comm])
  have hidx : (R₁.subgroupOf P).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := R₁) (K := P)
    rw [inf_eq_left.mpr (le_sup_left : R₁ ≤ P), hcardP] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hsP : s ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have hasR : a⁻¹ * s ∈ R₁ := by
    have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a⁻¹, P.inv_mem haP⟩ : ↥P))
      (b := ⟨s, hsP⟩)).mpr (iff_of_false (fun h => haR₁ (by
        have := R₁.inv_mem (Subgroup.mem_subgroupOf.mp h)
        simpa using this)) (fun h => hsR₁ (Subgroup.mem_subgroupOf.mp h)))
    exact Subgroup.mem_subgroupOf.mp key
  have hasN : a⁻¹ * s ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ haN) hsN
  have hΨr := normalizerToPGammaL2Mod_mem_range_inl_of_mem e hFcard hF h3 (hR₁K hasR) hasN
  have e1 : (⟨s, hsN⟩ : Subgroup.normalizer (K : Set G)) = ⟨a, haN⟩ * ⟨a⁻¹ * s, hasN⟩ :=
    Subtype.ext (by simp)
  rw [e1, map_mul]
  exact Subgroup.mul_mem _ hΨa hΨr

theorem exists_mul_of_conj_mem [IsSimpleGroup G] (hd : Sec19Data p f K z S W) {g : G}
    (hgS : g * z * g⁻¹ ∈ (S : Subgroup G)) :
    ∃ a ∈ (S : Subgroup G) ⊓ sec19X K z,
      a⁻¹ * (g * z * g⁻¹) ∈ (S : Subgroup G) ⊓ centralizerModOdd ⊤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := hd.tight
  have htb := ht.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hΩ := hypOmegaMod_of_tightD ht
  have hKX := le_sec19X ht.branch.member
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
    hd.hSz.trans (sd_normalizer_eq hd).ge
  have hone : (1 : G) ∈ (S : Subgroup G) ⊓ centralizerModOdd ⊤ K := Subgroup.one_mem _
  by_cases hsz : g * z * g⁻¹ = z
  · refine ⟨g * z * g⁻¹, ⟨hgS, by rw [hsz]; exact hKX hI.mem⟩, ?_⟩
    rw [inv_mul_cancel]
    exact hone
  have hJ : conjSub g K ∈ CoreAssembly.conjClass K := ⟨g, rfl⟩
  have hJs : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := hI.conj g
  have htwin : conjSub g K ∉ twinSet (CoreAssembly.conjClass K) K := by
    rintro ⟨-, z', hz'K, hz'J⟩
    exact hsz ((hJs.eq hz'J).trans (hI.eq hz'K).symm)
  have hs2 : IsPGroup 2 ↥(Subgroup.zpowers (g * z * g⁻¹)) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hgS)
  obtain ⟨V, hV, hsV⟩ := IsSylow2In.exists_ge hs2
    (Subgroup.zpowers_le.mpr ⟨hJs.mem, hd.hSz hgS⟩ :
      Subgroup.zpowers (g * z * g⁻¹) ≤ conjSub g K ⊓ Subgroup.centralizer ({z} : Set G))
  have hsV' : g * z * g⁻¹ ∈ V := hsV (Subgroup.mem_zpowers _)
  have hsN := hSN hgS
  rcases Asc77.l6_2 p f ht.branch.odd ht.branch.five G _ hΩ K
      (CoreAssembly.mem_conjClass_self K) z hI (conjSub g K) hJ htwin _ hJs V hV hsV' with
    ⟨-, hKs⟩ | ⟨hV1, -, R₁, hR₁, hR₁K, hVR₁, hSD⟩ | ⟨hVU, -⟩ | ⟨-, hVK⟩
  · exact absurd (conjSub_eq_of_mem_normalizer hsN) hKs
  ·
    rw [hV1] at hVR₁ hSD
    have hsR₁ : g * z * g⁻¹ ∉ R₁ := fun h =>
      hsz ((hI.unique _ (hR₁K h) hJs.sq).resolve_left hJs.ne_one)
    exact exists_mul_of_mem_sup hd hgS (mem_sup_cStar_of_isSemidihedral hd hR₁ hR₁K hsN
      (hVR₁ (Subgroup.mem_zpowers _)) hJs.sq hsR₁ hSD)
  ·
    have hVX : V ≤ sec19X K z := le_iSup₂ (f := fun B (_ : B ∈ {A : Subgroup G |
      (A ∈ USet (CoreAssembly.conjClass K) ∨ A ∈ RSet (CoreAssembly.conjClass K)) ∧
        A ≤ Subgroup.centralizer ({z} : Set G)}) => B) V ⟨Or.inl hVU, hV.1.trans inf_le_right⟩
    refine ⟨g * z * g⁻¹, ⟨hgS, hVX hsV'⟩, ?_⟩
    rw [inv_mul_cancel]
    exact hone
  ·
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [inv_one, one_mul]
    exact ⟨hgS, Subgroup.mem_top _, hsN, mem_normalizer_oddCoreOf_of_mem_normalizer hsN,
      fun k hk => hVK (Subgroup.commutator_mem_commutator hsV' hk)⟩

theorem conj_mem_sec19X_of_le [IsSimpleGroup G] (hd : Sec19Data p f K z S W)
    (hC : (S : Subgroup G) ⊓ centralizerModOdd ⊤ K ≤ sec19X K z) {g : G}
    (hgS : g * z * g⁻¹ ∈ (S : Subgroup G)) : g * z * g⁻¹ ∈ sec19X K z := by
  obtain ⟨a, haA, hac⟩ := exists_mul_of_conj_mem hd hgS
  have e : g * z * g⁻¹ = a * (a⁻¹ * (g * z * g⁻¹)) := by group
  rw [e]
  exact (sec19X K z).mul_mem haA.2 (hC hac)

variable (p f) in
theorem c19_14Z_of (hC : C19_14CTmp p f) : C19_14ZTmp p f :=
  fun G _ _ _ K z S W hd h1 _ hgS => conj_mem_sec19X_of_le hd (hC G K z S W hd h1) hgS

variable (p f) in
theorem c19_14_of_C (hC : C19_14CTmp p f) (hB3 : GoldschmidtB3Tmp) : C19_14Tmp p f :=
  c19_14_of_Z p f (c19_14Z_of p f hC) hB3

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
