module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11W
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11Y
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11S
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S8

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace X11

theorem odd_orderOf_of_mem_core {L : Type*} [Group L] [Finite L] {u : L}
    (hu : u ∈ pPrimeCore 2 L) : Odd (orderOf u) := by
  have h1 := orderOf_dvd_natCard (⟨u, hu⟩ : ↥(pPrimeCore 2 L))
  rw [Subgroup.orderOf_mk] at h1
  have h2 : ¬ 2 ∣ Nat.card (pPrimeCore 2 L) :=
    (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := L))
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  exact fun h3 => h2 (h3.trans h1)

theorem eq_one_of_mem_core {L : Type*} [Group L] [Finite L] {u : L} (hu : u ∈ pPrimeCore 2 L)
    {n : ℕ} (hn : u ^ 2 ^ n = 1) : u = 1 := by
  have hodd := odd_orderOf_of_mem_core hu
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · rw [hk] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, k.succ_ne_zero⟩))

end X11

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem a_mem_Lc (I : In81) (F : d.Facts) : h.a ∈ conjugate h.K (h.x * d.g) := by
  rw [mem_conjugate_iff, conj_c_a I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F]
  exact d.tau_K

theorem z_mem_Lc (F : d.Facts) : d.z ∈ conjugate h.K (h.x * d.g) := by
  rw [mem_conjugate_iff]
  have h1 : d.g * d.z * d.g⁻¹ = d.z := by
    calc d.g * d.z * d.g⁻¹ = d.g * (d.g⁻¹ * d.z * d.g) * d.g⁻¹ := by rw [F.z_g]
      _ = d.z := by group
  have h2 : h.x * d.z * h.x⁻¹ = d.z := by
    calc h.x * d.z * h.x⁻¹ = h.x * (h.x⁻¹ * d.z * h.x) * h.x⁻¹ := by rw [d.x_inv_z_x]
      _ = d.z := by group
  rw [show h.x * d.g * d.z * (h.x * d.g)⁻¹ = h.x * (d.g * d.z * d.g⁻¹) * h.x⁻¹ by group, h1, h2]
  exact H₁.kloc.fixedLayer_le_K (h.toHyp52.D_le_JB d.z_D)

theorem Lc_le_centralizer :
    conjugate h.K (h.x * d.g) ≤ centralizer ({h.a * d.sigma} : Set H) := by
  intro y hy
  rw [mem_conjugate_iff] at hy
  rw [mem_centralizer_singleton_iff, ← conj_b]
  have h1 := d.comm_b_of_mem_M3 (mem_sup_left hy : h.x * d.g * y * (h.x * d.g)⁻¹ ∈ h.M3)
  calc y * ((h.x * d.g)⁻¹ * d.b * (h.x * d.g)) =
        (h.x * d.g)⁻¹ * ((h.x * d.g * y * (h.x * d.g)⁻¹) * d.b) * (h.x * d.g) := by group
    _ = (h.x * d.g)⁻¹ * (d.b * (h.x * d.g * y * (h.x * d.g)⁻¹)) * (h.x * d.g) := by rw [h1]
    _ = (h.x * d.g)⁻¹ * d.b * (h.x * d.g) * y := by group

variable {v : H} (hv : d.IsV v) (I : In81) (hst : d.Stage7 v)
include hv I hst

theorem exists_w
    (hK : Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 3 1) :
    ∃ w ∈ h.U81 v, w ∉ h.S ∧ w * w = 1 ∧ w * (h.a * d.sigma) = h.a * d.sigma * w ∧
      ∃ ℓ ∈ conjugate h.K (h.x * d.g), ℓ⁻¹ * h.a * ℓ = w ∨ ℓ⁻¹ * (h.a * d.z) * ℓ = w := by
  have F := hst.facts
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := conjugate h.K (h.x * d.g)
  set R := h.U81 v ⊓ centralizer ({h.a * d.sigma} : Set H)
  obtain ⟨-, R', hR'⟩ := Seven.IsSylowIn.inf_of_le_normalizer
    (isSylowIn_R hv I F (not_conj_asigma_sigma F hst.not_b_bz) hst.conj_asigma)
    Lc_le_centralizer centralizer_asigma_le_normalizer_L
  have hmemR' : ∀ x : ↥L, x ∈ (R' : Subgroup ↥L) ↔ (x : H) ∈ R := fun x => by
    rw [hR', mem_subgroupOf, mem_inf]
    exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, x.2⟩⟩
  set e := L_bar_equiv (h := h) (h.x * d.g)
  set φ : ↥L →* ↥h.K ⧸ pPrimeCore 2 ↥h.K :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L))
  have hφsurj : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφeq : ∀ x y : ↥L, φ x = φ y →
      (QuotientGroup.mk x : ↥L ⧸ pPrimeCore 2 ↥L) = QuotientGroup.mk y := fun x y hxy => by
    have h1 : e (QuotientGroup.mk x) = e (QuotientGroup.mk y) := hxy
    exact e.injective h1
  have hφone : ∀ x : ↥L, φ x = 1 → x ∈ pPrimeCore 2 ↥L := fun x hx => by
    rw [← map_one φ] at hx
    have h1 := hφeq x 1 hx
    rwa [QuotientGroup.mk_one, QuotientGroup.eq_one_iff] at h1
  set T : Sylow 2 (↥h.K ⧸ pPrimeCore 2 ↥h.K) := R'.mapSurjective hφsurj with hT
  have hTmem : ∀ t, t ∈ (T : Subgroup _) ↔ ∃ r ∈ (R' : Subgroup ↥L), φ r = t := fun t => by
    rw [hT, Sylow.coe_mapSurjective, mem_map]
  have ha1 : h.a ≠ 1 := fun h1 => by
    have h2 := h.orderOf_a
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hz1 : d.z ≠ 1 := fun h1 => by
    have h2 := d.z_ord
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  set aL : ↥L := ⟨h.a, a_mem_Lc I F⟩
  set zL : ↥L := ⟨d.z, z_mem_Lc F⟩
  have haa : aL * aL = 1 := Subtype.ext (Six.a_mul_a_self h.toHyp52)
  have hzz : zL * zL = 1 := Subtype.ext d.z_mul_self
  have hazaz : aL * zL * (aL * zL) = 1 :=
    Subtype.ext (X11.mul_mul_self_of_comm d.z_comm_a (Six.a_mul_a_self h.toHyp52) d.z_mul_self)
  have haz1 : aL * zL ≠ 1 := fun h1 => by
    have h2 : h.a * d.z = 1 := congrArg Subtype.val h1
    apply d.z_ne_a
    rw [eq_inv_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right (Six.a_mul_a_self h.toHyp52)]
  have haR : h.a ∈ R := mem_inf.mpr ⟨mem_sup_left h.toHyp52.a_mem_S,
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (mem_inf.mp (asigma_mem_ZF I F)).2 _ (a_mem_F I F))⟩
  have hzR : d.z ∈ R := mem_inf.mpr ⟨mem_sup_left (h.toHyp52.D_le_S d.z_D),
    mem_centralizer_singleton_iff.mpr
      (d.comm_z_of_mem_S (mul_mem h.toHyp52.a_mem_S d.sigma_mem_S)).symm⟩
  have hsaT : φ aL ∈ (T : Subgroup _) := (hTmem _).mpr ⟨aL, (hmemR' aL).mpr haR, rfl⟩
  have hszT : φ zL ∈ (T : Subgroup _) := (hTmem _).mpr ⟨zL, (hmemR' zL).mpr hzR, rfl⟩
  have hsq : ∀ x : ↥L, x * x = 1 → φ x * φ x = 1 := fun x hx => by rw [← map_mul, hx, map_one]
  have hne1 : ∀ x : ↥L, x * x = 1 → x ≠ 1 → φ x ≠ 1 := fun x hx hx1 h1 =>
    hx1 (X11.eq_one_of_mem_core (hφone x h1) (n := 1) (by rw [pow_one, pow_two, hx]))
  have hsa1 : φ aL ≠ 1 := hne1 aL haa fun h1 => ha1 (congrArg Subtype.val h1)
  have hsz1 : φ zL ≠ 1 := hne1 zL hzz fun h1 => hz1 (congrArg Subtype.val h1)
  have hne : φ aL ≠ φ zL := fun h1 => by
    have h2 : aL⁻¹ * zL ∈ pPrimeCore 2 ↥L := QuotientGroup.eq.mp (hφeq _ _ h1)
    rw [inv_eq_of_mul_eq_one_right haa] at h2
    exact haz1 (X11.eq_one_of_mem_core h2 (n := 1) (by rw [pow_one, pow_two, hazaz]))
  obtain ⟨t, htT, ht2, ht1, htc⟩ : ∃ t ∈ (T : Subgroup _), t * t = 1 ∧ t ≠ 1 ∧
      ¬ (φ aL * t = t * φ aL ∧ φ zL * t = t * φ zL) := by
    by_contra hno
    exact hne (sp43_eq_of_comm_inv hK T hsaT hszT (hsq _ haa) hsa1 (hsq _ hzz) hsz1
      fun t ht h2 h1 => Classical.byContradiction fun hc => hno ⟨t, ht, h2, h1, hc⟩)
  obtain ⟨r, hrR', rfl⟩ := (hTmem _).mp htT
  have hrR := (hmemR' r).mp hrR'
  have hr2 : r * r = 1 := by
    have h1 : φ (r * r) = 1 := by rw [map_mul]; exact ht2
    obtain ⟨n, hn⟩ := R'.isPGroup' ⟨r * r, mul_mem hrR' hrR'⟩
    refine X11.eq_one_of_mem_core (hφone _ h1) (n := n) ?_
    have := congrArg Subtype.val hn
    simpa using this
  refine ⟨(r : H), (mem_inf.mp hrR).1, fun hrS => htc ⟨?_, ?_⟩, congrArg Subtype.val hr2,
    mem_centralizer_singleton_iff.mp (mem_inf.mp hrR).2, ?_⟩
  · rw [← map_mul, ← map_mul,
      show aL * r = r * aL from Subtype.ext (h.toHyp52.comm_a hrS).symm]
  · rw [← map_mul, ← map_mul,
      show zL * r = r * zL from Subtype.ext (d.comm_z_of_mem_S hrS).symm]
  have hord : ∀ y : ↥h.K ⧸ pPrimeCore 2 ↥h.K, y * y = 1 → y ≠ 1 → orderOf y = 2 :=
    fun y h2 h1 => orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  have hlift : ∀ (u : ↥L) (g : ↥h.K ⧸ pPrimeCore 2 ↥h.K), u * u = 1 → g⁻¹ * φ u * g = φ r →
      ∃ ℓ : ↥L, ℓ⁻¹ * u * ℓ = r := by
    intro u g hu hg
    obtain ⟨ℓ, rfl⟩ := hφsurj g
    have h1 : φ (ℓ⁻¹ * u * ℓ) = φ r := by rw [map_mul, map_mul, map_inv]; exact hg
    exact X11.exists_conj_of_mk_conj hu hr2 (hφeq _ _ h1)
  have hn : ∀ g, g⁻¹ * φ aL * g ≠ φ (aL * zL) := by
    intro g hg
    obtain ⟨ℓ, rfl⟩ := hφsurj g
    have h1 : φ (ℓ⁻¹ * aL * ℓ) = φ (aL * zL) := by rw [map_mul, map_mul, map_inv]; exact hg
    obtain ⟨ℓ', hℓ'⟩ := X11.exists_conj_of_mk_conj haa hazaz (hφeq _ _ h1)
    have h2 : (ℓ' : H)⁻¹ * h.a * ℓ' = h.a * d.z := congrArg Subtype.val hℓ'
    have h3 := conj_a_of_mem_ZF hv I F (c := (ℓ' : H))
      (by rw [h2]; exact mul_mem (a_mem_ZF I F) (z_mem_ZF I F))
    rw [h2] at h3
    rcases h3 with h3 | h3
    · exact hz1 (mul_left_cancel (h3.trans (mul_one _).symm))
    · exact ha1 (mul_right_cancel (h3.trans (one_mul _).symm))
  rcases X11.psp4_conj_of_not_conj Nat.prime_three (by norm_num) hK (hord _ (hsq _ haa) hsa1)
    (hord _ (hsq _ hazaz) (hne1 _ hazaz haz1)) (hord _ ht2 ht1) hn with ⟨g, hg⟩ | ⟨g, hg⟩
  · obtain ⟨ℓ, hℓ⟩ := hlift aL g haa hg
    exact ⟨(ℓ : H), ℓ.2, Or.inl (congrArg Subtype.val hℓ)⟩
  · obtain ⟨ℓ, hℓ⟩ := hlift (aL * zL) g hazaz hg
    exact ⟨(ℓ : H), ℓ.2, Or.inr (congrArg Subtype.val hℓ)⟩

theorem not_conj_w_asigma {w ℓ : H} (hℓC : ℓ ∈ centralizer ({h.a * d.sigma} : Set H))
    (hℓ : ℓ⁻¹ * h.a * ℓ = w ∨ ℓ⁻¹ * (h.a * d.z) * ℓ = w) {s : H}
    (hsw : s * w * s⁻¹ = w * (h.a * d.sigma)) : False := by
  have F := hst.facts
  have hℓc : ℓ * (h.a * d.sigma) * ℓ⁻¹ = h.a * d.sigma := by
    rw [mem_centralizer_singleton_iff.mp hℓC, mul_inv_cancel_right]
  have hσ := d.sigma_not_mem_DP I.cf1 I.cf2 F
  have haa := Six.a_mul_a_self h.toHyp52
  rcases hℓ with hℓ | hℓ
  · have key : (ℓ * s⁻¹ * ℓ⁻¹)⁻¹ * h.a * (ℓ * s⁻¹ * ℓ⁻¹) = d.sigma := by
      calc (ℓ * s⁻¹ * ℓ⁻¹)⁻¹ * h.a * (ℓ * s⁻¹ * ℓ⁻¹) = ℓ * (s * (ℓ⁻¹ * h.a * ℓ) * s⁻¹) * ℓ⁻¹ := by
            group
        _ = ℓ * (w * (h.a * d.sigma)) * ℓ⁻¹ := by rw [hℓ, hsw]
        _ = (ℓ * w * ℓ⁻¹) * (ℓ * (h.a * d.sigma) * ℓ⁻¹) := by group
        _ = h.a * (h.a * d.sigma) := by rw [hℓc, ← hℓ]; group
        _ = d.sigma := by rw [← mul_assoc, haa, one_mul]
    have h1 := conj_a_of_mem_ZF hv I F (c := ℓ * s⁻¹ * ℓ⁻¹) (by rw [key]; exact sigma_mem_ZF I F)
    rw [key] at h1
    rcases h1 with h1 | h1
    · exact hσ (h1 ▸ mem_sup_right h.toHyp52.a_mem_P)
    · exact hσ (h1 ▸ mem_sup_left d.z_D)
  · have key : (ℓ * s⁻¹ * ℓ⁻¹)⁻¹ * (h.a * d.z) * (ℓ * s⁻¹ * ℓ⁻¹) = d.z * d.sigma := by
      calc (ℓ * s⁻¹ * ℓ⁻¹)⁻¹ * (h.a * d.z) * (ℓ * s⁻¹ * ℓ⁻¹) =
            ℓ * (s * (ℓ⁻¹ * (h.a * d.z) * ℓ) * s⁻¹) * ℓ⁻¹ := by group
        _ = ℓ * (w * (h.a * d.sigma)) * ℓ⁻¹ := by rw [hℓ, hsw]
        _ = (ℓ * w * ℓ⁻¹) * (ℓ * (h.a * d.sigma) * ℓ⁻¹) := by group
        _ = h.a * (d.z * h.a) * d.sigma := by rw [hℓc, ← hℓ]; group
        _ = d.z * d.sigma := by
            rw [d.z_comm_a, ← mul_assoc h.a h.a, haa, one_mul]
    have h1 := conj_az_of_mem_ZF hv I F (c := ℓ * s⁻¹ * ℓ⁻¹)
      (by rw [key]; exact mul_mem (z_mem_ZF I F) (sigma_mem_ZF I F))
    rw [key, ← d.z_comm_a] at h1
    exact hσ (mul_left_cancel h1 ▸ mem_sup_right h.toHyp52.a_mem_P)

end Data

end L81Hyp

end Hyp59

theorem gs81Step11Input
    (I : In81) : GS81Step11Input := by
  intro H _ _ h H₁ d v hst hJ hK
  obtain ⟨w, hwU, hwS, hw2, hwc, ℓ, hℓL, hℓ⟩ := Hyp59.L81Hyp.Data.exists_w hst.isV I hst hK
  refine ⟨w, hwU, hwS, ?_⟩
  rcases Hyp59.L81Hyp.Data.conj_or_le_sup hst.isV I hst hJ hwU hwS hw2 hwc with
    ⟨s, -, hsw⟩ | hle
  · exact (Hyp59.L81Hyp.Data.not_conj_w_asigma hst.isV I hst
      (Hyp59.L81Hyp.Data.Lc_le_centralizer hℓL) hℓ hsw).elim
  · exact hle

end CFSG.ComponentClassification.GSThmB
