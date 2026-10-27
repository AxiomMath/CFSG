module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83S2Sigma

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight

theorem oddBarAction_eq_one_of_mem {G : Type*} [Group G] {L : Subgroup G} {n : G}
    (hn : n ∈ (pPrimeCore 2 L).map L.subtype) (hnN : n ∈ normalizer (L : Set G)) :
    oddBarAction L ⟨n, hnN⟩ = 1 := by
  obtain ⟨n', hn', rfl⟩ := mem_map.mp hn
  refine (oddBarAction_of_mem n').trans ?_
  rw [(QuotientGroup.eq_one_iff n').mpr hn', map_one]

end Eight

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

namespace S2Data

variable (d : S2Data H)
include d

theorem epsL_mul_self : d.epsL * d.epsL = 1 := by
  show Eight.oddBarAction d.L ⟨d.e, d.e_mem_normalizer_L⟩ *
    Eight.oddBarAction d.L ⟨d.e, d.e_mem_normalizer_L⟩ = 1
  rw [← map_mul, show (⟨d.e, d.e_mem_normalizer_L⟩ : normalizer (d.L : Set X)) *
    ⟨d.e, d.e_mem_normalizer_L⟩ = 1 from Subtype.ext d.e_mul_self, map_one]

theorem odd_card_oddCore_L : Odd (Nat.card ((pPrimeCore 2 d.L).map d.L.subtype)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_map_of_injective d.L.subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem mem_oddCore_of_oddBarAction (hCF1 : CFSec8Simple) {u : X} (hu : u ∈ d.L)
    (h1 : Eight.oddBarAction d.L ⟨u, le_normalizer hu⟩ = 1) :
    u ∈ (pPrimeCore 2 d.L).map d.L.subtype := by
  have h2 : MulAut.conj ((⟨u, hu⟩ : d.L) : d.L ⧸ pPrimeCore 2 d.L) = 1 := by
    rw [← Eight.oddBarAction_of_mem]
    exact h1
  have h3 : ((⟨u, hu⟩ : d.L) : d.L ⧸ pPrimeCore 2 d.L) = 1 :=
    conj_eq_conj_of_center_eq_bot (d.center_Lbar hCF1) (h2.trans (map_one MulAut.conj).symm)
  exact ⟨⟨u, hu⟩, (QuotientGroup.eq_one_iff _).mp h3, rfl⟩

theorem exists_lift (hCF1 : CFSec8Simple) {y : MulAut (d.L ⧸ pPrimeCore 2 d.L)}
    (hy : y ∈ Cat8.Inn (d.L ⧸ pPrimeCore 2 d.L) ⊔ zpowers d.epsL)
    (hya : y * d.alphaL = d.alphaL * y) :
    ∃ s : X, ∃ hs : s ∈ normalizer (d.L : Set X), s * h.a = h.a * s ∧
      s ∈ centralizer ({d.w} : Set X) ∧ Eight.oddBarAction d.L ⟨s, hs⟩ = y := by
  have hea : h.a * d.e * h.a⁻¹ = d.e := by rw [← d.e_comm_a, mul_inv_cancel_right]
  obtain ⟨k, ⟨mbar, rfl⟩, hyk⟩ :=
    Eight.mem_sup_zpowers_cases (Eight.mem_normalizer_range_conj d.epsL) d.epsL_mul_self hy
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective mbar
  have hmN : (m : X) ∈ normalizer (d.L : Set X) := le_normalizer m.2
  have hmw : (m : X) ∈ centralizer ({d.w} : Set X) := d.L_le_centralizer_w m.2
  have hm : Eight.oddBarAction d.L ⟨m, hmN⟩ = MulAut.conj ((m : d.L) : d.L ⧸ pPrimeCore 2 d.L) :=
    Eight.oddBarAction_of_mem m
  have hma : (m : X)⁻¹ * (h.a * m * h.a⁻¹) ∈ d.L :=
    mul_mem (inv_mem m.2) ((mem_normalizer_iff.mp d.a_mem_normalizer_L _).mp m.2)
  obtain ⟨s₀, hs₀N, hs₀w, hs₀y, hs₀L⟩ : ∃ s₀ : X, ∃ hs₀ : s₀ ∈ normalizer (d.L : Set X),
      s₀ ∈ centralizer ({d.w} : Set X) ∧ Eight.oddBarAction d.L ⟨s₀, hs₀⟩ = y ∧
        s₀⁻¹ * (h.a * s₀ * h.a⁻¹) ∈ d.L := by
    rcases hyk with rfl | rfl
    · exact ⟨m, hmN, hmw, hm, hma⟩
    · refine ⟨m * d.e, mul_mem hmN d.e_mem_normalizer_L, mul_mem hmw d.e_mem_centralizer_w, ?_,
        ?_⟩
      · rw [show (⟨(m : X) * d.e, mul_mem hmN d.e_mem_normalizer_L⟩ : normalizer (d.L : Set X)) =
          ⟨m, hmN⟩ * ⟨d.e, d.e_mem_normalizer_L⟩ from Subtype.ext rfl, map_mul, hm]
      · have h2 := (mem_normalizer_iff.mp (inv_mem d.e_mem_normalizer_L) _).mp hma
        rw [show ((m : X) * d.e)⁻¹ * (h.a * (m * d.e) * h.a⁻¹) =
            d.e⁻¹ * ((m : X)⁻¹ * (h.a * m * h.a⁻¹)) * d.e⁻¹⁻¹ by
          rw [show h.a * ((m : X) * d.e) * h.a⁻¹ = (h.a * m * h.a⁻¹) * (h.a * d.e * h.a⁻¹) by
            group, hea]
          group]
        exact h2
  have hu1 : Eight.oddBarAction d.L ⟨s₀⁻¹ * (h.a * s₀ * h.a⁻¹), le_normalizer hs₀L⟩ = 1 := by
    rw [show (⟨s₀⁻¹ * (h.a * s₀ * h.a⁻¹), le_normalizer hs₀L⟩ : normalizer (d.L : Set X)) =
        (⟨s₀, hs₀N⟩ : normalizer (d.L : Set X))⁻¹ * (⟨h.a, d.a_mem_normalizer_L⟩ * ⟨s₀, hs₀N⟩ *
          (⟨h.a, d.a_mem_normalizer_L⟩ : normalizer (d.L : Set X))⁻¹) from Subtype.ext rfl,
      map_mul, map_inv, map_mul, map_mul, map_inv, hs₀y]
    show y⁻¹ * (d.alphaL * y * d.alphaL⁻¹) = 1
    rw [← hya, mul_inv_cancel_right, inv_mul_cancel]
  have hu := d.mem_oddCore_of_oddBarAction hCF1 hs₀L hu1
  have haN : h.a ∈ normalizer (((pPrimeCore 2 d.L).map d.L.subtype : Subgroup X) : Set X) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic d.L (pPrimeCore 2 d.L)
      d.a_mem_normalizer_L
  obtain ⟨n, hn, hfix⟩ :=
    Eight.exists_conj_fixed_mul d.odd_card_oddCore_L (Six.a_mul_a_self h) haN hu
  have hnL : n ∈ d.L := (map_subtype_le _) hn
  refine ⟨s₀ * n, mul_mem hs₀N (le_normalizer hnL), ?_,
    mul_mem hs₀w (d.L_le_centralizer_w hnL), ?_⟩
  · calc s₀ * n * h.a = h.a * (s₀ * n) * h.a⁻¹ * h.a := by rw [hfix]
      _ = h.a * (s₀ * n) := by group
  · rw [show (⟨s₀ * n, mul_mem hs₀N (le_normalizer hnL)⟩ : normalizer (d.L : Set X)) =
        ⟨s₀, hs₀N⟩ * ⟨n, le_normalizer hnL⟩ from Subtype.ext rfl, map_mul, hs₀y,
      Eight.oddBarAction_eq_one_of_mem hn, mul_one]

theorem conj_mem_TX {s : X} (hs : s ∈ normalizer (d.L : Set X))
    (hsa : s ∈ centralizer ({h.a} : Set X)) {t : X} (ht : t ∈ d.TX) : s * t * s⁻¹ ∈ d.TX := by
  have hN : s ∈ normalizer (d.CLa : Set X) :=
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hs, le_normalizer hsa⟩)
  have h1 : conjugate d.CLa s⁻¹ = d.CLa := by
    ext x
    rw [mem_conjugate_iff, inv_inv, mem_normalizer_iff.mp hN (s⁻¹ * x * s),
      show s * (s⁻¹ * x * s) * s⁻¹ = x by group]
  have h2 : conjugate d.TX s⁻¹ = d.TX := by
    rw [S2Data.TX, Six.conjugate_layerIn, h1]
  have h3 : s * t * s⁻¹ ∈ conjugate d.TX s⁻¹ := by
    rw [mem_conjugate_iff, show s⁻¹ * (s * t * s⁻¹) * s⁻¹⁻¹ = t by group]
    exact ht
  rwa [h2] at h3

theorem sigmaA_lift_cases {Lφ : Subgroup (MulAut (h.J ⧸ pPrimeCore 2 h.J))}
    (hLφ3 : ∀ N : Subgroup (MulAut (h.J ⧸ pPrimeCore 2 h.J)), N ≤ Lφ → (N.subgroupOf Lφ).Normal →
      Odd (Nat.card N) → N = ⊥)
    (hLφ4 : ∀ y ∈ centralizer ({d.phi} : Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))),
      (∀ l ∈ Lφ, y * l = l * y) → y = 1 ∨ y = d.phi)
    (hpsi : d.psiT = Lφ) {s : X} (hs : s ∈ normalizer (d.L : Set X))
    (hsa : s ∈ centralizer ({h.a} : Set X)) (hsw : s ∈ centralizer ({d.w} : Set X))
    (hsE : ∀ t ∈ layerIn (Eight.fixSubgroup d.alphaL), Eight.oddBarAction d.L ⟨s, hs⟩ t = t) :
    H.sigmaA ⟨s, hsa⟩ = 1 ∨ H.sigmaA ⟨s, hsa⟩ = d.phi := by
  set OL : Subgroup X := (pPrimeCore 2 d.L).map d.L.subtype with hOL
  set N₀ : Subgroup (MulAut (h.J ⧸ pPrimeCore 2 h.J)) :=
    ((d.TX ⊓ OL).subgroupOf (centralizer ({h.a} : Set X))).map H.sigmaA with hN₀
  have hAB : (d.TX ⊓ OL).subgroupOf (centralizer ({h.a} : Set X)) ≤ d.TXa :=
    fun _ hx => mem_subgroupOf.mpr (Subgroup.mem_inf.mp (mem_subgroupOf.mp hx)).1
  have hN₀le : N₀ ≤ d.psiT := map_mono hAB
  have hN₀n : (N₀.subgroupOf d.psiT).Normal := by
    refine Eight.normal_map_subgroupOf H.sigmaA hAB ?_
    intro x hx y hy
    have hx' : (x : X) ∈ d.TX ⊓ OL := hx
    have hy' : (y : X) ∈ d.TX := hy
    obtain ⟨hxT, hxO⟩ := Subgroup.mem_inf.mp hx'
    have hyN : (y : X) ∈ normalizer (OL : Set X) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic d.L (pPrimeCore 2 d.L)
        (le_normalizer (d.TX_le_L hy'))
    show (y : X) * x * (y : X)⁻¹ ∈ d.TX ⊓ OL
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hy' hxT) (inv_mem hy'),
      (mem_normalizer_iff.mp hyN _).mp hxO⟩
  have hN₀odd : Odd (Nat.card N₀) := by
    have h1 : Nat.card N₀ ∣ Nat.card ((d.TX ⊓ OL).subgroupOf (centralizer ({h.a} : Set X))) :=
      card_map_dvd _ _
    have h2 : Nat.card ((d.TX ⊓ OL).subgroupOf (centralizer ({h.a} : Set X))) ∣
        Nat.card OL := by
      rw [← card_map_of_injective (centralizer ({h.a} : Set X)).subtype_injective,
        subgroupOf_map_subtype]
      exact card_dvd_of_le (inf_le_left.trans inf_le_right)
    exact d.odd_card_oddCore_L.of_dvd_nat (h1.trans h2)
  have hN₀bot : N₀ = ⊥ := by
    rw [← hpsi] at hLφ3
    exact hLφ3 N₀ hN₀le hN₀n hN₀odd
  apply hLφ4
  ·
    rw [mem_centralizer_singleton_iff]
    show H.sigmaA ⟨s, hsa⟩ * H.sigmaA d.wC = H.sigmaA d.wC * H.sigmaA ⟨s, hsa⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hsw)
  ·
    intro l hl
    rw [← hpsi] at hl
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hl
    have htT : (t : X) ∈ d.TX := ht
    have htL : (t : X) ∈ d.L := d.TX_le_L htT
    have hsT := d.conj_mem_TX hs hsa htT
    have htE : ((⟨t, htL⟩ : d.L) : d.L ⧸ pPrimeCore 2 d.L) ∈
        layerIn (Eight.fixSubgroup d.alphaL) := by
      rw [d.E_eq]
      exact mem_map_of_mem d.piL (show (⟨t, htL⟩ : d.L) ∈ d.TX.subgroupOf d.L from htT)
    have hfix := hsE _ htE
    have hst : (s * t * s⁻¹ : X) ∈ d.L := (mem_normalizer_iff.mp hs _).mp htL
    have h1 : ((⟨s * t * s⁻¹, hst⟩ : d.L) : d.L ⧸ pPrimeCore 2 d.L) =
        ((⟨t, htL⟩ : d.L) : d.L ⧸ pPrimeCore 2 d.L) := hfix
    have hoO : (t : X)⁻¹ * (s * t * s⁻¹) ∈ OL :=
      ⟨_, QuotientGroup.eq.mp h1.symm, rfl⟩
    set sC : ↥(centralizer ({h.a} : Set X)) := ⟨s, hsa⟩ with hsC
    have ho : t⁻¹ * (sC * t * sC⁻¹) ∈ (d.TX ⊓ OL).subgroupOf (centralizer ({h.a} : Set X)) :=
      mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem htT) hsT, hoO⟩)
    have hσo : H.sigmaA (t⁻¹ * (sC * t * sC⁻¹)) = 1 := by
      have : H.sigmaA (t⁻¹ * (sC * t * sC⁻¹)) ∈ N₀ := mem_map_of_mem _ ho
      rwa [hN₀bot, mem_bot] at this
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, inv_mul_eq_one] at hσo
    calc H.sigmaA sC * H.sigmaA t =
        H.sigmaA sC * H.sigmaA t * (H.sigmaA sC)⁻¹ * H.sigmaA sC := by group
      _ = H.sigmaA t * H.sigmaA sC := by rw [← hσo]

theorem sq_mem_O0_of_cases (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {s : X}
    (hsa : s ∈ centralizer ({h.a} : Set X))
    (hc : H.sigmaA ⟨s, hsa⟩ = 1 ∨ H.sigmaA ⟨s, hsa⟩ = d.phi) : s * s ∈ h.O0 := by
  rcases hc with hc | hc
  · have h1 : (⟨s, hsa⟩ : ↥(centralizer ({h.a} : Set X))) ∈ H.sigmaA.ker := hc
    rw [H.ker_sigmaA] at h1
    have h1' : s ∈ h.C0 := h1
    exact d.sq_mem_O0 hCF1 hCF2 h1'
  · have h1 : H.sigmaA (⟨s, hsa⟩ * d.tauC) = 1 := by
      rw [map_mul, hc, d.phi_eq, ← map_mul,
        show d.tauC * d.tauC = 1 from Subtype.ext d.tau_sq, map_one]
    have h2 : (⟨s, hsa⟩ * d.tauC : ↥(centralizer ({h.a} : Set X))) ∈ H.sigmaA.ker := h1
    rw [H.ker_sigmaA] at h2
    have h2' : s * d.tau ∈ h.C0 := h2
    have h3 := d.sq_mul_mem_O0 hCF1 hCF2 h2' (Subgroup.mem_inf.mp d.tau_mem).1 d.tau_sq
    rwa [show s * d.tau * d.tau = s by rw [mul_assoc, d.tau_sq, mul_one]] at h3

end S2Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
