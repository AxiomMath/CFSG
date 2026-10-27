module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83S2Conj

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

noncomputable abbrev sigmaA (H : L83Hyp h) :
    ↥(centralizer ({h.a} : Set X)) →* MulAut (h.J ⧸ pPrimeCore 2 h.J) :=
  (Eight.oddBarAction h.J).comp (inclusion (h.sec8_centralizer_a_le_normalizer_J H.J_normal))

theorem ker_sigmaA (H : L83Hyp h) :
    H.sigmaA.ker = h.C0.subgroupOf (centralizer ({h.a} : Set X)) := by
  ext c
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro hc
    exact Subgroup.mem_inf.mpr ⟨c.2, Eight.mem_ker_oddBarAction.mp hc⟩
  · intro hc
    exact Eight.mem_ker_oddBarAction.mpr (Subgroup.mem_inf.mp hc).2

theorem sigmaA_eq_one (H : L83Hyp h) {c : ↥(centralizer ({h.a} : Set X))} (hc : (c : X) ∈ h.C0) :
    H.sigmaA c = 1 := by
  have : c ∈ H.sigmaA.ker := by
    rw [H.ker_sigmaA]
    exact hc
  exact this

namespace S2Data

variable (d : S2Data H)
include d

abbrev tauC : ↥(centralizer ({h.a} : Set X)) :=
  ⟨d.tau, mem_centralizer_singleton_iff.mpr d.tau_comm_a⟩

abbrev wC : ↥(centralizer ({h.a} : Set X)) := ⟨d.w, d.w_mem_centralizer_a⟩

noncomputable abbrev phi : MulAut (h.J ⧸ pPrimeCore 2 h.J) := H.sigmaA d.wC

theorem phi_eq : d.phi = H.sigmaA d.tauC := by
  have haC : h.a ∈ centralizer ({h.a} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  have hbC : d.b ∈ centralizer ({h.a} : Set X) := mem_centralizer_singleton_iff.mpr d.ba
  have hw : d.wC = ⟨h.a, haC⟩ * d.tauC * ⟨d.b, hbC⟩ := Subtype.ext d.w_eq
  have ha1 : H.sigmaA ⟨h.a, haC⟩ = 1 := H.sigmaA_eq_one (P_le_C0 h (Six.a_mem_P H.C_eq))
  have hb1 : H.sigmaA ⟨d.b, hbC⟩ = 1 := H.sigmaA_eq_one (P_le_C0 h d.b_mem_P)
  show H.sigmaA d.wC = _
  rw [hw, map_mul, map_mul, ha1, hb1, one_mul, mul_one]

theorem phi_mul_self : d.phi * d.phi = 1 := by
  show H.sigmaA d.wC * H.sigmaA d.wC = 1
  rw [← map_mul, show d.wC * d.wC = 1 from Subtype.ext d.w_mul_self, map_one]

theorem phi_ne_one (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : d.phi ≠ 1 := by
  rw [d.phi_eq]
  intro h1
  have h2 : d.tauC ∈ H.sigmaA.ker := h1
  rw [H.ker_sigmaA] at h2
  have h3 : d.tau ∈ h.C0 := h2
  apply d.tau_not_mem_P hCF1 hCF2
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp d.tau_mem).1).1,
    (Subgroup.mem_inf.mp h3).2⟩

abbrev CLa : Subgroup X := d.L ⊓ centralizer ({h.a} : Set X)

abbrev TX : Subgroup X := layerIn d.CLa

theorem TX_le_L : d.TX ≤ d.L := (map_subtype_le _).trans inf_le_left

theorem TX_le_Ca : d.TX ≤ centralizer ({h.a} : Set X) := (map_subtype_le _).trans inf_le_right

theorem TX_perfect : ⁅d.TX, d.TX⁆ = d.TX := commutator_map_pLayer_eq d.CLa

abbrev TXa : Subgroup ↥(centralizer ({h.a} : Set X)) :=
  d.TX.subgroupOf (centralizer ({h.a} : Set X))

noncomputable abbrev psiT : Subgroup (MulAut (h.J ⧸ pPrimeCore 2 h.J)) := d.TXa.map H.sigmaA

theorem psiT_perfect : ⁅d.psiT, d.psiT⁆ = d.psiT := by
  have hA : ⁅d.TXa, d.TXa⁆ = d.TXa := by
    apply map_injective (centralizer ({h.a} : Set X)).subtype_injective
    rw [map_commutator, S2Data.TXa, subgroupOf_map_subtype, inf_eq_left.mpr d.TX_le_Ca,
      d.TX_perfect]
  show ⁅d.TXa.map H.sigmaA, d.TXa.map H.sigmaA⁆ = d.TXa.map H.sigmaA
  rw [← map_commutator, hA]

theorem psiT_le_centralizer_phi :
    d.psiT ≤ centralizer ({d.phi} : Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))) := by
  rintro _ ⟨t, ht, rfl⟩
  have htT : (t : X) ∈ d.TX := ht
  rw [mem_centralizer_singleton_iff]
  show H.sigmaA t * H.sigmaA d.wC = H.sigmaA d.wC * H.sigmaA t
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (d.L_le_centralizer_w (d.TX_le_L htT)))

noncomputable abbrev piL : ↥d.L →* d.L ⧸ pPrimeCore 2 d.L := QuotientGroup.mk' (pPrimeCore 2 d.L)

theorem not_two_dvd_ker_piL : ¬ 2 ∣ Nat.card d.piL.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [QuotientGroup.ker_mk']
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card

theorem sigL_isPGroup : IsPGroup 2 (zpowers d.sigL) := isPGroup_zpowers_of_mul_self d.sigL_mul_self

theorem fix_sigL : Eight.fixSubgroup d.sigL = d.CLa.subgroupOf d.L := by
  ext l
  refine (Eight.mem_fixSubgroup_normalizerMonoidHom d.L d.a_mem_normalizer_L l).trans ?_
  rw [mem_subgroupOf]
  constructor
  · intro h1
    exact Subgroup.mem_inf.mpr ⟨l.2, mem_centralizer_singleton_iff.mpr h1.symm⟩
  · intro h1
    exact (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp h1).2).symm

theorem fix_alphaL : Eight.fixSubgroup d.alphaL = (d.CLa.subgroupOf d.L).map d.piL := by
  rw [d.alphaL_eq, Eight.fixSubgroup_oddBarAut d.sigL d.sigL_isPGroup, d.fix_sigL]

theorem layerIn_subgroupOf_L : layerIn (d.CLa.subgroupOf d.L) = d.TX.subgroupOf d.L := by
  have h1 := OddQuot.map_layerIn d.L.subtype
    (by rw [(MonoidHom.ker_eq_bot_iff _).mpr d.L.subtype_injective, card_bot]; norm_num)
    (d.CLa.subgroupOf d.L)
  rw [subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_left : d.CLa ≤ d.L)] at h1
  show layerIn (d.CLa.subgroupOf d.L) = (layerIn d.CLa).subgroupOf d.L
  rw [← h1]
  exact (comap_map_eq_self_of_injective d.L.subtype_injective _).symm

theorem E_eq : layerIn (Eight.fixSubgroup d.alphaL) = (d.TX.subgroupOf d.L).map d.piL := by
  rw [d.fix_alphaL, ← OddQuot.map_layerIn d.piL d.not_two_dvd_ker_piL, d.layerIn_subgroupOf_L]

abbrev RX : Subgroup X := d.TX ⊓ h.C0

abbrev R1X : Subgroup X := d.TX ⊓ h.C0 ⊓ h.O0

noncomputable abbrev Rb : Subgroup (d.L ⧸ pPrimeCore 2 d.L) := (d.RX.subgroupOf d.L).map d.piL

noncomputable abbrev R1b : Subgroup (d.L ⧸ pPrimeCore 2 d.L) := (d.R1X.subgroupOf d.L).map d.piL

theorem Rb_le : d.Rb ≤ layerIn (Eight.fixSubgroup d.alphaL) := by
  rw [d.E_eq]
  exact map_mono fun _ hx => mem_subgroupOf.mpr (Subgroup.mem_inf.mp (mem_subgroupOf.mp hx)).1

theorem Rb_normal : (d.Rb.subgroupOf (layerIn (Eight.fixSubgroup d.alphaL))).Normal := by
  rw [d.E_eq]
  refine Eight.normal_map_subgroupOf d.piL
    (fun _ hx => mem_subgroupOf.mpr (Subgroup.mem_inf.mp (mem_subgroupOf.mp hx)).1) ?_
  intro x hx y hy
  have hx' : (x : X) ∈ d.TX ⊓ h.C0 := hx
  have hy' : (y : X) ∈ d.TX := hy
  obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx'
  show (y : X) * x * (y : X)⁻¹ ∈ d.TX ⊓ h.C0
  exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hy' hxT) (inv_mem hy'),
    (mem_normalizer_iff.mp (H.centralizer_a_le_normalizer_C0 (d.TX_le_Ca hy')) _).mp hxC⟩

theorem R1b_le : d.R1b ≤ d.Rb :=
  map_mono fun _ hx => mem_subgroupOf.mpr (Subgroup.mem_inf.mp (mem_subgroupOf.mp hx)).1

theorem R1b_normal : (d.R1b.subgroupOf d.Rb).Normal := by
  refine Eight.normal_map_subgroupOf d.piL
    (fun _ hx => mem_subgroupOf.mpr (Subgroup.mem_inf.mp (mem_subgroupOf.mp hx)).1) ?_
  intro x hx y hy
  have hx' : (x : X) ∈ d.TX ⊓ h.C0 ⊓ h.O0 := hx
  have hy' : (y : X) ∈ d.TX ⊓ h.C0 := hy
  obtain ⟨hxTC, hxO⟩ := Subgroup.mem_inf.mp hx'
  obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hxTC
  obtain ⟨hyT, -⟩ := Subgroup.mem_inf.mp hy'
  have hya := d.TX_le_Ca hyT
  show (y : X) * x * (y : X)⁻¹ ∈ d.TX ⊓ h.C0 ⊓ h.O0
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hyT hxT) (inv_mem hyT),
    (mem_normalizer_iff.mp (H.centralizer_a_le_normalizer_C0 hya) _).mp hxC⟩,
    (mem_normalizer_iff.mp (H.centralizer_a_le_normalizer_O0 hya) _).mp hxO⟩

theorem R1b_odd : Odd (Nat.card d.R1b) := by
  have h1 : Nat.card d.R1b ∣ Nat.card (d.R1X.subgroupOf d.L) := card_map_dvd _ _
  have h2 : Nat.card (d.R1X.subgroupOf d.L) ∣ Nat.card h.O0 := by
    rw [← card_map_of_injective d.L.subtype_injective, subgroupOf_map_subtype]
    exact card_dvd_of_le (inf_le_left.trans inf_le_right)
  exact (odd_card_O0 h).of_dvd_nat (h1.trans h2)

theorem Rb_pow (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    ∀ r ∈ d.Rb, ∃ k : ℕ, r ^ 2 ^ k ∈ d.R1b := by
  intro r hr
  obtain ⟨s, hs, rfl⟩ := mem_map.mp hr
  refine ⟨1, ?_⟩
  rw [pow_one, ← map_pow]
  refine mem_map_of_mem _ ?_
  have hs' : (s : X) ∈ d.TX ⊓ h.C0 := hs
  obtain ⟨hsT, hsC⟩ := Subgroup.mem_inf.mp hs'
  have hsq : (s : X) * s ∈ h.O0 := d.sq_mem_O0 hCF1 hCF2 hsC
  show ((s ^ 2 : d.L) : X) ∈ d.TX ⊓ h.C0 ⊓ h.O0
  rw [SubgroupClass.coe_pow, pow_two]
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨mul_mem hsT hsT, mul_mem hsC hsC⟩, hsq⟩

theorem relIndex_Rb_le :
    d.Rb.relIndex (layerIn (Eight.fixSubgroup d.alphaL)) ≤ Nat.card d.psiT := by
  rw [d.E_eq]
  refine (Eight.relIndex_map_le d.piL (d.RX.subgroupOf d.L) (d.TX.subgroupOf d.L)).trans
    (le_of_eq ?_)
  rw [relIndex_subgroupOf d.TX_le_L, S2Data.RX, inf_comm, inf_relIndex_right,
    ← relIndex_subgroupOf d.TX_le_Ca, ← H.ker_sigmaA, relIndex_ker]

theorem exists_y (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (hJo : CFSec8JOrder)
    (hSp : CFSp4Layer) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hK : IsSec8Socle (h.K ⧸ pPrimeCore 2 h.K) p f)
    (hJ : IsSec8JType (h.J ⧸ pPrimeCore 2 h.J) p f)
    (hle : Nat.card d.psiT ≤ Cat8.ordL2 (p ^ f)) :
    Nat.card d.psiT = Cat8.ordL2 (p ^ f) ∧
      ∃ y ∈ Cat8.Inn (d.L ⧸ pPrimeCore 2 d.L) ⊔ zpowers d.epsL, y * d.alphaL = d.alphaL * y ∧
        (∀ t ∈ layerIn (Eight.fixSubgroup d.alphaL), y t = t) ∧
        (orderOf y = 4 ∨ (Odd (orderOf y) ∧ y ≠ 1)) := by
  obtain ⟨heq, hy⟩ := hSp _ p f hp hp2 hf h5 (d.isSec8Socle_L hK) d.epsL
    (d.epsL_admQ hCF1 hCF2 hJo hp hp2 hf hJ) d.alphaL d.alphaL_mul_self d.Rb d.R1b d.Rb_le
    d.Rb_normal d.R1b_le d.R1b_normal d.R1b_odd (d.Rb_pow hCF1 hCF2) (d.relIndex_Rb_le.trans hle)
  refine ⟨le_antisymm hle ?_, hy⟩
  rw [← heq]
  exact d.relIndex_Rb_le

end S2Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
