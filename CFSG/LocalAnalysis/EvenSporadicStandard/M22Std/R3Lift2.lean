module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutXbarLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3FusionB
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutSetupL1

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {F L1 N : Subgroup G}

@[expose] def rhoOn (L1 : Subgroup G) {P : Subgroup G} (hPX : P ≤ normalizer (L1 : Set G)) :
    ↥P →* Xbar L1 :=
  (QuotientGroup.mk' ((centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G)))).comp
    (Subgroup.inclusion hPX)

omit [Finite G] in
theorem rhoOn_apply (L1 : Subgroup G) {P : Subgroup G} (hPX : P ≤ normalizer (L1 : Set G))
    (p : P) : rhoOn L1 hPX p = QuotientGroup.mk ⟨(p : G), hPX p.2⟩ := rfl

omit [Finite G] in
theorem mem_ker_rhoOn_iff (L1 : Subgroup G) {P : Subgroup G} (hPX : P ≤ normalizer (L1 : Set G))
    (p : P) : p ∈ (rhoOn L1 hPX).ker ↔ (p : G) ∈ centralizer (L1 : Set G) := by
  rw [MonoidHom.mem_ker, rhoOn_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

namespace OutSetup

variable (S : OutSetup L z F L1 N)

include S

omit [Finite G] in
theorem ker_rhoOn {P : Subgroup G} (hP : IsPGroup 2 P) (hL1P : L1 ≤ P)
    (hPX : P ≤ normalizer (L1 : Set G)) : (rhoOn L1 hPX).ker = L1.subgroupOf P := by
  ext p
  rw [mem_ker_rhoOn_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact S.mem_L1_of_mem_centralizer hP hL1P p.2 h
  · intro h
    exact mem_centralizer_iff.2 fun x hx => S.L1_comm x hx p h

theorem card_mul_le_of_pgroup {P : Subgroup G} (hP : IsPGroup 2 P) (hL1P : L1 ≤ P)
    (hPX : P ≤ normalizer (L1 : Set G)) {y : G} (hyP : y ∈ P) (hy2 : y * y = 1) :
    256 * Nat.card ↥((rhoOn L1 hPX).range ⊓
        centralizer ({(QuotientGroup.mk ⟨y, hPX hyP⟩ : Xbar L1)} : Set (Xbar L1))) ≤
      Nat.card ↥(P ⊓ centralizer ({y} : Set G)) *
        Nat.card ↥(centralizer ({y} : Set G) ⊓ L1) := by
  have hker := S.ker_rhoOn hP hL1P hPX
  have hks : ∀ a ∈ (rhoOn L1 hPX).ker, a * a = 1 := fun a ha => by
    rw [hker, Subgroup.mem_subgroupOf] at ha
    exact Subtype.ext (S.L1_sq _ ha)
  have h := card_ker_mul_card_range_le (rhoOn L1 hPX) (y := (⟨y, hyP⟩ : ↥P))
    (show (⟨y, hyP⟩ : ↥P) * ⟨y, hyP⟩ = 1 from Subtype.ext hy2) hks
  have hk256 : Nat.card (rhoOn L1 hPX).ker = 256 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL1P).toEquiv, S.L1_card]
  have hc : Nat.card ↥(centralizer ({(⟨y, hyP⟩ : ↥P)} : Set ↥P)) =
      Nat.card ↥(P ⊓ centralizer ({y} : Set G)) := by
    have hsub : (P ⊓ centralizer ({y} : Set G)).subgroupOf P =
        centralizer ({(⟨y, hyP⟩ : ↥P)} : Set ↥P) := by
      ext w
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff,
        mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨-, h⟩
        exact Subtype.ext h
      · intro h
        exact ⟨w.2, congrArg Subtype.val h⟩
    rw [← hsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : P ⊓ centralizer ({y} : Set G) ≤ P)).toEquiv
  have hkc : Nat.card ↥(((rhoOn L1 hPX).ker ⊓ centralizer ({(⟨y, hyP⟩ : ↥P)} : Set ↥P) :
      Subgroup ↥P)) = Nat.card ↥(centralizer ({y} : Set G) ⊓ L1) := by
    have hsub : ((rhoOn L1 hPX).ker ⊓ centralizer ({(⟨y, hyP⟩ : ↥P)} : Set ↥P) : Subgroup ↥P) =
        (centralizer ({y} : Set G) ⊓ L1).subgroupOf P := by
      ext w
      rw [Subgroup.mem_inf, hker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨congrArg Subtype.val h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨h1, Subtype.ext h2⟩
    rw [hsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hL1P)).toEquiv
  rw [hk256, hc, hkc] at h
  exact h

theorem exists_pgroup_lift {y : G} (hyX : y ∈ normalizer (L1 : Set G)) (hy2 : y * y = 1)
    {Pb : Subgroup (Xbar L1)} (hPb : IsPGroup 2 Pb)
    (hyP : (QuotientGroup.mk ⟨y, hyX⟩ : Xbar L1) ∈ Pb) :
    ∃ (P : Subgroup G) (hPX : P ≤ normalizer (L1 : Set G)), IsPGroup 2 P ∧ L1 ≤ P ∧ y ∈ P ∧
      Pb ≤ (rhoOn L1 hPX).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : ↥(normalizer (L1 : Set G)) →* Xbar L1 := QuotientGroup.mk' _
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  let Pre : Subgroup ↥(normalizer (L1 : Set G)) := Pb.comap ρ
  have hy1 : y ≠ 1 ∨ y = 1 := ne_or_eq y 1
  have hz2' : IsPGroup 2 (zpowers y) := by
    rcases hy1 with hy1 | hy1
    · exact IsPGroup.of_card (n := 1) (by rw [card_zpowers_invol hy2 hy1]; norm_num)
    · exact IsPGroup.of_card (n := 0) (by simp [hy1])
  have hyN : zpowers y ≤ normalizer (L1 : Set G) := Subgroup.zpowers_le.2 hyX
  have hK1 : IsPGroup 2 (L1 ⊔ zpowers y : Subgroup G) := by
    rw [sup_comm]
    exact hz2'.to_sup_of_normal_right' S.isPGroup_L1 hyN
  have hK1X : IsPGroup 2 ((L1 ⊔ zpowers y).subgroupOf (normalizer (L1 : Set G))) :=
    hK1.comap_subtype
  have hL1pre : ∀ (l : G) (hl : l ∈ L1),
      (⟨l, Subgroup.le_normalizer hl⟩ : ↥(normalizer (L1 : Set G))) ∈ Pre := by
    intro l hl
    show ρ ⟨l, Subgroup.le_normalizer hl⟩ ∈ Pb
    have : ρ ⟨l, Subgroup.le_normalizer hl⟩ = 1 := by
      show (QuotientGroup.mk _ : Xbar L1) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact mem_centralizer_iff.2 fun x hx => S.L1_comm x hx l hl
    rw [this]
    exact Pb.one_mem
  have hypre : (⟨y, hyX⟩ : ↥(normalizer (L1 : Set G))) ∈ Pre := hyP
  have hK1Pre : (L1 ⊔ zpowers y).subgroupOf (normalizer (L1 : Set G)) ≤ Pre := by
    intro k hk
    have hk' : (k : G) ∈ L1 ⊔ zpowers y := hk
    have hle : (L1 ⊔ zpowers y : Subgroup G) ≤ Pre.map (normalizer (L1 : Set G)).subtype :=
      sup_le (fun l hl => ⟨_, hL1pre l hl, rfl⟩)
        (Subgroup.zpowers_le.2 ⟨_, hypre, rfl⟩)
    obtain ⟨p, hp, hpk⟩ := hle hk'
    have : p = k := Subtype.ext hpk
    rwa [← this]
  have hK1' : IsPGroup 2
      (((L1 ⊔ zpowers y).subgroupOf (normalizer (L1 : Set G))).subgroupOf Pre) :=
    hK1X.comap_subtype
  obtain ⟨Sy, hSy⟩ := hK1'.exists_le_sylow
  let φ : ↥Pre →* G := (normalizer (L1 : Set G)).subtype.comp Pre.subtype
  have hφinj : Function.Injective φ :=
    Subtype.val_injective.comp Subtype.val_injective
  let P : Subgroup G := (Sy : Subgroup ↥Pre).map φ
  have hPX : P ≤ normalizer (L1 : Set G) := by
    rintro _ ⟨s, -, rfl⟩
    exact s.1.2
  have hSyin : ∀ g : G, g ∈ L1 ⊔ zpowers y → (hgX : g ∈ normalizer (L1 : Set G)) →
      g ∈ P := by
    intro g hg hgX
    have hk : (⟨g, hgX⟩ : ↥(normalizer (L1 : Set G))) ∈
        (L1 ⊔ zpowers y).subgroupOf (normalizer (L1 : Set G)) := hg
    have hkPre : (⟨g, hgX⟩ : ↥(normalizer (L1 : Set G))) ∈ Pre := hK1Pre hk
    have : (⟨⟨g, hgX⟩, hkPre⟩ : ↥Pre) ∈ (Sy : Subgroup ↥Pre) :=
      hSy (Subgroup.mem_subgroupOf.2 hk)
    exact ⟨_, this, rfl⟩
  refine ⟨P, hPX, ?_, fun l hl => hSyin l (Subgroup.mem_sup_left hl) (Subgroup.le_normalizer hl),
    hSyin y (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)) hyX, ?_⟩
  · obtain ⟨k, hk⟩ := Sy.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := k) (by
      rw [Subgroup.card_map_of_injective hφinj]
      exact hk)
  ·
    let g0 : ↥Pre →* ↥Pb := (ρ.comp Pre.subtype).codRestrict Pb (fun w => w.2)
    have hg0 : Function.Surjective g0 := by
      intro q
      obtain ⟨w, hw⟩ := hρ q
      refine ⟨⟨w, ?_⟩, Subtype.ext hw⟩
      show ρ w ∈ Pb
      rw [hw]
      exact q.2
    have hpb : IsPGroup 2 ↥Pb := hPb
    have hIdx := (Sylow.mapSurjective hg0 Sy).not_dvd_index
    obtain ⟨n, hn⟩ := hpb.index ((Sylow.mapSurjective hg0 Sy : Subgroup ↥Pb))
    have hn0 : n = 0 := by
      by_contra hne
      exact hIdx (by rw [hn]; exact dvd_pow_self 2 hne)
    have htop : ((Sylow.mapSurjective hg0 Sy : Subgroup ↥Pb)) = ⊤ := by
      rw [← Subgroup.index_eq_one, hn, hn0, pow_zero]
    intro q hq
    have hmem : (⟨q, hq⟩ : ↥Pb) ∈ (Sylow.mapSurjective hg0 Sy : Subgroup ↥Pb) := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨s, hsSy, hsq⟩ := hmem
    refine ⟨⟨(s : ↥(normalizer (L1 : Set G))), ⟨s, hsSy, rfl⟩⟩, ?_⟩
    have := congrArg Subtype.val hsq
    exact this

theorem card_le_sixtyfour (hcr : CentRank z)
    (hCG : Nat.card (centralizer ({z} : Set G)) = 1774080) {y : G}
    (hyX : y ∈ normalizer (L1 : Set G)) (hy2 : y * y = 1) (hconj : IsConj z y)
    {Pb : Subgroup (Xbar L1)} (hPb : IsPGroup 2 Pb)
    (hyP : (QuotientGroup.mk ⟨y, hyX⟩ : Xbar L1) ∈ Pb) :
    Nat.card ↥(Pb ⊓ centralizer ({(QuotientGroup.mk ⟨y, hyX⟩ : Xbar L1)} : Set (Xbar L1))) ≤ 64 :=
  by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPX, hP, hL1P, hyPG, hPb_le⟩ := S.exists_pgroup_lift hyX hy2 hPb hyP
  have h := S.card_mul_le_of_pgroup hP hL1P hPX hyPG hy2
  have hCy : Nat.card (centralizer ({y} : Set G)) = 1774080 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    rw [card_centralizer_eq_of_conj hc, hCG]
  have h512 : Nat.card ↥(P ⊓ centralizer ({y} : Set G)) ≤ 512 := by
    have hp : IsPGroup 2 ↥(P ⊓ centralizer ({y} : Set G)) := hP.to_inf_left
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hdvd : Nat.card ↥(P ⊓ centralizer ({y} : Set G)) ∣ 1774080 := by
      rw [← hCy]
      exact Subgroup.card_dvd_of_le inf_le_right
    by_contra hlt
    push Not at hlt
    have h10 : 10 ≤ n := by
      by_contra hn10
      push Not at hn10
      have : 2 ^ n ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h3 : 2 ^ 10 ∣ 2 ^ n := pow_dvd_pow 2 h10
    rw [hn] at hdvd
    have := dvd_trans h3 hdvd
    norm_num at this
  have h32 := S.card_centralizer_L1_le hcr hy2 hconj
  have hmono : Nat.card ↥(Pb ⊓ centralizer ({(QuotientGroup.mk ⟨y, hyX⟩ : Xbar L1)} :
      Set (Xbar L1))) ≤ Nat.card ↥((rhoOn L1 hPX).range ⊓
        centralizer ({(QuotientGroup.mk ⟨y, hPX hyPG⟩ : Xbar L1)} : Set (Xbar L1))) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ hPb_le)
  have hmul := Nat.mul_le_mul h512 h32
  omega

end OutSetup

end CFSG.EvenSporadicStandard.M22Std
