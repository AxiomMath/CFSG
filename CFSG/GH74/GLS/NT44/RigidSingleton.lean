module

public import CFSG.GH74.GLS.NT44.RigidInnerActor
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.NT44.RigidQuotientAut
import CFSG.GH74.GLS.NT44.RootPreimageLift
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Model2

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4 CFSG.GH74.GLS.Stage1.Thm3.Sec4

theorem exists_isSylowOf_inf_centralizer {G : Type} [Group G] [Finite G] {x v : G}
    (hv2 : orderOf v = 2) (hvx : v * x = x * v) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({x} : Set G)) ∧ v ∈ S ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ centralizer ({v} : Set G))
        (centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let H : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G)
  have hvH : v ∈ H :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hvx,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨T₀, hT₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 H
  have hvT₀ : v ∈ T₀ :=
    CFSG.GH74.GLS.C3.Layer1.Back.mem_of_isSylowOf_of_central hT₀ hvH
      (fun s hs => Subgroup.mem_centralizer_singleton_iff.mp hs.2) hv2
  obtain ⟨S, hS, hT₀S⟩ :=
    exists_isSylowOf_centralizer_le_of_isPGroup hT₀.isPGroup (hT₀.le.trans inf_le_left)
  have hT₀le : T₀ ≤ S ⊓ centralizer ({v} : Set G) :=
    le_inf hT₀S (hT₀.le.trans inf_le_right)
  have hleH : S ⊓ centralizer ({v} : Set G) ≤ H :=
    inf_le_inf hS.le le_rfl
  have hP : IsPGroup 2 ↥(S ⊓ centralizer ({v} : Set G)) := hS.isPGroup.to_inf_left
  have heq : S ⊓ centralizer ({v} : Set G) = T₀ :=
    CFSG.ABGLocalTools.IsSylowOf.eq_of_le hT₀ hT₀le hleH hP
  exact ⟨S, hS, hT₀S hvT₀, heq ▸ hT₀⟩

theorem eq_one_of_mem_cxK_of_rigid_actor
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 → Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    {I L : Subgroup G} (hI : I ∈ RigidSet fullQ x) (hL : L ∈ RigidSet fullQ v)
    {b : G} (hbI : b ∈ CxK x I) (hbL : b ∈ CxK v L) (hb2 : ∃ n : ℕ, b ^ 2 ^ n = 1) :
    b = 1 := by
  have hodd :=
    odd_card_cxK_inf_cxK_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN
      hvact hxP hmax I hI L hL
  have hmem : b ∈ CxK x I ⊓ CxK v L := ⟨hbI, hbL⟩
  have hdvd : orderOf b ∣ Nat.card ↥(CxK x I ⊓ CxK v L) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  obtain ⟨n, hn⟩ := hb2
  have hdvd2 : orderOf b ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hodd' : Odd (orderOf b) := hodd.of_dvd_nat hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hk0 : k = 0 := by
    have h2 : (2 : ℕ) ^ k % 2 = 1 := Nat.odd_iff.mp (hk ▸ hodd')
    exact Nat.two_pow_mod_two_eq_one.mp h2
  have h1 : orderOf b = 1 := by rw [hk, hk0, pow_zero]
  exact orderOf_eq_one_iff.mp h1

theorem false_of_z4E4_mem_normalizer
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 → Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    {I L : Subgroup G} (hI : I ∈ RigidSet fullQ x) (hL : L ∈ RigidSet fullQ v) {a b c : G}
    (ha : a ∈ CxK x I ⊓ centralizer ({v} : Set G) ⊓ normalizer (L : Set G))
    (hb : b ∈ CxK x I ⊓ centralizer ({v} : Set G) ⊓ normalizer (L : Set G))
    (hc : c ∈ CxK x I ⊓ centralizer ({v} : Set G) ⊓ normalizer (L : Set G))
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha4 : a ^ 4 = 1) (hb2 : b ^ 2 = 1) (hc2 : c ^ 2 = 1)
    (ha2 : a ^ 2 ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a ^ 2) (hc1 : c ≠ 1) (hca : c ≠ a ^ 2)
    (hcb : c ≠ b) (hcab : c ≠ a ^ 2 * b) : False := by
  classical
  let φ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (kBar L) :=
    (MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥L)).comp L.normalizerMonoidHom
  have haI : a ∈ CxK x I := ha.1.1
  have hav : a ∈ centralizer ({v} : Set G) := ha.1.2
  have haN : a ∈ Subgroup.normalizer (L : Set G) := ha.2
  have hbI : b ∈ CxK x I := hb.1.1
  have hbv : b ∈ centralizer ({v} : Set G) := hb.1.2
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hb.2
  have hcI : c ∈ CxK x I := hc.1.1
  have hcv : c ∈ centralizer ({v} : Set G) := hc.1.2
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hc.2
  have haa2 : a ^ 2 * a ^ 2 = 1 := by
    rw [← pow_two (a ^ 2), ← pow_mul]
    rw [show (2 : ℕ) * 2 = 4 by norm_num]
    exact ha4
  have habc : Commute a b := (commute_iff_eq a b).mpr hab
  have hacc : Commute a c := (commute_iff_eq a c).mpr hac
  have ha2b : a ^ 2 * b = b * a ^ 2 := (habc.pow_left 2).eq
  have ha2c : a ^ 2 * c = c * a ^ 2 := (hacc.pow_left 2).eq
  have hpair : ({a ^ 2, b, c} : Set G).Pairwise Commute := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact (commute_iff_eq _ _).mpr ha2b
    · exact (commute_iff_eq _ _).mpr ha2c
    · exact (commute_iff_eq _ _).mpr ha2b.symm
    · exact absurd rfl hxy
    · exact (commute_iff_eq _ _).mpr hbc
    · exact (commute_iff_eq _ _).mpr ha2c.symm
    · exact (commute_iff_eq _ _).mpr hbc.symm
    · exact absurd rfl hxy
  let K : Subgroup G := Subgroup.closure ({a ^ 2, b, c} : Set G)
  have haK : a ^ 2 ∈ K := Subgroup.subset_closure (by simp)
  have hbK : b ∈ K := Subgroup.subset_closure (by simp)
  have hcK : c ∈ K := Subgroup.subset_closure (by simp)
  have hKI : K ≤ CxK x I := by
    change Subgroup.closure ({a ^ 2, b, c} : Set G) ≤ CxK x I
    rw [Subgroup.closure_le]
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact pow_mem haI 2
    · exact hbI
    · exact hcI
  have hKv : K ≤ centralizer ({v} : Set G) := by
    change Subgroup.closure ({a ^ 2, b, c} : Set G) ≤ centralizer ({v} : Set G)
    rw [Subgroup.closure_le]
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact pow_mem hav 2
    · exact hbv
    · exact hcv
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := by
    change Subgroup.closure ({a ^ 2, b, c} : Set G) ≤ Subgroup.normalizer (L : Set G)
    rw [Subgroup.closure_le]
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact pow_mem haN 2
    · exact hbN
    · exact hcN
  have hKcomm : ∀ u ∈ K, ∀ w ∈ K, u * w = w * u := by
    let : CommGroup K :=
      Subgroup.closureCommGroupOfComm (k := ({a ^ 2, b, c} : Set G)) hpair
    intro u hu w hw
    exact congrArg Subtype.val (mul_comm (⟨u, hu⟩ : K) ⟨w, hw⟩)
  have hsq : ∀ u ∈ K, u * u = 1 := by
    intro u hu
    have hu' : u ∈ Subgroup.closure ({a ^ 2, b, c} : Set G) := hu
    exact Subgroup.closure_induction (k := ({a ^ 2, b, c} : Set G))
      (p := fun x _ => x * x = 1)
      (fun x hx => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact haa2
        · simpa [pow_two] using hb2
        · simpa [pow_two] using hc2)
      (by simp)
      (fun x y hx hy hpx hpy => by
        have hxK : x ∈ K := hx
        have hyK : y ∈ K := hy
        have hxy : x * y = y * x := hKcomm x hxK y hyK
        calc (x * y) * (x * y) = (x * y) ^ 2 := by rw [pow_two]
          _ = x ^ 2 * y ^ 2 := ((commute_iff_eq x y).mpr hxy).mul_pow 2
          _ = 1 := by rw [pow_two x, pow_two y, hpx, hpy, mul_one])
      (fun x hx hpx => by
        have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hpx
        rw [hxinv, hpx]) hu'
  have hKtriv : ∀ (e : G) (he : e ∈ K), φ ⟨e, hKN he⟩ = 1 → e = 1 := by
    intro e he hker
    have hker' : MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥L)
        (L.normalizerMonoidHom ⟨e, hKN he⟩) = 1 := by
      simpa only [φ, MonoidHom.comp_apply] using hker
    have hsec : e ∈ centralizerSection L (pPrimeCoreOf 2 L) :=
      (mapQuotient_normalizerMonoidHom_eq_one_iff (hKN he)).mp hker'
    refine eq_one_of_mem_cxK_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN
      hvact hxP hmax hI hL (hKI he) ⟨hKv he, hsec⟩ ⟨1, ?_⟩
    simpa [pow_two] using hsq e he
  have hab' : φ ⟨a, haN⟩ * φ ⟨b, hbN⟩ = φ ⟨b, hbN⟩ * φ ⟨a, haN⟩ := by
    have h := congrArg φ (Subtype.ext hab :
      (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨b, hbN⟩ =
        ⟨b, hbN⟩ * ⟨a, haN⟩)
    simpa only [map_mul] using h
  have hac' : φ ⟨a, haN⟩ * φ ⟨c, hcN⟩ = φ ⟨c, hcN⟩ * φ ⟨a, haN⟩ := by
    have h := congrArg φ (Subtype.ext hac :
      (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨c, hcN⟩ =
        ⟨c, hcN⟩ * ⟨a, haN⟩)
    simpa only [map_mul] using h
  have hbc' : φ ⟨b, hbN⟩ * φ ⟨c, hcN⟩ = φ ⟨c, hcN⟩ * φ ⟨b, hbN⟩ := by
    have h := congrArg φ (Subtype.ext hbc :
      (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨c, hcN⟩ =
        ⟨c, hcN⟩ * ⟨b, hbN⟩)
    simpa only [map_mul] using h
  have ha4' : φ ⟨a, haN⟩ ^ 4 = 1 := by
    have hp : (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 4 = 1 := by
      apply Subtype.ext
      simpa using ha4
    calc φ ⟨a, haN⟩ ^ 4 = φ ((⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 4) :=
          (map_pow φ _ 4).symm
      _ = 1 := by rw [hp, map_one]
  have hb2' : φ ⟨b, hbN⟩ ^ 2 = 1 := by
    have hp : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hb2
    calc φ ⟨b, hbN⟩ ^ 2 = φ ((⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2) :=
          (map_pow φ _ 2).symm
      _ = 1 := by rw [hp, map_one]
  have hc2' : φ ⟨c, hcN⟩ ^ 2 = 1 := by
    have hp : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hc2
    calc φ ⟨c, hcN⟩ ^ 2 = φ ((⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2) :=
          (map_pow φ _ 2).symm
      _ = 1 := by rw [hp, map_one]
  have hmul := mulAut_noZ4E4_of_mem_rigidSet hL34 h16 hL hab' hac' hbc' ha4' hb2' hc2'
  rcases hmul with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hker : φ ⟨a ^ 2, hKN haK⟩ = 1 := by
      have hx : (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 =
          ⟨a ^ 2, hKN haK⟩ := Subtype.ext rfl
      calc φ ⟨a ^ 2, hKN haK⟩
          = φ ((⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2) := by rw [hx]
        _ = φ ⟨a, haN⟩ ^ 2 := map_pow φ _ 2
        _ = 1 := h1
    exact ha2 (hKtriv (a ^ 2) haK hker)
  · have hker : φ ⟨b, hKN hbK⟩ = 1 := by
      change φ ⟨b, hbN⟩ = 1
      exact h2
    exact hb1 (hKtriv b hbK hker)
  · have heK : b⁻¹ * a ^ 2 ∈ K := K.mul_mem (K.inv_mem hbK) haK
    have hker : φ ⟨b⁻¹ * a ^ 2, hKN heK⟩ = 1 := by
      have hsub : (⟨b⁻¹ * a ^ 2, hKN heK⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ *
            (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 := by
        apply Subtype.ext
        simp
      calc φ ⟨b⁻¹ * a ^ 2, hKN heK⟩
          = φ ((⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ *
              (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2) := by rw [hsub]
        _ = (φ ⟨b, hbN⟩)⁻¹ * (φ ⟨a, haN⟩) ^ 2 := by
            simp only [map_mul, map_inv, map_pow]
        _ = 1 := by rw [h3]; exact inv_mul_cancel _
    exact hba (inv_mul_eq_one.mp (hKtriv (b⁻¹ * a ^ 2) heK hker))
  · have hker : φ ⟨c, hKN hcK⟩ = 1 := by
      change φ ⟨c, hcN⟩ = 1
      exact h4
    exact hc1 (hKtriv c hcK hker)
  · have heK : c⁻¹ * a ^ 2 ∈ K := K.mul_mem (K.inv_mem hcK) haK
    have hker : φ ⟨c⁻¹ * a ^ 2, hKN heK⟩ = 1 := by
      have hsub : (⟨c⁻¹ * a ^ 2, hKN heK⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          (⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ *
            (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 := by
        apply Subtype.ext
        simp
      calc φ ⟨c⁻¹ * a ^ 2, hKN heK⟩
          = φ ((⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ *
              (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2) := by rw [hsub]
        _ = (φ ⟨c, hcN⟩)⁻¹ * (φ ⟨a, haN⟩) ^ 2 := by
            simp only [map_mul, map_inv, map_pow]
        _ = 1 := by rw [h5]; exact inv_mul_cancel _
    exact hca (inv_mul_eq_one.mp (hKtriv (c⁻¹ * a ^ 2) heK hker))
  · have heK : c⁻¹ * b ∈ K := K.mul_mem (K.inv_mem hcK) hbK
    have hker : φ ⟨c⁻¹ * b, hKN heK⟩ = 1 := by
      have hsub : (⟨c⁻¹ * b, hKN heK⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          (⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ *
            (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) := by
        apply Subtype.ext
        simp
      calc φ ⟨c⁻¹ * b, hKN heK⟩
          = φ ((⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ *
              (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G)))) := by rw [hsub]
        _ = (φ ⟨c, hcN⟩)⁻¹ * φ ⟨b, hbN⟩ := by
            simp only [map_mul, map_inv]
        _ = 1 := by rw [h6]; exact inv_mul_cancel _
    exact hcb (inv_mul_eq_one.mp (hKtriv (c⁻¹ * b) heK hker))
  · have heK : c⁻¹ * a ^ 2 * b ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hcK) haK) hbK
    have hker : φ ⟨c⁻¹ * a ^ 2 * b, hKN heK⟩ = 1 := by
      have hsub : (⟨c⁻¹ * a ^ 2 * b, hKN heK⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          (⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ *
            (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 *
              (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) := by
        apply Subtype.ext
        simp
      calc φ ⟨c⁻¹ * a ^ 2 * b, hKN heK⟩
          = φ ((⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ *
              (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 *
                (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G)))) := by rw [hsub]
        _ = (φ ⟨c, hcN⟩)⁻¹ * (φ ⟨a, haN⟩) ^ 2 * φ ⟨b, hbN⟩ := by
            simp only [map_mul, map_inv, map_pow]
        _ = 1 := by
            rw [h7, mul_assoc]
            exact inv_mul_cancel _
    have h1 := hKtriv (c⁻¹ * a ^ 2 * b) heK hker
    have h2 : c⁻¹ * (a ^ 2 * b) = 1 := by
      rwa [mul_assoc] at h1
    exact hcab (inv_mul_eq_one.mp h2)

theorem card_le_sixteen_of_le_normalizer
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 → Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    {I L : Subgroup G} (hI : I ∈ RigidSet fullQ x) (hL : L ∈ RigidSet fullQ v)
    {E : Subgroup G} (hE : E ≤ CxK x I ⊓ centralizer ({v} : Set G) ⊓ normalizer (L : Set G))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a * a = 1) :
    Nat.card E ≤ 16 := by
  classical
  let φ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (kBar L) :=
    (MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥L)).comp L.normalizerMonoidHom
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := fun e he => (hE he).2
  let f : ↥E →* MulAut (kBar L) := φ.comp (Subgroup.inclusion hEN)
  have hf : Function.Injective f := by
    intro p q hpq
    have hf1 : f (p⁻¹ * q) = 1 := by
      rw [map_mul, map_inv, hpq]
      exact inv_mul_cancel _
    have he1 : ((p⁻¹ * q : ↥E) : G) = 1 := by
      have hmemE : ((p⁻¹ * q : ↥E) : G) ∈ E := (p⁻¹ * q).2
      have heI : ((p⁻¹ * q : ↥E) : G) ∈ CxK x I := (hE hmemE).1.1
      have hev : ((p⁻¹ * q : ↥E) : G) ∈ centralizer ({v} : Set G) := (hE hmemE).1.2
      have heN : ((p⁻¹ * q : ↥E) : G) ∈ Subgroup.normalizer (L : Set G) :=
        hEN (p⁻¹ * q).2
      have hincl : Subgroup.inclusion hEN (p⁻¹ * q) =
          (⟨((p⁻¹ * q : ↥E) : G), heN⟩ : ↥(Subgroup.normalizer (L : Set G))) := by
        apply Subtype.ext
        exact Subgroup.coe_inclusion hEN (p⁻¹ * q)
      have hker : φ ⟨((p⁻¹ * q : ↥E) : G), heN⟩ = 1 := by
        have h : φ (Subgroup.inclusion hEN (p⁻¹ * q)) = 1 := by
          simpa only [f, MonoidHom.comp_apply] using hf1
        rwa [hincl] at h
      have hsec : ((p⁻¹ * q : ↥E) : G) ∈ centralizerSection L (pPrimeCoreOf 2 L) :=
        (mapQuotient_normalizerMonoidHom_eq_one_iff heN).mp (by
          simpa only [φ, MonoidHom.comp_apply] using hker)
      refine eq_one_of_mem_cxK_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN
        hvact hxP hmax hI hL heI ⟨hev, hsec⟩ ⟨1, ?_⟩
      simpa [pow_two] using hE2 ((p⁻¹ * q : ↥E) : G) (p⁻¹ * q).2
    exact inv_mul_eq_one.mp (Subtype.ext he1)
  let A : Subgroup (MulAut (kBar L)) := f.range
  have hAcard : Nat.card ↥E ≤ Nat.card A := by
    let g : ↥E → A := fun p => ⟨f p, MonoidHom.mem_range.mpr ⟨p, rfl⟩⟩
    have hg : Function.Injective g := by
      intro p q hpq
      exact hf (Subtype.ext_iff.mp hpq)
    simpa using Nat.card_le_card_of_injective g hg
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hb
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (hEc (p : G) p.2 (q : G) q.2))
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp ha
    rw [← map_mul, show p * p = 1 from Subtype.ext (hE2 (p : G) p.2), map_one]
  calc Nat.card ↥E ≤ Nat.card A := hAcard
    _ ≤ 16 := card_le_sixteen_of_mem_rigidSet hL34 h16 hL hAc hA2

theorem exists_swap_of_inner_rigid_actor
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 → Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    (hr : 1 < Nat.card ↥(RigidSet fullQ x))
    (hvin : MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨v, hvN⟩) ∈
      (MulAut.conj : kBar J →* MulAut (kBar J)).range)
    {g : G} (hg : g * x * g⁻¹ = v) :
    ∃ K ∈ RigidSet fullQ x, K ≠ J ∧ ∃ y ∈ zStar J, y ^ 4 = 1 ∧ y * v = v * y ∧
      cmap y (cmap g J) = cmap g K := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨S, hS, hvS, hT⟩ := exists_isSylowOf_inf_centralizer hv2 hvx
  have hv2' : v ^ 2 = 1 := by rw [← hv2]; exact pow_orderOf_eq_one v
  obtain ⟨V, X, hVJ, hVcomm, hWV, hXV, hXWbot, hX4, hX2, hVeq⟩ :=
    exists_root_preimage_lift_of_inner_actor hL34 h16 hJ hv2' hvN hvin hS hT
  let W : Subgroup G := S ⊓ zStar J
  let L₁ : Subgroup G := cmap g J
  obtain ⟨eZ, e4, -⟩ :=
    exists_rigid_center_sylow_equiv_of_center_card_sixteen hJ hS hL34 h16
  let eW : ↥W ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := eZ.trans e4
  have hL₁ : L₁ ∈ RigidSet fullQ v := by
    have h := isRigidOfType_conj (Q := fullQ) hJ g
    rw [show g * x * g⁻¹ = v from hg] at h
    exact h
  have hVJ' : V ≤ J := fun a ha => (hVJ ha).1.1
  have hVS : V ≤ S := fun a ha => (hVJ ha).1.2
  have hVcv : V ≤ centralizer ({v} : Set G) := fun a ha => (hVJ ha).2
  have hXS : X ≤ S := hXV.trans hVS
  have hXW : X ⊓ W = ⊥ := by
    have h : X ⊓ W = X ⊓ zStar J := by
      dsimp [W]
      rw [← inf_assoc, inf_eq_left.mpr hXS]
    rw [h, hXWbot]
  have hVsup : X ⊔ W ≤ V := le_of_eq hVeq
  have hcomm : ∀ a ∈ X ⊔ W, ∀ b ∈ X ⊔ W, a * b = b * a :=
    fun a ha b hb => hVcomm a (hVsup ha) b (hVsup hb)
  have hr2 : 2 ≤ (RigidSet fullQ x).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact hr
  obtain ⟨K₂, hK₂, hK₂J⟩ : ∃ K₂ ∈ RigidSet fullQ x, K₂ ≠ J := by
    by_contra h
    push Not at h
    have hsub : RigidSet fullQ x ⊆ ({J} : Set (Subgroup G)) := fun K hK => by
      simp [h K hK]
    have hle : (RigidSet fullQ x).ncard ≤ 1 := by
      calc (RigidSet fullQ x).ncard ≤ ({J} : Set (Subgroup G)).ncard := Set.ncard_mono hsub
        _ = 1 := by simp
    omega
  have hJK₂ : J ≤ CFSG.GH74.GLS.Stage1.Thm2.Recip.cSec K₂ :=
    CFSG.GH74.GLS.Stage1.Thm2.Recip.le_cSec_of_ne hJ.1.1.2.2 hK₂.1.1.2.2
      (Ne.symm hK₂J)
  have hVK₂ : V ≤ CxK x K₂ := fun a ha =>
    ⟨(hJ.1.1.2.2.1) (hVJ' ha), hJK₂ (hVJ' ha)⟩
  by_cases hVN : ∀ a ∈ V, a ∈ normalizer (L₁ : Set G)
  ·
    obtain ⟨a, haV, b, hbV, c, hcV, ha4, hb2, hc2, ha2, hb1, hba, hc1, hca, hcb, hcab⟩ :=
      exists_z4E4_of_two_mul_card_le (X := X) (W := W) (B := V) hXW hcomm hX4 hX2 eW
        (le_of_eq hVeq.symm) (by rw [hVeq]; omega)
    exact (false_of_z4E4_mem_normalizer hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact
      hxP hmax hK₂ hL₁
      ⟨⟨hVK₂ haV, hVcv haV⟩, hVN a haV⟩
      ⟨⟨hVK₂ hbV, hVcv hbV⟩, hVN b hbV⟩
      ⟨⟨hVK₂ hcV, hVcv hcV⟩, hVN c hcV⟩
      (hVcomm a haV b hbV) (hVcomm a haV c hcV) (hVcomm b hbV c hcV)
      ha4 hb2 hc2 ha2 hb1 hba hc1 hca hcb hcab).elim
  ·
    push Not at hVN
    obtain ⟨a, haV, haN⟩ := hVN
    have hcommXW : ∀ p ∈ X, ∀ q ∈ W, p * q = q * p :=
      fun p hp q hq => hVcomm p (hXV hp) q (hWV hq)
    let T : Subgroup G :=
      { carrier := {p | ∃ x' ∈ X, ∃ w ∈ W, x' * w = p}
        one_mem' := ⟨1, X.one_mem, 1, W.one_mem, by simp⟩
        mul_mem' := by
          intro a b ha hb
          obtain ⟨x₁, hx₁, w₁, hw₁, rfl⟩ := ha
          obtain ⟨x₂, hx₂, w₂, hw₂, rfl⟩ := hb
          refine ⟨x₁ * x₂, X.mul_mem hx₁ hx₂, w₁ * w₂, W.mul_mem hw₁ hw₂, ?_⟩
          calc (x₁ * x₂) * (w₁ * w₂) = x₁ * (x₂ * w₁) * w₂ := by group
            _ = x₁ * (w₁ * x₂) * w₂ := by rw [hcommXW x₂ hx₂ w₁ hw₁]
            _ = (x₁ * w₁) * (x₂ * w₂) := by group
        inv_mem' := by
          intro a ha
          obtain ⟨x₁, hx₁, w₁, hw₁, rfl⟩ := ha
          refine ⟨x₁⁻¹, X.inv_mem hx₁, w₁⁻¹, W.inv_mem hw₁, ?_⟩
          have h1 : w₁⁻¹ * x₁⁻¹ = x₁⁻¹ * w₁⁻¹ := by
            simpa only [mul_inv_rev] using congrArg Inv.inv (hcommXW x₁ hx₁ w₁ hw₁)
          rw [mul_inv_rev, h1] }
    have hXT : X ≤ T := fun p hp => ⟨p, hp, 1, W.one_mem, by simp⟩
    have hWT : W ≤ T := fun q hq => ⟨1, X.one_mem, q, hq, by simp⟩
    have hsupT : X ⊔ W ≤ T := sup_le hXT hWT
    have hVle : V ≤ X ⊔ W := le_of_eq hVeq.symm
    obtain ⟨x', hx'X, w, hwW, hx'w⟩ := hsupT (hVle haV)
    have hx'N : x' ∈ normalizer (L₁ : Set G) := by
      by_cases hx'1 : x' = 1
      · rw [hx'1]; exact one_mem _
      · have hx'2 : orderOf x' = 2 := by
          have hpow : x' ^ 2 = 1 := by simpa [pow_two] using hX2 x' hx'X
          have hdvd : orderOf x' ∣ 2 := by simpa using orderOf_dvd_of_pow_eq_one hpow
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hx'1
          · exact h
        exact normalizes_rigid_family_of_centralizing_involution hnonab hKproper hL34 h16 hx2
          hv2 hxv hvx hJ hvN hvact hxP hmax S hS hvS K₂ hK₂ x' hx'2 (hXS hx'X)
          ((hVJ (hXV hx'X)).2) ((hVK₂ (hXV hx'X)).2) L₁ hL₁
    have hwN : w ∉ normalizer (L₁ : Set G) := by
      intro hwNL
      refine haN ?_
      rw [← hx'w]
      exact mul_mem hx'N hwNL
    have hwZ : w ∈ zStar J := hwW.2
    have hwv : w * v = v * w :=
      Subgroup.mem_centralizer_singleton_iff.mp (hVcv (hWV hwW))
    have hw4 : w ^ 4 = 1 := by
      have h4all : ∀ u : Multiplicative (ZMod 4) × Multiplicative (ZMod 4), u ^ 4 = 1 := by
        decide
      have h := h4all (eW ⟨w, hwW⟩)
      rw [← map_pow] at h
      have h4 : (⟨w, hwW⟩ : ↥W) ^ 4 = 1 := eW.injective (h.trans (map_one eW).symm)
      simpa using congrArg (fun z : ↥W => (z : G)) h4
    refine ⟨cmap g⁻¹ (cmap w L₁), ?_, ?_, w, hwZ, hw4, hwv, ?_⟩
    · have hwL₁ : cmap w L₁ ∈ RigidSet fullQ v := by
        have h := isRigidOfType_conj (Q := fullQ) hL₁ w
        rw [show w * v * w⁻¹ = v from by rw [hwv]; group] at h
        exact h
      have h := isRigidOfType_conj (Q := fullQ) hwL₁ g⁻¹
      rw [show g⁻¹ * v * g⁻¹⁻¹ = x from by rw [← hg]; group] at h
      exact h
    · intro hEq
      have h1 : cmap w L₁ = L₁ := by
        have h := congrArg (cmap g) hEq
        rw [cmap_cancel] at h
        exact h
      exact hwN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1)
    · rw [cmap_cancel]

theorem false_of_inner_rigid_actor_pair_of_two_lt_card
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 → Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    (hr : 2 < Nat.card ↥(RigidSet fullQ x))
    (hvin : MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨v, hvN⟩) ∈
      (MulAut.conj : kBar J →* MulAut (kBar J)).range)
    {K : Subgroup G} (hK : K ∈ RigidSet fullQ x) (hKJ : K ≠ J)
    (hvK : v ∈ normalizer (K : Set G))
    (hvinK : MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥K) (K.normalizerMonoidHom ⟨v, hvK⟩) ∈
      (MulAut.conj : kBar K →* MulAut (kBar K)).range) : False := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hvS, hT⟩ := exists_isSylowOf_inf_centralizer hv2 hvx
  have hv2' : v ^ 2 = 1 := by
    simpa [hv2] using pow_orderOf_eq_one v
  obtain ⟨V_J, X_J, hVJ_le, hVJ_comm, hWJ_le, hXJ_le, hXJ_bot, hXJ_card, hXJ_sq, -⟩ :=
    exists_root_preimage_lift_of_inner_actor hL34 h16 hJ hv2' hvN hvin hS hT
  obtain ⟨V_K, X_K, hVK_le, hVK_comm, hWK_le, hXK_le, hXK_bot, hXK_card, hXK_sq, -⟩ :=
    exists_root_preimage_lift_of_inner_actor hL34 h16 hK hv2' hvK hvinK hS hT
  have hXJ_J : X_J ≤ J := fun a ha => (hVJ_le (hXJ_le ha)).1.1
  have hXJ_S : X_J ≤ S := fun a ha => (hVJ_le (hXJ_le ha)).1.2
  have hXJ_v : X_J ≤ centralizer ({v} : Set G) := fun a ha => (hVJ_le (hXJ_le ha)).2
  have hXK_K : X_K ≤ K := fun a ha => (hVK_le (hXK_le ha)).1.1
  have hXK_S : X_K ≤ S := fun a ha => (hVK_le (hXK_le ha)).1.2
  have hXK_v : X_K ≤ centralizer ({v} : Set G) := fun a ha => (hVK_le (hXK_le ha)).2
  have hJcomp : IsPCompIn 2 (centralizer ({x} : Set G)) J := hJ.1.1.2.2
  have hKcomp : IsPCompIn 2 (centralizer ({x} : Set G)) K := hK.1.1.2.2
  obtain ⟨eZ, e4, -⟩ := exists_rigid_center_sylow_equiv_of_center_card_sixteen hJ hS hL34 h16
  let W_J : Subgroup G := S ⊓ zStar J
  let eW : ↥W_J ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := eZ.trans e4
  let Ω : Set G := {w : G | w ∈ W_J ∧ w * w = 1}
  have hΩ_card : Nat.card ↥Ω = 4 := by
    have hmodel : Fintype.card
        {m : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // m ^ 2 = 1} = 4 := by
      decide
    have hiff : ∀ w : ↥W_J, ((w : G) * (w : G) = 1) ↔ ((eW.toEquiv w) ^ 2 = 1) := by
      intro w
      constructor
      · intro hw
        have hww : w * w = 1 := Subtype.ext hw
        have h1 : eW (w * w) = 1 := by rw [hww, map_one]
        simpa [pow_two, map_mul] using h1
      · intro hw
        have hww : w * w = 1 := by
          apply eW.injective
          rw [map_mul, map_one]
          simpa [pow_two] using hw
        simpa using congrArg (fun z : ↥W_J => (z : G)) hww
    let e1 : ↥Ω ≃ {w : ↥W_J // ((w : G) * (w : G) = 1)} :=
      { toFun := fun w => ⟨⟨w.1, w.2.1⟩, w.2.2⟩
        invFun := fun w => ⟨w.1.1, w.1.2, w.2⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
    let e2 : {w : ↥W_J // ((w : G) * (w : G) = 1)} ≃
        {m : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // m ^ 2 = 1} :=
      Equiv.subtypeEquiv eW.toEquiv hiff
    calc Nat.card ↥Ω
        = Nat.card {w : ↥W_J // ((w : G) * (w : G) = 1)} := Nat.card_congr e1
      _ = Nat.card {m : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // m ^ 2 = 1} :=
          Nat.card_congr e2
      _ = Fintype.card {m : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // m ^ 2 = 1} :=
          Nat.card_eq_fintype_card
      _ = 4 := hmodel
  have hthird : ∃ K₃ ∈ RigidSet fullQ x, K₃ ≠ J ∧ K₃ ≠ K := by
    by_contra h
    push Not at h
    have hsub : (RigidSet fullQ x : Set (Subgroup G)) ⊆ ({J, K} : Set (Subgroup G)) := by
      intro K₃ hK₃
      by_cases hJ₃ : K₃ = J
      · rw [hJ₃]
        simp
      · have hK₃K : K₃ = K := h K₃ hK₃ hJ₃
        rw [hK₃K]
        simp
    have hle : (RigidSet fullQ x).ncard ≤ ({J, K} : Set (Subgroup G)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have hpair : ({J, K} : Set (Subgroup G)).ncard = 2 := Set.ncard_pair hKJ.symm
    have hcard : Nat.card ↥(RigidSet fullQ x) = (RigidSet fullQ x).ncard :=
      Nat.card_coe_set_eq _
    omega
  obtain ⟨K₃, hK₃, hK₃J, hK₃K⟩ := hthird
  have hK₃comp : IsPCompIn 2 (centralizer ({x} : Set G)) K₃ := hK₃.1.1.2.2
  have hJ_cK₃ : J ≤ centralizerSection K₃ (pPrimeCoreOf 2 K₃) :=
    CFSG.GH74.GLS.Stage1.Thm2.Recip.le_cSec_of_ne hJcomp hK₃comp hK₃J.symm
  have hK_cK₃ : K ≤ centralizerSection K₃ (pPrimeCoreOf 2 K₃) :=
    CFSG.GH74.GLS.Stage1.Thm2.Recip.le_cSec_of_ne hKcomp hK₃comp hK₃K.symm
  obtain ⟨g, hg⟩ := isConj_iff.mp hxv
  have hL₁ : cmap g J ∈ RigidSet fullQ v := by
    have h := isRigidOfType_conj (Q := fullQ) hJ g
    rwa [hg] at h
  let E : Subgroup G := Subgroup.closure ((X_J : Set G) ∪ (X_K : Set G) ∪ Ω)
  have hXJ_E : X_J ≤ E := fun a ha => Subgroup.subset_closure (Or.inl (Or.inl ha))
  have hXK_E : X_K ≤ E := fun a ha => Subgroup.subset_closure (Or.inl (Or.inr ha))
  have hΩ_E : Ω ⊆ E := fun a ha => Subgroup.subset_closure (Or.inr ha)
  have hXJ_ab : ∀ a ∈ X_J, ∀ b ∈ X_J, a * b = b * a :=
    CFSG.GH74.GLS.Stage1.Thm4.P92.comm_of_sq
      (fun x hx => by simpa [pow_two] using hXJ_sq x hx)
  have hXK_ab : ∀ a ∈ X_K, ∀ b ∈ X_K, a * b = b * a :=
    CFSG.GH74.GLS.Stage1.Thm4.P92.comm_of_sq
      (fun x hx => by simpa [pow_two] using hXK_sq x hx)
  have hgen_comm : ∀ a ∈ ((X_J : Set G) ∪ (X_K : Set G) ∪ Ω),
      ∀ b ∈ ((X_J : Set G) ∪ (X_K : Set G) ∪ Ω), a * b = b * a := by
    intro a ha b hb
    rcases ha with (ha | ha) | ha
    · rcases hb with (hb | hb) | hb
      · exact hXJ_ab a ha b hb
      · exact commute_of_mem_isPCompIn_of_ne hJcomp hKcomp hKJ.symm hS.isPGroup
          ⟨hXJ_S ha, hXJ_J ha⟩ ⟨hXK_S hb, hXK_K hb⟩
      · exact hVJ_comm a (hXJ_le ha) b (hWJ_le hb.1)
    · rcases hb with (hb | hb) | hb
      · exact commute_of_mem_isPCompIn_of_ne hKcomp hJcomp hKJ hS.isPGroup
          ⟨hXK_S ha, hXK_K ha⟩ ⟨hXJ_S hb, hXJ_J hb⟩
      · exact hXK_ab a ha b hb
      · exact commute_of_mem_isPCompIn_of_ne hKcomp hJcomp hKJ hS.isPGroup
          ⟨hXK_S ha, hXK_K ha⟩ ⟨hb.1.1, hb.1.2.1⟩
    · rcases hb with (hb | hb) | hb
      · exact hVJ_comm a (hWJ_le ha.1) b (hXJ_le hb)
      · exact commute_of_mem_isPCompIn_of_ne hJcomp hKcomp hKJ.symm hS.isPGroup
          ⟨ha.1.1, ha.1.2.1⟩ ⟨hXK_S hb, hXK_K hb⟩
      · exact commute_of_mem_inf_zStar eZ ha.1 hb.1
  have hE_comm : IsMulCommutative ↥E := by
    change IsMulCommutative ↥(Subgroup.closure ((X_J : Set G) ∪ (X_K : Set G) ∪ Ω))
    exact Subgroup.isMulCommutative_closure (fun a ha b hb _ => hgen_comm a ha b hb)
  have hE_sq : ∀ a ∈ E, a * a = 1 := by
    intro a ha
    refine Subgroup.closure_induction
      (k := ((X_J : Set G) ∪ (X_K : Set G) ∪ Ω))
      (p := fun a _ => a * a = 1) ?_ ?_ ?_ ?_ ha
    · intro y hy
      rcases hy with (hy | hy) | hy
      · simpa [pow_two] using hXJ_sq y hy
      · simpa [pow_two] using hXK_sq y hy
      · exact hy.2
    · simp
    · intro y z hy hz hy2 hz2
      have hyz : y * z = z * y := by
        have h := (isMulCommutative_iff.mp hE_comm) (⟨y, hy⟩ : ↥E) (⟨z, hz⟩ : ↥E)
        exact congrArg Subtype.val h
      calc (y * z) * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [← hyz]
        _ = (y * y) * (z * z) := by group
        _ = 1 := by rw [hy2, hz2, one_mul]
    · intro y _ hy2
      rw [inv_eq_of_mul_eq_one_right hy2]
      exact hy2
  have hE_commG : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h := (isMulCommutative_iff.mp hE_comm) (⟨a, ha⟩ : ↥E) (⟨b, hb⟩ : ↥E)
    exact congrArg Subtype.val h
  have hker : ∀ (x₁ : G), x₁ ∈ X_J → ∀ (x₂ : G), x₂ ∈ X_K → ∀ (w : G), w ∈ Ω →
      x₁ * x₂ * w = 1 → x₁ = 1 ∧ x₂ = 1 ∧ w = 1 := by
    intro x₁ hx₁ x₂ hx₂ w hw hprod
    have hK_cJ : K ≤ centralizerSection J (pPrimeCoreOf 2 J) :=
      CFSG.GH74.GLS.Stage1.Thm2.Recip.le_cSec_of_ne hKcomp hJcomp hKJ
    have hJ_cK : J ≤ centralizerSection K (pPrimeCoreOf 2 K) :=
      CFSG.GH74.GLS.Stage1.Thm2.Recip.le_cSec_of_ne hJcomp hKcomp hKJ.symm
    have hx₂_cJ : x₂ ∈ centralizerSection J (pPrimeCoreOf 2 J) := hK_cJ (hXK_K hx₂)
    have hw_cJ : w ∈ centralizerSection J (pPrimeCoreOf 2 J) := hw.1.2.2
    have hx₁_eq : x₁ = (x₂ * w)⁻¹ := by
      rw [mul_assoc] at hprod
      exact eq_inv_of_mul_eq_one_left hprod
    have hx₁_cJ : x₁ ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
      rw [hx₁_eq]
      exact (centralizerSection J (pPrimeCoreOf 2 J)).inv_mem
        ((centralizerSection J (pPrimeCoreOf 2 J)).mul_mem hx₂_cJ hw_cJ)
    have hx₁_one : x₁ = 1 := by
      have hmem : x₁ ∈ X_J ⊓ zStar J := ⟨hx₁, ⟨hXJ_J hx₁, hx₁_cJ⟩⟩
      rw [hXJ_bot] at hmem
      simpa using hmem
    have hx₂w_one : x₂ * w = 1 := by
      rw [hx₁_one, one_mul] at hprod
      exact hprod
    have hx₂_eq : x₂ = w⁻¹ := eq_inv_of_mul_eq_one_left hx₂w_one
    have hwJ : w ∈ J := hw.1.2.1
    have hx₂_cK : x₂ ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
      rw [hx₂_eq]
      exact hJ_cK (J.inv_mem hwJ)
    have hx₂_one : x₂ = 1 := by
      have hmem : x₂ ∈ X_K ⊓ zStar K := ⟨hx₂, ⟨hXK_K hx₂, hx₂_cK⟩⟩
      rw [hXK_bot] at hmem
      simpa using hmem
    refine ⟨hx₁_one, hx₂_one, ?_⟩
    rw [hx₂_one, one_mul] at hx₂w_one
    exact hx₂w_one
  have hE_le_S : E ≤ S := by
    refine (Subgroup.closure_le S).mpr ?_
    intro a ha
    rcases ha with (ha | ha) | ha
    · exact hXJ_S ha
    · exact hXK_S ha
    · exact ha.1.1
  have hE_le_v : E ≤ centralizer ({v} : Set G) := by
    refine (Subgroup.closure_le (centralizer ({v} : Set G))).mpr ?_
    intro a ha
    rcases ha with (ha | ha) | ha
    · exact hXJ_v ha
    · exact hXK_v ha
    · exact (hVJ_le (hWJ_le ha.1)).2
  have hE_le_Cx : E ≤ centralizer ({x} : Set G) := hE_le_S.trans hS.le
  have hE_le_cK₃ : E ≤ centralizerSection K₃ (pPrimeCoreOf 2 K₃) := by
    refine (Subgroup.closure_le (centralizerSection K₃ (pPrimeCoreOf 2 K₃))).mpr ?_
    intro a ha
    rcases ha with (ha | ha) | ha
    · exact hJ_cK₃ (hXJ_J ha)
    · exact hK_cK₃ (hXK_K ha)
    · exact hJ_cK₃ ha.1.2.1
  have hE_le_N : E ≤ normalizer ((cmap g J : Subgroup G) : Set G) := by
    intro e he
    by_cases he1 : e = 1
    · rw [he1]
      exact Subgroup.one_mem _
    · have he2 : orderOf e = 2 := by
        have h2 : e * e = 1 := hE_sq e he
        have hdvd : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using h2)
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) he1
        · exact h
      exact normalizes_rigid_family_of_centralizing_involution hnonab hKproper hL34 h16
        hx2 hv2 hxv hvx hJ hvN hvact hxP hmax S hS hvS K₃ hK₃ e he2 (hE_le_S he)
        (hE_le_v he) (hE_le_cK₃ he) (cmap g J) hL₁
  have h64 : 64 ≤ Nat.card ↥E := by
    have hinj : Function.Injective
        (fun p : ↥X_J × ↥X_K × ↥Ω =>
          (⟨(p.1 : G) * (p.2.1 : G) * (p.2.2 : G),
            E.mul_mem (E.mul_mem (hXJ_E p.1.2) (hXK_E p.2.1.2)) (hΩ_E p.2.2.2)⟩ : ↥E)) := by
      rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, ⟨w, hw⟩⟩ ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, ⟨w', hw'⟩⟩ heq
      have heq' : x₁ * x₂ * w = y₁ * y₂ * w' := by simpa using heq
      have hx₁E : x₁ ∈ E := hXJ_E hx₁
      have hy₁E : y₁ ∈ E := hXJ_E hy₁
      have hx₂E : x₂ ∈ E := hXK_E hx₂
      have hy₂E : y₂ ∈ E := hXK_E hy₂
      have hwE : w ∈ E := hΩ_E hw
      have hw'E : w' ∈ E := hΩ_E hw'
      have hWW : w * w' ∈ Ω := by
        refine ⟨W_J.mul_mem hw.1 hw'.1, ?_⟩
        have hc : w * w' = w' * w := commute_of_mem_inf_zStar eZ hw.1 hw'.1
        calc (w * w') * (w * w') = w * (w' * w) * w' := by group
          _ = w * (w * w') * w' := by rw [← hc]
          _ = (w * w) * (w' * w') := by group
          _ = 1 := by rw [hw.2, hw'.2, one_mul]
      have hXYW : (x₁ * y₁) * (x₂ * y₂) * (w * w') = 1 := by
        have : CommGroup ↥E := IsMulCommutative.instCommGroup
        let a₁ : ↥E := ⟨x₁, hx₁E⟩
        let b₁ : ↥E := ⟨y₁, hy₁E⟩
        let a₂ : ↥E := ⟨x₂, hx₂E⟩
        let b₂ : ↥E := ⟨y₂, hy₂E⟩
        let c₁ : ↥E := ⟨w, hwE⟩
        let c₂ : ↥E := ⟨w', hw'E⟩
        have hheq : a₁ * a₂ * c₁ = b₁ * b₂ * c₂ := by
          apply Subtype.ext
          simpa [a₁, b₁, a₂, b₂, c₁, c₂] using heq'
        have hsq : a₁ * a₂ * c₁ * (a₁ * a₂ * c₁) = 1 := by
          apply Subtype.ext
          have hmem : x₁ * x₂ * w ∈ E := E.mul_mem (E.mul_mem hx₁E hx₂E) hwE
          simpa [a₁, a₂, c₁, Subgroup.coe_mul, mul_assoc] using hE_sq (x₁ * x₂ * w) hmem
        have hbig : a₁ * b₁ * (a₂ * b₂) * (c₁ * c₂) = 1 := by
          calc a₁ * b₁ * (a₂ * b₂) * (c₁ * c₂)
              = (a₁ * a₂ * c₁) * (b₁ * b₂ * c₂) := by ac_rfl
            _ = (a₁ * a₂ * c₁) * (a₁ * a₂ * c₁) := by rw [hheq]
            _ = 1 := hsq
        have := congrArg Subtype.val hbig
        simpa [a₁, b₁, a₂, b₂, c₁, c₂, Subgroup.coe_mul, mul_assoc] using this
      obtain ⟨hxy1, hxy2, hww⟩ :=
        hker (x₁ * y₁) (X_J.mul_mem hx₁ hy₁) (x₂ * y₂) (X_K.mul_mem hx₂ hy₂) (w * w') hWW hXYW
      have hy₁_inv : y₁⁻¹ = y₁ :=
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hXJ_sq y₁ hy₁)
      have hy₂_inv : y₂⁻¹ = y₂ :=
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hXK_sq y₂ hy₂)
      have hw'_inv : w'⁻¹ = w' := inv_eq_of_mul_eq_one_right hw'.2
      have h1 : x₁ = y₁ := by rw [eq_inv_of_mul_eq_one_left hxy1, hy₁_inv]
      have h2 : x₂ = y₂ := by rw [eq_inv_of_mul_eq_one_left hxy2, hy₂_inv]
      have h3 : w = w' := by rw [eq_inv_of_mul_eq_one_left hww, hw'_inv]
      exact Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2) (Subtype.ext h3))
    have hcard := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, Nat.card_prod, hXJ_card, hXK_card, hΩ_card] at hcard
    norm_num at hcard
    exact hcard
  have h16E : Nat.card ↥E ≤ 16 :=
    card_le_sixteen_of_le_normalizer hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact
      hxP hmax hK₃ hL₁ (le_inf (le_inf (le_inf hE_le_Cx hE_le_cK₃) hE_le_v) hE_le_N)
      hE_commG hE_sq
  omega

theorem false_of_inner_rigid_actor_of_card_eq_two
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 → Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    (hr : Nat.card ↥(RigidSet fullQ x) = 2)
    (hvin : MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨v, hvN⟩) ∈
      (MulAut.conj : kBar J →* MulAut (kBar J)).range) : False := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨g, hg⟩ := isConj_iff.mp hxv
  obtain ⟨S, hS, hvS, hT⟩ := exists_isSylowOf_inf_centralizer hv2 hvx
  have hv2' : v ^ 2 = 1 := by rw [← hv2]; exact pow_orderOf_eq_one v
  obtain ⟨V, X, hVJ, hVcomm, hWV, hXV, hXWbot, hX4, hX2, hVeq⟩ :=
    exists_root_preimage_lift_of_inner_actor hL34 h16 hJ hv2' hvN hvin hS hT
  let W : Subgroup G := S ⊓ zStar J
  let L₁ : Subgroup G := cmap g J
  obtain ⟨eZ, e4, -⟩ :=
    exists_rigid_center_sylow_equiv_of_center_card_sixteen hJ hS hL34 h16
  let eW : ↥W ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := eZ.trans e4
  have hL₁ : L₁ ∈ RigidSet fullQ v := by
    have h := isRigidOfType_conj (Q := fullQ) hJ g
    rw [show g * x * g⁻¹ = v from hg] at h
    exact h
  have hcardv : (RigidSet fullQ v).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    have h := card_rigidSet_conj (fullQ := fullQ) x g
    rw [hg] at h
    rw [h, hr]
  have hVJ' : V ≤ J := fun a ha => (hVJ ha).1.1
  have hVS : V ≤ S := fun a ha => (hVJ ha).1.2
  have hVcv : V ≤ centralizer ({v} : Set G) := fun a ha => (hVJ ha).2
  have hXS : X ≤ S := hXV.trans hVS
  have hXW : X ⊓ W = ⊥ := by
    have h : X ⊓ W = X ⊓ zStar J := by
      dsimp [W]
      rw [← inf_assoc, inf_eq_left.mpr hXS]
    rw [h, hXWbot]
  have hVsup : X ⊔ W ≤ V := le_of_eq hVeq
  have hcomm : ∀ a ∈ X ⊔ W, ∀ b ∈ X ⊔ W, a * b = b * a :=
    fun a ha b hb => hVcomm a (hVsup ha) b (hVsup hb)
  have hr2 : (RigidSet fullQ x).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hr
  obtain ⟨K₂, hK₂, hK₂J⟩ : ∃ K₂ ∈ RigidSet fullQ x, K₂ ≠ J := by
    by_contra h
    push Not at h
    have hsub : RigidSet fullQ x ⊆ ({J} : Set (Subgroup G)) := fun K hK => by
      simp [h K hK]
    have hle : (RigidSet fullQ x).ncard ≤ 1 := by
      calc (RigidSet fullQ x).ncard ≤ ({J} : Set (Subgroup G)).ncard := Set.ncard_mono hsub
        _ = 1 := by simp
    omega
  have hJK₂ : J ≤ CFSG.GH74.GLS.Stage1.Thm2.Recip.cSec K₂ :=
    CFSG.GH74.GLS.Stage1.Thm2.Recip.le_cSec_of_ne hJ.1.1.2.2 hK₂.1.1.2.2
      (Ne.symm hK₂J)
  have hVK₂ : V ≤ CxK x K₂ := fun a ha =>
    ⟨(hJ.1.1.2.2.1) (hVJ' ha), hJK₂ (hVJ' ha)⟩
  have hBcard : Nat.card V ≤ 2 * Nat.card ↥(V ⊓ normalizer (L₁ : Set G)) := by
    refine CFSG.ComponentClassification.HSFLit.AutL34.card_le_two_mul
      (A := V) (C := normalizer (L₁ : Set G)) ?_
    intro a haV b hbV haN hbN
    have ha_rig : cmap a L₁ ∈ RigidSet fullQ v := by
      have hav : a * v * a⁻¹ = v := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp (hVcv haV)]
        group
      have h := isRigidOfType_conj (Q := fullQ) hL₁ a
      rw [hav] at h
      exact h
    have hb_rig : cmap b L₁ ∈ RigidSet fullQ v := by
      have hbv : b * v * b⁻¹ = v := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp (hVcv hbV)]
        group
      have h := isRigidOfType_conj (Q := fullQ) hL₁ b
      rw [hbv] at h
      exact h
    have ha_ne : cmap a L₁ ≠ L₁ := fun h =>
      haN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    have hb_ne : cmap b L₁ ≠ L₁ := fun h =>
      hbN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    have hsub : (RigidSet fullQ v \ {L₁}).Subsingleton := by
      apply Set.ncard_le_one_iff_subsingleton.mp
      rw [Set.ncard_sdiff_singleton_of_mem hL₁, hcardv]
    have heq : cmap a L₁ = cmap b L₁ := hsub ⟨ha_rig, ha_ne⟩ ⟨hb_rig, hb_ne⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change cmap (a⁻¹ * b) L₁ = L₁
    rw [← cmap_cmap a⁻¹ b L₁, ← heq, cmap_inv_cancel]
  have hBV : V ⊓ normalizer (L₁ : Set G) ≤ X ⊔ W :=
    fun p hp => le_of_eq hVeq.symm hp.1
  have hB : Nat.card ↥(X ⊔ W) ≤ 2 * Nat.card ↥(V ⊓ normalizer (L₁ : Set G)) := by
    rw [hVeq]
    exact hBcard
  obtain ⟨a, haB, b, hbB, c, hcB, ha4, hb2, hc2, ha2, hb1, hba, hc1, hca, hcb, hcab⟩ :=
    exists_z4E4_of_two_mul_card_le (X := X) (W := W) (B := V ⊓ normalizer (L₁ : Set G))
      hXW hcomm hX4 hX2 eW hBV hB
  exact false_of_z4E4_mem_normalizer hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact
    hxP hmax hK₂ hL₁
    ⟨⟨hVK₂ haB.1, hVcv haB.1⟩, haB.2⟩
    ⟨⟨hVK₂ hbB.1, hVcv hbB.1⟩, hbB.2⟩
    ⟨⟨hVK₂ hcB.1, hVcv hcB.1⟩, hcB.2⟩
    (hVcomm a haB.1 b hbB.1) (hVcomm a haB.1 c hcB.1) (hVcomm b hbB.1 c hcB.1)
    ha4 hb2 hc2 ha2 hb1 hba hc1 hca hcb hcab

theorem card_rigidSet_eq_one_of_rigid_actor
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 → Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x)) :
    Nat.card ↥(RigidSet fullQ x) = 1 := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have : Nonempty ↥(RigidSet fullQ x) := ⟨⟨J, hJ⟩⟩
  have hpos : 0 < Nat.card ↥(RigidSet fullQ x) := Nat.card_pos
  by_contra hne
  have hr : 1 < Nat.card ↥(RigidSet fullQ x) := by
    rcases lt_or_ge 1 (Nat.card ↥(RigidSet fullQ x)) with h | h
    · exact h
    · exfalso
      exact hne (by omega)
  obtain ⟨t₁, ht₁N, ht₁2, ht₁conj, ht₁x, ht₁act, ht₁in⟩ :=
    exists_inner_rigid_actor_of_one_lt_card hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN
      hvact hxP hmax hr
  by_cases hr2 : Nat.card ↥(RigidSet fullQ x) = 2
  · exact false_of_inner_rigid_actor_of_card_eq_two hnonab hKproper hL34 h16 hx2 ht₁2 ht₁conj
      ht₁x hJ ht₁N ht₁act hxP hmax hr2 ht₁in
  · have hr3 : 2 < Nat.card ↥(RigidSet fullQ x) := by
      rcases lt_or_ge 2 (Nat.card ↥(RigidSet fullQ x)) with h | h
      · exact h
      · exfalso
        exact hr2 (by omega)
    obtain ⟨g, hg⟩ := isConj_iff.mp ht₁conj
    obtain ⟨K, hK, hKJ, y, hyZ, hy4, hyv, hswap⟩ :=
      exists_swap_of_inner_rigid_actor hnonab hKproper hL34 h16 hx2 ht₁2 ht₁conj ht₁x hJ
        ht₁N ht₁act hxP hmax hr ht₁in hg
    obtain ⟨t₂, ht₂J, ht₂K, ht₂2, ht₂conj, ht₂x, ht₂actJ, ht₂inJ, ht₂actK, ht₂inK⟩ :=
      exists_inner_rigid_actor_pair_of_one_lt_card hnonab hKproper hL34 h16 hx2 ht₁2 ht₁conj
        ht₁x hJ ht₁N ht₁act hxP hmax hr hK hg hyZ hy4 hyv hswap
    exact false_of_inner_rigid_actor_pair_of_two_lt_card hnonab hKproper hL34 h16 hx2 ht₂2
      ht₂conj ht₂x hJ ht₂J ht₂actJ hxP hmax hr3 ht₂inJ hK hKJ ht₂K ht₂inK

theorem rigidSet_subsingleton_of_rigid_actor
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 → Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x)) :
    ∀ s : G, orderOf s = 2 → (RigidSet fullQ s).Subsingleton := by
  have hz : (RigidSet fullQ x).ncard = 1 := by
    have h := Nat.card_coe_set_eq (RigidSet fullQ x)
    rw [← h]
    exact card_rigidSet_eq_one_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN
      hvact hxP hmax
  have hmax' : ∀ s : G, orderOf s = 2 →
      (RigidSet fullQ s).ncard ≤ (RigidSet fullQ x).ncard := by
    intro s hs
    rw [← Nat.card_coe_set_eq (RigidSet fullQ s),
      ← Nat.card_coe_set_eq (RigidSet fullQ x)]
    exact hmax s hs
  exact rigidSet_subsingleton_of_global_max_one (Q := fullQ) (G := G) hz hmax'

end CFSG.GH74.GLS.NT44
