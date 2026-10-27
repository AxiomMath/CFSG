module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017Alt7Orb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017Image

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H2017L

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.LocalAnalysis.GLTheoremA.I2017

variable {G : Type} [Group G] [Finite G]

theorem mem_imageMod_top (K : Subgroup G) (q : PQuot 3 K) : q ∈ imageMod 3 K K := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K) q
  exact Subgroup.mem_map.2 ⟨k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩

theorem exists_elemAb_lift {K D : Subgroup G} (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hDp : IsPGroup 3 D) {E : Subgroup (PQuot 3 K)} (hEab : IsElemAbelian 3 E)
    (hEcard : Nat.card ↥E = 3 ^ 4)
    (hEfix : ∀ q ∈ E, ∀ (e : G) (he : e ∈ D), barAut 3 K ⟨e, hDK he⟩ q = q) :
    ∃ P : Subgroup G, P ≤ K ⊓ Subgroup.centralizer (D : Set G) ∧ IsElemAbelian 3 P ∧
      Nat.card ↥P = 3 ^ 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  set N : Subgroup ↥K := GLAPPrimeCore 3 ↥K with hNdef
  set φ : ↥K →* PQuot 3 K := QuotientGroup.mk' N with hφdef
  set C : Subgroup ↥K := (K ⊓ Subgroup.centralizer (D : Set G)).subgroupOf K with hCdef
  have hlift : ∀ q ∈ E, ∃ c ∈ C, φ c = q := by
    intro q hq
    have hmem := imageMod_fixed_lift hDp hDK hDK le_rfl (mem_imageMod_top K q)
      (fun e he => hEfix q hq e he)
    obtain ⟨c, hc, hcq⟩ := Subgroup.mem_map.1 hmem
    exact ⟨c, hc, hcq⟩
  set Hs : Subgroup ↥K := C ⊓ E.comap φ with hHsdef
  have hHsE : ∀ h ∈ Hs, φ h ∈ E := fun h hh => hh.2
  have hHsurj : ∀ q ∈ E, ∃ h ∈ Hs, φ h = q := by
    intro q hq
    obtain ⟨c, hc, hcq⟩ := hlift q hq
    exact ⟨c, ⟨hc, by simpa [hcq] using hq⟩, hcq⟩
  let f : ↥Hs →* PQuot 3 K := φ.comp Hs.subtype
  have hfrange : f.range = E := by
    apply le_antisymm
    · rintro _ ⟨h, rfl⟩
      exact hHsE h.1 h.2
    · intro q hq
      obtain ⟨h, hh, hhq⟩ := hHsurj q hq
      exact ⟨⟨h, hh⟩, hhq⟩
  have hker_le : f.ker.map Hs.subtype ≤ N := by
    rintro _ ⟨h, hh, rfl⟩
    have h1 : φ (h : ↥K) = 1 := hh
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hkerdvd : Nat.card ↥f.ker ∣ Nat.card ↥N := by
    rw [← Subgroup.card_map_of_injective (f := Hs.subtype) Hs.subtype_injective]
    exact Subgroup.card_dvd_of_le hker_le
  have hkercop : Nat.Coprime 3 (Nat.card ↥f.ker) := Nat.Coprime.coprime_dvd_right hkerdvd hcop
  have hHscard : Nat.card ↥Hs = 3 ^ 4 * Nat.card ↥f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hfrange, hEcard]
  have hdvd : 3 ^ 4 ∣ Nat.card ↥Hs := ⟨_, hHscard⟩
  obtain ⟨Ps, hPs⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  set P : Subgroup ↥K := Ps.map Hs.subtype with hPdef
  have hPcard : Nat.card ↥P = 3 ^ 4 := by
    rw [hPdef, Subgroup.card_map_of_injective Hs.subtype_injective, hPs]
  have hPHs : P ≤ Hs := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hPN : P ⊓ N = ⊥ := by
    have h1 : Nat.card ↥(P ⊓ N) ∣ 3 ^ 4 := by
      rw [← hPcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(P ⊓ N) ∣ Nat.card ↥N := Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.Coprime (Nat.card ↥(P ⊓ N)) (3 ^ 4) :=
      Nat.Coprime.pow_right 4 (Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right h2 hcop))
    exact Subgroup.card_eq_one.1 (Nat.Coprime.eq_one_of_dvd h3 h1)
  have hφinjP : ∀ a ∈ P, φ a = 1 → a = 1 := by
    intro a ha h1
    have haN : a ∈ P ⊓ N := ⟨ha, (QuotientGroup.eq_one_iff a).1 h1⟩
    rw [hPN] at haN
    exact haN
  have hφP : ∀ a ∈ P, φ a ∈ E := fun a ha => hHsE a (hPHs ha)
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    have hc : φ a * φ b = φ b * φ a :=
      congrArg Subtype.val (hEab.1.is_comm.comm ⟨φ a, hφP a ha⟩ ⟨φ b, hφP b hb⟩)
    have hab : a * b * (b * a)⁻¹ ∈ P := P.mul_mem (P.mul_mem ha hb) (P.inv_mem (P.mul_mem hb ha))
    have h1 : φ (a * b * (b * a)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc]
      exact mul_inv_cancel _
    exact mul_inv_eq_one.1 (hφinjP _ hab h1)
  have hPexp : ∀ a ∈ P, a ^ 3 = 1 := by
    intro a ha
    apply hφinjP _ (P.pow_mem ha 3)
    rw [map_pow]
    exact hEab.2 _ (hφP a ha)
  refine ⟨P.map K.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxC : x ∈ C := (inf_le_left : Hs ≤ C) (hPHs hx)
    exact Subgroup.mem_subgroupOf.1 hxC
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      show (a : G) * (b : G) = (b : G) * (a : G)
      rw [← hxa, ← hyb]
      show ((x : ↥K) : G) * ((y : ↥K) : G) = ((y : ↥K) : G) * ((x : ↥K) : G)
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hPcomm x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      show ((x ^ 3 : ↥K) : G) = 1
      rw [hPexp x hx]
      rfl
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hPcard]

theorem zpowers_inter_eq_one {K : Subgroup G} {d : G} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hdK : d ∉ K) {z : G}
    (hz : z ∈ Subgroup.zpowers d) (hzK : z ∈ K) : z = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hmod : d ^ j = d ^ (j % 3) := by
    have h := zpow_mod_orderOf d j
    rw [hord] at h
    exact h.symm
  have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hcases with h | h | h
  · rw [hmod, h, zpow_zero]
  · exfalso
    apply hdK
    have h1 : d ^ j = d := by rw [hmod, h, zpow_one]
    rw [← h1]
    exact hzK
  · exfalso
    apply hdK
    have h2 : d ^ j = d ^ 2 := by rw [hmod, h]; norm_cast
    have hd2K : d ^ 2 ∈ K := by rw [← h2]; exact hzK
    have h4 : (d ^ 2) ^ 2 = d := by
      rw [← pow_mul]
      calc d ^ (2 * 2) = d * d ^ 3 := by
            rw [show 2 * 2 = 1 + 3 from rfl, pow_add, pow_one]
        _ = d := by rw [hd3, mul_one]
    rw [← h4]
    exact K.pow_mem hd2K 2

theorem not_mem_of_centMod {K D : Subgroup G} (hDK : D ≤ Subgroup.normalizer (K : Set G)) {d : G}
    (hd : d ∈ D) (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1) (hdC : CentMod 3 K d)
    (hZ : ∀ z ∈ Subgroup.center (PQuot 3 K), z ^ 3 = 1 → z = 1) : d ∉ K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hdK
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  have hdN : d ∈ Subgroup.normalizer (K : Set G) := hDK hd
  have hbar : barAut 3 K ⟨d, hdN⟩ = 1 := (barAut_eq_one_iff_centMod hdN).2 hdC
  set γ : ↥K := ⟨d, hdK⟩ with hγdef
  set z : PQuot 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) γ with hzdef
  have hzc : z ∈ Subgroup.center (PQuot 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K) g
    have hk : barAut 3 K ⟨d, hdN⟩ (QuotientGroup.mk k) = QuotientGroup.mk k := by
      rw [hbar, MulAut.one_apply]
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at hk
    have hk' : (QuotientGroup.mk (γ * k * γ⁻¹) : PQuot 3 K) = QuotientGroup.mk k := hk
    have key : z * (QuotientGroup.mk k : PQuot 3 K) = QuotientGroup.mk k * z := by
      calc z * (QuotientGroup.mk k : PQuot 3 K) = QuotientGroup.mk (γ * k) := by
            rw [hzdef]; rfl
        _ = QuotientGroup.mk (γ * k * γ⁻¹ * γ) := by
            congr 1; group
        _ = QuotientGroup.mk (γ * k * γ⁻¹) * QuotientGroup.mk γ := rfl
        _ = QuotientGroup.mk k * QuotientGroup.mk γ := by rw [hk']
        _ = QuotientGroup.mk k * z := by rw [hzdef]; rfl
    exact key.symm
  have hγ3 : γ ^ 3 = 1 := Subtype.ext (by simpa [hγdef] using hd3)
  have hz3 : z ^ 3 = 1 := by rw [hzdef, ← map_pow, hγ3, map_one]
  have hz1 : z = 1 := hZ z hzc hz3
  have hγN : γ ∈ GLAPPrimeCore 3 ↥K := (QuotientGroup.eq_one_iff γ).1 hz1
  have hγ1 : γ ≠ 1 := by
    intro h
    apply hd1
    have := congrArg Subtype.val h
    simpa [hγdef] using this
  have hord : orderOf γ = 3 := orderOf_eq_prime hγ3 hγ1
  have hdvd : orderOf (⟨γ, hγN⟩ : ↥(GLAPPrimeCore 3 ↥K)) ∣ Nat.card ↥(GLAPPrimeCore 3 ↥K) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at hdvd
  have h3 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  norm_num at h3

theorem exists_rank_five {K D P : Subgroup G} {d : G} (hDab : IsElemAbelian 3 D) (hd : d ∈ D)
    (hd1 : d ≠ 1) (hdK : d ∉ K) (hPK : P ≤ K ⊓ Subgroup.centralizer (D : Set G))
    (hPab : IsElemAbelian 3 P) (hP81 : Nat.card ↥P = 3 ^ 4) :
    ∃ P' : Subgroup G, P' ≤ (K ⊔ D) ⊓ Subgroup.centralizer (D : Set G) ∧ IsElemAbelian 3 P' ∧
      Nat.card ↥P' = 3 ^ 5 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3 : d ^ 3 = 1 := hDab.2 d hd
  set Z : Subgroup G := Subgroup.zpowers d with hZdef
  have hZD : Z ≤ D := Subgroup.zpowers_le.2 hd
  have hZcard : Nat.card ↥Z = 3 := by
    rw [hZdef, Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hDab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hPZ : ∀ p ∈ P, ∀ z ∈ Z, p * z = z * p := by
    intro p hp z hz
    exact ((Subgroup.mem_centralizer_iff.1 (hPK hp).2) z (hZD hz)).symm
  have hZcomm : ∀ z ∈ Z, ∀ w ∈ Z, z * w = w * z := fun z hz w hw => hDcomm z (hZD hz) w (hZD hw)
  let Φ : (↥P × ↥Z) →* G :=
    { toFun := fun u => (u.1 : G) * (u.2 : G)
      map_one' := by simp
      map_mul' := by
        intro u v
        have hc : (v.1 : G) * (u.2 : G) = (u.2 : G) * (v.1 : G) := hPZ _ v.1.2 _ u.2.2
        show ((u.1 : G) * (v.1 : G)) * ((u.2 : G) * (v.2 : G)) =
          ((u.1 : G) * (u.2 : G)) * ((v.1 : G) * (v.2 : G))
        calc ((u.1 : G) * (v.1 : G)) * ((u.2 : G) * (v.2 : G))
            = (u.1 : G) * (((v.1 : G) * (u.2 : G)) * (v.2 : G)) := by group
          _ = (u.1 : G) * (((u.2 : G) * (v.1 : G)) * (v.2 : G)) := by rw [hc]
          _ = ((u.1 : G) * (u.2 : G)) * ((v.1 : G) * (v.2 : G)) := by group }
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hu' : (u.1 : G) * (u.2 : G) = 1 := hu
    have h2 : (u.2 : G) = (u.1 : G)⁻¹ := eq_inv_of_mul_eq_one_right hu'
    have hz2K : (u.2 : G) ∈ K := by
      rw [h2]
      exact K.inv_mem (hPK u.1.2).1
    have hz2 : (u.2 : G) = 1 := zpowers_inter_eq_one hd3 hd1 hdK u.2.2 hz2K
    have h1 : (u.1 : G) = 1 := by
      rw [hz2, mul_one] at hu'
      exact hu'
    exact Prod.ext (Subtype.ext h1) (Subtype.ext hz2)
  refine ⟨MonoidHom.range Φ, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    have hu1 : (u.1 : G) ∈ K ⊓ Subgroup.centralizer (D : Set G) := hPK u.1.2
    have hu2 : (u.2 : G) ∈ D := hZD u.2.2
    refine ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu1.1) (Subgroup.mem_sup_right hu2)
    · refine Subgroup.mem_centralizer_iff.2 ?_
      intro h hh
      show h * ((u.1 : G) * (u.2 : G)) = ((u.1 : G) * (u.2 : G)) * h
      have c1 : h * (u.1 : G) = (u.1 : G) * h := (Subgroup.mem_centralizer_iff.1 hu1.2) h hh
      have c2 : h * (u.2 : G) = (u.2 : G) * h := hDcomm h hh _ hu2
      rw [← mul_assoc, c1, mul_assoc, c2, mul_assoc]
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨u, hu⟩ := a.2
      obtain ⟨v, hv⟩ := b.2
      show (a : G) * (b : G) = (b : G) * (a : G)
      rw [← hu, ← hv]
      show ((u.1 : G) * (u.2 : G)) * ((v.1 : G) * (v.2 : G)) =
        ((v.1 : G) * (v.2 : G)) * ((u.1 : G) * (u.2 : G))
      have hP : (u.1 : G) * (v.1 : G) = (v.1 : G) * (u.1 : G) :=
        congrArg Subtype.val (hPab.1.is_comm.comm u.1 v.1)
      have hZ2 : (u.2 : G) * (v.2 : G) = (v.2 : G) * (u.2 : G) := hZcomm _ u.2.2 _ v.2.2
      have hPZ1 : (v.1 : G) * (u.2 : G) = (u.2 : G) * (v.1 : G) := hPZ _ v.1.2 _ u.2.2
      have hPZ2 : (u.1 : G) * (v.2 : G) = (v.2 : G) * (u.1 : G) := hPZ _ u.1.2 _ v.2.2
      calc ((u.1 : G) * (u.2 : G)) * ((v.1 : G) * (v.2 : G))
          = (u.1 : G) * (((u.2 : G) * (v.1 : G)) * (v.2 : G)) := by group
        _ = (u.1 : G) * (((v.1 : G) * (u.2 : G)) * (v.2 : G)) := by rw [hPZ1]
        _ = ((u.1 : G) * (v.1 : G)) * ((u.2 : G) * (v.2 : G)) := by group
        _ = ((v.1 : G) * (u.1 : G)) * ((v.2 : G) * (u.2 : G)) := by rw [hP, hZ2]
        _ = (v.1 : G) * (((u.1 : G) * (v.2 : G)) * (u.2 : G)) := by group
        _ = (v.1 : G) * (((v.2 : G) * (u.1 : G)) * (u.2 : G)) := by rw [hPZ2]
        _ = ((v.1 : G) * (v.2 : G)) * ((u.1 : G) * (u.2 : G)) := by group
    · rintro _ ⟨u, rfl⟩
      show ((u.1 : G) * (u.2 : G)) ^ 3 = 1
      have hcomm12 : (u.1 : G) * (u.2 : G) = (u.2 : G) * (u.1 : G) := hPZ _ u.1.2 _ u.2.2
      rw [Commute.mul_pow hcomm12, hPab.2 _ u.1.2, hDab.2 _ (hZD u.2.2), one_mul]
  · rw [Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv.symm, Nat.card_prod, hP81, hZcard]
    norm_num

end CFSG.LocalAnalysis.GLTheoremA.H2017L
