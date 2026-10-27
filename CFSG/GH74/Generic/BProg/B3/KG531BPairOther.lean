module

public import CFSG.GH74.Generic.BProg.B3.KG531BPairMain
public import CFSG.GH74.Generic.BProg.B3.KG531BPairOrd
public import CFSG.GH74.Generic.BProg.B3.KG531Basic
public import CFSG.GH74.Generic.BProg.B3.KG531Ord
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.AS16.Defs
public import CFSG.GH74.E2.OddRankG
public import CFSG.GH74.GLS.C3.Layer1.BkIvk73Q
public import CFSG.GH74.GLS.C3.Layer2.L5C19
public import CFSG.GH74.GLS.C3.Layer2.L5C5c
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Kill
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Defs
public import CFSG.GH74.GLS.Stage4.RestP93
public import CFSG.GH74.GLS.Stage4.RestSetup
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace KG531BP

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups

theorem three_dvd_sq_sub_one {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have h : q % 3 = 1 ∨ q % 3 = 2 := by omega
  have h2 : q ^ 2 % 3 = 1 := by
    rcases h with h | h <;> simp [Nat.pow_mod, h]
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem false_of_sq_dvd {N : ℕ} (l : List ℕ) (hl : l.prod = N) (hpr : ∀ q ∈ l, q.Prime)
    (h5 : ∀ q ∈ l, 5 ≤ q → q ^ 2 ∣ N → ¬ 9 ∣ N) (h3 : 3 ^ 4 ∣ N → ¬ 25 ∣ N ∧ ¬ 3 ^ 6 ∣ N)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq5 : 5 ≤ p ^ f)
    (hD : ∀ m : ℕ, Odd m → m ∣ p ^ f * ((p ^ f) ^ 2 - 1) → m ^ 2 ∣ N) : False := by
  by_cases hp3 : p = 3
  · subst hp3
    have hf2 : 2 ≤ f := by
      by_contra h
      have : f = 1 := by omega
      subst this
      norm_num at hq5
    have hpow : (3 ^ f) ^ 2 ∣ N := hD (3 ^ f) (Odd.pow (by decide)) (Dvd.intro _ rfl)
    rw [← pow_mul] at hpow
    have h34 : 3 ^ 4 ∣ N := (pow_dvd_pow 3 (by omega : 4 ≤ f * 2)).trans hpow
    obtain ⟨h25, h36⟩ := h3 h34
    rcases Nat.eq_or_lt_of_le hf2 with rfl | hf3
    · exact h25 (by simpa using hD 5 (by decide) (by norm_num))
    · exact h36 ((pow_dvd_pow 3 (by omega : 6 ≤ f * 2)).trans hpow)
  · have hp4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
    have hp5 : 5 ≤ p := by have := hp.two_le; omega
    have hpp : p ^ 2 ∣ N := hD p (hp.odd_of_ne_two hp2)
      (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _)
    have hpN : p ∣ l.prod := hl ▸ (dvd_pow_self p two_ne_zero).trans hpp
    obtain ⟨q, hq, hpq⟩ := KG531Ord.exists_mem_dvd_of_prime_dvd_prod hp l hpN
    have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp (hpr q hq)).1 hpq
    subst hpq'
    have h9 := h5 p hq hp5 hpp
    have h3q : ¬ 3 ∣ p ^ f := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    have h3dvd : 3 ∣ p ^ f * ((p ^ f) ^ 2 - 1) := dvd_mul_of_dvd_right (three_dvd_sq_sub_one h3q) _
    exact h9 (by simpa using hD 3 (by decide) h3dvd)

theorem coprime_card_center {Q : Type} [Group Q] [Finite Q] (hO : pPrimeCore 2 Q = ⊥) {m : ℕ}
    (hm : Odd m) : Nat.Coprime m (Nat.card ↥(center Q)) := by
  apply Nat.coprime_of_dvd
  intro r hr hrm hrZ
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hrm)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center Q)) r hrZ
  have hzc : zpowers (z : Q) ≤ center Q := (Subgroup.zpowers_le).2 z.2
  have hN : (zpowers (z : Q)).Normal := CFSG.GroupTheory.normal_of_le_center hzc
  have hcard : Nat.card ↥(zpowers (z : Q)) = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
  have hle := CFSG.GroupTheory.le_pPrimeCore_of_normal hN (by
    rw [hcard]
    exact (Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2))
  rw [hO, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  have : z = 1 := Subtype.ext hle
  rw [this, orderOf_one] at hz
  exact hr.one_lt.ne hz

noncomputable def coreQuotEquiv {X : Type} [Group X] {L K : Subgroup X} (h : L ≤ K) {F : Type}
    [Field F] (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F)) :
    ↥(L.subgroupOf K) ⧸ pPrimeCore 2 ↥(L.subgroupOf K) ≃* SL(2, F) :=
  (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe h)
    (CFSG.pPrimeCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe h))).trans e

theorem not_le_of_pComponent {Q : Type*} [Group Q] [Finite Q] {J N : Subgroup Q}
    (hJ : IsPComponent 2 J) (hN : N ≤ center Q) : ¬ J ≤ N := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥J :=
    CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_perfect 2 J hJ
  have : IsMulCommutative ↥J :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp (hN (hle a.2)) (b : Q)).symm)⟩⟩
  have hss : Subsingleton ↥J := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hb : J = ⊥ := Subgroup.eq_bot_of_subsingleton _
  rw [hb] at hJ
  obtain ⟨Kc, hKc, -, hmap, -⟩ := hJ
  rw [Subgroup.map_bot] at hmap
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hKc.1
  rw [← hmap] at hnt
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt rfl

theorem ne_of_pair {X : Type} [Group X] [Finite X] {M : Subgroup X} {t s : X} (htM : t ∈ M)
    (htZ : (⟨t, htM⟩ : ↥M) ∉ center ↥M) {L₁ L₂ : Subgroup X}
    (h₁ : L₁ ≤ centralizer ({t} : Set X) ⊓ M) (hsL₁ : s ∈ L₁) (hs2 : orderOf s = 2)
    (hsZ : s ∈ (center ↥M).map M.subtype) (htL₂ : t ∈ L₂) (ht2 : orderOf t = 2) {F : Type}
    [Field F] (e₁ : ↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, F)) : L₁ ≠ L₂ := by
  rintro rfl
  classical
  set φ : ↥L₁ →* SL(2, F) := e₁.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L₁)) with hφ
  have hφs : Function.Surjective φ := e₁.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφk : ∀ y : ↥L₁, φ y = 1 ↔ y ∈ pPrimeCore 2 ↥L₁ := by
    intro y
    show e₁ (QuotientGroup.mk y) = 1 ↔ _
    rw [← map_one e₁, e₁.injective.eq_iff, QuotientGroup.eq_one_iff]
  obtain ⟨z, hzZ, hzs⟩ := hsZ
  set sl : ↥L₁ := ⟨s, hsL₁⟩ with hsl
  set tl : ↥L₁ := ⟨t, htL₂⟩ with htl
  have hsc : sl ∈ center ↥L₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgM : (g : X) ∈ M := (h₁ g.2).2
    have h' := congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨g, hgM⟩)
    simp only [Subgroup.coe_mul] at h'
    show (g : X) * s = s * g
    rw [← hzs]
    exact h'
  have htc : tl ∈ center ↥L₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (h₁ g.2).1
  have himg : ∀ y ∈ center ↥L₁, φ y ∈ center SL(2, F) := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := hφs g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy g']
  have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥L₁)) := CFSG.pPrimeCore_coprime_card
  have hone : ∀ y : ↥L₁, y ∈ pPrimeCore 2 ↥L₁ → orderOf y ∣ 2 → y = 1 := by
    intro y hyO hy2
    have hd : orderOf (⟨y, hyO⟩ : ↥(pPrimeCore 2 ↥L₁)) ∣ Nat.card ↥(pPrimeCore 2 ↥L₁) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hd
    have h1 : orderOf y = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hy2 hcop) hd
    exact orderOf_eq_one_iff.1 h1
  have hnot : ∀ y : ↥L₁, orderOf y = 2 → φ y ≠ 1 := by
    intro y hy h1
    have := hone y ((hφk y).1 h1) (by rw [hy])
    rw [this, orderOf_one] at hy
    omega
  have hsl2 : orderOf sl = 2 := by rw [hsl, Subgroup.orderOf_mk]; exact hs2
  have htl2 : orderOf tl = 2 := by rw [htl, Subgroup.orderOf_mk]; exact ht2
  have heq : φ sl = φ tl := by
    rcases KG531Red.sl2_center_cases (himg sl hsc) (himg tl htc) (hnot tl htl2) with h | h
    · exact absurd h (hnot sl hsl2)
    · exact h
  have hO : sl * tl⁻¹ ∈ pPrimeCore 2 ↥L₁ :=
    (hφk _).1 (by rw [map_mul, map_inv, heq, mul_inv_cancel])
  have hsq : (sl * tl⁻¹) ^ 2 = 1 := by
    have hc : Commute sl tl := (Subgroup.mem_center_iff.mp htc sl)
    have hs1 : sl ^ 2 = 1 := by rw [← hsl2]; exact pow_orderOf_eq_one sl
    have ht1 : tl ^ 2 = 1 := by rw [← htl2]; exact pow_orderOf_eq_one tl
    rw [(hc.inv_right).mul_pow, hs1, inv_pow, ht1, inv_one, one_mul]
  have h1 : sl * tl⁻¹ = 1 := hone _ hO (orderOf_dvd_of_pow_eq_one hsq)
  have hst : s = t := by
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, hsl, htl] at h2
    exact mul_inv_eq_one.1 h2
  apply htZ
  have : (⟨t, htM⟩ : ↥M) = z := Subtype.ext (by
    show t = (z : X)
    rw [← hst]
    exact hzs.symm)
  rw [this]
  exact hzZ

section Families

open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore in
theorem quasisimple_centralizer_mcl
    {S : Type} [Group S]
    (hSp : NativeSporadic.IsSporadic S .McL) {u : S} (hu : orderOf u = 2) :
    IsQuasisimple ↥(centralizer ({u} : Set S)) := by
  obtain ⟨e⟩ := hSp
  let e' : S ≃* ↥mclP := e.trans mclPermEquiv
  have hord : orderOf ((e' u : ↥mclP) : Equiv.Perm (Fin 275)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hu
  obtain ⟨g, hg, hgt⟩ := (mclT0_facts).2.2.2.2 _ (e' u).2 hord
  have hperf : Group.IsPerfect ↥mclCt := Subgroup.isPerfect_iff.2 CFSG.GH74.GLS.IVK.mclCt_perfect
  obtain ⟨hrange, -⟩ := mclRho_range
  obtain ⟨hs, hnab⟩ := mclX_simple
  have hs' : IsSimpleGroup mclRho.range := by rw [hrange]; exact hs
  have hn' : ∃ a b : mclRho.range, a * b ≠ b * a := by rw [hrange]; exact hnab
  have hq : IsQuasisimple ↥mclCt :=
    CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_of_perfect_cover hperf mclRho.rangeRestrict
      mclRho.rangeRestrict_surjective hs' hn'
      (by rw [MonoidHom.ker_rangeRestrict]; exact CFSG.GH74.GLS.IVK.mclRho_ker_le_center)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (CFSG.GH74.GLS.IVK.GHInv.centralizerEquivConj mclP e' u hg hgt).symm hq

open CFSG.Sporadic.Schreier CFSG.ClassicalInvolution CFSG.Sporadic.Ly in
theorem quasisimple_centralizer_ly
    {S : Type} [Group S] (hSL : NativeSporadic.IsSporadic S .Ly) {u : S} (hu : orderOf u = 2) :
    IsQuasisimple ↥(centralizer ({u} : Set S)) := by
  obtain ⟨hkey, hq, -, -⟩ := LyProof.K_facts
  obtain ⟨hSp, hidx⟩ := LyProof.S_sylow
  obtain ⟨-, hcover⟩ := LyProof.S_facts
  obtain ⟨e⟩ := hSL
  let e' : S ≃* ↥J := e.trans lyEquivJ
  have hord : orderOf (e' u) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hu
  have hSr : ∀ s ∈ LyProof.SJ, orderOf s = 2 →
      ∃ c ∈ (⊤ : Subgroup J), s = c * LyProof.zJ * c⁻¹ := by
    intro s hs hso
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hso, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hso
      exact absurd hso (by norm_num)
    obtain ⟨C, hC⟩ := hcover s hs hss hs1
    exact ⟨C, Subgroup.mem_top C, hC⟩
  obtain ⟨c, -, hc⟩ := cover_of_sylow (⊤ : Subgroup J) LyProof.SJ hSp hidx LyProof.zJ hSr (e' u)
    (Subgroup.mem_top _) hord
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv ?_
    (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.isQuasisimple_of_open' hq)
  refine MulEquiv.symm ?_
  exact (CFSG.GH74.GLS.IVK.GHInv.centralizerEquivConj
      (J : Subgroup (GL (Fin 111) (ZMod 5))) e' u
      (t := ((LyProof.zJ : J) : GL (Fin 111) (ZMod 5)))
      (g := (c : GL (Fin 111) (ZMod 5))) c.2 (by rw [hc]; simp)).trans
      ((CFSG.GH74.GLS.IVK.GHInv.centralizerSubtypeEquiv J LyProof.zJ).symm.trans
        (MulEquiv.subgroupCongr hkey))

end Families

section Proof


theorem kg531BPairOther_proved : KG531BPairOther := by
  intro X _ _ M hM hGH hodl hO t htM ht2 htZ L₁ L₂ h₁ h₂ s hsL₁ hs2 hsZ htL₂ F _ _ hodd h5 he₁ he₂
  obtain ⟨e₁⟩ := he₁
  obtain ⟨e₂⟩ := he₂
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup X := centralizer ({t} : Set X) ⊓ M with hK
  have hKM : K ≤ M := inf_le_right
  have hne : L₁ ≠ L₂ := ne_of_pair htM htZ h₁.1 hsL₁ hs2 hsZ htL₂ ht2 e₁
  set J₁ : Subgroup ↥K := L₁.subgroupOf K with hJ₁
  set J₂ : Subgroup ↥K := L₂.subgroupOf K with hJ₂
  have hJne : J₁ ≠ J₂ := by
    intro h
    apply hne
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_of_le_left h₁.1, inf_of_le_left h₂.1] at this
  have hsq := sq_card_sl2_dvd h₁.2 h₂.2 hJne hodd h5 (coreQuotEquiv h₁.1 e₁) (coreQuotEquiv h₂.1 e₂)
  have hJK : Nat.card ↥(J₁ ⊔ J₂) ∣ Nat.card ↥K := Subgroup.card_subgroup_dvd_card _
  obtain ⟨p, f, hp, hp2, hf, hqF, hq5⟩ := KG531Red.exists_prime_pow_card hodd h5
  have hSL : Nat.card SL(2, F) = p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hqF]
  have hDK : ∀ m : ℕ, Odd m → m ∣ p ^ f * ((p ^ f) ^ 2 - 1) → m ^ 2 ∣ Nat.card ↥K := by
    intro m hm hmd
    have h1 : m ^ 2 ∣ 2 * Nat.card ↥K :=
      (pow_dvd_pow_of_dvd (hSL ▸ hmd) 2).trans (hsq.trans (mul_dvd_mul_left 2 hJK))
    have hcop : Nat.Coprime (m ^ 2) 2 :=
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hm).symm
    exact hcop.dvd_of_dvd_mul_left h1
  set π : ↥M →* ↥M ⧸ center ↥M := QuotientGroup.mk' (center ↥M) with hπ
  set t' : ↥M := ⟨t, htM⟩ with ht'
  set κ : ↥K →* ↥M := Subgroup.inclusion hKM with hκdef
  have hrange : κ.range = centralizer ({t'} : Set ↥M) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).1
      simpa [ht', hκdef] using this
    · intro hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      refine ⟨⟨x, Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, x.2⟩⟩, rfl⟩
      simpa [ht'] using congrArg Subtype.val hx
  set ρ : ↥K →* ↥M ⧸ center ↥M := π.comp κ with hρ
  have hρker : ρ.ker ≤ center ↥K := by
    intro k hk
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hk
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subgroup.inclusion_injective hKM
    simpa using (Subgroup.mem_center_iff.mp hk (κ g))
  have hu1 : π t' ≠ 1 := by
    intro h
    exact htZ ((QuotientGroup.eq_one_iff _).1 h)
  have ht'2 : t' ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← ht2]
    exact pow_orderOf_eq_one t
  have hu2 : orderOf (π t') = 2 := by
    refine orderOf_eq_prime ?_ hu1
    rw [← map_pow, ht'2, map_one]
  have hDS : ∀ m : ℕ, Odd m → m ∣ p ^ f * ((p ^ f) ^ 2 - 1) →
      m ^ 2 ∣ Nat.card (↥M ⧸ center ↥M) := by
    intro m hm hmd
    have h1 : m ^ 2 ∣ Nat.card ↥M := (hDK m hm hmd).trans (Subgroup.card_dvd_of_le hKM)
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥M)] at h1
    exact (Nat.Coprime.pow_left 2 (coprime_card_center hO hm)).dvd_of_dvd_mul_right h1
  have hDC : ∀ m : ℕ, Odd m → m ∣ p ^ f * ((p ^ f) ^ 2 - 1) →
      m ^ 2 ∣ Nat.card ↥(centralizer ({π t'} : Set (↥M ⧸ center ↥M))) := by
    intro m hm hmd
    have h1 := hDK m hm hmd
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv] at h1
    have hk : Nat.card ↥ρ.ker ∣ Nat.card ↥(center ↥M) := by
      have hmap : ρ.ker.map κ ≤ center ↥M := by
        rintro _ ⟨k, hk, rfl⟩
        have hk' : ρ k = 1 := hk
        rw [hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hk'
        exact hk'
      rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKM)]
      exact Subgroup.card_dvd_of_le hmap
    have hcop : Nat.Coprime (m ^ 2) (Nat.card ↥ρ.ker) :=
      Nat.Coprime.coprime_dvd_right hk (Nat.Coprime.pow_left 2 (coprime_card_center hO hm))
    exact (hcop.dvd_of_dvd_mul_right h1).trans
      (Subgroup.card_dvd_of_le (KG531Red.range_le_centralizer κ hrange))
  have hord : ∀ {N : ℕ} (l : List ℕ), Nat.card (↥M ⧸ center ↥M) = N → l.prod = N →
      (∀ q ∈ l, q.Prime) → (∀ q ∈ l, 5 ≤ q → q ^ 2 ∣ N → ¬ 9 ∣ N) →
      (3 ^ 4 ∣ N → ¬ 25 ∣ N ∧ ¬ 3 ^ 6 ∣ N) → False := by
    intro N l hN hl hpr h5' h3'
    exact false_of_sq_dvd l hl hpr h5' h3' hp hp2 hf hq5 (fun m hm hmd => hN ▸ hDS m hm hmd)
  have hqC : IsQuasisimple ↥(centralizer ({π t'} : Set (↥M ⧸ center ↥M))) → False := by
    intro hq
    have himg : ∀ J : Subgroup ↥K, IsPComponent 2 J →
        J.map ρ = centralizer ({π t'} : Set (↥M ⧸ center ↥M)) := by
      intro J hJ
      obtain ⟨hle, hP⟩ := isPComponent_image κ hrange hJ (not_le_of_pComponent hJ hρker)
      have htop := eq_top_of_pComponent_quasisimple hq hP
      exact le_antisymm hle (Subgroup.subgroupOf_eq_top.1 htop)
    have h12 : J₁.map ρ ≤ J₂.map ρ := by rw [himg J₁ h₁.2, himg J₂ h₂.2]
    have : Group.IsPerfect ↥J₁ :=
      CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_perfect 2 J₁ h₁.2
    have hle : J₁ ≤ J₂ :=
      CFSG.ComponentClassification.CatalogueBCentralQuotient.perfect_le_of_map_le ρ hρker J₁ J₂ h12
    exact hJne ((CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      2 Nat.prime_two J₁ J₂ h₁.2 h₂.2).1 hle)
  rcases hGH with ⟨n, h7, h11, ⟨eA⟩⟩ | hspor | ⟨p', f', hp', hf', hlie⟩
  ·
    have hJ₂p : Group.IsPerfect ↥J₂ :=
      CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_perfect 2 J₂ h₂.2
    have hL₂p : Group.IsPerfect ↥L₂ :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe h₂.1).toMonoidHom)
        (MulEquiv.surjective _)
    have hL₂Mp : Group.IsPerfect ↥(L₂.subgroupOf M) :=
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe (h₂.1.trans hKM)).symm.toMonoidHom)
        (MulEquiv.surjective _)
    set P : Subgroup (alternatingGroup (Fin n)) :=
      ((L₂.subgroupOf M).map π).map eA.toMonoidHom with hP
    have hperf : Group.IsPerfect ↥P := by
      have : Group.IsPerfect ↥((L₂.subgroupOf M).map π) := Group.IsPerfect.map _
      exact Group.IsPerfect.map _
    have hx2 : eA (π t') * eA (π t') = 1 := by
      rw [← map_mul, ← map_mul, ← pow_two, ht'2, map_one, map_one]
    have hx1 : eA (π t') ≠ 1 := fun h => hu1 (eA.injective (by rw [h, map_one]))
    refine KG531Basic.alt_false h11 hx2 hx1 hperf ?_ ?_
    · rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      have hlt : (l : X) * t = t * l :=
        Subgroup.mem_centralizer_singleton_iff.1 (h₂.1 (Subgroup.mem_subgroupOf.1 hl)).1
      have hlt' : l * t' = t' * l := Subtype.ext hlt
      show eA (π l) * eA (π t') = eA (π t') * eA (π l)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hlt']
    · exact ⟨π t', ⟨t', Subgroup.mem_subgroupOf.2 htL₂, rfl⟩, rfl⟩
  · rcases hspor with hs | hs | hs | hs | hs | hs | hs | hs | hs
    · exact hord [2, 2, 2, 2, 3, 3, 5, 11]
        (CFSG.GH74.card_eq_of_isSporadic (s := .M11) CFSG.Sporadic.Mathieu.card_M11 hs)
        (by decide) (by decide) (by decide) (by decide)
    · exact hord (N := 95040) [2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 11]
        ((CFSG.GH74.card_of_isSporadic_M12 hs).trans (by norm_num))
        (by decide) (by decide) (by decide) (by decide)
    · exact hord (N := 443520) [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 11]
        ((CFSG.GH74.card_of_isSporadic_M22 hs).trans (by norm_num))
        (by decide) (by decide) (by decide) (by decide)
    · exact hord (N := 10200960) [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 11, 23]
        ((CFSG.GH74.card_of_isSporadic_M23 hs).trans (by norm_num))
        (by decide) (by decide) (by decide) (by decide)
    · exact hord (N := 175560) [2, 2, 2, 3, 5, 7, 11, 19]
        ((CFSG.GH74.card_of_isSporadic_J1 hs).trans (by norm_num))
        (by decide) (by decide) (by decide) (by decide)
    · rcases KG531Ord.card_centralizer_j2 hs hu2 with hc | hc
      · exact false_of_sq_dvd (N := 1920) [2, 2, 2, 2, 2, 2, 2, 3, 5] (by decide) (by decide) (by decide)
          (by decide) hp hp2 hf hq5 (fun m hm hmd => hc ▸ hDC m hm hmd)
      · exact false_of_sq_dvd (N := 240) [2, 2, 2, 2, 3, 5] (by decide) (by decide) (by decide)
          (by decide) hp hp2 hf hq5 (fun m hm hmd => hc ▸ hDC m hm hmd)
    · exact hord (N := 50232960) [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 17, 19]
        ((CFSG.GH74.card_of_isSporadic_J3 hs).trans (by norm_num))
        (by decide) (by decide) (by decide) (by decide)
    · exact hqC (quasisimple_centralizer_mcl hs hu2)
    · exact hqC (quasisimple_centralizer_ly hs hu2)
  · rcases hlie with h | h | h | h | h | h | ⟨-, hm⟩
    · exact hodl ⟨p', f', hp', hf', Or.inl h⟩
    · exact hodl ⟨p', f', hp', hf', Or.inr (Or.inl h)⟩
    · exact hodl ⟨p', f', hp', hf', Or.inr (Or.inr (Or.inl h))⟩
    · exact hodl ⟨p', f', hp', hf', Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact hodl ⟨p', f', hp', hf', Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
    · exact hodl ⟨p', f', hp', hf', Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
    · rcases hm with hm | hm | hm | hm | hm
      · exact hord (N := 504) [2, 2, 2, 3, 3, 7]
          ((CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hm).trans (by decide))
          (by decide) (by decide) (by decide) (by decide)
      · exact hord (N := 4080) [2, 2, 2, 2, 3, 5, 17]
          ((CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hm).trans (by decide))
          (by decide) (by decide) (by decide) (by decide)
      · exact hord (N := 20160) [2, 2, 2, 2, 2, 2, 3, 3, 5, 7]
          ((CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hm).trans (by decide))
          (by decide) (by decide) (by decide) (by decide)
      · have hc := CFSG.GH74.Generic.S1.kl5_card_mul_gcd_psu_three
          (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hm)
        exact hord (N := 62400) [2, 2, 2, 2, 2, 2, 3, 5, 5, 13] (by norm_num at hc; exact hc)
          (by decide) (by decide) (by decide) (by decide)
      · exact hord (N := 29120) [2, 2, 2, 2, 2, 2, 5, 7, 13]
          ((CFSG.GH74.card_of_lieModel_twistedB2 hm).trans (by decide))
          (by decide) (by decide) (by decide) (by decide)

end Proof

end KG531BP

end CFSG.GH74.Generic.BProg.B3
