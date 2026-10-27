module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoBasic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmRank1
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSPGroup
import CFSG.RankThree.PartOne.D4RC.Burnside

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNS

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

variable {Z : Type} [Group Z] [Finite Z] {p : ℕ}

theorem zpowers_eq_of_mem_of_ne_one {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {u v : X} (hv : orderOf v = p) (hu : u ∈ zpowers v) (hu1 : u ≠ 1) :
    zpowers u = zpowers v := by
  have hdvd : orderOf u ∣ p := hv ▸ orderOf_dvd_of_mem_zpowers hu
  have hne : orderOf u ≠ 1 := fun h1 => hu1 (orderOf_eq_one_iff.mp h1)
  have hou : orderOf u = p := ((Nat.dvd_prime hp).mp hdvd).resolve_left hne
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hu) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hou, hv]

theorem mem_normalizer_of_map_conj_le {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ normalizer (H : Set G) :=
  mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge h
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge)

theorem lines_aux {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) {x a z g : X}
    (hxo : orderOf x = p) (hao : orderOf a = p) (hzo : orderOf z = p) (hxa : x * a = a * x)
    (hzB : z ∈ zpowers x ⊔ zpowers a) (hgx : g * x * g⁻¹ = x)
    (hga : g * a * g⁻¹ ∈ zpowers a) (hne : g * a * g⁻¹ ≠ a)
    (hgz : g * z * g⁻¹ ∈ zpowers z) (hxz : x ∉ zpowers z) : z ∈ zpowers a := by
  have hcomm : ∀ s ∈ zpowers x, ∀ t ∈ zpowers a, s * t = t * s := by
    intro s hs t ht
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hs
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ht
    exact (Commute.zpow_zpow (show Commute x a from hxa) i j).eq
  obtain ⟨u, hu, v, hv, huv⟩ := SU1.mem_sup_of_commute hcomm hzB
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
  subst huv
  obtain ⟨a', ha'⟩ : ∃ a', a' = g * a * g⁻¹ := ⟨_, rfl⟩
  rw [← ha'] at hga hne
  obtain ⟨ε, hε⟩ : ∃ ε, ε = a' * a⁻¹ := ⟨_, rfl⟩
  have hεa : ε ∈ zpowers a := hε ▸ mul_mem hga (inv_mem (mem_zpowers a))
  have hε1 : ε ≠ 1 := fun h1 => hne (by rw [hε] at h1; exact mul_inv_eq_one.mp h1)
  have hεa' : a' = ε * a := by rw [hε]; group
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hεa
  have hεcomm : Commute ε a := by
    rw [← hm]
    exact (Commute.refl a).zpow_left m
  have hxε : Commute x ε := by
    rw [← hm]
    exact Commute.zpow_right (show Commute x a from hxa) m
  have e1 : g * (x ^ i * a ^ j) * g⁻¹ = x ^ i * (ε ^ j * a ^ j) := by
    have h1 : g * (x ^ i * a ^ j) * g⁻¹ = (g * x * g⁻¹) ^ i * (g * a * g⁻¹) ^ j := by
      rw [conj_zpow, conj_zpow]
      group
    rw [h1, hgx, ← ha', hεa', hεcomm.mul_zpow]
  have hc : g * (x ^ i * a ^ j) * g⁻¹ * (x ^ i * a ^ j)⁻¹ = ε ^ j := by
    rw [e1]
    have hcomm' : x ^ i * ε ^ j = ε ^ j * x ^ i := (Commute.zpow_zpow hxε i j).eq
    calc x ^ i * (ε ^ j * a ^ j) * (x ^ i * a ^ j)⁻¹
        = (x ^ i * ε ^ j) * (x ^ i)⁻¹ := by group
      _ = ε ^ j := by rw [hcomm']; group
  have hcz : ε ^ j ∈ zpowers (x ^ i * a ^ j) := by
    rw [← hc]
    exact mul_mem hgz (inv_mem (mem_zpowers _))
  have hca : ε ^ j ∈ zpowers a := Subgroup.zpow_mem _ hεa j
  by_contra hzA
  have hεj : ε ^ j = 1 := by
    by_contra hne1
    have h1 : zpowers (ε ^ j) = zpowers a := zpowers_eq_of_mem_of_ne_one hp hao hca hne1
    have h2 : zpowers (ε ^ j) = zpowers (x ^ i * a ^ j) :=
      zpowers_eq_of_mem_of_ne_one hp hzo hcz hne1
    apply hzA
    rw [← h1, h2]
    exact mem_zpowers _
  have hεo : orderOf ε = p := by
    have : zpowers ε = zpowers a := zpowers_eq_of_mem_of_ne_one hp hao hεa hε1
    rw [← Nat.card_zpowers, this, Nat.card_zpowers, hao]
  have hpj : (p : ℤ) ∣ j := by
    rw [← hεo]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hεj
  have haj : a ^ j = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hao]; exact hpj)
  rw [haj, mul_one] at hxz hzo
  have hz1 : x ^ i ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hzo
    exact hp.one_lt.ne hzo
  have hzx : zpowers (x ^ i) = zpowers x :=
    zpowers_eq_of_mem_of_ne_one hp hxo (Subgroup.zpow_mem _ (mem_zpowers x) i) hz1
  apply hxz
  rw [hzx]
  exact mem_zpowers x

structure AbSetup (p : ℕ) {Z : Type} [Group Z] [Finite Z] (S : Sylow p Z) (x z : Z) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  core : primeComplementCore (G := Z) p = ⊥
  abelian : ∀ a ∈ (S : Subgroup Z), ∀ b ∈ (S : Subgroup Z), a * b = b * a
  x_center : x ∈ center Z
  x_order : orderOf x = p
  x_mem : x ∈ (S : Subgroup Z)
  z_mem : z ∈ (S : Subgroup Z)
  z_order : orderOf z = p
  x_not_mem : x ∉ zpowers z
  omega : ∀ q ∈ (S : Subgroup Z), q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z

namespace AbSetup

variable {S : Sylow p Z} {x z : Z} (h : AbSetup p S x z)

include h

theorem x_pow : x ^ p = 1 := by
  rw [← h.x_order]
  exact pow_orderOf_eq_one x

theorem z_pow : z ^ p = 1 := by
  rw [← h.z_order]
  exact pow_orderOf_eq_one z

theorem commute_xz : x * z = z * x := (Subgroup.mem_center_iff.mp h.x_center z).symm

theorem x_ne_one : x ≠ 1 := by
  intro h1
  have := h.x_order
  rw [h1, orderOf_one] at this
  exact h.prime.one_lt.ne this

theorem z_not_mem : z ∉ zpowers x := by
  intro hz
  apply h.x_not_mem
  have heq : zpowers z = zpowers x := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, h.x_order, h.z_order])
  rw [heq]
  exact mem_zpowers x

theorem comm_zpowers : ∀ a ∈ zpowers x, ∀ b ∈ zpowers z, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
  exact ((Commute.zpow_zpow (show Commute x z from h.commute_xz) i j)).eq

theorem card_plane : Nat.card ↥(zpowers x ⊔ zpowers z) = p ^ 2 := by
  have hcomm : ∀ e ∈ zpowers x, e * z = z * e := fun e he => h.comm_zpowers e he z (mem_zpowers z)
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers h.prime (zpowers x) h.z_pow h.z_not_mem
    hcomm, Nat.card_zpowers, h.x_order, pow_two]

theorem plane_elem : IsElemAbelian p (zpowers x ⊔ zpowers z) :=
  SU1.IsElemAbelian.sup (SU1.isElemAbelian_zpowers h.x_pow) (SU1.isElemAbelian_zpowers h.z_pow)
    h.comm_zpowers

theorem plane_le : zpowers x ⊔ zpowers z ≤ (S : Subgroup Z) :=
  sup_le (zpowers_le.mpr h.x_mem) (zpowers_le.mpr h.z_mem)

theorem exists_sylow_component {K : Subgroup Z} (hK : IsComponentOf K ⊤) :
    ∃ P : Sylow p ↥K, (P : Subgroup ↥K).map K.subtype = (S : Subgroup Z) ⊓ K := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (CFSG.Open.IsSubnormal.top_iff.1 hK.2.1)

theorem comm_sylow_component {K : Subgroup Z} (P : Sylow p ↥K)
    (hP : (P : Subgroup ↥K).map K.subtype = (S : Subgroup Z) ⊓ K) :
    ∀ a ∈ (P : Subgroup ↥K), ∀ b ∈ (P : Subgroup ↥K), a * b = b * a := by
  intro a ha b hb
  have ha' : (a : Z) ∈ (S : Subgroup Z) ⊓ K := hP ▸ ⟨a, ha, rfl⟩
  have hb' : (b : Z) ∈ (S : Subgroup Z) ⊓ K := hP ▸ ⟨b, hb, rfl⟩
  exact Subtype.ext (h.abelian _ ha'.1 _ hb'.1)

theorem center_component_eq_bot {K : Subgroup Z} (hK : IsComponentOf K ⊤) :
    Subgroup.center ↥K = ⊥ := by
  by_contra hne
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (center ↥K) ≠ 1 := fun h1 => hne (Subgroup.card_eq_one.mp h1)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hcard
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center ↥K) q hqd
  set cK : ↥K := (c : ↥K) with hcK
  have hcc : ∀ g : ↥K, g * cK = cK * g := fun g => Subgroup.mem_center_iff.mp c.2 g
  have hcord : orderOf cK = q := (Subgroup.orderOf_coe c).trans hc
  have hsub : K.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hK.2.1
  have hZn : (zpowers cK).Normal := normal_zpowers_of_central hcc
  by_cases hqp : q = p
  · subst hqp
    obtain ⟨P, hP⟩ := h.exists_sylow_component hK
    have hpc : IsPGroup q (zpowers cK) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hcord, pow_one])
    have hle : zpowers cK ≤ CFSG.pCore q ↥K := le_sSup ⟨hZn, hpc⟩
    have hcP : cK ∈ (P : Subgroup ↥K) := P64Free.pCore_le_sylow P (hle (mem_zpowers cK))
    have hcomm' : cK ∈ commutator ↥K := by
      rw [hK.2.2.1]
      exact mem_top _
    have h1 : cK = 1 := transfer_center_commutator P.isPGroup' P.not_dvd_index
      (h.comm_sylow_component P hP) hcP c.2 hcomm'
    rw [h1, orderOf_one] at hcord
    exact hq.one_lt.ne hcord
  · set W : Subgroup Z := (zpowers cK).map K.subtype with hW
    have hWsub : W.IsSubnormal := by
      refine Subgroup.IsSubnormal.step W K (Subgroup.map_subtype_le _) hsub ?_
      have : W.subgroupOf K = zpowers cK :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
      rw [this]
      exact hZn
    have hWcard : Nat.card W = q := by
      rw [hW, Subgroup.card_map_of_injective K.subtype_injective, Nat.card_zpowers, hcord]
    have hle : W ≤ CFSG.pPrimeCore p Z :=
      CFSG.LocalAnalysis.RankThreeTheoremC.ths_le_pPrimeCore_of_isSubnormal hWsub
        (by rw [hWcard]; exact (Nat.coprime_primes hp hq).mpr fun h' => hqp h'.symm)
    have hcore : CFSG.pPrimeCore p Z = ⊥ := h.core
    rw [hcore, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hWcard
    exact hq.one_lt.ne hWcard

theorem isSimpleGroup_component {K : Subgroup Z} (hK : IsComponentOf K ⊤) :
    IsSimpleGroup ↥K ∧ ∃ a b : ↥K, a * b ≠ b * a :=
  isSimpleGroup_of_center_eq_bot hK (h.center_component_eq_bot hK)

theorem x_not_mem_component {K : Subgroup Z} (hK : IsComponentOf K ⊤) : x ∉ K := by
  intro hxK
  have hz : (⟨x, hxK⟩ : ↥K) ∈ center ↥K :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp h.x_center g)
  rw [h.center_component_eq_bot hK, Subgroup.mem_bot] at hz
  exact h.x_ne_one (congrArg Subtype.val hz)

theorem card_plane_inf_le {K : Subgroup Z} (hK : IsComponentOf K ⊤) :
    Nat.card ↥((zpowers x ⊔ zpowers z) ⊓ K) = 1 ∨
      Nat.card ↥((zpowers x ⊔ zpowers z) ⊓ K) = p := by
  have hp := h.prime
  have hdvd : Nat.card ↥((zpowers x ⊔ zpowers z) ⊓ K) ∣ p ^ 2 := by
    rw [← h.card_plane]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  interval_cases i
  · left
    simpa using hcard
  · right
    simpa using hcard
  · exfalso
    have heq : (zpowers x ⊔ zpowers z) ⊓ K = zpowers x ⊔ zpowers z :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [h.card_plane, hcard]))
    apply h.x_not_mem_component hK
    have : x ∈ (zpowers x ⊔ zpowers z) ⊓ K := by
      rw [heq]
      exact mem_sup_left (mem_zpowers x)
    exact this.2

theorem pRank_sylow_component_le_one {K : Subgroup Z} (hK : IsComponentOf K ⊤) (P : Sylow p ↥K)
    (hP : (P : Subgroup ↥K).map K.subtype = (S : Subgroup Z) ⊓ K) :
    Open.pRank p (P : Subgroup ↥K) ≤ 1 := by
  have hp := h.prime
  have h2 : Open.pRank p (P : Subgroup ↥K) = Open.pRank p ((S : Subgroup Z) ⊓ K) := by
    rw [← hP, pRank_map_subtype hp.one_lt]
  rw [h2]
  refine SU1.pRank_le_of fun E hEle hE k hk => ?_
  by_contra hk1
  push Not at hk1
  have hEB : E ≤ (zpowers x ⊔ zpowers z) ⊓ K := fun e he =>
    ⟨h.omega e (hEle he).1 ((SU1.isElemAbelian_iff.mp hE).2 e he), (hEle he).2⟩
  have hcard := Subgroup.card_le_of_le hEB
  rw [hk] at hcard
  have hpk : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk1
  have hp2 := hp.two_le
  rcases h.card_plane_inf_le hK with h1 | h1
  · rw [h1] at hcard
    have := Nat.one_lt_pow (by omega : k ≠ 0) hp.one_lt
    omega
  · rw [h1] at hcard
    nlinarith

theorem pRank_component_le_one {K : Subgroup Z} (hK : IsComponentOf K ⊤) :
    Open.pRank p K ≤ 1 := by
  have hp := h.prime
  obtain ⟨P, hP⟩ := h.exists_sylow_component hK
  have h1 : Open.pRank p K = Open.pRank p (⊤ : Subgroup ↥K) := by
    rw [← pRank_map_subtype hp.one_lt, Subgroup.map_top, Subgroup.range_subtype]
  rw [h1]
  exact (pRank_top_le_of_sylow hp P).trans (h.pRank_sylow_component_le_one hK P hP)

theorem isCyclic_sylow_component {K : Subgroup Z} (hK : IsComponentOf K ⊤) (P : Sylow p ↥K)
    (hP : (P : Subgroup ↥K).map K.subtype = (S : Subgroup Z) ⊓ K) :
    IsCyclic ↥(P : Subgroup ↥K) :=
  isCyclic_of_pRank_le_one h.prime h.ne_two P.isPGroup' (h.pRank_sylow_component_le_one hK P hP)

theorem z_mem_component {K : Subgroup Z} (hK : IsComponentOf K ⊤)
    (hNB : normalizer ((zpowers x ⊔ zpowers z : Subgroup Z) : Set Z) ≤
      normalizer ((zpowers z : Subgroup Z) : Set Z)) : z ∈ K := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := h.exists_sylow_component hK
  have hcyc := h.isCyclic_sylow_component hK P hP
  have hP1 : (P : Subgroup ↥K) ≠ ⊥ := fun h0 => P.not_dvd_index (by
    rw [h0, Subgroup.index_bot]
    exact dvd_card_of_isComponentOf hp h.core hK)
  have hperf : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := hK.2.2.1
  obtain ⟨g, hgN, a, haP, hap, hga⟩ :=
    CFSG.RankThree.PartOne.D4RC.rcb_exists_normalizer_elt_perfect hperf P.isPGroup'
      P.not_dvd_index hcyc hP1
  have haSK : (a : Z) ∈ (S : Subgroup Z) ⊓ K := hP ▸ ⟨a, haP, rfl⟩
  have hgaP : g * a * g⁻¹ ∈ (P : Subgroup ↥K) := (mem_normalizer_iff.mp hgN a).mp haP
  have hga' : (g : Z) * (a : Z) * (g : Z)⁻¹ ∈ (S : Subgroup Z) ⊓ K :=
    hP ▸ ⟨_, hgaP, rfl⟩
  have haz : (a : Z) ^ p = 1 := by simpa using congrArg Subtype.val hap
  have hgaz : ((g : Z) * (a : Z) * (g : Z)⁻¹) ^ p = 1 := by
    rw [conj_pow, haz]
    simp
  have hne : (g : Z) * (a : Z) * (g : Z)⁻¹ ≠ (a : Z) := fun h' => hga (Subtype.ext h')
  have ha1 : (a : Z) ≠ 1 := fun h1 => hne (by rw [h1]; simp)
  have hao : orderOf (a : Z) = p := orderOf_eq_prime haz ha1
  have haB : (a : Z) ∈ zpowers x ⊔ zpowers z := h.omega _ haSK.1 haz
  have haK : (a : Z) ∈ K := a.2
  have hcardBK : Nat.card ↥((zpowers x ⊔ zpowers z) ⊓ K) = p := by
    rcases h.card_plane_inf_le hK with h1 | h1
    · exfalso
      have := Subgroup.card_le_of_le (show zpowers (a : Z) ≤ (zpowers x ⊔ zpowers z) ⊓ K from
        zpowers_le.mpr ⟨haB, haK⟩)
      rw [Nat.card_zpowers, hao, h1] at this
      exact absurd hp.one_lt (not_lt.mpr this)
    · exact h1
  have hzBK : zpowers (a : Z) = (zpowers x ⊔ zpowers z) ⊓ K :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ⟨haB, haK⟩)
      (by rw [hcardBK, Nat.card_zpowers, hao])
  have hgaB : (g : Z) * (a : Z) * (g : Z)⁻¹ ∈ zpowers (a : Z) := by
    rw [hzBK]
    exact ⟨h.omega _ hga'.1 hgaz, hga'.2⟩
  have hxa : x * (a : Z) = (a : Z) * x := (Subgroup.mem_center_iff.mp h.x_center a).symm
  have hgx : (g : Z) * x * (g : Z)⁻¹ = x :=
    mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_center_iff.mp h.x_center g)
  have ha_not : (a : Z) ∉ zpowers x := by
    intro hmem
    have heq : zpowers (a : Z) = zpowers x :=
      zpowers_eq_of_mem_of_ne_one hp h.x_order hmem ha1
    apply h.x_not_mem_component hK
    have hxa' : x ∈ zpowers (a : Z) := by
      rw [heq]
      exact mem_zpowers x
    exact (zpowers_le.mpr haK) hxa'
  have hcomm : ∀ e ∈ zpowers x, e * (a : Z) = (a : Z) * e := by
    intro e he
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left (show Commute x (a : Z) from hxa) k).eq
  have hBeq : zpowers x ⊔ zpowers (a : Z) = zpowers x ⊔ zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left (zpowers_le.mpr haB)) ?_
    rw [h.card_plane, CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers x) haz ha_not
      hcomm, Nat.card_zpowers, h.x_order, pow_two]
  have hgB : (g : Z) ∈ normalizer ((zpowers x ⊔ zpowers z : Subgroup Z) : Set Z) := by
    refine mem_normalizer_of_map_conj_le ?_
    rw [← hBeq, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · have : (MulAut.conj (g : Z)).toMonoidHom x = x := hgx
      rw [this]
      exact mem_sup_left (mem_zpowers x)
    · have : (MulAut.conj (g : Z)).toMonoidHom (a : Z) ∈ zpowers (a : Z) := hgaB
      exact mem_sup_right this
  have hgz : (g : Z) * z * (g : Z)⁻¹ ∈ zpowers z :=
    (mem_normalizer_iff.mp (hNB hgB) z).mp (mem_zpowers z)
  have hzB : z ∈ zpowers x ⊔ zpowers (a : Z) := by
    rw [hBeq]
    exact mem_sup_right (mem_zpowers z)
  exact (zpowers_le.mpr haK)
    (lines_aux hp h.x_order hao h.z_order hxa hzB hgx hgaB hne hgz h.x_not_mem)

theorem not_isCyclic_sylow : ¬ IsCyclic (S : Subgroup Z) := by
  intro hcyc
  have hp := h.prime
  have hBS := h.plane_le
  haveI : IsCyclic ↥((zpowers x ⊔ zpowers z).subgroupOf (S : Subgroup Z)) := inferInstance
  haveI : IsCyclic ↥(zpowers x ⊔ zpowers z) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hBS).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hBS).surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(zpowers x ⊔ zpowers z))
  have hord : orderOf g = p ^ 2 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, h.card_plane]
  have hgp : g ^ p = 1 :=
    Subtype.ext (by simpa using (SU1.isElemAbelian_iff.mp h.plane_elem).2 g.1 g.2)
  have hdvd : p ^ 2 ∣ p := hord ▸ orderOf_dvd_of_pow_eq_one hgp
  have := Nat.le_of_dvd hp.pos hdvd
  nlinarith [hp.two_le]

theorem exists_uncovered_component {Mb : Subgroup Z} (hSM : (S : Subgroup Z) ≤ Mb)
    (hΓ2 : ∀ T : Subgroup Z, T ≤ S → 2 ≤ Open.pRank p T → normalizer (T : Set Z) ≤ Mb)
    (hMtop : ¬ ⊤ ≤ Mb) : ∃ K : Subgroup Z, IsComponentOf K ⊤ ∧ ¬ K ≤ Mb := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨L₀, hL₀⟩ :=
    exists_isComponentOf_Z hp h.ne_two h.core S h.not_isCyclic_sylow hSM hΓ2 hMtop
  by_contra hcon
  push Not at hcon
  set N : Subgroup Z := sSup {K : Subgroup Z | IsComponentOf K ⊤} ⊔ zpowers x with hN
  have hNM : N ≤ Mb := sup_le (sSup_le fun K hK => hcon K hK) (zpowers_le.mpr (hSM h.x_mem))
  haveI hnl : (sSup {K : Subgroup Z | IsComponentOf K ⊤}).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : sSup {K : Subgroup Z | IsComponentOf K ⊤} ≤
        (sSup {K : Subgroup Z | IsComponentOf K ⊤}).comap (MulAut.conj g).toMonoidHom := by
      refine sSup_le fun M hM => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup (isComponentOf_map_conj hM g)
    exact hle hn
  haveI hzn : (zpowers x).Normal :=
    normal_zpowers_of_central fun g => Subgroup.mem_center_iff.mp h.x_center g
  haveI hNn : N.Normal := inferInstance
  obtain ⟨y, hyQK, hyo, hyc⟩ := exists_mem_inf_sylow_component hp h.ne_two h.core S hL₀
  have hyp : y ^ p = 1 := by
    rw [← hyo]
    exact pow_orderOf_eq_one y
  have hyx : y ∉ zpowers x := by
    intro hy
    obtain ⟨l, -, hne⟩ := hyc
    apply hne
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute l x from Subgroup.mem_center_iff.mp h.x_center l)
      k).eq
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers hp h.x_pow hyp h.x_ne_one hyx
    (h.abelian x h.x_mem y hyQK.1)
  have hle : zpowers x ⊔ zpowers y ≤ (S : Subgroup Z) ⊓ N :=
    sup_le (zpowers_le.mpr ⟨h.x_mem, mem_sup_right (mem_zpowers x)⟩)
      (zpowers_le.mpr ⟨hyQK.1, mem_sup_left ((le_sSup hL₀ : L₀ ≤ _) hyQK.2)⟩)
  have h2 : 2 ≤ Open.pRank p ((S : Subgroup Z) ⊓ N) := SU1.le_pRank hp.one_lt hle hel hcard
  exact hMtop (top_le_of_normal hp S hNM h2 hΓ2)

theorem exists_component {Mb : Subgroup Z} (hSM : (S : Subgroup Z) ≤ Mb)
    (hΓ2 : ∀ T : Subgroup Z, T ≤ S → 2 ≤ Open.pRank p T → normalizer (T : Set Z) ≤ Mb)
    (hNz : normalizer (zpowers z : Set Z) ≤ Mb)
    (hNB : normalizer ((zpowers x ⊔ zpowers z : Subgroup Z) : Set Z) ≤
      normalizer ((zpowers z : Subgroup Z) : Set Z))
    (hMtop : ¬ ⊤ ≤ Mb) :
    ∃ K : Subgroup Z, IsComponentOf K ⊤ ∧ IsSimpleGroup ↥K ∧ (∃ a b : ↥K, a * b ≠ b * a) ∧
      z ∈ K ∧ Open.pRank p K ≤ 1 ∧ ¬ K ≤ Mb ∧ Mb ≤ normalizer (K : Set Z) := by
  obtain ⟨K, hK, hKM⟩ := h.exists_uncovered_component hSM hΓ2 hMtop
  have hzK := h.z_mem_component hK hNB
  have hother : ∀ K' : Subgroup Z, IsComponentOf K' ⊤ → K' ≠ K → K' ≤ Mb := by
    intro K' hK' hne m hm
    exact hNz (P64Free.mem_normalizer_zpowers_of_commute (component_commute hK' hK hne hm hzK))
  refine ⟨K, hK, (h.isSimpleGroup_component hK).1, (h.isSimpleGroup_component hK).2, hzK,
    h.pRank_component_le_one hK, hKM, fun m hm => ?_⟩
  by_cases hKm : K.map (MulAut.conj m).toMonoidHom = K
  · exact (map_conj_eq_self_iff m K).1 hKm
  · exfalso
    apply hKM
    intro k hk
    have hK' : IsComponentOf (K.map (MulAut.conj m).toMonoidHom) ⊤ := isComponentOf_map_conj hK m
    have hmem : m * k * m⁻¹ ∈ K.map (MulAut.conj m).toMonoidHom := ⟨k, hk, by simp⟩
    have h1 := hother _ hK' hKm hmem
    have e : k = m⁻¹ * (m * k * m⁻¹) * m := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hm) h1) hm

end AbSetup

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNS
