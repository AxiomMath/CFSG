module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSZ
public import CFSG.Walter.Cited.Huppert
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64ii

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

variable {Z : Type} [Group Z] [Finite Z] {p : ℕ}

@[expose] def conjAut {Z : Type} [Group Z] (K : Subgroup Z) (y : Z)
    (hy : y ∈ normalizer (K : Set Z)) : MulAut ↥K where
  toFun g := ⟨y * g * y⁻¹, (mem_normalizer_iff.mp hy g).mp g.2⟩
  invFun g := ⟨y⁻¹ * g * y, by
    have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) g).mp g.2
    simpa using this⟩
  left_inv g := by
    ext
    simp [mul_assoc]
  right_inv g := by
    ext
    simp [mul_assoc]
  map_mul' a b := by
    ext
    simp [mul_assoc]

theorem conjAut_apply {Z : Type} [Group Z] (K : Subgroup Z) (y : Z)
    (hy : y ∈ normalizer (K : Set Z)) (g : ↥K) :
    ((conjAut K y hy g : ↥K) : Z) = y * g * y⁻¹ := rfl

theorem conjAut_pow {Z : Type} [Group Z] (K : Subgroup Z) (y : Z)
    (hy : y ∈ normalizer (K : Set Z)) (n : ℕ) (g : ↥K) :
    ((((conjAut K y hy) ^ n) g : ↥K) : Z) = y ^ n * g * (y ^ n)⁻¹ := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, conjAut_apply]
    simp [pow_succ, mul_assoc]

@[expose] def OuterAction (p : ℕ) {Z : Type} [Group Z] (K : Subgroup Z) (y : Z) : Prop :=
  ∃ hy : y ∈ normalizer (K : Set Z), orderOf (conjAut K y hy) = p ∧
    conjAut K y hy ∉ (MulAut.conj : ↥K →* MulAut ↥K).range

theorem transvection_aux {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {a y z r c : X} (hao : orderOf a = p) (hyo : orderOf y = p) (hzo : orderOf z = p)
    (hay : a * y = y * a) (hzB : z ∈ zpowers a ⊔ zpowers y) (hra : r * a * r⁻¹ = a)
    (hry : r * y * r⁻¹ = c * y) (hc : c ∈ zpowers a) (hc1 : c ≠ 1)
    (hrz : r * z * r⁻¹ ∈ zpowers z) : z ∈ zpowers a := by
  have hcomm : ∀ s ∈ zpowers a, ∀ t ∈ zpowers y, s * t = t * s := by
    intro s hs t ht
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hs
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ht
    exact (Commute.zpow_zpow (show Commute a y from hay) i j).eq
  have hcyc : zpowers c = zpowers a := L6LeavesNS.zpowers_eq_of_mem_of_ne_one hp hao hc hc1
  have hco : orderOf c = p := by
    rw [← Nat.card_zpowers, hcyc, Nat.card_zpowers, hao]
  obtain ⟨u, hu, v, hv, huv⟩ := SU1.mem_sup_of_commute hcomm hzB
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
  subst huv
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hc
  have hca : Commute a c := by
    rw [← hm]
    exact (Commute.refl a).zpow_right m
  have hcy : Commute c y := by
    rw [← hm]
    exact Commute.zpow_left (show Commute a y from hay) m
  have e1 : r * (a ^ i * y ^ j) * r⁻¹ = c ^ j * (a ^ i * y ^ j) := by
    have h1 : r * (a ^ i * y ^ j) * r⁻¹ = (r * a * r⁻¹) ^ i * (r * y * r⁻¹) ^ j := by
      rw [conj_zpow, conj_zpow]
      group
    rw [h1, hra, hry, hcy.mul_zpow]
    have h2 : Commute (a ^ i) (c ^ j) := (hca.zpow_zpow i j)
    calc a ^ i * (c ^ j * y ^ j) = (a ^ i * c ^ j) * y ^ j := by rw [mul_assoc]
      _ = (c ^ j * a ^ i) * y ^ j := by rw [h2.eq]
      _ = c ^ j * (a ^ i * y ^ j) := by rw [mul_assoc]
  have hcj : c ^ j ∈ zpowers (a ^ i * y ^ j) := by
    have h3 : c ^ j * (a ^ i * y ^ j) ∈ zpowers (a ^ i * y ^ j) := by rw [← e1]; exact hrz
    have h4 := mul_mem h3 (inv_mem (mem_zpowers (a ^ i * y ^ j)))
    have e : c ^ j * (a ^ i * y ^ j) * (a ^ i * y ^ j)⁻¹ = c ^ j := by group
    rwa [e] at h4
  have hcja : c ^ j ∈ zpowers a := Subgroup.zpow_mem _ hc j
  by_cases hcj1 : c ^ j = 1
  · have hpj : (p : ℤ) ∣ j := by
      rw [← hco]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hcj1
    have hyj : y ^ j = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hyo]; exact hpj)
    rw [hyj, mul_one]
    exact Subgroup.zpow_mem _ (mem_zpowers a) i
  · have h5 : zpowers (c ^ j) = zpowers a := L6LeavesNS.zpowers_eq_of_mem_of_ne_one hp hao hcja hcj1
    have h6 : zpowers (c ^ j) = zpowers (a ^ i * y ^ j) :=
      L6LeavesNS.zpowers_eq_of_mem_of_ne_one hp hzo hcj hcj1
    rw [← h5, h6]
    exact mem_zpowers _

structure Ctx (p : ℕ) {Z : Type} [Group Z] [Finite Z] (S : Sylow p Z) (x z : Z)
    (M : Subgroup Z) : Prop where
  prime : p.Prime
  three_le : 3 ≤ p
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections Z
  core : primeComplementCore (G := Z) p = ⊥
  x_order : orderOf x = p
  z_order : orderOf z = p
  commute : x * z = z * x
  x_not_mem : x ∉ zpowers z
  x_mem : x ∈ (S : Subgroup Z)
  z_mem : z ∈ (S : Subgroup Z)
  omega : ∀ q ∈ (S : Subgroup Z), q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z
  metacyclic : CFSG.IsMetacyclic ↥(S : Subgroup Z)
  S_le : (S : Subgroup Z) ≤ M
  gamma : ∀ T : Subgroup Z, T ≤ S → 2 ≤ Open.pRank p T → normalizer (T : Set Z) ≤ M
  Nz : normalizer (zpowers z : Set Z) ≤ M
  NB : normalizer ((zpowers x ⊔ zpowers z : Subgroup Z) : Set Z) ≤
    normalizer ((zpowers z : Subgroup Z) : Set Z)
  not_top : ¬ ⊤ ≤ M

namespace Ctx

variable {S : Sylow p Z} {x z : Z} {M : Subgroup Z} (h : Ctx p S x z M)

include h

theorem ne_two : p ≠ 2 := by
  have := h.three_le
  omega

theorem x_pow : x ^ p = 1 := by
  rw [← h.x_order]
  exact pow_orderOf_eq_one x

theorem z_pow : z ^ p = 1 := by
  rw [← h.z_order]
  exact pow_orderOf_eq_one z

theorem x_ne_one : x ≠ 1 := by
  intro h1
  have := h.x_order
  rw [h1, orderOf_one] at this
  exact h.prime.one_lt.ne this

theorem z_ne_one : z ≠ 1 := by
  intro h1
  have := h.z_order
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
  exact ((Commute.zpow_zpow (show Commute x z from h.commute) i j)).eq

theorem card_plane : Nat.card ↥(zpowers x ⊔ zpowers z) = p ^ 2 := by
  have hcomm : ∀ e ∈ zpowers x, e * z = z * e := fun e he => h.comm_zpowers e he z (mem_zpowers z)
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers h.prime (zpowers x) h.z_pow h.z_not_mem
    hcomm, Nat.card_zpowers, h.x_order, pow_two]

theorem plane_elem : IsElemAbelian p (zpowers x ⊔ zpowers z) :=
  SU1.IsElemAbelian.sup (SU1.isElemAbelian_zpowers h.x_pow) (SU1.isElemAbelian_zpowers h.z_pow)
    h.comm_zpowers

theorem plane_le : zpowers x ⊔ zpowers z ≤ (S : Subgroup Z) :=
  sup_le (zpowers_le.mpr h.x_mem) (zpowers_le.mpr h.z_mem)

theorem plane_comm : ∀ a ∈ zpowers x ⊔ zpowers z, ∀ b ∈ zpowers x ⊔ zpowers z, a * b = b * a :=
  (SU1.isElemAbelian_iff.mp h.plane_elem).1

theorem plane_pow : ∀ a ∈ zpowers x ⊔ zpowers z, a ^ p = 1 :=
  (SU1.isElemAbelian_iff.mp h.plane_elem).2

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

theorem exists_sylow_component {K : Subgroup Z} (hK : IsComponentOf K ⊤) :
    ∃ P : Sylow p ↥K, (P : Subgroup ↥K).map K.subtype = (S : Subgroup Z) ⊓ K := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (CFSG.Open.IsSubnormal.top_iff.1 hK.2.1)

theorem abelian_sylow_component {K : Subgroup Z} (hK : IsComponentOf K ⊤) (P : Sylow p ↥K)
    (hP : (P : Subgroup ↥K).map K.subtype = (S : Subgroup Z) ⊓ K) :
    ∀ a ∈ (P : Subgroup ↥K), ∀ b ∈ (P : Subgroup ↥K), a * b = b * a := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, b, hb, hab⟩ := hcon
  have hnab : ¬ IsMulCommutative (P : Subgroup ↥K) := fun hc =>
    hab (congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hle : (P : Subgroup ↥K).map K.subtype ≤ (S : Subgroup Z) := hP ▸ inf_le_left
  have hmeta1 : CFSG.IsMetacyclic ↥((P : Subgroup ↥K).map K.subtype) :=
    CFSG.Walter.Huppert.isMetacyclic_of_le hle h.metacyclic
  have hmeta : CFSG.IsMetacyclic ↥(P : Subgroup ↥K) :=
    CFSG.Walter.Huppert.isMetacyclic_of_mulEquiv
      ((P : Subgroup ↥K).equivMapOfInjective K.subtype K.subtype_injective).symm hmeta1
  obtain ⟨N, hN, hNtop, hNp⟩ :=
    CFSG.Walter.huppertMetacyclicTheorem ↥K p h.ne_two P hnab hmeta
  haveI : N.Normal := hN
  haveI : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
  haveI : Nontrivial (↥K ⧸ N) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    exact hNtop ((QuotientGroup.subsingleton_iff (N := N)).1 hs)
  haveI : Fact (IsPGroup p (↥K ⧸ N)) := ⟨hNp⟩
  exact Group.IsPerfect.not_isNilpotent (↥K ⧸ N) hNp.isNilpotent

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
  have hZn : (zpowers cK).Normal := L6LeavesNS.normal_zpowers_of_central hcc
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
    have h1 : cK = 1 := L6LeavesNS.transfer_center_commutator P.isPGroup' P.not_dvd_index
      (h.abelian_sylow_component hK P hP) hcP c.2 hcomm'
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

theorem isCatalog_component {K : Subgroup Z} (hK : IsComponentOf K ⊤) : IsCatalogGroup ↥K :=
  h.catalog.simple_subgroup K (h.isSimpleGroup_component hK).1 (h.isSimpleGroup_component hK).2

theorem pRank_sylow_component_le_one (hI121 : KFact64iiI121) {K : Subgroup Z}
    (hK : IsComponentOf K ⊤) (P : Sylow p ↥K)
    (hP : (P : Subgroup ↥K).map K.subtype = (S : Subgroup Z) ⊓ K) :
    Open.pRank p (P : Subgroup ↥K) ≤ 1 := by
  by_contra hrk
  push Not at hrk
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have habel := h.abelian_sylow_component hK P hP
  obtain ⟨hs1, hs2⟩ := h.isSimpleGroup_component hK
  have hcat := h.isCatalog_component hK
  obtain ⟨E, hEP, hE, hEc⟩ := SU1.exists_isElemAbelian_of_le_pRank hp (k := 2) hrk
  set E' : Subgroup Z := E.map K.subtype with hE'
  have hE'S : E' ≤ (S : Subgroup Z) ⊓ K := hP ▸ Subgroup.map_mono hEP
  have hE'B : E' ≤ zpowers x ⊔ zpowers z := by
    rintro _ ⟨e, he, rfl⟩
    refine h.omega _ (hE'S ⟨e, he, rfl⟩).1 ?_
    have := (SU1.isElemAbelian_iff.mp hE).2 e he
    have h2 := congrArg Subtype.val this
    simpa using h2
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective K.subtype_injective, hEc]
  have hE'eq : E' = zpowers x ⊔ zpowers z :=
    Subgroup.eq_of_le_of_card_ge hE'B (by rw [hE'c, h.card_plane])
  have hBSK : zpowers x ⊔ zpowers z ≤ (S : Subgroup Z) ⊓ K := hE'eq ▸ hE'S
  have hzK : zpowers z ≤ K := (zpowers_le.mpr (hBSK (mem_sup_right (mem_zpowers z))).2)
  set A : Subgroup ↥K := (zpowers z).subgroupOf K with hA
  have hAc : Nat.card A = p := by
    rw [hA, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzK).toEquiv, Nat.card_zpowers,
      h.z_order]
  have hAP : A ≤ (P : Subgroup ↥K) := by
    intro g hg
    have hgB : (g : Z) ∈ (S : Subgroup Z) ⊓ K :=
      hBSK (mem_sup_right (Subgroup.mem_subgroupOf.mp hg))
    rw [← hP] at hgB
    obtain ⟨g', hg'P, hg'⟩ := hgB
    have : g' = g := Subtype.ext hg'
    rw [← this]
    exact hg'P
  have hcomm : IsMulCommutative (P : Subgroup ↥K) :=
    ⟨⟨fun a b => Subtype.ext (habel a.1 a.2 b.1 b.2)⟩⟩
  refine hI121 p hp h.three_le K hs1 hs2 hcat P hcomm hrk A hAP hAc ?_
  intro n hn
  have hnB : (n : Z) ∈ normalizer ((zpowers x ⊔ zpowers z : Subgroup Z) : Set Z) := by
    refine L6LeavesNS.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨b, hb, rfl⟩
    have hbPK : b ∈ (S : Subgroup Z) ⊓ K := hBSK hb
    rw [← hP] at hbPK
    obtain ⟨b', hb'P, rfl⟩ := hbPK
    have hnb' : n * b' * n⁻¹ ∈ (P : Subgroup ↥K) := (mem_normalizer_iff.mp hn b').mp hb'P
    have hS1 : ((n * b' * n⁻¹ : ↥K) : Z) ∈ (S : Subgroup Z) ⊓ K := by
      rw [← hP]
      exact ⟨_, hnb', rfl⟩
    have hpow : (((n * b' * n⁻¹ : ↥K) : Z)) ^ p = 1 := by
      have h1 : ((b' : ↥K) : Z) ^ p = 1 := h.plane_pow _ hb
      have h2 : (((n * b' * n⁻¹ : ↥K) : Z)) = (n : Z) * (b' : Z) * (n : Z)⁻¹ := by simp
      rw [h2, conj_pow, h1]
      simp
    have := h.omega _ hS1.1 hpow
    simpa using this
  have hnz : (n : Z) ∈ normalizer ((zpowers z : Subgroup Z) : Set Z) := h.NB hnB
  rw [mem_normalizer_iff]
  intro g
  rw [hA, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using (mem_normalizer_iff.mp hnz (g : Z))

theorem isCyclic_sylow_component (hI121 : KFact64iiI121) {K : Subgroup Z}
    (hK : IsComponentOf K ⊤) (P : Sylow p ↥K)
    (hP : (P : Subgroup ↥K).map K.subtype = (S : Subgroup Z) ⊓ K) :
    IsCyclic ↥(P : Subgroup ↥K) :=
  P64Asm.isCyclic_of_pRank_le_one h.prime h.ne_two P.isPGroup'
    (h.pRank_sylow_component_le_one hI121 hK P hP)

theorem pRank_component_le_one (hI121 : KFact64iiI121) {K : Subgroup Z}
    (hK : IsComponentOf K ⊤) : Open.pRank p K ≤ 1 := by
  have hp := h.prime
  obtain ⟨P, hP⟩ := h.exists_sylow_component hK
  have h1 : Open.pRank p K = Open.pRank p (⊤ : Subgroup ↥K) := by
    rw [← pRank_map_subtype hp.one_lt, Subgroup.map_top, Subgroup.range_subtype]
  rw [h1]
  exact (pRank_top_le_of_sylow hp P).trans (h.pRank_sylow_component_le_one hI121 hK P hP)

theorem not_plane_le (hI121 : KFact64iiI121) {K : Subgroup Z} (hK : IsComponentOf K ⊤) :
    ¬ zpowers x ⊔ zpowers z ≤ K := by
  intro hBK
  have hp := h.prime
  have hrk := h.pRank_component_le_one hI121 hK
  have h2 : 2 ≤ Open.pRank p K :=
    SU1.le_pRank hp.one_lt hBK h.plane_elem (k := 2) h.card_plane
  omega

theorem S_le_normalizer_plane : (S : Subgroup Z) ≤ normalizer ((zpowers x ⊔ zpowers z :
    Subgroup Z) : Set Z) := by
  intro s hs
  refine L6LeavesNS.mem_normalizer_of_map_conj_le ?_
  rintro _ ⟨b, hb, rfl⟩
  refine h.omega _ ?_ ?_
  · exact (S : Subgroup Z).mul_mem ((S : Subgroup Z).mul_mem hs (h.plane_le hb))
      ((S : Subgroup Z).inv_mem hs)
  · have h1 := h.plane_pow b hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, h1]
    simp

theorem exists_inf_plane (hI121 : KFact64iiI121) {K : Subgroup Z} (hK : IsComponentOf K ⊤) :
    ∃ a : Z, a ∈ K ∧ a ∈ (S : Subgroup Z) ∧ orderOf a = p ∧
      (zpowers x ⊔ zpowers z) ⊓ K = zpowers a := by
  have hp := h.prime
  obtain ⟨y, hyS, hyo, -⟩ := exists_mem_inf_sylow_component hp h.ne_two h.core S hK
  have hyp : y ^ p = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hyo] at this
  have hyB : y ∈ zpowers x ⊔ zpowers z := h.omega y hyS.1 hyp
  have hle : zpowers y ≤ (zpowers x ⊔ zpowers z) ⊓ K := zpowers_le.mpr ⟨hyB, hyS.2⟩
  have hcard1 : Nat.card ↥(zpowers y) = p := by rw [Nat.card_zpowers, hyo]
  have hdvd : Nat.card ↥((zpowers x ⊔ zpowers z) ⊓ K) ∣ p ^ 2 := by
    rw [← h.card_plane]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hci2 : i ≠ 2 := by
    rintro rfl
    apply h.not_plane_le hI121 hK
    have : (zpowers x ⊔ zpowers z) ⊓ K = zpowers x ⊔ zpowers z :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hci, h.card_plane])
    rw [← this]
    exact inf_le_right
  have h1 := Subgroup.card_le_of_le hle
  rw [hcard1, hci] at h1
  have hi1 : 1 ≤ i := by
    by_contra h0
    have : i = 0 := by omega
    rw [this, pow_zero] at h1
    have := hp.one_lt
    omega
  have hi1' : i = 1 := by omega
  refine ⟨y, hyS.2, hyS.1, hyo, (Subgroup.eq_of_le_of_card_ge hle ?_).symm⟩
  rw [hcard1, hci, hi1', pow_one]

theorem plane_le_normalizer (hI121 : KFact64iiI121) {K : Subgroup Z} (hK : IsComponentOf K ⊤) :
    zpowers x ⊔ zpowers z ≤ normalizer (K : Set Z) := by
  intro b hb
  have hp := h.prime
  obtain ⟨a, haK, haS, hao, hBK⟩ := h.exists_inf_plane hI121 hK
  have haB : a ∈ (zpowers x ⊔ zpowers z) ⊓ K := hBK ▸ mem_zpowers a
  rw [← map_conj_eq_self_iff]
  by_contra hne
  have hK' := isComponentOf_map_conj hK b
  have hba : b * a * b⁻¹ = a := mul_inv_eq_iff_eq_mul.mpr (h.plane_comm b hb a haB.1)
  have ha' : a ∈ K.map (MulAut.conj b).toMonoidHom := ⟨a, haB.2, by simpa using hba⟩
  have hcen : (⟨a, haB.2⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (component_commute hK hK' (fun h' => hne h'.symm) g.2 ha')
  rw [h.center_component_eq_bot hK, Subgroup.mem_bot] at hcen
  have : a = 1 := congrArg Subtype.val hcen
  rw [this, orderOf_one] at hao
  exact hp.one_lt.ne hao

theorem pRank_top_component (hI121 : KFact64iiI121) {K : Subgroup Z} (hK : IsComponentOf K ⊤) :
    Open.pRank p (⊤ : Subgroup ↥K) = 1 := by
  have hp := h.prime
  have h1 : Open.pRank p K = Open.pRank p (⊤ : Subgroup ↥K) := by
    rw [← pRank_map_subtype hp.one_lt, Subgroup.map_top, Subgroup.range_subtype]
  rw [← h1]
  refine le_antisymm (h.pRank_component_le_one hI121 hK) ?_
  obtain ⟨a, haK, haS, hao, -⟩ := h.exists_inf_plane hI121 hK
  have hap : a ^ p = 1 := by
    have := pow_orderOf_eq_one a
    rwa [hao] at this
  have hzK : zpowers a ≤ K := zpowers_le.mpr haK
  have hel : IsElemAbelian p ((zpowers a).subgroupOf K) :=
    CFSG.Open.IsElemAbelian.subgroupOf (SU1.isElemAbelian_zpowers hap) K
  have hc : Nat.card ((zpowers a).subgroupOf K) = p ^ 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzK).toEquiv, Nat.card_zpowers, hao, pow_one]
  have h2 := SU1.le_pRank hp.one_lt (le_top : (zpowers a).subgroupOf K ≤ (⊤ : Subgroup ↥K)) hel hc
  rw [h1]
  exact h2

end Ctx

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64ii
