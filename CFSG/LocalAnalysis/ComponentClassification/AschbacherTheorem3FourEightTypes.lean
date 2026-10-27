module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightLayer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoverExclCenter
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.GH74.Bender.Suzuki
public import CFSG.Walter.J1Props.Elt
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.Walter.Bender1970.S2.Basic

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped MatrixGroups

theorem psl2_card_two_part {n : ℕ} (h8 : n % 8 = 3 ∨ n % 8 = 5) :
    ∃ k, Odd k ∧ n * (n ^ 2 - 1) / 2 = 4 * k := by
  rcases h8 with h | h
  · obtain ⟨j, rfl⟩ : ∃ j, n = 8 * j + 3 := ⟨n / 8, by omega⟩
    refine ⟨(8 * j + 3) * (8 * j ^ 2 + 6 * j + 1), ?_, ?_⟩
    · exact Odd.mul ⟨4 * j + 1, by ring⟩ ⟨4 * j ^ 2 + 3 * j, by ring⟩
    · have h1 : (8 * j + 3) ^ 2 - 1 = 8 * (8 * j ^ 2 + 6 * j + 1) := by
        have : (8 * j + 3) ^ 2 = 8 * (8 * j ^ 2 + 6 * j + 1) + 1 := by ring
        omega
      rw [h1]
      have h2 : (8 * j + 3) * (8 * (8 * j ^ 2 + 6 * j + 1)) =
          2 * (4 * ((8 * j + 3) * (8 * j ^ 2 + 6 * j + 1))) := by ring
      rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]
  · obtain ⟨j, rfl⟩ : ∃ j, n = 8 * j + 5 := ⟨n / 8, by omega⟩
    refine ⟨(8 * j + 5) * (8 * j ^ 2 + 10 * j + 3), ?_, ?_⟩
    · exact Odd.mul ⟨4 * j + 2, by ring⟩ ⟨4 * j ^ 2 + 5 * j + 1, by ring⟩
    · have h1 : (8 * j + 5) ^ 2 - 1 = 8 * (8 * j ^ 2 + 10 * j + 3) := by
        have : (8 * j + 5) ^ 2 = 8 * (8 * j ^ 2 + 10 * j + 3) + 1 := by ring
        omega
      rw [h1]
      have h2 : (8 * j + 5) * (8 * (8 * j ^ 2 + 10 * j + 3)) =
          2 * (4 * ((8 * j + 5) * (8 * j ^ 2 + 10 * j + 3))) := by ring
      rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]

theorem three_pow_odd_mod_eight (m : ℕ) : 3 ^ (2 * m + 1) % 8 = 3 := by
  have h9 : (3 ^ 2) ^ m % 8 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [pow_succ, pow_mul, Nat.mul_mod, h9]

theorem ordRee_two_part (m : ℕ) : ∃ k, Odd k ∧ ordRee (3 ^ (2 * m + 1)) = 8 * k := by
  obtain ⟨q, hqdef⟩ : ∃ q, q = 3 ^ (2 * m + 1) := ⟨_, rfl⟩
  rw [← hqdef]
  have hq8 : q % 8 = 3 := hqdef ▸ three_pow_odd_mod_eight m
  have hq3 : q ^ 3 % 8 = 3 := by
    rw [Nat.pow_mod, hq8]
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  obtain ⟨a, ha, haodd⟩ : ∃ a, q ^ 3 + 1 = 4 * a ∧ a % 2 = 1 :=
    ⟨(q ^ 3 + 1) / 4, by omega, by omega⟩
  obtain ⟨b, hb, hbodd⟩ : ∃ b, q - 1 = 2 * b ∧ b % 2 = 1 := ⟨(q - 1) / 2, by omega, by omega⟩
  refine ⟨q ^ 3 * a * b, Odd.mul (Odd.mul hqodd.pow (Nat.odd_iff.mpr haodd))
    (Nat.odd_iff.mpr hbodd), ?_⟩
  unfold ordRee
  rw [ha, hb]
  ring

theorem card_goldschmidtJ1 : Nat.card goldschmidtJ1 = 175560 := by
  rw [show goldschmidtJ1 = walterJ1 from rfl]
  exact CFSG.Walter.J1Props.card_walterJ1

theorem card_map_mul_card_inf {A : Type*} [Group A] [Finite A] (H N : Subgroup A) [N.Normal] :
    Nat.card (H.map (QuotientGroup.mk' N)) * Nat.card (H ⊓ N : Subgroup A) = Nat.card H := by
  set φ := (QuotientGroup.mk' N).comp H.subtype with hφ
  have hrange : φ.range = H.map (QuotientGroup.mk' N) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = N.subgroupOf H := by
    ext x
    simp [hφ, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, hker] at h1
  have h2 : Nat.card (N.subgroupOf H) = Nat.card (H ⊓ N : Subgroup A) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [h2] at h1
  rw [mul_comm]
  exact h1

theorem mem_center_of_sq_eq_one {K : Type} [Group K] [Finite K] {q k : ℕ}
    (hB : fusionBenderBorel K q k) (hq : 2 ≤ q) (Q₀ : Sylow 2 K) {x : K}
    (hx : x ∈ (Q₀ : Subgroup K)) (hx2 : x ^ 2 = 1) :
    ∀ p ∈ (Q₀ : Subgroup K), x * p = p * x := by
  obtain ⟨hSE, -, hZ2, hZcard, -⟩ := hB Q₀
  by_cases hx1 : x = 1
  · intro p _
    rw [hx1, one_mul, mul_one]
  obtain ⟨z, hz1⟩ : ∃ z : Subgroup.center (Q₀ : Subgroup K), z ≠ 1 := by
    have h1 : 1 < Nat.card (Subgroup.center (Q₀ : Subgroup K)) := by
      rw [hZcard]
      omega
    have := Finite.one_lt_card_iff_nontrivial.mp h1
    exact exists_ne 1
  set z' : K := ((z : Q₀) : K) with hz'def
  have hz'Q : z' ∈ (Q₀ : Subgroup K) := (z : Q₀).2
  have hz'1 : z' ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hz'2 : z' ^ 2 = 1 := by
    have := congrArg Subtype.val (hZ2 (z : Q₀) z.2)
    simpa [hz'def] using this
  have hM :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.isStronglyEmbedded_of_fusion hSE
  obtain ⟨d, hdN, hd⟩ := hM.involutions_conjugate_in (Subgroup.le_normalizer hz'Q)
    ⟨hz'1, hz'2⟩ (Subgroup.le_normalizer hx) ⟨hx1, hx2⟩
  change d⁻¹ * z' * d = x at hd
  intro p hp
  have hpd : d * p * d⁻¹ ∈ (Q₀ : Subgroup K) := (Subgroup.mem_normalizer_iff.mp hdN p).mp hp
  have hzd : z' * (d * p * d⁻¹) = (d * p * d⁻¹) * z' := by
    have := Subgroup.mem_center_iff.mp z.2 ⟨_, hpd⟩
    exact (congrArg Subtype.val this).symm
  rw [← hd]
  calc d⁻¹ * z' * d * p = d⁻¹ * (z' * (d * p * d⁻¹)) * d := by group
    _ = d⁻¹ * ((d * p * d⁻¹) * z') * d := by rw [hzd]
    _ = p * (d⁻¹ * z' * d) := by group

theorem eq_of_fusionBenderBorel {K : Type} [Group K] [Finite K] {q k q' k' : ℕ}
    (hB : fusionBenderBorel K q k) (hB' : fusionBenderBorel K q' k') :
    q = q' ∧ q ^ k = q' ^ k' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨-, -, -, hZ, hQ⟩ := hB Q₀
  obtain ⟨-, -, -, hZ', hQ'⟩ := hB' Q₀
  exact ⟨hZ.symm.trans hZ', hQ.symm.trans hQ'⟩

variable {X : Type} [Group X] [Finite X]
variable {G T S Q H : Subgroup X} {g y : X}

namespace ElemCtx

theorem center_le_Z (c : ElemCtx G T S Q H g y) :
    (Subgroup.center G).map G.subtype ≤ (T ⊔ rightConjugate T g) ⊓ G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  set ZG := (Subgroup.center G).map G.subtype with hZGdef
  have hZGG : ZG ≤ G := Subgroup.map_subtype_le _
  have hZGc : ∀ z ∈ ZG, ∀ x ∈ G, x * z = z * x := by
    rintro _ ⟨z, hz, rfl⟩ x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)
  have hZGN : G ⊔ T ≤ Subgroup.normalizer (ZG : Set X) := fun x hx =>
    mem_normalizer_map_of_characteristic (Subgroup.center G)
      ((sup_le Subgroup.le_normalizer c.frame.le_normalizer) hx)
  have hZGab : IsMulCommutative ZG := ⟨⟨fun a b => Subtype.ext (hZGc b b.2 a (hZGG a.2))⟩⟩
  have hZG2 : IsPGroup 2 ZG :=
    isPGroup_of_abelian hZGG (le_sup_left.trans hZGN) hZGab c.oddCore_eq_bot
  have hZGP : ZG ≤ S ⊓ G :=
    le_of_isSylowOf_of_normal c.isSylowOf_P hZG2 hZGG (le_sup_left.trans hZGN)
  have hZnot : ¬ (T ⊔ rightConjugate T g) ⊓ G ≤ ZG := by
    intro hle
    apply c.false_of_normal_Z
    intro x hx
    have key : ∀ x' ∈ G, ∀ z ∈ (T ⊔ rightConjugate T g) ⊓ G,
        x' * z * x'⁻¹ ∈ (T ⊔ rightConjugate T g) ⊓ G := by
      intro x' hx' z hz
      rw [hZGc z (hle hz) x' hx', mul_inv_cancel_right]
      exact hz
    exact mem_normalizer_of_conj_le (key x hx) (by simpa using key x⁻¹ (G.inv_mem hx))
  have hA : ∀ r ∈ ZG, r ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) →
      r ∈ (T ⊔ rightConjugate T g) ⊓ G := by
    intro r hrZG hrW
    by_contra hrZ
    have hmem : ∀ t ∈ T, r⁻¹ * (t⁻¹ * r * t) ∈ ZG ⊓ ((T ⊔ rightConjugate T g) ⊓ G) := by
      intro t ht
      refine ⟨ZG.mul_mem (ZG.inv_mem hrZG) ?_, comm_mem_Z_of_mem_W e hrW
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left ht))⟩
      have := (Subgroup.mem_normalizer_iff.mp (hZGN (Subgroup.mem_sup_right (T.inv_mem ht)))
        r).mp hrZG
      simpa using this
    let f : T → ↥(ZG ⊓ ((T ⊔ rightConjugate T g) ⊓ G)) :=
      fun t => ⟨r⁻¹ * ((t : X)⁻¹ * r * t), hmem t t.2⟩
    have hf : Function.Injective f := by
      intro t s hts
      have h1 : r⁻¹ * ((t : X)⁻¹ * r * t) = r⁻¹ * ((s : X)⁻¹ * r * s) :=
        congrArg Subtype.val hts
      have h2 : (t : X)⁻¹ * r * t = (s : X)⁻¹ * r * s := mul_left_cancel h1
      by_contra hne
      have hts1 : (t : X) * (s : X)⁻¹ ≠ 1 := fun h =>
        hne (Subtype.ext (mul_inv_eq_one.mp h))
      have hmemT : (t : X) * (s : X)⁻¹ ∈ T := T.mul_mem t.2 (T.inv_mem s.2)
      apply hrZ
      rw [← inf_centralizer_eq_Z e hmemT hts1]
      refine ⟨⟨e.A_le_S hrW, hZGG hrZG⟩, ?_⟩
      show r ∈ Subgroup.centralizer {(t : X) * (s : X)⁻¹}
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc r * ((t : X) * (s : X)⁻¹) = t * ((t : X)⁻¹ * r * t) * (s : X)⁻¹ := by group
        _ = t * ((s : X)⁻¹ * r * s) * (s : X)⁻¹ := by rw [h2]
        _ = (t : X) * (s : X)⁻¹ * r := by group
    have hcard := Nat.card_le_card_of_injective f hf
    have heq : ZG ⊓ ((T ⊔ rightConjugate T g) ⊓ G) = (T ⊔ rightConjugate T g) ⊓ G :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [e.card_Z]; exact hcard)
    exact hZnot (heq ▸ inf_le_left)
  have hB : ∀ u ∈ ZG, u ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
    intro u hu
    by_contra huW
    obtain ⟨t, ht, ht1⟩ := c.exists_ne_one
    have huP := hZGP hu
    have hrR := comm_mem_R e huP.1 huP.2 ht
    have hrZG : u⁻¹ * (t⁻¹ * u * t) ∈ ZG := by
      refine ZG.mul_mem (ZG.inv_mem hu) ?_
      have := (Subgroup.mem_normalizer_iff.mp (hZGN (Subgroup.mem_sup_right (T.inv_mem ht)))
        u).mp hu
      simpa using this
    exact ht1 (eq_one_of_comm_mem_Z e huP.1 huW ht (hA _ hrZG hrR.1))
  intro u hu
  exact hA u hu (hB u hu)

theorem center_facts (c : ElemCtx G T S Q H g y) :
    IsPGroup 2 (Subgroup.center G) ∧
      G ≤ Subgroup.normalizer (((Subgroup.center G).map G.subtype : Subgroup X) : Set X) ∧
      (Subgroup.center G).map G.subtype ≤ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := c.center_le_Z
  refine ⟨?_, fun x hx => mem_normalizer_map_of_characteristic (Subgroup.center G)
    (Subgroup.le_normalizer hx), fun z hz => ⟨Subgroup.mem_sup_right (hZ hz).1, (hZ hz).2⟩⟩
  have h2 : IsPGroup 2 ((Subgroup.center G).map G.subtype) :=
    (c.sylowFrame.sylow.isPGroup.to_le (c.Z_le_P.trans inf_le_left)).to_le hZ
  exact h2.of_equiv ((Subgroup.center G).equivMapOfInjective _ G.subtype_injective).symm

theorem false_of_abelian (c : ElemCtx G T S Q H g y)
    (hab : ∀ Q₀ : Sylow 2 (G ⧸ Subgroup.center G),
      IsMulCommutative (Q₀ : Subgroup (G ⧸ Subgroup.center G))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hN, hNR⟩ := c.center_facts
  set π := QuotientGroup.mk' (Subgroup.center G) with hπ
  have hP2 : IsPGroup 2 ((S ⊓ G).subgroupOf G) := c.isSylowOf_P.isPGroup.comap_subtype
  obtain ⟨Q₀, hQ₀⟩ := (hP2.map π).exists_le_sylow
  refine c.false_of_comm_le hNR hN fun a ha b hb => ?_
  have haQ : π ⟨a, ha.2⟩ ∈ (Q₀ : Subgroup _) :=
    hQ₀ (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha))
  have hbQ : π ⟨b, hb.2⟩ ∈ (Q₀ : Subgroup _) :=
    hQ₀ (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hb))
  have h1 : π ⟨a, ha.2⟩ * π ⟨b, hb.2⟩ = π ⟨b, hb.2⟩ * π ⟨a, ha.2⟩ :=
    congrArg Subtype.val ((hab Q₀).is_comm.comm ⟨_, haQ⟩ ⟨_, hbQ⟩)
  have h2 : (⟨a, ha.2⟩ : G)⁻¹ * ((⟨b, hb.2⟩ : G)⁻¹ * ⟨a, ha.2⟩ * ⟨b, hb.2⟩) ∈
      Subgroup.center G := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center G), MonoidHom.mem_ker, ← hπ, map_mul, map_mul,
      map_mul, map_inv, map_inv]
    calc (π ⟨a, ha.2⟩)⁻¹ * ((π ⟨b, hb.2⟩)⁻¹ * π ⟨a, ha.2⟩ * π ⟨b, hb.2⟩)
        = (π ⟨a, ha.2⟩)⁻¹ * ((π ⟨b, hb.2⟩)⁻¹ * (π ⟨a, ha.2⟩ * π ⟨b, hb.2⟩)) := by group
      _ = (π ⟨a, ha.2⟩)⁻¹ * ((π ⟨b, hb.2⟩)⁻¹ * (π ⟨b, hb.2⟩ * π ⟨a, ha.2⟩)) := by rw [h1]
      _ = 1 := by group
  exact ⟨_, h2, rfl⟩

omit [Finite X] in
theorem card_eq_mul_center (G : Subgroup X) :
    Nat.card G = Nat.card (G ⧸ Subgroup.center G) * Nat.card (Subgroup.center G) := by
  rw [← Subgroup.index_eq_card, mul_comm, Subgroup.card_mul_index]

theorem false_of_card (c : ElemCtx G T S Q H g y)
    (hk : ∃ k, Odd k ∧ Nat.card (G ⧸ Subgroup.center G) ∣ 8 * k) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  obtain ⟨k, hkodd, hdvd⟩ := hk
  obtain ⟨hcen2, hN, -⟩ := c.center_facts
  have hZGZ := c.center_le_Z
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp c.isSylowOf_P.isPGroup
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hcen2
  have hPG : Nat.card (S ⊓ G : Subgroup X) ∣ Nat.card G := Subgroup.card_dvd_of_le inf_le_right
  have h1 : 2 ^ m ∣ k * (8 * 2 ^ n) := by
    rw [← hm]
    refine hPG.trans ?_
    rw [card_eq_mul_center, hn]
    have : k * (8 * 2 ^ n) = 8 * k * 2 ^ n := by ring
    rw [this]
    exact Nat.mul_dvd_mul_right hdvd _
  have h2 : 2 ^ m ∣ 8 * 2 ^ n :=
    (Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hkodd)).dvd_of_dvd_mul_left h1
  have h3 : Nat.card (S ⊓ G : Subgroup X) ≤
      8 * Nat.card ((Subgroup.center G).map G.subtype) := by
    rw [hm, Subgroup.card_map_of_injective G.subtype_injective, hn]
    exact Nat.le_of_dvd (by positivity) h2
  have hZGcard : Nat.card ((Subgroup.center G).map G.subtype) ≤ Nat.card T :=
    (Subgroup.card_le_of_le hZGZ).trans_eq e.card_Z
  rw [card_SG e] at h3
  have h4 := e.four_le_card
  have hq : Nat.card T ≤ 4 := by nlinarith
  have hq4 : Nat.card T = 4 := by omega
  rw [hq4] at h3 hZGcard
  have heq : (Subgroup.center G).map G.subtype = (T ⊔ rightConjugate T g) ⊓ G :=
    Subgroup.eq_of_le_of_card_ge hZGZ (by rw [e.card_Z, hq4]; omega)
  exact c.false_of_normal_Z (heq ▸ hN)

theorem false_of_outer (c : ElemCtx G T S Q H g y)
    (hodd : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer G))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  obtain ⟨t, ht, ht1⟩ := c.exists_ne_one
  have ht2 : t ^ 2 = 1 := e.sq_T t ht
  have htt : t * t = 1 := by rw [← pow_two, ht2]
  have htG := c.frame.le_normalizer ht
  have htS := c.sylowFrame.le ht
  let α : MulAut G :=
    { toFun := fun x => ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp htG x).mp x.2⟩
      invFun := fun x => ⟨t⁻¹ * x * t, by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htG) x).mp x.2
        simpa using this⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x x' => Subtype.ext (by simp [mul_assoc]) }
  have hα : ∀ x : G, ((α x : G) : X) = t * x * t⁻¹ := fun _ => rfl
  have hα2 : α * α = 1 := by
    ext x
    change t * (t * (x : X) * t⁻¹) * t⁻¹ = x
    calc t * (t * (x : X) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [htt]; group
  set φ := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner G)
    with hφ
  have hord : orderOf (φ α) = 1 := by
    have h1 : orderOf (φ α) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_two, hα2, map_one])
    have h2 : orderOf (φ α) ∣ Nat.card
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer G) := orderOf_dvd_natCard _
    exact Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h2 (Nat.coprime_two_right.mpr hodd)) h1
  have hαin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G := by
    rw [← QuotientGroup.ker_mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner G),
      MonoidHom.mem_ker, ← hφ]
    exact orderOf_eq_one_iff.mp hord
  obtain ⟨h, hh⟩ := hαin
  have hconj : ∀ x ∈ G, (h : X) * x * (h : X)⁻¹ = t * x * t⁻¹ := by
    intro x hx
    have h1 := congrArg (fun β : MulAut G => ((β ⟨x, hx⟩ : G) : X)) hh
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact h1.trans (hα ⟨x, hx⟩)
  have hhG : (h : X) ∈ G := h.2
  have htP : t ∈ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer htS, htG⟩
  have hhP : (h : X) ∈ G ⊓ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X) := by
    refine ⟨hhG, ?_⟩
    show (h : X) ∈ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X)
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      rw [hconj p hp.2]
      exact (Subgroup.mem_normalizer_iff.mp htP p).mp hp
    · intro hp
      have hpG : p ∈ G := by
        have := G.mul_mem (G.mul_mem (G.inv_mem hhG) hp.2) hhG
        simpa [mul_assoc] using this
      rw [hconj p hpG] at hp
      exact (Subgroup.mem_normalizer_iff.mp htP p).mpr hp
  have hh2 : (h : X) ^ 2 ∈ (Subgroup.center G).map G.subtype := by
    refine ⟨h ^ 2, ?_, by simp⟩
    show h ^ 2 ∈ Subgroup.center G
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    have htx : t * (x : X) * t⁻¹ ∈ G := (Subgroup.mem_normalizer_iff.mp htG x).mp x.2
    have h1 : (h : X) * ((h : X) * x * (h : X)⁻¹) * (h : X)⁻¹ = x := by
      rw [hconj x x.2, hconj _ htx]
      calc t * (t * (x : X) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
        _ = x := by rw [htt]; group
    calc (x : X) * (h : X) ^ 2
        = (h : X) * ((h : X) * x * (h : X)⁻¹) * (h : X)⁻¹ * (h : X) ^ 2 := by rw [h1]
      _ = (h : X) ^ 2 * x := by rw [pow_two]; group
  have hh4 : ((h : X) ^ 2) ^ 2 = 1 := sq_Z e (c.center_le_Z hh2)
  have hz2 : IsPGroup 2 (Subgroup.zpowers (h : X)) := by
    have h4 : (h : X) ^ (2 ^ 2) = 1 := by
      rw [show 2 ^ 2 = 2 * 2 by norm_num, pow_mul]
      exact hh4
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h4)
    exact IsPGroup.iff_card.mpr ⟨j, by rw [Nat.card_zpowers, hj]⟩
  have hPK : IsSylowOf 2 (S ⊓ G) (G ⊓ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X)) :=
    c.isSylowOf_P.of_le (le_inf inf_le_right Subgroup.le_normalizer) inf_le_left
  obtain ⟨k, hk, hkey⟩ := isSylowOf_exists_conj_mem hPK (Subgroup.zpowers_le.mpr hhP) hz2
  have hhPmem : (h : X) ∈ S ⊓ G := by
    have h1 := hkey _ (Subgroup.mem_zpowers (h : X))
    have := (Subgroup.mem_normalizer_iff.mp hk.2 _).mp h1
    simpa [mul_assoc] using this
  have hhZ : (h : X) ∈ (T ⊔ rightConjugate T g) ⊓ G := by
    rw [← inf_centralizer_eq_Z e ht ht1]
    refine ⟨hhPmem, ?_⟩
    show (h : X) ∈ Subgroup.centralizer {t}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hconj (h : X) hhG
    calc (h : X) * t = (h : X) * (h : X) * (h : X)⁻¹ * t := by group
      _ = t * (h : X) * t⁻¹ * t := by rw [h1]
      _ = t * (h : X) := by group
  have hRZ : (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G ≤
      (T ⊔ rightConjugate T g) ⊓ G := by
    intro r hr
    rw [← inf_centralizer_eq_Z e ht ht1]
    refine ⟨⟨e.A_le_S hr.1, hr.2⟩, ?_⟩
    show r ∈ Subgroup.centralizer {t}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hconj r hr.2
    have h2 := e.Z_comm hhZ hr.1
    have h3 : t * r * t⁻¹ = r := by
      rw [← h1, h2]
      group
    calc r * t = (t * r * t⁻¹) * t := by rw [h3]
      _ = t * r := by group
  have hcard := Subgroup.card_le_of_le hRZ
  rw [card_R e, e.card_Z] at hcard
  have h4 := e.four_le_card
  nlinarith

theorem false_of_psl2_even (c : ElemCtx G T S Q H g y) {f : ℕ} (hf : 2 ≤ f)
    (eL : (G ⧸ Subgroup.center G) ≃* PSL(2, GaloisField 2 f)) : False := by
  have : Finite (PSL(2, GaloisField 2 f)) := Finite.of_surjective eL eL.surjective
  have hBB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
    f hf).map_mulEquiv eL.symm
  apply c.false_of_abelian
  intro Q₀
  obtain ⟨-, -, -, hZ, hQ⟩ := hBB Q₀
  rw [pow_one] at hQ
  have htop : Subgroup.center (Q₀ : Subgroup (G ⧸ Subgroup.center G)) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hZ, hQ])
  exact ⟨⟨fun a b => Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a⟩⟩

theorem false_of_suzuki (c : ElemCtx G T S Q H g y) (hq : CFSG.Open.IsQuasisimple G) {a : ℕ}
    (ha : 1 ≤ a) (eS : (G ⧸ Subgroup.center G) ≃* Sz a) : False := by
  have hM := CFSG.GH74.Bender.suzukiModel_of_mulEquiv_sz ha eS
  have : Group.IsPerfect G := ⟨hq.1⟩
  have h := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity _ 2 (2 * a + 1)
    hM).2 G ⟨MulEquiv.refl _⟩
  exact c.false_of_outer h.2.2

theorem false_of_unitary (c : ElemCtx G T S Q H g y) (hin : Theorem48Inputs)
    (hq : CFSG.Open.IsQuasisimple G) {f : ℕ} (hf : 2 ≤ f)
    (eU : (G ⧸ Subgroup.center G) ≃* PSU3 2 f) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  have : Finite (PSU3 2 f) := Finite.of_surjective eU eU.surjective
  have hBB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_2
    f hf).map_mulEquiv eU.symm
  have h2f : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  obtain ⟨hcen2, -, -⟩ := c.center_facts
  set π := QuotientGroup.mk' (Subgroup.center G) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨Q₀, hQ₀⟩ := c.isSylowOf_P
  have hmemQ : ∀ v : G, v ∈ (Q₀ : Subgroup G) ↔ (v : X) ∈ S ⊓ G := by
    intro v
    constructor
    · intro hv
      exact hQ₀ ▸ ⟨v, hv, rfl⟩
    · intro hv
      obtain ⟨w, hw, hwv⟩ := (hQ₀ ▸ hv : (v : X) ∈ (Q₀ : Subgroup G).map G.subtype)
      rwa [← Subtype.ext hwv]
  by_cases hcen : Subgroup.center G = ⊥
  ·
    have hπi : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk', hcen]
    set Qb := Q₀.mapSurjective hπs with hQbdef
    obtain ⟨-, -, hZ2, hZcard, hQcard⟩ := hBB Qb
    have hQbcard : Nat.card (Qb : Subgroup (G ⧸ Subgroup.center G)) =
        Nat.card (S ⊓ G : Subgroup X) := by
      rw [hQbdef, Sylow.coe_mapSurjective, Subgroup.card_map_of_injective hπi, ← hQ₀,
        Subgroup.card_map_of_injective G.subtype_injective]
    set Zb := (((T ⊔ rightConjugate T g) ⊓ G).subgroupOf G).map π with hZbdef
    set Cb := (Subgroup.center (Qb : Subgroup (G ⧸ Subgroup.center G))).map
      (Qb : Subgroup (G ⧸ Subgroup.center G)).subtype with hCbdef
    have hZC : Zb ≤ Cb := by
      rintro _ ⟨z, hz, rfl⟩
      have hzP : (z : X) ∈ S ⊓ G := c.Z_le_P (Subgroup.mem_subgroupOf.mp hz)
      have hzQ : π z ∈ (Qb : Subgroup (G ⧸ Subgroup.center G)) := ⟨z, (hmemQ z).mpr hzP, rfl⟩
      have hz2 : (π z) ^ 2 = 1 := by
        rw [← map_pow]
        have : z ^ 2 = 1 := Subtype.ext (by simpa using sq_Z e (Subgroup.mem_subgroupOf.mp hz))
        rw [this, map_one]
      have hcent := mem_center_of_sq_eq_one hBB h2f Qb hzQ hz2
      refine ⟨⟨π z, hzQ⟩, Subgroup.mem_center_iff.mpr fun p => Subtype.ext ?_, rfl⟩
      exact (hcent p p.2).symm
    have hCZ : Cb ≤ Zb := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨v, hv, hvw⟩ := w.2
      have hw2 : ((w : G ⧸ Subgroup.center G)) ^ 2 = 1 := by
        simpa using congrArg Subtype.val (hZ2 w hw)
      have hv2 : v ^ 2 = 1 := by
        apply hπi
        rw [map_pow, map_one]
        have : π v = (w : G ⧸ Subgroup.center G) := hvw
        rw [this]
        exact hw2
      have hvZ := c.omegaOne_eq hin ((hmemQ v).mp hv) (by simpa using congrArg Subtype.val hv2)
      exact ⟨v, Subgroup.mem_subgroupOf.mpr hvZ, hvw⟩
    have hcardZ : Nat.card Zb = Nat.card T := by
      rw [hZbdef, Subgroup.card_map_of_injective hπi, ← e.card_Z,
        ← Subgroup.card_map_of_injective G.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr inf_le_right]
    have hcardC : Nat.card Cb = 2 ^ f := by
      rw [hCbdef, Subgroup.card_map_of_injective
        (Qb : Subgroup (G ⧸ Subgroup.center G)).subtype_injective, hZcard]
    have heq := le_antisymm hZC hCZ
    rw [heq, hcardC] at hcardZ
    rw [hQbcard, card_SG e, ← hcardZ] at hQcard
    have h4 := e.four_le_card
    rw [← hcardZ] at h4
    nlinarith
  ·
    exfalso
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hcen2
    have hn1 : 1 ≤ n := by
      rcases n with _ | n
      · exact absurd (Subgroup.card_eq_one.mp (by rw [hn, pow_zero])) hcen
      · omega
    obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := Subgroup.center G) 2
      (n := n - 1) (by rw [hn]; exact pow_dvd_pow 2 (Nat.sub_le n 1))
    set Z₀ := K₀.map (Subgroup.center G).subtype with hZ₀def
    have hZ₀c : Z₀ ≤ Subgroup.center G := Subgroup.map_subtype_le _
    have : Z₀.Normal := ⟨fun x hx k => by
      have := Subgroup.mem_center_iff.mp (hZ₀c hx) k
      rw [this, mul_inv_cancel_right]
      exact hx⟩
    have hsimple : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2
    have hbot := CFSG.ProperTwoGeneratedCore.Lemma37.CoverExcl.center_eq_bot_of_isSimpleGroup
      (CFSG.Walter.IsQuasisimple.exists_mul_ne_mul (isQuasisimple_gw hq))
    have hcJ := CFSG.ProperTwoGeneratedCore.Lemma37.CoverExcl.center_quotient_eq_map hZ₀c hbot
    have hcard2 : Nat.card (Subgroup.center (G ⧸ Z₀)) = 2 := by
      rw [hcJ]
      have h1 := card_map_mul_card_inf (Subgroup.center G) Z₀
      have hZ₀card : Nat.card Z₀ = 2 ^ (n - 1) := by
        rw [hZ₀def, Subgroup.card_map_of_injective (Subgroup.center G).subtype_injective, hK₀]
      rw [inf_eq_right.mpr hZ₀c, hZ₀card, hn] at h1
      have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h2] at h1
      exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
    have hperf : commutator (G ⧸ Z₀) = ⊤ := by
      have h1 := congrArg (Subgroup.map (QuotientGroup.mk' Z₀)) hq.1
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z₀)] at h1
      rw [commutator_def]
      exact h1
    obtain ⟨eJ⟩ := CFSG.ProperTwoGeneratedCore.Lemma37.CoverExcl.quotientCenterEquiv hZ₀c hcJ
    have hmodel : CFSG.Theory.Comparator.PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
    have hB : CFSG.BenderSuzuki.IsBenderGroup ((G ⧸ Z₀) ⧸ Subgroup.center (G ⧸ Z₀)) :=
      .isPSU3 f hf ((eJ.trans eU).trans (MulEquiv.subgroupCongr hmodel.symm))
    rcases CFSG.ProperTwoGeneratedCore.Lemma37.bender_cover_quotient hperf hcard2 hB with
      hL | hS
    · obtain ⟨eL⟩ := hL
      have : Finite (CFSG.Theory.Comparator.PSL2Model 2) := Finite.of_surjective eL eL.surjective
      have hBL :=
        (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
          2 le_rfl).map_mulEquiv ((eJ.symm.trans eL).symm)
      obtain ⟨h1, h2⟩ := eq_of_fusionBenderBorel hBB hBL
      rw [h1] at h2
      norm_num at h2
    · obtain ⟨eS⟩ := hS
      have hmodelS : CFSG.Theory.Comparator.SzModel 1 = Sz 1 := by
        simp only [CFSG.Theory.Comparator.SzModel, CFSG.Theory.Comparator.SzGenerators, CFSG.Open.Sz,
          CFSG.Open.SzGenerators]
      have eS' := (eJ.symm.trans eS).trans (MulEquiv.subgroupCongr hmodelS)
      have : Finite (Sz 1) := Finite.of_surjective eS' eS'.surjective
      have hBS :=
        (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4
          1 le_rfl).map_mulEquiv eS'.symm
      obtain ⟨h1, h2⟩ := eq_of_fusionBenderBorel hBB hBS
      rw [h1] at h2
      norm_num at h2

theorem false_of_inputs (c : ElemCtx G T S Q H g y) (hin : Theorem48Inputs) : False := by
  obtain ⟨hq, htype⟩ := c.isQuasisimple_G hin
  rcases htype with ⟨f, hf, ⟨eL⟩⟩ | ⟨a, ha, ⟨eS⟩⟩ | ⟨f, hf, ⟨eU⟩⟩ |
      ⟨p, f, hp, hodd, hf, -, h8, ⟨eP⟩⟩ | ⟨m, -, hcard⟩ | ⟨⟨eJ⟩⟩
  · exact c.false_of_psl2_even (by omega) eL
  · exact c.false_of_suzuki hq ha eS
  · exact c.false_of_unitary hin hq hf eU
  · apply c.false_of_card
    obtain ⟨k, hk, hkeq⟩ := psl2_card_two_part h8
    refine ⟨k, hk, ?_⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have h1 := CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (p := p) (m := f) hp2
      (by omega)
    rw [Nat.card_congr eP.toEquiv]
    change Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField p f)) ∣ _
    rw [h1, mul_comm 2 f, pow_mul, hkeq]
    exact Dvd.intro_left 2 (by ring)
  · apply c.false_of_card
    obtain ⟨k, hk, hkeq⟩ := ordRee_two_part m
    exact ⟨k, hk, by rw [hcard, hkeq]⟩
  · apply c.false_of_card
    refine ⟨21945, by decide, ?_⟩
    rw [Nat.card_congr eJ.toEquiv, card_goldschmidtJ1]

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
