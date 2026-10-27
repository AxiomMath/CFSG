module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step37
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step17
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3G2NQ0
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Q0Model
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBActionKernel
public import CFSG.Sporadic.SuzOddCore.SmallAut
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.Sporadic.SuzOddCore

namespace G2

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem mem_g2ShortParabolicRadical_of_pow_eq_one
    (hK : Nat.card K = 4) {w : ModGL .G2 K} (hw : w ∈ g2ShortParabolicRadical K ⊔ g2TorusR K)
    {n : ℕ} (hwn : w ^ 2 ^ n = 1) : w ∈ g2ShortParabolicRadical K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : g2ShortParabolicRadical K ⊔ g2TorusR K ≤
      normalizer (g2ShortParabolicRadical K : Set (ModGL .G2 K)) :=
    sup_le le_normalizer ((le_sup_right : g2TorusR K ≤ g2Para K).trans g2Para_le_normalizer)
  have hX : Nat.card (g2ShortParabolicRadical K) = 2 ^ 10 := by
    rw [card_g2ShortParabolicRadical, hK]
    norm_num
  have hw2 : IsPGroup 2 (zpowers w) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hwn)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hW2 : IsPGroup 2 ↥(g2ShortParabolicRadical K ⊔ zpowers w) :=
    (IsPGroup.of_card hX).to_sup_of_normal_left' hw2 (zpowers_le.mpr (hN hw))
  have hdvd : Nat.card ↥(g2ShortParabolicRadical K ⊔ zpowers w) ∣ 2 ^ 10 * 3 := by
    rw [← card_g2D0Hr hK]
    exact card_dvd_of_le (sup_le le_sup_left (zpowers_le.mpr hw))
  have : Finite ↥(g2ShortParabolicRadical K ⊔ zpowers w) :=
    Nat.finite_of_card_ne_zero fun h => by rw [h] at hdvd; norm_num at hdvd
  obtain ⟨m, hm⟩ := hW2.exists_card_eq
  have hm10 : 2 ^ m ∣ 2 ^ 10 := by
    rw [← hm]
    exact (Nat.Coprime.dvd_mul_right
      (by rw [hm]; exact Nat.Coprime.pow_left m (by norm_num))).mp hdvd
  have heq := eq_of_le_of_card_ge (le_sup_left : g2ShortParabolicRadical K ≤ _ ⊔ zpowers w)
    (by rw [hm, hX]; exact Nat.le_of_dvd (by norm_num) hm10)
  rw [heq]
  exact mem_sup_right (mem_zpowers w)

end G2

namespace Sec3

section General

variable {G : Type} [Group G]

theorem eq_or_eq_of_quaternion {Q₀ : Subgroup G} (hQ : Nonempty (↥Q₀ ≃* QuaternionGroup 2))
    {a b : G} (ha : a ∈ Q₀) (hb : b ∈ Q₀) (ha2 : a * a = 1) (hb2 : b * b = 1) :
    a = 1 ∨ b = 1 ∨ a = b := by
  obtain ⟨e⟩ := hQ
  have ha' : e ⟨a, ha⟩ * e ⟨a, ha⟩ = 1 := by
    rw [← map_mul, MulEquiv.map_eq_one_iff]
    exact Subtype.ext ha2
  have hb' : e ⟨b, hb⟩ * e ⟨b, hb⟩ = 1 := by
    rw [← map_mul, MulEquiv.map_eq_one_iff]
    exact Subtype.ext hb2
  rcases quaternion_facts.2.2 _ _ ha' hb' with h | h | h
  · exact Or.inl (congrArg Subtype.val ((MulEquiv.map_eq_one_iff e).mp h))
  · exact Or.inr (Or.inl (congrArg Subtype.val ((MulEquiv.map_eq_one_iff e).mp h)))
  · exact Or.inr (Or.inr (congrArg Subtype.val (e.injective h)))

theorem exists_mem_commute_of_quaternion {Q₀ R : Subgroup G}
    (hQ : Nonempty (↥Q₀ ≃* QuaternionGroup 2)) (hRQ : R ≤ centralizer (Q₀ : Set G))
    (hR : ∀ r ∈ R, r * r = 1) (hR4 : 4 ≤ Nat.card R) {s : G}
    (hs : ∀ r ∈ R, s * r * s⁻¹ * r⁻¹ ∈ Q₀) : ∃ r ∈ R, r ≠ 1 ∧ s * r = r * s := by
  have hsq : ∀ r ∈ R, (s * r * s⁻¹ * r⁻¹) * (s * r * s⁻¹ * r⁻¹) = 1 := by
    intro r hr
    have hc : (s * r * s⁻¹ * r⁻¹) * r = r * (s * r * s⁻¹ * r⁻¹) :=
      mem_centralizer_iff.mp (hRQ hr) _ (hs r hr)
    have hr2 := hR r hr
    calc (s * r * s⁻¹ * r⁻¹) * (s * r * s⁻¹ * r⁻¹)
        = (s * r * s⁻¹ * r⁻¹) * (s * r * s⁻¹ * r⁻¹) * (r * r) := by rw [hr2, mul_one]
      _ = (s * r * s⁻¹ * r⁻¹) * ((s * r * s⁻¹ * r⁻¹) * r) * r := by group
      _ = (s * r * s⁻¹ * r⁻¹) * (r * (s * r * s⁻¹ * r⁻¹)) * r := by rw [hc]
      _ = s * (r * r) * s⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  have hmul : ∀ u ∈ R, ∀ v ∈ R, s * (u * v) * s⁻¹ * (u * v)⁻¹ =
      (s * u * s⁻¹ * u⁻¹) * (s * v * s⁻¹ * v⁻¹) := by
    intro u hu v hv
    have hc : (s * v * s⁻¹ * v⁻¹) * u = u * (s * v * s⁻¹ * v⁻¹) :=
      mem_centralizer_iff.mp (hRQ hu) _ (hs v hv)
    calc s * (u * v) * s⁻¹ * (u * v)⁻¹ =
        s * u * s⁻¹ * (u⁻¹ * (u * (s * v * s⁻¹ * v⁻¹)) * u⁻¹) := by group
      _ = s * u * s⁻¹ * (u⁻¹ * ((s * v * s⁻¹ * v⁻¹) * u) * u⁻¹) := by rw [hc]
      _ = (s * u * s⁻¹ * u⁻¹) * (s * v * s⁻¹ * v⁻¹) := by group
  have hRne : R ≠ ⊥ := fun h => by
    rw [h, card_bot] at hR4
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := ne_bot_iff_exists_ne_one.mp hRne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hlt : zpowers u < R := by
    refine lt_of_le_of_ne (zpowers_le.mpr hu) fun h => ?_
    have h2 : Nat.card (zpowers u) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hR u hu) hu1'
    rw [h] at h2
    omega
  obtain ⟨v, hv, hvu⟩ := IsConcreteLE.exists_of_lt hlt
  have hv1 : v ≠ 1 := fun h => hvu (by rw [h]; exact one_mem _)
  have huv : u * v ≠ 1 := fun h => hvu (by
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_mem (mem_zpowers u))
  have hcomm : ∀ w : G, s * w * s⁻¹ * w⁻¹ = 1 → s * w = w * s := fun w h => by
    calc s * w = s * w * s⁻¹ * w⁻¹ * (w * s) := by group
      _ = w * s := by rw [h, one_mul]
  rcases eq_or_eq_of_quaternion hQ (hs u hu) (hs v hv) (hsq u hu) (hsq v hv) with h | h | h
  · exact ⟨u, hu, hu1', hcomm u h⟩
  · exact ⟨v, hv, hv1, hcomm v h⟩
  · refine ⟨u * v, mul_mem hu hv, huv, hcomm _ ?_⟩
    rw [hmul u hu v hv, ← h]
    exact hsq u hu

theorem exists_mem_commutator_mem [Finite G] {p : ℕ} [Fact p.Prime] {P N₁ N₂ : Subgroup G}
    (hP : IsPGroup p P) (h12 : N₁ ≤ N₂) (h2P : N₂ ≤ P) (hne : N₁ ≠ N₂)
    (hN₁ : P ≤ normalizer (N₁ : Set G)) (hN₂ : P ≤ normalizer (N₂ : Set G)) :
    ∃ s ∈ N₂, s ∉ N₁ ∧ ∀ u ∈ P, s * u * s⁻¹ * u⁻¹ ∈ N₁ := by
  have : (N₁.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer (h12.trans h2P)).mpr hN₁
  have hn₂ : (N₂.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer h2P).mpr hN₂
  have : Group.IsNilpotent (↥P ⧸ N₁.subgroupOf P) := (hP.to_quotient _).isNilpotent
  have : ((N₂.subgroupOf P).map (QuotientGroup.mk' (N₁.subgroupOf P))).Normal :=
    hn₂.map _ (QuotientGroup.mk'_surjective _)
  have hne' : (N₂.subgroupOf P).map (QuotientGroup.mk' (N₁.subgroupOf P)) ≠ ⊥ := by
    obtain ⟨s, hs2, hs1⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne h12 hne)
    intro hbot
    have h : QuotientGroup.mk' (N₁.subgroupOf P) ⟨s, h2P hs2⟩ ∈
        (N₂.subgroupOf P).map (QuotientGroup.mk' (N₁.subgroupOf P)) := ⟨⟨s, h2P hs2⟩, hs2, rfl⟩
    rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact hs1 h
  obtain ⟨⟨γ, hγ⟩, hγ1⟩ := ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  obtain ⟨⟨s, hsP⟩, hs2, rfl⟩ := (mem_inf.mp hγ).1
  refine ⟨s, hs2, fun hs1 => hγ1 (Subtype.ext ?_), fun u hu => ?_⟩
  · change QuotientGroup.mk' (N₁.subgroupOf P) ⟨s, hsP⟩ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hs1
  · have hc := mem_center_iff.mp (mem_inf.mp hγ).2
      (QuotientGroup.mk' (N₁.subgroupOf P) ⟨u, hu⟩)
    have h1 : QuotientGroup.mk' (N₁.subgroupOf P)
        (⟨s, hsP⟩ * ⟨u, hu⟩ * ⟨s, hsP⟩⁻¹ * ⟨u, hu⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1

end General

section Suz

variable {H : Type} [Group H]

theorem exists_suzT_hom
    {B : Subgroup H}
    (hB : commutator B = ⊤) (e : ↥B ⧸ center ↥B ≃* ↥suzM) :
    ∃ ψ : normalizer (B : Set H) →* ↥suzT,
      (∀ (b : H) (hb : b ∈ B), ((ψ ⟨b, le_normalizer hb⟩ : ↥suzT) : Equiv.Perm (Fin 1782)) =
        (e (QuotientGroup.mk ⟨b, hb⟩) : Equiv.Perm (Fin 1782))) ∧
      ∀ n, ψ n = 1 ↔ (n : H) ∈ centralizer (B : Set H) := by
  let L : Subgroup (normalizer (B : Set H)) := B.subgroupOf (normalizer (B : Set H))
  let eL : ↥L ≃* ↥B := subgroupOfEquivOfLe le_normalizer
  have hBp : Group.IsPerfect ↥B := (Group.isPerfect_def).2 hB
  have hperf : Group.IsPerfect ↥L :=
    Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  let π : ↥L →* ↥suzM := e.toMonoidHom.comp ((QuotientGroup.mk' (center ↥B)).comp eL.toMonoidHom)
  have hπ : Function.Surjective π :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp eL.surjective)
  have hker : π.ker = center ↥L := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [← map_center_eq eL]
    constructor
    · intro h
      obtain ⟨m, hm, hml⟩ := h
      rwa [eL.injective hml] at hm
    · intro h
      exact ⟨l, h, rfl⟩
  let θ := CentralCover.fullAction π hπ hker
  let β : ↥suzT ≃* MulAut ↥suzM := MulEquiv.ofBijective suzConjT suzConjT_bijective
  have key : ∀ l : ↥L, β.symm (θ (l : normalizer (B : Set H))) =
      ⟨(π l : Equiv.Perm (Fin 1782)), suzM_le_suzT (π l).2⟩ := by
    intro l
    rw [MulEquiv.symm_apply_eq]
    change θ (l : normalizer (B : Set H)) = suzConjT ⟨(π l : Equiv.Perm (Fin 1782)), _⟩
    rw [CentralCover.fullAction_coe]
    refine MulEquiv.ext fun m => Subtype.ext ?_
    rw [suzConjT_apply, MulAut.conj_apply]
    rfl
  refine ⟨β.symm.toMonoidHom.comp θ, fun b hb => ?_, fun n => ?_⟩
  · have := key ⟨⟨b, le_normalizer hb⟩, hb⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [this]
    rfl
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    rw [← MonoidHom.mem_ker, CentralCover.ker_fullAction, mem_centralizer_iff,
      mem_centralizer_iff]
    constructor
    · intro h b hb
      have := h ⟨b, le_normalizer hb⟩ hb
      exact congrArg Subtype.val this
    · intro h m hm
      exact Subtype.ext (h (m : H) hm)

end Suz

section Bounds

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}

theorem eq_one_of_mem_centralizer_sec3B (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y)
    {w : G} (hw : w ∈ centralizer (sec3B A₁ x : Set G)) {n : ℕ} (hwn : w ^ 2 ^ n = 1) :
    w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' := hS.setting
  obtain ⟨_, _, _, hC⟩ := hS'.config
  have hsyl := hC.sylow_inf
  rw [hS'.layer] at hsyl
  have hxZ : x ∈ centerIn (sec3B A₁ x) := by rw [hS.B_center]; exact mem_zpowers x
  have hxB : x ∈ sec3B A₁ x := (mem_inf.mp hxZ).1
  have hxA₁ : x ∈ centerIn A₁ := by rw [hS'.center_A₁]; exact mem_zpowers x
  have hA₁x : A₁ ≤ centralizer ({x} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (mem_inf.mp hxA₁).2 a ha)
  have hwx : w ∈ centralizer ((zpowers x : Subgroup G) : Set G) := by
    rw [centralizer_zpowers]
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hw x hxB).symm
  have hwA₁ : w ∈ centralizer (A₁ : Set G) := Subgroup.centralizer_le (le_sec3B hA₁x) hw
  have hwR : w ∈ normalizer (R : Set G) :=
    centralizer_le_normalizer _ (Subgroup.centralizer_le hS.R_le hw)
  have hw2 : IsPGroup 2 (zpowers w) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hwn)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hX2 : IsPGroup 2 ↥(R ⊔ zpowers w) :=
    hS'.sylowR.isPGroup.to_sup_of_normal_left' hw2 (zpowers_le.mpr hwR)
  have hXR := hsyl.eq_of_le le_sup_left (sup_le hsyl.le (zpowers_le.mpr ⟨⟨hwx, hwA₁⟩, hwR⟩)) hX2
  have hwR' : w ∈ R := by
    rw [← hXR]
    exact mem_sup_right (mem_zpowers w)
  have hwZ : w ∈ centerIn (sec3B A₁ x) := mem_inf.mpr ⟨hS.R_le hwR', hw⟩
  rw [hS.B_center] at hwZ
  have h3 : orderOf w ∣ 3 := hS'.order_x ▸ orderOf_dvd_of_mem_zpowers hwZ
  have h2 : orderOf w ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hwn
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h3 h2))

theorem card_le_two_of_le_centralizer_Q
    (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSQ : S ≤ centralizer (Q : Set G)) (hSx : S ≤ centralizer ({x} : Set G)) :
    Nat.card S ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKB : sec3B A₁ x ⊓ centralizer ({z} : Set G) ≤ sec3B A₁ x := inf_le_left
  obtain ⟨e₀⟩ := hS.B_suz
  obtain ⟨c, hcT, π, hπs, hπk, hπe⟩ := exists_hom_invE hS e₀
  have hQ₁8 : IsQ8Cube (SuzB0.coord_qVec.Q.subgroupOf (invE 1)) := by
    rw [← isQ8Cube_map_iff (invE 1).subtype (invE 1).subtype_injective, subgroupOf_map_subtype,
      inf_eq_left.mpr SuzB0.Q_le_invE]
    exact SuzB0.coord_qVec.isQ8Cube SuzB0.b0_parts.2.2.2.2.2.2
  have hQ₁n : (SuzB0.coord_qVec.Q.subgroupOf (invE 1)).Normal :=
    ⟨fun a ha w => mem_subgroupOf.mpr
      ((mem_normalizer_iff.mp (SuzB0.invE_le w.2).1 a).mp (mem_subgroupOf.mp ha))⟩
  have hCcard : Nat.card ↥(invE 1) = 3317760 := by
    rw [card_invE (by norm_num)]
    rfl
  obtain ⟨L, -, -, -, hQL, hLQ⟩ := exists_lift_eq_Q hS hQ₁8 hQ₁n hCcard rfl hπs hπk
  have hQ₁Q : ∀ q ∈ SuzB0.coord_qVec.Q, ∃ k : ↥(sec3B A₁ x ⊓ centralizer ({z} : Set G)),
      (k : G) ∈ Q ∧ (π k : Equiv.Perm (Fin 1782)) = q := by
    intro q hq
    obtain ⟨a, ha⟩ := hπs ⟨q, SuzB0.Q_le_invE hq⟩
    obtain ⟨l, hl, m, hm, rfl⟩ := hQL a (by rw [ha]; exact mem_subgroupOf.mpr hq)
    refine ⟨l, by rw [← hLQ]; exact mem_map_of_mem _ hl, ?_⟩
    rw [map_mul, MonoidHom.mem_ker.mp hm, mul_one] at ha
    rw [ha]
  obtain ⟨ψ, hψ, hψk⟩ := exists_suzT_hom hS.B_perf (e₀.trans suzEquivM)
  have hSN : S ≤ normalizer (sec3B A₁ x : Set G) :=
    hSx.trans (centralizer_le_normalizer_sec3B A₁ x)
  set χ : ↥S →* Equiv.Perm (Fin 1782) := (MulAut.conj c⁻¹).toMonoidHom.comp
    (suzT.subtype.comp (ψ.comp (inclusion hSN))) with hχdef
  have hχ : ∀ s, χ s = c⁻¹ * (ψ (inclusion hSN s) : Equiv.Perm (Fin 1782)) * c := fun s => by
    simp [hχdef]
  have hχt : ∀ s, χ s ∈ zpowers (suzInv 1) := by
    intro s
    rw [hχ]
    refine SuzB0.mem_zpowers_of_mem_centralizer_Q
      (mul_mem (mul_mem (inv_mem hcT) (ψ _).2) hcT) (mem_centralizer_iff.mpr fun q hq => ?_)
    obtain ⟨k, hkQ, hkq⟩ := hQ₁Q q hq
    have hkB : (k : G) ∈ sec3B A₁ x := hKB k.2
    set u := (ψ ⟨k, le_normalizer hkB⟩ : Equiv.Perm (Fin 1782)) with hu
    set v := (ψ (inclusion hSN s) : Equiv.Perm (Fin 1782)) with hv
    have hq : q = c⁻¹ * u * c := by
      rw [← hkq, hπe k, hu, hψ k hkB]
      rfl
    have huv : v * u = u * v := by
      have hsk : (inclusion hSN s) * ⟨k, le_normalizer hkB⟩ =
          ⟨k, le_normalizer hkB⟩ * (inclusion hSN s) :=
        Subtype.ext (mem_centralizer_iff.mp (hSQ s.2) k hkQ).symm
      rw [hu, hv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hsk]
    rw [hq]
    calc c⁻¹ * u * c * (c⁻¹ * v * c) = c⁻¹ * (u * v) * c := by group
      _ = c⁻¹ * (v * u) * c := by rw [huv]
      _ = c⁻¹ * v * c * (c⁻¹ * u * c) := by group
  have hχi : Function.Injective χ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, hχ] at hs
    have hψ1 : ψ (inclusion hSN s) = 1 := by
      apply Subtype.ext
      calc (ψ (inclusion hSN s) : Equiv.Perm (Fin 1782)) =
          c * (c⁻¹ * (ψ (inclusion hSN s) : Equiv.Perm (Fin 1782)) * c) * c⁻¹ := by group
        _ = 1 := by rw [hs]; group
    obtain ⟨n, hn⟩ := hS2 s
    have hn' : (s : G) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact mem_bot.mpr (Subtype.ext (eq_one_of_mem_centralizer_sec3B hS ((hψk _).mp hψ1) hn'))
  calc Nat.card S = Nat.card χ.range := Nat.card_congr (MonoidHom.ofInjective hχi).toEquiv
    _ ≤ Nat.card (zpowers (suzInv 1)) :=
      Subgroup.card_le_of_le (by rintro _ ⟨s, rfl⟩; exact hχt s)
    _ = 2 := by rw [Nat.card_zpowers, SuzB0.coord_qVec.orderOf_t]

theorem exists_sec3Model_Q₀
    (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    ∃ (K : Type) (_ : Field K) (_ : CharP K 2) (_ : Finite K), Nat.card K = 4 ∧
      ∃ f : ↥(adjointGroup .G2 K) →* G, Sec3Model G A A₁ E F x K f ∧ ∃ l : K, l ≠ 0 ∧
        D = ((g2ShortParabolicRadical K).subgroupOf (adjointGroup .G2 K)).map f ∧
        Q₀ = ((G2.g2Q0 K l).subgroupOf (adjointGroup .G2 K)).map f := by
  obtain ⟨K, _, _, _, hK, f, hM, l, -, -, hl0, -, -, -, hDf, hQm⟩ := exists_sec3Q0_model hQ.dData
  have hV₀ : V₀ = ((G2.g2V0 K).subgroupOf (adjointGroup .G2 K)).map f :=
    SetLike.coe_injective (hQ.V₀_eq.trans hQm.V₀_eq.symm)
  have hV : V = ((G2.g2V K).subgroupOf (adjointGroup .G2 K)).map f := by
    rw [hQ.V_eq, hQm.V_eq, hV₀]
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK, f, hM, l, hl0, hDf,
    (hQ.unique _ (hV ▸ hQm.Q₀_le) hQm.x_Q₀ hQm.Q₀_iso hQm.center_Q₀).symm⟩

theorem card_le_eight_of_le_centralizer_Q
    (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) {r : G} (hr : r ∈ R)
    (hr1 : r ≠ 1) {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSQ : S ≤ centralizer (Q : Set G))
    (hSr : S ≤ centralizer ({r} : Set G)) (hSN : S ≤ normalizer (Q₀ : Set G)) :
    Nat.card S ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hQ.dData
  have hSz := hD.suz
  have hS := hSz.setting
  have hFr := hS.frame
  have hstd := hS.base.hyp.standard
  have hKt := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hRK : R ≤ centralizer (A : Set G) := hS.sylowR.le
  have hAK : ∀ a ∈ A, a ∈ centralizer (A : Set G) → a = 1 := by
    intro a haA haK
    have ha : (⟨a, haA⟩ : A) ∈ center A := mem_center_iff.mpr fun b =>
      Subtype.ext (mem_centralizer_iff.mp haK b b.2)
    rw [hS.center_eq, mem_bot] at ha
    exact congrArg Subtype.val ha
  have hAN : A ≤ normalizer (centralizer (A : Set G) : Set G) := by
    rw [hNK]
    exact le_normalizer
  have hSA : S ≤ normalizer (A : Set G) := fun s hs => by
    rw [← hNK]
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hKt (hRK hr) hr1
      (hS.elemR.2 r hr) (mem_centralizer_singleton_iff.mp (hSr hs))
  obtain ⟨Kf, _, _, _, hKf, f, hM, l, hl0, hDf, hQ₀⟩ := exists_sec3Model_Q₀ hQ
  have hfinj := hM.inj
  have hD₀C : g2ShortParabolicRadical Kf ≤ adjointGroup .G2 Kf :=
    G2.g2ShortParabolicRadical_le_adjointGroup
  have hQ₀D₀ : G2.g2Q0 Kf l ≤ g2ShortParabolicRadical Kf :=
    (G2.g2Q0_le_g2V l).trans (G2.g2V_le_g2V0.trans G2.g2V0_le_g2ShortParabolicRadical)
  have hQC : G2.g2Q0 Kf l ≤ adjointGroup .G2 Kf := hQ₀D₀.trans hD₀C
  have hBCC : g2BCGroup Kf ≤ adjointGroup .G2 Kf :=
    G2.g2BCGroup_le_g2ShortParabolicRadical.trans hD₀C
  have hQ₀D : Q₀ ≤ D := by
    rw [hQ₀, hDf]
    exact tr_mono hQ₀D₀
  have hQ₀A : Q₀ ≤ A := by
    rw [hQ₀, ← hM.range_eq]
    exact map_le_range f _
  obtain ⟨hEA, -, -, -, hE16, -⟩ := frame_inf_A₁ hS
  have hB8 : 8 ≤ Nat.card (E ⊓ A₁ ⊓ Q : Subgroup G) := by
    have h := relIndex_mul_card (E ⊓ A₁ ⊓ Q) (E ⊓ A₁)
    rw [inf_eq_left.mpr inf_le_left, hSz.Q_EA, hE16] at h
    omega
  have hBEA : E ⊓ A₁ ⊓ Q ≤ E ⊓ A := by
    rw [hEA]
    exact inf_le_left
  have hdec : ∀ s ∈ S, ∃ k ∈ centralizer (A : Set G), ∃ c ∈ Q₀ ⊔ (E ⊓ A), s = k * c := by
    intro s hs
    obtain ⟨k, hk, c, hc, rfl⟩ := Sec3Model.exists_mul_of_fix g24Hyp hKf hM (hSA hs) hBEA hB8
      (Subgroup.centralizer_le (fun q hq => hq.2) (hSQ hs))
    refine ⟨k, hk, c, ?_, rfl⟩
    obtain ⟨c', hc', rfl⟩ := hc
    have hcA : f c' ∈ A := by
      rw [← hM.range_eq]
      exact ⟨c', rfl⟩
    obtain ⟨n, hn⟩ := hS2 ⟨k * f c', hs⟩
    have hn' : (k * f c') ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    rw [(Commute.mul_pow (mem_centralizer_iff.mp hk (f c') hcA).symm _)] at hn'
    have hc1 : f c' ^ 2 ^ n = 1 :=
      hAK _ (pow_mem hcA _) (by
        rw [eq_inv_of_mul_eq_one_right hn']
        exact inv_mem (pow_mem hk _))
    have hc'1 : (c' : ModGL .G2 Kf) ^ 2 ^ n = 1 := by
      have h1 : c' ^ 2 ^ n = 1 := hfinj (by rw [map_pow, hc1, map_one])
      simpa using congrArg Subtype.val h1
    have hc'D₀ : (c' : ModGL .G2 Kf) ∈ g2ShortParabolicRadical Kf :=
      G2.mem_g2ShortParabolicRadical_of_pow_eq_one hKf (mem_subgroupOf.mp hc') hc'1
    have hcN : f c' ∈ normalizer (Q₀ : Set G) := by
      have hkN : k ∈ normalizer (Q₀ : Set G) :=
        centralizer_le_normalizer _ (Subgroup.centralizer_le hQ₀A hk)
      simpa using mul_mem (inv_mem hkN) (hSN hs)
    have key : ∀ u : ↥(adjointGroup .G2 Kf), f u ∈ normalizer (Q₀ : Set G) →
        ∀ q ∈ G2.g2Q0 Kf l, (u : ModGL .G2 Kf) * q * (u : ModGL .G2 Kf)⁻¹ ∈ G2.g2Q0 Kf l := by
      intro u hu q hq
      have hfq : f ⟨q, hQC hq⟩ ∈ Q₀ := by
        rw [hQ₀]
        exact ⟨⟨q, hQC hq⟩, mem_subgroupOf.mpr hq, rfl⟩
      have h1 : f (u * ⟨q, hQC hq⟩ * u⁻¹) ∈ Q₀ := by
        rw [map_mul, map_mul, map_inv]
        exact (mem_normalizer_iff.mp hu _).mp hfq
      rw [hQ₀, mem_map_iff_mem hfinj, mem_subgroupOf] at h1
      exact h1
    have hc'N : (c' : ModGL .G2 Kf) ∈ normalizer (G2.g2Q0 Kf l : Set (ModGL .G2 Kf)) :=
      G2.mem_normalizer_of_conj (key c' hcN) fun q hq => by
        simpa using key c'⁻¹ (by rw [map_inv]; exact inv_mem hcN) q hq
    have hc'Q := G2.g2ShortParabolicRadical_inf_normalizer_g2Q0_le hKf hl0 ⟨hc'D₀, hc'N⟩
    rw [hQ₀, ← hM.E_eq, ← tr_sup hQC hBCC]
    exact ⟨c', mem_subgroupOf.mpr hc'Q, rfl⟩
  obtain ⟨eQ⟩ := hQ.Q₀_iso
  have hQ₀8 : Nat.card Q₀ = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hEA16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    rw [hEA]
    exact hE16
  have hz2 : orderOf z = 2 := by
    have h1 := hSz.q8.1.2.2.2
    rw [← card_centerIn, hSz.Q_center, Nat.card_zpowers] at h1
    exact h1
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    omega
  have hzQ₀ : z ∈ Q₀ := by
    have h : z ∈ centerIn Q₀ := by
      rw [hQ.center_Q₀, hSz.Q_center]
      exact mem_zpowers z
    exact (mem_inf.mp h).1
  have hzZ : z ∈ sec2Z A₁ E F := hSz.Zs_eq ▸ hSz.z_mem
  have hzE : z ∈ E := by
    have h2 : z ∈ centerIn (E ⊔ F) := (mem_inf.mp hzZ).2
    rw [← hFr.inf_eq_center] at h2
    exact (mem_inf.mp h2).1
  have hzA : z ∈ A := hS.le (mem_inf.mp hzZ).1
  have hQZ : Q₀ ⊓ (E ⊓ A) = zpowers z := by
    refine le_antisymm (fun w hw => ?_) (zpowers_le.mpr ⟨hzQ₀, hzE, hzA⟩)
    have hw2 : w * w = 1 := by
      rw [← pow_two]
      exact hFr.elemE.2 w (mem_inf.mp (mem_inf.mp hw).2).1
    rcases eq_or_eq_of_quaternion hQ.Q₀_iso (mem_inf.mp hw).1 hzQ₀ hw2 hzz with h | h | h
    · rw [h]
      exact one_mem _
    · exact absurd h hz1
    · rw [h]
      exact mem_zpowers z
  have hZN : E ⊓ A ≤ normalizer (Q₀ : Set G) := by
    intro w hw
    rw [hD.center_D] at hw
    exact centralizer_le_normalizer _ (Subgroup.centralizer_le hQ₀D (mem_inf.mp hw).2)
  have hW64 : Nat.card (Q₀ ⊔ (E ⊓ A) : Subgroup G) = 64 := by
    have h := card_sup_mul_card_inf hZN
    rw [hQZ, Nat.card_zpowers, hz2, hQ₀8, hEA16] at h
    omega
  have hWA : Q₀ ⊔ (E ⊓ A) ≤ A := sup_le hQ₀A inf_le_right
  have hKW : centralizer (A : Set G) ⊓ (Q₀ ⊔ (E ⊓ A)) = ⊥ :=
    eq_bot_iff.mpr fun w hw => mem_bot.mpr (hAK w (hWA (mem_inf.mp hw).2) (mem_inf.mp hw).1)
  have hKZ : centralizer (A : Set G) ⊓ (E ⊓ A) = ⊥ :=
    eq_bot_iff.mpr fun w hw =>
      mem_bot.mpr (hAK w (mem_inf.mp (mem_inf.mp hw).2).2 (mem_inf.mp hw).1)
  have hM₁ := card_sup_mul_card_inf (hWA.trans hAN)
  rw [hKW, card_bot, mul_one, hW64] at hM₁
  have hN₁ := card_sup_mul_card_inf ((inf_le_right : E ⊓ A ≤ A).trans hAN)
  rw [hKZ, card_bot, mul_one, hEA16] at hN₁
  have hidx : (centralizer (A : Set G) ⊔ (E ⊓ A)).relIndex
      (centralizer (A : Set G) ⊔ (Q₀ ⊔ (E ⊓ A))) = 4 := by
    have h := relIndex_mul_card (centralizer (A : Set G) ⊔ (E ⊓ A))
      (centralizer (A : Set G) ⊔ (Q₀ ⊔ (E ⊓ A)))
    have hle : centralizer (A : Set G) ⊔ (E ⊓ A) ≤ centralizer (A : Set G) ⊔ (Q₀ ⊔ (E ⊓ A)) :=
      sup_le_sup_left le_sup_right _
    rw [inf_eq_left.mpr hle, hN₁, hM₁] at h
    have hpos : 0 < Nat.card (centralizer (A : Set G)) * 16 :=
      Nat.mul_pos Nat.card_pos (by norm_num)
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h]; ring)
  have hSM : S ≤ centralizer (A : Set G) ⊔ (Q₀ ⊔ (E ⊓ A)) := fun s hs => by
    obtain ⟨k, hk, c, hc, rfl⟩ := hdec s hs
    exact mul_mem (mem_sup_left hk) (mem_sup_right hc)
  have hrel : (centralizer (A : Set G) ⊔ (E ⊓ A)).relIndex S ≤ 4 := by
    rw [← hidx]
    exact relIndex_le_of_le_right hSM (by rw [hidx]; norm_num)
  have hxZ : x ∈ centerIn A₁ := by rw [hS.center_A₁]; exact mem_zpowers x
  have hxA : x ∈ A := hS.le (mem_inf.mp hxZ).1
  have hA₁x : A₁ ≤ centralizer ({x} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (mem_inf.mp hxZ).2 a ha)
  have hKx : centralizer (A : Set G) ⊔ (E ⊓ A) ≤ centralizer ({x} : Set G) := by
    refine sup_le (fun k hk => ?_) ?_
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hk x hxA).symm
    · rw [hEA]
      exact inf_le_right.trans hA₁x
  have hS₀ : Nat.card ((centralizer (A : Set G) ⊔ (E ⊓ A)) ⊓ S : Subgroup G) ≤ 2 :=
    card_le_two_of_le_centralizer_Q hSz (hS2.to_le inf_le_right) (inf_le_right.trans hSQ)
      (inf_le_left.trans hKx)
  have h := relIndex_mul_card (centralizer (A : Set G) ⊔ (E ⊓ A)) S
  calc Nat.card S = _ := h.symm
    _ ≤ 4 * 2 := Nat.mul_le_mul hrel hS₀

end Bounds

end Sec3

section Step37iii

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
  {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}

theorem step37_iii
    (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    IsSylowOf 2 Q₀ (centralizer (Q : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSz := hQ.dData.suz
  have hS := hSz.setting
  have hFr := hS.frame
  have hQ₀C : Q₀ ≤ centralizer (Q : Set G) := le_centralizer_iff.mpr (hSz.Q_le.trans (step37_i hQ))
  obtain ⟨eQ⟩ := hQ.Q₀_iso
  have hQ₀8 : Nat.card Q₀ = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQ₀2 : IsPGroup 2 Q₀ := IsPGroup.of_card (n := 3) (by rw [hQ₀8]; norm_num)
  refine Sec3.isSylowOf_of_isSylowOf_inf_normalizer' hQ₀C ?_
  set M := centralizer (Q : Set G) ⊓ normalizer (Q₀ : Set G) with hMdef
  have hQ₀A : Q₀ ≤ A := by
    obtain ⟨Kf, _, _, _, -, f, hM, l, -, -, hQ₀⟩ := Sec3.exists_sec3Model_Q₀ hQ
    rw [hQ₀, ← hM.range_eq]
    exact map_le_range f _
  have hRQ₀ : R ≤ centralizer (Q₀ : Set G) := fun r hr =>
    Subgroup.centralizer_le hQ₀A (hS.sylowR.le hr)
  have hEP : E ≤ P := hSz.P_cE.symm.le.trans inf_le_left
  have hRT : R ≤ T := hFr.R_le_E.trans (hEP.trans hSz.P_le)
  have hRM : R ≤ normalizer (M : Set G) := fun r hr =>
    mem_normalizer_inf (mem_normalizer_centralizer (hSz.T_Q (hRT hr)))
      (mem_normalizer_normalizer (centralizer_le_normalizer _ (hRQ₀ hr)))
  have hHM : M ⊔ R ≤ normalizer (M : Set G) := sup_le le_normalizer hRM
  have hHQ₀ : M ⊔ R ≤ normalizer (Q₀ : Set G) :=
    sup_le inf_le_right (hRQ₀.trans (centralizer_le_normalizer _))
  obtain ⟨S₀, hRS₀⟩ :=
    (hS.sylowR.isPGroup.comap_subtype : IsPGroup 2 (R.subgroupOf (M ⊔ R))).exists_le_sylow
  set S₁ : Subgroup G := (S₀ : Subgroup ↥(M ⊔ R)).map (M ⊔ R).subtype with hS₁def
  have hS₁ : IsSylowOf 2 S₁ (M ⊔ R) := ⟨S₀, rfl⟩
  have hRS₁ : R ≤ S₁ := fun r hr => ⟨⟨r, (le_sup_right : R ≤ M ⊔ R) hr⟩, hRS₀ hr, rfl⟩
  have hS₂ : IsSylowOf 2 (S₁ ⊓ M) M := hS₁.inf_of_le_normalizer le_sup_left hHM
  have hQ₀M : Q₀ ≤ M := le_inf hQ₀C le_normalizer
  have hQ₀S₁ : Q₀ ≤ S₁ := by
    have h2 : IsPGroup 2 ↥(Q₀ ⊔ S₁) :=
      hQ₀2.to_sup_of_normal_left' hS₁.isPGroup (hS₁.le.trans hHQ₀)
    exact le_sup_left.trans
      (hS₁.eq_of_le le_sup_right (sup_le (hQ₀M.trans le_sup_left) hS₁.le) h2).le
  by_cases heq : Q₀ = S₁ ⊓ M
  · rw [heq]
    exact hS₂
  exfalso
  have hS₁N : S₁ ≤ normalizer ((S₁ ⊓ M : Subgroup G) : Set G) := fun w hw =>
    mem_normalizer_inf (le_normalizer hw) (hHM (hS₁.le hw))
  obtain ⟨s, hs, hsQ₀, hsc⟩ := Sec3.exists_mem_commutator_mem hS₁.isPGroup (le_inf hQ₀S₁ hQ₀M)
    inf_le_left heq (hS₁.le.trans hHQ₀) hS₁N
  obtain ⟨r, hr, hr1, hrs⟩ := Sec3.exists_mem_commute_of_quaternion hQ.Q₀_iso hRQ₀
    (fun r hr => by rw [← pow_two]; exact hS.elemR.2 r hr) hS.four_le
    (fun r hr => hsc r (hRS₁ hr))
  have hsub : Q₀ ⊔ zpowers s ≤ S₁ ⊓ M := sup_le (le_inf hQ₀S₁ hQ₀M) (zpowers_le.mpr hs)
  have hQ₀r : Q₀ ≤ centralizer ({r} : Set G) := fun q hq =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hRQ₀ hr) q hq)
  have h8 := Sec3.card_le_eight_of_le_centralizer_Q hQ hr hr1 (hS₂.isPGroup.to_le hsub)
    (hsub.trans (inf_le_right.trans inf_le_left))
    (sup_le hQ₀r (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hrs)))
    (hsub.trans (inf_le_right.trans inf_le_right))
  have heq' := eq_of_le_of_card_ge (le_sup_left : Q₀ ≤ Q₀ ⊔ zpowers s) (by rw [hQ₀8]; exact h8)
  exact hsQ₀ (by
    rw [heq']
    exact mem_sup_right (mem_zpowers s))

end Step37iii

end CFSG.ComponentClassification.AS81
