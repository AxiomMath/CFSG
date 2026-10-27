module

public import CFSG.GH74.GLS.LU.Local.Defs
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.LieType.Catalog.Realization
public import CFSG.GH74.GLS.LU.Final
public import CFSG.GH74.GLS.LU.Local.Core
public import CFSG.GH74.GLS.LU.Local.Core2

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G]

namespace LUComps

variable {q : ℕ} {z : G} {K₁ K₂ : Subgroup G}

theorem quasi₁ (h : LUComps G q z K₁ K₂) : CFSG.IsQuasisimple ↥K₁ :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.comp₁.1) h.comp₁.2.1

theorem quasi₂ (h : LUComps G q z K₁ K₂) : CFSG.IsQuasisimple ↥K₂ :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.comp₂.1) h.comp₂.2.1

theorem perfect₁ (h : LUComps G q z K₁ K₂) : ⁅K₁, K₁⁆ = K₁ :=
  commutator_self_of_isPerfect K₁ h.quasi₁.1

theorem perfect₂ (h : LUComps G q z K₁ K₂) : ⁅K₂, K₂⁆ = K₂ :=
  commutator_self_of_isPerfect K₂ h.quasi₂.1

theorem cz₁ (h : LUComps G q z K₁ K₂) {k : G} (hk : k ∈ K₁) : k * z = z * k :=
  mem_centralizer_singleton_iff.mp (h.comp₁.1 hk)

theorem cz₂ (h : LUComps G q z K₁ K₂) {k : G} (hk : k ∈ K₂) : k * z = z * k :=
  mem_centralizer_singleton_iff.mp (h.comp₂.1 hk)

theorem z_mem₁ (h : LUComps G q z K₁ K₂) : z ∈ K₁ := by
  have : z ∈ (center ↥K₁).map K₁.subtype := by rw [h.cen₁]; exact mem_zpowers z
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp this
  rw [← hy]; exact y.2

theorem z_mem₂ (h : LUComps G q z K₁ K₂) : z ∈ K₂ := by
  have : z ∈ (center ↥K₂).map K₂.subtype := by rw [h.cen₂]; exact mem_zpowers z
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp this
  rw [← hy]; exact y.2

theorem isPCompIn₁ [Finite G] (h : LUComps G q z K₁ K₂) : IsPCompIn 2 (Cz z) K₁ :=
  ⟨h.comp₁.1, CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent h.comp₁.2⟩

theorem isPCompIn₂ [Finite G] (h : LUComps G q z K₁ K₂) : IsPCompIn 2 (Cz z) K₂ :=
  ⟨h.comp₂.1, CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent h.comp₂.2⟩

theorem comm [Finite G] (h : LUComps G q z K₁ K₂) : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := by
  have hne : K₁.subgroupOf (Cz z) ≠ K₂.subgroupOf (Cz z) := by
    intro heq
    apply h.ne
    have := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_eq_left.mpr h.comp₁.1, inf_eq_left.mpr h.comp₂.1] at this
  have hc := (CFSG.LocalCores.distinct_components_commute h.comp₁.2 h.comp₂.2).resolve_left hne
  intro a ha b hb
  have h1 : ⁅(⟨a, h.comp₁.1 ha⟩ : ↥(Cz z)), (⟨b, h.comp₂.1 hb⟩ : ↥(Cz z))⁆ ∈
      ⁅K₁.subgroupOf (Cz z), K₂.subgroupOf (Cz z)⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr ha)
      (Subgroup.mem_subgroupOf.mpr hb)
  rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact congrArg Subtype.val h1

theorem inf_eq [Finite G] (h : LUComps G q z K₁ K₂) : K₁ ⊓ K₂ = zpowers z := by
  apply le_antisymm
  · intro x hx
    have hxc : x ∈ (center ↥K₁).map K₁.subtype := by
      refine Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact h.comm y y.2 x hx.2
    rw [h.cen₁] at hxc
    exact hxc
  · rw [zpowers_le]
    exact ⟨h.z_mem₁, h.z_mem₂⟩

theorem perm [Finite G] (h : LUComps G q z K₁ K₂) {c : G} (hc : c ∈ Cz z) :
    (K₁.map (MulAut.conj c).toMonoidHom = K₁ ∧ K₂.map (MulAut.conj c).toMonoidHom = K₂) ∨
    (K₁.map (MulAut.conj c).toMonoidHom = K₂ ∧ K₂.map (MulAut.conj c).toMonoidHom = K₁) := by
  have hcz : c * z * c⁻¹ = z := by
    have := mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = z * c * c⁻¹ := by rw [this]
      _ = z := by group
  have hCc : (Cz z).map (MulAut.conj c).toMonoidHom = Cz z := by
    rw [CFSG.GH74.GLS.Stage1.Thm2.Recip.map_centralizer_singleton_conj, hcz]
  have h1 := CFSG.GH74.GLS.Stage1.Thm2.Recip.isPCompIn_map_conj h.isPCompIn₁ c
  have h2 := CFSG.GH74.GLS.Stage1.Thm2.Recip.isPCompIn_map_conj h.isPCompIn₂ c
  rw [hCc] at h1 h2
  have hinj : K₁.map (MulAut.conj c).toMonoidHom ≠ K₂.map (MulAut.conj c).toMonoidHom := by
    intro heq
    exact h.ne (Subgroup.map_injective (MulAut.conj c).injective heq)
  rcases h.only _ h1 with e1 | e1 <;> rcases h.only _ h2 with e2 | e2
  · exact absurd (e1.trans e2.symm) hinj
  · exact Or.inl ⟨e1, e2⟩
  · exact Or.inr ⟨e1, e2⟩
  · exact absurd (e1.trans e2.symm) hinj

theorem mem_of_map {H H' : Subgroup G} {c : G} (e : H.map (MulAut.conj c).toMonoidHom = H') {a : G}
    (ha : a ∈ H) : c * a * c⁻¹ ∈ H' := by
  rw [← e]
  exact ⟨a, ha, by simp [MulAut.conj_apply]⟩

theorem perm' [Finite G] (h : LUComps G q z K₁ K₂) :
    ∀ c ∈ centralizer ({z} : Set G),
      ((∀ a ∈ K₁, c * a * c⁻¹ ∈ K₁) ∧ (∀ a ∈ K₂, c * a * c⁻¹ ∈ K₂)) ∨
      ((∀ a ∈ K₁, c * a * c⁻¹ ∈ K₂) ∧ (∀ a ∈ K₂, c * a * c⁻¹ ∈ K₁)) := by
  intro c hc
  rcases h.perm hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨fun a ha => mem_of_map e1 ha, fun a ha => mem_of_map e2 ha⟩
  · exact Or.inr ⟨fun a ha => mem_of_map e1 ha, fun a ha => mem_of_map e2 ha⟩

theorem conj_sup_mem [Finite G] (h : LUComps G q z K₁ K₂) {c : G} (hc : c ∈ Cz z) {k : G}
    (hk : k ∈ K₁ ⊔ K₂) : c * k * c⁻¹ ∈ K₁ ⊔ K₂ := by
  have hle : (K₁ ⊔ K₂).map (MulAut.conj c).toMonoidHom ≤ K₁ ⊔ K₂ := by
    rw [Subgroup.map_sup]
    rcases h.perm hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, sup_comm]
  exact hle ⟨k, hk, by simp [MulAut.conj_apply]⟩

theorem pLayerOf_eq [Finite G] (h : LUComps G q z K₁ K₂) : pLayerOf 2 (Cz z) = K₁ ⊔ K₂ := by
  have hset : {L | IsPCompIn 2 (Cz z) L} = {K₁, K₂} := by
    ext L
    constructor
    · intro hL; exact h.only L hL
    · rintro (rfl | rfl)
      · exact h.isPCompIn₁
      · exact h.isPCompIn₂
  unfold pLayerOf
  rw [hset, sSup_pair]

end LUComps

theorem mem_normalizer_pPrimeCoreOf {X : Subgroup G} {c : G} (hc : c ∈ X) :
    c ∈ normalizer ((pPrimeCoreOf 2 X : Subgroup G) : Set G) := by
  have hN : (pPrimeCore 2 ↥X).Normal := inferInstance
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    exact Subgroup.mem_map.mpr ⟨⟨c, hc⟩ * a' * ⟨c, hc⟩⁻¹, hN.conj_mem a' ha' ⟨c, hc⟩, rfl⟩
  · intro ha
    obtain ⟨a', ha', hae⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr ⟨⟨c, hc⟩⁻¹ * a' * ⟨c, hc⟩, ?_, ?_⟩
    · simpa using hN.conj_mem a' ha' ⟨c, hc⟩⁻¹
    · have : (a' : G) = c * a * c⁻¹ := hae
      show (c⁻¹ * (a' : G) * c) = a
      rw [this]; group

theorem odd_orderOf_A0 [Finite G] {z : G} {a : G} (ha : a ∈ A0 z) : Odd (orderOf a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(Cz z))) := pPrimeCore_coprime_card
  have hd : orderOf a' ∣ Nat.card (pPrimeCore 2 ↥(Cz z)) := Subgroup.orderOf_dvd_natCard _ ha'
  have hodd : Odd (orderOf a') :=
    Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right hd hcop)
  have h2 : orderOf ((a' : ↥(Cz z)) : G) = orderOf a' := Subgroup.orderOf_coe _
  rw [show ((Cz z).subtype a' : G) = ((a' : ↥(Cz z)) : G) from rfl, h2]
  exact hodd

theorem coprime_card_A0 [Finite G] (z : G) : Nat.Coprime 2 (Nat.card (A0 z)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(Cz z))) := pPrimeCore_coprime_card
  have : Nat.card (A0 z) = Nat.card (pPrimeCore 2 ↥(Cz z)) :=
    (Nat.card_congr ((pPrimeCore 2 ↥(Cz z)).equivMapOfInjective (Cz z).subtype
      (Cz z).subtype_injective).toEquiv).symm
  rw [this]; exact hcop

namespace LUComps

variable {q : ℕ} {z : G} {K₁ K₂ : Subgroup G}

theorem le_centralizer_A0 [Finite G] (h : LUComps G q z K₁ K₂) [IsCyclic ↥(A0 z)] :
    K₁ ⊔ K₂ ≤ centralizer ((A0 z : Subgroup G) : Set G) := by
  have hN : ∀ K : Subgroup G, K ≤ Cz z → K ≤ normalizer ((A0 z : Subgroup G) : Set G) :=
    fun K hK k hk => mem_normalizer_pPrimeCoreOf (hK hk)
  exact sup_le (perfect_le_centralizer_of_cyclic h.perfect₁ (hN K₁ h.comp₁.1))
    (perfect_le_centralizer_of_cyclic h.perfect₂ (hN K₂ h.comp₂.1))

theorem swap_of_not_normalizer [Finite G] (h : LUComps G q z K₁ K₂) {c : G} (hc : c ∈ Cz z)
    (hn : c ∉ normalizer (K₁ : Set G)) :
    K₁.map (MulAut.conj c).toMonoidHom = K₂ ∧ K₂.map (MulAut.conj c).toMonoidHom = K₁ := by
  rcases h.perm hc with ⟨e1, _⟩ | h2
  · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr e1) hn
  · exact h2

theorem card_eq [Finite G] (h : LUComps G q z K₁ K₂) {c : G} (hc : c ∈ Cz z)
    (hn : c ∉ normalizer (K₁ : Set G)) : Nat.card K₁ = Nat.card K₂ := by
  rw [← (h.swap_of_not_normalizer hc hn).1]
  exact (card_map_conj K₁ c).symm

theorem le_normalizer₁ [Finite G] (h : LUComps G q z K₁ K₂) : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set G) := by
  refine sup_le Subgroup.le_normalizer (fun b hb => ?_)
  have : b ∈ centralizer (K₁ : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact h.comm a ha b hb
  exact Subgroup.centralizer_le_normalizer (K₁ : Set G) this

theorem z_mem_normalizer₁ (h : LUComps G q z K₁ K₂) :
    z ∈ normalizer (K₁ : Set G) := by
  have : z ∈ centralizer (K₁ : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact h.cz₁ ha
  exact Subgroup.centralizer_le_normalizer (K₁ : Set G) this

end LUComps

namespace LUSyl

variable {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}

theorem comm_z (h : LUSyl G z S K₁ K₂ t u) {s : G} (hs : s ∈ (S : Subgroup G)) : s * z = z * s := by
  have hz : z ∈ (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype := by
    rw [h.z_cen]; exact mem_zpowers z
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
  have h1 := Subgroup.mem_center_iff.mp hy ⟨s, hs⟩
  have h3 : s * (y : G) = (y : G) * s := congrArg Subtype.val h1
  have h4 : (y : G) = z := hyz
  rw [h4] at h3
  exact h3

theorem z_mem (h : LUSyl G z S K₁ K₂ t u) : z ∈ (S : Subgroup G) := by
  have hz : z ∈ (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype := by
    rw [h.z_cen]; exact mem_zpowers z
  obtain ⟨y, -, hyz⟩ := Subgroup.mem_map.mp hz
  rw [← hyz]; exact y.2

theorem S_le_Cz (h : LUSyl G z S K₁ K₂ t u) : (S : Subgroup G) ≤ Cz z := fun _ hs =>
  mem_centralizer_singleton_iff.mpr (h.comm_z hs)

theorem z_sq (h : LUSyl G z S K₁ K₂ t u) : z * z = 1 := by
  have : z ^ 2 = 1 := by rw [← h.z_inv]; exact pow_orderOf_eq_one z
  rwa [pow_two] at this

theorem z_ne_one (h : LUSyl G z S K₁ K₂ t u) : z ≠ 1 := by
  intro hz
  have := h.z_inv
  rw [hz, orderOf_one] at this
  omega

theorem cs_inv (h : LUSyl G z S K₁ K₂ t u) {s : G} (hs : s ∈ (S : Subgroup G))
    (hc : ∀ k ∈ K₁ ⊔ K₂, s * k = k * s) (h2 : s * s = 1) : s = 1 ∨ s = z := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (h.cs s hs hc)
  have hmod : z ^ (i % 2) = z ^ i := by
    have := zpow_mod_orderOf z i
    rwa [h.z_inv, Nat.cast_ofNat] at this
  rw [← hmod]
  rcases Int.emod_two_eq_zero_or_one i with h0 | h1
  · left; rw [h0]; simp
  · right; rw [h1]; simp

end LUSyl

theorem not_prime_ordBC_two {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q) : ¬ (CFSG.Open.ordBC 2 q).Prime := by
  intro hp
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  have hq1 : 2 ∣ q ^ (2 * 1) - 1 := by
    have : Odd (q ^ (2 * 1)) := hq.pow
    have := (Nat.odd_iff.mp this)
    omega
  obtain ⟨k, hk⟩ := hq1
  have hg : Nat.gcd 2 (q - 1) = 2 := by
    apply Nat.gcd_eq_left
    obtain ⟨m, hm⟩ := hq
    omega
  have hord : CFSG.Open.ordBC 2 q = q ^ 4 * (k * (q ^ 4 - 1)) := by
    unfold CFSG.Open.ordBC
    rw [h1, Finset.prod_pair (by norm_num), hg, hk]
    have : q ^ (2 * 2) = q ^ 4 := by norm_num
    rw [this]
    have h2 : q ^ 4 * (2 * k * (q ^ 4 - 1)) = 2 * (q ^ 4 * (k * (q ^ 4 - 1))) := by ring
    rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]
  have hqq : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h5 2
  have hk2 : 2 ≤ k := by
    have : q ^ (2 * 1) = q ^ 2 := by norm_num
    rw [this] at hk
    omega
  have hq4 : 5 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left h5 4
  have hr : 2 ≤ q ^ 4 - 1 := by norm_num at hq4; omega
  have hdvd : q ^ 4 ∣ CFSG.Open.ordBC 2 q := ⟨_, hord⟩
  have hX : 1 < k * (q ^ 4 - 1) := by
    calc 1 < 2 * 2 := by norm_num
      _ ≤ k * (q ^ 4 - 1) := Nat.mul_le_mul hk2 hr
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · norm_num at hq4; omega
  · rw [hord] at h
    have h' : q ^ 4 * 1 = q ^ 4 * (k * (q ^ 4 - 1)) := by rw [mul_one]; exact h
    have := Nat.eq_of_mul_eq_mul_left (show 0 < q ^ 4 by positivity) h'
    omega

theorem not_comm_of_lieModel_psp
    {N : Type} [Group N] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (h : CFSG.Blueprint.LieModel N CFSG.Assembly.LowTwoRank.StatedLieTag.PSp 2 p f) :
    ∃ a b : N, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsSimpleGroup N :=
    (CFSG.LieType.Catalog.lieModel_finite_simple N _ 2 p f h).2.2
  let _ : CommGroup N := { ‹Group N› with mul_comm := fun a b => hcon a b }
  have hprime := IsSimpleGroup.prime_card (α := N)
  rw [natCard_of_lieModel_psp hp2 h] at hprime
  exact not_prime_ordBC_two ((hp.odd_of_ne_two hp2).pow) hq hprime

theorem hmax_of_6A
    [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {z : G} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h6A : MaxOverCentralizerPSp4 z p f) {Y : Subgroup G} (hY : Y ≠ ⊥)
    (hYr : ∃ r : ℕ, r.Prime ∧ IsPGroup r Y) (hCY : Cz z ≤ normalizer (Y : Set G)) :
    normalizer (Y : Set G) = Cz z := by
  by_contra hne
  obtain ⟨r, hr, hYp⟩ := hYr
  have : Fact r.Prime := ⟨hr⟩
  set N : Subgroup G := normalizer (Y : Set G) with hN
  have hCN : Cz z < N := lt_of_le_of_ne hCY (Ne.symm hne)
  have hNtop : N ≠ ⊤ := by
    intro h
    have hnorm : Y.Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases hG.eq_bot_or_eq_top_of_normal Y with h1 | h1
    · exact hY h1
    · have hGp : IsPGroup r G := by
        have h2 : IsPGroup r (⊤ : Subgroup G) := h1 ▸ hYp
        exact IsPGroup.of_surjective h2 (Subgroup.topEquiv (G := G)).toMonoidHom
          (Subgroup.topEquiv (G := G)).surjective
      have : Group.IsNilpotent G := hGp.isNilpotent
      have : IsSimpleGroup G := hG
      have : IsCyclic G := inferInstance
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((IsCyclic.isMulCommutative (α := G)).is_comm.comm a b)
  obtain ⟨M, hMc, hNM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom N).resolve_left hNtop
  have hCM : Cz z < M := lt_of_lt_of_le hCN hNM
  obtain ⟨hmax, hFM⟩ := h6A M hMc hCM
  have hlt : (Cz z).subgroupOf M < N.subgroupOf M := by
    refine lt_of_le_of_ne (Subgroup.subgroupOf_mono M hCN.le) fun h => ?_
    have h' := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hCM.le, inf_eq_left.mpr hNM] at h'
    exact hCN.ne h'
  have hMN : M ≤ N := Subgroup.subgroupOf_eq_top.mp (hmax.2 _ hlt)
  have hYM : Y ≤ M := (Subgroup.le_normalizer : Y ≤ N).trans hNM
  have hYnorm : (Y.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr hMN
  have hY'p : IsPGroup r ↥(Y.subgroupOf M) :=
    hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYM).symm
  have hY'ne : Y.subgroupOf M ≠ ⊥ := by
    intro hbot
    apply hY
    rw [eq_bot_iff]
    intro y hy
    have hy' : (⟨y, hYM hy⟩ : ↥M) ∈ Y.subgroupOf M := hy
    rw [hbot, Subgroup.mem_bot] at hy'
    have := congrArg Subtype.val hy'
    simpa using this
  set Φ : Subgroup ↥M := CFSG.fittingSubgroup ↥M with hΦ
  set N₀ : Subgroup ↥M := CFSG.generalizedFitting ↥M with hN₀
  have hΦN₀ : Φ ≤ N₀ := le_sup_left
  have hY'Φ : Y.subgroupOf M ≤ Φ :=
    (le_sSup ⟨hYnorm, hY'p⟩ : Y.subgroupOf M ≤ CFSG.pCore r ↥M).trans
      (CFSG.pCore_le_fitting ↥M r)
  have hsimple : IsSimpleGroup ↥N₀ :=
    (CFSG.LieType.Catalog.lieModel_finite_simple _ _ 2 p f hFM).2.2
  have hnc := not_comm_of_lieModel_psp hp hp2 hq hFM
  have : (Φ.subgroupOf N₀).Normal := inferInstance
  rcases hsimple.eq_bot_or_eq_top_of_normal (Φ.subgroupOf N₀) with h0 | h1
  · apply hY'ne
    rw [eq_bot_iff]
    intro x hx
    have hxΦ : x ∈ Φ := hY'Φ hx
    have hx' : (⟨x, hΦN₀ hxΦ⟩ : ↥N₀) ∈ Φ.subgroupOf N₀ := hxΦ
    rw [h0, Subgroup.mem_bot] at hx'
    have := congrArg Subtype.val hx'
    simpa using this
  · have hle : N₀ ≤ Φ := Subgroup.subgroupOf_eq_top.mp h1
    have : Group.IsNilpotent ↥(N₀.subgroupOf Φ) := inferInstance
    have : Group.IsNilpotent ↥N₀ := Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle)
    have : Group.IsSolvable ↥N₀ := inferInstance
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := ↥N₀)).mpr inferInstance a b)

theorem hCK_of_syl [Finite G] {q : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
    (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) :
    ∀ s : G, s * s = 1 → s * z = z * s → (∀ k ∈ K₁ ⊔ K₂, s * k = k * s) → s = 1 ∨ s = z := by
  intro s hs2 hsz hsK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsC : s ∈ Cz z := mem_centralizer_singleton_iff.mpr hsz
  have hord : ∃ n : ℕ, orderOf s = 2 ^ n := by
    have h2 : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hs2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  obtain ⟨c, hcC, hcs⟩ := exists_conj_mem_sylow_of_le S hs.S_le_Cz hsC hord
  have hs'2 : (c⁻¹ * s * c) * (c⁻¹ * s * c) = 1 := by
    calc (c⁻¹ * s * c) * (c⁻¹ * s * c) = c⁻¹ * (s * s) * c := by group
      _ = 1 := by rw [hs2]; group
  have hs'K : ∀ k ∈ K₁ ⊔ K₂, (c⁻¹ * s * c) * k = k * (c⁻¹ * s * c) := by
    intro k hk
    have hk' := hc.conj_sup_mem hcC hk
    have := hsK _ hk'
    calc (c⁻¹ * s * c) * k = c⁻¹ * (s * (c * k * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * k * c⁻¹) * s) * c := by rw [this]
      _ = k * (c⁻¹ * s * c) := by group
  rcases hs.cs_inv hcs hs'K hs'2 with h1 | h1
  · left
    have : s = c * (c⁻¹ * s * c) * c⁻¹ := by group
    rw [this, h1]; group
  · right
    have hcz : c * z * c⁻¹ = z := by
      have := mem_centralizer_singleton_iff.mp hcC
      calc c * z * c⁻¹ = z * c * c⁻¹ := by rw [this]
        _ = z := by group
    have : s = c * (c⁻¹ * s * c) * c⁻¹ := by group
    rw [this, h1, hcz]

theorem diag_le_cj [Finite G] {q : ℕ} {z t g : G} {K₁ K₂ : Subgroup G}
    (h : LUComps G q z K₁ K₂) (hz : orderOf z = 2) (ht2 : t * t = 1) (hzt : z * t = t * z)
    (hg : g⁻¹ * z * g = t) (hts₁ : ∀ k ∈ K₁, t * k * t⁻¹ ∈ K₂)
    (hts₂ : ∀ k ∈ K₂, t * k * t⁻¹ ∈ K₁) :
    (diagHom K₁ K₂ t h.comm hts₁).range ≤ cj K₁ g ⊔ cj K₂ g := by
  set D := (diagHom K₁ K₂ t h.comm hts₁).range with hD
  set X : Subgroup G := Cz z ⊓ Cz t with hX
  have hz2 : z * z = 1 := by
    have : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    rwa [pow_two] at this
  have htzt : t * z * t⁻¹ = z := by
    calc t * z * t⁻¹ = z * t * t⁻¹ := by rw [hzt]
      _ = z := by group
  have hta : ∀ k : G, t * (t * k * t⁻¹) * t⁻¹ = k := by
    intro k
    calc t * (t * k * t⁻¹) * t⁻¹ = (t * t) * k * (t * t)⁻¹ := by group
      _ = k := by rw [ht2]; group
  have hDmem : ∀ d ∈ D, ∃ k ∈ K₁, d = k * (t * k * t⁻¹) := by
    intro d hd
    obtain ⟨k, rfl⟩ := hd
    exact ⟨k, k.2, rfl⟩
  have hDX : D ≤ X := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := hDmem d hd
    refine ⟨mem_centralizer_singleton_iff.mpr ?_, mem_centralizer_singleton_iff.mpr ?_⟩
    · have h1 := h.cz₁ hk
      have h2 := h.cz₂ (hts₁ k hk)
      calc k * (t * k * t⁻¹) * z = k * ((t * k * t⁻¹) * z) := by group
        _ = k * (z * (t * k * t⁻¹)) := by rw [h2]
        _ = (k * z) * (t * k * t⁻¹) := by group
        _ = z * k * (t * k * t⁻¹) := by rw [h1]
        _ = z * (k * (t * k * t⁻¹)) := by group
    · have hc := h.comm k hk _ (hts₁ k hk)
      have e1 : t * (k * (t * k * t⁻¹)) * t⁻¹ = (t * k * t⁻¹) * (t * (t * k * t⁻¹) * t⁻¹) := by
        group
      rw [hta k] at e1
      have e2 : t * (k * (t * k * t⁻¹)) * t⁻¹ = k * (t * k * t⁻¹) := by rw [e1, ← hc]
      calc k * (t * k * t⁻¹) * t = (t * (k * (t * k * t⁻¹)) * t⁻¹) * t := by rw [e2]
        _ = t * (k * (t * k * t⁻¹)) := by group
  have hDnorm : (D.subgroupOf X).Normal := by
    refine ⟨fun n hn g' => ?_⟩
    have hn' : (n : G) ∈ D := hn
    obtain ⟨k, hk, hnk⟩ := hDmem _ hn'
    have hgz : (g' : G) ∈ Cz z := g'.2.1
    have hgt : (g' : G) * t = t * (g' : G) := mem_centralizer_singleton_iff.mp g'.2.2
    have hgt' : (g' : G) * t * (g' : G)⁻¹ = t := by rw [hgt]; group
    have key : ∀ x : G, (g' : G) * (t * x * t⁻¹) * (g' : G)⁻¹ =
        t * ((g' : G) * x * (g' : G)⁻¹) * t⁻¹ := by
      intro x
      calc (g' : G) * (t * x * t⁻¹) * (g' : G)⁻¹
          = ((g' : G) * t * (g' : G)⁻¹) * ((g' : G) * x * (g' : G)⁻¹) *
              (((g' : G) * t * (g' : G)⁻¹))⁻¹ := by group
        _ = t * ((g' : G) * x * (g' : G)⁻¹) * t⁻¹ := by rw [hgt']
    show (g' : G) * (n : G) * (g' : G)⁻¹ ∈ D
    rw [hnk]
    have hsplit : (g' : G) * (k * (t * k * t⁻¹)) * (g' : G)⁻¹ =
        ((g' : G) * k * (g' : G)⁻¹) * (t * ((g' : G) * k * (g' : G)⁻¹) * t⁻¹) := by
      calc (g' : G) * (k * (t * k * t⁻¹)) * (g' : G)⁻¹
          = ((g' : G) * k * (g' : G)⁻¹) * ((g' : G) * (t * k * t⁻¹) * (g' : G)⁻¹) := by group
        _ = _ := by rw [key k]
    rw [hsplit]
    rcases h.perm' _ hgz with ⟨hf1, hf2⟩ | ⟨hs1, hs2⟩
    · exact ⟨⟨_, hf1 k hk⟩, rfl⟩
    · have hk₂ : (g' : G) * k * (g' : G)⁻¹ ∈ K₂ := hs1 k hk
      have hk₁ : t * ((g' : G) * k * (g' : G)⁻¹) * t⁻¹ ∈ K₁ := hts₂ _ hk₂
      have hc := h.comm _ hk₁ _ hk₂
      refine ⟨⟨_, hk₁⟩, ?_⟩
      change (t * ((g' : G) * k * (g' : G)⁻¹) * t⁻¹) *
          (t * (t * ((g' : G) * k * (g' : G)⁻¹) * t⁻¹) * t⁻¹) =
        ((g' : G) * k * (g' : G)⁻¹) * (t * ((g' : G) * k * (g' : G)⁻¹) * t⁻¹)
      rw [hta]
      exact hc
  have hDq : CFSG.IsQuasisimple ↥D := by
    obtain ⟨e⟩ := diagHom_range_equiv h.comm hts₁ hz2 htzt h.inf_eq h.cen₁
    have : IsSimpleGroup ↥D := (MulEquiv.isSimpleGroup_congr e).mp h.quasi₁.2.1
    refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := ↥D) ?_).1
    obtain ⟨a, b, hab⟩ := h.quasi₁.2.2
    exact ⟨e a, e b, fun hh => hab (e.injective (by rw [map_mul, map_mul]; exact hh))⟩
  have hcomp : CFSG.IsComponent (D.subgroupOf X) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDX).symm hDq,
      hDnorm.isSubnormal⟩
  have hDc : IsPCompIn 2 X D :=
    ⟨hDX, CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hcomp⟩
  have hbal := CFSG.GH74.GLS.Stage1.Thm2.Recip.le_pLayerOf_of_isPCompIn_inf hz
    (mem_centralizer_singleton_iff.mpr hzt) hDc
  have hCt : Cz t = (Cz z).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [CFSG.GH74.GLS.Stage1.Thm2.Recip.map_centralizer_singleton_conj, inv_inv, hg]
  have hpl : pLayerOf 2 (Cz t) = cj K₁ g ⊔ cj K₂ g := by
    rw [hCt, CFSG.GH74.GLS.Stage1.Thm3.Sec4.pLayerOf_cmap g⁻¹ (Cz z), h.pLayerOf_eq]
    show (K₁ ⊔ K₂).map (MulAut.conj g⁻¹).toMonoidHom = _
    rw [Subgroup.map_sup]
    rfl
  exact hbal.trans hpl.le

theorem lemma62a
    [Finite G] {q p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq5 : 5 ≤ p ^ f) (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u)
    [IsCyclic ↥(A0 z)] (h6A : MaxOverCentralizerPSp4 z p f)
    {t₀ : G} (ht₀S : t₀ ∈ (S : Subgroup G)) (ht₀n : t₀ ∉ normalizer (K₁ : Set G))
    (ht₀c : IsConj z t₀) : ∀ a ∈ A0 z, t₀ * a * t₀⁻¹ = a⁻¹ := by
  have hz := hs.z_inv
  have hz2 := hs.z_sq
  have hz1 := hs.z_ne_one
  have ht₀C : t₀ ∈ Cz z := hs.S_le_Cz ht₀S
  have hzt : z * t₀ = t₀ * z := (hs.comm_z ht₀S).symm
  obtain ⟨c, hcz⟩ := isConj_iff.mp ht₀c
  have ht₀2 : t₀ * t₀ = 1 := by
    rw [← hcz]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hg : c⁻¹⁻¹ * z * c⁻¹ = t₀ := by rw [inv_inv]; exact hcz
  obtain ⟨hsw1, hsw2⟩ := hc.swap_of_not_normalizer ht₀C ht₀n
  have hts₁ : ∀ k ∈ K₁, t₀ * k * t₀⁻¹ ∈ K₂ := fun k hk => LUComps.mem_of_map hsw1 hk
  have hts₂ : ∀ k ∈ K₂, t₀ * k * t₀⁻¹ ∈ K₁ := fun k hk => LUComps.mem_of_map hsw2 hk
  have htz : t₀ ≠ z := fun h => ht₀n (by rw [h]; exact hc.z_mem_normalizer₁)
  have hKcard : Nat.card K₁ = Nat.card K₂ := hc.card_eq ht₀C ht₀n
  have hKsup : Nat.card ↥(K₁ ⊔ K₂) * 2 = Nat.card K₁ * Nat.card K₂ := by
    have h1 := card_sup_mul_card_inf_of_commute hc.comm
    rw [hc.inf_eq, Nat.card_zpowers, hz] at h1
    exact h1
  have hA₀n : ∀ c ∈ centralizer ({z} : Set G), c ∈ normalizer ((A0 z : Subgroup G) : Set G) :=
    fun c hcc => mem_normalizer_pPrimeCoreOf hcc
  have hDJ := diag_le_cj hc hz ht₀2 hzt hg hts₁ hts₂
  have hmax : ∀ Y : Subgroup G, Y ≠ ⊥ → (∃ r : ℕ, r.Prime ∧ IsPGroup r Y) →
      centralizer ({z} : Set G) ≤ normalizer (Y : Set G) →
        normalizer (Y : Set G) = centralizer ({z} : Set G) :=
    fun Y hY hYr hCY => hmax_of_6A hG hnab hp hp2 hq5 h6A hY hYr hCY
  have hfix : ∀ a ∈ A0 z, t₀ * a * t₀⁻¹ = a → a = 1 := by
    intro a ha hfx
    refine lemma62a_math (z := z) (t := t₀) (g := c⁻¹) (K₁ := K₁) (K₂ := K₂) (A₀ := A0 z)
      hz2 hz1 htz hzt hg (fun k hk => hc.cz₁ hk) (fun k hk => hc.cz₂ hk) hc.perfect₁ hc.perfect₂
      hc.comm hc.inf_eq hKcard hKsup hts₁ hc.perm' hc.cen₁ hc.quasi₁.2.1 hA₀n
      (fun a ha => odd_orderOf_A0 ha) hDJ hmax (hCK_of_syl hc hs) a ha ?_
    calc a * t₀ = (t₀ * a * t₀⁻¹) * t₀ := by rw [hfx]
      _ = t₀ * a := by group
  have hAc : ∀ a ∈ A0 z, ∀ b ∈ A0 z, a * b = b * a := by
    intro a ha b hb
    have := (IsCyclic.isMulCommutative (α := ↥(A0 z))).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have htn : ∀ a ∈ A0 z, t₀ * a * t₀⁻¹ ∈ A0 z := fun a ha =>
    (mem_normalizer_iff.mp (mem_normalizer_pPrimeCoreOf ht₀C) a).mp ha
  exact inverts_of_fixed_eq_bot ht₀2 hAc htn hfix

theorem lemma62b
    [Finite G] {q p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq5 : 5 ≤ p ^ f) (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u)
    [IsCyclic ↥(A0 z)] (h6A : MaxOverCentralizerPSp4 z p f) :
    ∀ a ∈ A0 z, u * a * u⁻¹ = a := by
  have htn : t ∉ normalizer (K₁ : Set G) := by
    intro hn
    apply hc.ne
    rw [← hs.t_swap]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp hn).symm
  have ht : ∀ a ∈ A0 z, t * a * t⁻¹ = a⁻¹ :=
    lemma62a hG hnab hp hp2 hq5 hc hs h6A hs.t_mem htn hs.t_conj
  have hutn : u * t ∉ normalizer (K₁ : Set G) := by
    intro hn
    apply htn
    have : t = u⁻¹ * (u * t) := by group
    rw [this]
    exact mul_mem (inv_mem hs.u_norm) hn
  obtain ⟨q', hq', hq'c⟩ := hs.coset (u * t) (mul_mem hs.u_mem hs.t_mem) hutn
  have hq'N : q' ∈ normalizer (K₁ : Set G) := hc.le_normalizer₁ hq'.2
  have ht₀n : q' * (u * t) ∉ normalizer (K₁ : Set G) := by
    intro hn
    apply hutn
    have : u * t = q'⁻¹ * (q' * (u * t)) := by group
    rw [this]
    exact mul_mem (inv_mem hq'N) hn
  have ht₀ : ∀ a ∈ A0 z, (q' * (u * t)) * a * (q' * (u * t))⁻¹ = a⁻¹ :=
    lemma62a hG hnab hp hp2 hq5 hc hs h6A (mul_mem hq'.1 (mul_mem hs.u_mem hs.t_mem)) ht₀n hq'c
  have hq : ∀ a ∈ A0 z, q' * a * q'⁻¹ = a := by
    intro a ha
    have h1 := mem_centralizer_iff.mp (hc.le_centralizer_A0 hq'.2) a ha
    calc q' * a * q'⁻¹ = a * q' * q'⁻¹ := by rw [h1]
      _ = a := by group
  exact lemma62b_core hq ht ht₀ (by rw [mul_assoc])

@[expose] def Fstar (S K₁ K₂ : Subgroup G) (u : G) : Subgroup G :=
  pPrimeCoreOf 2 (centralizer ((S ⊓ (K₁ ⊔ K₂) ⊔ zpowers u : Subgroup G) : Set G))

theorem lemma62c
    [Finite G] {q p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq5 : 5 ≤ p ^ f) (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u)
    [IsCyclic ↥(A0 z)] (h6A : MaxOverCentralizerPSp4 z p f) :
    A0 z ≤ Fstar (S : Subgroup G) K₁ K₂ u := by
  have hb := lemma62b hG hnab hp hp2 hq5 hc hs h6A
  set Qu : Subgroup G := (S : Subgroup G) ⊓ (K₁ ⊔ K₂) ⊔ zpowers u with hQu
  set M : Subgroup G := centralizer (Qu : Set G) with hM
  have hQuA : Qu ≤ centralizer ((A0 z : Subgroup G) : Set G) := by
    refine sup_le (inf_le_right.trans hc.le_centralizer_A0) ?_
    rw [zpowers_le]
    rw [mem_centralizer_iff]
    intro a ha
    have h1 := hb a ha
    calc a * u = (u * a * u⁻¹) * u := by rw [h1]
      _ = u * a := by group
  have hAM : A0 z ≤ M := by
    intro a ha
    show a ∈ centralizer (Qu : Set G)
    rw [mem_centralizer_iff]
    intro x hx
    exact (mem_centralizer_iff.mp (hQuA hx) a ha).symm
  have hzQ : z ∈ Qu :=
    Subgroup.mem_sup_left (show z ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂) from
      ⟨hs.z_mem, (le_sup_left : K₁ ≤ K₁ ⊔ K₂) hc.z_mem₁⟩)
  have hMC : M ≤ Cz z := by
    intro x hx
    have h1 := mem_centralizer_iff.mp hx z hzQ
    exact mem_centralizer_singleton_iff.mpr h1.symm
  have hnorm : ((A0 z).subgroupOf M).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ A0 z := hn
    exact (mem_normalizer_iff.mp (mem_normalizer_pPrimeCoreOf (hMC g.2)) (n : G)).mp hn'
  have hcop : Nat.Coprime 2 (Nat.card ↥((A0 z).subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]
    exact coprime_card_A0 z
  have hle : (A0 z).subgroupOf M ≤ pPrimeCore 2 ↥M := le_sSup ⟨hnorm, hcop⟩
  intro a ha
  show a ∈ (pPrimeCore 2 ↥M).map M.subtype
  exact ⟨⟨a, hAM ha⟩, hle (show (⟨a, hAM ha⟩ : ↥M) ∈ (A0 z).subgroupOf M from ha), rfl⟩

end CFSG.GH74.GLS.LU.Local
