module

public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

open Subgroup
open scoped Pointwise

variable {X : Type*} [Group X]

theorem index_two_facts [Finite X] {K H : Subgroup X} (hKH : K ≤ H)
    (hcard : Nat.card H = 2 * Nat.card K) :
    (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) ∧
      (∀ a ∈ H, ∀ b ∈ H, a ∉ K → b ∉ K → a⁻¹ * b ∈ K) ∧ ⁅H, H⁆ ≤ K := by
  have hidx : (K.subgroupOf H).index = 2 := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf H)
    rw [Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv, hcard] at h1
    have hpos : 0 < Nat.card K := Nat.card_pos
    nlinarith
  have hmem : ∀ a : H, a ∈ K.subgroupOf H ↔ (a : X) ∈ K := fun a => mem_subgroupOf
  refine ⟨fun h hh k hk => ?_, fun a ha b hb haK hbK => ?_, ?_⟩
  · have hn := Subgroup.normal_of_index_eq_two hidx
    have := hn.conj_mem ⟨k, hKH hk⟩ ((hmem _).2 hk) ⟨h, hh⟩
    exact (hmem _).1 this
  · have := (mul_mem_iff_of_index_two hidx (a := (⟨a, ha⟩ : H)⁻¹) (b := ⟨b, hb⟩)).2
      ⟨fun h => absurd ((hmem _).1 (by simpa using inv_mem h)) haK,
        fun h => absurd ((hmem _).1 h) hbK⟩
    exact (hmem _).1 this
  · rw [commutator_le]
    intro a ha b hb
    set a' : H := ⟨a, ha⟩
    set b' : H := ⟨b, hb⟩
    have key : a' * b' * a'⁻¹ * b'⁻¹ ∈ K.subgroupOf H := by
      rw [mul_mem_iff_of_index_two hidx, mul_mem_iff_of_index_two hidx,
        mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
      tauto
    have := (hmem _).1 key
    simpa [commutatorElement_def] using this

theorem exists_conj_mem_of_index_two [Finite X] (hperf : commutator X = ⊤) (T : Sylow 2 X)
    {K : Subgroup X} (hKT : K ≤ T) (hcard : Nat.card T = 2 * Nat.card K) {g : X}
    (hgT : g ∈ T) (hgK : g ∉ K) (hg : orderOf g = 2) : ∃ a : X, a⁻¹ * g * a ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKn, hcos, habel⟩ := index_two_facts hKT hcard
  by_contra hne
  push Not at hne
  have hKn' : (K.subgroupOf (T : Subgroup X)).Normal := by
    rw [normal_subgroupOf_iff hKT]
    intro k h hk hh
    exact hKn h hh k hk
  have hindex : Nat.Coprime 2 (T : Subgroup X).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 T.not_dvd_index
  have hmain := CFSG.Quasithin.generalized_thompson_transfer_two hindex ⟨hKT, hKn'⟩ habel hgT
    hgK hg (fun a ha => hcos g hgT _ ha hgK (hne a))
  exact hmain (hperf ▸ mem_top g)

theorem exists_conj_mem_of_index_two_subgroup {G : Type*} [Group G] [Finite G]
    {A S K : Subgroup G} (hperf : ⁅A, A⁆ = A) (hSA : S ≤ A)
    (hS2 : Nat.Coprime 2 (S.relIndex A)) (hKS : K ≤ S) (hcard : Nat.card S = 2 * Nat.card K)
    {g : G} (hgS : g ∈ S) (hgK : g ∉ K) (hg : orderOf g = 2) :
    ∃ a ∈ A, a⁻¹ * g * a ∈ K := by
  obtain ⟨hKn, hcos, habel⟩ := index_two_facts hKS hcard
  by_contra hne
  push Not at hne
  have hmain := CFSG.Quasithin.generalized_thompson_transfer_two_subgroup hSA hS2 hKS hKn
    habel hgS hgK hg (fun a ha haS => hcos g hgS _ haS hgK (hne a ha))
  exact hmain (by rw [hperf]; exact hSA hgS)

theorem isWeaklyClosedIn_self [Finite X] {p : ℕ} (T : Sylow p X) :
    CFSG.Quasithin.IsWeaklyClosedIn (T : Subgroup X) T := by
  intro g hg
  refine Subgroup.eq_of_le_of_card_ge hg (le_of_eq ?_)
  rw [CFSG.Quasithin.conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

theorem exists_sq_of_conj_central [Finite X] (T : Sylow 2 X) {u v : X}
    (hu : u ∈ centralizer ((T : Subgroup X) : Set X))
    (hv : v ∈ centralizer ((T : Subgroup X) : Set X)) {g : X} (hg : g⁻¹ * u * g = v)
    {y : X} (hy : y ∈ T) (hvy : v = y ^ 2) : ∃ y' ∈ T, u = y' ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hnv⟩ := CFSG.Quasithin.burnside_fusion_lemma_centralizer T le_rfl
    (isWeaklyClosedIn_self T) hu hv hg
  refine ⟨n * y * n⁻¹, (mem_normalizer_iff.1 hn y).1 hy, ?_⟩
  rw [conj_pow, ← hvy, ← hnv]
  group

theorem false_of_abelian_sylow_fixed [Finite X] (hperf : commutator X = ⊤) (T : Sylow 2 X)
    (hT : IsMulCommutative (T : Subgroup X)) {e : X} (he : e ∈ T) (he1 : e ≠ 1)
    (hfix : ∀ n ∈ normalizer ((T : Subgroup X) : Set X), n * e * n⁻¹ = e) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : ∀ w ∈ (T : Subgroup X), w ∈ centralizer ((T : Subgroup X) : Set X) := by
    intro w hw
    rw [mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val (hT.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hindex : Nat.Coprime 2 (T : Subgroup X).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 T.not_dvd_index
  have hbot : ((⊥ : Subgroup X).subgroupOf (T : Subgroup X)).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  have habel : ⁅(T : Subgroup X), (T : Subgroup X)⁆ ≤ ⊥ := by
    rw [commutator_le]
    intro a ha b hb
    have hab := congrArg Subtype.val (hT.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    simp only [Subgroup.coe_mul] at hab
    rw [mem_bot, commutatorElement_def, hab]
    group
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨e, he⟩
  have hmain := CFSG.Quasithin.generalized_thompson_transfer_one (p := 2) hindex
    ⟨bot_le, hbot⟩ habel he (fun h => he1 ((mem_bot).1 h))
    ⟨k, by simpa using congrArg Subtype.val hk⟩ (fun m a ha => by
      have hem : e ^ m ∈ (T : Subgroup X) := zpow_mem he m
      obtain ⟨n, hn, hnv⟩ := CFSG.Quasithin.burnside_fusion_lemma_centralizer T le_rfl
        (isWeaklyClosedIn_self T) (hcent _ hem) (hcent _ ha) (g := a) rfl
      have hfix' : n⁻¹ * e * n = e := by
        have := hfix n⁻¹ (inv_mem hn)
        simpa using this
      have hfixm : n⁻¹ * e ^ m * n = e ^ m := by
        have h1 : n⁻¹ * e ^ m * n = (n⁻¹ * e * n⁻¹⁻¹) ^ m := by
          rw [conj_zpow, inv_inv]
        rw [h1, inv_inv, hfix']
      rw [mem_bot, ← hnv, hfixm, inv_mul_cancel])
  exact hmain (hperf ▸ mem_top e)

theorem card_le_four_of_involutions_mem [Finite X] {T V : Subgroup X} (hV4 : Nat.card V = 4)
    (hinv : ∀ g ∈ T, g ^ 2 = 1 → g ∈ V) (E : Subgroup X) (hET : E ≤ T)
    (hE : Assembly.IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  have hEV : E ≤ V := fun g hg => hinv g (hET hg) (hE.2 g hg)
  calc Nat.card E ≤ Nat.card V := Subgroup.card_le_of_le hEV
    _ = 4 := hV4

theorem twoRank_eq_two [Finite X] (T : Sylow 2 X) {V : Subgroup X}
    (hV : Assembly.IsElemAbelian 2 V) (hV4 : Nat.card V = 4)
    (hle : ∀ E : Subgroup X, E ≤ T → Assembly.IsElemAbelian 2 E → Nat.card E ≤ 4) :
    Assembly.twoRank X = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbdd : BddAbove {k | ∃ E : Subgroup X, E ≤ ⊤ ∧ Assembly.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro r ⟨E', -, -, hcard⟩
    have hle' := E'.card_le_card_group
    rw [hcard] at hle'
    exact (Nat.lt_two_pow_self (n := r)).le.trans hle'
  apply le_antisymm
  · apply csSup_le'
    rintro k ⟨E, -, hE, hcard⟩
    have hEp : IsPGroup 2 E := fun e => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hE.2 e e.2)⟩
    obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X T Q
    set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
    have hE'T : E' ≤ T := by
      rintro _ ⟨a, ha, rfl⟩
      have haQ : a ∈ MulAut.conj g • (T : Subgroup X) := hEQ ha
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haQ
      simpa [MulAut.smul_def] using haQ
    have hE'el : Assembly.IsElemAbelian 2 E' := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
      · obtain ⟨a', ha', ha'e⟩ := a.2
        obtain ⟨b', hb', hb'e⟩ := b.2
        have hc := congrArg Subtype.val (hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
        simp only [Subgroup.coe_mul] at hc ⊢
        rw [← ha'e, ← hb'e, ← map_mul, ← map_mul, hc]
      · rintro _ ⟨a, ha, rfl⟩
        rw [← map_pow, hE.2 a ha, map_one]
    have hcardE' : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have h4 := hle E' hE'T hE'el
    rw [hcardE', hcard] at h4
    have : k ≤ 2 := by
      by_contra hk
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact this
  · exact le_csSup hbdd ⟨V, le_top, hV, by rw [hV4]; norm_num⟩

end CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion
