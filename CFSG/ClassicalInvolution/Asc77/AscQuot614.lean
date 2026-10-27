module

public import CFSG.ClassicalInvolution.Asc77.AscQuot614Five

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace AscQuot

theorem map_conjSub {H : Type} [Group H] (φ : G →* H) (g : G) (K : Subgroup G) :
    (conjSub g K).map φ = conjSub (φ g) (K.map φ) := by
  ext y
  simp only [Subgroup.mem_map, mem_conjSub_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp [map_mul, map_inv]
  · rintro ⟨k, hk, hky⟩
    refine ⟨g * k * g⁻¹, ?_, ?_⟩
    · simpa [mul_assoc] using hk
    · rw [map_mul, map_mul, map_inv, hky]
      group

theorem orderOf_mk_eq {J X : Subgroup G} [X.Normal] (hJX : J ⊓ X = ⊥) {v : G} (hv : v ∈ J) :
    orderOf (QuotientGroup.mk' X v) = orderOf v := by
  have h1 := orderOf_injective (quotRestrict J X : ↥J →* ↥(J.map (QuotientGroup.mk' X)))
    (quotRestrict_injective hJX) ⟨v, hv⟩
  rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe] at h1
  exact h1

theorem isPGroup_zpowers_iff [Finite G] {J X : Subgroup G} [X.Normal] (hJX : J ⊓ X = ⊥) {v : G}
    (hv : v ∈ J) :
    IsPGroup 2 (Subgroup.zpowers (QuotientGroup.mk' X v)) ↔ IsPGroup 2 (Subgroup.zpowers v) := by
  have h := orderOf_mk_eq hJX hv
  constructor
  · intro hp2
    obtain ⟨n, hn⟩ := hp2.exists_card_eq
    rw [Nat.card_zpowers, h] at hn
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  · intro hp2
    obtain ⟨n, hn⟩ := hp2.exists_card_eq
    rw [Nat.card_zpowers] at hn
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, h, hn])

theorem isSubnormal_centralizer {H : Type} [Group H] {K : Subgroup H} {z : H}
    (hzc : ∀ w ∈ K, z * w = w * z)
    (hcomm : ∀ c : H, c * z = z * c → conjSub c K ≠ K → ⁅K, conjSub c K⁆ ≤ oddCoreOf K) :
    IsSubnormal K (Subgroup.centralizer ({z} : Set H)) := by
  set C : Subgroup H := Subgroup.centralizer ({z} : Set H) with hC
  set L : Subgroup H := ⨆ c : ↥C, conjSub (c : H) K with hL
  have hcC : ∀ c : H, c ∈ C ↔ c * z = z * c := fun c => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have hKL : K ≤ L := by
    have h1 : conjSub ((1 : ↥C) : H) K = K := conjSub_one K
    calc K = conjSub ((1 : ↥C) : H) K := h1.symm
      _ ≤ L := le_iSup (fun c : ↥C => conjSub (c : H) K) 1
  have hkeyK : ∀ c : H, c ∈ C → conjSub c K ≤ Subgroup.normalizer (K : Set H) := by
    intro c hc
    by_cases hcK : conjSub c K = K
    · rw [hcK]
      exact Subgroup.le_normalizer
    · exact le_normalizer_of_commutator_le_oddCoreOf
        (by rw [Subgroup.commutator_comm]; exact hcomm c ((hcC c).mp hc) hcK)
  have hLK : L ≤ Subgroup.normalizer (K : Set H) := iSup_le fun c => hkeyK c c.2
  have hkeyC : ∀ c : H, c ∈ C → conjSub c K ≤ C := by
    intro c hc y hy
    rw [mem_conjSub_iff] at hy
    have h2 : c * z = z * c := (hcC c).mp hc
    have h3 : c⁻¹ * z = z * c⁻¹ := by
      have h4 : c⁻¹ * (c * z) * c⁻¹ = c⁻¹ * (z * c) * c⁻¹ := by rw [h2]
      simpa [mul_assoc] using h4.symm
    have h1 := hzc _ hy
    rw [hcC]
    have hy' : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    rw [hy']
    calc c * (c⁻¹ * y * c) * c⁻¹ * z = c * (c⁻¹ * y * c) * (c⁻¹ * z) := by group
      _ = c * (c⁻¹ * y * c) * (z * c⁻¹) := by rw [h3]
      _ = c * ((c⁻¹ * y * c) * z) * c⁻¹ := by group
      _ = c * (z * (c⁻¹ * y * c)) * c⁻¹ := by rw [← h1]
      _ = (c * z) * (c⁻¹ * y * c) * c⁻¹ := by group
      _ = (z * c) * (c⁻¹ * y * c) * c⁻¹ := by rw [h2]
      _ = z * (c * (c⁻¹ * y * c) * c⁻¹) := by group
  have hLC : L ≤ C := iSup_le fun c => hkeyC c c.2
  have hCL : C ≤ Subgroup.normalizer (L : Set H) := by
    have hle : ∀ d : ↥C, conjSub (d : H) L ≤ L := by
      intro d
      have h1 : conjSub (d : H) L = ⨆ c : ↥C, conjSub (d : H) (conjSub (c : H) K) :=
        Subgroup.map_iSup _ _
      rw [h1]
      refine iSup_le fun c => ?_
      rw [← conjSub_mul]
      exact le_iSup (fun c : ↥C => conjSub (c : H) K) (d * c)
    intro d hd
    refine mem_normalizer_iff_conjSub_eq.mpr (le_antisymm (hle ⟨d, hd⟩) ?_)
    have h2 := hle ⟨d⁻¹, C.inv_mem hd⟩
    have h3 := conjSub_mono (n := d) h2
    rwa [conjSub_conjSub_inv] at h3
  exact IsSubnormal.step hKL ((Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr hLK)
    (IsSubnormal.step hLC ((Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr hCL)
      (IsSubnormal.refl C))

section Fields

variable [Finite G]

omit [Finite G] in
theorem conjInvariant_quot (hΩ : ConjInvariant Ω) (X : Subgroup G) [X.Normal] :
    ConjInvariant (Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω) := by
  rintro n _ ⟨K, hK, rfl⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective X n
  exact ⟨conjSub g K, hΩ g K hK, map_conjSub _ g K⟩

theorem classical_quot (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (h62 : L6_2On Ω)
    (X : Subgroup G) [X.Normal] (hRX : ∀ R ∈ RSet Ω, Commutes R X)
    (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) :
    ∀ L ∈ Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω,
      ∃ z : G ⧸ X, IsClassicalMember p f L z := by
  rintro _ ⟨K, hK, rfl⟩
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  have hz' := isUniqueInvolution_map_mk_of_odd (hXK K hK) hz
  obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hK
  obtain ⟨e'⟩ := nonempty_quotOddCoreEquiv (hXK K hK)
  refine ⟨QuotientGroup.mk' X z, ?_⟩
  refine
    { orderOf_eq_two := orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one
      mem := hz'.mem
      perfect := ?_
      subnormal := ?_
      nonempty_equiv := ⟨e'.symm.trans e⟩ }
  · have : Group.IsPerfect ↥K := hΩ.isPerfect hK
    exact Group.IsPerfect.ofSurjective (quotRestrict_surjective K X)
  refine isSubnormal_centralizer ?_ ?_
  · rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, hz.commute_of_mem hk]
  · intro c hc hne
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective X c
    rw [← map_conjSub] at hne ⊢
    have hJ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
    have hKJ : K ≠ conjSub g K := fun h => hne (by rw [← h])
    obtain ⟨h4, h4'⟩ := omega4_quot hp hq hΩ h62 X hRX hXK hK hJ hKJ
    have hzJ : QuotientGroup.mk' X z ∈ (conjSub g K).map (QuotientGroup.mk' X) := by
      have h1 : g * z * g⁻¹ ∈ conjSub g K := conj_mem_conjSub hz.mem
      refine ⟨g * z * g⁻¹, h1, ?_⟩
      rw [map_mul, map_mul, map_inv]
      rw [mul_inv_eq_iff_eq_mul]
      exact hc
    have hdvd : 2 ∣ Nat.card ↥(K.map (QuotientGroup.mk' X) ⊓
        (conjSub g K).map (QuotientGroup.mk' X)) := by
      have := Subgroup.orderOf_dvd_natCard
        (K.map (QuotientGroup.mk' X) ⊓ (conjSub g K).map (QuotientGroup.mk' X))
        (x := QuotientGroup.mk' X z) ⟨hz'.mem, hzJ⟩
      rwa [orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one] at this
    have h1 := one_le_padicValNat_of_dvd Nat.card_pos.ne' hdvd
    exact (h4' (le_antisymm h4 h1)).trans inf_le_left

theorem omega5_quot (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (h67 : L6_7On Ω)
    (h62 : L6_2On Ω) (h69 : L6_9On Ω) (h611 : L6_11On Ω) (X : Subgroup G) [X.Normal]
    (hRX : ∀ R ∈ RSet Ω, Commutes R X) (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) :
    ∀ L ∈ Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω,
      ∀ L' ∈ Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω, L ≠ L' →
        ∀ z : G ⧸ X, IsUniqueInvolution L z → ∀ v ∈ L',
          (¬ ∀ w ∈ L', v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
            v ∈ Subgroup.normalizer (L : Set (G ⧸ X)) := by
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne z' hz' _ ⟨v₀, hv₀J, rfl⟩ hvnc hv2 hcomm
  have hKJ : K ≠ J := fun h => hne (by rw [h])
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  have hz'eq : z' = QuotientGroup.mk' X z :=
    hz'.eq (isUniqueInvolution_map_mk_of_odd (hXK K hK) hz)
  have hv2a : IsPGroup 2 (Subgroup.zpowers
      (⟨QuotientGroup.mk' X v₀, Subgroup.mem_map_of_mem _ hv₀J⟩ :
        ↥(J.map (QuotientGroup.mk' X)))) := by
    obtain ⟨n, hn⟩ := hv2.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers]
    exact hn
  obtain ⟨v, hvb, hv2b⟩ := exists_isPGroup_zpowers_lift (quotRestrict J X)
    (quotRestrict_surjective J X) hv2a
  have hvc : QuotientGroup.mk' X (v : G) = QuotientGroup.mk' X v₀ := congrArg Subtype.val hvb
  have hv2c : IsPGroup 2 (Subgroup.zpowers (v : G)) := by
    obtain ⟨n, hn⟩ := hv2b.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ← Nat.card_zpowers]
    exact hn
  have hvnc' : ¬ ∀ w ∈ J, (v : G) * w = w * v := fun h => hvnc (by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hvc, ← map_mul, ← map_mul, h w hw])
  have hvz : QuotientGroup.mk' X (v : G) * QuotientGroup.mk' X z =
      QuotientGroup.mk' X z * QuotientGroup.mk' X (v : G) := by
    rw [hvc]
    exact hz'eq ▸ hcomm
  have hvz' : (v : G) * z = z * v :=
    commutes_of_quot hp hq hΩ h67 h62 h69 h611 X hRX hK hJ hKJ hz v.2 hvnc' hv2c hvz
  have hvK : (v : G) ∈ Subgroup.normalizer (K : Set G) :=
    hΩ.omega5 K hK J hJ hKJ z hz v v.2 hvnc' hv2c hvz'
  rw [← hvc, mem_normalizer_iff_conjSub_eq, ← map_conjSub,
    mem_normalizer_iff_conjSub_eq.mp hvK]

theorem quotient_hypOmega (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h67 : L6_7On Ω) (h62 : L6_2On Ω) (h69 : L6_9On Ω) (h611 : L6_11On Ω) (X : Subgroup G)
    [X.Normal] (hO : oddCoreOf X = ⊥) (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) :
    (∀ R ∈ RSet Ω, Commutes R X) ∧
      HypOmegaMod p f (Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω) := by
  have hRX : ∀ R ∈ RSet Ω, Commutes R X := fun R hR => commutes_of_mem_RSet hp hΩ h67 X hO hXK hR
  refine ⟨hRX, ?_⟩
  refine
    { conjInvariant := conjInvariant_quot hΩ.conjInvariant X
      classical := classical_quot hp hq hΩ h62 X hRX hXK
      omega4 := ?_
      omega5 := omega5_quot hp hq hΩ h67 h62 h69 h611 X hRX hXK }
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne
  exact omega4_quot hp hq hΩ h62 X hRX hXK hK hJ (fun h => hne (by rw [h]))

end Fields

end AscQuot

theorem l6_14' (h67 : L6_7 p f) (h62 : L6_2 p f) (h69 : L6_9 p f) (h611 : L6_11 p f) :
    L6_14' p f := by
  intro hp hq G _ _ Ω hΩ X _ hO hXK
  exact AscQuot.quotient_hypOmega hp hq hΩ (l6_7On_of_l6_7 h67 hp hq hΩ)
    (l6_2On_of_l6_2 h62 hp hq hΩ) (l6_9On_of_l6_9 h69 hp hq hΩ)
    (l6_11On_of_l6_11 h611 hp hq hΩ) X hO hXK

end CFSG.ClassicalInvolution.Asc77
