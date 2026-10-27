module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Basic
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619L32

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [Finite G] {M B H S K : Subgroup G} {z : G} {f : ↥K →* GL32}

private def fourVbar (S K : Subgroup G) (f : ↥K →* GL32) : Subgroup GL32 :=
  ((K ⊓ S).subgroupOf K).map f

omit [Finite G] in
private theorem mem_fourVbar {S K : Subgroup G} {f : ↥K →* GL32} {v : GL32} :
    v ∈ fourVbar S K f ↔ ∃ k : ↥K, (k : G) ∈ S ∧ f k = v := by
  unfold fourVbar
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨k.2, hk⟩), rfl⟩

private theorem four_isPGroup (h : Data619 M B H S K z f) : IsPGroup 2 (fourVbar S K f) := by
  have h1 : IsPGroup 2 ↥(K ⊓ S) := h.maxInv.1.2.1.to_le inf_le_right
  have h2 : IsPGroup 2 ↥((K ⊓ S).subgroupOf K) :=
    h1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ S ≤ K)).symm
  exact h2.map f

private theorem four_orderOf_l (h : Data619 M B H S K z f) :
    orderOf (f ⟨z, h.z_mem_K⟩) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : (⟨z, h.z_mem_K⟩ : ↥K) ^ 3 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one z
    rw [h.z_order] at this
    simpa using this
  have hl3 : f ⟨z, h.z_mem_K⟩ ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hl1 : f ⟨z, h.z_mem_K⟩ ≠ 1 := by
    intro h1
    have hzO : z ∈ pCoreOf 2 H := (h.f_ker ⟨z, h.z_mem_K⟩).1 h1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨z, hzO⟩
    have hz2 : z ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hd : 3 ∣ 2 ^ n := h.z_order ▸ orderOf_dvd_of_pow_eq_one hz2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  exact orderOf_eq_prime hl3 hl1

private theorem four_ne_bot (h : Data619 M B H S K z f) (hV : ¬ K ⊓ S ≤ pCoreOf 2 H) :
    fourVbar S K f ≠ ⊥ := by
  obtain ⟨k, hk, hko⟩ := IsConcreteLE.not_le_iff_exists.1 hV
  intro hbot
  have hmem : f ⟨k, (Subgroup.mem_inf.1 hk).1⟩ ∈ fourVbar S K f :=
    mem_fourVbar.2 ⟨⟨k, (Subgroup.mem_inf.1 hk).1⟩, (Subgroup.mem_inf.1 hk).2, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hko ((h.f_ker _).1 hmem)

omit [Finite G] in
private theorem four_conj_mem {S K : Subgroup G} {f : ↥K →* GL32} {w : G} (hw : w ∈ K)
    (hwS : ∀ s ∈ S, w * s * w⁻¹ ∈ S) {v : GL32} (hv : v ∈ fourVbar S K f) :
    f ⟨w, hw⟩ * v * (f ⟨w, hw⟩)⁻¹ ∈ fourVbar S K f := by
  obtain ⟨k, hkS, rfl⟩ := mem_fourVbar.1 hv
  refine mem_fourVbar.2 ⟨⟨w * k * w⁻¹, K.mul_mem (K.mul_mem hw k.2) (K.inv_mem hw)⟩, hwS _ hkS, ?_⟩
  have : (⟨w * k * w⁻¹, K.mul_mem (K.mul_mem hw k.2) (K.inv_mem hw)⟩ : ↥K) =
      ⟨w, hw⟩ * k * ⟨w, hw⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]

private theorem four_mem_normalizer (h : Data619 M B H S K z f) :
    f ⟨z, h.z_mem_K⟩ ∈ normalizer (fourVbar S K f : Set GL32) := by
  have hzN : z ∈ normalizer (S : Set G) := h.maxInv.1.2.2 h.z_mem_B
  have hzS : ∀ s ∈ S, z * s * z⁻¹ ∈ S := fun s hs => (mem_normalizer_iff.1 hzN s).1 hs
  have hzS' : ∀ s ∈ S, z⁻¹ * s * z⁻¹⁻¹ ∈ S := fun s hs =>
    (mem_normalizer_iff.1 ((normalizer (S : Set G)).inv_mem hzN) s).1 hs
  rw [mem_normalizer_iff]
  intro v
  refine ⟨four_conj_mem h.z_mem_K hzS, fun hv => ?_⟩
  have h' := four_conj_mem (S := S) (f := f) (K.inv_mem h.z_mem_K) hzS' hv
  have e : f ⟨z⁻¹, K.inv_mem h.z_mem_K⟩ = (f ⟨z, h.z_mem_K⟩)⁻¹ := by
    rw [← map_inv]; rfl
  rw [e, inv_inv] at h'
  have e2 : (f ⟨z, h.z_mem_K⟩)⁻¹ * (f ⟨z, h.z_mem_K⟩ * v * (f ⟨z, h.z_mem_K⟩)⁻¹) *
      f ⟨z, h.z_mem_K⟩ = v := by group
  rw [e2] at h'
  exact h'

private theorem four_map_eq (h : Data619 M B H S K z f) {Φ : ↥S →* MulAut GL32}
    (hΦ : ∀ (n : ↥S) (k k' : ↥K),
      (k' : G) = (n : G) * (k : G) * (n : G)⁻¹ → Φ n (f k) = f k')
    (a : ↥S) : (fourVbar S K f).map (Φ a).toMonoidHom = fourVbar S K f := by
  have hle : ∀ b : ↥S, ∀ v ∈ fourVbar S K f, Φ b v ∈ fourVbar S K f := by
    intro b v hv
    obtain ⟨k, hkS, rfl⟩ := mem_fourVbar.1 hv
    have hk' : (b : G) * k * (b : G)⁻¹ ∈ K :=
      (mem_normalizer_iff.1 (h.K_normal (h.maxInv.1.1 b.2)) _).1 k.2
    rw [hΦ b k ⟨b * k * b⁻¹, hk'⟩ rfl]
    exact mem_fourVbar.2 ⟨_, S.mul_mem (S.mul_mem b.2 hkS) (S.inv_mem b.2), rfl⟩
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact hle a v hv
  · intro v hv
    refine ⟨Φ a⁻¹ v, hle _ v hv, ?_⟩
    show Φ a (Φ a⁻¹ v) = v
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem Data619.four_of_not_inf_le (h : Data619 M B H S K z f) (hV : ¬ K ⊓ S ≤ pCoreOf 2 H) :
    S ≤ K ⊔ pCoreOf 2 H ∧ (pCoreOf 2 H).relIndex S = 4 := by
  obtain ⟨Φ, hΦ⟩ := h.exists_phi
  have hl := four_orderOf_l h
  have hV2 := four_isPGroup h
  have hne := four_ne_bot h hV
  have hlV := four_mem_normalizer h
  have hcard : Nat.card (fourVbar S K f) = 4 :=
    L32Insp.card_eq_four_of_normalized_two_subgroup hl hV2 hne hlV
  have hSle : S ≤ K ⊔ pCoreOf 2 H := fun a ha =>
    h.mem_sup_of_mem_Inn hΦ (a := ⟨a, ha⟩)
      (L32Insp.mem_Inn_of_map_eq_of_normalized hl hV2 hne hlV (four_map_eq h hΦ ⟨a, ha⟩))
  refine ⟨hSle, ?_⟩
  have hOS : ((pCoreOf 2 H).subgroupOf S).Normal :=
    (normal_subgroupOf_iff_le_normalizer h.core_le).2 (h.maxInv.1.1.trans h.eq_normalizer.le)
  let θ : ↥(K ⊓ S) →* ↥S ⧸ (pCoreOf 2 H).subgroupOf S :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion (inf_le_right : K ⊓ S ≤ S))
  let π : ↥(K ⊓ S) →* GL32 := f.comp (Subgroup.inclusion (inf_le_left : K ⊓ S ≤ K))
  have hθs : Function.Surjective θ := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, o, ho, hao⟩ := h.exists_mul_of_mem_sup a.2 (hSle a.2)
    refine ⟨⟨k, hk⟩, ?_⟩
    show (QuotientGroup.mk (⟨k, (Subgroup.mem_inf.1 hk).2⟩ : ↥S) : ↥S ⧸ _) = QuotientGroup.mk a
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : k⁻¹ * (a : G) = o := by rw [hao]; group
    change k⁻¹ * (a : G) ∈ pCoreOf 2 H
    rw [this]
    exact ho
  have hker : θ.ker = π.ker := by
    ext k
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hk
      have := (QuotientGroup.eq_one_iff _).1 hk
      exact (h.f_ker _).2 (Subgroup.mem_subgroupOf.1 this)
    · intro hk
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 ((h.f_ker _).1 hk))
  have hrange : π.range = fourVbar S K f := by
    ext v
    constructor
    · rintro ⟨k, rfl⟩
      exact mem_fourVbar.2 ⟨⟨k, (Subgroup.mem_inf.1 k.2).1⟩, (Subgroup.mem_inf.1 k.2).2, rfl⟩
    · intro hv
      obtain ⟨k, hkS, rfl⟩ := mem_fourVbar.1 hv
      exact ⟨⟨k, Subgroup.mem_inf.2 ⟨k.2, hkS⟩⟩, rfl⟩
  calc (pCoreOf 2 H).relIndex S = Nat.card (↥S ⧸ (pCoreOf 2 H).subgroupOf S) :=
        Subgroup.index_eq_card _
    _ = Nat.card (↥(K ⊓ S) ⧸ θ.ker) :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθs).toEquiv).symm
    _ = Nat.card (↥(K ⊓ S) ⧸ π.ker) := by rw [hker]
    _ = Nat.card π.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv
    _ = 4 := by rw [hrange, hcard]

end CFSG.LocalAnalysis.RankThreeTheoremC
